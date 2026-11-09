use anyhow::{Context, Result};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use crate::db::TurboStore;
use crate::lake_build::{detect_toolchain, resolve_lean_bin};
use crate::splitter;

/// Kernel-attested declaration identity and canonical `statement-v1` kernel type hash
/// read from a frozen, isolated `.olean` module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConfirmedDeclIdentity {
    pub(crate) decl_name: String,
    pub(crate) kernel_type_hash: String,
}

#[derive(Debug, Clone)]
pub(super) struct OleanDeclEntry {
    pub(super) decl_name: String,
    pub(super) kernel_type_hash: String,
    pub(super) line: Option<usize>,
}

#[cfg_attr(not(test), allow(private_interfaces))]
pub(super) fn match_expected_decl_identity(
    expected: &str,
    entries: &[OleanDeclEntry],
    span: Option<(usize, usize)>,
) -> Result<ConfirmedDeclIdentity> {
    let expected_canon = splitter::canonicalize_lean_name(expected);
    let mut matched: Option<ConfirmedDeclIdentity> = None;
    for entry in entries {
        if let Some((min_line, max_line)) = span {
            let Some(ln) = entry.line else {
                continue;
            };
            if ln < min_line || ln > max_line {
                continue;
            }
        }
        if splitter::canonicalize_lean_name(&entry.decl_name) != expected_canon {
            continue;
        }
        if let Some(ref prev) = matched {
            anyhow::ensure!(
                prev.kernel_type_hash == entry.kernel_type_hash,
                "Declaration identity confirmation failed for `{expected}`: conflicting declarations in probe span"
            );
        } else {
            matched = Some(ConfirmedDeclIdentity {
                decl_name: expected_canon.clone(),
                kernel_type_hash: entry.kernel_type_hash.clone(),
            });
        }
    }
    matched.ok_or_else(|| {
        anyhow::anyhow!(
            "Declaration identity confirmation failed for `{expected}`: the compiled module declares {:?}",
            entries.iter().map(|d| d.decl_name.as_str()).collect::<Vec<_>>()
        )
    })
}

#[allow(clippy::too_many_arguments)]
/// Return a per-UID `0700` scratch base inside `std::env::temp_dir()` when every ancestor is
/// owned by `root` or `geteuid()` and only sticky when writable by others (falling back to
/// `ensure_verified_private_staging_dir(Some("scratch"))`).
pub(crate) fn verified_private_temp_scratch_base() -> Result<PathBuf> {
    if let Some(dir) = crate::zygote::private_temp_subdir("turbo_lean_scratch") {
        return Ok(dir);
    }
    crate::shm_cache::ensure_verified_private_staging_dir(Some("scratch")).ok_or_else(|| {
        anyhow::anyhow!("Failed to establish a verified private (0700) temporary scratch root")
    })
}

#[allow(clippy::too_many_arguments)]
fn compile_and_read_probe_identities(
    probe: &str,
    project_dir: &Path,
    is_untrusted: bool,
    lean_args: &[String],
    env: Option<&HashMap<String, String>>,
    extra_ro_olean_dirs: &[PathBuf],
    min_line: usize,
    max_line: usize,
    probe_started: Instant,
) -> Result<Vec<OleanDeclEntry>> {
    // Three disjoint private (0700, exclusively created) scratch directories separate
    // read-only probe input (`src_scratch`), compiler output (`out_scratch`), and the
    // trusted reader's frozen `.olean` copy (`reader_scratch`).
    let scratch_base = verified_private_temp_scratch_base()?;
    let src_scratch = PrivateScratchDir::create(&scratch_base, "turbo_id_src")?;
    let nonce = src_scratch.nonce.clone();
    let out_scratch =
        PrivateScratchDir::create_with_nonce(&scratch_base, "turbo_id_out", nonce.clone())?;
    let reader_scratch =
        PrivateScratchDir::create_with_nonce(&scratch_base, "turbo_id_rdr", nonce.clone())?;
    let probe_nonce = format!("id_{nonce}");
    let result = (|| -> Result<Vec<OleanDeclEntry>> {
        let module = format!("TurboIdentityProbe_{nonce}");
        let source = src_scratch.path.join(format!("{module}.lean"));
        let out_olean = out_scratch.path.join(format!("{module}.olean"));
        create_readonly_private_file(&source, probe.as_bytes())?;
        freeze_private_dir(&src_scratch.path)?;
        let mut ro_binds: Vec<&Path> = Vec::with_capacity(1 + extra_ro_olean_dirs.len());
        ro_binds.push(&src_scratch.path);
        for d in extra_ro_olean_dirs {
            ro_binds.push(d.as_path());
        }
        let mut compile = if let Some(cmd) = crate::pr_verify::probe_lean_ro_bwrap_command(
            project_dir,
            is_untrusted,
            &ro_binds,
            &[&out_scratch.path],
            &probe_nonce,
        )? {
            cmd
        } else {
            let env_ref = env.context("Missing Lean environment for declaration identity probe")?;
            let lean_bin = resolve_lean_bin(project_dir)?;
            let mut command =
                crate::module_builder::verifier_command(Path::new(&lean_bin), env_ref)?;
            command
                .current_dir(project_dir)
                .env("TURBO_LEAN_PROBE_NONCE", &probe_nonce);
            command
        };
        compile
            .args(crate::module_builder::filter_allowed_lean_args(lean_args))
            .arg(&source)
            .arg("-R")
            .arg(&src_scratch.path)
            .arg("-o")
            .arg(&out_olean);
        // Reap the entire compiler process group and any background child carrying `probe_nonce`
        // BEFORE inspecting or freezing `out_scratch`.
        let compile_budget =
            crate::zygote::decl_identity_reader_budget_ms(is_untrusted, Some(probe_started));
        let compiled_res = crate::zygote::run_lean_command(&mut compile, Some(compile_budget));
        crate::zygote::reap_processes_with_nonce(&probe_nonce);
        let compiled = compiled_res?;
        freeze_private_dir(&out_scratch.path)?;
        stage_isolated_module_artifacts(&out_scratch.path, &reader_scratch.path, &module)
            .with_context(|| {
                format!(
                    "Declaration identity probe failed isolated `.olean` validation: {}{}",
                    String::from_utf8_lossy(&compiled.stdout),
                    String::from_utf8_lossy(&compiled.stderr)
                )
            })?;
        freeze_private_dir(&reader_scratch.path)?;
        read_olean_theorem_identities(
            project_dir,
            &reader_scratch.path,
            &module,
            min_line,
            max_line,
            env,
            extra_ro_olean_dirs,
            is_untrusted,
            Some(probe_started),
        )
    })();
    let c1 = src_scratch.remove();
    let c2 = out_scratch.remove();
    let c3 = reader_scratch.remove();
    result.and_then(|decls| {
        c1?;
        c2?;
        c3?;
        Ok(decls)
    })
}

type IdentityProbeContext = (Vec<String>, Option<HashMap<String, String>>);

fn resolve_identity_probe_context(
    project_dir: &Path,
    file: &Path,
    is_untrusted: bool,
    extra_ro_olean_dirs: &[PathBuf],
) -> Result<IdentityProbeContext> {
    let lean_args = if project_dir.join("lakefile.toml").try_exists()?
        || project_dir.join("lakefile.lean").try_exists()?
    {
        let pkg = crate::module_builder::resolve_package_config(project_dir, is_untrusted)
            .context("Failed to resolve Lean options for declaration identity")?;
        crate::module_builder::resolve_file_lean_args_in_package(&pkg, file)
    } else {
        Vec::new()
    };
    let env = if is_untrusted {
        None
    } else {
        let mut ev = crate::lake_build::spawn_lake_env(project_dir)?;
        crate::lake_build::merge_caller_lean_path(&mut ev);
        if !extra_ro_olean_dirs.is_empty() {
            let prefix = extra_ro_olean_dirs
                .iter()
                .map(|d| d.to_string_lossy().to_string())
                .collect::<Vec<_>>()
                .join(":");
            let combined = match ev.get("LEAN_PATH").filter(|s| !s.is_empty()) {
                Some(existing) => format!("{prefix}:{existing}"),
                None => prefix,
            };
            ev.insert("LEAN_PATH".to_string(), combined);
        }
        Some(ev)
    };
    Ok((lean_args, env))
}

/// Build the local zygote before the request timer starts, but only on the local miss path.
/// Remote checks and full cache hits never call this, so they do not need a local Lean compiler.
pub(super) fn prewarm_local_check_zygote(
    store: &TurboStore,
    canon_dir: &Path,
    toolchain: &str,
    t0: &Instant,
) -> Result<Instant> {
    if crate::zygote::invocation_timeout_ms().is_some() {
        return Ok(*t0);
    }
    let (lean_bin, _, _, _) =
        crate::module_builder::resolve_toolchain_compiler(canon_dir, toolchain)?;
    crate::zygote::ensure_zygote_binary(store, &lean_bin, &HashMap::new())?;
    Ok(Instant::now())
}

/// Confirm the selected source declaration and its canonical kernel statement type in Lean's
/// environment, independently of textual scope tracking. This probe replaces only the proof:
/// false statements must still have an attested identity before Stage-1 can attribute a
/// counterexample, and proof verification must match `kernel_type_hash` in the elaborated kernel
/// environment. No result or identity is cached; unavailable elaboration fails closed.
pub(crate) fn confirm_decl_identity(
    src: &str,
    shard: &splitter::TheoremShard,
    project_dir: &Path,
    file: &Path,
) -> Result<ConfirmedDeclIdentity> {
    confirm_decl_identity_with_budget(src, shard, project_dir, file, false, None)
}

#[cfg(test)]
pub(crate) fn confirm_decl_identity_with_trust(
    src: &str,
    shard: &splitter::TheoremShard,
    project_dir: &Path,
    file: &Path,
    is_untrusted: bool,
) -> Result<ConfirmedDeclIdentity> {
    confirm_decl_identity_with_budget(src, shard, project_dir, file, is_untrusted, None)
}

pub(crate) fn confirm_decl_identity_with_budget(
    src: &str,
    shard: &splitter::TheoremShard,
    project_dir: &Path,
    file: &Path,
    is_untrusted: bool,
    request_started: Option<Instant>,
) -> Result<ConfirmedDeclIdentity> {
    confirm_decl_identity_with_extra_dirs(
        src,
        shard,
        project_dir,
        file,
        is_untrusted,
        &[],
        request_started,
    )
}

pub(super) fn confirm_decl_identity_with_extra_dirs(
    src: &str,
    shard: &splitter::TheoremShard,
    project_dir: &Path,
    file: &Path,
    is_untrusted: bool,
    extra_ro_olean_dirs: &[PathBuf],
    request_started: Option<Instant>,
) -> Result<ConfirmedDeclIdentity> {
    let probe_started = request_started.unwrap_or_else(Instant::now);
    let expected = shard.decl_name();
    let prefix = splitter::declaration_identity_prefix(src, shard);
    let header_info = crate::module_builder::parse_header_info(&prefix);
    let (header, prefix) = prefix.split_at(header_info.body_byte_offset);
    let (signature, _) = splitter::extract_shard_stmt_and_proof(src, shard);
    anyhow::ensure!(
        !signature.is_empty(),
        "Declaration identity unavailable for `{expected}`: missing signature"
    );
    let before = format!(
        "{header}\nset_option warningAsError false\nset_option warn.sorry false\n{prefix}\nset_option warningAsError false\nset_option warn.sorry false\n"
    );
    let probe_start_line = before.matches('\n').count() + 1;
    let stub_end_line = probe_start_line + signature.matches('\n').count();
    let stub_probe = format!("{before}{signature}\n:= by sorry\n");
    let (lean_args, env) =
        resolve_identity_probe_context(project_dir, file, is_untrusted, extra_ro_olean_dirs)?;
    let stub_attempt = compile_and_read_probe_identities(
        &stub_probe,
        project_dir,
        is_untrusted,
        &lean_args,
        env.as_ref(),
        extra_ro_olean_dirs,
        probe_start_line,
        stub_end_line,
        probe_started,
    )
    .and_then(|decls| match_expected_decl_identity(expected, &decls, None));
    let result = match stub_attempt {
        Ok(att) => Ok(att),
        Err(stub_err) => {
            // Proof-driven type inference (`theorem t : _ := ...` or equation-compiler arms)
            // cannot elaborate against `:= by sorry`; retry once in a fresh isolated scratch
            // probe with the declaration's original text.
            let decl_lines = splitter::extract_shard_orig_decl(src, shard);
            if decl_lines.trim().is_empty() {
                Err(stub_err)
            } else {
                let full_end_line = probe_start_line + decl_lines.matches('\n').count();
                let full_probe = format!("{before}{decl_lines}\n");
                compile_and_read_probe_identities(
                    &full_probe,
                    project_dir,
                    is_untrusted,
                    &lean_args,
                    env.as_ref(),
                    extra_ro_olean_dirs,
                    probe_start_line,
                    full_end_line,
                    probe_started,
                )
                .and_then(|decls| match_expected_decl_identity(expected, &decls, None))
                .map_err(|_| stub_err)
            }
        }
    };
    result.with_context(|| {
        format!("Cannot report a verdict: declaration identity unconfirmed for `{expected}`")
    })
}

/// Confirm all `shards` in `file` via a single batched stubbed file probe when possible,
/// falling back per-shard to `confirm_decl_identity_with_budget` only for declarations whose
/// statement requires proof-driven type inference or equation-compiler elaboration.
pub(crate) fn confirm_file_decl_identities_with_budget(
    src: &str,
    shards: &[&splitter::TheoremShard],
    project_dir: &Path,
    file: &Path,
    is_untrusted: bool,
    request_started: Option<Instant>,
) -> Result<Vec<ConfirmedDeclIdentity>> {
    confirm_file_decl_identities_with_extra_dirs(
        src,
        shards,
        project_dir,
        file,
        is_untrusted,
        &[],
        request_started,
    )
}

pub(crate) fn confirm_file_decl_identities_with_extra_dirs(
    src: &str,
    shards: &[&splitter::TheoremShard],
    project_dir: &Path,
    file: &Path,
    is_untrusted: bool,
    extra_ro_olean_dirs: &[PathBuf],
    request_started: Option<Instant>,
) -> Result<Vec<ConfirmedDeclIdentity>> {
    if shards.is_empty() {
        return Ok(Vec::new());
    }
    if shards.len() == 1 {
        return Ok(vec![confirm_decl_identity_with_extra_dirs(
            src,
            shards[0],
            project_dir,
            file,
            is_untrusted,
            extra_ro_olean_dirs,
            request_started,
        )?]);
    }
    let probe_started = request_started.unwrap_or_else(Instant::now);
    let (lean_args, env) =
        resolve_identity_probe_context(project_dir, file, is_untrusted, extra_ro_olean_dirs)?;
    let (batch_probe, line_offset) = splitter::build_file_identity_probe(src);
    let max_probe_line = batch_probe.matches('\n').count() + 1;
    let batch_entries = compile_and_read_probe_identities(
        &batch_probe,
        project_dir,
        is_untrusted,
        &lean_args,
        env.as_ref(),
        extra_ro_olean_dirs,
        1,
        max_probe_line,
        probe_started,
    )
    .ok();
    let mut out = Vec::with_capacity(shards.len());
    for shard in shards {
        let min_ln = shard.start_line + line_offset;
        let max_ln = shard.end_line + line_offset;
        if let Some(att) = batch_entries.as_deref().and_then(|entries| {
            match_expected_decl_identity(shard.decl_name(), entries, Some((min_ln, max_ln))).ok()
        }) {
            out.push(att);
        } else {
            let probe_started = request_started.unwrap_or_else(Instant::now);
            out.push(confirm_decl_identity_with_extra_dirs(
                src,
                shard,
                project_dir,
                file,
                is_untrusted,
                extra_ro_olean_dirs,
                Some(probe_started),
            )?);
        }
    }
    Ok(out)
}

/// Read the theorem names and canonical `statement-v1` kernel type hashes a compiled probe
/// declares within `[min_line, max_line]` from its isolated `.olean`, in a separate trusted
/// process (the audited zygote reader, initializers disabled).
#[allow(clippy::too_many_arguments)]
fn read_olean_theorem_identities(
    project_dir: &Path,
    scratch: &Path,
    module: &str,
    min_line: usize,
    max_line: usize,
    env: Option<&HashMap<String, String>>,
    extra_ro_olean_dirs: &[PathBuf],
    is_untrusted: bool,
    request_started: Option<Instant>,
) -> Result<Vec<OleanDeclEntry>> {
    let budget_left = |stage: &str| -> Result<Option<std::time::Duration>> {
        request_started
            .map(|t0| {
                let left_ms = crate::zygote::decl_identity_reader_budget_ms(is_untrusted, Some(t0));
                anyhow::ensure!(left_ms > 0, "Lean request timed out before {stage}");
                Ok(std::time::Duration::from_millis(left_ms))
            })
            .transpose()
    };
    let toolchain = detect_toolchain(project_dir);
    let mut reader = if is_untrusted {
        let cfg = crate::pr_verify::resolve_static_or_bare_project_config(project_dir, &toolchain)?;
        let (base_lp, _) = crate::module_builder::build_lean_search_path(&cfg, true);
        let mut lp_parts = Vec::with_capacity(1 + extra_ro_olean_dirs.len() + 1);
        lp_parts.push(scratch.display().to_string());
        for d in extra_ro_olean_dirs {
            lp_parts.push(d.display().to_string());
        }
        if !base_lp.is_empty() {
            lp_parts.push(base_lp);
        }
        let lean_path = lp_parts.join(":");
        let mut reader_ro_binds = Vec::with_capacity(1 + extra_ro_olean_dirs.len());
        reader_ro_binds.push(scratch.to_path_buf());
        reader_ro_binds.extend(extra_ro_olean_dirs.iter().cloned());
        match budget_left("the `.olean` declaration-identity reader was ready")? {
            None => {
                crate::zygote::kernel_reader_command(
                    &crate::shm_cache::cache_root(),
                    &cfg,
                    &lean_path,
                    &reader_ro_binds,
                    true,
                )?
                .0
            }
            Some(left) => {
                let (tx, rx) = std::sync::mpsc::channel();
                let root = crate::shm_cache::cache_root();
                let boot_env = crate::zygote::build_auditor_bootstrap_env(&cfg);
                let lb = cfg.lean_bin.clone();
                std::thread::spawn(move || {
                    let _ = tx.send(crate::zygote::ensure_zygote_binary_at(
                        &root, &lb, &boot_env,
                    ));
                });
                rx.recv_timeout(left).map_err(|_| {
                    anyhow::anyhow!(
                        "Lean request timed out before the `.olean` declaration-identity reader was ready"
                    )
                })??;
                crate::zygote::kernel_reader_command(
                    &crate::shm_cache::cache_root(),
                    &cfg,
                    &lean_path,
                    &reader_ro_binds,
                    true,
                )?
                .0
            }
        }
    } else {
        let env = env.context("Missing Lean environment for identity reader")?;
        let lean_bin = PathBuf::from(resolve_lean_bin(project_dir)?);
        let tools = crate::module_builder::ToolchainExecutables::from_lean(&lean_bin)?;
        let lean_bin = tools.lean.clone();
        let mut sanitized_env = env.clone();
        tools.apply_env(&mut sanitized_env);
        let zygote = match budget_left("the `.olean` declaration-identity reader was ready")? {
            None => crate::zygote::ensure_zygote_binary_at(
                &crate::shm_cache::cache_root(),
                &lean_bin,
                &sanitized_env,
            )?,
            Some(left) => {
                let (tx, rx) = std::sync::mpsc::channel();
                let root = crate::shm_cache::cache_root();
                let lb = lean_bin.clone();
                let ev = sanitized_env.clone();
                std::thread::spawn(move || {
                    let _ = tx.send(crate::zygote::ensure_zygote_binary_at(&root, &lb, &ev));
                });
                rx.recv_timeout(left).map_err(|_| {
                    anyhow::anyhow!(
                        "Lean request timed out before the `.olean` declaration-identity reader was ready"
                    )
                })??
            }
        };
        let mut prefix_cmd = crate::module_builder::verifier_command(&lean_bin, &sanitized_env)?;
        prefix_cmd.arg("--print-prefix");
        let prefix = match budget_left("the toolchain prefix query")? {
            None => prefix_cmd
                .output()
                .context("Failed to query the Lean toolchain prefix for the identity reader")?,
            Some(left) => crate::zygote::run_lean_command(
                &mut prefix_cmd,
                Some(left.as_millis().max(1) as u64),
            )
            .context("Failed to query the Lean toolchain prefix for the identity reader")?,
        };
        anyhow::ensure!(prefix.status.success(), "`lean --print-prefix` failed");
        let prefix = PathBuf::from(String::from_utf8_lossy(&prefix.stdout).trim());
        let lean_path = std::iter::once(scratch.display().to_string())
            .chain(extra_ro_olean_dirs.iter().map(|d| d.display().to_string()))
            .chain(sanitized_env.get("LEAN_PATH").cloned())
            .chain(std::iter::once(
                prefix.join("lib/lean").display().to_string(),
            ))
            .collect::<Vec<_>>()
            .join(":");
        let mut command = Command::new(zygote);
        command
            .current_dir(project_dir)
            .envs(&sanitized_env)
            .env("PATH", crate::module_builder::verifier_path(&lean_bin))
            .env("LEAN", &lean_bin)
            .env("LEAN_PATH", lean_path)
            .env(
                "LD_LIBRARY_PATH",
                format!(
                    "{}:{}",
                    prefix.join("lib/lean").display(),
                    prefix.join("lib").display()
                ),
            );
        command
    };
    reader
        .arg("--decl-identity")
        .arg(module)
        .arg(min_line.to_string())
        .arg(max_line.to_string());
    // Same budget as the module auditor (it imports the same closure), capped by any remaining request budget.
    let budget_ms = crate::zygote::decl_identity_reader_budget_ms(is_untrusted, request_started);
    let out = crate::zygote::run_lean_command(&mut reader, Some(budget_ms))
        .context("Failed to run the `.olean` declaration-identity reader")?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    let reply = stdout
        .lines()
        .rev()
        .find(|l| l.trim_start().starts_with('{'))
        .filter(|_| out.status.success())
        .and_then(|l| serde_json::from_str::<serde_json::Value>(l).ok())
        .with_context(|| {
            format!(
                "`.olean` declaration-identity reader failed closed: {stdout}{}",
                String::from_utf8_lossy(&out.stderr)
            )
        })?;
    reply["decls"]
        .as_array()
        .context("`.olean` declaration-identity reader returned no decls")?
        .iter()
        .map(|d| {
            let name = d["name"]
                .as_str()
                .map(str::to_string)
                .context("missing or non-string declaration name in `--decl-identity`")?;
            let type_hash = d["type_hash"]
                .as_str()
                .filter(|h| h.len() == 64 && h.bytes().all(|b| b.is_ascii_hexdigit()))
                .map(str::to_string)
                .context("missing or invalid 64-hex `type_hash` in `--decl-identity`")?;
            let line = d["line"].as_u64().and_then(|n| usize::try_from(n).ok());
            Ok(OleanDeclEntry {
                decl_name: name,
                kernel_type_hash: type_hash,
                line,
            })
        })
        .collect()
}

/// A fresh, exclusively created, owner-only scratch directory. `remove` reports cleanup
/// failures; `Drop` is only the fallback for early returns and panics.
pub(crate) struct PrivateScratchDir {
    pub(crate) path: PathBuf,
    pub(crate) nonce: String,
    armed: bool,
    lease: Option<crate::shm_cache::StagingLeaseGuard>,
}

impl PrivateScratchDir {
    pub(crate) fn create(base: &Path, label: &str) -> Result<Self> {
        let nonce = format!(
            "{}_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_nanos(),
            crate::pack::next_tmp_id()
        );
        Self::create_with_nonce(base, label, nonce)
    }

    pub(crate) fn create_with_nonce(base: &Path, label: &str, nonce: String) -> Result<Self> {
        let path = base.join(format!("{label}_{nonce}"));
        let lease = crate::shm_cache::StagingLeaseGuard::acquire_for_target(&path)
            .with_context(|| format!("Failed to acquire staging lease for `{}`", path.display()))?;
        let mut builder = fs::DirBuilder::new();
        #[cfg(unix)]
        std::os::unix::fs::DirBuilderExt::mode(&mut builder, 0o700);
        // `create` (not `create_all`) fails on any existing entry, including symlinks.
        if let Err(e) = builder
            .create(&path)
            .with_context(|| format!("Failed to create private scratch dir `{}`", path.display()))
        {
            drop(lease);
            return Err(e);
        }
        Ok(Self {
            path,
            nonce,
            armed: true,
            lease: Some(lease),
        })
    }

    pub(crate) fn remove(mut self) -> Result<()> {
        self.armed = false;
        thaw_private_dir_tree(&self.path);
        let res = fs::remove_dir_all(&self.path)
            .with_context(|| format!("Failed to remove scratch dir `{}`", self.path.display()));
        drop(self.lease.take());
        res
    }
}

impl Drop for PrivateScratchDir {
    fn drop(&mut self) {
        if self.armed {
            thaw_private_dir_tree(&self.path);
            let _ = fs::remove_dir_all(&self.path);
        }
        drop(self.lease.take());
    }
}

pub(crate) fn thaw_private_dir_tree(dir: &Path) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if let Ok(meta) = fs::symlink_metadata(dir) {
            if meta.file_type().is_dir() {
                let _ = fs::set_permissions(dir, fs::Permissions::from_mode(0o700));
                if let Ok(entries) = fs::read_dir(dir) {
                    for entry in entries.flatten() {
                        let p = entry.path();
                        if let Ok(em) = fs::symlink_metadata(&p) {
                            if em.file_type().is_dir() {
                                thaw_private_dir_tree(&p);
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Freeze `dir` to `0o500` (never following symlinks) so no process can create, unlink, or
/// rename entries inside it.
pub(crate) fn freeze_private_dir(dir: &Path) -> Result<()> {
    let meta = fs::symlink_metadata(dir)
        .with_context(|| format!("Missing scratch dir `{}`", dir.display()))?;
    anyhow::ensure!(
        meta.file_type().is_dir() && !meta.file_type().is_symlink(),
        "Refusing to freeze non-directory `{}`",
        dir.display()
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(dir, fs::Permissions::from_mode(0o500))
            .with_context(|| format!("Failed to freeze scratch dir `{}`", dir.display()))?;
    }
    Ok(())
}

/// Exclusively create `path` (never following or replacing an existing entry) and write `bytes`.
#[cfg(test)]
pub(crate) fn create_private_file(path: &Path, bytes: &[u8]) -> Result<()> {
    create_private_file_with_mode(path, bytes, 0o600)
}

/// Exclusively create read-only (`0o400`) `path` and write `bytes`.
pub(crate) fn create_readonly_private_file(path: &Path, bytes: &[u8]) -> Result<()> {
    create_private_file_with_mode(path, bytes, 0o400)
}

fn create_private_file_with_mode(path: &Path, bytes: &[u8], mode: u32) -> Result<()> {
    use std::io::Write;
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(mode).custom_flags(libc::O_NOFOLLOW);
    }
    #[cfg(not(unix))]
    let _ = mode;
    let mut file = options
        .open(path)
        .with_context(|| format!("Refusing to reuse existing probe file `{}`", path.display()))?;
    file.write_all(bytes)?;
    file.sync_all()?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        file.set_permissions(fs::Permissions::from_mode(mode))?;
    }
    Ok(())
}

fn read_verified_isolated_artifact(artifact_path: &Path) -> Result<Vec<u8>> {
    let mut options = fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NOFOLLOW);
    }
    let mut file = options.open(artifact_path).with_context(|| {
        format!(
            "Failed to open isolated artifact `{}` without following symlinks",
            artifact_path.display()
        )
    })?;
    #[cfg(unix)]
    let snap1 = {
        use std::os::fd::AsRawFd;
        let mut st1: libc::stat = unsafe { std::mem::zeroed() };
        anyhow::ensure!(
            unsafe { libc::fstat(file.as_raw_fd(), &mut st1) } == 0,
            "fstat failed on `{}`",
            artifact_path.display()
        );
        let euid = unsafe { libc::geteuid() };
        anyhow::ensure!(
            (st1.st_mode & libc::S_IFMT) == libc::S_IFREG,
            "`{}` is not a regular file",
            artifact_path.display()
        );
        anyhow::ensure!(
            st1.st_uid == euid,
            "`{}` uid {} does not match effective uid {}",
            artifact_path.display(),
            st1.st_uid,
            euid
        );
        anyhow::ensure!(
            st1.st_nlink == 1,
            "`{}` has unexpected hard-link count {} (expected 1)",
            artifact_path.display(),
            st1.st_nlink
        );
        anyhow::ensure!(st1.st_size > 0, "`{}` is empty", artifact_path.display());
        (
            st1.st_dev,
            st1.st_ino,
            st1.st_size,
            st1.st_mtime,
            st1.st_mtime_nsec,
            st1.st_ctime,
            st1.st_ctime_nsec,
        )
    };
    use std::io::{Read, Seek, SeekFrom};
    let mut bytes1 = Vec::new();
    file.read_to_end(&mut bytes1)?;
    anyhow::ensure!(
        !bytes1.is_empty(),
        "`{}` read 0 bytes",
        artifact_path.display()
    );
    file.seek(SeekFrom::Start(0))?;
    let mut bytes2 = Vec::with_capacity(bytes1.len());
    file.read_to_end(&mut bytes2)?;
    #[cfg(unix)]
    {
        use std::os::fd::AsRawFd;
        let mut st2: libc::stat = unsafe { std::mem::zeroed() };
        anyhow::ensure!(
            unsafe { libc::fstat(file.as_raw_fd(), &mut st2) } == 0,
            "second fstat failed on `{}`",
            artifact_path.display()
        );
        let snap2 = (
            st2.st_dev,
            st2.st_ino,
            st2.st_size,
            st2.st_mtime,
            st2.st_mtime_nsec,
            st2.st_ctime,
            st2.st_ctime_nsec,
        );
        anyhow::ensure!(
            snap1 == snap2,
            "Concurrent mutation detected via fstat on `{}` ({snap1:?} != {snap2:?})",
            artifact_path.display()
        );
    }
    anyhow::ensure!(
        blake3::hash(&bytes1) == blake3::hash(&bytes2) && bytes1 == bytes2,
        "Concurrent mutation detected while reading `{}`",
        artifact_path.display()
    );
    Ok(bytes1)
}

/// Validate that `out_dir` contains `<module>.olean` and ONLY Lean 4.35 single-module companion
/// artifacts (`<module>.olean.{server,private}` and `<module>.ir{,.sig}`), verify every present
/// file with `O_NOFOLLOW`, `st_uid == geteuid()`, `st_nlink == 1`, `st_size > 0`, and
/// double-read + double-`fstat` snapshot stability, and copy `<module>.olean{,.server,.private}`
/// into `reader_dir` as `0o400` read-only files.
pub(crate) fn stage_isolated_module_artifacts(
    out_dir: &Path,
    reader_dir: &Path,
    module: &str,
) -> Result<()> {
    let expected_olean = format!("{module}.olean");
    let allowed_companions = [
        format!("{module}.olean.server"),
        format!("{module}.olean.private"),
        format!("{module}.ir"),
        format!("{module}.ir.sig"),
    ];
    let mut entries = Vec::new();
    for entry in fs::read_dir(out_dir).with_context(|| {
        format!(
            "Failed to inspect compiler output dir `{}`",
            out_dir.display()
        )
    })? {
        let entry = entry?;
        entries.push(entry.file_name().to_string_lossy().to_string());
    }
    anyhow::ensure!(
        entries.iter().any(|e| e == &expected_olean),
        "produced no `.olean` in isolated output dir `{}` (expected `{expected_olean}`, found {entries:?})",
        out_dir.display()
    );
    entries.sort();
    for name in &entries {
        let is_allowed = name == &expected_olean || allowed_companions.iter().any(|c| c == name);
        anyhow::ensure!(
            is_allowed,
            "Isolated `.olean` output dir `{}` must contain only `{expected_olean}` (and optional module companions), found {entries:?}",
            out_dir.display()
        );
        let bytes = read_verified_isolated_artifact(&out_dir.join(name))?;
        if name == &expected_olean
            || name.ends_with(".olean.server")
            || name.ends_with(".olean.private")
        {
            create_readonly_private_file(&reader_dir.join(name), &bytes)?;
        }
    }
    Ok(())
}

/// Validate that `out_dir` contains ONLY the exact expected `<module>.olean` regular file
/// (`st_uid == geteuid()`, `st_nlink == 1`, `st_size > 0`, opened with `O_NOFOLLOW`), and
/// return its contents only if two consecutive reads and `fstat` snapshots agree identically.
#[cfg(test)]
pub(crate) fn read_single_isolated_olean(out_dir: &Path, module: &str) -> Result<Vec<u8>> {
    let expected_name = format!("{module}.olean");
    let mut entries = Vec::new();
    for entry in fs::read_dir(out_dir).with_context(|| {
        format!(
            "Failed to inspect compiler output dir `{}`",
            out_dir.display()
        )
    })? {
        let entry = entry?;
        entries.push(entry.file_name().to_string_lossy().to_string());
    }
    anyhow::ensure!(
        !entries.is_empty(),
        "produced no `.olean` in isolated output dir `{}` (expected `{expected_name}`)",
        out_dir.display()
    );
    anyhow::ensure!(
        entries == [expected_name.as_str()],
        "Isolated `.olean` output dir `{}` must contain only `{expected_name}`, found {entries:?}",
        out_dir.display()
    );
    read_verified_isolated_artifact(&out_dir.join(&expected_name))
}
