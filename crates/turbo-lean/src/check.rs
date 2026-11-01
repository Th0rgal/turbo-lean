//! Incremental theorem-level (`--decl`), file-level, and directory-wide (`check <dir>`)
//! verification with `/dev/shm` stat-split singleflight, local Zygote CoW prefix reuse,
//! and cross-file coalesced shard batching.

use anyhow::{Context, Result};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use crate::db::{self, SingleflightOutcome, TurboStore};
use crate::lake_build::{
    collect_lean_files, compact_split_for_shm_cache, compute_imported_olean_interface_hashes,
    compute_shard_key_with_args, compute_single_stat_hash, detect_toolchain,
    is_file_hash_verified_in_lake_build, is_file_verified_in_lake_build,
    load_and_split_files_with_hashes_cached, load_verified_project_manifest, resolve_lake_env,
    resolve_lean_bin, resolve_prebuilt_module_import, resolve_remote_lean_path,
    shm_file_splits_dir, split_and_audit_cached, ShmCachedFileSplit,
};
use crate::pack;
use crate::pr_verify::{try_fast_split_single_file, try_fast_split_single_file_from_path};
use crate::splitter::{self, split_lean_source};

/// Kernel-attested declaration identity and canonical `statement-v1` kernel type hash
/// read from a frozen, isolated `.olean` module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConfirmedDeclIdentity {
    pub(crate) decl_name: String,
    pub(crate) kernel_type_hash: String,
}

#[derive(Debug, Clone)]
struct OleanDeclEntry {
    decl_name: String,
    kernel_type_hash: String,
    line: Option<usize>,
}

fn match_expected_decl_identity(
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
fn compile_and_read_probe_identities(
    probe: &str,
    project_dir: &Path,
    is_untrusted: bool,
    lean_args: &[String],
    env: Option<&HashMap<String, String>>,
    min_line: usize,
    max_line: usize,
    probe_started: Instant,
) -> Result<Vec<OleanDeclEntry>> {
    // Three disjoint private (0700, exclusively created) scratch directories separate
    // read-only probe input (`src_scratch`), compiler output (`out_scratch`), and the
    // trusted reader's frozen `.olean` copy (`reader_scratch`).
    let src_scratch = PrivateScratchDir::create(&std::env::temp_dir(), "turbo_id_src")?;
    let nonce = src_scratch.nonce.clone();
    let out_scratch =
        PrivateScratchDir::create_with_nonce(&std::env::temp_dir(), "turbo_id_out", nonce.clone())?;
    let reader_scratch =
        PrivateScratchDir::create_with_nonce(&std::env::temp_dir(), "turbo_id_rdr", nonce.clone())?;
    let probe_nonce = format!("id_{nonce}");
    let result = (|| -> Result<Vec<OleanDeclEntry>> {
        let module = format!("TurboIdentityProbe_{nonce}");
        let source = src_scratch.path.join(format!("{module}.lean"));
        let out_olean = out_scratch.path.join(format!("{module}.olean"));
        create_readonly_private_file(&source, probe.as_bytes())?;
        freeze_private_dir(&src_scratch.path)?;
        let mut compile = if let Some(cmd) = crate::pr_verify::probe_lean_ro_bwrap_command(
            project_dir,
            is_untrusted,
            &[&src_scratch.path],
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
        Some(ev)
    };
    Ok((lean_args, env))
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

#[cfg_attr(not(test), allow(dead_code))]
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
    let probe_started = request_started.unwrap_or_else(Instant::now);
    let expected = shard.decl_name();
    let prefix = splitter::declaration_identity_prefix(src, shard.start_line);
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
    let (lean_args, env) = resolve_identity_probe_context(project_dir, file, is_untrusted)?;
    let stub_attempt = compile_and_read_probe_identities(
        &stub_probe,
        project_dir,
        is_untrusted,
        &lean_args,
        env.as_ref(),
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
            let decl_lines = if shard.start_line >= 1 && shard.end_line >= shard.start_line {
                src.lines()
                    .skip(shard.start_line - 1)
                    .take(shard.end_line - shard.start_line + 1)
                    .collect::<Vec<_>>()
                    .join("\n")
            } else {
                String::new()
            };
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
    if shards.is_empty() {
        return Ok(Vec::new());
    }
    if shards.len() == 1 {
        return Ok(vec![confirm_decl_identity_with_budget(
            src,
            shards[0],
            project_dir,
            file,
            is_untrusted,
            request_started,
        )?]);
    }
    let probe_started = request_started.unwrap_or_else(Instant::now);
    let (lean_args, env) = resolve_identity_probe_context(project_dir, file, is_untrusted)?;
    let (batch_probe, line_offset) = splitter::build_file_identity_probe(src);
    let max_probe_line = batch_probe.matches('\n').count() + 1;
    let batch_entries = compile_and_read_probe_identities(
        &batch_probe,
        project_dir,
        is_untrusted,
        &lean_args,
        env.as_ref(),
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
            out.push(confirm_decl_identity_with_budget(
                src,
                shard,
                project_dir,
                file,
                is_untrusted,
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
        let (lean_path, _) = crate::module_builder::build_lean_search_path(&cfg, true);
        let lean_path = if lean_path.is_empty() {
            scratch.display().to_string()
        } else {
            format!("{}:{lean_path}", scratch.display())
        };
        match budget_left("the `.olean` declaration-identity reader was ready")? {
            None => {
                crate::zygote::kernel_reader_command(
                    &crate::shm_cache::cache_root(),
                    &cfg,
                    &lean_path,
                    &[scratch.to_path_buf()],
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
                    &[scratch.to_path_buf()],
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
#[cfg_attr(not(test), allow(dead_code))]
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
#[cfg_attr(not(test), allow(dead_code))]
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

#[allow(dead_code)]
/// Resolve a fresh source split before any single-declaration verdict (including Stage-1).
pub(crate) fn confirm_selected_decl(
    src: &str,
    target: &str,
    project_dir: &Path,
    file: &Path,
) -> Result<ConfirmedDeclIdentity> {
    let split = splitter::split_lean_source(src, &[]);
    let idx = splitter::find_decl_shard_index(&split.shards, target)?
        .with_context(|| format!("Declaration `{target}` not found in {}", file.display()))?;
    confirm_decl_identity(src, &split.shards[idx], project_dir, file)
}

pub(crate) fn make_shard_receipt_bytes(
    decl: &str,
    prefix_env_hash: &str,
    stmt_hash: &str,
    proof_hash: &str,
    verified_at: i64,
) -> Result<Vec<u8>> {
    make_attested_shard_receipt_bytes(
        decl,
        prefix_env_hash,
        stmt_hash,
        proof_hash,
        verified_at,
        None,
    )
}

pub(crate) fn make_attested_shard_receipt_bytes(
    decl: &str,
    prefix_env_hash: &str,
    stmt_hash: &str,
    proof_hash: &str,
    verified_at: i64,
    kernel_type_hash: Option<&str>,
) -> Result<Vec<u8>> {
    let mut obj = serde_json::json!({
        "decl": decl,
        "prefix_env_hash": prefix_env_hash,
        "stmt_hash": stmt_hash,
        "proof_hash": proof_hash,
        "verified_at": verified_at
    });
    if let Some(kth) = kernel_type_hash {
        obj["kernel_type_hash"] = serde_json::Value::String(kth.to_string());
    }
    Ok(serde_json::to_vec(&obj)?)
}

fn cache_shm_stat_split(
    store: &TurboStore,
    canon_file: &Path,
    active_src: &str,
    split: &splitter::SplitResult,
    dep_hashes: Vec<String>,
) {
    if let Ok(meta) = fs::metadata(canon_file) {
        let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&meta);
        let pk = canon_file.to_string_lossy();
        let st_hash = compute_single_stat_hash(&pk, ms, mn, sz);
        let st_path = shm_file_splits_dir(store).join(format!("st_{}.json", &st_hash[..24]));
        let src_b3 = blake3::hash(active_src.as_bytes()).to_hex().to_string();
        let entry = ShmCachedFileSplit {
            split_key: format!("file-split:v10:{}", src_b3),
            src_blake3: src_b3,
            split: compact_split_for_shm_cache(split),
            prefix_src: String::new(),
            known_modified: false,
            dep_hashes,
        };
        if let Ok(bytes) = serde_json::to_vec(&entry) {
            let _ = crate::shm_cache::atomic_write_shm(&st_path, &bytes);
        }
    }
}

fn emit_remote_decl_result(
    json_output: bool,
    emit_stdout: bool,
    resp_json: &serde_json::Value,
    remote_status: &str,
    target_decl: &str,
    shard_key: &str,
    remote_url: &str,
    fast_olean_used: bool,
    interface_hash: &str,
    prefix_env_hash: &str,
    total_shards_in_file: usize,
    dur_ms: i64,
) -> Result<(u64, serde_json::Value)> {
    let server_arch = resp_json
        .get("server_arch")
        .and_then(|v| v.as_str())
        .unwrap_or("unknown");
    let server_elapsed_ms = resp_json
        .get("server_elapsed_ms")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);
    let out_json = serde_json::json!({
        "status": remote_status,
        "decl": target_decl,
        "shard_key": shard_key,
        "remote_url": remote_url,
        "server_arch": server_arch,
        "server_elapsed_ms": server_elapsed_ms,
        "fast_olean_import": fast_olean_used,
        "zygote_used": resp_json.get("zygote_used").and_then(|v| v.as_bool()).unwrap_or(false),
        "zygote_env_cache_hit": resp_json.get("zygote_env_cache_hit").and_then(|v| v.as_bool()).unwrap_or(false),
        "zygote_import_us": resp_json.get("zygote_import_us").and_then(|v| v.as_u64()).unwrap_or(0),
        "zygote_elab_us": resp_json.get("zygote_elab_us").and_then(|v| v.as_u64()).unwrap_or(0),
        "proof_term_nodes": resp_json.get("proof_term_nodes").and_then(|v| v.as_u64()).unwrap_or(0),
        "interface_hash": interface_hash,
        "prefix_env_hash": prefix_env_hash,
        "total_shards_in_file": total_shards_in_file,
        "compact_summary": format!("OK decl={} ms={} stage=remote_{}", target_decl, dur_ms, server_arch),
        "estimated_tokens": 18,
        "elapsed_ms": dur_ms
    });
    if emit_stdout {
        if json_output {
            println!("{}", serde_json::to_string_pretty(&out_json)?);
        } else {
            println!(
                "[turbo-lean] {} `{}` via {} (arch={}, server={} ms, total={} ms)",
                remote_status.to_uppercase(),
                target_decl,
                remote_url,
                server_arch,
                server_elapsed_ms,
                dur_ms
            );
        }
    }
    Ok((server_elapsed_ms, out_json))
}

fn default_parallel_jobs(jobs: Option<usize>) -> usize {
    match jobs {
        Some(j) => j.max(1),
        None => {
            let governor = crate::shm_cache::MemoryBudgetGovernor::detect();
            if governor.is_low_memory_mode() {
                governor.recommended_parallel_workers(512)
            } else {
                std::thread::available_parallelism()
                    .map(|n| n.get())
                    .unwrap_or(4)
            }
            .max(1)
        }
    }
}

/// Execute `turbo-lean check` in-process and return the structured JSON value without printing to stdout.
#[allow(dead_code, clippy::too_many_arguments)]
pub fn run_check_command_value(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    file: PathBuf,
    decl: Option<String>,
    project_dir: PathBuf,
    jobs: Option<usize>,
    parallel_shards: bool,
    remote_http: Option<String>,
) -> Result<serde_json::Value> {
    run_check_command_inner(
        store,
        db_warm_on_open,
        false,
        false,
        file,
        decl,
        project_dir,
        jobs,
        parallel_shards,
        remote_http,
    )
}

/// Evaluate `turbo-lean check` in-process (`emit_stdout: false`) and return its JSON payload.
pub fn evaluate_check_command_value(
    store: &mut TurboStore,
    file: PathBuf,
    decl: Option<String>,
    project_dir: PathBuf,
) -> Result<serde_json::Value> {
    run_check_command_inner(
        store,
        true,
        false,
        false,
        file,
        decl,
        project_dir,
        None,
        true,
        None,
    )
}

type StatelessRemoteInit = (
    PathBuf,
    PathBuf,
    String,
    String,
    String,
    String,
    Vec<String>,
    splitter::SplitResult,
);

fn prepare_stateless_remote_file(file: &Path, project_dir: &Path) -> Option<StatelessRemoteInit> {
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let resolved_file = if file == Path::new(".") {
        return None;
    } else if file.is_relative() && canon_dir.join(file).exists() {
        canon_dir.join(file)
    } else if file.exists() {
        file.to_path_buf()
    } else {
        canon_dir.join(file)
    };
    if resolved_file.is_dir() || !resolved_file.exists() {
        return None;
    }
    let active_src = fs::read_to_string(&resolved_file)
        .ok()
        .filter(|s| s.len() <= 64 * 1024)?;
    let canon_file = resolved_file
        .canonicalize()
        .unwrap_or_else(|_| resolved_file);
    let toolchain = detect_toolchain(&canon_dir);
    let effective_tc = if toolchain.is_empty() || toolchain == "unknown" {
        "leanprover/lean4:v4.35.0".to_string()
    } else {
        toolchain.clone()
    };
    let local_lean_path = resolve_remote_lean_path(&canon_dir, None);
    let dep_hashes = compute_imported_olean_interface_hashes(&active_src, &canon_dir, None);
    let split = splitter::split_lean_source_fast_no_cone(&active_src, &dep_hashes);
    Some((
        canon_dir,
        canon_file,
        active_src,
        toolchain,
        effective_tc,
        local_lean_path,
        dep_hashes,
        split,
    ))
}

fn rollback_inflight(store_opt: &Option<TurboStore>, inflight_tx_open: bool) {
    if inflight_tx_open {
        if let Some(ref st) = store_opt {
            st.rollback_inflight_publish();
        }
    }
}

pub fn try_stateless_remote_check(
    cache_root: &Path,
    json_output: bool,
    file: &Path,
    decl: Option<&str>,
    project_dir: &Path,
    jobs: Option<usize>,
    remote_url: &str,
) -> Result<bool> {
    if let Some(target_decl) = decl {
        return try_stateless_remote_single_decl_check(
            cache_root,
            json_output,
            file,
            target_decl,
            project_dir,
            remote_url,
        );
    }
    let t0 = Instant::now();
    let Some((
        canon_dir,
        canon_file,
        active_src,
        toolchain,
        effective_tc,
        local_lean_path,
        dep_hashes,
        split,
    )) = prepare_stateless_remote_file(file, project_dir)
    else {
        return Ok(false);
    };
    if !split.eligible_for_sharding
        || split.shards.is_empty()
        || !split.hygiene.is_clean_for_certification()
    {
        return Ok(false);
    }
    let uncached_names: HashSet<String> = split
        .shards
        .iter()
        .map(|s| s.decl_name().to_string())
        .collect();
    let pruned_batch_src =
        splitter::build_pruned_imports_shard_source(&active_src, &uncached_names);
    let fast_batch_src = if pruned_batch_src.is_some() || split.shards.len() <= 1 {
        None
    } else {
        resolve_prebuilt_module_import(&canon_dir, &canon_file).and_then(|mod_imp| {
            splitter::build_fast_olean_shard_source_with_split(
                &active_src,
                &split,
                &mod_imp,
                &uncached_names,
            )
        })
    };
    let Some(batch_src) = pruned_batch_src.or(fast_batch_src) else {
        return Ok(false);
    };
    let shard_refs: Vec<&splitter::TheoremShard> = split.shards.iter().collect();
    let attested = confirm_file_decl_identities_with_budget(
        &active_src,
        &shard_refs,
        &canon_dir,
        &canon_file,
        false,
        Some(t0),
    )?;
    let expected_type_pairs: Vec<(String, String)> = split
        .shards
        .iter()
        .zip(&attested)
        .map(|(s, att)| (s.decl_name().to_string(), att.kernel_type_hash.clone()))
        .collect();
    let file_lean_args =
        crate::module_builder::try_resolve_lean_args_for_path(&canon_dir, Some(&canon_file))?;
    let req_items: Vec<pack::CheckShardBatchItem> = split
        .shards
        .iter()
        .zip(&attested)
        .map(|(s, att)| pack::CheckShardBatchItem {
            shard_key: compute_shard_key_with_args(&toolchain, s, &file_lean_args),
            decl_name: s.decl_name().to_string(),
            prefix_env_hash: s.prefix_env_hash.clone(),
            stmt_hash: s.stmt_hash.clone(),
            proof_hash: s.proof_hash.clone(),
            expected_kernel_type_hash: Some(att.kernel_type_hash.clone()),
        })
        .collect();
    let endpoint = format!("{}/check-shards-batch", remote_url.trim_end_matches('/'));
    let req_body = serde_json::to_vec(&pack::CheckShardsBatchRequest {
        items: req_items.clone(),
        coalesced_shard_source: batch_src,
        trust_domain: "trusted".to_string(),
        toolchain: effective_tc,
        lean_path: local_lean_path,
        allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
        lean_args: file_lean_args,
    })?;

    let mut store_opt: Option<TurboStore> = None;
    let mut inflight_tx_open = false;
    let mut publish_items = Vec::new();
    let resp_bytes = match pack::http_request_with_inflight(
        "POST",
        &endpoint,
        "application/json",
        &req_body,
        || {
            if let Ok(st) = TurboStore::open(Some(cache_root)) {
                let now = db::now_unix();
                publish_items.reserve(req_items.len());
                for item in &req_items {
                    if let Ok(r_bytes) = make_attested_shard_receipt_bytes(
                        &item.decl_name,
                        &item.prefix_env_hash,
                        &item.stmt_hash,
                        &item.proof_hash,
                        now,
                        item.expected_kernel_type_hash.as_deref(),
                    ) {
                        publish_items.push((
                            item.shard_key.clone(),
                            item.decl_name.clone(),
                            r_bytes,
                            1i64,
                        ));
                    }
                }
                if publish_items.len() == req_items.len()
                    && st
                        .begin_inflight_publish_theorem_shards(
                            &toolchain,
                            "trusted",
                            &publish_items,
                        )
                        .is_ok()
                {
                    inflight_tx_open = true;
                }
                store_opt = Some(st);
            }
        },
    ) {
        Ok(b) => b,
        Err(_) => {
            rollback_inflight(&store_opt, inflight_tx_open);
            return Ok(false);
        }
    };

    let Ok(resp) = serde_json::from_slice::<pack::CheckShardsBatchResponse>(&resp_bytes) else {
        rollback_inflight(&store_opt, inflight_tx_open);
        return Ok(false);
    };
    if !resp.ok
        || crate::zygote::verify_attested_decl_types(
            &resp.verified_decl_types,
            &expected_type_pairs,
        )
        .is_err()
    {
        rollback_inflight(&store_opt, inflight_tx_open);
        return Ok(false);
    }

    let mut store = match store_opt {
        Some(st) => st,
        None => TurboStore::open(Some(cache_root))?,
    };
    if inflight_tx_open {
        store.commit_inflight_publish()?;
    } else if !publish_items.is_empty() {
        store.batch_publish_theorem_shards(&toolchain, "trusted", &publish_items)?;
    }

    cache_shm_stat_split(&store, &canon_file, &active_src, &split, dep_hashes);

    let dur_ms = t0.elapsed().as_millis() as i64;
    crate::lake_build::recheck_dependents_if_nonlocal(&canon_dir, &canon_file)?;
    let misses = req_items.len();
    let effective_jobs = default_parallel_jobs(jobs).min(misses);
    let out_json = serde_json::json!({
        "status": "file_verified",
        "mode": "remote_coalesced_shards",
        "remote_url": remote_url,
        "remote_cache_hits": resp.cache_hits,
        "remote_verified": resp.verified_count,
        "server_elapsed_ms": resp.elapsed_ms,
        "file": file.display().to_string(),
        "shard_hits": 0usize,
        "shard_misses": misses,
        "parallel_jobs": effective_jobs,
        "lake_env_cache_hit": false,
        "interface_hash": split.interface_hash,
        "elapsed_ms": dur_ms
    });
    if json_output {
        println!("{}", serde_json::to_string_pretty(&out_json)?);
    } else {
        println!(
            "[turbo-lean] VERIFIED {} via remote_coalesced_shards on {} (0 local hits, {} remote hits, {} remote verified, {} ms)",
            file.display(),
            remote_url,
            resp.cache_hits,
            resp.verified_count,
            dur_ms
        );
    }
    Ok(true)
}

pub fn try_stateless_remote_single_decl_check(
    cache_root: &Path,
    json_output: bool,
    file: &Path,
    target_decl: &str,
    project_dir: &Path,
    remote_url: &str,
) -> Result<bool> {
    let t0 = Instant::now();
    let Some((
        canon_dir,
        canon_file,
        active_src,
        toolchain,
        effective_tc,
        local_lean_path,
        dep_hashes,
        split,
    )) = prepare_stateless_remote_file(file, project_dir)
    else {
        return Ok(false);
    };
    let Some(shard_idx) = splitter::find_decl_shard_index(&split.shards, target_decl)? else {
        return Ok(false);
    };
    let shard = &split.shards[shard_idx];
    let target_decl = shard.decl_name();
    let attested = confirm_decl_identity_with_budget(
        &active_src,
        shard,
        &canon_dir,
        &canon_file,
        false,
        Some(t0),
    )?;
    let expected_type_pair = [(
        attested.decl_name.clone(),
        attested.kernel_type_hash.clone(),
    )];
    let file_lean_args =
        crate::module_builder::try_resolve_lean_args_for_path(&canon_dir, Some(&canon_file))?;
    let shard_key = compute_shard_key_with_args(&toolchain, shard, &file_lean_args);
    let mut single_set = HashSet::new();
    single_set.insert(shard.decl_name().to_string());
    let pruned_src = splitter::build_pruned_imports_shard_source(&active_src, &single_set);
    let fast_olean_src = if pruned_src.is_some() || split.shards.len() <= 1 {
        None
    } else {
        resolve_prebuilt_module_import(&canon_dir, &canon_file).and_then(|mod_imp| {
            splitter::build_fast_olean_shard_source_with_split(
                &active_src,
                &split,
                &mod_imp,
                &single_set,
            )
        })
    };
    let Some(cand_src) = pruned_src.as_deref().or(fast_olean_src.as_deref()) else {
        return Ok(false);
    };
    let is_fast = true;
    let endpoint = format!("{}/check-shard", remote_url.trim_end_matches('/'));
    let req_body = serde_json::to_vec(&pack::CheckShardHttpRequest {
        decl: target_decl.to_string(),
        shard_key: shard_key.clone(),
        shard_source: cand_src.to_string(),
        interface_hash: split.interface_hash.clone(),
        prefix_env_hash: shard.prefix_env_hash.clone(),
        stmt_hash: shard.stmt_hash.clone(),
        proof_hash: shard.proof_hash.clone(),
        toolchain: effective_tc,
        lean_path: local_lean_path,
        skip_cas_lock: false,
        allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
        lean_args: file_lean_args,
        expected_kernel_type_hash: Some(attested.kernel_type_hash.clone()),
    })?;

    let mut store_opt: Option<TurboStore> = None;
    let mut inflight_tx_open = false;
    let mut prestaged_receipt: Option<Vec<u8>> = None;
    let resp_bytes = match pack::http_request_with_inflight(
        "POST",
        &endpoint,
        "application/json",
        &req_body,
        || {
            if let Ok(st) = TurboStore::open(Some(cache_root)) {
                if let Ok(r_bytes) = make_attested_shard_receipt_bytes(
                    target_decl,
                    &shard.prefix_env_hash,
                    &shard.stmt_hash,
                    &shard.proof_hash,
                    db::now_unix(),
                    Some(&attested.kernel_type_hash),
                ) {
                    let items = [(
                        shard_key.clone(),
                        target_decl.to_string(),
                        r_bytes.clone(),
                        1,
                    )];
                    if st
                        .begin_inflight_publish_theorem_shards(&toolchain, "trusted", &items)
                        .is_ok()
                    {
                        inflight_tx_open = true;
                    }
                    prestaged_receipt = Some(r_bytes);
                }
                store_opt = Some(st);
            }
        },
    ) {
        Ok(b) => b,
        Err(_) => {
            rollback_inflight(&store_opt, inflight_tx_open);
            return Ok(false);
        }
    };

    let Ok(resp_json) = serde_json::from_slice::<serde_json::Value>(&resp_bytes) else {
        rollback_inflight(&store_opt, inflight_tx_open);
        return Ok(false);
    };
    let remote_status = resp_json
        .get("status")
        .and_then(|v| v.as_str())
        .unwrap_or("unknown")
        .to_string();
    if remote_status != "remote_theorem_verified" && remote_status != "remote_theorem_cache_hit" {
        rollback_inflight(&store_opt, inflight_tx_open);
        return Ok(false);
    }
    let remote_type_ok = resp_json
        .get("kernel_type_hash")
        .and_then(|v| v.as_str())
        .is_some_and(|h| h == attested.kernel_type_hash)
        || resp_json
            .get("decl_types")
            .and_then(|v| {
                serde_json::from_value::<std::collections::BTreeMap<String, String>>(v.clone()).ok()
            })
            .is_some_and(|m| {
                crate::zygote::verify_attested_decl_types(&m, &expected_type_pair).is_ok()
            });
    if !remote_type_ok {
        rollback_inflight(&store_opt, inflight_tx_open);
        return Ok(false);
    }

    let dur_ms = t0.elapsed().as_millis() as i64;
    let server_elapsed_ms = resp_json
        .get("server_elapsed_ms")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);

    let mut store = match store_opt {
        Some(st) => st,
        None => TurboStore::open(Some(cache_root))?,
    };
    if inflight_tx_open {
        store.commit_inflight_publish()?;
    } else {
        let receipt = match prestaged_receipt {
            Some(r) => r,
            None => make_attested_shard_receipt_bytes(
                target_decl,
                &shard.prefix_env_hash,
                &shard.stmt_hash,
                &shard.proof_hash,
                db::now_unix(),
                Some(&attested.kernel_type_hash),
            )?,
        };
        store.batch_publish_theorem_shards(
            &toolchain,
            "trusted",
            &[(
                shard_key.clone(),
                target_decl.to_string(),
                receipt,
                (server_elapsed_ms as i64).max(dur_ms),
            )],
        )?;
    }

    cache_shm_stat_split(&store, &canon_file, &active_src, &split, dep_hashes);
    crate::lake_build::recheck_dependents_if_nonlocal(&canon_dir, &canon_file)?;

    emit_remote_decl_result(
        json_output,
        true,
        &resp_json,
        &remote_status,
        target_decl,
        &shard_key,
        remote_url,
        is_fast,
        &split.interface_hash,
        &shard.prefix_env_hash,
        split.shards.len(),
        dur_ms,
    )?;
    Ok(true)
}

/// Execute `turbo-lean check` on a directory, a single file, or a specific `--decl` theorem.
#[allow(clippy::too_many_arguments)]
pub fn run_check_command(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    json_output: bool,
    file: PathBuf,
    decl: Option<String>,
    project_dir: PathBuf,
    jobs: Option<usize>,
    parallel_shards: bool,
    remote_http: Option<String>,
) -> Result<()> {
    run_check_command_inner(
        store,
        db_warm_on_open,
        json_output,
        true,
        file,
        decl,
        project_dir,
        jobs,
        parallel_shards,
        remote_http,
    )
    .map(|_| ())
}

#[allow(clippy::too_many_arguments)]
fn run_check_command_inner(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    json_output: bool,
    emit_stdout: bool,
    file: PathBuf,
    decl: Option<String>,
    project_dir: PathBuf,
    jobs: Option<usize>,
    parallel_shards: bool,
    remote_http: Option<String>,
) -> Result<serde_json::Value> {
    let _lifecycle = crate::zygote::lifecycle_lock(false)?;
    let t0 = Instant::now();
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.clone());
    let toolchain = detect_toolchain(&canon_dir);
    let resolved_file = if file == Path::new(".") {
        canon_dir.clone()
    } else if file.is_relative() && canon_dir.join(&file).exists() {
        canon_dir.join(&file)
    } else if file.exists() {
        file.clone()
    } else {
        canon_dir.join(&file)
    };

    if resolved_file.is_dir() && decl.is_none() {
        return check_directory(
            store,
            json_output,
            emit_stdout,
            &t0,
            &file,
            &resolved_file,
            &canon_dir,
            &toolchain,
            jobs,
            remote_http.as_deref(),
        );
    }

    let canon_resolved_initial = resolved_file
        .canonicalize()
        .unwrap_or_else(|_| resolved_file.clone());
    if canon_resolved_initial.is_file() {
        crate::lake_build::ensure_project_imports_fresh_for_check(
            &canon_dir,
            std::slice::from_ref(&canon_resolved_initial),
        )?;
    }
    let file_stat_tuple: Option<(i64, i64, i64)> = fs::metadata(&canon_resolved_initial)
        .ok()
        .map(|m| TurboStore::extract_file_stat_tuple(&m));

    let splits_dir = shm_file_splits_dir(store);
    let st_paths_opt = file_stat_tuple.map(|(ms, mn, sz)| {
        let pk = canon_resolved_initial.to_string_lossy();
        let st_hash = compute_single_stat_hash(&pk, ms, mn, sz);
        let st_path = splits_dir.join(format!("st_{}.json", &st_hash[..24]));
        let lock_path = splits_dir.join(format!("st_{}.lock", &st_hash[..24]));
        (st_path, lock_path)
    });

    let disk_spill_dir = store.root.join("disk_spill");
    let read_valid_stat_split = |st_path: &Path| -> Option<ShmCachedFileSplit> {
        crate::shm_cache::read_shm_or_disk_spill(st_path, Some(&disk_spill_dir))
            .and_then(|bytes| serde_json::from_slice::<ShmCachedFileSplit>(&bytes).ok())
            .filter(|c| {
                compute_imported_olean_interface_hashes(&c.split.imports_header, &canon_dir, None)
                    == c.dep_hashes
            })
    };
    let mut stat_cached_entry = st_paths_opt
        .as_ref()
        .and_then(|(st_path, _)| read_valid_stat_split(st_path));

    let mut held_split_lock: Option<crate::shm_cache::FlockGuard> = None;
    if stat_cached_entry.is_none() {
        if let Some((ref st_path, ref lock_path)) = st_paths_opt {
            if let Ok(Some(g)) = crate::shm_cache::acquire_flock(lock_path, true, true) {
                held_split_lock = Some(g);
            } else if let Ok(_sh) = crate::shm_cache::acquire_flock(lock_path, false, false) {
                stat_cached_entry = read_valid_stat_split(st_path);
            }
        }
    }

    let mut known_modified_vs_head = false;
    let (mut src, mut cached_file_blake3, mut split, single_split_hits) = if let Some(c) =
        stat_cached_entry
    {
        known_modified_vs_head = c.known_modified;
        let cb3 = (!c.src_blake3.is_empty()).then_some(c.src_blake3);
        (c.prefix_src, cb3, c.split, 1usize)
    } else if let Some((pref_src, fast_sp, 0)) = file_stat_tuple
        .filter(|(_, _, sz)| *sz > 64 * 1024)
        .and_then(|(_, _, sz)| {
            try_fast_split_single_file_from_path(
                store,
                &canon_dir,
                &canon_resolved_initial,
                sz,
                &toolchain,
            )
        })
    {
        known_modified_vs_head = true;
        if let Some((ref st_path, _)) = st_paths_opt {
            let dep_hashes =
                compute_imported_olean_interface_hashes(&fast_sp.imports_header, &canon_dir, None);
            let entry = ShmCachedFileSplit {
                split_key: String::new(),
                src_blake3: String::new(),
                split: compact_split_for_shm_cache(&fast_sp),
                prefix_src: pref_src.clone(),
                known_modified: true,
                dep_hashes,
            };
            if let Ok(bytes) = serde_json::to_vec(&entry) {
                let _ = crate::shm_cache::atomic_write_shm(st_path, &bytes);
            }
        }
        (pref_src, None, fast_sp, 0usize)
    } else {
        let mut loaded_src = fs::read_to_string(&resolved_file)
            .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
        let dep_hashes = compute_imported_olean_interface_hashes(&loaded_src, &canon_dir, None);
        let mut opt_src_b3: Option<String> = None;
        let (sp, hits) = if loaded_src.len() <= 64 * 1024 {
            let sp = split_lean_source(&loaded_src, &dep_hashes);
            let src_b3 = blake3::hash(loaded_src.as_bytes()).to_hex().to_string();
            if let Some((ref st_path, _)) = st_paths_opt {
                let entry = ShmCachedFileSplit {
                    split_key: format!("file-split:v10:{}", src_b3),
                    src_blake3: src_b3.clone(),
                    split: compact_split_for_shm_cache(&sp),
                    prefix_src: String::new(),
                    known_modified: false,
                    dep_hashes: dep_hashes.clone(),
                };
                if let Ok(bytes) = serde_json::to_vec(&entry) {
                    let _ = crate::shm_cache::atomic_write_shm(st_path, &bytes);
                }
            }
            opt_src_b3 = Some(src_b3);
            (sp, usize::from(db_warm_on_open))
        } else if let Some(fast_res) = try_fast_split_single_file(
            store,
            &canon_dir,
            &canon_resolved_initial,
            &loaded_src,
            &toolchain,
        ) {
            if fast_res.1 == 0 {
                known_modified_vs_head = true;
            }
            if let Some((ref st_path, _)) = st_paths_opt {
                let (src_b3, pref_src) = if fast_res.1 > 0 {
                    (
                        blake3::hash(loaded_src.as_bytes()).to_hex().to_string(),
                        String::new(),
                    )
                } else {
                    (String::new(), loaded_src[..fast_res.2].to_string())
                };
                if !src_b3.is_empty() {
                    opt_src_b3 = Some(src_b3.clone());
                }
                let entry = ShmCachedFileSplit {
                    split_key: if src_b3.is_empty() {
                        String::new()
                    } else {
                        format!("file-split:v10:{}", src_b3)
                    },
                    src_blake3: src_b3,
                    split: compact_split_for_shm_cache(&fast_res.0),
                    prefix_src: pref_src,
                    known_modified: fast_res.1 == 0,
                    dep_hashes: dep_hashes.clone(),
                };
                if let Ok(bytes) = serde_json::to_vec(&entry) {
                    let _ = crate::shm_cache::atomic_write_shm(st_path, &bytes);
                }
            }
            if fast_res.2 > 0 && fast_res.2 < loaded_src.len() {
                loaded_src.truncate(fast_res.2);
            }
            (fast_res.0, fast_res.1)
        } else {
            let src_b3 = blake3::hash(loaded_src.as_bytes()).to_hex().to_string();
            let split_key =
                crate::lake_build::compute_file_split_key_with_deps(&src_b3, &dep_hashes);
            let fk_path = crate::lake_build::shm_file_splits_dir(store)
                .join(format!("fk_{}.json", &split_key[..24]));
            let (sp, hits) = if let Ok(sp) = fs::read(&fk_path).and_then(|b| {
                serde_json::from_slice::<splitter::SplitResult>(&b).map_err(std::io::Error::other)
            }) {
                (sp, 1usize)
            } else {
                let (mut single_parsed, hits) =
                    split_and_audit_cached(store, &[(resolved_file.clone(), loaded_src.clone())])?;
                (
                    single_parsed
                        .pop()
                        .map(|(_, _, sp)| sp)
                        .unwrap_or_else(|| split_lean_source(&loaded_src, &dep_hashes)),
                    hits,
                )
            };
            if let Some((ref st_path, _)) = st_paths_opt {
                let entry = ShmCachedFileSplit {
                    split_key,
                    src_blake3: src_b3.clone(),
                    split: compact_split_for_shm_cache(&sp),
                    prefix_src: String::new(),
                    known_modified: false,
                    dep_hashes: dep_hashes.clone(),
                };
                if let Ok(bytes) = serde_json::to_vec(&entry) {
                    let _ = crate::shm_cache::atomic_write_shm(st_path, &bytes);
                }
            }
            opt_src_b3 = Some(src_b3);
            (sp, hits)
        };
        (loaded_src, opt_src_b3, sp, hits)
    };

    drop(held_split_lock);

    let res = if let Some(target_decl) = decl {
        check_single_decl(
            store,
            db_warm_on_open,
            json_output,
            emit_stdout,
            &t0,
            &file,
            &resolved_file,
            &canon_resolved_initial,
            &canon_dir,
            &toolchain,
            &target_decl,
            src,
            &mut cached_file_blake3,
            &mut split,
            known_modified_vs_head,
            single_split_hits,
            remote_http.as_deref(),
        )?
    } else {
        check_single_file(
            store,
            db_warm_on_open,
            json_output,
            emit_stdout,
            &t0,
            &file,
            &resolved_file,
            &canon_resolved_initial,
            &canon_dir,
            &toolchain,
            &mut src,
            cached_file_blake3.as_deref(),
            &split,
            single_split_hits,
            jobs,
            parallel_shards,
            remote_http.as_deref(),
        )?
    };
    crate::lake_build::recheck_dependents_if_nonlocal(&canon_dir, &resolved_file)?;
    Ok(res)
}

#[allow(clippy::too_many_arguments)]
fn check_directory(
    store: &mut TurboStore,
    json_output: bool,
    emit_stdout: bool,
    t0: &Instant,
    file: &Path,
    resolved_file: &Path,
    canon_dir: &Path,
    toolchain: &str,
    jobs: Option<usize>,
    remote_http: Option<&str>,
) -> Result<serde_json::Value> {
    let dir_files = collect_lean_files(resolved_file);
    crate::lake_build::ensure_project_imports_fresh_for_check(canon_dir, &dir_files)?;
    let mut dir_hasher = blake3::Hasher::new();
    dir_hasher.update(toolchain.as_bytes());

    let dir_pkg_cfg = crate::module_builder::optional_package_config(canon_dir)?;
    let (split_entries, split_cache_hits) =
        load_and_split_files_with_hashes_cached(store, &dir_files)?;
    let mut parsed_files = Vec::with_capacity(split_entries.len());
    let mut all_shard_keys = Vec::new();

    for (lf, src_blake3, src, split) in split_entries {
        let rel = lf.strip_prefix(canon_dir).unwrap_or(&lf);
        dir_hasher.update(rel.to_string_lossy().as_bytes());
        dir_hasher.update(b":");
        dir_hasher.update(split.interface_hash.as_bytes());
        dir_hasher.update(b"\n");

        let file_lean_args = dir_pkg_cfg
            .as_ref()
            .map(|pkg| crate::module_builder::resolve_file_lean_args_in_package(pkg, &lf))
            .unwrap_or_default();
        let mut file_keys = Vec::with_capacity(split.shards.len());
        for s in &split.shards {
            let k = compute_shard_key_with_args(toolchain, s, &file_lean_args);
            all_shard_keys.push(k.clone());
            file_keys.push(k);
        }
        parsed_files.push((lf, src_blake3, src, split, file_keys, file_lean_args));
    }

    let dir_interface_hash = dir_hasher.finalize().to_hex().to_string();
    let cached_map = store.batch_get_theorem_shards(&all_shard_keys, "trusted")?;

    let mut total_hits = 0usize;
    let mut uncached_files = Vec::new();
    let mut all_uncached_hygiene_clean = true;
    for (lf, src_blake3, src, split, file_keys, file_lean_args) in parsed_files {
        let file_hygiene_clean = split.hygiene.is_clean_for_certification();
        let mut file_uncached = Vec::new();
        for (idx, shard) in split.shards.into_iter().enumerate() {
            let k = file_keys[idx].clone();
            if cached_map.contains_key(&k) {
                total_hits += 1;
            } else {
                file_uncached.push((k, shard));
            }
        }
        if !file_uncached.is_empty() {
            if !file_hygiene_clean {
                all_uncached_hygiene_clean = false;
            }
            uncached_files.push((lf, src_blake3, src, file_uncached, file_lean_args));
        }
    }

    let total_misses: usize = uncached_files.iter().map(|(_, _, _, u, _)| u.len()).sum();
    if total_misses == 0 {
        let elapsed_ms = t0.elapsed().as_millis();
        let out_json = serde_json::json!({
            "status": "all_shards_cached",
            "file": file.display().to_string(),
            "files_checked": dir_files.len(),
            "file_split_cache_hits": split_cache_hits,
            "shard_hits": total_hits,
            "shard_misses": 0,
            "interface_hash": dir_interface_hash,
            "elapsed_ms": elapsed_ms
        });
        if emit_stdout {
            if json_output {
                println!("{}", serde_json::to_string_pretty(&out_json)?);
            } else {
                println!(
                    "[turbo-lean] ALL {} THEOREM SHARDS CACHED across {} files in {} ({} ms)",
                    total_hits,
                    dir_files.len(),
                    file.display(),
                    elapsed_ms
                );
            }
        }
        if remote_http.is_none() && !crate::zygote::daemon_disabled() {
            let mut fast_ev = HashMap::new();
            fast_ev.insert(
                "LEAN_PATH".to_string(),
                resolve_remote_lean_path(canon_dir, None),
            );
            pack::warm_local_zygote_daemon_nonblocking(store, &fast_ev);
        }
        return Ok(out_json);
    }

    let effective_jobs = default_parallel_jobs(jobs).min(uncached_files.len());
    let _staging_dir = store.fast_staging_dir();
    let pid = std::process::id();

    let proj_build_verified = remote_http.is_none()
        && all_uncached_hygiene_clean
        && load_verified_project_manifest(canon_dir).is_some_and(|manifest| {
            uncached_files.iter().all(|(lf, sb, _, _, _)| {
                !sb.is_empty()
                    && crate::lake_build::is_file_and_imports_verified_in_manifest(
                        canon_dir, lf, sb, &manifest,
                    )
            })
        });

    if !proj_build_verified {
        for (lf, _sb, src, _, _) in &mut uncached_files {
            if src.is_empty() {
                *src = fs::read_to_string(&*lf).unwrap_or_default();
            }
        }
    }
    let uncached_files: Vec<(
        PathBuf,
        String,
        Vec<(String, splitter::TheoremShard)>,
        Vec<String>,
    )> = uncached_files
        .into_iter()
        .map(|(lf, _sb, src, fu, fa)| (lf, src, fu, fa))
        .collect();

    let mut cross_eligible = Vec::with_capacity(uncached_files.len());
    let mut cross_shared_args: Option<Vec<String>> = None;
    for (lf, src, file_uncached, file_lean_args) in &uncached_files {
        match &cross_shared_args {
            None => cross_shared_args = Some(file_lean_args.clone()),
            Some(prev) if prev != file_lean_args => break,
            Some(_) => {}
        }
        let canon_lf = lf.canonicalize().unwrap_or_else(|_| lf.clone());
        if let Some(mod_imp) = resolve_prebuilt_module_import(canon_dir, &canon_lf) {
            if proj_build_verified {
                cross_eligible.push((mod_imp, src.as_str(), file_uncached));
            } else {
                let uncached_names: HashSet<String> = file_uncached
                    .iter()
                    .map(|(_, sh)| sh.decl_name().to_string())
                    .collect();
                if splitter::can_use_fast_olean_import(src, &uncached_names) {
                    cross_eligible.push((mod_imp, src.as_str(), file_uncached));
                }
            }
        }
    }

    let (env_vars, env_cache_hit) = if proj_build_verified
        && remote_http.is_none()
        && cross_eligible.len() == uncached_files.len()
    {
        (HashMap::new(), true)
    } else {
        resolve_lake_env(store, canon_dir)?
    };
    let lean_bin = resolve_lean_bin(&canon_dir)?;

    let mut cross_verified_items: Option<Vec<(String, String, Vec<u8>, i64)>> = None;
    let mut cross_verify_mode = "cross_file_coalesced_shards";
    let lean_path_str = if proj_build_verified
        && remote_http.is_none()
        && cross_eligible.len() == uncached_files.len()
    {
        String::new()
    } else {
        resolve_remote_lean_path(canon_dir, Some(&env_vars))
    };
    if cross_eligible.len() == uncached_files.len() {
        let cross_args = cross_shared_args.unwrap_or_default();
        let cross_src = if proj_build_verified {
            let mut s = String::new();
            for (mod_imp, _, _) in &cross_eligible {
                s.push_str("import ");
                s.push_str(mod_imp);
                s.push('\n');
            }
            s.push_str("#check Nat\n");
            s
        } else {
            let shard_ref_vecs: Vec<Vec<&splitter::TheoremShard>> = cross_eligible
                .iter()
                .map(|(_, _, fu)| fu.iter().map(|(_, sh)| sh).collect())
                .collect();
            let cross_inputs: Vec<(&str, &str, &[&splitter::TheoremShard])> = cross_eligible
                .iter()
                .enumerate()
                .map(|(i, (m, s, _))| (m.as_str(), *s, shard_ref_vecs[i].as_slice()))
                .collect();
            splitter::build_cross_file_coalesced_shard(&cross_inputs)
        };
        if let Some(remote_url) = remote_http {
            let mut req_items = Vec::with_capacity(total_misses);
            for (_, _, file_uncached, _) in &uncached_files {
                for (k, sh) in file_uncached {
                    req_items.push(pack::CheckShardBatchItem {
                        shard_key: k.clone(),
                        decl_name: sh.decl_name().to_string(),
                        prefix_env_hash: sh.prefix_env_hash.clone(),
                        stmt_hash: sh.stmt_hash.clone(),
                        proof_hash: sh.proof_hash.clone(),
                        expected_kernel_type_hash: None,
                    });
                }
            }
            if let Ok(resp) = pack::offload_check_shards_batch_http(
                store,
                remote_url,
                &req_items,
                &cross_src,
                "trusted",
                toolchain,
                &lean_path_str,
                &cross_args,
            ) {
                if resp.ok {
                    cross_verify_mode = "remote_cross_file_coalesced_shards";
                    cross_verified_items = Some(Vec::new());
                }
            }
        }

        if cross_verified_items.is_none() {
            let cross_t0 = Instant::now();
            let zreq = pack::CheckShardHttpRequest {
                decl: "__batch__".to_string(),
                shard_key: format!("cross_batch_{}", pid),
                shard_source: cross_src.clone(),
                interface_hash: String::new(),
                prefix_env_hash: String::new(),
                stmt_hash: String::new(),
                proof_hash: String::new(),
                toolchain: toolchain.to_string(),
                lean_path: lean_path_str.clone(),
                skip_cas_lock: true,
                allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
                lean_args: cross_args.clone(),
                expected_kernel_type_hash: None,
            };
            let mut cross_ok = proj_build_verified
                || pack::try_local_zygote_check_shard(store, &env_vars, &zreq).is_some();
            if !cross_ok {
                let cross_audit: HashSet<String> = uncached_files
                    .iter()
                    .flat_map(|(_, _, fu, _)| fu.iter().map(|(_, sh)| sh.decl_name().to_string()))
                    .collect();
                let cross_out = crate::zygote::run_audited_lean_shard(
                    store,
                    Path::new(&lean_bin),
                    &env_vars,
                    Some(canon_dir),
                    &cross_src,
                    &cross_audit,
                    &cross_args,
                    Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                )?;
                cross_ok = cross_out.status.success();
            }
            if cross_ok {
                let dur_ms =
                    (cross_t0.elapsed().as_millis() as i64 / (total_misses as i64).max(1)).max(1);
                let now = db::now_unix();
                let mut items = Vec::with_capacity(total_misses);
                for (_, _, file_uncached, _) in &uncached_files {
                    for (k, sh) in file_uncached {
                        let receipt = make_shard_receipt_bytes(
                            sh.decl_name(),
                            &sh.prefix_env_hash,
                            &sh.stmt_hash,
                            &sh.proof_hash,
                            now,
                        )?;
                        items.push((k.clone(), sh.decl_name().to_string(), receipt, dur_ms));
                    }
                }
                cross_verified_items = Some(items);
            }
        }
    }

    let (all_batch_items, dir_verify_mode) = if let Some(items) = cross_verified_items {
        (items, cross_verify_mode)
    } else {
        let local_zygote_url = pack::ensure_local_zygote_daemon(store, &env_vars);
        let store_root = store.root.as_path();
        let next_file_idx = std::sync::atomic::AtomicUsize::new(0);
        type DirBatchItem = (String, String, Vec<u8>, i64);
        let worker_results: Vec<Result<Vec<DirBatchItem>>> = std::thread::scope(|s| {
            let mut handles = Vec::with_capacity(effective_jobs);
            for _w in 0..effective_jobs {
                let next_ref = &next_file_idx;
                let files_ref = &uncached_files;
                let canon_ref = canon_dir;
                let env_ref = &env_vars;
                let lean_bin_ref = &lean_bin;
                let z_url_ref = local_zygote_url.as_deref();
                let tc_ref = toolchain;
                let lp_ref = &lean_path_str;

                handles.push(s.spawn(move || -> Result<Vec<DirBatchItem>> {
                    let worker_store = TurboStore::open(Some(store_root))?;
                    let mut items = Vec::new();
                    loop {
                        let f_idx = next_ref.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        if f_idx >= files_ref.len() {
                            break;
                        }
                        let (ref lf, ref src, ref file_uncached, ref file_lean_args) =
                            files_ref[f_idx];
                        let canon_lf = lf.canonicalize().unwrap_or_else(|_| lf.clone());
                        let uncached_names: HashSet<String> = file_uncached
                            .iter()
                            .map(|(_, sh)| sh.decl_name().to_string())
                            .collect();
                        let f_t0 = Instant::now();

                        let mut batch_ok = false;
                        if let Some(mod_imp) = resolve_prebuilt_module_import(canon_ref, &canon_lf)
                        {
                            if let Some(fast_src) = splitter::build_fast_olean_shard_source(
                                src,
                                &mod_imp,
                                &uncached_names,
                            ) {
                                if let Some(z_url) = z_url_ref {
                                    let zreq = pack::CheckShardHttpRequest {
                                        decl: "__batch__".to_string(),
                                        shard_key: format!("dir_batch_{}_{}", pid, f_idx),
                                        shard_source: fast_src.clone(),
                                        interface_hash: String::new(),
                                        prefix_env_hash: String::new(),
                                        stmt_hash: String::new(),
                                        proof_hash: String::new(),
                                        toolchain: tc_ref.to_string(),
                                        lean_path: lp_ref.clone(),
                                        skip_cas_lock: true,
                                        allowed_axioms: Some(
                                            splitter::extra_allowed_axiom_patterns(),
                                        ),
                                        lean_args: file_lean_args.clone(),
                                        expected_kernel_type_hash: None,
                                    };
                                    if pack::try_zygote_url_check_shard(z_url, &zreq).is_some() {
                                        batch_ok = true;
                                    }
                                }
                                if !batch_ok {
                                    let out = crate::zygote::run_audited_lean_shard(
                                        &worker_store,
                                        Path::new(lean_bin_ref),
                                        env_ref,
                                        Some(canon_ref),
                                        &fast_src,
                                        &uncached_names,
                                        file_lean_args,
                                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                                    )?;
                                    if out.status.success() {
                                        batch_ok = true;
                                    }
                                }
                            }
                        }

                        if !batch_ok {
                            let coal_src =
                                splitter::build_coalesced_shard_source(src, &uncached_names);
                            let out = crate::zygote::run_audited_lean_shard(
                                &worker_store,
                                Path::new(lean_bin_ref),
                                env_ref,
                                Some(canon_ref),
                                &coal_src,
                                &uncached_names,
                                file_lean_args,
                                Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                            )?;
                            if !out.status.success() {
                                let stderr = String::from_utf8_lossy(&out.stderr);
                                let stdout = String::from_utf8_lossy(&out.stdout);
                                anyhow::bail!(
                                    "Directory check failed in {}:\n{}\n{}",
                                    lf.display(),
                                    stdout,
                                    stderr
                                );
                            }
                        }

                        let dur_ms = (f_t0.elapsed().as_millis() as i64
                            / (file_uncached.len() as i64).max(1))
                        .max(1);
                        let now = db::now_unix();
                        for (k, sh) in file_uncached {
                            let receipt = make_shard_receipt_bytes(
                                sh.decl_name(),
                                &sh.prefix_env_hash,
                                &sh.stmt_hash,
                                &sh.proof_hash,
                                now,
                            )?;
                            items.push((k.clone(), sh.decl_name().to_string(), receipt, dur_ms));
                        }
                    }
                    Ok(items)
                }));
            }
            handles
                .into_iter()
                .map(|h| {
                    h.join()
                        .unwrap_or_else(|_| Err(anyhow::anyhow!("Worker thread panicked")))
                })
                .collect()
        });

        let mut items = Vec::with_capacity(total_misses);
        for wr in worker_results {
            items.extend(wr?);
        }
        (items, "directory_coalesced_shards")
    };

    store.batch_publish_theorem_shards(toolchain, "trusted", &all_batch_items)?;

    let elapsed_ms = t0.elapsed().as_millis();
    let out_json = serde_json::json!({
        "status": "file_verified",
        "mode": dir_verify_mode,
        "file": file.display().to_string(),
        "files_checked": dir_files.len(),
        "shard_hits": total_hits,
        "shard_misses": total_misses,
        "parallel_jobs": effective_jobs,
        "lake_env_cache_hit": env_cache_hit,
        "interface_hash": dir_interface_hash,
        "elapsed_ms": elapsed_ms
    });
    if emit_stdout {
        if json_output {
            println!("{}", serde_json::to_string_pretty(&out_json)?);
        } else {
            println!(
                "[turbo-lean] VERIFIED {} files in {} ({} hits, {} misses cached, {} ms)",
                dir_files.len(),
                file.display(),
                total_hits,
                total_misses,
                elapsed_ms
            );
        }
    }
    if remote_http.is_none() && !crate::zygote::daemon_disabled() {
        let ev = if !env_vars.is_empty() {
            env_vars
        } else if canon_dir.join(".lake/build/lib/lean").exists()
            || canon_dir.join(".lake/packages").is_dir()
        {
            let mut fast_ev = HashMap::new();
            fast_ev.insert(
                "LEAN_PATH".to_string(),
                resolve_remote_lean_path(canon_dir, None),
            );
            fast_ev
        } else {
            resolve_lake_env(store, canon_dir)
                .map(|(m, _)| m)
                .unwrap_or_default()
        };
        pack::warm_local_zygote_daemon_nonblocking(store, &ev);
    }
    crate::lake_build::recheck_dependents_if_nonlocal(canon_dir, resolved_file)?;
    Ok(out_json)
}

#[cfg(test)]
pub(crate) fn compute_fission_store_key(
    toolchain: &str,
    prefix_env_hash: &str,
    sub_shard_key: &str,
) -> String {
    compute_fission_store_key_with_args(toolchain, prefix_env_hash, sub_shard_key, &[])
}

pub(crate) fn compute_fission_store_key_with_args(
    toolchain: &str,
    prefix_env_hash: &str,
    sub_shard_key: &str,
    lean_args: &[String],
) -> String {
    let allowed = splitter::allowed_axioms();
    let mut base = if allowed.len() > splitter::STANDARD_AXIOMS.len() {
        let ax_hash = blake3::hash(allowed.join(",").as_bytes()).to_hex();
        format!(
            "fission-v2:{}:{}:{}:ax:{}",
            toolchain,
            prefix_env_hash,
            sub_shard_key,
            &ax_hash.as_str()[..24]
        )
    } else {
        format!(
            "fission-v2:{}:{}:{}",
            toolchain, prefix_env_hash, sub_shard_key
        )
    };
    if let Some(opts_digest) = crate::module_builder::effective_lean_args_digest(lean_args) {
        base.push_str(":opts:");
        base.push_str(&opts_digest);
    }
    base
}

fn extract_decl_source_from_file(active_src: &str, shard: &splitter::TheoremShard) -> String {
    if shard.start_line >= 1 && shard.end_line >= shard.start_line {
        let lines: Vec<&str> = active_src
            .lines()
            .skip(shard.start_line - 1)
            .take(shard.end_line - shard.start_line + 1)
            .collect();
        if !lines.is_empty() {
            return lines.join("\n");
        }
    }
    if !shard.signature_text.is_empty() && !shard.proof_text.is_empty() {
        return format!("{} := {}", shard.signature_text, shard.proof_text);
    }
    String::new()
}

#[allow(clippy::too_many_arguments)]
fn check_single_decl(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    json_output: bool,
    emit_stdout: bool,
    t0: &Instant,
    file: &Path,
    resolved_file: &Path,
    canon_resolved_initial: &Path,
    canon_dir: &Path,
    toolchain: &str,
    target_decl: &str,
    src: String,
    cached_file_blake3: &mut Option<String>,
    split: &mut splitter::SplitResult,
    known_modified_vs_head: bool,
    _single_split_hits: usize,
    remote_http: Option<&str>,
) -> Result<serde_json::Value> {
    let mut active_src = src;
    let mut active_file = resolved_file.to_path_buf();

    if splitter::find_decl_shard_index(&split.shards, target_decl)?.is_none() {
        for mod_name in crate::module_builder::parse_header_imports(&split.imports_header) {
            if mod_name != "Init" {
                let rel_mod = crate::module_builder::module_name_to_rel_slash(&mod_name) + ".lean";
                let sub_path = canon_dir.join(rel_mod);
                let sub_canon = sub_path.canonicalize().unwrap_or_else(|_| sub_path.clone());
                let sub_split_opt = fs::metadata(&sub_canon).ok().and_then(|m| {
                    let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&m);
                    let pk = sub_canon.to_string_lossy();
                    let st_hash = compute_single_stat_hash(&pk, ms, mn, sz);
                    let st_path =
                        shm_file_splits_dir(store).join(format!("st_{}.json", &st_hash[..24]));
                    crate::shm_cache::read_shm_or_disk_spill(
                        &st_path,
                        Some(&store.root.join("disk_spill")),
                    )
                    .and_then(|b| serde_json::from_slice::<ShmCachedFileSplit>(&b).ok())
                    .filter(|c| {
                        compute_imported_olean_interface_hashes(
                            &c.split.imports_header,
                            canon_dir,
                            None,
                        ) == c.dep_hashes
                    })
                    .map(|c| {
                        let cb3 = (!c.src_blake3.is_empty()).then_some(c.src_blake3);
                        (c.prefix_src, cb3, c.split)
                    })
                });
                if let Some((sub_src, sub_cb3, sub_split)) = sub_split_opt {
                    if splitter::find_decl_shard_index(&sub_split.shards, target_decl)?.is_some() {
                        *split = sub_split;
                        *cached_file_blake3 = sub_cb3;
                        active_src = sub_src;
                        active_file = sub_path;
                        break;
                    }
                    continue;
                }
                if let Ok(sub_src) = fs::read_to_string(&sub_path) {
                    let sub_deps =
                        compute_imported_olean_interface_hashes(&sub_src, canon_dir, None);
                    let sub_split = split_lean_source(&sub_src, &sub_deps);
                    let sub_b3 = blake3::hash(sub_src.as_bytes()).to_hex().to_string();
                    if let Ok(m) = fs::metadata(&sub_canon) {
                        let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&m);
                        let pk = sub_canon.to_string_lossy();
                        let st_hash = compute_single_stat_hash(&pk, ms, mn, sz);
                        let st_path =
                            shm_file_splits_dir(store).join(format!("st_{}.json", &st_hash[..24]));
                        let entry = ShmCachedFileSplit {
                            split_key: format!("file-split:v10:{}", sub_b3),
                            src_blake3: sub_b3.clone(),
                            split: compact_split_for_shm_cache(&sub_split),
                            prefix_src: if sub_src.len() <= 64 * 1024 {
                                sub_src.clone()
                            } else {
                                String::new()
                            },
                            known_modified: false,
                            dep_hashes: sub_deps,
                        };
                        if let Ok(bytes) = serde_json::to_vec(&entry) {
                            let _ = crate::shm_cache::atomic_write_shm(&st_path, &bytes);
                        }
                    }
                    if splitter::find_decl_shard_index(&sub_split.shards, target_decl)?.is_some() {
                        *split = sub_split;
                        *cached_file_blake3 = Some(sub_b3);
                        active_src = sub_src;
                        active_file = sub_path;
                        break;
                    }
                }
            }
        }
    }

    let shard_idx =
        splitter::find_decl_shard_index(&split.shards, target_decl)?.with_context(|| {
            format!(
                "Declaration `{}` not found in {} (found {} theorem shards)",
                target_decl,
                file.display(),
                split.shards.len()
            )
        })?;
    if split.shards[shard_idx].signature_text.is_empty()
        || split.shards[shard_idx].proof_text.is_empty()
    {
        let end_line = split.shards[shard_idx].end_line;
        if active_src.is_empty() || active_src.lines().count() < end_line {
            if let Ok(full_src) = fs::read_to_string(&active_file) {
                active_src = full_src;
            }
        }
        let (sig, prf) =
            splitter::extract_shard_stmt_and_proof(&active_src, &split.shards[shard_idx]);
        if split.shards[shard_idx].signature_text.is_empty() {
            split.shards[shard_idx].signature_text = sig;
        }
        if split.shards[shard_idx].proof_text.is_empty() {
            split.shards[shard_idx].proof_text = prf;
        }
    }
    // Every verdict, receipt and cache entry carries the resolved full Lean name.
    let resolved_decl = split.shards[shard_idx].decl_name().to_string();
    let target_decl = resolved_decl.as_str();
    let shard = &split.shards[shard_idx];
    // Stat/split caches are not evidence of the identity in the current source.
    if active_src.is_empty() {
        active_src = fs::read_to_string(&active_file)?;
    }
    let attested = confirm_decl_identity_with_budget(
        &active_src,
        shard,
        canon_dir,
        &active_file,
        false,
        Some(*t0),
    )?;
    let expected_type_pair = [(
        attested.decl_name.clone(),
        attested.kernel_type_hash.clone(),
    )];
    let file_lean_args =
        crate::module_builder::try_resolve_lean_args_for_path(canon_dir, Some(&active_file))?;

    let shard_key = compute_shard_key_with_args(toolchain, shard, &file_lean_args);
    let make_cache_hit_json = |coalesced: bool, elapsed_ms: u128| {
        let cached_consts =
            crate::accelerators::lookup_distilled_constants(target_decl, &shard.signature_text);
        let feats = crate::matryoshka::parse_lean_stmt_features(target_decl, &shard.signature_text);
        let skel = crate::matryoshka::extract_tactic_skeleton(&shard.proof_text);
        let cached_proof_nodes = crate::accelerators::lookup_distilled_proof_term_nodes(
            target_decl,
            &shard.signature_text,
        )
        .unwrap_or_else(|| {
            crate::matryoshka::estimate_decl_proof_term_nodes(
                target_decl,
                &shard.signature_text,
                &shard.proof_text,
            )
        });
        serde_json::json!({
            "status": "theorem_cache_hit",
            "decl": target_decl,
            "coalesced": coalesced,
            "shard_key": &shard_key,
            "interface_hash": &split.interface_hash,
            "prefix_env_hash": &shard.prefix_env_hash,
            "used_constants": cached_consts,
            "stmt_nodes": feats.stmt_nodes,
            "stmt_depth": feats.stmt_depth,
            "num_binders": feats.num_binders,
            "goal_head": feats.goal_head,
            "stmt_consts": feats.stmt_consts,
            "tactic_skeleton": skel,
            "proof_term_nodes": cached_proof_nodes,
            "compact_summary": format!("OK decl={} ms={} stage=cache_hit", target_decl, elapsed_ms),
            "estimated_tokens": 18,
            "elapsed_ms": elapsed_ms
        })
    };

    if let Some(remote_url) = remote_http {
        if db_warm_on_open
            && store.has_attested_decl_receipt(
                &shard_key,
                "trusted",
                target_decl,
                &attested.kernel_type_hash,
            )
        {
            let elapsed_ms = t0.elapsed().as_millis();
            let out_json = make_cache_hit_json(false, elapsed_ms);
            if emit_stdout {
                if json_output {
                    println!("{}", serde_json::to_string_pretty(&out_json)?);
                } else {
                    println!(
                        "[turbo-lean] SHARD CACHE HIT `{}` (coalesced=false, {} ms)",
                        target_decl, elapsed_ms
                    );
                }
            }
            return Ok(out_json);
        }
        if active_src.is_empty() {
            active_src = fs::read_to_string(&active_file)
                .with_context(|| format!("Failed to read {}", active_file.display()))?;
        }
        let canon_file = if active_file == resolved_file {
            canon_resolved_initial.to_path_buf()
        } else {
            active_file
                .canonicalize()
                .unwrap_or_else(|_| active_file.clone())
        };
        let mut single_set = HashSet::new();
        single_set.insert(shard.decl_name().to_string());
        let pruned_src = splitter::build_pruned_imports_shard_source(&active_src, &single_set);
        let fast_olean_src = if split.shards.len() <= 1 {
            None
        } else {
            resolve_prebuilt_module_import(canon_dir, &canon_file).and_then(|mod_imp| {
                splitter::build_fast_olean_shard_source_with_split(
                    &active_src,
                    split,
                    &mod_imp,
                    &single_set,
                )
            })
        };
        let endpoint = format!("{}/check-shard", remote_url.trim_end_matches('/'));
        let cached_env = if db_warm_on_open {
            let env_key = TurboStore::compute_lake_env_key(canon_dir);
            store.get_lake_env(&env_key).ok().flatten()
        } else {
            None
        };
        let local_lean_path = resolve_remote_lean_path(canon_dir, cached_env.as_ref());

        let fast_candidates: Vec<(&str, bool)> = if let Some(ref psrc) = pruned_src {
            if let Some(ref fsrc) = fast_olean_src {
                vec![(psrc.as_str(), true), (fsrc.as_str(), true)]
            } else {
                vec![(psrc.as_str(), true)]
            }
        } else if let Some(ref fsrc) = fast_olean_src {
            vec![(fsrc.as_str(), true)]
        } else {
            vec![]
        };

        let mut resp_json = serde_json::Value::Null;
        let mut remote_status = String::from("unknown");
        let mut fast_olean_used = false;
        let mut last_err: Option<anyhow::Error> = None;
        let mut prestaged_receipt: Option<Vec<u8>> = None;
        let mut inflight_tx_open = false;

        let full_shard_src: String;
        let mut candidates = fast_candidates;
        if candidates.is_empty() {
            full_shard_src = if !shard.shard_source.is_empty() {
                shard.shard_source.clone()
            } else {
                splitter::reconstruct_single_shard_source(&active_src, shard.decl_name())?
                    .unwrap_or_default()
            };
            candidates.push((full_shard_src.as_str(), false));
        }

        for (cand_src, is_fast) in &candidates {
            let is_fast = *is_fast;
            let req_body = serde_json::to_vec(&pack::CheckShardHttpRequest {
                decl: target_decl.to_string(),
                shard_key: shard_key.clone(),
                shard_source: (*cand_src).to_string(),
                interface_hash: split.interface_hash.clone(),
                prefix_env_hash: shard.prefix_env_hash.clone(),
                stmt_hash: shard.stmt_hash.clone(),
                proof_hash: shard.proof_hash.clone(),
                toolchain: toolchain.to_string(),
                lean_path: local_lean_path.clone(),
                skip_cas_lock: false,
                allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
                lean_args: file_lean_args.clone(),
                expected_kernel_type_hash: Some(attested.kernel_type_hash.clone()),
            })?;
            match pack::http_request_with_inflight(
                "POST",
                &endpoint,
                "application/json",
                &req_body,
                || {
                    if db_warm_on_open && !inflight_tx_open {
                        if let Ok(r_bytes) = make_attested_shard_receipt_bytes(
                            target_decl,
                            &shard.prefix_env_hash,
                            &shard.stmt_hash,
                            &shard.proof_hash,
                            db::now_unix(),
                            Some(&attested.kernel_type_hash),
                        ) {
                            let items = [(
                                shard_key.clone(),
                                target_decl.to_string(),
                                r_bytes.clone(),
                                1,
                            )];
                            if store
                                .begin_inflight_publish_theorem_shards(toolchain, "trusted", &items)
                                .is_ok()
                            {
                                inflight_tx_open = true;
                            }
                            prestaged_receipt = Some(r_bytes);
                        }
                    }
                },
            ) {
                Ok(resp_bytes) => {
                    if let Ok(rj) = serde_json::from_slice::<serde_json::Value>(&resp_bytes) {
                        let st = rj
                            .get("status")
                            .and_then(|v| v.as_str())
                            .unwrap_or("unknown")
                            .to_string();
                        if st == "remote_theorem_verified" || st == "remote_theorem_cache_hit" {
                            let remote_type_ok = rj
                                .get("kernel_type_hash")
                                .and_then(|v| v.as_str())
                                .is_some_and(|h| h == attested.kernel_type_hash)
                                || rj
                                    .get("decl_types")
                                    .and_then(|v| {
                                        serde_json::from_value::<
                                            std::collections::BTreeMap<String, String>,
                                        >(v.clone())
                                        .ok()
                                    })
                                    .is_some_and(|m| {
                                        crate::zygote::verify_attested_decl_types(
                                            &m,
                                            &expected_type_pair,
                                        )
                                        .is_ok()
                                    });
                            if remote_type_ok {
                                resp_json = rj;
                                remote_status = st;
                                fast_olean_used = is_fast;
                                last_err = None;
                                break;
                            }
                            last_err = Some(anyhow::anyhow!(
                                "Remote shard check for `{target_decl}` on {endpoint} missed or mismatched `kernel_type_hash`"
                            ));
                        } else {
                            last_err = Some(anyhow::anyhow!(
                                "Remote shard check failed on {}: {}",
                                endpoint,
                                rj
                            ));
                        }
                    }
                }
                Err(e) => {
                    last_err = Some(e);
                }
            }
        }
        if last_err.is_some() && !candidates.iter().any(|(_, is_fast)| !*is_fast) {
            let fallback_src = if !shard.shard_source.is_empty() {
                shard.shard_source.clone()
            } else {
                splitter::reconstruct_single_shard_source(&active_src, shard.decl_name())?
                    .unwrap_or_default()
            };
            let req_body = serde_json::to_vec(&pack::CheckShardHttpRequest {
                decl: target_decl.to_string(),
                shard_key: shard_key.clone(),
                shard_source: fallback_src,
                interface_hash: split.interface_hash.clone(),
                prefix_env_hash: shard.prefix_env_hash.clone(),
                stmt_hash: shard.stmt_hash.clone(),
                proof_hash: shard.proof_hash.clone(),
                toolchain: toolchain.to_string(),
                lean_path: local_lean_path.clone(),
                skip_cas_lock: false,
                allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
                lean_args: file_lean_args.clone(),
                expected_kernel_type_hash: Some(attested.kernel_type_hash.clone()),
            })?;
            if let Ok(resp_bytes) =
                pack::http_request("POST", &endpoint, "application/json", &req_body)
            {
                if let Ok(rj) = serde_json::from_slice::<serde_json::Value>(&resp_bytes) {
                    let st = rj
                        .get("status")
                        .and_then(|v| v.as_str())
                        .unwrap_or("unknown")
                        .to_string();
                    let remote_type_ok = rj
                        .get("kernel_type_hash")
                        .and_then(|v| v.as_str())
                        .is_some_and(|h| h == attested.kernel_type_hash)
                        || rj
                            .get("decl_types")
                            .and_then(|v| {
                                serde_json::from_value::<
                                    std::collections::BTreeMap<String, String>,
                                >(v.clone())
                                .ok()
                            })
                            .is_some_and(|m| {
                                crate::zygote::verify_attested_decl_types(&m, &expected_type_pair)
                                    .is_ok()
                            });
                    if (st == "remote_theorem_verified" || st == "remote_theorem_cache_hit")
                        && remote_type_ok
                    {
                        resp_json = rj;
                        remote_status = st;
                        fast_olean_used = false;
                        last_err = None;
                    }
                }
            }
        }
        if let Some(err) = last_err {
            if inflight_tx_open {
                store.rollback_inflight_publish();
            }
            return Err(err);
        }

        let dur_ms = t0.elapsed().as_millis() as i64;
        let server_elapsed_ms = resp_json
            .get("server_elapsed_ms")
            .and_then(|v| v.as_u64())
            .unwrap_or(0);
        if inflight_tx_open {
            store.commit_inflight_publish()?;
        } else {
            let receipt = match prestaged_receipt {
                Some(r) => r,
                None => make_attested_shard_receipt_bytes(
                    target_decl,
                    &shard.prefix_env_hash,
                    &shard.stmt_hash,
                    &shard.proof_hash,
                    db::now_unix(),
                    Some(&attested.kernel_type_hash),
                )?,
            };
            store.batch_publish_theorem_shards(
                toolchain,
                "trusted",
                &[(
                    shard_key.clone(),
                    target_decl.to_string(),
                    receipt,
                    (server_elapsed_ms as i64).max(dur_ms),
                )],
            )?;
        }

        let (_, out_json) = emit_remote_decl_result(
            json_output,
            emit_stdout,
            &resp_json,
            &remote_status,
            target_decl,
            &shard_key,
            remote_url,
            fast_olean_used,
            &split.interface_hash,
            &shard.prefix_env_hash,
            split.shards.len(),
            dur_ms,
        )?;
        return Ok(out_json);
    }

    let singleflight_outcome =
        match store.acquire_singleflight(&shard_key, toolchain, "theorem_shard", "trusted")? {
            SingleflightOutcome::CacheHit { outputs, coalesced } => {
                if store.outputs_have_attested_decl_receipt(
                    &outputs,
                    target_decl,
                    &attested.kernel_type_hash,
                ) {
                    SingleflightOutcome::CacheHit { outputs, coalesced }
                } else {
                    store.invalidate_action_for_reattestation(&shard_key)?;
                    store.acquire_singleflight(&shard_key, toolchain, "theorem_shard", "trusted")?
                }
            }
            other => other,
        };

    match singleflight_outcome {
        SingleflightOutcome::CacheHit { coalesced, .. } => {
            let elapsed_ms = t0.elapsed().as_millis();
            let out_json = make_cache_hit_json(coalesced, elapsed_ms);
            if emit_stdout {
                if json_output {
                    println!("{}", serde_json::to_string_pretty(&out_json)?);
                } else {
                    println!(
                        "[turbo-lean] SHARD CACHE HIT `{}` (coalesced={}, {} ms)",
                        target_decl, coalesced, elapsed_ms
                    );
                }
            }
            Ok(out_json)
        }
        SingleflightOutcome::Leader(lease) => {
            let same_as_initial = active_file == resolved_file;
            let canon_file = if same_as_initial {
                canon_resolved_initial.to_path_buf()
            } else {
                active_file
                    .canonicalize()
                    .unwrap_or_else(|_| active_file.clone())
            };
            let mut single_set = HashSet::new();
            single_set.insert(shard.decl_name().to_string());

            let proj_build_verified = !(known_modified_vs_head && same_as_initial)
                && split.hygiene.is_clean_for_certification()
                && cached_file_blake3
                    .as_deref()
                    .map(|h| is_file_hash_verified_in_lake_build(canon_dir, &canon_file, h))
                    .unwrap_or_else(|| {
                        if active_src.is_empty() {
                            active_src = fs::read_to_string(&active_file).unwrap_or_default();
                        }
                        is_file_verified_in_lake_build(canon_dir, &canon_file, &active_src)
                    });
            let prebuilt_mod = resolve_prebuilt_module_import(canon_dir, &canon_file);
            let mut verified_via_fast_olean = if proj_build_verified {
                if let (Some(ref mod_imp), Ok(cfg)) = (
                    &prebuilt_mod,
                    crate::module_builder::resolve_project_config(canon_dir),
                ) {
                    let lp = resolve_remote_lean_path(canon_dir, None);
                    crate::zygote::audit_compiled_shard_module_with_zygote(
                        store,
                        &cfg,
                        mod_imp,
                        &lp,
                        &[],
                        &[],
                        &single_set,
                        &expected_type_pair,
                        false,
                    )
                    .is_ok()
                } else {
                    false
                }
            } else {
                false
            };
            let mut verified_via_zygote = verified_via_fast_olean;
            let mut zygote_env_cache_hit = verified_via_fast_olean;
            let mut zygote_import_us = 0u64;
            let mut zygote_elab_us = 0u64;
            let mut heartbeats_used = 0u64;
            let mut proof_term_nodes = 0u64;
            let mut rss_delta_mb = 0i64;
            let mut peak_rss_mb = if verified_via_fast_olean {
                0
            } else {
                crate::zygote::measure_process_rss_mb(std::process::id())
            };
            let mut used_constants: Vec<String> = Vec::new();
            let mut fission_cached_subshards = 0usize;
            let mut fission_verified_subshards = 0usize;
            let mut accelerator_assisted = false;
            let mut winning_accelerator: Option<String> = None;

            let fast_lib_dir = canon_dir.join(".lake/build/lib/lean");
            let has_pkg_lib_dir = canon_dir.join(".lake/packages").is_dir();
            let fast_local_zygote_url = if !verified_via_zygote {
                let mut fast_ev = HashMap::new();
                if fast_lib_dir.exists() || has_pkg_lib_dir {
                    fast_ev.insert(
                        "LEAN_PATH".to_string(),
                        resolve_remote_lean_path(canon_dir, None),
                    );
                }
                pack::ensure_local_zygote_daemon(store, &fast_ev)
            } else {
                None
            };
            let (mut env_vars, mut env_cache_hit, mut lean_bin, local_lean_path) =
                if verified_via_zygote {
                    (
                        HashMap::new(),
                        db_warm_on_open,
                        resolve_lean_bin(canon_dir)?,
                        String::new(),
                    )
                } else if fast_lib_dir.exists()
                    || has_pkg_lib_dir
                    || fast_local_zygote_url.is_some()
                {
                    let lp = resolve_remote_lean_path(canon_dir, None);
                    let mut fast_ev = HashMap::new();
                    fast_ev.insert("LEAN_PATH".to_string(), lp.clone());
                    (fast_ev, db_warm_on_open, resolve_lean_bin(&canon_dir)?, lp)
                } else {
                    let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                    let lb = resolve_lean_bin(&canon_dir)?;
                    let lp = resolve_remote_lean_path(canon_dir, Some(&ev));
                    (ev, ech, lb, lp)
                };

            if !verified_via_zygote && active_src.is_empty() {
                active_src = fs::read_to_string(&active_file)
                    .with_context(|| format!("Failed to read {}", active_file.display()))?;
            }

            let decl_src = if verified_via_zygote {
                String::new()
            } else {
                extract_decl_source_from_file(&active_src, shard)
            };
            let fission_sub_shards: Vec<splitter::FissionSubShard> =
                if !verified_via_zygote && decl_src.contains("have ") {
                    let accel_cfg = crate::accelerators::AcceleratorConfig::load(Some(canon_dir));
                    let cut_fission_enabled = accel_cfg.enabled
                        && !accel_cfg
                            .disabled_builtins
                            .iter()
                            .any(|d| d == "builtin:cut-fission" || d == "cut-fission");
                    if cut_fission_enabled {
                        splitter::fission_theorem_have_blocks(&decl_src, &shard.name)
                    } else {
                        Vec::new()
                    }
                } else {
                    Vec::new()
                };

            // Closed-Loop Incremental `FissionPlan` Replay:
            // When at least 1 prior `have` cut or conclusion sub-shard is already verified in CAS
            // under this exact `(toolchain, prefix_env_hash)`, skip re-elaborating cached sub-shards
            // and verify only the uncached/edited sub-shard(s) via `ZygoteWorker` (`0 sorryAx`).
            if !verified_via_zygote && fission_sub_shards.len() >= 2 {
                let fission_keys: Vec<String> = fission_sub_shards
                    .iter()
                    .map(|s| {
                        compute_fission_store_key_with_args(
                            toolchain,
                            &shard.prefix_env_hash,
                            &s.sub_shard_key,
                            &file_lean_args,
                        )
                    })
                    .collect();
                let cached_subs = store
                    .batch_get_theorem_shards(&fission_keys, "trusted")
                    .unwrap_or_default();
                let fission_cold_enabled = std::env::var("TURBO_LEAN_FISSION_COLD").as_deref()
                    == Ok("1")
                    || crate::shm_cache::MemoryBudgetGovernor::detect().is_low_memory_mode();
                if !cached_subs.is_empty() || fission_cold_enabled {
                    if env_vars.len() <= 1 {
                        let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                        lean_bin = resolve_lean_bin(&canon_dir)?;
                        env_vars = ev;
                        env_cache_hit = ech;
                    }
                    let full_shard_src = if !shard.shard_source.is_empty() {
                        shard.shard_source.clone()
                    } else {
                        splitter::reconstruct_single_shard_source(&active_src, shard.decl_name())?
                            .unwrap_or_default()
                    };
                    let (prefix_src, closing_suffix) = if !decl_src.is_empty() {
                        if let Some(pos) = full_shard_src.rfind(&decl_src) {
                            (
                                full_shard_src[..pos].to_string(),
                                full_shard_src[pos + decl_src.len()..].to_string(),
                            )
                        } else {
                            (String::new(), String::new())
                        }
                    } else {
                        (String::new(), String::new())
                    };
                    let stub_sig = if closing_suffix.trim().is_empty() {
                        format!(
                            "set_option warn.sorry false in\n{} := sorry",
                            shard.signature_text.trim_end()
                        )
                    } else {
                        format!(
                            "set_option warn.sorry false in\n{} := sorry\n{}",
                            shard.signature_text.trim_end(),
                            closing_suffix.trim_start()
                        )
                    };
                    let prefix_type_matches = !shard.signature_text.trim().is_empty()
                        && crate::zygote::probe_stub_decl_types_via_zygote(
                            store,
                            toolchain,
                            &local_lean_path,
                            &env_vars,
                            Path::new(&lean_bin),
                            &prefix_src,
                            &stub_sig,
                            &file_lean_args,
                        )
                        .is_ok_and(|rep| {
                            rep.import_ok
                                && rep.ok
                                && crate::zygote::verify_attested_decl_types(
                                    &rep.decl_types,
                                    &expected_type_pair,
                                )
                                .is_ok()
                        });

                    let mut cached_hit_keys: Vec<String> = Vec::new();
                    let mut uncached_subs: Vec<(&splitter::FissionSubShard, &String, String)> =
                        Vec::new();
                    if prefix_type_matches {
                        for (sub, f_key) in fission_sub_shards.iter().zip(fission_keys.iter()) {
                            if cached_subs.contains_key(f_key) {
                                cached_hit_keys.push(f_key.clone());
                            } else {
                                let sub_decl_full = if closing_suffix.trim().is_empty() {
                                    sub.sub_decl_source.clone()
                                } else {
                                    format!(
                                        "{}\n{}",
                                        sub.sub_decl_source,
                                        closing_suffix.trim_start()
                                    )
                                };
                                uncached_subs.push((sub, f_key, sub_decl_full));
                            }
                        }
                    }

                    if prefix_type_matches && uncached_subs.is_empty() {
                        if !cached_hit_keys.is_empty() {
                            let _ = store.batch_increment_action_hits(&cached_hit_keys);
                        }
                        fission_cached_subshards = cached_hit_keys.len();
                        fission_verified_subshards = 0;
                        verified_via_zygote = true;
                        accelerator_assisted = true;
                        winning_accelerator = Some("builtin:cut-fission".to_string());
                    } else if prefix_type_matches {
                        let batch_t0 = Instant::now();
                        let uncached_decl_texts: Vec<String> = uncached_subs
                            .iter()
                            .map(|(_, _, full_txt)| full_txt.clone())
                            .collect();
                        if let Ok(reply) = crate::zygote::eval_subshards_batch_via_zygote(
                            store,
                            toolchain,
                            &local_lean_path,
                            &env_vars,
                            Path::new(&lean_bin),
                            &prefix_src,
                            &uncached_decl_texts,
                            &file_lean_args,
                        ) {
                            let c_abi_sound = unsafe {
                                crate::splitter::turbo_spec_is_sound_decl_summary(
                                    0,
                                    0,
                                    0,
                                    if reply.ok { 0 } else { 1 },
                                ) != 0
                            };
                            if reply.import_ok && reply.ok && c_abi_sound {
                                let per_sub_dur_ms = ((batch_t0.elapsed().as_millis() as i64)
                                    / (uncached_subs.len() as i64).max(1))
                                .max(1);
                                zygote_env_cache_hit |= reply.env_cache_hit;
                                zygote_import_us += reply.import_us;
                                zygote_elab_us += reply.elab_us;
                                heartbeats_used += reply.heartbeats;
                                proof_term_nodes += reply.proof_term_nodes;
                                rss_delta_mb = rss_delta_mb.max(reply.rss_delta_mb);
                                peak_rss_mb = peak_rss_mb.max(reply.peak_rss_mb);
                                for c in reply.used_constants {
                                    if !used_constants.contains(&c) {
                                        used_constants.push(c);
                                    }
                                }
                                let now_ts = db::now_unix();
                                let mut newly_verified_subshards: Vec<(
                                    String,
                                    String,
                                    Vec<u8>,
                                    i64,
                                )> = Vec::with_capacity(uncached_subs.len());
                                for (sub, f_key, _) in &uncached_subs {
                                    let sub_hash = blake3::hash(sub.sub_decl_source.as_bytes())
                                        .to_hex()
                                        .to_string();
                                    let receipt_bytes = serde_json::to_vec(&serde_json::json!({
                                        "decl": sub.step_label,
                                        "parent_decl": target_decl,
                                        "sub_shard_key": sub.sub_shard_key,
                                        "prefix_env_hash": shard.prefix_env_hash,
                                        "stmt_hash": sub_hash,
                                        "proof_hash": sub_hash,
                                        "verified_at": now_ts,
                                    }))?;
                                    newly_verified_subshards.push((
                                        (*f_key).clone(),
                                        sub.step_label.clone(),
                                        receipt_bytes,
                                        per_sub_dur_ms,
                                    ));
                                }
                                store.batch_put_theorem_shards(
                                    toolchain,
                                    &newly_verified_subshards,
                                )?;
                                if !cached_hit_keys.is_empty() {
                                    let _ = store.batch_increment_action_hits(&cached_hit_keys);
                                }
                                fission_cached_subshards = cached_hit_keys.len();
                                fission_verified_subshards = uncached_subs.len();
                                verified_via_zygote = true;
                                accelerator_assisted = true;
                                winning_accelerator = Some("builtin:cut-fission".to_string());
                            }
                        }
                    }
                }
            }

            let pruned_src = if verified_via_zygote {
                None
            } else {
                splitter::build_pruned_imports_shard_source(&active_src, &single_set)
            };
            let fast_olean_src = if verified_via_zygote {
                None
            } else {
                prebuilt_mod.as_ref().and_then(|mod_imp| {
                    if split.shards.len() > 1 {
                        splitter::build_fast_olean_shard_source_with_split(
                            &active_src,
                            split,
                            mod_imp,
                            &single_set,
                        )
                    } else {
                        None
                    }
                })
            };

            let mut inflight_tx_open = false;
            let mut last_daemon_verify_err: Option<String> = None;
            let reply_json_matches_expected_type = |rj: &serde_json::Value| -> bool {
                rj.get("kernel_type_hash")
                    .and_then(|v| v.as_str())
                    .is_some_and(|h| h == attested.kernel_type_hash)
                    || rj
                        .get("decl_types")
                        .and_then(|v| {
                            serde_json::from_value::<std::collections::BTreeMap<String, String>>(
                                v.clone(),
                            )
                            .ok()
                        })
                        .is_some_and(|m| {
                            crate::zygote::verify_attested_decl_types(&m, &expected_type_pair)
                                .is_ok()
                        })
            };
            let mut try_zygote_src = |src_text: &str,
                                      ev: &HashMap<String, String>,
                                      record_err: bool|
             -> Option<serde_json::Value> {
                let zreq = pack::CheckShardHttpRequest {
                    decl: target_decl.to_string(),
                    shard_key: shard_key.clone(),
                    shard_source: src_text.to_string(),
                    interface_hash: split.interface_hash.clone(),
                    prefix_env_hash: shard.prefix_env_hash.clone(),
                    stmt_hash: shard.stmt_hash.clone(),
                    proof_hash: shard.proof_hash.clone(),
                    toolchain: toolchain.to_string(),
                    lean_path: local_lean_path.clone(),
                    skip_cas_lock: true,
                    allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
                    lean_args: file_lean_args.clone(),
                    expected_kernel_type_hash: Some(attested.kernel_type_hash.clone()),
                };
                if let Some(ref z_url) = fast_local_zygote_url {
                    let res = pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
                        z_url,
                        &zreq,
                        || {
                            if !inflight_tx_open {
                                if let Ok(r_bytes) = make_attested_shard_receipt_bytes(
                                    target_decl,
                                    &shard.prefix_env_hash,
                                    &shard.stmt_hash,
                                    &shard.proof_hash,
                                    db::now_unix(),
                                    Some(&attested.kernel_type_hash),
                                ) {
                                    let single_pub = vec![(
                                        shard_key.clone(),
                                        target_decl.to_string(),
                                        r_bytes,
                                        1i64,
                                    )];
                                    if store
                                        .begin_inflight_publish_theorem_shards(
                                            toolchain,
                                            "trusted",
                                            &single_pub,
                                        )
                                        .is_ok()
                                    {
                                        inflight_tx_open = true;
                                    }
                                }
                            }
                        },
                    );
                    match res {
                        Ok(Some(r)) if reply_json_matches_expected_type(&r) => return Some(r),
                        Ok(Some(_)) => {
                            if record_err {
                                last_daemon_verify_err = Some(format!(
                                    "[TurboLean.KernelGate] kernel declaration type mismatch for `{target_decl}`"
                                ));
                            }
                        }
                        Ok(None) => {}
                        Err(e) => {
                            if record_err {
                                let es = e.to_string();
                                if es.contains("Remote `lean` shard verification failed")
                                    || es.contains("Soundness hygiene violation")
                                    || es.contains("[TurboLean.KernelGate]")
                                {
                                    last_daemon_verify_err = Some(es);
                                }
                            }
                        }
                    }
                    if inflight_tx_open {
                        store.rollback_inflight_publish();
                        store.remove_singleflight_done(&shard_key);
                        inflight_tx_open = false;
                    }
                    return None;
                }
                match pack::try_local_zygote_check_shard_detailed(store, ev, &zreq) {
                    Ok(Some(r)) if reply_json_matches_expected_type(&r) => Some(r),
                    Ok(Some(_)) => {
                        if record_err {
                            last_daemon_verify_err = Some(format!(
                                "[TurboLean.KernelGate] kernel declaration type mismatch for `{target_decl}`"
                            ));
                        }
                        None
                    }
                    Ok(None) => None,
                    Err(e) => {
                        if record_err {
                            let es = e.to_string();
                            if es.contains("Remote `lean` shard verification failed")
                                || es.contains("Soundness hygiene violation")
                                || es.contains("[TurboLean.KernelGate]")
                            {
                                last_daemon_verify_err = Some(es);
                            }
                        }
                        None
                    }
                }
            };

            macro_rules! apply_zygote_json {
                ($zjson:expr) => {{
                    let zj = $zjson;
                    verified_via_zygote = true;
                    zygote_env_cache_hit = zj
                        .get("zygote_env_cache_hit")
                        .and_then(|v| v.as_bool())
                        .unwrap_or(false);
                    zygote_import_us = zj
                        .get("zygote_import_us")
                        .and_then(|v| v.as_u64())
                        .unwrap_or(0);
                    zygote_elab_us = zj
                        .get("zygote_elab_us")
                        .and_then(|v| v.as_u64())
                        .unwrap_or(0);
                    heartbeats_used = zj
                        .get("heartbeats")
                        .or_else(|| zj.get("heartbeats_used"))
                        .and_then(|v| v.as_u64())
                        .unwrap_or(heartbeats_used);
                    proof_term_nodes = zj
                        .get("proof_term_nodes")
                        .and_then(|v| v.as_u64())
                        .unwrap_or(proof_term_nodes);
                    if let Some(rd) = zj.get("rss_delta_mb").and_then(|v| v.as_i64()) {
                        rss_delta_mb = rd;
                    }
                    if let Some(pk) = zj.get("peak_rss_mb").and_then(|v| v.as_u64()) {
                        peak_rss_mb = peak_rss_mb.max(pk);
                    }
                    used_constants = zj
                        .get("used_constants")
                        .and_then(|v| v.as_array())
                        .map(|arr| {
                            arr.iter()
                                .filter_map(|x| x.as_str().map(str::to_string))
                                .collect()
                        })
                        .unwrap_or_default();
                    if proof_term_nodes > 0 {
                        crate::accelerators::record_distilled_proof_term_nodes(
                            canon_dir,
                            target_decl,
                            &shard.signature_text,
                            proof_term_nodes,
                        );
                        if shard.name != target_decl {
                            crate::accelerators::record_distilled_proof_term_nodes(
                                canon_dir,
                                &shard.name,
                                &shard.signature_text,
                                proof_term_nodes,
                            );
                        }
                    } else {
                        proof_term_nodes = crate::accelerators::lookup_distilled_proof_term_nodes(
                            target_decl,
                            &shard.signature_text,
                        )
                        .unwrap_or_else(|| {
                            crate::matryoshka::estimate_decl_proof_term_nodes(
                                target_decl,
                                &shard.signature_text,
                                &shard.proof_text,
                            )
                        });
                    }

                    if !used_constants.is_empty() {
                        crate::accelerators::record_distilled_constants(
                            target_decl,
                            &shard.signature_text,
                            &used_constants,
                        );
                    }
                }};
            }

            macro_rules! apply_zygote_reply {
                ($reply:expr) => {{
                    let rep = $reply;
                    verified_via_zygote = true;
                    zygote_env_cache_hit = rep.env_cache_hit;
                    zygote_import_us = rep.import_us;
                    zygote_elab_us = rep.elab_us;
                    heartbeats_used = rep.heartbeats;
                    proof_term_nodes = rep.proof_term_nodes;
                    rss_delta_mb = rep.rss_delta_mb;
                    peak_rss_mb = peak_rss_mb.max(rep.peak_rss_mb);
                    if !rep.used_constants.is_empty() {
                        crate::accelerators::record_distilled_constants(
                            target_decl,
                            &shard.signature_text,
                            &rep.used_constants,
                        );
                    }
                    if rep.proof_term_nodes > 0 {
                        crate::accelerators::record_distilled_proof_term_nodes(
                            canon_dir,
                            target_decl,
                            &shard.signature_text,
                            rep.proof_term_nodes,
                        );
                    }
                    used_constants = rep.used_constants;
                }};
            }

            if !verified_via_zygote {
                if let Some(ref psrc) = pruned_src {
                    if let Some(zjson) = try_zygote_src(psrc, &env_vars, false) {
                        verified_via_fast_olean = true;
                        apply_zygote_json!(&zjson);
                    }
                }
            }

            if !verified_via_zygote {
                if let Some(ref fsrc) = fast_olean_src {
                    if let Some(zjson) = try_zygote_src(fsrc, &env_vars, false) {
                        verified_via_fast_olean = true;
                        apply_zygote_json!(&zjson);
                    }
                }
            }

            if !verified_via_zygote && env_vars.is_empty() && fast_local_zygote_url.is_none() {
                let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                lean_bin = resolve_lean_bin(&canon_dir)?;
                env_vars = ev;
                env_cache_hit = ech;
            }

            if !verified_via_zygote && !verified_via_fast_olean {
                let full_shard_src = if !shard.shard_source.is_empty() {
                    shard.shard_source.clone()
                } else {
                    splitter::reconstruct_single_shard_source(&active_src, shard.decl_name())?
                        .unwrap_or_default()
                };
                if !verified_via_zygote {
                    if let Some(zjson) = try_zygote_src(&full_shard_src, &env_vars, true) {
                        apply_zygote_json!(&zjson);
                    }
                }
                drop(try_zygote_src);
                if !verified_via_zygote
                    && last_daemon_verify_err.is_none()
                    && !decl_src.is_empty()
                    && !shard.signature_text.is_empty()
                    && !shard.proof_text.is_empty()
                    && !decl_src.contains("sorry")
                    && !decl_src.contains("admit")
                {
                    if let Some(pos) = full_shard_src.rfind(&decl_src) {
                        let prefix_src = full_shard_src[..pos].to_string();
                        let closing_suffix = full_shard_src[pos + decl_src.len()..].to_string();
                        let accel_cfg =
                            crate::accelerators::AcceleratorConfig::load(Some(canon_dir));
                        if accel_cfg.enabled {
                            let registry =
                                crate::accelerators::AcceleratorRegistry::from_config(accel_cfg);
                            let (imports_csv, _) =
                                crate::zygote::split_shard_for_zygote(&full_shard_src);
                            let accel_input = crate::accelerators::AcceleratorInput {
                                decl_name: shard.name.clone(),
                                stmt_src: shard.signature_text.clone(),
                                body_src: shard.proof_text.clone(),
                                imports_csv,
                                available_constants:
                                    crate::accelerators::lookup_distilled_constants(
                                        target_decl,
                                        &shard.signature_text,
                                    ),
                                budget_ms: 25,
                            };
                            let certs = registry.run_all(&accel_input);
                            let mut cand_decls: Vec<String> = Vec::new();
                            let mut cand_accels: Vec<String> = Vec::new();
                            for cert in certs {
                                if let crate::accelerators::AcceleratorCertificate::RewrittenProof {
                                    new_body_src,
                                    accelerator_name,
                                    ..
                                } = cert
                                {
                                    let clean_body = new_body_src
                                        .trim()
                                        .strip_prefix(":=")
                                        .map(str::trim_start)
                                        .unwrap_or_else(|| new_body_src.trim());
                                    let rewritten_decl = if closing_suffix.trim().is_empty() {
                                        format!(
                                            "{} := {}",
                                            shard.signature_text.trim_end(),
                                            clean_body
                                        )
                                    } else {
                                        format!(
                                            "{} := {}\n{}",
                                            shard.signature_text.trim_end(),
                                            clean_body,
                                            closing_suffix.trim_start()
                                        )
                                    };
                                    if !cand_decls.contains(&rewritten_decl) {
                                        cand_decls.push(rewritten_decl);
                                        cand_accels.push(accelerator_name);
                                    }
                                }
                            }
                            if !cand_decls.is_empty() {
                                if env_vars.len() <= 1 {
                                    let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                                    lean_bin = resolve_lean_bin(&canon_dir)?;
                                    env_vars = ev;
                                    env_cache_hit = ech;
                                }
                                let orig_full = if closing_suffix.trim().is_empty() {
                                    decl_src.clone()
                                } else {
                                    format!("{}\n{}", decl_src, closing_suffix.trim_start())
                                };
                                if !cand_decls.contains(&orig_full) {
                                    cand_decls.push(orig_full);
                                    cand_accels.push("original".to_string());
                                }
                                if let Ok(reply) = crate::zygote::eval_candidates_race_via_zygote(
                                    store,
                                    toolchain,
                                    &local_lean_path,
                                    &env_vars,
                                    Path::new(&lean_bin),
                                    &prefix_src,
                                    &cand_decls,
                                    &file_lean_args,
                                ) {
                                    let c_abi_sound = unsafe {
                                        crate::splitter::turbo_spec_is_sound_decl_summary(
                                            0,
                                            0,
                                            0,
                                            if reply.ok { 0 } else { 1 },
                                        ) != 0
                                    };
                                    if reply.import_ok
                                        && reply.ok
                                        && c_abi_sound
                                        && crate::zygote::verify_attested_decl_types(
                                            &reply.decl_types,
                                            &expected_type_pair,
                                        )
                                        .is_ok()
                                    {
                                        if let Some(win_idx) = reply.winning_candidate_idx {
                                            if let Some(acc_name) = cand_accels.get(win_idx) {
                                                accelerator_assisted = true;
                                                winning_accelerator = Some(acc_name.clone());
                                            }
                                        }
                                        apply_zygote_reply!(reply);
                                    } else if reply.import_ok
                                        && !reply.ok
                                        && !reply.errors.is_empty()
                                    {
                                        last_daemon_verify_err = Some(reply.errors.join("\n"));
                                    }
                                }
                            }
                        }
                    }
                }
                if !verified_via_zygote {
                    if let Some(daemon_err) = last_daemon_verify_err.take() {
                        let orig_display = file.display().to_string();
                        let raw_err = daemon_err
                            .replace("<zygote-decl>", &orig_display)
                            .replace("<zygote-shard>", &orig_display);
                        let m_diags = extract_mismatch_diagnostics(&raw_err);
                        let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                        anyhow::bail!(
                            "lean check failed for `{}` in {} (lines {}..={}):\n{}{}",
                            target_decl,
                            file.display(),
                            shard.start_line,
                            shard.end_line,
                            raw_err,
                            m_suffix
                        );
                    }
                    if env_vars.len() <= 1 {
                        let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                        lean_bin = resolve_lean_bin(canon_dir)?;
                        env_vars = ev;
                        env_cache_hit = ech;
                    }
                    if let Ok(reply) = crate::zygote::eval_with_zygote_pool_with_args(
                        store,
                        toolchain,
                        &local_lean_path,
                        &env_vars,
                        Path::new(&lean_bin),
                        &full_shard_src,
                        true,
                        &file_lean_args,
                    ) {
                        let c_abi_sound = unsafe {
                            crate::splitter::turbo_spec_is_sound_decl_summary(
                                0,
                                0,
                                0,
                                if reply.ok { 0 } else { 1 },
                            ) != 0
                        };
                        if reply.import_ok && reply.ok && c_abi_sound {
                            crate::zygote::verify_attested_decl_types(
                                &reply.decl_types,
                                &expected_type_pair,
                            )?;
                            apply_zygote_reply!(reply);
                        } else if reply.import_ok && !reply.ok {
                            let orig_display = file.display().to_string();
                            let raw_err = reply
                                .errors
                                .join("\n")
                                .replace("<zygote-decl>", &orig_display)
                                .replace("<zygote-shard>", &orig_display);
                            let m_diags = extract_mismatch_diagnostics(&raw_err);
                            let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                            anyhow::bail!(
                                "lean check failed for `{}` in {} (lines {}..={}):\n{}{}",
                                target_decl,
                                file.display(),
                                shard.start_line,
                                shard.end_line,
                                raw_err,
                                m_suffix
                            );
                        }
                    }
                }
                if !verified_via_zygote {
                    let out = crate::zygote::run_audited_lean_shard_with_types(
                        store,
                        Path::new(&lean_bin),
                        &env_vars,
                        Some(canon_dir),
                        &full_shard_src,
                        &single_set,
                        &expected_type_pair,
                        &file_lean_args,
                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                    )
                    .context("Failed to execute audited `lean` on theorem shard")?;

                    if !out.status.success() {
                        let orig_display = file.display().to_string();
                        let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
                        let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                        let combined_err = format!("{}\n{}", stdout, stderr);
                        let m_diags = extract_mismatch_diagnostics(&combined_err);
                        let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                        anyhow::bail!(
                            "Shard check failed for `{}` in {} (lines {}..={}):\n{}{}",
                            target_decl,
                            orig_display,
                            shard.start_line,
                            shard.end_line,
                            combined_err,
                            m_suffix
                        );
                    }
                }
            }

            if proof_term_nodes == 0 {
                proof_term_nodes = crate::accelerators::lookup_distilled_proof_term_nodes(
                    target_decl,
                    &shard.signature_text,
                )
                .unwrap_or_else(|| {
                    crate::matryoshka::estimate_decl_proof_term_nodes(
                        target_decl,
                        &shard.signature_text,
                        &shard.proof_text,
                    )
                });
            }

            if !used_constants.is_empty() {
                crate::accelerators::record_distilled_constants(
                    target_decl,
                    &shard.signature_text,
                    &used_constants,
                );
                if shard.name != target_decl {
                    crate::accelerators::record_distilled_constants(
                        &shard.name,
                        &shard.signature_text,
                        &used_constants,
                    );
                }
            } else if shard.proof_text.contains("simp") && !shard.proof_text.contains("simp only") {
                let cached_distilled = crate::accelerators::lookup_distilled_constants(
                    target_decl,
                    &shard.signature_text,
                );
                if !cached_distilled.is_empty() {
                    used_constants = cached_distilled;
                }
            }

            let dur_ms = t0.elapsed().as_millis() as i64;
            let distilled_non_core: Vec<String> = used_constants
                .iter()
                .filter(|c| !crate::accelerators::is_excluded_core_constant(c))
                .cloned()
                .collect();
            let distilled_list = if !distilled_non_core.is_empty() {
                &distilled_non_core
            } else {
                &used_constants
            };
            let has_distilled_hint = !distilled_list.is_empty()
                && shard.proof_text.contains("simp")
                && !shard.proof_text.contains("simp only");
            let compact_summary = if has_distilled_hint {
                format!(
                    "OK decl={} ms={} hbs={} hint=simp only [{}]",
                    target_decl,
                    dur_ms,
                    heartbeats_used,
                    distilled_list.join(", ")
                )
            } else {
                format!(
                    "OK decl={} ms={} hbs={} stage={}",
                    target_decl,
                    dur_ms,
                    heartbeats_used,
                    if verified_via_zygote {
                        "zygote"
                    } else {
                        "lean"
                    }
                )
            };
            let stmt_feats =
                crate::matryoshka::parse_lean_stmt_features(target_decl, &shard.signature_text);
            let tactic_skeleton = crate::matryoshka::extract_tactic_skeleton(&shard.proof_text);
            let emitted_used_constants = used_constants.clone();
            let mut out_json = serde_json::json!({
                "status": "theorem_verified",
                "decl": target_decl,
                "shard_key": shard_key,
                "lake_env_cache_hit": env_cache_hit,
                "fast_olean_import": verified_via_fast_olean,
                "zygote_used": verified_via_zygote,
                "zygote_env_cache_hit": zygote_env_cache_hit,
                "zygote_import_us": zygote_import_us,
                "zygote_elab_us": zygote_elab_us,
                "heartbeats_used": heartbeats_used,
                "proof_term_nodes": proof_term_nodes,
                "used_constants": emitted_used_constants,
                "stmt_nodes": stmt_feats.stmt_nodes,
                "stmt_depth": stmt_feats.stmt_depth,
                "num_binders": stmt_feats.num_binders,
                "goal_head": stmt_feats.goal_head,
                "stmt_consts": stmt_feats.stmt_consts,
                "tactic_skeleton": tactic_skeleton,
                "rss_delta_mb": rss_delta_mb,
                "peak_rss_mb": peak_rss_mb,
                "accelerator_assisted": accelerator_assisted,
                "winning_accelerator": winning_accelerator,
                "fission_cached_subshards": fission_cached_subshards,
                "fission_verified_subshards": fission_verified_subshards,
                "interface_hash": split.interface_hash,
                "prefix_env_hash": shard.prefix_env_hash,
                "total_shards_in_file": split.shards.len(),
                "compact_summary": compact_summary,
                "estimated_tokens": 18,
                "elapsed_ms": dur_ms
            });
            if has_distilled_hint {
                if let Some(obj) = out_json.as_object_mut() {
                    obj.insert(
                        "distilled_simp_hint".to_string(),
                        serde_json::Value::String(format!(
                            "simp only [{}]",
                            distilled_list.join(", ")
                        )),
                    );
                }
            }
            if inflight_tx_open {
                store.commit_inflight_publish_for_lease(&lease.action_key)?;
            } else {
                let receipt = make_attested_shard_receipt_bytes(
                    target_decl,
                    &shard.prefix_env_hash,
                    &shard.stmt_hash,
                    &shard.proof_hash,
                    db::now_unix(),
                    Some(&attested.kernel_type_hash),
                )?;
                store.publish_action_with_blob(
                    &lease,
                    &receipt,
                    "expr_shard",
                    &format!("thm:{}", target_decl),
                    dur_ms,
                    "trusted",
                )?;
            }
            drop(lease);

            if db_warm_on_open
                && fission_sub_shards.len() >= 2
                && fission_cached_subshards == 0
                && fission_verified_subshards == 0
            {
                let now = db::now_unix();
                let per_sub_dur = (dur_ms / (fission_sub_shards.len() as i64).max(1)).max(1);
                let mut seed_items = Vec::with_capacity(fission_sub_shards.len());
                for sub in &fission_sub_shards {
                    let f_key = compute_fission_store_key_with_args(
                        toolchain,
                        &shard.prefix_env_hash,
                        &sub.sub_shard_key,
                        &file_lean_args,
                    );
                    let sub_hash = blake3::hash(sub.sub_decl_source.as_bytes())
                        .to_hex()
                        .to_string();
                    let sub_receipt = serde_json::to_vec(&serde_json::json!({
                        "decl": sub.step_label,
                        "parent_decl": target_decl,
                        "sub_shard_key": sub.sub_shard_key,
                        "prefix_env_hash": shard.prefix_env_hash,
                        "stmt_hash": sub_hash,
                        "proof_hash": sub_hash,
                        "seeded_from_full_decl": true,
                        "verified_at": now,
                    }))?;
                    seed_items.push((f_key, sub.step_label.clone(), sub_receipt, per_sub_dur));
                }
                store.batch_put_theorem_shards(toolchain, &seed_items)?;
            }
            if emit_stdout {
                if json_output {
                    println!("{}", serde_json::to_string_pretty(&out_json)?);
                } else {
                    println!(
                        "[turbo-lean] SHARD VERIFIED `{}` ({}/{} shards in file, env_cache_hit={}, fast_olean={}, zygote={}, interface_hash={}.., {} ms)",
                        target_decl,
                        1,
                        split.shards.len(),
                        env_cache_hit,
                        verified_via_fast_olean,
                        verified_via_zygote,
                        &split.interface_hash[..12],
                        dur_ms
                    );
                }
            }
            if remote_http.is_none()
                && fast_local_zygote_url.is_none()
                && !crate::zygote::daemon_disabled()
            {
                let ev = if !env_vars.is_empty() {
                    env_vars
                } else if fast_lib_dir.exists() || has_pkg_lib_dir {
                    let mut fast_ev = HashMap::new();
                    fast_ev.insert(
                        "LEAN_PATH".to_string(),
                        resolve_remote_lean_path(canon_dir, None),
                    );
                    fast_ev
                } else {
                    resolve_lake_env(store, canon_dir)
                        .map(|(m, _)| m)
                        .unwrap_or_default()
                };
                pack::warm_local_zygote_daemon_nonblocking(store, &ev);
            }
            Ok(out_json)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn check_single_file(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    json_output: bool,
    emit_stdout: bool,
    t0: &Instant,
    file: &Path,
    resolved_file: &Path,
    canon_resolved_initial: &Path,
    canon_dir: &Path,
    toolchain: &str,
    src: &mut String,
    cached_file_blake3: Option<&str>,
    split: &splitter::SplitResult,
    _single_split_hits: usize,
    jobs: Option<usize>,
    _parallel_shards: bool,
    remote_http: Option<&str>,
) -> Result<serde_json::Value> {
    let file_lean_args = crate::module_builder::try_resolve_lean_args_for_path(
        canon_dir,
        Some(canon_resolved_initial),
    )?;
    let file_shard_keys: Vec<String> = split
        .shards
        .iter()
        .map(|shard| compute_shard_key_with_args(toolchain, shard, &file_lean_args))
        .collect();
    let cached_map = if db_warm_on_open {
        store.batch_get_theorem_shards(&file_shard_keys, "trusted")?
    } else {
        HashMap::new()
    };

    let mut hits = 0usize;
    let mut uncached_shards = Vec::new();
    let mut attested_kths: HashMap<String, String> = HashMap::new();
    if split.hygiene.is_clean_for_certification() && !split.shards.is_empty() {
        if src.is_empty() {
            *src = fs::read_to_string(resolved_file)
                .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
        }
        let shard_refs: Vec<&splitter::TheoremShard> = split.shards.iter().collect();
        let attested = confirm_file_decl_identities_with_budget(
            src,
            &shard_refs,
            canon_dir,
            resolved_file,
            false,
            Some(*t0),
        )?;
        for (idx, att) in attested.into_iter().enumerate() {
            attested_kths.insert(file_shard_keys[idx].clone(), att.kernel_type_hash);
        }
    }
    for (idx, shard) in split.shards.iter().enumerate() {
        let shard_key = file_shard_keys[idx].clone();
        let is_attested_hit = cached_map.contains_key(&shard_key)
            && attested_kths.get(&shard_key).is_some_and(|kth| {
                store.has_attested_decl_receipt(&shard_key, "trusted", shard.decl_name(), kth)
            });
        if is_attested_hit {
            hits += 1;
        } else {
            if cached_map.contains_key(&shard_key) {
                store.invalidate_action_for_reattestation(&shard_key)?;
            }
            uncached_shards.push((shard_key, shard));
        }
    }
    let misses = uncached_shards.len();

    if !split.hygiene.is_clean_for_certification() {
        if !crate::zygote::daemon_disabled() {
            if src.is_empty() {
                *src = fs::read_to_string(resolved_file).unwrap_or_default();
            }
            let (imports_csv, _) = crate::zygote::split_shard_for_zygote(src);
            if !imports_csv.is_empty() && imports_csv != "Init" && imports_csv != "__PRELUDE__" {
                let existing_daemon = crate::zygote::has_active_local_zygote_daemon(store);
                if !existing_daemon {
                    if let Ok((ev, _)) = resolve_lake_env(store, canon_dir) {
                        let lb = resolve_lean_bin(&canon_dir)?;
                        let lp = resolve_remote_lean_path(canon_dir, Some(&ev));
                        let _ = crate::zygote::try_local_zygote_eval_with_args(
                            store,
                            &ev,
                            Path::new(&lb),
                            toolchain,
                            &lp,
                            &split.imports_header,
                            None,
                            30_000,
                            &file_lean_args,
                        );
                    }
                }
            }
        }
        anyhow::bail!(
            "Soundness hygiene violation in {}: {}",
            file.display(),
            if split.hygiene.disallowed_items().is_empty() {
                "file contains sorry/admit or forbidden axioms".to_string()
            } else {
                split.hygiene.disallowed_items().join(", ")
            }
        );
    }

    if misses == 0 && !split.shards.is_empty() && split.eligible_for_sharding {
        let elapsed_ms = t0.elapsed().as_millis();
        let out_json = serde_json::json!({
            "status": "all_shards_cached",
            "file": file.display().to_string(),
            "shard_hits": hits,
            "shard_misses": 0,
            "interface_hash": split.interface_hash,
            "elapsed_ms": elapsed_ms
        });
        if emit_stdout {
            if json_output {
                println!("{}", serde_json::to_string_pretty(&out_json)?);
            } else {
                println!(
                    "[turbo-lean] ALL {} THEOREM SHARDS CACHED in {} ({} ms)",
                    hits,
                    file.display(),
                    elapsed_ms
                );
            }
        }
        return Ok(out_json);
    }

    let requested_jobs = default_parallel_jobs(jobs);

    if split.eligible_for_sharding && !uncached_shards.is_empty() {
        if let Some(remote_url) = remote_http {
            if src.is_empty() {
                *src = fs::read_to_string(resolved_file)
                    .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
            }
            let effective_jobs = requested_jobs.min(uncached_shards.len());
            let uncached_names: HashSet<String> = uncached_shards
                .iter()
                .map(|(_, s)| s.decl_name().to_string())
                .collect();
            let fast_lib_lean = canon_dir.join(".lake/build/lib/lean");
            let has_pkg_lib_dir = canon_dir.join(".lake/packages").is_dir();
            let (env_cache_hit, lean_path_str) = if fast_lib_lean.exists() || has_pkg_lib_dir {
                (db_warm_on_open, resolve_remote_lean_path(canon_dir, None))
            } else {
                let cached_env = if db_warm_on_open {
                    let project_key = TurboStore::compute_lake_env_key(canon_dir);
                    store.get_lake_env(&project_key)?
                } else {
                    None
                };
                let hit = cached_env.is_some();
                let lp = resolve_remote_lean_path(canon_dir, cached_env.as_ref());
                (hit, lp)
            };
            let req_items: Vec<pack::CheckShardBatchItem> = uncached_shards
                .iter()
                .map(|(k, s)| pack::CheckShardBatchItem {
                    shard_key: k.clone(),
                    decl_name: s.decl_name().to_string(),
                    prefix_env_hash: s.prefix_env_hash.clone(),
                    stmt_hash: s.stmt_hash.clone(),
                    proof_hash: s.proof_hash.clone(),
                    expected_kernel_type_hash: attested_kths.get(k).cloned(),
                })
                .collect();

            let mut remote_resp = if split.shards.len() <= 1 {
                None
            } else {
                resolve_prebuilt_module_import(canon_dir, canon_resolved_initial)
                    .and_then(|mod_imp| {
                        splitter::build_fast_olean_shard_source_with_split(
                            src,
                            split,
                            &mod_imp,
                            &uncached_names,
                        )
                    })
                    .and_then(|fast_src| {
                        pack::offload_check_shards_batch_http(
                            store,
                            remote_url,
                            &req_items,
                            &fast_src,
                            "trusted",
                            toolchain,
                            &lean_path_str,
                            &file_lean_args,
                        )
                        .ok()
                    })
                    .filter(|r| r.ok)
            };

            if remote_resp.is_none() {
                let coalesced_src = splitter::build_coalesced_shard_source(src, &uncached_names);
                let r = pack::offload_check_shards_batch_http(
                    store,
                    remote_url,
                    &req_items,
                    &coalesced_src,
                    "trusted",
                    toolchain,
                    &lean_path_str,
                    &file_lean_args,
                )?;
                if !r.ok {
                    anyhow::bail!(
                        "Remote batch shard check failed on {}: {}",
                        remote_url,
                        r.error.unwrap_or_else(|| r.stderr)
                    );
                }
                remote_resp = Some(r);
            }

            let resp = remote_resp.unwrap();
            let dur_ms = t0.elapsed().as_millis() as i64;
            let out_json = serde_json::json!({
                "status": "file_verified",
                "mode": "remote_coalesced_shards",
                "remote_url": remote_url,
                "remote_cache_hits": resp.cache_hits,
                "remote_verified": resp.verified_count,
                "server_elapsed_ms": resp.elapsed_ms,
                "file": file.display().to_string(),
                "shard_hits": hits,
                "shard_misses": misses,
                "parallel_jobs": effective_jobs,
                "lake_env_cache_hit": env_cache_hit,
                "interface_hash": split.interface_hash,
                "elapsed_ms": dur_ms
            });
            if emit_stdout {
                if json_output {
                    println!("{}", serde_json::to_string_pretty(&out_json)?);
                } else {
                    println!(
                        "[turbo-lean] VERIFIED {} via remote_coalesced_shards on {} ({} local hits, {} remote hits, {} remote verified, {} ms)",
                        file.display(),
                        remote_url,
                        hits,
                        resp.cache_hits,
                        resp.verified_count,
                        dur_ms
                    );
                }
            }
            return Ok(out_json);
        }
    }

    let use_parallel_shards = split.eligible_for_sharding && !uncached_shards.is_empty();

    let proj_build_verified = split.hygiene.is_clean_for_certification()
        && cached_file_blake3
            .map(|h| is_file_hash_verified_in_lake_build(canon_dir, canon_resolved_initial, h))
            .unwrap_or_else(|| {
                if src.is_empty() {
                    *src = fs::read_to_string(resolved_file).unwrap_or_default();
                }
                is_file_verified_in_lake_build(canon_dir, canon_resolved_initial, src)
            });
    let prebuilt_batch_mod = resolve_prebuilt_module_import(canon_dir, canon_resolved_initial);
    let fast_verified_batch =
        use_parallel_shards && proj_build_verified && prebuilt_batch_mod.is_some();

    let (env_vars, env_cache_hit, lean_bin, local_lean_path) = if fast_verified_batch {
        (
            HashMap::new(),
            db_warm_on_open,
            resolve_lean_bin(canon_dir)?,
            String::new(),
        )
    } else {
        let fast_lib_lean = canon_dir.join(".lake/build/lib/lean");
        let has_pkg_lib_dir = canon_dir.join(".lake/packages").is_dir();
        let has_local_daemon = crate::zygote::has_active_local_zygote_daemon(store);
        if !has_pkg_lib_dir && fast_lib_lean.exists() && has_local_daemon {
            let lp = resolve_remote_lean_path(canon_dir, None);
            let mut fast_ev = HashMap::new();
            fast_ev.insert("LEAN_PATH".to_string(), lp.clone());
            (fast_ev, db_warm_on_open, resolve_lean_bin(&canon_dir)?, lp)
        } else {
            let (ev, ech) = resolve_lake_env(store, canon_dir)?;
            let lb = resolve_lean_bin(&canon_dir)?;
            let lp = if fast_lib_lean.exists() || has_pkg_lib_dir {
                resolve_remote_lean_path(canon_dir, None)
            } else {
                resolve_remote_lean_path(canon_dir, Some(&ev))
            };
            (ev, ech, lb, lp)
        }
    };

    if use_parallel_shards {
        let effective_jobs = requested_jobs.min(uncached_shards.len());
        let uncached_names: HashSet<String> = uncached_shards
            .iter()
            .map(|(_, s)| s.decl_name().to_string())
            .collect();
        let batch_t0 = Instant::now();

        let expected_batch_types: Vec<(String, String)> = uncached_shards
            .iter()
            .filter_map(|(k, s)| {
                attested_kths
                    .get(k)
                    .map(|kth| (s.decl_name().to_string(), kth.clone()))
            })
            .collect();
        let mut batch_succeeded = if fast_verified_batch {
            if let (Some(ref mod_imp), Ok(cfg)) = (
                &prebuilt_batch_mod,
                crate::module_builder::resolve_project_config(canon_dir),
            ) {
                let lp = resolve_remote_lean_path(canon_dir, None);
                let audit_set: HashSet<String> = uncached_shards
                    .iter()
                    .map(|(_, s)| s.decl_name().to_string())
                    .collect();
                crate::zygote::audit_compiled_shard_module_with_zygote(
                    store,
                    &cfg,
                    mod_imp,
                    &lp,
                    &[],
                    &[],
                    &audit_set,
                    &expected_batch_types,
                    false,
                )
                .is_ok()
            } else {
                false
            }
        } else {
            false
        };
        if !batch_succeeded && src.is_empty() {
            *src = fs::read_to_string(resolved_file)
                .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
        }
        let pruned_batch_src = (!batch_succeeded)
            .then(|| splitter::build_pruned_imports_shard_source(src, &uncached_names))
            .flatten();
        let fast_batch_src = (!batch_succeeded)
            .then(|| {
                prebuilt_batch_mod.as_ref().and_then(|mod_imp| {
                    if split.shards.len() > 1 {
                        splitter::build_fast_olean_shard_source_with_split(
                            src,
                            split,
                            mod_imp,
                            &uncached_names,
                        )
                    } else {
                        None
                    }
                })
            })
            .flatten();

        let make_batch_zreq = |cand_src: &str| pack::CheckShardHttpRequest {
            decl: "__coalesced_batch__".to_string(),
            shard_key: uncached_shards[0].0.clone(),
            shard_source: cand_src.to_string(),
            interface_hash: split.interface_hash.clone(),
            prefix_env_hash: String::new(),
            stmt_hash: String::new(),
            proof_hash: String::new(),
            toolchain: toolchain.to_string(),
            lean_path: local_lean_path.clone(),
            skip_cas_lock: true,
            allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
            lean_args: file_lean_args.clone(),
            expected_kernel_type_hash: None,
        };

        let mut last_batch_zygote_err: Option<String> = None;
        for cand_src in [pruned_batch_src.as_deref(), fast_batch_src.as_deref()]
            .into_iter()
            .flatten()
        {
            if !batch_succeeded {
                match pack::try_local_zygote_check_shard_detailed(
                    store,
                    &env_vars,
                    &make_batch_zreq(cand_src),
                ) {
                    Ok(Some(reply)) => {
                        if let Some(dt) = reply.get("decl_types").and_then(|v| v.as_object()) {
                            let pairs: std::collections::BTreeMap<String, String> = dt
                                .iter()
                                .filter_map(|(k, v)| Some((k.clone(), v.as_str()?.to_string())))
                                .collect();
                            if crate::zygote::verify_attested_decl_types(
                                &pairs,
                                &expected_batch_types,
                            )
                            .is_ok()
                            {
                                batch_succeeded = true;
                            }
                        }
                    }
                    Ok(None) => {}
                    Err(e) => {
                        last_batch_zygote_err = Some(e.to_string());
                    }
                }
            }
        }

        if !batch_succeeded {
            let coalesced_src = splitter::build_coalesced_shard_source(src, &uncached_names);
            match pack::try_local_zygote_check_shard_detailed(
                store,
                &env_vars,
                &make_batch_zreq(&coalesced_src),
            ) {
                Ok(Some(reply)) => {
                    let pairs: std::collections::BTreeMap<String, String> = reply
                        .get("decl_types")
                        .and_then(|v| v.as_object())
                        .map(|dt| {
                            dt.iter()
                                .filter_map(|(k, v)| Some((k.clone(), v.as_str()?.to_string())))
                                .collect()
                        })
                        .unwrap_or_default();
                    crate::zygote::verify_attested_decl_types(&pairs, &expected_batch_types)?;
                    batch_succeeded = true;
                }
                Ok(None) => {
                    let batch_out = crate::zygote::run_audited_lean_shard_with_types(
                        store,
                        Path::new(&lean_bin),
                        &env_vars,
                        Some(canon_dir),
                        &coalesced_src,
                        &uncached_names,
                        &expected_batch_types,
                        &file_lean_args,
                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                    )
                    .context("Failed to execute `lean` on coalesced shard batch")?;
                    if batch_out.status.success() {
                        batch_succeeded = true;
                    }
                }
                Err(e) => {
                    last_batch_zygote_err = Some(e.to_string());
                }
            }
        }

        if !batch_succeeded && uncached_shards.len() == 1 {
            if let Some(daemon_err) = last_batch_zygote_err {
                let (_, shard) = uncached_shards[0];
                let orig_display = file.display().to_string();
                let raw_err = daemon_err
                    .replace("<zygote-decl>", &orig_display)
                    .replace("<zygote-shard>", &orig_display);
                let m_diags = extract_mismatch_diagnostics(&raw_err);
                let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                anyhow::bail!(
                    "Check failed for `{}` in {} (lines {}..={}):\n{}{}",
                    shard.name,
                    orig_display,
                    shard.start_line,
                    shard.end_line,
                    raw_err,
                    m_suffix
                );
            }
        }

        let (all_verified, verify_mode) = if batch_succeeded {
            let batch_dur_ms = batch_t0.elapsed().as_millis() as i64;
            let per_shard_ms = (batch_dur_ms / (uncached_shards.len() as i64).max(1)).max(1);
            let verified = uncached_shards
                .iter()
                .map(|(k, s)| (k.clone(), *s, per_shard_ms))
                .collect::<Vec<_>>();
            (verified, "coalesced_shards")
        } else {
            let local_zygote_url = pack::ensure_local_zygote_daemon(store, &env_vars);
            let store_root = store.root.as_path();
            let effective_jobs = if local_zygote_url.is_some() {
                effective_jobs.min(1)
            } else {
                effective_jobs
            };
            let next_idx = std::sync::atomic::AtomicUsize::new(0);
            let abort_flag = std::sync::atomic::AtomicBool::new(false);
            let src_ref: &str = src.as_str();
            let worker_results: Vec<Result<Vec<(String, &splitter::TheoremShard, i64)>>> =
                std::thread::scope(|s| {
                    let mut handles = Vec::with_capacity(effective_jobs);
                    for _worker_id in 0..effective_jobs {
                        let next_idx_ref = &next_idx;
                        let abort_ref = &abort_flag;
                        let uncached_ref = &uncached_shards;
                        let canon_ref = canon_dir;
                        let env_ref = &env_vars;
                        let lean_bin_ref = &lean_bin;
                        let file_display = file.display().to_string();
                        let z_url_ref = local_zygote_url.as_deref();
                        let tc_ref = toolchain;
                        let lp_ref = &local_lean_path;
                        let iface_ref = &split.interface_hash;
                        let args_ref = &file_lean_args;

                        let kth_ref = &attested_kths;

                        handles.push(s.spawn(move || -> Result<Vec<(String, &splitter::TheoremShard, i64)>> {
                            let worker_store = TurboStore::open(Some(store_root))?;
                            let mut verified = Vec::new();
                            loop {
                                if abort_ref.load(std::sync::atomic::Ordering::Relaxed) {
                                    break;
                                }
                                let idx = next_idx_ref.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                                if idx >= uncached_ref.len() {
                                    break;
                                }
                                let (ref shard_key, shard) = uncached_ref[idx];
                                let expected_kth = kth_ref.get(shard_key).cloned();
                                let expected_pair: Vec<(String, String)> = expected_kth
                                    .as_ref()
                                    .map(|k| vec![(shard.decl_name().to_string(), k.clone())])
                                    .unwrap_or_default();
                                let shard_t0 = Instant::now();
                                let shard_src_owned = if shard.shard_source.is_empty() {
                                    let mut single_set = HashSet::with_capacity(1);
                                    single_set.insert(shard.decl_name().to_string());
                                    splitter::build_coalesced_shard_source(src_ref, &single_set)
                                } else {
                                    shard.shard_source.clone()
                                };

                                if let Some(z_url) = z_url_ref {
                                    let zreq = pack::CheckShardHttpRequest {
                                        decl: shard.decl_name().to_string(),
                                        shard_key: shard_key.clone(),
                                        shard_source: shard_src_owned.clone(),
                                        interface_hash: iface_ref.clone(),
                                        prefix_env_hash: shard.prefix_env_hash.clone(),
                                        stmt_hash: shard.stmt_hash.clone(),
                                        proof_hash: shard.proof_hash.clone(),
                                        toolchain: tc_ref.to_string(),
                                        lean_path: lp_ref.clone(),
                                        skip_cas_lock: true,
                                        allowed_axioms: Some(
                                            splitter::extra_allowed_axiom_patterns(),
                                        ),
                                        lean_args: args_ref.clone(),
                                        expected_kernel_type_hash: expected_kth.clone(),
                                    };
                                    match pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
                                        z_url,
                                        &zreq,
                                        || {},
                                    ) {
                                        Ok(Some(_)) => {
                                            let shard_dur_ms = shard_t0.elapsed().as_millis() as i64;
                                            verified.push((shard_key.clone(), shard, shard_dur_ms));
                                            continue;
                                        }
                                        Ok(None) => {}
                                        Err(e) => {
                                            abort_ref.store(true, std::sync::atomic::Ordering::Relaxed);
                                            let raw_err = e
                                                .to_string()
                                                .replace("<zygote-decl>", &file_display)
                                                .replace("<zygote-shard>", &file_display);
                                            let m_diags = extract_mismatch_diagnostics(&raw_err);
                                            let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                                            anyhow::bail!(
                                                "Parallel shard check failed for `{}` in {} (lines {}..={}):\n{}{}",
                                                shard.decl_name(),
                                                file_display,
                                                shard.start_line,
                                                shard.end_line,
                                                raw_err,
                                                m_suffix
                                            );
                                        }
                                    }
                                }

                                let audit_one = HashSet::from([shard.decl_name().to_string()]);
                                let out = crate::zygote::run_audited_lean_shard_with_types(
                                    &worker_store,
                                    Path::new(lean_bin_ref),
                                    env_ref,
                                    Some(canon_ref),
                                    &shard_src_owned,
                                    &audit_one,
                                    &expected_pair,
                                    args_ref,
                                    Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                                )
                                .with_context(|| {
                                    format!("Failed to execute `lean` on shard `{}`", shard.decl_name())
                                })?;

                                if !out.status.success() {
                                    abort_ref.store(true, std::sync::atomic::Ordering::Relaxed);
                                    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
                                    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                                    let combined_err = format!("{}\n{}", stdout, stderr);
                                    let m_diags = extract_mismatch_diagnostics(&combined_err);
                                    let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                                    anyhow::bail!(
                                        "Parallel shard check failed for `{}` in {} (lines {}..={}):\n{}{}",
                                        shard.name,
                                        file_display,
                                        shard.start_line,
                                        shard.end_line,
                                        combined_err,
                                        m_suffix
                                    );
                                }
                                let shard_dur_ms = shard_t0.elapsed().as_millis() as i64;
                                verified.push((shard_key.clone(), shard, shard_dur_ms));
                            }
                            Ok(verified)
                        }));
                    }
                    handles
                        .into_iter()
                        .map(|h| {
                            h.join()
                                .unwrap_or_else(|_| Err(anyhow::anyhow!("Worker thread panicked")))
                        })
                        .collect()
                });

            let mut verified = Vec::with_capacity(uncached_shards.len());
            let mut first_err: Option<anyhow::Error> = None;
            for wr in worker_results {
                match wr {
                    Ok(v) => verified.extend(v),
                    Err(e) => {
                        if first_err.is_none() {
                            first_err = Some(e);
                        }
                    }
                }
            }
            if !verified.is_empty() {
                let now = db::now_unix();
                let mut partial_items = Vec::with_capacity(verified.len());
                for (shard_key, shard, shard_dur_ms) in &verified {
                    if let Ok(receipt) = make_attested_shard_receipt_bytes(
                        shard.decl_name(),
                        &shard.prefix_env_hash,
                        &shard.stmt_hash,
                        &shard.proof_hash,
                        now,
                        attested_kths.get(shard_key).map(String::as_str),
                    ) {
                        partial_items.push((
                            shard_key.clone(),
                            shard.decl_name().to_string(),
                            receipt,
                            *shard_dur_ms,
                        ));
                    }
                }
                let _ = store.batch_publish_theorem_shards(toolchain, "trusted", &partial_items);
            }
            if let Some(e) = first_err {
                return Err(e);
            }
            (verified, "parallel_shards")
        };

        let now = db::now_unix();
        let mut batch_items = Vec::with_capacity(all_verified.len());
        for (shard_key, shard, shard_dur_ms) in all_verified {
            let receipt = make_attested_shard_receipt_bytes(
                shard.decl_name(),
                &shard.prefix_env_hash,
                &shard.stmt_hash,
                &shard.proof_hash,
                now,
                attested_kths.get(&shard_key).map(String::as_str),
            )?;
            batch_items.push((
                shard_key,
                shard.decl_name().to_string(),
                receipt,
                shard_dur_ms,
            ));
        }
        store.batch_publish_theorem_shards(toolchain, "trusted", &batch_items)?;
        let dur_ms = t0.elapsed().as_millis() as i64;
        let out_json = serde_json::json!({
            "status": "file_verified",
            "mode": verify_mode,
            "file": file.display().to_string(),
            "shard_hits": hits,
            "shard_misses": misses,
            "parallel_jobs": effective_jobs,
            "lake_env_cache_hit": env_cache_hit,
            "interface_hash": split.interface_hash,
            "elapsed_ms": dur_ms
        });
        if emit_stdout {
            if json_output {
                println!("{}", serde_json::to_string_pretty(&out_json)?);
            } else {
                println!(
                    "[turbo-lean] VERIFIED {} via {} ({} hits, {} misses cached, interface_hash={}.., {} ms)",
                    file.display(),
                    verify_mode,
                    hits,
                    misses,
                    &split.interface_hash[..12],
                    dur_ms
                );
            }
        }
        if !fast_verified_batch && remote_http.is_none() && !crate::zygote::daemon_disabled() {
            let ev = if env_vars.is_empty() {
                resolve_lake_env(store, canon_dir)
                    .map(|(m, _)| m)
                    .unwrap_or_default()
            } else {
                env_vars
            };
            pack::warm_local_zygote_daemon_nonblocking(store, &ev);
        }
        Ok(out_json)
    } else {
        if src.is_empty() {
            *src = fs::read_to_string(resolved_file)
                .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
        }
        let orig_display = file.display().to_string();
        let mut verified_via_zygote_eval = false;
        let mut eval_stdout_text = String::new();
        let mut eval_messages: Vec<String> = Vec::new();
        let can_use_zygote_eval = !crate::zygote::daemon_disabled()
            && !src.contains("IO.Process.exit")
            && !src.lines().take(20).any(|l| {
                let t = l.split("--").next().unwrap_or(l).trim();
                t == "module" || t.starts_with("module ")
            });
        let whole_expected_types: Vec<(String, String)> = uncached_shards
            .iter()
            .filter_map(|(k, sh)| {
                attested_kths
                    .get(k)
                    .map(|kth| (sh.decl_name().to_string(), kth.clone()))
            })
            .collect();
        if can_use_zygote_eval {
            if let Some(rep) = crate::zygote::try_local_zygote_eval_with_args(
                store,
                &env_vars,
                Path::new(&lean_bin),
                toolchain,
                &local_lean_path,
                src,
                Some(&orig_display),
                0,
                &file_lean_args,
            ) {
                if rep.import_ok && rep.ok && !rep.crashed && !rep.timed_out {
                    if whole_expected_types.is_empty()
                        || crate::zygote::verify_attested_decl_types(
                            &rep.decl_types,
                            &whole_expected_types,
                        )
                        .is_ok()
                    {
                        verified_via_zygote_eval = true;
                        eval_stdout_text = rep.stdout;
                        eval_messages = rep.messages;
                    }
                } else if rep.import_ok && !rep.ok && !rep.crashed && !rep.timed_out {
                    let raw_err = rep
                        .errors
                        .join("\n")
                        .replace("<zygote-eval>", &orig_display)
                        .replace("<zygote-decl>", &orig_display)
                        .replace("<zygote-shard>", &orig_display);
                    let m_diags = extract_mismatch_diagnostics(&raw_err);
                    let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                    anyhow::bail!(
                        "Check failed for {}:\n{}{}",
                        orig_display,
                        raw_err,
                        m_suffix
                    );
                }
            }
        }
        if !verified_via_zygote_eval {
            let whole_audit: HashSet<String> = uncached_shards
                .iter()
                .map(|(_, sh)| sh.decl_name().to_string())
                .collect();
            let whole_expected_types: Vec<(String, String)> = uncached_shards
                .iter()
                .filter_map(|(k, sh)| {
                    attested_kths
                        .get(k)
                        .map(|kth| (sh.decl_name().to_string(), kth.clone()))
                })
                .collect();
            let out = crate::zygote::run_audited_lean_shard_with_types(
                store,
                Path::new(&lean_bin),
                &env_vars,
                Some(canon_dir),
                src,
                &whole_audit,
                &whole_expected_types,
                &file_lean_args,
                Some(crate::zygote::remaining_timeout_ms(None, *t0)),
            )
            .context("Failed to execute `lean`")?;
            if !out.status.success() {
                let stderr = String::from_utf8_lossy(&out.stderr);
                let stdout = String::from_utf8_lossy(&out.stdout);
                anyhow::bail!(
                    "Check failed for {}:\n{}\n{}",
                    file.display(),
                    stdout,
                    stderr
                );
            }
            eval_stdout_text = String::from_utf8_lossy(&out.stdout).to_string();
        }
        if emit_stdout && !json_output {
            if !eval_stdout_text.is_empty() {
                print!("{}", eval_stdout_text);
                if !eval_stdout_text.ends_with('\n') {
                    println!();
                }
            }
            for msg in &eval_messages {
                println!(
                    "{}",
                    msg.replace("<zygote-eval>", &orig_display)
                        .replace("<zygote-decl>", &orig_display)
                        .replace("<zygote-shard>", &orig_display)
                );
            }
        }
        let dur_ms = t0.elapsed().as_millis() as i64;
        if !uncached_shards.is_empty() {
            let now = db::now_unix();
            for (shard_key, shard) in uncached_shards {
                if let SingleflightOutcome::Leader(lease) =
                    store.acquire_singleflight(&shard_key, toolchain, "theorem_shard", "trusted")?
                {
                    let receipt = make_attested_shard_receipt_bytes(
                        shard.decl_name(),
                        &shard.prefix_env_hash,
                        &shard.stmt_hash,
                        &shard.proof_hash,
                        now,
                        attested_kths.get(&shard_key).map(String::as_str),
                    )?;
                    let rel_path = format!("thm:{}", shard.decl_name());
                    store.publish_action_with_blob(
                        &lease,
                        &receipt,
                        "expr_shard",
                        &rel_path,
                        dur_ms,
                        "trusted",
                    )?;
                }
            }
        }
        let out_json = serde_json::json!({
            "status": "file_verified",
            "mode": if verified_via_zygote_eval { "zygote_whole_file" } else { "whole_file" },
            "file": file.display().to_string(),
            "shard_hits": hits,
            "shard_misses": misses,
            "lake_env_cache_hit": env_cache_hit,
            "interface_hash": split.interface_hash,
            "stdout": eval_stdout_text,
            "messages": eval_messages,
            "elapsed_ms": dur_ms
        });
        if emit_stdout {
            if json_output {
                println!("{}", serde_json::to_string_pretty(&out_json)?);
            } else {
                println!(
                    "[turbo-lean] VERIFIED {} ({} hits, {} misses cached, interface_hash={}.., {} ms)",
                    file.display(),
                    hits,
                    misses,
                    &split.interface_hash[..12],
                    dur_ms
                );
            }
        }
        if remote_http.is_none() && !verified_via_zygote_eval && !crate::zygote::daemon_disabled() {
            pack::warm_local_zygote_daemon_nonblocking(store, &env_vars);
        }
        Ok(out_json)
    }
}

impl TurboStore {
    #[allow(dead_code)]
    pub fn has_theorem_shard(&self, shard_key: &str) -> bool {
        self.has_cached_action_readonly(shard_key, "trusted")
            .unwrap_or(false)
    }
    #[allow(dead_code)]
    pub fn put_theorem_shard(
        &mut self,
        toolchain: &str,
        shard_key: &str,
        decl_name: &str,
        receipt_bytes: &[u8],
        duration_ms: i64,
    ) -> Result<()> {
        let items = [(
            shard_key.to_string(),
            decl_name.to_string(),
            receipt_bytes.to_vec(),
            duration_ms.max(1),
        )];
        self.batch_publish_theorem_shards(toolchain, "trusted", &items)
    }
    #[allow(dead_code)]
    pub fn batch_put_theorem_shards(
        &mut self,
        toolchain: &str,
        items: &[(String, String, Vec<u8>, i64)],
    ) -> Result<()> {
        self.batch_publish_theorem_shards(toolchain, "trusted", items)
    }
}

#[allow(dead_code)]
pub fn verify_subshards_out_of_core(
    store: &mut TurboStore,
    toolchain: &str,
    lean_path: &str,
    env_vars: &HashMap<String, String>,
    lean_bin: &Path,
    prefix_source: &str,
    subshards: &[(String, String, String)],
) -> Result<(usize, usize)> {
    let governor = crate::shm_cache::MemoryBudgetGovernor::detect();
    if governor.is_low_memory_mode() {
        let shm_dir = store.fast_staging_dir();
        let disk_spill_dir = store.root.join("disk_spill");
        let _ = crate::shm_cache::spill_shm_to_disk_dir(
            &shm_dir,
            &disk_spill_dir,
            governor.recommended_shm_quota_bytes(),
        );
    }
    let prefix_env_hash = blake3::hash(prefix_source.as_bytes()).to_hex().to_string();
    let (mut disk_cached_hits, mut newly_verified) = (0usize, 0usize);
    for (step_label, sub_shard_key, sub_decl_source) in subshards {
        if store.has_theorem_shard(sub_shard_key) {
            let _ = store.batch_increment_action_hits(std::slice::from_ref(sub_shard_key));
            disk_cached_hits += 1;
            continue;
        }
        let step_t0 = Instant::now();
        let reply = crate::zygote::eval_shard_via_zygote(
            store,
            toolchain,
            lean_path,
            env_vars,
            lean_bin,
            prefix_source,
            sub_decl_source,
            &[],
        )?;
        if !reply.import_ok || !reply.ok {
            anyhow::bail!(
                "Out-of-core sub-shard `{}` ({}) verification failed: {}",
                step_label,
                sub_shard_key,
                reply.errors.join("; ")
            );
        }
        let dur_ms = (step_t0.elapsed().as_millis() as i64).max(1);
        let sub_hash = blake3::hash(sub_decl_source.as_bytes())
            .to_hex()
            .to_string();
        let receipt = serde_json::to_vec(&serde_json::json!({
            "decl": step_label, "sub_shard_key": sub_shard_key, "prefix_env_hash": prefix_env_hash,
            "stmt_hash": sub_hash, "proof_hash": sub_hash, "verified_at": db::now_unix(),
        }))?;
        store.put_theorem_shard(toolchain, sub_shard_key, step_label, &receipt, dur_ms)?;
        newly_verified += 1;
    }
    Ok((disk_cached_hits, newly_verified))
}

fn parse_last_int_literal(s: &str) -> Option<i128> {
    s.split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .filter_map(|raw| {
            let tok = raw.replace('_', "");
            if let Some(h) = tok.strip_prefix("0x").or_else(|| tok.strip_prefix("0X")) {
                i128::from_str_radix(h, 16).ok()
            } else {
                tok.parse::<i128>().ok()
            }
        })
        .last()
}

fn strip_trailing_type_ascription(expr: &str) -> &str {
    let trimmed = expr.trim();
    [
        " : Prop",
        " : Type",
        " : Bool",
        " : Nat",
        " : Int",
        " : UInt64",
    ]
    .into_iter()
    .find_map(|s| trimmed.strip_suffix(s))
    .unwrap_or(trimmed)
    .trim()
}

/// Parse Lean 4 `type mismatch` error messages into structured `mismatch_diagnostics` JSON objects
/// containing `term`, `inferred_type`, `expected_type`, `inferred_rhs`, `expected_rhs`, and `numeric_delta`.
/// This allows LLM agents to immediately compute exact offset shifts (e.g., `+14` on EVM `pc` or stack depths)
/// in a single turn instead of burning 8–10 turns of trial-and-error.
pub fn extract_mismatch_diagnostics(err_text: &str) -> Vec<serde_json::Value> {
    let mut out = Vec::new();
    for chunk in err_text.split("type mismatch").skip(1) {
        let Some((term_part, after_has_type)) = chunk.split_once("has type") else {
            continue;
        };
        let Some((inferred_part, after_expected)) =
            after_has_type.split_once("but is expected to have type")
        else {
            continue;
        };
        let mut expected_lines = Vec::new();
        for line in after_expected.lines().map(str::trim) {
            if (line.is_empty() && !expected_lines.is_empty())
                || line.starts_with("<zygote")
                || line.contains(": error:")
                || line.contains(": warning:")
                || line.starts_with("---")
            {
                break;
            }
            if !line.is_empty() {
                expected_lines.push(line);
            }
        }
        let join_lines = |s: &str| {
            s.lines()
                .map(str::trim)
                .filter(|l| !l.is_empty())
                .collect::<Vec<_>>()
                .join(" ")
        };
        let (term, inferred_type, expected_type) = (
            join_lines(term_part),
            join_lines(inferred_part),
            expected_lines.join(" "),
        );
        if inferred_type.is_empty() || expected_type.is_empty() {
            continue;
        }
        let (inf_clean, exp_clean) = (
            strip_trailing_type_ascription(&inferred_type),
            strip_trailing_type_ascription(&expected_type),
        );
        let inf_rhs = inf_clean
            .rsplit_once('=')
            .map(|(_, r)| r.trim().to_string());
        let exp_rhs = exp_clean
            .rsplit_once('=')
            .map(|(_, r)| r.trim().to_string());
        let numeric_delta = match (&inf_rhs, &exp_rhs) {
            (Some(ir), Some(er)) => parse_last_int_literal(ir)
                .zip(parse_last_int_literal(er))
                .map(|(vi, ve)| ve - vi),
            _ => parse_last_int_literal(inf_clean)
                .zip(parse_last_int_literal(exp_clean))
                .filter(|(vi, ve)| vi != ve)
                .map(|(vi, ve)| ve - vi),
        };
        out.push(serde_json::json!({
            "term": term,
            "inferred_type": inferred_type,
            "expected_type": expected_type,
            "inferred_rhs": inf_rhs,
            "expected_rhs": exp_rhs,
            "numeric_delta": numeric_delta,
        }));
    }
    out
}

pub fn format_mismatch_diagnostics_summary(diags: &[serde_json::Value]) -> String {
    let Some(d0) = diags.first() else {
        return String::new();
    };
    let term = d0.get("term").and_then(|v| v.as_str()).unwrap_or("?");
    let inf = d0
        .get("inferred_rhs")
        .or_else(|| d0.get("inferred_type"))
        .and_then(|v| v.as_str())
        .unwrap_or("?");
    let exp = d0
        .get("expected_rhs")
        .or_else(|| d0.get("expected_type"))
        .and_then(|v| v.as_str())
        .unwrap_or("?");
    let token_saver_line = if let Some(delta) = d0.get("numeric_delta").and_then(|v| v.as_i64()) {
        format!(
            "\n[TOKEN-SAVER FIX HINT] term=`{}` expected_rhs={} inferred_rhs={} numeric_delta={:+}",
            term, exp, inf, delta
        )
    } else {
        format!(
            "\n[TOKEN-SAVER FIX HINT] term=`{}` expected=`{}` inferred=`{}`",
            term, exp, inf
        )
    };
    serde_json::to_string(diags)
        .map(|j| {
            format!(
                "{}\n[turbo-lean mismatch_diagnostics] {}",
                token_saver_line, j
            )
        })
        .unwrap_or(token_saver_line)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lake_build::compute_shard_key;

    #[test]
    fn declaration_identity_rejects_mislabeled_shards_and_unavailable_elaboration() {
        let dir = std::env::temp_dir().join(format!(
            "turbo_identity_guard_{}",
            crate::pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        let file = dir.join("Identity.lean");
        let src = "namespace A\ntheorem same : True := True.intro\nend A\nnamespace B\ntheorem same (n : Nat) : n = n + 1 := by rfl\nend B\n";
        let split = split_lean_source(src, &[]);
        let mut shard = split.shards[1].clone();
        confirm_decl_identity(src, &shard, &dir, &file).unwrap();
        shard.qualified_name = "A.same".into();
        let error = format!(
            "{:#}",
            confirm_decl_identity(src, &shard, &dir, &file).unwrap_err()
        );
        assert!(error.contains("identity unconfirmed"), "{error}");
        assert!(error.contains("B.same"), "{error}");
        let invalid = "namespace B\ndef broken : Nat := noSuchConstant\ntheorem same : True := True.intro\nend B\n";
        let split = split_lean_source(invalid, &[]);
        assert!(confirm_decl_identity(invalid, &split.shards[0], &dir, &file).is_err());
        // The checked source controls the compiler's stdout and exit code: forging the old
        // marker and exiting 0 before any `.olean` exists must not confirm an identity.
        let spoof = "import Lean\nopen Lean Elab Command in\nrun_cmd do\n  let f ← getFileName\n  IO.println s!\"TURBO_IDENTITY_0 A.same {f}\"\n  (IO.Process.exit 0 : IO Unit)\nnamespace A\ntheorem same : True := True.intro\nend A\n";
        // Dynamic namespaces are invisible to the splitter, which labels this `A.same`;
        // Lean declares `B.A.same`.
        let dynamic = "import Lean\nrun_cmd Lean.Elab.Command.elabCommand (← `(namespace $(Lean.mkIdent `B)))\ntheorem A.same (n : Nat) : n = n + 1 := by rfl\n";
        for src in [spoof, dynamic] {
            let split = split_lean_source(src, &[]);
            let shard = &split.shards[0];
            assert_eq!(shard.decl_name(), "A.same");
            let error = format!(
                "{:#}",
                confirm_decl_identity(src, shard, &dir, &file).unwrap_err()
            );
            assert!(error.contains("identity unconfirmed"), "{error}");
            let reason = if src == spoof {
                "produced no `.olean`"
            } else {
                "declares [\"B.A.same\"]"
            };
            assert!(error.contains(reason), "{error}");
        }
        assert!(fs::read_dir(&dir).unwrap().all(|e| !e
            .unwrap()
            .file_name()
            .to_string_lossy()
            .contains("identity")));
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn identity_probe_scratch_never_reuses_existing_entries() {
        let base =
            std::env::temp_dir().join(format!("turbo_scratch_{}", crate::pack::next_tmp_id()));
        fs::create_dir_all(&base).unwrap();
        // A colliding nonce must fail instead of adopting or clearing someone else's dir.
        let taken = base.join("turbo_identity_collide");
        fs::create_dir(&taken).unwrap();
        fs::write(taken.join("keep.lean"), "victim").unwrap();
        assert!(
            PrivateScratchDir::create_with_nonce(&base, "turbo_identity", "collide".into())
                .is_err()
        );
        assert_eq!(
            fs::read_to_string(taken.join("keep.lean")).unwrap(),
            "victim"
        );
        #[cfg(unix)]
        {
            std::os::unix::fs::symlink(&taken, base.join("turbo_identity_link")).unwrap();
            assert!(
                PrivateScratchDir::create_with_nonce(&base, "turbo_identity", "link".into())
                    .is_err()
            );
            std::os::unix::fs::symlink(taken.join("keep.lean"), base.join("probe.lean")).unwrap();
            assert!(create_private_file(&base.join("probe.lean"), b"clobber").is_err());
        }
        // Neither an existing file nor a symlink to one is ever written through.
        assert!(create_private_file(&taken.join("keep.lean"), b"clobber").is_err());
        assert_eq!(
            fs::read_to_string(taken.join("keep.lean")).unwrap(),
            "victim"
        );
        let scratch = PrivateScratchDir::create(&base, "turbo_identity").unwrap();
        let path = scratch.path.clone();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(
                fs::metadata(&path).unwrap().permissions().mode() & 0o777,
                0o700
            );
        }
        create_private_file(&path.join("probe.lean"), b"ok").unwrap();
        scratch.remove().unwrap();
        assert!(!path.exists());
        fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn test_extract_mismatch_diagnostics_parses_rhs_and_numeric_delta() {
        let sample_err = "\
<zygote-decl>:42:4: error: type mismatch
  h_pc_step
has type
  sym_78.pc = 1138 : Prop
but is expected to have type
  sym_78.pc = 1152 : Prop
";
        let diags = extract_mismatch_diagnostics(sample_err);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0]["term"], "h_pc_step");
        assert_eq!(diags[0]["inferred_rhs"], "1138");
        assert_eq!(diags[0]["expected_rhs"], "1152");
        assert_eq!(diags[0]["numeric_delta"], 14);
    }

    #[test]
    fn test_verify_subshards_out_of_core_disk_checkpoint_resume() {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_ooc_subshards_test_{}",
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(&tmp_dir).unwrap();
        let mut store = TurboStore::open(Some(&tmp_dir)).unwrap();
        let toolchain = "leanprover/lean4:v4.35.0";
        let (env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "").unwrap();
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }
        // Worker compilation is fixture setup, before any request deadline starts.
        crate::zygote::ensure_zygote_binary(&store, &lean_bin, &env_vars).unwrap();

        let prefix_src = "namespace OutOfCoreFission\ndef doubleNat (n : Nat) : Nat := n + n\n";
        let step0 = (
            "cut_step_0".to_string(),
            "ooc_subshard_key_step_0".to_string(),
            "theorem cut_step_0 (n : Nat) : doubleNat n = n + n := rfl\n".to_string(),
        );
        let step1 = (
            "cut_step_1".to_string(),
            "ooc_subshard_key_step_1".to_string(),
            "theorem cut_step_1 : doubleNat 3 = 6 := rfl\n".to_string(),
        );
        let step2 = (
            "cut_step_2".to_string(),
            "ooc_subshard_key_step_2".to_string(),
            "theorem cut_step_2 (a : Nat) : doubleNat a + 0 = a + a := by\n  simp [doubleNat]\n"
                .to_string(),
        );

        let (hits1, verified1) = verify_subshards_out_of_core(
            &mut store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            prefix_src,
            &[step0.clone(), step1.clone()],
        )
        .unwrap();
        assert_eq!((hits1, verified1), (0, 2));
        assert!(
            store.has_theorem_shard(&step0.1)
                && store.has_theorem_shard(&step1.1)
                && !store.has_theorem_shard(&step2.1)
        );

        let (hits2, verified2) = verify_subshards_out_of_core(
            &mut store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            prefix_src,
            &[step0, step1, step2.clone()],
        )
        .unwrap();
        assert_eq!((hits2, verified2), (2, 1));
        assert!(store.has_theorem_shard(&step2.1));
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_closed_loop_fission_plan_incremental_edit_skips_unchanged_have_cuts() {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_closed_loop_fission_test_{}",
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let (store_dir, proj_dir) = (tmp_dir.join("store"), tmp_dir.join("proj"));
        fs::create_dir_all(&store_dir).unwrap();
        fs::create_dir_all(&proj_dir).unwrap();

        let toolchain = "leanprover/lean4:v4.35.0";
        fs::write(proj_dir.join("lean-toolchain"), format!("{}\n", toolchain)).unwrap();
        let mut store = TurboStore::open(Some(&store_dir)).unwrap();
        let (env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "").unwrap();
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }
        // Worker compilation is fixture setup, before any request deadline starts.
        crate::zygote::ensure_zygote_binary(&store, &lean_bin, &env_vars).unwrap();

        let lean_file = proj_dir.join("FissionLoopTest.lean");
        let canon_proj = proj_dir.canonicalize().unwrap_or_else(|_| proj_dir.clone());
        let src_v1 = "def stepA (n : Nat) : Nat := n + 1\ndef stepB (n : Nat) : Nat := n + 2\ntheorem multi_step_thm (a b : Nat) : (a + 1) + (b + 2) = a + b + 3 := by\n  have h1 : a + 1 = 1 + a := by\n    omega\n  have h2 : b + 2 = 2 + b := by\n    omega\n  have h3 : (1 + a) + (2 + b) = a + b + 3 := by\n    omega\n  omega\n";
        fs::write(&lean_file, src_v1).unwrap();
        let canon_file = lean_file
            .canonicalize()
            .unwrap_or_else(|_| lean_file.clone());

        let run_decl = |st: &mut TurboStore, src: &str| {
            fs::write(&lean_file, src).unwrap();
            let mut split = split_lean_source(src, &[]);
            let mut cb3 = None;
            let t0 = Instant::now();
            let res = check_single_decl(
                st,
                true,
                false,
                false,
                &t0,
                &lean_file,
                &lean_file,
                &canon_file,
                &canon_proj,
                toolchain,
                "multi_step_thm",
                src.to_string(),
                &mut cb3,
                &mut split,
                true,
                0,
                None,
            );
            (res, split)
        };

        let (res_v1, split_v1) = run_decl(&mut store, src_v1);
        assert_eq!(res_v1.unwrap()["status"], "theorem_verified");
        let shard_v1 = &split_v1.shards[0];
        let subs_v1 = splitter::fission_theorem_have_blocks(
            &extract_decl_source_from_file(src_v1, shard_v1),
            "multi_step_thm",
        );
        assert_eq!(subs_v1.len(), 4);
        for sub in &subs_v1 {
            assert!(store.has_theorem_shard(&compute_fission_store_key(
                toolchain,
                &shard_v1.prefix_env_hash,
                &sub.sub_shard_key
            )));
        }

        let src_v2 = src_v1.replacen(
            "    omega\n  omega\n",
            "    omega\n  rw [h1, h2]\n  exact h3\n",
            1,
        );
        let (res_v2, _) = run_decl(&mut store, &src_v2);
        let res_v2 = res_v2.unwrap();
        assert_eq!(
            (
                res_v2["status"].as_str(),
                res_v2["fission_cached_subshards"].as_i64(),
                res_v2["fission_verified_subshards"].as_i64(),
                res_v2["winning_accelerator"].as_str()
            ),
            (
                Some("theorem_verified"),
                Some(3),
                Some(1),
                Some("builtin:cut-fission")
            )
        );

        let src_v3 = src_v1.replacen(
            "    omega\n  omega\n",
            "    omega\n  exact nonexistent_lemma_xyz\n",
            1,
        );
        assert!(run_decl(&mut store, &src_v3).0.is_err());
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_batch_fission_ipc_verifies_multiple_have_cuts_in_single_roundtrip() {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_batch_fission_ipc_test_{}",
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(&tmp_dir).unwrap();
        let store = TurboStore::open(Some(&tmp_dir)).unwrap();
        let toolchain = "leanprover/lean4:v4.35.0";
        let (env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "").unwrap();
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }
        // Worker compilation is fixture setup, before any request deadline starts.
        crate::zygote::ensure_zygote_binary(&store, &lean_bin, &env_vars).unwrap();

        let prefix_src = "def incNat (n : Nat) : Nat := n + 1\n";
        let thm_decl = "theorem batch_cut_thm (a b : Nat) : incNat a + incNat b = a + b + 2 := by\n  have h1 : incNat a = a + 1 := by\n    rfl\n  have h2 : incNat b = b + 1 := by\n    rfl\n  omega\n";
        let sub_decl_sources: Vec<String> =
            splitter::fission_theorem_have_blocks(thm_decl, "batch_cut_thm")
                .into_iter()
                .map(|s| s.sub_decl_source)
                .collect();
        assert_eq!(sub_decl_sources.len(), 3);

        let reply = crate::zygote::eval_subshards_batch_via_zygote(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            prefix_src,
            &sub_decl_sources,
            &[],
        )
        .unwrap();
        assert!(reply.import_ok && reply.ok && reply.subshards_verified == 3);

        let mut bad_sub_decl_sources = sub_decl_sources;
        bad_sub_decl_sources[1] =
            "theorem _fission_cut_1 (a b : Nat) : incNat b = b + 999 := sorry\n".to_string();
        let bad_reply = crate::zygote::eval_subshards_batch_via_zygote(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            prefix_src,
            &bad_sub_decl_sources,
            &[],
        )
        .unwrap();
        assert!(!bad_reply.ok && bad_reply.subshards_verified == 1);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_race_candidates_single_roundtrip_speculative_tactic_replay() {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_race_candidates_test_{}",
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(&tmp_dir).unwrap();
        let store = TurboStore::open(Some(&tmp_dir)).unwrap();
        let toolchain = "leanprover/lean4:v4.35.0";
        let (env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "").unwrap();
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }
        // Worker compilation is fixture setup, before any request deadline starts.
        crate::zygote::ensure_zygote_binary(&store, &lean_bin, &env_vars).unwrap();

        let candidates: Vec<String> = [
            "theorem race_thm (a b : Nat) : a + b = b + a := rfl\n",
            "theorem race_thm (a b : Nat) : a + b = b + a := sorry\n",
            "theorem race_thm (a b : Nat) : a + b = b + a := by omega\n",
            "theorem race_thm (a b : Nat) : a + b = b + a := by simp [Nat.add_comm]\n",
        ]
        .into_iter()
        .map(String::from)
        .collect();

        let reply = crate::zygote::eval_candidates_race_via_zygote(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            "def stepAdd (n : Nat) : Nat := n + 1\n",
            &candidates,
            &[],
        )
        .unwrap();
        assert!(reply.import_ok && reply.ok && reply.winning_candidate_idx == Some(2));
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_law15_c_abi_routing_and_prng_exports() {
        use crate::cluster::*;

        unsafe {
            assert_eq!(turbo_spec_node_effective_cost(0, 0, 420, 1), 420);
            assert_eq!(
                turbo_spec_node_effective_cost(1500, 3, 400, 2),
                1500 + (4 * 400) / 2
            );
            assert_eq!(turbo_spec_is_remote_eligible(0, 1, 1), 0);
            assert_eq!(turbo_spec_is_remote_eligible(2, 0, 1), 0);
            assert_eq!(turbo_spec_is_remote_eligible(2, 1, 1), 1);
            assert_eq!(turbo_spec_should_switch_route(420, 1800, 1), 0);
            assert_eq!(turbo_spec_should_switch_route(1800, 900, 1), 1);
            assert_eq!(turbo_spec_should_switch_route(1800, 900, 0), 0);
            assert_eq!(turbo_spec_classify_compute_target(1024, 1, 1, 1, 1), 0);
            assert_eq!(turbo_spec_classify_compute_target(65536, 0, 1, 1, 1), 2);
            assert_eq!(turbo_spec_classify_compute_target(65536, 1, 0, 1, 1), 1);
            assert_ne!(turbo_spec_splitmix64(1), turbo_spec_splitmix64(2));
            assert_eq!(turbo_spec_boundary_u256_limb(2, 0), u64::MAX);
            assert_eq!(turbo_spec_gen_u256_limb(2, 42, 0, 0), u64::MAX);
            assert_eq!(turbo_spec_u256_lt(1, 0, 0, 0, 2, 0, 0, 0), 1);
            assert_eq!(turbo_spec_u256_lt(5, 0, 0, 1, 9, 0, 0, 0), 0);
            assert_eq!(turbo_spec_eval_u64_binop(0, 10, 20), 30);
            assert_eq!(turbo_spec_eval_u64_binop(1, 5, 20), 0);
            assert_eq!(turbo_spec_step_verdict_consistent(1, 1), 1);
            assert_eq!(turbo_spec_step_verdict_consistent(1, 0), 0);
        }
    }

    #[test]
    fn test_stage1_qualified_decl_selection_cli_and_stateful() {
        // Unit-test executables live in <profile>/deps; exercise the actual CLI too.
        let mut build = Command::new(env!("CARGO"));
        build
            .arg("build")
            .current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/../.."));
        if !cfg!(debug_assertions) {
            build.arg("--release");
        }
        assert!(build.status().unwrap().success());
        let binary = std::env::current_exe()
            .unwrap()
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("turbo-lean");
        let dir = std::env::temp_dir().join(format!(
            "turbo_stage1_selection_{}",
            crate::pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        let file = dir.join("Selection.lean");
        let good = "namespace A\ntheorem same (n : Nat) : n = n := rfl\nend A\n";
        let bad = "namespace B\ntheorem same (n : Nat) : n = n + 1 := by rfl\nend B\n";
        let indented = format!("{good}{bad}")
            .lines()
            .map(|line| format!("  {line}\n"))
            .collect::<String>();
        let quoted = format!("def message := \"\nnamespace Literal\ntheorem same (n : Nat) : n = n + 1 := by rfl\nend Literal\n\"\n{good}{bad}");
        for (order, src) in [
            format!("{good}{bad}"),
            format!("{bad}{good}"),
            indented,
            quoted,
            "namespace B\ndef message : String := \"\nend B\nnamespace A\n\"\ntheorem same (n : Nat) : n = n + 1 := by rfl\nend B\n".to_string() + good,
        ]
        .iter()
        .enumerate()
        {
            fs::write(&file, src).unwrap();
            let cache = dir.join(format!("cache{order}"));
            let mut store = TurboStore::open(Some(&dir.join(format!("stateful{order}")))).unwrap();
            for target in ["A.same", "same", "B.same", "Other.A.same", "Literal.same"] {
                let stateful = crate::gpu_fastcheck::evaluate_agent_step_value(
                    &mut store,
                    &file,
                    Some(target),
                    Some(&dir),
                    false,
                    false,
                );
                match target {
                    "same" => assert!(stateful
                        .unwrap_err()
                        .to_string()
                        .contains("Ambiguous declaration")),
                    "Other.A.same" | "Literal.same" => assert!(stateful.is_err()),
                    _ => {
                        let value = stateful.unwrap();
                        assert_eq!(value["decl"], target);
                        assert_eq!(
                            value["status"],
                            if target == "A.same" {
                                "theorem_verified"
                            } else {
                                "counterexample_rejected"
                            }
                        );
                    }
                }
                for command in ["agent-step", "fast-check"] {
                    let mut cli = Command::new(&binary);
                    cli.current_dir(&dir)
                        .arg("--cache-dir")
                        .arg(&cache)
                        .args(["--json", command])
                        .arg(&file)
                        .args(["--decl", target]);
                    if command == "agent-step" {
                        cli.arg("--project-dir").arg(&dir);
                    }
                    let output = cli.output().unwrap();
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    let stdout = String::from_utf8_lossy(&output.stdout);
                    if matches!(target, "same" | "Other.A.same" | "Literal.same") {
                        assert!(
                            !output.status.success(),
                            "{command} {target}: {stdout} {stderr}"
                        );
                        if target == "same" {
                            assert!(
                                stderr.contains("Ambiguous declaration")
                                    && stderr.contains("A.same")
                                    && stderr.contains("B.same"),
                                "{stderr}"
                            );
                        }
                        assert!(!stdout.contains("counterexample"), "{stdout}");
                        continue;
                    }
                    let value: serde_json::Value = serde_json::from_slice(&output.stdout)
                        .unwrap_or_else(|_| panic!("{command} {target}: {stdout} {stderr}"));
                    if command == "agent-step" {
                        assert!(output.status.success(), "{stderr}");
                        assert_eq!(value["decl"], target);
                        assert_eq!(
                            value["status"],
                            if target == "A.same" {
                                "theorem_verified"
                            } else {
                                "counterexample_rejected"
                            }
                        );
                    } else {
                        assert_eq!(value["decl_name"], target);
                        assert_eq!(value["verified"], target == "A.same");
                        assert_eq!(
                            value["status"],
                            if target == "A.same" {
                                "ok"
                            } else {
                                "counterexample_found"
                            }
                        );
                    }
                }
            }
        }
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn test_check_qualified_decl_rebuilds_legacy_stat_split() {
        let dir = std::env::temp_dir().join(format!(
            "turbo_legacy_qualified_split_{}",
            crate::pack::next_tmp_id()
        ));
        let proj = dir.join("proj");
        fs::create_dir_all(&proj).unwrap();
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        let file = proj.join("Legacy.lean");
        // Checking A must succeed even though the later, same-spelled B theorem is invalid.
        let src = "namespace A\ntheorem same : True := True.intro\nend A\nnamespace B\ntheorem same : False := True.intro\nend B\n";
        fs::write(&file, src).unwrap();
        let mut store = TurboStore::open(Some(&dir.join("store"))).unwrap();
        let src_b3 = blake3::hash(src.as_bytes()).to_hex().to_string();
        let split = split_lean_source(src, &[]);
        let mut legacy = serde_json::to_value(ShmCachedFileSplit {
            src_blake3: src_b3.clone(),
            split_key: format!("file-split:v3:{}", src_b3),
            split: compact_split_for_shm_cache(&split),
            prefix_src: String::new(),
            known_modified: false,
            dep_hashes: Vec::new(),
        })
        .unwrap();
        for shard in legacy["split"]["shards"].as_array_mut().unwrap() {
            shard["name"] = serde_json::json!("same");
            shard.as_object_mut().unwrap().remove("qualified_name");
        }
        let canon_file = file.canonicalize().unwrap();
        let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&fs::metadata(&file).unwrap());
        let pk = canon_file.to_string_lossy();
        let hash_for_version = |version: &[u8]| {
            let mut hash = blake3::Hasher::new();
            hash.update(version);
            hash.update(pk.as_bytes());
            hash.update(b":");
            hash.update(&ms.to_le_bytes());
            hash.update(&mn.to_le_bytes());
            hash.update(&sz.to_le_bytes());
            hash.finalize().to_hex().to_string()
        };
        let old_hash = hash_for_version(b"single-stat-split:v3\n");
        let splits_dir = shm_file_splits_dir(&store);
        let old_path = splits_dir.join(format!("st_{}.json", &old_hash[..24]));
        fs::write(&old_path, serde_json::to_vec(&legacy).unwrap()).unwrap();
        // The previous PR head stored nonempty, but lexically wrong, identities.
        let stale_hash = hash_for_version(b"single-stat-split:v6\n");
        let stale_path = splits_dir.join(format!("st_{}.json", &stale_hash[..24]));
        for shard in legacy["split"]["shards"].as_array_mut().unwrap() {
            shard["qualified_name"] = serde_json::json!("Wrong.same");
        }
        fs::write(&stale_path, serde_json::to_vec(&legacy).unwrap()).unwrap();

        let new_hash = compute_single_stat_hash(&pk, ms, mn, sz);
        assert_ne!(new_hash, old_hash);
        assert_ne!(new_hash, stale_hash);

        let result = evaluate_check_command_value(
            &mut store,
            file.clone(),
            Some("A.same".into()),
            proj.clone(),
        )
        .unwrap();
        assert_eq!(result["status"], "theorem_verified");
        assert_eq!(result["decl"], "A.same");
        let rebuilt: ShmCachedFileSplit = serde_json::from_slice(
            &fs::read(splits_dir.join(format!("st_{}.json", &new_hash[..24]))).unwrap(),
        )
        .unwrap();
        assert_eq!(rebuilt.split.shards[0].decl_name(), "A.same");
        assert_eq!(rebuilt.split.shards[1].decl_name(), "B.same");
        let warm = evaluate_check_command_value(
            &mut store,
            file.clone(),
            Some("A.same".into()),
            proj.clone(),
        )
        .unwrap();
        assert_eq!(warm["status"], "theorem_cache_hit");
        let agent = crate::gpu_fastcheck::evaluate_agent_step_value(
            &mut store,
            &file,
            Some("A.same"),
            Some(&proj),
            false,
            false,
        )
        .unwrap();
        assert_eq!(agent["status"], "theorem_cache_hit");
        assert_eq!(agent["shard_hits"], 1);
        let ambiguous = crate::gpu_fastcheck::evaluate_agent_step_value(
            &mut store,
            &file,
            Some("same"),
            Some(&proj),
            false,
            false,
        )
        .unwrap_err();
        assert!(ambiguous.to_string().contains("Ambiguous declaration"));
        assert!(
            evaluate_check_command_value(&mut store, file, Some("B.same".into()), proj).is_err()
        );
        let _ = fs::remove_file(old_path);
        let _ = fs::remove_file(stale_path);
        let _ = fs::remove_file(splits_dir.join(format!("st_{}.json", &new_hash[..24])));
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn test_check_decl_stat_cache_reconstructs_signature_and_proof_telemetry() {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_stat_cache_telemetry_{}",
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let (store_dir, proj_dir) = (tmp_dir.join("store"), tmp_dir.join("proj"));
        fs::create_dir_all(&store_dir).unwrap();
        fs::create_dir_all(&proj_dir).unwrap();

        let toolchain = "leanprover/lean4:v4.35.0";
        fs::write(proj_dir.join("lean-toolchain"), format!("{}\n", toolchain)).unwrap();
        let lean_file = proj_dir.join("StatCacheTelemetry.lean");
        let src = "theorem stat_cache_eq_thm (a b : Nat) (h : a = b) : Nat.succ a = Nat.succ b := by\n  simp only [h]\n";
        fs::write(&lean_file, src).unwrap();

        let mut store = TurboStore::open(Some(&store_dir)).unwrap();
        let split = split_lean_source(src, &[]);
        let shard = &split.shards[0];
        let attested = confirm_decl_identity(src, shard, &proj_dir, &lean_file).unwrap();
        let shard_key = compute_shard_key(toolchain, shard);
        let receipt = make_attested_shard_receipt_bytes(
            &shard.name,
            &shard.prefix_env_hash,
            &shard.stmt_hash,
            &shard.proof_hash,
            db::now_unix(),
            Some(&attested.kernel_type_hash),
        )
        .unwrap();
        store
            .batch_publish_theorem_shards(
                toolchain,
                "trusted",
                &[(shard_key, shard.name.clone(), receipt, 1)],
            )
            .unwrap();

        let first = evaluate_check_command_value(
            &mut store,
            lean_file.clone(),
            Some("stat_cache_eq_thm".to_string()),
            proj_dir.clone(),
        )
        .unwrap();
        let second = evaluate_check_command_value(
            &mut store,
            lean_file.clone(),
            Some("stat_cache_eq_thm".to_string()),
            proj_dir.clone(),
        )
        .unwrap();

        for res in [&first, &second] {
            assert_eq!(res["status"], "theorem_cache_hit");
            assert_eq!(res["goal_head"], "Eq");
            assert_eq!(res["tactic_skeleton"], "simp_only");
            assert!(res["stmt_nodes"].as_u64().unwrap_or(0) > 4);
            assert!(res["proof_term_nodes"].as_u64().unwrap_or(0) > 0);
            let consts: Vec<&str> = res["stmt_consts"]
                .as_array()
                .unwrap()
                .iter()
                .filter_map(|v| v.as_str())
                .collect();
            assert!(consts.contains(&"Nat") && consts.contains(&"Nat.succ"));
        }
        assert_eq!(first["stmt_nodes"], second["stmt_nodes"]);
        assert_eq!(first["stmt_depth"], second["stmt_depth"]);
        assert_eq!(first["num_binders"], second["num_binders"]);
        assert_eq!(first["stmt_consts"], second["stmt_consts"]);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_fission_store_key_namespaces_axiom_allowlist_and_mcp_rechecks_dependents() {
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let prev_allow = std::env::var(splitter::ALLOWED_AXIOMS_ENV).ok();
        std::env::remove_var(splitter::ALLOWED_AXIOMS_ENV);
        let k_default = compute_fission_store_key("tc", "pref", "sub0");
        std::env::set_var(splitter::ALLOWED_AXIOMS_ENV, "*");
        let k_wildcard = compute_fission_store_key("tc", "pref", "sub0");
        std::env::set_var(splitter::ALLOWED_AXIOMS_ENV, "*._native.bv_decide.ax_*");
        let k_bv = compute_fission_store_key("tc", "pref", "sub0");
        match prev_allow {
            Some(v) => std::env::set_var(splitter::ALLOWED_AXIOMS_ENV, v),
            None => std::env::remove_var(splitter::ALLOWED_AXIOMS_ENV),
        }
        assert_ne!(k_default, k_wildcard);
        assert_ne!(k_default, k_bv);
        assert_ne!(k_wildcard, k_bv);

        let dir = std::env::temp_dir().join(format!(
            "turbo_mcp_nonlocal_recheck_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(dir.join("P")).unwrap();
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"p\"\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n[[lean_exe]]\nname = \"app\"\nroot = \"Main\"\n",
        )
        .unwrap();
        let a_src = "theorem t (n : Nat) : n + 0 = n := by\n  simp\n";
        fs::write(dir.join("P/A.lean"), a_src).unwrap();
        fs::write(
            dir.join("P/B.lean"),
            "import P.A\ntheorem u (m : Nat) : m + 0 = m := by\n  omega\n",
        )
        .unwrap();
        fs::write(
            dir.join("Main.lean"),
            "import P.A\ntheorem exe_dep (m : Nat) : m + 0 = m := t m\ndef main : IO Unit := pure ()\n",
        )
        .unwrap();
        let ok = |c: &mut Command| c.current_dir(&dir).output().map(|o| o.status.success());
        if !ok(Command::new("lake").args(["build", "P", "Main"])).unwrap_or(false) {
            let _ = fs::remove_dir_all(&dir);
            return;
        }
        for args in [
            &["init", "-q"][..],
            &["add", "."],
            &[
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@t",
                "commit",
                "-qm",
                "base",
            ],
        ] {
            assert!(ok(Command::new("git").args(args)).unwrap());
        }
        // Statement edit on `P/A.lean` remains locally provable in `P.A` (`0 + n = n`),
        // but breaks importer `P.B`: in-process `evaluate_agent_step_value`,
        // `evaluate_check_command_value`, and `execute_mcp_agent_step` must all reject!
        fs::write(
            dir.join("P/A.lean"),
            "theorem t (n : Nat) : 0 + n = n := by\n  omega\n",
        )
        .unwrap();
        let mut store = TurboStore::open(Some(&dir.join(".cache"))).unwrap();
        assert!(crate::gpu_fastcheck::evaluate_agent_step_value(
            &mut store,
            &dir.join("P/A.lean"),
            Some("t"),
            Some(&dir),
            false,
            false,
        )
        .is_err());
        assert!(evaluate_check_command_value(
            &mut store,
            dir.join("P/A.lean"),
            Some("t".to_string()),
            dir.clone(),
        )
        .is_err());
        let mcp_out = crate::mcp::execute_mcp_agent_step(
            &dir.join("P/A.lean"),
            Some("t"),
            false,
            false,
            Some(&dir),
            Some(&dir.join(".cache")),
        );
        assert_eq!(mcp_out["ok"], false);
        assert_eq!(mcp_out["verified"], false);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn invalid_config_errors_before_empty_option_cache_lookup() -> Result<()> {
        let dir =
            std::env::temp_dir().join(format!("turbo_check_bad_options_{}", pack::next_tmp_id()));
        let project = dir.join("project");
        fs::create_dir_all(&project)?;
        let file = project.join("Options.lean");
        let source = "theorem option_error : True := by trivial\n";
        fs::write(&file, source)?;
        let tc = "leanprover/lean4:v4.35.0";
        let split = split_lean_source(source, &[]);
        let shard = &split.shards[0];
        let key = compute_shard_key(tc, shard);
        let receipt = make_shard_receipt_bytes(
            &shard.name,
            &shard.prefix_env_hash,
            &shard.stmt_hash,
            &shard.proof_hash,
            db::now_unix(),
        )?;
        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        store.batch_publish_theorem_shards(
            tc,
            "trusted",
            &[(key, shard.name.clone(), receipt, 1)],
        )?;
        fs::write(
            project.join("lakefile.toml"),
            "name = \"invalid\"\nmoreLeanArgs = [\"--plugin=bad.so\"]\n",
        )?;
        for decl in [Some("option_error".to_string()), None] {
            let err = evaluate_check_command_value(&mut store, file.clone(), decl, project.clone())
                .unwrap_err();
            assert!(format!("{err:#}").contains("Failed to resolve Lean options"));
        }
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    #[test]
    fn test_lean_args_digest_isolates_shard_and_fission_cache_keys() {
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let src = "theorem hb_thm (n : Nat) : n + 0 = n := by\n  simp\n";
        let split = split_lean_source(src, &[]);
        let shard = &split.shards[0];
        let tc = "leanprover/lean4:v4.35.0";
        let bare = compute_shard_key(tc, shard);
        let with_hb = crate::lake_build::compute_shard_key_with_args(
            tc,
            shard,
            &["-DmaxHeartbeats=4000000".to_string()],
        );
        let with_other = crate::lake_build::compute_shard_key_with_args(
            tc,
            shard,
            &["-DmaxHeartbeats=200000".to_string()],
        );
        assert_ne!(bare, with_hb);
        assert_ne!(with_hb, with_other);
        assert_eq!(
            crate::lake_build::compute_shard_key_with_args(tc, shard, &[]),
            bare
        );

        let f_bare = compute_fission_store_key(tc, "pref", "sub0");
        let f_hb = compute_fission_store_key_with_args(
            tc,
            "pref",
            "sub0",
            &["-DmaxHeartbeats=4000000".to_string()],
        );
        assert_ne!(f_bare, f_hb);
    }

    #[cfg(unix)]
    #[test]
    fn test_active_check_staging_writer_protected_against_store_local_gc_and_shm_spill(
    ) -> Result<()> {
        use std::os::unix::fs::PermissionsExt;
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_check_staging_gc_race_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let project = dir.join("project");
        let store_root = dir.join("store");
        let store_staging = store_root.join("staging");
        let fake_elan_root = dir.join("fake_elan");
        let tc_name = "leanprover/lean4:v4.35.0-check-gc-race";
        let tc_root = fake_elan_root
            .join("toolchains")
            .join("leanprover--lean4---v4.35.0-check-gc-race");
        let bin_dir = tc_root.join("bin");
        fs::create_dir_all(&project)?;
        fs::create_dir_all(&store_staging)?;
        fs::create_dir_all(&bin_dir)?;

        // Configure `fast_staging_dir()` to resolve directly to `<store>/staging` (exercising the
        // store-local fallback where `run_gc(0, ...)` sweeps 0-second unleased entries immediately),
        // point `ELAN_HOME` at our isolated synthetic toolchain so `ToolchainExecutables` resolves
        // our wrapper `lean` binary cleanly under PR #308's absolute toolchain gate, and disable
        // the background Zygote daemon so `evaluate_check_command_value` executes the real
        // `PrivateScratchDir` -> `run_audited_lean_shard_with_types` staging path.
        let prev_staging = std::env::var("TURBO_LEAN_STAGING_DIR").ok();
        let prev_no_daemon = std::env::var("TURBO_LEAN_NO_DAEMON").ok();
        let prev_elan_home = std::env::var("ELAN_HOME").ok();
        struct RestoreCheckEnv(Option<String>, Option<String>, Option<String>);
        impl Drop for RestoreCheckEnv {
            fn drop(&mut self) {
                match &self.0 {
                    Some(v) => std::env::set_var("TURBO_LEAN_STAGING_DIR", v),
                    None => std::env::remove_var("TURBO_LEAN_STAGING_DIR"),
                }
                match &self.1 {
                    Some(v) => std::env::set_var("TURBO_LEAN_NO_DAEMON", v),
                    None => std::env::remove_var("TURBO_LEAN_NO_DAEMON"),
                }
                match &self.2 {
                    Some(v) => std::env::set_var("ELAN_HOME", v),
                    None => std::env::remove_var("ELAN_HOME"),
                }
            }
        }
        let _restore_env = RestoreCheckEnv(prev_staging, prev_no_daemon, prev_elan_home);
        std::env::set_var("TURBO_LEAN_STAGING_DIR", &store_staging);
        std::env::set_var("TURBO_LEAN_NO_DAEMON", "1");

        let fake_lean = bin_dir.join("lean");
        let repo_lean_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lean");
        let resolve_cwd = if repo_lean_dir.is_dir() {
            repo_lean_dir
        } else {
            dir.clone()
        };
        let real_prefix = Command::new("lean")
            .arg("--print-prefix")
            .current_dir(&resolve_cwd)
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| PathBuf::from(String::from_utf8_lossy(&o.stdout).trim()))
            .and_then(|p| p.canonicalize().ok())
            .filter(|p| {
                p.join("bin/lean").is_file()
                    && !p.starts_with(&fake_elan_root)
                    && !p.join("bin/elan").exists()
            });
        let Some(real_prefix) = real_prefix else {
            let _ = fs::remove_dir_all(&dir);
            return Ok(());
        };
        let real_lean = real_prefix.join("bin/lean");
        for sub in ["lib", "include", "share"] {
            let src_sub = real_prefix.join(sub);
            if src_sub.exists() {
                std::os::unix::fs::symlink(&src_sub, tc_root.join(sub))?;
            }
        }
        for sib in ["lake", "leanc"] {
            let real_sib = real_prefix.join("bin").join(sib);
            let sp = bin_dir.join(sib);
            if real_sib.is_file() {
                fs::write(
                    &sp,
                    format!("#!/bin/sh\nexec '{}' \"$@\"\n", real_sib.display()),
                )?;
            } else {
                fs::write(&sp, "#!/bin/sh\nexit 0\n")?;
            }
            fs::set_permissions(&sp, fs::Permissions::from_mode(0o755))?;
        }
        std::env::set_var("ELAN_HOME", &fake_elan_root);

        // Wrapper `lean` binary: forwards identity/build calls directly, then when invoked on the
        // staged `TurboAuditedShard_*.lean` file inside `<store>/staging` signals `arrived_marker`
        // BEFORE compiling it, blocks until concurrent `run_gc(0, ...)` and `spill_shm_to_disk_dir`
        // sweeps complete (`proceed_marker`), and finally compiles the staged shard.
        let arrived_marker = dir.join("child_arrived");
        let proceed_marker = dir.join("child_proceed");
        let script = format!(
            "#!/bin/sh\nif [ \"${{1:-}}\" = \"--githash\" ]; then exec '{rl}' --githash; fi\nif [ \"${{1:-}}\" = \"--print-prefix\" ]; then echo '{tc}'; exit 0; fi\nif [ \"${{1:-}}\" = \"--version\" ]; then exec '{rl}' --version; fi\ncase \"$*\" in\n  *TurboAuditedShard_*)\n    : > '{arr}'\n    while [ ! -f '{proc}' ]; do\n      if [ -x /bin/sleep ]; then /bin/sleep 0.01; elif [ -x /usr/bin/sleep ]; then /usr/bin/sleep 0.01; fi\n    done\n    ;;\nesac\nexec '{rl}' \"$@\"\n",
            rl = real_lean.display(),
            tc = tc_root.display(),
            arr = arrived_marker.display(),
            proc = proceed_marker.display(),
        );
        fs::write(&fake_lean, script)?;
        fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755))?;

        fs::write(project.join("lean-toolchain"), format!("{tc_name}\n"))?;
        let lean_file = project.join("CheckGcRace.lean");
        fs::write(&lean_file, "theorem gc_race_a : True := trivial\n")?;

        let store = TurboStore::open(Some(&store_root))?;
        assert_eq!(store.fast_staging_dir(), store_staging);
        let canon_project = project.canonicalize()?;
        let proj_key = TurboStore::compute_lake_env_key(&canon_project);
        let mut fake_env = HashMap::new();
        fake_env.insert("LEAN_PATH".to_string(), String::new());
        store.put_lake_env(&proj_key, &fake_env)?;
        drop(store);

        // Pre-warm the declaration-identity / shard auditor binary BEFORE spawning the timed
        // `evaluate_check_command_value` worker so a cold `ensure_zygote_binary_at` compile does
        // not consume the request timeout budget, and give the parked subprocess generous slack.
        let prev_timeout_ms = std::env::var("TURBO_LEAN_TIMEOUT_MS").ok();
        std::env::set_var("TURBO_LEAN_TIMEOUT_MS", "120000");
        struct RestoreTimeout(Option<String>);
        impl Drop for RestoreTimeout {
            fn drop(&mut self) {
                match &self.0 {
                    Some(v) => std::env::set_var("TURBO_LEAN_TIMEOUT_MS", v),
                    None => std::env::remove_var("TURBO_LEAN_TIMEOUT_MS"),
                }
            }
        }
        let _restore_timeout = RestoreTimeout(prev_timeout_ms);
        let mut warm_env = HashMap::new();
        warm_env.insert("LEAN_PATH".to_string(), String::new());
        let _ = crate::zygote::ensure_zygote_binary_at(
            &crate::shm_cache::cache_root(),
            &fake_lean,
            &warm_env,
        )?;
        let _ = crate::zygote::ensure_zygote_binary_at(&store_root, &fake_lean, &warm_env)?;

        // Seed unleased file and directory orphans in `<store>/staging` so we prove `run_gc(0, ...)`
        // actively sweeps `<store>/staging` during the window while sparing the live leased scratch dirs.
        let orphan_tmp = store_staging.join("unleased_orphan_before_check.lean");
        fs::write(&orphan_tmp, b"-- stale unleased staging file\n")?;
        let orphan_dir = store_staging.join("turbo_audited_src_stale_orphan");
        fs::create_dir_all(&orphan_dir)?;
        fs::write(orphan_dir.join("Stale.lean"), b"-- stale orphan dir\n")?;

        let check_store_root = store_root.clone();
        let check_file = lean_file.clone();
        let check_proj = project.clone();
        let worker = std::thread::spawn(move || -> Result<serde_json::Value> {
            let mut worker_store = TurboStore::open(Some(&check_store_root))?;
            evaluate_check_command_value(&mut worker_store, check_file, None, check_proj)
        });

        let wait_t0 = Instant::now();
        while !arrived_marker.exists() {
            if worker.is_finished() {
                break;
            }
            assert!(
                wait_t0.elapsed().as_secs() < 120,
                "timed out waiting for check subprocess to spawn"
            );
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        assert!(
            arrived_marker.exists(),
            "check path must invoke lean subprocess on staged file"
        );
        let active_src_dir = fs::read_dir(&store_staging)?
            .flatten()
            .map(|e| e.path())
            .find(|p| {
                p != &orphan_dir
                    && p.is_dir()
                    && p.file_name()
                        .and_then(|n| n.to_str())
                        .is_some_and(|n| n.starts_with("turbo_audited_src_"))
            })
            .expect("active leased turbo_audited_src_* dir must exist while lean is parked");
        let active_leased_lean = fs::read_dir(&active_src_dir)?
            .flatten()
            .map(|e| e.path())
            .find(|p| p.extension().and_then(|s| s.to_str()) == Some("lean"))
            .expect("staged TurboAuditedShard_*.lean must exist inside active_src_dir");

        let mut gc_store = TurboStore::open(Some(&store_root))?;
        let gc_rep = gc_store.run_gc(0, 7 * 86400, true)?;
        assert!(
            !orphan_tmp.exists() && !orphan_dir.exists(),
            "run_gc(0) must still reap unleased file and dir orphans in <store>/staging"
        );
        assert!(
            active_src_dir.exists() && fs::symlink_metadata(&active_leased_lean).is_ok(),
            "run_gc(0) must preserve active leased check staging scratch dir and file in <store>/staging"
        );
        assert!(gc_rep.cleaned_staging_files >= 2);

        let spill_dir = dir.join("shm_spill");
        let _ = crate::shm_cache::spill_shm_to_disk_dir(&store_staging, &spill_dir, 0)?;
        assert!(
            fs::symlink_metadata(&active_leased_lean).is_ok()
                && !spill_dir
                    .join(active_leased_lean.file_name().unwrap())
                    .exists(),
            "spill_shm_to_disk_dir must not evict/move leased active check staging files"
        );
        let _ = crate::shm_cache::enforce_shm_quota_lru(&store_staging, 1)?;
        assert!(
            fs::symlink_metadata(&active_leased_lean).is_ok(),
            "enforce_shm_quota_lru must not evict leased active check staging files"
        );

        fs::write(&proceed_marker, b"go")?;
        let check_val = worker
            .join()
            .expect("check worker thread panicked")
            .context("active check must succeed despite concurrent run_gc(0) + SHM eviction")?;
        assert_eq!(check_val["status"], "file_verified");

        // After check completes and drops `PrivateScratchDir`, neither scratch dirs nor `.lease.lock` remain.
        let remaining: Vec<String> = fs::read_dir(&store_staging)?
            .flatten()
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .filter(|n| n.contains("turbo_audited_") || n.ends_with(".lease.lock"))
            .collect();
        assert!(
            remaining.is_empty(),
            "PrivateScratchDir drop must clean up both scratch dirs and sidecar .lease.lock, found {remaining:?}"
        );
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_read_single_isolated_olean_rejects_extra_files_symlinks_and_hardlinks() -> Result<()> {
        let scratch = PrivateScratchDir::create(&std::env::temp_dir(), "turbo_iso_olean_test")?;
        let out_dir = scratch.path.join("out");
        fs::create_dir_all(&out_dir)?;

        // Empty output dir fails closed.
        assert!(read_single_isolated_olean(&out_dir, "ExpectedMod").is_err());

        // Exact single regular `.olean` succeeds.
        let expected = out_dir.join("ExpectedMod.olean");
        fs::write(&expected, b"valid-olean-bytes")?;
        assert_eq!(
            read_single_isolated_olean(&out_dir, "ExpectedMod")?,
            b"valid-olean-bytes"
        );

        // Any extra/forged file inside `out_dir` fails closed.
        let forged = out_dir.join("ForgedOther.olean");
        fs::write(&forged, b"forged-bytes")?;
        let err = read_single_isolated_olean(&out_dir, "ExpectedMod").unwrap_err();
        assert!(
            format!("{err:#}").contains("must contain only"),
            "unexpected error: {err:#}"
        );
        fs::remove_file(&forged)?;

        #[cfg(unix)]
        {
            // Hardlink (`st_nlink > 1`) fails closed so no out-of-dir alias can mutate after check.
            let outside_link = scratch.path.join("alias.olean");
            fs::hard_link(&expected, &outside_link)?;
            let err = read_single_isolated_olean(&out_dir, "ExpectedMod").unwrap_err();
            assert!(
                format!("{err:#}").contains("hard-link count"),
                "unexpected error: {err:#}"
            );
            fs::remove_file(&outside_link)?;

            // Symlink at expected path fails closed via O_NOFOLLOW.
            let target = scratch.path.join("real.olean");
            fs::write(&target, b"real-olean-bytes")?;
            fs::remove_file(&expected)?;
            std::os::unix::fs::symlink(&target, &expected)?;
            assert!(read_single_isolated_olean(&out_dir, "ExpectedMod").is_err());
        }
        Ok(())
    }

    #[test]
    #[cfg(unix)]
    fn test_post_exit_background_child_reaped_and_frozen_dir_blocks_overwrite() -> Result<()> {
        use std::os::unix::fs::PermissionsExt;
        let scratch = PrivateScratchDir::create(&std::env::temp_dir(), "turbo_bg_reap_test")?;
        let out_dir = scratch.path.join("out");
        fs::create_dir_all(&out_dir)?;
        let expected = out_dir.join("Mod.olean");
        let nonce = format!("reap-nonce-{}-{}", std::process::id(), pack::next_tmp_id());

        let mut cmd = Command::new("/bin/sh");
        cmd.env("TURBO_LEAN_PROBE_NONCE", &nonce)
            .env("OUT_DIR", &out_dir)
            .arg("-c")
            .arg(
                "printf 'clean-olean' > \"$OUT_DIR/Mod.olean\"; \
                 (sleep 0.35; printf 'forged' > \"$OUT_DIR/Mod.olean.new\" 2>/dev/null && mv \"$OUT_DIR/Mod.olean.new\" \"$OUT_DIR/Mod.olean\" 2>/dev/null; printf 'forged' > \"$OUT_DIR/Mod.olean\" 2>/dev/null) </dev/null >/dev/null 2>&1 & \
                 exit 0",
            );
        let out = crate::module_builder::run_command_with_timeout(
            &mut cmd,
            std::time::Duration::from_secs(10),
            false,
        )?;
        assert!(out.status.success());
        crate::zygote::reap_processes_with_nonce(&nonce);
        freeze_private_dir(&out_dir)?;
        fs::set_permissions(&expected, fs::Permissions::from_mode(0o400))?;

        std::thread::sleep(std::time::Duration::from_millis(500));
        let bytes = read_single_isolated_olean(&out_dir, "Mod")?;
        assert_eq!(bytes, b"clean-olean");
        Ok(())
    }

    #[test]
    fn test_agent_step_rejects_unattested_or_mislabeled_cached_receipt_and_reattests() -> Result<()>
    {
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir =
            std::env::temp_dir().join(format!("turbo_agent_step_reattest_{}", pack::next_tmp_id()));
        let project = dir.join("project");
        let cache = dir.join("cache");
        fs::create_dir_all(&project)?;
        fs::write(
            project.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )?;
        fs::write(
            project.join("lakefile.toml"),
            "name = \"reattest\"\nversion = \"0.1.0\"\n",
        )?;
        let file = project.join("Identity.lean");
        // Valid proof first: seed an unattested legacy receipt (no `kernel_type_hash` and short name).
        let valid_src = "namespace B\ntheorem same (n : Nat) : n = n := rfl\nend B\n";
        fs::write(&file, valid_src)?;
        let tc = detect_toolchain(&project);
        let split = split_lean_source(valid_src, &[]);
        let shard = &split.shards[0];
        let key = compute_shard_key(&tc, shard);
        let mut store = TurboStore::open(Some(&cache))?;
        let unattested_receipt = make_shard_receipt_bytes(
            &shard.name,
            &shard.prefix_env_hash,
            &shard.stmt_hash,
            &shard.proof_hash,
            db::now_unix(),
        )?;
        store.batch_publish_theorem_shards(
            &tc,
            "trusted",
            &[(key.clone(), shard.name.clone(), unattested_receipt, 1)],
        )?;
        // Untargeted (`None`) and `"auto"` must NOT accept the unattested receipt as a `stage0_cas_hit`:
        // they must invalidate it, run Stage-2 kernel verification, and write an attested receipt.
        let v_cold = crate::gpu_fastcheck::evaluate_agent_step_value(
            &mut store,
            &file,
            Some("auto"),
            Some(&project),
            false,
            false,
        )?;
        assert_eq!(v_cold["verified"], true, "{v_cold}");
        assert_eq!(
            v_cold["status"], "file_verified",
            "unattested cached receipt must not short-circuit as cached hit: {v_cold}"
        );
        assert_eq!(v_cold["shard_hits"], 0, "{v_cold}");
        // Subsequent untargeted call now hits the freshly attested receipt.
        let v_warm = crate::gpu_fastcheck::evaluate_agent_step_value(
            &mut store,
            &file,
            None,
            Some(&project),
            false,
            false,
        )?;
        assert_eq!(v_warm["verified"], true, "{v_warm}");
        assert_eq!(v_warm["status"], "all_shards_cached", "{v_warm}");
        assert_eq!(v_warm["decl"], "B.same", "{v_warm}");

        // Now poison the cache for a broken proof on a true statement (`True`) with an unattested
        // receipt: `agent-step` must NOT accept the unattested receipt as a cached hit (`verified: true`)
        // and must fail closed in Stage 2.
        let invalid_src = "namespace B\ntheorem broken : True := 0\nend B\n";
        fs::write(&file, invalid_src)?;
        let bad_split = split_lean_source(invalid_src, &[]);
        let bad_shard = &bad_split.shards[0];
        let bad_key = compute_shard_key(&tc, bad_shard);
        let forged_unattested = make_shard_receipt_bytes(
            bad_shard.decl_name(),
            &bad_shard.prefix_env_hash,
            &bad_shard.stmt_hash,
            &bad_shard.proof_hash,
            db::now_unix(),
        )?;
        store.batch_publish_theorem_shards(
            &tc,
            "trusted",
            &[(
                bad_key,
                bad_shard.decl_name().to_string(),
                forged_unattested,
                1,
            )],
        )?;
        assert!(crate::gpu_fastcheck::evaluate_agent_step_value(
            &mut store,
            &file,
            None,
            Some(&project),
            false,
            false,
        )
        .is_err());

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_identity_probe_hardening_escaped_aux_inferred_module_werror_readonly_and_lean_path(
    ) -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!("turbo_id_hardening_{}", pack::next_tmp_id()));
        let ext_pkg = dir.join("ext_pkg");
        let project = dir.join("project");
        fs::create_dir_all(&ext_pkg)?;
        fs::create_dir_all(&project)?;
        let tc_text = include_str!("../../../lean/lean-toolchain");
        fs::write(project.join("lean-toolchain"), tc_text)?;
        fs::write(
            project.join("lakefile.toml"),
            "name = \"idhard\"\nversion = \"0.1.0\"\nleanOptions = { warningAsError = true }\n",
        )?;

        // Build an external `.olean` outside `project` and expose it only via `LEAN_PATH`.
        let ext_src = ext_pkg.join("ExtIdDep.lean");
        let ext_olean = ext_pkg.join("ExtIdDep.olean");
        fs::write(&ext_src, "def ext_magic : Nat := 7\n")?;
        let base_env = crate::lake_build::spawn_lake_env(&project)?;
        let lean_bin = resolve_lean_bin(&project)?;
        let ext_out = Command::new(&lean_bin)
            .envs(&base_env)
            .arg(&ext_src)
            .arg("-R")
            .arg(&ext_pkg)
            .arg("-o")
            .arg(&ext_olean)
            .output()?;
        assert!(
            ext_out.status.success(),
            "failed to compile ExtIdDep.lean: {}",
            String::from_utf8_lossy(&ext_out.stderr)
        );
        let prev_lp = std::env::var("LEAN_PATH").ok();
        let new_lp = match &prev_lp {
            Some(p) if !p.is_empty() => format!("{}:{p}", ext_pkg.display()),
            _ => ext_pkg.display().to_string(),
        };
        std::env::set_var("LEAN_PATH", &new_lp);
        struct RestoreLeanPath(Option<String>);
        impl Drop for RestoreLeanPath {
            fn drop(&mut self) {
                match &self.0 {
                    Some(v) => std::env::set_var("LEAN_PATH", v),
                    None => std::env::remove_var("LEAN_PATH"),
                }
            }
        }
        let _restore_lp = RestoreLeanPath(prev_lp);

        // 1) Escaped names (`«foo»`), macro-generated auxiliary theorem in same command span,
        //    `warningAsError = true` with earlier theorem stubbed to `sorry`, body-inferred `def`
        //    (`def inferred_ty := ...`), external `LEAN_PATH` import, and read-only (`0o555`)
        //    source project directory.
        let src = "\
import ExtIdDep
macro \"declare_with_aux \" id:ident : command => `(
  theorem aux_generated_helper : True := True.intro
  theorem $id : ext_magic = 7 := rfl
)
theorem earlier_for_werror : ext_magic = 7 := rfl
namespace «EscNs»
theorem «foo» : ext_magic = 7 := rfl
end «EscNs»
declare_with_aux macro_primary
theorem after_macro : ext_magic = 7 := rfl
";
        let file = project.join("Hardening.lean");
        fs::write(&file, src)?;

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&file, fs::Permissions::from_mode(0o444))?;
            fs::set_permissions(&project, fs::Permissions::from_mode(0o555))?;
        }

        let split = split_lean_source(src, &[]);
        // Shards in split: `earlier_for_werror`, `«EscNs».«foo»`, `after_macro`.
        let esc_idx = splitter::find_decl_shard_index(&split.shards, "EscNs.foo")?
            .expect("escaped shard resolved");
        let after_idx = splitter::find_decl_shard_index(&split.shards, "after_macro")?
            .expect("after_macro shard resolved");
        let shard_refs: Vec<&splitter::TheoremShard> = split.shards.iter().collect();
        let batch_atts = confirm_file_decl_identities_with_budget(
            src,
            &shard_refs,
            &project,
            &file,
            false,
            None,
        )?;
        assert_eq!(batch_atts.len(), split.shards.len());
        assert_eq!(batch_atts[esc_idx].decl_name, "EscNs.foo");
        assert_eq!(batch_atts[after_idx].decl_name, "after_macro");

        // Equation-compiler / macro-elaborated theorem whose `signature_text` cannot elaborate
        // against `:= by sorry` falls back from stubbed probe to the declaration's original text in
        // `confirm_decl_identity_with_budget`.
        let eq_src = format!(
            "{src}theorem eqn_inferred : Nat → ext_magic = 7\n  | 0 => rfl\n  | _ + 1 => rfl\n"
        );
        let eq_split = split_lean_source(&eq_src, &[]);
        let mut eq_shard = eq_split
            .shards
            .iter()
            .find(|s| s.name == "eqn_inferred")
            .expect("eqn_inferred shard")
            .clone();
        // Simulate a header whose stubbed `:= by sorry` form fails elaboration, forcing full-body retry.
        eq_shard.signature_text = "theorem eqn_inferred : _".to_string();
        let inferred_att =
            confirm_decl_identity_with_budget(&eq_src, &eq_shard, &project, &file, false, None)?;
        assert_eq!(inferred_att.decl_name, "eqn_inferred");
        assert_eq!(inferred_att.kernel_type_hash.len(), 64);

        // Also test `match_expected_decl_identity` directly when auxiliary theorems share the probe span.
        let aux_entries = vec![
            OleanDeclEntry {
                decl_name: "aux_generated_helper".to_string(),
                kernel_type_hash: "1".repeat(64),
                line: Some(10),
            },
            OleanDeclEntry {
                decl_name: "«EscNs».«foo»".to_string(),
                kernel_type_hash: "2".repeat(64),
                line: Some(10),
            },
        ];
        let matched = match_expected_decl_identity("EscNs.foo", &aux_entries, Some((10, 11)))?;
        assert_eq!(matched.decl_name, "EscNs.foo");
        assert_eq!(matched.kernel_type_hash, "2".repeat(64));

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&project, fs::Permissions::from_mode(0o755))?;
            fs::set_permissions(&file, fs::Permissions::from_mode(0o644))?;
        }

        // 2) Lean 4.35 `module` header emits `.olean`, `.olean.server`, `.olean.private`, `.ir`, `.ir.sig`.
        let mod_src = "module\npublic theorem pub_mod_thm : True := True.intro\ntheorem priv_mod_thm : (1 : Nat) = 1 := rfl\n";
        let mod_file = project.join("ModFile.lean");
        fs::write(&mod_file, mod_src)?;
        let mod_split = split_lean_source(mod_src, &[]);
        assert_eq!(mod_split.shards.len(), 2);
        let mod_refs: Vec<&splitter::TheoremShard> = mod_split.shards.iter().collect();
        let mod_atts = confirm_file_decl_identities_with_budget(
            mod_src, &mod_refs, &project, &mod_file, false, None,
        )?;
        assert_eq!(mod_atts.len(), 2);
        assert_eq!(mod_atts[0].decl_name, "pub_mod_thm");
        assert_eq!(mod_atts[1].decl_name, "priv_mod_thm");

        // Stage isolated module artifacts rejects unexpected files while accepting `.olean.{server,private}` and `.ir{,.sig}`.
        let iso = PrivateScratchDir::create(&std::env::temp_dir(), "turbo_iso_mod_test")?;
        let out_m = iso.path.join("out");
        let rdr_m = iso.path.join("rdr");
        fs::create_dir_all(&out_m)?;
        fs::create_dir_all(&rdr_m)?;
        for suffix in [
            ".olean",
            ".olean.server",
            ".olean.private",
            ".ir",
            ".ir.sig",
        ] {
            fs::write(out_m.join(format!("M{suffix}")), b"artifact")?;
        }
        stage_isolated_module_artifacts(&out_m, &rdr_m, "M")?;
        assert!(rdr_m.join("M.olean").is_file());
        assert!(rdr_m.join("M.olean.server").is_file());
        assert!(rdr_m.join("M.olean.private").is_file());
        assert!(!rdr_m.join("M.ir").exists());
        fs::write(out_m.join("Forged.olean"), b"bad")?;
        assert!(stage_isolated_module_artifacts(&out_m, &rdr_m, "M").is_err());

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }
}
