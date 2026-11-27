use anyhow::{Context, Result};
use std::collections::{HashMap, HashSet};
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

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
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
    let cache_path = (!is_untrusted && extra_ro_olean_dirs.is_empty())
        .then(|| identity_cache_path(probe, project_dir, lean_args, env?, min_line, max_line))
        .flatten();
    if let Some(entries) = cache_path.as_ref().and_then(|path| {
        read_verified_isolated_artifact(path)
            .ok()
            .and_then(|bytes| serde_json::from_slice::<Vec<OleanDeclEntry>>(&bytes).ok())
    }) {
        return Ok(entries);
    }
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
        if let Some(path) = cache_path {
            if let Ok(bytes) = serde_json::to_vec(&decls) {
                let _ = crate::shm_cache::atomic_write_shm(&path, &bytes);
            }
        }
        Ok(decls)
    })
}

/// Verified elaboration-context inputs shared by both the fine-grained (`identity_cache_path`)
/// and coarse (`decl_identity_coarse_lookup`) declaration-identity caches: toolchain/compiler,
/// `LEAN_PATH` search dirs, effective `leanOptions` (`filter_allowed_lean_args`), and the sorted
/// transitive non-toolchain import closure (`(module, olean_path, source_blake3, olean_digest)`).
///
/// Fails closed (`None`) whenever the probe or any transitive non-toolchain import has a header
/// error, may read host state (`source_may_read_host_state`), uses `include_str`/`include_bin`
/// (`source_uses_include_str`), or cannot resolve its `.olean`/source artifacts.
struct IdentityElaborationContext {
    toolchain: String,
    githash: String,
    compiler: PathBuf,
    dirs: Vec<PathBuf>,
    filtered_lean_args: Vec<String>,
    pins: Vec<(String, PathBuf, String, String)>,
}

impl IdentityElaborationContext {
    fn compute(
        probe_source: &str,
        project_dir: &Path,
        lean_args: &[String],
        env: &HashMap<String, String>,
    ) -> Option<Self> {
        let toolchain = detect_toolchain(project_dir);
        let (compiler, githash, tc_lib, _) =
            crate::module_builder::resolve_toolchain_compiler(project_dir, &toolchain).ok()?;
        Self::compute_with_toolchain(
            probe_source,
            project_dir,
            lean_args,
            env,
            toolchain,
            compiler,
            githash,
            &tc_lib,
        )
    }

    /// [`Self::compute`] against an already-resolved toolchain. Only the canonical toolchain
    /// artifact `tc_lib/<rel>.olean` (winning search root canonicalizes to `tc_lib`, header
    /// githash verified) is left unpinned; every other resolved `.olean` — including an
    /// `Init`/`Std`/`Lean`/`Lake` tree shadowing the toolchain from an earlier `LEAN_PATH`
    /// entry, even one nested under `tc_lib` with a matching githash — is pinned by source and
    /// artifact digest (or fails closed when its source is missing).
    #[allow(clippy::too_many_arguments)]
    fn compute_with_toolchain(
        probe_source: &str,
        project_dir: &Path,
        lean_args: &[String],
        env: &HashMap<String, String>,
        toolchain: String,
        compiler: PathBuf,
        githash: String,
        tc_lib: &Path,
    ) -> Option<Self> {
        let header = crate::module_builder::parse_header_info(probe_source);
        if header.header_error.is_some()
            || splitter::source_may_read_host_state(probe_source)
            || crate::module_builder::source_uses_include_str(probe_source)
        {
            return None;
        }
        let lean_path = env.get("LEAN_PATH").map(String::as_str).unwrap_or("");
        let mut dirs: Vec<PathBuf> = std::env::split_paths(lean_path)
            .filter(|p| !p.as_os_str().is_empty())
            .map(|p| project_dir.join(p))
            .collect();
        dirs.push(tc_lib.to_path_buf());
        let canon_tc_lib = tc_lib.canonicalize().ok();
        let search_dirs: Vec<&Path> = dirs.iter().map(PathBuf::as_path).collect();
        let cfg = crate::module_builder::resolve_project_config(project_dir).ok();
        let mut pending = header.imports;
        let mut visited = HashSet::new();
        let mut pins = Vec::new();
        while let Some(import) = pending.pop() {
            if !visited.insert(import.clone()) {
                continue;
            }
            let path =
                crate::module_builder::resolve_olean_along_search_dirs(&search_dirs, &import)?;
            if is_canonical_toolchain_olean(tc_lib, canon_tc_lib.as_deref(), &import, &path)
                && crate::module_builder::is_verified_toolchain_olean_file(
                    tc_lib,
                    Some(&githash),
                    &path,
                )
            {
                continue;
            }
            let src_path = cfg
                .as_ref()
                .and_then(|cfg| {
                    crate::module_builder::resolve_source_spec_for_prebuilt_olean(cfg, &path)
                        .map(|spec| spec.src_path)
                })
                .unwrap_or_else(|| path.with_extension("lean"));
            let source = fs::read_to_string(&src_path).ok()?;
            if splitter::source_may_read_host_state(&source)
                || crate::module_builder::source_uses_include_str(&source)
            {
                return None;
            }
            let source_header = crate::module_builder::parse_header_info(&source);
            if source_header.header_error.is_some() {
                return None;
            }
            pending.extend(source_header.imports);
            pending.extend(
                crate::module_builder::read_olean_binary_imports_cached(&path)
                    .ok()?
                    .0
                    .into_iter()
                    .map(|imp| imp.module),
            );
            pins.push((
                import,
                path.clone(),
                blake3::hash(source.as_bytes()).to_hex().to_string(),
                crate::module_builder::compute_olean_artifact_set_digest_with_policy(&path, true)
                    .ok()?,
            ));
        }
        pins.sort();
        let filtered_lean_args = crate::module_builder::filter_allowed_lean_args(lean_args);
        Some(Self {
            toolchain,
            githash,
            compiler,
            dirs,
            filtered_lean_args,
            pins,
        })
    }

    fn fingerprint(&self, project_dir: &Path) -> Option<String> {
        let bytes = serde_json::to_vec(&(
            2u32,
            crate::zygote::ZYGOTE_SCANNER_VERSION,
            crate::zygote::ZYGOTE_REPLAY_VERSION,
            &self.toolchain,
            &self.githash,
            &self.compiler,
            project_dir,
            &self.dirs,
            &self.filtered_lean_args,
            &self.pins,
        ))
        .ok()?;
        Some(blake3::hash(&bytes).to_hex().to_string())
    }
}

/// Whether `path` (resolved for `import` along the search dirs) is exactly the toolchain's own
/// `tc_lib/<rel>.olean`, i.e. the winning search root is `tc_lib` itself (modulo symlinks).
/// A same-githash `Init`/`Std`/`Lean` tree in an earlier `LEAN_PATH` entry nested anywhere
/// under `tc_lib` (e.g. `tc_lib/shadow/Init.olean`) is NOT canonical and must be pinned.
fn is_canonical_toolchain_olean(
    tc_lib: &Path,
    canon_tc_lib: Option<&Path>,
    import: &str,
    path: &Path,
) -> bool {
    let rel = format!(
        "{}.olean",
        crate::module_builder::module_name_to_rel_slash(import)
    );
    if path == tc_lib.join(&rel) {
        return true;
    }
    let Some(canon_tc) = canon_tc_lib else {
        return false;
    };
    let Some(parent) = path.parent().and_then(|p| p.canonicalize().ok()) else {
        return false;
    };
    let Some(file_name) = path.file_name() else {
        return false;
    };
    parent.join(file_name) == canon_tc.join(&rel)
}

fn identity_cache_path(
    probe: &str,
    project_dir: &Path,
    lean_args: &[String],
    env: &HashMap<String, String>,
    min_line: usize,
    max_line: usize,
) -> Option<PathBuf> {
    let ctx = IdentityElaborationContext::compute(probe, project_dir, lean_args, env)?;
    let bytes = serde_json::to_vec(&(
        2u32,
        crate::zygote::ZYGOTE_SCANNER_VERSION,
        crate::zygote::ZYGOTE_REPLAY_VERSION,
        ctx.toolchain,
        ctx.githash,
        ctx.compiler,
        project_dir,
        &ctx.dirs,
        ctx.filtered_lean_args,
        ctx.pins,
        probe,
        min_line,
        max_line,
    ))
    .ok()?;
    let root = crate::shm_cache::ensure_verified_private_staging_dir(Some("decl_identities"))?;
    Some(root.join(format!("{}.json", blake3::hash(&bytes).to_hex())))
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

/// Build the local zygote on the local miss path while preserving the caller's command start `t0`
/// and recording the prewarm duration in the active [`crate::phase_timing::PhaseTimer`].
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
    crate::phase_timing::record_active_phase("zygote_prewarm", || -> Result<()> {
        let (lean_bin, _, _, _) =
            crate::module_builder::resolve_toolchain_compiler(canon_dir, toolchain)?;
        crate::zygote::ensure_zygote_binary(store, &lean_bin, &HashMap::new())?;
        Ok(())
    })?;
    Ok(*t0)
}

/// Confirm the selected source declaration and its canonical kernel statement type in Lean's
/// environment, independently of textual scope tracking. This probe replaces only the proof:
/// false statements must still have an attested identity before Stage-1 can attribute a
/// counterexample, and proof verification must match `kernel_type_hash` in the elaborated kernel
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
    crate::phase_timing::record_active_phase("identity_probe", || {
        confirm_decl_identity_with_extra_dirs(
            src,
            shard,
            project_dir,
            file,
            is_untrusted,
            &[],
            request_started,
        )
    })
}

/// Process-wide memo of coarse-keyed declaration identity results.
///
/// Keyed by [`splitter::declaration_identity_cache_key`] (which commits to the stubbed prefix,
/// target declaration, toolchain, compiler githash, and the full [`IdentityElaborationContext`]
/// fingerprint covering `project_dir`, filtered `leanOptions`, `LEAN_PATH` search dirs, and the
/// transitive imported `.olean`/source closure) plus the full probe env. A repeated
/// `check --decl` that only edits inside a proof body under unchanged elaboration inputs
/// resolves from this memo instead of re-running the stock-`lean` probe.
fn decl_identity_coarse_memo() -> &'static std::sync::Mutex<HashMap<String, ConfirmedDeclIdentity>> {
    static MEMO: std::sync::OnceLock<std::sync::Mutex<HashMap<String, ConfirmedDeclIdentity>>> =
        std::sync::OnceLock::new();
    MEMO.get_or_init(|| std::sync::Mutex::new(HashMap::new()))
}

/// Lookup handle for the coarse declaration-identity cache: where to memoize a fresh result
/// and any identity already resolved for this key.
struct DeclIdentityCoarseLookup {
    memo_key: String,
    disk_path: Option<PathBuf>,
    disk_key: String,
    cached: Option<ConfirmedDeclIdentity>,
}

/// Resolve the coarse cache for one stub-probe identity confirmation: the memory memo first,
/// then the cross-invocation `coarse-<key>.json` entry under the verified private
/// `decl_identities` staging dir. `None` when the coarse cache does not apply (untrusted
/// probes, extra read-only `.olean` dirs, missing env, host-state-reading or `include_str`
/// sources in the probe or any transitive import, or unresolvable toolchain/import closure).
#[allow(clippy::too_many_arguments)]
fn decl_identity_coarse_lookup(
    project_dir: &Path,
    coarse_prefix: &str,
    expected: &str,
    is_untrusted: bool,
    extra_ro_olean_dirs: &[PathBuf],
    lean_args: &[String],
    env: Option<&HashMap<String, String>>,
) -> Option<DeclIdentityCoarseLookup> {
    if is_untrusted || !extra_ro_olean_dirs.is_empty() {
        return None;
    }
    let env = env?;
    let ctx = IdentityElaborationContext::compute(coarse_prefix, project_dir, lean_args, env)?;
    let elab_fingerprint = ctx.fingerprint(project_dir)?;
    let key = splitter::declaration_identity_cache_key(
        coarse_prefix,
        expected,
        &ctx.toolchain,
        &ctx.githash,
        &elab_fingerprint,
    );
    // `key` already commits to `project_dir`, filtered lean args, `LEAN_PATH` dirs, and the
    // transitive imported `.olean`/source closure; pin the remaining env vars in-process as well.
    let mut env_pairs: Vec<(&String, &String)> = env.iter().collect();
    env_pairs.sort();
    let memo_key = format!(
        "{key}\u{0}{}",
        env_pairs
            .iter()
            .map(|(k, v)| format!("{k}={v}"))
            .collect::<Vec<_>>()
            .join("\u{0}"),
    );
    if let Ok(memo) = decl_identity_coarse_memo().lock() {
        if let Some(att) = memo.get(&memo_key) {
            return Some(DeclIdentityCoarseLookup {
                memo_key,
                disk_path: None,
                disk_key: key,
                cached: Some(att.clone()),
            });
        }
    }
    let root = crate::shm_cache::ensure_verified_private_staging_dir(Some("decl_identities"))?;
    let path = root.join(format!("coarse-{key}.json"));
    if let Some(att) = read_coarse_decl_identity_entry(&path, &key) {
        if let Ok(mut memo) = decl_identity_coarse_memo().lock() {
            memo.insert(memo_key.clone(), att.clone());
        }
        return Some(DeclIdentityCoarseLookup {
            memo_key,
            disk_path: None,
            disk_key: key,
            cached: Some(att),
        });
    }
    Some(DeclIdentityCoarseLookup {
        memo_key,
        disk_path: Some(path),
        disk_key: key,
        cached: None,
    })
}

/// Read and validate one coarse entry
/// (`{"v":2,"key":...,"decl_name":...,"kernel_type_hash":...}`), opened fail-closed through
/// `read_verified_isolated_artifact` and refused unless it echoes the key it was filed under.
fn read_coarse_decl_identity_entry(path: &Path, key: &str) -> Option<ConfirmedDeclIdentity> {
    let bytes = read_verified_isolated_artifact(path).ok()?;
    let val: serde_json::Value = serde_json::from_slice(&bytes).ok()?;
    if val.get("v")?.as_u64()? != 2 || val.get("key")?.as_str()? != key {
        return None;
    }
    Some(ConfirmedDeclIdentity {
        decl_name: val.get("decl_name")?.as_str()?.to_string(),
        kernel_type_hash: val.get("kernel_type_hash")?.as_str()?.to_string(),
    })
}

/// Persist one confirmed identity under its coarse key (best-effort: a failed write only costs
/// the next run its probe) and memoize it for the remainder of this process.
fn store_coarse_decl_identity(lookup: &DeclIdentityCoarseLookup, att: &ConfirmedDeclIdentity) {
    if let Ok(mut memo) = decl_identity_coarse_memo().lock() {
        memo.insert(lookup.memo_key.clone(), att.clone());
    }
    if let Some(path) = &lookup.disk_path {
        if let Ok(bytes) = serde_json::to_vec(&serde_json::json!({
            "v": 2,
            "key": lookup.disk_key,
            "decl_name": att.decl_name,
            "kernel_type_hash": att.kernel_type_hash,
        })) {
            let _ = crate::shm_cache::atomic_write_shm(path, &bytes);
        }
    }
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
    // Coarse cache: the probe prefix (header + suppression options + stubbed earlier
    // declarations + this signature) is invariant under edits inside a proof body, so repeated
    // confirmations of the same declaration under the same toolchain resolve from the memo or
    // the cross-invocation coarse entry without compiling a fresh probe. Only stub successes
    // are cached: the full-declaration fallback depends on the proof text.
    let coarse = decl_identity_coarse_lookup(
        project_dir,
        &format!("{before}{signature}"),
        expected,
        is_untrusted,
        extra_ro_olean_dirs,
        &lean_args,
        env.as_ref(),
    );
    let stub_attempt = match coarse.as_ref().and_then(|c| c.cached.clone()) {
        Some(att) => Ok(att),
        None => compile_and_read_probe_identities(
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
        .and_then(|decls| match_expected_decl_identity(expected, &decls, None))
        .inspect(|att| {
            if let Some(c) = coarse.as_ref() {
                store_coarse_decl_identity(c, att);
            }
        }),
    };
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
    crate::phase_timing::record_active_phase("identity_probe", || {
        confirm_file_decl_identities_with_extra_dirs(
            src,
            shards,
            project_dir,
            file,
            is_untrusted,
            &[],
            request_started,
        )
    })
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

#[cfg(test)]
mod memo_tests {
    use super::*;

    /// The coarse cache must let a repeated confirmation of the same declaration resolve from
    /// the memo without compiling a probe: this is the `check --decl` loop that edits inside a
    /// proof body and re-runs the seconds-long stock-`lean` probe today. A sentinel identity is
    /// seeded under exactly the lookup key the confirmation computes, so the probe could not
    /// have run and still returned it.
    #[test]
    fn coarse_memo_serves_stub_identity_without_compiling() {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_coarse_memo_{}",
            crate::pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        let file = dir.join("M.lean");
        let src = "theorem t1 : True := True.intro\ntheorem target : True := True.intro\n";
        let split = splitter::split_lean_source(src, &[]);
        let shard = &split.shards[1];
        assert_eq!(shard.name, "target");
        let prefix = splitter::declaration_identity_prefix(src, shard);
        let header_info = crate::module_builder::parse_header_info(&prefix);
        let (header, prefix_body) = prefix.split_at(header_info.body_byte_offset);
        let (signature, _) = splitter::extract_shard_stmt_and_proof(src, shard);
        let before = format!(
            "{header}\nset_option warningAsError false\nset_option warn.sorry false\n{prefix_body}\nset_option warningAsError false\nset_option warn.sorry false\n"
        );
        let (lean_args, env) =
            resolve_identity_probe_context(&dir, &file, false, &[]).expect("probe context");
        let lookup = decl_identity_coarse_lookup(
            &dir,
            &format!("{before}{signature}"),
            "target",
            false,
            &[],
            &lean_args,
            env.as_ref(),
        )
        .expect("coarse lookup");
        assert!(lookup.cached.is_none(), "fresh key must miss");
        let sentinel = ConfirmedDeclIdentity {
            decl_name: "target".into(),
            kernel_type_hash: "sentinel-coarse-hash".into(),
        };
        decl_identity_coarse_memo()
            .lock()
            .unwrap()
            .insert(lookup.memo_key.clone(), sentinel.clone());
        let attested = confirm_decl_identity(src, shard, &dir, &file).expect("confirmed");
        assert_eq!(attested, sentinel, "memo hit must serve the seeded identity");
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn coarse_cache_invalidates_on_dependency_options_lean_path_and_project_dir() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = crate::worktree_test_support::LakeTree::new(
            "coarse_identity_invalidation",
            &[
                ("P/Leaf.lean", "def leaf : Nat := 1\n"),
                ("P/Middle.lean", "import P.Leaf\ndef middle := leaf\n"),
            ],
        )?;
        let lib_dir = tree
            .project
            .join(".lake/build/lib/lean")
            .to_string_lossy()
            .into_owned();
        let env = HashMap::from([("LEAN_PATH".into(), lib_dir.clone())]);
        let coarse_prefix = "import P.Middle\nset_option warningAsError false\nset_option warn.sorry false\ntheorem target : middle = 1";
        let base = decl_identity_coarse_lookup(
            &tree.project,
            coarse_prefix,
            "target",
            false,
            &[],
            &[],
            Some(&env),
        )
        .expect("pure imported probe must yield a coarse cache lookup");
        assert!(base.cached.is_none(), "fresh key must miss");

        // Persist an entry to disk, clear the in-process memo, and confirm disk hit works
        // only when all elaboration inputs match.
        let sentinel = ConfirmedDeclIdentity {
            decl_name: "target".into(),
            kernel_type_hash: "0".repeat(64),
        };
        store_coarse_decl_identity(&base, &sentinel);
        decl_identity_coarse_memo().lock().unwrap().clear();
        let disk_hit = decl_identity_coarse_lookup(
            &tree.project,
            coarse_prefix,
            "target",
            false,
            &[],
            &[],
            Some(&env),
        )
        .expect("disk hit lookup");
        assert_eq!(
            disk_hit.cached.as_ref(),
            Some(&sentinel),
            "unchanged elaboration inputs must hit the persisted coarse entry"
        );
        assert_eq!(disk_hit.disk_key, base.disk_key);

        // 1. Changing effective leanOptions (`lean_args`) must invalidate the disk key.
        decl_identity_coarse_memo().lock().unwrap().clear();
        let opts_lookup = decl_identity_coarse_lookup(
            &tree.project,
            coarse_prefix,
            "target",
            false,
            &[],
            &["-DmaxRecDepth=2048".into()],
            Some(&env),
        )
        .expect("lookup with different lean_args");
        assert_ne!(
            opts_lookup.disk_key, base.disk_key,
            "changing leanOptions must change the coarse disk key"
        );
        assert!(
            opts_lookup.cached.is_none(),
            "changing leanOptions must miss the coarse disk cache"
        );

        // 2. Changing LEAN_PATH must invalidate the disk key.
        let extra_dir = tree.project.join("extra_lib");
        fs::create_dir_all(&extra_dir)?;
        let env_alt_lp = HashMap::from([(
            "LEAN_PATH".into(),
            format!("{}:{}", extra_dir.display(), lib_dir),
        )]);
        let lp_lookup = decl_identity_coarse_lookup(
            &tree.project,
            coarse_prefix,
            "target",
            false,
            &[],
            &[],
            Some(&env_alt_lp),
        )
        .expect("lookup with different LEAN_PATH");
        assert_ne!(
            lp_lookup.disk_key, base.disk_key,
            "changing LEAN_PATH must change the coarse disk key"
        );
        assert!(lp_lookup.cached.is_none());

        // 3. Changing project_dir must invalidate the disk key.
        let other_dir = std::env::temp_dir().join(format!(
            "turbo_coarse_other_proj_{}",
            crate::pack::next_tmp_id()
        ));
        fs::create_dir_all(&other_dir)?;
        fs::write(other_dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        let other_proj_lookup = decl_identity_coarse_lookup(
            &other_dir,
            "theorem target : True",
            "target",
            false,
            &[],
            &[],
            Some(&env),
        )
        .expect("lookup in other project_dir");
        let same_src_orig_proj = decl_identity_coarse_lookup(
            &tree.project,
            "theorem target : True",
            "target",
            false,
            &[],
            &[],
            Some(&env),
        )
        .expect("lookup in original project_dir");
        assert_ne!(
            other_proj_lookup.disk_key, same_src_orig_proj.disk_key,
            "changing project_dir must change the coarse disk key"
        );
        let _ = fs::remove_dir_all(&other_dir);

        // 4. Modifying a transitive dependency's `.lean` source must invalidate the disk key.
        let leaf = tree.project.join("P/Leaf.lean");
        fs::write(&leaf, "def leaf : Nat := 2\n")?;
        let dep_src_lookup = decl_identity_coarse_lookup(
            &tree.project,
            coarse_prefix,
            "target",
            false,
            &[],
            &[],
            Some(&env),
        )
        .expect("lookup after dependency source edit");
        assert_ne!(
            dep_src_lookup.disk_key, base.disk_key,
            "editing an imported dependency source must change the coarse disk key"
        );
        assert!(dep_src_lookup.cached.is_none());

        // 5. Modifying a transitive dependency's `.olean` artifact must invalidate the disk key.
        let leaf_olean = tree.project.join(".lake/build/lib/lean/P/Leaf.olean");
        let mut bytes = fs::read(&leaf_olean)?;
        bytes.push(0);
        fs::write(&leaf_olean, bytes)?;
        let dep_olean_lookup = decl_identity_coarse_lookup(
            &tree.project,
            coarse_prefix,
            "target",
            false,
            &[],
            &[],
            Some(&env),
        )
        .expect("lookup after dependency .olean edit");
        assert_ne!(
            dep_olean_lookup.disk_key, dep_src_lookup.disk_key,
            "modifying an imported dependency .olean must change the coarse disk key"
        );
        assert!(dep_olean_lookup.cached.is_none());

        if let Some(p) = base.disk_path {
            let _ = fs::remove_file(p);
        }
        Ok(())
    }

    /// A same-githash `Init` tree shadowing the toolchain from an earlier `LEAN_PATH` entry
    /// (here nested under `tc_lib`, so `is_verified_toolchain_olean_file` alone accepts it) must
    /// be pinned: mutating the shadowed `Init.olean` must change the coarse cache key.
    #[test]
    fn coarse_key_pins_shadowed_toolchain_init_on_lean_path() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let scratch = PrivateScratchDir::create(
            &verified_private_temp_scratch_base()?,
            "identity_shadow_init",
        )?;
        let root = scratch.path.clone();
        let project = root.join("proj");
        let tc_lib = root.join("tc/lib/lean");
        let shadow = tc_lib.join("shadow");
        fs::create_dir_all(&project)?;
        fs::create_dir_all(&shadow)?;
        fs::write(project.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        let init_src = "prelude\n";
        for dir in [&tc_lib, &shadow] {
            fs::write(dir.join("Init.lean"), init_src)?;
            let output = Command::new("lean")
                .args(["-o", "Init.olean", "Init.lean"])
                .current_dir(dir)
                .output()?;
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        let (_, githash) = crate::module_builder::read_olean_header_version_and_githash(
            &tc_lib.join("Init.olean"),
        )
        .expect("compiled Init.olean header");
        let shadow_olean = shadow.join("Init.olean");
        assert!(
            crate::module_builder::is_verified_toolchain_olean_file(
                &tc_lib,
                Some(&githash),
                &shadow_olean
            ),
            "precondition: nested same-githash shadow passes the toolchain-file check"
        );
        let probe = "theorem target : True";
        let key_for = |env: &HashMap<String, String>| -> (Vec<PathBuf>, String) {
            let ctx = IdentityElaborationContext::compute_with_toolchain(
                probe,
                &project,
                &[],
                env,
                "leanprover/lean4:v4.35.0".into(),
                PathBuf::from("/nonexistent/lean"),
                githash.clone(),
                &tc_lib,
            )
            .expect("pure prelude-only context");
            let fp = ctx.fingerprint(&project).expect("fingerprint");
            let key = splitter::declaration_identity_cache_key(
                probe,
                "target",
                &ctx.toolchain,
                &ctx.githash,
                &fp,
            );
            (ctx.pins.iter().map(|p| p.1.clone()).collect(), key)
        };

        // Canonical toolchain `Init` stays unpinned.
        let (pins, _) = key_for(&HashMap::new());
        assert!(
            pins.is_empty(),
            "canonical toolchain Init must not be pinned: {pins:?}"
        );

        // Shadowed `Init` earlier on `LEAN_PATH` is pinned and its bytes drive the key.
        let env = HashMap::from([("LEAN_PATH".into(), shadow.to_string_lossy().into_owned())]);
        let (pins, before) = key_for(&env);
        assert_eq!(
            pins,
            vec![shadow_olean.clone()],
            "shadowed Init must be pinned"
        );
        let mut bytes = fs::read(&shadow_olean)?;
        bytes.push(0);
        fs::write(&shadow_olean, bytes)?;
        let (_, after) = key_for(&env);
        assert_ne!(
            before, after,
            "mutating a shadowed Init.olean on LEAN_PATH must invalidate the coarse key"
        );
        scratch.remove()?;
        Ok(())
    }

    #[test]
    fn coarse_cache_bypasses_host_state_and_include_str_sources() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = crate::worktree_test_support::LakeTree::new(
            "coarse_identity_host_bypass",
            &[
                ("P/Leaf.lean", "def leaf : Nat := 1\n"),
                ("P/Middle.lean", "import P.Leaf\ndef middle := leaf\n"),
                ("P/data.txt", "hello"),
            ],
        )?;
        let env = HashMap::from([(
            "LEAN_PATH".into(),
            tree.project
                .join(".lake/build/lib/lean")
                .to_string_lossy()
                .into_owned(),
        )]);

        // Direct host-state read (`IO.getEnv`) and `include_str`/`include_bin` in the probe
        // prefix must bypass the coarse cache completely (return `None` -> neither read nor write).
        for direct_prefix in [
            "initialize nonce : Option String ← IO.getEnv \"SECRET\"\ntheorem target : True",
            "def embedded : String := include_str \"P/data.txt\"\ntheorem target : True",
            "def embedded : ByteArray := include_bin \"P/data.txt\"\ntheorem target : True",
        ] {
            assert!(
                decl_identity_coarse_lookup(
                    &tree.project,
                    direct_prefix,
                    "target",
                    false,
                    &[],
                    &[],
                    Some(&env),
                )
                .is_none(),
                "coarse cache must bypass direct host-effect/include source: {direct_prefix}"
            );
        }

        // Transitive host-state read or `include_str` in an imported dependency must also bypass.
        let imported_prefix = "import P.Middle\ntheorem target : middle = 1";
        assert!(
            decl_identity_coarse_lookup(
                &tree.project,
                imported_prefix,
                "target",
                false,
                &[],
                &[],
                Some(&env),
            )
            .is_some(),
            "baseline pure transitive import must be cacheable"
        );
        let leaf = tree.project.join("P/Leaf.lean");
        for dep_source in [
            "initialize nonce : Option String ← IO.getEnv \"SECRET\"\ndef leaf : Nat := 1\n",
            "def embedded := include_str \"data.txt\"\ndef leaf : Nat := 1\n",
        ] {
            fs::write(&leaf, dep_source)?;
            assert!(
                decl_identity_coarse_lookup(
                    &tree.project,
                    imported_prefix,
                    "target",
                    false,
                    &[],
                    &[],
                    Some(&env),
                )
                .is_none(),
                "coarse cache must bypass transitive host-effect/include import: {dep_source}"
            );
        }

        // Missing dependency source must also fail closed (`None`).
        fs::remove_file(&leaf)?;
        assert!(
            decl_identity_coarse_lookup(
                &tree.project,
                imported_prefix,
                "target",
                false,
                &[],
                &[],
                Some(&env),
            )
            .is_none(),
            "coarse cache must fail closed when a non-toolchain import source is missing"
        );
        Ok(())
    }

    #[test]
    fn identity_memo_rejects_transitive_host_inputs() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = crate::worktree_test_support::LakeTree::new(
            "identity_transitive_inputs",
            &[
                ("P/Leaf.lean", "def leaf : Nat := 1\n"),
                ("P/Middle.lean", "import P.Leaf\ndef middle := leaf\n"),
                ("P/data.txt", "first"),
            ],
        )?;
        let mut env = HashMap::from([(
            "LEAN_PATH".into(),
            tree.project
                .join(".lake/build/lib/lean")
                .to_string_lossy()
                .into_owned(),
        )]);
        let probe = "import P.Middle\ntheorem target : middle = 1 := rfl\n";
        let key = identity_cache_path(probe, &tree.project, &[], &env, 2, 2).unwrap();
        let leaf = tree.project.join("P/Leaf.lean");
        for source in [
            "initialize nonce : Option String ← IO.getEnv \"IDENTITY_TEST_NONCE\"\ndef leaf : Nat := 1\n",
            "def embedded := include_str \"data.txt\"\ndef leaf : Nat := 1\n",
        ] {
            fs::write(&leaf, source)?;
            for value in ["first", "second"] {
                env.insert("IDENTITY_TEST_NONCE".into(), value.into());
                fs::write(tree.project.join("P/data.txt"), value)?;
                assert!(
                    identity_cache_path(probe, &tree.project, &[], &env, 2, 2).is_none(),
                    "transitive input must bypass identity memo: {source}, {value}",
                );
            }
        }
        fs::write(&leaf, "def leaf : Nat := 2\n")?;
        assert_ne!(
            Some(key),
            identity_cache_path(probe, &tree.project, &[], &env, 2, 2)
        );
        let pure_key = identity_cache_path(probe, &tree.project, &[], &env, 2, 2).unwrap();
        let artifact = tree.project.join(".lake/build/lib/lean/P/Leaf.olean");
        let mut bytes = fs::read(&artifact)?;
        bytes.push(0);
        fs::write(&artifact, bytes)?;
        assert_ne!(
            Some(pure_key),
            identity_cache_path(probe, &tree.project, &[], &env, 2, 2),
        );
        fs::remove_file(&leaf)?;
        assert!(identity_cache_path(probe, &tree.project, &[], &env, 2, 2).is_none());
        assert!(identity_cache_path(
            "def embedded := include_str \"P/data.txt\"\n",
            &tree.project,
            &[],
            &env,
            1,
            1,
        )
        .is_none());
        Ok(())
    }

    #[test]
    fn identity_memo_separates_probe_context_and_rejects_missing_imports() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let scratch = PrivateScratchDir::create(
            &verified_private_temp_scratch_base()?,
            "identity_memo_test",
        )?;
        let dir = scratch.path.clone();
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        let env = HashMap::new();
        let probe = "theorem memoIdentity : True := by trivial\n";
        let key = identity_cache_path(probe, &dir, &[], &env, 1, 1).expect("cache key");
        assert_eq!(
            Some(key.clone()),
            identity_cache_path(probe, &dir, &[], &env, 1, 1)
        );
        assert_ne!(
            Some(key.clone()),
            identity_cache_path(probe, &dir, &[], &env, 1, 2)
        );
        assert_ne!(
            Some(key.clone()),
            identity_cache_path(
                "theorem memoIdentity : False := by sorry\n",
                &dir,
                &[],
                &env,
                1,
                1
            )
        );
        assert_ne!(
            Some(key),
            identity_cache_path(probe, &dir, &["-DmaxRecDepth=2048".into()], &env, 1, 1)
        );
        assert!(
            identity_cache_path("import MissingIdentityImport\n", &dir, &[], &env, 1, 1).is_none()
        );
        assert!(identity_cache_path(
            "initialize x ← IO.getEnv \"MEMO_TEST\"\n",
            &dir,
            &[],
            &env,
            1,
            1
        )
        .is_none());
        let first = compile_and_read_probe_identities(
            probe,
            &dir,
            false,
            &[],
            Some(&env),
            &[],
            1,
            1,
            Instant::now(),
        )?;
        let second = compile_and_read_probe_identities(
            probe,
            &dir,
            false,
            &[],
            Some(&env),
            &[],
            1,
            1,
            Instant::now(),
        )?;
        assert_eq!(first.len(), 1);
        assert_eq!(first[0].decl_name, second[0].decl_name);
        assert_eq!(first[0].kernel_type_hash, second[0].kernel_type_hash);
        let import_path = dir.join("MemoImport.olean");
        fs::write(dir.join("MemoImport.lean"), "def memoValue : Nat := 1\n")?;
        let output = std::process::Command::new("lean")
            .args(["-o", "MemoImport.olean", "MemoImport.lean"])
            .current_dir(&dir)
            .output()?;
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let env = HashMap::from([("LEAN_PATH".into(), dir.to_string_lossy().into_owned())]);
        let imported_probe = format!("import MemoImport\n{probe}");
        let old_key =
            identity_cache_path(&imported_probe, &dir, &[], &env, 2, 2).expect("import memo key");
        fs::write(&old_key, b"[]")?;
        let mut bytes = fs::read(&import_path)?;
        bytes.push(0);
        fs::write(&import_path, bytes)?;
        let new_key = identity_cache_path(&imported_probe, &dir, &[], &env, 2, 2)
            .expect("changed import memo key");
        assert_ne!(old_key, new_key);
        assert!(
            !new_key.exists(),
            "changed import must miss the old memo entry"
        );
        fs::remove_file(old_key)?;
        scratch.remove()?;
        Ok(())
    }
}
