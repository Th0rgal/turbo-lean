use crate::db::TurboStore;
use crate::pack::next_tmp_id;
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use super::*;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub(crate) struct ZygoteAuditModulesReply {
    pub ok: bool,
    #[serde(default)]
    pub audited: Option<Vec<String>>,
    #[serde(default)]
    pub violations: Vec<String>,
    #[serde(default)]
    pub csimp_entries: Vec<(String, String, String)>,
    /// `--shard` mode: the module's non-stub theorems, read from the kernel environment.
    #[serde(default)]
    pub decls: Option<Vec<String>>,
    /// `--shard` mode: newly declared non-stub theorems mapped to `statement-v1` kernel type hash.
    #[serde(default)]
    pub decl_types: Option<std::collections::BTreeMap<String, String>>,
    #[serde(default)]
    pub used_sorry: bool,
    #[serde(default)]
    pub sorry_decls: Vec<String>,
}

/// Verify that every expected `(decl_name, expected_kernel_type_hash)` pair was elaborated in the
/// kernel environment (matching exact declaration name or namespace-scoped `_turbo_verify_<n>_`
/// fast-verify wrapper) AND its canonical `statement-v1` kernel type hash matches `expected_hash`.
pub(crate) fn verify_attested_decl_types(
    got_decl_types: &std::collections::BTreeMap<String, String>,
    expected: &[(String, String)],
) -> Result<()> {
    for (exp_name, exp_hash) in expected {
        let mut saw_name = false;
        let mut matched_hash = false;
        let mut mismatched_got = None;
        for (got_name, got_hash) in got_decl_types {
            if crate::splitter::matches_attested_decl_or_fast_verify(got_name, exp_name) {
                saw_name = true;
                if got_hash == exp_hash {
                    matched_hash = true;
                    break;
                }
                mismatched_got = Some((got_name.as_str(), got_hash.as_str()));
            }
        }
        if !saw_name {
            anyhow::bail!(
                "[TurboLean.KernelGate] attested theorem `{}` missing from elaborated kernel environment (got {:?})",
                exp_name,
                got_decl_types.keys().collect::<Vec<_>>()
            );
        }
        if !matched_hash {
            let (got_name, got_hash) = mismatched_got.unwrap_or(("", ""));
            anyhow::bail!(
                "[TurboLean.KernelGate] kernel statement type mismatch for `{}` (elaborated as `{}` with hash `{}`, expected attested hash `{}`)",
                exp_name,
                got_name,
                got_hash,
                exp_hash
            );
        }
    }
    Ok(())
}

pub(crate) struct PinnedFfiPackage {
    pub name: &'static str,
    pub url: &'static str,
    pub rev: &'static str,
    pub module: &'static str,
    pub rel_src: &'static str,
    pub src_sha256: &'static str,
    pub decls: &'static [(&'static str, &'static str)],
}

pub(crate) const PINNED_FFI_PACKAGES: &[PinnedFfiPackage] = &[
    PinnedFfiPackage {
        name: "lean-sys",
        url: "https://github.com/Th0rgal/lean-sys.git",
        rev: "077775ba387f1eeb2976cb8763b4633b8d5ce313",
        module: "LeanSys.Posix",
        rel_src: "LeanSys/Posix.lean",
        src_sha256: "35aacd3f54a985e2365de92eea17d167a2945538c0533cebf2a44338936ce2d8",
        decls: &[
            ("LeanSys.Posix.rawOpenFlock", "leansys_open_flock"),
            ("LeanSys.Posix.rawFsCloneOrLink", "leansys_fs_clone_or_link"),
            ("LeanSys.Posix.rawWriteAll", "leansys_write_all"),
            ("LeanSys.Posix.rawPreadBa", "leansys_pread_ba"),
            ("LeanSys.Posix.rawSpawnGroup", "leansys_spawn_group"),
            ("LeanSys.Posix.rawKillWaitGroup", "leansys_kill_wait_group"),
            ("LeanSys.Posix.rawNetListen", "leansys_net_listen"),
            ("LeanSys.Posix.rawNetAcceptPoll", "leansys_net_accept_poll"),
        ],
    },
    PinnedFfiPackage {
        name: "evmyul",
        url: "https://github.com/lfglabs-dev/EVMYulLean.git",
        rev: "a132798069be50e8b03f88d6a96f2618c128ae7f",
        module: "EvmYul.FFI.ffi",
        rel_src: "EvmYul/FFI/ffi.lean",
        src_sha256: "c0b6b455399a476fd3c5be3fd3e1df5788a112dd92b520397512d073b6317562",
        decls: &[
            ("ffi.sha256", "sha256"),
            ("ffi.BLAKE2Compress", "blake2compressb64"),
            ("ffi.ByteArray.zeroes", "memset_zero"),
            ("ffi.keccak256", "keccak256"),
        ],
    },
];

pub(crate) fn pinned_ffi_allow_args(
    cfg: &crate::module_builder::ProjectConfig,
    mod_names: &[String],
) -> Vec<String> {
    use sha2::Digest;
    let mut out = Vec::new();
    let root = cfg
        .root_pkg
        .pkg_root
        .canonicalize()
        .unwrap_or_else(|_| cfg.root_pkg.pkg_root.clone());
    for pin in PINNED_FFI_PACKAGES {
        if !mod_names.iter().any(|m| m == pin.module) {
            continue;
        }
        let Some(mp) = cfg.manifest_packages.iter().find(|mp| {
            mp.name == pin.name
                && mp.pkg_type == "git"
                && mp.rev.as_deref() == Some(pin.rev)
                && mp.url.as_deref() == Some(pin.url)
        }) else {
            continue;
        };
        let Ok(dir) = mp.dir.canonicalize() else {
            continue;
        };
        if dir == root
            || !cfg
                .dep_pkgs
                .iter()
                .any(|d| d.pkg_root.canonicalize().ok().as_deref() == Some(dir.as_path()))
        {
            continue;
        }
        let root_src = cfg.root_pkg.pkg_root.join(&cfg.root_pkg.src_dir);
        if fs::symlink_metadata(root_src.join(pin.rel_src)).is_ok()
            || fs::symlink_metadata(cfg.root_pkg.pkg_root.join(pin.rel_src)).is_ok()
        {
            continue;
        }
        let src_path = dir.join(pin.rel_src);
        let src_ok = fs::symlink_metadata(&src_path)
            .map(|m| m.file_type().is_file())
            .unwrap_or(false)
            && fs::read(&src_path)
                .map(|b| format!("{:x}", sha2::Sha256::digest(&b)) == pin.src_sha256)
                .unwrap_or(false);
        if !src_ok {
            continue;
        }
        for (decl, sym) in pin.decls {
            out.push(format!("--ffi-allow={}={}={}", pin.module, decl, sym));
        }
    }
    out.extend(project_ffi_allow_args(mod_names));
    out
}

/// Project-declared FFI from `turbo-lean.toml` (`[ffi] allow = ["Module=decl=c_symbol"]`), limited
/// to `mod_names`. The worker still requires each entry to be a safe `@[extern]` opaque defined in
/// that exact module and bound to that exact C symbol, so an entry cannot admit anything broader.
pub(crate) fn project_ffi_allow_args(mod_names: &[String]) -> Vec<String> {
    parse_project_ffi_allow(
        &std::env::var("TURBO_LEAN_ALLOWED_FFI").unwrap_or_default(),
        mod_names,
    )
}

pub(super) fn parse_project_ffi_allow(raw: &str, mod_names: &[String]) -> Vec<String> {
    raw.split(',')
        .map(str::trim)
        .filter_map(|entry| {
            let mut parts = entry.split('=');
            let (m, d, s) = (parts.next()?, parts.next()?, parts.next()?);
            (parts.next().is_none()
                && ![m, d, s].iter().any(|p| p.is_empty())
                && mod_names.iter().any(|n| n == m))
            .then(|| format!("--ffi-allow={m}={d}={s}"))
        })
        .collect()
}

pub(super) fn audit_batch_size() -> usize {
    std::env::var("TURBO_LEAN_AUDIT_BATCH_SIZE")
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .filter(|&v| v > 0)
        .unwrap_or(8)
}

/// Materialize an immutable `ClosureSnapshot` over `mod_names` (and their full transitive
/// non-toolchain `.olean` closure) so multi-phase kernel replay, `--skip-child-replay` policy
/// audit, and `TurboStore` authority recording all read the exact same sealed snapshot bytes.
pub(crate) fn materialize_bound_audit_closure(
    cfg: &crate::module_builder::ProjectConfig,
    mod_names: &[String],
    lean_path_env: &str,
) -> Result<ClosureSnapshot> {
    let tc_opt = (!cfg.toolchain_lib_lean.as_os_str().is_empty())
        .then_some(cfg.toolchain_lib_lean.as_path());
    let csv = mod_names.join(",");
    let mut snap = ClosureSnapshot::take(&csv, lean_path_env, tc_opt);
    snap.materialize(tc_opt);
    anyhow::ensure!(
        snap.materialized.is_some() && snap.binding() == ClosureBinding::Bound,
        "Failed to bind immutable `.olean` closure snapshot across kernel replay/audit phases (concurrent artifact mutation or incomplete closure): fail-closed"
    );
    Ok(snap)
}

pub(crate) fn ensure_bound_audit_closure(
    snap: &ClosureSnapshot,
    phase: &'static str,
) -> Result<(String, PathBuf)> {
    run_digest_test_hook(phase);
    let Some(ref mat) = snap.materialized else {
        anyhow::bail!(
            "Immutable `.olean` closure snapshot missing materialized directory before `{}`: fail-closed",
            phase
        );
    };
    anyhow::ensure!(
        snap.binding() == ClosureBinding::Bound,
        "Immutable `.olean` closure snapshot lost binding before `{}`: fail-closed",
        phase
    );
    Ok((mat.search_path.clone(), mat.dir.clone()))
}

pub(crate) fn snapshot_parent_search_path(snap: &ClosureSnapshot) -> Option<String> {
    let mat = snap.materialized.as_ref()?;
    #[cfg(target_os = "linux")]
    {
        use std::os::unix::io::AsRawFd;
        let fd_root = format!("/proc/self/fd/{}", mat.dir_fd.as_raw_fd());
        Some(match &mat.toolchain_lib {
            Some(t) => format!("{fd_root}:{}", t.display()),
            None => fd_root,
        })
    }
    #[cfg(not(target_os = "linux"))]
    {
        Some(mat.search_path.clone())
    }
}

#[cfg(target_os = "linux")]
pub(crate) fn snapshot_pinned_dir_raw_fd(
    snap: &ClosureSnapshot,
) -> Option<std::os::unix::io::RawFd> {
    use std::os::unix::io::AsRawFd;
    snap.materialized.as_ref().map(|m| m.dir_fd.as_raw_fd())
}

#[cfg(not(target_os = "linux"))]
pub(crate) fn snapshot_pinned_dir_raw_fd(_snap: &ClosureSnapshot) -> Option<i32> {
    None
}

pub(crate) fn ensure_live_closure_matches_snapshot(
    snap: &ClosureSnapshot,
    phase: &'static str,
) -> Result<()> {
    let _ = ensure_bound_audit_closure(snap, phase)?;
    anyhow::ensure!(
        snap.rebind() != ClosureBinding::Changed,
        "Caller live `.olean` closure mutated or swapped during `{}` relative to verified closure snapshot: fail-closed",
        phase
    );
    Ok(())
}

pub(crate) fn snapshot_module_artifact_set_digest(
    snap: &ClosureSnapshot,
    mod_name: &str,
) -> Option<String> {
    let (_, entry) = snap.entries.get(mod_name)?.as_ref()?;
    let mut h = blake3::Hasher::new();
    h.update(b"olean-art-v2\n");
    let main_hex = entry.hashes[0].as_deref()?;
    let mut main_bytes = [0u8; 32];
    for (i, b) in main_bytes.iter_mut().enumerate() {
        *b = u8::from_str_radix(main_hex.get(i * 2..i * 2 + 2)?, 16).ok()?;
    }
    h.update(&(5u64).to_le_bytes());
    h.update(b"olean");
    h.update(&(32u64).to_le_bytes());
    h.update(&main_bytes);
    // `OleanEntryDigest::hashes` order: [0]=olean, [1]=srv, [2]=priv, [3]=ilean, [4]=ir_sig, [5]=ir.
    // `olean_artifact_paths` order:     [0]=olean, [1]=srv, [2]=priv, [3]=ilean, [4]=ir,     [5]=ir_sig.
    for (tag, hash_idx) in [
        ("srv", 1usize),
        ("priv", 2),
        ("ilean", 3),
        ("ir", 5),
        ("ir_sig", 4),
    ] {
        match entry.hashes[hash_idx].as_deref() {
            Some(hex) => {
                let mut hb = [0u8; 32];
                for (i, b) in hb.iter_mut().enumerate() {
                    *b = u8::from_str_radix(hex.get(i * 2..i * 2 + 2)?, 16).ok()?;
                }
                h.update(&[1u8]);
                h.update(&(tag.len() as u64).to_le_bytes());
                h.update(tag.as_bytes());
                h.update(&(32u64).to_le_bytes());
                h.update(&hb);
            }
            None => {
                h.update(&[0u8]);
                h.update(&(tag.len() as u64).to_le_bytes());
                h.update(tag.as_bytes());
                h.update(&(0u64).to_le_bytes());
            }
        }
    }
    Some(h.finalize().to_hex().to_string())
}

pub(crate) fn validate_untrusted_audit_caller_paths(
    cfg: &crate::module_builder::ProjectConfig,
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
) -> Result<()> {
    let tc_prefix = cfg
        .toolchain_lib
        .parent()
        .filter(|p| p.is_dir() && p.is_absolute() && *p != Path::new("/"))
        .ok_or_else(|| {
            anyhow::anyhow!(
                "Invalid toolchain prefix `{}` for bubblewrap sandbox: fail-closed sandbox gate",
                cfg.toolchain_lib.display()
            )
        })?;
    let bootstrap_env = build_auditor_bootstrap_env(cfg);
    let auditor_ld_library_path = bootstrap_env
        .get("LD_LIBRARY_PATH")
        .map(String::as_str)
        .unwrap_or("");
    if extra_ro_binds.is_empty() {
        crate::module_builder::validate_untrusted_sandbox_search_paths(
            cfg,
            tc_prefix,
            lean_path_env,
            auditor_ld_library_path,
        )?;
    }
    Ok(())
}

pub(crate) fn record_snapshot_modules_in_store(
    store: &TurboStore,
    cfg: &crate::module_builder::ProjectConfig,
    snap: &ClosureSnapshot,
    replayed_mods: &[String],
    audited_mods: &[String],
    live_lean_path_env: &str,
    extra_root_lib: Option<&Path>,
) -> Result<()> {
    let (snap_lp, _) = ensure_bound_audit_closure(snap, "audit_record_authority")?;
    let parent_snap_lp = snapshot_parent_search_path(snap).unwrap_or(snap_lp);
    let live_batch = crate::module_builder::ReplayLookupBatchCache::new_with_extra_root_lib(
        store,
        cfg,
        live_lean_path_env,
        extra_root_lib,
    );
    let mut snap_batch = crate::module_builder::ReplayLookupBatchCache::new_with_extra_root_lib(
        store,
        cfg,
        &parent_snap_lp,
        extra_root_lib,
    );
    fn resolve_binds_policy(
        snap: &ClosureSnapshot,
        snap_batch: &mut crate::module_builder::ReplayLookupBatchCache,
        live_batch: &crate::module_builder::ReplayLookupBatchCache,
        m: &str,
    ) -> Result<(PathBuf, bool)> {
        let Some(snap_olean) = snap_batch.resolve_module_olean(m) else {
            anyhow::bail!(
                "Verified module `{}` missing `.olean` in bound closure snapshot: fail-closed",
                m
            );
        };
        let Some((ref orig_olean, _)) = snap.entries.get(m).and_then(|e| e.as_ref()) else {
            anyhow::bail!(
                "Verified module `{}` missing origin entry in bound closure snapshot: fail-closed",
                m
            );
        };
        Ok((snap_olean, live_batch.is_root_module_olean(orig_olean)))
    }
    for m in replayed_mods {
        let (snap_olean, binds_policy) =
            resolve_binds_policy(snap, &mut snap_batch, &live_batch, m)?;
        let dig = crate::module_builder::compute_replayed_olean_ilean_digest(&snap_olean)
            .with_context(|| {
                format!(
                    "Failed to compute snapshot `.olean`+`.ilean` digest for `{}`",
                    m
                )
            })?;
        let env_dig = snap_batch
            .compute_env_digest_with_binds_policy(cfg, &snap_olean, binds_policy)
            .with_context(|| {
                format!(
                    "Failed to compute snapshot transitive import environment digest for `{}`",
                    m
                )
            })?;
        ensure_bound_audit_closure(snap, "audit_record_replayed_post")?;
        store.record_kernel_replayed_olean(
            &dig,
            &env_dig,
            ZYGOTE_REPLAY_VERSION,
            &cfg.lean_githash,
            m,
            live_batch.disallowed_roots(),
        )?;
    }
    for m in audited_mods {
        let (snap_olean, binds_policy) =
            resolve_binds_policy(snap, &mut snap_batch, &live_batch, m)?;
        let dig = crate::module_builder::compute_replayed_olean_ilean_digest(&snap_olean)
            .with_context(|| {
                format!(
                    "Failed to compute snapshot `.olean`+`.ilean` digest for `{}`",
                    m
                )
            })?;
        let env_dig = snap_batch
            .compute_env_digest_with_binds_policy(cfg, &snap_olean, binds_policy)
            .with_context(|| {
                format!(
                    "Failed to compute snapshot transitive import environment digest for `{}`",
                    m
                )
            })?;
        let policy_dig = compute_module_audit_policy_digest(cfg, m);
        ensure_bound_audit_closure(snap, "audit_record_audited_post")?;
        store.record_kernel_audited_olean(
            &dig,
            &env_dig,
            ZYGOTE_REPLAY_VERSION,
            &cfg.lean_githash,
            &policy_dig,
            m,
            live_batch.disallowed_roots(),
        )?;
    }
    Ok(())
}

// -------------------------------------------------------------------------------------------
// P9 (issues #411 / #412): early imported-posture policy decision, wired through the landed
// `kernel.rs` transitive csimp posture scan (#455). One cheap `--import-posture` worker pass
// (a single `importModules`, no snapshot, no kernel replay, no per-declaration axiom-closure
// walk) reports the posture facts; `kernel::decide_import_posture_policy` applies the
// `turbo-lean.toml` allowlists and refuses forbidden postures with the knob named BEFORE the
// expensive audit machinery runs, deciding exactly the posture set that audit considers (for
// csimp entries: those a target module owns or touches; the worker already filtered the
// per-target candidates through the audit's structural exemptions). Allowed postures proceed
// into the unchanged, authoritative audit; any infrastructure failure of this pass falls
// through to that audit (never fail-open).
// -------------------------------------------------------------------------------------------

#[derive(Debug, Deserialize)]
struct WirePostureCsimpEntry {
    e: String,
    u: String,
    s: bool,
    t: bool,
}

#[derive(Debug, Deserialize)]
// The worker also reports `init_sysroot` per module (the import-audit mode's `Init.*` baseline);
// the non-import decision mirrored here never consults it, so serde ignores that key.
struct WirePostureModule {
    m: String,
    #[serde(default)]
    imports: Vec<String>,
    #[serde(default)]
    csimp: Vec<WirePostureCsimpEntry>,
}

#[derive(Debug, Deserialize)]
struct WirePostureUnsafe {
    r: String,
    u: String,
    p: bool,
    c: bool,
    #[serde(default)]
    w: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct WirePostureBridge {
    r: String,
    u: String,
    x: bool,
    i: bool,
    a: bool,
    #[serde(default)]
    w: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct WirePostureTarget {
    m: String,
    #[serde(default)]
    axioms: Vec<String>,
    #[serde(default)]
    uind: Vec<String>,
    #[serde(default, rename = "unsafe")]
    unsafe_decls: Vec<WirePostureUnsafe>,
    #[serde(default)]
    bridge: Vec<WirePostureBridge>,
}

#[derive(Debug, Deserialize)]
struct WirePostureReply {
    ok: bool,
    #[serde(default)]
    error: Option<String>,
    #[serde(default)]
    modules: Vec<WirePostureModule>,
    #[serde(default)]
    targets: Vec<WirePostureTarget>,
}

/// Decide the imported-`.olean` policy (csimp / unsafe / implemented_by / axioms allowlists)
/// before the expensive audit. `Ok(())` means the audit proceeds: either the pass decided the
/// set is allowed, or it did not decide (untrusted mode, the
/// `TURBO_LEAN_EARLY_IMPORT_POLICY=off` opt-out, or an infrastructure failure of the posture
/// scan) and the authoritative audit decides as before; an `Err` is the decided early refusal.
fn early_import_policy_prepass(
    store_root: &Path,
    cfg: &crate::module_builder::ProjectConfig,
    sorted_mods: &[String],
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
    is_untrusted: bool,
) -> Result<()> {
    if is_untrusted || sorted_mods.is_empty() || !crate::kernel::early_import_policy_enabled() {
        return Ok(());
    }
    let undecided = |why: String| {
        eprintln!(
            "[turbo-lean] early import-policy posture scan did not decide ({why}); the in-kernel audit decides"
        );
        Ok(())
    };
    let (mut cmd, timeout) =
        match kernel_reader_command(store_root, cfg, lean_path_env, extra_ro_binds, false) {
            Ok(v) => v,
            Err(e) => return undecided(format!("reader unavailable: {e:#}")),
        };
    cmd.arg("--import-posture");
    for a in pinned_ffi_allow_args(cfg, sorted_mods) {
        cmd.arg(a);
    }
    for m in sorted_mods {
        cmd.arg(m);
    }
    let out = match crate::module_builder::run_command_with_timeout(&mut cmd, timeout, false) {
        Ok(o) => o,
        Err(e) => return undecided(format!("posture reader failed to run: {e:#}")),
    };
    let stdout_str = String::from_utf8_lossy(&out.stdout);
    let json_line = stdout_str
        .lines()
        .rev()
        .map(str::trim)
        .find(|l| l.starts_with('{') && l.ends_with('}'))
        .unwrap_or("");
    let reply: WirePostureReply = match serde_json::from_str(json_line) {
        Ok(r) => r,
        Err(e) => {
            return undecided(format!(
                "unparsable posture reply (exit={}): {e}; stderr: {}",
                out.status,
                String::from_utf8_lossy(&out.stderr).trim()
            ))
        }
    };
    if !out.status.success() || !reply.ok {
        return undecided(format!(
            "posture reader rejected the module set (exit={}): {}",
            out.status,
            reply.error.unwrap_or_default()
        ));
    }

    let mut decision_modules: std::collections::BTreeMap<String, crate::kernel::ImportPostureModule> =
        std::collections::BTreeMap::new();
    for m in &reply.modules {
        let mut entries = Vec::with_capacity(m.csimp.len());
        for we in &m.csimp {
            let observation = match crate::kernel::parse_public_signature_csimp_entry(&we.e) {
                Ok(o) => o,
                Err(e) => return undecided(format!("malformed posture csimp entry: {e:#}")),
            };
            entries.push(crate::kernel::PostureCsimpEntry {
                observation,
                thm_user_name: we.u.clone(),
                strict: we.s,
                touches_target: we.t,
            });
        }
        decision_modules.insert(
            m.m.clone(),
            crate::kernel::ImportPostureModule {
                module: m.m.clone(),
                imports: m.imports.clone(),
                csimp: entries,
            },
        );
    }
    let targets: Vec<crate::kernel::ImportPostureTarget> = reply
        .targets
        .iter()
        .map(|t| crate::kernel::ImportPostureTarget {
            module: t.m.clone(),
            axioms: t.axioms.clone(),
            unsafe_inductives: t.uind.clone(),
            unsafe_decls: t
                .unsafe_decls
                .iter()
                .map(|u| crate::kernel::PostureUnsafeCandidate {
                    raw: u.r.clone(),
                    user: u.u.clone(),
                    pattern_allowable: u.p,
                    can_allow: u.c,
                    wrapper_names: u.w.clone(),
                })
                .collect(),
            bridge_decls: t
                .bridge
                .iter()
                .map(|b| crate::kernel::PostureBridgeCandidate {
                    raw: b.r.clone(),
                    user: b.u.clone(),
                    is_extern: b.x,
                    is_implemented_by: b.i,
                    auxiliary: b.a,
                    wrapper_names: b.w.clone(),
                })
                .collect(),
        })
        .collect();
    let lists = crate::kernel::ImportPolicyAllowlists {
        axioms: crate::splitter::allowed_axioms(),
        csimp: crate::splitter::normalized_policy_env_vec("TURBO_LEAN_ALLOWED_CSIMP"),
        unsafe_decls: crate::splitter::normalized_policy_env_vec("TURBO_LEAN_ALLOWED_UNSAFE"),
        implemented_by: crate::splitter::normalized_policy_env_vec(
            "TURBO_LEAN_ALLOWED_IMPLEMENTED_BY",
        ),
    };
    let target_set: std::collections::BTreeSet<String> = sorted_mods.iter().cloned().collect();
    let decision = crate::kernel::decide_import_posture_policy(
        &targets,
        &decision_modules,
        &target_set,
        &lists,
    );
    if !decision.violations.is_empty() {
        anyhow::bail!(
            "Imported `.olean` import policy refused before the in-kernel audit (decided early from the compiled posture; allowlisted postures proceed):\n  {}",
            decision.violations.join("\n  ")
        );
    }
    Ok(())
}

pub(crate) fn audit_compiled_modules_with_zygote(
    store: &TurboStore,
    cfg: &crate::module_builder::ProjectConfig,
    mod_names: &[String],
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
    is_untrusted: bool,
) -> Result<()> {
    audit_compiled_modules_with_zygote_options(
        store,
        cfg,
        mod_names,
        lean_path_env,
        extra_ro_binds,
        is_untrusted,
        false,
    )
}

pub(crate) fn audit_compiled_modules_with_zygote_options(
    store: &TurboStore,
    cfg: &crate::module_builder::ProjectConfig,
    mod_names: &[String],
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
    is_untrusted: bool,
    allow_sorry_axiom: bool,
) -> Result<()> {
    let _ = audit_compiled_modules_with_zygote_snapshot(
        store,
        cfg,
        mod_names,
        lean_path_env,
        extra_ro_binds,
        is_untrusted,
        allow_sorry_axiom,
    )?;
    Ok(())
}

pub(crate) fn audit_compiled_modules_with_zygote_snapshot(
    store: &TurboStore,
    cfg: &crate::module_builder::ProjectConfig,
    mod_names: &[String],
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
    is_untrusted: bool,
    allow_sorry_axiom: bool,
) -> Result<Option<ClosureSnapshot>> {
    if mod_names.is_empty() {
        return Ok(None);
    }
    let mut sorted: Vec<String> = mod_names.to_vec();
    sorted.sort();
    sorted.dedup();
    // P9: decide the import policy (csimp / unsafe / implemented_by / axioms allowlists) before
    // the expensive snapshot + whole-closure replay + per-declaration audit work below.
    early_import_policy_prepass(
        &store.root,
        cfg,
        &sorted,
        lean_path_env,
        extra_ro_binds,
        is_untrusted,
    )?;
    if is_untrusted {
        // Validate the caller's live search paths against the untrusted sandbox gate first, then
        // bind-mount only the immutable `ClosureSnapshot` directory inside `bwrap` so multi-module
        // closure pre-replay and `--skip-child-replay` policy audit read identical sealed bytes.
        validate_untrusted_audit_caller_paths(cfg, lean_path_env, extra_ro_binds)?;
    }
    let snap = materialize_bound_audit_closure(cfg, &sorted, lean_path_env)?;
    let (snap_lp, snap_dir) = ensure_bound_audit_closure(&snap, "audit_before_replay")?;
    let pinned_fd = snapshot_pinned_dir_raw_fd(&snap);
    let parent_snap_lp = snapshot_parent_search_path(&snap).unwrap_or_else(|| snap_lp.clone());
    let snap_binds: Vec<PathBuf> = if is_untrusted {
        vec![snap_dir]
    } else {
        Vec::new()
    };
    // Pre-replay multi-module batches via topological `--kernel-replay-closure` slices against
    // the sealed snapshot `LEAN_PATH` so `--audit-modules --skip-child-replay` and authority
    // recording read the exact same immutable bytes.
    let pre_replayed = if sorted.len() > 1 {
        let replay_lp = if is_untrusted {
            &snap_lp
        } else {
            &parent_snap_lp
        };
        kernel_replay_modules_exec_pinned(
            &store.root,
            cfg,
            &sorted,
            replay_lp,
            &snap_binds,
            is_untrusted,
            pinned_fd,
        )?;
        true
    } else {
        false
    };
    let _ = ensure_bound_audit_closure(&snap, "audit_after_replay")?;
    let batch_sz = if pre_replayed && !is_untrusted {
        audit_batch_size().max(32)
    } else {
        audit_batch_size()
    };
    let chunks: Vec<&[String]> = sorted.chunks(batch_sz).collect();
    let should_record_chunk = |chunk: &[String]| -> bool {
        !is_untrusted
            && !allow_sorry_axiom
            && extra_ro_binds.is_empty()
            && !chunk.is_empty()
            && chunk
                .iter()
                .all(|m| snap.entries.get(m).and_then(|e| e.as_ref()).is_some())
    };
    // #435: thread the budget-derived hard cap to the audit workers.
    // The sequential branches run one audit subprocess at a time, so their per-process
    // backstop is the budget's single-worker share.
    let solo_audit_rlimit_mb = if is_untrusted {
        None
    } else {
        WorkerBudget::from_env().per_worker_rlimit_mb(1)
    };
    if is_untrusted || chunks.len() <= 1 {
        for chunk in chunks {
            let (chunk_lp, _) = ensure_bound_audit_closure(&snap, "audit_before_chunk")?;
            audit_compiled_module_batch_exec_pinned(
                &store.root,
                cfg,
                chunk,
                &chunk_lp,
                &snap_binds,
                is_untrusted,
                allow_sorry_axiom,
                pre_replayed,
                pinned_fd,
                solo_audit_rlimit_mb,
            )?;
            let _ = ensure_bound_audit_closure(&snap, "audit_after_chunk")?;
            if should_record_chunk(chunk) {
                record_snapshot_modules_in_store(
                    store,
                    cfg,
                    &snap,
                    chunk,
                    chunk,
                    lean_path_env,
                    None,
                )?;
            }
        }
        ensure_live_closure_matches_snapshot(&snap, "audit_complete")?;
        return Ok(Some(snap));
    }
    let parallelism = WorkerBudget::from_env().effective_parallelism(
        chunks.len(),
        REPLAY_WORKER_EST_RSS_MB,
        || {
            let cores = std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4);
            if pre_replayed {
                cores
            } else {
                cores.div_ceil(4).max(1)
            }
        },
    );
    // #435: each fan-out worker's hard cap is its share of the budget.
    let audit_rlimit_mb = WorkerBudget::from_env().per_worker_rlimit_mb(parallelism);
    if parallelism <= 1 {
        for chunk in chunks {
            let (chunk_lp, _) = ensure_bound_audit_closure(&snap, "audit_before_chunk")?;
            audit_compiled_module_batch_exec_pinned(
                &store.root,
                cfg,
                chunk,
                &chunk_lp,
                &[],
                false,
                allow_sorry_axiom,
                pre_replayed,
                pinned_fd,
                audit_rlimit_mb,
            )?;
            let _ = ensure_bound_audit_closure(&snap, "audit_after_chunk")?;
            if should_record_chunk(chunk) {
                record_snapshot_modules_in_store(
                    store,
                    cfg,
                    &snap,
                    chunk,
                    chunk,
                    lean_path_env,
                    None,
                )?;
            }
        }
        ensure_live_closure_matches_snapshot(&snap, "audit_complete")?;
        return Ok(Some(snap));
    }
    let bootstrap_env = build_auditor_bootstrap_env(cfg);
    let _ = ensure_zygote_binary_at(&store.root, &cfg.lean_bin, &bootstrap_env)?;
    let store_root = store.root.clone();
    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let first_err: std::sync::Mutex<Option<anyhow::Error>> = std::sync::Mutex::new(None);
    let record_lock: std::sync::Mutex<()> = std::sync::Mutex::new(());
    std::thread::scope(|s| {
        for _ in 0..parallelism {
            s.spawn(|| loop {
                if first_err.lock().map(|g| g.is_some()).unwrap_or(true) {
                    break;
                }
                let idx = next_idx.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if idx >= chunks.len() {
                    break;
                }
                let chunk = chunks[idx];
                let res = ensure_bound_audit_closure(&snap, "audit_before_chunk").and_then(
                    |(chunk_lp, _)| {
                        audit_compiled_module_batch_exec_pinned(
                            &store_root,
                            cfg,
                            chunk,
                            &chunk_lp,
                            &[],
                            false,
                            allow_sorry_axiom,
                            pre_replayed,
                            pinned_fd,
                            audit_rlimit_mb,
                        )?;
                        let _ = ensure_bound_audit_closure(&snap, "audit_after_chunk")?;
                        Ok(())
                    },
                );
                let res = res.and_then(|()| {
                    if should_record_chunk(chunk) {
                        let _guard = record_lock
                            .lock()
                            .map_err(|_| anyhow::anyhow!("audit record mutex poisoned"))?;
                        let worker_store = TurboStore::open(Some(&store_root))?;
                        record_snapshot_modules_in_store(
                            &worker_store,
                            cfg,
                            &snap,
                            chunk,
                            chunk,
                            lean_path_env,
                            None,
                        )?;
                    }
                    Ok(())
                });
                if let Err(e) = res {
                    if let Ok(mut g) = first_err.lock() {
                        if g.is_none() {
                            *g = Some(e);
                        }
                    }
                    break;
                }
            });
        }
    });
    if let Some(e) = first_err.into_inner().ok().flatten() {
        return Err(e);
    }
    ensure_live_closure_matches_snapshot(&snap, "audit_complete")?;
    Ok(Some(snap))
}

/// Unified closure replay + soundness audit for `certify_head_statement_modules_and_replay` in
/// trusted mode: replays `audit_mods ∪ replay_only_mods` together in a single topological closure
/// batch pass so interleaved packages (e.g. `Verity.Core` -> `Compiler.*` -> `Verity.Macro`) do not
/// taint/fragment each other's closure slices, then runs `--audit-modules --skip-child-replay` over
/// `audit_mods` only and persists replay authority for both sets (including `extra_root_lib`
/// overlay `.olean` roots).
#[cfg(test)]
pub(crate) fn replay_and_audit_modules_with_zygote(
    store: &TurboStore,
    cfg: &crate::module_builder::ProjectConfig,
    audit_mods: &[String],
    replay_only_mods: &[String],
    lean_path_env: &str,
    extra_root_lib: Option<&Path>,
) -> Result<()> {
    let _ = replay_and_audit_modules_with_zygote_snapshot(
        store,
        cfg,
        audit_mods,
        replay_only_mods,
        lean_path_env,
        extra_root_lib,
    )?;
    Ok(())
}

pub(crate) fn replay_and_audit_modules_with_zygote_snapshot(
    store: &TurboStore,
    cfg: &crate::module_builder::ProjectConfig,
    audit_mods: &[String],
    replay_only_mods: &[String],
    lean_path_env: &str,
    extra_root_lib: Option<&Path>,
) -> Result<Option<ClosureSnapshot>> {
    let mut sorted_audit: Vec<String> = audit_mods.to_vec();
    sorted_audit.sort();
    sorted_audit.dedup();
    let mut union_mods: Vec<String> =
        Vec::with_capacity(sorted_audit.len() + replay_only_mods.len());
    union_mods.extend(sorted_audit.iter().cloned());
    union_mods.extend(replay_only_mods.iter().cloned());
    union_mods.sort();
    union_mods.dedup();
    if union_mods.is_empty() {
        return Ok(None);
    }
    let snap = materialize_bound_audit_closure(cfg, &union_mods, lean_path_env)?;
    let (snap_lp, _) = ensure_bound_audit_closure(&snap, "replay_and_audit_before_replay")?;
    let pinned_fd = snapshot_pinned_dir_raw_fd(&snap);
    let parent_snap_lp = snapshot_parent_search_path(&snap).unwrap_or_else(|| snap_lp.clone());
    kernel_replay_modules_exec_pinned(
        &store.root,
        cfg,
        &union_mods,
        &parent_snap_lp,
        &[],
        false,
        pinned_fd,
    )?;
    let _ = ensure_bound_audit_closure(&snap, "replay_and_audit_after_replay")?;
    if !sorted_audit.is_empty() {
        let batch_sz = audit_batch_size().max(32);
        let chunks: Vec<&[String]> = sorted_audit.chunks(batch_sz).collect();
        let parallelism = WorkerBudget::from_env().effective_parallelism(
            chunks.len(),
            REPLAY_WORKER_EST_RSS_MB,
            || {
                std::thread::available_parallelism()
                    .map(|n| n.get())
                    .unwrap_or(4)
            },
        );
        // #435: each fan-out worker's hard cap is its budget share.
        let audit_rlimit_mb = WorkerBudget::from_env().per_worker_rlimit_mb(parallelism);
        if parallelism <= 1 {
            for chunk in chunks {
                let (chunk_lp, _) =
                    ensure_bound_audit_closure(&snap, "replay_and_audit_before_chunk")?;
                audit_compiled_module_batch_exec_pinned(
                    &store.root,
                    cfg,
                    chunk,
                    &chunk_lp,
                    &[],
                    false,
                    false,
                    true,
                    pinned_fd,
                    audit_rlimit_mb,
                )?;
                let _ = ensure_bound_audit_closure(&snap, "replay_and_audit_after_chunk")?;
            }
        } else {
            let bootstrap_env = build_auditor_bootstrap_env(cfg);
            let _ = ensure_zygote_binary_at(&store.root, &cfg.lean_bin, &bootstrap_env)?;
            let store_root = store.root.clone();
            let next_idx = std::sync::atomic::AtomicUsize::new(0);
            let first_err: std::sync::Mutex<Option<anyhow::Error>> = std::sync::Mutex::new(None);
            std::thread::scope(|s| {
                for _ in 0..parallelism {
                    s.spawn(|| loop {
                        if first_err.lock().map(|g| g.is_some()).unwrap_or(true) {
                            break;
                        }
                        let idx = next_idx.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if idx >= chunks.len() {
                            break;
                        }
                        if let Err(e) =
                            ensure_bound_audit_closure(&snap, "replay_and_audit_before_chunk")
                                .and_then(|(chunk_lp, _)| {
                                    audit_compiled_module_batch_exec_pinned(
                                        &store_root,
                                        cfg,
                                        chunks[idx],
                                        &chunk_lp,
                                        &[],
                                        false,
                                        false,
                                        true,
                                        pinned_fd,
                                        audit_rlimit_mb,
                                    )?;
                                    let _ = ensure_bound_audit_closure(
                                        &snap,
                                        "replay_and_audit_after_chunk",
                                    )?;
                                    Ok(())
                                })
                        {
                            if let Ok(mut g) = first_err.lock() {
                                if g.is_none() {
                                    *g = Some(e);
                                }
                            }
                            break;
                        }
                    });
                }
            });
            if let Some(e) = first_err.into_inner().ok().flatten() {
                return Err(e);
            }
        }
    }
    record_snapshot_modules_in_store(
        store,
        cfg,
        &snap,
        &union_mods,
        &sorted_audit,
        lean_path_env,
        extra_root_lib,
    )?;
    ensure_live_closure_matches_snapshot(&snap, "replay_and_audit_complete")?;
    Ok(Some(snap))
}

pub(crate) fn compute_module_audit_policy_digest(
    cfg: &crate::module_builder::ProjectConfig,
    mod_name: &str,
) -> String {
    let base_policy = crate::splitter::current_kernel_policy_digest();
    let ffi_args = pinned_ffi_allow_args(cfg, &[mod_name.to_string()]);
    if base_policy.is_empty() && ffi_args.is_empty() {
        return String::new();
    }
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-audit-policy-v1\n");
    h.update(&(base_policy.len() as u64).to_le_bytes());
    h.update(base_policy.as_bytes());
    for a in &ffi_args {
        h.update(&(a.len() as u64).to_le_bytes());
        h.update(a.as_bytes());
    }
    h.finalize().to_hex().to_string()
}

pub(super) fn replay_closure_batch_size() -> usize {
    std::env::var("TURBO_LEAN_REPLAY_CLOSURE_BATCH_SIZE")
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .filter(|&v| v > 0)
        .unwrap_or(32)
}

pub(crate) fn verify_proof_irrelevant_olean_update_exec(
    store_root: &Path,
    cfg: &crate::module_builder::ProjectConfig,
    mod_name: &str,
    old_olean_path: &Path,
    new_olean_path: &Path,
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
) -> Result<bool> {
    if mod_name.trim().is_empty() || !old_olean_path.is_file() || !new_olean_path.is_file() {
        return Ok(false);
    }
    let (mut cmd, timeout) =
        kernel_reader_command(store_root, cfg, lean_path_env, extra_ro_binds, false)?;
    cmd.arg("--verify-proof-irrelevant-olean-update")
        .arg(mod_name)
        .arg(old_olean_path)
        .arg(new_olean_path);
    let out = crate::module_builder::run_command_with_timeout(&mut cmd, timeout, false)?;
    Ok(out.status.success())
}

/// Compute a global topological ordering of all non-toolchain `.olean` modules transitively
/// reachable from `mod_names`, then partition `mod_names` into topological closure slices of at
/// most `batch_size` such that no module outside a slice transitively bridges two modules in that
/// slice (so `importModulesCore` on the slice's frontier never imports any target in the slice).
pub(super) fn build_replay_closure_batches(
    cfg: &crate::module_builder::ProjectConfig,
    mod_names: &[String],
    lean_path_env: &str,
    batch_size: usize,
) -> Result<Vec<Vec<String>>> {
    let mut dirs: Vec<PathBuf> = std::env::split_paths(lean_path_env).collect();
    if !cfg.toolchain_lib_lean.as_os_str().is_empty() && !dirs.contains(&cfg.toolchain_lib_lean) {
        dirs.push(cfg.toolchain_lib_lean.clone());
    }
    let tc_gh = if cfg.lean_githash.is_empty() {
        None
    } else {
        Some(cfg.lean_githash.as_str())
    };
    let target_set: std::collections::HashSet<String> = mod_names.iter().cloned().collect();
    let mut path_memo: std::collections::HashMap<String, Option<PathBuf>> =
        std::collections::HashMap::new();
    let resolve_non_tc = |m: &str,
                          memo: &mut std::collections::HashMap<String, Option<PathBuf>>|
     -> Result<Option<PathBuf>> {
        if let Some(cached) = memo.get(m) {
            return Ok(cached.clone());
        }
        let Some(p) = crate::module_builder::resolve_olean_along_search_dirs(&dirs, m) else {
            return Ok(None);
        };
        if !cfg.toolchain_lib_lean.as_os_str().is_empty()
            && crate::module_builder::is_verified_toolchain_olean_file(
                &cfg.toolchain_lib_lean,
                tc_gh,
                &p,
            )
        {
            memo.insert(m.to_string(), None);
            return Ok(None);
        }
        memo.insert(m.to_string(), Some(p.clone()));
        Ok(Some(p))
    };

    // Iterative post-order DFS over all reachable non-toolchain `.olean`s for topological order.
    enum Frame {
        Enter(String),
        Exit(String),
    }
    let mut state: std::collections::HashMap<String, u8> = std::collections::HashMap::new(); // 1=visiting, 2=done
    let mut topo_all: Vec<String> = Vec::new();
    let mut roots: Vec<String> = target_set.iter().cloned().collect();
    roots.sort();
    for root in roots {
        if state.get(&root) == Some(&2) {
            continue;
        }
        let mut stack = vec![Frame::Enter(root)];
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Enter(m) => {
                    match state.get(&m).copied() {
                        Some(2) => continue,
                        Some(1) => {
                            // Import cycle: fall back to single-module batches so replayAuditedModule reports cleanly.
                            return Ok(mod_names.iter().map(|s| vec![s.clone()]).collect());
                        }
                        _ => {}
                    }
                    let Some(path) = resolve_non_tc(&m, &mut path_memo)? else {
                        state.insert(m, 2);
                        continue;
                    };
                    let (imps, _) = crate::module_builder::read_olean_binary_imports_cached(&path)?;
                    state.insert(m.clone(), 1);
                    stack.push(Frame::Exit(m));
                    for imp in imps.into_iter().rev() {
                        if state.get(&imp.module) != Some(&2) {
                            stack.push(Frame::Enter(imp.module));
                        }
                    }
                }
                Frame::Exit(m) => {
                    state.insert(m.clone(), 2);
                    topo_all.push(m);
                }
            }
        }
    }

    // Scan `topo_all` in topological order while tracking `tainted` (non-batch modules that
    // transitively import at least one module in `cur_batch`). Flushing whenever `m` imports a
    // `tainted` module or `cur_batch.len() >= batch_size` guarantees no frontier import outside
    // `cur_batch` can reach `cur_batch`.
    let mut batches: Vec<Vec<String>> = Vec::new();
    let mut cur_batch: Vec<String> = Vec::new();
    let mut cur_set: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut tainted: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut seen_targets: std::collections::HashSet<String> = std::collections::HashSet::new();

    for m in topo_all {
        let direct_imps: Vec<String> = if let Some(Some(p)) = path_memo.get(&m) {
            crate::module_builder::read_olean_binary_imports_cached(p)?
                .0
                .into_iter()
                .map(|i| i.module)
                .collect()
        } else {
            Vec::new()
        };
        if target_set.contains(&m) {
            seen_targets.insert(m.clone());
            let touches_tainted = direct_imps.iter().any(|imp| tainted.contains(imp));
            if !cur_batch.is_empty() && (cur_batch.len() >= batch_size || touches_tainted) {
                batches.push(std::mem::take(&mut cur_batch));
                cur_set.clear();
                tainted.clear();
            }
            cur_set.insert(m.clone());
            cur_batch.push(m);
        } else if !cur_set.is_empty()
            && direct_imps
                .iter()
                .any(|imp| cur_set.contains(imp) || tainted.contains(imp))
        {
            tainted.insert(m);
        }
    }
    if !cur_batch.is_empty() {
        batches.push(cur_batch);
    }
    // Any target module whose `.olean` was missing on disk (so `resolve_non_tc` returned `None`)
    // MUST still be passed to `--kernel-replay-module` so it fails closed with the exact Lean error!
    for m in mod_names {
        if !seen_targets.contains(m) {
            batches.push(vec![m.clone()]);
        }
    }
    Ok(batches)
}

pub(crate) fn kernel_replay_modules_exec_pinned(
    store_root: &Path,
    cfg: &crate::module_builder::ProjectConfig,
    mod_names: &[String],
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
    is_untrusted: bool,
    pinned_dir_raw_fd: Option<i32>,
) -> Result<()> {
    for m in mod_names {
        anyhow::ensure!(
            !m.trim().is_empty(),
            "Kernel replay received an empty module name: fail-closed"
        );
    }
    if mod_names.is_empty() {
        return Ok(());
    }
    let budget = WorkerBudget::from_env();
    let worker_budget = if is_untrusted {
        1
    } else {
        budget.effective_parallelism(mod_names.len(), REPLAY_WORKER_EST_RSS_MB, || {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4)
        })
    };
    let explicit_batch_cap = std::env::var("TURBO_LEAN_REPLAY_CLOSURE_BATCH_SIZE")
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .filter(|&v| v > 0);
    let slice_cap = if is_untrusted {
        replay_closure_batch_size().min(32)
    } else if let Some(explicit) = explicit_batch_cap {
        explicit
    } else {
        // #435: shrink the closure batch under an explicit memory budget so one replay
        // process never loads a 32-module closure into a small per-worker share.
        let base_cap = budget.replay_batch_cap(replay_closure_batch_size(), worker_budget);
        if worker_budget > 1 && mod_names.len() > worker_budget {
            (mod_names.len() / (worker_budget * 2)).clamp(8.min(base_cap), base_cap)
        } else {
            base_cap
        }
    };
    let batches = build_replay_closure_batches(cfg, mod_names, lean_path_env, slice_cap)
        .unwrap_or_else(|_| mod_names.iter().map(|s| vec![s.clone()]).collect());
    let parallelism = if is_untrusted {
        1
    } else {
        worker_budget.min(batches.len()).max(1)
    };
    // #435: an explicit `--max-memory-mb` budget reaches every replay worker as a real
    // rlimit (its share of the budget), not only the advisory governor.
    let per_worker_rlimit_mb = if is_untrusted {
        None
    } else {
        budget.per_worker_rlimit_mb(parallelism)
    };
    let run_replay_slice = |slice: &[String]| -> Result<()> {
        let (mut cmd, _audit_timeout) =
            kernel_reader_command(store_root, cfg, lean_path_env, extra_ro_binds, is_untrusted)?;
        if let Some(mb) = per_worker_rlimit_mb {
            WorkerBudget::apply_worker_rlimit(&mut cmd, mb);
        }
        // #437: the replay budget has its own knob (`[replay] timeout_secs` /
        // TURBO_LEAN_REPLAY_TIMEOUT_SECS), defaulting to the audit budget.
        let replay_timeout = std::time::Duration::from_millis(replay_timeout_ms(is_untrusted));
        let timeout = if slice.len() == 1 {
            cmd.args(["--kernel-replay-module", &slice[0]]);
            replay_timeout
        } else {
            cmd.arg("--kernel-replay-closure");
            cmd.args(slice.iter().map(|s| s.as_str()));
            if is_untrusted {
                replay_timeout
            } else {
                replay_timeout.max(std::time::Duration::from_secs(600))
            }
        };
        let out = crate::module_builder::run_command_with_timeout_pinned_fd(
            &mut cmd,
            timeout,
            is_untrusted,
            pinned_dir_raw_fd,
        )
        .map_err(|e| {
            // #437: a timeout names the knob.
            if e.downcast_ref::<crate::module_builder::CommandTimedOut>()
                .is_some()
            {
                e.context(format!(
                    "independent kernel replay of {} module(s) exceeded its {}s budget (raise `[replay] timeout_secs` in turbo-lean.toml or `TURBO_LEAN_REPLAY_TIMEOUT_SECS`)",
                    slice.len(),
                    timeout.as_secs()
                ))
            } else {
                e.context("Failed to execute independent kernel replay")
            }
        })?;
        if out.status.success() {
            return Ok(());
        }
        if slice.len() == 1 {
            anyhow::bail!(
                "[TurboLean.KernelReplay] independent kernel re-check of `{}` failed (exit={}):\n{}{}",
                slice[0],
                out.status,
                String::from_utf8_lossy(&out.stderr).trim(),
                WorkerBudget::memory_kill_note(
                    &out.status,
                    &String::from_utf8_lossy(&out.stderr),
                    per_worker_rlimit_mb
                )
            );
        }
        for m in slice {
            let (mut single_cmd, _single_audit_timeout) = kernel_reader_command(
                store_root,
                cfg,
                lean_path_env,
                extra_ro_binds,
                is_untrusted,
            )?;
            if let Some(mb) = per_worker_rlimit_mb {
                WorkerBudget::apply_worker_rlimit(&mut single_cmd, mb);
            }
            single_cmd.args(["--kernel-replay-module", m]);
            let single_out = crate::module_builder::run_command_with_timeout_pinned_fd(
                &mut single_cmd,
                replay_timeout,
                is_untrusted,
                pinned_dir_raw_fd,
            )
            .map_err(|e| {
                if e.downcast_ref::<crate::module_builder::CommandTimedOut>()
                    .is_some()
                {
                    e.context(format!(
                        "independent kernel replay of `{}` exceeded its {}s budget (raise `[replay] timeout_secs` in turbo-lean.toml or `TURBO_LEAN_REPLAY_TIMEOUT_SECS`)",
                        m,
                        replay_timeout.as_secs()
                    ))
                } else {
                    e.context(
                        "Failed to execute independent kernel replay (`--kernel-replay-module`)",
                    )
                }
            })?;
            anyhow::ensure!(
                single_out.status.success(),
                "[TurboLean.KernelReplay] independent kernel re-check of `{}` failed (exit={}):\n{}{}",
                m,
                single_out.status,
                String::from_utf8_lossy(&single_out.stderr).trim(),
                WorkerBudget::memory_kill_note(
                    &single_out.status,
                    &String::from_utf8_lossy(&single_out.stderr),
                    per_worker_rlimit_mb
                )
            );
        }
        Ok(())
    };
    if parallelism <= 1 {
        for batch in &batches {
            run_replay_slice(batch)?;
        }
        return Ok(());
    }
    let bootstrap_env = build_auditor_bootstrap_env(cfg);
    let _ = ensure_zygote_binary_at(store_root, &cfg.lean_bin, &bootstrap_env)?;
    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let first_err: std::sync::Mutex<Option<anyhow::Error>> = std::sync::Mutex::new(None);
    std::thread::scope(|s| {
        for _ in 0..parallelism {
            s.spawn(|| loop {
                if first_err.lock().map(|g| g.is_some()).unwrap_or(true) {
                    break;
                }
                let idx = next_idx.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if idx >= batches.len() {
                    break;
                }
                if let Err(e) = run_replay_slice(&batches[idx]) {
                    if let Ok(mut g) = first_err.lock() {
                        if g.is_none() {
                            *g = Some(e);
                        }
                    }
                    break;
                }
            });
        }
    });
    if let Some(e) = first_err.into_inner().unwrap_or(None) {
        return Err(e);
    }
    Ok(())
}

/// Independent kernel replay (`--kernel-replay-closure` / `--kernel-replay-module`, one OS child
/// per bounded topological slice so import regions are reclaimed between batches) of trusted
/// dependency artifacts that skip the full policy audit: their declarations are rechecked against
/// their frontier imports before anything imports them.
pub(crate) fn kernel_replay_modules_with_zygote(
    store: &TurboStore,
    cfg: &crate::module_builder::ProjectConfig,
    mod_names: &[String],
    lean_path_env: &str,
) -> Result<()> {
    if mod_names.is_empty() {
        return Ok(());
    }
    let mut sorted: Vec<String> = mod_names.to_vec();
    sorted.sort();
    sorted.dedup();
    let snap = materialize_bound_audit_closure(cfg, &sorted, lean_path_env)?;
    let (snap_lp, _) = ensure_bound_audit_closure(&snap, "kernel_replay_before_replay")?;
    let pinned_fd = snapshot_pinned_dir_raw_fd(&snap);
    let parent_snap_lp = snapshot_parent_search_path(&snap).unwrap_or(snap_lp);
    kernel_replay_modules_exec_pinned(
        &store.root,
        cfg,
        &sorted,
        &parent_snap_lp,
        &[],
        false,
        pinned_fd,
    )?;
    let _ = ensure_bound_audit_closure(&snap, "kernel_replay_after_replay")?;
    record_snapshot_modules_in_store(store, cfg, &snap, &sorted, &[], lean_path_env, None)?;
    ensure_live_closure_matches_snapshot(&snap, "kernel_replay_complete")
}

pub(crate) fn build_auditor_bootstrap_env(
    cfg: &crate::module_builder::ProjectConfig,
) -> std::collections::HashMap<String, String> {
    let mut bootstrap_env = std::collections::HashMap::new();
    bootstrap_env.insert(
        "LEAN".to_string(),
        cfg.lean_bin.to_string_lossy().to_string(),
    );
    let tc_lp = cfg.toolchain_lib_lean.to_string_lossy().to_string();
    if !tc_lp.is_empty() {
        bootstrap_env.insert("LEAN_PATH".to_string(), tc_lp.clone());
    }
    let mut tc_ld_parts = Vec::new();
    if !tc_lp.is_empty() {
        tc_ld_parts.push(tc_lp);
    }
    let tc_lib = cfg.toolchain_lib.to_string_lossy().to_string();
    if !tc_lib.is_empty() && !tc_ld_parts.contains(&tc_lib) {
        tc_ld_parts.push(tc_lib);
    }
    if !tc_ld_parts.is_empty() {
        bootstrap_env.insert("LD_LIBRARY_PATH".to_string(), tc_ld_parts.join(":"));
    }
    bootstrap_env.insert(
        "PATH".into(),
        crate::module_builder::verifier_path(&cfg.lean_bin),
    );
    bootstrap_env.insert("ELAN_TOOLCHAIN".to_string(), cfg.toolchain.clone());
    bootstrap_env
}

/// The audited `.olean` reader process (the zygote binary with initializers disabled; sandboxed
/// for untrusted inputs), shared by module audits and declaration-identity readout.
pub(crate) fn kernel_reader_command(
    store_root: &Path,
    cfg: &crate::module_builder::ProjectConfig,
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
    is_untrusted: bool,
) -> Result<(Command, std::time::Duration)> {
    let bootstrap_env = build_auditor_bootstrap_env(cfg);
    let auditor_ld_library_path = bootstrap_env
        .get("LD_LIBRARY_PATH")
        .map(String::as_str)
        .unwrap_or("");
    let zygote_bin = ensure_zygote_binary_at(store_root, &cfg.lean_bin, &bootstrap_env)?;
    let canon_zygote = zygote_bin.canonicalize().unwrap_or(zygote_bin);

    let stack_kb = if is_untrusted {
        "262144".to_string()
    } else {
        std::env::var("LEAN_STACK_SIZE_KB").unwrap_or_else(|_| "262144".to_string())
    };
    let timeout_ms = audit_timeout_ms(is_untrusted);

    let cmd = if is_untrusted {
        let bwrap_path = crate::module_builder::probe_bwrap_sandbox(&cfg.root_pkg.pkg_root)
            .ok_or_else(|| {
            anyhow::anyhow!(
                "Untrusted kernel `.olean` audit requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
            )
        })?;
        let tc_prefix = cfg
            .toolchain_lib
            .parent()
            .filter(|p| p.is_dir() && p.is_absolute() && *p != Path::new("/"))
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "Invalid toolchain prefix `{}` for bubblewrap sandbox: fail-closed sandbox gate",
                    cfg.toolchain_lib.display()
                )
            })?;
        if extra_ro_binds.is_empty() {
            crate::module_builder::validate_untrusted_sandbox_search_paths(
                cfg,
                tc_prefix,
                lean_path_env,
                auditor_ld_library_path,
            )?;
        }
        let mut c = Command::new(bwrap_path);
        c.args([
            "--unshare-all",
            "--new-session",
            "--die-with-parent",
            "--clearenv",
            "--setenv",
            "PATH",
            "/usr/bin:/bin",
            "--setenv",
            "LEAN",
            &cfg.lean_bin.to_string_lossy(),
            "--setenv",
            "LEAN_PATH",
            lean_path_env,
            "--setenv",
            "LEAN_STACK_SIZE_KB",
            &stack_kb,
        ]);
        if !auditor_ld_library_path.is_empty() {
            c.args(["--setenv", "LD_LIBRARY_PATH", auditor_ld_library_path]);
        }
        for (key, allow) in request_policy(&Default::default()) {
            c.args(["--setenv", &key, &allow]);
        }
        c.args(["--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp"]);
        for sys_p in [
            "/usr",
            "/bin",
            "/lib",
            "/lib64",
            "/etc/ld.so.cache",
            "/etc/localtime",
        ] {
            c.args(["--ro-bind-try", sys_p, sys_p]);
        }
        c.arg("--ro-bind").arg(tc_prefix).arg(tc_prefix);
        c.arg("--ro-bind")
            .arg(&cfg.root_pkg.pkg_root)
            .arg(&cfg.root_pkg.pkg_root);
        for dp in &cfg.dep_pkgs {
            if !dp.pkg_root.starts_with(&cfg.root_pkg.pkg_root) {
                c.arg("--ro-bind").arg(&dp.pkg_root).arg(&dp.pkg_root);
            }
        }
        for extra in extra_ro_binds {
            if extra.exists() {
                c.arg("--ro-bind").arg(extra).arg(extra);
            }
        }
        c.arg("--ro-bind").arg(&canon_zygote).arg(&canon_zygote);
        c.arg("--chdir").arg(&cfg.root_pkg.pkg_root);
        c.arg(&canon_zygote);
        crate::module_builder::scrub_untrusted_env(&mut c);
        c
    } else {
        let mut c = Command::new(&canon_zygote);
        c.current_dir(&cfg.root_pkg.pkg_root)
            .env("PATH", crate::module_builder::verifier_path(&cfg.lean_bin))
            .env("LEAN", &cfg.lean_bin)
            .env("LEAN_PATH", lean_path_env)
            .env("LD_LIBRARY_PATH", auditor_ld_library_path)
            .env("LEAN_STACK_SIZE_KB", &stack_kb);
        c
    };
    Ok((cmd, std::time::Duration::from_millis(timeout_ms)))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn audit_compiled_module_batch_exec_pinned(
    store_root: &Path,
    cfg: &crate::module_builder::ProjectConfig,
    mod_names: &[String],
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
    is_untrusted: bool,
    allow_sorry_axiom: bool,
    skip_child_replay: bool,
    pinned_dir_raw_fd: Option<i32>,
    per_worker_rlimit_mb: Option<u64>,
) -> Result<()> {
    if mod_names.is_empty() || mod_names.iter().any(|m| m.trim().is_empty()) {
        anyhow::bail!("In-kernel `.olean` audit received an empty module name: fail-closed");
    }
    let (mut cmd, timeout) =
        kernel_reader_command(store_root, cfg, lean_path_env, extra_ro_binds, is_untrusted)?;
    // #435: the budget-derived hard cap reaches `--audit-modules`
    // workers too, so `--max-memory-mb` means the same thing on the audit path as on the
    // replay path. Untrusted audits keep the sandbox's own fixed RLIMIT_DATA instead.
    if !is_untrusted {
        if let Some(mb) = per_worker_rlimit_mb {
            WorkerBudget::apply_worker_rlimit(&mut cmd, mb);
        }
    }
    if allow_sorry_axiom && !is_untrusted {
        let mut allowed = crate::splitter::allowed_axioms();
        if !allowed.iter().any(|a| a == "sorryAx") {
            allowed.push("sorryAx".to_string());
        }
        cmd.env(crate::splitter::ALLOWED_AXIOMS_ENV, allowed.join(","));
    }
    cmd.arg("--audit-modules");
    if allow_sorry_axiom && !is_untrusted {
        cmd.arg("--allow-sorry");
    }
    if skip_child_replay {
        cmd.arg("--skip-child-replay");
    }
    for a in pinned_ffi_allow_args(cfg, mod_names) {
        cmd.arg(a);
    }
    for m in mod_names {
        cmd.arg(m);
    }

    let applied_rlimit_mb = if is_untrusted {
        None
    } else {
        per_worker_rlimit_mb
    };
    let out = crate::module_builder::run_command_with_timeout_pinned_fd(
        &mut cmd,
        timeout,
        is_untrusted,
        pinned_dir_raw_fd,
    );
    // An allocation failure under the worker cap names the knob (so
    // `error_names_memory_cap` can classify it), and a memory-capped failure is never
    // bisected — the recursive halving below would redo full-closure loads under the
    // same cap and end in the same unhelpful error.
    let attempt = out.and_then(|o| {
        parse_audit_modules_reply(&o, mod_names).map_err(|e| {
            let note = WorkerBudget::memory_kill_note(
                &o.status,
                &String::from_utf8_lossy(&o.stderr),
                applied_rlimit_mb,
            );
            if note.is_empty() {
                e
            } else {
                e.context(note.trim_start().to_string())
            }
        })
    });
    match attempt {
        Ok(_) => Ok(()),
        Err(e) if mod_names.len() > 1 && !WorkerBudget::error_names_definite_memory_cap(&e) => {
            let mid = mod_names.len() / 2;
            audit_compiled_module_batch_exec_pinned(
                store_root,
                cfg,
                &mod_names[..mid],
                lean_path_env,
                extra_ro_binds,
                is_untrusted,
                allow_sorry_axiom,
                skip_child_replay,
                pinned_dir_raw_fd,
                per_worker_rlimit_mb,
            )?;
            audit_compiled_module_batch_exec_pinned(
                store_root,
                cfg,
                &mod_names[mid..],
                lean_path_env,
                extra_ro_binds,
                is_untrusted,
                allow_sorry_axiom,
                skip_child_replay,
                pinned_dir_raw_fd,
                per_worker_rlimit_mb,
            )
        }
        Err(e) => Err(e),
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct OleanPublicDeclSig {
    pub name: String,
    pub kind: String,
    pub type_hash: String,
    #[serde(default)]
    pub body_hash: String,
    pub reducibility: String,
    pub inline: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct OleanPublicSignatureReply {
    pub ok: bool,
    pub module: String,
    pub is_module: bool,
    #[serde(default)]
    pub has_opaque_ext: bool,
    pub public_sig_digest: String,
    #[serde(default)]
    pub exported_imports: Vec<String>,
    #[serde(default)]
    pub simp_entries: Vec<String>,
    #[serde(default)]
    pub csimp_entries: Vec<String>,
    #[serde(default)]
    pub instance_entries: Vec<String>,
    #[serde(default)]
    pub decls: Vec<OleanPublicDeclSig>,
}

pub(crate) fn read_module_public_signature_with_zygote(
    store_root: &Path,
    cfg: &crate::module_builder::ProjectConfig,
    mod_name: &str,
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
    is_untrusted: bool,
) -> Result<OleanPublicSignatureReply> {
    let trimmed = mod_name.trim();
    anyhow::ensure!(
        !trimmed.is_empty(),
        "Cannot read `.olean` public signature for empty module name"
    );
    let (mut cmd, timeout) =
        kernel_reader_command(store_root, cfg, lean_path_env, extra_ro_binds, is_untrusted)?;
    cmd.arg("--public-sig").arg(trimmed);
    let out = crate::module_builder::run_command_with_timeout(&mut cmd, timeout, is_untrusted)
        .with_context(|| format!("Failed to run `--public-sig` reader for `{trimmed}`"))?;
    let stdout_str = String::from_utf8_lossy(&out.stdout);
    let stderr_str = String::from_utf8_lossy(&out.stderr);
    let json_line = stdout_str
        .lines()
        .rev()
        .map(str::trim)
        .find(|l| l.starts_with('{') && l.ends_with('}'))
        .unwrap_or("");
    let parsed: OleanPublicSignatureReply =
        serde_json::from_str(json_line).with_context(|| {
            format!(
                "`--public-sig` reader failed closed for `{trimmed}` (exit={}):\nstdout: {}\nstderr: {}",
                out.status,
                stdout_str.trim(),
                stderr_str.trim()
            )
        })?;
    anyhow::ensure!(
        out.status.success() && parsed.ok && parsed.public_sig_digest.len() == 64,
        "`--public-sig` reader rejected `{trimmed}` (exit={}):\nstdout: {}\nstderr: {}",
        out.status,
        stdout_str.trim(),
        stderr_str.trim()
    );
    Ok(parsed)
}

/// The auditor's verdict on `mod_names`: its JSON reply when every module passed, else an error.
pub(crate) fn parse_audit_modules_reply(
    out: &std::process::Output,
    mod_names: &[String],
) -> Result<ZygoteAuditModulesReply> {
    let stdout_str = String::from_utf8_lossy(&out.stdout);
    let stderr_str = String::from_utf8_lossy(&out.stderr);
    let json_line = stdout_str
        .lines()
        .rev()
        .map(str::trim)
        .find(|l| l.starts_with('{') && l.ends_with('}'))
        .unwrap_or("");
    let parsed: Option<ZygoteAuditModulesReply> = serde_json::from_str(json_line).ok();

    match parsed {
        Some(reply)
            if out.status.success()
                && reply.ok
                && reply.violations.is_empty()
                && reply.audited.as_deref() == Some(mod_names) =>
        {
            Ok(reply)
        }
        Some(reply) => {
            let details = if reply.violations.is_empty() {
                format!(
                    "exit={} stdout={} stderr={}",
                    out.status,
                    stdout_str.trim(),
                    stderr_str.trim()
                )
            } else {
                reply.violations.join("\n")
            };
            anyhow::bail!(
                "In-kernel `.olean` soundness audit rejected compiled artifact(s) ({:?}):\n{}",
                mod_names,
                details
            );
        }
        None => {
            anyhow::bail!(
                "In-kernel `.olean` soundness auditor failed closed (exit={}, modules={:?}):\nstdout: {}\nstderr: {}",
                out.status,
                mod_names,
                stdout_str.trim(),
                stderr_str.trim()
            );
        }
    }
}

/// Plain-`lean` fallback for a shard the zygote could not check (unavailable or import failure):
/// compile `source` to a scratch `.olean`, then accept it only on the kernel-level
/// `--audit-modules --shard` verdict over the compiled module (axioms incl. `sorryAx`,
/// extern/implemented_by, csimp, `unsafe`), never on output the shard itself controls. When
/// `allow_prefix_stubs` is true, only the source's `:= sorry` prefix stubs outside `audit` are
/// exempt, by name and kernel value; when false (whole-file audit), zero stubs are exempt. Every
/// `audit` theorem must be declared. A failed compile returns its non-success output; an audit
/// rejection is an error.
#[allow(clippy::too_many_arguments)]
pub(crate) fn run_audited_lean_shard(
    store: &TurboStore,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
    cwd: Option<&Path>,
    source: &str,
    audit: &std::collections::HashSet<String>,
    lean_args: &[String],
    timeout_ms: Option<u64>,
) -> Result<std::process::Output> {
    run_audited_lean_shard_with_types(
        store,
        lean_bin,
        env_vars,
        cwd,
        source,
        audit,
        &[],
        lean_args,
        timeout_ms,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_audited_lean_shard_with_types(
    store: &TurboStore,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
    cwd: Option<&Path>,
    source: &str,
    audit: &std::collections::HashSet<String>,
    expected_types: &[(String, String)],
    lean_args: &[String],
    timeout_ms: Option<u64>,
) -> Result<std::process::Output> {
    run_audited_lean_shard_with_types_report(
        store,
        lean_bin,
        env_vars,
        cwd,
        source,
        audit,
        expected_types,
        lean_args,
        timeout_ms,
    )
    .map(|(out, _)| out)
}

#[derive(Debug, Clone, Default)]
pub(crate) struct AuditedShardReport {
    pub decl_types: std::collections::BTreeMap<String, String>,
    pub used_sorry: bool,
    pub sorry_decls: Vec<String>,
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_audited_lean_shard_with_types_report(
    store: &TurboStore,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
    cwd: Option<&Path>,
    source: &str,
    audit: &std::collections::HashSet<String>,
    expected_types: &[(String, String)],
    lean_args: &[String],
    timeout_ms: Option<u64>,
) -> Result<(
    std::process::Output,
    std::collections::BTreeMap<String, String>,
)> {
    run_audited_lean_shard_at_with_types_report(
        &store.root,
        &store.fast_staging_dir(),
        lean_bin,
        env_vars,
        cwd,
        None,
        source,
        audit,
        true,
        expected_types,
        lean_args,
        timeout_ms,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_audited_lean_shard_with_sorry_report(
    store: &TurboStore,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
    cwd: Option<&Path>,
    source: &str,
    audit: &std::collections::HashSet<String>,
    expected_types: &[(String, String)],
    lean_args: &[String],
    timeout_ms: Option<u64>,
    allow_sorry: bool,
) -> Result<(std::process::Output, AuditedShardReport)> {
    run_audited_lean_shard_at_with_full_report(
        &store.root,
        &store.fast_staging_dir(),
        lean_bin,
        env_vars,
        cwd,
        None,
        source,
        audit,
        true,
        allow_sorry,
        expected_types,
        lean_args,
        timeout_ms,
    )
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn run_audited_lean_shard_at(
    store_root: &Path,
    staging_dir: &Path,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
    cwd: Option<&Path>,
    source_path: Option<&Path>,
    source: &str,
    audit: &std::collections::HashSet<String>,
    allow_prefix_stubs: bool,
    lean_args: &[String],
    timeout_ms: Option<u64>,
) -> Result<std::process::Output> {
    run_audited_lean_shard_at_with_types_report(
        store_root,
        staging_dir,
        lean_bin,
        env_vars,
        cwd,
        source_path,
        source,
        audit,
        allow_prefix_stubs,
        &[],
        lean_args,
        timeout_ms,
    )
    .map(|(out, _)| out)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_audited_lean_shard_at_with_types_report(
    store_root: &Path,
    staging_dir: &Path,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
    cwd: Option<&Path>,
    source_path: Option<&Path>,
    source: &str,
    audit: &std::collections::HashSet<String>,
    allow_prefix_stubs: bool,
    expected_types: &[(String, String)],
    lean_args: &[String],
    timeout_ms: Option<u64>,
) -> Result<(
    std::process::Output,
    std::collections::BTreeMap<String, String>,
)> {
    run_audited_lean_shard_at_with_full_report(
        store_root,
        staging_dir,
        lean_bin,
        env_vars,
        cwd,
        source_path,
        source,
        audit,
        allow_prefix_stubs,
        false,
        expected_types,
        lean_args,
        timeout_ms,
    )
    .map(|(out, rep)| (out, rep.decl_types))
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_audited_lean_shard_at_with_full_report(
    store_root: &Path,
    staging_dir: &Path,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
    cwd: Option<&Path>,
    source_path: Option<&Path>,
    source: &str,
    audit: &std::collections::HashSet<String>,
    allow_prefix_stubs: bool,
    allow_sorry: bool,
    expected_types: &[(String, String)],
    lean_args: &[String],
    timeout_ms: Option<u64>,
) -> Result<(std::process::Output, AuditedShardReport)> {
    crate::module_builder::validate_lean_args(lean_args)?;
    let started = std::time::Instant::now();
    let nonce = format!("{}_{}", std::process::id(), next_tmp_id());
    let mod_name = format!("TurboAuditedShard_{}", nonce);
    let src_dir = crate::check::PrivateScratchDir::create_with_nonce(
        staging_dir,
        "turbo_audited_src",
        nonce.clone(),
    )?;
    let out_dir = crate::check::PrivateScratchDir::create_with_nonce(
        staging_dir,
        "turbo_audited_out",
        nonce.clone(),
    )?;
    let reader_dir = crate::check::PrivateScratchDir::create_with_nonce(
        staging_dir,
        "turbo_audited_rdr",
        nonce.clone(),
    )?;
    let expected_source_hash = blake3::hash(source.as_bytes());
    let read_verified_live_source = |orig: &Path| -> Result<(OleanFileStatSig, i128)> {
        use std::io::Read;
        let sym_meta = fs::symlink_metadata(orig).with_context(|| {
            format!(
                "[TurboLean.KernelGate] failed to stat live source `{}`",
                orig.display()
            )
        })?;
        if sym_meta.file_type().is_symlink() || !sym_meta.is_file() {
            anyhow::bail!(
                "[TurboLean.KernelGate] live source `{}` must be a regular non-symlink file",
                orig.display()
            );
        }
        let sym_sig = OleanFileStatSig::from_meta(&sym_meta);
        let mut f = fs::File::open(orig).with_context(|| {
            format!(
                "[TurboLean.KernelGate] failed to open live source `{}`",
                orig.display()
            )
        })?;
        let pre_sig = OleanFileStatSig::from_meta(&f.metadata()?);
        if pre_sig != sym_sig {
            anyhow::bail!(
                "[TurboLean.KernelGate] live source `{}` changed concurrently before verification",
                orig.display()
            );
        }
        let read_started_ns = wall_clock_ns();
        let mut disk_bytes = Vec::with_capacity(pre_sig.size as usize);
        f.read_to_end(&mut disk_bytes)?;
        let post_sig = OleanFileStatSig::from_meta(&f.metadata()?);
        if post_sig != pre_sig || blake3::hash(&disk_bytes) != expected_source_hash {
            anyhow::bail!(
                "[TurboLean.KernelGate] live source `{}` diverged from audited in-memory snapshot",
                orig.display()
            );
        }
        Ok((pre_sig, read_started_ns))
    };
    let (lean_file, root_dir, live_source_pre_sig) = if let Some(orig) = source_path {
        let (mut pre_sig, mut read_started_ns) = read_verified_live_source(orig)?;
        if !dev_records_subsecond_timestamps(&pre_sig)
            && read_started_ns > 0
            && pre_sig.ctime_ns() >= read_started_ns - STAT_TRUST_WINDOW_NS
        {
            std::thread::sleep(std::time::Duration::from_millis(2100));
            (pre_sig, read_started_ns) = read_verified_live_source(orig)?;
        }
        let _ = read_started_ns;
        let root = cwd
            .filter(|d| orig.starts_with(d))
            .or_else(|| orig.parent())
            .unwrap_or(&src_dir.path);
        (orig.to_path_buf(), root.to_path_buf(), Some(pre_sig))
    } else {
        let lf = src_dir.path.join(format!("{}.lean", mod_name));
        crate::check::create_readonly_private_file(&lf, source.as_bytes())?;
        crate::check::freeze_private_dir(&src_dir.path)?;
        (lf, src_dir.path.clone(), None)
    };
    let out_olean = out_dir.path.join(format!("{}.olean", mod_name));
    let reader_olean = reader_dir.path.join(format!("{}.olean", mod_name));
    let nonce_env_val = format!("shard_{}", nonce);
    // Pinned toolchain executables replace any PATH/LEAN/LAKE/LEANC overrides in `env_vars`.
    let mut cmd = crate::module_builder::verifier_command(lean_bin, env_vars)?;
    let default_stack = env_vars
        .get("LEAN_STACK_SIZE_KB")
        .cloned()
        .or_else(|| std::env::var("LEAN_STACK_SIZE_KB").ok())
        .unwrap_or_else(|| "262144".to_string());
    cmd.env("LEAN_STACK_SIZE_KB", default_stack);
    cmd.args(crate::module_builder::filter_allowed_lean_args(lean_args))
        .arg("-Dwarn.sorry=true")
        .arg("-Ddebug.skipKernelTC=false")
        .arg("-R")
        .arg(&root_dir)
        .arg(&lean_file)
        .arg("-o")
        .arg(&out_olean)
        .env("TURBO_LEAN_PROBE_NONCE", &nonce_env_val);
    if let Some(dir) = cwd {
        cmd.current_dir(dir);
    }
    run_digest_test_hook("audited_shard_before_lean");
    let out_res = run_lean_command(&mut cmd, timeout_ms);
    reap_processes_with_nonce(&nonce_env_val);
    let out = out_res.context("Failed to execute `lean` on shard fallback")?;
    run_digest_test_hook("audited_shard_after_lean");
    if let (Some(orig), Some(pre_sig)) = (source_path, live_source_pre_sig.as_ref()) {
        let (post_compile_sig, _) = read_verified_live_source(orig)?;
        if &post_compile_sig != pre_sig {
            anyhow::bail!(
                "[TurboLean.KernelGate] live source `{}` changed on disk during compilation",
                orig.display()
            );
        }
    }
    if !out.status.success() {
        return Ok((out, AuditedShardReport::default()));
    }
    crate::check::freeze_private_dir(&out_dir.path)?;
    crate::check::stage_isolated_module_artifacts(&out_dir.path, &reader_dir.path, &mod_name)
        .context("Lean verification produced no `.olean` artifact; refusing verification")?;
    crate::check::freeze_private_dir(&reader_dir.path)?;

    let artifact = fs::symlink_metadata(&reader_olean)
        .context("Lean verification produced no `.olean` artifact; refusing verification")?;
    anyhow::ensure!(
        artifact.is_file() && artifact.len() > 0,
        "Lean verification produced no regular, nonempty `.olean` artifact"
    );

    let lean_path = env_vars
        .get("LEAN_PATH")
        .cloned()
        .or_else(|| std::env::var("LEAN_PATH").ok())
        .filter(|lp| !lp.is_empty())
        .map_or_else(
            || reader_dir.path.display().to_string(),
            |lp| format!("{}:{}", reader_dir.path.display(), lp),
        );
    // A request budget bounds the whole fallback: compile, auditor preparation and audit.
    let budget_left = |stage: &str| -> Result<Option<std::time::Duration>> {
        timeout_ms
            .map(|ms| {
                let left = std::time::Duration::from_millis(ms).saturating_sub(started.elapsed());
                anyhow::ensure!(!left.is_zero(), "Lean request timed out before {}", stage);
                Ok(left)
            })
            .transpose()
    };
    let zygote_bin = match budget_left("the shard auditor was ready")? {
        None => ensure_zygote_binary_at(store_root, lean_bin, env_vars)?,
        // A cold auditor build may outlive the request; it still warms the cache in the background.
        Some(left) => {
            let (tx, rx) = std::sync::mpsc::channel();
            let (root, lean, env) = (
                store_root.to_path_buf(),
                lean_bin.to_path_buf(),
                env_vars.clone(),
            );
            std::thread::spawn(move || {
                let _ = tx.send(ensure_zygote_binary_at(&root, &lean, &env));
            });
            rx.recv_timeout(left).map_err(|_| {
                anyhow::anyhow!("Lean request timed out before the shard auditor was ready")
            })??
        }
    };
    let mut auditor = Command::new(zygote_bin);
    auditor
        .envs(env_vars)
        .env("PATH", crate::module_builder::verifier_path(lean_bin))
        .env("LEAN", lean_bin)
        .env("LEAN_PATH", lean_path)
        .args(["--audit-modules", "--shard"]);
    // The auditor links `libleanshared` from the toolchain, which an elan-proxied `lean` does not
    // put on the loader path.
    let mut prefix_cmd = crate::module_builder::verifier_command(lean_bin, env_vars)?;
    prefix_cmd.arg("--print-prefix");
    if let Some(dir) = cwd {
        prefix_cmd.current_dir(dir);
    }
    let prefix_out = match budget_left("the toolchain prefix query")? {
        None => prefix_cmd.output().ok(),
        Some(left) => run_lean_command(&mut prefix_cmd, Some(left.as_millis().max(1) as u64)).ok(),
    };
    if let Some(p) = prefix_out.filter(|p| p.status.success()) {
        let prefix = PathBuf::from(String::from_utf8_lossy(&p.stdout).trim());
        let mut ld = format!(
            "{}:{}",
            prefix.join("lib/lean").display(),
            prefix.join("lib").display()
        );
        if let Some(prev) = env_vars
            .get("LD_LIBRARY_PATH")
            .cloned()
            .or_else(|| std::env::var("LD_LIBRARY_PATH").ok())
            .filter(|l| !l.is_empty())
        {
            ld = format!("{}:{}", ld, prev);
        }
        auditor.env("LD_LIBRARY_PATH", ld);
    }
    auditor.envs(request_policy(env_vars));
    let parsed_shards = crate::splitter::split_lean_source(source, &[]).shards;
    let fast_map = crate::splitter::FastVerifyMap::parse_and_validate(source, &parsed_shards)?;
    for entry in fast_map.entries() {
        auditor.arg(format!(
            "--fast-map={}:{}",
            hex_encode_bytes(entry.orig_rooted.as_bytes()),
            hex_encode_bytes(entry.gen_rooted.as_bytes())
        ));
    }
    if allow_sorry {
        auditor.arg("--allow-sorry");
    }
    if allow_prefix_stubs {
        for sh in &parsed_shards {
            if crate::splitter::strip_lean_comments(&sh.proof_text).trim() == "sorry"
                && !fast_map.shard_matches_targets(sh, audit)
                && !crate::splitter::matches_uncached_or_fast_verify_name(sh.decl_name(), audit)
            {
                auditor.arg(format!("--stub-ok={}", sh.rooted_name()));
            }
        }
    }
    auditor.arg(&mod_name);
    if let Some(dir) = cwd {
        auditor.current_dir(dir);
    }
    // #443: an explicitly unbounded request lifts the DEFAULT audit cap too, so
    // `--timeout-ms 0` truly means no artificial timeout; an explicitly configured finite
    // TURBO_LEAN_AUDIT_TIMEOUT_SECS still binds. Both sides read the one shared parser
    // (`explicit_audit_timeout_ms`), so `0`, an empty value and an unparsable value mean
    // the same thing here as in `audit_timeout_ms`; and the unbounded test is a threshold
    // (`is_unbounded_timeout_ms`), never an exact sentinel match, so a derived budget
    // (the sentinel minus elapsed time) stays unbounded too (#443 review, finding 3).
    let mut audit_timeout = if timeout_ms.is_some_and(is_unbounded_timeout_ms)
        && explicit_audit_timeout_ms().is_none()
    {
        std::time::Duration::from_millis(UNBOUNDED_TIMEOUT_MS)
    } else {
        std::time::Duration::from_millis(audit_timeout_ms(false))
    };
    // #443: when the remaining request budget is the binding limit,
    // the timeout error names the request knob, not `[audit] timeout_secs`.
    let mut request_budget_bound = false;
    if let Some(left) = budget_left("the shard audit")? {
        if left < audit_timeout {
            audit_timeout = left;
            request_budget_bound = true;
        }
    }
    let audit_out =
        crate::module_builder::run_command_with_timeout(&mut auditor, audit_timeout, false)
            .map_err(|e| {
                // #437: a timeout names the knob.
                if e.downcast_ref::<crate::module_builder::CommandTimedOut>()
                    .is_some()
                {
                    if request_budget_bound {
                        e.context(format!(
                            "shard audit exceeded the request's remaining {}s budget (the explicit `--timeout-ms` / `TURBO_LEAN_TIMEOUT_MS` request budget was the binding limit; raise it)",
                            audit_timeout.as_secs()
                        ))
                    } else {
                        e.context(format!(
                            "shard audit exceeded its {}s budget (raise `[audit] timeout_secs` in turbo-lean.toml or `TURBO_LEAN_AUDIT_TIMEOUT_SECS`)",
                            audit_timeout.as_secs()
                        ))
                    }
                } else {
                    e.context(
                        "Failed to execute in-kernel shard auditor (`--audit-modules --shard`)",
                    )
                }
            })?;
    let parsed_reply = parse_audit_modules_reply(&audit_out, std::slice::from_ref(&mod_name))?;
    let decls = parsed_reply.decls.unwrap_or_default();
    let missing: Vec<&String> = audit
        .iter()
        .filter(|name| {
            !decls
                .iter()
                .any(|d| crate::splitter::decl_name_matches_target(d, name.as_str()))
        })
        .collect();
    if !missing.is_empty() {
        anyhow::bail!(
            "[TurboLean.KernelGate] audited theorem(s) {:?} missing from the compiled shard",
            missing
        );
    }
    if let (Some(orig), Some(pre_sig)) = (source_path, live_source_pre_sig.as_ref()) {
        let (post_audit_sig, _) = read_verified_live_source(orig)?;
        if &post_audit_sig != pre_sig {
            anyhow::bail!(
                "[TurboLean.KernelGate] live source `{}` changed on disk during kernel audit",
                orig.display()
            );
        }
    }
    let decl_types = parsed_reply.decl_types.unwrap_or_default();
    if !expected_types.is_empty() {
        verify_attested_decl_types(&decl_types, expected_types)?;
    }
    let sorry_decls = parsed_reply.sorry_decls;
    let used_sorry = parsed_reply.used_sorry || !sorry_decls.is_empty();
    Ok((
        out,
        AuditedShardReport {
            decl_types,
            used_sorry,
            sorry_decls,
        },
    ))
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn audit_compiled_shard_module_with_zygote(
    store: &TurboStore,
    cfg: &crate::module_builder::ProjectConfig,
    mod_name: &str,
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
    stub_ok: &[String],
    audit: &std::collections::HashSet<String>,
    expected_types: &[(String, String)],
    is_untrusted: bool,
) -> Result<()> {
    anyhow::ensure!(
        !mod_name.trim().is_empty(),
        "In-kernel `.olean` shard audit received an empty module name: fail-closed"
    );
    let mod_names = vec![mod_name.to_string()];
    let (mut cmd, timeout) = kernel_reader_command(
        &store.root,
        cfg,
        lean_path_env,
        extra_ro_binds,
        is_untrusted,
    )?;
    cmd.args(["--audit-modules", "--shard"]);
    for a in pinned_ffi_allow_args(cfg, &mod_names) {
        cmd.arg(a);
    }
    for stub in stub_ok {
        cmd.arg(format!("--stub-ok={stub}"));
    }
    cmd.arg(mod_name);
    let out = crate::module_builder::run_command_with_timeout(&mut cmd, timeout, is_untrusted)
        .context(
            "Failed to execute in-kernel `.olean` shard auditor (`--audit-modules --shard`)",
        )?;
    let parsed_reply = parse_audit_modules_reply(&out, &mod_names)?;
    let decls = parsed_reply.decls.unwrap_or_default();
    let missing: Vec<&String> = audit
        .iter()
        .filter(|name| {
            let one = std::collections::HashSet::from([(*name).clone()]);
            !decls
                .iter()
                .any(|d| crate::splitter::matches_uncached_or_fast_verify_name(d, &one))
        })
        .collect();
    if !missing.is_empty() {
        anyhow::bail!(
            "[TurboLean.KernelGate] audited theorem(s) {:?} missing from compiled module `{}`",
            missing,
            mod_name
        );
    }
    if !expected_types.is_empty() {
        verify_attested_decl_types(&parsed_reply.decl_types.unwrap_or_default(), expected_types)?;
    }
    Ok(())
}
