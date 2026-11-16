use crate::db::TurboStore;
use crate::pack::next_tmp_id;
use anyhow::{Context, Result};
use serde::Deserialize;
use std::fs;
use std::io::{BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

use super::*;

/// Check `shard_source` with its prefix `sorry` stubs admitted, but never the `sorryAx` of `stub_targets`.
#[allow(clippy::too_many_arguments)]
pub fn eval_with_zygote_pool_for_targets(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    stub_targets: &[String],
    timeout_ms: Option<u64>,
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_for_targets_modulo_sorry(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        stub_targets,
        timeout_ms,
        lean_args,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn eval_with_zygote_pool_for_targets_and_stubs(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    stub_targets: &[String],
    extra_stubs: &[String],
    timeout_ms: Option<u64>,
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_inner_with_context_ext(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        true,
        false,
        None,
        timeout_ms,
        None,
        lean_args,
        stub_targets,
        extra_stubs,
        false,
        false,
        false,
        None,
    )
    .map(|(rep, _, _)| rep)
}

#[allow(clippy::too_many_arguments)]
pub fn eval_with_zygote_pool_for_targets_modulo_sorry(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    stub_targets: &[String],
    timeout_ms: Option<u64>,
    lean_args: &[String],
    allow_sorry: bool,
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_inner_ext(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        true,
        false,
        None,
        timeout_ms,
        None,
        lean_args,
        stub_targets,
        false,
        allow_sorry,
        false,
    )
}

/// Check `shard_source` with no `sorry` stub exempt anywhere, prefix checkpoints included (`strict_all`):
/// the kernel-gate audit of a whole file.
#[allow(clippy::too_many_arguments)]
pub fn eval_with_zygote_pool_audit_all(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    file_name: Option<&str>,
    timeout_ms: Option<u64>,
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_audit_all_modulo_sorry(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        file_name,
        timeout_ms,
        lean_args,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn eval_with_zygote_pool_audit_all_modulo_sorry(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    file_name: Option<&str>,
    timeout_ms: Option<u64>,
    lean_args: &[String],
    allow_sorry: bool,
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_inner_ext(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        false,
        false,
        file_name,
        timeout_ms,
        None,
        lean_args,
        &[],
        true,
        allow_sorry,
        false,
    )
}

pub fn reply_indicates_timeout_or_heartbeat(rep: &ZygoteEvalReply) -> bool {
    if rep.ok {
        return false;
    }
    if rep.timed_out {
        return true;
    }
    let matches_text = |s: &str| {
        let lower = s.to_ascii_lowercase();
        lower.contains("deterministic timeout")
            || lower.contains("maximum number of heartbeats")
            || lower.contains("heartbeats")
            || lower.contains("maximum recursion depth")
    };
    rep.errors.iter().any(|e| matches_text(e))
        || rep.messages.iter().any(|m| matches_text(m))
        || matches_text(&rep.stderr_tail)
}

pub fn text_indicates_timeout_or_heartbeat(text: &str) -> bool {
    let lower = text.to_ascii_lowercase();
    lower.contains("timed out")
        || lower.contains("deterministic timeout")
        || lower.contains("maximum number of heartbeats")
        || lower.contains("heartbeats")
        || lower.contains("maximum recursion depth")
}

pub fn format_hotspot_diagnostics(
    timeout_hotspots: &[TimeoutHotspot],
    simp_hotspots: &[SimpHotspot],
) -> String {
    if timeout_hotspots.is_empty() && simp_hotspots.is_empty() {
        return String::new();
    }
    let mut lines = Vec::new();
    lines.push("[hotspot] timeout/heartbeat hotspot attribution:".to_string());
    for h in timeout_hotspots.iter().take(5) {
        if h.line > 0 {
            lines.push(format!(
                "  - line {} [{}]: {} ({} ms, {} heartbeats)",
                h.line, h.kind, h.label, h.elapsed_ms, h.heartbeats
            ));
        } else {
            lines.push(format!(
                "  - [{}]: {} ({} ms, {} heartbeats)",
                h.kind, h.label, h.elapsed_ms, h.heartbeats
            ));
        }
    }
    if !simp_hotspots.is_empty() {
        lines.push("[hotspot] top `simp` lemma attempts:".to_string());
        for s in simp_hotspots.iter().take(5) {
            lines.push(format!(
                "  - {}: {} attempts ({} succeeded)",
                s.lemma, s.attempts, s.succeeded
            ));
        }
    }
    lines.join("\n")
}

#[allow(clippy::too_many_arguments)]
pub fn diagnose_hotspots_with_zygote_pool(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    file_name: Option<&str>,
    timeout_ms: Option<u64>,
    lean_args: &[String],
) -> Option<(Vec<TimeoutHotspot>, Vec<SimpHotspot>)> {
    let bounded_ms = timeout_ms.unwrap_or(2_500).clamp(250, 4_000);
    let rep = eval_with_zygote_pool_inner_ext(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        true,
        false,
        file_name,
        Some(bounded_ms),
        None,
        lean_args,
        &[],
        false,
        false,
        true,
    )
    .ok()?;
    if rep.timeout_hotspots.is_empty() && rep.simp_hotspots.is_empty() {
        None
    } else {
        Some((rep.timeout_hotspots, rep.simp_hotspots))
    }
}

pub(super) fn attach_host_closure_digest(req_line: &str, host_closure_digest: &str) -> String {
    if host_closure_digest.is_empty() {
        return req_line.to_string();
    }
    let trimmed = req_line.trim_end_matches('\n');
    let cols = trimmed.split('\t').count();
    let mut out = String::with_capacity(trimmed.len() + host_closure_digest.len() + 8);
    out.push_str(trimmed);
    for _ in cols..6 {
        out.push('\t');
    }
    out.push('\t');
    out.push_str(host_closure_digest);
    out.push('\n');
    out
}

pub(super) fn toolchain_lib_dir(lean_bin: &Path) -> Option<PathBuf> {
    lean_bin
        .parent()
        .and_then(|b| b.parent())
        .map(|tc| tc.join("lib").join("lean"))
        .filter(|p| p.exists())
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn resolve_zygote_context(
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    raw_imports_csv: &str,
) -> ResolvedZygoteContext {
    let env_lp = env_vars.get("LEAN_PATH").cloned().unwrap_or_default();
    let lp_cache_key = (
        req_lean_path.to_string(),
        env_lp.clone(),
        lean_bin.to_path_buf(),
    );
    let lp_cache_mutex = ZYGOTE_LEAN_PATH_CACHE
        .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    let cached_lp = lp_cache_mutex
        .lock()
        .ok()
        .and_then(|g| g.get(&lp_cache_key).cloned());

    let tc_lib = toolchain_lib_dir(lean_bin);
    let effective_lean_path = if let Some(eff) = cached_lp {
        eff
    } else {
        let mut path_parts: Vec<String> = Vec::new();
        let mut add_part = |p: &str| {
            for seg in p.split(':') {
                let s = seg.trim();
                if !s.is_empty() {
                    let norm = fs::canonicalize(s)
                        .map(|c| c.to_string_lossy().to_string())
                        .unwrap_or_else(|_| s.to_string());
                    if is_toolchain_dir_match(Path::new(&norm), tc_lib.as_deref()) {
                        continue;
                    }
                    if !path_parts.iter().any(|x| x == &norm) {
                        path_parts.push(norm);
                    }
                }
            }
        };
        if !req_lean_path.is_empty() {
            add_part(req_lean_path);
        }
        if !env_lp.is_empty() {
            add_part(&env_lp);
        }
        if req_lean_path.is_empty() && env_lp.is_empty() {
            if let Some(repo_lean_dir) = Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .and_then(|p| p.parent())
                .map(|r| r.join("lean"))
                .filter(|p| p.join(".lake/build/lib/lean").exists())
            {
                add_part(&crate::lake_build::resolve_remote_lean_path(
                    &repo_lean_dir,
                    None,
                ));
            }
        }
        if let Some(ref tc_lib_lean) = tc_lib {
            let norm = fs::canonicalize(tc_lib_lean)
                .map(|c| c.to_string_lossy().to_string())
                .unwrap_or_else(|_| tc_lib_lean.to_string_lossy().to_string());
            if !path_parts.iter().any(|x| x == &norm) {
                path_parts.push(norm);
            }
        }
        let eff = path_parts.join(":");
        if let Ok(mut g) = lp_cache_mutex.lock() {
            if g.len() >= 512 {
                g.clear();
            }
            g.insert(lp_cache_key, eff.clone());
        }
        eff
    };

    let imports_csv = coalesce_proofkit_imports(raw_imports_csv, &effective_lean_path);
    let search_path_digest =
        compute_search_path_oleans_digest_with_toolchain(&effective_lean_path, tc_lib.as_deref());
    // Every cache below (worker env, warm pool, verdicts) is labelled with this snapshot's
    // digest, and is only populated once `rebind` proves the worker read these bytes.
    let mut closure = ClosureSnapshot::take(&imports_csv, &effective_lean_path, tc_lib.as_deref());
    // The worker imports a verified private copy of the closure, so later changes to the
    // search path cannot reach it; the copy's manifest digest labels its env and verdicts.
    closure.materialize(tc_lib.as_deref());
    run_digest_test_hook("after_closure_snapshot");
    let imported_digest = match closure.label() {
        Some(label) => format!("snap:{label}"),
        None => format!("unbound:{}", closure.digest),
    };
    let host_closure_digest = closure.label().unwrap_or("");
    // Declared Lake file inputs move no `.olean` byte, so they have to be named separately in both
    // the pool key (never hand back a worker warmed against older input bytes) and `olean_digest`
    // (which keys the verified-shard memo and the `warm_imports` / `warm_prefixes` match).
    let (lake_inputs_digest, lake_inputs_uncacheable) =
        compute_lean_path_lake_inputs_digest(&effective_lean_path, env_vars);
    // Workers enforce the axiom policy they were spawned with: key them (and their replies) by it.
    let extra_axioms: Vec<String> = env_vars
        .get(crate::splitter::ALLOWED_AXIOMS_ENV)
        .map(|s| {
            s.split(',')
                .map(str::trim)
                .filter(|p| !p.is_empty())
                .map(String::from)
                .collect()
        })
        .unwrap_or_else(|| {
            request_policy(env_vars)[crate::splitter::ALLOWED_AXIOMS_ENV]
                .split(',')
                .filter(|s| !s.is_empty())
                .map(String::from)
                .collect()
        });
    let policy = request_policy(env_vars);
    let policy_digest = blake3::hash(&serde_json::to_vec(&policy).expect("policy serializes")).to_hex().to_string();
    let toolchain_policy = format!(
        "{}#{}#{}",
        toolchain,
        crate::splitter::allowed_axioms_with_extra(&extra_axioms).join(","),
        policy_digest
    );
    let olean_digest = if lake_inputs_digest.is_empty() {
        format!("{}:{}", search_path_digest, imported_digest)
    } else {
        format!(
            "{}:{}#inputs:{}",
            search_path_digest, imported_digest, lake_inputs_digest
        )
    };
    let closure_pool_digest = if closure.label().is_some() {
        if lake_inputs_digest.is_empty() {
            imported_digest.clone()
        } else {
            format!("{}#inputs:{}", imported_digest, lake_inputs_digest)
        }
    } else {
        olean_digest.clone()
    };
    let closure_pool_digest = format!("{closure_pool_digest}#policy:{policy_digest}");
    let compiler_path = fs::canonicalize(lean_bin).unwrap_or_else(|_| lean_bin.to_path_buf());
    let compiler_digest = fs::read(&compiler_path)
        .map(|bytes| blake3::hash(&bytes).to_hex().to_string())
        .unwrap_or_default();
    let compiler_identity = blake3::hash(
        &serde_json::to_vec(&(&toolchain_policy, &compiler_path, compiler_digest))
            .expect("compiler identity serializes"),
    )
    .to_hex()
    .to_string();
    let identity = blake3::hash(
        &serde_json::to_vec(&(
            &compiler_identity,
            &effective_lean_path,
            &imports_csv,
            &olean_digest,
        ))
        .expect("execution identity serializes"),
    )
    .to_hex()
    .to_string();
    let toolchain_policy = format!("{}#{}", toolchain_policy, compiler_identity);
    ResolvedZygoteContext {
        worker_lean_path: closure.worker_lean_path(),
        lean_path: effective_lean_path,
        imports_csv,
        olean_digest,
        closure_pool_digest,
        host_closure_digest: host_closure_digest.to_string(),
        toolchain_policy,
        lake_inputs_uncacheable,
        identity,
        closure,
    }
}

pub(super) const CLOSURE_CHANGED_ERR: &str = "[turbo-lean] imported .olean closure changed while it was \
     being evaluated (twice); refusing to report a verdict for bytes that were not hashed";

#[allow(clippy::too_many_arguments)]
pub(crate) fn eval_with_resolved_context_opts_with_args(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
    eval_mode: bool,
    file_name: Option<&str>,
    timeout_ms: Option<u64>,
    lean_args: &[String],
    initial_context: Option<&ResolvedZygoteContext>,
) -> Result<(ZygoteEvalReply, ClosureBinding, String)> {
    eval_with_zygote_pool_inner_with_context_ext(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        allow_stub,
        eval_mode,
        file_name,
        timeout_ms,
        None,
        lean_args,
        &[],
        &[],
        false,
        false,
        false,
        initial_context,
    )
}

/// Runs a request against a snapshot of its imported `.olean` closure; if the closure changed
/// while the worker imported it, the reply is discarded (nothing cached, worker killed) and
/// the request retried once on a fresh snapshot, then fails closed.
#[allow(clippy::too_many_arguments)]
pub(super) fn eval_with_zygote_pool_inner(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
    eval_mode: bool,
    file_name: Option<&str>,
    timeout_ms: Option<u64>,
    batch_fission_override: Option<(String, String, String)>,
    lean_args: &[String],
    stub_targets: &[String],
    audit_all: bool,
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_inner_ext(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        allow_stub,
        eval_mode,
        file_name,
        timeout_ms,
        batch_fission_override,
        lean_args,
        stub_targets,
        audit_all,
        false,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn eval_with_zygote_pool_inner_ext(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
    eval_mode: bool,
    file_name: Option<&str>,
    timeout_ms: Option<u64>,
    batch_fission_override: Option<(String, String, String)>,
    lean_args: &[String],
    stub_targets: &[String],
    audit_all: bool,
    allow_sorry: bool,
    diagnose_hotspots: bool,
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_inner_with_context_ext(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        allow_stub,
        eval_mode,
        file_name,
        timeout_ms,
        batch_fission_override,
        lean_args,
        stub_targets,
        &[],
        audit_all,
        allow_sorry,
        diagnose_hotspots,
        None,
    )
    .map(|(rep, _, _)| rep)
}

pub(super) fn encode_mode_with_file_and_cwd(
    base: &str,
    env_vars: &std::collections::HashMap<String, String>,
    file_name: Option<&str>,
) -> String {
    let caller_cwd = env_vars
        .get("TURBO_LEAN_CALLER_CWD")
        .cloned()
        .or_else(|| {
            std::env::current_dir()
                .ok()
                .map(|p| p.to_string_lossy().to_string())
        })
        .unwrap_or_default();
    let hex_fn = file_name
        .filter(|s| !s.is_empty())
        .map(|s| hex_encode_bytes(s.as_bytes()))
        .unwrap_or_default();
    let hex_cwd = if caller_cwd.is_empty() {
        String::new()
    } else {
        hex_encode_bytes(caller_cwd.as_bytes())
    };
    if hex_fn.is_empty() && hex_cwd.is_empty() {
        base.to_string()
    } else {
        format!("{base}:{hex_fn}:{hex_cwd}")
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn eval_with_zygote_pool_inner_with_context_ext(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
    eval_mode: bool,
    file_name: Option<&str>,
    timeout_ms: Option<u64>,
    batch_fission_override: Option<(String, String, String)>,
    lean_args: &[String],
    stub_targets: &[String],
    extra_stubs: &[String],
    audit_all: bool,
    allow_sorry: bool,
    diagnose_hotspots: bool,
    initial_context: Option<&ResolvedZygoteContext>,
) -> Result<(ZygoteEvalReply, ClosureBinding, String)> {
    if !eval_mode && !diagnose_hotspots {
        crate::splitter::reject_checking_weakening(shard_source)?;
    }
    let request_started = std::time::Instant::now();
    crate::module_builder::validate_lean_args(lean_args)?;
    let base_stub_mode = if diagnose_hotspots {
        encode_mode_with_file_and_cwd("diagnose_hotspots", env_vars, file_name)
    } else if eval_mode {
        "eval".to_string()
    } else if audit_all {
        let shards = crate::splitter::split_lean_source(shard_source, &[]).shards;
        let fmap = crate::splitter::FastVerifyMap::parse_and_validate(shard_source, &shards)?;
        if !fmap.is_empty() {
            anyhow::bail!(
                "Fast-verify renamed declarations are forbidden in `strict_all` whole-file audits"
            );
        }
        encode_mode_with_file_and_cwd("strict_all", env_vars, file_name)
    } else {
        stub_mode_flag(allow_stub, stub_targets, extra_stubs, shard_source)?
    };
    let stub_mode = if !eval_mode && !diagnose_hotspots && allow_sorry {
        if base_stub_mode == "strict_all" {
            "allow_sorry".to_string()
        } else {
            format!("allow_sorry+{base_stub_mode}")
        }
    } else {
        base_stub_mode
    };
    let attempt = |timeout_ms: Option<u64>,
                   ctx: Option<&ResolvedZygoteContext>|
     -> Result<(ZygoteEvalReply, ClosureBinding, String)> {
        let (mut rep, binding, identity) = eval_with_zygote_pool_attempt(
            store,
            toolchain,
            req_lean_path,
            env_vars,
            lean_bin,
            shard_source,
            allow_stub,
            eval_mode,
            file_name,
            timeout_ms,
            batch_fission_override.clone(),
            lean_args,
            &stub_mode,
            stub_targets,
            request_started,
            ctx,
        )?;
        if !eval_mode
            && !diagnose_hotspots
            && rep.timeout_hotspots.is_empty()
            && rep.simp_hotspots.is_empty()
            && reply_indicates_timeout_or_heartbeat(&rep)
        {
            let probe_ms = timeout_ms.map(|ms| ms.clamp(250, 2_500)).or(Some(2_500));
            if let Some((th, sh)) = diagnose_hotspots_with_zygote_pool(
                store,
                toolchain,
                req_lean_path,
                env_vars,
                lean_bin,
                shard_source,
                file_name,
                probe_ms,
                lean_args,
            ) {
                rep.timeout_hotspots = th;
                rep.simp_hotspots = sh;
            }
        }
        Ok((rep, binding, identity))
    };
    let (rep, binding, identity) = attempt(timeout_ms, initial_context)?;
    if binding != ClosureBinding::Changed {
        return Ok((rep, binding, identity));
    }
    let (rep, binding, identity) = attempt(timeout_ms, None)?;
    if binding != ClosureBinding::Changed {
        return Ok((rep, binding, identity));
    }
    Ok((
        ZygoteEvalReply {
            kernel_gate_active: !eval_mode,
            errors: vec![CLOSURE_CHANGED_ERR.to_string()],
            messages: vec![CLOSURE_CHANGED_ERR.to_string()],
            ..Default::default()
        },
        ClosureBinding::Changed,
        identity,
    ))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn eval_with_zygote_pool_attempt(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
    eval_mode: bool,
    file_name: Option<&str>,
    timeout_ms: Option<u64>,
    batch_fission_override: Option<(String, String, String)>,
    lean_args: &[String],
    stub_mode: &str,
    stub_targets: &[String],
    request_started: std::time::Instant,
    pre_resolved_context: Option<&ResolvedZygoteContext>,
) -> Result<(ZygoteEvalReply, ClosureBinding, String)> {
    let mut effective_env = env_vars.clone();
    effective_env.extend(request_policy(env_vars));
    let env_vars = &effective_env;
    crate::module_builder::validate_lean_args(lean_args)?;
    let default_timeout_ms = if eval_mode { 900_000 } else { 90_000 };
    let effective_timeout_ms = timeout_ms.unwrap_or_else(|| {
        std::env::var("TURBO_LEAN_TIMEOUT_MS")
            .ok()
            .and_then(|v| v.trim().parse::<u64>().ok())
            .filter(|&ms| ms > 0)
            .unwrap_or(default_timeout_ms)
    });
    let deadline = request_started + std::time::Duration::from_millis(effective_timeout_ms);
    let _lifecycle = lifecycle_lock(false)?;

    // Validate the original arguments before encoding can discard unsupported flags.
    let args_digest_opt = crate::module_builder::compute_lean_args_digest(lean_args)?;
    let hex_opts = encode_lean_args_hex(lean_args);
    let (raw_imports_csv, body_code) = if let Some((ref imp, _, _)) = batch_fission_override {
        (imp.clone(), String::new())
    } else {
        split_shard_for_zygote(shard_source)
    };
    let owned_context;
    let context = match pre_resolved_context {
        Some(ctx) => ctx,
        None => {
            owned_context = resolve_zygote_context(
                toolchain,
                req_lean_path,
                env_vars,
                lean_bin,
                &raw_imports_csv,
            );
            &owned_context
        }
    };
    let closure = &context.closure;
    let effective_lean_path = context.worker_lean_path.clone();
    let imports_csv = context.imports_csv.clone();
    let closure_pool_digest = context.closure_pool_digest.clone();
    let toolchain_policy = context.toolchain_policy.clone();
    let lake_inputs_uncacheable = context.lake_inputs_uncacheable;
    let host_closure_digest = context.host_closure_digest.as_str();
    let executed_identity = context.identity.clone();
    let worker_scope_key = if closure.label().is_some() {
        format!("closure:{}", host_closure_digest)
    } else {
        effective_lean_path.clone()
    };
    let pool_key = (
        toolchain_policy.clone(),
        worker_scope_key,
        format!("{}#{}", closure_pool_digest, imports_csv),
    );
    let verified_cache_policy = match &args_digest_opt {
        Some(ad) => format!("{}#opts:{}", toolchain_policy, ad),
        None => toolchain_policy.clone(),
    };
    let warm_imports_tag = match &args_digest_opt {
        Some(ad) => format!("{}#opts:{}", imports_csv, ad),
        None => imports_csv.clone(),
    };

    #[allow(clippy::type_complexity)]
    static ZYGOTE_VERIFIED_SHARD_CACHE: std::sync::OnceLock<
        std::sync::Mutex<
            std::collections::HashMap<(String, String, String, String), ZygoteEvalReply>,
        >,
    > = std::sync::OnceLock::new();
    let is_allow_sorry_mode = stub_mode == "allow_sorry" || stub_mode.starts_with("allow_sorry+");
    let is_diagnose_mode =
        stub_mode == "diagnose_hotspots" || stub_mode.starts_with("diagnose_hotspots:");
    let verified_cache_key = if !eval_mode
        && !is_allow_sorry_mode
        && !is_diagnose_mode
        && !lake_inputs_uncacheable
        && batch_fission_override.is_none()
        && closure.label().is_some()
    {
        Some((
            verified_cache_policy,
            closure_pool_digest.clone(),
            stub_mode.to_string(),
            shard_source.to_string(),
        ))
    } else {
        None
    };
    if let Some(ref vkey) = verified_cache_key {
        let vcache = ZYGOTE_VERIFIED_SHARD_CACHE
            .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
        if let Ok(guard) = vcache.lock() {
            if let Some(cached) = guard.get(vkey) {
                let mut hit = cached.clone();
                hit.env_cache_hit = true;
                hit.import_us = 0;
                hit.prefix_us = 0;
                hit.elab_us = 1;
                return Ok((hit, ClosureBinding::Bound, executed_identity));
            }
        }
    }

    #[cfg(target_os = "linux")]
    let expected_pinned_dir = closure.materialized.as_ref().map(|m| m.dir_dev_ino);

    let spawn_zygote_worker = || -> Result<ZygoteChild> {
        let tools = crate::module_builder::ToolchainExecutables::from_lean(lean_bin)?;
        let lean_bin = tools.lean.as_path();
        let mut worker_env = env_vars.clone();
        tools.apply_env(&mut worker_env);
        let zygote_bin = ensure_zygote_binary(store, lean_bin, &worker_env)?;
        let mut cmd = Command::new(&zygote_bin);
        let default_stack_kb = worker_env
            .get("LEAN_STACK_SIZE_KB")
            .cloned()
            .or_else(|| std::env::var("LEAN_STACK_SIZE_KB").ok())
            .unwrap_or_else(|| "262144".to_string());
        #[cfg(target_os = "linux")]
        let spawn_dir_fd: Option<std::os::unix::io::OwnedFd> = match &closure.materialized {
            Some(m) => {
                use std::os::unix::io::{AsRawFd, FromRawFd};
                let dup_raw =
                    unsafe { libc::fcntl(m.dir_fd.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 32) };
                anyhow::ensure!(
                    dup_raw >= 0,
                    "Failed to dup closure snapshot fd: {}",
                    std::io::Error::last_os_error()
                );
                Some(unsafe { std::os::unix::io::OwnedFd::from_raw_fd(dup_raw) })
            }
            None => None,
        };
        #[cfg(target_os = "linux")]
        let child_lean_path = match (&closure.materialized, &spawn_dir_fd) {
            (Some(m), Some(fd)) => {
                use std::os::unix::io::AsRawFd;
                m.worker_spawn_lean_path(fd.as_raw_fd())
            }
            _ => effective_lean_path.clone(),
        };
        #[cfg(not(target_os = "linux"))]
        let child_lean_path = effective_lean_path.clone();

        cmd.envs(&worker_env)
            .env("LEAN_STACK_SIZE_KB", default_stack_kb)
            .env("LEAN_PATH", &child_lean_path)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped());
        for k in [
            "GH_TOKEN",
            "GITHUB_TOKEN",
            "OPENAI_API_KEY",
            "AWS_SECRET_ACCESS_KEY",
            "AWS_SESSION_TOKEN",
            "NPM_TOKEN",
            "CARGO_REGISTRY_TOKEN",
        ] {
            cmd.env_remove(k);
        }
        scrub_worker_api_keys(&mut cmd);
        if let Some(sysroot) = lean_bin.parent().and_then(|b| b.parent()) {
            cmd.env("LEAN_SYSROOT", sysroot);
        }
        if !toolchain.is_empty() && toolchain != "unknown" {
            cmd.env("ELAN_TOOLCHAIN", toolchain.trim());
        }
        #[cfg(target_os = "linux")]
        unsafe {
            use std::os::unix::io::AsRawFd;
            use std::os::unix::process::CommandExt;
            let parent = libc::getpid();
            let inherit_fd = spawn_dir_fd.as_ref().map(|f| f.as_raw_fd());
            cmd.pre_exec(move || {
                if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL) != 0 {
                    return Err(std::io::Error::last_os_error());
                }
                if libc::getppid() != parent {
                    libc::_exit(1);
                }
                if let Some(fd) = inherit_fd {
                    let flags = libc::fcntl(fd, libc::F_GETFD);
                    if flags < 0 || libc::fcntl(fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0 {
                        return Err(std::io::Error::last_os_error());
                    }
                }
                Ok(())
            });
        }
        cmd.env(
            "TURBO_LEAN_STAGING_DIR",
            crate::shm_cache::staging_shm_dir(),
        );
        let (owner, lifetime) = std::sync::mpsc::channel();
        let (send_child, receive_child) = std::sync::mpsc::sync_channel(1);
        std::thread::spawn(move || {
            #[cfg(target_os = "linux")]
            let hold_fd = spawn_dir_fd;
            let res = cmd.spawn();
            #[cfg(target_os = "linux")]
            drop(hold_fd);
            let _ = send_child.send(res);
            let _ = lifetime.recv();
        });
        let mut child = receive_child
            .recv()?
            .with_context(|| format!("Failed to spawn Zygote worker {:?}", zygote_bin))?;
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| anyhow::anyhow!("Missing Zygote stdin"))?;
        let stdout = BufReader::new(
            child
                .stdout
                .take()
                .ok_or_else(|| anyhow::anyhow!("Missing Zygote stdout"))?,
        );
        let stderr_tail = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_scan = std::sync::Arc::new(StderrScan::default());
        if let Some(mut child_stderr) = child.stderr.take() {
            let tail_clone = stderr_tail.clone();
            let scan_clone = stderr_scan.clone();
            std::thread::spawn(move || {
                use std::io::Read;
                let mut chunk = [0u8; 1024];
                while let Ok(n) = child_stderr.read(&mut chunk) {
                    if n == 0 {
                        break;
                    }
                    scan_clone.feed(&chunk[..n]);
                    if let Ok(mut g) = tail_clone.lock() {
                        g.extend_from_slice(&chunk[..n]);
                        if g.len() > ZYGOTE_STDERR_TAIL_CAP {
                            let excess = g.len() - ZYGOTE_STDERR_TAIL_CAP;
                            g.drain(..excess);
                        }
                    }
                }
            });
        }
        Ok(ZygoteWorkerProcess {
            child: Some(child),
            clone_pid: None,
            _owner: owner,
            stdin: worker_input(stdin),
            stdout: BufReader::new(worker_output(stdout.into_inner())),
            stderr_tail,
            stderr_scan,
            #[cfg(target_os = "linux")]
            pinned_snapshot_dir: expected_pinned_dir,
            spawn_lean_path: effective_lean_path.clone(),
            warm_prefixes: std::collections::HashSet::new(),
            warm_prefix_tree: Vec::new(),
            warm_imports: std::collections::HashMap::new(),
            request_count: 0,
            cold_import_us: None,
            is_master: false,
            _master: None,
        })
    };

    let governor = crate::shm_cache::MemoryBudgetGovernor::detect();
    let worker_rss_limit_mb = std::env::var("TURBO_LEAN_WORKER_RSS_LIMIT_MB")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .filter(|&mb| mb > 0)
        .unwrap_or_else(|| governor.worker_rss_limit_mb());
    let effective_rss_limit_mb = if std::env::var("TURBO_LEAN_WORKER_RSS_LIMIT_MB").is_ok()
        || std::env::var("TURBO_LEAN_MAX_MEMORY_MB").is_ok()
    {
        worker_rss_limit_mb
    } else {
        worker_rss_limit_mb.max(2048)
    };
    let max_global_idle = std::env::var("TURBO_LEAN_MAX_IDLE_ZYGOTES")
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .filter(|&n| n >= 1)
        .unwrap_or_else(|| governor.recommended_parallel_workers(1024).clamp(4, 8));
    #[cfg(test)]
    let max_global_idle = max_global_idle.max(64);
    let max_pool_per_key = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .max(4)
        .min(max_global_idle);

    #[allow(clippy::large_enum_variant)]
    enum WorkerReqOutcome {
        Reply(ZygoteEvalReply),
        TimedOut {
            elapsed_us: u64,
            peak_rss_mb: u64,
            stderr_tail: String,
            last_request: String,
        },
        Crashed(WorkerCrashDiagnostics),
    }

    let worker_timeout = |worker: &ZygoteChild, req_id: &str| WorkerReqOutcome::TimedOut {
        elapsed_us: request_started.elapsed().as_micros() as u64,
        peak_rss_mb: measure_process_rss_mb(worker.pid()),
        stderr_tail: snapshot_worker_stderr_tail(&worker.stderr_tail),
        last_request: req_id.to_string(),
    };

    let request_identity = format!(
        "imports={} file={} mode={} bytes={}",
        if imports_csv.is_empty() {
            "Init"
        } else {
            imports_csv.as_str()
        },
        file_name.unwrap_or("<zygote-shard>"),
        if eval_mode {
            "eval"
        } else if allow_stub {
            "allow_stub"
        } else {
            "strict"
        },
        shard_source.len()
    );

    let run_worker_req =
        |worker: &mut ZygoteChild, req_line: &str, req_id: &str| -> WorkerReqOutcome {
            if std::time::Instant::now() >= deadline {
                return worker_timeout(worker, req_id);
            }
            let pid = worker.pid();
            if worker.clone_pid.is_some() { run_digest_test_hook("cloned_worker_request"); }
            let rss_before = measure_process_rss_mb(pid);
            let scan_before = worker.stderr_scan.snapshot();
            if let Err(e) = worker
                .stdin
                .write_all(req_line.as_bytes())
                .and_then(|_| worker.stdin.flush())
            {
                let rss_now = measure_process_rss_mb(pid).max(rss_before);
                return WorkerReqOutcome::Crashed(build_worker_crash_diagnostics(
                    worker,
                    &format!("Failed to write to Zygote stdin: {}", e),
                    rss_now,
                    req_id,
                ));
            }
            let mut resp_line = String::new();
            match read_line_with_timeout(&mut worker.stdout, &mut resp_line, deadline) {
                Ok(None) => {
                    let rss_now = measure_process_rss_mb(pid).max(rss_before);
                    let stderr_tail = snapshot_worker_stderr_tail(&worker.stderr_tail);
                    WorkerReqOutcome::TimedOut {
                        elapsed_us: request_started.elapsed().as_micros() as u64,
                        peak_rss_mb: rss_now,
                        stderr_tail,
                        last_request: req_id.to_string(),
                    }
                }
                Ok(Some(0)) => {
                    let rss_now = measure_process_rss_mb(pid).max(rss_before);
                    WorkerReqOutcome::Crashed(build_worker_crash_diagnostics(
                        worker,
                        "Zygote worker closed stdout unexpectedly",
                        rss_now,
                        req_id,
                    ))
                }
                Ok(Some(_)) => match serde_json::from_str::<ZygoteEvalReply>(resp_line.trim()) {
                    Ok(mut parsed) => {
                        if let Some(us) = worker.cold_import_us.take() {
                            parsed.env_cache_hit = false;
                            parsed.import_us = us;
                        }
                        let rss_after = measure_process_rss_mb(pid);
                        parsed.rss_delta_mb = (rss_after as i64) - (rss_before as i64);
                        parsed.peak_rss_mb = rss_after.max(rss_before);
                        let stderr_panic = worker
                            .stderr_scan
                            .panicked_since(scan_before, ZYGOTE_STDERR_MARK_WAIT);
                        mark_runtime_panic(&mut parsed, stderr_panic);
                        parsed.scanner_version = ZYGOTE_SCANNER_VERSION;
                        parsed.replay_version = ZYGOTE_REPLAY_VERSION;
                        WorkerReqOutcome::Reply(parsed)
                    }
                    Err(e) => {
                        let rss_now = measure_process_rss_mb(pid).max(rss_before);
                        WorkerReqOutcome::Crashed(build_worker_crash_diagnostics(
                            worker,
                            &format!(
                                "Invalid JSON from Zygote worker ({}): {}",
                                e,
                                resp_line.trim()
                            ),
                            rss_now,
                            req_id,
                        ))
                    }
                },
                Err(e) => {
                    let rss_now = measure_process_rss_mb(pid).max(rss_before);
                    WorkerReqOutcome::Crashed(build_worker_crash_diagnostics(
                        worker,
                        &format!("Zygote stdout read error: {}", e),
                        rss_now,
                        req_id,
                    ))
                }
            }
        };

    let acquire_worker = || -> Result<ZygoteChild> {
        #[cfg(target_os = "linux")]
        if !lake_inputs_uncacheable && closure.label().is_some() && !daemon_disabled() {
            let masters = ZYGOTE_MASTERS.get_or_init(|| {
                // Explicit CLI exits bypass OneShotGuard::drop and static destructors.
                unsafe { libc::atexit(cleanup_zygote_processes); }
                Default::default()
            });
            let cached = masters.lock().map_err(|_| anyhow::anyhow!("Zygote masters poisoned"))?
                .get(&pool_key).cloned();
            let mut entry = cached;
            if let Some(existing) = &entry {
                let worker = existing.worker.lock().map_err(|_| anyhow::anyhow!("Zygote master poisoned"))?;
                let matches = owned_process_alive(worker.pid())
                    && worker.pinned_snapshot_dir == expected_pinned_dir
                    && worker.spawn_lean_path == effective_lean_path;
                drop(worker);
                if !matches {
                    let mut map = masters.lock().unwrap_or_else(|e| e.into_inner());
                    if map.get(&pool_key).is_some_and(|e| std::sync::Arc::ptr_eq(e, existing)) {
                        map.remove(&pool_key);
                    }
                    drop(map);
                    entry = None;
                }
            }
            if entry.is_none() {
                let mut master = spawn_zygote_worker()?;
                let warm = attach_host_closure_digest(&format!("{}\t\tstrict\n", imports_csv), host_closure_digest);
                if let WorkerReqOutcome::Reply(rep) = run_worker_req(&mut master, &warm, "warm clone master") {
                    if rep.ok && rep.import_ok && closure.binding() == ClosureBinding::Bound {
                        master.warm_imports.insert(imports_csv.clone(), closure_pool_digest.clone());
                        master.cold_import_us = Some(rep.import_us);
                        let rss = measure_process_rss_mb(master.pid());
                        if rss > effective_rss_limit_mb {
                            return Ok(master);
                        }
                        master.is_master = true;
                        let candidate = std::sync::Arc::new(ZygoteMasterEntry {
                            pid: master.pid(), worker: std::sync::Mutex::new(master),
                            last_used_seq: std::sync::atomic::AtomicU64::new(0),
                        });
                        candidate.touch();
                        let max_cached = std::env::var("TURBO_LEAN_MAX_ZYGOTE_MASTERS")
                            .ok()
                            .and_then(|v| v.parse::<usize>().ok())
                            .unwrap_or_else(|| {
                                (governor.recommended_parallel_workers(1024) / 2).clamp(1, 4)
                            })
                            .min(max_zygote_processes().saturating_sub(1));
                        let mut retired = Vec::new();
                        let mut map = masters.lock().unwrap_or_else(|e| e.into_inner());
                        if let Some(existing) = map.get(&pool_key) {
                            entry = Some(existing.clone());
                        } else {
                            while !map.is_empty()
                                && (map.len() >= max_cached
                                    || map
                                        .values()
                                        .map(|e| measure_process_rss_mb(e.pid))
                                        .sum::<u64>()
                                        .saturating_add(rss)
                                        > max_total_zygote_rss_mb())
                            {
                                let key = map
                                    .iter()
                                    .min_by_key(|(_, e)| {
                                        (
                                            std::sync::Arc::strong_count(e) != 1,
                                            e.last_used_seq
                                                .load(std::sync::atomic::Ordering::Relaxed),
                                        )
                                    })
                                    .unwrap()
                                    .0
                                    .clone();
                                retired.push(map.remove(&key).unwrap());
                            }
                            if max_cached > 0 && rss <= max_total_zygote_rss_mb() {
                                map.insert(pool_key.clone(), candidate.clone());
                            }
                            entry = Some(candidate.clone());
                        }
                        drop(map);
                        drop(retired);
                    }
                }
            }
            if let Some(entry) = entry {
                entry.touch();
                let mut master = entry.worker.lock().map_err(|_| anyhow::anyhow!("Zygote master poisoned"))?;
                if let Ok(mut worker) = master.fork_clone(deadline) {
                    mark_closure_snapshot_used(host_closure_digest);
                    worker.cold_import_us = master.cold_import_us.take();
                    worker._master = Some(entry.clone());
                    return Ok(worker);
                }
                drop(master);
                let mut map = masters.lock().unwrap_or_else(|e| e.into_inner());
                if map.get(&pool_key).is_some_and(|e| std::sync::Arc::ptr_eq(e, &entry)) {
                    map.remove(&pool_key);
                }
            }
        }
        spawn_zygote_worker()
    };

    #[allow(clippy::type_complexity)]
    let return_worker_to_pool = |pool_mutex: &std::sync::Mutex<
        std::collections::HashMap<(String, String, String), Vec<ZygoteWorkerProcess>>,
    >,
                                 key: (String, String, String),
                                 mut w: ZygoteChild| {
        if daemon_disabled() {
            drop(w);
            return;
        }
        w.request_count += 1;
        if w.request_count >= 256 {
            drop(w);
            return;
        }
        let pid = w.pid();
        let worker_rss_mb = measure_process_rss_mb(pid);
        if worker_rss_mb > effective_rss_limit_mb {
            drop(w);
            return;
        }
        govern_machine_wide_zygote_rss(pid, worker_rss_mb);
        if let Ok(mut pool) = pool_mutex.lock() {
            let mut total_idle: usize = pool.values().map(|v| v.len()).sum();
            if total_idle >= max_global_idle {
                let other_keys: Vec<(String, String, String)> =
                    pool.keys().filter(|k| **k != key).cloned().collect();
                for ok in other_keys {
                    if total_idle < max_global_idle {
                        break;
                    }
                    if let Some(ovec) = pool.get_mut(&ok) {
                        if let Some(evicted) = ovec.pop() {
                            drop(evicted);
                            total_idle = total_idle.saturating_sub(1);
                        }
                    }
                }
                pool.retain(|_, v| !v.is_empty());
            }
            let vec = pool.entry(key).or_default();
            while vec.len() >= max_pool_per_key || total_idle >= max_global_idle {
                if vec.is_empty() {
                    break;
                }
                let evict_idx = vec
                    .iter()
                    .position(|cand| cand.warm_prefixes.is_empty())
                    .unwrap_or(0);
                let _ = vec.remove(evict_idx);
                total_idle = total_idle.saturating_sub(1);
            }
            if vec.len() < max_pool_per_key && total_idle < max_global_idle {
                vec.push(w);
            } else {
                drop(w);
            }
        }
    };

    let pool_mutex =
        ZYGOTE_POOL.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));

    if !eval_mode && !is_diagnose_mode && body_code.contains("-- namespace _TurboCrossFileShard_1")
    {
        let blocks: Vec<String> = body_code
            .split("-- namespace _TurboCrossFileShard_")
            .filter_map(|part| {
                let t = part.trim();
                if t.is_empty() {
                    return None;
                }
                if t.as_bytes()
                    .first()
                    .map(|b| b.is_ascii_digit())
                    .unwrap_or(false)
                {
                    Some(format!("-- namespace _TurboCrossFileShard_{}\n", t))
                } else {
                    Some(format!("{}\n", t))
                }
            })
            .collect();
        if blocks.len() >= 2 && blocks.len() <= 4 {
            let needed = blocks.len();
            let mut workers: Vec<ZygoteChild> = Vec::with_capacity(needed);
            {
                let mut pool = pool_mutex
                    .lock()
                    .map_err(|_| anyhow::anyhow!("ZygotePool mutex poisoned"))?;
                let matching_keys: Vec<(String, String, String)> = vec![pool_key.clone()];
                for k in &matching_keys {
                    if let Some(vec) = pool.get_mut(k) {
                        vec.retain(|w| {
                            if !owned_process_alive(w.pid()) {
                                return false;
                            }
                            #[cfg(target_os = "linux")]
                            {
                                if w.pinned_snapshot_dir != expected_pinned_dir {
                                    return false;
                                }
                                if expected_pinned_dir.is_none()
                                    && w.spawn_lean_path != effective_lean_path
                                {
                                    return false;
                                }
                            }
                            #[cfg(not(target_os = "linux"))]
                            if w.spawn_lean_path != effective_lean_path {
                                return false;
                            }
                            (w.warm_imports.is_empty()
                                || (w.warm_imports.len() == 1
                                    && w.warm_imports.contains_key(&imports_csv)))
                                && w.warm_imports
                                    .get(&imports_csv)
                                    .map(|d| d == &closure_pool_digest)
                                    .unwrap_or(true)
                        });
                    }
                }
                for k in &matching_keys {
                    if workers.len() >= needed {
                        break;
                    }
                    if let Some(vec) = pool.get_mut(k) {
                        while workers.len() < needed {
                            if let Some(pos) = vec
                                .iter()
                                .rposition(|w| w.warm_imports.contains_key(&imports_csv))
                            {
                                workers.push(vec.swap_remove(pos));
                            } else {
                                break;
                            }
                        }
                    }
                }
                if let Some(vec) = pool.get_mut(&pool_key) {
                    while workers.len() < needed {
                        if let Some(pos) = vec.iter().rposition(|w| w.warm_imports.is_empty()) {
                            workers.push(vec.swap_remove(pos));
                        } else {
                            break;
                        }
                    }
                }
            }
            if !workers.is_empty() {
                mark_closure_snapshot_used(host_closure_digest);
            }
            while workers.len() < needed {
                workers.push(acquire_worker()?);
            }

            let req_lines: Vec<String> = blocks
                .iter()
                .map(|blk| -> Result<String> {
                    let hb = hex_encode_bytes(blk.as_bytes());
                    let mode_flag = block_stub_mode(stub_mode, stub_targets, blk)?;
                    let base = if hex_opts.is_empty() {
                        if mode_flag != "strict" {
                            format!("{}\t{}\t{}\n", imports_csv, hb, mode_flag)
                        } else {
                            format!("{}\t{}\n", imports_csv, hb)
                        }
                    } else {
                        format!("{}\t{}\t{}\t\t\t{}\n", imports_csv, hb, mode_flag, hex_opts)
                    };
                    Ok(attach_host_closure_digest(&base, host_closure_digest))
                })
                .collect::<Result<Vec<_>>>()?;

            let results: Vec<(ZygoteChild, WorkerReqOutcome)> = std::thread::scope(|s| {
                let req_id_ref = request_identity.as_str();
                let handles: Vec<_> = workers
                    .into_iter()
                    .zip(req_lines)
                    .map(|(mut w, rl)| {
                        s.spawn(move || {
                            let res = run_worker_req(&mut w, &rl, req_id_ref);
                            (w, res, rl)
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|h| {
                        let (mut w, mut res, rl) =
                            h.join().expect("Zygote parallel eval thread panicked");
                        if matches!(res, WorkerReqOutcome::Crashed(_))
                            && std::time::Instant::now() < deadline
                        {
                            if let Ok(retry) = spawn_zygote_worker() {
                                w = retry;
                                res = run_worker_req(&mut w, &rl, req_id_ref);
                            }
                        }
                        (w, res)
                    })
                    .collect()
            });

            run_digest_test_hook("after_worker_reply");
            let binding = closure.binding();
            let mut replies = Vec::with_capacity(needed);
            let mut first_err: Option<anyhow::Error> = None;
            for (mut w, res) in results {
                match res {
                    WorkerReqOutcome::Reply(r) => {
                        // A worker whose env is not proven to hold the hashed bytes is killed:
                        // its in-process env cache is labelled with this digest.
                        if binding == ClosureBinding::Bound
                            && r.import_ok
                            && !r.errors.iter().any(|e| e == RUNTIME_PANIC_ERR)
                        {
                            w.warm_imports
                                .insert(imports_csv.clone(), closure_pool_digest.clone());
                            return_worker_to_pool(pool_mutex, pool_key.clone(), w);
                        }
                        replies.push(r);
                    }
                    WorkerReqOutcome::TimedOut {
                        elapsed_us,
                        peak_rss_mb,
                        stderr_tail,
                        last_request,
                    } => {
                        drop(w);
                        return Ok((
                            ZygoteEvalReply::timed_out_reply(
                                eval_mode,
                                elapsed_us,
                                effective_timeout_ms,
                                peak_rss_mb,
                                stderr_tail,
                                Some(last_request),
                            ),
                            binding,
                            executed_identity,
                        ));
                    }
                    WorkerReqOutcome::Crashed(diag) => {
                        drop(w);
                        if first_err.is_none() {
                            first_err = Some(anyhow::anyhow!("{}", diag.message));
                        }
                    }
                }
            }
            if let Some(e) = first_err {
                return Err(e);
            }
            let import_ok = replies.iter().all(|r| r.import_ok);
            let ok = replies.iter().all(|r| r.ok);
            let kernel_gate_active = replies.iter().all(|r| r.kernel_gate_active);
            let env_cache_hit = replies.iter().all(|r| r.env_cache_hit);
            let prefix_cache_hit = replies.iter().all(|r| r.prefix_cache_hit);
            let import_us = replies.iter().map(|r| r.import_us).max().unwrap_or(0);
            let prefix_us = replies.iter().map(|r| r.prefix_us).max().unwrap_or(0);
            let elab_us = replies.iter().map(|r| r.elab_us).max().unwrap_or(0);
            let heartbeats: u64 = replies.iter().map(|r| r.heartbeats).sum();
            let proof_term_nodes: u64 = replies.iter().map(|r| r.proof_term_nodes).sum();
            let rss_delta_mb: i64 = replies.iter().map(|r| r.rss_delta_mb).max().unwrap_or(0);
            let peak_rss_mb: u64 = replies.iter().map(|r| r.peak_rss_mb).max().unwrap_or(0);
            let subshards_verified: usize = replies.iter().map(|r| r.subshards_verified).sum();
            let scanner_version = replies.iter().map(|r| r.scanner_version).min().unwrap_or(0);
            let replay_version = replies.iter().map(|r| r.replay_version).min().unwrap_or(0);
            let mut stdout = String::new();
            let mut messages = Vec::new();
            let mut errors = Vec::new();
            let mut used_constants = Vec::new();
            let mut decl_types = std::collections::BTreeMap::new();
            let mut used_sorry = false;
            let mut sorry_decls = Vec::new();
            let mut timeout_hotspots = Vec::new();
            let mut simp_hotspots = Vec::new();
            for r in replies {
                stdout.push_str(&r.stdout);
                messages.extend(r.messages);
                errors.extend(r.errors);
                decl_types.extend(r.decl_types);
                if r.used_sorry {
                    used_sorry = true;
                }
                for sd in r.sorry_decls {
                    if !sorry_decls.contains(&sd) {
                        sorry_decls.push(sd);
                    }
                }
                timeout_hotspots.extend(r.timeout_hotspots);
                simp_hotspots.extend(r.simp_hotspots);
                for c in r.used_constants {
                    if used_constants.len() < 32 && !used_constants.contains(&c) {
                        used_constants.push(c);
                    }
                }
            }
            if !sorry_decls.is_empty() {
                used_sorry = true;
            }
            let combined_rep = ZygoteEvalReply {
                ok,
                winning_candidate_idx: None,
                kernel_gate_active,
                import_ok,
                env_cache_hit,
                prefix_cache_hit,
                import_us,
                prefix_us,
                elab_us,
                heartbeats,
                proof_term_nodes,
                rss_delta_mb,
                peak_rss_mb,
                subshards_verified,
                stdout,
                messages,
                errors,
                used_constants,
                decl_types,
                used_sorry,
                sorry_decls,
                timeout_hotspots,
                simp_hotspots,
                scanner_version,
                replay_version,
                timed_out: false,
                crashed: false,
                ..Default::default()
            };
            if combined_rep.import_ok
                && combined_rep.ok
                && !combined_rep.used_sorry
                && combined_rep.sorry_decls.is_empty()
                && binding == ClosureBinding::Bound
            {
                if let Some(vkey) = verified_cache_key {
                    let vcache = ZYGOTE_VERIFIED_SHARD_CACHE
                        .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
                    if let Ok(mut guard) = vcache.lock() {
                        if guard.len() >= 2048 {
                            guard.clear();
                        }
                        guard.insert(vkey, combined_rep.clone());
                    }
                }
            }
            return Ok((combined_rep, binding, executed_identity));
        }
    }

    let (req_line, active_prefix_key, active_prefix_code) =
        if let Some((_, pk, rl)) = batch_fission_override {
            let warm_pk = if pk.is_empty() {
                None
            } else {
                Some(match &args_digest_opt {
                    Some(ad) => format!("{}:opts:{}", pk, ad),
                    None => pk,
                })
            };
            (rl, warm_pk, None)
        } else if !eval_mode && !is_diagnose_mode {
            if let Some((prefix_code, decl_code, prefix_key)) =
                split_body_into_prefix_and_decl(&body_code)
            {
                let hex_decl = hex_encode_bytes(decl_code.as_bytes());
                let hex_prefix = hex_encode_bytes(prefix_code.as_bytes());
                let mode_flag = stub_mode;
                let rl = if hex_opts.is_empty() {
                    format!(
                        "{}\t{}\t{}\t{}\t{}\n",
                        imports_csv, hex_decl, mode_flag, prefix_key, hex_prefix
                    )
                } else {
                    format!(
                        "{}\t{}\t{}\t{}\t{}\t{}\n",
                        imports_csv, hex_decl, mode_flag, prefix_key, hex_prefix, hex_opts
                    )
                };
                let warm_pk = match &args_digest_opt {
                    Some(ad) => format!("{}:opts:{}", prefix_key, ad),
                    None => prefix_key,
                };
                (rl, Some(warm_pk), Some(prefix_code))
            } else {
                let hex_body = hex_encode_bytes(body_code.as_bytes());
                let rl = if hex_opts.is_empty() {
                    if stub_mode != "strict" {
                        format!("{}\t{}\t{}\n", imports_csv, hex_body, stub_mode)
                    } else {
                        format!("{}\t{}\n", imports_csv, hex_body)
                    }
                } else {
                    let mode_flag = stub_mode;
                    format!(
                        "{}\t{}\t{}\t\t\t{}\n",
                        imports_csv, hex_body, mode_flag, hex_opts
                    )
                };
                (rl, None, None)
            }
        } else if is_diagnose_mode {
            let hex_body = hex_encode_bytes(body_code.as_bytes());
            let rl = if hex_opts.is_empty() {
                format!("{}\t{}\t{}\n", imports_csv, hex_body, stub_mode)
            } else {
                format!(
                    "{}\t{}\t{}\t\t\t{}\n",
                    imports_csv, hex_body, stub_mode, hex_opts
                )
            };
            (rl, None, None)
        } else {
            let mode_flag = encode_mode_with_file_and_cwd("eval", env_vars, file_name);
            if let Some((prefix_key, prefix_code, decl_code)) =
                split_eval_body_into_prefix_and_cmds(&body_code)
            {
                let hex_decl = hex_encode_bytes(decl_code.as_bytes());
                let hex_prefix = hex_encode_bytes(prefix_code.as_bytes());
                let rl = if hex_opts.is_empty() {
                    format!(
                        "{}\t{}\t{}\t{}\t{}\n",
                        imports_csv, hex_decl, mode_flag, prefix_key, hex_prefix
                    )
                } else {
                    format!(
                        "{}\t{}\t{}\t{}\t{}\t{}\n",
                        imports_csv, hex_decl, mode_flag, prefix_key, hex_prefix, hex_opts
                    )
                };
                let warm_pk = match &args_digest_opt {
                    Some(ad) => format!("{}:opts:{}", prefix_key, ad),
                    None => prefix_key,
                };
                (rl, Some(warm_pk), Some(prefix_code))
            } else {
                let hex_body = hex_encode_bytes(body_code.as_bytes());
                let rl = if hex_opts.is_empty() {
                    format!("{}\t{}\t{}\n", imports_csv, hex_body, mode_flag)
                } else {
                    format!(
                        "{}\t{}\t{}\t\t\t{}\n",
                        imports_csv, hex_body, mode_flag, hex_opts
                    )
                };
                (rl, None, None)
            }
        };
    let req_line = attach_host_closure_digest(&req_line, host_closure_digest);

    let mut worker = {
        let mut pool = pool_mutex
            .lock()
            .map_err(|_| anyhow::anyhow!("ZygotePool mutex poisoned"))?;
        let mut selected: Option<ZygoteChild> = None;
        let matching_keys: Vec<(String, String, String)> = vec![pool_key.clone()];
        for k in &matching_keys {
            if let Some(vec) = pool.get_mut(k) {
                vec.retain(|w| {
                    if !owned_process_alive(w.pid()) {
                        return false;
                    }
                    #[cfg(target_os = "linux")]
                    {
                        if w.pinned_snapshot_dir != expected_pinned_dir {
                            return false;
                        }
                        if expected_pinned_dir.is_none() && w.spawn_lean_path != effective_lean_path
                        {
                            return false;
                        }
                    }
                    #[cfg(not(target_os = "linux"))]
                    if w.spawn_lean_path != effective_lean_path {
                        return false;
                    }
                    (w.warm_imports.is_empty()
                        || (w.warm_imports.len() == 1 && w.warm_imports.contains_key(&imports_csv)))
                        && w.warm_imports
                            .get(&imports_csv)
                            .map(|d| d == &closure_pool_digest)
                            .unwrap_or(true)
                });
            }
        }
        if let Some(ref pk) = active_prefix_key {
            for k in &matching_keys {
                if let Some(vec) = pool.get_mut(k) {
                    if let Some(pos) = vec.iter().rposition(|w| {
                        w.warm_imports.contains_key(&imports_csv) && w.warm_prefixes.contains(pk)
                    }) {
                        selected = Some(vec.swap_remove(pos));
                        break;
                    }
                }
            }
        }
        if selected.is_none() {
            if let Some(ref p_code) = active_prefix_code {
                let mut best_lca: Option<((String, String, String), usize, usize)> = None;
                for k in &matching_keys {
                    if let Some(vec) = pool.get(k) {
                        for (idx, w) in vec.iter().enumerate() {
                            if !w.warm_imports.contains_key(&imports_csv) {
                                continue;
                            }
                            for (imp, anc_code) in &w.warm_prefix_tree {
                                if imp == &warm_imports_tag
                                    && p_code.starts_with(anc_code.as_str())
                                    && unsafe {
                                        turbo_spec_zygote_lca_reuse_safe(
                                            anc_code.len() as u64,
                                            p_code.len() as u64,
                                        ) != 0
                                    }
                                {
                                    let len = anc_code.len();
                                    if best_lca.as_ref().map(|(_, _, b)| len >= *b).unwrap_or(true)
                                    {
                                        best_lca = Some((k.clone(), idx, len));
                                    }
                                }
                            }
                        }
                    }
                }
                if let Some((best_k, best_idx, _)) = best_lca {
                    if let Some(vec) = pool.get_mut(&best_k) {
                        selected = Some(vec.swap_remove(best_idx));
                    }
                }
            }
        }
        if selected.is_none() {
            for k in &matching_keys {
                if let Some(vec) = pool.get_mut(k) {
                    if let Some(pos) = vec
                        .iter()
                        .rposition(|w| w.warm_imports.contains_key(&imports_csv))
                    {
                        selected = Some(vec.swap_remove(pos));
                        break;
                    }
                }
            }
        }
        if selected.is_none() {
            if let Some(vec) = pool.get_mut(&pool_key) {
                if let Some(pos) = vec.iter().rposition(|w| w.warm_imports.is_empty()) {
                    selected = Some(vec.swap_remove(pos));
                }
            }
        }
        selected
    };
    if worker.is_some() {
        mark_closure_snapshot_used(host_closure_digest);
    }
    if std::time::Instant::now() >= deadline {
        return Ok((
            ZygoteEvalReply::timed_out_reply(
                eval_mode,
                request_started.elapsed().as_micros() as u64,
                effective_timeout_ms,
                0,
                String::new(),
                Some(request_identity.clone()),
            ),
            ClosureBinding::Unproven,
            executed_identity,
        ));
    }
    if worker.is_none() {
        worker = Some(acquire_worker()?);
    }

    let mut w = worker.unwrap();
    let mut outcome = run_worker_req(&mut w, &req_line, &request_identity);
    if let WorkerReqOutcome::Crashed(first_diag) = outcome {
        drop(w);
        // Respawn and replay share the original request deadline, including on a cold worker.
        if std::time::Instant::now() >= deadline {
            return Ok((
                ZygoteEvalReply::timed_out_reply(
                    eval_mode,
                    request_started.elapsed().as_micros() as u64,
                    effective_timeout_ms,
                    first_diag.peak_rss_mb,
                    first_diag.stderr_tail,
                    first_diag.last_request,
                ),
                ClosureBinding::Unproven,
                executed_identity,
            ));
        }
        match spawn_zygote_worker() {
            Ok(retry_w) => w = retry_w,
            Err(_) => {
                let mut diag = first_diag;
                diag.message = format!("{} (respawn failed)", diag.message);
                return Ok((
                    ZygoteEvalReply::crashed_reply_with_diag(eval_mode, diag),
                    ClosureBinding::Unproven,
                    executed_identity,
                ));
            }
        }
        outcome = run_worker_req(&mut w, &req_line, &request_identity);
    }

    if std::time::Instant::now() >= deadline {
        outcome = worker_timeout(&w, &request_identity);
    }

    match outcome {
        WorkerReqOutcome::Reply(rep) => {
            run_digest_test_hook("after_worker_reply");
            let binding = closure.binding();
            let unusable = rep
                .errors
                .iter()
                .any(|e| e == RUNTIME_PANIC_ERR || e.contains("importsCsv changed"));
            // Only a worker proven to have imported the hashed bytes stays warm: its env cache
            // and every verdict are labelled with `imported_digest`.
            if binding == ClosureBinding::Bound
                && rep.import_ok
                && !unusable
                && !lake_inputs_uncacheable
            {
                w.warm_imports
                    .insert(imports_csv.clone(), closure_pool_digest.clone());
                if let Some(pk) = active_prefix_key {
                    w.warm_prefixes.insert(pk);
                }
                if let Some(p_code) = active_prefix_code {
                    w.warm_prefix_tree
                        .retain(|(imp, c)| !(imp == &warm_imports_tag && c == &p_code));
                    if w.warm_prefix_tree.len() >= 32 {
                        w.warm_prefix_tree.remove(0);
                    }
                    w.warm_prefix_tree.push((warm_imports_tag.clone(), p_code));
                }
                if rep.ok
                    && !rep.timed_out
                    && !rep.crashed
                    && !rep.used_sorry
                    && rep.sorry_decls.is_empty()
                {
                    if let Some(vkey) = verified_cache_key {
                        let vcache = ZYGOTE_VERIFIED_SHARD_CACHE.get_or_init(|| {
                            std::sync::Mutex::new(std::collections::HashMap::new())
                        });
                        if let Ok(mut guard) = vcache.lock() {
                            if guard.len() >= 2048 {
                                guard.clear();
                            }
                            guard.insert(vkey, rep.clone());
                        }
                    }
                }
                return_worker_to_pool(pool_mutex, pool_key, w);
            } else {
                drop(w);
            }
            Ok((rep, binding, executed_identity))
        }
        WorkerReqOutcome::TimedOut {
            elapsed_us,
            peak_rss_mb,
            stderr_tail,
            last_request,
        } => {
            drop(w);
            Ok((
                ZygoteEvalReply::timed_out_reply(
                    eval_mode,
                    elapsed_us,
                    effective_timeout_ms,
                    peak_rss_mb,
                    stderr_tail,
                    Some(last_request),
                ),
                ClosureBinding::Unproven,
                executed_identity,
            ))
        }
        WorkerReqOutcome::Crashed(diag) => {
            drop(w);
            Ok((
                ZygoteEvalReply::crashed_reply_with_diag(eval_mode, diag),
                ClosureBinding::Unproven,
                executed_identity,
            ))
        }
    }
}

/// Evaluate a single stubbed declaration signature (`allow_stub = true`) on top of `prefix_source`
/// so cut-fission can verify `decl_types` matches `expected_kernel_type_hash` in the prefix context.
#[allow(clippy::too_many_arguments)]
pub(crate) fn probe_stub_decl_types_via_zygote(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    prefix_source: &str,
    stub_decl_source: &str,
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    let (imports_csv, prefix_body) = split_shard_for_zygote(prefix_source);
    let mut decl = stub_decl_source.trim_end().to_string();
    decl.push('\n');
    let hex_decl = hex_encode_bytes(decl.as_bytes());
    let hex_opts = encode_lean_args_hex(lean_args);
    let (prefix_key, req_line) = if prefix_body.trim().is_empty() {
        let rl = if hex_opts.is_empty() {
            format!("{}\t{}\tprobe_stub\n", imports_csv, hex_decl)
        } else {
            format!(
                "{}\t{}\tprobe_stub\t\t\t{}\n",
                imports_csv, hex_decl, hex_opts
            )
        };
        (String::new(), rl)
    } else {
        let pk = blake3::hash(prefix_body.as_bytes()).to_hex().to_string();
        let hex_prefix = hex_encode_bytes(prefix_body.as_bytes());
        let rl = if hex_opts.is_empty() {
            format!(
                "{}\t{}\tprobe_stub\t{}\t{}\n",
                imports_csv, hex_decl, pk, hex_prefix
            )
        } else {
            format!(
                "{}\t{}\tprobe_stub\t{}\t{}\t{}\n",
                imports_csv, hex_decl, pk, hex_prefix, hex_opts
            )
        };
        (pk, rl)
    };
    eval_with_zygote_pool_inner(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        "",
        true,
        false,
        None,
        None,
        Some((imports_csv, prefix_key, req_line)),
        lean_args,
        &[],
        false,
    )
}
#[allow(clippy::too_many_arguments)]
pub fn eval_shard_via_zygote(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    prefix_source: &str,
    sub_decl_source: &str,
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    let combined_source = if prefix_source.trim().is_empty() {
        format!("{}\n", sub_decl_source.trim_end())
    } else {
        format!(
            "{}\n\n{}\n",
            prefix_source.trim_end(),
            sub_decl_source.trim_start()
        )
    };
    let ns_prefix = crate::splitter::open_namespace_prefix(prefix_source);
    let scoped_sub = if ns_prefix.is_empty() {
        std::borrow::Cow::Borrowed(sub_decl_source)
    } else {
        std::borrow::Cow::Owned(format!("{}{}", ns_prefix, sub_decl_source))
    };
    let sub_targets: Vec<String> = crate::splitter::split_lean_source(&scoped_sub, &[])
        .shards
        .into_iter()
        .map(|s| s.rooted_name())
        .collect();
    if sub_targets.is_empty() {
        return eval_with_zygote_pool_with_args(
            store,
            toolchain,
            req_lean_path,
            env_vars,
            lean_bin,
            &combined_source,
            false,
            lean_args,
        );
    }
    eval_with_zygote_pool_for_targets(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        &combined_source,
        &sub_targets,
        None,
        lean_args,
    )
}

/// Evaluate a batch of cut-fission sub-shards (`prefix_source` + each `sub_decl` in `sub_decl_sources`)
/// Evaluate a batch of sub-proof cuts (`sub_decl_sources`) against a shared `prefix_source`
/// in a single IPC roundtrip over the warm `ZygotePool` (`batch_fission` mode).
/// Each sub-shard is elaborated from the clean functional `ckptState` checkpoint (bounding peak heap
/// by a single `have` block) and individually audited by `auditNewKernelDecls` (`0 sorryAx`).
#[allow(dead_code)]
pub(super) fn encode_multi_decl_zygote_req(
    prefix_source: &str,
    mode: &str,
    decl_sources: &[String],
    lean_args: &[String],
) -> Result<(String, String, String)> {
    let (imports_csv, prefix_body) = split_shard_for_zygote(prefix_source);
    let prefix_key = blake3::hash(prefix_body.as_bytes()).to_hex().to_string();
    let hex_prefix = hex_encode_bytes(prefix_body.as_bytes());
    let ns_prefix = crate::splitter::open_namespace_prefix(prefix_source);
    let mut targets: Vec<String> = Vec::new();
    for s in decl_sources {
        let scoped = if ns_prefix.is_empty() {
            std::borrow::Cow::Borrowed(s.as_str())
        } else {
            std::borrow::Cow::Owned(format!("{}{}", ns_prefix, s))
        };
        let sub_shards = crate::splitter::split_lean_source(&scoped, &[]).shards;
        let sub_map = crate::splitter::FastVerifyMap::parse_and_validate(&scoped, &sub_shards)?;
        if !sub_map.is_empty() {
            anyhow::bail!(
                "Fast-verify renamed declarations are forbidden in `{}` sub-shards",
                mode
            );
        }
        for sh in sub_shards {
            let rooted = sh.rooted_name();
            if !targets.contains(&rooted) {
                targets.push(rooted);
            }
        }
    }
    let target_set: std::collections::HashSet<String> = targets.iter().cloned().collect();
    let prefix_shards = crate::splitter::split_lean_source(prefix_source, &[]).shards;
    let prefix_map =
        crate::splitter::FastVerifyMap::parse_and_validate(prefix_source, &prefix_shards)?;
    if !prefix_map.is_empty() {
        anyhow::bail!(
            "Fast-verify renamed declarations are forbidden in `{}` prefix",
            mode
        );
    }
    let stubs: Vec<String> = prefix_shards
        .into_iter()
        .filter(|sh| {
            crate::splitter::strip_lean_comments(&sh.proof_text).trim() == "sorry"
                && !prefix_map.shard_matches_targets(sh, &target_set)
        })
        .map(|sh| sh.rooted_name())
        .collect();
    let mode_with_stubs = if stubs.is_empty() && targets.is_empty() {
        mode.to_string()
    } else {
        format!(
            "{}:{}:{}",
            mode,
            hex_encode_bytes(targets.join("\n").as_bytes()),
            hex_encode_bytes(stubs.join("\n").as_bytes())
        )
    };
    let hex_decls_csv = decl_sources
        .iter()
        .map(|s| {
            let mut decl = s.trim_end().to_string();
            decl.push('\n');
            hex_encode_bytes(decl.as_bytes())
        })
        .collect::<Vec<_>>()
        .join(",");
    let hex_opts = encode_lean_args_hex(lean_args);
    let req_line = if hex_opts.is_empty() {
        format!(
            "{}\t{}\t{}\t{}\t{}\n",
            imports_csv, mode_with_stubs, prefix_key, hex_prefix, hex_decls_csv
        )
    } else {
        format!(
            "{}\t{}\t{}\t{}\t{}\t{}\n",
            imports_csv, mode_with_stubs, prefix_key, hex_prefix, hex_decls_csv, hex_opts
        )
    };
    Ok((imports_csv, prefix_key, req_line))
}

#[allow(clippy::too_many_arguments)]
pub fn eval_subshards_batch_via_zygote(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    prefix_source: &str,
    sub_decl_sources: &[String],
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    crate::splitter::reject_checking_weakening(prefix_source)?;
    for source in sub_decl_sources {
        crate::splitter::reject_checking_weakening(source)?;
    }
    crate::module_builder::validate_lean_args(lean_args)?;
    if sub_decl_sources.is_empty() {
        return Ok(ZygoteEvalReply {
            ok: true,
            kernel_gate_active: true,
            import_ok: true,
            env_cache_hit: true,
            prefix_cache_hit: true,
            ..Default::default()
        });
    }
    let req_tuple =
        encode_multi_decl_zygote_req(prefix_source, "batch_fission", sub_decl_sources, lean_args)?;
    eval_with_zygote_pool_inner(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        "",
        false,
        false,
        None,
        None,
        Some(req_tuple),
        lean_args,
        &[],
        false,
    )
}

/// Evaluate an ordered list of candidate declarations (`candidate_decl_sources`) against a shared
/// `prefix_source` in a single IPC roundtrip (`race_candidates` mode).
/// The Zygote worker checkpoints `prefix_source` once and tests each candidate in order, stopping
/// immediately at the first candidate that elaborates cleanly and passes `auditNewKernelDecls` (`0 sorryAx`),
/// returning its index in `reply.winning_candidate_idx`.
#[allow(clippy::too_many_arguments)]
pub fn eval_candidates_race_via_zygote(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    prefix_source: &str,
    candidate_decl_sources: &[String],
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    crate::splitter::reject_checking_weakening(prefix_source)?;
    for source in candidate_decl_sources {
        crate::splitter::reject_checking_weakening(source)?;
    }
    crate::module_builder::validate_lean_args(lean_args)?;
    if candidate_decl_sources.is_empty() {
        return Ok(ZygoteEvalReply {
            kernel_gate_active: true,
            import_ok: true,
            env_cache_hit: true,
            prefix_cache_hit: true,
            errors: vec!["no candidate declarations provided".to_string()],
            ..Default::default()
        });
    }
    let req_tuple = encode_multi_decl_zygote_req(
        prefix_source,
        "race_candidates",
        candidate_decl_sources,
        lean_args,
    )?;
    eval_with_zygote_pool_inner(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        "",
        false,
        false,
        None,
        None,
        Some(req_tuple),
        lean_args,
        &[],
        false,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn ensure_prefix_outline_olean(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    outline_source: &str,
    file_name: &str,
    lean_args: &[String],
) -> Result<(PathBuf, String)> {
    crate::splitter::reject_checking_weakening(outline_source)?;
    crate::module_builder::validate_lean_args(lean_args)?;
    let (raw_imports_csv, body_code) = split_shard_for_zygote(outline_source);
    if raw_imports_csv == "__HEADER_ERR__" {
        anyhow::bail!("Unsupported header in prefix outline source");
    }
    let context = resolve_zygote_context(
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        &raw_imports_csv,
    );
    let args_digest = crate::module_builder::compute_lean_args_digest(lean_args)?;
    let mut key_hasher = blake3::Hasher::new();
    key_hasher.update(b"turbo-prefix-outline:v2\0");
    key_hasher.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    key_hasher.update(b"\0");
    key_hasher.update(context.toolchain_policy.as_bytes());
    key_hasher.update(b"\0");
    key_hasher.update(context.closure_pool_digest.as_bytes());
    key_hasher.update(b"\0");
    key_hasher.update(context.imports_csv.as_bytes());
    key_hasher.update(b"\0");
    if let Some(ref ad) = args_digest {
        key_hasher.update(ad.as_bytes());
    }
    key_hasher.update(b"\0");
    key_hasher.update(outline_source.as_bytes());
    let key_hex = key_hasher.finalize().to_hex().to_string();
    let outline_mod = format!("_TurboOutline_{}", &key_hex[..24]);

    let outline_dir = store.fast_staging_dir().join("prefix_outlines");
    fs::create_dir_all(&outline_dir)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        if let Ok(m) = fs::symlink_metadata(&outline_dir) {
            if m.is_dir() && m.uid() == unsafe { libc::geteuid() } && m.mode() & 0o077 != 0 {
                let mut p = m.permissions();
                p.set_mode(0o700);
                let _ = fs::set_permissions(&outline_dir, p);
            }
        }
    }
    let final_olean = outline_dir.join(format!("{}.olean", outline_mod));
    if final_olean.is_file() && final_olean.metadata().map(|m| m.len() > 0).unwrap_or(false) {
        return Ok((outline_dir, outline_mod));
    }

    let lock_path = outline_dir.join(format!("{}.lock", outline_mod));
    let _flock = crate::shm_cache::acquire_flock(&lock_path, true, false).ok();
    if final_olean.is_file() && final_olean.metadata().map(|m| m.len() > 0).unwrap_or(false) {
        return Ok((outline_dir, outline_mod));
    }

    let tmp_olean = outline_dir.join(format!(
        ".{}.tmp.{}.{}.olean",
        outline_mod,
        std::process::id(),
        next_tmp_id()
    ));
    let outline_shards = crate::splitter::split_lean_source(outline_source, &[]).shards;
    let stubs: Vec<String> = outline_shards
        .into_iter()
        .filter(|sh| crate::splitter::strip_lean_comments(&sh.proof_text).trim() == "sorry")
        .map(|sh| sh.rooted_name())
        .collect();
    let mode = format!(
        "emit_outline_olean:{}:{}:{}:{}",
        hex_encode_bytes(outline_mod.as_bytes()),
        hex_encode_bytes(tmp_olean.to_string_lossy().as_bytes()),
        hex_encode_bytes(file_name.as_bytes()),
        hex_encode_bytes(stubs.join("\n").as_bytes()),
    );
    let hex_body = hex_encode_bytes(body_code.as_bytes());
    let hex_opts = encode_lean_args_hex(lean_args);
    let req_line = if hex_opts.is_empty() {
        format!("{}\t{}\t{}\n", context.imports_csv, hex_body, mode)
    } else {
        format!(
            "{}\t{}\t{}\t\t\t{}\n",
            context.imports_csv, hex_body, mode, hex_opts
        )
    };
    let res = eval_with_zygote_pool_inner(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        "",
        false,
        false,
        Some(file_name),
        None,
        Some((context.imports_csv.clone(), String::new(), req_line)),
        lean_args,
        &[],
        false,
    );
    match res {
        Ok(rep)
            if rep.import_ok
                && rep.ok
                && !rep.timed_out
                && !rep.crashed
                && tmp_olean.metadata().map(|m| m.len() > 0).unwrap_or(false) =>
        {
            fs::rename(&tmp_olean, &final_olean)?;
            Ok((outline_dir, outline_mod))
        }
        Ok(rep) => {
            let _ = fs::remove_file(&tmp_olean);
            anyhow::bail!(
                "Prefix outline `.olean` emission failed for `{}`: {}",
                outline_mod,
                rep.errors.join("\n")
            );
        }
        Err(e) => {
            let _ = fs::remove_file(&tmp_olean);
            Err(e)
        }
    }
}

pub(super) fn is_pure_eval_source(source: &str) -> bool {
    !source.contains("IO.FS")
        && !source.contains("IO.mono")
        && !source.contains("IO.rand")
        && !source.contains("IO.getEnv")
        && !source.contains("IO.Process")
        && !source.contains("System.FilePath")
}

/// One `Lean.importModules` for both `Midnight.Spec` and `ProofKit`.
/// `ProofKit` only pulls `Compiler.CompilationModel`, which `Midnight.Spec`
/// already imports, so loading them together is ~one import, not two.
pub(crate) fn coalesce_proofkit_imports(imports_csv: &str, lean_path: &str) -> String {
    if imports_csv == "__HEADER_ERR__" {
        return imports_csv.to_string();
    }
    let is_mod = imports_csv.split(',').any(|m| m.trim() == "__MODULE__");
    let has_midnight = imports_csv
        .split(',')
        .filter_map(parse_zygote_import_entry)
        .any(|(m, _, _, _)| m == "Midnight.Spec");
    let has_proofkit = imports_csv
        .split(',')
        .filter_map(parse_zygote_import_entry)
        .any(|(m, _, _, _)| m == "ProofKit");
    if !is_mod
        && has_midnight
        && !has_proofkit
        && lean_path
            .split(':')
            .any(|d| !d.is_empty() && Path::new(d).join("ProofKit.olean").exists())
    {
        format!("{},ProofKit", imports_csv)
    } else {
        imports_csv.to_string()
    }
}

/// The cache file name, keyed by `context.identity` (which covers the imported-closure snapshot).
/// A reply may only be stored under it once `context.closure` `rebind`s as `Bound` after the
/// eval (`write_eval_shm_cache`).
pub(super) fn compute_eval_shm_cache_filename(
    context: &ResolvedZygoteContext,
    file_name: &str,
    caller_cwd: Option<&str>,
    source: &str,
    lean_args: &[String],
) -> Result<String> {
    let args_digest = crate::module_builder::compute_lean_args_digest(lean_args)?;
    // v8: scanner v5 + kernel replay + `decl_types` kernel statement hashes + fast-verify/stub-mode.
    let bytes = serde_json::to_vec(&(
        "eval-shm:v9",
        crate::TURBO_LEAN_BUILD_EPOCH,
        ZYGOTE_SCANNER_VERSION,
        ZYGOTE_REPLAY_VERSION,
        &context.identity,
        file_name,
        caller_cwd,
        source,
        args_digest,
    ))?;
    let key_hex = blake3::hash(&bytes).to_hex().to_string();
    Ok(format!("ev_{}.json", &key_hex[..24]))
}

/// Only successful, import-clean replies may be cached: failures (missing toolchain, import
/// errors, ...) are environmental and must be re-evaluated rather than replayed forever.
/// Only replies vetted by the current host scanner are cacheable.
pub(super) fn eval_reply_cacheable(rep: &ZygoteEvalReply) -> bool {
    rep.ok
        && rep.import_ok
        && !rep.crashed
        && !rep.timed_out
        && !rep.used_sorry
        && rep.sorry_decls.is_empty()
        && verifier_provenance_ok(rep.scanner_version, rep.replay_version)
}

/// Write an eval reply into `eval_shm_cache/` and periodically enforce the `/dev/shm` quota.
/// Nothing is written unless `closure` (the snapshot keying `path`) provably still describes
/// the bytes the eval imported.
pub(super) fn write_eval_shm_cache(path: &Path, closure: &ClosureSnapshot, bytes: &[u8]) {
    run_digest_test_hook("before_eval_shm_write");
    if closure.label().is_none() || closure.binding() != ClosureBinding::Bound {
        return;
    }
    static WRITES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    // A failed write (e.g. ENOSPC) also counts: evict so a full cache can recover.
    let wrote = crate::shm_cache::atomic_write_shm(path, bytes).is_ok();
    let Some(dir) = path.parent() else { return };
    if !wrote {
        // Pressure-driven: the quota may not be exceeded yet (small or shared /dev/shm), so
        // halve what the cache holds and retry once.
        let held: u64 = fs::read_dir(dir)
            .into_iter()
            .flatten()
            .flatten()
            .filter_map(|e| e.metadata().ok())
            .map(|m| m.len())
            .sum();
        let _ = crate::shm_cache::enforce_shm_quota_lru(dir, (held / 2).max(1));
        let _ = crate::shm_cache::atomic_write_shm(path, bytes);
    } else if WRITES
        .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        .is_multiple_of(32)
    {
        let _ = crate::shm_cache::enforce_shm_quota_lru(dir, 0);
    }
}

pub(super) fn read_cached_eval_shm_reply(path: &Path) -> Option<ZygoteEvalReply> {
    let bytes = crate::shm_cache::read_verified_private_file_at(path)?;
    let mut cached_rep: ZygoteEvalReply = serde_json::from_slice(&bytes).ok()?;
    // Fail closed on entries without current provenance (older hosts, foreign writers).
    if !eval_reply_cacheable(&cached_rep) {
        let _ = fs::remove_file(path);
        return None;
    }
    cached_rep.env_cache_hit = true;
    cached_rep.prefix_cache_hit = true;
    cached_rep.import_us = 0;
    cached_rep.prefix_us = 0;
    Some(cached_rep)
}

pub fn try_stateless_eval_shm_cache(
    cache_root: &Path,
    file: &Path,
    project_dir: Option<&Path>,
    lean_path: Option<&str>,
) -> Option<(String, ZygoteEvalReply)> {
    let source = fs::read_to_string(file).ok()?;
    if !is_pure_eval_source(&source) {
        return None;
    }
    let proj_dir = project_dir
        .map(crate::lake_build::find_project_root)
        .unwrap_or_else(|| crate::lake_build::find_project_root(file));
    if crate::lake_build::has_lake_config(&proj_dir) {
        crate::module_builder::try_project_lake_inputs_tag(&proj_dir).ok()?;
    }
    let may_declare_inputs = crate::module_builder::workspace_may_declare_lake_inputs(&proj_dir);
    let explicit_lp: Option<String> = lean_path
        .map(str::to_string)
        .or_else(|| std::env::var("LEAN_PATH").ok());
    let req_lp = match explicit_lp {
        Some(lp) => lp,
        None if !crate::lake_build::has_lake_config(&proj_dir) => String::new(),
        None if !may_declare_inputs
            && !proj_dir.join(".lake/packages").is_dir()
            && proj_dir.join(".lake/build/lib/lean").exists() =>
        {
            let canon_proj = proj_dir.canonicalize().unwrap_or_else(|_| proj_dir.clone());
            crate::lake_build::resolve_remote_lean_path(&canon_proj, None)
        }
        None => return None,
    };
    let toolchain = crate::lake_build::detect_toolchain(&proj_dir);
    let resolved_lean_args =
        crate::module_builder::try_resolve_lean_args_for_path(&proj_dir, Some(file)).ok()?;
    let caller_cwd = std::env::current_dir()
        .ok()
        .map(|p| p.to_string_lossy().to_string());
    let file_display = file.to_string_lossy();
    let (lean_bin, _, _, _) =
        crate::module_builder::resolve_toolchain_compiler(&proj_dir, &toolchain).ok()?;
    let mut env_vars: std::collections::HashMap<String, String> = std::env::vars().collect();
    if crate::lake_build::has_lake_config(&proj_dir) {
        let canon_proj = proj_dir.canonicalize().unwrap_or_else(|_| proj_dir.clone());
        env_vars.insert(
            "TURBO_LEAN_PROJECT_DIR".to_string(),
            canon_proj.to_string_lossy().to_string(),
        );
    }
    let (imports_csv, _) = split_shard_for_zygote(&source);
    let context = resolve_zygote_context(&toolchain, &req_lp, &env_vars, &lean_bin, &imports_csv);
    if context.lake_inputs_uncacheable {
        return None;
    }
    let filename = compute_eval_shm_cache_filename(
        &context,
        &file_display,
        caller_cwd.as_deref(),
        &source,
        &resolved_lean_args,
    )
    .ok()?;
    let base_staging =
        if Path::new("/dev/shm").is_dir() || std::env::var("TURBO_LEAN_STAGING_DIR").is_ok() {
            crate::shm_cache::ensure_verified_private_staging_dir(None)
                .unwrap_or_else(|| cache_root.join("staging"))
        } else {
            cache_root.join("staging")
        };
    let path = base_staging.join("eval_shm_cache").join(filename);
    let cached_rep = read_cached_eval_shm_reply(&path)?;
    Some((source, cached_rep))
}

#[allow(clippy::too_many_arguments)]
pub fn try_local_zygote_eval(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    toolchain: &str,
    lean_path: &str,
    source: &str,
    file_name: Option<&str>,
    timeout_ms: u64,
) -> Option<ZygoteEvalReply> {
    try_local_zygote_eval_with_args(
        store,
        env_vars,
        lean_bin,
        toolchain,
        lean_path,
        source,
        file_name,
        timeout_ms,
        &[],
    )
    .ok()
    .flatten()
}

#[derive(Debug, Deserialize)]
pub(super) struct DaemonEvalEnvelope {
    #[serde(flatten)]
    pub(super) reply: ZygoteEvalReply,
    #[serde(default)]
    pub(super) executed_execution_identity: Option<String>,
    #[serde(default)]
    pub(super) binding_ok: bool,
}

impl std::ops::Deref for DaemonEvalEnvelope {
    type Target = ZygoteEvalReply;
    fn deref(&self) -> &Self::Target {
        &self.reply
    }
}

pub(super) fn finish_eval_http_request(response: Result<Vec<u8>>) -> Result<Option<DaemonEvalEnvelope>> {
    match response {
        Ok(bytes) => serde_json::from_slice::<DaemonEvalEnvelope>(&bytes)
            .map(Some)
            .map_err(|err| anyhow::anyhow!("unparseable zygote /eval reply: {err}")),
        Err(err) if is_expired_daemon_transport_error(&err) => Ok(None),
        Err(err) => Err(extract_http_error_detail(err)),
    }
}

#[allow(clippy::too_many_arguments)]
pub fn try_local_zygote_eval_with_args(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    toolchain: &str,
    lean_path: &str,
    source: &str,
    file_name: Option<&str>,
    timeout_ms: u64,
    lean_args: &[String],
) -> Result<Option<ZygoteEvalReply>> {
    let filtered_args = match crate::module_builder::validate_effective_lean_args(lean_args) {
        Ok(args) => args,
        Err(error) => {
            return Ok(Some(ZygoteEvalReply {
                errors: vec![format!("{error:#}")],
                ..Default::default()
            }))
        }
    };
    let effective_tc = if toolchain.is_empty() || toolchain == "unknown" {
        "leanprover/lean4:v4.35.0"
    } else {
        toolchain
    };
    let resolved_lean_bin;
    let lean_bin = if !lean_bin.exists() && lean_bin.components().count() == 1 {
        match crate::server::resolve_server_lean_env_and_bin(store, effective_tc, "") {
            Ok((_, bin)) => {
                resolved_lean_bin = bin;
                resolved_lean_bin.as_path()
            }
            Err(_) => lean_bin,
        }
    } else {
        lean_bin
    };
    let (imports_csv, _) = split_shard_for_zygote(source);
    let context = resolve_zygote_context(effective_tc, lean_path, env_vars, lean_bin, &imports_csv);
    let timeout_ms = if timeout_ms > 0 {
        timeout_ms
    } else {
        invocation_timeout_ms().unwrap_or(0)
    };
    let t0 = std::time::Instant::now();
    let caller_cwd = env_vars.get("TURBO_LEAN_CALLER_CWD").cloned().or_else(|| {
        std::env::current_dir()
            .ok()
            .map(|p| p.to_string_lossy().to_string())
    });
    let eval_shm_file = if !context.lake_inputs_uncacheable && is_pure_eval_source(source) {
        let filename = compute_eval_shm_cache_filename(
            &context,
            file_name.unwrap_or(""),
            caller_cwd.as_deref(),
            source,
            &filtered_args,
        )?;
        let dir = store.fast_staging_dir().join("eval_shm_cache");
        if crate::shm_cache::ensure_private_dir_all(&dir).is_ok() {
            let path = dir.join(filename);
            if let Some(cached_rep) = read_cached_eval_shm_reply(&path) {
                return Ok(Some(cached_rep));
            }
            Some(path)
        } else {
            None
        }
    } else {
        None
    };

    let existing_daemon = if daemon_disabled() {
        None
    } else {
        current_exe_daemon_paths(store)
            .and_then(|(_, exe_mtime_sec, exe_mtime_nsec, _, state_file)| {
                #[cfg(test)]
                if let Some(injected) = check_existing_daemon_state(&store.root.join("zygote_daemon.json"), exe_mtime_sec, exe_mtime_nsec, false) {
                    return Some(injected);
                }
                check_existing_daemon_state(&state_file, exe_mtime_sec, exe_mtime_nsec, false)
        .or_else(|| {
            check_existing_daemon_state(
                            &store.root.join("zygote_daemon.json"),
                            exe_mtime_sec,
                            exe_mtime_nsec,
                            false,
                        )
                    })
            })
            .or_else(|| ensure_local_zygote_daemon_with_token(store, env_vars))
    };

    let Some((base_url, auth_token)) = existing_daemon else {
        anyhow::ensure!(cfg!(test) || daemon_disabled(), "Shared daemon startup failed; set TURBO_LEAN_NO_DAEMON=1 for in-process execution");
        let (rep, executed_binding, executed_identity) = eval_with_resolved_context_opts_with_args(
            store,
            effective_tc,
            lean_path,
            env_vars,
            lean_bin,
            source,
            false,
            true,
            file_name,
            if timeout_ms > 0 {
                Some(timeout_ms)
            } else {
                None
            },
            &filtered_args,
            Some(&context),
        )?;
        if eval_reply_cacheable(&rep) {
            if executed_binding == ClosureBinding::Bound && executed_identity == context.identity {
                if let Some(ref path) = eval_shm_file {
                    if let Ok(bytes) = serde_json::to_vec(&rep) {
                        write_eval_shm_cache(path, &context.closure, &bytes);
                    }
                }
            }
            warm_local_zygote_daemon_nonblocking(store, env_vars);
        }
        return Ok(Some(rep));
    };
    let endpoint = format!("{}/eval", base_url.trim_end_matches('/'));
    let mut forwarded_env: std::collections::HashMap<String, String> = std::env::vars()
        .filter(|(k, v)| crate::server::is_safe_lean_env_key(k) && !v.contains('\0'))
        .collect();
    for (k, v) in env_vars {
        if crate::server::is_safe_lean_env_key(k) && !v.contains('\0') {
            forwarded_env.insert(k.clone(), v.clone());
        }
    }
    let effective_timeout_opt = if timeout_ms > 0 {
        Some(timeout_ms)
    } else {
        None
    };
    let policy = request_policy(env_vars);
    let allowed_axioms: Vec<String> = policy
        .get(crate::splitter::ALLOWED_AXIOMS_ENV)
        .map(|s| {
            s.split(',')
                .map(str::trim)
                .filter(|p| !p.is_empty())
                .map(String::from)
                .collect()
        })
        .unwrap_or_default();
    let body = serde_json::to_vec(&serde_json::json!({
        "toolchain": effective_tc,
        "lean_path": context.lean_path,
        "execution_identity": context.identity,
        "source": source,
        "file_name": file_name,
        "cwd": caller_cwd,
        "env_vars": forwarded_env,
        "allowed_axioms": allowed_axioms,
        "policy_tags": request_policy(env_vars),
        "timeout_ms": effective_timeout_opt,
        "verify_determinism": false,
        "lean_args": filtered_args
    }))?;
    let http_timeout = effective_timeout_opt.map(|ms| ms.saturating_add(250));
    let outcome = match http_request_with_timeout_and_token(
        "POST",
        &endpoint,
        "application/json",
        &body,
        http_timeout,
        Some(&auth_token),
        || {},
    ) {
        Ok(b) => finish_eval_http_request(Ok(b))?,
        Err(e) => {
            if let Some(limit_ms) = effective_timeout_opt {
                if t0.elapsed().as_millis() as u64 >= limit_ms
                    || e.to_string().contains("Resource temporarily unavailable")
                    || e.to_string().contains("timed out")
                    || e.to_string().contains("TimedOut")
                {
                    return Ok(Some(ZygoteEvalReply::timed_out_reply(
                        true,
                        t0.elapsed().as_micros() as u64,
                        limit_ms,
                        0,
                        String::new(),
                        None,
                    )));
                }
            }
            if !is_expired_daemon_transport_error(&e) {
                return Err(extract_http_error_detail(e));
            }
            if let Some((_, _, _, _, state_file)) = current_exe_daemon_paths(store) {
                terminate_and_remove_daemon_state_file(&state_file);
            }
            let Some((retry_url, retry_token)) =
                ensure_local_zygote_daemon_with_token(store, env_vars)
            else {
                return Ok(None);
            };
            let retry_endpoint = format!("{}/eval", retry_url.trim_end_matches('/'));
            finish_eval_http_request(http_request_with_timeout_and_token(
                "POST",
                &retry_endpoint,
                "application/json",
                &body,
                http_timeout,
                Some(&retry_token),
                || {},
            ))?
        }
    };
    if let Some(ref env) = outcome {
        if eval_reply_cacheable(&env.reply)
            && env.binding_ok
            && env.executed_execution_identity.as_deref() == Some(context.identity.as_str())
        {
            if let Some(ref path) = eval_shm_file {
                if let Ok(bytes) = serde_json::to_vec(&env.reply) {
                    write_eval_shm_cache(path, &context.closure, &bytes);
                }
            }
        }
    }
    Ok(outcome.map(|env| env.reply))
}
