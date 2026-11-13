use anyhow::Result;
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::db::{self, TurboStore};
use crate::lake_build::{
    compute_imported_olean_interface_hashes, compute_shard_key_with_args, detect_toolchain,
    resolve_remote_lean_path, resolve_replayed_prebuilt_module_import,
};
use crate::pack;
use crate::splitter;

use super::identity::{
    confirm_decl_identity_with_budget, confirm_file_decl_identities_with_budget,
};
use super::single_decl::target_hygiene_violations;
use super::{cache_shm_stat_split, default_parallel_jobs, make_attested_shard_receipt_bytes};

#[allow(clippy::too_many_arguments)]
pub(super) fn emit_remote_decl_result(
    json_output: bool,
    emit_stdout: bool,
    kernel_prov: &crate::kernel::KernelProvenance,
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
    t0: Instant,
) -> Result<(u64, serde_json::Value)> {
    let server_arch = resp_json
        .get("server_arch")
        .and_then(|v| v.as_str())
        .unwrap_or("unknown");
    let server_elapsed_ms = resp_json
        .get("server_elapsed_ms")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);
    let mut out_json = serde_json::json!({
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
    kernel_prov.insert_json_fields(&mut out_json);
    super::insert_check_timings(&mut out_json, t0);
    if emit_stdout {
        if json_output {
            println!("{}", serde_json::to_string_pretty(&out_json)?);
        } else {
            println!(
                "[turbo-lean] {} `{}` via {} (arch={}, server={} ms, total={} ms, wall={} ms)",
                remote_status.to_uppercase(),
                target_decl,
                remote_url,
                server_arch,
                server_elapsed_ms,
                dur_ms,
                super::process_wall_ms(t0).max(dur_ms)
            );
        }
    }
    Ok((server_elapsed_ms, out_json))
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

pub(super) fn resolve_check_project_and_target(
    file: &Path,
    project_dir: &Path,
) -> (PathBuf, PathBuf) {
    let initial_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let resolved_file = if file == Path::new(".") {
        initial_dir.clone()
    } else if file.is_relative() && initial_dir.join(file).exists() {
        initial_dir.join(file)
    } else if file.exists() {
        file.to_path_buf()
    } else {
        initial_dir.join(file)
    };
    let canon_dir = if project_dir == Path::new(".") {
        let search_start = if file == Path::new(".") {
            initial_dir.as_path()
        } else if !resolved_file.exists() && resolved_file.extension().is_some_and(|e| e == "lean")
        {
            resolved_file
                .parent()
                .filter(|p| !p.as_os_str().is_empty())
                .unwrap_or(Path::new("."))
        } else {
            resolved_file.as_path()
        };
        let inferred = crate::lake_build::find_project_root(search_start);
        inferred.canonicalize().unwrap_or(inferred)
    } else {
        initial_dir
    };
    (canon_dir, resolved_file)
}

fn prepare_stateless_remote_file(
    file: &Path,
    project_dir: &Path,
) -> Result<Option<StatelessRemoteInit>> {
    crate::module_builder::reset_lake_inputs_tag_memo();
    let (canon_dir, resolved_file) = resolve_check_project_and_target(file, project_dir);
    crate::module_builder::try_project_lake_inputs_tag(&canon_dir)?;
    if file == Path::new(".") || resolved_file.is_dir() || !resolved_file.exists() {
        return Ok(None);
    }
    let Ok(active_src) = fs::read_to_string(&resolved_file) else {
        return Ok(None);
    };
    if active_src.len() > 64 * 1024 {
        return Ok(None);
    }
    let canon_file = resolved_file.canonicalize().unwrap_or(resolved_file);
    crate::lake_build::ensure_project_imports_fresh_for_check(
        &canon_dir,
        std::slice::from_ref(&canon_file),
    )?;
    let toolchain = detect_toolchain(&canon_dir);
    let effective_tc = if toolchain.is_empty() || toolchain == "unknown" {
        "leanprover/lean4:v4.35.0".to_string()
    } else {
        toolchain.clone()
    };
    let local_lean_path = resolve_remote_lean_path(&canon_dir, None);
    let dep_hashes = compute_imported_olean_interface_hashes(
        &active_src,
        &canon_dir,
        (!local_lean_path.is_empty()).then_some(local_lean_path.as_str()),
    );
    let split = splitter::split_lean_source_fast_no_cone(&active_src, &dep_hashes);
    Ok(Some((
        canon_dir,
        canon_file,
        active_src,
        toolchain,
        effective_tc,
        local_lean_path,
        dep_hashes,
        split,
    )))
}

fn stateless_imports_replayed_in_store(
    ro_store: &TurboStore,
    canon_dir: &Path,
    local_lean_path: &str,
    active_src: &str,
) -> bool {
    let Ok(cfg) = crate::module_builder::resolve_project_config(canon_dir) else {
        return false;
    };
    let mut dirs: Vec<PathBuf> = std::env::split_paths(local_lean_path).collect();
    if !cfg.toolchain_lib_lean.as_os_str().is_empty() && !dirs.contains(&cfg.toolchain_lib_lean) {
        dirs.push(cfg.toolchain_lib_lean.clone());
    }
    let mut replay_batch =
        crate::module_builder::ReplayLookupBatchCache::new(ro_store, &cfg, local_lean_path);
    let mut worklist = crate::module_builder::parse_header_info(active_src).imports;
    let mut seen = HashSet::new();
    while let Some(m) = worklist.pop() {
        if !seen.insert(m.clone()) {
            continue;
        }
        let Some(path) = replay_batch.resolve_module_olean(&m) else {
            return false;
        };
        if crate::module_builder::is_verified_toolchain_olean_file(
            &cfg.toolchain_lib_lean,
            Some(&cfg.lean_githash),
            &path,
        ) {
            continue;
        }
        if !replay_batch.is_replayed_in_store(ro_store, &cfg, local_lean_path, &path) {
            return false;
        }
        let Ok((imps, _)) = crate::module_builder::read_olean_binary_imports_cached(&path) else {
            return false;
        };
        worklist.extend(imps.into_iter().map(|i| i.module));
    }
    true
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
    super::CHECK_START.with(|start| start.set(Some(Instant::now())));
    super::PHASES.with(|p| p.set(super::CheckPhaseTimings::default()));
    let (inferred_canon_dir, _) = resolve_check_project_and_target(file, project_dir);
    let kernel_prov = crate::kernel::resolve_kernel_engine(
        crate::kernel::resolve_kernel_selection_from_env(None)?,
        &detect_toolchain(&inferred_canon_dir),
    )?;
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
    )) = prepare_stateless_remote_file(file, project_dir)?
    else {
        return Ok(false);
    };
    if !split.eligible_for_sharding
        || split.shards.is_empty()
        || !split.hygiene.is_clean_for_certification()
    {
        return Ok(false);
    }
    let uncached_names: HashSet<String> = split.shards.iter().map(|s| s.rooted_name()).collect();
    let pruned_batch_src =
        splitter::build_pruned_imports_shard_source(&active_src, &uncached_names);
    let need_store =
        !dep_hashes.is_empty() || (pruned_batch_src.is_none() && split.shards.len() > 1);
    let ro_store = if need_store && cache_root.join("state.db").is_file() {
        TurboStore::open(Some(cache_root)).ok()
    } else {
        None
    };
    if !dep_hashes.is_empty()
        && !ro_store.as_ref().is_some_and(|st| {
            stateless_imports_replayed_in_store(st, &canon_dir, &local_lean_path, &active_src)
        })
    {
        return Ok(false);
    }
    let fast_batch_src = if pruned_batch_src.is_some() || split.shards.len() <= 1 {
        None
    } else {
        ro_store
            .as_ref()
            .and_then(|st| resolve_replayed_prebuilt_module_import(st, &canon_dir, &canon_file))
            .and_then(|mod_imp| {
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
    let file_lean_args = crate::module_builder::validate_effective_lean_args(
        &crate::module_builder::try_resolve_lean_args_for_path(&canon_dir, Some(&canon_file))?,
    )?;
    let req_items: Vec<pack::CheckShardBatchItem> = split
        .shards
        .iter()
        .zip(&attested)
        .map(|(s, att)| pack::CheckShardBatchItem {
            shard_key: compute_shard_key_with_args(&toolchain, s, &file_lean_args),
            decl_name: s.rooted_name(),
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

    let Ok(resp_bytes) = pack::http_request("POST", &endpoint, "application/json", &req_body)
    else {
        return Ok(false);
    };
    let Ok(resp) = serde_json::from_slice::<pack::CheckShardsBatchResponse>(&resp_bytes) else {
        return Ok(false);
    };
    if !resp.ok
        || crate::zygote::verify_attested_decl_types(
            &resp.verified_decl_types,
            &expected_type_pairs,
        )
        .is_err()
    {
        return Ok(false);
    }

    let now = db::now_unix();
    let per_shard_ms = ((resp.elapsed_ms as i64) / (req_items.len() as i64).max(1)).max(1);
    let mut publish_items = Vec::with_capacity(req_items.len());
    for item in &req_items {
        let clean_decl = item
            .decl_name
            .strip_prefix("_root_.")
            .unwrap_or(&item.decl_name);
        let r_bytes = make_attested_shard_receipt_bytes(
            clean_decl,
            &item.prefix_env_hash,
            &item.stmt_hash,
            &item.proof_hash,
            now,
            item.expected_kernel_type_hash.as_deref(),
        )?;
        publish_items.push((
            item.shard_key.clone(),
            clean_decl.to_string(),
            r_bytes,
            per_shard_ms,
        ));
    }

    let mut store = TurboStore::open(Some(cache_root))?;
    if !publish_items.is_empty() {
        store.batch_publish_theorem_shards(&toolchain, "trusted", &publish_items)?;
    }

    cache_shm_stat_split(&store, &canon_file, &active_src, &split, dep_hashes);

    let dur_ms = t0.elapsed().as_millis() as i64;
    crate::lake_build::recheck_dependents_if_nonlocal(&store, &canon_dir, &canon_file)?;
    let misses = req_items.len();
    let effective_jobs = default_parallel_jobs(jobs).min(misses);
    let mut out_json = serde_json::json!({
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
    kernel_prov.insert_json_fields(&mut out_json);
    super::insert_check_timings(&mut out_json, t0);
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

fn try_stateless_remote_single_decl_check(
    cache_root: &Path,
    json_output: bool,
    file: &Path,
    target_decl: &str,
    project_dir: &Path,
    remote_url: &str,
) -> Result<bool> {
    let t0 = Instant::now();
    let (inferred_canon_dir, _) = resolve_check_project_and_target(file, project_dir);
    let kernel_prov = crate::kernel::resolve_kernel_engine(
        crate::kernel::resolve_kernel_selection_from_env(None)?,
        &detect_toolchain(&inferred_canon_dir),
    )?;
    let Some((
        canon_dir,
        canon_file,
        active_src,
        toolchain,
        effective_tc,
        local_lean_path,
        dep_hashes,
        split,
    )) = prepare_stateless_remote_file(file, project_dir)?
    else {
        return Ok(false);
    };
    let Ok(Some(shard_idx)) = splitter::resolve_target_shard_idx(&split.shards, target_decl) else {
        return Ok(false);
    };
    let shard = &split.shards[shard_idx];
    // The full `check --decl` path reports (rejects) a target that fails its hygiene gate.
    if !target_hygiene_violations(&split, shard, false).is_empty() {
        return Ok(false);
    }
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
    let file_lean_args = crate::module_builder::validate_effective_lean_args(
        &crate::module_builder::try_resolve_lean_args_for_path(&canon_dir, Some(&canon_file))?,
    )?;
    let shard_key = compute_shard_key_with_args(&toolchain, shard, &file_lean_args);
    let rooted_target = shard.rooted_name();
    let single_set = HashSet::from([rooted_target.clone()]);
    let pruned_src = splitter::build_pruned_imports_shard_source(&active_src, &single_set);
    let need_store = !dep_hashes.is_empty() || (pruned_src.is_none() && split.shards.len() > 1);
    let ro_store = if need_store && cache_root.join("state.db").is_file() {
        TurboStore::open(Some(cache_root)).ok()
    } else {
        None
    };
    if !dep_hashes.is_empty()
        && !ro_store.as_ref().is_some_and(|st| {
            stateless_imports_replayed_in_store(st, &canon_dir, &local_lean_path, &active_src)
        })
    {
        return Ok(false);
    }
    let fast_olean_src = if pruned_src.is_some() || split.shards.len() <= 1 {
        None
    } else {
        ro_store
            .as_ref()
            .and_then(|st| resolve_replayed_prebuilt_module_import(st, &canon_dir, &canon_file))
            .and_then(|mod_imp| {
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
        targets: vec![rooted_target],
        expected_kernel_type_hash: Some(attested.kernel_type_hash.clone()),
    })?;

    let Ok(resp_bytes) = pack::http_request("POST", &endpoint, "application/json", &req_body)
    else {
        return Ok(false);
    };
    let Ok(resp_json) = serde_json::from_slice::<serde_json::Value>(&resp_bytes) else {
        return Ok(false);
    };
    let remote_status = resp_json
        .get("status")
        .and_then(|v| v.as_str())
        .unwrap_or("unknown")
        .to_string();
    if remote_status != "remote_theorem_verified" && remote_status != "remote_theorem_cache_hit" {
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
        return Ok(false);
    }

    let dur_ms = t0.elapsed().as_millis() as i64;
    let server_elapsed_ms = resp_json
        .get("server_elapsed_ms")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);

    let receipt = make_attested_shard_receipt_bytes(
        target_decl,
        &shard.prefix_env_hash,
        &shard.stmt_hash,
        &shard.proof_hash,
        db::now_unix(),
        Some(&attested.kernel_type_hash),
    )?;
    let mut store = TurboStore::open(Some(cache_root))?;
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

    cache_shm_stat_split(&store, &canon_file, &active_src, &split, dep_hashes);
    crate::lake_build::recheck_dependents_if_nonlocal(&store, &canon_dir, &canon_file)?;

    emit_remote_decl_result(
        json_output,
        true,
        &kernel_prov,
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
        t0,
    )?;
    Ok(true)
}
