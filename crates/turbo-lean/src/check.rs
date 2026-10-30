//! Incremental theorem-level (`--decl`), file-level, and directory-wide (`check <dir>`)
//! verification with `/dev/shm` stat-split singleflight, local Zygote CoW prefix reuse,
//! and cross-file coalesced shard batching.

use anyhow::{Context, Result};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use crate::db::{self, BlobEntry, SingleflightOutcome, TurboStore};
use crate::lake_build::{
    collect_lean_files, compact_split_for_shm_cache, compute_imported_olean_interface_hashes,
    compute_shard_key_with_args, compute_single_stat_hash, detect_toolchain,
    is_file_hash_verified_in_lake_build, is_file_verified_in_lake_build, lean_bin_from_env,
    load_and_split_files_with_hashes_cached, load_verified_project_manifest, resolve_lake_env,
    resolve_prebuilt_module_import, resolve_remote_lean_path, shm_file_splits_dir,
    split_and_audit_cached, ShmCachedFileSplit,
};
use crate::pack;
use crate::pr_verify::{try_fast_split_single_file, try_fast_split_single_file_from_path};
use crate::splitter::{self, split_lean_source};

pub(crate) fn make_shard_receipt_bytes(
    decl: &str,
    prefix_env_hash: &str,
    stmt_hash: &str,
    proof_hash: &str,
    verified_at: i64,
) -> Result<Vec<u8>> {
    Ok(serde_json::to_vec(&serde_json::json!({
        "decl": decl,
        "prefix_env_hash": prefix_env_hash,
        "stmt_hash": stmt_hash,
        "proof_hash": proof_hash,
        "verified_at": verified_at
    }))?)
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
            split_key: format!("file-split:v3:{}", src_b3),
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
    let uncached_names: HashSet<String> = split.shards.iter().map(|s| s.name.clone()).collect();
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
    let file_lean_args =
        crate::module_builder::try_resolve_lean_args_for_path(&canon_dir, Some(&canon_file));
    let req_items: Vec<pack::CheckShardBatchItem> = split
        .shards
        .iter()
        .map(|s| pack::CheckShardBatchItem {
            shard_key: compute_shard_key_with_args(&toolchain, s, &file_lean_args),
            decl_name: s.name.clone(),
            prefix_env_hash: s.prefix_env_hash.clone(),
            stmt_hash: s.stmt_hash.clone(),
            proof_hash: s.proof_hash.clone(),
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
                    if let Ok(r_bytes) = make_shard_receipt_bytes(
                        &item.decl_name,
                        &item.prefix_env_hash,
                        &item.stmt_hash,
                        &item.proof_hash,
                        now,
                    ) {
                        publish_items.push((
                            item.shard_key.clone(),
                            item.decl_name.clone(),
                            r_bytes,
                            1i64,
                        ));
                    }
                }
                if publish_items.len() == req_items.len() {
                    let _ = st.prestage_theorem_shard_blobs(&publish_items);
                    if st
                        .begin_inflight_publish_theorem_shards(
                            &toolchain,
                            "trusted",
                            &publish_items,
                        )
                        .is_ok()
                    {
                        inflight_tx_open = true;
                    }
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
    if !resp.ok {
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
    let Some(shard) = split
        .shards
        .iter()
        .find(|s| splitter::decl_name_matches_target(&s.name, target_decl))
    else {
        return Ok(false);
    };
    let file_lean_args =
        crate::module_builder::try_resolve_lean_args_for_path(&canon_dir, Some(&canon_file));
    let shard_key = compute_shard_key_with_args(&toolchain, shard, &file_lean_args);
    let mut single_set = HashSet::new();
    single_set.insert(target_decl.to_string());
    single_set.insert(shard.name.clone());
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
                if let Ok(r_bytes) = make_shard_receipt_bytes(
                    target_decl,
                    &shard.prefix_env_hash,
                    &shard.stmt_hash,
                    &shard.proof_hash,
                    db::now_unix(),
                ) {
                    let items = [(
                        shard_key.clone(),
                        target_decl.to_string(),
                        r_bytes.clone(),
                        1,
                    )];
                    let _ = st.prestage_theorem_shard_blobs(&items);
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
            None => make_shard_receipt_bytes(
                target_decl,
                &shard.prefix_env_hash,
                &shard.stmt_hash,
                &shard.proof_hash,
                db::now_unix(),
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
                    split_key: format!("file-split:v3:{}", src_b3),
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
                        format!("file-split:v3:{}", src_b3)
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

    let dir_pkg_cfg = crate::module_builder::resolve_package_config(canon_dir, false).ok();
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
        if remote_http.is_none() && std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
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
    let staging_dir = store.fast_staging_dir();
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
                    .map(|(_, sh)| sh.name.clone())
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
    let lean_bin = lean_bin_from_env(&env_vars);

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
                        decl_name: sh.name.clone(),
                        prefix_env_hash: sh.prefix_env_hash.clone(),
                        stmt_hash: sh.stmt_hash.clone(),
                        proof_hash: sh.proof_hash.clone(),
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
            };
            let mut cross_ok = proj_build_verified
                || pack::try_local_zygote_check_shard(store, &env_vars, &zreq).is_some();
            if !cross_ok {
                let tmp_cross = staging_dir.join(format!("cross_file_coalesced_{}.lean", pid));
                fs::write(&tmp_cross, &cross_src)?;
                let mut cmd = Command::new(&lean_bin);
                for arg in crate::module_builder::filter_allowed_lean_args(&cross_args) {
                    cmd.arg(arg);
                }
                let cross_out = crate::zygote::run_lean_command(
                    &mut cmd
                        .arg(&tmp_cross)
                        .current_dir(canon_dir)
                        .envs(&env_vars),
                    Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                )?;
                let _ = fs::remove_file(&tmp_cross);
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
                            &sh.name,
                            &sh.prefix_env_hash,
                            &sh.stmt_hash,
                            &sh.proof_hash,
                            now,
                        )?;
                        items.push((k.clone(), sh.name.clone(), receipt, dur_ms));
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
        let next_file_idx = std::sync::atomic::AtomicUsize::new(0);
        let worker_results: Vec<Result<Vec<(String, String, Vec<u8>, i64)>>> =
            std::thread::scope(|s| {
                let mut handles = Vec::with_capacity(effective_jobs);
                for _w in 0..effective_jobs {
                    let next_ref = &next_file_idx;
                    let files_ref = &uncached_files;
                    let staging_ref = &staging_dir;
                    let canon_ref = canon_dir;
                    let env_ref = &env_vars;
                    let lean_bin_ref = &lean_bin;
                    let z_url_ref = local_zygote_url.as_deref();
                    let tc_ref = toolchain;
                    let lp_ref = &lean_path_str;

                    handles.push(s.spawn(
                        move || -> Result<Vec<(String, String, Vec<u8>, i64)>> {
                            let mut items = Vec::new();
                            loop {
                                let f_idx =
                                    next_ref.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                                if f_idx >= files_ref.len() {
                                    break;
                                }
                                let (ref lf, ref src, ref file_uncached, ref file_lean_args) =
                                    files_ref[f_idx];
                                let canon_lf = lf.canonicalize().unwrap_or_else(|_| lf.clone());
                                let uncached_names: HashSet<String> = file_uncached
                                    .iter()
                                    .map(|(_, sh)| sh.name.clone())
                                    .collect();
                                let tmp_batch =
                                    staging_ref.join(format!("dir_batch_{}_{}.lean", pid, f_idx));
                                let f_t0 = Instant::now();

                                let mut batch_ok = false;
                                if let Some(mod_imp) =
                                    resolve_prebuilt_module_import(canon_ref, &canon_lf)
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
                                            };
                                            if pack::try_zygote_url_check_shard(z_url, &zreq)
                                                .is_some()
                                            {
                                                batch_ok = true;
                                            }
                                        }
                                        if !batch_ok {
                                            fs::write(&tmp_batch, &fast_src)?;
                                            let mut cmd = Command::new(lean_bin_ref);
                                            for arg in
                                                crate::module_builder::filter_allowed_lean_args(
                                                    file_lean_args,
                                                )
                                            {
                                                cmd.arg(arg);
                                            }
                                            let out = crate::zygote::run_lean_command(
                                                &mut cmd
                                                    .arg(&tmp_batch)
                                                    .current_dir(canon_ref)
                                                    .envs(env_ref),
                                                Some(crate::zygote::remaining_timeout_ms(
                                                    None, *t0,
                                                )),
                                            )?;
                                            let _ = fs::remove_file(&tmp_batch);
                                            if out.status.success() {
                                                batch_ok = true;
                                            }
                                        }
                                    }
                                }

                                if !batch_ok {
                                    let coal_src = splitter::build_coalesced_shard_source(
                                        src,
                                        &uncached_names,
                                    );
                                    fs::write(&tmp_batch, &coal_src)?;
                                    let mut cmd = Command::new(lean_bin_ref);
                                    for arg in crate::module_builder::filter_allowed_lean_args(
                                        file_lean_args,
                                    ) {
                                        cmd.arg(arg);
                                    }
                                    let out = crate::zygote::run_lean_command(
                                        &mut cmd
                                            .arg(&tmp_batch)
                                            .current_dir(canon_ref)
                                            .envs(env_ref),
                                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                                    )?;
                                    let _ = fs::remove_file(&tmp_batch);
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
                                        &sh.name,
                                        &sh.prefix_env_hash,
                                        &sh.stmt_hash,
                                        &sh.proof_hash,
                                        now,
                                    )?;
                                    items.push((k.clone(), sh.name.clone(), receipt, dur_ms));
                                }
                            }
                            Ok(items)
                        },
                    ));
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
    if remote_http.is_none() && std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
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
            "fission:{}:{}:{}:ax:{}",
            toolchain,
            prefix_env_hash,
            sub_shard_key,
            &ax_hash.as_str()[..24]
        )
    } else {
        format!(
            "fission:{}:{}:{}",
            toolchain, prefix_env_hash, sub_shard_key
        )
    };
    if let Some(opts_digest) = crate::module_builder::compute_lean_args_digest(lean_args) {
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

    if !split
        .shards
        .iter()
        .any(|s| splitter::decl_name_matches_target(&s.name, target_decl))
    {
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
                    if sub_split
                        .shards
                        .iter()
                        .any(|s| splitter::decl_name_matches_target(&s.name, target_decl))
                    {
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
                            split_key: format!("file-split:v3:{}", sub_b3),
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
                    if sub_split
                        .shards
                        .iter()
                        .any(|s| splitter::decl_name_matches_target(&s.name, target_decl))
                    {
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

    let shard_idx = split
        .shards
        .iter()
        .position(|s| splitter::decl_name_matches_target(&s.name, target_decl))
        .with_context(|| {
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
    let shard = &split.shards[shard_idx];
    let file_lean_args =
        crate::module_builder::try_resolve_lean_args_for_path(canon_dir, Some(&active_file));

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
        if db_warm_on_open && store.get_cached_action(&shard_key, "trusted")?.is_some() {
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
        single_set.insert(target_decl.to_string());
        single_set.insert(shard.name.clone());
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
                splitter::reconstruct_single_shard_source(&active_src, &shard.name)
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
            })?;
            match pack::http_request_with_inflight(
                "POST",
                &endpoint,
                "application/json",
                &req_body,
                || {
                    if prestaged_receipt.is_none() {
                        if let Ok(r_bytes) = make_shard_receipt_bytes(
                            target_decl,
                            &shard.prefix_env_hash,
                            &shard.stmt_hash,
                            &shard.proof_hash,
                            db::now_unix(),
                        ) {
                            let items = [(
                                shard_key.clone(),
                                target_decl.to_string(),
                                r_bytes.clone(),
                                1,
                            )];
                            let _ = store.prestage_theorem_shard_blobs(&items);
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
                            resp_json = rj;
                            remote_status = st;
                            fast_olean_used = is_fast;
                            last_err = None;
                            break;
                        }
                        last_err = Some(anyhow::anyhow!(
                            "Remote shard check failed on {}: {}",
                            endpoint,
                            rj
                        ));
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
                splitter::reconstruct_single_shard_source(&active_src, &shard.name)
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
                    if st == "remote_theorem_verified" || st == "remote_theorem_cache_hit" {
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
                None => make_shard_receipt_bytes(
                    target_decl,
                    &shard.prefix_env_hash,
                    &shard.stmt_hash,
                    &shard.proof_hash,
                    db::now_unix(),
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

    match store.acquire_singleflight(&shard_key, toolchain, "theorem_shard", "trusted")? {
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
            let safe_name: String = target_decl
                .chars()
                .map(|c| {
                    if c.is_ascii_alphanumeric() || c == '_' {
                        c
                    } else {
                        '_'
                    }
                })
                .collect();
            let staging_dir = store.fast_staging_dir();
            let tmp_shard =
                staging_dir.join(format!("shard_{}_{}.lean", safe_name, std::process::id()));

            let mut single_set = HashSet::new();
            single_set.insert(target_decl.to_string());
            single_set.insert(shard.name.clone());

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
            let mut verified_via_fast_olean = proj_build_verified && prebuilt_mod.is_some();
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
                        String::new(),
                        String::new(),
                    )
                } else if fast_lib_dir.exists()
                    || has_pkg_lib_dir
                    || fast_local_zygote_url.is_some()
                {
                    let lp = resolve_remote_lean_path(canon_dir, None);
                    let mut fast_ev = HashMap::new();
                    fast_ev.insert("LEAN_PATH".to_string(), lp.clone());
                    (fast_ev, db_warm_on_open, "lean".to_string(), lp)
                } else {
                    let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                    let lb = lean_bin_from_env(&ev);
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
                        lean_bin = lean_bin_from_env(&ev);
                        env_vars = ev;
                        env_cache_hit = ech;
                    }
                    let full_shard_src = if !shard.shard_source.is_empty() {
                        shard.shard_source.clone()
                    } else {
                        splitter::reconstruct_single_shard_source(&active_src, &shard.name)
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

                    let mut cached_hit_keys: Vec<String> = Vec::new();
                    let mut uncached_subs: Vec<(&splitter::FissionSubShard, &String, String)> =
                        Vec::new();
                    for (sub, f_key) in fission_sub_shards.iter().zip(fission_keys.iter()) {
                        if cached_subs.contains_key(f_key) {
                            cached_hit_keys.push(f_key.clone());
                        } else {
                            let sub_decl_full = if closing_suffix.trim().is_empty() {
                                sub.sub_decl_source.clone()
                            } else {
                                format!("{}\n{}", sub.sub_decl_source, closing_suffix.trim_start())
                            };
                            uncached_subs.push((sub, f_key, sub_decl_full));
                        }
                    }

                    if uncached_subs.is_empty() {
                        if !cached_hit_keys.is_empty() {
                            let _ = store.batch_increment_action_hits(&cached_hit_keys);
                        }
                        fission_cached_subshards = cached_hit_keys.len();
                        fission_verified_subshards = 0;
                        verified_via_zygote = true;
                        accelerator_assisted = true;
                        winning_accelerator = Some("builtin:cut-fission".to_string());
                    } else {
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
                    if proj_build_verified {
                        Some(format!("import {}\n#check Nat\n", mod_imp))
                    } else if split.shards.len() > 1 {
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
                };
                if let Some(ref z_url) = fast_local_zygote_url {
                    let res = pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
                        z_url,
                        &zreq,
                        || {
                            if !inflight_tx_open {
                                if let Ok(r_bytes) = make_shard_receipt_bytes(
                                    target_decl,
                                    &shard.prefix_env_hash,
                                    &shard.stmt_hash,
                                    &shard.proof_hash,
                                    db::now_unix(),
                                ) {
                                    let single_pub = vec![(
                                        shard_key.clone(),
                                        target_decl.to_string(),
                                        r_bytes,
                                        1i64,
                                    )];
                                    let _ = store.prestage_theorem_shard_blobs(&single_pub);
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
                        Ok(Some(r)) => return Some(r),
                        Ok(None) => {}
                        Err(e) => {
                            if record_err {
                                let es = e.to_string();
                                if es.contains("Remote `lean` shard verification failed")
                                    || es.contains("Soundness hygiene violation")
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
                    Ok(Some(r)) => Some(r),
                    Ok(None) => None,
                    Err(e) => {
                        if record_err {
                            let es = e.to_string();
                            if es.contains("Remote `lean` shard verification failed")
                                || es.contains("Soundness hygiene violation")
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
                lean_bin = lean_bin_from_env(&ev);
                env_vars = ev;
                env_cache_hit = ech;
            }

            if !verified_via_zygote && !verified_via_fast_olean {
                let full_shard_src = if !shard.shard_source.is_empty() {
                    shard.shard_source.clone()
                } else {
                    splitter::reconstruct_single_shard_source(&active_src, &shard.name)
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
                                    lean_bin = lean_bin_from_env(&ev);
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
                                    if reply.import_ok && reply.ok && c_abi_sound {
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
                            lean_bin = lean_bin_from_env(&ev);
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
                }
                if !verified_via_zygote {
                    fs::write(&tmp_shard, &full_shard_src)?;
                    let default_stack = env_vars
                        .get("LEAN_STACK_SIZE_KB")
                        .cloned()
                        .or_else(|| std::env::var("LEAN_STACK_SIZE_KB").ok())
                        .unwrap_or_else(|| "262144".to_string());
                    let mut cmd = Command::new(&lean_bin);
                    for arg in crate::module_builder::filter_allowed_lean_args(&file_lean_args) {
                        cmd.arg(arg);
                    }
                    let out = crate::zygote::run_lean_command(
                        &mut cmd
                            .arg(&tmp_shard)
                            .current_dir(canon_dir)
                            .envs(&env_vars)
                            .env("LEAN_STACK_SIZE_KB", default_stack),
                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                    )
                    .context("Failed to execute `lean` on theorem shard")?;
                    let _ = fs::remove_file(&tmp_shard);

                    if !out.status.success() {
                        let tmp_display = tmp_shard.display().to_string();
                        let orig_display = file.display().to_string();
                        let stderr = String::from_utf8_lossy(&out.stderr)
                            .replace(&tmp_display, &orig_display);
                        let stdout = String::from_utf8_lossy(&out.stdout)
                            .replace(&tmp_display, &orig_display);
                        let combined_err = format!("{}\n{}", stdout, stderr);
                        let m_diags = extract_mismatch_diagnostics(&combined_err);
                        let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                        anyhow::bail!(
                            "Shard check failed for `{}` in {} (lines {}..={}):\n{}{}",
                            target_decl,
                            file.display(),
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
                let receipt = make_shard_receipt_bytes(
                    target_decl,
                    &shard.prefix_env_hash,
                    &shard.stmt_hash,
                    &shard.proof_hash,
                    db::now_unix(),
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
                && std::env::var("TURBO_LEAN_NO_DAEMON").is_err()
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
    );
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
    for (idx, shard) in split.shards.iter().enumerate() {
        let shard_key = file_shard_keys[idx].clone();
        if cached_map.contains_key(&shard_key) {
            hits += 1;
        } else {
            uncached_shards.push((shard_key, shard));
        }
    }
    let misses = uncached_shards.len();

    if !split.hygiene.is_clean_for_certification() {
        if std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
            if src.is_empty() {
                *src = fs::read_to_string(resolved_file).unwrap_or_default();
            }
            let (imports_csv, _) = crate::zygote::split_shard_for_zygote(src);
            if !imports_csv.is_empty() && imports_csv != "Init" && imports_csv != "__PRELUDE__" {
                let existing_daemon = crate::zygote::has_active_local_zygote_daemon(store);
                if !existing_daemon {
                    if let Ok((ev, _)) = resolve_lake_env(store, canon_dir) {
                        let lb = lean_bin_from_env(&ev);
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
                .map(|(_, s)| s.name.clone())
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
                    decl_name: s.name.clone(),
                    prefix_env_hash: s.prefix_env_hash.clone(),
                    stmt_hash: s.stmt_hash.clone(),
                    proof_hash: s.proof_hash.clone(),
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
            String::new(),
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
            (fast_ev, db_warm_on_open, "lean".to_string(), lp)
        } else {
            let (ev, ech) = resolve_lake_env(store, canon_dir)?;
            let lb = lean_bin_from_env(&ev);
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
        let staging_dir = store.fast_staging_dir();
        let pid = std::process::id();

        let uncached_names: HashSet<String> = uncached_shards
            .iter()
            .map(|(_, s)| s.name.clone())
            .collect();
        let tmp_coalesced = staging_dir.join(format!("coalesced_batch_{}.lean", pid));
        let batch_t0 = Instant::now();

        let mut batch_succeeded = fast_verified_batch;
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
                    if proj_build_verified {
                        Some(format!("import {}\n#check Nat\n", mod_imp))
                    } else if split.shards.len() > 1 {
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
                    Ok(Some(_)) => {
                        batch_succeeded = true;
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
                Ok(Some(_)) => {
                    batch_succeeded = true;
                }
                Ok(None) => {
                    fs::write(&tmp_coalesced, &coalesced_src)?;
                    let mut cmd = Command::new(&lean_bin);
                    for arg in crate::module_builder::filter_allowed_lean_args(&file_lean_args) {
                        cmd.arg(arg);
                    }
                    let batch_out = crate::zygote::run_lean_command(
                        &mut cmd
                            .arg(&tmp_coalesced)
                            .current_dir(canon_dir)
                            .envs(&env_vars),
                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                    )
                    .context("Failed to execute `lean` on coalesced shard batch")?;
                    let _ = fs::remove_file(&tmp_coalesced);
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
                        let staging_ref = &staging_dir;
                        let canon_ref = canon_dir;
                        let env_ref = &env_vars;
                        let lean_bin_ref = &lean_bin;
                        let file_display = file.display().to_string();
                        let z_url_ref = local_zygote_url.as_deref();
                        let tc_ref = toolchain;
                        let lp_ref = &local_lean_path;
                        let iface_ref = &split.interface_hash;
                        let args_ref = &file_lean_args;

                        handles.push(s.spawn(move || -> Result<Vec<(String, &splitter::TheoremShard, i64)>> {
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
                                let shard_t0 = Instant::now();
                                let shard_src_owned = if shard.shard_source.is_empty() {
                                    let mut single_set = HashSet::with_capacity(1);
                                    single_set.insert(shard.name.clone());
                                    splitter::build_coalesced_shard_source(src_ref, &single_set)
                                } else {
                                    shard.shard_source.clone()
                                };

                                if let Some(z_url) = z_url_ref {
                                    let zreq = pack::CheckShardHttpRequest {
                                        decl: shard.name.clone(),
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
                                                shard.name,
                                                file_display,
                                                shard.start_line,
                                                shard.end_line,
                                                raw_err,
                                                m_suffix
                                            );
                                        }
                                    }
                                }

                                let safe_name: String = shard
                                    .name
                                    .chars()
                                    .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
                                    .collect();
                                let tmp_shard = staging_ref.join(format!(
                                    "par_shard_{}_{}_{}.lean",
                                    safe_name, pid, idx
                                ));
                                fs::write(&tmp_shard, &shard_src_owned)?;

                                let mut cmd = Command::new(lean_bin_ref);
                                for arg in crate::module_builder::filter_allowed_lean_args(args_ref)
                                {
                                    cmd.arg(arg);
                                }
                                let out = crate::zygote::run_lean_command(&mut cmd
                                    .arg(&tmp_shard)
                                    .current_dir(canon_ref)
                                    .envs(env_ref), Some(crate::zygote::remaining_timeout_ms(None, *t0)))
                                    .with_context(|| {
                                        format!("Failed to execute `lean` on shard `{}`", shard.name)
                                    })?;
                                let tmp_display = tmp_shard.display().to_string();
                                let _ = fs::remove_file(&tmp_shard);

                                if !out.status.success() {
                                    abort_ref.store(true, std::sync::atomic::Ordering::Relaxed);
                                    let stderr = String::from_utf8_lossy(&out.stderr)
                                        .replace(&tmp_display, &file_display);
                                    let stdout = String::from_utf8_lossy(&out.stdout)
                                        .replace(&tmp_display, &file_display);
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
                    if let Ok(receipt) = make_shard_receipt_bytes(
                        &shard.name,
                        &shard.prefix_env_hash,
                        &shard.stmt_hash,
                        &shard.proof_hash,
                        now,
                    ) {
                        partial_items.push((
                            shard_key.clone(),
                            shard.name.clone(),
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
            let receipt = make_shard_receipt_bytes(
                &shard.name,
                &shard.prefix_env_hash,
                &shard.stmt_hash,
                &shard.proof_hash,
                now,
            )?;
            batch_items.push((shard_key, shard.name.clone(), receipt, shard_dur_ms));
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
        if !fast_verified_batch
            && remote_http.is_none()
            && std::env::var("TURBO_LEAN_NO_DAEMON").is_err()
        {
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
        let can_use_zygote_eval = std::env::var("TURBO_LEAN_NO_DAEMON").is_err()
            && !src.contains("IO.Process.exit")
            && !src.lines().take(20).any(|l| {
                let t = l.split("--").next().unwrap_or(l).trim();
                t == "module" || t.starts_with("module ")
            });
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
                    verified_via_zygote_eval = true;
                    eval_stdout_text = rep.stdout;
                    eval_messages = rep.messages;
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
            let mut cmd = Command::new(&lean_bin);
            for arg in crate::module_builder::filter_allowed_lean_args(&file_lean_args) {
                cmd.arg(arg);
            }
            let out = crate::zygote::run_lean_command(
                &mut cmd
                    .arg(canon_resolved_initial)
                    .current_dir(canon_dir)
                    .envs(&env_vars),
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
                    let receipt = make_shard_receipt_bytes(
                        &shard.name,
                        &shard.prefix_env_hash,
                        &shard.stmt_hash,
                        &shard.proof_hash,
                        now,
                    )?;
                    let bh = store.store_immutable_blob(&receipt, "expr_shard", "trusted", 0)?;
                    let entries = vec![BlobEntry {
                        blob_hash: bh,
                        kind: "expr_shard".to_string(),
                        size_bytes: receipt.len() as u64,
                        rel_path: format!("thm:{}", shard.name),
                    }];
                    store.publish_action(&lease, &entries, dur_ms, 0, 0, "trusted")?;
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
        if remote_http.is_none()
            && !verified_via_zygote_eval
            && std::env::var("TURBO_LEAN_NO_DAEMON").is_err()
        {
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
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "");
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }

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
        let (_env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "");
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }

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
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "");
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }

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
            crate::pack::resolve_server_lean_env_and_bin(&store, toolchain, "");
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        }

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
        let shard_key = compute_shard_key(toolchain, shard);
        let receipt = make_shard_receipt_bytes(
            &shard.name,
            &shard.prefix_env_hash,
            &shard.stmt_hash,
            &shard.proof_hash,
            db::now_unix(),
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
    fn test_lean_args_digest_isolates_shard_and_fission_cache_keys() {
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
}
