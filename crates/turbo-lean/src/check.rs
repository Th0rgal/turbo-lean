//! Incremental theorem-level (`--decl`), file-level, and directory-wide (`check <dir>`)
//! verification with `/dev/shm` stat-split singleflight, local Zygote CoW prefix reuse,
//! and cross-file coalesced shard batching.

use anyhow::{Context, Result};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs::{self, OpenOptions};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use crate::db::{self, BlobEntry, SingleflightOutcome, TurboStore};
use crate::lake_build::{
    collect_lean_files, compact_split_for_shm_cache, compute_imported_olean_interface_hashes,
    compute_shard_key, compute_single_stat_hash, detect_toolchain,
    is_file_hash_verified_in_lake_build, is_file_verified_in_lake_build, lean_bin_from_env,
    load_and_split_files_with_hashes_cached, resolve_lake_env, resolve_prebuilt_module_import,
    resolve_remote_lean_path, shm_file_splits_dir, split_and_audit_cached,
    verified_sources_manifest_path, ShmCachedFileSplit,
};
use crate::pack;
use crate::pr_verify::{try_fast_split_single_file, try_fast_split_single_file_from_path};
use crate::splitter::{self, split_lean_source};

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
    let file_stat_tuple: Option<(i64, i64, i64)> = fs::metadata(&canon_resolved_initial)
        .ok()
        .map(|m| TurboStore::extract_file_stat_tuple(&m));

    // Singleflight-coalesced `/dev/shm` stat-split lookup so concurrent agents checking the same
    // freshly edited file never duplicate prefix splitting.
    let splits_dir = shm_file_splits_dir(store);
    let st_paths_opt = file_stat_tuple.map(|(ms, mn, sz)| {
        let pk = canon_resolved_initial.to_string_lossy();
        let st_hash = compute_single_stat_hash(&pk, ms, mn, sz);
        let st_path = splits_dir.join(format!("st_{}.json", &st_hash[..24]));
        let lock_path = splits_dir.join(format!("st_{}.lock", &st_hash[..24]));
        (st_path, lock_path)
    });

    let disk_spill_dir = store.root.join("disk_spill");
    let mut stat_cached_entry: Option<ShmCachedFileSplit> = st_paths_opt
        .as_ref()
        .and_then(|(st_path, _)| {
            crate::shm_cache::read_shm_or_disk_spill(st_path, Some(&disk_spill_dir))
        })
        .and_then(|bytes| serde_json::from_slice::<ShmCachedFileSplit>(&bytes).ok())
        .filter(|c| {
            compute_imported_olean_interface_hashes(&c.split.imports_header, &canon_dir, None)
                == c.dep_hashes
        });

    let mut held_split_lock: Option<fs::File> = None;
    if stat_cached_entry.is_none() {
        if let Some((ref st_path, ref lock_path)) = st_paths_opt {
            if let Ok(lf) = OpenOptions::new()
                .create(true)
                .read(true)
                .write(true)
                .open(lock_path)
            {
                use std::os::unix::io::AsRawFd;
                let fd = lf.as_raw_fd();
                let rc = unsafe { libc::flock(fd, libc::LOCK_EX | libc::LOCK_NB) };
                if rc == 0 {
                    held_split_lock = Some(lf);
                } else {
                    let _ = unsafe { libc::flock(fd, libc::LOCK_SH) };
                    if let Some(bytes) =
                        crate::shm_cache::read_shm_or_disk_spill(st_path, Some(&disk_spill_dir))
                    {
                        stat_cached_entry = serde_json::from_slice::<ShmCachedFileSplit>(&bytes)
                            .ok()
                            .filter(|c| {
                                compute_imported_olean_interface_hashes(
                                    &c.split.imports_header,
                                    &canon_dir,
                                    None,
                                ) == c.dep_hashes
                            });
                    }
                    let _ = unsafe { libc::flock(fd, libc::LOCK_UN) };
                }
            }
        }
    }

    let mut known_modified_vs_head = false;
    let (mut src, mut cached_file_blake3, mut split, single_split_hits) =
        if let Some(c) = stat_cached_entry {
            known_modified_vs_head = c.known_modified;
            let cb3 = if c.src_blake3.is_empty() {
                None
            } else {
                Some(c.src_blake3)
            };
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
                let dep_hashes = compute_imported_olean_interface_hashes(
                    &fast_sp.imports_header,
                    &canon_dir,
                    None,
                );
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
            let dep_hashes =
                compute_imported_olean_interface_hashes(&loaded_src, &canon_dir, None);
            let (sp, hits) = if loaded_src.len() <= 64 * 1024 {
                let sp = split_lean_source(&loaded_src, &dep_hashes);
                if let Some((ref st_path, _)) = st_paths_opt {
                    let src_b3 = blake3::hash(loaded_src.as_bytes()).to_hex().to_string();
                    let entry = ShmCachedFileSplit {
                        split_key: format!("file-split:v2:{}", src_b3),
                        src_blake3: src_b3,
                        split: compact_split_for_shm_cache(&sp),
                        prefix_src: loaded_src.clone(),
                        known_modified: false,
                        dep_hashes: dep_hashes.clone(),
                    };
                    if let Ok(bytes) = serde_json::to_vec(&entry) {
                        let _ = crate::shm_cache::atomic_write_shm(st_path, &bytes);
                    }
                }
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
                    let entry = ShmCachedFileSplit {
                        split_key: if src_b3.is_empty() {
                            String::new()
                        } else {
                            format!("file-split:v2:{}", src_b3)
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
            (loaded_src, None, sp, hits)
        };

    if let Some(lf) = held_split_lock.take() {
        use std::os::unix::io::AsRawFd;
        let _ = unsafe { libc::flock(lf.as_raw_fd(), libc::LOCK_UN) };
    }

    if let Some(target_decl) = decl {
        check_single_decl(
            store,
            db_warm_on_open,
            json_output,
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
        )
    } else {
        check_single_file(
            store,
            db_warm_on_open,
            json_output,
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
        )
    }
}

#[allow(clippy::too_many_arguments)]
fn check_directory(
    store: &mut TurboStore,
    json_output: bool,
    t0: &Instant,
    file: &Path,
    resolved_file: &Path,
    canon_dir: &Path,
    toolchain: &str,
    jobs: Option<usize>,
    remote_http: Option<&str>,
) -> Result<()> {
    let dir_files = collect_lean_files(resolved_file);
    let mut dir_hasher = blake3::Hasher::new();
    dir_hasher.update(toolchain.as_bytes());

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

        let mut file_keys = Vec::with_capacity(split.shards.len());
        for s in &split.shards {
            let k = compute_shard_key(toolchain, s);
            all_shard_keys.push(k.clone());
            file_keys.push(k);
        }
        parsed_files.push((lf, src_blake3, src, split, file_keys));
    }

    let dir_interface_hash = dir_hasher.finalize().to_hex().to_string();
    let cached_map = store.batch_get_theorem_shards(&all_shard_keys, "trusted")?;

    let mut total_hits = 0usize;
    let mut uncached_files = Vec::new();
    let mut all_uncached_hygiene_clean = true;
    for (lf, src_blake3, src, split, file_keys) in parsed_files {
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
            uncached_files.push((lf, src_blake3, src, file_uncached));
        }
    }

    let total_misses: usize = uncached_files.iter().map(|(_, _, _, u)| u.len()).sum();
    if total_misses == 0 {
        let elapsed_ms = t0.elapsed().as_millis();
        if json_output {
            println!(
                "{}",
                serde_json::to_string_pretty(&serde_json::json!({
                    "status": "all_shards_cached",
                    "file": file.display().to_string(),
                    "files_checked": dir_files.len(),
                    "file_split_cache_hits": split_cache_hits,
                    "shard_hits": total_hits,
                    "shard_misses": 0,
                    "interface_hash": dir_interface_hash,
                    "elapsed_ms": elapsed_ms
                }))?
            );
        } else {
            println!(
                "[turbo-lean] ALL {} THEOREM SHARDS CACHED across {} files in {} ({} ms)",
                total_hits,
                dir_files.len(),
                file.display(),
                elapsed_ms
            );
        }
        return Ok(());
    }

    let governor = crate::shm_cache::MemoryBudgetGovernor::detect();
    let default_jobs = if governor.is_low_memory_mode() {
        governor.recommended_parallel_workers(512)
    } else {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
    };
    let effective_jobs = jobs.unwrap_or(default_jobs).max(1).min(uncached_files.len());
    let staging_dir = store.fast_staging_dir();
    let pid = std::process::id();

    let proj_build_verified = remote_http.is_none()
        && all_uncached_hygiene_clean
        && fs::read(verified_sources_manifest_path(canon_dir))
            .ok()
            .and_then(|b| serde_json::from_slice::<BTreeMap<String, String>>(&b).ok())
            .map(|recorded| {
                uncached_files.iter().all(|(lf, sb, _, _)| {
                    !sb.is_empty() && {
                        let rel = lf
                            .strip_prefix(canon_dir)
                            .unwrap_or(lf)
                            .to_string_lossy()
                            .replace('\\', "/");
                        recorded.get(&rel).map(|h| h == sb).unwrap_or(false)
                    }
                })
            })
            .unwrap_or(false);

    if !proj_build_verified {
        for (lf, _sb, src, _) in &mut uncached_files {
            if src.is_empty() {
                *src = fs::read_to_string(&*lf).unwrap_or_default();
            }
        }
    }
    let uncached_files: Vec<(PathBuf, String, Vec<(String, splitter::TheoremShard)>)> =
        uncached_files
            .into_iter()
            .map(|(lf, _sb, src, fu)| (lf, src, fu))
            .collect();

    let mut cross_eligible = Vec::with_capacity(uncached_files.len());
    for (lf, src, file_uncached) in &uncached_files {
        let canon_lf = lf.canonicalize().unwrap_or_else(|_| lf.clone());
        if let Some(mod_imp) = resolve_prebuilt_module_import(canon_dir, &canon_lf) {
            if proj_build_verified {
                cross_eligible.push((mod_imp, src.as_str(), file_uncached));
            } else {
                let uncached_names: HashSet<String> =
                    file_uncached.iter().map(|(_, sh)| sh.name.clone()).collect();
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
            for (_, _, file_uncached) in &uncached_files {
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
            };
            let mut cross_ok = proj_build_verified
                || pack::try_local_zygote_check_shard(store, &env_vars, &zreq).is_some();
            if !cross_ok {
                let tmp_cross = staging_dir.join(format!("cross_file_coalesced_{}.lean", pid));
                fs::write(&tmp_cross, &cross_src)?;
                let cross_out = Command::new(&lean_bin)
                    .arg(&tmp_cross)
                    .current_dir(canon_dir)
                    .envs(&env_vars)
                    .output()?;
                let _ = fs::remove_file(&tmp_cross);
                cross_ok = cross_out.status.success();
            }
            if cross_ok {
                let dur_ms =
                    (cross_t0.elapsed().as_millis() as i64 / (total_misses as i64).max(1)).max(1);
                let now = db::now_unix();
                let mut items = Vec::with_capacity(total_misses);
                for (_, _, file_uncached) in &uncached_files {
                    for (k, sh) in file_uncached {
                        let receipt = serde_json::to_vec(&serde_json::json!({
                            "decl": sh.name,
                            "prefix_env_hash": sh.prefix_env_hash,
                            "stmt_hash": sh.stmt_hash,
                            "proof_hash": sh.proof_hash,
                            "verified_at": now
                        }))?;
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

                    handles.push(s.spawn(move || -> Result<Vec<(String, String, Vec<u8>, i64)>> {
                        let mut items = Vec::new();
                        loop {
                            let f_idx = next_ref.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                            if f_idx >= files_ref.len() {
                                break;
                            }
                            let (ref lf, ref src, ref file_uncached) = files_ref[f_idx];
                            let canon_lf = lf.canonicalize().unwrap_or_else(|_| lf.clone());
                            let uncached_names: HashSet<String> =
                                file_uncached.iter().map(|(_, sh)| sh.name.clone()).collect();
                            let tmp_batch =
                                staging_ref.join(format!("dir_batch_{}_{}.lean", pid, f_idx));
                            let f_t0 = Instant::now();

                            let mut batch_ok = false;
                            if let Some(mod_imp) = resolve_prebuilt_module_import(canon_ref, &canon_lf) {
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
                                        };
                                        if pack::try_zygote_url_check_shard(z_url, &zreq).is_some() {
                                            batch_ok = true;
                                        }
                                    }
                                    if !batch_ok {
                                        fs::write(&tmp_batch, &fast_src)?;
                                        let out = Command::new(lean_bin_ref)
                                            .arg(&tmp_batch)
                                            .current_dir(canon_ref)
                                            .envs(env_ref)
                                            .output()?;
                                        let _ = fs::remove_file(&tmp_batch);
                                        if out.status.success() {
                                            batch_ok = true;
                                        }
                                    }
                                }
                            }

                            if !batch_ok {
                                let coal_src = splitter::build_coalesced_shard_source(src, &uncached_names);
                                fs::write(&tmp_batch, &coal_src)?;
                                let out = Command::new(lean_bin_ref)
                                    .arg(&tmp_batch)
                                    .current_dir(canon_ref)
                                    .envs(env_ref)
                                    .output()?;
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
                                let receipt = serde_json::to_vec(&serde_json::json!({
                                    "decl": sh.name,
                                    "prefix_env_hash": sh.prefix_env_hash,
                                    "stmt_hash": sh.stmt_hash,
                                    "proof_hash": sh.proof_hash,
                                    "verified_at": now
                                }))?;
                                items.push((k.clone(), sh.name.clone(), receipt, dur_ms));
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
    if json_output {
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
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
            }))?
        );
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
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_single_decl(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    json_output: bool,
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
) -> Result<()> {
    let mut active_src = src;
    let mut active_file = resolved_file.to_path_buf();
    let matches_decl = |s_name: &str, q: &str| -> bool {
        s_name == q || q.ends_with(&format!(".{}", s_name)) || s_name.ends_with(&format!(".{}", q))
    };

    if !split.shards.iter().any(|s| matches_decl(&s.name, target_decl)) {
        for line in split.imports_header.lines() {
            if let Some(mod_name) = line.trim().strip_prefix("import ") {
                let rel_mod = mod_name.trim().replace('.', "/") + ".lean";
                let sub_path = canon_dir.join(rel_mod);
                if let Ok(sub_src) = fs::read_to_string(&sub_path) {
                    let sub_deps =
                        compute_imported_olean_interface_hashes(&sub_src, canon_dir, None);
                    let sub_split = split_lean_source(&sub_src, &sub_deps);
                    if sub_split
                        .shards
                        .iter()
                        .any(|s| matches_decl(&s.name, target_decl))
                    {
                        *split = sub_split;
                        *cached_file_blake3 = None;
                        active_src = sub_src;
                        active_file = sub_path;
                        break;
                    }
                }
            }
        }
    }

    let shard = split
        .shards
        .iter()
        .find(|s| matches_decl(&s.name, target_decl))
        .with_context(|| {
            format!(
                "Declaration `{}` not found in {} (found {} theorem shards)",
                target_decl,
                file.display(),
                split.shards.len()
            )
        })?;

    let shard_key = compute_shard_key(toolchain, shard);

    if let Some(remote_url) = remote_http {
        if db_warm_on_open && store.get_cached_action(&shard_key, "trusted")?.is_some() {
            let elapsed_ms = t0.elapsed().as_millis();
            if json_output {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "status": "theorem_cache_hit",
                        "decl": target_decl,
                        "coalesced": false,
                        "shard_key": shard_key,
                        "interface_hash": split.interface_hash,
                        "prefix_env_hash": shard.prefix_env_hash,
                        "elapsed_ms": elapsed_ms
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] SHARD CACHE HIT `{}` (coalesced=false, {} ms)",
                    target_decl, elapsed_ms
                );
            }
            return Ok(());
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
        let fast_olean_src =
            resolve_prebuilt_module_import(canon_dir, &canon_file).and_then(|mod_imp| {
                splitter::build_fast_olean_shard_source_with_split(
                    &active_src,
                    split,
                    &mod_imp,
                    &single_set,
                )
            });
        let endpoint = format!("{}/check-shard", remote_url.trim_end_matches('/'));
        let fast_lib_lean = canon_dir.join(".lake/build/lib/lean");
        let local_lean_path =
            if fast_lib_lean.exists() && !canon_dir.join(".lake/build/packages").is_dir() {
                fast_lib_lean.to_string_lossy().to_string()
            } else {
                let cached_env = if db_warm_on_open {
                    let env_key = TurboStore::compute_lake_env_key(canon_dir);
                    store.get_lake_env(&env_key).ok().flatten()
                } else {
                    None
                };
                resolve_remote_lean_path(canon_dir, cached_env.as_ref())
            };

        let mut fast_candidates: Vec<(&str, bool)> = Vec::new();
        if let Some(ref psrc) = pruned_src {
            fast_candidates.push((psrc.as_str(), true));
        }
        if let Some(ref fsrc) = fast_olean_src {
            fast_candidates.push((fsrc.as_str(), true));
        }

        let mut resp_json = serde_json::Value::Null;
        let mut remote_status = String::from("unknown");
        let mut fast_olean_used = false;
        let mut last_err: Option<anyhow::Error> = None;
        let mut succeeded = false;
        let mut prestaged_receipt: Option<Vec<u8>> = None;
        let mut inflight_tx_open = false;

        for (cand_src, is_fast) in fast_candidates {
            let req_body = serde_json::to_vec(&pack::CheckShardHttpRequest {
                decl: target_decl.to_string(),
                shard_key: shard_key.clone(),
                shard_source: cand_src.to_string(),
                interface_hash: split.interface_hash.clone(),
                prefix_env_hash: shard.prefix_env_hash.clone(),
                stmt_hash: shard.stmt_hash.clone(),
                proof_hash: shard.proof_hash.clone(),
                toolchain: toolchain.to_string(),
                lean_path: local_lean_path.clone(),
                skip_cas_lock: false,
            })?;
            match pack::http_request_with_inflight(
                "POST",
                &endpoint,
                "application/json",
                &req_body,
                || {
                    if prestaged_receipt.is_none() {
                        if let Ok(r_bytes) = serde_json::to_vec(&serde_json::json!({
                            "decl": target_decl,
                            "prefix_env_hash": &shard.prefix_env_hash,
                            "stmt_hash": &shard.stmt_hash,
                            "proof_hash": &shard.proof_hash,
                            "verified_at": db::now_unix()
                        })) {
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
                            succeeded = true;
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
        if !succeeded {
            let full_shard_src = if !shard.shard_source.is_empty() {
                shard.shard_source.clone()
            } else {
                splitter::reconstruct_single_shard_source(&active_src, &shard.name)
                    .unwrap_or_default()
            };
            let req_body = serde_json::to_vec(&pack::CheckShardHttpRequest {
                decl: target_decl.to_string(),
                shard_key: shard_key.clone(),
                shard_source: full_shard_src,
                interface_hash: split.interface_hash.clone(),
                prefix_env_hash: shard.prefix_env_hash.clone(),
                stmt_hash: shard.stmt_hash.clone(),
                proof_hash: shard.proof_hash.clone(),
                toolchain: toolchain.to_string(),
                lean_path: local_lean_path,
                skip_cas_lock: false,
            })?;
            match pack::http_request_with_inflight(
                "POST",
                &endpoint,
                "application/json",
                &req_body,
                || {
                    if prestaged_receipt.is_none() {
                        if let Ok(r_bytes) = serde_json::to_vec(&serde_json::json!({
                            "decl": target_decl,
                            "prefix_env_hash": &shard.prefix_env_hash,
                            "stmt_hash": &shard.stmt_hash,
                            "proof_hash": &shard.proof_hash,
                            "verified_at": db::now_unix()
                        })) {
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
                            fast_olean_used = false;
                            last_err = None;
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
        if let Some(err) = last_err {
            if inflight_tx_open {
                store.rollback_inflight_publish();
            }
            return Err(err);
        }

        let dur_ms = t0.elapsed().as_millis() as i64;
        let server_arch = resp_json
            .get("server_arch")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown");
        let server_elapsed_ms = resp_json
            .get("server_elapsed_ms")
            .and_then(|v| v.as_u64())
            .unwrap_or(0);
        let zygote_used = resp_json
            .get("zygote_used")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);
        let zygote_env_cache_hit = resp_json
            .get("zygote_env_cache_hit")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);
        let zygote_import_us = resp_json
            .get("zygote_import_us")
            .and_then(|v| v.as_u64())
            .unwrap_or(0);
        let zygote_elab_us = resp_json
            .get("zygote_elab_us")
            .and_then(|v| v.as_u64())
            .unwrap_or(0);
        if inflight_tx_open {
            store.commit_inflight_publish()?;
        } else {
            let receipt = match prestaged_receipt {
                Some(r) => r,
                None => serde_json::to_vec(&serde_json::json!({
                    "decl": target_decl,
                    "prefix_env_hash": shard.prefix_env_hash,
                    "stmt_hash": shard.stmt_hash,
                    "proof_hash": shard.proof_hash,
                    "verified_at": db::now_unix()
                }))?,
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

        if json_output {
            println!(
                "{}",
                serde_json::to_string_pretty(&serde_json::json!({
                    "status": remote_status,
                    "decl": target_decl,
                    "shard_key": shard_key,
                    "remote_url": remote_url,
                    "server_arch": server_arch,
                    "server_elapsed_ms": server_elapsed_ms,
                    "fast_olean_import": fast_olean_used,
                    "zygote_used": zygote_used,
                    "zygote_env_cache_hit": zygote_env_cache_hit,
                    "zygote_import_us": zygote_import_us,
                    "zygote_elab_us": zygote_elab_us,
                    "interface_hash": split.interface_hash,
                    "prefix_env_hash": shard.prefix_env_hash,
                    "total_shards_in_file": split.shards.len(),
                    "elapsed_ms": dur_ms
                }))?
            );
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
        return Ok(());
    }

    match store.acquire_singleflight(&shard_key, toolchain, "theorem_shard", "trusted")? {
        SingleflightOutcome::CacheHit { coalesced, .. } => {
            let elapsed_ms = t0.elapsed().as_millis();
            if json_output {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "status": "theorem_cache_hit",
                        "decl": target_decl,
                        "coalesced": coalesced,
                        "shard_key": shard_key,
                        "interface_hash": split.interface_hash,
                        "prefix_env_hash": shard.prefix_env_hash,
                        "elapsed_ms": elapsed_ms
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] SHARD CACHE HIT `{}` (coalesced={}, {} ms)",
                    target_decl, coalesced, elapsed_ms
                );
            }
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
                .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
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
            let mut used_constants: Vec<String> = Vec::new();

            let fast_local_zygote_url = if !verified_via_zygote && db_warm_on_open {
                pack::ensure_local_zygote_daemon(store, &HashMap::new())
            } else {
                None
            };
            let fast_lib_dir = canon_dir.join(".lake/build/lib/lean");
            let (mut env_vars, mut env_cache_hit, mut lean_bin, local_lean_path) =
                if fast_local_zygote_url.is_some() && fast_lib_dir.exists() {
                    let lp = resolve_remote_lean_path(canon_dir, None);
                    let mut fast_ev = HashMap::new();
                    fast_ev.insert("LEAN_PATH".to_string(), lp.clone());
                    (fast_ev, true, "lean".to_string(), lp)
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
                    } else {
                        splitter::build_fast_olean_shard_source_with_split(
                            &active_src,
                            split,
                            mod_imp,
                            &single_set,
                        )
                    }
                })
            };

            let mut inflight_tx_open = false;
            let mut try_zygote_src =
                |src_text: &str, ev: &HashMap<String, String>| -> Option<serde_json::Value> {
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
                    };
                    if let Some(ref z_url) = fast_local_zygote_url {
                        let res = pack::try_zygote_url_check_shard_with_inflight(z_url, &zreq, || {
                            if !inflight_tx_open {
                                if let Ok(r_bytes) = serde_json::to_vec(&serde_json::json!({
                                    "decl": target_decl,
                                    "prefix_env_hash": shard.prefix_env_hash,
                                    "stmt_hash": shard.stmt_hash,
                                    "proof_hash": shard.proof_hash,
                                    "verified_at": db::now_unix()
                                })) {
                                    let bh = blake3::hash(&r_bytes).to_hex().to_string();
                                    let sz = r_bytes.len() as i64;
                                    let single_pub = vec![(
                                        shard_key.clone(),
                                        target_decl.to_string(),
                                        r_bytes,
                                        1i64,
                                    )];
                                    if store.prestage_theorem_shard_blobs(&single_pub).is_ok() {
                                        store.write_singleflight_done(
                                            &shard_key,
                                            &[BlobEntry {
                                                blob_hash: bh,
                                                kind: "expr_shard".to_string(),
                                                rel_path: format!("thm:{}", target_decl),
                                                size_bytes: sz as u64,
                                            }],
                                        );
                                    }
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
                        });
                        if let Some(r) = res {
                            return Some(r);
                        }
                        if inflight_tx_open {
                            store.rollback_inflight_publish();
                            store.remove_singleflight_done(&shard_key);
                            inflight_tx_open = false;
                        }
                    }
                    pack::try_local_zygote_check_shard(store, ev, &zreq)
                };

            let extract_used_consts = |zjson: &serde_json::Value| -> Vec<String> {
                zjson
                    .get("used_constants")
                    .and_then(|v| v.as_array())
                    .map(|arr| {
                        arr.iter()
                            .filter_map(|x| x.as_str().map(|s| s.to_string()))
                            .collect()
                    })
                    .unwrap_or_default()
            };

            if !verified_via_zygote {
                if let Some(ref fsrc) = fast_olean_src {
                    if let Some(zjson) = try_zygote_src(fsrc, &env_vars) {
                        verified_via_fast_olean = true;
                        verified_via_zygote = true;
                        zygote_env_cache_hit = zjson
                            .get("zygote_env_cache_hit")
                            .and_then(|v| v.as_bool())
                            .unwrap_or(false);
                        zygote_import_us = zjson
                            .get("zygote_import_us")
                            .and_then(|v| v.as_u64())
                            .unwrap_or(0);
                        zygote_elab_us = zjson
                            .get("zygote_elab_us")
                            .and_then(|v| v.as_u64())
                            .unwrap_or(0);
                        used_constants = extract_used_consts(&zjson);
                    }
                }
            }

            if !verified_via_zygote {
                if let Some(ref psrc) = pruned_src {
                    if let Some(zjson) = try_zygote_src(psrc, &env_vars) {
                        verified_via_fast_olean = true;
                        verified_via_zygote = true;
                        zygote_env_cache_hit = zjson
                            .get("zygote_env_cache_hit")
                            .and_then(|v| v.as_bool())
                            .unwrap_or(false);
                        zygote_import_us = zjson
                            .get("zygote_import_us")
                            .and_then(|v| v.as_u64())
                            .unwrap_or(0);
                        zygote_elab_us = zjson
                            .get("zygote_elab_us")
                            .and_then(|v| v.as_u64())
                            .unwrap_or(0);
                        used_constants = extract_used_consts(&zjson);
                    }
                }
            }

            if !verified_via_zygote && env_vars.is_empty() {
                let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                lean_bin = lean_bin_from_env(&ev);
                env_vars = ev;
                env_cache_hit = ech;
            }

            if !verified_via_zygote {
                if let Some(ref fast_src) = fast_olean_src {
                    fs::write(&tmp_shard, fast_src)?;
                    let fast_out = Command::new(&lean_bin)
                        .arg(&tmp_shard)
                        .current_dir(canon_dir)
                        .envs(&env_vars)
                        .output()
                        .context("Failed to execute `lean` on fast-olean shard")?;
                    let _ = fs::remove_file(&tmp_shard);
                    if fast_out.status.success() {
                        verified_via_fast_olean = true;
                    }
                }
            }

            if !verified_via_zygote && !verified_via_fast_olean {
                if let Some(ref psrc) = pruned_src {
                    fs::write(&tmp_shard, psrc)?;
                    let pruned_out = Command::new(&lean_bin)
                        .arg(&tmp_shard)
                        .current_dir(canon_dir)
                        .envs(&env_vars)
                        .output()
                        .context("Failed to execute `lean` on pruned-imports shard")?;
                    let _ = fs::remove_file(&tmp_shard);
                    if pruned_out.status.success() {
                        verified_via_fast_olean = true;
                    }
                }
            }

            if !verified_via_zygote && !verified_via_fast_olean {
                let full_shard_src = if !shard.shard_source.is_empty() {
                    shard.shard_source.clone()
                } else {
                    splitter::reconstruct_single_shard_source(&active_src, &shard.name)
                        .unwrap_or_default()
                };
                if let Some(zjson) = try_zygote_src(&full_shard_src, &env_vars) {
                    verified_via_zygote = true;
                    zygote_env_cache_hit = zjson
                        .get("zygote_env_cache_hit")
                        .and_then(|v| v.as_bool())
                        .unwrap_or(false);
                    zygote_import_us = zjson
                        .get("zygote_import_us")
                        .and_then(|v| v.as_u64())
                        .unwrap_or(0);
                    zygote_elab_us = zjson
                        .get("zygote_elab_us")
                        .and_then(|v| v.as_u64())
                        .unwrap_or(0);
                    used_constants = extract_used_consts(&zjson);
                } else if let Ok(reply) = crate::zygote::eval_with_zygote_pool(
                    store,
                    toolchain,
                    &local_lean_path,
                    &env_vars,
                    Path::new(&lean_bin),
                    &full_shard_src,
                    true,
                ) {
                    if reply.import_ok && reply.ok {
                        verified_via_zygote = true;
                        zygote_env_cache_hit = reply.env_cache_hit;
                        zygote_import_us = reply.import_us;
                        zygote_elab_us = reply.elab_us;
                        if !reply.used_constants.is_empty() {
                            crate::accelerators::record_distilled_constants(
                                target_decl,
                                &shard.signature_text,
                                &reply.used_constants,
                            );
                        }
                        used_constants = reply.used_constants;
                    }
                }
                if !verified_via_zygote {
                    fs::write(&tmp_shard, &full_shard_src)?;
                    let out = Command::new(&lean_bin)
                        .arg(&tmp_shard)
                        .current_dir(canon_dir)
                        .envs(&env_vars)
                        .output()
                        .context("Failed to execute `lean` on theorem shard")?;
                    let _ = fs::remove_file(&tmp_shard);

                    if !out.status.success() {
                        let stderr = String::from_utf8_lossy(&out.stderr);
                        let stdout = String::from_utf8_lossy(&out.stdout);
                        anyhow::bail!(
                            "Shard check failed for `{}`:\n{}\n{}",
                            target_decl,
                            stdout,
                            stderr
                        );
                    }
                }
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
            } else {
                let cached_distilled = crate::accelerators::lookup_distilled_constants(
                    target_decl,
                    &shard.signature_text,
                );
                if !cached_distilled.is_empty() {
                    used_constants = cached_distilled;
                }
            }

            let dur_ms = t0.elapsed().as_millis() as i64;
            if inflight_tx_open {
                store.commit_inflight_publish_for_lease(&shard_key)?;
                drop(lease);
            } else {
                let receipt = serde_json::to_vec(&serde_json::json!({
                    "decl": target_decl,
                    "prefix_env_hash": shard.prefix_env_hash,
                    "stmt_hash": shard.stmt_hash,
                    "proof_hash": shard.proof_hash,
                    "verified_at": db::now_unix()
                }))?;
                store.publish_action_with_blob(
                    &lease,
                    &receipt,
                    "expr_shard",
                    &format!("thm:{}", target_decl),
                    dur_ms,
                    "trusted",
                )?;
                drop(lease);
            }

            if json_output {
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
                    "interface_hash": split.interface_hash,
                    "prefix_env_hash": shard.prefix_env_hash,
                    "total_shards_in_file": split.shards.len(),
                    "elapsed_ms": dur_ms
                });
                if !used_constants.is_empty()
                    && shard.proof_text.contains("simp")
                    && !shard.proof_text.contains("simp only")
                {
                    if let Some(obj) = out_json.as_object_mut() {
                        obj.insert(
                            "used_constants".to_string(),
                            serde_json::json!(used_constants),
                        );
                        obj.insert(
                            "distilled_simp_hint".to_string(),
                            serde_json::Value::String(format!(
                                "simp only [{}]",
                                used_constants.join(", ")
                            )),
                        );
                    }
                }
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
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn check_single_file(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    json_output: bool,
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
    parallel_shards: bool,
    remote_http: Option<&str>,
) -> Result<()> {
    let file_shard_keys: Vec<String> = split
        .shards
        .iter()
        .map(|shard| compute_shard_key(toolchain, shard))
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

    if misses == 0 && !split.shards.is_empty() && split.eligible_for_sharding {
        let elapsed_ms = t0.elapsed().as_millis();
        if json_output {
            println!(
                "{}",
                serde_json::to_string_pretty(&serde_json::json!({
                    "status": "all_shards_cached",
                    "file": file.display().to_string(),
                    "shard_hits": hits,
                    "shard_misses": 0,
                    "interface_hash": split.interface_hash,
                    "elapsed_ms": elapsed_ms
                }))?
            );
        } else {
            println!(
                "[turbo-lean] ALL {} THEOREM SHARDS CACHED in {} ({} ms)",
                hits,
                file.display(),
                elapsed_ms
            );
        }
        return Ok(());
    }

    let governor = crate::shm_cache::MemoryBudgetGovernor::detect();
    let default_jobs = if governor.is_low_memory_mode() {
        governor.recommended_parallel_workers(512)
    } else {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
    };
    let requested_jobs = jobs.unwrap_or(default_jobs).max(1);

    if split.eligible_for_sharding && !uncached_shards.is_empty() {
        if let Some(remote_url) = remote_http {
            if src.is_empty() {
                *src = fs::read_to_string(resolved_file)
                    .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
            }
            let effective_jobs = requested_jobs.min(uncached_shards.len());
            let uncached_names: HashSet<String> =
                uncached_shards.iter().map(|(_, s)| s.name.clone()).collect();
            let fast_lib_lean = canon_dir.join(".lake/build/lib/lean");
            let (env_cache_hit, lean_path_str) =
                if fast_lib_lean.exists() && !canon_dir.join(".lake/build/packages").is_dir() {
                    (db_warm_on_open, fast_lib_lean.to_string_lossy().to_string())
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

            let mut remote_resp = None;
            if let Some(mod_imp) = resolve_prebuilt_module_import(canon_dir, canon_resolved_initial)
            {
                if let Some(fast_src) = splitter::build_fast_olean_shard_source_with_split(
                    src,
                    split,
                    &mod_imp,
                    &uncached_names,
                ) {
                    if let Ok(r) = pack::offload_check_shards_batch_http(
                        store,
                        remote_url,
                        &req_items,
                        &fast_src,
                        "trusted",
                        toolchain,
                        &lean_path_str,
                    ) {
                        if r.ok {
                            remote_resp = Some(r);
                        }
                    }
                }
            }

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
            if json_output {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
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
                    }))?
                );
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
            return Ok(());
        }
    }

    let (env_vars, env_cache_hit) = resolve_lake_env(store, canon_dir)?;
    let lean_bin = lean_bin_from_env(&env_vars);
    let local_lean_path = resolve_remote_lean_path(canon_dir, Some(&env_vars));
    let use_parallel_shards = split.eligible_for_sharding
        && !uncached_shards.is_empty()
        && (parallel_shards || jobs.is_some() || hits > 0 || uncached_shards.len() > 1);

    if use_parallel_shards {
        let effective_jobs = requested_jobs.min(uncached_shards.len());
        let staging_dir = store.fast_staging_dir();
        let pid = std::process::id();

        let uncached_names: HashSet<String> =
            uncached_shards.iter().map(|(_, s)| s.name.clone()).collect();
        let tmp_coalesced = staging_dir.join(format!("coalesced_batch_{}.lean", pid));
        let batch_t0 = Instant::now();

        let proj_build_verified = split.hygiene.is_clean_for_certification()
            && cached_file_blake3
                .map(|h| is_file_hash_verified_in_lake_build(canon_dir, canon_resolved_initial, h))
                .unwrap_or_else(|| {
                    if src.is_empty() {
                        *src = fs::read_to_string(resolved_file).unwrap_or_default();
                    }
                    is_file_verified_in_lake_build(canon_dir, canon_resolved_initial, src)
                });
        let prebuilt_batch_mod =
            resolve_prebuilt_module_import(canon_dir, canon_resolved_initial);
        let mut batch_succeeded = proj_build_verified && prebuilt_batch_mod.is_some();
        if !batch_succeeded && src.is_empty() {
            *src = fs::read_to_string(resolved_file)
                .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
        }
        let pruned_batch_src = if batch_succeeded {
            None
        } else {
            splitter::build_pruned_imports_shard_source(src, &uncached_names)
        };
        let fast_batch_src = if batch_succeeded {
            None
        } else {
            prebuilt_batch_mod.as_ref().and_then(|mod_imp| {
                if proj_build_verified {
                    Some(format!("import {}\n#check Nat\n", mod_imp))
                } else {
                    splitter::build_fast_olean_shard_source_with_split(
                        src,
                        split,
                        mod_imp,
                        &uncached_names,
                    )
                }
            })
        };

        for cand_src in [pruned_batch_src.as_deref(), fast_batch_src.as_deref()]
            .into_iter()
            .flatten()
        {
            if batch_succeeded {
                break;
            }
            if pack::try_local_zygote_check_shard(
                store,
                &env_vars,
                &pack::CheckShardHttpRequest {
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
                },
            )
            .is_some()
            {
                batch_succeeded = true;
            }
        }

        for cand_src in [pruned_batch_src.as_deref(), fast_batch_src.as_deref()]
            .into_iter()
            .flatten()
        {
            if batch_succeeded {
                break;
            }
            fs::write(&tmp_coalesced, cand_src)?;
            let out = Command::new(&lean_bin)
                .arg(&tmp_coalesced)
                .current_dir(canon_dir)
                .envs(&env_vars)
                .output()
                .context("Failed to execute `lean` on fast coalesced batch")?;
            let _ = fs::remove_file(&tmp_coalesced);
            if out.status.success() {
                batch_succeeded = true;
            }
        }

        if !batch_succeeded {
            let coalesced_src = splitter::build_coalesced_shard_source(src, &uncached_names);
            if pack::try_local_zygote_check_shard(
                store,
                &env_vars,
                &pack::CheckShardHttpRequest {
                    decl: "__coalesced_batch__".to_string(),
                    shard_key: uncached_shards[0].0.clone(),
                    shard_source: coalesced_src.clone(),
                    interface_hash: split.interface_hash.clone(),
                    prefix_env_hash: String::new(),
                    stmt_hash: String::new(),
                    proof_hash: String::new(),
                    toolchain: toolchain.to_string(),
                    lean_path: local_lean_path,
                    skip_cas_lock: true,
                },
            )
            .is_some()
            {
                batch_succeeded = true;
            } else {
                fs::write(&tmp_coalesced, &coalesced_src)?;
                let batch_out = Command::new(&lean_bin)
                    .arg(&tmp_coalesced)
                    .current_dir(canon_dir)
                    .envs(&env_vars)
                    .output()
                    .context("Failed to execute `lean` on coalesced shard batch")?;
                let _ = fs::remove_file(&tmp_coalesced);
                if batch_out.status.success() {
                    batch_succeeded = true;
                }
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
            let next_idx = std::sync::atomic::AtomicUsize::new(0);
            let src_ref: &str = src.as_str();
            let worker_results: Vec<Result<Vec<(String, &splitter::TheoremShard, i64)>>> =
                std::thread::scope(|s| {
                    let mut handles = Vec::with_capacity(effective_jobs);
                    for _worker_id in 0..effective_jobs {
                        let next_idx_ref = &next_idx;
                        let uncached_ref = &uncached_shards;
                        let staging_ref = &staging_dir;
                        let canon_ref = canon_dir;
                        let env_ref = &env_vars;
                        let lean_bin_ref = &lean_bin;

                        handles.push(s.spawn(move || -> Result<Vec<(String, &splitter::TheoremShard, i64)>> {
                            let mut verified = Vec::new();
                            loop {
                                let idx = next_idx_ref.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                                if idx >= uncached_ref.len() {
                                    break;
                                }
                                let (ref shard_key, shard) = uncached_ref[idx];
                                let shard_t0 = Instant::now();
                                let safe_name: String = shard
                                    .name
                                    .chars()
                                    .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
                                    .collect();
                                let tmp_shard = staging_ref.join(format!(
                                    "par_shard_{}_{}_{}.lean",
                                    safe_name, pid, idx
                                ));
                                if shard.shard_source.is_empty() {
                                    let mut single_set = HashSet::with_capacity(1);
                                    single_set.insert(shard.name.clone());
                                    let reconstructed = splitter::build_coalesced_shard_source(src_ref, &single_set);
                                    fs::write(&tmp_shard, &reconstructed)?;
                                } else {
                                    fs::write(&tmp_shard, &shard.shard_source)?;
                                }

                                let out = Command::new(lean_bin_ref)
                                    .arg(&tmp_shard)
                                    .current_dir(canon_ref)
                                    .envs(env_ref)
                                    .output()
                                    .with_context(|| {
                                        format!("Failed to execute `lean` on shard `{}`", shard.name)
                                    })?;
                                let _ = fs::remove_file(&tmp_shard);

                                if !out.status.success() {
                                    let stderr = String::from_utf8_lossy(&out.stderr);
                                    let stdout = String::from_utf8_lossy(&out.stdout);
                                    anyhow::bail!(
                                        "Parallel shard check failed for `{}`:\n{}\n{}",
                                        shard.name,
                                        stdout,
                                        stderr
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
            for wr in worker_results {
                verified.extend(wr?);
            }
            (verified, "parallel_shards")
        };

        let now = db::now_unix();
        let mut batch_items = Vec::with_capacity(all_verified.len());
        for (shard_key, shard, shard_dur_ms) in all_verified {
            let receipt = serde_json::to_vec(&serde_json::json!({
                "decl": shard.name,
                "prefix_env_hash": shard.prefix_env_hash,
                "stmt_hash": shard.stmt_hash,
                "proof_hash": shard.proof_hash,
                "verified_at": now
            }))?;
            batch_items.push((shard_key, shard.name.clone(), receipt, shard_dur_ms));
        }
        store.batch_publish_theorem_shards(toolchain, "trusted", &batch_items)?;

        let dur_ms = t0.elapsed().as_millis() as i64;
        if json_output {
            println!(
                "{}",
                serde_json::to_string_pretty(&serde_json::json!({
                    "status": "file_verified",
                    "mode": verify_mode,
                    "file": file.display().to_string(),
                    "shard_hits": hits,
                    "shard_misses": misses,
                    "parallel_jobs": effective_jobs,
                    "lake_env_cache_hit": env_cache_hit,
                    "interface_hash": split.interface_hash,
                    "elapsed_ms": dur_ms
                }))?
            );
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
    } else {
        let out = Command::new(&lean_bin)
            .arg(canon_resolved_initial)
            .current_dir(canon_dir)
            .envs(&env_vars)
            .output()
            .context("Failed to execute `lean`")?;

        if !out.status.success() {
            let stderr = String::from_utf8_lossy(&out.stderr);
            let stdout = String::from_utf8_lossy(&out.stdout);
            anyhow::bail!("Check failed for {}:\n{}\n{}", file.display(), stdout, stderr);
        }

        let dur_ms = t0.elapsed().as_millis() as i64;
        for (shard_key, shard) in uncached_shards {
            if let SingleflightOutcome::Leader(lease) =
                store.acquire_singleflight(&shard_key, toolchain, "theorem_shard", "trusted")?
            {
                let receipt = serde_json::to_vec(&serde_json::json!({
                    "decl": shard.name,
                    "prefix_env_hash": shard.prefix_env_hash,
                    "stmt_hash": shard.stmt_hash,
                    "proof_hash": shard.proof_hash,
                    "verified_at": db::now_unix()
                }))?;
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

        if json_output {
            println!(
                "{}",
                serde_json::to_string_pretty(&serde_json::json!({
                    "status": "file_verified",
                    "mode": "whole_file",
                    "file": file.display().to_string(),
                    "shard_hits": hits,
                    "shard_misses": misses,
                    "lake_env_cache_hit": env_cache_hit,
                    "interface_hash": split.interface_hash,
                    "elapsed_ms": dur_ms
                }))?
            );
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
    Ok(())
}

impl TurboStore {
    /// Fast `< 0.1 ms` disk check for whether `shard_key` is already verified and backed by a CAS blob on disk.
    #[allow(dead_code)]
    pub fn has_theorem_shard(&self, shard_key: &str) -> bool {
        self.has_cached_action_readonly(shard_key, "trusted")
            .unwrap_or(false)
    }

    /// Persist a single verified theorem or sub-shard receipt immediately to SQLite + CAS on disk.
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
}

/// Out-of-Core Disk Checkpointing Helper for decomposed sub-shards (`have`-fission cuts).
///
/// Takes a slice of `(step_label, sub_shard_key, sub_decl_source)` tuples:
/// 1. Checks `store.has_theorem_shard(&sub_shard_key)` on disk first (`< 0.1 ms` instant hit if resuming after interruption at step `k`).
/// 2. Evaluates any uncached sub-shard via `crate::zygote::eval_shard_via_zygote` with `prefix_source + sub_decl_source`.
/// 3. Immediately persists each verified sub-shard receipt into `store.put_theorem_shard(...)` on disk before moving to the next step.
/// 4. Returns `Ok((disk_cached_hits, newly_verified_count))`.
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
    let mut disk_cached_hits = 0usize;
    let mut newly_verified = 0usize;

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
        let sub_hash = blake3::hash(sub_decl_source.as_bytes()).to_hex().to_string();
        let receipt = serde_json::to_vec(&serde_json::json!({
            "decl": step_label,
            "sub_shard_key": sub_shard_key,
            "prefix_env_hash": prefix_env_hash,
            "stmt_hash": sub_hash,
            "proof_hash": sub_hash,
            "verified_at": db::now_unix(),
        }))?;
        store.put_theorem_shard(toolchain, sub_shard_key, step_label, &receipt, dur_ms)?;
        newly_verified += 1;
    }

    Ok((disk_cached_hits, newly_verified))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_subshards_out_of_core_disk_checkpoint_resume() {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_ooc_subshards_test_{}",
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(&tmp_dir).expect("create temp store dir");
        let mut store = TurboStore::open(Some(&tmp_dir)).expect("open TurboStore");
        let toolchain = "leanprover/lean4:v4.31.0";
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

        // Simulate run interrupted after step 0 and step 1:
        let first_batch = vec![step0.clone(), step1.clone()];
        let (hits1, verified1) = verify_subshards_out_of_core(
            &mut store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            prefix_src,
            &first_batch,
        )
        .expect("verify first 2 sub-shards out-of-core");
        assert_eq!(hits1, 0);
        assert_eq!(verified1, 2);
        assert!(store.has_theorem_shard(&step0.1));
        assert!(store.has_theorem_shard(&step1.1));
        assert!(!store.has_theorem_shard(&step2.1));

        // Resume full 3-step sequence: steps 0..1 must be instant disk hits, only step 2 newly verified!
        let full_batch = vec![step0, step1, step2.clone()];
        let (hits2, verified2) = verify_subshards_out_of_core(
            &mut store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            prefix_src,
            &full_batch,
        )
        .expect("resume full 3-step sub-shards out-of-core");
        assert_eq!(hits2, 2);
        assert_eq!(verified2, 1);
        assert!(store.has_theorem_shard(&step2.1));

        let _ = fs::remove_dir_all(&tmp_dir);
    }
}

