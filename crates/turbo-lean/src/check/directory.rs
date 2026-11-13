use anyhow::{Context, Result};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::db::{self, TurboStore};
use crate::lake_build::{
    collect_lean_files, compute_imported_olean_interface_hashes, compute_shard_key_with_args,
    load_and_split_files_with_hashes_cached, load_verified_project_manifest, resolve_lake_env,
    resolve_lean_bin, resolve_remote_lean_path, resolve_replayed_prebuilt_module_import,
};
use crate::pack;
use crate::splitter::{self, split_lean_source};

use super::diagnostics::insert_allow_sorry_fields;
use super::identity::prewarm_local_check_zygote;
use super::single_file::check_single_file;
use super::{default_parallel_jobs, make_shard_receipt_bytes};

#[allow(clippy::too_many_arguments)]
pub(super) fn check_directory(
    store: &mut TurboStore,
    json_output: bool,
    emit_stdout: bool,
    kernel_prov: &crate::kernel::KernelProvenance,
    t0: &Instant,
    file: &Path,
    resolved_file: &Path,
    canon_dir: &Path,
    toolchain: &str,
    jobs: Option<usize>,
    remote_http: Option<&str>,
    allow_sorry: bool,
) -> Result<serde_json::Value> {
    let dir_files = collect_lean_files(resolved_file);
    let refresh_start = Instant::now();
    let fresh_res = crate::lake_build::ensure_project_imports_fresh_for_check_with_options(
        canon_dir,
        &dir_files,
        allow_sorry,
    );
    if fresh_res.is_err() && allow_sorry {
        crate::lake_build::purge_sorry_artifacts_after_allow_sorry_failure(canon_dir, &dir_files);
    }
    fresh_res?;
    let import_res = crate::module_builder::ensure_imported_oleans_replayed_with_options(
        store,
        canon_dir,
        &dir_files,
        allow_sorry,
    );
    if import_res.is_err() && allow_sorry {
        crate::lake_build::purge_sorry_artifacts_after_allow_sorry_failure(canon_dir, &dir_files);
    }
    import_res?;
    super::record_phase("import_refresh", refresh_start);
    let mut dir_hasher = blake3::Hasher::new();
    dir_hasher.update(b"dir-check-v2\n");
    dir_hasher.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    dir_hasher.update(b"\n");
    dir_hasher.update(toolchain.as_bytes());

    let dir_pkg_cfg = crate::module_builder::optional_package_config(canon_dir)?;
    let (split_entries, split_cache_hits) =
        load_and_split_files_with_hashes_cached(store, &dir_files)?;
    let mut parsed_files = Vec::with_capacity(split_entries.len());
    let mut all_shard_keys = Vec::new();
    let mut sorry_files: Vec<PathBuf> = Vec::new();
    let tainted_sorry_paths = if allow_sorry {
        crate::lake_build::workspace_tainted_sorry_paths(canon_dir, &dir_files)
    } else {
        HashSet::new()
    };

    for (lf, src_blake3, src, split) in split_entries {
        let rel = lf.strip_prefix(canon_dir).unwrap_or(&lf);
        dir_hasher.update(rel.to_string_lossy().as_bytes());
        dir_hasher.update(b":");
        dir_hasher.update(split.interface_hash.as_bytes());
        dir_hasher.update(b"\n");

        let lf_canon = lf.canonicalize().unwrap_or_else(|_| lf.clone());
        if allow_sorry
            && split.hygiene.is_clean_modulo_sorry()
            && (!split.hygiene.is_clean_for_certification()
                || tainted_sorry_paths.contains(&lf_canon))
        {
            sorry_files.push(lf);
            continue;
        }

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
    let dirty: Vec<String> = parsed_files
        .iter()
        .filter(|(_, _, _, split, _, _)| {
            if allow_sorry {
                !split.hygiene.is_clean_modulo_sorry()
                    && !split.hygiene.is_clean_or_deferred_to_kernel_gate()
            } else {
                !split.hygiene.is_clean_or_deferred_to_kernel_gate()
            }
        })
        .map(|(lf, _, _, split, _, _)| {
            let items = if allow_sorry {
                split.hygiene.disallowed_items_modulo_sorry()
            } else {
                split.hygiene.disallowed_items()
            };
            format!("{}: {}", lf.display(), items.join(", "))
        })
        .collect();
    if !dirty.is_empty() {
        if allow_sorry {
            crate::lake_build::purge_sorry_artifacts_after_allow_sorry_failure(
                canon_dir, &dir_files,
            );
        }
        anyhow::bail!("Soundness hygiene violation in {}", dirty.join("; "));
    }

    let mut dir_used_sorry = false;
    let mut dir_sorry_decls: Vec<String> = Vec::new();
    let mut dir_sorry_hits = 0usize;
    let mut dir_sorry_misses = 0usize;
    for sf in &sorry_files {
        let mut sf_src =
            fs::read_to_string(sf).with_context(|| format!("Failed to read {}", sf.display()))?;
        let sf_canon = sf.canonicalize().unwrap_or_else(|_| sf.clone());
        let sf_deps = compute_imported_olean_interface_hashes(&sf_src, canon_dir, None);
        let sf_split = split_lean_source(&sf_src, &sf_deps);
        let sf_b3 = blake3::hash(sf_src.as_bytes()).to_hex().to_string();
        let sf_res = check_single_file(
            store,
            true,
            false,
            false,
            kernel_prov,
            t0,
            sf,
            sf,
            &sf_canon,
            canon_dir,
            toolchain,
            &mut sf_src,
            Some(sf_b3.as_str()),
            &sf_split,
            0,
            jobs,
            true,
            remote_http,
            true,
        );
        if sf_res.is_err() && allow_sorry {
            crate::lake_build::purge_sorry_artifacts_after_allow_sorry_failure(
                canon_dir, &dir_files,
            );
        }
        let sf_json = sf_res?;
        dir_sorry_hits += sf_json
            .get("shard_hits")
            .and_then(|v| v.as_u64())
            .unwrap_or(0) as usize;
        dir_sorry_misses += sf_json
            .get("shard_misses")
            .and_then(|v| v.as_u64())
            .unwrap_or(0) as usize;
        if sf_json
            .get("used_sorry")
            .and_then(|v| v.as_bool())
            .unwrap_or(false)
        {
            dir_used_sorry = true;
        }
        if let Some(arr) = sf_json.get("sorry_decls").and_then(|v| v.as_array()) {
            for item in arr.iter().filter_map(|x| x.as_str()) {
                let s = item.to_string();
                if !dir_sorry_decls.contains(&s) {
                    dir_sorry_decls.push(s);
                }
            }
        }
    }

    let cached_map = store.batch_get_theorem_shards(&all_shard_keys, "trusted")?;

    let mut total_hits = 0usize;
    let mut uncached_files = Vec::new();
    let mut deferred_kernel_gate_files = Vec::new();
    for (lf, src_blake3, src, split, file_keys, file_lean_args) in parsed_files {
        let file_hygiene_clean = split.hygiene.is_clean_for_certification();
        if !file_hygiene_clean {
            let names: HashSet<String> = split.shards.iter().map(|s| s.rooted_name()).collect();
            deferred_kernel_gate_files.push((lf, src, names, file_lean_args));
            continue;
        }
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
            uncached_files.push((lf, src_blake3, src, file_uncached, file_lean_args));
        }
    }

    let deferred_verified_files = deferred_kernel_gate_files.len();
    if !deferred_kernel_gate_files.is_empty() {
        let (def_env_vars, _) = resolve_lake_env(store, canon_dir)?;
        let def_lean_bin = resolve_lean_bin(canon_dir)?;
        for (lf, mut src, names, file_lean_args) in deferred_kernel_gate_files {
            if src.is_empty() {
                src = fs::read_to_string(&lf).with_context(|| {
                    format!(
                        "Failed to read deferred policy-gated file `{}`",
                        lf.display()
                    )
                })?;
            }
            let (out, _) = crate::zygote::run_audited_lean_shard_at_with_types_report(
                &store.root,
                &store.fast_staging_dir(),
                Path::new(&def_lean_bin),
                &def_env_vars,
                Some(canon_dir),
                Some(&lf),
                &src,
                &names,
                false,
                &[],
                &file_lean_args,
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
    }

    let total_misses: usize = uncached_files.iter().map(|(_, _, _, u, _)| u.len()).sum();
    if total_misses == 0 {
        let elapsed_ms = t0.elapsed().as_millis();
        let combined_hits = total_hits + dir_sorry_hits;
        let combined_misses = dir_sorry_misses;
        let mut out_json = serde_json::json!({
            "status": if dir_used_sorry {
                "verified_modulo_sorry"
            } else if dir_sorry_misses > 0 || deferred_verified_files > 0 {
                "file_verified"
            } else {
                "all_shards_cached"
            },
            "file": file.display().to_string(),
            "files_checked": dir_files.len(),
            "file_split_cache_hits": split_cache_hits,
            "shard_hits": combined_hits,
            "shard_misses": combined_misses,
            "interface_hash": dir_interface_hash,
            "elapsed_ms": elapsed_ms
        });
        insert_allow_sorry_fields(&mut out_json, allow_sorry, dir_used_sorry, &dir_sorry_decls);
        kernel_prov.insert_json_fields(&mut out_json);
        super::insert_check_timings(&mut out_json, *t0);
        if emit_stdout {
            if json_output {
                println!("{}", serde_json::to_string_pretty(&out_json)?);
            } else if dir_used_sorry {
                println!(
                    "[turbo-lean] VERIFIED MODULO SORRY {} files in {} ({} sorry decl(s): [{}], {} clean hits, {} ms)",
                    dir_files.len(),
                    file.display(),
                    dir_sorry_decls.len(),
                    dir_sorry_decls.join(", "),
                    combined_hits,
                    elapsed_ms
                );
            } else if deferred_verified_files == 0 {
                println!(
                    "[turbo-lean] ALL {} THEOREM SHARDS CACHED across {} files in {} ({} ms)",
                    combined_hits,
                    dir_files.len(),
                    file.display(),
                    elapsed_ms
                );
            } else {
                println!(
                    "[turbo-lean] DIRECTORY VERIFIED across {} files in {} ({} shard hits, {} policy-gated files, {} ms)",
                    dir_files.len(),
                    file.display(),
                    combined_hits,
                    deferred_verified_files,
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
        crate::lake_build::recheck_dependents_if_nonlocal_with_options(
            store,
            canon_dir,
            resolved_file,
            allow_sorry,
        )?;
        return Ok(out_json);
    }

    let t0 = &prewarm_local_check_zygote(store, canon_dir, toolchain, t0)?;
    let effective_jobs = default_parallel_jobs(jobs).min(uncached_files.len());
    let _staging_dir = store.fast_staging_dir();
    let pid = std::process::id();

    let proj_build_verified = remote_http.is_none()
        && load_verified_project_manifest(canon_dir).is_some_and(|manifest| {
            uncached_files.iter().all(|(lf, sb, _, _, _)| {
                !sb.is_empty()
                    && crate::lake_build::is_file_and_imports_verified_in_manifest(
                        canon_dir, lf, sb, &manifest,
                    )
                    && resolve_replayed_prebuilt_module_import(store, canon_dir, lf).is_some()
            })
        });

    if !proj_build_verified {
        for (lf, _sb, src, _, _) in &mut uncached_files {
            if src.is_empty() {
                *src = fs::read_to_string(&*lf).unwrap_or_default();
            }
        }
    }
    #[allow(clippy::type_complexity)]
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
        if let Some(mod_imp) = resolve_replayed_prebuilt_module_import(store, canon_dir, &canon_lf)
        {
            let uncached_names: HashSet<String> = file_uncached
                .iter()
                .map(|(_, sh)| sh.rooted_name())
                .collect();
            if splitter::can_use_fast_olean_import(src, &uncached_names) {
                cross_eligible.push((mod_imp, src.as_str(), file_uncached));
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
    let lean_bin = resolve_lean_bin(canon_dir)?;

    #[allow(clippy::type_complexity)]
    let mut cross_verified_items: Option<Vec<(String, String, Vec<u8>, i64)>> = None;
    let mut cross_zygote_err: Option<anyhow::Error> = None;
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
        let shard_ref_vecs: Vec<Vec<&splitter::TheoremShard>> = cross_eligible
            .iter()
            .map(|(_, _, fu)| fu.iter().map(|(_, sh)| sh).collect())
            .collect();
        let cross_inputs: Vec<(&str, &str, &[&splitter::TheoremShard])> = cross_eligible
            .iter()
            .enumerate()
            .map(|(i, (m, s, _))| (m.as_str(), *s, shard_ref_vecs[i].as_slice()))
            .collect();
        let cross_src = splitter::build_cross_file_coalesced_shard(&cross_inputs);
        if let Some(remote_url) = remote_http {
            let mut req_items = Vec::with_capacity(total_misses);
            for (_, _, file_uncached, _) in &uncached_files {
                for (k, sh) in file_uncached {
                    req_items.push(pack::CheckShardBatchItem {
                        shard_key: k.clone(),
                        decl_name: sh.rooted_name(),
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
            let cross_names: HashSet<String> = uncached_files
                .iter()
                .flat_map(|(_, _, fu, _)| fu.iter().map(|(_, sh)| sh.rooted_name()))
                .collect();
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
                targets: cross_names.iter().cloned().collect(),
                expected_kernel_type_hash: None,
            };
            let mut cross_ok = proj_build_verified;
            if !cross_ok {
                match pack::try_local_zygote_check_shard_detailed(store, &env_vars, &zreq) {
                    Ok(Some(_)) => cross_ok = true,
                    Ok(None) => {
                        cross_ok = crate::zygote::run_audited_lean_shard(
                            store,
                            Path::new(&lean_bin),
                            &env_vars,
                            Some(canon_dir),
                            &cross_src,
                            &cross_names,
                            &cross_args,
                            Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                        )?
                        .status
                        .success();
                    }
                    Err(e) => cross_zygote_err = Some(e),
                }
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
        if local_zygote_url.is_none() {
            if let Some(e) = cross_zygote_err {
                return Err(e);
            }
        }
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
                            .map(|(_, sh)| sh.rooted_name())
                            .collect();
                        let f_t0 = Instant::now();

                        let mut batch_ok = false;
                        if let Some(mod_imp) = resolve_replayed_prebuilt_module_import(
                            &worker_store,
                            canon_ref,
                            &canon_lf,
                        ) {
                            if let Some(fast_src) = splitter::build_fast_olean_shard_source(
                                src,
                                &mod_imp,
                                &uncached_names,
                            ) {
                                let mut fast_unavailable = true;
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
                                        targets: uncached_names.iter().cloned().collect(),
                                        expected_kernel_type_hash: None,
                                    };
                                    match pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
                                        z_url, &zreq, || {},
                                    ) {
                                        Ok(Some(_)) => {
                                            batch_ok = true;
                                            fast_unavailable = false;
                                        }
                                        Ok(None) => {}
                                        Err(_) => fast_unavailable = false,
                                    }
                                }
                                if !batch_ok && fast_unavailable {
                                    batch_ok = crate::zygote::run_audited_lean_shard(
                                        &worker_store,
                                        Path::new(lean_bin_ref),
                                        env_ref,
                                        Some(canon_ref),
                                        &fast_src,
                                        &uncached_names,
                                        file_lean_args,
                                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                                    )?
                                    .status
                                    .success();
                                }
                            }
                        }

                        if !batch_ok {
                            let coal_src =
                                splitter::build_coalesced_shard_source(src, &uncached_names);
                            if let Some(z_url) = z_url_ref {
                                let zreq = pack::CheckShardHttpRequest {
                                    decl: "__batch__".to_string(),
                                    shard_key: format!("dir_coal_{}_{}", pid, f_idx),
                                    shard_source: coal_src.clone(),
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
                                    targets: uncached_names.iter().cloned().collect(),
                                    expected_kernel_type_hash: None,
                                };
                                match pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
                                    z_url, &zreq, || {},
                                ) {
                                    Ok(Some(_)) => batch_ok = true,
                                    Ok(None) => {}
                                    Err(e) => {
                                        anyhow::bail!(
                                            "Directory check failed in {}:\n{}",
                                            lf.display(),
                                            e
                                        );
                                    }
                                }
                            }
                            if !batch_ok {
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
                                    let combined = format!("{}\n{}", stdout, stderr);
                                    let hotspot_suffix =
                                        if crate::zygote::text_indicates_timeout_or_heartbeat(
                                            &combined,
                                        ) {
                                            crate::zygote::diagnose_hotspots_with_zygote_pool(
                                                &worker_store,
                                                tc_ref,
                                                lp_ref,
                                                env_ref,
                                                Path::new(lean_bin_ref),
                                                &coal_src,
                                                Some(&lf.to_string_lossy()),
                                                None,
                                                file_lean_args,
                                            )
                                            .map(|(th, sh)| {
                                                let fmt =
                                                    crate::zygote::format_hotspot_diagnostics(
                                                        &th, &sh,
                                                    );
                                                if fmt.is_empty() {
                                                    String::new()
                                                } else {
                                                    format!("\n{fmt}")
                                                }
                                            })
                                            .unwrap_or_default()
                                        } else {
                                            String::new()
                                        };
                                    anyhow::bail!(
                                        "Directory check failed in {}:\n{}{}",
                                        lf.display(),
                                        combined,
                                        hotspot_suffix
                                    );
                                }
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
    let combined_hits = total_hits + dir_sorry_hits;
    let combined_misses = total_misses + dir_sorry_misses;
    let mut out_json = serde_json::json!({
        "status": if dir_used_sorry { "verified_modulo_sorry" } else { "file_verified" },
        "mode": dir_verify_mode,
        "file": file.display().to_string(),
        "files_checked": dir_files.len(),
        "shard_hits": combined_hits,
        "shard_misses": combined_misses,
        "parallel_jobs": effective_jobs,
        "lake_env_cache_hit": env_cache_hit,
        "interface_hash": dir_interface_hash,
        "elapsed_ms": elapsed_ms
    });
    insert_allow_sorry_fields(&mut out_json, allow_sorry, dir_used_sorry, &dir_sorry_decls);
    kernel_prov.insert_json_fields(&mut out_json);
    super::insert_check_timings(&mut out_json, *t0);
    if emit_stdout {
        if json_output {
            println!("{}", serde_json::to_string_pretty(&out_json)?);
        } else if dir_used_sorry {
            println!(
                "[turbo-lean] VERIFIED MODULO SORRY {} files in {} ({} sorry decl(s): [{}], {} clean hits, {} clean misses cached, {} ms)",
                dir_files.len(),
                file.display(),
                dir_sorry_decls.len(),
                dir_sorry_decls.join(", "),
                combined_hits,
                total_misses,
                elapsed_ms
            );
        } else {
            println!(
                "[turbo-lean] VERIFIED {} files in {} ({} hits, {} misses cached, {} ms)",
                dir_files.len(),
                file.display(),
                combined_hits,
                combined_misses,
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
    crate::lake_build::recheck_dependents_if_nonlocal_with_options(
        store,
        canon_dir,
        resolved_file,
        allow_sorry,
    )?;
    Ok(out_json)
}
