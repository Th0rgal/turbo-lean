use anyhow::{Context, Result};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;
use std::time::Instant;

use crate::db::{self, SingleflightOutcome, TurboStore};
use crate::lake_build::{
    compute_imported_olean_interface_hashes, compute_shard_key_with_args, compute_single_stat_hash,
    is_file_hash_verified_in_lake_build, is_file_verified_in_lake_build, resolve_lake_env,
    resolve_lean_bin, resolve_remote_lean_path, resolve_replayed_prebuilt_module_import,
    shm_file_splits_dir, ShmCachedFileSplit,
};
use crate::pack;
use crate::splitter::{self, split_lean_source};

use super::diagnostics::{
    extract_mismatch_diagnostics, format_mismatch_diagnostics_summary, insert_allow_sorry_fields,
};
use super::identity::{confirm_decl_identity_with_budget, prewarm_local_check_zygote};
use super::remote::emit_remote_decl_result;
use super::{cache_shm_stat_split_with_prefix, make_attested_shard_receipt_bytes};

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
            "fission-v8:{}:{}:{}:{}:{}:ax:{}",
            crate::zygote::ZYGOTE_SCANNER_VERSION,
            crate::zygote::ZYGOTE_REPLAY_VERSION,
            toolchain,
            prefix_env_hash,
            sub_shard_key,
            &ax_hash.as_str()[..24]
        )
    } else {
        format!(
            "fission-v8:{}:{}:{}:{}:{}",
            crate::zygote::ZYGOTE_SCANNER_VERSION,
            crate::zygote::ZYGOTE_REPLAY_VERSION,
            toolchain,
            prefix_env_hash,
            sub_shard_key
        )
    };
    if let Some(opts_digest) = crate::module_builder::effective_lean_args_digest(lean_args) {
        base.push_str(":opts:");
        base.push_str(&opts_digest);
    }
    base
}

fn subshard_receipt_provenance_ok(store: &TurboStore, blob_hash: &str) -> bool {
    let Some(bytes) = store.read_verified_blob(blob_hash) else {
        return false;
    };
    let Ok(val) = serde_json::from_slice::<serde_json::Value>(&bytes) else {
        return false;
    };
    let version = |field: &str| val[field].as_u64().and_then(|v| u32::try_from(v).ok());
    crate::zygote::verifier_provenance_ok(
        version("scanner_version").unwrap_or(0),
        version("replay_version").unwrap_or(0),
    )
}

#[cfg(test)]
pub(super) fn store_has_provenanced_subshard(store: &TurboStore, key: &str) -> bool {
    store
        .batch_get_theorem_shards_readonly(std::slice::from_ref(&key.to_string()), "trusted")
        .ok()
        .and_then(|m| m.get(key).cloned())
        .is_some_and(|bh| subshard_receipt_provenance_ok(store, &bh))
}

pub(super) fn extract_decl_source_from_file(
    active_src: &str,
    shard: &splitter::TheoremShard,
) -> String {
    let extracted = splitter::extract_shard_orig_decl(active_src, shard);
    if !extracted.is_empty() {
        return extracted;
    }
    if !shard.signature_text.is_empty() && !shard.proof_text.is_empty() {
        return format!("{} := {}", shard.signature_text, shard.proof_text);
    }
    String::new()
}

/// Hygiene items (`sorry`/`admit`/`sorryAx`, forbidden axioms, ...) that block certifying `shard` alone:
/// the file report's items on its lines, else those of a fresh audit of its statement and proof text.
pub(super) fn target_hygiene_violations(
    split: &splitter::SplitResult,
    shard: &splitter::TheoremShard,
    allow_sorry: bool,
) -> Vec<String> {
    let on_shard_lines = |item: &String| {
        item.strip_prefix('L')
            .and_then(|r| r.split_once(": "))
            .and_then(|(ln, _)| ln.parse::<usize>().ok())
            .is_some_and(|ln| shard.start_line <= ln && ln <= shard.end_line)
    };
    let mut items: Vec<String> = if allow_sorry {
        split.hygiene.disallowed_items_modulo_sorry()
    } else {
        split.hygiene.disallowed_items()
    };
    items.retain(on_shard_lines);
    if items.is_empty() {
        let text = format!("{}\n{}", shard.signature_text, shard.proof_text);
        let fresh = splitter::audit_hygiene(&splitter::strip_lean_comments(&text));
        items = if allow_sorry {
            fresh.disallowed_items_modulo_sorry()
        } else {
            fresh.disallowed_items()
        };
    }
    items
}

pub(super) fn shard_text_contains_sorry_or_admit(shard: &splitter::TheoremShard) -> bool {
    let text = format!("{}\n{}", shard.signature_text, shard.proof_text);
    let rep = splitter::audit_hygiene(&splitter::strip_lean_comments(&text));
    rep.has_sorry
}

#[allow(clippy::too_many_arguments)]
pub(super) fn maybe_append_hotspot_diagnostics_for_source(
    store: &TurboStore,
    toolchain: &str,
    local_lean_path: &str,
    env_vars: &HashMap<String, String>,
    lean_bin: &Path,
    source: &str,
    file_name: Option<&str>,
    lean_args: &[String],
    err_text: &str,
) -> String {
    if !crate::zygote::text_indicates_timeout_or_heartbeat(err_text)
        || err_text.contains("[hotspot] ")
    {
        return String::new();
    }
    crate::zygote::diagnose_hotspots_with_zygote_pool(
        store,
        toolchain,
        local_lean_path,
        env_vars,
        lean_bin,
        source,
        file_name,
        None,
        lean_args,
    )
    .map(|(th, sh)| {
        let fmt = crate::zygote::format_hotspot_diagnostics(&th, &sh);
        if fmt.is_empty() {
            String::new()
        } else {
            format!("\n{fmt}")
        }
    })
    .unwrap_or_default()
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_single_decl(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    json_output: bool,
    emit_stdout: bool,
    kernel_prov: &crate::kernel::KernelProvenance,
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
    allow_sorry: bool,
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
                    let pref_src = if sub_src.len() <= 64 * 1024 {
                        sub_src.clone()
                    } else {
                        String::new()
                    };
                    cache_shm_stat_split_with_prefix(
                        store, &sub_canon, &sub_b3, &sub_split, pref_src, sub_deps,
                    );
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
    anyhow::ensure!(
        !split.hygiene.has_checking_weakening,
        "Soundness hygiene violation in {}: {:?}",
        active_file.display(),
        split.hygiene.disallowed_items()
    );
    // Every verdict, receipt and cache entry carries the resolved full Lean name.
    let resolved_decl = split.shards[shard_idx].decl_name().to_string();
    let target_decl = resolved_decl.as_str();
    let shard = &split.shards[shard_idx];
    let target_violations = target_hygiene_violations(split, shard, allow_sorry);
    if !target_violations.is_empty() {
        anyhow::bail!(
            "Soundness hygiene violation in `{}` ({}): {}",
            target_decl,
            file.display(),
            target_violations.join(", ")
        );
    }
    let shard_has_sorry = shard_text_contains_sorry_or_admit(shard);
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
        let mut hit_json = serde_json::json!({
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
        });
        insert_allow_sorry_fields(&mut hit_json, allow_sorry, false, &[]);
        kernel_prov.insert_json_fields(&mut hit_json);
        hit_json
    };

    if allow_sorry {
        // Under `--allow-sorry`, a clean sibling shard may still hit `TheoremProofCAS`,
        // whereas any modulo-sorry check runs in-process without touching singleflight or CAS.
        // Always route `allow_sorry` through this branch even when `file` itself is lexically
        // `sorry`-free so a transitive `sorryAx` dependency from an imported workspace module
        // is reported as `verified_modulo_sorry` (and never cached in `TheoremProofCAS`).
        if !shard_has_sorry
            && db_warm_on_open
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

        let rooted_target = shard.rooted_name();
        let single_set = HashSet::from([rooted_target.clone()]);
        let full_shard_src = if !shard.shard_source.is_empty() {
            shard.shard_source.clone()
        } else {
            splitter::reconstruct_single_shard_source(&active_src, &rooted_target)?
                .unwrap_or_default()
        };
        let (env_vars, env_cache_hit) = resolve_lake_env(store, canon_dir)?;
        let lean_bin = resolve_lean_bin(canon_dir)?;
        let t0 = &prewarm_local_check_zygote(store, canon_dir, toolchain, t0)?;
        let local_lean_path = resolve_remote_lean_path(canon_dir, Some(&env_vars));
        let mut stub_targets: Vec<String> = single_set.iter().cloned().collect();
        stub_targets.sort();

        let mut verified_via_zygote = false;
        let mut zygote_env_cache_hit = false;
        let mut zygote_import_us = 0u64;
        let mut zygote_elab_us = 0u64;
        let mut heartbeats_used = 0u64;
        let mut proof_term_nodes = 0u64;
        let mut rss_delta_mb = 0i64;
        let mut peak_rss_mb = crate::zygote::measure_process_rss_mb(std::process::id());
        let mut used_constants: Vec<String> = Vec::new();
        let mut used_sorry = shard_has_sorry;
        let mut sorry_decls: Vec<String> = Vec::new();

        let reply = crate::zygote::eval_with_zygote_pool_for_targets_modulo_sorry(
            store,
            toolchain,
            &local_lean_path,
            &env_vars,
            Path::new(&lean_bin),
            &full_shard_src,
            &stub_targets,
            Some(crate::zygote::remaining_timeout_ms(None, *t0)),
            &file_lean_args,
            true,
        )
        .with_context(|| {
            format!(
                "Zygote check failed for `{}` in {} (lines {}..={})",
                target_decl,
                file.display(),
                shard.start_line,
                shard.end_line
            )
        })?;
        let c_abi_sound = unsafe {
            crate::splitter::turbo_spec_is_sound_decl_summary(0, 0, 0, if reply.ok { 0 } else { 1 })
                != 0
        };
        if reply.import_ok && reply.ok && !reply.crashed && !reply.timed_out && c_abi_sound {
            crate::zygote::verify_attested_decl_types(&reply.decl_types, &expected_type_pair)?;
            verified_via_zygote = true;
            zygote_env_cache_hit = reply.env_cache_hit;
            zygote_import_us = reply.import_us;
            zygote_elab_us = reply.elab_us;
            heartbeats_used = reply.heartbeats;
            proof_term_nodes = reply.proof_term_nodes;
            rss_delta_mb = reply.rss_delta_mb;
            peak_rss_mb = peak_rss_mb.max(reply.peak_rss_mb);
            used_constants = reply.used_constants;
            used_sorry |= reply.used_sorry || !reply.sorry_decls.is_empty();
            sorry_decls = reply.sorry_decls;
        } else if reply.crashed || reply.timed_out || reply.import_ok {
            let orig_display = file.display().to_string();
            let raw_err = reply
                .errors
                .join("\n")
                .replace("<zygote-decl>", &orig_display)
                .replace("<zygote-shard>", &orig_display);
            let m_diags = extract_mismatch_diagnostics(&raw_err);
            let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
            let h_fmt = crate::zygote::format_hotspot_diagnostics(
                &reply.timeout_hotspots,
                &reply.simp_hotspots,
            );
            let h_suffix = if h_fmt.is_empty() {
                String::new()
            } else {
                format!("\n{h_fmt}")
            };
            anyhow::bail!(
                "lean check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                target_decl,
                file.display(),
                shard.start_line,
                shard.end_line,
                raw_err,
                m_suffix,
                h_suffix
            );
        }

        if !verified_via_zygote {
            let default_stack = env_vars
                .get("LEAN_STACK_SIZE_KB")
                .cloned()
                .or_else(|| std::env::var("LEAN_STACK_SIZE_KB").ok())
                .unwrap_or_else(|| "262144".to_string());
            let mut fallback_env = env_vars.clone();
            fallback_env.insert("LEAN_STACK_SIZE_KB".to_string(), default_stack);
            let (out, audit_rep) = crate::zygote::run_audited_lean_shard_with_sorry_report(
                store,
                Path::new(&lean_bin),
                &fallback_env,
                Some(canon_dir),
                &full_shard_src,
                &single_set,
                &expected_type_pair,
                &file_lean_args,
                Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                true,
            )
            .with_context(|| {
                format!(
                    "Shard check failed for `{}` in {} (lines {}..={})",
                    target_decl,
                    file.display(),
                    shard.start_line,
                    shard.end_line
                )
            })?;
            if !out.status.success() {
                let orig_display = file.display().to_string();
                let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
                let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                let combined_err = format!("{}\n{}", stdout, stderr);
                let m_diags = extract_mismatch_diagnostics(&combined_err);
                let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                let h_suffix = maybe_append_hotspot_diagnostics_for_source(
                    store,
                    toolchain,
                    &local_lean_path,
                    &fallback_env,
                    Path::new(&lean_bin),
                    &full_shard_src,
                    Some(&orig_display),
                    &file_lean_args,
                    &combined_err,
                );
                anyhow::bail!(
                    "Shard check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                    target_decl,
                    orig_display,
                    shard.start_line,
                    shard.end_line,
                    combined_err,
                    m_suffix,
                    h_suffix
                );
            }
            used_sorry |= audit_rep.used_sorry || !audit_rep.sorry_decls.is_empty();
            sorry_decls = audit_rep.sorry_decls;
        }

        if used_sorry && sorry_decls.is_empty() {
            sorry_decls.push(target_decl.to_string());
        }
        sorry_decls.sort();
        sorry_decls.dedup();

        let dur_ms = t0.elapsed().as_millis() as i64;
        if !used_sorry && !shard_has_sorry && sorry_decls.is_empty() {
            let receipt = make_attested_shard_receipt_bytes(
                target_decl,
                &shard.prefix_env_hash,
                &shard.stmt_hash,
                &shard.proof_hash,
                db::now_unix(),
                Some(&attested.kernel_type_hash),
            )?;
            store.batch_publish_theorem_shards(
                toolchain,
                "trusted",
                &[(
                    shard_key.clone(),
                    target_decl.to_string(),
                    receipt,
                    dur_ms.max(1),
                )],
            )?;
        }

        if proof_term_nodes == 0 {
            proof_term_nodes = crate::matryoshka::estimate_decl_proof_term_nodes(
                target_decl,
                &shard.signature_text,
                &shard.proof_text,
            );
        }
        let stmt_feats =
            crate::matryoshka::parse_lean_stmt_features(target_decl, &shard.signature_text);
        let tactic_skeleton = crate::matryoshka::extract_tactic_skeleton(&shard.proof_text);
        let status_str = if used_sorry {
            "verified_modulo_sorry"
        } else {
            "theorem_verified"
        };
        let compact_summary = if used_sorry {
            format!(
                "MODULO_SORRY decl={} sorry_count={} ms={} hbs={}",
                target_decl,
                sorry_decls.len(),
                dur_ms,
                heartbeats_used
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
        let mut out_json = serde_json::json!({
            "status": status_str,
            "allow_sorry": true,
            "used_sorry": used_sorry,
            "sorry_count": sorry_decls.len(),
            "sorry_decls": sorry_decls,
            "decl": target_decl,
            "shard_key": shard_key,
            "lake_env_cache_hit": env_cache_hit,
            "fast_olean_import": false,
            "zygote_used": verified_via_zygote,
            "zygote_env_cache_hit": zygote_env_cache_hit,
            "zygote_import_us": zygote_import_us,
            "zygote_elab_us": zygote_elab_us,
            "heartbeats_used": heartbeats_used,
            "proof_term_nodes": proof_term_nodes,
            "used_constants": used_constants,
            "stmt_nodes": stmt_feats.stmt_nodes,
            "stmt_depth": stmt_feats.stmt_depth,
            "num_binders": stmt_feats.num_binders,
            "goal_head": stmt_feats.goal_head,
            "stmt_consts": stmt_feats.stmt_consts,
            "tactic_skeleton": tactic_skeleton,
            "rss_delta_mb": rss_delta_mb,
            "peak_rss_mb": peak_rss_mb,
            "accelerator_assisted": false,
            "winning_accelerator": serde_json::Value::Null,
            "fission_cached_subshards": 0,
            "fission_verified_subshards": 0,
            "interface_hash": split.interface_hash,
            "prefix_env_hash": shard.prefix_env_hash,
            "total_shards_in_file": split.shards.len(),
            "compact_summary": compact_summary,
            "estimated_tokens": 18,
            "elapsed_ms": dur_ms
        });
        kernel_prov.insert_json_fields(&mut out_json);
        if emit_stdout {
            if json_output {
                println!("{}", serde_json::to_string_pretty(&out_json)?);
            } else if used_sorry {
                println!(
                    "[turbo-lean] VERIFIED MODULO SORRY `{}` ({} sorry decl(s): [{}], {} ms)",
                    target_decl,
                    sorry_decls.len(),
                    sorry_decls.join(", "),
                    dur_ms
                );
            } else {
                println!(
                    "[turbo-lean] SHARD VERIFIED `{}` ({}/{} shards in file, env_cache_hit={}, fast_olean=false, zygote={}, interface_hash={}.., {} ms)",
                    target_decl,
                    1,
                    split.shards.len(),
                    env_cache_hit,
                    verified_via_zygote,
                    &split.interface_hash[..12],
                    dur_ms
                );
            }
        }
        return Ok(out_json);
    }

    if split.hygiene.is_clean_for_certification() {
        if let Some(remote_url) = remote_http {
            if db_warm_on_open
                && (store.has_attested_decl_receipt(
                    &shard_key,
                    "trusted",
                    target_decl,
                    &attested.kernel_type_hash,
                ) || store.has_attested_decl_receipt(
                    &pack::client_attested_receipt_key(&shard_key),
                    "trusted",
                    target_decl,
                    &attested.kernel_type_hash,
                ))
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
            let rooted_target = shard.rooted_name();
            let single_set = HashSet::from([rooted_target.clone()]);
            let pruned_src = splitter::build_pruned_imports_shard_source(&active_src, &single_set);
            let fast_olean_src = if split.shards.len() <= 1 {
                None
            } else {
                resolve_replayed_prebuilt_module_import(store, canon_dir, &canon_file).and_then(
                    |mod_imp| {
                        splitter::build_fast_olean_shard_source_with_split(
                            &active_src,
                            split,
                            &mod_imp,
                            &single_set,
                        )
                    },
                )
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

            let full_shard_src: String;
            let mut candidates = fast_candidates;
            if candidates.is_empty() {
                full_shard_src = if !shard.shard_source.is_empty() {
                    shard.shard_source.clone()
                } else {
                    splitter::reconstruct_single_shard_source(&active_src, &rooted_target)?
                        .unwrap_or_default()
                };
                candidates.push((full_shard_src.as_str(), false));
            }

            let effective_remote_args =
                crate::module_builder::validate_effective_lean_args(&file_lean_args)?;
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
                    lean_args: effective_remote_args.clone(),
                    targets: vec![rooted_target.clone()],
                    expected_kernel_type_hash: Some(attested.kernel_type_hash.clone()),
                })?;
                match pack::http_request("POST", &endpoint, "application/json", &req_body) {
                    Ok(resp_bytes) => {
                        match serde_json::from_slice::<serde_json::Value>(&resp_bytes) {
                            Ok(rj) => {
                                let st = rj
                                    .get("status")
                                    .and_then(|v| v.as_str())
                                    .unwrap_or("unknown")
                                    .to_string();
                                if st == "remote_theorem_verified"
                                    || st == "remote_theorem_cache_hit"
                                {
                                    let remote_type_ok = rj
                                        .get("kernel_type_hash")
                                        .and_then(|v| v.as_str())
                                        .is_some_and(|h| h == attested.kernel_type_hash)
                                        || rj
                                            .get("decl_types")
                                            .and_then(|v| {
                                                serde_json::from_value::<
                                                    std::collections::BTreeMap<String, String>,
                                                >(
                                                    v.clone()
                                                )
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
                            Err(e) => {
                                last_err = Some(anyhow::anyhow!(
                                    "Remote shard check on {endpoint} returned invalid JSON: {e}"
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
                    splitter::reconstruct_single_shard_source(&active_src, &rooted_target)?
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
                    lean_args: effective_remote_args,
                    targets: vec![rooted_target],
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
                                    crate::zygote::verify_attested_decl_types(
                                        &m,
                                        &expected_type_pair,
                                    )
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
                return Err(err);
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

            let (_, out_json) = emit_remote_decl_result(
                json_output,
                emit_stdout,
                kernel_prov,
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
    }

    if split.hygiene.is_clean_for_certification()
        && db_warm_on_open
        && store.has_attested_decl_receipt(
            &pack::client_attested_receipt_key(&shard_key),
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

    let t0 = &prewarm_local_check_zygote(store, canon_dir, toolchain, t0)?;
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
            let rooted_target = shard.rooted_name();
            let single_set = HashSet::from([rooted_target.clone()]);

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
            let prebuilt_mod =
                resolve_replayed_prebuilt_module_import(store, canon_dir, &canon_file);
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
                    (fast_ev, db_warm_on_open, resolve_lean_bin(canon_dir)?, lp)
                } else {
                    let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                    let lb = resolve_lean_bin(canon_dir)?;
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
                let cached_subs: HashMap<String, String> = store
                    .batch_get_theorem_shards_readonly(&fission_keys, "trusted")
                    .unwrap_or_default()
                    .into_iter()
                    .filter(|(_, bh)| subshard_receipt_provenance_ok(store, bh))
                    .collect();
                let fission_cold_enabled = std::env::var("TURBO_LEAN_FISSION_COLD").as_deref()
                    == Ok("1")
                    || crate::shm_cache::MemoryBudgetGovernor::detect().is_low_memory_mode();
                if !cached_subs.is_empty() || fission_cold_enabled {
                    if env_vars.len() <= 1 {
                        let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                        lean_bin = resolve_lean_bin(canon_dir)?;
                        env_vars = ev;
                        env_cache_hit = ech;
                    }
                    let full_shard_src = if !shard.shard_source.is_empty() {
                        shard.shard_source.clone()
                    } else {
                        splitter::reconstruct_single_shard_source(&active_src, &rooted_target)?
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
                        format!("{} := sorry", shard.signature_text.trim_end())
                    } else {
                        format!(
                            "{} := sorry\n{}",
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
                                        "scanner_version": crate::zygote::ZYGOTE_SCANNER_VERSION,
                                        "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION,
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
                    targets: vec![rooted_target.clone()],
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
                                last_daemon_verify_err = Some(e.to_string());
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
                            last_daemon_verify_err = Some(e.to_string());
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

            if !verified_via_zygote && fast_olean_src.is_none() {
                if let Some(outline_plan) = splitter::build_prefix_outline_plan_with_split(
                    &active_src,
                    split,
                    &rooted_target,
                ) {
                    if env_vars.len() <= 1 {
                        let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                        lean_bin = resolve_lean_bin(canon_dir)?;
                        env_vars = ev;
                        env_cache_hit = ech;
                    }
                    let orig_display = file.display().to_string();
                    if let Ok((outline_dir, outline_mod)) =
                        crate::zygote::ensure_prefix_outline_olean(
                            store,
                            toolchain,
                            &local_lean_path,
                            &env_vars,
                            Path::new(&lean_bin),
                            &outline_plan.outline_source,
                            &orig_display,
                            &file_lean_args,
                        )
                    {
                        let delta_lp = if local_lean_path.is_empty() {
                            outline_dir.to_string_lossy().into_owned()
                        } else {
                            format!("{}:{}", outline_dir.display(), local_lean_path)
                        };
                        let delta_src = outline_plan.render_delta_shard_source(&outline_mod);
                        let mut delta_ev = env_vars.clone();
                        delta_ev.insert("LEAN_PATH".to_string(), delta_lp.clone());
                        let mut stub_targets: Vec<String> = single_set.iter().cloned().collect();
                        stub_targets.sort();
                        if let Ok(reply) =
                            crate::zygote::eval_with_zygote_pool_for_targets_and_stubs(
                                store,
                                toolchain,
                                &delta_lp,
                                &delta_ev,
                                Path::new(&lean_bin),
                                &delta_src,
                                &stub_targets,
                                &outline_plan.outline_stubs,
                                Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                                &file_lean_args,
                            )
                        {
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
                                && !reply.crashed
                                && !reply.timed_out
                                && c_abi_sound
                                && crate::zygote::verify_attested_decl_types(
                                    &reply.decl_types,
                                    &expected_type_pair,
                                )
                                .is_ok()
                            {
                                verified_via_fast_olean = true;
                                apply_zygote_reply!(reply);
                            }
                        }
                    }
                }
            }

            if !verified_via_zygote && env_vars.is_empty() && fast_local_zygote_url.is_none() {
                let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                lean_bin = resolve_lean_bin(canon_dir)?;
                env_vars = ev;
                env_cache_hit = ech;
            }

            if !verified_via_zygote && !verified_via_fast_olean {
                let full_shard_src = if !shard.shard_source.is_empty() {
                    shard.shard_source.clone()
                } else {
                    splitter::reconstruct_single_shard_source(&active_src, &rooted_target)?
                        .unwrap_or_default()
                };
                if !verified_via_zygote {
                    if let Some(zjson) = try_zygote_src(&full_shard_src, &env_vars, true) {
                        apply_zygote_json!(&zjson);
                    }
                }
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
                                    lean_bin = resolve_lean_bin(canon_dir)?;
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
                        let h_suffix = maybe_append_hotspot_diagnostics_for_source(
                            store,
                            toolchain,
                            &local_lean_path,
                            &env_vars,
                            Path::new(&lean_bin),
                            &full_shard_src,
                            Some(&orig_display),
                            &file_lean_args,
                            &raw_err,
                        );
                        anyhow::bail!(
                            "lean check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                            target_decl,
                            file.display(),
                            shard.start_line,
                            shard.end_line,
                            raw_err,
                            m_suffix,
                            h_suffix
                        );
                    }
                    if env_vars.len() <= 1 {
                        let (ev, ech) = resolve_lake_env(store, canon_dir)?;
                        lean_bin = resolve_lean_bin(canon_dir)?;
                        env_vars = ev;
                        env_cache_hit = ech;
                    }
                    let mut stub_targets: Vec<String> = single_set.iter().cloned().collect();
                    stub_targets.sort();
                    let reply = crate::zygote::eval_with_zygote_pool_for_targets(
                        store,
                        toolchain,
                        &local_lean_path,
                        &env_vars,
                        Path::new(&lean_bin),
                        &full_shard_src,
                        &stub_targets,
                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                        &file_lean_args,
                    )
                    .with_context(|| {
                        format!(
                            "Zygote check failed for `{}` in {} (lines {}..={})",
                            target_decl,
                            file.display(),
                            shard.start_line,
                            shard.end_line
                        )
                    })?;
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
                        && !reply.crashed
                        && !reply.timed_out
                        && c_abi_sound
                    {
                        crate::zygote::verify_attested_decl_types(
                            &reply.decl_types,
                            &expected_type_pair,
                        )?;
                        apply_zygote_reply!(reply);
                    } else if reply.crashed || reply.timed_out || reply.import_ok {
                        let orig_display = file.display().to_string();
                        let raw_err = reply
                            .errors
                            .join("\n")
                            .replace("<zygote-decl>", &orig_display)
                            .replace("<zygote-shard>", &orig_display);
                        let m_diags = extract_mismatch_diagnostics(&raw_err);
                        let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                        let h_fmt = crate::zygote::format_hotspot_diagnostics(
                            &reply.timeout_hotspots,
                            &reply.simp_hotspots,
                        );
                        let h_suffix = if h_fmt.is_empty() {
                            String::new()
                        } else {
                            format!("\n{h_fmt}")
                        };
                        anyhow::bail!(
                            "lean check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                            target_decl,
                            file.display(),
                            shard.start_line,
                            shard.end_line,
                            raw_err,
                            m_suffix,
                            h_suffix
                        );
                    }
                }
                if !verified_via_zygote {
                    let default_stack = env_vars
                        .get("LEAN_STACK_SIZE_KB")
                        .cloned()
                        .or_else(|| std::env::var("LEAN_STACK_SIZE_KB").ok())
                        .unwrap_or_else(|| "262144".to_string());
                    let mut fallback_env = env_vars.clone();
                    fallback_env.insert("LEAN_STACK_SIZE_KB".to_string(), default_stack);
                    let out = crate::zygote::run_audited_lean_shard_with_types(
                        store,
                        Path::new(&lean_bin),
                        &fallback_env,
                        Some(canon_dir),
                        &full_shard_src,
                        &single_set,
                        &expected_type_pair,
                        &file_lean_args,
                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                    )
                    .with_context(|| {
                        format!(
                            "Shard check failed for `{}` in {} (lines {}..={})",
                            target_decl,
                            file.display(),
                            shard.start_line,
                            shard.end_line
                        )
                    })?;

                    if !out.status.success() {
                        let orig_display = file.display().to_string();
                        let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
                        let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                        let combined_err = format!("{}\n{}", stdout, stderr);
                        let m_diags = extract_mismatch_diagnostics(&combined_err);
                        let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                        let h_suffix = maybe_append_hotspot_diagnostics_for_source(
                            store,
                            toolchain,
                            &local_lean_path,
                            &fallback_env,
                            Path::new(&lean_bin),
                            &full_shard_src,
                            Some(&orig_display),
                            &file_lean_args,
                            &combined_err,
                        );
                        anyhow::bail!(
                            "Shard check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                            target_decl,
                            orig_display,
                            shard.start_line,
                            shard.end_line,
                            combined_err,
                            m_suffix,
                            h_suffix
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
            insert_allow_sorry_fields(&mut out_json, allow_sorry, false, &[]);
            kernel_prov.insert_json_fields(&mut out_json);
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
                        "scanner_version": crate::zygote::ZYGOTE_SCANNER_VERSION,
                        "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION,
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
