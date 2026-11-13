use anyhow::{Context, Result};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;
use std::time::Instant;

use crate::db::{self, SingleflightOutcome, TurboStore};
use crate::lake_build::{
    compute_imported_olean_interface_hashes, compute_shard_key_with_args,
    is_file_hash_verified_in_lake_build, is_file_verified_in_lake_build, resolve_lake_env,
    resolve_lean_bin, resolve_remote_lean_path, resolve_replayed_prebuilt_module_import,
};
use crate::pack;
use crate::splitter::{self, split_lean_source};

use super::diagnostics::{
    extract_mismatch_diagnostics, format_mismatch_diagnostics_summary, insert_allow_sorry_fields,
};
use super::identity::{confirm_file_decl_identities_with_budget, prewarm_local_check_zygote};
use super::single_decl::{
    maybe_append_hotspot_diagnostics_for_source, shard_text_contains_sorry_or_admit,
};
use super::{default_parallel_jobs, make_attested_shard_receipt_bytes};

#[allow(clippy::too_many_arguments)]
pub(super) fn check_single_file(
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
    src: &mut String,
    cached_file_blake3: Option<&str>,
    split: &splitter::SplitResult,
    _single_split_hits: usize,
    jobs: Option<usize>,
    _parallel_shards: bool,
    remote_http: Option<&str>,
    allow_sorry: bool,
) -> Result<serde_json::Value> {
    let cache_start = Instant::now();
    let file_lean_args = crate::module_builder::try_resolve_lean_args_for_path(
        canon_dir,
        Some(canon_resolved_initial),
    )?;
    let file_shard_keys: Vec<String> = split
        .shards
        .iter()
        .map(|shard| compute_shard_key_with_args(toolchain, shard, &file_lean_args))
        .collect();
    let client_attested_keys: Vec<String> = file_shard_keys
        .iter()
        .map(|k| pack::client_attested_receipt_key(k))
        .collect();
    let cached_map = if db_warm_on_open {
        let mut lookup_keys = Vec::with_capacity(file_shard_keys.len() * 2);
        lookup_keys.extend(file_shard_keys.iter().cloned());
        lookup_keys.extend(client_attested_keys.iter().cloned());
        store.batch_get_theorem_shards(&lookup_keys, "trusted")?
    } else {
        HashMap::new()
    };
    super::record_phase("cache", cache_start);

    let mut hits = 0usize;
    let mut uncached_shards = Vec::new();
    let mut attested_kths: HashMap<String, String> = HashMap::new();
    let hygiene_deferrable = split.hygiene.is_clean_or_deferred_to_kernel_gate();
    let hygiene_ok_for_split = if allow_sorry {
        split.hygiene.is_clean_modulo_sorry() || hygiene_deferrable
    } else {
        hygiene_deferrable
    };
    if split.eligible_for_sharding && hygiene_ok_for_split && !split.shards.is_empty() {
        if src.is_empty() {
            *src = fs::read_to_string(resolved_file)
                .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
        }
        let shard_refs: Vec<&splitter::TheoremShard> = split.shards.iter().collect();
        let identity_start = Instant::now();
        let attested = confirm_file_decl_identities_with_budget(
            src,
            &shard_refs,
            canon_dir,
            resolved_file,
            false,
            Some(*t0),
        )?;
        super::record_phase("identity", identity_start);
        for (idx, att) in attested.into_iter().enumerate() {
            attested_kths.insert(file_shard_keys[idx].clone(), att.kernel_type_hash);
        }
    }
    let hygiene_strictly_clean = split.hygiene.is_clean_for_certification();
    for (idx, shard) in split.shards.iter().enumerate() {
        let shard_key = file_shard_keys[idx].clone();
        let client_att_key = &client_attested_keys[idx];
        let raw_present = cached_map.contains_key(&shard_key);
        let client_att_present = cached_map.contains_key(client_att_key);
        let hygiene_ok_for_hit = if allow_sorry {
            hygiene_strictly_clean
                || (split.hygiene.is_clean_modulo_sorry()
                    && !shard_text_contains_sorry_or_admit(shard))
        } else {
            hygiene_strictly_clean
        };
        let kth_opt = attested_kths.get(&shard_key);
        let raw_attested = hygiene_ok_for_hit
            && raw_present
            && kth_opt.is_some_and(|kth| {
                store.has_attested_decl_receipt(&shard_key, "trusted", shard.decl_name(), kth)
            });
        let client_attested = hygiene_strictly_clean
            && !allow_sorry
            && client_att_present
            && kth_opt.is_some_and(|kth| {
                store.has_attested_decl_receipt(client_att_key, "trusted", shard.decl_name(), kth)
            });
        if raw_present && !raw_attested {
            store.invalidate_action_for_reattestation(&shard_key)?;
        }
        if !allow_sorry && client_att_present && !client_attested {
            store.invalidate_action_for_reattestation(client_att_key)?;
        }
        if raw_attested || client_attested {
            hits += 1;
        } else {
            uncached_shards.push((shard_key, shard));
        }
    }
    let misses = uncached_shards.len();

    if allow_sorry && (split.hygiene.is_clean_modulo_sorry() || !hygiene_deferrable) {
        if !split.hygiene.is_clean_modulo_sorry() {
            let items = split.hygiene.disallowed_items_modulo_sorry();
            anyhow::bail!(
                "Soundness hygiene violation in {}: {}",
                file.display(),
                if items.is_empty() {
                    "file contains forbidden axioms or checking-weakening options".to_string()
                } else {
                    items.join(", ")
                }
            );
        }
        if misses == 0 && split.hygiene.is_clean_for_certification() && !split.shards.is_empty() {
            let elapsed_ms = t0.elapsed().as_millis() as i64;
            let mut out_json = serde_json::json!({
                "status": "all_shards_cached",
                "allow_sorry": true,
                "used_sorry": false,
                "sorry_count": 0,
                "sorry_decls": [],
                "file": file.display().to_string(),
                "shard_hits": hits,
                "shard_misses": 0,
                "interface_hash": split.interface_hash,
                "elapsed_ms": elapsed_ms
            });
            kernel_prov.insert_json_fields(&mut out_json);
            super::insert_check_timings(&mut out_json, *t0);
            if emit_stdout {
                if json_output {
                    println!("{}", serde_json::to_string_pretty(&out_json)?);
                } else {
                    println!(
                        "[turbo-lean] ALL {} THEOREM SHARDS CACHED in {} (interface_hash={}.., {} ms)",
                        hits,
                        file.display(),
                        &split.interface_hash[..12],
                        elapsed_ms
                    );
                }
            }
            return Ok(out_json);
        }
        if src.is_empty() {
            *src = fs::read_to_string(resolved_file)
                .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
        }
        let (env_vars, env_cache_hit) = resolve_lake_env(store, canon_dir)?;
        let lean_bin = resolve_lean_bin(canon_dir)?;
        let t0 = &prewarm_local_check_zygote(store, canon_dir, toolchain, t0)?;
        let local_lean_path = resolve_remote_lean_path(canon_dir, Some(&env_vars));
        let orig_display = file.display().to_string();
        let mut file_used_sorry = split.hygiene.has_sorry;
        let mut file_sorry_decls: Vec<String> = Vec::new();
        let mut clean_batch_items: Vec<(String, String, Vec<u8>, i64)> = Vec::new();

        if split.eligible_for_sharding && !split.shards.is_empty() {
            let now = db::now_unix();
            for (shard_key, shard) in &uncached_shards {
                let shard_has_sorry = shard_text_contains_sorry_or_admit(shard);
                let rooted_target = shard.rooted_name();
                let single_set = HashSet::from([rooted_target.clone()]);
                let shard_src_owned = if shard.shard_source.is_empty() {
                    splitter::build_coalesced_shard_source(src, &single_set)
                } else {
                    shard.shard_source.clone()
                };
                let expected_pair: Vec<(String, String)> = attested_kths
                    .get(shard_key)
                    .map(|k| vec![(shard.decl_name().to_string(), k.clone())])
                    .unwrap_or_default();
                let shard_t0 = Instant::now();
                let targets_vec = vec![rooted_target.clone()];

                if !shard_has_sorry {
                    // Try strict verification first so clean sibling shards with `0 sorryAx`
                    // in their kernel closure can be certified and cached in `TheoremProofCAS`.
                    let strict_reply = crate::zygote::eval_with_zygote_pool_for_targets(
                        store,
                        toolchain,
                        &local_lean_path,
                        &env_vars,
                        Path::new(&lean_bin),
                        &shard_src_owned,
                        &targets_vec,
                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                        &file_lean_args,
                    )?;
                    let c_abi_sound = unsafe {
                        crate::splitter::turbo_spec_is_sound_decl_summary(
                            0,
                            0,
                            0,
                            if strict_reply.ok { 0 } else { 1 },
                        ) != 0
                    };
                    if strict_reply.import_ok
                        && strict_reply.ok
                        && !strict_reply.crashed
                        && !strict_reply.timed_out
                        && c_abi_sound
                    {
                        if !expected_pair.is_empty() {
                            crate::zygote::verify_attested_decl_types(
                                &strict_reply.decl_types,
                                &expected_pair,
                            )?;
                        }
                        let shard_dur_ms = (shard_t0.elapsed().as_millis() as i64).max(1);
                        let receipt = make_attested_shard_receipt_bytes(
                            shard.decl_name(),
                            &shard.prefix_env_hash,
                            &shard.stmt_hash,
                            &shard.proof_hash,
                            now,
                            attested_kths.get(shard_key).map(String::as_str),
                        )?;
                        clean_batch_items.push((
                            shard_key.clone(),
                            shard.decl_name().to_string(),
                            receipt,
                            shard_dur_ms,
                        ));
                        continue;
                    }
                }

                // Modulo-sorry check for sorry-bearing shards or clean-text shards that depend
                // on an upstream `sorry`-bearing helper definition. Never cached in CAS!
                let mut shard_verified_modulo = false;
                let mod_reply = crate::zygote::eval_with_zygote_pool_for_targets_modulo_sorry(
                    store,
                    toolchain,
                    &local_lean_path,
                    &env_vars,
                    Path::new(&lean_bin),
                    &shard_src_owned,
                    &targets_vec,
                    Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                    &file_lean_args,
                    true,
                )?;
                let c_abi_sound = unsafe {
                    crate::splitter::turbo_spec_is_sound_decl_summary(
                        0,
                        0,
                        0,
                        if mod_reply.ok { 0 } else { 1 },
                    ) != 0
                };
                if mod_reply.import_ok
                    && mod_reply.ok
                    && !mod_reply.crashed
                    && !mod_reply.timed_out
                    && c_abi_sound
                {
                    if !expected_pair.is_empty() {
                        crate::zygote::verify_attested_decl_types(
                            &mod_reply.decl_types,
                            &expected_pair,
                        )?;
                    }
                    shard_verified_modulo = true;
                    let this_used_sorry = shard_has_sorry
                        || mod_reply.used_sorry
                        || !mod_reply.sorry_decls.is_empty();
                    file_used_sorry |= this_used_sorry;
                    for sd in mod_reply.sorry_decls {
                        if !file_sorry_decls.contains(&sd) {
                            file_sorry_decls.push(sd);
                        }
                    }
                    if this_used_sorry && !file_sorry_decls.iter().any(|d| d == shard.decl_name()) {
                        file_sorry_decls.push(shard.decl_name().to_string());
                    }
                } else if mod_reply.crashed || mod_reply.timed_out || mod_reply.import_ok {
                    let raw_err = mod_reply
                        .errors
                        .join("\n")
                        .replace("<zygote-decl>", &orig_display)
                        .replace("<zygote-shard>", &orig_display);
                    let m_diags = extract_mismatch_diagnostics(&raw_err);
                    let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                    let h_fmt = crate::zygote::format_hotspot_diagnostics(
                        &mod_reply.timeout_hotspots,
                        &mod_reply.simp_hotspots,
                    );
                    let h_suffix = if h_fmt.is_empty() {
                        String::new()
                    } else {
                        format!("\n{h_fmt}")
                    };
                    anyhow::bail!(
                        "Check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                        shard.decl_name(),
                        orig_display,
                        shard.start_line,
                        shard.end_line,
                        raw_err,
                        m_suffix,
                        h_suffix
                    );
                }

                if !shard_verified_modulo {
                    let (out, audit_rep) = crate::zygote::run_audited_lean_shard_with_sorry_report(
                        store,
                        Path::new(&lean_bin),
                        &env_vars,
                        Some(canon_dir),
                        &shard_src_owned,
                        &single_set,
                        &expected_pair,
                        &file_lean_args,
                        Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                        true,
                    )?;
                    if !out.status.success() {
                        let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
                        let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                        let combined_err = format!("{}\n{}", stdout, stderr);
                        let m_diags = extract_mismatch_diagnostics(&combined_err);
                        let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                        let h_suffix = maybe_append_hotspot_diagnostics_for_source(
                            store,
                            toolchain,
                            &local_lean_path,
                            &env_vars,
                            Path::new(&lean_bin),
                            &shard_src_owned,
                            Some(&orig_display),
                            &file_lean_args,
                            &combined_err,
                        );
                        anyhow::bail!(
                            "Check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                            shard.decl_name(),
                            orig_display,
                            shard.start_line,
                            shard.end_line,
                            combined_err,
                            m_suffix,
                            h_suffix
                        );
                    }
                    if !shard_has_sorry && !audit_rep.used_sorry && audit_rep.sorry_decls.is_empty()
                    {
                        let shard_dur_ms = (shard_t0.elapsed().as_millis() as i64).max(1);
                        let receipt = make_attested_shard_receipt_bytes(
                            shard.decl_name(),
                            &shard.prefix_env_hash,
                            &shard.stmt_hash,
                            &shard.proof_hash,
                            now,
                            attested_kths.get(shard_key).map(String::as_str),
                        )?;
                        clean_batch_items.push((
                            shard_key.clone(),
                            shard.decl_name().to_string(),
                            receipt,
                            shard_dur_ms,
                        ));
                    } else {
                        file_used_sorry = true;
                        for sd in audit_rep.sorry_decls {
                            if !file_sorry_decls.contains(&sd) {
                                file_sorry_decls.push(sd);
                            }
                        }
                        if !file_sorry_decls.iter().any(|d| d == shard.decl_name()) {
                            file_sorry_decls.push(shard.decl_name().to_string());
                        }
                    }
                }
            }

            if !clean_batch_items.is_empty() {
                store.batch_publish_theorem_shards(toolchain, "trusted", &clean_batch_items)?;
            }
            file_sorry_decls.sort();
            file_sorry_decls.dedup();
            let dur_ms = t0.elapsed().as_millis() as i64;
            let status_str = if file_used_sorry {
                "verified_modulo_sorry"
            } else {
                "file_verified"
            };
            let mut out_json = serde_json::json!({
                "status": status_str,
                "allow_sorry": true,
                "used_sorry": file_used_sorry,
                "sorry_count": file_sorry_decls.len(),
                "sorry_decls": file_sorry_decls,
                "mode": "modulo_sorry_shards",
                "file": file.display().to_string(),
                "shard_hits": hits,
                "shard_misses": misses,
                "clean_shards_cached": clean_batch_items.len(),
                "lake_env_cache_hit": env_cache_hit,
                "interface_hash": split.interface_hash,
                "elapsed_ms": dur_ms
            });
            kernel_prov.insert_json_fields(&mut out_json);
            super::insert_check_timings(&mut out_json, *t0);
            if emit_stdout {
                if json_output {
                    println!("{}", serde_json::to_string_pretty(&out_json)?);
                } else if file_used_sorry {
                    println!(
                        "[turbo-lean] VERIFIED MODULO SORRY {} ({} sorry decl(s): [{}], {} clean hits, {} clean misses cached, interface_hash={}.., {} ms)",
                        file.display(),
                        file_sorry_decls.len(),
                        file_sorry_decls.join(", "),
                        hits,
                        clean_batch_items.len(),
                        &split.interface_hash[..12],
                        dur_ms
                    );
                } else {
                    println!(
                        "[turbo-lean] VERIFIED {} ({} hits, {} misses cached, interface_hash={}.., {} ms)",
                        file.display(),
                        hits,
                        clean_batch_items.len(),
                        &split.interface_hash[..12],
                        dur_ms
                    );
                }
            }
            return Ok(out_json);
        }

        // Whole-file modulo-sorry path when the file is not eligible for per-theorem sharding:
        // never publish any shard or file receipt to `TheoremProofCAS`.
        let mut zygote_env = env_vars.clone();
        zygote_env
            .entry("TURBO_LEAN_CALLER_CWD".to_string())
            .or_insert_with(|| canon_dir.to_string_lossy().to_string());
        let can_audit_in_zygote = !src.contains("IO.Process.exit")
            && !src.lines().take(20).any(|l| {
                let t = l.split("--").next().unwrap_or(l).trim();
                t == "module" || t.starts_with("module ")
            });
        let mut whole_verified = false;
        let mut eval_stdout_text = String::new();
        let mut eval_messages: Vec<String> = Vec::new();
        if can_audit_in_zygote {
            let rep = crate::zygote::eval_with_zygote_pool_audit_all_modulo_sorry(
                store,
                toolchain,
                &local_lean_path,
                &zygote_env,
                Path::new(&lean_bin),
                src,
                Some(&canon_resolved_initial.to_string_lossy()),
                Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                &file_lean_args,
                true,
            )?;
            if rep.import_ok && rep.ok && !rep.crashed && !rep.timed_out {
                whole_verified = true;
                eval_stdout_text = rep.stdout;
                eval_messages = rep.messages;
                file_used_sorry |= rep.used_sorry || !rep.sorry_decls.is_empty();
                for sd in rep.sorry_decls {
                    if !file_sorry_decls.contains(&sd) {
                        file_sorry_decls.push(sd);
                    }
                }
            } else if rep.crashed || rep.timed_out || rep.import_ok {
                let raw_err = rep
                    .errors
                    .join("\n")
                    .replace("<zygote-decl>", &orig_display)
                    .replace("<zygote-shard>", &orig_display);
                let m_diags = extract_mismatch_diagnostics(&raw_err);
                let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                let h_fmt = crate::zygote::format_hotspot_diagnostics(
                    &rep.timeout_hotspots,
                    &rep.simp_hotspots,
                );
                let h_suffix = if h_fmt.is_empty() {
                    String::new()
                } else {
                    format!("\n{h_fmt}")
                };
                anyhow::bail!(
                    "lean check failed for {orig_display}:\n{raw_err}{m_suffix}{h_suffix}"
                );
            }
        }
        if !whole_verified {
            let names: HashSet<String> = split.shards.iter().map(|s| s.rooted_name()).collect();
            let (out, audit_rep) = crate::zygote::run_audited_lean_shard_at_with_full_report(
                &store.root,
                &store.fast_staging_dir(),
                Path::new(&lean_bin),
                &env_vars,
                Some(canon_dir),
                Some(canon_resolved_initial),
                src,
                &names,
                false,
                true,
                &[],
                &file_lean_args,
                Some(crate::zygote::remaining_timeout_ms(None, *t0)),
            )
            .with_context(|| format!("Check failed for {}", file.display()))?;
            if !out.status.success() {
                let stderr = String::from_utf8_lossy(&out.stderr);
                let stdout = String::from_utf8_lossy(&out.stdout);
                let combined_err = format!("{}\n{}", stdout, stderr);
                let h_suffix = maybe_append_hotspot_diagnostics_for_source(
                    store,
                    toolchain,
                    &local_lean_path,
                    &env_vars,
                    Path::new(&lean_bin),
                    src,
                    Some(&orig_display),
                    &file_lean_args,
                    &combined_err,
                );
                anyhow::bail!(
                    "Check failed for {}:\n{}{}",
                    file.display(),
                    combined_err,
                    h_suffix
                );
            }
            eval_stdout_text = String::from_utf8_lossy(&out.stdout).to_string();
            file_used_sorry |= audit_rep.used_sorry || !audit_rep.sorry_decls.is_empty();
            file_sorry_decls = audit_rep.sorry_decls;
        }
        file_sorry_decls.sort();
        file_sorry_decls.dedup();
        let dur_ms = t0.elapsed().as_millis() as i64;
        let status_str = if file_used_sorry {
            "verified_modulo_sorry"
        } else {
            "file_verified"
        };
        let mut out_json = serde_json::json!({
            "status": status_str,
            "allow_sorry": true,
            "used_sorry": file_used_sorry,
            "sorry_count": file_sorry_decls.len(),
            "sorry_decls": file_sorry_decls,
            "mode": "whole_file_modulo_sorry",
            "file": file.display().to_string(),
            "shard_hits": hits,
            "shard_misses": misses,
            "lake_env_cache_hit": env_cache_hit,
            "interface_hash": split.interface_hash,
            "stdout": eval_stdout_text,
            "messages": eval_messages,
            "elapsed_ms": dur_ms
        });
        kernel_prov.insert_json_fields(&mut out_json);
        super::insert_check_timings(&mut out_json, *t0);
        if emit_stdout {
            if json_output {
                println!("{}", serde_json::to_string_pretty(&out_json)?);
            } else if file_used_sorry {
                println!(
                    "[turbo-lean] VERIFIED MODULO SORRY {} ({} sorry decl(s): [{}], interface_hash={}.., {} ms)",
                    file.display(),
                    file_sorry_decls.len(),
                    file_sorry_decls.join(", "),
                    &split.interface_hash[..12],
                    dur_ms
                );
            } else {
                println!(
                    "[turbo-lean] VERIFIED {} (interface_hash={}.., {} ms)",
                    file.display(),
                    &split.interface_hash[..12],
                    dur_ms
                );
            }
        }
        return Ok(out_json);
    }

    if !hygiene_deferrable {
        if !crate::zygote::daemon_disabled() {
            if src.is_empty() {
                *src = fs::read_to_string(resolved_file).unwrap_or_default();
            }
            let (imports_csv, _) = crate::zygote::split_shard_for_zygote(src);
            if !imports_csv.is_empty() && imports_csv != "Init" && imports_csv != "__PRELUDE__" {
                let existing_daemon = crate::zygote::has_active_local_zygote_daemon(store);
                if !existing_daemon {
                    if let Ok((ev, _)) = resolve_lake_env(store, canon_dir) {
                        let lb = resolve_lean_bin(canon_dir)?;
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

    if hygiene_strictly_clean
        && misses == 0
        && !split.shards.is_empty()
        && split.eligible_for_sharding
    {
        let elapsed_ms = t0.elapsed().as_millis();
        let mut out_json = serde_json::json!({
            "status": "all_shards_cached",
            "file": file.display().to_string(),
            "shard_hits": hits,
            "shard_misses": 0,
            "interface_hash": split.interface_hash,
            "elapsed_ms": elapsed_ms
        });
        insert_allow_sorry_fields(&mut out_json, allow_sorry, false, &[]);
        kernel_prov.insert_json_fields(&mut out_json);
        super::insert_check_timings(&mut out_json, *t0);
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

    if hygiene_strictly_clean && split.eligible_for_sharding && !uncached_shards.is_empty() {
        if let Some(remote_url) = remote_http {
            if src.is_empty() {
                *src = fs::read_to_string(resolved_file)
                    .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
            }
            let effective_jobs = requested_jobs.min(uncached_shards.len());
            let uncached_names: HashSet<String> = uncached_shards
                .iter()
                .map(|(_, s)| s.rooted_name())
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
                    decl_name: s.rooted_name(),
                    prefix_env_hash: s.prefix_env_hash.clone(),
                    stmt_hash: s.stmt_hash.clone(),
                    proof_hash: s.proof_hash.clone(),
                    expected_kernel_type_hash: attested_kths.get(k).cloned(),
                })
                .collect();

            let mut remote_resp = if split.shards.len() <= 1 {
                None
            } else {
                resolve_replayed_prebuilt_module_import(store, canon_dir, canon_resolved_initial)
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
                        r.error.unwrap_or(r.stderr)
                    );
                }
                remote_resp = Some(r);
            }

            let resp = remote_resp.unwrap();
            let dur_ms = t0.elapsed().as_millis() as i64;
            let mut out_json = serde_json::json!({
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
            kernel_prov.insert_json_fields(&mut out_json);
            super::insert_check_timings(&mut out_json, *t0);
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

    let t0 = &prewarm_local_check_zygote(store, canon_dir, toolchain, t0)?;
    let use_parallel_shards =
        hygiene_strictly_clean && split.eligible_for_sharding && !uncached_shards.is_empty();

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
        resolve_replayed_prebuilt_module_import(store, canon_dir, canon_resolved_initial);
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
            (fast_ev, db_warm_on_open, resolve_lean_bin(canon_dir)?, lp)
        } else {
            let (ev, ech) = resolve_lake_env(store, canon_dir)?;
            let lb = resolve_lean_bin(canon_dir)?;
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
            .map(|(_, s)| s.rooted_name())
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
                crate::zygote::audit_compiled_shard_module_with_zygote(
                    store,
                    &cfg,
                    mod_imp,
                    &lp,
                    &[],
                    &[],
                    &uncached_names,
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
            targets: uncached_names.iter().cloned().collect(),
            expected_kernel_type_hash: None,
        };

        for cand_src in [pruned_batch_src.as_deref(), fast_batch_src.as_deref()]
            .into_iter()
            .flatten()
        {
            if !batch_succeeded {
                if let Ok(Some(reply)) = pack::try_local_zygote_check_shard_detailed(
                    store,
                    &env_vars,
                    &make_batch_zreq(cand_src),
                ) {
                    if let Some(dt) = reply.get("decl_types").and_then(|v| v.as_object()) {
                        let pairs: std::collections::BTreeMap<String, String> = dt
                            .iter()
                            .filter_map(|(k, v)| Some((k.clone(), v.as_str()?.to_string())))
                            .collect();
                        if crate::zygote::verify_attested_decl_types(&pairs, &expected_batch_types)
                            .is_ok()
                        {
                            batch_succeeded = true;
                        }
                    }
                }
            }
        }

        let mut coalesced_zygote_err: Option<String> = None;
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
                    coalesced_zygote_err = Some(e.to_string());
                }
            }
        }

        if !batch_succeeded {
            if let Some(daemon_err) = coalesced_zygote_err {
                let orig_display = file.display().to_string();
                let raw_err = daemon_err
                    .replace("<zygote-decl>", &orig_display)
                    .replace("<zygote-shard>", &orig_display);
                let m_diags = extract_mismatch_diagnostics(&raw_err);
                let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                let coalesced_src_for_diag =
                    splitter::build_coalesced_shard_source(src, &uncached_names);
                let h_suffix = maybe_append_hotspot_diagnostics_for_source(
                    store,
                    toolchain,
                    &local_lean_path,
                    &env_vars,
                    Path::new(&lean_bin),
                    &coalesced_src_for_diag,
                    Some(&orig_display),
                    &file_lean_args,
                    &raw_err,
                );
                if uncached_shards.len() == 1 {
                    let (_, shard) = uncached_shards[0];
                    anyhow::bail!(
                        "Check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                        shard.name,
                        orig_display,
                        shard.start_line,
                        shard.end_line,
                        raw_err,
                        m_suffix,
                        h_suffix
                    );
                }
                anyhow::bail!(
                    "Check failed for {}:\n{}{}{}",
                    orig_display,
                    raw_err,
                    m_suffix,
                    h_suffix
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
            #[allow(clippy::type_complexity)]
            let worker_results: Vec<
                Result<Vec<(String, &splitter::TheoremShard, i64)>>,
            > = std::thread::scope(|s| {
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

                    let phases = super::phase_context();
                    handles.push(s.spawn(move || -> Result<Vec<(String, &splitter::TheoremShard, i64)>> {
                        super::set_phase_context(phases);
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
                                let rooted_target = shard.rooted_name();
                                let expected_kth = kth_ref.get(shard_key).cloned();
                                let expected_pair: Vec<(String, String)> = expected_kth
                                    .as_ref()
                                    .map(|k| vec![(shard.decl_name().to_string(), k.clone())])
                                    .unwrap_or_default();
                                let shard_t0 = Instant::now();
                                let shard_src_owned = if shard.shard_source.is_empty() {
                                    let single_set = HashSet::from([rooted_target.clone()]);
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
                                        targets: vec![rooted_target.clone()],
                                        expected_kernel_type_hash: expected_kth.clone(),
                                    };
                                    match pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
                                        z_url,
                                        &zreq,
                                        || {},
                                    ) {
                                        Ok(Some(r)) => {
                                            if !expected_pair.is_empty() {
                                                let pairs: std::collections::BTreeMap<String, String> = r
                                                    .get("decl_types")
                                                    .and_then(|v| v.as_object())
                                                    .map(|dt| {
                                                        dt.iter()
                                                            .filter_map(|(k, v)| Some((k.clone(), v.as_str()?.to_string())))
                                                            .collect()
                                                    })
                                                    .unwrap_or_default();
                                                if let Err(e) = crate::zygote::verify_attested_decl_types(&pairs, &expected_pair) {
                                                    abort_ref.store(true, std::sync::atomic::Ordering::Relaxed);
                                                    anyhow::bail!(
                                                        "Parallel shard check failed for `{}` in {} (lines {}..={}):\n{}",
                                                        shard.decl_name(),
                                                        file_display,
                                                        shard.start_line,
                                                        shard.end_line,
                                                        e
                                                    );
                                                }
                                            }
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
                                            let h_suffix = maybe_append_hotspot_diagnostics_for_source(
                                                &worker_store,
                                                tc_ref,
                                                lp_ref,
                                                env_ref,
                                                Path::new(lean_bin_ref),
                                                &shard_src_owned,
                                                Some(&file_display),
                                                args_ref,
                                                &raw_err,
                                            );
                                            anyhow::bail!(
                                                "Parallel shard check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                                                shard.decl_name(),
                                                file_display,
                                                shard.start_line,
                                                shard.end_line,
                                                raw_err,
                                                m_suffix,
                                                h_suffix
                                            );
                                        }
                                    }
                                }

                                let audit_one = HashSet::from([rooted_target]);
                                let out = match crate::zygote::run_audited_lean_shard_with_types(
                                    &worker_store,
                                    Path::new(lean_bin_ref),
                                    env_ref,
                                    Some(canon_ref),
                                    &shard_src_owned,
                                    &audit_one,
                                    &expected_pair,
                                    args_ref,
                                    Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                                ) {
                                    Ok(o) => o,
                                    Err(e) => {
                                        abort_ref.store(true, std::sync::atomic::Ordering::Relaxed);
                                        anyhow::bail!(
                                            "Parallel shard check failed for `{}` in {} (lines {}..={}):\n{}",
                                            shard.name,
                                            file_display,
                                            shard.start_line,
                                            shard.end_line,
                                            e
                                        );
                                    }
                                };

                                if !out.status.success() {
                                    abort_ref.store(true, std::sync::atomic::Ordering::Relaxed);
                                    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
                                    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                                    let combined_err = format!("{}\n{}", stdout, stderr);
                                    let m_diags = extract_mismatch_diagnostics(&combined_err);
                                    let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                                    let h_suffix = maybe_append_hotspot_diagnostics_for_source(
                                        &worker_store,
                                        tc_ref,
                                        lp_ref,
                                        env_ref,
                                        Path::new(lean_bin_ref),
                                        &shard_src_owned,
                                        Some(&file_display),
                                        args_ref,
                                        &combined_err,
                                    );
                                    anyhow::bail!(
                                        "Parallel shard check failed for `{}` in {} (lines {}..={}):\n{}{}{}",
                                        shard.name,
                                        file_display,
                                        shard.start_line,
                                        shard.end_line,
                                        combined_err,
                                        m_suffix,
                                        h_suffix
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
        let mut out_json = serde_json::json!({
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
        insert_allow_sorry_fields(&mut out_json, allow_sorry, false, &[]);
        kernel_prov.insert_json_fields(&mut out_json);
        super::insert_check_timings(&mut out_json, *t0);
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
        let needs_fresh_read = match cached_file_blake3 {
            None => true,
            Some(expected_hex) => {
                src.is_empty() || blake3::hash(src.as_bytes()).to_hex().as_str() != expected_hex
            }
        };
        let mut actual_hygiene_strictly_clean = hygiene_strictly_clean;
        if needs_fresh_read {
            *src = fs::read_to_string(resolved_file)
                .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
            let actual_deps = compute_imported_olean_interface_hashes(src, canon_dir, None);
            let actual_split = split_lean_source(src, &actual_deps);
            if !actual_split.hygiene.is_clean_or_deferred_to_kernel_gate() {
                anyhow::bail!(
                    "Soundness hygiene violation in {}: {}",
                    file.display(),
                    if actual_split.hygiene.disallowed_items().is_empty() {
                        "file contains sorry/admit or forbidden axioms".to_string()
                    } else {
                        actual_split.hygiene.disallowed_items().join(", ")
                    }
                );
            }
            actual_hygiene_strictly_clean &= actual_split.hygiene.is_clean_for_certification();
            if actual_split.interface_hash != split.interface_hash
                || actual_split.shards.len() != split.shards.len()
                || actual_split
                    .shards
                    .iter()
                    .zip(split.shards.iter())
                    .any(|(a, b)| {
                        a.rooted_name() != b.rooted_name()
                            || a.prefix_env_hash != b.prefix_env_hash
                            || a.stmt_hash != b.stmt_hash
                            || a.proof_hash != b.proof_hash
                    })
            {
                anyhow::bail!(
                    "[TurboLean.KernelGate] source `{}` diverged from cached split before whole-file verification",
                    file.display()
                );
            }
        }
        let orig_display = file.display().to_string();
        let mut verified_via_zygote_eval = false;
        let mut eval_stdout_text = String::new();
        let mut eval_messages: Vec<String> = Vec::new();
        let can_use_zygote_eval = actual_hygiene_strictly_clean
            && !crate::zygote::daemon_disabled()
            && !src.contains("IO.Process.exit")
            && !src.lines().take(20).any(|l| {
                let t = l.split("--").next().unwrap_or(l).trim();
                t == "module" || t.starts_with("module ")
            });
        let mut zygote_env = env_vars.clone();
        zygote_env
            .entry("TURBO_LEAN_CALLER_CWD".to_string())
            .or_insert_with(|| canon_dir.to_string_lossy().to_string());
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
                &zygote_env,
                Path::new(&lean_bin),
                toolchain,
                &local_lean_path,
                src,
                Some(&canon_resolved_initial.to_string_lossy()),
                0,
                &file_lean_args,
            )
            .with_context(|| format!("Check failed for {}", orig_display))?
            {
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
                } else if rep.crashed || rep.timed_out || rep.import_ok {
                    let raw_err = rep
                        .errors
                        .join("\n")
                        .replace("<zygote-eval>", &orig_display)
                        .replace("<zygote-decl>", &orig_display)
                        .replace("<zygote-shard>", &orig_display);
                    let m_diags = extract_mismatch_diagnostics(&raw_err);
                    let m_suffix = format_mismatch_diagnostics_summary(&m_diags);
                    let h_fmt = crate::zygote::format_hotspot_diagnostics(
                        &rep.timeout_hotspots,
                        &rep.simp_hotspots,
                    );
                    let h_suffix = if h_fmt.is_empty() {
                        maybe_append_hotspot_diagnostics_for_source(
                            store,
                            toolchain,
                            &local_lean_path,
                            &zygote_env,
                            Path::new(&lean_bin),
                            src,
                            Some(&orig_display),
                            &file_lean_args,
                            &raw_err,
                        )
                    } else {
                        format!("\n{h_fmt}")
                    };
                    anyhow::bail!(
                        "Check failed for {}:\n{}{}{}",
                        orig_display,
                        raw_err,
                        m_suffix,
                        h_suffix
                    );
                }
            }
        }
        let run_cli_audit =
            |label: &str| -> Result<(String, std::collections::BTreeMap<String, String>)> {
                let names: HashSet<String> = split.shards.iter().map(|s| s.rooted_name()).collect();
                let (out, cli_types) = crate::zygote::run_audited_lean_shard_at_with_types_report(
                    &store.root,
                    &store.fast_staging_dir(),
                    Path::new(&lean_bin),
                    &env_vars,
                    Some(canon_dir),
                    Some(canon_resolved_initial),
                    src,
                    &names,
                    false,
                    &whole_expected_types,
                    &file_lean_args,
                    Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                )
                .with_context(|| format!("{label} failed for {}", file.display()))?;
                if !out.status.success() {
                    let stdout = String::from_utf8_lossy(&out.stdout);
                    let stderr = String::from_utf8_lossy(&out.stderr);
                    let combined_err = format!("{stdout}\n{stderr}");
                    let h_suffix = maybe_append_hotspot_diagnostics_for_source(
                        store,
                        toolchain,
                        &local_lean_path,
                        &env_vars,
                        Path::new(&lean_bin),
                        src,
                        Some(&orig_display),
                        &file_lean_args,
                        &combined_err,
                    );
                    anyhow::bail!(
                        "{label} failed for {}:\n{combined_err}{h_suffix}",
                        file.display()
                    );
                }
                Ok((String::from_utf8_lossy(&out.stdout).to_string(), cli_types))
            };
        let mut audited_via_cli = false;
        let mut whole_verified_types = std::collections::BTreeMap::new();
        if !verified_via_zygote_eval {
            let (stdout_text, cli_types) = run_cli_audit("Check")?;
            eval_stdout_text = stdout_text;
            whole_verified_types = cli_types;
            audited_via_cli = true;
        }
        // Zygote eval has no kernel gate, and messages can be dropped by `#guard_msgs`:
        // check the whole file under the zygote's `strict_all` kernel gate, else compile
        // and audit a scratch `.olean` with zero stub exemptions.
        if !audited_via_cli {
            let can_audit_in_zygote = !src.contains("IO.Process.exit")
                && !src.lines().take(20).any(|l| {
                    let t = l.split("--").next().unwrap_or(l).trim();
                    t == "module" || t.starts_with("module ")
                });
            let mut kernel_audited = false;
            if can_audit_in_zygote {
                let rep = crate::zygote::eval_with_zygote_pool_audit_all(
                    store,
                    toolchain,
                    &local_lean_path,
                    &zygote_env,
                    Path::new(&lean_bin),
                    src,
                    Some(&canon_resolved_initial.to_string_lossy()),
                    Some(crate::zygote::remaining_timeout_ms(None, *t0)),
                    &file_lean_args,
                )
                .with_context(|| format!("Soundness audit failed for {}", file.display()))?;
                if rep.import_ok && rep.ok && !rep.crashed && !rep.timed_out {
                    if !whole_expected_types.is_empty() {
                        crate::zygote::verify_attested_decl_types(
                            &rep.decl_types,
                            &whole_expected_types,
                        )
                        .with_context(|| {
                            format!("Soundness audit failed for {}", file.display())
                        })?;
                    }
                    whole_verified_types = rep.decl_types;
                    kernel_audited = true;
                } else if rep.crashed || rep.timed_out || rep.import_ok {
                    let raw_err = rep
                        .errors
                        .join("\n")
                        .replace("<zygote-shard>", &orig_display);
                    let h_fmt = crate::zygote::format_hotspot_diagnostics(
                        &rep.timeout_hotspots,
                        &rep.simp_hotspots,
                    );
                    let h_suffix = if h_fmt.is_empty() {
                        String::new()
                    } else {
                        format!("\n{h_fmt}")
                    };
                    anyhow::bail!(
                        "Soundness audit failed for {}:\n{}{}",
                        file.display(),
                        raw_err,
                        h_suffix
                    );
                }
            }
            if !kernel_audited {
                whole_verified_types = run_cli_audit("Soundness audit")?.1;
            }
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
        if actual_hygiene_strictly_clean && !uncached_shards.is_empty() {
            let now = db::now_unix();
            for (shard_key, shard) in uncached_shards {
                if let SingleflightOutcome::Leader(lease) =
                    store.acquire_singleflight(&shard_key, toolchain, "theorem_shard", "trusted")?
                {
                    let kth_opt = attested_kths
                        .get(&shard_key)
                        .or_else(|| whole_verified_types.get(shard.decl_name()))
                        .map(String::as_str);
                    let receipt = make_attested_shard_receipt_bytes(
                        shard.decl_name(),
                        &shard.prefix_env_hash,
                        &shard.stmt_hash,
                        &shard.proof_hash,
                        now,
                        kth_opt,
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
        let mut out_json = serde_json::json!({
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
        insert_allow_sorry_fields(&mut out_json, allow_sorry, false, &[]);
        kernel_prov.insert_json_fields(&mut out_json);
        super::insert_check_timings(&mut out_json, *t0);
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
