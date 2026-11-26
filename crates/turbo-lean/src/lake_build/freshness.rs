use anyhow::{Context, Result};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::db::{BlobEntry, TurboStore};
use crate::pack;
use crate::splitter;

use super::*;

pub(crate) fn verified_sources_manifest_path(canon_dir: &Path) -> PathBuf {
    canon_dir
        .join(".lake")
        .join("build")
        .join(".turbo_verified_sources.json")
}

pub(crate) fn load_verified_project_manifest(
    canon_dir: &Path,
) -> Option<crate::module_builder::VerifiedDepManifest> {
    let manifest_path = verified_sources_manifest_path(canon_dir);
    let bytes = fs::read(&manifest_path).ok()?;
    let mut manifest: crate::module_builder::VerifiedDepManifest =
        serde_json::from_slice(&bytes).ok()?;
    let cfg = crate::module_builder::resolve_project_config(canon_dir).ok()?;
    let expected_inputs = crate::module_builder::workspace_lake_inputs_digest(&cfg).ok()?;
    if manifest.pkg_name != cfg.root_pkg.name
        || manifest.toolchain != cfg.toolchain
        || manifest.lean_githash != cfg.lean_githash
        || manifest.pkg_config_digest != cfg.root_pkg.config_digest
        // `pkg_config_digest` pins the input *declarations* but not their contents, and every
        // module check below is a source hash or an mtime: without this a `.sol` edit would leave
        // the whole manifest -- and so every `.olean` it vouches for -- accepted as fresh. The
        // workspace digest, not just the root package's: the manifest vouches for `.olean` files
        // whose modules import dependency modules, whose own elaboration reads the dependency's
        // inputs.
        || manifest.lake_inputs_digest != expected_inputs
        || manifest.workspace_config_digest != cfg.canonical_config_digest
        || manifest.allowed_axioms != crate::splitter::allowed_axioms()
        || manifest.kernel_policy_digest != crate::splitter::current_kernel_policy_digest()
    {
        return None;
    }
    manifest.cfg = Some(cfg);
    Some(manifest)
}

/// P0-4: whether `entry` (a root-package module importing `imports`) was elaborated against the
/// current artifacts of its direct imports, each resolved as at build time and verified with its
/// whole closure (`module_builder::import_pin_current`).
pub(super) fn entry_import_pins_current(
    manifest: &crate::module_builder::VerifiedDepManifest,
    entry: &crate::module_builder::VerifiedDepModuleEntry,
    hdr: &crate::module_builder::HeaderInfo,
) -> bool {
    let Some(cfg) = manifest.cfg.as_ref() else {
        return false;
    };
    crate::module_builder::verified_entry_imports_current_for_header(entry, hdr, |imp, pin_spec| {
        crate::module_builder::import_pin_current(cfg, &manifest.dep_import_memo, imp, pin_spec)
    })
}

pub(super) fn entry_import_pins_fresh_for_build(
    manifest: &crate::module_builder::VerifiedDepManifest,
    entry: &crate::module_builder::VerifiedDepModuleEntry,
    hdr: &crate::module_builder::HeaderInfo,
    cache: &mut crate::module_builder::LakeClosureCache,
) -> bool {
    let Some(cfg) = manifest.cfg.as_ref() else {
        return false;
    };
    crate::module_builder::verified_entry_imports_current_for_header(entry, hdr, |imp, pin_spec| {
        crate::module_builder::import_pin_fresh_for_build(cfg, cache, imp, pin_spec)
    })
}

/// `true` when the package declares Lake file inputs whose current contents are not the ones
/// `.turbo_verified_sources.json` was recorded against -- including when there is no manifest at
/// all, which is exactly the "built by plain `lake build`, or by a turbo-lean that predates this
/// field" case.
///
/// [`load_verified_project_manifest`] already rejects a mismatched manifest, but callers that read
/// a missing manifest as "nothing to invalidate" need the difference spelled out: dropping the
/// manifest *removes* the only per-module signal they have, so they must be told to treat the
/// modules as stale rather than merely losing the record.
///
/// Always `false` for a workspace that declares no inputs, so no existing project pays anything.
pub(crate) fn lake_inputs_changed_since_manifest(canon_dir: &Path) -> bool {
    // No Lake config at all means no declared inputs, so there is nothing this can be wrong
    // about. But a config that *exists* and will not resolve is a different answer: the inputs it
    // declares are unknown, and reporting "unchanged" there would accept every `.olean` the
    // manifest vouches for against bytes nobody looked at. That case fails closed.
    if !has_lake_config(canon_dir)
        && !crate::module_builder::workspace_may_declare_lake_inputs(canon_dir)
    {
        return false;
    }
    let Ok(cfg) = crate::module_builder::resolve_project_config(canon_dir) else {
        return true;
    };
    let Ok(expected) = crate::module_builder::workspace_lake_inputs_digest(&cfg) else {
        return true;
    };
    if expected.is_empty() {
        return false;
    }
    let recorded = fs::read(verified_sources_manifest_path(canon_dir))
        .ok()
        .and_then(|b| serde_json::from_slice::<crate::module_builder::VerifiedDepManifest>(&b).ok())
        .map(|m| m.lake_inputs_digest);
    recorded.as_deref() != Some(expected.as_str())
}

pub(super) fn verify_project_module_entry_and_sidecars(
    canon_dir: &Path,
    rel_src: &str,
    expected_src_blake3: &str,
    manifest: &crate::module_builder::VerifiedDepManifest,
) -> bool {
    let Some(entry) = manifest.modules.get(rel_src) else {
        return false;
    };
    if !entry.kernel_audited
        || entry.src_blake3 != expected_src_blake3
        || entry.lake_inputs_digest != manifest.lake_inputs_digest
    {
        return false;
    }
    let olean_path = resolve_project_olean_for_rel_path(canon_dir, rel_src);
    if !olean_path.is_file() {
        return false;
    }
    let Ok(actual_art_dig) =
        crate::module_builder::compute_olean_artifact_set_digest_with_policy(&olean_path, true)
    else {
        return false;
    };
    if entry.olean_artifact_digest != actual_art_dig {
        return false;
    }
    let src_path = canon_dir.join(rel_src);
    let Ok(src_raw) = fs::read_to_string(&src_path) else {
        return false;
    };
    let actual_src_b3 = blake3::hash(src_raw.as_bytes()).to_hex().to_string();
    if actual_src_b3 != expected_src_blake3 {
        return false;
    }
    let lib_lean_dir = canon_dir.join(".lake/build/lib/lean");
    let rel_slash = olean_path
        .strip_prefix(&lib_lean_dir)
        .unwrap_or(&olean_path)
        .with_extension("")
        .to_string_lossy()
        .replace('\\', "/");
    let mod_name = rel_slash.replace('/', ".");
    let has_disallowed_effects = match manifest.cfg.as_ref().and_then(|cfg| {
        crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, &mod_name)
            .map(|spec| (cfg, spec))
    }) {
        Some((cfg, spec)) => crate::module_builder::spec_source_has_disallowed_elab_host_effects(
            cfg, &spec, &src_raw,
        ),
        None => crate::splitter::source_may_execute_elab_host_effects(&src_raw, false),
    };
    if has_disallowed_effects {
        return false;
    }
    let hdr = crate::module_builder::parse_header_info(&src_raw);
    if hdr.header_error.is_some() {
        return false;
    }
    // P0-4: reject `.olean`s elaborated against an older artifact of one of their imports
    // (toolchain, configuration, and source were matched above).
    if !crate::c_abi::verify_module_cache_key(
        true,
        true,
        true,
        entry_import_pins_current(manifest, entry, &hdr),
        true,
    ) {
        return false;
    }
    let needs_c = crate::module_builder::global_emit_c_enabled()
        || hdr.has_c_export
        || manifest.cfg.as_ref().is_some_and(|cfg| {
            crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, &mod_name)
                .is_some_and(|sp| sp.precompile_modules || sp.emit_c_default || sp.is_exe_target)
        });
    let ir_dir = canon_dir.join(".lake/build/ir");
    crate::module_builder::verify_module_lake_sidecars(
        &olean_path,
        Some(&ir_dir),
        &rel_slash,
        &src_raw,
        hdr.is_module,
        needs_c,
    )
    .is_ok()
}

pub(crate) fn are_all_project_oleans_up_to_date(
    canon_dir: &Path,
    file_hashes: &BTreeMap<String, String>,
) -> bool {
    let lib_lean_dir = canon_dir.join(".lake/build/lib/lean");
    if file_hashes.is_empty() || !lib_lean_dir.is_dir() {
        return false;
    }
    let Some(manifest) = load_verified_project_manifest(canon_dir) else {
        return false;
    };

    let Ok(cfg) = crate::module_builder::resolve_project_config(canon_dir) else {
        return false;
    };
    let lakefile_mtime = std::iter::once(&cfg.root_pkg)
        .chain(cfg.dep_pkgs.iter())
        .flat_map(|pkg| {
            [
                "lakefile.lean",
                "lakefile.toml",
                "lake-manifest.json",
                "lean-toolchain",
            ]
            .into_iter()
            .filter_map(|name| {
                fs::metadata(pkg.pkg_root.join(name))
                    .and_then(|m| m.modified())
                    .ok()
            })
        })
        .max();
    let opt_out = worktree_auto_link_disabled(canon_dir);
    let mut checked_oleans = 0usize;

    for (rel_path, cur_b3) in file_hashes {
        if rel_path == "lakefile.lean" || rel_path.ends_with("/lakefile.lean") {
            continue;
        }
        let rel_no_ext = Path::new(rel_path).with_extension("");
        let olean_path = resolve_project_olean_for_rel_path(canon_dir, rel_path);
        let olean_meta = match fs::metadata(&olean_path) {
            Ok(m) if m.is_file() && m.len() > 0 => m,
            _ => {
                if rel_no_ext.components().count() == 1
                    && canon_dir.join(&rel_no_ext).is_dir()
                    && !manifest.modules.contains_key(rel_path)
                {
                    continue;
                }
                return false;
            }
        };
        if !verify_project_module_entry_and_sidecars(canon_dir, rel_path, cur_b3, &manifest) {
            return false;
        }
        checked_oleans += 1;
        let olean_mtime = olean_meta.modified().ok();
        if let (Some(om), Some(lm)) = (olean_mtime, lakefile_mtime) {
            if om < lm {
                return false;
            }
        }
        if opt_out {
            let src_path = canon_dir.join(rel_path);
            let src_mtime = fs::metadata(&src_path).and_then(|m| m.modified()).ok();
            let is_mtime_fresh = match (src_mtime, olean_mtime) {
                (Some(sm), Some(om)) if om >= sm => lakefile_mtime.is_none_or(|lm| om >= lm),
                _ => false,
            };
            if !is_mtime_fresh {
                return false;
            }
            let Some(imps) = read_header_imports_from_file(&src_path) else {
                return false;
            };
            if let Some(om) = olean_mtime {
                for imp in imps {
                    let imp_slash = crate::module_builder::module_name_to_rel_slash(&imp);
                    if let Some(dep_src) = resolve_project_lean_source(canon_dir, &imp_slash) {
                        if fs::metadata(&dep_src)
                            .and_then(|m| m.modified())
                            .is_ok_and(|dep_sm| om < dep_sm)
                        {
                            return false;
                        }
                        let dep_olean = lib_lean_dir.join(format!("{}.olean", imp_slash));
                        if fs::metadata(&dep_olean)
                            .and_then(|m| m.modified())
                            .map_or(true, |dep_om| om < dep_om)
                        {
                            return false;
                        }
                    }
                }
            }
        }
    }

    if checked_oleans == 0 {
        return false;
    }
    crate::module_builder::verify_project_native_and_c_sidecars_up_to_date(&cfg, &[])
}

pub(crate) fn are_all_project_oleans_replayed_in_store(
    store: &TurboStore,
    canon_dir: &Path,
    file_hashes: &BTreeMap<String, String>,
) -> bool {
    let Ok(cfg) = crate::module_builder::resolve_project_config(canon_dir) else {
        return false;
    };
    let (lean_path, _) = crate::module_builder::build_lean_search_path(&cfg, false);
    let mut dirs: Vec<PathBuf> = std::env::split_paths(&lean_path).collect();
    if !cfg.toolchain_lib_lean.as_os_str().is_empty() && !dirs.contains(&cfg.toolchain_lib_lean) {
        dirs.push(cfg.toolchain_lib_lean.clone());
    }
    let mut replay_batch =
        crate::module_builder::ReplayLookupBatchCache::new(store, &cfg, &lean_path);
    let mut worklist = Vec::new();
    for rel_path in file_hashes.keys() {
        if rel_path == "lakefile.lean" || rel_path.ends_with("/lakefile.lean") {
            continue;
        }
        let olean_path = resolve_project_olean_for_rel_path(canon_dir, rel_path);
        if olean_path.is_file() {
            match infer_module_name_from_olean_path(&cfg, &olean_path) {
                Some((mod_name, true)) => {
                    if !replay_batch.is_audited_in_store(
                        store,
                        &cfg,
                        &lean_path,
                        &mod_name,
                        &olean_path,
                    ) {
                        return false;
                    }
                }
                _ => {
                    if !replay_batch.is_replayed_in_store(store, &cfg, &lean_path, &olean_path) {
                        return false;
                    }
                }
            }
            if let Ok((imps, _)) =
                crate::module_builder::read_olean_binary_imports_cached(&olean_path)
            {
                worklist.extend(imps.into_iter().map(|i| i.module));
            }
        }
    }
    let allowed_axioms = crate::splitter::allowed_axioms();
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
        if crate::module_builder::is_root_project_olean_path(&cfg, &path) {
            if !replay_batch.is_audited_in_store(store, &cfg, &lean_path, &m, &path) {
                return false;
            }
        } else {
            let Ok(needs_audit) =
                crate::module_builder::verify_imported_package_module_source_hygiene(
                    &cfg,
                    &m,
                    &path,
                    &allowed_axioms,
                )
            else {
                return false;
            };
            if needs_audit {
                if !replay_batch.is_audited_in_store(store, &cfg, &lean_path, &m, &path) {
                    return false;
                }
            } else if !replay_batch.is_replayed_in_store(store, &cfg, &lean_path, &path) {
                return false;
            }
        }
        let Ok((imps, _)) = crate::module_builder::read_olean_binary_imports_cached(&path) else {
            return false;
        };
        worklist.extend(imps.into_iter().map(|i| i.module));
    }
    true
}

pub(super) fn infer_module_name_from_olean_path(
    cfg: &crate::module_builder::ProjectConfig,
    olean_path: &Path,
) -> Option<(String, bool)> {
    let root_lib = cfg
        .root_pkg
        .pkg_root
        .join(&cfg.root_pkg.build_dir)
        .join(&cfg.root_pkg.lean_lib_dir);
    if let Ok(rel) = olean_path.strip_prefix(&root_lib) {
        let rel_no_ext = rel.with_extension("");
        let parts: Vec<String> = rel_no_ext
            .components()
            .filter_map(|c| c.as_os_str().to_str().map(|s| s.to_string()))
            .collect();
        if !parts.is_empty() {
            return Some((
                crate::module_builder::format_lean_module_name_from_parts(
                    parts.iter().map(String::as_str),
                ),
                true,
            ));
        }
    }
    for dp in &cfg.dep_pkgs {
        let dep_lib = dp.pkg_root.join(&dp.build_dir).join(&dp.lean_lib_dir);
        if let Ok(rel) = olean_path.strip_prefix(&dep_lib) {
            let rel_no_ext = rel.with_extension("");
            let parts: Vec<String> = rel_no_ext
                .components()
                .filter_map(|c| c.as_os_str().to_str().map(|s| s.to_string()))
                .collect();
            if !parts.is_empty() {
                return Some((
                    crate::module_builder::format_lean_module_name_from_parts(
                        parts.iter().map(String::as_str),
                    ),
                    false,
                ));
            }
        }
    }
    None
}

pub(super) fn ensure_olean_roots_and_imports_replayed_in_store(
    store: &TurboStore,
    cfg: &crate::module_builder::ProjectConfig,
    seed_oleans: Vec<(String, PathBuf, bool)>,
) -> Result<()> {
    let (replay_lp, _) = crate::module_builder::build_lean_search_path(cfg, false);
    let mut dirs: Vec<PathBuf> = std::env::split_paths(&replay_lp).collect();
    if !cfg.toolchain_lib_lean.as_os_str().is_empty() && !dirs.contains(&cfg.toolchain_lib_lean) {
        dirs.push(cfg.toolchain_lib_lean.clone());
    }
    let mut root_mods: Vec<(String, PathBuf)> = Vec::new();
    let mut dep_mods: Vec<(String, PathBuf)> = Vec::new();
    let mut seen: HashSet<String> = HashSet::new();
    let mut worklist = Vec::new();
    for (mod_name, olean_path, is_root_pkg) in seed_oleans {
        if !olean_path.is_file() || !seen.insert(mod_name.clone()) {
            continue;
        }
        let (imps, _) = crate::module_builder::read_olean_binary_imports_cached(&olean_path)
            .with_context(|| {
                format!(
                    "Failed to parse binary `.olean` header of `{mod_name}` (`{}`): fail-closed",
                    olean_path.display()
                )
            })?;
        worklist.extend(imps.into_iter().map(|i| i.module));
        if is_root_pkg {
            root_mods.push((mod_name, olean_path));
        } else {
            dep_mods.push((mod_name, olean_path));
        }
    }
    while let Some(m) = worklist.pop() {
        if !seen.insert(m.clone()) {
            continue;
        }
        let Some(path) = crate::module_builder::resolve_olean_along_search_dirs(&dirs, &m) else {
            continue;
        };
        if crate::module_builder::is_verified_toolchain_olean_file(
            &cfg.toolchain_lib_lean,
            Some(&cfg.lean_githash),
            &path,
        ) {
            continue;
        }
        let (imps, _) = crate::module_builder::read_olean_binary_imports_cached(&path)
            .with_context(|| {
                format!(
                    "Failed to parse binary `.olean` header of imported `{m}` (`{}`): fail-closed",
                    path.display()
                )
            })?;
        worklist.extend(imps.into_iter().map(|i| i.module));
        if crate::module_builder::is_root_project_olean_path(cfg, &path) {
            root_mods.push((m, path));
        } else {
            dep_mods.push((m, path));
        }
    }
    let allowed_axioms = crate::splitter::allowed_axioms();
    let mut replay_batch =
        crate::module_builder::ReplayLookupBatchCache::new(store, cfg, &replay_lp);
    let mut pending_deps = Vec::new();
    let mut pending_roots = Vec::new();
    for (m, path) in &dep_mods {
        let needs_audit = crate::module_builder::verify_imported_package_module_source_hygiene(
            cfg,
            m,
            path,
            &allowed_axioms,
        )?;
        if needs_audit {
            if !replay_batch.is_audited_in_store(store, cfg, &replay_lp, m, path) {
                pending_roots.push(m.clone());
            }
        } else if !replay_batch.is_replayed_in_store(store, cfg, &replay_lp, path) {
            pending_deps.push(m.clone());
        }
    }
    if !pending_deps.is_empty() {
        crate::zygote::kernel_replay_modules_with_zygote(store, cfg, &pending_deps, &replay_lp)
            .context("Imported `.olean` failed independent kernel replay")?;
    }
    for (m, path) in &root_mods {
        if !replay_batch.is_audited_in_store(store, cfg, &replay_lp, m, path) {
            pending_roots.push(m.clone());
        }
    }
    if !pending_roots.is_empty() {
        crate::zygote::audit_compiled_modules_with_zygote(
            store,
            cfg,
            &pending_roots,
            &replay_lp,
            &[],
            false,
        )
        .context("Project `.olean` failed in-kernel soundness & replay audit")?;
    }
    Ok(())
}

pub(crate) fn ensure_project_and_imported_oleans_replayed_in_store(
    store: &TurboStore,
    canon_dir: &Path,
    file_hashes: &BTreeMap<String, String>,
) -> Result<()> {
    let cfg = crate::module_builder::resolve_project_config(canon_dir).context(
        "Cannot kernel-replay project `.olean`s without a resolvable project configuration: fail-closed",
    )?;
    let mut seed_oleans = Vec::new();
    for rel_path in file_hashes.keys() {
        if rel_path == "lakefile.lean" || rel_path.ends_with("/lakefile.lean") {
            continue;
        }
        let olean_path = resolve_project_olean_for_rel_path(canon_dir, rel_path);
        if olean_path.is_file() {
            if let Some((mod_name, is_root)) = infer_module_name_from_olean_path(&cfg, &olean_path)
            {
                seed_oleans.push((mod_name, olean_path, is_root));
            }
        }
    }
    ensure_olean_roots_and_imports_replayed_in_store(store, &cfg, seed_oleans)
}

pub(super) fn ensure_materialized_outputs_replayed_in_store(
    store: &TurboStore,
    canon_dir: &Path,
    outputs: &[BlobEntry],
    file_hashes: &BTreeMap<String, String>,
    targets: &[String],
) -> Result<()> {
    if targets.is_empty() {
        return ensure_project_and_imported_oleans_replayed_in_store(store, canon_dir, file_hashes);
    }
    let cfg = crate::module_builder::resolve_project_config(canon_dir).context(
        "Cannot kernel-replay materialized target `.olean`s without a resolvable project configuration: fail-closed",
    )?;
    let mut seed_oleans = Vec::new();
    for entry in outputs {
        if entry.kind != "olean" {
            continue;
        }
        let olean_path = canon_dir.join(&entry.rel_path);
        if olean_path.is_file() {
            if let Some((mod_name, is_root)) = infer_module_name_from_olean_path(&cfg, &olean_path)
            {
                seed_oleans.push((mod_name, olean_path, is_root));
            }
        }
    }
    ensure_olean_roots_and_imports_replayed_in_store(store, &cfg, seed_oleans)
}

pub(crate) fn is_file_and_imports_verified_in_manifest(
    canon_dir: &Path,
    canon_file: &Path,
    actual_hash: &str,
    manifest: &crate::module_builder::VerifiedDepManifest,
) -> bool {
    let rel_path = canon_file
        .strip_prefix(canon_dir)
        .unwrap_or(canon_file)
        .to_string_lossy()
        .replace('\\', "/");
    if !verify_project_module_entry_and_sidecars(canon_dir, &rel_path, actual_hash, manifest) {
        return false;
    }
    let Some(mut worklist) = read_header_imports_from_file(canon_file) else {
        return false;
    };
    let mut visited = HashSet::new();
    while let Some(mod_name) = worklist.pop() {
        if !visited.insert(mod_name.clone()) {
            continue;
        }
        let imp_slash = crate::module_builder::module_name_to_rel_slash(&mod_name);
        if let Some(dep_src) = resolve_project_lean_source(canon_dir, &imp_slash) {
            let dep_rel = dep_src
                .strip_prefix(canon_dir)
                .unwrap_or(&dep_src)
                .to_string_lossy()
                .replace('\\', "/");
            let Some(actual_dep_hash) = compute_cached_source_blake3(&dep_src) else {
                return false;
            };
            if !verify_project_module_entry_and_sidecars(
                canon_dir,
                &dep_rel,
                &actual_dep_hash,
                manifest,
            ) {
                return false;
            }
            let Some(sub_imps) = read_header_imports_from_file(&dep_src) else {
                return false;
            };
            for sub_imp in sub_imps {
                if !visited.contains(&sub_imp) {
                    worklist.push(sub_imp);
                }
            }
        }
    }
    true
}

pub(crate) fn is_file_hash_verified_in_lake_build(
    canon_dir: &Path,
    canon_file: &Path,
    actual_hash: &str,
) -> bool {
    let Some(manifest) = load_verified_project_manifest(canon_dir) else {
        return false;
    };
    is_file_and_imports_verified_in_manifest(canon_dir, canon_file, actual_hash, &manifest)
}

pub(crate) fn is_file_verified_in_lake_build(
    canon_dir: &Path,
    canon_file: &Path,
    src: &str,
) -> bool {
    let actual_hash = blake3::hash(src.as_bytes()).to_hex().to_string();
    is_file_hash_verified_in_lake_build(canon_dir, canon_file, &actual_hash)
}

#[cfg(test)]
pub(crate) fn resolve_prebuilt_module_import(
    canon_project_dir: &Path,
    canon_file: &Path,
) -> Option<String> {
    resolve_prebuilt_module_import_with_path(canon_project_dir, canon_file).map(|(m, _)| m)
}

pub(super) fn resolve_prebuilt_module_import_with_path(
    canon_project_dir: &Path,
    canon_file: &Path,
) -> Option<(String, PathBuf)> {
    let rel = canon_file.strip_prefix(canon_project_dir).ok()?;
    let rel_no_ext = rel.with_extension("");
    let parts: Vec<String> = rel_no_ext
        .components()
        .filter_map(|c| c.as_os_str().to_str().map(|s| s.to_string()))
        .collect();
    if parts.is_empty() {
        return None;
    }
    if parts.len() >= 4 && parts[0] == ".lake" && parts[1] == "packages" {
        let pkg_name = &parts[2];
        let pkg_root = canon_project_dir
            .join(".lake")
            .join("packages")
            .join(pkg_name);
        return resolve_prebuilt_module_import_with_path(&pkg_root, canon_file);
    }
    let lib_lean_dir = canon_project_dir
        .join(".lake")
        .join("build")
        .join("lib")
        .join("lean");
    let direct_olean = lib_lean_dir.join(&rel_no_ext).with_extension("olean");
    let (olean_path, mod_parts) = if direct_olean.is_file() {
        (direct_olean, parts.as_slice())
    } else if parts.len() >= 2 && matches!(parts[0].as_str(), "submission" | "src" | "lean") {
        let mut stripped_rel = PathBuf::new();
        for p in &parts[1..] {
            stripped_rel.push(p);
        }
        let alt_olean = lib_lean_dir.join(&stripped_rel).with_extension("olean");
        if alt_olean.is_file() {
            (alt_olean, &parts[1..])
        } else {
            return None;
        }
    } else {
        return None;
    };

    let manifest = load_verified_project_manifest(canon_project_dir)?;
    let actual_hash = compute_cached_source_blake3(canon_file)?;
    if !is_file_and_imports_verified_in_manifest(
        canon_project_dir,
        canon_file,
        &actual_hash,
        &manifest,
    ) {
        return None;
    }
    Some((
        crate::module_builder::format_lean_module_name_from_parts(
            mod_parts.iter().map(String::as_str),
        ),
        olean_path,
    ))
}

/// Resolve the pre-compiled `.olean` module import name ONLY when both local manifest freshness AND
/// `TurboStore` SQLite DB kernel-replay authority (`kernel_replayed_oleans`) hold for the target
/// `.olean` and all of its transitive non-toolchain `.olean` imports.
pub(crate) fn resolve_replayed_prebuilt_module_import(
    store: &TurboStore,
    canon_project_dir: &Path,
    canon_file: &Path,
) -> Option<String> {
    let (mod_name, olean_path) =
        resolve_prebuilt_module_import_with_path(canon_project_dir, canon_file)?;
    verify_module_olean_and_imports_replayed_in_store(
        store,
        canon_project_dir,
        &mod_name,
        &olean_path,
    )
}

/// Resolve the pre-compiled `.olean` module import name for a proof-only edited PR file whose
/// on-disk `.lake/build/lib/lean/<Mod>.olean` has already passed `pr-verify`'s kernel statement /
/// proof-irrelevance gate and whose `.olean` + transitive non-toolchain `.olean` imports hold
/// `TurboStore` kernel-replay authority (`kernel_replayed_oleans`), without requiring a
/// `.turbo_verified_sources.json` manifest (e.g. on stock `lake build` checkouts) or unmodified
/// source hash.
pub(crate) fn resolve_replayed_proof_only_module_import(
    store: &TurboStore,
    canon_project_dir: &Path,
    canon_file: &Path,
    allowed_src: &str,
) -> Option<String> {
    if allowed_src.is_empty() {
        return None;
    }
    let cfg = crate::module_builder::resolve_project_config(canon_project_dir).ok()?;
    let canon_target = canon_file
        .canonicalize()
        .unwrap_or_else(|_| canon_file.to_path_buf());
    let pkg_src_base = cfg.root_pkg.pkg_root.join(&cfg.root_pkg.src_dir);
    let mut resolved_mod: Option<crate::module_builder::DiscoveredModuleSpec> = None;
    for lib in cfg.root_pkg.libs.iter().rev() {
        let lib_src = match &lib.src_dir {
            Some(sd) => pkg_src_base.join(sd),
            None => pkg_src_base.clone(),
        };
        let lib_src_canon = lib_src.canonicalize().unwrap_or(lib_src);
        let Ok(rel) = canon_target.strip_prefix(&lib_src_canon) else {
            continue;
        };
        if rel.extension().and_then(|e| e.to_str()) != Some("lean") {
            continue;
        }
        let rel_no_ext = rel.with_extension("");
        let parts: Vec<String> = rel_no_ext
            .components()
            .filter_map(|c| c.as_os_str().to_str().map(|s| s.to_string()))
            .collect();
        if parts.is_empty() {
            continue;
        }
        let mod_name = crate::module_builder::format_lean_module_name_from_parts(
            parts.iter().map(String::as_str),
        );
        if let Some(spec) = crate::module_builder::resolve_importable_module_in_package(
            &cfg.root_pkg,
            true,
            &mod_name,
        ) {
            let spec_src_canon = spec
                .src_path
                .canonicalize()
                .unwrap_or_else(|_| spec.src_path.clone());
            if spec_src_canon == canon_target {
                resolved_mod = Some(spec);
                break;
            }
        }
    }
    let spec = resolved_mod?;
    let rel_slash = crate::module_builder::module_name_to_rel_slash(&spec.module_name);
    let olean_path = spec.build_lib_lean_dir.join(format!("{rel_slash}.olean"));
    if !olean_path.is_file() {
        return None;
    }
    let header = crate::module_builder::parse_header_info(allowed_src);
    if header.header_error.is_some() {
        return None;
    }
    let needs_c = spec.emit_c_default || crate::module_builder::global_emit_c_enabled();
    crate::module_builder::verify_module_lake_sidecars_inner_opts_ext(
        &olean_path,
        needs_c.then_some(spec.build_ir_dir.as_path()),
        &rel_slash,
        allowed_src,
        header.is_module,
        needs_c,
        true,
        true,
        !needs_c,
    )
    .ok()?;
    verify_module_olean_and_imports_replayed_in_store(
        store,
        canon_project_dir,
        &spec.module_name,
        &olean_path,
    )
}

pub(super) fn verify_module_olean_and_imports_replayed_in_store(
    store: &TurboStore,
    canon_project_dir: &Path,
    mod_name: &str,
    olean_path: &Path,
) -> Option<String> {
    let cfg = crate::module_builder::resolve_project_config(canon_project_dir).ok()?;
    let lean_path = resolve_remote_lean_path(canon_project_dir, None);
    let mut replay_batch =
        crate::module_builder::ReplayLookupBatchCache::new(store, &cfg, &lean_path);
    if !replay_batch.is_replayed_in_store(store, &cfg, &lean_path, olean_path) {
        return None;
    }
    let (imps, _) = crate::module_builder::read_olean_binary_imports_cached(olean_path).ok()?;
    let mut worklist: Vec<String> = imps.into_iter().map(|i| i.module).collect();
    let mut seen = HashSet::new();
    while let Some(m) = worklist.pop() {
        if !seen.insert(m.clone()) {
            continue;
        }
        let path = replay_batch.resolve_module_olean(&m)?;
        if crate::module_builder::is_verified_toolchain_olean_file(
            &cfg.toolchain_lib_lean,
            Some(&cfg.lean_githash),
            &path,
        ) {
            continue;
        }
        if !replay_batch.is_replayed_in_store(store, &cfg, &lean_path, &path) {
            return None;
        }
        let (sub_imps, _) = crate::module_builder::read_olean_binary_imports_cached(&path).ok()?;
        worklist.extend(sub_imps.into_iter().map(|i| i.module));
    }
    Some(mod_name.to_string())
}

pub(super) fn remove_module_node_artifacts(node: &crate::module_builder::ModuleNode) {
    let rel_slash = crate::module_builder::module_name_to_rel_slash(&node.module_name);
    let olean_suffix = format!("{rel_slash}.olean");
    let c_suffix = format!("{rel_slash}.c");
    if let Some(lib_base) = node
        .olean_path
        .to_string_lossy()
        .strip_suffix(&olean_suffix)
    {
        let lib_lean_dir = PathBuf::from(lib_base.trim_end_matches('/'));
        for suffix in [
            ".olean",
            ".olean.hash",
            ".olean.server",
            ".olean.server.hash",
            ".olean.private",
            ".olean.private.hash",
            ".ilean",
            ".ilean.hash",
            ".ir",
            ".ir.hash",
            ".ir.sig",
            ".ir.sig.hash",
            ".trace",
        ] {
            let _ = fs::remove_file(lib_lean_dir.join(format!("{rel_slash}{suffix}")));
        }
    } else {
        let _ = fs::remove_file(&node.olean_path);
    }
    if let Some(ir_base) = node.c_path.to_string_lossy().strip_suffix(&c_suffix) {
        let ir_dir = PathBuf::from(ir_base.trim_end_matches('/'));
        for suffix in [
            ".c",
            ".c.hash",
            ".ltar",
            ".ltar.hash",
            ".bc",
            ".bc.hash",
            ".setup.json",
            ".ilean",
            ".ilean.hash",
            ".trace",
        ] {
            let _ = fs::remove_file(ir_dir.join(format!("{rel_slash}{suffix}")));
        }
    } else {
        let _ = fs::remove_file(&node.c_path);
    }
}

pub(crate) fn purge_sorry_artifacts_after_allow_sorry_failure(
    canon_dir: &Path,
    seed_files: &[PathBuf],
) {
    if !worktree_auto_link_disabled(canon_dir) {
        let _ = purge_workspace_sorry_artifacts_and_manifest(canon_dir, seed_files, &[]);
    }
}

/// Purge modulo-`sorry` build artifacts and `.turbo_verified_sources.json` entries across the
/// full workspace DAG + standalone graph (covering non-root `srcDir`, multi-hop transitive
/// dependents `A -> B -> C`, and pre-existing sorry-bearing imports).
pub(crate) fn workspace_tainted_sorry_paths(
    canon_dir: &Path,
    extra_seed_files: &[PathBuf],
) -> HashSet<PathBuf> {
    collect_workspace_sorry_taint(canon_dir, extra_seed_files, &[]).1
}

pub(super) fn collect_workspace_sorry_taint(
    canon_dir: &Path,
    extra_seed_files: &[PathBuf],
    extra_seed_mods: &[String],
) -> (
    HashSet<String>,
    HashSet<PathBuf>,
    Option<ProjectDependentClosure>,
) {
    let file_has_sorry = |p: &Path| -> bool {
        fs::read_to_string(p)
            .map(|s| splitter::audit_hygiene(&splitter::strip_lean_comments(&s)).has_sorry)
            .unwrap_or(false)
    };
    let canon = |p: &Path| p.canonicalize().unwrap_or_else(|_| p.to_path_buf());

    let mut sorry_mod_set: HashSet<String> = HashSet::new();
    let mut sorry_canon_paths: HashSet<PathBuf> = HashSet::new();

    for (rf, rm) in extra_seed_files.iter().zip(extra_seed_mods.iter()) {
        if file_has_sorry(rf) {
            sorry_mod_set.insert(rm.clone());
            sorry_canon_paths.insert(canon(rf));
        }
    }
    for rf in extra_seed_files {
        if file_has_sorry(rf) {
            sorry_canon_paths.insert(canon(rf));
        }
    }

    let closure_opt = compute_project_dependent_closure(canon_dir, &[], false).ok();
    let roots_fallback = closure_opt
        .as_ref()
        .map(|c| package_source_roots(canon_dir, &c.cfg.root_pkg))
        .unwrap_or_else(|| vec![canon(canon_dir)]);

    if let Some(ref closure) = closure_opt {
        if let Some(ref dag) = closure.dag {
            for (m, node) in &dag.nodes {
                let cpath = canon(&node.src_path);
                if sorry_canon_paths.contains(&cpath) || file_has_sorry(&node.src_path) {
                    sorry_mod_set.insert(m.clone());
                    sorry_canon_paths.insert(cpath);
                }
            }
        }
        for (m, spec) in &closure.standalone_all {
            let cpath = canon(&spec.src_path);
            if sorry_canon_paths.contains(&cpath) || file_has_sorry(&spec.src_path) {
                sorry_mod_set.insert(m.clone());
                sorry_canon_paths.insert(cpath);
            }
        }
    } else {
        for lf in collect_project_lean_files(canon_dir, false, None) {
            let cpath = canon(&lf);
            if sorry_canon_paths.contains(&cpath) || file_has_sorry(&lf) {
                sorry_canon_paths.insert(cpath.clone());
                if let Some(r) = roots_fallback.iter().find(|r| cpath.starts_with(r)) {
                    if let Ok(rel) = cpath.strip_prefix(r) {
                        let m = crate::module_builder::format_lean_module_name_from_parts(
                            rel.with_extension("")
                                .components()
                                .filter_map(|c| c.as_os_str().to_str()),
                        );
                        if !m.is_empty() {
                            sorry_mod_set.insert(m);
                        }
                    }
                }
            }
        }
    }

    if sorry_mod_set.is_empty() && sorry_canon_paths.is_empty() {
        return (sorry_mod_set, sorry_canon_paths, closure_opt);
    }

    // Fixed-point transitive dependent closure across DAG nodes, standalone modules, and rechecked files.
    if let Some(ref closure) = closure_opt {
        let mut changed = true;
        while changed {
            changed = false;
            if let Some(ref dag) = closure.dag {
                for (m, node) in &dag.nodes {
                    if !sorry_mod_set.contains(m)
                        && node
                            .direct_dag_deps
                            .iter()
                            .any(|d| sorry_mod_set.contains(d))
                    {
                        sorry_mod_set.insert(m.clone());
                        sorry_canon_paths.insert(canon(&node.src_path));
                        changed = true;
                    }
                }
            }
            for (m, spec) in &closure.standalone_all {
                if !sorry_mod_set.contains(m)
                    && spec.imports.iter().any(|d| sorry_mod_set.contains(d))
                {
                    sorry_mod_set.insert(m.clone());
                    sorry_canon_paths.insert(canon(&spec.src_path));
                    changed = true;
                }
            }
        }
    }

    let mut recheck_changed = true;
    while recheck_changed {
        recheck_changed = false;
        for (rf, rm) in extra_seed_files.iter().zip(extra_seed_mods.iter()) {
            if sorry_mod_set.contains(rm) {
                sorry_canon_paths.insert(canon(rf));
                continue;
            }
            let imports_sorry = fs::read_to_string(rf)
                .map(|s| {
                    crate::module_builder::parse_header_info(&s)
                        .imports
                        .iter()
                        .any(|imp| sorry_mod_set.contains(imp))
                })
                .unwrap_or(false);
            if imports_sorry {
                sorry_mod_set.insert(rm.clone());
                sorry_canon_paths.insert(canon(rf));
                recheck_changed = true;
            }
        }
    }

    (sorry_mod_set, sorry_canon_paths, closure_opt)
}

pub(super) fn purge_workspace_sorry_artifacts_and_manifest(
    canon_dir: &Path,
    extra_seed_files: &[PathBuf],
    extra_seed_mods: &[String],
) -> HashSet<String> {
    let canon = |p: &Path| p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
    let (sorry_mod_set, sorry_canon_paths, closure_opt) =
        collect_workspace_sorry_taint(canon_dir, extra_seed_files, extra_seed_mods);
    if sorry_mod_set.is_empty() && sorry_canon_paths.is_empty() {
        return sorry_mod_set;
    }

    // Purge all build artifacts for tainted modules.
    if let Some(ref closure) = closure_opt {
        if let Some(ref dag) = closure.dag {
            for m in &sorry_mod_set {
                if let Some(node) = dag.nodes.get(m) {
                    remove_module_node_artifacts(node);
                }
            }
        }
    }
    for m in &sorry_mod_set {
        let rel_slash = crate::module_builder::module_name_to_rel_slash(m);
        remove_module_build_artifacts(canon_dir, &rel_slash);
    }

    // Remove tainted `pkg_root`-relative keys from `.turbo_verified_sources.json`.
    let manifest_path = verified_sources_manifest_path(canon_dir);
    if let Some(mut manifest) = fs::read(&manifest_path)
        .ok()
        .and_then(|b| serde_json::from_slice::<crate::module_builder::VerifiedDepManifest>(&b).ok())
    {
        let mut keys_to_remove: HashSet<String> = HashSet::new();
        if let Some(ref closure) = closure_opt {
            if let Some(ref dag) = closure.dag {
                for m in &sorry_mod_set {
                    if let Some(node) = dag.nodes.get(m) {
                        let rel = node
                            .src_path
                            .strip_prefix(&node.pkg_root)
                            .unwrap_or(&node.src_path)
                            .to_string_lossy()
                            .replace('\\', "/");
                        keys_to_remove.insert(rel);
                    }
                }
            }
        }
        let canon_root = canon(canon_dir);
        for cp in &sorry_canon_paths {
            let rel = cp
                .strip_prefix(&canon_root)
                .or_else(|_| cp.strip_prefix(canon_dir))
                .unwrap_or(cp)
                .to_string_lossy()
                .replace('\\', "/");
            keys_to_remove.insert(rel);
        }
        let mut modified = false;
        for k in keys_to_remove {
            if manifest.modules.remove(&k).is_some() {
                modified = true;
            }
        }
        if modified {
            if let Ok(json_bytes) = serde_json::to_vec(&manifest) {
                let _ = fs::write(&manifest_path, json_bytes);
            } else {
                let _ = fs::remove_file(&manifest_path);
            }
        }
    }

    sorry_mod_set
}

pub(super) fn remove_file_if_present_checked(path: &Path) -> Result<()> {
    match fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => anyhow::bail!(
            "Failed to purge stale build artifact `{}` before Lake refresh: {}",
            path.display(),
            e
        ),
    }
}

pub(super) fn remove_build_artifacts_in_dirs_checked(
    lib_lean_dir: &Path,
    ir_dir: &Path,
    rel_slash: &str,
) -> Result<()> {
    for suffix in [
        ".olean",
        ".olean.hash",
        ".olean.server",
        ".olean.server.hash",
        ".olean.private",
        ".olean.private.hash",
        ".ilean",
        ".ilean.hash",
        ".ir",
        ".ir.hash",
        ".ir.sig",
        ".ir.sig.hash",
        ".trace",
    ] {
        let p = lib_lean_dir.join(format!("{}{}", rel_slash, suffix));
        remove_file_if_present_checked(&p)?;
    }
    for suffix in [
        ".c",
        ".c.hash",
        ".ltar",
        ".ltar.hash",
        ".bc",
        ".bc.hash",
        ".setup.json",
        ".ilean",
        ".ilean.hash",
        ".trace",
    ] {
        let p = ir_dir.join(format!("{}{}", rel_slash, suffix));
        remove_file_if_present_checked(&p)?;
    }
    Ok(())
}

pub(crate) fn remove_spec_build_artifacts_checked(
    spec: &crate::module_builder::DiscoveredModuleSpec,
) -> Result<()> {
    let rel_slash = crate::module_builder::module_name_to_rel_slash(&spec.module_name);
    remove_build_artifacts_in_dirs_checked(&spec.build_lib_lean_dir, &spec.build_ir_dir, &rel_slash)
}

pub(super) fn remove_module_build_artifacts_checked(canon_dir: &Path, rel_slash: &str) -> Result<()> {
    let lib_lean_dir = canon_dir.join(".lake/build/lib/lean");
    let ir_dir = canon_dir.join(".lake/build/ir");
    remove_build_artifacts_in_dirs_checked(&lib_lean_dir, &ir_dir, rel_slash)
}

pub(super) fn remove_module_build_artifacts(canon_dir: &Path, rel_slash: &str) {
    let _ = remove_module_build_artifacts_checked(canon_dir, rel_slash);
}

/// Translate a list of stale modules into the targets to hand `lake build`, replacing any module
/// that an input-bearing library can build by that library's name, and appending `@<pkg>/<exe>:exe`
/// for any `lean_exe` whose root module is in `modules`.
///
/// `lake build <Mod>` uses Lake's own attribution (the *last* `lean_lib` that can build `Mod`, or
/// the `lean_exe` whose root is `Mod`), and:
/// 1. That attribution may not be the library whose `needs` names the input `Mod` reads. Lake would
///    then compare a trace with no input entry in it, find it unchanged, and report `Mod` up to
///    date -- leaving the stale `.olean` in place.
/// 2. Passing `<Mod>` for a `lean_exe` root module only refreshes `<Mod>.olean` and leaves the
///    compiled executable in `.lake/build/bin/<exe>` stale; `@<pkg>/<exe>:exe` both evaluates the
///    executable's own `extraDep` (`needs`) trace and relinks the binary.
///
/// Ordering matters inside a single `lake build` invocation: Lake memoizes each module's build job
/// under the *first* target that schedules it. Input-bearing library targets are therefore placed
/// **before** plain module and `@<pkg>/<exe>:exe` targets so a shared module (or one imported by a
/// non-input-bearing target) is never memoized under an input-blind `extraDep` first.
///
/// Deleting the artifacts first would not be enough on its own: Lake can restore an `.olean` from
/// its artifact cache keyed on that same input-blind trace.
///
/// Returns `modules` unchanged for every project without Lake file inputs and without matching
/// `lean_exe` roots.
pub(crate) fn lake_refresh_targets(canon_dir: &Path, modules: &[String]) -> Vec<String> {
    // A project whose config does not resolve has no Lake file inputs this path can
    // see, so the stale-import refresh keeps its documented pass-through shape.
    let Ok(cfg) = crate::module_builder::resolve_project_config(canon_dir) else {
        return modules.to_vec();
    };
    lake_refresh_targets_inner(&cfg, modules, false)
}

/// The Lake-inputs closure sweep's variant (#434 / DA 449989b1 F3): dependency-package
/// lake targets are driven from the dependency's own workspace unless the project owns
/// the package, so every dependency-shaped target — an input-bearing `<dep>/<lib>`, an
/// `@<dep>/<exe>:exe`, a `+<Mod>` qualification — is emitted only for owned packages,
/// and a non-owned module (a shared checkout behind a symlinked `.lake/packages`
/// entry) emits nothing, matching the sweep's input-target seed gate and its purge
/// skip. Which modules the sweep considers at all is [`input_closure_sweep_mods`]'s
/// job: a non-owned module must not pull its owned dependents into the closure
/// either, or `lake build <dependent>` writes the stale non-owned module into the
/// shared checkout's build dir (DA 47e88386 F4). Taking the resolved config the
/// caller already holds closes the fail-open the path-taking shape had (an
/// unresolvable config returned the module list unfiltered) and drops the duplicate
/// resolution. The unfiltered [`lake_refresh_targets`] stays the stale-import
/// refresh's shape: asking Lake to bring a pinned dependency import up to date is
/// that path's sanctioned job (the worktree opt-out is its off switch), distinct
/// from this project driving a non-owned package's input-bearing targets.
pub(crate) fn lake_refresh_targets_for_input_closure(
    cfg: &crate::module_builder::ProjectConfig,
    modules: &[String],
) -> Vec<String> {
    lake_refresh_targets_inner(cfg, modules, true)
}

fn lake_refresh_targets_inner(
    cfg: &crate::module_builder::ProjectConfig,
    modules: &[String],
    owned_only: bool,
) -> Vec<String> {
    let owned_dep: std::collections::HashSet<&str> = if owned_only {
        cfg.dep_pkgs
            .iter()
            .filter(|dp| crate::module_builder::dep_pkg_lake_targets_owned_by_project(cfg, dp))
            .map(crate::module_builder::pkg_target_base_name)
            .collect()
    } else {
        std::collections::HashSet::new()
    };
    let root_base = crate::module_builder::pkg_target_base_name(&cfg.root_pkg);
    // Target shapes: "<lib>" (root), "<depBase>/<lib>", or "@<base>/<exe>:exe".
    let dep_target_owned = |t: &str| -> bool {
        if !owned_only {
            return true;
        }
        if let Some(rest) = t.strip_prefix('@') {
            let base = rest.split('/').next().unwrap_or("");
            return base == root_base || owned_dep.contains(base);
        }
        match t.split_once('/') {
            None => true,
            Some((base, _)) => owned_dep.contains(base),
        }
    };
    let any_inputs =
        !cfg.root_pkg.inputs.is_empty() || cfg.dep_pkgs.iter().any(|dp| !dp.inputs.is_empty());
    let any_matching_exe = modules.iter().any(|m| {
        crate::module_builder::exe_targets_for_module(cfg, m)
            .iter()
            .any(|t| dep_target_owned(t))
    });
    // `None` means a module of a non-owned dependency package: no target at all.
    let qualify_non_root_mod = |m: &str| -> Option<String> {
        if m.starts_with('+')
            || m.starts_with('@')
            || m.contains('/')
            || crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, m).is_some()
        {
            return Some(m.to_string());
        }
        match cfg
            .dep_pkgs
            .iter()
            .find(|dp| crate::module_builder::resolve_module_in_package(dp, false, m).is_some())
        {
            Some(dp)
                if !owned_only
                    || owned_dep
                        .contains(crate::module_builder::pkg_target_base_name(dp)) =>
            {
                Some(format!("+{m}"))
            }
            Some(_) => None,
            None => Some(m.to_string()),
        }
    };
    if !any_inputs && !any_matching_exe {
        return modules
            .iter()
            .filter_map(|m| qualify_non_root_mod(m))
            .collect();
    }
    let mut input_lib_targets: Vec<String> = Vec::new();
    let mut other_targets: Vec<String> = Vec::new();
    for m in modules {
        let libs: Vec<String> = if any_inputs {
            crate::module_builder::input_bearing_libs_for_module(cfg, m)
                .into_iter()
                .filter(|t| dep_target_owned(t))
                .collect()
        } else {
            Vec::new()
        };
        let exes: Vec<String> = crate::module_builder::exe_targets_for_module(cfg, m)
            .into_iter()
            .filter(|t| dep_target_owned(t))
            .collect();
        input_lib_targets.extend(libs.iter().cloned());
        if libs.is_empty() && exes.is_empty() {
            if let Some(t) = qualify_non_root_mod(m) {
                other_targets.push(t);
            }
        } else {
            other_targets.extend(exes);
        }
    }
    input_lib_targets.sort();
    input_lib_targets.dedup();
    other_targets.sort();
    other_targets.dedup();
    other_targets.retain(|t| !input_lib_targets.contains(t));
    input_lib_targets.extend(other_targets);
    input_lib_targets
}

/// The Lake-inputs sweep's module closure over `dag`: every OWNED module whose own
/// build reads a Lake file input (an input-bearing library or executable can build
/// it, or its source uses `include_str`), plus every transitive OWNED dependent,
/// each of which has to be re-checked once an input changes.
///
/// Non-owned modules never enter the closure, as seed or as dependent (DA 47e88386
/// F4): the explicit input-target seeds are already ownership-gated, and a non-owned
/// seed here would pull its owned dependents in, whose emitted targets make
/// `lake build <dependent>` rebuild the stale non-owned module inside the shared
/// checkout's `.lake/build`, the #434 write the emission filter cannot catch. The
/// dependency's own workspace refreshes it; the stale-import refresh then covers the
/// owned importers.
pub(crate) fn input_closure_sweep_mods(
    cfg: &crate::module_builder::ProjectConfig,
    dag: &crate::module_builder::ModuleDag,
) -> std::collections::BTreeSet<String> {
    // Review cf31dd1e F4 (elevating 29baa2ab F3): ownership is keyed on the package
    // ROOT — an identity — never on name strings. A non-owned package whose origName
    // collides with an owned package's name must not ride into the closure, and an
    // owned package whose node spells the other name form must not silently drop out
    // (an empty closure makes `all_fresh_on_disk` vacuously true and clears the
    // explicit `input_libs` seeds). Both the raw and the canonical root forms go into
    // the set, so the lookup needs no per-node syscall whichever form the dag recorded.
    let owned_dep_roots: std::collections::HashSet<std::path::PathBuf> = cfg
        .dep_pkgs
        .iter()
        .filter(|dp| crate::module_builder::dep_pkg_lake_targets_owned_by_project(cfg, dp))
        .flat_map(|dp| {
            let raw = dp.pkg_root.clone();
            let canon = dp.pkg_root.canonicalize().unwrap_or_else(|_| raw.clone());
            [raw, canon]
        })
        .collect();
    let node_owned = |n: &crate::module_builder::ModuleNode| {
        n.is_root_pkg || owned_dep_roots.contains(&n.pkg_root)
    };
    let mut closure: std::collections::BTreeSet<String> = dag
        .nodes
        .iter()
        .filter_map(|(m, n)| {
            // Review a64324fd F6 (reshaping cf31dd1e F6): ownership is decided FIRST.
            // A non-owned node runs only the config-walking gates (an input-bearing
            // library or executable can build it) before it is dismissed — never the
            // module resolvers or per-module source reads, which on a Mathlib import
            // meant thousands of file reads on every sweep just to decide whether to
            // print a warning.
            if !node_owned(n) {
                // cf31dd1e F6: an EXCLUDED non-owned input-bearing seed used to fail
                // the freshness check loudly; now that the sweep skips it, a stale one
                // must not go silent while the purge path fails closed on the same
                // state. Review bfa9d056 F4 orders the work by cost: the artifact
                // STALENESS check (resolver + mtimes) runs first, and the per-module
                // SOURCE reads that decide `include_str` input-bearing run only for
                // nodes that came out stale — so a fresh Mathlib import still costs no
                // file reads per sweep, while a stale include_str-only module keeps
                // its warning (the purge path fails closed on exactly that state).
                let config_input_bearing =
                    !crate::module_builder::input_bearing_libs_for_module(cfg, m).is_empty()
                        || !crate::module_builder::input_bearing_exes_for_module(cfg, m)
                            .is_empty();
                let spec =
                    crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, m)
                        .or_else(|| {
                            match crate::module_builder::resolve_import_site(cfg, m) {
                                crate::module_builder::ImportSite::Module(s) => Some(*s),
                                _ => None,
                            }
                        });
                let stale = spec
                    .as_ref()
                    .is_some_and(crate::module_builder::spec_own_artifact_stale_on_disk);
                // Review bfa9d056 F5: the dedupe key carries the package root (two
                // packages may share a module name), and a node seen FRESH clears its
                // entry, so a module the user refreshes and later lets go stale again
                // is warned about again, even in a long-lived daemon.
                static WARNED_STALE_NON_OWNED: std::sync::OnceLock<
                    std::sync::Mutex<std::collections::BTreeSet<(std::path::PathBuf, String)>>,
                > = std::sync::OnceLock::new();
                let warned = WARNED_STALE_NON_OWNED
                    .get_or_init(|| std::sync::Mutex::new(std::collections::BTreeSet::new()));
                let key = (n.pkg_root.clone(), m.clone());
                if !stale {
                    if let Ok(mut guard) = warned.lock() {
                        guard.remove(&key);
                    }
                    return None;
                }
                let input_bearing = config_input_bearing
                    || spec.as_ref().is_some_and(|spec| {
                        fs::read_to_string(&spec.src_path)
                            .map(|s| {
                                crate::module_builder::module_directly_depends_on_lake_inputs(
                                    cfg,
                                    &spec.pkg_root,
                                    &spec.module_name,
                                    &s,
                                )
                            })
                            .unwrap_or(true)
                    })
                    || fs::read_to_string(&n.src_path)
                        .map(|s| crate::module_builder::source_uses_include_str(&s))
                        .unwrap_or(false);
                if !input_bearing {
                    return None;
                }
                let first_time = warned
                    .lock()
                    .map(|mut guard| guard.insert(key))
                    .unwrap_or(true);
                if first_time {
                    eprintln!(
                        "[turbo-lean] input-bearing module `{}` lives in a non-owned checkout and its artifacts are stale on disk; the freshness sweep does not cover it — {}",
                        m,
                        crate::module_builder::non_owned_dep_refresh_remedy(
                            m,
                            &cfg.root_pkg.pkg_root,
                            &n.pkg_root,
                            crate::module_builder::OwnerMarkerSite::PkgRootOrParent {
                                clean_git_pinned:
                                    crate::module_builder::pkg_is_clean_git_pinned(
                                        cfg,
                                        &n.pkg_name,
                                        &n.pkg_base_name,
                                        &n.pkg_root,
                                    ),
                            },
                        )
                    );
                }
                return None;
            }
            let spec = crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, m)
                .or_else(
                    || match crate::module_builder::resolve_import_site(cfg, m) {
                        crate::module_builder::ImportSite::Module(s) => Some(*s),
                        _ => None,
                    },
                );
            let spec_has_include_str = spec.as_ref().is_some_and(|spec| {
                fs::read_to_string(&spec.src_path)
                    .map(|s| {
                        crate::module_builder::module_directly_depends_on_lake_inputs(
                            cfg,
                            &spec.pkg_root,
                            &spec.module_name,
                            &s,
                        )
                    })
                    .unwrap_or(true)
            });
            let input_bearing = !crate::module_builder::input_bearing_libs_for_module(cfg, m)
                .is_empty()
                || !crate::module_builder::input_bearing_exes_for_module(cfg, m).is_empty()
                || spec_has_include_str
                || fs::read_to_string(&n.src_path)
                    .map(|s| crate::module_builder::source_uses_include_str(&s))
                    .unwrap_or(false);
            if !input_bearing {
                return None;
            }
            Some(m.clone())
        })
        .collect();
    let mut changed = !closure.is_empty();
    while changed {
        changed = false;
        for (m, n) in &dag.nodes {
            if node_owned(n)
                && !closure.contains(m)
                && n.direct_dag_deps.iter().any(|d| closure.contains(d))
            {
                closure.insert(m.clone());
                changed = true;
            }
        }
    }
    closure
}

pub(super) struct DiscoveredRootImportMod {
    pub(super) mod_name: String,
    pub(super) imp_slash: String,
    pub(super) dep_src: PathBuf,
    pub(super) dep_olean: PathBuf,
    pub(super) is_lake_target: bool,
}

/// Inspect all transitive workspace imports (root package and workspace dependencies) of
/// `target_files` in `canon_dir`.
/// If any imported module `<M>` has a stale `.olean` on disk (older than `<M>.lean`,
/// older than one of its transitive dependencies, or mismatched against `.turbo_verified_sources.json`),
/// bring it up to date with Lake when the project has a Lake config (failing if Lake cannot),
/// or else purge the stale `.olean` artifacts, so `lean` / `ZygoteWorker` never elaborates against a stale `.olean`.
/// With the worktree opt-out, report stale modules before changing any artifacts or manifests.
pub(crate) fn ensure_project_imports_fresh(
    canon_dir: &Path,
    target_files: &[PathBuf],
    rev: Option<&str>,
    build_missing: bool,
) -> Result<usize> {
    ensure_project_imports_fresh_inner(canon_dir, target_files, rev, build_missing, false)
}

pub(super) fn ensure_project_imports_fresh_inner(
    canon_dir: &Path,
    target_files: &[PathBuf],
    rev: Option<&str>,
    build_missing: bool,
    verify_only: bool,
) -> Result<usize> {
    // Fail closed immediately if the workspace may declare Lake file inputs (`input_dir` /
    // `input_file`) or has an unparseable manifest/config that fails static resolution.
    let _ = crate::module_builder::try_project_lake_inputs_tag(canon_dir)?;

    let manifest_path = verified_sources_manifest_path(canon_dir);
    // Pins and artifact digests describe disk whatever policy they were recorded under, so only
    // the schema has to match here. A manifest that exists but does not parse (legacy schema,
    // corruption) gives no evidence: every built import is refreshed and the file dropped.
    let (mut manifest_opt, unusable_manifest) = match fs::read(&manifest_path) {
        Ok(bytes) => {
            match serde_json::from_slice::<crate::module_builder::VerifiedDepManifest>(&bytes) {
                Ok(m) => (Some(m), false),
                Err(_) => (None, true),
            }
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => (None, false),
        Err(_) => (None, true),
    };

    let mut worklist: Vec<String> = Vec::new();
    let mut target_rel_slashes: Vec<String> = Vec::new();
    for tf in target_files {
        if tf.try_exists()? || fs::symlink_metadata(tf).is_ok() {
            let imps = read_header_imports_from_file(tf).ok_or_else(|| {
                anyhow::anyhow!(
                    "Unparseable or unreadable import header in `{}`: fail-closed import freshness gate",
                    tf.display()
                )
            })?;
            worklist.extend(imps);
        }
        if let Ok(rel) = tf.strip_prefix(canon_dir) {
            let rel_no_ext = rel.with_extension("");
            let mut comps = rel_no_ext.components();
            if let Some(first) = comps.next().and_then(|c| c.as_os_str().to_str()) {
                if matches!(first, "submission" | "src" | "lean") {
                    let rest: PathBuf = comps.collect();
                    if !rest.as_os_str().is_empty() {
                        target_rel_slashes.push(rest.to_string_lossy().replace('\\', "/"));
                        continue;
                    }
                }
            }
            target_rel_slashes.push(rel_no_ext.to_string_lossy().replace('\\', "/"));
        }
    }
    if worklist.is_empty() {
        return Ok(0);
    }

    // Ownership matches build order (root, then dependency packages, ambiguity fail-closed, then
    // toolchain). A name in `Init`/`Std`/`Lean`/`Lake` is not reserved: skip it only once it
    // actually resolves as a toolchain module. A present Lake config (or non-empty
    // `lake-manifest.json` / `.lake/packages/*`) that fails to resolve is not "no config":
    // dependency ownership cannot be established, so fail closed before any cache lookup or
    // `.lake` write. Standalone directories keep the legacy filesystem lookup only when every
    // non-root import resolves in the active toolchain's `lib/lean`.
    let has_dep_packages = (canon_dir.join("lake-manifest.json").try_exists()? && {
        let (_, pkgs, _) = crate::module_builder::parse_lake_manifest(canon_dir, false)
            .with_context(|| {
                format!(
                    "Failed to resolve Lean options and workspace configuration in {}",
                    canon_dir.display()
                )
            })?;
        !pkgs.is_empty()
    }) || (canon_dir.join(".lake/packages").try_exists()?
        && fs::read_dir(canon_dir.join(".lake/packages"))
            .with_context(|| {
                format!(
                    "Failed to read dependency packages in {}",
                    canon_dir.display()
                )
            })?
            .next()
            .is_some());
    let has_workspace_cfg = canon_dir.join("lakefile.lean").try_exists()?
        || canon_dir.join("lakefile.toml").try_exists()?
        || has_dep_packages;
    let root_cfg = if has_workspace_cfg {
        Some(
            crate::module_builder::resolve_project_config(canon_dir).with_context(|| {
                format!(
                    "Failed to resolve Lean options and workspace configuration in {}",
                    canon_dir.display()
                )
            })?,
        )
    } else {
        None
    };
    if let Some(m) = manifest_opt.as_mut() {
        m.cfg = root_cfg.clone();
    }
    let root_lib_lean_dir = root_cfg
        .as_ref()
        .map(|cfg| {
            cfg.root_pkg
                .pkg_root
                .join(&cfg.root_pkg.build_dir)
                .join(&cfg.root_pkg.lean_lib_dir)
        })
        .unwrap_or_else(|| canon_dir.join(".lake/build/lib/lean"));
    let root_lake_inputs_stale = lake_inputs_changed_since_manifest(canon_dir);
    let expected_lake_inputs = match &root_cfg {
        Some(cfg) => crate::module_builder::workspace_lake_inputs_digest(cfg)?,
        None => String::new(),
    };
    let has_lake_inputs = !expected_lake_inputs.is_empty();

    let resolve_root_import = |mod_name: &str,
                               imp_slash: &str|
     -> Option<DiscoveredRootImportMod> {
        if let Some(ref cfg) = root_cfg {
            if let Some(spec) =
                crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, mod_name)
            {
                let dep_olean = spec.build_lib_lean_dir.join(format!("{imp_slash}.olean"));
                return Some(DiscoveredRootImportMod {
                    mod_name: mod_name.to_string(),
                    imp_slash: imp_slash.to_string(),
                    dep_src: spec.src_path,
                    dep_olean,
                    is_lake_target: true,
                });
            }
            if matches!(
                crate::module_builder::resolve_import_site(cfg, mod_name),
                crate::module_builder::ImportSite::Toolchain
            ) || cfg.dep_pkgs.iter().any(|dp| {
                crate::module_builder::resolve_module_in_package(dp, false, mod_name).is_some()
            }) {
                return None;
            }
        }
        resolve_project_lean_source(canon_dir, imp_slash).map(|dep_src| DiscoveredRootImportMod {
            mod_name: mod_name.to_string(),
            imp_slash: imp_slash.to_string(),
            dep_src,
            dep_olean: root_lib_lean_dir.join(format!("{imp_slash}.olean")),
            is_lake_target: false,
        })
    };

    let mut visited = HashSet::new();
    let mut ordered_imports: Vec<DiscoveredRootImportMod> = Vec::new();
    let mut mod_index: HashMap<String, usize> = HashMap::new();
    let mut adj: HashMap<String, Vec<String>> = HashMap::new();
    let mut hdr_by_mod: HashMap<String, crate::module_builder::HeaderInfo> = HashMap::new();
    let mut non_root_imports: Vec<String> = Vec::new();
    let mut standalone_tc_lib_lean: Option<PathBuf> = None;
    while let Some(mod_name) = worklist.pop() {
        if !visited.insert(mod_name.clone()) {
            continue;
        }
        let imp_slash = crate::module_builder::module_name_to_rel_slash(&mod_name);
        if let Some(info) = resolve_root_import(&mod_name, &imp_slash) {
            let hdr = fs::read_to_string(&info.dep_src)
                .ok()
                .map(|src| crate::module_builder::parse_header_info(&src))
                .filter(|h| h.header_error.is_none())
                .ok_or_else(|| {
                    anyhow::anyhow!(
                        "Unparseable or unreadable import header in `{}`: fail-closed import freshness gate",
                        info.dep_src.display()
                    )
                })?;
            for sub_imp in &hdr.imports {
                if !visited.contains(sub_imp) {
                    worklist.push(sub_imp.clone());
                }
            }
            adj.insert(mod_name.clone(), hdr.imports.clone());
            hdr_by_mod.insert(mod_name.clone(), hdr);
            mod_index.insert(mod_name, ordered_imports.len());
            ordered_imports.push(info);
        } else if let Some(cfg) = root_cfg.as_ref() {
            if !matches!(
                crate::module_builder::resolve_import_site(cfg, &mod_name),
                crate::module_builder::ImportSite::Toolchain
            ) {
                non_root_imports.push(mod_name);
            }
        } else if mod_name == "Init" {
            continue;
        } else {
            let tc_lib = match standalone_tc_lib_lean.as_ref() {
                Some(tc_lib) => tc_lib,
                None => {
                    let tc = detect_toolchain(canon_dir);
                    let (_, _, tc_lib, _) =
                        crate::module_builder::resolve_toolchain_compiler_with_trust(
                            canon_dir, &tc, true,
                        )
                        .with_context(|| {
                            format!(
                                "Cannot verify standalone import `{mod_name}` without an installed Lean toolchain in {}",
                                canon_dir.display()
                            )
                        })?;
                    standalone_tc_lib_lean.insert(tc_lib)
                }
            };
            anyhow::ensure!(
                tc_lib
                    .join(format!(
                        "{}.olean",
                        crate::module_builder::module_name_to_rel_slash(&mod_name)
                    ))
                    .is_file(),
                "Unresolved non-root import `{mod_name}` in Lake-less directory {}: fail-closed import freshness gate",
                canon_dir.display()
            );
        }
    }
    // Dependency-package and prebuilt imports whose closure is not provably consistent (P0-4):
    // Lean would otherwise load them next to their rebuilt imports without re-checking. Their
    // evidence lives in their own package manifests / Lake traces, so it is inspected even
    // without a root manifest.
    let mut closure_cache = crate::module_builder::LakeClosureCache::default();
    closure_cache.post_lake_refresh = verify_only;
    closure_cache.ignore_mtime_skew = !worktree_auto_link_disabled(canon_dir);
    let mut stale_dep_mods: HashSet<String> = HashSet::new();
    non_root_imports.sort();
    non_root_imports.dedup();
    let dep_cfg = if non_root_imports.is_empty() {
        None
    } else {
        root_cfg.clone()
    };
    if let Some(cfg) = dep_cfg.as_ref() {
        let fresh_memo = crate::module_builder::DepImportMemo::default();
        let memo = manifest_opt
            .as_ref()
            .map_or(&fresh_memo, |m| &m.dep_import_memo);
        stale_dep_mods.extend(non_root_imports.into_iter().filter(|m| {
            crate::module_builder::dep_pkg_module_stale(cfg, memo, &mut closure_cache, m)
                || (build_missing && crate::module_builder::dep_pkg_module_missing_olean(cfg, m))
        }));
    }
    if ordered_imports.is_empty() && stale_dep_mods.is_empty() {
        return Ok(0);
    }

    let root_pkg_has_inputs = root_cfg
        .as_ref()
        .is_some_and(|cfg| !cfg.root_pkg.inputs.is_empty());

    let mut stale_mods: HashSet<String> = HashSet::new();
    let mut tier_pin_exempt_mods: HashSet<String> = HashSet::new();
    for info in &ordered_imports {
        let dep_olean = &info.dep_olean;
        let olean_meta = fs::metadata(dep_olean).ok();
        let src_meta = fs::metadata(&info.dep_src).ok();
        let dep_rel = info
            .dep_src
            .strip_prefix(canon_dir)
            .unwrap_or(&info.dep_src)
            .to_string_lossy()
            .replace('\\', "/");
        let cur_hash = compute_cached_source_blake3(&info.dep_src);
        let root_spec_opt = root_cfg.as_ref().and_then(|cfg| {
            crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, &info.mod_name)
                .map(|spec| (cfg, spec))
        });
        let src_elab_host_effects_stale = !verify_only
            && olean_meta.is_some()
            && fs::read_to_string(&info.dep_src)
                .map(|s| match root_spec_opt.as_ref() {
                    Some((cfg, spec)) => {
                        crate::module_builder::spec_source_has_disallowed_elab_host_effects(
                            cfg, spec, &s,
                        )
                    }
                    None => crate::splitter::source_may_execute_elab_host_effects(&s, false),
                })
                .unwrap_or(true);

        let opt_out = worktree_auto_link_disabled(canon_dir);
        let closure_uses_lake_inputs = opt_out
            || match root_spec_opt.as_ref() {
                Some((cfg, spec)) => closure_cache.module_closure_depends_on_lake_inputs(cfg, spec),
                None => true,
            };

        let pkg_inputs_stale = !verify_only
            && root_lake_inputs_stale
            && closure_uses_lake_inputs
            && (olean_meta.is_some()
                || (info.is_lake_target && (build_missing || root_pkg_has_inputs)));

        // An entry whose artifacts or import pins moved on (e.g. an import rebuilt, restored,
        // or CAS-restored without a newer mtime) marks its `.olean` stale even when timestamps
        // look ordered; staleness then propagates to dependents below.
        // A recorded toolchain or Lean githash other than the one this check elaborates with
        // is stale evidence, even when sources, artifacts, and unpinned toolchain imports match.
        // Without a resolvable config (`lean_githash` unknown) or an installed compiler, the
        // manifest's toolchain identity cannot be matched, so fail closed.
        let identity_stale = manifest_opt.as_ref().is_some_and(|m| {
            m.modules.contains_key(&dep_rel)
                && match root_cfg.as_ref() {
                    Some(cfg) => {
                        cfg.lean_bin.as_os_str().is_empty()
                            || m.pkg_name != cfg.root_pkg.name
                            || m.toolchain != cfg.toolchain
                            || m.lean_githash != cfg.lean_githash
                            || m.pkg_config_digest != cfg.root_pkg.config_digest
                            || (closure_uses_lake_inputs
                                && m.lake_inputs_digest != expected_lake_inputs)
                    }
                    None => true,
                }
        });
        let has_manifest_entry = manifest_opt
            .as_ref()
            .is_some_and(|m| m.modules.contains_key(&dep_rel));
        let manifest_stale = identity_stale
            || match (&manifest_opt, &cur_hash) {
                (Some(m), Some(ch)) => match m.modules.get(&dep_rel) {
                    Some(e) => {
                        e.src_blake3 != *ch
                            || (closure_uses_lake_inputs
                                && e.lake_inputs_digest != expected_lake_inputs)
                            || (olean_meta.is_some()
                                && !(m.cfg.as_ref().is_some_and(|cfg| {
                                    crate::module_builder::entry_artifacts_current(
                                        cfg, dep_olean, e,
                                    ) && (!info.is_lake_target
                                        || crate::module_builder::root_module_lake_sidecars_current(
                                            cfg,
                                            &info.mod_name,
                                        ))
                                }) && hdr_by_mod.get(&info.mod_name).is_some_and(|hdr| {
                                    let prev_allow = closure_cache.allow_stale_manifest_hydration;
                                    closure_cache.allow_stale_manifest_hydration = !opt_out;
                                    let ok = entry_import_pins_fresh_for_build(
                                        m,
                                        e,
                                        hdr,
                                        &mut closure_cache,
                                    );
                                    closure_cache.allow_stale_manifest_hydration = prev_allow;
                                    ok
                                })))
                    }
                    None => {
                        !verify_only
                            && has_lake_inputs
                            && closure_uses_lake_inputs
                            && (olean_meta.is_some()
                                || (info.is_lake_target && root_pkg_has_inputs))
                    }
                },
                (None, _) => {
                    !verify_only
                        && info.is_lake_target
                        && root_pkg_has_inputs
                        && closure_uses_lake_inputs
                }
                _ => false,
            };
        let lake_root_stale = info.is_lake_target
            && !has_manifest_entry
            && olean_meta.is_some()
            && root_cfg.as_ref().is_some_and(|cfg| {
                let prev_allow = closure_cache.allow_stale_manifest_hydration;
                closure_cache.allow_stale_manifest_hydration = !opt_out;
                let stale = crate::module_builder::root_pkg_lake_module_stale(
                    cfg,
                    &mut closure_cache,
                    &info.mod_name,
                );
                closure_cache.allow_stale_manifest_hydration = prev_allow;
                stale
            });
        let src_elab_host_effects_stale = src_elab_host_effects_stale
            && (fs::read_to_string(&info.dep_src)
                .map(|s| {
                    root_spec_opt.as_ref().is_none_or(|(cfg, spec)| {
                        crate::module_builder::source_ineligible_for_stamp_reuse(
                            cfg,
                            &spec.pkg_root,
                            &spec.module_name,
                            &spec.src_path,
                            &s,
                        )
                    })
                })
                .unwrap_or(true)
                || opt_out
                || unusable_manifest
                || identity_stale
                || manifest_stale
                || !has_manifest_entry);
        let cryptographically_verified = !opt_out
            && olean_meta.is_some()
            && !src_elab_host_effects_stale
            && !pkg_inputs_stale
            && !manifest_stale
            && !lake_root_stale
            && !unusable_manifest
            && (has_manifest_entry
                || (info.is_lake_target
                    && root_cfg
                        .as_ref()
                        .is_some_and(|cfg| !cfg.lean_bin.as_os_str().is_empty())));
        let mtime_stale = if cryptographically_verified {
            false
        } else {
            match (&olean_meta, &src_meta) {
                (Some(om), Some(sm)) => match (om.modified(), sm.modified()) {
                    (Ok(ot), Ok(st)) => ot < st,
                    _ => true,
                },
                (Some(_), None) => true,
                (None, _) => has_manifest_entry,
            }
        };
        let trace_stale = if olean_meta.as_ref().is_some_and(|m| m.is_file()) {
            let trace_path = dep_olean.with_extension("trace");
            if trace_path.is_file() {
                fs::read(&trace_path)
                    .ok()
                    .and_then(|b| serde_json::from_slice::<serde_json::Value>(&b).ok())
                    .is_none()
            } else {
                info.is_lake_target || has_manifest_entry
            }
        } else {
            false
        };
        let olean_githash_stale = olean_meta.is_some()
            && match root_cfg.as_ref() {
                Some(cfg)
                    if !cfg.lean_bin.as_os_str().is_empty()
                        && cfg.lean_githash != "lean-not-installed" =>
                {
                    crate::module_builder::read_olean_header_version_and_githash(dep_olean)
                        .is_none_or(|(_, gh)| !gh.eq_ignore_ascii_case(cfg.lean_githash.trim()))
                }
                _ => false,
            };
        let refreshed_sidecars_stale = verify_only
            && info.is_lake_target
            && root_cfg.as_ref().is_none_or(|cfg| {
                !crate::module_builder::root_module_lake_sidecars_current(cfg, &info.mod_name)
            });
        if refreshed_sidecars_stale
            || src_elab_host_effects_stale
            || pkg_inputs_stale
            || manifest_stale
            || lake_root_stale
            || olean_githash_stale
            || mtime_stale
            || trace_stale
            || (unusable_manifest && olean_meta.is_some())
            || (build_missing
                && info.is_lake_target
                && !olean_meta.as_ref().is_some_and(|m| m.is_file()))
        {
            stale_mods.insert(info.mod_name.clone());
        } else if olean_meta.is_some()
            && hdr_by_mod.get(&info.mod_name).is_some_and(|h| h.is_module)
            && ((has_manifest_entry
                && manifest_opt
                    .as_ref()
                    .and_then(|m| m.modules.get(&dep_rel))
                    .is_some_and(|e| {
                        !e.import_export_digests.is_empty() || !e.import_meta_digests.is_empty()
                    }))
                || (!has_manifest_entry && info.is_lake_target && root_cfg.is_some()))
        {
            tier_pin_exempt_mods.insert(info.mod_name.clone());
        }
    }

    stale_mods.extend(stale_dep_mods.iter().cloned());
    let opt_out_for_prop = worktree_auto_link_disabled(canon_dir);
    // Propagate staleness downstream across the imported workspace subgraph.
    // Force at least one pass even when `stale_mods` is initially empty so mtime inversions
    // between non-manifest modules are still caught.
    let mut changed = true;
    while changed {
        changed = false;
        for info in &ordered_imports {
            if stale_mods.contains(&info.mod_name) {
                continue;
            }
            let dep_rel = info
                .dep_src
                .strip_prefix(canon_dir)
                .unwrap_or(&info.dep_src)
                .to_string_lossy()
                .replace('\\', "/");
            let self_crypto_verified = !opt_out_for_prop
                && (tier_pin_exempt_mods.contains(&info.mod_name)
                    || manifest_opt
                        .as_ref()
                        .is_some_and(|m| m.modules.contains_key(&dep_rel))
                    || (info.is_lake_target
                        && root_cfg
                            .as_ref()
                            .is_some_and(|cfg| !cfg.lean_bin.as_os_str().is_empty())));
            let self_om = fs::metadata(&info.dep_olean)
                .and_then(|m| m.modified())
                .ok();
            if let Some(children) = adj.get(&info.mod_name) {
                for ch in children {
                    if stale_mods.contains(ch) {
                        stale_mods.insert(info.mod_name.clone());
                        changed = true;
                        break;
                    }
                    if !self_crypto_verified {
                        if let Some(&ch_idx) = mod_index.get(ch) {
                            let ch_info = &ordered_imports[ch_idx];
                            let ch_om = fs::metadata(&ch_info.dep_olean)
                                .and_then(|m| m.modified())
                                .ok();
                            let ch_sm = fs::metadata(&ch_info.dep_src)
                                .and_then(|m| m.modified())
                                .ok();
                            if let (Some(som), Some(com)) = (self_om, ch_om) {
                                if som < com {
                                    stale_mods.insert(info.mod_name.clone());
                                    changed = true;
                                    break;
                                }
                            }
                            if let (Some(som), Some(csm)) = (self_om, ch_sm) {
                                if som < csm {
                                    stale_mods.insert(info.mod_name.clone());
                                    changed = true;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    if stale_mods.is_empty() {
        return Ok(0);
    }
    let mut targets: Vec<String> = stale_mods.iter().cloned().collect();
    targets.sort();
    if verify_only {
        anyhow::bail!(
            "Imports remained stale after `lake build`: {}",
            targets.join(", ")
        );
    }
    if worktree_auto_link_disabled(canon_dir) {
        anyhow::bail!(
            "Worktree opt-out prevents refreshing stale imports: {}. Rebuild explicitly with Lake (`lake build {}`), then retry.",
            targets.join(", "),
            targets.join(" ")
        );
    }
    if has_lake_config(canon_dir) {
        let (lake_targets, non_target_stale): (Vec<String>, Vec<String>) = if let Some(ref cfg) =
            root_cfg
        {
            targets.iter().cloned().partition(|m| {
                crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, m).is_some()
                    || cfg.dep_pkgs.iter().any(|dp| {
                        crate::module_builder::resolve_module_in_package(dp, false, m).is_some()
                    })
            })
        } else if let Some(pkg) = crate::module_builder::optional_package_config(canon_dir)
            .ok()
            .flatten()
        {
            targets.iter().cloned().partition(|m| {
                crate::module_builder::resolve_module_in_package(&pkg, true, m).is_some()
            })
        } else {
            (targets.clone(), Vec::new())
        };
        if !non_target_stale.is_empty() {
            if let Some(ref cfg) = root_cfg {
                for m in &non_target_stale {
                    if !matches!(
                        crate::module_builder::resolve_import_site(cfg, m),
                        crate::module_builder::ImportSite::Toolchain
                    ) && resolve_project_lean_source(
                        canon_dir,
                        &crate::module_builder::module_name_to_rel_slash(m),
                    )
                    .is_none()
                    {
                        anyhow::bail!(
                            "Stale non-workspace/prebuilt imports {} cannot be rebuilt by Lake; rebuild their source packages, then retry.",
                            non_target_stale.join(", ")
                        );
                    }
                }
            }
        }
        // Lake owns `.lake/build` for target-owned modules (whose files may be hard links into its
        // artifact cache): let Lake bring stale target imports up to date, and purge any stale
        // standalone non-target `.olean`s left in `.lake/build/lib/lean`.
        let mut locally_rebuilt = None;
        if !lake_targets.is_empty() {
            let bypass_lake_cache = if let Some(ref cfg) = root_cfg {
                crate::module_builder::purge_elab_host_effect_artifacts_in_closure(
                    cfg,
                    &lake_targets,
                )?
            } else {
                let mut purged = false;
                for info in &ordered_imports {
                    if stale_mods.contains(&info.mod_name)
                        && fs::read_to_string(&info.dep_src)
                            .map(|s| {
                                crate::splitter::source_may_execute_elab_host_effects(&s, false)
                            })
                            .unwrap_or(true)
                    {
                        remove_module_build_artifacts_checked(canon_dir, &info.imp_slash)?;
                        purged = true;
                    }
                }
                purged
            };
            let rebuild_dag = root_cfg
                .as_ref()
                .filter(|_| bypass_lake_cache)
                .map(|cfg| crate::module_builder::build_module_dag(cfg, &lake_targets))
                .transpose()?;
            lake_build_modules_opts(
                canon_dir,
                &lake_refresh_targets(canon_dir, &lake_targets),
                rev,
                bypass_lake_cache,
            )?;
            locally_rebuilt = rebuild_dag;
        }
        for mod_name in &non_target_stale {
            let imp_slash = crate::module_builder::module_name_to_rel_slash(mod_name);
            remove_module_build_artifacts_checked(canon_dir, &imp_slash)?;
        }
        if let Some(mut manifest) = manifest_opt {
            for info in &ordered_imports {
                if stale_mods.contains(&info.mod_name) {
                    let dep_rel = info
                        .dep_src
                        .strip_prefix(canon_dir)
                        .unwrap_or(&info.dep_src)
                        .to_string_lossy()
                        .replace('\\', "/");
                    manifest.modules.remove(&dep_rel);
                }
            }
            if let Ok(json_bytes) = serde_json::to_vec(&manifest) {
                let _ = fs::write(&manifest_path, json_bytes);
            } else {
                let _ = fs::remove_file(&manifest_path);
            }
        } else if unusable_manifest {
            let _ = fs::remove_file(&manifest_path);
        }
        if let Some(cfg) = dep_cfg.as_ref() {
            for m in &stale_dep_mods {
                crate::module_builder::forget_refreshed_dep_module(cfg, m);
            }
        }
        ensure_project_imports_fresh_inner(canon_dir, target_files, rev, build_missing, true)?;
        if let (Some(cfg), Some(dag)) = (root_cfg.as_ref(), locally_rebuilt.as_ref()) {
            crate::module_builder::record_locally_rebuilt_sources(cfg, dag, &lake_targets)?;
        }
        return Ok(targets.len());
    }
    if !stale_dep_mods.is_empty() {
        let mut deps: Vec<_> = stale_dep_mods.into_iter().collect();
        deps.sort();
        anyhow::bail!(
            "Stale dependency-package imports {} (built against older imports); rebuild them with `turbo-lean build`, then retry.",
            deps.join(", ")
        );
    }

    if let Some(mut manifest) = manifest_opt {
        for info in &ordered_imports {
            if stale_mods.contains(&info.mod_name) {
                let dep_rel = info
                    .dep_src
                    .strip_prefix(canon_dir)
                    .unwrap_or(&info.dep_src)
                    .to_string_lossy()
                    .replace('\\', "/");
                manifest.modules.remove(&dep_rel);
            }
        }
        if let Ok(json_bytes) = serde_json::to_vec(&manifest) {
            let _ = fs::write(&manifest_path, json_bytes);
        } else {
            let _ = fs::remove_file(&manifest_path);
        }
    } else {
        let _ = fs::remove_file(&manifest_path);
    }
    for info in &ordered_imports {
        if stale_mods.contains(&info.mod_name) {
            remove_module_build_artifacts(canon_dir, &info.imp_slash);
        }
    }
    for t_slash in &target_rel_slashes {
        remove_module_build_artifacts(canon_dir, t_slash);
    }

    Ok(stale_mods.len())
}

pub(crate) fn ensure_project_imports_fresh_for_check_with_options(
    canon_dir: &Path,
    target_files: &[PathBuf],
    build_missing: bool,
) -> Result<usize> {
    ensure_project_imports_fresh(canon_dir, target_files, None, build_missing)
}

pub(crate) fn ensure_project_imports_fresh_for_check(
    canon_dir: &Path,
    target_files: &[PathBuf],
) -> Result<usize> {
    ensure_project_imports_fresh_for_check_with_options(canon_dir, target_files, false)
}

/// Verification rebuilds always use stock Lake. Project build_command wrappers may
/// otherwise substitute the compiler whose artifacts support the verdict.
pub(crate) fn lake_build_modules(
    canon_dir: &Path,
    modules: &[String],
    rev: Option<&str>,
) -> Result<()> {
    lake_build_modules_opts(canon_dir, modules, rev, false)
}

pub(super) fn lake_build_modules_opts(
    canon_dir: &Path,
    modules: &[String],
    _rev: Option<&str>,
    bypass_artifact_cache: bool,
) -> Result<()> {
    if worktree_auto_link_disabled(canon_dir) {
        anyhow::bail!(
            "Worktree opt-out prevents automatic Lake rebuild of modules: {}. Rebuild explicitly with Lake (`lake build {}`), then retry.",
            modules.join(", "),
            modules.join(" ")
        );
    }
    let tools = crate::module_builder::ToolchainExecutables::resolve(
        canon_dir,
        &detect_toolchain(canon_dir),
    )?;
    let _isolated_cache = if bypass_artifact_cache {
        Some(crate::check::PrivateScratchDir::create(
            &crate::check::verified_private_temp_scratch_base()?,
            "turbo_lake_nocache",
        )?)
    } else {
        None
    };
    let mut cmd = Command::new(&tools.lake);
    cmd.env("PATH", tools.lake_build_path(canon_dir))
        .env("LEAN", &tools.lean)
        .env("LAKE", &tools.lake)
        .env("LEANC", &tools.leanc);
    if let Some(ref scratch) = _isolated_cache {
        cmd.arg("--no-cache")
            .env("LAKE_ARTIFACT_CACHE", "false")
            .env("LAKE_CACHE_DIR", &scratch.path);
    }
    crate::module_builder::log_lake_build_invocation(
        canon_dir,
        "build",
        modules,
        bypass_artifact_cache,
    );
    let out = cmd
        .arg("build")
        .args(modules)
        .current_dir(canon_dir)
        .output()
        .map_err(|e| anyhow::anyhow!("failed to run `{}`: {}", tools.lake.display(), e))?;
    if !out.status.success() {
        let log = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let tail: Vec<&str> = log.lines().rev().take(40).collect();
        anyhow::bail!(
            "`{} <{} modules>` failed:\n{}",
            tools.lake.display(),
            modules.len(),
            tail.into_iter().rev().collect::<Vec<_>>().join("\n")
        );
    }
    Ok(())
}

pub(crate) fn has_lake_config(canon_dir: &Path) -> bool {
    canon_dir.join("lakefile.lean").is_file()
        || canon_dir.join("lakefile.toml").is_file()
        || canon_dir.join("lake-manifest.json").is_file()
        || crate::module_builder::package_config_path(canon_dir, None)
            .ok()
            .flatten()
            .is_some()
}

#[derive(Clone, Debug)]
pub(super) struct StandaloneModuleSpec {
    pub(super) module_name: String,
    pub(super) src_path: PathBuf,
    pub(super) src_root: PathBuf,
    pub(super) is_module: bool,
    pub(super) imports: Vec<String>,
    pub(super) import_visibilities: HashMap<String, crate::module_builder::DepImportVisibility>,
}

pub(super) struct ProjectDependentClosure {
    pub(super) cfg: crate::module_builder::ProjectConfig,
    pub(super) dag: Option<crate::module_builder::ModuleDag>,
    pub(super) dag_seeds: Vec<String>,
    pub(super) lake_seeds: Vec<String>,
    pub(super) edited_dag_modules: Vec<String>,
    pub(super) deleted_modules: Vec<String>,
    pub(super) dag_modules: Option<Vec<String>>,
    pub(super) dag_files: Option<Vec<PathBuf>>,
    pub(super) standalone_all: BTreeMap<String, StandaloneModuleSpec>,
    pub(super) standalone_modules: Vec<StandaloneModuleSpec>,
}

pub(super) fn package_source_roots(
    canon_dir: &Path,
    pkg: &crate::module_builder::PackageConfig,
) -> Vec<PathBuf> {
    let canon = |p: PathBuf| p.canonicalize().unwrap_or(p);
    let base = canon(canon_dir.join(&pkg.src_dir));
    let mut roots = vec![base.clone()];
    roots.extend(
        pkg.libs
            .iter()
            .filter_map(|lib| lib.src_dir.as_ref())
            .map(|dir| canon(base.join(dir))),
    );
    roots.extend(
        pkg.exes
            .iter()
            .filter_map(|exe| exe.src_dir.as_ref())
            .map(|dir| canon(base.join(dir))),
    );
    let canon_proj = canon(canon_dir.to_path_buf());
    if !roots.contains(&canon_proj) {
        roots.push(canon_proj);
    }
    roots.sort_by_key(|root| std::cmp::Reverse(root.components().count()));
    roots.dedup();
    roots
}

pub(super) fn discover_standalone_project_modules(
    canon_dir: &Path,
    cfg: &crate::module_builder::ProjectConfig,
    dag: Option<&crate::module_builder::ModuleDag>,
    edited: &HashSet<PathBuf>,
    is_untrusted: bool,
    strict_sources: bool,
) -> Result<BTreeMap<String, StandaloneModuleSpec>> {
    let canon = |p: &Path| p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
    let roots = package_source_roots(canon_dir, &cfg.root_pkg);
    let dag_paths: HashSet<PathBuf> = dag
        .map(|d| d.nodes.values().map(|n| canon(&n.src_path)).collect())
        .unwrap_or_default();
    let mut out = BTreeMap::new();
    for source in collect_project_lean_files(canon_dir, false, None) {
        let canon_src = canon(&source);
        if dag_paths.contains(&canon_src) {
            continue;
        }
        let Some(root) = roots.iter().find(|r| canon_src.starts_with(r)).cloned() else {
            continue;
        };
        let Ok(rel) = canon_src.strip_prefix(&root) else {
            continue;
        };
        let mod_name = crate::module_builder::format_lean_module_name_from_parts(
            rel.with_extension("")
                .components()
                .filter_map(|c| c.as_os_str().to_str()),
        );
        if mod_name.is_empty() || dag.is_some_and(|d| d.nodes.contains_key(&mod_name)) {
            continue;
        }
        if crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, &mod_name)
            .is_some_and(|spec| canon(&spec.src_path) == canon_src)
        {
            continue;
        }
        if is_untrusted {
            let meta = fs::symlink_metadata(&source).with_context(|| {
                format!(
                    "Failed to stat standalone Lean source `{}`",
                    source.display()
                )
            })?;
            anyhow::ensure!(
                !meta.file_type().is_symlink(),
                "Untrusted dependent recheck rejected symlink standalone source `{}`",
                source.display()
            );
        }
        let is_edited = edited.contains(&canon_src);
        let src_text = match fs::read_to_string(&source) {
            Ok(s) => s,
            Err(e) if is_untrusted || strict_sources || is_edited => {
                return Err(e).with_context(|| {
                    format!(
                        "Failed to read standalone Lean source `{}`",
                        source.display()
                    )
                });
            }
            Err(_) => continue,
        };
        let hdr = crate::module_builder::parse_header_info(&src_text);
        if let Some(err) = hdr.header_error {
            if is_untrusted || strict_sources || is_edited {
                anyhow::bail!(
                    "Invalid module header in standalone Lean file `{}`: {}",
                    source.display(),
                    err
                );
            }
            continue;
        }
        let import_visibilities = crate::module_builder::header_direct_import_visibilities(&hdr);
        if let Some(prev) = out.insert(
            mod_name.clone(),
            StandaloneModuleSpec {
                module_name: mod_name.clone(),
                src_path: canon_src,
                src_root: root,
                is_module: hdr.is_module,
                imports: hdr.imports,
                import_visibilities,
            },
        ) {
            anyhow::bail!(
                "Ambiguous standalone Lean module `{}` resolved to both `{}` and `{}`",
                mod_name,
                prev.src_path.display(),
                source.display()
            );
        }
    }
    Ok(out)
}

/// Which of the proof-edited project files `rels` need their importers re-checked. The import graph is
/// built once for the whole set, in the run's trust mode, and an unresolvable DAG is an error (fail
/// closed) rather than a silent fallback to "every standalone module". Unedited standalone files that
/// cannot be read or parsed are skipped, as the lenient dependent recheck does: only an unresolvable part
/// that could hold an importer should fail a proof-only PR. A project without a Lake config has no
/// import graph to read, so it reports none: the dependent recheck cannot run there.
///
/// Sound and cheap rather than exact: if any module outside the edited set depends on an edited file,
/// or more than one file is edited (edited files may import each other), every edited file is rechecked.
pub(crate) fn proof_edited_files_needing_recheck(
    canon_dir: &Path,
    rels: &[String],
    is_untrusted: bool,
) -> Result<Vec<String>> {
    if rels.is_empty() || !has_lake_config(canon_dir) {
        return Ok(Vec::new());
    }
    let closure = compute_project_dependent_closure_with_policy(
        canon_dir,
        rels,
        is_untrusted,
        true,
        is_untrusted,
    )?;
    let canon = |p: &Path| p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
    let edited: HashSet<PathBuf> = rels.iter().map(|r| canon(&canon_dir.join(r))).collect();
    let has_other_member = match closure.dag_files.as_ref() {
        Some(files) => {
            files.iter().any(|p| !edited.contains(&canon(p)))
                || closure
                    .standalone_modules
                    .iter()
                    .any(|s| !edited.contains(&canon(&s.src_path)))
        }
        None => true,
    };
    Ok(if has_other_member || rels.len() > 1 {
        rels.to_vec()
    } else {
        Vec::new()
    })
}

pub(super) fn compute_project_dependent_closure(
    canon_dir: &Path,
    edits: &[String],
    is_untrusted: bool,
) -> Result<ProjectDependentClosure> {
    compute_project_dependent_closure_inner(canon_dir, edits, is_untrusted, is_untrusted)
}

pub(super) fn compute_project_dependent_closure_inner(
    canon_dir: &Path,
    edits: &[String],
    is_untrusted: bool,
    strict_graph: bool,
) -> Result<ProjectDependentClosure> {
    compute_project_dependent_closure_with_policy(
        canon_dir,
        edits,
        is_untrusted,
        strict_graph,
        strict_graph,
    )
}

/// `strict_graph` makes an unresolvable module DAG an error; `strict_sources` makes an unreadable or
/// bad-headered UNEDITED standalone file an error (edited ones always are).
pub(super) fn compute_project_dependent_closure_with_policy(
    canon_dir: &Path,
    edits: &[String],
    is_untrusted: bool,
    strict_graph: bool,
    strict_sources: bool,
) -> Result<ProjectDependentClosure> {
    let cfg = crate::module_builder::resolve_project_config_with_trust(canon_dir, is_untrusted)?;
    let roots = package_source_roots(canon_dir, &cfg.root_pkg);
    let root_base = crate::module_builder::pkg_target_base_name(&cfg.root_pkg);
    let edited: HashSet<PathBuf> = edits
        .iter()
        .map(|e| canon_dir.join(e))
        .map(|p| p.canonicalize().unwrap_or(p))
        .collect();
    let assurance = if !is_untrusted {
        let allowed = splitter::allowed_axioms();
        crate::module_builder::discover_trusted_assurance_surface(
            canon_dir,
            &cfg.root_pkg,
            &allowed,
        )
    } else {
        crate::module_builder::TrustedAssuranceSurface::default()
    };
    let mut dag_seeds: Vec<String> =
        cfg.root_pkg
            .libs
            .iter()
            .filter(|l| {
                !assurance.lib_names.contains(&l.name)
                    || crate::module_builder::expand_lib_configured_modules(&cfg.root_pkg, l)
                        .is_ok_and(|pairs| {
                            pairs.iter().any(|(_, p)| {
                                edited.contains(&p.canonicalize().unwrap_or_else(|_| p.clone()))
                            })
                        })
            })
            .map(|l| format!("@{}/{}", root_base, l.name))
            .collect();
    let mut lake_seeds: Vec<String> = cfg
        .root_pkg
        .libs
        .iter()
        .filter(|l| dag_seeds.contains(&format!("@{}/{}", root_base, l.name)))
        .map(|l| l.name.clone())
        .collect();
    for exe in &cfg.root_pkg.exes {
        if assurance.exe_names.contains(&exe.name) {
            let exe_edited =
                crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, &exe.root)
                    .is_some_and(|spec| {
                        edited.contains(&spec.src_path.canonicalize().unwrap_or(spec.src_path))
                    });
            if !exe_edited {
                continue;
            }
        }
        let exe_dag_target = format!("@{}/{}:default", root_base, exe.name);
        if !dag_seeds.contains(&exe_dag_target) {
            dag_seeds.push(exe_dag_target);
        }
        let exe_lake_target = format!("@{}/{}:exe", root_base, exe.name);
        if !lake_seeds.contains(&exe_lake_target) {
            lake_seeds.push(exe_lake_target);
        }
    }
    let mut deleted = Vec::new();
    for e in edited.iter().filter(|e| !e.exists()) {
        for r in &roots {
            if let Ok(rel) = e.strip_prefix(r) {
                let m = rel.with_extension("").to_string_lossy().replace('/', ".");
                if !m.is_empty() && !deleted.contains(&m) {
                    deleted.push(m);
                }
            }
        }
    }
    let matches_deleted = |dep: &str| -> bool {
        deleted
            .iter()
            .any(|x| dep == x || x.ends_with(&format!(".{}", dep)))
    };

    let dag_opt = if is_untrusted || strict_graph {
        Some(crate::module_builder::build_module_dag_with_trust(
            &cfg,
            &dag_seeds,
            is_untrusted,
        )?)
    } else {
        crate::module_builder::build_module_dag_with_trust(&cfg, &dag_seeds, false).ok()
    };
    let mut standalone_all = discover_standalone_project_modules(
        canon_dir,
        &cfg,
        dag_opt.as_ref(),
        &edited,
        is_untrusted,
        strict_sources,
    )?;
    if !is_untrusted && !assurance.mod_names.is_empty() {
        standalone_all
            .retain(|m, s| !assurance.mod_names.contains(m) || edited.contains(&s.src_path));
    }

    if let Some(dag) = dag_opt {
        let edited_dag_modules: Vec<String> = dag
            .nodes
            .iter()
            .filter(|(_, n)| {
                edited.contains(&n.src_path.canonicalize().unwrap_or(n.src_path.clone()))
            })
            .map(|(m, _)| m.clone())
            .collect();
        let mut dag_closure: std::collections::BTreeSet<String> =
            edited_dag_modules.iter().cloned().collect();
        let mut standalone_closure: std::collections::BTreeSet<String> = standalone_all
            .iter()
            .filter(|(_, s)| edited.contains(&s.src_path))
            .map(|(m, _)| m.clone())
            .collect();

        let mut changed = true;
        while changed {
            changed = false;
            for (m, n) in &dag.nodes {
                if !dag_closure.contains(m)
                    && n.direct_dag_deps.iter().any(|d| {
                        dag_closure.contains(d)
                            || standalone_closure.contains(d)
                            || matches_deleted(d)
                    })
                {
                    dag_closure.insert(m.clone());
                    changed = true;
                }
            }
            for (m, s) in &standalone_all {
                if !standalone_closure.contains(m)
                    && s.imports.iter().any(|d| {
                        dag_closure.contains(d)
                            || standalone_closure.contains(d)
                            || matches_deleted(d)
                    })
                {
                    standalone_closure.insert(m.clone());
                    changed = true;
                }
            }
        }
        // Also pull in any upstream standalone module transitively imported by a standalone module in the closure,
        // so standalone elaboration always has `.olean`s for upstream standalone imports.
        let mut up_changed = true;
        while up_changed {
            up_changed = false;
            let current: Vec<String> = standalone_closure.iter().cloned().collect();
            for m in current {
                if let Some(spec) = standalone_all.get(&m) {
                    for imp in &spec.imports {
                        if standalone_all.contains_key(imp)
                            && standalone_closure.insert(imp.clone())
                        {
                            up_changed = true;
                        }
                    }
                }
            }
        }
        let files: Vec<PathBuf> = dag_closure
            .iter()
            .filter_map(|m| dag.nodes.get(m).map(|n| n.src_path.clone()))
            .collect();
        let standalone_specs =
            topologically_order_standalone_modules(&standalone_all, &standalone_closure)?;
        Ok(ProjectDependentClosure {
            cfg,
            dag: Some(dag),
            dag_seeds,
            lake_seeds,
            edited_dag_modules,
            deleted_modules: deleted,
            dag_modules: Some(dag_closure.into_iter().collect()),
            dag_files: Some(files),
            standalone_all,
            standalone_modules: standalone_specs,
        })
    } else {
        let standalone_closure: std::collections::BTreeSet<String> =
            standalone_all.keys().cloned().collect();
        let standalone_specs =
            topologically_order_standalone_modules(&standalone_all, &standalone_closure)?;
        Ok(ProjectDependentClosure {
            cfg,
            dag: None,
            dag_seeds,
            lake_seeds,
            edited_dag_modules: Vec::new(),
            deleted_modules: deleted,
            dag_modules: None,
            dag_files: None,
            standalone_all,
            standalone_modules: standalone_specs,
        })
    }
}

pub(super) fn topologically_order_standalone_modules(
    all_standalone: &BTreeMap<String, StandaloneModuleSpec>,
    selected: &std::collections::BTreeSet<String>,
) -> Result<Vec<StandaloneModuleSpec>> {
    let mut remaining: BTreeMap<String, StandaloneModuleSpec> = selected
        .iter()
        .filter_map(|m| all_standalone.get(m).map(|s| (m.clone(), s.clone())))
        .collect();
    let mut ordered = Vec::with_capacity(remaining.len());
    while !remaining.is_empty() {
        let ready: Vec<String> = remaining
            .iter()
            .filter(|(name, spec)| {
                !spec
                    .imports
                    .iter()
                    .any(|dep| dep != *name && remaining.contains_key(dep))
            })
            .map(|(name, _)| name.clone())
            .collect();
        anyhow::ensure!(
            !ready.is_empty(),
            "Module import cycle detected among standalone Lean files: {:?}",
            remaining.keys().collect::<Vec<_>>()
        );
        for name in ready {
            let spec = remaining.remove(&name).expect("ready module present");
            anyhow::ensure!(
                !spec.imports.iter().any(|dep| dep == &spec.module_name),
                "Module import cycle detected: {} -> {}",
                spec.module_name,
                spec.module_name
            );
            ordered.push(spec);
        }
    }
    Ok(ordered)
}

pub struct StandaloneOleanOverlay {
    pub olean_dir: PathBuf,
    pub(super) _scratch: crate::check::PrivateScratchDir,
}

/// Stage one package build artifact into the standalone re-check staging tree.
/// `allow_hardlink` is false when `.lake` link counts and `ctime` must stay
/// untouched (`--no-auto-worktree-link` worktrees).
pub(super) fn stage_artifact_link(
    src: &Path,
    dst: &Path,
    allow_hardlink: bool,
) -> std::io::Result<()> {
    if allow_hardlink && fs::hard_link(src, dst).is_ok() {
        return Ok(());
    }
    // Never fall back to a byte copy of package artifacts (#440): a staging dir
    // on another filesystem (tmpfs) failed every hard link and silently copied
    // the whole dependency `.olean` tree into /dev/shm (6.4 GB of Mathlib,
    // charged to the cgroup). A symlink costs no bytes and leaves the source's
    // link count and `ctime` untouched, which also covers the
    // `.lake`-preserving (`allow_hardlink == false`) case.
    #[cfg(unix)]
    if src.is_absolute() {
        return std::os::unix::fs::symlink(src, dst);
    }
    fs::copy(src, dst).map(|_| ())
}

/// Budgeted timeout for the standalone re-check `lean` invocations (#441):
/// `TURBO_LEAN_MODULE_TIMEOUT_SECS` (trusted default 1800 s when no compile
/// history is recorded, per #437; clamped to [15, 600] in untrusted mode),
/// the same budget every other per-module compile honors, instead of a
/// hard-coded 300 s that killed legitimate long modules after VERIFIED.
pub(super) fn standalone_lean_timeout_from(
    raw_env: Option<&str>,
    is_untrusted: bool,
) -> std::time::Duration {
    std::time::Duration::from_secs(crate::module_builder::module_compile_timeout_secs_from(
        raw_env,
        is_untrusted,
    ))
}

/// Map a path relative to a package's `lib/lean` build dir to its
/// module-relative base path when it carries a staged-artifact suffix the
/// standalone re-check tree merges.
pub(super) fn standalone_merge_rel_base(rel: &str) -> Option<String> {
    rel.strip_suffix(".olean.server")
        .or_else(|| rel.strip_suffix(".olean.private"))
        .or_else(|| rel.strip_suffix(".olean"))
        .or_else(|| rel.strip_suffix(".ilean"))
        // Lean 4.31 module-system imports also read `<Module>.ir`; without it
        // the re-check fails `missing IR data file for module ...` (#442).
        .or_else(|| rel.strip_suffix(".ir"))
        .map(String::from)
}

fn standalone_lean_timeout(is_untrusted: bool) -> std::time::Duration {
    standalone_lean_timeout_from(
        std::env::var("TURBO_LEAN_MODULE_TIMEOUT_SECS")
            .ok()
            .as_deref(),
        is_untrusted,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_and_audit_standalone_modules(
    store_opt: Option<&TurboStore>,
    canon_dir: &Path,
    standalone_modules: &[StandaloneModuleSpec],
    is_untrusted: bool,
    verified_target_modules: Option<&HashSet<String>>,
    rev: Option<&str>,
    retain_oleans: bool,
    allow_sorry: bool,
) -> Result<(Vec<PathBuf>, Option<StandaloneOleanOverlay>)> {
    if standalone_modules.is_empty() {
        return Ok((Vec::new(), None));
    }
    let mut ephemeral_store_dir: Option<PathBuf> = None;
    struct EphemeralDirGuard(Option<PathBuf>);
    impl Drop for EphemeralDirGuard {
        fn drop(&mut self) {
            if let Some(ref p) = self.0 {
                let _ = fs::remove_dir_all(p);
            }
        }
    }
    let owned_store: Option<TurboStore> = if store_opt.is_none() {
        let dir = std::env::temp_dir().join(format!(
            "turbo_standalone_store_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir)?;
        ephemeral_store_dir = Some(dir.clone());
        Some(TurboStore::open(Some(&dir))?)
    } else {
        None
    };
    let _ephemeral_guard = EphemeralDirGuard(ephemeral_store_dir);
    let store: &TurboStore = match store_opt {
        Some(s) => s,
        None => owned_store.as_ref().expect("owned store initialized"),
    };

    let cfg = crate::module_builder::resolve_project_config_with_trust(canon_dir, is_untrusted)?;
    let standalone_names: HashSet<&str> = standalone_modules
        .iter()
        .map(|s| s.module_name.as_str())
        .collect();
    let standalone_files: Vec<PathBuf> = standalone_modules
        .iter()
        .map(|s| s.src_path.clone())
        .collect();

    if !is_untrusted {
        let mut target_imports: Vec<String> = Vec::new();
        for spec in standalone_modules {
            for imp in &spec.imports {
                if standalone_names.contains(imp.as_str()) {
                    continue;
                }
                if crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, imp)
                    .is_some()
                    || cfg.dep_pkgs.iter().any(|dp| {
                        crate::module_builder::resolve_module_in_package(dp, false, imp).is_some()
                    })
                {
                    target_imports.push(imp.clone());
                }
            }
        }
        target_imports.sort();
        target_imports.dedup();
        if worktree_auto_link_disabled(canon_dir) {
            ensure_project_imports_fresh_for_check(canon_dir, &standalone_files)?;
        } else {
            ensure_project_imports_fresh_for_check(canon_dir, &standalone_files)?;
            let lib_lean_dir = canon_dir.join(".lake/build/lib/lean");
            let missing_target_imports: Vec<String> = target_imports
                .iter()
                .filter(|m| {
                    let rel = crate::module_builder::module_name_to_rel_slash(m);
                    if let Some(spec) =
                        crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, m)
                    {
                        return !spec
                            .build_lib_lean_dir
                            .join(format!("{}.olean", rel))
                            .is_file();
                    }
                    for dp in &cfg.dep_pkgs {
                        if let Some(spec) =
                            crate::module_builder::resolve_module_in_package(dp, false, m)
                        {
                            return !spec
                                .build_lib_lean_dir
                                .join(format!("{}.olean", rel))
                                .is_file();
                        }
                    }
                    !lib_lean_dir.join(format!("{}.olean", rel)).is_file()
                })
                .cloned()
                .collect();
            if !missing_target_imports.is_empty() {
                let targets = lake_refresh_targets(canon_dir, &missing_target_imports);
                lake_build_modules(canon_dir, &targets, rev)?;
            }
        }
        if allow_sorry {
            let mut allowed = splitter::allowed_axioms();
            if !allowed.iter().any(|a| a == "sorryAx") {
                allowed.push("sorryAx".to_string());
            }
            crate::module_builder::ensure_imported_oleans_replayed_with_roots_and_axioms(
                store,
                canon_dir,
                &standalone_files,
                &target_imports,
                &allowed,
            )?;
        } else {
            ensure_modules_and_imports_replayed(
                store,
                canon_dir,
                &standalone_files,
                &target_imports,
            )?;
        }
    }

    // Elaborate standalone modules in topological order into an isolated staging directory outside `.lake`
    // (preserving `--no-auto-worktree-link` worktrees) and run Stage 1C / kernel replay over the outputs.
    let staging_base = store.fast_staging_dir();
    fs::create_dir_all(&staging_base)?;
    let scratch = crate::check::PrivateScratchDir::create(&staging_base, "standalone_recheck")?;
    let staging_dir = scratch
        .path
        .canonicalize()
        .unwrap_or_else(|_| scratch.path.clone());
    let olean_out_dir = staging_dir.join("oleans");
    fs::create_dir_all(&olean_out_dir)?;

    // Populate `olean_out_dir` with hard links (falling back to copies; always copying when
    // `preserve_lake` is active so `.lake` link counts and `ctime` stay untouched) of target-owned
    // `.olean` files from root/dependency `.lake/build/lib/lean` directories so `olean_out_dir` can
    // sit FIRST on `LEAN_PATH`. In Lean 4's `SearchPath.findWithExt`, a matching top-level subdirectory
    // (e.g. `TurboLean/` in `.lake/build/lib/lean`) pins module resolution (`TurboLean.olean` AND
    // `TurboLean.Spec`) to the first directory containing either `TurboLean/` or `TurboLean.olean`.
    // Merging target-owned `.olean`s into `olean_out_dir` lets both `TurboLean.olean` and
    // `TurboLean/Spec.olean` resolve cleanly without touching `.lake` (preserving
    // `--no-auto-worktree-link` snapshots) while never copying unverified non-target `.olean`s.
    let preserve_lake = worktree_auto_link_disabled(canon_dir);
    let merge_pkg_oleans = |pkg: &crate::module_builder::PackageConfig,
                            is_root: bool,
                            dst_dir: &Path|
     -> Result<()> {
        let pkg_preserve_lake = preserve_lake || worktree_auto_link_disabled(&pkg.pkg_root);
        let src_dir = pkg.pkg_root.join(&pkg.build_dir).join(&pkg.lean_lib_dir);
        if !src_dir.is_dir() {
            return Ok(());
        }
        let mut stack = vec![(src_dir.clone(), dst_dir.to_path_buf())];
        while let Some((cur_src, cur_dst)) = stack.pop() {
            let Ok(rd) = fs::read_dir(&cur_src) else {
                continue;
            };
            for entry in rd.flatten() {
                let p = entry.path();
                let Ok(meta) = fs::symlink_metadata(&p) else {
                    continue;
                };
                if meta.file_type().is_symlink() {
                    continue;
                }
                let dst_p = cur_dst.join(entry.file_name());
                if meta.file_type().is_dir() {
                    stack.push((p, dst_p));
                } else if meta.file_type().is_file() {
                    let base_rel = if let Ok(r) = p.strip_prefix(&src_dir) {
                        standalone_merge_rel_base(&r.to_string_lossy())
                    } else {
                        None
                    };
                    let Some(rel_no_ext) = base_rel else {
                        continue;
                    };
                    let mod_name = crate::module_builder::format_lean_module_name_from_parts(
                        Path::new(&rel_no_ext)
                            .components()
                            .filter_map(|c| c.as_os_str().to_str()),
                    );
                    if mod_name.is_empty()
                        || standalone_names.contains(mod_name.as_str())
                        || crate::module_builder::resolve_module_in_package(pkg, is_root, &mod_name)
                            .is_none()
                        || (is_untrusted
                            && !verified_target_modules
                                .is_some_and(|allowed| allowed.contains(mod_name.as_str())))
                    {
                        continue;
                    }
                    if dst_p.exists() {
                        continue;
                    }
                    if let Some(parent) = dst_p.parent() {
                        fs::create_dir_all(parent)?;
                    }
                    stage_artifact_link(&p, &dst_p, !pkg_preserve_lake)?;
                }
            }
        }
        Ok(())
    };
    merge_pkg_oleans(&cfg.root_pkg, true, &olean_out_dir)?;
    for dp in &cfg.dep_pkgs {
        merge_pkg_oleans(dp, false, &olean_out_dir)?;
    }

    let (base_lp, ld_library_path_env) =
        crate::module_builder::build_lean_search_path(&cfg, is_untrusted);
    let combined_lp = if base_lp.is_empty() {
        olean_out_dir.to_string_lossy().to_string()
    } else {
        format!("{}:{}", olean_out_dir.display(), base_lp)
    };

    if is_untrusted {
        let bwrap_path = crate::module_builder::probe_bwrap_sandbox(canon_dir).ok_or_else(|| {
            anyhow::anyhow!(
                "Untrusted standalone module verification requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
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
        crate::module_builder::validate_untrusted_sandbox_search_paths(
            &cfg,
            tc_prefix,
            &base_lp,
            &ld_library_path_env,
        )?;
        for (idx, spec) in standalone_modules.iter().enumerate() {
            let src_text = fs::read_to_string(&spec.src_path)?;
            let split = splitter::split_lean_source(&src_text, &[]);
            anyhow::ensure!(
                !split.hygiene.has_checking_weakening,
                "Soundness hygiene violation in {}: {:?}",
                spec.src_path.display(),
                split.hygiene.disallowed_items()
            );
            anyhow::ensure!(
                !split.hygiene.native_violation(),
                "[TurboLean.KernelGate] native_decide/bv_decide in {} requires the base project's axiom allowlist",
                spec.src_path.display()
            );
            let file_args = crate::module_builder::resolve_file_lean_args_in_package(
                &cfg.root_pkg,
                &spec.src_path,
            );
            crate::module_builder::validate_lean_args(&file_args)?;

            let work_dir = staging_dir.join(format!("work_{idx}"));
            fs::create_dir_all(&work_dir)?;
            let rel_slash = crate::module_builder::module_name_to_rel_slash(&spec.module_name);
            let staged_olean = work_dir.join(format!("{}.olean", rel_slash));
            if let Some(parent) = staged_olean.parent() {
                fs::create_dir_all(parent)?;
            }

            let mut cmd = Command::new(&bwrap_path);
            cmd.args([
                "--unshare-all",
                "--new-session",
                "--die-with-parent",
                "--clearenv",
                "--setenv",
                "PATH",
                "/usr/bin:/bin",
                "--setenv",
                "LEAN_PATH",
                &combined_lp,
                "--setenv",
                "LEAN_STACK_SIZE_KB",
                "262144",
            ]);
            if !ld_library_path_env.is_empty() {
                cmd.args(["--setenv", "LD_LIBRARY_PATH", &ld_library_path_env]);
            }
            cmd.args(["--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp"]);
            for sys_p in [
                "/usr",
                "/bin",
                "/lib",
                "/lib64",
                "/etc/ld.so.cache",
                "/etc/localtime",
            ] {
                cmd.args(["--ro-bind-try", sys_p, sys_p]);
            }
            cmd.arg("--ro-bind").arg(tc_prefix).arg(tc_prefix);
            cmd.arg("--ro-bind")
                .arg(&cfg.root_pkg.pkg_root)
                .arg(&cfg.root_pkg.pkg_root);
            for dp in &cfg.dep_pkgs {
                if !dp.pkg_root.starts_with(&cfg.root_pkg.pkg_root) {
                    cmd.arg("--ro-bind").arg(&dp.pkg_root).arg(&dp.pkg_root);
                }
            }
            cmd.arg("--ro-bind").arg(&olean_out_dir).arg(&olean_out_dir);
            cmd.arg("--bind").arg(&work_dir).arg(&work_dir);
            cmd.arg("--chdir").arg(&cfg.root_pkg.pkg_root);
            cmd.arg(&cfg.lean_bin);
            crate::module_builder::scrub_untrusted_env(&mut cmd);
            cmd.args(["-M", "4096"]);
            for arg in crate::module_builder::filter_allowed_lean_args(&file_args) {
                cmd.arg(arg);
            }
            cmd.arg("-Dwarn.sorry=true")
                .arg("-Ddebug.skipKernelTC=false")
                .arg(&spec.src_path)
                .arg("-R")
                .arg(&spec.src_root)
                .arg("-o")
                .arg(&staged_olean);

            let out = crate::module_builder::run_command_with_timeout(
                &mut cmd,
                standalone_lean_timeout(is_untrusted),
                true,
            )?;
            if !out.status.success() {
                anyhow::bail!(
                    "Untrusted standalone Lean module `{}` failed compilation:\n{}\n{}",
                    spec.module_name,
                    String::from_utf8_lossy(&out.stdout),
                    String::from_utf8_lossy(&out.stderr)
                );
            }
            let stdout_str = String::from_utf8_lossy(&out.stdout);
            let stderr_str = String::from_utf8_lossy(&out.stderr);
            if stdout_str.contains("declaration uses ") || stderr_str.contains("declaration uses ")
            {
                anyhow::bail!(
                    "Untrusted standalone module `{}` rejected due to `sorry` axiom usage",
                    spec.module_name
                );
            }
            let meta = fs::symlink_metadata(&staged_olean).with_context(|| {
                format!(
                    "Untrusted standalone compilation produced no `.olean` for `{}`",
                    spec.module_name
                )
            })?;
            anyhow::ensure!(
                !meta.file_type().is_symlink() && meta.file_type().is_file() && meta.len() > 0,
                "Untrusted standalone `.olean` for `{}` is missing, empty, or a symlink",
                spec.module_name
            );
            let published_olean = olean_out_dir.join(format!("{}.olean", rel_slash));
            let _ = fs::remove_file(&published_olean);
            if let Some(parent) = published_olean.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::copy(&staged_olean, &published_olean)?;
            for suffix in [".olean.server", ".olean.private"] {
                let side_dst = olean_out_dir.join(format!("{}{}", rel_slash, suffix));
                let _ = fs::remove_file(&side_dst);
                let side_src = work_dir.join(format!("{}{}", rel_slash, suffix));
                if let Ok(sm) = fs::symlink_metadata(&side_src) {
                    if !sm.file_type().is_symlink() && sm.file_type().is_file() {
                        let _ = fs::copy(&side_src, &side_dst);
                    }
                }
            }
        }
        let mod_names: Vec<String> = standalone_modules
            .iter()
            .map(|s| s.module_name.clone())
            .collect();
        crate::zygote::audit_compiled_modules_with_zygote(
            store,
            &cfg,
            &mod_names,
            &combined_lp,
            std::slice::from_ref(&olean_out_dir),
            true,
        )
        .context(
            "Untrusted standalone module `.olean` failed in-kernel soundness & replay audit",
        )?;
    } else {
        let mut env_vars = HashMap::new();
        env_vars.insert("LEAN_PATH".to_string(), combined_lp.clone());
        if !ld_library_path_env.is_empty() {
            env_vars.insert("LD_LIBRARY_PATH".to_string(), ld_library_path_env);
        }
        let allowed = splitter::allowed_axioms();
        let assurance = crate::module_builder::discover_trusted_assurance_surface(
            canon_dir,
            &cfg.root_pkg,
            &allowed,
        );
        for spec in standalone_modules {
            let src_text = fs::read_to_string(&spec.src_path)?;
            let split = splitter::split_lean_source(&src_text, &[]);
            let canon_spec = spec
                .src_path
                .canonicalize()
                .unwrap_or_else(|_| spec.src_path.clone());
            let is_assurance = !split.hygiene.has_checking_weakening_option
                && split.shards.is_empty()
                && assurance.canon_paths.contains(&canon_spec);
            anyhow::ensure!(
                !split.hygiene.has_checking_weakening || is_assurance,
                "Soundness hygiene violation in {}: {:?}",
                spec.src_path.display(),
                split.hygiene.disallowed_items_under(&allowed)
            );
            anyhow::ensure!(
                !split.hygiene.native_violation_under(&allowed),
                "[TurboLean.KernelGate] native_decide/bv_decide in {} requires the base project's axiom allowlist",
                spec.src_path.display()
            );
            let file_args = crate::module_builder::resolve_file_lean_args_in_package(
                &cfg.root_pkg,
                &spec.src_path,
            );
            crate::module_builder::validate_lean_args(&file_args)?;

            let rel_slash = crate::module_builder::module_name_to_rel_slash(&spec.module_name);
            let published_olean = olean_out_dir.join(format!("{}.olean", rel_slash));
            for suffix in [".olean", ".olean.server", ".olean.private", ".ilean"] {
                let _ = fs::remove_file(olean_out_dir.join(format!("{}{}", rel_slash, suffix)));
            }
            if let Some(parent) = published_olean.parent() {
                fs::create_dir_all(parent)?;
            }
            let mut cmd = crate::module_builder::verifier_command(&cfg.lean_bin, &env_vars)?;
            cmd.current_dir(canon_dir);
            for arg in crate::module_builder::filter_allowed_lean_args(&file_args) {
                cmd.arg(arg);
            }
            cmd.arg(if allow_sorry {
                "-Dwarn.sorry=false"
            } else {
                "-Dwarn.sorry=true"
            })
            .arg("-Ddebug.skipKernelTC=false")
            .arg(&spec.src_path)
            .arg("-R")
            .arg(&spec.src_root)
            .arg("-o")
            .arg(&published_olean);
            let out = crate::module_builder::run_command_with_timeout(
                &mut cmd,
                standalone_lean_timeout(is_untrusted),
                false,
            )?;
            if !out.status.success() {
                anyhow::bail!(
                    "Standalone Lean module `{}` failed compilation:\n{}\n{}",
                    spec.module_name,
                    String::from_utf8_lossy(&out.stdout),
                    String::from_utf8_lossy(&out.stderr)
                );
            }
            let stdout_str = String::from_utf8_lossy(&out.stdout);
            let stderr_str = String::from_utf8_lossy(&out.stderr);
            if !allow_sorry
                && (stdout_str.contains("declaration uses ")
                    || stderr_str.contains("declaration uses "))
            {
                anyhow::bail!(
                    "Standalone module `{}` rejected due to `sorry` axiom usage",
                    spec.module_name
                );
            }
            let meta = fs::symlink_metadata(&published_olean).with_context(|| {
                format!(
                    "Standalone compilation produced no `.olean` for `{}`",
                    spec.module_name
                )
            })?;
            anyhow::ensure!(
                meta.file_type().is_file() && meta.len() > 0,
                "Standalone `.olean` for `{}` is missing or empty",
                spec.module_name
            );
        }
        let mod_names: Vec<String> = standalone_modules
            .iter()
            .filter(|s| !assurance.mod_names.contains(&s.module_name))
            .map(|s| s.module_name.clone())
            .collect();
        if !mod_names.is_empty() {
            crate::zygote::audit_compiled_modules_with_zygote_options(
                store,
                &cfg,
                &mod_names,
                &combined_lp,
                std::slice::from_ref(&olean_out_dir),
                false,
                allow_sorry,
            )
            .context("Standalone module `.olean` failed in-kernel soundness & replay audit")?;
        }
    }

    let overlay = if retain_oleans {
        Some(StandaloneOleanOverlay {
            olean_dir: olean_out_dir,
            _scratch: scratch,
        })
    } else {
        None
    };

    Ok((standalone_files, overlay))
}

/// After a non-local edit, re-check with Lake the edited modules and every project module that
/// imports them, directly or not (Lake replays unchanged imports from its build or artifact
/// cache). Without a module graph it re-checks every `lean_lib`; without a Lake config it
/// refuses to pass. Returns the number of modules re-checked (0: all libraries).
pub(crate) fn recheck_dependents_if_nonlocal(
    store: &TurboStore,
    canon_dir: &Path,
    target: &Path,
) -> Result<()> {
    recheck_dependents_if_nonlocal_with_options(store, canon_dir, target, false)
}

pub(crate) fn recheck_dependents_if_nonlocal_with_options(
    store: &TurboStore,
    canon_dir: &Path,
    target: &Path,
    allow_sorry: bool,
) -> Result<()> {
    recheck_dependents_if_nonlocal_for_check(store, canon_dir, target, allow_sorry, false, false)
}

pub(crate) fn recheck_dependents_if_nonlocal_for_check(
    store: &TurboStore,
    canon_dir: &Path,
    target: &Path,
    allow_sorry: bool,
    decl_mode: bool,
    decl_with_sorry_siblings: bool,
) -> Result<()> {
    let lake_root = target.canonicalize().ok().and_then(|f| {
        f.ancestors()
            .find(|a| has_lake_config(a) || a.join("lake-manifest.json").is_file())
            .map(PathBuf::from)
    });
    let dir = if has_lake_config(canon_dir) || canon_dir.join("lake-manifest.json").is_file() {
        canon_dir.to_path_buf()
    } else {
        lake_root.unwrap_or_else(|| canon_dir.to_path_buf())
    };
    // An empty project dir means the working directory (`current_dir("")` cannot spawn Lake).
    let dir = Path::new(".").join(dir);
    let dir = dir.canonicalize().unwrap_or(dir);
    let _ = crate::module_builder::try_project_lake_inputs_tag(&dir)?;
    let file = Some(dir.join(target))
        .filter(|f| f.exists())
        .unwrap_or_else(|| target.to_path_buf());
    let files = collect_project_lean_files(&dir, false, Some(&file));
    let edits = nonlocal_edits(&files, "HEAD");
    if !edits.is_empty() {
        if decl_mode && has_lake_config(&dir) {
            if let Ok(closure) = compute_project_dependent_closure(&dir, &edits, false) {
                let canon_target = file.canonicalize().unwrap_or_else(|_| file.clone());
                let has_strict_reverse_dependent = match closure.dag_files.as_ref() {
                    Some(df) => {
                        df.iter()
                            .any(|p| p.canonicalize().unwrap_or_else(|_| p.clone()) != canon_target)
                            || closure.standalone_modules.iter().any(|s| {
                                s.src_path
                                    .canonicalize()
                                    .unwrap_or_else(|_| s.src_path.clone())
                                    != canon_target
                            })
                    }
                    None => true,
                };
                if !has_strict_reverse_dependent {
                    if decl_with_sorry_siblings || allow_sorry {
                        let mut fail_seeds = vec![file.clone()];
                        for e in &edits {
                            fail_seeds.push(dir.join(e));
                        }
                        purge_sorry_artifacts_after_allow_sorry_failure(&dir, &fail_seeds);
                    }
                    return Ok(());
                }
            }
        }
        eprintln!(
            "[turbo-lean] non-local edit in {}: re-checking dependents with Lake",
            edits.join(", ")
        );
        let recheck_allow_sorry = allow_sorry || decl_with_sorry_siblings;
        let recheck_res = if recheck_allow_sorry {
            lake_recheck_dependents_with_store_and_options(
                None,
                &dir,
                &edits,
                None,
                !allow_sorry && decl_with_sorry_siblings,
                true,
            )
        } else {
            lake_recheck_dependents_with_store(Some(store), &dir, &edits, None, false)
        };
        if recheck_res.is_err() && recheck_allow_sorry {
            let mut fail_seeds = vec![file.clone()];
            for e in &edits {
                fail_seeds.push(dir.join(e));
            }
            purge_sorry_artifacts_after_allow_sorry_failure(&dir, &fail_seeds);
        }
        let (n, rechecked_files, rechecked_mods, _overlay) = recheck_res?;
        if recheck_allow_sorry {
            // Replay only clean modules; purge Lake `.olean` / `.ir` / `.c` artifacts and manifest
            // entries for any module whose source contains `sorry` (or transitively imports a
            // sorry-bearing module across the full DAG + standalone graph, including non-root `srcDir`).
            let mut seed_files = rechecked_files.clone();
            seed_files.push(file.clone());
            for e in &edits {
                seed_files.push(dir.join(e));
            }
            let dependent_audit = (|| -> Result<()> {
                if allow_sorry || !decl_with_sorry_siblings {
                    return Ok(());
                }
                let cfg = crate::module_builder::resolve_project_config(&dir)?;
                let canon_target = file.canonicalize().unwrap_or_else(|_| file.clone());
                let assurance = crate::module_builder::discover_trusted_assurance_surface(
                    &dir,
                    &cfg.root_pkg,
                    &splitter::allowed_axioms(),
                );
                let modules: Vec<_> = rechecked_files
                    .iter()
                    .zip(&rechecked_mods)
                    .filter(|(path, module)| {
                        let canon = path.canonicalize().unwrap_or_else(|_| (*path).clone());
                        canon != canon_target
                            && !assurance.canon_paths.contains(&canon)
                            && !assurance.mod_names.contains(*module)
                    })
                    .map(|(_, module)| module.clone())
                    .collect();
                if modules.is_empty() {
                    return Ok(());
                }
                let (mut lean_path, _) = crate::module_builder::build_lean_search_path(&cfg, false);
                let extra: Vec<_> = _overlay
                    .iter()
                    .map(|overlay| overlay.olean_dir.clone())
                    .collect();
                if let Some(path) = extra.first() {
                    lean_path = format!("{}:{lean_path}", path.display());
                }
                crate::zygote::audit_compiled_modules_with_zygote(
                    store, &cfg, &modules, &lean_path, &extra, false,
                )
                .context("Dependent modules failed strict soundness audit")
            })();
            let sorry_mod_set =
                purge_workspace_sorry_artifacts_and_manifest(&dir, &seed_files, &rechecked_mods);
            dependent_audit?;
            if !allow_sorry && decl_with_sorry_siblings {
                let canon_target = file.canonicalize().unwrap_or_else(|_| file.clone());
                let assurance = crate::module_builder::optional_package_config(&dir)
                    .ok()
                    .flatten()
                    .map(|pkg| {
                        let allowed = splitter::allowed_axioms();
                        crate::module_builder::discover_trusted_assurance_surface(
                            &dir, &pkg, &allowed,
                        )
                    })
                    .unwrap_or_default();
                for (rf, rm) in rechecked_files.iter().zip(rechecked_mods.iter()) {
                    let canon_rf = rf.canonicalize().unwrap_or_else(|_| rf.clone());
                    if canon_rf == canon_target
                        || assurance.canon_paths.contains(&canon_rf)
                        || assurance.mod_names.contains(rm)
                    {
                        continue;
                    }
                    if let Ok(rf_src) = fs::read_to_string(rf) {
                        let hyg = splitter::audit_hygiene(&splitter::strip_lean_comments(&rf_src));
                        if !hyg.is_clean_or_deferred_to_kernel_gate() {
                            let violations: Vec<_> = hyg
                                .disallowed_items()
                                .into_iter()
                                .filter(|v| {
                                    !splitter::HygieneReport {
                                        flagged_items: vec![v.clone()],
                                        ..Default::default()
                                    }
                                    .is_clean_or_deferred_to_kernel_gate()
                                })
                                .collect();
                            anyhow::ensure!(
                                violations.is_empty(),
                                "Soundness hygiene violation in dependent {}: {}",
                                rf.display(),
                                violations.join(", ")
                            );
                        }
                        anyhow::ensure!(
                            !hyg.has_sorry,
                            "Dependent module `{}` ({}) contains `sorry`",
                            rm,
                            rf.display()
                        );
                    }
                }
            }
            let mut clean_files = Vec::new();
            let mut clean_mods = Vec::new();
            for (rf, rm) in rechecked_files.iter().zip(rechecked_mods.iter()) {
                if !sorry_mod_set.contains(rm) {
                    clean_files.push(rf.clone());
                    clean_mods.push(rm.clone());
                }
            }
            if !clean_files.is_empty() {
                ensure_modules_and_imports_replayed(store, &dir, &clean_files, &clean_mods)?;
            }
        } else {
            let assurance = crate::module_builder::optional_package_config(&dir)
                .ok()
                .flatten()
                .map(|pkg| {
                    let allowed = splitter::allowed_axioms();
                    crate::module_builder::discover_trusted_assurance_surface(&dir, &pkg, &allowed)
                })
                .unwrap_or_default();
            let mut replay_files = Vec::with_capacity(rechecked_files.len());
            let mut replay_mods = Vec::with_capacity(rechecked_mods.len());
            for (rf, rm) in rechecked_files.iter().zip(rechecked_mods.iter()) {
                let canon_rf = rf.canonicalize().unwrap_or_else(|_| rf.clone());
                if !assurance.canon_paths.contains(&canon_rf) && !assurance.mod_names.contains(rm) {
                    replay_files.push(rf.clone());
                    replay_mods.push(rm.clone());
                }
            }
            if !replay_files.is_empty() {
                ensure_modules_and_imports_replayed(store, &dir, &replay_files, &replay_mods)?;
            }
        }
        eprintln!(
            "[turbo-lean] Lake re-checked {} modules (0: all libraries)",
            n
        );
    } else if lake_inputs_changed_since_manifest(&dir) {
        if let Ok(cfg) = crate::module_builder::resolve_project_config(&dir) {
            let root_base = crate::module_builder::pkg_target_base_name(&cfg.root_pkg);
            let allowed = splitter::allowed_axioms();
            let assurance = crate::module_builder::discover_trusted_assurance_surface(
                &dir,
                &cfg.root_pkg,
                &allowed,
            );
            let target_canon = file.canonicalize().unwrap_or_else(|_| file.clone());
            let target_in_assurance = assurance
                .canon_paths
                .iter()
                .any(|ap| ap == &target_canon || ap.starts_with(&target_canon));
            let keep_root_lib = |lib: &crate::module_builder::LeanLibConfig| -> bool {
                target_in_assurance || !assurance.lib_names.contains(&lib.name)
            };
            let keep_root_exe = |exe: &crate::module_builder::LeanExeConfig| -> bool {
                target_in_assurance || !assurance.exe_names.contains(&exe.name)
            };
            let mut input_libs: Vec<String> = Vec::new();
            let mut input_exes: Vec<String> = Vec::new();
            let mut input_exe_dag_seeds: Vec<String> = Vec::new();
            if !cfg.root_pkg.inputs.is_empty() {
                input_libs.extend(
                    cfg.root_pkg
                        .libs
                        .iter()
                        .filter(|l| !l.needs.is_empty() && keep_root_lib(l))
                        .map(|l| l.name.clone()),
                );
                for e in cfg
                    .root_pkg
                    .exes
                    .iter()
                    .filter(|e| !e.needs.is_empty() && keep_root_exe(e))
                {
                    input_exes.push(format!("@{}/{}:exe", root_base, e.name));
                    input_exe_dag_seeds.push(format!("@{}/{}:default", root_base, e.name));
                }
            }
            for dp in &cfg.dep_pkgs {
                if !dp.inputs.is_empty()
                    && crate::module_builder::dep_pkg_lake_targets_owned_by_project(&cfg, dp)
                {
                    let dp_base = crate::module_builder::pkg_target_base_name(dp);
                    input_libs.extend(
                        dp.libs
                            .iter()
                            .filter(|l| !l.needs.is_empty())
                            .map(|l| format!("{}/{}", dp_base, l.name)),
                    );
                    for e in dp.exes.iter().filter(|e| !e.needs.is_empty()) {
                        input_exes.push(format!("@{}/{}:exe", dp_base, e.name));
                        input_exe_dag_seeds.push(format!("@{}/{}:default", dp_base, e.name));
                    }
                }
            }
            input_libs.sort();
            input_libs.dedup();
            input_exes.sort();
            input_exes.dedup();
            input_exe_dag_seeds.sort();
            input_exe_dag_seeds.dedup();
            let has_pkg_inputs = !cfg.root_pkg.inputs.is_empty()
                || cfg.dep_pkgs.iter().any(|dp| !dp.inputs.is_empty());
            if has_pkg_inputs && has_lake_config(&dir) {
                let mut lib_seeds: Vec<String> = cfg
                    .root_pkg
                    .libs
                    .iter()
                    .filter(|l| keep_root_lib(l))
                    .map(|l| l.name.clone())
                    .collect();
                lib_seeds.extend(input_libs.iter().cloned());
                lib_seeds.sort();
                lib_seeds.dedup();

                let mut dag_seeds: Vec<String> = cfg
                    .root_pkg
                    .libs
                    .iter()
                    .filter(|l| keep_root_lib(l))
                    .map(|l| format!("@{}/{}", root_base, l.name))
                    .collect();
                dag_seeds.extend(input_libs.iter().cloned());
                dag_seeds.extend(
                    cfg.root_pkg
                        .exes
                        .iter()
                        .filter(|e| keep_root_exe(e))
                        .map(|e| format!("@{}/{}:default", root_base, e.name)),
                );
                dag_seeds.extend(input_exe_dag_seeds);
                dag_seeds.sort();
                dag_seeds.dedup();

                let mut lake_exe_seeds: Vec<String> = input_exes.clone();
                lake_exe_seeds.sort();
                lake_exe_seeds.dedup();

                let mut ordered_targets = input_libs.clone();
                let mut bypass_lake_cache = false;
                let closure_files: Vec<PathBuf>;
                let closure_mods: Vec<String>;
                if let Ok(dag) =
                    crate::module_builder::build_module_dag_with_trust(&cfg, &dag_seeds, false)
                {
                    let closure = input_closure_sweep_mods(&cfg, &dag);
                    closure_files = closure
                        .iter()
                        .filter_map(|m| dag.nodes.get(m).map(|n| n.src_path.clone()))
                        .collect();
                    closure_mods = closure.into_iter().collect();
                    for m in &closure_mods {
                        if let Some(spec) =
                            crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, m)
                                .or_else(|| {
                                    match crate::module_builder::resolve_import_site(&cfg, m) {
                                        crate::module_builder::ImportSite::Module(s) => Some(*s),
                                        _ => None,
                                    }
                                })
                        {
                            let has_target_needs =
                                !crate::module_builder::input_bearing_libs_for_module(&cfg, m)
                                    .is_empty()
                                    || !crate::module_builder::input_bearing_exes_for_module(
                                        &cfg, m,
                                    )
                                    .is_empty();
                            if !has_target_needs
                                && fs::read_to_string(&spec.src_path)
                                    .map(|s| crate::module_builder::source_uses_include_str(&s))
                                    .unwrap_or(false)
                                && crate::module_builder::spec_artifacts_purgeable_from_project_root(
                                    &cfg, &spec,
                                )
                            {
                                remove_spec_build_artifacts_checked(&spec)?;
                                bypass_lake_cache = true;
                            }
                        }
                    }
                    let all_fresh_on_disk = !bypass_lake_cache
                        && {
                            let mut fresh_cache =
                                crate::module_builder::LakeClosureCache::for_project(&cfg);
                            fresh_cache.allow_stale_manifest_hydration = true;
                            let mut all_ok = true;
                            for m in &closure_mods {
                                let spec_opt = crate::module_builder::resolve_module_in_package(
                                    &cfg.root_pkg,
                                    true,
                                    m,
                                )
                                .or_else(|| {
                                    match crate::module_builder::resolve_import_site(&cfg, m) {
                                        crate::module_builder::ImportSite::Module(s) => Some(*s),
                                        _ => None,
                                    }
                                });
                                let mod_ok = spec_opt.is_some_and(|spec| {
                                    let mut vis = HashSet::new();
                                    crate::module_builder::lake_closure_export_info(
                                        &cfg,
                                        &spec,
                                        false,
                                        &mut fresh_cache,
                                        &mut vis,
                                    )
                                    .is_some()
                                });
                                if !mod_ok {
                                    all_ok = false;
                                    break;
                                }
                            }
                            if all_ok {
                                let check_exes: Vec<String> =
                                    lake_refresh_targets_for_input_closure(&cfg, &closure_mods)
                                        .into_iter()
                                        .chain(input_exes.iter().cloned())
                                        .filter(|t| t.ends_with(":exe"))
                                        .collect();
                                if !check_exes.is_empty()
                                && !crate::module_builder::verify_project_native_and_c_sidecars_up_to_date(
                                    &cfg,
                                    &check_exes,
                                )
                            {
                                all_ok = false;
                            }
                            }
                            all_ok
                        };
                    if all_fresh_on_disk {
                        ordered_targets.clear();
                    } else {
                        for t in lake_refresh_targets_for_input_closure(&cfg, &closure_mods) {
                            if !ordered_targets.contains(&t) {
                                ordered_targets.push(t);
                            }
                        }
                        for t in input_exes {
                            if !ordered_targets.contains(&t) {
                                ordered_targets.push(t);
                            }
                        }
                    }
                } else {
                    for t in lib_seeds.into_iter().chain(lake_exe_seeds) {
                        if !ordered_targets.contains(&t) {
                            ordered_targets.push(t);
                        }
                    }
                    closure_files = collect_project_lean_files(&dir, false, None)
                        .into_iter()
                        .filter(|f| {
                            target_in_assurance
                                || !assurance
                                    .canon_paths
                                    .contains(&f.canonicalize().unwrap_or_else(|_| f.clone()))
                        })
                        .collect();
                    closure_mods = closure_files
                        .iter()
                        .filter_map(|f| f.strip_prefix(&dir).ok())
                        .map(|r| r.with_extension("").to_string_lossy().replace('/', "."))
                        .collect();
                }

                if !ordered_targets.is_empty() {
                    eprintln!(
                        "[turbo-lean] Lake file inputs changed: re-checking input-bearing targets and dependents ({}) with Lake",
                        ordered_targets.join(", ")
                    );
                    lake_build_modules_opts(&dir, &ordered_targets, None, bypass_lake_cache)?;
                }
                if allow_sorry {
                    let sorry_mod_set = purge_workspace_sorry_artifacts_and_manifest(
                        &dir,
                        &closure_files,
                        &closure_mods,
                    );
                    let mut clean_files = Vec::new();
                    let mut clean_mods = Vec::new();
                    for (rf, rm) in closure_files.iter().zip(closure_mods.iter()) {
                        if !sorry_mod_set.contains(rm) {
                            clean_files.push(rf.clone());
                            clean_mods.push(rm.clone());
                        }
                    }
                    if !clean_files.is_empty() {
                        ensure_modules_and_imports_replayed(
                            store,
                            &dir,
                            &clean_files,
                            &clean_mods,
                        )?;
                    }
                } else if !closure_files.is_empty() {
                    ensure_modules_and_imports_replayed(
                        store,
                        &dir,
                        &closure_files,
                        &closure_mods,
                    )?;
                }
                if allow_sorry
                    || worktree_auto_link_disabled(&dir)
                    || crate::module_builder::hydrate_project_traces_with_store(&dir, Some(store))
                        .is_err()
                {
                    let _ = fs::remove_file(verified_sources_manifest_path(&dir));
                    for dp in &cfg.dep_pkgs {
                        let _ = fs::remove_file(
                            dp.pkg_root
                                .join(&dp.build_dir)
                                .join(".turbo_verified_sources.json"),
                        );
                    }
                }
            }
        }
    } else if (allow_sorry || decl_with_sorry_siblings) && !worktree_auto_link_disabled(&dir) {
        // Even when `nonlocal_edits` is empty (e.g. a sorry-bearing upstream import was
        // already committed at `HEAD` and refreshed by `ensure_project_imports_fresh_for_check`),
        // purge any sorry-tainted workspace `.olean` / `.ir` / `.c` artifacts and manifest entries.
        let _ =
            purge_workspace_sorry_artifacts_and_manifest(&dir, std::slice::from_ref(&file), &[]);
    }
    Ok(())
}

pub(super) fn read_git_baseline_source(src_path: &Path, rev: &str) -> Option<String> {
    let name = src_path.file_name()?.to_string_lossy();
    let parent = src_path.parent().unwrap_or(Path::new("."));
    let mut git = crate::trusted_tools::git(parent).ok()?;
    git.arg("-C")
        .arg(parent)
        .args(["show", "--no-textconv", "--no-ext-diff"])
        .arg(format!("{}:./{}", rev, name))
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).into_owned())
}

pub(super) fn read_git_baseline_source_checked(
    src_path: &Path,
    rev: &str,
    explicit_rev: bool,
) -> Result<Option<String>> {
    let trimmed = rev.trim();
    anyhow::ensure!(
        !trimmed.is_empty() && !trimmed.starts_with('-'),
        "Invalid git revision `{rev}`"
    );
    let name = src_path
        .file_name()
        .context("Target path has no file name")?
        .to_string_lossy();
    let parent = src_path.parent().unwrap_or(Path::new("."));
    let run_git = |args: &[&str]| -> Result<std::process::Output> {
        crate::trusted_tools::git(parent)?
            .arg("-C")
            .arg(parent)
            .args(args)
            .output()
            .with_context(|| format!("Failed to invoke git in {}", parent.display()))
    };
    let rev_tree = format!("{trimmed}^{{tree}}");
    let verified = run_git(&["rev-parse", "--verify", "--end-of-options", &rev_tree]);
    match verified {
        Ok(out) if out.status.success() => {}
        Ok(out) => {
            if explicit_rev {
                let stderr = String::from_utf8_lossy(&out.stderr);
                let detail = stderr.trim();
                if detail.is_empty() {
                    anyhow::bail!("Invalid git revision `{rev}` in {}", parent.display());
                }
                anyhow::bail!(
                    "Invalid git revision `{rev}` in {}: {detail}",
                    parent.display()
                );
            }
            return Ok(None);
        }
        Err(e) => {
            if explicit_rev {
                return Err(e);
            }
            return Ok(None);
        }
    }
    let spec = format!("{trimmed}:./{name}");
    let shown = run_git(&["show", "--no-textconv", "--no-ext-diff", &spec])?;
    if shown.status.success() {
        return Ok(Some(String::from_utf8_lossy(&shown.stdout).into_owned()));
    }
    let named = run_git(&["rev-parse", "--verify", "-q", "--end-of-options", &spec])?;
    anyhow::ensure!(
        !named.status.success(),
        "Cannot read `{spec}` in {}: {}",
        parent.display(),
        String::from_utf8_lossy(&shown.stderr).trim()
    );
    Ok(None)
}

#[derive(Clone, Debug)]
pub(super) struct PreRebuildModuleBaseline {
    pub(super) full_dig: String,
    pub(super) export_dig: String,
    pub(super) meta_dig: String,
    pub(super) lake_export_info: Option<crate::module_builder::LakeModuleExportInfo>,
    pub(super) ir_pair_dig: Option<([u8; 32], Option<[u8; 32]>)>,
    pub(super) olean_pub_sig: crate::zygote::OleanPublicSignatureReply,
    pub(super) base_pub_sig_digest: Option<String>,
    pub(super) base_meta_sig_digest: Option<String>,
    pub(super) cur_pub_sig_digest: String,
    pub(super) cur_meta_sig_digest: String,
}

pub(super) fn read_module_ir_pair_digest(olean_path: &Path) -> Option<([u8; 32], Option<[u8; 32]>)> {
    let ir_path = olean_path.with_extension("ir");
    let ir_sig_path = PathBuf::from(format!("{}.sig", ir_path.display()));
    let ir_bytes = fs::read(&ir_path).ok()?;
    let need_sig = crate::module_builder::olean_requires_ir_sig(olean_path);
    let ir_sig = match fs::read(&ir_sig_path) {
        Ok(b) => Some(*blake3::hash(&b).as_bytes()),
        Err(_) if !need_sig => None,
        Err(_) => return None,
    };
    Some((*blake3::hash(&ir_bytes).as_bytes(), ir_sig))
}

#[derive(Clone, Copy, Debug, Default)]
pub(super) struct ModuleCutoffVerdict {
    pub(super) cuts_off_public: bool,
    pub(super) cuts_off_meta: bool,
}

pub(super) fn capture_pre_rebuild_module_baselines(
    store_root: &Path,
    cfg: &crate::module_builder::ProjectConfig,
    dag: &crate::module_builder::ModuleDag,
    edited_dag_modules: &[String],
    rev: Option<&str>,
    is_untrusted: bool,
) -> Option<HashMap<String, PreRebuildModuleBaseline>> {
    if edited_dag_modules.is_empty() {
        return None;
    }
    let (lean_path_env, _) = crate::module_builder::build_lean_search_path(cfg, is_untrusted);
    let mut pre_lake_memo = HashMap::new();
    let mut out = HashMap::new();
    for m in edited_dag_modules {
        let node = dag.nodes.get(m)?;
        if !node.is_module
            || node.precompile_modules
            || node.is_exe_target
            || node.needs_dynlib
            || !node.olean_path.is_file()
        {
            return None;
        }
        let cur_src = fs::read_to_string(&node.src_path).ok()?;
        let cur_sig = splitter::extract_public_signature(&cur_src);
        if !cur_sig.is_module
            || cur_sig
                .public_signature_digest
                .starts_with("pubsig-invalid:")
        {
            return None;
        }
        let (base_pub_sig_digest, base_meta_sig_digest) = if let Some(r) = rev {
            let base_src = read_git_baseline_source(&node.src_path, r)?;
            let base_sig = splitter::extract_public_signature(&base_src);
            if !base_sig.is_module
                || base_sig
                    .public_signature_digest
                    .starts_with("pubsig-invalid:")
                || base_sig.public_signature_digest != cur_sig.public_signature_digest
            {
                return None;
            }
            (
                Some(base_sig.public_signature_digest),
                Some(base_sig.meta_signature_digest),
            )
        } else {
            (None, None)
        };
        let tiers = crate::module_builder::compute_module_artifact_tier_digests_with_policy(
            &node.olean_path,
            true,
        )
        .ok()?;
        let ir_pair_dig = read_module_ir_pair_digest(&node.olean_path);
        let lake_export_info = {
            let mut visiting = HashSet::new();
            crate::module_builder::compute_lake_export_info(
                cfg,
                dag,
                node,
                m,
                &mut pre_lake_memo,
                &mut visiting,
            )
            .ok()
        };
        let olean_pub_sig = crate::zygote::read_module_public_signature_with_zygote(
            store_root,
            cfg,
            m,
            &lean_path_env,
            &[],
            is_untrusted,
        )
        .ok()?;
        if !olean_pub_sig.is_module {
            return None;
        }
        out.insert(
            m.clone(),
            PreRebuildModuleBaseline {
                full_dig: tiers.full,
                export_dig: tiers.dep_export,
                meta_dig: tiers.dep_meta,
                lake_export_info,
                ir_pair_dig,
                olean_pub_sig,
                base_pub_sig_digest,
                base_meta_sig_digest,
                cur_pub_sig_digest: cur_sig.public_signature_digest,
                cur_meta_sig_digest: cur_sig.meta_signature_digest,
            },
        );
    }
    Some(out)
}

pub(super) fn evaluate_post_rebuild_module_cutoffs(
    store_root: &Path,
    cfg: &crate::module_builder::ProjectConfig,
    dag: &crate::module_builder::ModuleDag,
    baselines: &HashMap<String, PreRebuildModuleBaseline>,
    is_untrusted: bool,
) -> HashMap<String, ModuleCutoffVerdict> {
    let (lean_path_env, _) = crate::module_builder::build_lean_search_path(cfg, is_untrusted);
    let mut verdicts = HashMap::new();
    for (m, pre) in baselines {
        let Some(node) = dag.nodes.get(m) else {
            continue;
        };
        let Ok(tiers) = crate::module_builder::compute_module_artifact_tier_digests_with_policy(
            &node.olean_path,
            true,
        ) else {
            continue;
        };
        let _ = &pre.export_dig;
        let Ok(post_pub_sig) = crate::zygote::read_module_public_signature_with_zygote(
            store_root,
            cfg,
            m,
            &lean_path_env,
            &[],
            is_untrusted,
        ) else {
            continue;
        };
        if post_pub_sig != pre.olean_pub_sig {
            continue;
        }
        let base_pub_ok = pre
            .base_pub_sig_digest
            .as_ref()
            .is_none_or(|b| b == &pre.cur_pub_sig_digest);
        if !base_pub_ok {
            continue;
        }
        let base_meta_ok = pre
            .base_meta_sig_digest
            .as_ref()
            .is_none_or(|b| b == &pre.cur_meta_sig_digest);
        let ir_pair_unchanged = match (
            pre.ir_pair_dig,
            read_module_ir_pair_digest(&node.olean_path),
        ) {
            (Some(pre_ir), Some(post_ir)) => pre_ir == post_ir,
            _ => false,
        };
        let export_exact = tiers.dep_export == pre.export_dig;
        let has_opaque_ext = pre.olean_pub_sig.has_opaque_ext || post_pub_sig.has_opaque_ext;
        let cuts_off_public = export_exact || (!has_opaque_ext && ir_pair_unchanged);
        if !cuts_off_public {
            continue;
        }
        let cuts_off_meta = (tiers.dep_meta == pre.meta_dig
            || (!has_opaque_ext && ir_pair_unchanged))
            && base_meta_ok;
        verdicts.insert(
            m.clone(),
            ModuleCutoffVerdict {
                cuts_off_public,
                cuts_off_meta,
            },
        );
    }
    verdicts
}

pub(super) fn load_pre_rebuild_root_manifest(
    canon_dir: &Path,
) -> (
    Option<std::result::Result<crate::module_builder::VerifiedDepManifest, ()>>,
    Option<crate::module_builder::VerifiedDepManifest>,
) {
    let manifest_path = verified_sources_manifest_path(canon_dir);
    let raw = match fs::read(&manifest_path) {
        Ok(bytes) => Some(
            serde_json::from_slice::<crate::module_builder::VerifiedDepManifest>(&bytes)
                .map_err(|_| ()),
        ),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
        Err(_) => Some(Err(())),
    };
    let validated = load_verified_project_manifest(canon_dir);
    (raw, validated)
}

#[allow(clippy::too_many_arguments, clippy::type_complexity)]
pub(super) fn compute_stage2_dependent_closure_after_cutoff(
    canon_dir: &Path,
    closure: &ProjectDependentClosure,
    dag: &crate::module_builder::ModuleDag,
    edited_standalone: &std::collections::BTreeSet<String>,
    baselines: &HashMap<String, PreRebuildModuleBaseline>,
    verdicts: &HashMap<String, ModuleCutoffVerdict>,
    pre_raw_manifest: &Option<std::result::Result<crate::module_builder::VerifiedDepManifest, ()>>,
    pre_manifest_opt: Option<&crate::module_builder::VerifiedDepManifest>,
    require_kernel_audited: Option<&TurboStore>,
) -> Result<(
    Vec<String>,
    Vec<PathBuf>,
    Vec<StandaloneModuleSpec>,
    HashMap<String, bool>,
)> {
    use crate::module_builder::{DepImportMemo, DepImportVisibility, LakeClosureCache};

    let strict_policy = require_kernel_audited.is_some();
    let edited_dag_set: HashSet<&str> = closure
        .edited_dag_modules
        .iter()
        .map(String::as_str)
        .collect();
    let matches_deleted = |dep: &str| -> bool {
        closure
            .deleted_modules
            .iter()
            .any(|x| dep == x || x.ends_with(&format!(".{}", dep)))
    };
    let shared_lib_mods: HashSet<&str> = dag
        .shared_libs
        .iter()
        .flat_map(|sl| sl.local_modules.iter().map(String::as_str))
        .collect();

    let expected_lake_inputs =
        crate::module_builder::workspace_lake_inputs_digest(&closure.cfg).ok();
    let mut closure_cache = LakeClosureCache::for_project(&closure.cfg);
    closure_cache.insert_pre_pkg_manifest(
        closure.cfg.root_pkg.pkg_root.clone(),
        strict_policy,
        pre_raw_manifest.clone(),
        pre_manifest_opt.cloned(),
    );
    for (em, v) in verdicts {
        if let (Some(en), Some(pre)) = (dag.nodes.get(em), baselines.get(em)) {
            closure_cache.seed_cutoff_module_pin(
                en.pkg_root.clone(),
                em.clone(),
                crate::module_builder::CutoffPinBaseline {
                    full_dig: pre.full_dig.clone(),
                    export_dig: pre.export_dig.clone(),
                    meta_dig: pre.meta_dig.clone(),
                    cuts_off_public: v.cuts_off_public,
                    cuts_off_meta: v.cuts_off_meta,
                },
            );
            if let Some(exp_info) = pre.lake_export_info {
                closure_cache.seed_module_export_info(
                    en.pkg_root.clone(),
                    em.clone(),
                    strict_policy,
                    exp_info,
                );
            }
        }
    }
    let dep_memo = DepImportMemo::default();
    let mut node_fresh_memo: HashMap<String, bool> = HashMap::new();
    for m in &dag.topological_order {
        if edited_dag_set.contains(m.as_str()) {
            node_fresh_memo.insert(m.clone(), false);
            continue;
        }
        let Some(node) = dag.nodes.get(m) else {
            node_fresh_memo.insert(m.clone(), false);
            continue;
        };
        let fresh = (|| -> bool {
            let Some(ref expected_inputs) = expected_lake_inputs else {
                return false;
            };
            if !node.olean_path.is_file() {
                return false;
            }
            let Ok(src_raw) = fs::read_to_string(&node.src_path) else {
                return false;
            };
            if blake3::hash(src_raw.as_bytes()).to_hex().as_str() != node.src_blake3 {
                return false;
            }
            let hdr = crate::module_builder::parse_header_info(&src_raw);
            if hdr.header_error.is_some() || hdr.is_module != node.is_module {
                return false;
            }
            let rel_slash = crate::module_builder::module_name_to_rel_slash(&node.module_name);
            let ir_dir = node
                .c_path
                .to_string_lossy()
                .strip_suffix(&format!("{rel_slash}.c"))
                .map(|s| PathBuf::from(s.trim_end_matches('/')));
            if crate::module_builder::verify_module_lake_sidecars(
                &node.olean_path,
                ir_dir.as_deref(),
                &rel_slash,
                &src_raw,
                node.is_module,
                node.needs_c,
            )
            .is_err()
            {
                return false;
            }
            for d in &node.direct_dag_deps {
                if matches_deleted(d) {
                    return false;
                }
                if !edited_dag_set.contains(d.as_str())
                    && !node_fresh_memo.get(d).copied().unwrap_or(false)
                {
                    return false;
                }
            }
            let spec_opt = if node.is_root_pkg {
                crate::module_builder::resolve_module_in_package(
                    &closure.cfg.root_pkg,
                    true,
                    &node.module_name,
                )
            } else {
                closure.cfg.dep_pkgs.iter().find_map(|dp| {
                    if dp.pkg_root == node.pkg_root {
                        crate::module_builder::resolve_module_in_package(
                            dp,
                            false,
                            &node.module_name,
                        )
                    } else {
                        None
                    }
                })
            };
            let Some(spec) = spec_opt else {
                return false;
            };
            let rel_src = crate::module_builder::spec_rel_src(&spec);
            let (raw_has_entry, entry_opt) = if node.is_root_pkg {
                if matches!(pre_raw_manifest, Some(Err(()))) {
                    return false;
                }
                let raw_has = matches!(
                    pre_raw_manifest.as_ref(),
                    Some(Ok(rm)) if rm.modules.contains_key(&rel_src)
                );
                let ent = pre_manifest_opt
                    .and_then(|pm| pm.modules.get(&rel_src))
                    .cloned();
                (raw_has, ent)
            } else {
                let Some(cm) = closure_cache.load_pkg_manifest(&closure.cfg, &spec, strict_policy)
                else {
                    return false;
                };
                let raw_has = matches!(
                    cm.raw.as_ref(),
                    Some(Ok(rm)) if rm.modules.contains_key(&rel_src)
                );
                let ent = cm
                    .validated
                    .as_ref()
                    .and_then(|vm| vm.modules.get(&rel_src))
                    .cloned();
                (raw_has, ent)
            };
            if raw_has_entry && entry_opt.is_none() {
                return false;
            }
            if let Some(entry) = entry_opt {
                if (strict_policy && node.is_root_pkg && !entry.kernel_audited)
                    || entry.lake_inputs_digest != *expected_inputs
                    || entry.src_blake3 != node.src_blake3
                    || !crate::module_builder::entry_artifacts_current(
                        &closure.cfg,
                        &node.olean_path,
                        &entry,
                    )
                    || !crate::module_builder::compute_module_raw_import_dynlibs(dag, node)
                        .is_empty()
                {
                    return false;
                }
                crate::module_builder::verified_entry_imports_current_for_header(
                    &entry,
                    &hdr,
                    |imp, pin_spec| {
                        if matches_deleted(imp) {
                            return false;
                        }
                        if edited_dag_set.contains(imp) {
                            let Some(ps) = pin_spec else {
                                return false;
                            };
                            let (Some(v), Some(pre)) = (verdicts.get(imp), baselines.get(imp))
                            else {
                                return false;
                            };
                            return match ps.tier_pin {
                                Some((DepImportVisibility::PublicExport, exp)) => {
                                    v.cuts_off_public
                                        && !exp.is_empty()
                                        && (exp == pre.export_dig || ps.full_pin == pre.full_dig)
                                }
                                Some((DepImportVisibility::MetaExport, meta)) => {
                                    v.cuts_off_meta
                                        && !meta.is_empty()
                                        && (meta == pre.meta_dig || ps.full_pin == pre.full_dig)
                                }
                                _ => false,
                            };
                        }
                        crate::module_builder::import_pin_current_with_policy(
                            &closure.cfg,
                            &dep_memo,
                            &mut closure_cache,
                            imp,
                            pin_spec,
                            strict_policy,
                        )
                    },
                )
            } else {
                if strict_policy && node.is_root_pkg {
                    return false;
                }
                if node
                    .direct_dag_deps
                    .iter()
                    .any(|d| edited_dag_set.contains(d.as_str()) && !verdicts.contains_key(d))
                {
                    return false;
                }
                for d in &node.direct_dag_deps {
                    if verdicts.contains_key(d)
                        && baselines.get(d).and_then(|b| b.lake_export_info).is_none()
                    {
                        return false;
                    }
                }
                let mut visiting = HashSet::new();
                crate::module_builder::lake_closure_export_info(
                    &closure.cfg,
                    &spec,
                    strict_policy,
                    &mut closure_cache,
                    &mut visiting,
                )
                .is_some()
            }
        })();
        node_fresh_memo.insert(m.clone(), fresh);
    }

    let dep_requires_rebuild_for_vis = |dep: &str,
                                        vis: DepImportVisibility,
                                        dag_dirty: &std::collections::BTreeSet<String>,
                                        standalone_dirty: &std::collections::BTreeSet<String>|
     -> bool {
        if matches_deleted(dep) || standalone_dirty.contains(dep) {
            return true;
        }
        if !dag_dirty.contains(dep) {
            return false;
        }
        if edited_dag_set.contains(dep) {
            if let Some(v) = verdicts.get(dep) {
                return match vis {
                    DepImportVisibility::PublicExport => !v.cuts_off_public,
                    DepImportVisibility::MetaExport => !v.cuts_off_meta,
                    DepImportVisibility::All => true,
                };
            }
        }
        true
    };

    let _ = canon_dir;
    let mut dag_dirty: std::collections::BTreeSet<String> =
        closure.edited_dag_modules.iter().cloned().collect();
    let mut standalone_dirty: std::collections::BTreeSet<String> = edited_standalone.clone();

    let mut changed = true;
    while changed {
        changed = false;
        for (m, n) in &dag.nodes {
            if dag_dirty.contains(m) {
                continue;
            }
            let (vis_map, _dep_is_mod_map) =
                crate::module_builder::compute_node_dep_visibility_map(&closure.cfg, dag, n);
            let mut dep_triggers = false;
            for d in &n.direct_dag_deps {
                let vis = if !n.is_module
                    || n.precompile_modules
                    || n.is_exe_target
                    || n.needs_dynlib
                    || shared_lib_mods.contains(m.as_str())
                {
                    DepImportVisibility::All
                } else {
                    vis_map.get(d).copied().unwrap_or(DepImportVisibility::All)
                };
                if dep_requires_rebuild_for_vis(d, vis, &dag_dirty, &standalone_dirty) {
                    dep_triggers = true;
                    break;
                }
            }
            if !dep_triggers
                && n.direct_dag_deps
                    .iter()
                    .any(|d| dag_dirty.contains(d) || standalone_dirty.contains(d))
                && !node_fresh_memo.get(m).copied().unwrap_or(false)
            {
                dep_triggers = true;
            }
            if dep_triggers {
                dag_dirty.insert(m.clone());
                changed = true;
            }
        }
        for (m, s) in &closure.standalone_all {
            if standalone_dirty.contains(m) {
                continue;
            }
            let mut dep_triggers = s.imports.iter().any(|d| {
                let vis = if !s.is_module {
                    DepImportVisibility::All
                } else {
                    s.import_visibilities
                        .get(d)
                        .copied()
                        .unwrap_or(DepImportVisibility::All)
                };
                dep_requires_rebuild_for_vis(d, vis, &dag_dirty, &standalone_dirty)
            });
            if !dep_triggers
                && s.imports
                    .iter()
                    .any(|d| dag_dirty.contains(d) || standalone_dirty.contains(d))
            {
                let imports_fresh = s.imports.iter().all(|d| {
                    if matches_deleted(d) {
                        return false;
                    }
                    if dag_dirty.contains(d) || closure.standalone_all.contains_key(d) {
                        return true;
                    }
                    if dag.nodes.contains_key(d) {
                        return node_fresh_memo.get(d).copied().unwrap_or(false);
                    }
                    crate::module_builder::import_pin_current_with_policy(
                        &closure.cfg,
                        &dep_memo,
                        &mut closure_cache,
                        d,
                        None,
                        strict_policy,
                    )
                });
                if !imports_fresh {
                    dep_triggers = true;
                }
            }
            if dep_triggers {
                standalone_dirty.insert(m.clone());
                changed = true;
            }
        }
    }

    let mut up_changed = true;
    while up_changed {
        up_changed = false;
        let current: Vec<String> = standalone_dirty.iter().cloned().collect();
        for m in current {
            if let Some(spec) = closure.standalone_all.get(&m) {
                for imp in &spec.imports {
                    if closure.standalone_all.contains_key(imp)
                        && standalone_dirty.insert(imp.clone())
                    {
                        up_changed = true;
                    }
                }
            }
        }
    }

    let stage2_dag_mods: Vec<String> = dag_dirty
        .iter()
        .filter(|m| !edited_dag_set.contains(m.as_str()))
        .cloned()
        .collect();
    let all_rechecked_mods: Vec<String> = dag_dirty.into_iter().collect();
    let all_rechecked_files: Vec<PathBuf> = all_rechecked_mods
        .iter()
        .filter_map(|m| dag.nodes.get(m).map(|n| n.src_path.clone()))
        .collect();
    let standalone_specs =
        topologically_order_standalone_modules(&closure.standalone_all, &standalone_dirty)?;
    let _ = stage2_dag_mods;
    Ok((
        all_rechecked_mods,
        all_rechecked_files,
        standalone_specs,
        node_fresh_memo,
    ))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn refresh_cutoff_shielded_manifest_and_traces(
    canon_dir: &Path,
    cfg: &crate::module_builder::ProjectConfig,
    dag: &crate::module_builder::ModuleDag,
    rebuilt_mods: &[String],
    verdicts: &HashMap<String, ModuleCutoffVerdict>,
    node_fresh_memo: &HashMap<String, bool>,
    pre_raw_manifest: &Option<std::result::Result<crate::module_builder::VerifiedDepManifest, ()>>,
    pre_manifest_opt: Option<&crate::module_builder::VerifiedDepManifest>,
) {
    use crate::module_builder::DepImportVisibility;
    if verdicts.is_empty()
        || worktree_auto_link_disabled(canon_dir)
        || matches!(pre_raw_manifest, Some(Err(())))
    {
        return;
    }
    let Ok(expected_lake_inputs) = crate::module_builder::workspace_lake_inputs_digest(cfg) else {
        return;
    };
    let rebuilt_set: HashSet<&str> = rebuilt_mods.iter().map(String::as_str).collect();
    let shared_lib_mods: HashSet<&str> = dag
        .shared_libs
        .iter()
        .flat_map(|sl| sl.local_modules.iter().map(String::as_str))
        .collect();
    let mut olean_digests: HashMap<String, String> = HashMap::new();
    let mut tier_digests: HashMap<String, crate::module_builder::ModuleArtifactTierDigests> =
        HashMap::new();
    fn ensure_dep_digest(
        olean_digests: &mut HashMap<String, String>,
        tier_digests: &mut HashMap<String, crate::module_builder::ModuleArtifactTierDigests>,
        dep_name: &str,
        dep_olean: &Path,
    ) -> Option<()> {
        if !olean_digests.contains_key(dep_name) {
            let td = crate::module_builder::compute_module_artifact_tier_digests_with_policy(
                dep_olean, true,
            )
            .ok()?;
            olean_digests.insert(dep_name.to_string(), td.full.clone());
            tier_digests.insert(dep_name.to_string(), td);
        }
        Some(())
    }

    for m in &dag.topological_order {
        if rebuilt_set.contains(m.as_str()) || !node_fresh_memo.get(m).copied().unwrap_or(false) {
            continue;
        }
        let Some(node) = dag.nodes.get(m) else {
            continue;
        };
        if !node.is_root_pkg
            || !node.is_module
            || node.precompile_modules
            || node.is_exe_target
            || node.needs_dynlib
            || shared_lib_mods.contains(m.as_str())
        {
            continue;
        }
        let touches_cutoff_dep = node
            .expected_all_deps
            .iter()
            .any(|d| verdicts.contains_key(d));
        if !touches_cutoff_dep {
            continue;
        }
        let (vis_map, _dep_is_mod_map) =
            crate::module_builder::compute_node_dep_visibility_map(cfg, dag, node);
        let all_deps_shielded = node.direct_dag_deps.iter().all(|d| {
            if !rebuilt_set.contains(d.as_str()) {
                return true;
            }
            let Some(v) = verdicts.get(d) else {
                return false;
            };
            match vis_map.get(d).copied().unwrap_or(DepImportVisibility::All) {
                DepImportVisibility::PublicExport => v.cuts_off_public,
                DepImportVisibility::MetaExport => v.cuts_off_meta,
                DepImportVisibility::All => false,
            }
        });
        if !all_deps_shielded {
            continue;
        }
        let rel_src = node
            .src_path
            .strip_prefix(&node.pkg_root)
            .unwrap_or(&node.src_path)
            .to_string_lossy()
            .replace('\\', "/");
        let raw_has_entry = matches!(
            pre_raw_manifest.as_ref(),
            Some(Ok(rm)) if rm.modules.contains_key(&rel_src)
        );
        let pre_entry_opt = pre_manifest_opt.and_then(|pm| pm.modules.get(&rel_src));
        if raw_has_entry && pre_entry_opt.is_none() {
            continue;
        }
        let Ok(src_now) = fs::read_to_string(&node.src_path) else {
            continue;
        };
        let actual_src_b3 = blake3::hash(src_now.as_bytes()).to_hex().to_string();
        if actual_src_b3 != node.src_blake3 {
            continue;
        }
        let rel_slash = crate::module_builder::module_name_to_rel_slash(&node.module_name);
        let ir_dir = node
            .c_path
            .to_string_lossy()
            .strip_suffix(&format!("{rel_slash}.c"))
            .map(|s| PathBuf::from(s.trim_end_matches('/')));
        if crate::module_builder::verify_module_lake_sidecars(
            &node.olean_path,
            ir_dir.as_deref(),
            &rel_slash,
            &src_now,
            node.is_module,
            node.needs_c,
        )
        .is_err()
        {
            continue;
        }
        if ensure_dep_digest(&mut olean_digests, &mut tier_digests, m, &node.olean_path).is_none() {
            continue;
        }
        let Some(actual_full_dig) = olean_digests.get(m).cloned() else {
            continue;
        };
        let should_stamp_manifest = if let Some(pre_entry) = pre_entry_opt {
            if !pre_entry.kernel_audited
                || pre_entry.lake_inputs_digest != expected_lake_inputs
                || pre_entry.src_blake3 != actual_src_b3
                || pre_entry.olean_artifact_digest != actual_full_dig
            {
                continue;
            }
            true
        } else {
            false
        };
        let mut deps_ok = true;
        for d in &node.direct_dag_deps {
            if let Some(dn) = dag.nodes.get(d) {
                if ensure_dep_digest(&mut olean_digests, &mut tier_digests, d, &dn.olean_path)
                    .is_none()
                {
                    deps_ok = false;
                    break;
                }
            } else {
                deps_ok = false;
                break;
            }
        }
        for (ext_m, ext_p) in &node.external_olean_deps {
            if ensure_dep_digest(&mut olean_digests, &mut tier_digests, ext_m, ext_p).is_none() {
                deps_ok = false;
                break;
            }
        }
        if !deps_ok {
            continue;
        }
        if crate::module_builder::write_lake_module_hashes_and_trace(
            cfg,
            dag,
            node,
            &actual_full_dig,
            Some(&actual_full_dig),
            true,
        )
        .is_ok()
            && should_stamp_manifest
        {
            crate::module_builder::record_verified_dep_source(
                cfg,
                dag,
                node,
                &actual_full_dig,
                true,
                &olean_digests,
                &tier_digests,
            );
        }
    }
}

pub(super) fn stamp_manifest_after_lake_cutoff_rebuild(
    store: &TurboStore,
    canon_dir: &Path,
    cfg: &crate::module_builder::ProjectConfig,
    dag: &crate::module_builder::ModuleDag,
    rebuilt_mods: &[String],
) -> Result<()> {
    if rebuilt_mods.is_empty() || worktree_auto_link_disabled(canon_dir) {
        return Ok(());
    }
    let manifest_path = verified_sources_manifest_path(canon_dir);
    if !manifest_path.is_file() {
        return Ok(());
    }
    let rebuilt_files: Vec<PathBuf> = rebuilt_mods
        .iter()
        .filter_map(|m| dag.nodes.get(m).map(|n| n.src_path.clone()))
        .collect();
    ensure_modules_and_imports_replayed(store, canon_dir, &rebuilt_files, rebuilt_mods)?;
    let mut olean_digests: HashMap<String, String> = HashMap::new();
    let mut tier_digests: HashMap<String, crate::module_builder::ModuleArtifactTierDigests> =
        HashMap::new();
    for m in rebuilt_mods {
        let Some(node) = dag.nodes.get(m) else {
            continue;
        };
        let hygiene = splitter::audit_hygiene(&splitter::strip_lean_comments(
            &fs::read_to_string(&node.src_path).unwrap_or_default(),
        ));
        let checking_weakening_bad =
            if crate::module_builder::node_is_git_pinned_manifest_package(cfg, node) {
                hygiene.has_checking_weakening_option
            } else {
                hygiene.has_checking_weakening
            };
        if (node.is_root_pkg
            && (hygiene.has_sorry
                || hygiene.has_axiom
                || hygiene.native_violation()
                || hygiene.has_trust_compiler))
            || checking_weakening_bad
        {
            return Ok(());
        }
        let mut record_dep = |dep_name: &str, dep_olean: &Path| -> Option<()> {
            if !olean_digests.contains_key(dep_name) {
                let td = crate::module_builder::compute_module_artifact_tier_digests_with_policy(
                    dep_olean, true,
                )
                .ok()?;
                olean_digests.insert(dep_name.to_string(), td.full.clone());
                tier_digests.insert(dep_name.to_string(), td);
            }
            Some(())
        };
        if record_dep(m, &node.olean_path).is_none() {
            return Ok(());
        }
        for d in &node.direct_dag_deps {
            if let Some(dn) = dag.nodes.get(d) {
                if record_dep(d, &dn.olean_path).is_none() {
                    return Ok(());
                }
            }
        }
        for (ext_m, ext_p) in &node.external_olean_deps {
            if record_dep(ext_m, ext_p).is_none() {
                return Ok(());
            }
        }
    }
    for m in rebuilt_mods {
        if let Some(node) = dag.nodes.get(m) {
            let mut fresh_node = node.clone();
            if let Ok(src_now) = fs::read_to_string(&fresh_node.src_path) {
                fresh_node.src_blake3 = blake3::hash(src_now.as_bytes()).to_hex().to_string();
            }
            if let Some(full_dig) = olean_digests.get(m).cloned() {
                crate::module_builder::record_verified_dep_source(
                    cfg,
                    dag,
                    &fresh_node,
                    &full_dig,
                    fresh_node.is_root_pkg,
                    &olean_digests,
                    &tier_digests,
                );
            }
        }
    }
    Ok(())
}

pub(super) fn node_is_kernel_audited_in_untrusted(
    _store: &TurboStore,
    canon_dir: &Path,
    node: &crate::module_builder::ModuleNode,
) -> bool {
    is_file_hash_verified_in_lake_build(canon_dir, &node.src_path, &node.src_blake3)
}

#[cfg(test)]
pub(crate) fn lake_recheck_dependents(
    canon_dir: &Path,
    edits: &[String],
    rev: Option<&str>,
) -> Result<(usize, Vec<PathBuf>, Vec<String>)> {
    let (count, files, mods, _overlay) =
        lake_recheck_dependents_with_store(None, canon_dir, edits, rev, false)?;
    Ok((count, files, mods))
}

#[allow(clippy::type_complexity)]
pub(crate) fn lake_recheck_dependents_with_store(
    store_opt: Option<&TurboStore>,
    canon_dir: &Path,
    edits: &[String],
    rev: Option<&str>,
    retain_standalone_oleans: bool,
) -> Result<(
    usize,
    Vec<PathBuf>,
    Vec<String>,
    Option<StandaloneOleanOverlay>,
)> {
    lake_recheck_dependents_with_store_and_options(
        store_opt,
        canon_dir,
        edits,
        rev,
        retain_standalone_oleans,
        false,
    )
}

#[allow(clippy::type_complexity)]
pub(crate) fn lake_recheck_dependents_with_store_and_options(
    store_opt: Option<&TurboStore>,
    canon_dir: &Path,
    edits: &[String],
    rev: Option<&str>,
    retain_standalone_oleans: bool,
    allow_sorry: bool,
) -> Result<(
    usize,
    Vec<PathBuf>,
    Vec<String>,
    Option<StandaloneOleanOverlay>,
)> {
    if !has_lake_config(canon_dir) {
        anyhow::bail!(
            "non-local edit in {} needs its dependents re-checked, but {} has no Lake config: refusing to pass",
            edits.join(", "),
            canon_dir.display()
        );
    }
    let closure = compute_project_dependent_closure(canon_dir, edits, false)?;
    let edited_set: HashSet<PathBuf> = edits
        .iter()
        .map(|e| canon_dir.join(e))
        .map(|p| p.canonicalize().unwrap_or(p))
        .collect();
    let edited_standalone: std::collections::BTreeSet<String> = closure
        .standalone_all
        .iter()
        .filter(|(_, s)| edited_set.contains(&s.src_path))
        .map(|(m, _)| m.clone())
        .collect();

    let mut effective_standalone = closure.standalone_modules.clone();
    let (dag_count, files, mods) = match (closure.dag_modules.clone(), closure.dag_files.clone()) {
        // As in `ensure_project_imports_fresh_for_check`: a module whose input-bearing library is
        // not the one Lake attributes it to has to be asked for by library name, or Lake compares
        // an input-blind trace and reports it up to date.
        (Some(mods), Some(files)) if !mods.is_empty() => {
            let mut store_root_buf: Option<PathBuf> = None;
            let store_root: Option<&Path> = match store_opt {
                Some(s) => Some(s.root.as_path()),
                None => {
                    let p = std::env::temp_dir().join(format!(
                        "turbo_cutoff_probe_{}_{}",
                        std::process::id(),
                        pack::next_tmp_id()
                    ));
                    let _ = fs::create_dir_all(&p);
                    store_root_buf = Some(p);
                    store_root_buf.as_deref()
                }
            };
            let allowed = splitter::allowed_axioms();
            let assurance = crate::module_builder::discover_trusted_assurance_surface(
                canon_dir,
                &closure.cfg.root_pkg,
                &allowed,
            );
            let touches_assurance = closure
                .edited_dag_modules
                .iter()
                .any(|m| assurance.mod_names.contains(m));
            let cutoff_attempted = if !allow_sorry && !touches_assurance {
                if let (Some(sr), Some(dag)) = (store_root, closure.dag.as_ref()) {
                    let stage1_targets =
                        lake_refresh_targets(canon_dir, &closure.edited_dag_modules);
                    let stage1_only_modules = !closure.edited_dag_modules.is_empty()
                        && closure.deleted_modules.is_empty()
                        && stage1_targets == closure.edited_dag_modules;
                    if stage1_only_modules {
                        capture_pre_rebuild_module_baselines(
                            sr,
                            &closure.cfg,
                            dag,
                            &closure.edited_dag_modules,
                            rev,
                            false,
                        )
                        .map(|baselines| (sr, dag, baselines))
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            };

            if let Some((sr, dag, baselines)) = cutoff_attempted {
                let (pre_raw_manifest, pre_manifest) = load_pre_rebuild_root_manifest(canon_dir);
                if let Some(s) = store_opt {
                    let mut mut_store = TurboStore::open(Some(&s.root))?;
                    crate::module_builder::build_project_modules_native(
                        &mut mut_store,
                        canon_dir,
                        &closure.edited_dag_modules,
                        "trusted",
                        0,
                        false,
                        true,
                        None,
                    )?;
                } else {
                    lake_build_modules(canon_dir, &closure.edited_dag_modules, rev)?;
                }
                let verdicts =
                    evaluate_post_rebuild_module_cutoffs(sr, &closure.cfg, dag, &baselines, false);
                let (rechecked_mods, rechecked_files, stage2_standalone, node_fresh_memo) =
                    compute_stage2_dependent_closure_after_cutoff(
                        canon_dir,
                        &closure,
                        dag,
                        &edited_standalone,
                        &baselines,
                        &verdicts,
                        &pre_raw_manifest,
                        pre_manifest.as_ref(),
                        None,
                    )?;
                let edited_dag_set: HashSet<&str> = closure
                    .edited_dag_modules
                    .iter()
                    .map(String::as_str)
                    .collect();
                let stage2_only_mods: Vec<String> = rechecked_mods
                    .iter()
                    .filter(|m| !edited_dag_set.contains(m.as_str()))
                    .cloned()
                    .collect();
                if !stage2_only_mods.is_empty() {
                    if let Some(s) = store_opt {
                        let mut mut_store = TurboStore::open(Some(&s.root))?;
                        crate::module_builder::build_project_modules_native(
                            &mut mut_store,
                            canon_dir,
                            &stage2_only_mods,
                            "trusted",
                            0,
                            false,
                            true,
                            None,
                        )?;
                    } else {
                        lake_build_modules(
                            canon_dir,
                            &lake_refresh_targets(canon_dir, &stage2_only_mods),
                            rev,
                        )?;
                    }
                }
                if !allow_sorry {
                    if let Some(s) = store_opt {
                        stamp_manifest_after_lake_cutoff_rebuild(
                            s,
                            canon_dir,
                            &closure.cfg,
                            dag,
                            &rechecked_mods,
                        )?;
                    }
                    refresh_cutoff_shielded_manifest_and_traces(
                        canon_dir,
                        &closure.cfg,
                        dag,
                        &rechecked_mods,
                        &verdicts,
                        &node_fresh_memo,
                        &pre_raw_manifest,
                        pre_manifest.as_ref(),
                    );
                }
                if let Some(ref tmp_p) = store_root_buf {
                    let _ = fs::remove_dir_all(tmp_p);
                }
                effective_standalone = stage2_standalone;
                (rechecked_mods.len(), rechecked_files, rechecked_mods)
            } else {
                lake_build_modules(canon_dir, &lake_refresh_targets(canon_dir, &mods), rev)?;
                if !allow_sorry {
                    if let (Some(s), Some(dag)) = (store_opt, closure.dag.as_ref()) {
                        let _ = stamp_manifest_after_lake_cutoff_rebuild(
                            s,
                            canon_dir,
                            &closure.cfg,
                            dag,
                            &mods,
                        );
                    }
                }
                if let Some(ref tmp_p) = store_root_buf {
                    let _ = fs::remove_dir_all(tmp_p);
                }
                (mods.len(), files, mods)
            }
        }
        (Some(_), Some(_)) => (0, Vec::new(), Vec::new()),
        _ => {
            lake_build_modules(canon_dir, &closure.lake_seeds, rev)?;
            let all_files = collect_project_lean_files(canon_dir, false, None);
            let fallback_mods: Vec<String> = all_files
                .iter()
                .filter_map(|f| f.strip_prefix(canon_dir).ok())
                .map(|r| r.with_extension("").to_string_lossy().replace('/', "."))
                .collect();
            (0, all_files, fallback_mods)
        }
    };
    let (standalone_files, overlay) = check_and_audit_standalone_modules(
        store_opt,
        canon_dir,
        &effective_standalone,
        false,
        None,
        rev,
        retain_standalone_oleans,
        allow_sorry,
    )?;
    let mut files = files;
    let mut mods = mods;
    if retain_standalone_oleans {
        files.extend(standalone_files);
        mods.extend(
            effective_standalone
                .iter()
                .map(|spec| spec.module_name.clone()),
        );
    }
    let standalone_count = effective_standalone.len();
    Ok((dag_count + standalone_count, files, mods, overlay))
}

pub(crate) fn ensure_modules_and_imports_replayed(
    store: &TurboStore,
    canon_dir: &Path,
    target_files: &[PathBuf],
    module_names: &[String],
) -> Result<usize> {
    crate::module_builder::ensure_imported_oleans_replayed_with_roots(
        store,
        canon_dir,
        target_files,
        module_names,
    )
}

pub(crate) fn untrusted_recheck_dependents(
    store: &mut TurboStore,
    canon_dir: &Path,
    edits: &[String],
    trust_domain: &str,
    json: bool,
) -> Result<(usize, bool, Option<StandaloneOleanOverlay>)> {
    if !has_lake_config(canon_dir) {
        anyhow::bail!(
            "non-local edit in {} needs its dependents re-checked, but {} has no Lake config: refusing to pass",
            edits.join(", "),
            canon_dir.display()
        );
    }
    let closure = compute_project_dependent_closure(canon_dir, edits, true)?;
    let edited_set: HashSet<PathBuf> = edits
        .iter()
        .map(|e| canon_dir.join(e))
        .map(|p| p.canonicalize().unwrap_or(p))
        .collect();
    let edited_standalone: std::collections::BTreeSet<String> = closure
        .standalone_all
        .iter()
        .filter(|(_, s)| edited_set.contains(&s.src_path))
        .map(|(m, _)| m.clone())
        .collect();

    let cfg = closure.cfg.clone();
    let cutoff_baselines = if let Some(ref dag) = closure.dag {
        if !closure.edited_dag_modules.is_empty() && closure.deleted_modules.is_empty() {
            capture_pre_rebuild_module_baselines(
                &store.root,
                &cfg,
                dag,
                &closure.edited_dag_modules,
                None,
                true,
            )
        } else {
            None
        }
    } else {
        None
    };

    let mut verified_targets = HashSet::new();
    let (dag_count, built_all, effective_standalone) = if let (Some(dag), Some(baselines)) =
        (closure.dag.as_ref(), cutoff_baselines.as_ref())
    {
        let (pre_raw_manifest, pre_manifest) = load_pre_rebuild_root_manifest(canon_dir);
        crate::module_builder::build_project_modules_native(
            store,
            canon_dir,
            &closure.edited_dag_modules,
            trust_domain,
            1,
            true,
            json,
            None,
        )
        .map_err(|e| e.context("Untrusted PR Stage-1 dependent re-check failed"))?;
        let built_stage1 = crate::module_builder::build_module_dag_with_trust(
            &cfg,
            &closure.edited_dag_modules,
            true,
        )?;
        verified_targets.extend(built_stage1.nodes.into_keys());

        let verdicts =
            evaluate_post_rebuild_module_cutoffs(&store.root, &cfg, dag, baselines, true);
        let (rechecked_mods, _rechecked_files, stage2_standalone, node_fresh_memo) =
            compute_stage2_dependent_closure_after_cutoff(
                canon_dir,
                &closure,
                dag,
                &edited_standalone,
                baselines,
                &verdicts,
                &pre_raw_manifest,
                pre_manifest.as_ref(),
                Some(store),
            )?;
        let edited_dag_set: HashSet<&str> = closure
            .edited_dag_modules
            .iter()
            .map(String::as_str)
            .collect();
        let mut stage2_targets: Vec<String> = rechecked_mods
            .iter()
            .filter(|m| !edited_dag_set.contains(m.as_str()))
            .cloned()
            .collect();

        let _ = stamp_manifest_after_lake_cutoff_rebuild(
            store,
            canon_dir,
            &cfg,
            dag,
            &closure.edited_dag_modules,
        );
        refresh_cutoff_shielded_manifest_and_traces(
            canon_dir,
            &cfg,
            dag,
            &rechecked_mods,
            &verdicts,
            &node_fresh_memo,
            &pre_raw_manifest,
            pre_manifest.as_ref(),
        );
        for (m, n) in &dag.nodes {
            if !rechecked_mods.contains(m)
                && node_is_kernel_audited_in_untrusted(store, canon_dir, n)
            {
                verified_targets.insert(m.clone());
            }
        }

        let standalone_names: HashSet<&str> = stage2_standalone
            .iter()
            .map(|s| s.module_name.as_str())
            .collect();
        let mut standalone_target_imports: Vec<String> = Vec::new();
        for spec in &stage2_standalone {
            for imp in &spec.imports {
                if standalone_names.contains(imp.as_str()) {
                    continue;
                }
                if crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, imp)
                    .is_some()
                    || cfg.dep_pkgs.iter().any(|dp| {
                        crate::module_builder::resolve_module_in_package(dp, false, imp).is_some()
                    })
                {
                    standalone_target_imports.push(imp.clone());
                }
            }
        }
        standalone_target_imports.sort();
        standalone_target_imports.dedup();

        for imp in standalone_target_imports {
            if !stage2_targets.contains(&imp) && !verified_targets.contains(&imp) {
                stage2_targets.push(imp);
            }
        }
        if !stage2_targets.is_empty() {
            crate::module_builder::build_project_modules_native(
                store,
                canon_dir,
                &stage2_targets,
                trust_domain,
                1,
                true,
                json,
                None,
            )
            .map_err(|e| e.context("Untrusted PR Stage-2 dependent re-check failed"))?;
            let built_stage2 =
                crate::module_builder::build_module_dag_with_trust(&cfg, &stage2_targets, true)?;
            verified_targets.extend(built_stage2.nodes.into_keys());
            let _ = stamp_manifest_after_lake_cutoff_rebuild(
                store,
                canon_dir,
                &cfg,
                dag,
                &stage2_targets,
            );
            refresh_cutoff_shielded_manifest_and_traces(
                canon_dir,
                &cfg,
                dag,
                &rechecked_mods,
                &verdicts,
                &node_fresh_memo,
                &pre_raw_manifest,
                pre_manifest.as_ref(),
            );
        }
        (rechecked_mods.len(), false, stage2_standalone)
    } else {
        let standalone_names: HashSet<&str> = closure
            .standalone_modules
            .iter()
            .map(|s| s.module_name.as_str())
            .collect();
        let mut standalone_target_imports: Vec<String> = Vec::new();
        for spec in &closure.standalone_modules {
            for imp in &spec.imports {
                if standalone_names.contains(imp.as_str()) {
                    continue;
                }
                if crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, imp)
                    .is_some()
                    || cfg.dep_pkgs.iter().any(|dp| {
                        crate::module_builder::resolve_module_in_package(dp, false, imp).is_some()
                    })
                {
                    standalone_target_imports.push(imp.clone());
                }
            }
        }
        standalone_target_imports.sort();
        standalone_target_imports.dedup();

        let (mut targets, dag_count, built_all) = match closure.dag_modules {
            Some(mods) if !mods.is_empty() => {
                let n = mods.len();
                (mods, n, false)
            }
            Some(_) => (Vec::new(), 0, false),
            None => (closure.dag_seeds, 0, true),
        };
        if !built_all {
            for imp in standalone_target_imports {
                if !targets.contains(&imp) {
                    targets.push(imp);
                }
            }
        }
        if built_all || !targets.is_empty() {
            crate::module_builder::build_project_modules_native(
                store,
                canon_dir,
                &targets,
                trust_domain,
                1,
                true,
                json,
                None,
            )
            .map_err(|e| e.context("Untrusted PR dependent re-check failed"))?;
            let built_dag =
                crate::module_builder::build_module_dag_with_trust(&cfg, &targets, true)?;
            verified_targets.extend(built_dag.nodes.into_keys());
        }
        (dag_count, built_all, closure.standalone_modules)
    };

    let (_standalone_files, overlay) = check_and_audit_standalone_modules(
        Some(store),
        canon_dir,
        &effective_standalone,
        true,
        Some(&verified_targets),
        None,
        true,
        false,
    )?;
    Ok((dag_count + effective_standalone.len(), built_all, overlay))
}

/// Build any standalone (non-target) project modules transitively imported by `target_files`
/// and return an overlay holding their audited `.olean` directory.
pub(crate) fn build_imported_standalone_modules_overlay(
    store: &mut TurboStore,
    canon_dir: &Path,
    target_files: &[PathBuf],
    is_untrusted: bool,
    trust_domain: &str,
    json: bool,
    rev: Option<&str>,
) -> Result<Option<StandaloneOleanOverlay>> {
    if !has_lake_config(canon_dir) || target_files.is_empty() {
        return Ok(None);
    }
    let cfg =
        match crate::module_builder::resolve_project_config_with_trust(canon_dir, is_untrusted) {
            Ok(c) => c,
            Err(_) if !is_untrusted => return Ok(None),
            Err(e) => return Err(e),
        };
    let root_base = crate::module_builder::pkg_target_base_name(&cfg.root_pkg);
    let mut seeds: Vec<String> = cfg
        .root_pkg
        .libs
        .iter()
        .map(|l| format!("@{}/{}", root_base, l.name))
        .collect();
    for exe in &cfg.root_pkg.exes {
        let target = format!("@{}/{}:default", root_base, exe.name);
        if !seeds.contains(&target) {
            seeds.push(target);
        }
    }
    let dag_opt = if is_untrusted {
        Some(crate::module_builder::build_module_dag_with_trust(
            &cfg, &seeds, true,
        )?)
    } else {
        crate::module_builder::build_module_dag_with_trust(&cfg, &seeds, false).ok()
    };
    let empty_edits = HashSet::new();
    let standalone_all = discover_standalone_project_modules(
        canon_dir,
        &cfg,
        dag_opt.as_ref(),
        &empty_edits,
        is_untrusted,
        false,
    )?;
    if standalone_all.is_empty() {
        return Ok(None);
    }
    let canon = |p: &Path| p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
    let target_canon_set: HashSet<PathBuf> = target_files.iter().map(|f| canon(f)).collect();
    let mut needed: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut worklist: Vec<String> = target_files
        .iter()
        .flat_map(|f| read_header_imports_from_file(f).unwrap_or_default())
        .collect();
    for (m, spec) in &standalone_all {
        if target_canon_set.contains(&spec.src_path) {
            for imp in &spec.imports {
                worklist.push(imp.clone());
            }
        }
        // Only treat `m` itself as an imported standalone prerequisite when another target imports `m`,
        // not when `m` is the file undergoing local per-theorem shard checks.
        let _ = m;
    }
    let mut visited = HashSet::new();
    while let Some(m) = worklist.pop() {
        if !visited.insert(m.clone()) {
            continue;
        }
        if let Some(spec) = standalone_all.get(&m) {
            needed.insert(m.clone());
            for sub in &spec.imports {
                if !visited.contains(sub) {
                    worklist.push(sub.clone());
                }
            }
        }
    }
    if needed.is_empty() {
        return Ok(None);
    }
    let ordered = topologically_order_standalone_modules(&standalone_all, &needed)?;
    let mut verified_targets_opt: Option<HashSet<String>> = None;
    if is_untrusted {
        let standalone_names: HashSet<&str> =
            ordered.iter().map(|s| s.module_name.as_str()).collect();
        let mut target_imports: Vec<String> = Vec::new();
        for spec in &ordered {
            for imp in &spec.imports {
                if standalone_names.contains(imp.as_str()) {
                    continue;
                }
                if crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, imp)
                    .is_some()
                    || cfg.dep_pkgs.iter().any(|dp| {
                        crate::module_builder::resolve_module_in_package(dp, false, imp).is_some()
                    })
                {
                    target_imports.push(imp.clone());
                }
            }
        }
        for f in target_files {
            for imp in read_header_imports_from_file(f).unwrap_or_default() {
                if standalone_names.contains(imp.as_str()) {
                    continue;
                }
                if crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, &imp)
                    .is_some()
                    || cfg.dep_pkgs.iter().any(|dp| {
                        crate::module_builder::resolve_module_in_package(dp, false, &imp).is_some()
                    })
                {
                    target_imports.push(imp);
                }
            }
        }
        target_imports.sort();
        target_imports.dedup();
        if !target_imports.is_empty() {
            crate::module_builder::build_project_modules_native(
                store,
                canon_dir,
                &target_imports,
                trust_domain,
                1,
                true,
                json,
                None,
            )
            .context("Untrusted standalone module target-import build failed")?;
            let sub_dag =
                crate::module_builder::build_module_dag_with_trust(&cfg, &target_imports, true)?;
            verified_targets_opt = Some(sub_dag.nodes.into_keys().collect());
        } else {
            verified_targets_opt = Some(HashSet::new());
        }
    }
    let (_files, overlay) = check_and_audit_standalone_modules(
        Some(store),
        canon_dir,
        &ordered,
        is_untrusted,
        verified_targets_opt.as_ref(),
        rev,
        true,
        false,
    )?;
    Ok(overlay)
}
