use anyhow::{Context, Result};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;
use walkdir::WalkDir;

use crate::db::{BlobEntry, SingleflightOutcome, TurboStore};
use crate::pack;
use crate::splitter;

use super::*;

/// Seed `TheoremProofCAS` in a single atomic SQLite transaction for all hygienic `.lean` files
/// in `canon_dir` (optionally requiring a pre-compiled `.olean` in `.lake/build/lib/lean`).
/// Returns `(files_seeded, shards_seeded)`.
pub(crate) fn seed_project_theorem_shards_from_splits(
    store: &mut TurboStore,
    canon_dir: &Path,
    toolchain: &str,
    trust_domain: &str,
    require_olean: bool,
    split_entries: &[(PathBuf, String, splitter::SplitResult)],
) -> Result<(usize, usize)> {
    let shared_receipt = format!("verified:seeded:{}", toolchain).into_bytes();
    let mut files_seeded = 0usize;
    let mut batch_items: Vec<(String, String, Vec<u8>, i64)> = Vec::new();

    let _ = crate::module_builder::try_project_lake_inputs_tag(canon_dir)?;
    let pkg_cfg_opt = crate::module_builder::optional_package_config(canon_dir)?;
    for (lf, _src, split) in split_entries {
        if require_olean && resolve_replayed_prebuilt_module_import(store, canon_dir, lf).is_none()
        {
            continue;
        }
        if split.shards.is_empty() || !split.hygiene.is_clean_for_certification() {
            continue;
        }
        let file_lean_args = pkg_cfg_opt
            .as_ref()
            .map(|pkg| crate::module_builder::resolve_file_lean_args_in_package(pkg, lf))
            .unwrap_or_default();
        let file_has_sorry = split.hygiene.has_sorry;
        let mut file_had_clean_shard = false;
        for shard in &split.shards {
            if file_has_sorry
                && splitter::audit_hygiene(&splitter::strip_lean_comments(&shard.proof_text))
                    .has_sorry
            {
                continue;
            }
            file_had_clean_shard = true;
            let shard_key = compute_shard_key_with_args(toolchain, shard, &file_lean_args);
            batch_items.push((shard_key, shard.name.clone(), shared_receipt.clone(), 1i64));
        }
        if file_had_clean_shard {
            files_seeded += 1;
        }
    }

    let shards_seeded = batch_items.len();
    if !batch_items.is_empty() {
        store.batch_publish_theorem_shards(toolchain, trust_domain, &batch_items)?;
    }
    Ok((files_seeded, shards_seeded))
}

pub(crate) fn seed_theorem_shards_for_files(
    store: &mut TurboStore,
    canon_dir: &Path,
    toolchain: &str,
    trust_domain: &str,
    lean_files: &[PathBuf],
) -> Result<(usize, usize, usize)> {
    let (split_entries, split_cache_hits) = load_and_split_files_cached(store, lean_files)?;
    let (files_seeded, shards_seeded) = seed_project_theorem_shards_from_splits(
        store,
        canon_dir,
        toolchain,
        trust_domain,
        false,
        &split_entries,
    )?;
    Ok((files_seeded, shards_seeded, split_cache_hits))
}

pub(crate) fn seed_project_theorem_shards(
    store: &mut TurboStore,
    canon_dir: &Path,
    toolchain: &str,
    trust_domain: &str,
    require_olean: bool,
) -> Result<(usize, usize, usize)> {
    let lean_files: Vec<PathBuf> = collect_lean_files(canon_dir)
        .into_iter()
        .filter(|lf| {
            !require_olean
                || resolve_replayed_prebuilt_module_import(store, canon_dir, lf).is_some()
        })
        .collect();

    let (split_entries, split_cache_hits) = load_and_split_files_cached(store, &lean_files)?;
    let (files_seeded, shards_seeded) = seed_project_theorem_shards_from_splits(
        store,
        canon_dir,
        toolchain,
        trust_domain,
        false,
        &split_entries,
    )?;
    Ok((files_seeded, shards_seeded, split_cache_hits))
}

pub(crate) fn has_out_of_tree_dep_build_dir(project_dir: &Path) -> bool {
    let canon_proj = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let Ok(cfg) = crate::module_builder::resolve_project_config(&canon_proj) else {
        return false;
    };
    cfg.dep_pkgs.iter().any(|dp| {
        let bdir = dp.pkg_root.join(&dp.build_dir);
        let canon_b = bdir.canonicalize().unwrap_or(bdir);
        canon_b.exists() && !canon_b.starts_with(&canon_proj)
    })
}

pub(super) fn classify_lake_build_artifact(
    path: &Path,
    build_dir: &Path,
    extra_bin_dirs: &[PathBuf],
) -> Option<&'static str> {
    let file_name = path.file_name().and_then(|s| s.to_str())?;
    if file_name.starts_with(".turbo_tmp_")
        || file_name.starts_with(".turbo_stage_")
        || file_name.contains(".tl_tmp")
        || file_name == ".publish.lock"
    {
        return None;
    }
    if file_name == ".turbo_verified_sources.json" {
        return Some("manifest");
    }
    if file_name.ends_with(".olean.server") {
        return Some("olean_server");
    }
    if file_name.ends_with(".olean.private") {
        return Some("olean_private");
    }
    if file_name.ends_with(".ir.sig") {
        return Some("ir_sig");
    }
    if file_name.ends_with(".c.o.export") {
        return Some("co_export");
    }
    if file_name.ends_with(".c.o.noexport") {
        return Some("co_noexport");
    }
    if file_name.ends_with(".c.o") {
        return Some("co");
    }
    if file_name.ends_with(".setup.json") {
        return Some("setup_json");
    }
    let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
    match ext {
        "olean" => Some("olean"),
        "ilean" => Some("ilean"),
        "ir" => Some("ir"),
        "c" => Some("c"),
        "hash" => Some("hash"),
        "trace" => Some("trace"),
        "so" | "dylib" | "dll" => Some("dynlib"),
        "a" | "lib" => Some("staticlib"),
        "rsp" => Some("rsp"),
        "ltar" => Some("ltar"),
        "bc" => Some("bc"),
        "o" => Some("obj"),
        "export" | "noexport"
            if path
                .file_stem()
                .and_then(|s| s.to_str())
                .is_some_and(|s| s.ends_with(".c.o")) =>
        {
            Some("obj")
        }
        "exe" => Some("exe"),
        "" if path
            .strip_prefix(build_dir)
            .ok()
            .and_then(|r| r.components().next())
            .is_some_and(|c| c.as_os_str() == "bin")
            || extra_bin_dirs.iter().any(|bd| path.starts_with(bd)) =>
        {
            Some("exe")
        }
        _ => None,
    }
}

pub(super) fn collect_workspace_bin_dirs(canon_proj: &Path) -> Vec<PathBuf> {
    let mut dirs = Vec::new();
    if let Ok(cfg) = crate::module_builder::resolve_project_config(canon_proj) {
        for pkg in std::iter::once(&cfg.root_pkg).chain(&cfg.dep_pkgs) {
            let b = pkg.pkg_root.join(&pkg.build_dir).join(&pkg.bin_dir);
            if b.starts_with(canon_proj) && !dirs.contains(&b) {
                dirs.push(b);
            }
        }
    }
    dirs
}

/// Stage compiled `.olean`, `.ilean`, `.c`, native `.c.o*`/`.so`/`.dylib`/`.dll`/`.rsp`, and Lake sidecars
/// from workspace `.lake/build` directories into the immutable CAS blobs directory without opening a SQLite
/// transaction, returning `(outputs, reg_blobs)`.
#[allow(clippy::type_complexity)]
pub(crate) fn stage_lake_build_outputs(
    store: &TurboStore,
    project_dir: &Path,
) -> Result<(Vec<BlobEntry>, Vec<(String, String, i64, i64)>)> {
    let canon_proj = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let mut build_dirs: Vec<PathBuf> = Vec::new();
    let mut push_build_dir = |bdir: PathBuf| {
        if bdir.is_dir() {
            let canon_b = bdir.canonicalize().unwrap_or_else(|_| bdir.clone());
            if canon_b.starts_with(&canon_proj)
                && !build_dirs
                    .iter()
                    .any(|d| d.canonicalize().unwrap_or_else(|_| d.clone()) == canon_b)
            {
                build_dirs.push(bdir);
            }
        }
    };
    if let Ok(cfg) = crate::module_builder::resolve_project_config(&canon_proj) {
        push_build_dir(cfg.root_pkg.pkg_root.join(&cfg.root_pkg.build_dir));
        for dp in &cfg.dep_pkgs {
            push_build_dir(dp.pkg_root.join(&dp.build_dir));
        }
    }
    push_build_dir(project_dir.join(".lake").join("build"));
    if let Ok(entries) = fs::read_dir(project_dir.join(".lake").join("packages")) {
        let mut pkg_dirs: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
        pkg_dirs.sort();
        for pd in pkg_dirs {
            push_build_dir(pd.join(".lake").join("build"));
        }
    }
    if build_dirs.is_empty() {
        return Ok((Vec::new(), Vec::new()));
    }

    #[cfg(unix)]
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    let extra_bin_dirs = collect_workspace_bin_dirs(&canon_proj);
    let mut candidates: Vec<(PathBuf, &'static str, String, i64, i64, u64, u32, i64)> = Vec::new();
    for build_dir in &build_dirs {
        for entry in WalkDir::new(build_dir).into_iter().flatten() {
            if !entry.file_type().is_file() {
                continue;
            }
            let path = entry.path();
            let Some(kind) = classify_lake_build_artifact(path, build_dir, &extra_bin_dirs) else {
                continue;
            };

            let Ok(meta) = entry.metadata() else {
                continue;
            };
            let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&meta);
            #[cfg(unix)]
            let (mode, cand_ino) = (meta.permissions().mode(), meta.ino() as i64);
            #[cfg(not(unix))]
            let (mode, cand_ino) = (0o444u32, 0i64);
            let rel_path = path
                .strip_prefix(project_dir)
                .ok()
                .or_else(|| path.strip_prefix(&canon_proj).ok())
                .unwrap_or(path)
                .to_string_lossy()
                .replace('\\', "/");
            candidates.push((
                path.to_path_buf(),
                kind,
                rel_path,
                ms,
                mn,
                sz as u64,
                mode,
                cand_ino,
            ));
        }
    }

    stage_build_candidates(store, project_dir, candidates)
}

#[allow(clippy::type_complexity)]
pub(super) fn stage_build_candidates(
    store: &TurboStore,
    project_dir: &Path,
    mut candidates: Vec<(PathBuf, &'static str, String, i64, i64, u64, u32, i64)>,
) -> Result<(Vec<BlobEntry>, Vec<(String, String, i64, i64)>)> {
    let preserve_lake = worktree_auto_link_disabled(project_dir);
    #[cfg(unix)]
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    if candidates.is_empty() {
        return Ok((Vec::new(), Vec::new()));
    }
    candidates.sort_by(|a, b| a.2.cmp(&b.2));
    candidates.dedup_by(|a, b| a.2 == b.2);

    let mut sh = blake3::Hasher::new();
    sh.update(b"lake-build-ingest:v3\n");
    sh.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    sh.update(b"\n");
    for (_, kind, rel_path, ms, mn, sz, mode, _) in &candidates {
        sh.update(rel_path.as_bytes());
        sh.update(b":");
        sh.update(kind.as_bytes());
        sh.update(b":");
        sh.update(&ms.to_le_bytes());
        sh.update(&mn.to_le_bytes());
        sh.update(&sz.to_le_bytes());
        sh.update(&mode.to_le_bytes());
        sh.update(b"\n");
    }
    let ingest_cache_path = store.fast_staging_dir().join(format!(
        "lake_build_ingest_v2_{}.json",
        &sh.finalize().to_hex()[..24]
    ));

    let mut entries: Vec<BlobEntry> = fs::read(&ingest_cache_path)
        .ok()
        .and_then(|b| serde_json::from_slice::<Vec<BlobEntry>>(&b).ok())
        .filter(|v| v.len() == candidates.len())
        .unwrap_or_default();

    let entries = if entries.len() == candidates.len() {
        // Revalidate mutable sidecars directly from bytes rather than trusting stat metadata.
        for (entry, (path, kind, _, _, _, _, _, _)) in entries.iter_mut().zip(candidates.iter()) {
            if matches!(
                *kind,
                "trace" | "hash" | "c" | "manifest" | "rsp" | "setup_json"
            ) {
                let bytes = fs::read(path)?;
                entry.blob_hash = blake3::hash(&bytes).to_hex().to_string();
                entry.size_bytes = bytes.len() as u64;
            }
        }
        entries
    } else {
        let n_threads = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .min(candidates.len())
            .max(1);
        let chunk_size = candidates.len().div_ceil(n_threads);

        let mut computed: Vec<BlobEntry> = Vec::with_capacity(candidates.len());
        std::thread::scope(|s| -> Result<()> {
            let mut handles = Vec::with_capacity(n_threads);
            for chunk in candidates.chunks(chunk_size) {
                handles.push(s.spawn(move || -> Result<Vec<BlobEntry>> {
                    let mut local = Vec::with_capacity(chunk.len());
                    for (path, kind, rel_path, _, _, _, _, _) in chunk {
                        let bytes = fs::read(path)?;
                        local.push(BlobEntry {
                            blob_hash: blake3::hash(&bytes).to_hex().to_string(),
                            kind: (*kind).to_string(),
                            size_bytes: bytes.len() as u64,
                            rel_path: rel_path.clone(),
                        });
                    }
                    Ok(local)
                }));
            }
            for h in handles {
                computed.extend(
                    h.join()
                        .map_err(|_| anyhow::anyhow!("ingest worker panicked"))??,
                );
            }
            Ok(())
        })?;
        computed.sort_by(|a, b| a.rel_path.cmp(&b.rel_path));
        if let Ok(bytes) = serde_json::to_vec(&computed) {
            let _ = crate::shm_cache::atomic_write_shm(&ingest_cache_path, &bytes);
        }
        computed
    };

    let shared_blobs = pack::shared_cas_blobs_dir_for_store(&store.root);
    let fallback_shm_blobs = pack::shared_cas_blobs_dir();
    let has_distinct_fallback = fallback_shm_blobs != shared_blobs;
    let mut seen_prefix = [false; 256];
    let mut created_parents: Vec<PathBuf> = Vec::new();
    let mut seen_shared_prefix = [false; 256];
    let mut seen_blobs = std::collections::HashSet::with_capacity(entries.len());
    let mut reg_blobs = Vec::with_capacity(entries.len());

    for (entry, (path, kind, _, _, _, _, mode, _cand_ino)) in entries.iter().zip(candidates.iter())
    {
        // Never hardlink root `.lake/build` or mutable sidecars into CAS or mark them read-only (`0o444`):
        // in-place `lake build` / `lean -o` writes must never mutate CAS blobs (`nlink == 1`, `0o644` / `0o755`).
        #[cfg(unix)]
        {
            let is_exec = matches!(*kind, "exe" | "exe_bin");
            let target_mode = if is_exec { 0o755 } else { 0o644 };
            let needs_exec_fix = is_exec && (*mode & 0o111) == 0;
            let nlink = fs::metadata(path)?.nlink();
            if !preserve_lake && (needs_exec_fix || (*mode & 0o200) == 0 || nlink > 1) {
                let bytes = fs::read(path)?;
                crate::db::write_bytes_durable(path, &bytes, &[])?;
                if is_exec {
                    fs::set_permissions(path, fs::Permissions::from_mode(target_mode))?;
                }
                if fs::metadata(path)?.nlink() != 1 {
                    anyhow::bail!(
                        "Failed to detach `.lake/build` artifact `{}` from CAS hard-link",
                        path.display()
                    );
                }
            }
        }
        if !seen_blobs.insert(entry.blob_hash.clone()) {
            continue;
        }
        let prefix = if entry.blob_hash.len() >= 2 {
            &entry.blob_hash[0..2]
        } else {
            "00"
        };
        let p_idx = u8::from_str_radix(prefix, 16).unwrap_or(0) as usize;
        let dest = store.blob_path(&entry.blob_hash);
        if !seen_prefix[p_idx] {
            seen_prefix[p_idx] = true;
            if let Some(parent) = dest.parent() {
                created_parents.extend(crate::db::ensure_dir_tracking(parent, &store.root)?);
            }
        }
        let shared_dir = shared_blobs.join(prefix);
        let shared_p = shared_dir.join(&entry.blob_hash);
        let fallback_p = fallback_shm_blobs.join(prefix).join(&entry.blob_hash);
        let mut sync_shared = |dest_p: &Path| {
            let shared_stop = shared_blobs.parent().unwrap_or(&shared_blobs);
            let shared_created = if !seen_shared_prefix[p_idx] {
                let Ok(dirs) = crate::db::ensure_dir_tracking(&shared_dir, shared_stop) else {
                    return;
                };
                seen_shared_prefix[p_idx] = true;
                dirs
            } else {
                Vec::new()
            };
            let shared_intact = crate::db::open_regular_nofollow(&shared_p)
                .ok()
                .is_some_and(|(mut sf, sm)| {
                    use std::io::Read;
                    #[cfg(unix)]
                    let owned = crate::db::is_exclusively_created_immutable_cas_inode(
                        &sm,
                        &entry.blob_hash,
                    );
                    #[cfg(not(unix))]
                    let owned = true;
                    if !owned {
                        return false;
                    }
                    let mut b = Vec::with_capacity(sm.len().min(64 * 1024 * 1024) as usize);
                    sf.read_to_end(&mut b).is_ok()
                        && b.len() as u64 == entry.size_bytes
                        && blake3::hash(&b).to_hex().as_str() == entry.blob_hash
                });
            if !shared_intact {
                let _ = crate::db::publish_verified_durable_blob(
                    dest_p,
                    &shared_p,
                    &entry.blob_hash,
                    entry.size_bytes,
                    &shared_created,
                );
            } else {
                for dir in &shared_created {
                    let _ = crate::db::sync_dir(dir);
                }
            }
        };
        let existing_dest_ino =
            crate::db::open_regular_nofollow(&dest)
                .ok()
                .and_then(|(mut f, m)| {
                    use std::io::Read;
                    #[cfg(unix)]
                    if !crate::db::is_exclusively_created_immutable_cas_inode(&m, &entry.blob_hash)
                    {
                        return None;
                    }
                    let mut buf = Vec::with_capacity(m.len().min(64 * 1024 * 1024) as usize);
                    if f.read_to_end(&mut buf).is_ok()
                        && buf.len() as u64 == entry.size_bytes
                        && blake3::hash(&buf).to_hex().as_str() == entry.blob_hash
                    {
                        crate::db::durability_barrier(&f).ok()?;
                        Some(m.ino() as i64)
                    } else {
                        None
                    }
                });
        let ino = if let Some(d_ino) = existing_dest_ino {
            if let Some(parent) = dest.parent() {
                crate::db::sync_dir(parent)?;
            }
            sync_shared(&dest);
            d_ino
        } else if let Ok(published_ino) = crate::db::publish_verified_durable_blob(
            &shared_p,
            &dest,
            &entry.blob_hash,
            entry.size_bytes,
            &[],
        )
        .or_else(|e| {
            if has_distinct_fallback {
                crate::db::publish_verified_durable_blob(
                    &fallback_p,
                    &dest,
                    &entry.blob_hash,
                    entry.size_bytes,
                    &[],
                )
            } else {
                Err(e)
            }
        }) {
            sync_shared(&dest);
            published_ino
        } else {
            let bytes = match fs::read(path) {
                Ok(b) => b,
                Err(e) => {
                    created_parents.sort_by_key(|p| std::cmp::Reverse(p.components().count()));
                    created_parents.dedup();
                    for dir in &created_parents {
                        let _ = crate::db::sync_dir(dir);
                    }
                    return Err(e.into());
                }
            };
            if blake3::hash(&bytes).to_hex().as_str() != entry.blob_hash {
                created_parents.sort_by_key(|p| std::cmp::Reverse(p.components().count()));
                created_parents.dedup();
                for dir in &created_parents {
                    let _ = crate::db::sync_dir(dir);
                }
                anyhow::bail!(
                    "Concurrent mutation detected while staging `{}` into CAS",
                    path.display()
                );
            }
            let (ino, _) = match crate::db::ensure_blob_file(
                &store.root,
                &dest,
                &entry.blob_hash,
                &bytes,
                false,
            ) {
                Ok(v) => v,
                Err(e) => {
                    created_parents.sort_by_key(|p| std::cmp::Reverse(p.components().count()));
                    created_parents.dedup();
                    for dir in &created_parents {
                        let _ = crate::db::sync_dir(dir);
                    }
                    return Err(e);
                }
            };
            sync_shared(&dest);
            ino
        };
        reg_blobs.push((
            entry.blob_hash.clone(),
            entry.kind.clone(),
            entry.size_bytes as i64,
            ino,
        ));
    }
    created_parents.sort_by_key(|p| std::cmp::Reverse(p.components().count()));
    created_parents.dedup();
    for dir in created_parents {
        crate::db::sync_dir(&dir)?;
    }

    Ok((entries, reg_blobs))
}

#[allow(clippy::type_complexity)]
pub(crate) fn stage_lake_build_outputs_for_paths(
    store: &TurboStore,
    project_dir: &Path,
    paths: &[PathBuf],
) -> Result<(Vec<BlobEntry>, Vec<(String, String, i64, i64)>)> {
    #[cfg(unix)]
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    let canon_proj = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let mut build_dirs: Vec<PathBuf> = Vec::new();
    let mut push_build_dir = |bdir: PathBuf| {
        if bdir.is_dir() {
            let canon_b = bdir.canonicalize().unwrap_or_else(|_| bdir.clone());
            if canon_b.starts_with(&canon_proj)
                && !build_dirs
                    .iter()
                    .any(|d| d.canonicalize().unwrap_or_else(|_| d.clone()) == canon_b)
            {
                build_dirs.push(bdir);
            }
        }
    };
    if let Ok(cfg) = crate::module_builder::resolve_project_config(&canon_proj) {
        push_build_dir(cfg.root_pkg.pkg_root.join(&cfg.root_pkg.build_dir));
        for dp in &cfg.dep_pkgs {
            push_build_dir(dp.pkg_root.join(&dp.build_dir));
        }
    }
    push_build_dir(project_dir.join(".lake").join("build"));
    if let Ok(entries) = fs::read_dir(project_dir.join(".lake").join("packages")) {
        let mut pkg_dirs: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
        pkg_dirs.sort();
        for pd in pkg_dirs {
            push_build_dir(pd.join(".lake").join("build"));
        }
    }

    let extra_bin_dirs = collect_workspace_bin_dirs(&canon_proj);
    let mut candidates = Vec::new();
    for p in paths {
        let Ok(meta) = fs::symlink_metadata(p) else {
            continue;
        };
        if !meta.file_type().is_file() {
            continue;
        }
        let default_bdir = project_dir.join(".lake").join("build");
        let bdir = build_dirs
            .iter()
            .find(|bd| p.starts_with(bd))
            .unwrap_or(&default_bdir);
        let Some(kind) = classify_lake_build_artifact(p, bdir, &extra_bin_dirs) else {
            continue;
        };
        let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&meta);
        #[cfg(unix)]
        let (mode, cand_ino) = (meta.permissions().mode(), meta.ino() as i64);
        #[cfg(not(unix))]
        let (mode, cand_ino) = (0o444u32, 0i64);
        let rel_path = p
            .strip_prefix(project_dir)
            .ok()
            .or_else(|| p.strip_prefix(&canon_proj).ok())
            .unwrap_or(p)
            .to_string_lossy()
            .replace('\\', "/");
        candidates.push((p.clone(), kind, rel_path, ms, mn, sz as u64, mode, cand_ino));
    }
    stage_build_candidates(store, project_dir, candidates)
}

/// Deduplicate `.lake/packages` across multi-agent worktrees:
/// 1. Removes leftover `*.barrel` archive files in `.lake/packages` and `.lake/cache`.
/// 2. Strips `.git/objects/pack/*.pack` and loose objects inside `.lake/packages/*/.git/objects`.
/// 3. Deduplicates `.olean`, `.olean.private`, `.olean.server`, and `.ilean` files inside
///    `.lake/packages` against a shared `store.root.join("pkg_cas")` directory via BLAKE3 + hardlinking.
///
/// The worktree opt-out skips the entire operation, including archive/object removal.
pub fn dedup_worktree_packages(
    store: &TurboStore,
    project_dir: &Path,
) -> Result<serde_json::Value> {
    if worktree_auto_link_disabled(project_dir) {
        return Ok(serde_json::json!({
            "status": "worktree_link_disabled",
            "project_dir": project_dir.display().to_string(),
            "files_hardlinked": 0,
            "bytes_saved": 0,
        }));
    }
    #[cfg(unix)]
    use std::os::unix::fs::MetadataExt;

    let t0 = Instant::now();
    let lake_dir = project_dir.join(".lake");
    let packages_dir = lake_dir.join("packages");
    let pkg_cas_dir = store.root.join("pkg_cas");

    let mut purged_barrels = 0u64;
    let mut purged_git_packs = 0u64;
    let mut hardlinked_files = 0u64;
    let mut freed_bytes = 0u64;
    let mut deduped_bytes = 0u64;

    if lake_dir.is_dir() {
        let _pub_guard = crate::db::acquire_cas_publication_guard(&store.root)?;
        let mut stack = vec![lake_dir];
        while let Some(dir) = stack.pop() {
            let Ok(entries) = fs::read_dir(&dir) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                let Ok(ft) = entry.file_type() else {
                    continue;
                };
                if ft.is_symlink() {
                    continue;
                }
                if ft.is_dir() {
                    stack.push(path);
                    continue;
                }
                if !ft.is_file() {
                    continue;
                }

                let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
                let path_str = path.to_string_lossy();

                // 1. Purge *.barrel archives
                if name.ends_with(".barrel") {
                    let sz = entry.metadata().map(|m| m.len()).unwrap_or(0);
                    if fs::remove_file(&path).is_ok() {
                        purged_barrels += 1;
                        freed_bytes += sz;
                    }
                    continue;
                }

                // 2. Strip .lake/packages/*/.git/objects/* (both packfiles and loose objects)
                if path_str.contains("/.git/objects/") {
                    let sz = entry.metadata().map(|m| m.len()).unwrap_or(0);
                    if fs::remove_file(&path).is_ok() {
                        if name.ends_with(".pack") || name.ends_with(".idx") {
                            purged_git_packs += 1;
                        }
                        freed_bytes += sz;
                    }
                    continue;
                }

                // 3. Hardlink duplicate package artifacts (.olean, .olean.private, .olean.server, .ilean) via pkg_cas
                let is_dedup_ext = name.ends_with(".olean")
                    || name.ends_with(".olean.private")
                    || name.ends_with(".olean.server")
                    || name.ends_with(".ilean");
                if is_dedup_ext && path.starts_with(&packages_dir) {
                    let Ok((mut src_file, meta)) = crate::db::open_regular_nofollow(&path) else {
                        continue;
                    };
                    if meta.len() == 0 {
                        continue;
                    }
                    use std::io::Read;
                    let mut bytes = Vec::with_capacity(meta.len() as usize);
                    if src_file.read_to_end(&mut bytes).is_err() || bytes.is_empty() {
                        continue;
                    }
                    drop(src_file);
                    let sz = bytes.len() as u64;
                    let hash_hex = blake3::hash(&bytes).to_hex().to_string();

                    let shard_dir = pkg_cas_dir.join(&hash_hex[0..2]);
                    let Ok(_created) = crate::db::ensure_dir_tracking(&shard_dir, &store.root)
                    else {
                        continue;
                    };
                    let cas_file = shard_dir.join(&hash_hex);

                    let cas_ready = crate::db::ensure_blob_file(
                        &store.root,
                        &cas_file,
                        &hash_hex,
                        &bytes,
                        false,
                    )
                    .is_ok();

                    if cas_ready {
                        #[cfg(unix)]
                        let already_same_cas_inode = crate::db::open_regular_nofollow(&cas_file)
                            .ok()
                            .is_some_and(|(_cf, cm)| {
                                cm.dev() == meta.dev()
                                    && cm.ino() == meta.ino()
                                    && crate::db::is_exclusively_created_immutable_cas_inode(
                                        &cm, &hash_hex,
                                    )
                            });
                        #[cfg(not(unix))]
                        let already_same_cas_inode = false;

                        if !already_same_cas_inode
                            && crate::db::install_verified_blob_to_path(
                                &cas_file, &path, &hash_hex, sz,
                            )
                            .is_ok()
                        {
                            hardlinked_files += 1;
                            deduped_bytes += sz;
                        }
                    }
                }
            }
        }
    }

    let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
    let total_saved_bytes = freed_bytes + deduped_bytes;
    Ok(serde_json::json!({
        "status": "worktree_packages_deduped",
        "project_dir": project_dir.display().to_string(),
        "barrels_removed": purged_barrels,
        "purged_barrels": purged_barrels,
        "purged_git_packs": purged_git_packs,
        "files_hardlinked": hardlinked_files,
        "hardlinked_files": hardlinked_files,
        "freed_bytes": freed_bytes,
        "deduped_bytes": deduped_bytes,
        "bytes_saved": total_saved_bytes,
        "total_saved_bytes": total_saved_bytes,
        "elapsed_ms": elapsed_ms,
    }))
}

/// Execute `turbo-lean build` with proof-irrelevant interface hashing, singleflight coalescing,
/// and zero-write-lock worktree materialization on cache hits.
pub fn run_build_command(
    store: &mut TurboStore,
    json_output: bool,
    targets: Vec<String>,
    project_dir: PathBuf,
    trust_domain: String,
    pin_level: i64,
    seed_shards: bool,
) -> Result<()> {
    run_build_command_with_cas_replay(
        store,
        json_output,
        targets,
        project_dir,
        trust_domain,
        pin_level,
        seed_shards,
        false,
    )
}

pub fn validate_lnir_expr_v1_blob(bytes: &[u8]) -> bool {
    fn parse_lvl(bytes: &[u8]) -> Option<&[u8]> {
        let (&tag, rest) = bytes.split_first()?;
        match tag {
            0x00 => Some(rest),
            0x01 => parse_lvl(rest),
            0x02 | 0x03 => {
                let r1 = parse_lvl(rest)?;
                parse_lvl(r1)
            }
            _ => None,
        }
    }
    fn parse_lvls(mut bytes: &[u8], count: usize) -> Option<&[u8]> {
        for _ in 0..count {
            bytes = parse_lvl(bytes)?;
        }
        Some(bytes)
    }
    fn parse_expr(bytes: &[u8], fuel: usize) -> Option<&[u8]> {
        if fuel == 0 {
            return None;
        }
        let (&tag, rest) = bytes.split_first()?;
        match tag {
            0x00 => {
                let (_, tail) = rest.split_first()?;
                Some(tail)
            }
            0x01 => parse_lvl(rest),
            0x02 => {
                if rest.len() < 2 {
                    return None;
                }
                let name_len = rest[0] as usize;
                let lvl_count = rest[1] as usize;
                let after_hdr = &rest[2..];
                if after_hdr.len() < name_len {
                    return None;
                }
                let name_bytes = &after_hdr[..name_len];
                if std::str::from_utf8(name_bytes).is_err() {
                    return None;
                }
                parse_lvls(&after_hdr[name_len..], lvl_count)
            }
            0x03 | 0x04 | 0x05 => {
                let r1 = parse_expr(rest, fuel - 1)?;
                parse_expr(r1, fuel - 1)
            }
            0x06 => {
                let r1 = parse_expr(rest, fuel - 1)?;
                let r2 = parse_expr(r1, fuel - 1)?;
                parse_expr(r2, fuel - 1)
            }
            _ => None,
        }
    }
    if bytes.len() < 5 || &bytes[..4] != b"LNE1" {
        return false;
    }
    matches!(parse_expr(&bytes[4..], 256), Some(rem) if rem.is_empty())
}

pub(super) fn verify_cas_expr_shard_payload(bytes: &[u8], expected_decl: &str) -> bool {
    if validate_lnir_expr_v1_blob(bytes) {
        return true;
    }
    if bytes.starts_with(b"verified:seeded:") && bytes.len() > "verified:seeded:".len() {
        return true;
    }
    if let Ok(val) = serde_json::from_slice::<serde_json::Value>(bytes) {
        if let Some(d) = val["decl"].as_str() {
            if crate::splitter::canonicalize_lean_name(d)
                == crate::splitter::canonicalize_lean_name(expected_decl)
            {
                return true;
            }
        }
    }
    false
}

/// Replay statistics for CAS `expr_shard` proof-blob verification (G2b).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct CasExprReplayStats {
    /// Shards whose cached payload was found and verified.
    pub replayed: usize,
    /// Shards with no cached `expr_shard` entry in the CAS.
    pub missing: usize,
    /// Shards whose cached payload failed `verify_cas_expr_shard_payload`.
    pub invalid: usize,
}

fn replay_project_cas_expr_shards_inner(
    store: &mut TurboStore,
    canon_dir: &Path,
    toolchain: &str,
    trust_domain: &str,
    scoped_files: Option<&[PathBuf]>,
    fail_closed: bool,
) -> Result<CasExprReplayStats> {
    let lean_files: Vec<PathBuf> = match scoped_files {
        Some(files) if !files.is_empty() => files.to_vec(),
        _ => collect_lean_files(canon_dir),
    };
    let (split_entries, _) = load_and_split_files_cached(store, &lean_files)?;
    let _ = crate::module_builder::try_project_lake_inputs_tag(canon_dir)?;
    let pkg_cfg_opt = crate::module_builder::optional_package_config(canon_dir)?;
    let mut stats = CasExprReplayStats::default();
    for (lf, _src, split) in &split_entries {
        if split.shards.is_empty() || !split.hygiene.is_clean_for_certification() {
            continue;
        }
        let file_lean_args = pkg_cfg_opt
            .as_ref()
            .map(|pkg| crate::module_builder::resolve_file_lean_args_in_package(pkg, lf))
            .unwrap_or_default();
        let file_has_sorry = split.hygiene.has_sorry;
        for shard in &split.shards {
            if file_has_sorry
                && splitter::audit_hygiene(&splitter::strip_lean_comments(&shard.proof_text))
                    .has_sorry
            {
                continue;
            }
            let shard_key = compute_shard_key_with_args(toolchain, shard, &file_lean_args);
            let Some(entries) = store.get_cached_action_no_hit_bump(&shard_key, trust_domain)?
            else {
                if fail_closed {
                    anyhow::bail!(
                        "--replay-cas-expr failed closed: missing cached expr_shard in CAS for theorem `{}` (key={})",
                        shard.name,
                        shard_key
                    );
                }
                stats.missing += 1;
                continue;
            };
            let valid = entries.iter().any(|entry| {
                store
                    .read_verified_blob(&entry.blob_hash)
                    .is_some_and(|b| verify_cas_expr_shard_payload(&b, &shard.name))
            });
            if !valid {
                if fail_closed {
                    anyhow::bail!(
                        "--replay-cas-expr failed closed: corrupted or invalid CAS expr_shard blob for theorem `{}` (key={})",
                        shard.name,
                        shard_key
                    );
                }
                stats.invalid += 1;
                continue;
            }
            stats.replayed += 1;
        }
    }
    Ok(stats)
}

/// Fail-closed CAS proof replay behind the explicit `--replay-cas-expr` flag: a missing or
/// corrupted blob is a build error. Returns the number of replayed shards.
pub fn replay_project_cas_expr_shards(
    store: &mut TurboStore,
    canon_dir: &Path,
    toolchain: &str,
    trust_domain: &str,
    scoped_files: Option<&[PathBuf]>,
) -> Result<usize> {
    Ok(replay_project_cas_expr_shards_inner(
        store,
        canon_dir,
        toolchain,
        trust_domain,
        scoped_files,
        true,
    )?
    .replayed)
}

/// Best-effort CAS proof replay for the G2b warm-hit default: a missing or corrupted blob
/// is counted and skipped (the build transparently keeps its already-materialized
/// baseline), never a failure.
pub fn replay_project_cas_expr_shards_best_effort(
    store: &mut TurboStore,
    canon_dir: &Path,
    toolchain: &str,
    trust_domain: &str,
    scoped_files: Option<&[PathBuf]>,
) -> Result<CasExprReplayStats> {
    replay_project_cas_expr_shards_inner(
        store,
        canon_dir,
        toolchain,
        trust_domain,
        scoped_files,
        false,
    )
}

/// G2b opt-out: `TURBO_LEAN_NO_WARM_CAS_REPLAY=1` disables the warm-hit default replay
/// (same relaxed-bool grammar as the other `TURBO_LEAN_NO_*` switches).
pub(crate) fn warm_cas_replay_disabled() -> bool {
    crate::shm_cache::parse_relaxed_bool(
        &std::env::var("TURBO_LEAN_NO_WARM_CAS_REPLAY").unwrap_or_default(),
    ) == Some(true)
}

/// G2b decision: CAS proof replay runs by default exactly on a warm (cache-hit) build
/// path, unless the explicit fail-closed flag already runs it or the operator opted out.
pub(crate) fn should_replay_cas_expr_on_warm_hit(
    explicit_replay: bool,
    cache_hit: bool,
    opt_out: bool,
) -> bool {
    !explicit_replay && cache_hit && !opt_out
}

/// What one `run_build_command_with_cas_replay` branch did about CAS expr replay (G2b).
#[derive(Debug)]
pub(crate) struct CasExprBuildReplay {
    pub(crate) replayed: usize,
    /// Warm-default shards skipped because they were never seeded into the CAS.
    pub(crate) missing: usize,
    /// Warm-default shards whose cached payload failed verification: corruption or
    /// tamper evidence, counted on its own and warned about, never folded into
    /// `missing`.
    pub(crate) invalid: usize,
    /// `"explicit"` (fail-closed flag), `"warm_default"` (G2b), or `"off"`.
    pub(crate) mode: &'static str,
}

/// The one selector every `run_build_command_with_cas_replay` branch calls (G2b):
/// the explicit flag keeps the fail-closed wrapper; a warm (cache-hit) path gets the
/// best-effort replay by default; a cold path replays nothing.
pub(crate) fn run_cas_expr_replay_for_build(
    store: &mut TurboStore,
    canon_dir: &Path,
    toolchain: &str,
    trust_domain: &str,
    scoped_files: Option<&[PathBuf]>,
    explicit_replay: bool,
    cache_hit: bool,
) -> Result<CasExprBuildReplay> {
    if explicit_replay {
        let replayed = replay_project_cas_expr_shards(
            store,
            canon_dir,
            toolchain,
            trust_domain,
            scoped_files,
        )?;
        return Ok(CasExprBuildReplay {
            replayed,
            missing: 0,
            invalid: 0,
            mode: "explicit",
        });
    }
    if should_replay_cas_expr_on_warm_hit(explicit_replay, cache_hit, warm_cas_replay_disabled()) {
        let stats = replay_project_cas_expr_shards_best_effort(
            store,
            canon_dir,
            toolchain,
            trust_domain,
            scoped_files,
        )?;
        if stats.invalid > 0 {
            eprintln!(
                "[turbo-lean][warn] warm CAS replay: {} corrupted or invalid expr_shard blob(s) skipped (tamper/corruption evidence; run `turbo-lean build --replay-cas-expr` to fail closed)",
                stats.invalid
            );
        }
        return Ok(CasExprBuildReplay {
            replayed: stats.replayed,
            missing: stats.missing,
            invalid: stats.invalid,
            mode: "warm_default",
        });
    }
    Ok(CasExprBuildReplay {
        replayed: 0,
        missing: 0,
        invalid: 0,
        mode: "off",
    })
}

#[allow(clippy::too_many_arguments)]
pub fn run_build_command_with_cas_replay(
    store: &mut TurboStore,
    json_output: bool,
    targets: Vec<String>,
    project_dir: PathBuf,
    trust_domain: String,
    pin_level: i64,
    seed_shards: bool,
    replay_cas_expr: bool,
) -> Result<()> {
    // One top-level command, one Lake-input memo window.
    crate::module_builder::reset_lake_inputs_tag_memo();
    let t0 = Instant::now();
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.clone());
    let project_name = canon_dir
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "lean-project".to_string());
    let toolchain = detect_toolchain(&canon_dir);
    let emit_build_telemetry = |ev: serde_json::Value| {
        crate::mcp::emit_cli_telemetry_event(
            Some(&canon_dir),
            trust_domain == "trusted",
            ev,
            "turbo_lean_events.jsonl",
        );
    };
    let is_untrusted = trust_domain.starts_with("untrusted");
    let mut resolved_exe_targets: Vec<crate::module_builder::ResolvedExeLinkTarget> = Vec::new();
    let mut module_prep_targets: Vec<String> = targets.clone();
    if has_lake_config(&canon_dir) {
        let cfg =
            crate::module_builder::resolve_project_config_with_trust(&canon_dir, is_untrusted)
                .with_context(|| {
                    format!(
                        "Static Lake config validation failed for {}",
                        canon_dir.display()
                    )
                })?;
        let _ = crate::module_builder::workspace_lake_inputs_digest(&cfg)?;
        let (exe_t, prep_t) = if is_untrusted {
            (Vec::new(), targets.clone())
        } else {
            crate::module_builder::resolve_requested_exe_link_targets(&cfg, &targets)
        };
        if !targets.is_empty() && (is_untrusted || exe_t.is_empty()) {
            let build_report = crate::module_builder::build_project_modules_native(
                store,
                &canon_dir,
                &targets,
                &trust_domain,
                pin_level,
                is_untrusted,
                json_output,
                None,
            )?;
            let env_key = TurboStore::compute_lake_env_key(&canon_dir);
            let resolved_env = resolve_or_share_lake_env(store, &canon_dir, &env_key)?;
            if let Some((ref env_vars, is_new)) = resolved_env {
                if is_new {
                    let _ = store.put_lake_env(&env_key, env_vars);
                }
                if !crate::zygote::daemon_disabled() {
                    pack::warm_local_zygote_daemon_nonblocking(store, env_vars);
                }
            }
            let seeded_shards = if seed_shards {
                seed_theorem_shards_for_files(
                    store,
                    &canon_dir,
                    &toolchain,
                    &trust_domain,
                    &build_report.cone_source_paths,
                )?
                .1
            } else {
                0
            };
            let cache_hit = build_report.modules_compiled == 0
                && (build_report.modules_cached > 0 || build_report.modules_up_to_date_reused > 0);
            // G2b: on a warm target-cone hit, CAS proof replay runs by default (best-effort).
            let cas_replay = run_cas_expr_replay_for_build(
                store,
                &canon_dir,
                &toolchain,
                &trust_domain,
                Some(&build_report.cone_source_paths),
                replay_cas_expr,
                cache_hit,
            )?;
            let dur_ms = t0.elapsed().as_millis() as i64;
            emit_build_telemetry(serde_json::json!({
                "schema": "turbo-lean.telemetry.v1",
                "tool_name": "build",
                "command": "build",
                "decl_name": project_name,
                "status": if cache_hit { "cache_hit" } else { "built" },
                "cache_hit": cache_hit,
                "accepted": true,
                "target_cone_scoped": true,
                "targets": targets,
                "modules_total": build_report.modules_total,
                "modules_up_to_date_reused": build_report.modules_up_to_date_reused,
                "modules_compiled": build_report.modules_compiled,
                "modules_cached": build_report.modules_cached,
                "shards_seeded": seeded_shards,
                "cas_expr_replayed": cas_replay.replayed,
                "cas_expr_replay_missing": cas_replay.missing,
                "cas_expr_replay_invalid": cas_replay.invalid,
                "cas_expr_replay_mode": cas_replay.mode,
                "elapsed_ms": dur_ms,
            }));
            if json_output {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "status": if cache_hit { "cache_hit" } else { "built" },
                        "build_engine": "native_module_dag",
                        "target_cone_scoped": true,
                        "targets": targets,
                        "modules_total": build_report.modules_total,
                        "modules_up_to_date_reused": build_report.modules_up_to_date_reused,
                        "modules_compiled": build_report.modules_compiled,
                        "modules_cached": build_report.modules_cached,
                        "shards_seeded": seeded_shards,
                        "cas_expr_replayed": cas_replay.replayed,
                        "cas_expr_replay_missing": cas_replay.missing,
                        "cas_expr_replay_invalid": cas_replay.invalid,
                        "cas_expr_replay_mode": cas_replay.mode,
                        "config_digest": build_report.config_digest,
                        "elapsed_ms": dur_ms
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] BUILT TARGET CONE {} ({} modules: {} reused, {} cached, {} compiled in {} ms)",
                    project_name,
                    build_report.modules_total,
                    build_report.modules_up_to_date_reused,
                    build_report.modules_cached,
                    build_report.modules_compiled,
                    dur_ms
                );
            }
            return Ok(());
        }
        resolved_exe_targets = exe_t;
        module_prep_targets = prep_t;
    }
    let (action_key, interface_hash, file_hashes) = compute_project_interface_key_fast_summary(
        store,
        &canon_dir,
        &toolchain,
        &targets,
        &trust_domain,
    )?;

    let has_external_dep_build = has_out_of_tree_dep_build_dir(&canon_dir);
    let outcome = if has_external_dep_build {
        None
    } else {
        Some(store.acquire_singleflight(&action_key, &toolchain, "module_full", &trust_domain)?)
    };
    let link_resolved_executables =
        |exe_targets: &[crate::module_builder::ResolvedExeLinkTarget]| -> Result<()> {
            if exe_targets.is_empty() || is_untrusted {
                return Ok(());
            }
            if targets.is_empty() && worktree_auto_link_disabled(&canon_dir) {
                return Ok(());
            }
            let specs: Vec<String> = exe_targets.iter().map(|t| t.lake_spec.clone()).collect();
            lake_build_modules(&canon_dir, &specs, None)?;
            for exe_t in exe_targets {
                if !exe_t
                    .binary_path
                    .metadata()
                    .is_ok_and(|m| m.is_file() && m.len() > 0)
                {
                    anyhow::bail!(
                    "Lake build of `{}` succeeded without producing non-empty executable at `{}`",
                    exe_t.lake_spec,
                    exe_t.binary_path.display()
                );
                }
            }
            Ok(())
        };
    match outcome {
        Some(SingleflightOutcome::CacheHit { outputs, coalesced }) => {
            let linked = store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
            ensure_materialized_outputs_replayed_in_store(
                store,
                &canon_dir,
                &outputs,
                &file_hashes,
                &targets,
            )?;
            if !json_output {
                for entry in &outputs {
                    if !entry.rel_path.ends_with(".trace") || entry.rel_path.contains("/packages/")
                    {
                        continue;
                    }
                    let trace_path = canon_dir.join(&entry.rel_path);
                    let Ok(bytes) = fs::read(&trace_path) else {
                        continue;
                    };
                    let Ok(val) = serde_json::from_slice::<serde_json::Value>(&bytes) else {
                        continue;
                    };
                    if let Some(log_arr) = val.get("log").and_then(|v| v.as_array()) {
                        let rendered = crate::module_builder::format_lake_trace_log_stdout(log_arr);
                        if !rendered.is_empty() {
                            print!("{rendered}");
                        }
                    }
                }
            }
            let auto_link_off = targets.is_empty() && worktree_auto_link_disabled(&canon_dir);
            let missing_exe = !auto_link_off
                && (resolved_exe_targets.iter().any(|t| {
                    t.binary_path.starts_with(&canon_dir)
                        && !t
                            .binary_path
                            .metadata()
                            .is_ok_and(|m| m.is_file() && m.len() > 0)
                }) || resolved_exe_targets
                    .iter()
                    .any(|t| !t.binary_path.starts_with(&canon_dir)));
            if missing_exe {
                let _ = crate::module_builder::build_project_modules_native(
                    store,
                    &canon_dir,
                    &module_prep_targets,
                    &trust_domain,
                    pin_level,
                    false,
                    json_output,
                    Some(&file_hashes),
                )?;
                link_resolved_executables(&resolved_exe_targets)?;
            }
            let seeded_shards = if seed_shards {
                seed_project_theorem_shards(store, &canon_dir, &toolchain, &trust_domain, false)?.1
            } else {
                0
            };
            // G2b: this is the warm singleflight cache-hit path, so CAS proof replay runs
            // by default (best-effort) even without `--replay-cas-expr`.
            let cas_replay = run_cas_expr_replay_for_build(
                store,
                &canon_dir,
                &toolchain,
                &trust_domain,
                None,
                replay_cas_expr,
                true,
            )?;
            let elapsed_ms = t0.elapsed().as_millis();
            emit_build_telemetry(serde_json::json!({
                "schema": "turbo-lean.telemetry.v1",
                "tool_name": "build",
                "command": "build",
                "decl_name": project_name,
                "status": "cache_hit",
                "cache_hit": true,
                "accepted": true,
                "coalesced_singleflight": coalesced,
                "action_key": action_key,
                "interface_hash": interface_hash,
                "materialized_files": linked,
                "shards_seeded": seeded_shards,
                "cas_expr_replayed": cas_replay.replayed,
                "cas_expr_replay_missing": cas_replay.missing,
                "cas_expr_replay_invalid": cas_replay.invalid,
                "cas_expr_replay_mode": cas_replay.mode,
                "elapsed_ms": elapsed_ms,
            }));
            if json_output {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "status": "cache_hit",
                        "coalesced_singleflight": coalesced,
                        "action_key": action_key,
                        "interface_hash": interface_hash,
                        "materialized_files": linked,
                        "shards_seeded": seeded_shards,
                        "cas_expr_replayed": cas_replay.replayed,
                        "cas_expr_replay_missing": cas_replay.missing,
                        "cas_expr_replay_invalid": cas_replay.invalid,
                        "cas_expr_replay_mode": cas_replay.mode,
                        "elapsed_ms": elapsed_ms
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] CACHE HIT (coalesced={}) for {} ({} artifacts linked in {} ms)",
                    coalesced, project_name, linked, elapsed_ms
                );
            }
        }
        leader_opt => {
            let lease_opt = match leader_opt {
                Some(SingleflightOutcome::Leader(lease)) => Some(lease),
                _ => None,
            };
            let profile_phases = std::env::var("TURBO_LEAN_PROFILE_PHASES")
                .ok()
                .is_some_and(|v| matches!(v.trim(), "1" | "true" | "yes"));
            let mut build_report = crate::module_builder::NativeBuildReport::default();
            let oleans_up_to_date = targets.is_empty()
                && are_all_project_oleans_up_to_date(&canon_dir, &file_hashes)
                && are_all_project_oleans_replayed_in_store(store, &canon_dir, &file_hashes);
            let t_native = std::time::Instant::now();
            if !oleans_up_to_date {
                build_report = crate::module_builder::build_project_modules_native(
                    store,
                    &canon_dir,
                    &module_prep_targets,
                    &trust_domain,
                    pin_level,
                    is_untrusted,
                    json_output,
                    Some(&file_hashes),
                )?;
            }
            let native_ms = t_native.elapsed().as_millis();
            let t_link = std::time::Instant::now();
            if !resolved_exe_targets.is_empty() && (!oleans_up_to_date || !targets.is_empty()) {
                link_resolved_executables(&resolved_exe_targets)?;
            }
            let link_ms = t_link.elapsed().as_millis();
            if !targets.is_empty() && !resolved_exe_targets.is_empty() {
                let mut extra_paths: Vec<PathBuf> = Vec::new();
                for exe_t in &resolved_exe_targets {
                    if exe_t.binary_path.starts_with(&canon_dir) {
                        extra_paths.push(exe_t.binary_path.clone());
                        for suffix in [".hash", ".trace", ".rsp"] {
                            let sp =
                                PathBuf::from(format!("{}{suffix}", exe_t.binary_path.display()));
                            if sp.is_file() {
                                extra_paths.push(sp);
                            }
                        }
                    }
                    let ir_root = exe_t.pkg_root.join(".lake/build/ir");
                    if ir_root.starts_with(&canon_dir) && ir_root.is_dir() {
                        for entry in WalkDir::new(&ir_root).into_iter().flatten() {
                            if entry.file_type().is_file() {
                                let p = entry.path();
                                let fname = p.file_name().and_then(|s| s.to_str()).unwrap_or("");
                                if fname.contains(".c.o") {
                                    let stem_o = fname
                                        .strip_suffix(".hash")
                                        .or_else(|| fname.strip_suffix(".trace"))
                                        .unwrap_or(fname);
                                    if p.parent().is_some_and(|par| par.join(stem_o).is_file()) {
                                        extra_paths.push(p.to_path_buf());
                                    }
                                }
                            }
                        }
                    }
                }
                build_report.staged_target_paths.extend(extra_paths);
            }

            let t_env = std::time::Instant::now();
            let env_key = TurboStore::compute_lake_env_key(&canon_dir);
            let resolved_env = resolve_or_share_lake_env(store, &canon_dir, &env_key)?;
            let env_ms = t_env.elapsed().as_millis();

            let t_stage = std::time::Instant::now();
            let dur_ms = t0.elapsed().as_millis() as i64;
            let (outputs, manifest_hash, linked) = if has_out_of_tree_dep_build_dir(&canon_dir) {
                (Vec::new(), String::new(), 0usize)
            } else {
                let _pub_guard = crate::db::acquire_cas_publication_guard(&store.root)?;
                let (outputs, reg_blobs) = if targets.is_empty() {
                    stage_lake_build_outputs(store, &canon_dir)?
                } else {
                    stage_lake_build_outputs_for_paths(
                        store,
                        &canon_dir,
                        &build_report.staged_target_paths,
                    )?
                };
                let lake_env_to_put = resolved_env
                    .as_ref()
                    .filter(|(_, is_new)| *is_new)
                    .map(|(m, _)| (env_key.as_str(), m));
                let (manifest_hash, linked) = store.publish_ingested_worktree_action(
                    lease_opt.as_ref(),
                    &action_key,
                    &toolchain,
                    "module_full",
                    &canon_dir,
                    &project_name,
                    &reg_blobs,
                    &outputs,
                    dur_ms,
                    &trust_domain,
                    pin_level,
                    lake_env_to_put,
                    None,
                )?;
                drop(_pub_guard);
                (outputs, manifest_hash, linked)
            };
            let stage_ms = t_stage.elapsed().as_millis();

            if !crate::zygote::daemon_disabled() {
                if let Some((ref env_vars, _)) = resolved_env {
                    pack::warm_local_zygote_daemon_nonblocking(store, env_vars);
                }
            }
            let t_shards = std::time::Instant::now();
            let seeded_shards = if seed_shards {
                if !targets.is_empty() && !build_report.cone_source_paths.is_empty() {
                    seed_theorem_shards_for_files(
                        store,
                        &canon_dir,
                        &toolchain,
                        &trust_domain,
                        &build_report.cone_source_paths,
                    )?
                    .1
                } else {
                    seed_project_theorem_shards(
                        store,
                        &canon_dir,
                        &toolchain,
                        &trust_domain,
                        false,
                    )?
                    .1
                }
            } else {
                0
            };
            // G2b: a leader (cold) build just ran elaboration, so there is nothing to
            // skip; replay here stays behind the explicit fail-closed flag.
            let cas_replay = {
                let scoped = if !targets.is_empty() && !build_report.cone_source_paths.is_empty() {
                    Some(build_report.cone_source_paths.as_slice())
                } else {
                    None
                };
                run_cas_expr_replay_for_build(
                    store,
                    &canon_dir,
                    &toolchain,
                    &trust_domain,
                    scoped,
                    replay_cas_expr,
                    false,
                )?
            };
            let shards_ms = t_shards.elapsed().as_millis();
            if profile_phases {
                eprintln!(
                    "[turbo-lean][profile] lake_build: native={}ms link_exe={}ms env={}ms stage_publish={}ms seed_shards={}ms (outputs={} shards={})",
                    native_ms,
                    link_ms,
                    env_ms,
                    stage_ms,
                    shards_ms,
                    outputs.len(),
                    seeded_shards
                );
            }
            emit_build_telemetry(serde_json::json!({
                "schema": "turbo-lean.telemetry.v1",
                "tool_name": "build",
                "command": "build",
                "decl_name": project_name,
                "status": "built",
                "cache_hit": false,
                "accepted": true,
                "action_key": action_key,
                "interface_hash": interface_hash,
                "manifest_hash": manifest_hash,
                "artifacts_stored": outputs.len(),
                "materialized_files": linked,
                "shards_seeded": seeded_shards,
                "cas_expr_replayed": cas_replay.replayed,
                "cas_expr_replay_missing": cas_replay.missing,
                "cas_expr_replay_invalid": cas_replay.invalid,
                "cas_expr_replay_mode": cas_replay.mode,
                "elapsed_ms": dur_ms,
            }));

            if json_output {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "status": "built",
                        "build_engine": "native_module_dag",
                        "action_key": action_key,
                        "interface_hash": interface_hash,
                        "manifest_hash": manifest_hash,
                        "artifacts_stored": outputs.len(),
                        "materialized_files": linked,
                        "shards_seeded": seeded_shards,
                        "cas_expr_replayed": cas_replay.replayed,
                        "cas_expr_replay_missing": cas_replay.missing,
                        "cas_expr_replay_invalid": cas_replay.invalid,
                        "cas_expr_replay_mode": cas_replay.mode,
                        "modules_total": build_report.modules_total,
                        "modules_up_to_date_reused": build_report.modules_up_to_date_reused,
                        "modules_compiled": build_report.modules_compiled,
                        "modules_cached": build_report.modules_cached,
                        "config_digest": build_report.config_digest,
                        "elapsed_ms": dur_ms
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] BUILT & CACHED {} ({} artifacts, interface_hash={}.., {} ms)",
                    project_name,
                    linked,
                    &interface_hash[..12],
                    dur_ms
                );
            }
        }
    }
    Ok(())
}

pub fn run_hydrate_traces_command(json_output: bool, project_dir: PathBuf) -> Result<()> {
    let rep = crate::module_builder::hydrate_project_traces(&project_dir)?;
    if json_output {
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
                "status": "hydrated",
                "packages_scanned": rep.packages_scanned,
                "packages_updated": rep.packages_updated,
                "modules_scanned": rep.modules_scanned,
                "modules_verified": rep.modules_verified,
                "entries_written": rep.entries_written,
                "modules_stale_or_unverified": rep.modules_stale_or_unverified,
                "elapsed_ms": rep.elapsed_ms,
            }))?
        );
    } else {
        println!(
            "[turbo-lean] HYDRATED {} verified module traces across {}/{} packages ({} stale/skipped, {} ms)",
            rep.entries_written,
            rep.packages_updated,
            rep.packages_scanned,
            rep.modules_stale_or_unverified,
            rep.elapsed_ms
        );
    }
    Ok(())
}
