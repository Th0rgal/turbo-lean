//! Lake environment resolution, `/dev/shm` file-split & project-summary stat caching,
//! `.olean` freshness tracking, CAS artifact staging, and `turbo-lean build` execution.

use anyhow::{Context, Result};
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;
use walkdir::WalkDir;

use crate::db::{BlobEntry, SingleflightOutcome, TurboStore};
use crate::pack;
use crate::splitter::{self, split_lean_source};

pub(crate) fn detect_toolchain(project_dir: &Path) -> String {
    let tc_file = project_dir.join("lean-toolchain");
    if let Ok(s) = fs::read_to_string(&tc_file) {
        return s.trim().to_string();
    }
    "leanprover/lean4:v4.31.0".to_string()
}

pub(crate) fn spawn_lake_env(project_dir: &Path) -> Result<HashMap<String, String>> {
    if !project_dir.join(".lake").join("packages").is_dir() {
        let tc = detect_toolchain(project_dir);
        let tc_dir_name = tc.trim().replace('/', "--").replace(':', "---");
        let mut elan_roots = Vec::new();
        if let Ok(eh) = std::env::var("ELAN_HOME") {
            elan_roots.push(PathBuf::from(eh));
        }
        if let Ok(home) = std::env::var("HOME") {
            elan_roots.push(PathBuf::from(&home).join(".elan"));
            if let Some(parent) = Path::new(&home).parent() {
                elan_roots.push(parent.join("caches/elan"));
            }
        }
        if let Ok(path_var) = std::env::var("PATH") {
            for dir in std::env::split_paths(&path_var) {
                if let Some(parent) = dir.parent() {
                    if parent.join("toolchains").is_dir() {
                        elan_roots.push(parent.to_path_buf());
                    } else if let Some(gp) = parent.parent().and_then(|p| p.parent()) {
                        if gp.join("toolchains").is_dir() {
                            elan_roots.push(gp.to_path_buf());
                        }
                    }
                }
            }
        }

        for elan_home in elan_roots {
            let tc_root = elan_home.join("toolchains").join(&tc_dir_name);
            let lean_bin = tc_root.join("bin").join("lean");
            if lean_bin.exists() {
                let canon_proj = project_dir
                    .canonicalize()
                    .unwrap_or_else(|_| project_dir.to_path_buf());
                let proj_lib_lean = canon_proj.join(".lake/build/lib/lean");
                let tc_lib_lean = tc_root.join("lib/lean");
                let tc_lib = tc_root.join("lib");
                let tc_bin = tc_root.join("bin");
                let elan_bin = elan_home.join("bin");

                let mut env_map = HashMap::new();
                env_map.insert(
                    "ELAN_HOME".to_string(),
                    elan_home.to_string_lossy().to_string(),
                );
                env_map.insert(
                    "LAKE".to_string(),
                    tc_bin.join("lake").to_string_lossy().to_string(),
                );
                env_map.insert(
                    "LEAN_PATH".to_string(),
                    format!("{}:{}", proj_lib_lean.display(), tc_lib_lean.display()),
                );
                env_map.insert(
                    "LEAN_SRC_PATH".to_string(),
                    format!("{}:{}/src/lean", canon_proj.display(), tc_root.display()),
                );
                let orig_ld = std::env::var("LD_LIBRARY_PATH").unwrap_or_default();
                let ld_val = if orig_ld.is_empty() {
                    format!(
                        "{}:{}:{}",
                        canon_proj.join(".lake/build/lib").display(),
                        tc_lib_lean.display(),
                        tc_lib.display()
                    )
                } else {
                    format!(
                        "{}:{}:{}:{}",
                        canon_proj.join(".lake/build/lib").display(),
                        tc_lib_lean.display(),
                        tc_lib.display(),
                        orig_ld
                    )
                };
                env_map.insert("LD_LIBRARY_PATH".to_string(), ld_val);
                let orig_path = std::env::var("PATH").unwrap_or_default();
                env_map.insert(
                    "PATH".to_string(),
                    format!("{}:{}:{}", tc_bin.display(), elan_bin.display(), orig_path),
                );
                return Ok(env_map);
            }
        }
    }

    let output = Command::new("lake")
        .arg("env")
        .arg("env")
        .current_dir(project_dir)
        .output()
        .context("Failed to execute `lake env env`")?;

    let mut env_map = HashMap::new();
    let stdout = String::from_utf8_lossy(&output.stdout);
    for line in stdout.lines() {
        if let Some((k, v)) = line.split_once('=') {
            if matches!(
                k,
                "LEAN_PATH"
                    | "LEAN_SRC_PATH"
                    | "PATH"
                    | "LD_LIBRARY_PATH"
                    | "ELAN_HOME"
                    | "LAKE"
            ) {
                env_map.insert(k.to_string(), v.to_string());
            }
        }
    }
    Ok(env_map)
}

/// Resolve `LEAN_PATH` and environment variables once via SQLite `lake_env_cache` (< 0.2 ms),
/// shared `/dev/shm/turbo-lean-staging/lake_env_v1_<key>.json`, or `lake env env` on cache miss.
pub(crate) fn resolve_lake_env(
    store: &TurboStore,
    project_dir: &Path,
) -> Result<(HashMap<String, String>, bool)> {
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let project_key = TurboStore::compute_lake_env_key(&canon_dir);

    if let Some(cached) = store.get_lake_env(&project_key)? {
        return Ok((cached, true));
    }

    let shm_env_path = store
        .fast_staging_dir()
        .join(format!("lake_env_v1_{}.json", project_key));
    if let Ok(bytes) = fs::read(&shm_env_path) {
        if let Ok(env_map) = serde_json::from_slice::<HashMap<String, String>>(&bytes) {
            if !env_map.is_empty() {
                let _ = store.put_lake_env(&project_key, &env_map);
                return Ok((env_map, false));
            }
        }
    }

    let env_map = spawn_lake_env(&canon_dir)?;
    if !env_map.is_empty() {
        if let Ok(bytes) = serde_json::to_vec(&env_map) {
            let _ = crate::shm_cache::atomic_write_shm(&shm_env_path, &bytes);
        }
        let _ = store.put_lake_env(&project_key, &env_map);
    }
    Ok((env_map, false))
}

pub(crate) fn resolve_or_share_lake_env(
    store: &TurboStore,
    canon_dir: &Path,
    env_key: &str,
) -> Result<Option<(HashMap<String, String>, bool)>> {
    if let Some(m) = store.get_lake_env(env_key)? {
        return Ok(Some((m, false)));
    }
    let shm_env_path = store
        .fast_staging_dir()
        .join(format!("lake_env_v1_{}.json", env_key));
    if let Ok(bytes) = fs::read(&shm_env_path) {
        if let Ok(env_map) = serde_json::from_slice::<HashMap<String, String>>(&bytes) {
            if !env_map.is_empty() {
                return Ok(Some((env_map, true)));
            }
        }
    }
    if let Ok(env_map) = spawn_lake_env(canon_dir) {
        if !env_map.is_empty() {
            if let Ok(bytes) = serde_json::to_vec(&env_map) {
                let _ = crate::shm_cache::atomic_write_shm(&shm_env_path, &bytes);
            }
            return Ok(Some((env_map, true)));
        }
    }
    Ok(None)
}

pub(crate) fn lean_bin_from_env(env_vars: &HashMap<String, String>) -> String {
    if let Some(lake_bin) = env_vars.get("LAKE") {
        let lake_path = Path::new(lake_bin);
        if let Some(bin_dir) = lake_path.parent() {
            let direct_lean = bin_dir.join("lean");
            if direct_lean.exists() {
                return direct_lean.to_string_lossy().to_string();
            }
        }
    }
    "lean".to_string()
}

pub(crate) fn resolve_remote_lean_path(
    canon_dir: &Path,
    env_vars: Option<&HashMap<String, String>>,
) -> String {
    let mut parts = Vec::new();
    let local_lib = canon_dir.join(".lake").join("build").join("lib").join("lean");
    if local_lib.exists() {
        parts.push(local_lib.to_string_lossy().to_string());
    }
    let pkgs_dir = canon_dir.join(".lake").join("packages");
    if let Ok(entries) = fs::read_dir(&pkgs_dir) {
        let mut pkg_libs = Vec::new();
        for entry in entries.flatten() {
            let pkg_lib = entry.path().join(".lake").join("build").join("lib").join("lean");
            if pkg_lib.exists() {
                pkg_libs.push(pkg_lib.to_string_lossy().to_string());
            }
        }
        pkg_libs.sort();
        for p in pkg_libs {
            if !parts.contains(&p) {
                parts.push(p);
            }
        }
    }
    if let Some(env) = env_vars {
        if let Some(lp) = env.get("LEAN_PATH") {
            for p in lp.split(':') {
                if p.is_empty() {
                    continue;
                }
                let path = Path::new(p);
                let abs = if path.is_absolute() {
                    path.to_path_buf()
                } else {
                    canon_dir.join(path)
                };
                let s = abs.to_string_lossy().to_string();
                if !parts.contains(&s) {
                    parts.push(s);
                }
            }
        }
    }
    parts.join(":")
}

pub(crate) fn compute_shard_key(toolchain: &str, shard: &splitter::TheoremShard) -> String {
    let mut key_hasher = blake3::Hasher::new();
    key_hasher.update(b"theorem-shard-v1:");
    key_hasher.update(toolchain.as_bytes());
    key_hasher.update(b":");
    key_hasher.update(shard.prefix_env_hash.as_bytes());
    key_hasher.update(b":");
    key_hasher.update(shard.stmt_hash.as_bytes());
    key_hasher.update(b":");
    key_hasher.update(shard.proof_hash.as_bytes());
    key_hasher.finalize().to_hex().to_string()
}

/// Read `.lean` source files in parallel across worker threads while preserving input order.
pub(crate) fn read_lean_files_parallel(paths: &[PathBuf]) -> Vec<(PathBuf, String)> {
    if paths.len() < 8 {
        return paths
            .iter()
            .map(|p| (p.clone(), fs::read_to_string(p).unwrap_or_default()))
            .collect();
    }
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .min(paths.len());
    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let chunks: Vec<Vec<(usize, PathBuf, String)>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(workers);
        for _ in 0..workers {
            let next_ref = &next_idx;
            handles.push(s.spawn(move || {
                let mut local = Vec::new();
                loop {
                    let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if i >= paths.len() {
                        break;
                    }
                    let src = fs::read_to_string(&paths[i]).unwrap_or_default();
                    local.push((i, paths[i].clone(), src));
                }
                local
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or_default())
            .collect()
    });
    let mut indexed: Vec<(usize, PathBuf, String)> = chunks.into_iter().flatten().collect();
    indexed.sort_unstable_by_key(|(i, _, _)| *i);
    indexed.into_iter().map(|(_, p, s)| (p, s)).collect()
}

/// Stat `.lean` files in parallel across worker threads while preserving input order.
pub(crate) fn stat_lean_files_parallel(
    paths: &[PathBuf],
) -> Vec<Option<(String, i64, i64, i64)>> {
    if paths.len() < 16 {
        return paths
            .iter()
            .map(|p| {
                fs::metadata(p).ok().map(|m| {
                    let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&m);
                    (p.to_string_lossy().to_string(), ms, mn, sz)
                })
            })
            .collect();
    }
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .min(paths.len());
    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let chunks: Vec<Vec<(usize, Option<(String, i64, i64, i64)>)>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(workers);
        for _ in 0..workers {
            let next_ref = &next_idx;
            handles.push(s.spawn(move || {
                let mut local = Vec::new();
                loop {
                    let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if i >= paths.len() {
                        break;
                    }
                    let st = fs::metadata(&paths[i]).ok().map(|m| {
                        let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&m);
                        (paths[i].to_string_lossy().to_string(), ms, mn, sz)
                    });
                    local.push((i, st));
                }
                local
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or_default())
            .collect()
    });
    let mut indexed: Vec<(usize, Option<(String, i64, i64, i64)>)> =
        chunks.into_iter().flatten().collect();
    indexed.sort_unstable_by_key(|(i, _)| *i);
    indexed.into_iter().map(|(_, st)| st).collect()
}

static OLEAN_DIGEST_CACHE: std::sync::OnceLock<
    std::sync::Mutex<HashMap<(PathBuf, u64, i64), String>>,
> = std::sync::OnceLock::new();

fn parse_header_imports(src: &str) -> Vec<String> {
    let mut mods = Vec::new();
    let mut in_block_comment = 0usize;
    for line in src.lines() {
        let s = line.trim();
        if s.is_empty() || s.starts_with("--") {
            continue;
        }
        if s.starts_with("/-") {
            in_block_comment += s.matches("/-").count();
            in_block_comment = in_block_comment.saturating_sub(s.matches("-/").count());
            continue;
        }
        if in_block_comment > 0 {
            in_block_comment += s.matches("/-").count();
            in_block_comment = in_block_comment.saturating_sub(s.matches("-/").count());
            continue;
        }
        if s == "prelude" || s.starts_with("prelude ") {
            continue;
        }
        if let Some(rest) = s.strip_prefix("import ") {
            let without_comment = rest.split("--").next().unwrap_or(rest);
            let without_block = without_comment.split("/-").next().unwrap_or(without_comment);
            for tok in without_block.split_whitespace() {
                if tok == "public" || tok == "all" {
                    continue;
                }
                if !tok.is_empty() {
                    mods.push(tok.to_string());
                }
            }
        } else if !mods.is_empty()
            && (s.starts_with("namespace ")
                || s.starts_with("section ")
                || s.starts_with("theorem ")
                || s.starts_with("lemma ")
                || s.starts_with("def ")
                || s.starts_with("abbrev ")
                || s.starts_with("structure ")
                || s.starts_with("inductive ")
                || s.starts_with("class ")
                || s.starts_with("instance "))
        {
            break;
        }
    }
    mods
}

pub(crate) fn infer_project_dir_from_lean_file(path: &Path) -> PathBuf {
    let mut cur = if path.is_file() {
        path.parent()
    } else {
        Some(path)
    };
    while let Some(dir) = cur {
        if dir.join("lakefile.lean").exists()
            || dir.join("lakefile.toml").exists()
            || dir.join("lean-toolchain").exists()
            || dir.join(".lake").is_dir()
        {
            return dir.to_path_buf();
        }
        cur = dir.parent();
    }
    path.parent()
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| PathBuf::from("."))
}

fn compute_single_olean_digest(olean_path: &Path) -> Option<String> {
    let meta = fs::metadata(olean_path).ok()?;
    if !meta.is_file() {
        return None;
    }
    let file_len = meta.len();
    #[cfg(test)]
    if file_len <= 1_048_576 {
        let bytes = fs::read(olean_path).ok()?;
        return Some(blake3::hash(&bytes).to_hex().to_string());
    }
    let (ms, mn, _) = TurboStore::extract_file_stat_tuple(&meta);
    let mtime_ns = ms.saturating_mul(1_000_000_000).saturating_add(mn);
    let key = (olean_path.to_path_buf(), file_len, mtime_ns);
    let cache = OLEAN_DIGEST_CACHE.get_or_init(|| std::sync::Mutex::new(HashMap::new()));
    if let Ok(guard) = cache.lock() {
        if let Some(hit) = guard.get(&key) {
            return Some(hit.clone());
        }
    }
    let bytes = fs::read(olean_path).ok()?;
    let digest = blake3::hash(&bytes).to_hex().to_string();
    if let Ok(mut guard) = cache.lock() {
        guard.insert(key, digest.clone());
    }
    Some(digest)
}

/// Compute BLAKE3 content digests of all imported `.olean` modules for `src`.
/// Searches `lean_path` (or `LEAN_PATH`), `project_dir/.lake/build/lib/lean`, and
/// `project_dir/.lake/packages/*/.lake/build/lib/lean`.
/// Returns a sorted `Vec<String>` of `"<ModName>:<blake3_hex>"`.
pub fn compute_imported_olean_interface_hashes(
    src: &str,
    project_dir: &Path,
    lean_path: Option<&str>,
) -> Vec<String> {
    let mut worklist = parse_header_imports(src);
    if worklist.is_empty() {
        return Vec::new();
    }

    let mut search_dirs: Vec<PathBuf> = Vec::new();
    let lp_owned: Option<String> = lean_path
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .or_else(|| std::env::var("LEAN_PATH").ok().filter(|s| !s.is_empty()));
    if let Some(ref lp) = lp_owned {
        for part in lp.split(':') {
            if !part.is_empty() && !part.contains("/toolchains/") {
                let pb = PathBuf::from(part);
                if pb.is_dir() && !search_dirs.contains(&pb) {
                    search_dirs.push(pb);
                }
            }
        }
    }
    if !project_dir.as_os_str().is_empty() {
        let local_lib = project_dir.join(".lake/build/lib/lean");
        if local_lib.is_dir() && !search_dirs.contains(&local_lib) {
            search_dirs.push(local_lib);
        }
        let pkgs_dir = project_dir.join(".lake/packages");
        if let Ok(entries) = fs::read_dir(&pkgs_dir) {
            let mut pkg_libs = Vec::new();
            for entry in entries.flatten() {
                let pkg_lib = entry.path().join(".lake/build/lib/lean");
                if pkg_lib.is_dir() {
                    pkg_libs.push(pkg_lib);
                }
            }
            pkg_libs.sort();
            for p in pkg_libs {
                if !search_dirs.contains(&p) {
                    search_dirs.push(p);
                }
            }
        }
    }

    if search_dirs.is_empty() {
        return Vec::new();
    }

    let mut visited = std::collections::HashSet::new();
    let mut out = Vec::new();

    while let Some(mod_name) = worklist.pop() {
        if !visited.insert(mod_name.clone()) {
            continue;
        }
        let rel_slash = mod_name.replace('.', "/");
        let rel_olean = format!("{}.olean", rel_slash);
        for dir in &search_dirs {
            let cand = dir.join(&rel_olean);
            if let Some(digest) = compute_single_olean_digest(&cand) {
                out.push(format!("{}:{}", mod_name, digest));
                break;
            }
        }
        if !project_dir.as_os_str().is_empty() {
            let sub_lean = project_dir.join(format!("{}.lean", rel_slash));
            if let Ok(sub_src) = fs::read_to_string(&sub_lean) {
                for sub_mod in parse_header_imports(&sub_src) {
                    if !visited.contains(&sub_mod) {
                        worklist.push(sub_mod);
                    }
                }
            }
        }
    }

    out.sort();
    out.dedup();
    out
}

#[derive(serde::Serialize, serde::Deserialize, Clone)]
pub(crate) struct ShmCachedFileSplit {
    pub src_blake3: String,
    pub split_key: String,
    pub split: splitter::SplitResult,
    #[serde(default)]
    pub prefix_src: String,
    #[serde(default)]
    pub known_modified: bool,
    #[serde(default)]
    pub dep_hashes: Vec<String>,
}

/// Compact ~500-byte `/dev/shm` project stat summary so `build` and `ci-verify` never have to
/// deserialize 800 KB of full `SplitResult` shards when file stats are unchanged.
#[derive(serde::Serialize, serde::Deserialize, Clone)]
pub(crate) struct ShmProjectStatSummary {
    pub file_hashes: BTreeMap<String, String>,
    pub per_file_interfaces: BTreeMap<String, String>,
    pub total_files: usize,
    pub total_shards: usize,
    pub flagged_files: Vec<(String, Vec<String>)>,
}

pub(crate) fn shm_file_splits_dir(store: &TurboStore) -> PathBuf {
    let dir = store.fast_staging_dir().join("file_splits_v2");
    let _ = fs::create_dir_all(&dir);
    dir
}

pub(crate) fn compute_single_stat_hash(pk: &str, ms: i64, mn: i64, sz: i64) -> String {
    let mut h = blake3::Hasher::new();
    h.update(b"single-stat-split:v2\n");
    h.update(pk.as_bytes());
    h.update(b":");
    h.update(&ms.to_le_bytes());
    h.update(&mn.to_le_bytes());
    h.update(&sz.to_le_bytes());
    h.finalize().to_hex().to_string()
}

pub(crate) fn compact_split_for_shm_cache(split: &splitter::SplitResult) -> splitter::SplitResult {
    let mut compact = split.clone();
    let keep_proof_text = compact.hygiene.has_sorry;
    compact.skeleton_source.clear();
    for sh in &mut compact.shards {
        sh.shard_source.clear();
        sh.signature_text.clear();
        sh.cone_env_hash.clear();
        if !keep_proof_text {
            sh.proof_text.clear();
        }
    }
    compact
}

pub(crate) fn compute_stat_slice_hash(stats: &[(String, i64, i64, i64)]) -> String {
    let mut h = blake3::Hasher::new();
    h.update(b"project-stat-splits:v2\n");
    for (pk, ms, mn, sz) in stats {
        h.update(pk.as_bytes());
        h.update(b":");
        h.update(&ms.to_le_bytes());
        h.update(&mn.to_le_bytes());
        h.update(&sz.to_le_bytes());
        h.update(b"\n");
    }
    h.finalize().to_hex().to_string()
}

/// Fast ~500-byte `/dev/shm` project stat summary lookup for `build` and `ci-verify`.
pub(crate) fn load_project_stat_summary_cached(
    store: &TurboStore,
    project_dir: &Path,
    paths: &[PathBuf],
) -> Result<ShmProjectStatSummary> {
    if paths.is_empty() {
        return Ok(ShmProjectStatSummary {
            file_hashes: BTreeMap::new(),
            per_file_interfaces: BTreeMap::new(),
            total_files: 0,
            total_shards: 0,
            flagged_files: Vec::new(),
        });
    }
    let file_stats = stat_lean_files_parallel(paths);
    let valid_stats: Vec<(String, i64, i64, i64)> =
        file_stats.iter().filter_map(|s| s.clone()).collect();

    let summary_path = if paths.len() <= 32 && valid_stats.len() == paths.len() {
        let stat_hash = compute_stat_slice_hash(&valid_stats);
        let p = store
            .fast_staging_dir()
            .join(format!("project_stat_summary_v2_{}.json", &stat_hash[..24]));
        if let Ok(bytes) = fs::read(&p) {
            if let Ok(summary) = serde_json::from_slice::<ShmProjectStatSummary>(&bytes) {
                if summary.total_files == paths.len() {
                    return Ok(summary);
                }
            }
        }
        Some(p)
    } else {
        None
    };

    let (parsed_files, _) = load_and_split_files_with_hashes_cached(store, paths)?;
    let mut file_hashes = BTreeMap::new();
    let mut per_file_interfaces = BTreeMap::new();
    let mut total_shards = 0usize;
    let mut flagged_files = Vec::new();

    for (lf, src_hash_hex, src, split) in &parsed_files {
        total_shards += split.shards.len();
        let rel = lf.strip_prefix(project_dir).unwrap_or(lf);
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        let src_hash = if !src_hash_hex.is_empty() {
            src_hash_hex.clone()
        } else {
            blake3::hash(src.as_bytes()).to_hex().to_string()
        };
        file_hashes.insert(rel_str.clone(), src_hash);
        per_file_interfaces.insert(rel_str.clone(), split.interface_hash.clone());
        if !split.hygiene.is_clean_for_certification() {
            flagged_files.push((rel_str, split.hygiene.flagged_items.clone()));
        }
    }

    let summary = ShmProjectStatSummary {
        file_hashes,
        per_file_interfaces,
        total_files: parsed_files.len(),
        total_shards,
        flagged_files,
    };

    if let Some(p) = summary_path {
        if let Ok(bytes) = serde_json::to_vec(&summary) {
            let _ = crate::shm_cache::atomic_write_shm(&p, &bytes);
        }
    }

    Ok(summary)
}

/// Zero-read stat-backed file split loader returning `(path, src_blake3_hex, optional_src, SplitResult)`.
pub(crate) fn load_and_split_files_with_hashes_cached(
    store: &TurboStore,
    paths: &[PathBuf],
) -> Result<(Vec<(PathBuf, String, String, splitter::SplitResult)>, usize)> {
    if paths.is_empty() {
        return Ok((Vec::new(), 0));
    }
    let file_stats = stat_lean_files_parallel(paths);
    let valid_stats: Vec<(String, i64, i64, i64)> =
        file_stats.iter().filter_map(|s| s.clone()).collect();

    let shm_stat_path = if paths.len() <= 32 && valid_stats.len() == paths.len() {
        let stat_hash = compute_stat_slice_hash(&valid_stats);
        let p = store
            .fast_staging_dir()
            .join(format!("project_stat_splits_v2_{}.json", &stat_hash[..24]));
        if let Ok(bytes) = fs::read(&p) {
            if let Ok(cached_entries) = serde_json::from_slice::<Vec<ShmCachedFileSplit>>(&bytes) {
                if cached_entries.len() == paths.len()
                    && cached_entries.iter().zip(paths.iter()).all(|(c, path)| {
                        let proj_dir = infer_project_dir_from_lean_file(path);
                        compute_imported_olean_interface_hashes(
                            &c.split.imports_header,
                            &proj_dir,
                            None,
                        ) == c.dep_hashes
                    })
                {
                    let out: Vec<(PathBuf, String, String, splitter::SplitResult)> = paths
                        .iter()
                        .cloned()
                        .zip(cached_entries)
                        .map(|(path, c)| (path, c.src_blake3, c.prefix_src, c.split))
                        .collect();
                    return Ok((out, paths.len()));
                }
            }
        }
        Some(p)
    } else {
        None
    };

    let splits_dir = shm_file_splits_dir(store);
    let mut hits = 0usize;
    let mut results: Vec<Option<(PathBuf, String, String, splitter::SplitResult, Vec<String>)>> =
        vec![None; paths.len()];
    let mut miss_indices = Vec::new();

    for (idx, p) in paths.iter().enumerate() {
        if let Some((ref pk, ms, mn, sz)) = file_stats[idx] {
            let st_hash = compute_single_stat_hash(pk, ms, mn, sz);
            let st_path = splits_dir.join(format!("st_{}.json", &st_hash[..24]));
            if let Ok(bytes) = fs::read(&st_path) {
                if let Ok(c) = serde_json::from_slice::<ShmCachedFileSplit>(&bytes) {
                    if !c.src_blake3.is_empty() {
                        let proj_dir = infer_project_dir_from_lean_file(p);
                        let cur_deps = compute_imported_olean_interface_hashes(
                            &c.split.imports_header,
                            &proj_dir,
                            None,
                        );
                        if cur_deps == c.dep_hashes {
                            hits += 1;
                            results[idx] =
                                Some((p.clone(), c.src_blake3, c.prefix_src, c.split, cur_deps));
                            continue;
                        }
                    }
                }
            }
        }
        miss_indices.push(idx);
    }

    if !miss_indices.is_empty() {
        let miss_paths: Vec<PathBuf> = miss_indices.iter().map(|&i| paths[i].clone()).collect();
        let miss_srcs = read_lean_files_parallel(&miss_paths);
        let (miss_parsed, content_hits) = split_and_audit_with_hashes_cached(store, &miss_srcs)?;
        hits += content_hits;
        for (m_pos, (p, src_blake3, src, split)) in miss_parsed.into_iter().enumerate() {
            let orig_idx = miss_indices[m_pos];
            let proj_dir = infer_project_dir_from_lean_file(&p);
            let dep_hashes =
                compute_imported_olean_interface_hashes(&split.imports_header, &proj_dir, None);
            if let Some((ref pk, ms, mn, sz)) = file_stats[orig_idx] {
                let st_hash = compute_single_stat_hash(pk, ms, mn, sz);
                let st_path = splits_dir.join(format!("st_{}.json", &st_hash[..24]));
                let entry = ShmCachedFileSplit {
                    src_blake3: src_blake3.clone(),
                    split_key: String::new(),
                    split: compact_split_for_shm_cache(&split),
                    prefix_src: String::new(),
                    known_modified: false,
                    dep_hashes: dep_hashes.clone(),
                };
                if let Ok(bytes) = serde_json::to_vec(&entry) {
                    let _ = crate::shm_cache::atomic_write_shm(&st_path, &bytes);
                }
            }
            results[orig_idx] = Some((p, src_blake3, src, split, dep_hashes));
        }
    }

    let resolved_all: Vec<(PathBuf, String, String, splitter::SplitResult, Vec<String>)> = results
        .into_iter()
        .map(|r| r.expect("all file splits resolved"))
        .collect();
    if let Some(p) = shm_stat_path {
        let compacts: Vec<ShmCachedFileSplit> = resolved_all
            .iter()
            .map(|(_, sb, _, sp, dep_hashes)| ShmCachedFileSplit {
                src_blake3: sb.clone(),
                split_key: String::new(),
                split: compact_split_for_shm_cache(sp),
                prefix_src: String::new(),
                known_modified: false,
                dep_hashes: dep_hashes.clone(),
            })
            .collect();
        if let Ok(bytes) = serde_json::to_vec(&compacts) {
            let _ = crate::shm_cache::atomic_write_shm(&p, &bytes);
        }
    }
    let final_results: Vec<(PathBuf, String, String, splitter::SplitResult)> = resolved_all
        .into_iter()
        .map(|(p, sb, src, sp, _)| (p, sb, src, sp))
        .collect();
    Ok((final_results, hits))
}

/// Zero-read stat-backed file split loader: checks `(path_key, mtime_sec, mtime_nsec, size_bytes)`
/// in `/dev/shm` or `file_stat_cache` joined with `file_split_cache` first, and only reads/hashes/splits files
/// that miss the stat cache. On stat cache hit, the returned `String` source is empty (`""`) and
/// can be lazily loaded if a theorem shard miss requires source reconstruction.
pub(crate) fn load_and_split_files_cached(
    store: &TurboStore,
    paths: &[PathBuf],
) -> Result<(Vec<(PathBuf, String, splitter::SplitResult)>, usize)> {
    let (with_hashes, hits) = load_and_split_files_with_hashes_cached(store, paths)?;
    let out = with_hashes
        .into_iter()
        .map(|(p, _sb, src, sp)| (p, src, sp))
        .collect();
    Ok((out, hits))
}

fn compute_file_split_key_with_deps(src_blake3: &str, dep_hashes: &[String]) -> String {
    if dep_hashes.is_empty() {
        return TurboStore::compute_file_split_key_from_src_hash(src_blake3);
    }
    let mut h = blake3::Hasher::new();
    h.update(src_blake3.as_bytes());
    for dh in dep_hashes {
        h.update(b"\n");
        h.update(dh.as_bytes());
    }
    TurboStore::compute_file_split_key_from_src_hash(&h.finalize().to_hex())
}

pub(crate) fn split_and_audit_with_hashes_cached(
    store: &TurboStore,
    files: &[(PathBuf, String)],
) -> Result<(Vec<(PathBuf, String, String, splitter::SplitResult)>, usize)> {
    if files.is_empty() {
        return Ok((Vec::new(), 0));
    }
    let default_workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);

    let file_deps: Vec<Vec<String>> = files
        .iter()
        .map(|(path, src)| {
            let proj_dir = infer_project_dir_from_lean_file(path);
            compute_imported_olean_interface_hashes(src, &proj_dir, None)
        })
        .collect();

    let file_keys: Vec<(String, String)> = if files.len() < 8 {
        files
            .iter()
            .zip(file_deps.iter())
            .map(|((_, src), deps)| {
                let sb = blake3::hash(src.as_bytes()).to_hex().to_string();
                let fk = compute_file_split_key_with_deps(&sb, deps);
                (sb, fk)
            })
            .collect()
    } else {
        let workers = default_workers.min(files.len());
        let next_idx = std::sync::atomic::AtomicUsize::new(0);
        let deps_ref = &file_deps;
        let chunks: Vec<Vec<(usize, (String, String))>> = std::thread::scope(|s| {
            let mut handles = Vec::with_capacity(workers);
            for _ in 0..workers {
                let next_ref = &next_idx;
                handles.push(s.spawn(move || {
                    let mut local = Vec::new();
                    loop {
                        let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if i >= files.len() {
                            break;
                        }
                        let sb = blake3::hash(files[i].1.as_bytes()).to_hex().to_string();
                        let fk = compute_file_split_key_with_deps(&sb, &deps_ref[i]);
                        local.push((i, (sb, fk)));
                    }
                    local
                }));
            }
            handles
                .into_iter()
                .map(|h| h.join().unwrap_or_default())
                .collect()
        });
        let mut indexed: Vec<(usize, (String, String))> = chunks.into_iter().flatten().collect();
        indexed.sort_unstable_by_key(|(i, _)| *i);
        indexed.into_iter().map(|(_, pair)| pair).collect()
    };

    let shm_proj_path = if files.len() <= 32 {
        let mut ch = blake3::Hasher::new();
        ch.update(b"project-content-splits:v2\n");
        for (_, fk) in &file_keys {
            ch.update(fk.as_bytes());
            ch.update(b"\n");
        }
        let p = store.fast_staging_dir().join(format!(
            "project_splits_v2_{}.json",
            &ch.finalize().to_hex()[..24]
        ));
        if let Ok(bytes) = fs::read(&p) {
            if let Ok(cached_splits) = serde_json::from_slice::<Vec<splitter::SplitResult>>(&bytes)
            {
                if cached_splits.len() == files.len() {
                    let out: Vec<(PathBuf, String, String, splitter::SplitResult)> = files
                        .iter()
                        .cloned()
                        .zip(file_keys.into_iter())
                        .zip(cached_splits)
                        .map(|(((path, src), (sb, _)), sp)| (path, sb, src, sp))
                        .collect();
                    return Ok((out, files.len()));
                }
            }
        }
        Some(p)
    } else {
        None
    };

    let splits_dir = shm_file_splits_dir(store);
    let mut hits = 0usize;
    let mut results: Vec<Option<splitter::SplitResult>> = vec![None; files.len()];
    let mut db_miss_indices = Vec::new();
    let mut db_miss_hashes = Vec::new();

    for (idx, (_sb, fk)) in file_keys.iter().enumerate() {
        let fk_path = splits_dir.join(format!("fk_{}.json", &fk[..24]));
        if let Ok(bytes) = fs::read(&fk_path) {
            if let Ok(sp) = serde_json::from_slice::<splitter::SplitResult>(&bytes) {
                hits += 1;
                results[idx] = Some(sp);
                continue;
            }
        }
        db_miss_indices.push(idx);
        db_miss_hashes.push(fk.clone());
    }

    let mut miss_indices = Vec::new();
    if !db_miss_indices.is_empty() {
        let cached_map = store.batch_get_file_splits(&db_miss_hashes)?;
        for &idx in &db_miss_indices {
            let fk = &file_keys[idx].1;
            if let Some(split) = cached_map.get(fk).cloned() {
                hits += 1;
                let fk_path = splits_dir.join(format!("fk_{}.json", &fk[..24]));
                if let Ok(bytes) = serde_json::to_vec(&compact_split_for_shm_cache(&split)) {
                    let _ = crate::shm_cache::atomic_write_shm(&fk_path, &bytes);
                }
                results[idx] = Some(split);
            } else {
                miss_indices.push(idx);
            }
        }
    }

    let mut new_splits: Vec<(String, splitter::SplitResult)> =
        Vec::with_capacity(miss_indices.len());
    if !miss_indices.is_empty() {
        let deps_ref = &file_deps;
        let computed_misses: Vec<(usize, splitter::SplitResult)> = if miss_indices.len() < 2 {
            miss_indices
                .iter()
                .map(|&idx| (idx, split_lean_source(&files[idx].1, &deps_ref[idx])))
                .collect()
        } else {
            let workers = default_workers.min(miss_indices.len());
            let next_m = std::sync::atomic::AtomicUsize::new(0);
            let miss_ref = &miss_indices;
            let chunks: Vec<Vec<(usize, splitter::SplitResult)>> = std::thread::scope(|s| {
                let mut handles = Vec::with_capacity(workers);
                for _ in 0..workers {
                    let next_ref = &next_m;
                    handles.push(s.spawn(move || {
                        let mut local = Vec::new();
                        loop {
                            let m_pos =
                                next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            if m_pos >= miss_ref.len() {
                                break;
                            }
                            let file_idx = miss_ref[m_pos];
                            let sp = split_lean_source(&files[file_idx].1, &deps_ref[file_idx]);
                            local.push((file_idx, sp));
                        }
                        local
                    }));
                }
                handles
                    .into_iter()
                    .map(|h| h.join().unwrap_or_default())
                    .collect()
            });
            let mut flat: Vec<(usize, splitter::SplitResult)> =
                chunks.into_iter().flatten().collect();
            flat.sort_unstable_by_key(|(idx, _)| *idx);
            flat
        };

        for (file_idx, split) in computed_misses {
            let fk = &file_keys[file_idx].1;
            let fk_path = splits_dir.join(format!("fk_{}.json", &fk[..24]));
            if let Ok(bytes) = serde_json::to_vec(&compact_split_for_shm_cache(&split)) {
                let _ = crate::shm_cache::atomic_write_shm(&fk_path, &bytes);
            }
            new_splits.push((fk.clone(), split.clone()));
            results[file_idx] = Some(split);
        }
    }

    if !new_splits.is_empty() {
        let refs: Vec<(String, &splitter::SplitResult)> =
            new_splits.iter().map(|(h, sp)| (h.clone(), sp)).collect();
        let _ = store.batch_put_file_splits(&refs);
    }

    // Record `(path_key, mtime_sec, mtime_nsec, size_bytes, split_key)` in `file_stat_cache`
    // and `/dev/shm` `st_{stat_hash}.json` even if `new_splits` was empty (e.g., restored file mtime).
    let paths_only: Vec<PathBuf> = files.iter().map(|(p, _)| p.clone()).collect();
    let stats = stat_lean_files_parallel(&paths_only);
    let mut stat_rows = Vec::with_capacity(files.len());
    let mut valid_stats = Vec::with_capacity(files.len());
    for (idx, st_opt) in stats.into_iter().enumerate() {
        if let Some((pk, ms, mn, sz)) = st_opt {
            if let Some(ref sp) = results[idx] {
                let st_hash = compute_single_stat_hash(&pk, ms, mn, sz);
                let st_path = splits_dir.join(format!("st_{}.json", &st_hash[..24]));
                if !st_path.exists() || !file_deps[idx].is_empty() {
                    let entry = ShmCachedFileSplit {
                        src_blake3: file_keys[idx].0.clone(),
                        split_key: String::new(),
                        split: compact_split_for_shm_cache(sp),
                        prefix_src: String::new(),
                        known_modified: false,
                        dep_hashes: file_deps[idx].clone(),
                    };
                    if let Ok(bytes) = serde_json::to_vec(&entry) {
                        let _ = crate::shm_cache::atomic_write_shm(&st_path, &bytes);
                    }
                }
            }
            valid_stats.push((pk.clone(), ms, mn, sz));
            if !new_splits.is_empty() {
                stat_rows.push((pk, ms, mn, sz, file_keys[idx].1.clone()));
            }
        }
    }
    if !stat_rows.is_empty() {
        let _ = store.batch_put_file_stats(&stat_rows);
    }
    if files.len() <= 32 && valid_stats.len() == files.len() {
        let stat_hash = compute_stat_slice_hash(&valid_stats);
        let stat_p = store
            .fast_staging_dir()
            .join(format!("project_stat_splits_v2_{}.json", &stat_hash[..24]));
        if !stat_p.exists() || file_deps.iter().any(|d| !d.is_empty()) {
            let compacts: Vec<ShmCachedFileSplit> = results
                .iter()
                .enumerate()
                .filter_map(|(idx, r)| {
                    r.as_ref().map(|sp| ShmCachedFileSplit {
                        src_blake3: file_keys[idx].0.clone(),
                        split_key: String::new(),
                        split: compact_split_for_shm_cache(sp),
                        prefix_src: String::new(),
                        known_modified: false,
                        dep_hashes: file_deps[idx].clone(),
                    })
                })
                .collect();
            if compacts.len() == files.len() {
                if let Ok(bytes) = serde_json::to_vec(&compacts) {
                    let _ = crate::shm_cache::atomic_write_shm(&stat_p, &bytes);
                }
            }
        }
    }

    let final_results: Vec<(PathBuf, String, String, splitter::SplitResult)> = files
        .iter()
        .enumerate()
        .map(|(idx, (path, src))| {
            (
                path.clone(),
                file_keys[idx].0.clone(),
                src.clone(),
                results[idx].take().expect("all file splits resolved"),
            )
        })
        .collect();

    if let Some(p) = shm_proj_path {
        if !p.exists() {
            let compacts: Vec<splitter::SplitResult> = final_results
                .iter()
                .map(|(_, _, _, sp)| compact_split_for_shm_cache(sp))
                .collect();
            if let Ok(bytes) = serde_json::to_vec(&compacts) {
                let _ = crate::shm_cache::atomic_write_shm(&p, &bytes);
            }
        }
    }

    Ok((final_results, hits))
}

/// Batch-split and hygiene-audit `.lean` source files using `/dev/shm` + SQLite `file_split_cache`
/// and multi-threaded `std::thread::scope` workers for hashing and cache misses.
/// Returns `(Vec<(PathBuf, String, SplitResult)>, cache_hits)`.
pub(crate) fn split_and_audit_cached(
    store: &TurboStore,
    files: &[(PathBuf, String)],
) -> Result<(Vec<(PathBuf, String, splitter::SplitResult)>, usize)> {
    let (with_hashes, hits) = split_and_audit_with_hashes_cached(store, files)?;
    let out = with_hashes
        .into_iter()
        .map(|(p, _sb, src, sp)| (p, src, sp))
        .collect();
    Ok((out, hits))
}

pub(crate) fn verified_sources_manifest_path(canon_dir: &Path) -> PathBuf {
    canon_dir
        .join(".lake")
        .join("build")
        .join(".turbo_lean_verified_sources.json")
}

pub(crate) fn record_verified_project_oleans(
    canon_dir: &Path,
    file_hashes: &BTreeMap<String, String>,
) {
    let manifest_path = verified_sources_manifest_path(canon_dir);
    if let Some(parent) = manifest_path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    if let Ok(bytes) = serde_json::to_vec(file_hashes) {
        let _ = fs::write(&manifest_path, bytes);
    }
}

pub(crate) fn are_all_project_oleans_up_to_date(
    canon_dir: &Path,
    file_hashes: &BTreeMap<String, String>,
) -> bool {
    if file_hashes.is_empty() {
        return false;
    }
    let lib_lean_dir = canon_dir.join(".lake").join("build").join("lib").join("lean");
    if !lib_lean_dir.is_dir() {
        return false;
    }

    let manifest_path = verified_sources_manifest_path(canon_dir);
    if let Ok(bytes) = fs::read(&manifest_path) {
        if let Ok(recorded) = serde_json::from_slice::<BTreeMap<String, String>>(&bytes) {
            if &recorded != file_hashes {
                return false;
            }
            let mut checked_oleans = 0usize;
            for rel_path in file_hashes.keys() {
                if rel_path == "lakefile.lean" || rel_path.ends_with("/lakefile.lean") {
                    continue;
                }
                let rel_no_ext = Path::new(rel_path).with_extension("");
                let olean_path = lib_lean_dir.join(&rel_no_ext).with_extension("olean");
                match fs::metadata(&olean_path) {
                    Ok(m) if m.is_file() && m.len() > 0 => {
                        checked_oleans += 1;
                    }
                    _ => {
                        if rel_no_ext.components().count() == 1
                            && canon_dir.join(&rel_no_ext).is_dir()
                        {
                            continue;
                        }
                        return false;
                    }
                }
            }
            return checked_oleans > 0;
        }
    }

    let lakefile_mtime = fs::metadata(canon_dir.join("lakefile.lean"))
        .and_then(|m| m.modified())
        .ok();
    let mut checked_oleans = 0usize;
    let mut all_mtime_fresh = true;
    let mut all_have_trace = true;

    for rel_path in file_hashes.keys() {
        if rel_path == "lakefile.lean" || rel_path.ends_with("/lakefile.lean") {
            continue;
        }
        let rel_no_ext = Path::new(rel_path).with_extension("");
        let olean_path = lib_lean_dir.join(&rel_no_ext).with_extension("olean");
        let olean_meta = match fs::metadata(&olean_path) {
            Ok(m) if m.is_file() && m.len() > 0 => m,
            _ => {
                if rel_no_ext.components().count() == 1 && canon_dir.join(&rel_no_ext).is_dir() {
                    continue;
                }
                return false;
            }
        };
        checked_oleans += 1;

        let trace_path = lib_lean_dir.join(&rel_no_ext).with_extension("trace");
        if !trace_path.is_file() {
            all_have_trace = false;
        }

        let src_mtime = fs::metadata(canon_dir.join(rel_path))
            .and_then(|m| m.modified())
            .ok();
        let olean_mtime = olean_meta.modified().ok();
        match (src_mtime, olean_mtime) {
            (Some(sm), Some(om)) if om >= sm => {
                if let Some(lm) = lakefile_mtime {
                    if om < lm {
                        all_mtime_fresh = false;
                    }
                }
            }
            _ => {
                all_mtime_fresh = false;
            }
        }
    }

    if checked_oleans == 0 {
        return false;
    }

    if all_mtime_fresh {
        record_verified_project_oleans(canon_dir, file_hashes);
        return true;
    }

    if all_have_trace {
        let git_clean = Command::new("git")
            .args([
                "-C",
                &canon_dir.to_string_lossy(),
                "status",
                "--porcelain",
                "--untracked-files=no",
                "--",
                ".",
            ])
            .output()
            .map(|o| o.status.success() && o.stdout.is_empty())
            .unwrap_or(false);
        if git_clean {
            record_verified_project_oleans(canon_dir, file_hashes);
            return true;
        }
    }

    false
}

pub(crate) fn is_file_hash_verified_in_lake_build(
    canon_dir: &Path,
    canon_file: &Path,
    actual_hash: &str,
) -> bool {
    let rel_path = canon_file
        .strip_prefix(canon_dir)
        .unwrap_or(canon_file)
        .to_string_lossy()
        .replace('\\', "/");
    let manifest_path = verified_sources_manifest_path(canon_dir);
    let Ok(bytes) = fs::read(&manifest_path) else {
        return false;
    };
    let Ok(recorded) = serde_json::from_slice::<BTreeMap<String, String>>(&bytes) else {
        return false;
    };
    let Some(expected_hash) = recorded.get(&rel_path) else {
        return false;
    };
    expected_hash == actual_hash
}

pub(crate) fn is_file_verified_in_lake_build(
    canon_dir: &Path,
    canon_file: &Path,
    src: &str,
) -> bool {
    let actual_hash = blake3::hash(src.as_bytes()).to_hex().to_string();
    is_file_hash_verified_in_lake_build(canon_dir, canon_file, &actual_hash)
}

/// Compute the Proof-Irrelevant Interface Hash of all `.lean` sources in a project,
/// returning `(action_key, interface_hash, per_file_source_blake3_map)`.
pub(crate) fn compute_project_interface_key_with_hashes(
    store: &TurboStore,
    project_dir: &Path,
    toolchain: &str,
    targets: &[String],
    trust_domain: &str,
) -> Result<(String, String, BTreeMap<String, String>)> {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-lean-build-v1\n");
    hasher.update(toolchain.as_bytes());
    hasher.update(b"\n");
    hasher.update(trust_domain.as_bytes());
    hasher.update(b"\n");
    for t in targets {
        hasher.update(t.as_bytes());
        hasher.update(b",");
    }
    hasher.update(b"\n");

    let mut interface_hasher = blake3::Hasher::new();
    interface_hasher.update(toolchain.as_bytes());

    let mut lean_files: Vec<PathBuf> = Vec::new();
    for entry in WalkDir::new(project_dir)
        .into_iter()
        .filter_entry(|e| {
            let name = e.file_name().to_string_lossy();
            name != ".git" && name != ".lake" && name != "target"
        })
        .flatten()
    {
        if entry.file_type().is_file() {
            let p = entry.path();
            if p.extension().and_then(|s| s.to_str()) == Some("lean") {
                lean_files.push(p.to_path_buf());
            }
        }
    }
    lean_files.sort();

    let summary = load_project_stat_summary_cached(store, project_dir, &lean_files)?;
    for lf in &lean_files {
        let rel = lf.strip_prefix(project_dir).unwrap_or(lf);
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        if let Some(src_hash_hex) = summary.file_hashes.get(&rel_str) {
            hasher.update(rel_str.as_bytes());
            hasher.update(b":");
            if let Ok(raw) = blake3::Hash::from_hex(src_hash_hex.as_bytes()) {
                hasher.update(raw.as_bytes());
            } else {
                hasher.update(src_hash_hex.as_bytes());
            }
            hasher.update(b"\n");
        }
        if let Some(ih) = summary.per_file_interfaces.get(&rel_str) {
            interface_hasher.update(rel_str.as_bytes());
            interface_hasher.update(b":");
            interface_hasher.update(ih.as_bytes());
            interface_hasher.update(b"\n");
        }
    }

    Ok((
        hasher.finalize().to_hex().to_string(),
        interface_hasher.finalize().to_hex().to_string(),
        summary.file_hashes,
    ))
}

/// Recursively discover `.lean` source files inside a file or directory (excluding hidden directories, `target`, `node_modules`, and `lakefile.lean`).
pub(crate) fn collect_lean_files(root: &Path) -> Vec<PathBuf> {
    if root.is_file() {
        return vec![root.to_path_buf()];
    }
    let mut lean_files: Vec<PathBuf> = Vec::new();
    for entry in WalkDir::new(root)
        .into_iter()
        .filter_entry(|e| {
            let name = e.file_name().to_string_lossy();
            if e.depth() > 0 && name.starts_with('.') {
                return false;
            }
            name != ".git"
                && name != ".lake"
                && name != ".elan"
                && name != ".cargo"
                && name != "target"
                && name != "node_modules"
        })
        .flatten()
    {
        if entry.file_type().is_file() {
            let p = entry.path();
            if p.extension().and_then(|s| s.to_str()) == Some("lean")
                && p.file_name().and_then(|s| s.to_str()) != Some("lakefile.lean")
            {
                lean_files.push(p.to_path_buf());
            }
        }
    }
    lean_files.sort();
    lean_files
}

/// Resolve the pre-compiled `.olean` module import name (e.g. `TurboLean.Reflection`) if
/// `.lake/build/lib/lean/<Module>.olean` exists on disk.
pub(crate) fn resolve_prebuilt_module_import(
    canon_project_dir: &Path,
    canon_file: &Path,
) -> Option<String> {
    let rel = canon_file.strip_prefix(canon_project_dir).ok()?;
    let rel_no_ext = rel.with_extension("");
    let olean_path = canon_project_dir
        .join(".lake")
        .join("build")
        .join("lib")
        .join("lean")
        .join(&rel_no_ext)
        .with_extension("olean");
    if !olean_path.exists() {
        return None;
    }
    let parts: Vec<String> = rel_no_ext
        .components()
        .filter_map(|c| c.as_os_str().to_str().map(|s| s.to_string()))
        .collect();
    if parts.is_empty() {
        return None;
    }
    Some(parts.join("."))
}

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

    for (lf, _src, split) in split_entries {
        if require_olean && resolve_prebuilt_module_import(canon_dir, lf).is_none() {
            continue;
        }
        if split.shards.is_empty() {
            continue;
        }
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
            let shard_key = compute_shard_key(toolchain, shard);
            batch_items.push((
                shard_key,
                shard.name.clone(),
                shared_receipt.clone(),
                1i64,
            ));
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

pub(crate) fn seed_project_theorem_shards(
    store: &mut TurboStore,
    canon_dir: &Path,
    toolchain: &str,
    trust_domain: &str,
    require_olean: bool,
) -> Result<(usize, usize, usize)> {
    let lean_files: Vec<PathBuf> = collect_lean_files(canon_dir)
        .into_iter()
        .filter(|lf| !require_olean || resolve_prebuilt_module_import(canon_dir, lf).is_some())
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

/// Stage compiled `.olean`, `.ilean`, and `.c` files from `.lake/build` into the immutable CAS blobs directory
/// without opening a SQLite transaction, returning `(outputs, reg_blobs)`.
pub(crate) fn stage_lake_build_outputs(
    store: &TurboStore,
    project_dir: &Path,
) -> Result<(Vec<BlobEntry>, Vec<(String, String, i64, i64)>)> {
    let build_dir = project_dir.join(".lake").join("build");
    if !build_dir.exists() {
        return Ok((Vec::new(), Vec::new()));
    }

    #[cfg(unix)]
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    let mut candidates: Vec<(PathBuf, &'static str, String, i64, i64, u64, u32, i64)> = Vec::new();
    for entry in WalkDir::new(&build_dir).into_iter().flatten() {
        if !entry.file_type().is_file() {
            continue;
        }
        let path = entry.path();
        let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
        let kind = match ext {
            "olean" => "olean",
            "ilean" => "ilean",
            "c" => "c",
            _ => continue,
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
            .unwrap_or(path)
            .to_string_lossy()
            .to_string();
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

    if candidates.is_empty() {
        return Ok((Vec::new(), Vec::new()));
    }
    candidates.sort_by(|a, b| a.2.cmp(&b.2));

    let mut sh = blake3::Hasher::new();
    sh.update(b"lake-build-ingest:v1\n");
    for (_, kind, rel_path, ms, mn, sz, _, _) in &candidates {
        sh.update(rel_path.as_bytes());
        sh.update(b":");
        sh.update(kind.as_bytes());
        sh.update(b":");
        sh.update(&ms.to_le_bytes());
        sh.update(&mn.to_le_bytes());
        sh.update(&sz.to_le_bytes());
        sh.update(b"\n");
    }
    let ingest_cache_path = store.fast_staging_dir().join(format!(
        "lake_build_ingest_v1_{}.json",
        &sh.finalize().to_hex()[..24]
    ));

    let entries: Vec<BlobEntry> = if let Ok(cached_bytes) = fs::read(&ingest_cache_path) {
        if let Ok(parsed) = serde_json::from_slice::<Vec<BlobEntry>>(&cached_bytes) {
            if parsed.len() == candidates.len() {
                parsed
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        }
    } else {
        Vec::new()
    };

    let entries = if entries.len() == candidates.len() {
        entries
    } else {
        let n_threads = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .min(candidates.len())
            .max(1);
        let chunk_size = (candidates.len() + n_threads - 1) / n_threads;

        let mut computed: Vec<BlobEntry> = Vec::with_capacity(candidates.len());
        std::thread::scope(|s| -> Result<()> {
            let mut handles = Vec::with_capacity(n_threads);
            for chunk in candidates.chunks(chunk_size) {
                handles.push(s.spawn(move || -> Result<Vec<BlobEntry>> {
                    let mut local = Vec::with_capacity(chunk.len());
                    for (path, kind, rel_path, _, _, _, _, _) in chunk {
                        let bytes = fs::read(path)?;
                        let size_bytes = bytes.len() as u64;
                        let blob_hash = blake3::hash(&bytes).to_hex().to_string();
                        local.push(BlobEntry {
                            blob_hash,
                            kind: (*kind).to_string(),
                            size_bytes,
                            rel_path: rel_path.clone(),
                        });
                    }
                    Ok(local)
                }));
            }
            for h in handles {
                let chunk_res = h
                    .join()
                    .map_err(|_| anyhow::anyhow!("ingest worker panicked"))??;
                computed.extend(chunk_res);
            }
            Ok(())
        })?;
        computed.sort_by(|a, b| a.rel_path.cmp(&b.rel_path));
        if let Ok(bytes) = serde_json::to_vec(&computed) {
            let _ = crate::shm_cache::atomic_write_shm(&ingest_cache_path, &bytes);
        }
        computed
    };

    let shared_blobs = pack::shared_cas_blobs_dir();
    let mut seen_prefix = [false; 256];
    let mut seen_shared_prefix = [false; 256];
    let mut seen_blobs: std::collections::HashSet<String> =
        std::collections::HashSet::with_capacity(entries.len());
    let mut reg_blobs: Vec<(String, String, i64, i64)> = Vec::with_capacity(entries.len());

    for (entry, (path, _, _, _, _, _, mode, cand_ino)) in entries.iter().zip(candidates.iter()) {
        #[cfg(unix)]
        if (*mode & 0o222) != 0 {
            let _ = fs::set_permissions(path, fs::Permissions::from_mode(0o444));
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
                let _ = fs::create_dir(parent);
            }
        }
        let ino = if fs::hard_link(path, &dest).is_ok() {
            *cand_ino
        } else if let Ok(dm) = fs::metadata(&dest) {
            #[cfg(unix)]
            {
                dm.ino() as i64
            }
            #[cfg(not(unix))]
            {
                0i64
            }
        } else {
            let shared_dir = shared_blobs.join(prefix);
            if !seen_shared_prefix[p_idx] {
                seen_shared_prefix[p_idx] = true;
                let _ = fs::create_dir_all(&shared_dir);
            }
            let shared_p = shared_dir.join(&entry.blob_hash);
            if !shared_p.exists() {
                let tmp_shared = shared_dir.join(format!(
                    "{}.{}.tmp",
                    entry.blob_hash,
                    std::process::id()
                ));
                if fs::copy(path, &tmp_shared).is_ok() {
                    #[cfg(unix)]
                    if let Ok(tm) = fs::metadata(&tmp_shared) {
                        let mut perms = tm.permissions();
                        perms.set_mode(0o444);
                        let _ = fs::set_permissions(&tmp_shared, perms);
                    }
                    let _ = fs::rename(&tmp_shared, &shared_p);
                }
            }
            if fs::hard_link(&shared_p, &dest).is_err() && !dest.exists() {
                fs::copy(path, &dest)?;
                #[cfg(unix)]
                if let Ok(dm) = fs::metadata(&dest) {
                    let mut perms = dm.permissions();
                    perms.set_mode(0o444);
                    let _ = fs::set_permissions(&dest, perms);
                }
            }
            fs::metadata(&dest)
                .map(|m| {
                    #[cfg(unix)]
                    {
                        m.ino() as i64
                    }
                    #[cfg(not(unix))]
                    {
                        0i64
                    }
                })
                .unwrap_or(0)
        };
        reg_blobs.push((
            entry.blob_hash.clone(),
            entry.kind.clone(),
            entry.size_bytes as i64,
            ino,
        ));
    }

    Ok((entries, reg_blobs))
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
    let t0 = Instant::now();
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.clone());
    let project_name = canon_dir
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "lean-project".to_string());
    let toolchain = detect_toolchain(&canon_dir);
    let (action_key, interface_hash, file_hashes) = compute_project_interface_key_with_hashes(
        store,
        &canon_dir,
        &toolchain,
        &targets,
        &trust_domain,
    )?;

    match store.acquire_singleflight(&action_key, &toolchain, "module_full", &trust_domain)? {
        SingleflightOutcome::CacheHit { outputs, coalesced } => {
            let linked = store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
            let seeded_shards = if seed_shards {
                seed_project_theorem_shards(store, &canon_dir, &toolchain, &trust_domain, false)?.1
            } else {
                0
            };
            let elapsed_ms = t0.elapsed().as_millis();
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
        SingleflightOutcome::Leader(lease) => {
            if !targets.is_empty() || !are_all_project_oleans_up_to_date(&canon_dir, &file_hashes) {
                let mut cmd = Command::new("lake");
                cmd.arg("build").current_dir(&canon_dir);
                for t in &targets {
                    cmd.arg(t);
                }
                let out = cmd.output().context("Failed to execute `lake build`")?;
                if !out.status.success() {
                    let stdout = String::from_utf8_lossy(&out.stdout);
                    let stderr = String::from_utf8_lossy(&out.stderr);
                    anyhow::bail!("`lake build` failed:\n{}\n{}", stdout, stderr);
                }
                if !json_output {
                    print!("{}", String::from_utf8_lossy(&out.stdout));
                }
                if targets.is_empty() {
                    record_verified_project_oleans(&canon_dir, &file_hashes);
                }
            }

            let env_key = TurboStore::compute_lake_env_key(&canon_dir);
            let resolved_env = resolve_or_share_lake_env(store, &canon_dir, &env_key)?;

            let dur_ms = t0.elapsed().as_millis() as i64;
            let (outputs, reg_blobs) = stage_lake_build_outputs(store, &canon_dir)?;
            let lake_env_to_put = resolved_env
                .as_ref()
                .filter(|(_, is_new)| *is_new)
                .map(|(m, _)| (env_key.as_str(), m));
            let (manifest_hash, linked) = store.publish_ingested_worktree_action(
                Some(&lease),
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
            if std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
                if let Some((ref env_vars, _)) = resolved_env {
                    pack::warm_local_zygote_daemon_nonblocking(store, env_vars);
                }
            }
            let seeded_shards = if seed_shards {
                seed_project_theorem_shards(store, &canon_dir, &toolchain, &trust_domain, false)?.1
            } else {
                0
            };

            if json_output {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "status": "built",
                        "action_key": action_key,
                        "interface_hash": interface_hash,
                        "manifest_hash": manifest_hash,
                        "artifacts_stored": outputs.len(),
                        "materialized_files": linked,
                        "shards_seeded": seeded_shards,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_imported_olean_modification_invalidates_shard_key() {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_test_olean_inv_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let lib_dir = tmp_dir.join("lib");
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(lib_dir.join("Foo")).expect("create dummy LEAN_PATH dir");

        let olean_path = lib_dir.join("Foo/Bar.olean");
        let mut olean_bytes = vec![0x42u8; 256];
        fs::write(&olean_path, &olean_bytes).expect("write initial dummy .olean");

        let src = "import Foo.Bar\n\ntheorem my_thm : 1 + 1 = 2 := by rfl\n";
        let lp_str = lib_dir.to_string_lossy().to_string();

        let dep_hashes_v1 =
            compute_imported_olean_interface_hashes(src, &tmp_dir, Some(&lp_str));
        assert_eq!(dep_hashes_v1.len(), 1);
        assert!(dep_hashes_v1[0].starts_with("Foo.Bar:"));

        let split_v1 = split_lean_source(src, &dep_hashes_v1);
        assert_eq!(split_v1.shards.len(), 1);
        let shard_v1 = &split_v1.shards[0];
        let key_v1 = compute_shard_key("leanprover/lean4:v4.31.0", shard_v1);

        // Modify 1 byte inside the .olean file in place (preserving length)
        olean_bytes[128] ^= 0xFF;
        fs::write(&olean_path, &olean_bytes).expect("modify dummy .olean in place");

        let dep_hashes_v2 =
            compute_imported_olean_interface_hashes(src, &tmp_dir, Some(&lp_str));
        assert_eq!(dep_hashes_v2.len(), 1);
        assert_ne!(
            dep_hashes_v1, dep_hashes_v2,
            "dep_hashes must change immediately after 1-byte .olean mutation"
        );

        let split_v2 = split_lean_source(src, &dep_hashes_v2);
        let shard_v2 = &split_v2.shards[0];
        let key_v2 = compute_shard_key("leanprover/lean4:v4.31.0", shard_v2);

        assert_ne!(
            shard_v1.cone_env_hash, shard_v2.cone_env_hash,
            "cone_env_hash must change immediately after 1-byte .olean mutation"
        );
        assert_ne!(
            shard_v1.prefix_env_hash, shard_v2.prefix_env_hash,
            "prefix_env_hash must change immediately after 1-byte .olean mutation"
        );
        assert_ne!(
            key_v1, key_v2,
            "shard_key must change immediately after 1-byte .olean mutation"
        );

        let _ = fs::remove_dir_all(&tmp_dir);
    }
}

