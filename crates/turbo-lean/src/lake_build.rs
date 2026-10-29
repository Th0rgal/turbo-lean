//! Lake environment resolution, `/dev/shm` file-split & project-summary stat caching,
//! `.olean` freshness tracking, CAS artifact staging, and `turbo-lean build` execution.

use anyhow::Result;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;
use walkdir::WalkDir;

use crate::db::{BlobEntry, SingleflightOutcome, TurboStore};
use crate::pack;
use crate::splitter::{self, split_lean_source};

pub(crate) fn find_project_root(start: &Path) -> PathBuf {
    let mut cur = if start.is_file() {
        start
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."))
            .to_path_buf()
    } else if start.as_os_str().is_empty() {
        PathBuf::from(".")
    } else {
        start.to_path_buf()
    };
    if let Ok(canon) = cur.canonicalize() {
        cur = canon;
    }
    let mut dir = cur.as_path();
    loop {
        if dir.join("lean-toolchain").exists()
            || dir.join("lakefile.lean").exists()
            || dir.join("lakefile.toml").exists()
        {
            return dir.to_path_buf();
        }
        match dir.parent() {
            Some(parent) if parent != dir && !parent.as_os_str().is_empty() => dir = parent,
            _ => break,
        }
    }
    cur
}

pub(crate) fn detect_toolchain(project_dir: &Path) -> String {
    let tc_file = project_dir.join("lean-toolchain");
    if let Ok(s) = fs::read_to_string(&tc_file) {
        return s.trim().to_string();
    }
    let root = find_project_root(project_dir);
    let root_tc = root.join("lean-toolchain");
    if let Ok(s) = fs::read_to_string(&root_tc) {
        return s.trim().to_string();
    }
    "leanprover/lean4:v4.35.0".to_string()
}

pub(crate) fn spawn_lake_env(project_dir: &Path) -> Result<HashMap<String, String>> {
    let tc = detect_toolchain(project_dir);
    let tc_dir_name = tc.trim().replace('/', "--").replace(':', "---");
    let mut elan_roots = Vec::new();
    if let Ok(eh) = std::env::var("ELAN_HOME") {
        elan_roots.push(PathBuf::from(eh));
    }
    if let Ok(home) = std::env::var("HOME") {
        let home_path = PathBuf::from(&home);
        elan_roots.push(home_path.join(".elan"));
        let mut anc = home_path.parent();
        for _ in 0..3 {
            if let Some(p) = anc {
                elan_roots.push(p.join(".elan"));
                elan_roots.push(p.join("caches/elan"));
                anc = p.parent();
            }
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

    let mut matched_tc: Option<(PathBuf, PathBuf)> = None;
    for candidate_tc in [&tc_dir_name, &"leanprover--lean4---v4.35.0".to_string()] {
        for elan_home in &elan_roots {
            let tc_root = elan_home.join("toolchains").join(candidate_tc);
            if tc_root.join("bin").join("lean").exists() {
                matched_tc = Some((elan_home.clone(), tc_root));
                break;
            }
        }
        if matched_tc.is_some() {
            break;
        }
    }
    if matched_tc.is_none() {
        for elan_home in &elan_roots {
            if let Ok(entries) = fs::read_dir(elan_home.join("toolchains")) {
                let mut dirs: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
                dirs.sort();
                dirs.reverse();
                for d in dirs {
                    if d.join("bin").join("lean").exists() {
                        matched_tc = Some((elan_home.clone(), d));
                        break;
                    }
                }
            }
            if matched_tc.is_some() {
                break;
            }
        }
    }

    if let Some((elan_home, tc_root)) = matched_tc {
        {
            let canon_proj = project_dir
                .canonicalize()
                .unwrap_or_else(|_| project_dir.to_path_buf());
            let proj_lib_lean = canon_proj.join(".lake/build/lib/lean");
            let tc_lib_lean = tc_root.join("lib/lean");
            let tc_lib = tc_root.join("lib");
            let tc_bin = tc_root.join("bin");
            let elan_bin = elan_home.join("bin");

            let mut lean_path_parts = vec![proj_lib_lean.to_string_lossy().to_string()];
            let mut ld_parts = vec![canon_proj
                .join(".lake/build/lib")
                .to_string_lossy()
                .to_string()];
            let pkgs_dir = canon_proj.join(".lake").join("packages");
            if let Ok(entries) = fs::read_dir(&pkgs_dir) {
                let mut pkg_dirs: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
                pkg_dirs.sort();
                for pkg_dir in pkg_dirs {
                    let pkg_lib_lean = pkg_dir.join(".lake/build/lib/lean");
                    if pkg_lib_lean.is_dir() {
                        lean_path_parts.push(pkg_lib_lean.to_string_lossy().to_string());
                    }
                    let pkg_lib = pkg_dir.join(".lake/build/lib");
                    if pkg_lib.is_dir() {
                        ld_parts.push(pkg_lib.to_string_lossy().to_string());
                    }
                }
            }
            lean_path_parts.push(tc_lib_lean.to_string_lossy().to_string());
            ld_parts.push(tc_lib_lean.to_string_lossy().to_string());
            ld_parts.push(tc_lib.to_string_lossy().to_string());
            let orig_ld = std::env::var("LD_LIBRARY_PATH").unwrap_or_default();
            if !orig_ld.is_empty() {
                ld_parts.push(orig_ld);
            }

            let mut env_map = HashMap::new();
            env_map.insert(
                "ELAN_HOME".to_string(),
                elan_home.to_string_lossy().to_string(),
            );
            env_map.insert(
                "LAKE".to_string(),
                tc_bin.join("lake").to_string_lossy().to_string(),
            );
            env_map.insert("LEAN_PATH".to_string(), lean_path_parts.join(":"));
            env_map.insert(
                "LEAN_SRC_PATH".to_string(),
                format!("{}:{}/src/lean", canon_proj.display(), tc_root.display()),
            );
            env_map.insert("LD_LIBRARY_PATH".to_string(), ld_parts.join(":"));
            let orig_path = std::env::var("PATH").unwrap_or_default();
            env_map.insert(
                "PATH".to_string(),
                format!("{}:{}:{}", tc_bin.display(), elan_bin.display(), orig_path),
            );
            env_map.insert(
                "LEAN_STACK_SIZE_KB".to_string(),
                std::env::var("LEAN_STACK_SIZE_KB").unwrap_or_else(|_| "262144".to_string()),
            );
            return Ok(env_map);
        }
    }

    if let Ok(output) = Command::new("lake")
        .arg("env")
        .arg("env")
        .current_dir(project_dir)
        .output()
    {
        if output.status.success() {
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
            if !env_map.is_empty() {
                return Ok(env_map);
            }
        }
    }

    // Zero-compiler fallback when Lean 4 / `lake` is not installed on the host:
    // synthesize local `LEAN_PATH` and `LD_LIBRARY_PATH` from `.lake/build/lib/lean` and `.lake/packages`.
    let canon_proj = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let mut env_map = HashMap::new();
    env_map.insert(
        "LEAN_PATH".to_string(),
        resolve_remote_lean_path(&canon_proj, None),
    );
    Ok(env_map)
}

pub(crate) fn merge_caller_lean_path(env_map: &mut HashMap<String, String>) {
    if let Ok(caller_lp) = std::env::var("LEAN_PATH") {
        let trimmed = caller_lp.trim();
        if !trimmed.is_empty() {
            let entry = env_map.entry("LEAN_PATH".to_string()).or_default();
            let mut existing: Vec<String> = entry
                .split(':')
                .filter(|s| !s.is_empty())
                .map(|s| s.to_string())
                .collect();
            for p in trimmed.split(':') {
                let p_trim = p.trim();
                if !p_trim.is_empty() && !existing.iter().any(|e| e == p_trim) {
                    existing.push(p_trim.to_string());
                }
            }
            *entry = existing.join(":");
        }
    }
}

fn hardlink_tree_recursive(src: &Path, dst: &Path) -> usize {
    let Ok(entries) = fs::read_dir(src) else {
        return 0;
    };
    let _ = fs::create_dir_all(dst);
    let mut count = 0usize;
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        if name == ".git" {
            continue;
        }
        let target = dst.join(&name);
        if path.is_dir() {
            count += hardlink_tree_recursive(&path, &target);
        } else if path.is_file() && !target.exists() {
            if fs::hard_link(&path, &target).is_ok() || fs::copy(&path, &target).is_ok() {
                count += 1;
            }
        }
    }
    count
}

fn strip_module_artifact_rel_slash(rel_path: &Path) -> Option<String> {
    let rel_str = rel_path.to_string_lossy().replace('\\', "/");
    let stripped = if let Some(s) = rel_str.strip_prefix("lib/lean/") {
        s
    } else if let Some(s) = rel_str.strip_prefix("ir/") {
        s
    } else {
        return None;
    };
    for suffix in [
        ".olean.server",
        ".olean.private",
        ".olean",
        ".ilean",
        ".trace",
        ".setup.json",
        ".c",
    ] {
        if let Some(stem) = stripped.strip_suffix(suffix) {
            if !stem.is_empty() {
                return Some(stem.to_string());
            }
        }
    }
    None
}

fn is_worktree_module_identical_to_main(
    main_project_dir: &Path,
    wt_project_dir: &Path,
    rel_slash: &str,
    memo: &mut HashMap<String, bool>,
    visiting: &mut HashSet<String>,
) -> bool {
    if let Some(&res) = memo.get(rel_slash) {
        return res;
    }
    if !visiting.insert(rel_slash.to_string()) {
        return true;
    }
    let main_src = resolve_project_lean_source(main_project_dir, rel_slash);
    let wt_src = resolve_project_lean_source(wt_project_dir, rel_slash);
    let ok = match (main_src, wt_src) {
        (None, None) => true,
        (Some(ms), Some(ws)) => {
            let same_hash = match (
                compute_cached_source_blake3(&ms),
                compute_cached_source_blake3(&ws),
            ) {
                (Some(mh), Some(wh)) => mh == wh,
                _ => false,
            };
            let main_olean = main_project_dir
                .join(".lake/build/lib/lean")
                .join(format!("{}.olean", rel_slash));
            let main_olean_fresh = match (
                fs::metadata(&main_olean).and_then(|m| m.modified()),
                fs::metadata(&ms).and_then(|m| m.modified()),
            ) {
                (Ok(om), Ok(sm)) => om >= sm,
                _ => false,
            };
            if !same_hash || !main_olean_fresh {
                false
            } else if let Some(imps) = read_header_imports_from_file(&ws) {
                imps.into_iter().all(|imp| {
                    let imp_slash = imp.replace('.', "/");
                    if resolve_project_lean_source(main_project_dir, &imp_slash).is_some()
                        || resolve_project_lean_source(wt_project_dir, &imp_slash).is_some()
                    {
                        is_worktree_module_identical_to_main(
                            main_project_dir,
                            wt_project_dir,
                            &imp_slash,
                            memo,
                            visiting,
                        )
                    } else {
                        true
                    }
                })
            } else {
                true
            }
        }
        _ => false,
    };
    visiting.remove(rel_slash);
    memo.insert(rel_slash.to_string(), ok);
    ok
}

fn hardlink_worktree_build_tree_verified(
    main_project_dir: &Path,
    wt_project_dir: &Path,
    build_root: &Path,
    src: &Path,
    dst: &Path,
    memo: &mut HashMap<String, bool>,
) -> usize {
    let Ok(entries) = fs::read_dir(src) else {
        return 0;
    };
    let _ = fs::create_dir_all(dst);
    let mut count = 0usize;
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name_str = name.to_string_lossy();
        if name_str == ".git"
            || name_str == ".turbo_lean_verified_sources.json"
            || name_str == ".turbo_verified_sources.json"
        {
            continue;
        }
        let target = dst.join(&name);
        if path.is_dir() {
            count += hardlink_worktree_build_tree_verified(
                main_project_dir,
                wt_project_dir,
                build_root,
                &path,
                &target,
                memo,
            );
        } else if path.is_file() && !target.exists() {
            if let Ok(rel_in_build) = path.strip_prefix(build_root) {
                if let Some(rel_slash) = strip_module_artifact_rel_slash(rel_in_build) {
                    let mut visiting = HashSet::new();
                    if !is_worktree_module_identical_to_main(
                        main_project_dir,
                        wt_project_dir,
                        &rel_slash,
                        memo,
                        &mut visiting,
                    ) {
                        continue;
                    }
                }
            }
            if fs::hard_link(&path, &target).is_ok() || fs::copy(&path, &target).is_ok() {
                count += 1;
            }
        }
    }
    count
}

/// Automatically detect if `project_dir` is inside a git worktree (`git worktree add`) whose `.lake/build/lib`
/// is missing, and hardlink verified `.lake/build` + `.lake/packages` from the main repository's `.lake/` in `< 5 ms`.
pub(crate) fn auto_hardlink_worktree_oleans_from_main_repo(project_dir: &Path) -> usize {
    if project_dir.join(".lake/build/lib").is_dir() {
        return 0;
    }
    let mut cur = Some(project_dir);
    let mut found_wt_root: Option<PathBuf> = None;
    while let Some(dir) = cur {
        if dir.join(".git").is_file() {
            found_wt_root = Some(dir.to_path_buf());
            break;
        }
        cur = dir.parent();
    }
    let Some(wt_root) = found_wt_root else {
        return 0;
    };
    let Ok(git_file) = fs::read_to_string(wt_root.join(".git")) else {
        return 0;
    };
    let Some(gitdir_str) = git_file
        .lines()
        .find_map(|l| l.strip_prefix("gitdir:").map(str::trim))
    else {
        return 0;
    };
    let gitdir_path = if Path::new(gitdir_str).is_absolute() {
        PathBuf::from(gitdir_str)
    } else {
        wt_root.join(gitdir_str)
    };
    let main_git_dir = if let Ok(common) = fs::read_to_string(gitdir_path.join("commondir")) {
        gitdir_path.join(common.trim())
    } else if let Some(p) = gitdir_path.parent().and_then(|p| p.parent()) {
        p.to_path_buf()
    } else {
        return 0;
    };
    let Ok(canon_git) = main_git_dir.canonicalize() else {
        return 0;
    };
    let Some(main_repo_root) = canon_git.parent() else {
        return 0;
    };
    let rel_sub = project_dir.strip_prefix(&wt_root).unwrap_or(Path::new(""));
    let main_project_dir = main_repo_root.join(rel_sub);
    if !main_project_dir.join(".lake").is_dir() {
        return 0;
    }
    for cfg_name in ["lean-toolchain", "lake-manifest.json"] {
        let m_cfg = main_project_dir.join(cfg_name);
        let w_cfg = project_dir.join(cfg_name);
        if m_cfg.is_file() && w_cfg.is_file() {
            if fs::read(&m_cfg).ok() != fs::read(&w_cfg).ok() {
                return 0;
            }
        }
    }
    let mut linked = 0usize;
    let src_pkgs = main_project_dir.join(".lake").join("packages");
    if src_pkgs.is_dir() {
        linked += hardlink_tree_recursive(&src_pkgs, &project_dir.join(".lake").join("packages"));
    }
    let src_build = main_project_dir.join(".lake").join("build");
    if src_build.is_dir() {
        let mut memo = HashMap::new();
        linked += hardlink_worktree_build_tree_verified(
            &main_project_dir,
            project_dir,
            &src_build,
            &src_build,
            &project_dir.join(".lake").join("build"),
            &mut memo,
        );
    }
    linked
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
    let _ = auto_hardlink_worktree_oleans_from_main_repo(&canon_dir);
    let project_key = TurboStore::compute_lake_env_key(&canon_dir);

    if let Some(mut cached) = store.get_lake_env(&project_key)? {
        merge_caller_lean_path(&mut cached);
        return Ok((cached, true));
    }

    let shm_env_path = store
        .fast_staging_dir()
        .join(format!("lake_env_v1_{}.json", project_key));
    if let Ok(bytes) = fs::read(&shm_env_path) {
        if let Ok(mut env_map) = serde_json::from_slice::<HashMap<String, String>>(&bytes) {
            if !env_map.is_empty() {
                let _ = store.put_lake_env(&project_key, &env_map);
                merge_caller_lean_path(&mut env_map);
                return Ok((env_map, false));
            }
        }
    }

    let mut env_map = spawn_lake_env(&canon_dir)?;
    if !env_map.is_empty() {
        if let Ok(bytes) = serde_json::to_vec(&env_map) {
            let _ = crate::shm_cache::atomic_write_shm(&shm_env_path, &bytes);
        }
        let _ = store.put_lake_env(&project_key, &env_map);
    }
    merge_caller_lean_path(&mut env_map);
    Ok((env_map, false))
}

pub(crate) fn resolve_or_share_lake_env(
    store: &TurboStore,
    canon_dir: &Path,
    env_key: &str,
) -> Result<Option<(HashMap<String, String>, bool)>> {
    if let Some(mut m) = store.get_lake_env(env_key)? {
        merge_caller_lean_path(&mut m);
        return Ok(Some((m, false)));
    }
    let shm_env_path = store
        .fast_staging_dir()
        .join(format!("lake_env_v1_{}.json", env_key));
    if let Ok(bytes) = fs::read(&shm_env_path) {
        if let Ok(mut env_map) = serde_json::from_slice::<HashMap<String, String>>(&bytes) {
            if !env_map.is_empty() {
                merge_caller_lean_path(&mut env_map);
                return Ok(Some((env_map, true)));
            }
        }
    }
    if let Ok(mut env_map) = spawn_lake_env(canon_dir) {
        if !env_map.is_empty() {
            if let Ok(bytes) = serde_json::to_vec(&env_map) {
                let _ = crate::shm_cache::atomic_write_shm(&shm_env_path, &bytes);
            }
            merge_caller_lean_path(&mut env_map);
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
    let local_lib = canon_dir
        .join(".lake")
        .join("build")
        .join("lib")
        .join("lean");
    if local_lib.exists() {
        parts.push(local_lib.to_string_lossy().to_string());
    }
    let pkgs_dir = canon_dir.join(".lake").join("packages");
    if let Ok(entries) = fs::read_dir(&pkgs_dir) {
        let mut pkg_libs = Vec::new();
        for entry in entries.flatten() {
            let pkg_lib = entry
                .path()
                .join(".lake")
                .join("build")
                .join("lib")
                .join("lean");
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
    if let Ok(caller_lp) = std::env::var("LEAN_PATH") {
        for p in caller_lp.split(':') {
            let trimmed = p.trim();
            if trimmed.is_empty() {
                continue;
            }
            let path = Path::new(trimmed);
            let abs = if path.is_absolute() {
                path.to_path_buf()
            } else {
                canon_dir.join(path)
            };
            if abs.exists() {
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
    // A shard accepted under a wider axiom allowlist is no cache hit under the default one.
    let allowed = splitter::allowed_axioms();
    if allowed.len() > splitter::STANDARD_AXIOMS.len() {
        key_hasher.update(b":axioms:");
        key_hasher.update(allowed.join(",").as_bytes());
    }
    key_hasher.finalize().to_hex().to_string()
}

fn par_map_indexed<T: Send, F: Fn(usize) -> T + Sync>(
    len: usize,
    min_parallel: usize,
    max_workers: usize,
    f: F,
) -> Vec<T> {
    if len < min_parallel {
        return (0..len).map(f).collect();
    }
    let workers = max_workers.min(len).max(1);
    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let f_ref = &f;
    let chunks: Vec<Vec<(usize, T)>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(workers);
        for _ in 0..workers {
            let next_ref = &next_idx;
            handles.push(s.spawn(move || {
                let mut local = Vec::new();
                loop {
                    let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if i >= len {
                        break;
                    }
                    local.push((i, f_ref(i)));
                }
                local
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or_default())
            .collect()
    });
    let mut indexed: Vec<(usize, T)> = chunks.into_iter().flatten().collect();
    indexed.sort_unstable_by_key(|(i, _)| *i);
    indexed.into_iter().map(|(_, v)| v).collect()
}

/// Read `.lean` source files in parallel across worker threads while preserving input order.
pub(crate) fn read_lean_files_parallel(paths: &[PathBuf]) -> Vec<(PathBuf, String)> {
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);
    par_map_indexed(paths.len(), 8, workers, |i| {
        (
            paths[i].clone(),
            fs::read_to_string(&paths[i]).unwrap_or_default(),
        )
    })
}

/// Stat `.lean` files in parallel across worker threads while preserving input order.
pub(crate) fn stat_lean_files_parallel(paths: &[PathBuf]) -> Vec<Option<(String, i64, i64, i64)>> {
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);
    par_map_indexed(paths.len(), 16, workers, |i| {
        fs::metadata(&paths[i]).ok().map(|m| {
            let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&m);
            (paths[i].to_string_lossy().to_string(), ms, mn, sz)
        })
    })
}

pub(crate) fn parse_header_imports(src: &str) -> Vec<String> {
    crate::module_builder::parse_header_imports(src)
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
    if file_len <= 65536 {
        let bytes = fs::read(olean_path).ok()?;
        return Some(blake3::hash(&bytes).to_hex().to_string());
    }
    let (ms, mn, _) = TurboStore::extract_file_stat_tuple(&meta);
    let mtime_ns = ms.saturating_mul(1_000_000_000).saturating_add(mn);
    #[cfg(unix)]
    let ino = {
        use std::os::unix::fs::MetadataExt;
        meta.ino()
    };
    #[cfg(not(unix))]
    let ino = 0u64;
    let mut h = blake3::Hasher::new();
    h.update(b"olean-stat:v2:");
    h.update(&file_len.to_le_bytes());
    h.update(&mtime_ns.to_le_bytes());
    h.update(&ino.to_le_bytes());
    if let Ok(mut f) = fs::File::open(olean_path) {
        use std::io::{Read, Seek, SeekFrom};
        let mut buf = [0u8; 4096];
        if let Ok(n) = f.read(&mut buf) {
            h.update(&buf[..n]);
        }
        if file_len > 8192 && f.seek(SeekFrom::End(-4096)).is_ok() {
            if let Ok(n) = f.read(&mut buf) {
                h.update(&buf[..n]);
            }
        }
    }
    Some(h.finalize().to_hex().to_string())
}

static PROJECT_SOURCE_BLAKE3_MEMO: std::sync::OnceLock<
    std::sync::Mutex<HashMap<(PathBuf, u64, i64, u64, [u8; 32]), String>>,
> = std::sync::OnceLock::new();

pub(crate) fn compute_cached_source_blake3(path: &Path) -> Option<String> {
    let meta = fs::metadata(path).ok()?;
    if !meta.is_file() {
        return None;
    }
    let file_len = meta.len();
    if file_len <= 65536 {
        let bytes = fs::read(path).ok()?;
        return Some(blake3::hash(&bytes).to_hex().to_string());
    }
    let (ms, mn, _) = TurboStore::extract_file_stat_tuple(&meta);
    let mtime_ns = ms.saturating_mul(1_000_000_000).saturating_add(mn);
    #[cfg(unix)]
    let ino = {
        use std::os::unix::fs::MetadataExt;
        meta.ino()
    };
    #[cfg(not(unix))]
    let ino = 0u64;
    let mut sample_hasher = blake3::Hasher::new();
    if let Ok(mut f) = fs::File::open(path) {
        use std::io::{Read, Seek, SeekFrom};
        let mut buf = [0u8; 4096];
        if let Ok(n) = f.read(&mut buf) {
            sample_hasher.update(&buf[..n]);
        }
        if file_len > 8192 && f.seek(SeekFrom::End(-4096)).is_ok() {
            if let Ok(n) = f.read(&mut buf) {
                sample_hasher.update(&buf[..n]);
            }
        }
    }
    let sample_key = *sample_hasher.finalize().as_bytes();
    let memo_key = (path.to_path_buf(), file_len, mtime_ns, ino, sample_key);
    let cache = PROJECT_SOURCE_BLAKE3_MEMO.get_or_init(|| std::sync::Mutex::new(HashMap::new()));
    if let Ok(guard) = cache.lock() {
        if let Some(hit) = guard.get(&memo_key) {
            return Some(hit.clone());
        }
    }
    let bytes = fs::read(path).ok()?;
    let hex = blake3::hash(&bytes).to_hex().to_string();
    if let Ok(mut guard) = cache.lock() {
        if guard.len() > 8192 {
            guard.clear();
        }
        guard.insert(memo_key, hex.clone());
    }
    Some(hex)
}

pub(crate) fn resolve_project_lean_source(project_dir: &Path, rel_slash: &str) -> Option<PathBuf> {
    if project_dir.as_os_str().is_empty() || rel_slash.is_empty() {
        return None;
    }
    let rel_file = format!("{}.lean", rel_slash);
    let direct = project_dir.join(&rel_file);
    if direct.is_file() {
        return Some(direct);
    }
    for prefix in ["submission", "src", "lean"] {
        let cand = project_dir.join(prefix).join(&rel_file);
        if cand.is_file() {
            return Some(cand);
        }
    }
    None
}

pub(crate) fn resolve_project_olean_for_rel_path(canon_dir: &Path, rel_path: &str) -> PathBuf {
    let lib_lean_dir = canon_dir
        .join(".lake")
        .join("build")
        .join("lib")
        .join("lean");
    let rel_no_ext = Path::new(rel_path).with_extension("");
    let direct = lib_lean_dir.join(&rel_no_ext).with_extension("olean");
    if direct.is_file() {
        return direct;
    }
    let mut comps = rel_no_ext.components();
    if let Some(first) = comps.next().and_then(|c| c.as_os_str().to_str()) {
        if matches!(first, "submission" | "src" | "lean") {
            let rest: PathBuf = comps.collect();
            if !rest.as_os_str().is_empty() {
                let alt = lib_lean_dir.join(&rest).with_extension("olean");
                if alt.is_file() {
                    return alt;
                }
            }
        }
    }
    direct
}

fn read_header_imports_from_file(path: &Path) -> Option<Vec<String>> {
    use std::io::Read;
    let mut f = fs::File::open(path).ok()?;
    let mut buf = [0u8; 4096];
    let n = f.read(&mut buf).ok()?;
    let prefix = String::from_utf8_lossy(&buf[..n]);
    Some(parse_header_imports(&prefix))
}

/// Compute BLAKE3 content digests of all imported `.olean` modules (and project-local `.lean` sources) for `src`.
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

    if search_dirs.is_empty() && project_dir.as_os_str().is_empty() {
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
        let sub_lean_opt = resolve_project_lean_source(project_dir, &rel_slash);
        let src_digest_opt = sub_lean_opt
            .as_deref()
            .and_then(compute_cached_source_blake3);
        let mut olean_digest_opt = None;
        for dir in &search_dirs {
            let cand = dir.join(&rel_olean);
            if let Some(digest) = compute_single_olean_digest(&cand) {
                olean_digest_opt = Some(digest);
                break;
            }
        }
        match (olean_digest_opt, src_digest_opt) {
            (Some(od), Some(sd)) => {
                out.push(format!("{}:{}:src={}", mod_name, od, sd));
            }
            (Some(od), None) => {
                out.push(format!("{}:{}", mod_name, od));
            }
            (None, Some(sd)) if !search_dirs.is_empty() => {
                out.push(format!("{}:unbuilt:src={}", mod_name, sd));
            }
            _ => {}
        }
        if let Some(ref sub_lean) = sub_lean_opt {
            if let Some(sub_mods) = read_header_imports_from_file(sub_lean) {
                for sub_mod in sub_mods {
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
    let dir = store.fast_staging_dir().join("file_splits_v3");
    let _ = fs::create_dir_all(&dir);
    dir
}

pub(crate) fn compute_single_stat_hash(pk: &str, ms: i64, mn: i64, sz: i64) -> String {
    let mut h = blake3::Hasher::new();
    h.update(b"single-stat-split:v3\n");
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
    h.update(b"project-stat-splits:v3\n");
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

    let summary_path = if paths.len() <= 128 && valid_stats.len() == paths.len() {
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
        // Raw items: this summary is cached, so the axiom policy is applied where it is used.
        if !split.hygiene.flagged_items.is_empty() {
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

/// Fast-path project interface key computation using the `/dev/shm` project stat summary
/// so `build` and `ci-verify` cache hits never need to deserialize full `SplitResult` shard arrays.
pub(crate) fn compute_project_interface_key_fast_summary(
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

    for cfg_name in ["lakefile.toml", "lake-manifest.json"] {
        if let Ok(bytes) = fs::read(project_dir.join(cfg_name)) {
            let cfg_hash = blake3::hash(&bytes);
            hasher.update(cfg_name.as_bytes());
            hasher.update(b":");
            hasher.update(cfg_hash.as_bytes());
            hasher.update(b"\n");
        }
    }
    hasher.update(std::env::consts::OS.as_bytes());
    hasher.update(b"-");
    hasher.update(std::env::consts::ARCH.as_bytes());
    hasher.update(b"\n");

    let lean_files = collect_project_lean_files(project_dir, true, None);
    let summary = load_project_stat_summary_cached(store, project_dir, &lean_files)?;
    let mut interface_hasher = blake3::Hasher::new();
    interface_hasher.update(toolchain.as_bytes());

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

    let shm_stat_path = if paths.len() <= 128 && valid_stats.len() == paths.len() {
        let stat_hash = compute_stat_slice_hash(&valid_stats);
        let p = store
            .fast_staging_dir()
            .join(format!("project_stat_splits_v3_{}.json", &stat_hash[..24]));
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

pub(crate) fn compute_file_split_key_with_deps(src_blake3: &str, dep_hashes: &[String]) -> String {
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

    let file_keys: Vec<(String, String)> = par_map_indexed(files.len(), 8, default_workers, |i| {
        let sb = blake3::hash(files[i].1.as_bytes()).to_hex().to_string();
        let fk = compute_file_split_key_with_deps(&sb, &file_deps[i]);
        (sb, fk)
    });

    let shm_proj_path = if files.len() <= 128 {
        let mut ch = blake3::Hasher::new();
        ch.update(b"project-content-splits:v3\n");
        for (_, fk) in &file_keys {
            ch.update(fk.as_bytes());
            ch.update(b"\n");
        }
        let p = store.fast_staging_dir().join(format!(
            "project_splits_v3_{}.json",
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
        let computed_misses: Vec<(usize, splitter::SplitResult)> =
            par_map_indexed(miss_indices.len(), 2, default_workers, |m_pos| {
                let file_idx = miss_indices[m_pos];
                (
                    file_idx,
                    split_lean_source(&files[file_idx].1, &file_deps[file_idx]),
                )
            });

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
                if !st_path.exists() || !new_splits.is_empty() {
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
    if files.len() <= 128 && valid_stats.len() == files.len() {
        let stat_hash = compute_stat_slice_hash(&valid_stats);
        let stat_p = store
            .fast_staging_dir()
            .join(format!("project_stat_splits_v3_{}.json", &stat_hash[..24]));
        if !stat_p.exists() || !new_splits.is_empty() {
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
    let lib_lean_dir = canon_dir
        .join(".lake")
        .join("build")
        .join("lib")
        .join("lean");
    if !lib_lean_dir.is_dir() {
        return false;
    }

    let manifest_path = verified_sources_manifest_path(canon_dir);
    let mut recorded_opt: Option<BTreeMap<String, String>> = None;
    if let Ok(bytes) = fs::read(&manifest_path) {
        if let Ok(recorded) = serde_json::from_slice::<BTreeMap<String, String>>(&bytes) {
            if &recorded == file_hashes {
                let mut checked_oleans = 0usize;
                let mut all_present = true;
                for rel_path in file_hashes.keys() {
                    if rel_path == "lakefile.lean" || rel_path.ends_with("/lakefile.lean") {
                        continue;
                    }
                    let rel_no_ext = Path::new(rel_path).with_extension("");
                    let olean_path = resolve_project_olean_for_rel_path(canon_dir, rel_path);
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
                            all_present = false;
                            break;
                        }
                    }
                }
                if all_present && checked_oleans > 0 {
                    return true;
                }
            } else {
                return false;
            }
            recorded_opt = Some(recorded);
        } else {
            return false;
        }
    }

    let dep_manifest_path = canon_dir
        .join(".lake")
        .join("build")
        .join(".turbo_verified_sources.json");
    if let Ok(bytes) = fs::read(&dep_manifest_path) {
        if let Ok(val) = serde_json::from_slice::<serde_json::Value>(&bytes) {
            if let Some(mods) = val.get("modules").and_then(|m| m.as_object()) {
                for (rel_k, entry) in mods {
                    if let Some(rec_b3) = entry.get("src_blake3").and_then(|s| s.as_str()) {
                        if let Some(cur_b3) = file_hashes.get(rel_k) {
                            if rec_b3 != cur_b3 {
                                return false;
                            }
                        }
                    }
                }
            }
        }
    }

    let lakefile_mtime = [
        "lakefile.lean",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
    ]
    .into_iter()
    .filter_map(|name| {
        fs::metadata(canon_dir.join(name))
            .and_then(|m| m.modified())
            .ok()
    })
    .max();
    let mut checked_oleans = 0usize;
    let mut all_mtime_fresh = true;

    for rel_path in file_hashes.keys() {
        if rel_path == "lakefile.lean" || rel_path.ends_with("/lakefile.lean") {
            continue;
        }
        let rel_no_ext = Path::new(rel_path).with_extension("");
        let olean_path = resolve_project_olean_for_rel_path(canon_dir, rel_path);
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

        let src_path = canon_dir.join(rel_path);
        let src_mtime = fs::metadata(&src_path).and_then(|m| m.modified()).ok();
        let olean_mtime = olean_meta.modified().ok();
        let is_mtime_fresh = match (src_mtime, olean_mtime) {
            (Some(sm), Some(om)) if om >= sm => lakefile_mtime.map_or(true, |lm| om >= lm),
            _ => false,
        };
        if !is_mtime_fresh {
            all_mtime_fresh = false;
            break;
        }
        if let (Some(om), Some(imps)) = (olean_mtime, read_header_imports_from_file(&src_path)) {
            for imp in imps {
                let imp_slash = imp.replace('.', "/");
                if let Some(dep_src) = resolve_project_lean_source(canon_dir, &imp_slash) {
                    if let Ok(dep_sm) = fs::metadata(&dep_src).and_then(|m| m.modified()) {
                        if om < dep_sm {
                            all_mtime_fresh = false;
                            break;
                        }
                    }
                    let dep_olean = lib_lean_dir.join(format!("{}.olean", imp_slash));
                    if let Ok(dep_om) = fs::metadata(&dep_olean).and_then(|m| m.modified()) {
                        if om < dep_om {
                            all_mtime_fresh = false;
                            break;
                        }
                    } else {
                        all_mtime_fresh = false;
                        break;
                    }
                }
            }
            if !all_mtime_fresh {
                break;
            }
        }
    }

    if checked_oleans == 0 {
        return false;
    }

    if all_mtime_fresh && recorded_opt.is_none() {
        record_verified_project_oleans(canon_dir, file_hashes);
        return true;
    }

    false
}

pub(crate) fn is_file_and_imports_verified_in_manifest(
    canon_dir: &Path,
    canon_file: &Path,
    actual_hash: &str,
    recorded: &BTreeMap<String, String>,
) -> bool {
    let rel_path = canon_file
        .strip_prefix(canon_dir)
        .unwrap_or(canon_file)
        .to_string_lossy()
        .replace('\\', "/");
    if recorded.get(&rel_path).map(|s| s.as_str()) != Some(actual_hash) {
        return false;
    }
    let self_olean = resolve_project_olean_for_rel_path(canon_dir, &rel_path);
    if !self_olean.is_file() {
        return false;
    }
    let lib_lean_dir = canon_dir.join(".lake/build/lib/lean");
    let mut worklist = read_header_imports_from_file(canon_file).unwrap_or_default();
    let mut visited = HashSet::new();
    while let Some(mod_name) = worklist.pop() {
        if !visited.insert(mod_name.clone()) {
            continue;
        }
        let imp_slash = mod_name.replace('.', "/");
        if let Some(dep_src) = resolve_project_lean_source(canon_dir, &imp_slash) {
            let dep_rel = dep_src
                .strip_prefix(canon_dir)
                .unwrap_or(&dep_src)
                .to_string_lossy()
                .replace('\\', "/");
            let Some(expected_dep_hash) = recorded.get(&dep_rel) else {
                return false;
            };
            let Some(actual_dep_hash) = compute_cached_source_blake3(&dep_src) else {
                return false;
            };
            if &actual_dep_hash != expected_dep_hash {
                return false;
            }
            let dep_olean = lib_lean_dir.join(format!("{}.olean", imp_slash));
            if !dep_olean.is_file() {
                return false;
            }
            if let Some(sub_imps) = read_header_imports_from_file(&dep_src) {
                for sub_imp in sub_imps {
                    if !visited.contains(&sub_imp) {
                        worklist.push(sub_imp);
                    }
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
    let manifest_path = verified_sources_manifest_path(canon_dir);
    let Ok(bytes) = fs::read(&manifest_path) else {
        return false;
    };
    let Ok(recorded) = serde_json::from_slice::<BTreeMap<String, String>>(&bytes) else {
        return false;
    };
    is_file_and_imports_verified_in_manifest(canon_dir, canon_file, actual_hash, &recorded)
}

pub(crate) fn is_file_verified_in_lake_build(
    canon_dir: &Path,
    canon_file: &Path,
    src: &str,
) -> bool {
    let actual_hash = blake3::hash(src.as_bytes()).to_hex().to_string();
    is_file_hash_verified_in_lake_build(canon_dir, canon_file, &actual_hash)
}

/// Recursively discover `.lean` source files inside `root` (or optional `scope` subdirectory),
/// excluding all hidden directories (`.*` such as `.benchmark-tools`, `.lake`, `.git`, `.elan`),
/// `target`, and `node_modules`.
pub(crate) fn collect_project_lean_files(
    root: &Path,
    include_lakefile: bool,
    scope: Option<&Path>,
) -> Vec<PathBuf> {
    let walk_root = match scope {
        Some(sc) => {
            let joined = if sc.is_absolute() {
                sc.to_path_buf()
            } else {
                root.join(sc)
            };
            joined.canonicalize().unwrap_or(joined)
        }
        None => root.to_path_buf(),
    };
    if walk_root.is_file() {
        return vec![walk_root];
    }
    let mut lean_files: Vec<PathBuf> = Vec::new();
    for entry in WalkDir::new(&walk_root)
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
                && name != ".benchmark-tools"
                && name != "target"
                && name != "node_modules"
        })
        .flatten()
    {
        if entry.file_type().is_file() {
            let p = entry.path();
            if p.extension().and_then(|s| s.to_str()) == Some("lean")
                && (include_lakefile
                    || p.file_name().and_then(|s| s.to_str()) != Some("lakefile.lean"))
            {
                lean_files.push(p.to_path_buf());
            }
        }
    }
    lean_files.sort();
    lean_files
}

/// Recursively discover `.lean` source files inside a file or directory (excluding hidden directories, `target`, `node_modules`, and `lakefile.lean`).
pub(crate) fn collect_lean_files(root: &Path) -> Vec<PathBuf> {
    collect_project_lean_files(root, false, None)
}

/// Resolve the pre-compiled `.olean` module import name (e.g. `TurboLean.Reflection`) if
/// `.lake/build/lib/lean/<Module>.olean` exists on disk and its source + transitive project-local
/// imports are not stale relative to the `.olean` on disk.
pub(crate) fn resolve_prebuilt_module_import(
    canon_project_dir: &Path,
    canon_file: &Path,
) -> Option<String> {
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
        let pkg_rel_parts = &parts[3..];
        let mut pkg_rel = PathBuf::new();
        for p in pkg_rel_parts {
            pkg_rel.push(p);
        }
        let pkg_olean = canon_project_dir
            .join(".lake")
            .join("packages")
            .join(pkg_name)
            .join(".lake")
            .join("build")
            .join("lib")
            .join("lean")
            .join(&pkg_rel)
            .with_extension("olean");
        let root_olean = canon_project_dir
            .join(".lake")
            .join("build")
            .join("lib")
            .join("lean")
            .join(&pkg_rel)
            .with_extension("olean");
        if pkg_olean.exists() || root_olean.exists() {
            return Some(pkg_rel_parts.join("."));
        }
        return None;
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

    let manifest_path = verified_sources_manifest_path(canon_project_dir);
    let recorded_opt = fs::read(&manifest_path)
        .ok()
        .and_then(|b| serde_json::from_slice::<BTreeMap<String, String>>(&b).ok());
    if let Some(ref recorded) = recorded_opt {
        let actual_hash = compute_cached_source_blake3(canon_file)?;
        if !is_file_and_imports_verified_in_manifest(
            canon_project_dir,
            canon_file,
            &actual_hash,
            recorded,
        ) {
            return None;
        }
    } else {
        let self_om = fs::metadata(&olean_path).and_then(|m| m.modified()).ok()?;
        let self_sm = fs::metadata(canon_file).and_then(|m| m.modified()).ok()?;
        if self_om < self_sm {
            return None;
        }
        let mut worklist = read_header_imports_from_file(canon_file).unwrap_or_default();
        let mut visited = HashSet::new();
        while let Some(mod_name) = worklist.pop() {
            if !visited.insert(mod_name.clone()) {
                continue;
            }
            let imp_slash = mod_name.replace('.', "/");
            if let Some(dep_src) = resolve_project_lean_source(canon_project_dir, &imp_slash) {
                let dep_olean = lib_lean_dir.join(format!("{}.olean", imp_slash));
                let dep_om = fs::metadata(&dep_olean).and_then(|m| m.modified()).ok()?;
                let dep_sm = fs::metadata(&dep_src).and_then(|m| m.modified()).ok()?;
                if dep_om < dep_sm || self_om < dep_sm || self_om < dep_om {
                    return None;
                }
                if let Some(sub_imps) = read_header_imports_from_file(&dep_src) {
                    for sub_imp in sub_imps {
                        if !visited.contains(&sub_imp) {
                            worklist.push(sub_imp);
                        }
                    }
                }
            }
        }
    }
    Some(mod_parts.join("."))
}

fn remove_module_build_artifacts(canon_dir: &Path, rel_slash: &str) {
    let lib_lean_dir = canon_dir.join(".lake/build/lib/lean");
    let ir_dir = canon_dir.join(".lake/build/ir");
    for suffix in [
        ".olean",
        ".olean.server",
        ".olean.private",
        ".ilean",
        ".trace",
    ] {
        let p = lib_lean_dir.join(format!("{}{}", rel_slash, suffix));
        let _ = fs::remove_file(p);
    }
    for suffix in [".c", ".setup.json", ".ilean", ".trace"] {
        let p = ir_dir.join(format!("{}{}", rel_slash, suffix));
        let _ = fs::remove_file(p);
    }
}

/// Inspect all transitive project-local imports of `target_files` in `canon_dir`.
/// If any imported project-local module `<M>` has a stale `.olean` on disk (older than `<M>.lean`,
/// older than one of its transitive dependencies, or mismatched against `.turbo_lean_verified_sources.json` /
/// `.turbo_verified_sources.json`), immediately purge the stale `.olean` artifacts and, if a Lake
/// config is present, rebuild the stale imported modules natively so `lean` / `ZygoteWorker` never
/// elaborates against a stale `.olean`.
pub(crate) fn ensure_project_imports_fresh_for_check(
    store: &mut TurboStore,
    canon_dir: &Path,
    target_files: &[PathBuf],
) -> Result<usize> {
    let lib_lean_dir = canon_dir.join(".lake/build/lib/lean");
    if !lib_lean_dir.is_dir() {
        return Ok(0);
    }
    let manifest_path = verified_sources_manifest_path(canon_dir);
    let recorded_opt = fs::read(&manifest_path)
        .ok()
        .and_then(|b| serde_json::from_slice::<BTreeMap<String, String>>(&b).ok());
    let dep_manifest_path = canon_dir
        .join(".lake")
        .join("build")
        .join(".turbo_verified_sources.json");
    let dep_manifest_opt = fs::read(&dep_manifest_path)
        .ok()
        .and_then(|b| serde_json::from_slice::<serde_json::Value>(&b).ok());

    let mut worklist: Vec<String> = Vec::new();
    let mut target_rel_slashes: Vec<String> = Vec::new();
    for tf in target_files {
        if let Some(imps) = read_header_imports_from_file(tf) {
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

    let mut visited = HashSet::new();
    let mut ordered_imports: Vec<(String, String, PathBuf)> = Vec::new();
    let mut adj: HashMap<String, Vec<String>> = HashMap::new();
    while let Some(mod_name) = worklist.pop() {
        if !visited.insert(mod_name.clone()) {
            continue;
        }
        let imp_slash = mod_name.replace('.', "/");
        if let Some(dep_src) = resolve_project_lean_source(canon_dir, &imp_slash) {
            let sub_imps = read_header_imports_from_file(&dep_src).unwrap_or_default();
            for sub_imp in &sub_imps {
                if !visited.contains(sub_imp) {
                    worklist.push(sub_imp.clone());
                }
            }
            adj.insert(mod_name.clone(), sub_imps);
            ordered_imports.push((mod_name, imp_slash, dep_src));
        }
    }
    if ordered_imports.is_empty() {
        return Ok(0);
    }

    let mut stale_mods: HashSet<String> = HashSet::new();
    for (mod_name, imp_slash, dep_src) in &ordered_imports {
        let dep_olean = lib_lean_dir.join(format!("{}.olean", imp_slash));
        let olean_meta = fs::metadata(&dep_olean).ok();
        let src_meta = fs::metadata(dep_src).ok();
        let dep_rel = dep_src
            .strip_prefix(canon_dir)
            .unwrap_or(dep_src)
            .to_string_lossy()
            .replace('\\', "/");
        let cur_hash = compute_cached_source_blake3(dep_src);

        let mut is_stale = false;
        if let (Some(ref rec), Some(ref ch)) = (&recorded_opt, &cur_hash) {
            if rec.get(&dep_rel) != Some(ch) {
                is_stale = true;
            }
        }
        if let (Some(ref dm), Some(ref ch)) = (&dep_manifest_opt, &cur_hash) {
            if let Some(rec_b3) = dm
                .get("modules")
                .and_then(|m| m.get(&dep_rel))
                .and_then(|e| e.get("src_blake3"))
                .and_then(|s| s.as_str())
            {
                if rec_b3 != ch {
                    is_stale = true;
                }
            }
        }
        match (&olean_meta, &src_meta) {
            (Some(om), Some(sm)) => {
                if let (Ok(ot), Ok(st)) = (om.modified(), sm.modified()) {
                    if ot < st && recorded_opt.is_none() {
                        is_stale = true;
                    }
                }
            }
            _ => {}
        }
        if is_stale {
            stale_mods.insert(mod_name.clone());
        }
    }

    // Propagate staleness downstream across the imported project subgraph.
    let mut changed = !stale_mods.is_empty();
    while changed {
        changed = false;
        for (mod_name, imp_slash, _) in &ordered_imports {
            if stale_mods.contains(mod_name) {
                continue;
            }
            let dep_olean = lib_lean_dir.join(format!("{}.olean", imp_slash));
            let self_om = fs::metadata(&dep_olean).and_then(|m| m.modified()).ok();
            if let Some(children) = adj.get(mod_name) {
                for ch in children {
                    if stale_mods.contains(ch) {
                        stale_mods.insert(mod_name.clone());
                        changed = true;
                        break;
                    }
                    let ch_slash = ch.replace('.', "/");
                    if let Some(ch_src) = resolve_project_lean_source(canon_dir, &ch_slash) {
                        let ch_olean = lib_lean_dir.join(format!("{}.olean", ch_slash));
                        let ch_om = fs::metadata(&ch_olean).and_then(|m| m.modified()).ok();
                        let ch_sm = fs::metadata(&ch_src).and_then(|m| m.modified()).ok();
                        if let (Some(som), Some(com)) = (self_om, ch_om) {
                            if som < com && recorded_opt.is_none() {
                                stale_mods.insert(mod_name.clone());
                                changed = true;
                                break;
                            }
                        }
                        if let (Some(som), Some(csm)) = (self_om, ch_sm) {
                            if som < csm && recorded_opt.is_none() {
                                stale_mods.insert(mod_name.clone());
                                changed = true;
                                break;
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

    let _ = fs::remove_file(&manifest_path);
    for (mod_name, imp_slash, _) in &ordered_imports {
        if stale_mods.contains(mod_name) {
            remove_module_build_artifacts(canon_dir, imp_slash);
        }
    }
    for t_slash in &target_rel_slashes {
        remove_module_build_artifacts(canon_dir, t_slash);
    }

    let has_lake_cfg =
        canon_dir.join("lakefile.lean").is_file() || canon_dir.join("lakefile.toml").is_file();
    if has_lake_cfg {
        let mut rebuild_targets: Vec<String> = stale_mods.iter().cloned().collect();
        rebuild_targets.sort();
        let _ = crate::module_builder::build_project_modules_native(
            store,
            canon_dir,
            &rebuild_targets,
            "trusted",
            0,
            false,
            true,
            None,
        );
    }
    Ok(stale_mods.len())
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
        let file_name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
        let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
        let kind = if file_name.ends_with(".olean.server") {
            "olean_server"
        } else if file_name.ends_with(".olean.private") {
            "olean_private"
        } else if file_name.ends_with(".ir.sig") {
            "ir_sig"
        } else {
            match ext {
                "olean" => "olean",
                "ilean" => "ilean",
                "ir" => "ir",
                "c" => "c",
                _ => continue,
            }
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

    let entries: Vec<BlobEntry> = fs::read(&ingest_cache_path)
        .ok()
        .and_then(|b| serde_json::from_slice::<Vec<BlobEntry>>(&b).ok())
        .filter(|v| v.len() == candidates.len())
        .unwrap_or_default();

    let from_ingest_cache = entries.len() == candidates.len();
    let entries = if from_ingest_cache {
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
    let mut seen_shared_prefix = [false; 256];
    let mut seen_blobs = std::collections::HashSet::with_capacity(entries.len());
    let mut reg_blobs = Vec::with_capacity(entries.len());
    let dest_ino = |d: &Path| -> i64 {
        #[cfg(unix)]
        {
            fs::metadata(d).map(|m| m.ino() as i64).unwrap_or(0)
        }
        #[cfg(not(unix))]
        {
            let _ = d;
            0
        }
    };

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
        let shared_dir = shared_blobs.join(prefix);
        let shared_p = shared_dir.join(&entry.blob_hash);
        let fallback_p = fallback_shm_blobs.join(prefix).join(&entry.blob_hash);
        let mut sync_shared = |dest_p: &Path| {
            if !seen_shared_prefix[p_idx] {
                seen_shared_prefix[p_idx] = true;
                let _ = fs::create_dir_all(&shared_dir);
            }
            if !shared_p.exists() {
                let _ = fs::hard_link(dest_p, &shared_p);
            }
        };
        let ino = if fs::hard_link(path, &dest).is_ok() {
            if !from_ingest_cache {
                sync_shared(&dest);
            }
            *cand_ino
        } else if fs::hard_link(&shared_p, &dest).is_ok()
            || (has_distinct_fallback && fs::hard_link(&fallback_p, &dest).is_ok())
        {
            sync_shared(&dest);
            dest_ino(&dest)
        } else if dest.exists() {
            dest_ino(&dest)
        } else {
            let staging_dir = store.root.join("staging");
            let _ = fs::create_dir_all(&staging_dir);
            let tmp_dest =
                staging_dir.join(format!("{}.{}.tmp", entry.blob_hash, std::process::id()));
            fs::copy(path, &tmp_dest)?;
            #[cfg(unix)]
            let _ = fs::set_permissions(&tmp_dest, fs::Permissions::from_mode(0o444));
            let _ = fs::rename(&tmp_dest, &dest);
            sync_shared(&dest);
            dest_ino(&dest)
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

/// Deduplicate `.lake/packages` across multi-agent worktrees:
/// 1. Removes leftover `*.barrel` archive files in `.lake/packages` and `.lake/cache`.
/// 2. Strips `.git/objects/pack/*.pack` and loose objects inside `.lake/packages/*/.git/objects`.
/// 3. Deduplicates `.olean`, `.olean.private`, `.olean.server`, and `.ilean` files inside
///    `.lake/packages` against a shared `store.root.join("pkg_cas")` directory via BLAKE3 + hardlinking.
pub fn dedup_worktree_packages(
    store: &TurboStore,
    project_dir: &Path,
) -> Result<serde_json::Value> {
    #[cfg(unix)]
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    let t0 = Instant::now();
    let lake_dir = project_dir.join(".lake");
    let packages_dir = lake_dir.join("packages");
    let pkg_cas_dir = store.root.join("pkg_cas");
    let _ = fs::create_dir_all(&pkg_cas_dir);

    let mut purged_barrels = 0u64;
    let mut purged_git_packs = 0u64;
    let mut hardlinked_files = 0u64;
    let mut freed_bytes = 0u64;
    let mut deduped_bytes = 0u64;

    if lake_dir.is_dir() {
        let mut stack = vec![lake_dir];
        let mut seen_hash_cache: HashMap<(u64, u64), String> = HashMap::new();
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
                    let Ok(meta) = entry.metadata() else {
                        continue;
                    };
                    let sz = meta.len();
                    if sz == 0 {
                        continue;
                    }
                    #[cfg(unix)]
                    let file_ino = (meta.dev(), meta.ino());
                    #[cfg(not(unix))]
                    let file_ino = (0u64, 0u64);

                    let hash_hex = if let Some(h) = seen_hash_cache.get(&file_ino) {
                        h.clone()
                    } else {
                        let Ok(bytes) = fs::read(&path) else {
                            continue;
                        };
                        let h = blake3::hash(&bytes).to_hex().to_string();
                        if file_ino.1 != 0 {
                            seen_hash_cache.insert(file_ino, h.clone());
                        }
                        h
                    };

                    let shard_dir = pkg_cas_dir.join(&hash_hex[0..2]);
                    let _ = fs::create_dir_all(&shard_dir);
                    let cas_file = shard_dir.join(&hash_hex);

                    if let Ok(cas_meta) = fs::metadata(&cas_file) {
                        #[cfg(unix)]
                        let same_inode =
                            cas_meta.dev() == meta.dev() && cas_meta.ino() == meta.ino();
                        #[cfg(not(unix))]
                        let same_inode = false;

                        if !same_inode
                            && crate::db::try_reflink_or_hardlink(&cas_file, &path).is_ok()
                        {
                            hardlinked_files += 1;
                            deduped_bytes += sz;
                        }
                    } else {
                        #[cfg(unix)]
                        {
                            let mut perms = meta.permissions();
                            if (perms.mode() & 0o222) != 0 {
                                perms.set_mode(0o444);
                                let _ = fs::set_permissions(&path, perms);
                            }
                        }
                        if fs::hard_link(&path, &cas_file).is_ok() {
                            hardlinked_files += 1;
                        } else {
                            let tmp_cas =
                                shard_dir.join(format!("{}.{}.tmp", hash_hex, std::process::id()));
                            if fs::copy(&path, &tmp_cas).is_ok() {
                                #[cfg(unix)]
                                if let Ok(tm) = fs::metadata(&tmp_cas) {
                                    let mut perms = tm.permissions();
                                    perms.set_mode(0o444);
                                    let _ = fs::set_permissions(&tmp_cas, perms);
                                }
                                if fs::rename(&tmp_cas, &cas_file).is_ok() {
                                    if crate::db::try_reflink_or_hardlink(&cas_file, &path).is_ok()
                                    {
                                        hardlinked_files += 1;
                                    }
                                } else {
                                    let _ = fs::remove_file(&tmp_cas);
                                }
                            }
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
    let t0 = Instant::now();
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.clone());
    let project_name = canon_dir
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "lean-project".to_string());
    let toolchain = detect_toolchain(&canon_dir);
    let (action_key, interface_hash, file_hashes) = compute_project_interface_key_fast_summary(
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
            if !crate::mcp::is_invoked_by_autonomous_governor()
                && std::env::var("SANDBOXED_TELEMETRY_BATCH_ONLY")
                    .unwrap_or_default()
                    .trim()
                    != "1"
            {
                crate::mcp::emit_sandboxed_telemetry_event(
                    serde_json::json!({
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
                        "elapsed_ms": elapsed_ms,
                    }),
                    "turbo_lean_events.jsonl",
                );
            }
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
            let mut build_report = crate::module_builder::NativeBuildReport::default();
            if !targets.is_empty() || !are_all_project_oleans_up_to_date(&canon_dir, &file_hashes) {
                build_report = crate::module_builder::build_project_modules_native(
                    store,
                    &canon_dir,
                    &targets,
                    &trust_domain,
                    pin_level,
                    false,
                    json_output,
                    Some(&file_hashes),
                )?;
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
            if !crate::mcp::is_invoked_by_autonomous_governor()
                && std::env::var("SANDBOXED_TELEMETRY_BATCH_ONLY")
                    .unwrap_or_default()
                    .trim()
                    != "1"
            {
                crate::mcp::emit_sandboxed_telemetry_event(
                    serde_json::json!({
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
                        "elapsed_ms": dur_ms,
                    }),
                    "turbo_lean_events.jsonl",
                );
            }

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
                        "modules_total": build_report.modules_total,
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

        let dep_hashes_v1 = compute_imported_olean_interface_hashes(src, &tmp_dir, Some(&lp_str));
        assert!(dep_hashes_v1.len() == 1 && dep_hashes_v1[0].starts_with("Foo.Bar:"));

        let split_v1 = split_lean_source(src, &dep_hashes_v1);
        assert_eq!(split_v1.shards.len(), 1);
        let shard_v1 = &split_v1.shards[0];
        let key_v1 = compute_shard_key("leanprover/lean4:v4.35.0", shard_v1);

        // Modify 1 byte inside the .olean file in place (preserving length)
        olean_bytes[128] ^= 0xFF;
        fs::write(&olean_path, &olean_bytes).expect("modify dummy .olean in place");

        let dep_hashes_v2 = compute_imported_olean_interface_hashes(src, &tmp_dir, Some(&lp_str));
        assert!(dep_hashes_v2.len() == 1 && dep_hashes_v1 != dep_hashes_v2);

        let split_v2 = split_lean_source(src, &dep_hashes_v2);
        let shard_v2 = &split_v2.shards[0];
        let key_v2 = compute_shard_key("leanprover/lean4:v4.35.0", shard_v2);

        assert!(
            shard_v1.cone_env_hash != shard_v2.cone_env_hash
                && shard_v1.prefix_env_hash != shard_v2.prefix_env_hash
                && key_v1 != key_v2
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_dedup_worktree_packages_hardlinks_and_purges_barrels() -> Result<()> {
        #[cfg(unix)]
        use std::os::unix::fs::MetadataExt;
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_dedup_pkgs_test_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let (cache_dir, wt1, wt2) = (
            tmp_dir.join("cache"),
            tmp_dir.join("wt1"),
            tmp_dir.join("wt2"),
        );

        let pkg1_dir = wt1.join(".lake/packages/mathlib/.lake/build/lib/lean/Mathlib");
        let pkg2_dir = wt2.join(".lake/packages/mathlib/.lake/build/lib/lean/Mathlib");
        fs::create_dir_all(&pkg1_dir)?;
        fs::create_dir_all(&pkg2_dir)?;

        let (olean1, olean2) = (pkg1_dir.join("Basic.olean"), pkg2_dir.join("Basic.olean"));
        let barrel1 = wt1.join(".lake/packages/mathlib/mathlib.barrel");

        let payload = vec![0xABu8; 2048];
        fs::write(&olean1, &payload)?;
        fs::write(&olean2, &payload)?;
        fs::write(&barrel1, vec![0xCDu8; 1024])?;

        assert_ne!(fs::metadata(&olean1)?.ino(), fs::metadata(&olean2)?.ino());
        let store = TurboStore::open(Some(&cache_dir))?;

        let rep1 = dedup_worktree_packages(&store, &wt1)?;
        assert!(
            rep1["status"] == "worktree_packages_deduped"
                && rep1["barrels_removed"] == 1
                && !barrel1.exists()
        );

        let rep2 = dedup_worktree_packages(&store, &wt2)?;
        assert!(
            rep2["status"] == "worktree_packages_deduped"
                && rep2["files_hardlinked"] == 1
                && rep2["bytes_saved"].as_u64().unwrap_or(0) >= 2048
        );
        assert_eq!(fs::metadata(&olean1)?.ino(), fs::metadata(&olean2)?.ino());

        let main_repo = tmp_dir.join("main_repo");
        let main_git = main_repo.join(".git/worktrees/wt_auto");
        let main_olean = main_repo.join(".lake/build/lib/lean/MainMod.olean");
        fs::create_dir_all(&main_git)?;
        fs::create_dir_all(main_olean.parent().unwrap())?;
        fs::write(main_git.join("commondir"), "../..\n")?;
        fs::write(&main_olean, vec![0xEFu8; 512])?;

        let wt_auto = tmp_dir.join("wt_auto");
        fs::create_dir_all(&wt_auto)?;
        fs::write(
            wt_auto.join(".git"),
            format!("gitdir: {}\n", main_git.display()),
        )?;
        assert_eq!(auto_hardlink_worktree_oleans_from_main_repo(&wt_auto), 1);
        assert_eq!(
            fs::metadata(&main_olean)?.ino(),
            fs::metadata(wt_auto.join(".lake/build/lib/lean/MainMod.olean"))?.ino()
        );

        // Now verify that when a module or its transitive import differs in the worktree,
        // `auto_hardlink_worktree_oleans_from_main_repo` skips hardlinking that module's `.olean`
        // and never hardlinks `.turbo_lean_verified_sources.json`.
        let main_git2 = main_repo.join(".git/worktrees/wt_diff");
        fs::create_dir_all(&main_git2)?;
        fs::write(main_git2.join("commondir"), "../..\n")?;
        fs::create_dir_all(main_repo.join("Guest"))?;
        fs::create_dir_all(main_repo.join("submission/InitECandidate/Solver"))?;
        fs::write(
            main_repo.join("Guest/Ast.lean"),
            "namespace Guest\ndef totalCols : Nat := 928\nend Guest\n",
        )?;
        fs::write(
            main_repo.join("submission/InitECandidate/Solver/GuestStepBound.lean"),
            "import Guest.Ast\ntheorem t : Guest.totalCols = 928 := rfl\n",
        )?;
        let main_ast_olean = main_repo.join(".lake/build/lib/lean/Guest/Ast.olean");
        let main_bound_olean =
            main_repo.join(".lake/build/lib/lean/InitECandidate/Solver/GuestStepBound.olean");
        fs::create_dir_all(main_ast_olean.parent().unwrap())?;
        fs::create_dir_all(main_bound_olean.parent().unwrap())?;
        fs::write(&main_ast_olean, b"ast-928-olean")?;
        fs::write(&main_bound_olean, b"bound-928-olean")?;
        fs::write(
            main_repo.join(".lake/build/.turbo_lean_verified_sources.json"),
            b"{\"Guest/Ast.lean\":\"dummy\"}",
        )?;

        let wt_diff = tmp_dir.join("wt_diff");
        fs::create_dir_all(wt_diff.join("Guest"))?;
        fs::create_dir_all(wt_diff.join("submission/InitECandidate/Solver"))?;
        fs::write(
            wt_diff.join(".git"),
            format!("gitdir: {}\n", main_git2.display()),
        )?;
        // In wt_diff, `Guest/Ast.lean` is modified (`934`), while `GuestStepBound.lean` is identical!
        fs::write(
            wt_diff.join("Guest/Ast.lean"),
            "namespace Guest\ndef totalCols : Nat := 934\nend Guest\n",
        )?;
        fs::write(
            wt_diff.join("submission/InitECandidate/Solver/GuestStepBound.lean"),
            "import Guest.Ast\ntheorem t : Guest.totalCols = 928 := rfl\n",
        )?;
        let _ = auto_hardlink_worktree_oleans_from_main_repo(&wt_diff);
        assert!(
            !wt_diff
                .join(".lake/build/lib/lean/Guest/Ast.olean")
                .exists(),
            "modified Guest/Ast.olean must not be hardlinked into worktree"
        );
        assert!(
            !wt_diff
                .join(".lake/build/lib/lean/InitECandidate/Solver/GuestStepBound.olean")
                .exists(),
            "downstream GuestStepBound.olean with modified transitive import must not be hardlinked into worktree"
        );
        assert!(
            !wt_diff
                .join(".lake/build/.turbo_lean_verified_sources.json")
                .exists(),
            ".turbo_lean_verified_sources.json must not be hardlinked into worktree"
        );

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }
}
