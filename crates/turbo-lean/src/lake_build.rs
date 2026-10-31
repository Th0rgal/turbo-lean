//! Lake environment resolution, `/dev/shm` file-split & project-summary stat caching,
//! `.olean` freshness tracking, CAS artifact staging, and `turbo-lean build` execution.

use anyhow::{Context, Result};
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

    let has_explicit_tc = project_dir.join("lean-toolchain").is_file()
        || find_project_root(project_dir)
            .join("lean-toolchain")
            .is_file();
    let allow_tc_fallback = !has_explicit_tc
        || std::env::var("TURBO_LEAN_ALLOW_TOOLCHAIN_FALLBACK")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false);
    let tc_alt_1 = tc.trim().replace('/', "-").replace(':', "-");
    let mut candidate_tcs = vec![tc_dir_name, tc_alt_1];
    if allow_tc_fallback {
        candidate_tcs.push("leanprover--lean4---v4.35.0".to_string());
    }
    let mut matched_tc: Option<(Option<PathBuf>, PathBuf)> = None;
    for candidate_tc in &candidate_tcs {
        for elan_home in &elan_roots {
            let tc_root = elan_home.join("toolchains").join(candidate_tc);
            if tc_root.join("bin").join("lean").exists() {
                matched_tc = Some((Some(elan_home.clone()), tc_root));
                break;
            }
        }
        if matched_tc.is_some() {
            break;
        }
    }
    if matched_tc.is_none() && allow_tc_fallback {
        for elan_home in &elan_roots {
            if let Ok(entries) = fs::read_dir(elan_home.join("toolchains")) {
                let mut dirs: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
                dirs.sort();
                dirs.reverse();
                for d in dirs {
                    if d.join("bin").join("lean").exists() {
                        matched_tc = Some((Some(elan_home.clone()), d));
                        break;
                    }
                }
            }
            if matched_tc.is_some() {
                break;
            }
        }
    }

    // `lake env env` loads/compiles lakefile.lean and can write config artifacts even
    // though no build was requested. Under opt-out, discover a PATH-only installation
    // through Lean itself; never ask Lake to load the workspace, including on failure.
    if matched_tc.is_none() && worktree_auto_link_disabled(project_dir) {
        let diagnostic = "Worktree opt-out prevents loading Lake configuration with `lake env env`; \
            install the project's Lean toolchain and set PATH or ELAN_HOME so `lean --print-prefix` succeeds";
        let output = Command::new("lean")
            .arg("--print-prefix")
            .current_dir(project_dir)
            .output()
            .with_context(|| diagnostic)?;
        anyhow::ensure!(
            output.status.success(),
            "{diagnostic}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let prefix = PathBuf::from(String::from_utf8(output.stdout).with_context(|| diagnostic)?.trim());
        anyhow::ensure!(
            prefix.is_absolute()
                && prefix.join("bin/lean").is_file()
                && prefix.join("lib/lean").is_dir(),
            "{diagnostic}: invalid Lean prefix `{}`",
            prefix.display()
        );
        matched_tc = Some((None, prefix));
    }

    if let Some((elan_home, tc_root)) = matched_tc {
        let canon_proj = project_dir
            .canonicalize()
            .unwrap_or_else(|_| project_dir.to_path_buf());
        let proj_lib_lean = canon_proj.join(".lake/build/lib/lean");
        let tc_lib_lean = tc_root.join("lib/lean");
        let tc_lib = tc_root.join("lib");
        let tc_bin = tc_root.join("bin");

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
        let mut path_parts = vec![tc_bin.to_string_lossy().to_string()];
        if let Some(elan_home) = elan_home {
            path_parts.push(elan_home.join("bin").to_string_lossy().to_string());
            env_map.insert(
                "ELAN_HOME".to_string(),
                elan_home.to_string_lossy().to_string(),
            );
        }
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
        path_parts.push(std::env::var("PATH").unwrap_or_default());
        env_map.insert("PATH".to_string(), path_parts.join(":"));
        env_map.insert(
            "LEAN_STACK_SIZE_KB".to_string(),
            std::env::var("LEAN_STACK_SIZE_KB").unwrap_or_else(|_| "262144".to_string()),
        );
        return Ok(env_map);
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
    let stripped = rel_str
        .strip_prefix("lib/lean/")
        .or_else(|| rel_str.strip_prefix("ir/"))?;
    let stripped = stripped.strip_suffix(".hash").unwrap_or(stripped);
    for suffix in [
        ".olean.server",
        ".olean.private",
        ".ir.sig",
        ".olean",
        ".ilean",
        ".ir",
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
                    let imp_slash = crate::module_builder::module_name_to_rel_slash(&imp);
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
                false
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
            || name_str == ".turbo_verified_sources.json"
            || name_str == ".turbo_lean_verified_sources.json"
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
            if fs::copy(&path, &target).is_ok() {
                #[cfg(unix)]
                {
                    use std::os::unix::fs::PermissionsExt;
                    let _ = fs::set_permissions(&target, fs::Permissions::from_mode(0o644));
                }
                count += 1;
            }
        }
    }
    count
}

/// True when auto worktree `.lake` linking is opted out. Any one of `--no-auto-worktree-link`
/// (which sets `TURBO_LEAN_NO_WORKTREE_LINK`), `TURBO_LEAN_NO_WORKTREE_LINK=1`, or
/// `[worktree] auto_link = false` in `turbo-lean.toml` is enough.
pub(crate) fn worktree_auto_link_disabled(project_dir: &Path) -> bool {
    if crate::shm_cache::parse_relaxed_bool(
        &std::env::var("TURBO_LEAN_NO_WORKTREE_LINK").unwrap_or_default(),
    ) == Some(true)
    {
        return true;
    }
    crate::shm_cache::find_nearest_project_toml(Some(project_dir))
        .and_then(|p| fs::read_to_string(p).ok())
        .and_then(|t| crate::accelerators::toml_value(&t, "worktree", "auto_link"))
        .and_then(|v| crate::shm_cache::parse_relaxed_bool(&v))
        == Some(false)
}

/// Automatically detect if `project_dir` is inside a git worktree (`git worktree add`) whose `.lake/build/lib`
/// is missing, and hardlink verified `.lake/build` + `.lake/packages` from the main repository's `.lake/` in `< 5 ms`.
pub(crate) fn auto_hardlink_worktree_oleans_from_main_repo(project_dir: &Path) -> usize {
    if worktree_auto_link_disabled(project_dir) {
        return 0;
    }
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
    let mut env_map = spawn_lake_env(canon_dir)?;
    if !env_map.is_empty() {
        if let Ok(bytes) = serde_json::to_vec(&env_map) {
            let _ = crate::shm_cache::atomic_write_shm(&shm_env_path, &bytes);
        }
        merge_caller_lean_path(&mut env_map);
        return Ok(Some((env_map, true)));
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

#[cfg(test)]
pub(crate) fn compute_shard_key(toolchain: &str, shard: &splitter::TheoremShard) -> String {
    compute_shard_key_with_args(toolchain, shard, &[])
}

pub(crate) fn compute_shard_key_with_args(
    toolchain: &str,
    shard: &splitter::TheoremShard,
    lean_args: &[String],
) -> String {
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
    if let Some(ad) = crate::module_builder::effective_lean_args_digest(lean_args) {
        key_hasher.update(b":opts:");
        key_hasher.update(ad.as_bytes());
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

fn compute_single_olean_digest_and_imports(olean_path: &Path) -> Option<(String, Vec<String>)> {
    let meta = fs::metadata(olean_path).ok()?;
    if !meta.is_file() {
        return None;
    }
    let bytes = fs::read(olean_path).ok()?;
    let olean_deps = crate::module_builder::parse_olean_binary_imports(&bytes)
        .map(|(imps, _)| imps.into_iter().map(|i| i.module).collect::<Vec<String>>())
        .unwrap_or_default();
    let mut h = blake3::Hasher::new();
    h.update(b"olean-full:v3:");
    h.update(blake3::hash(&bytes).as_bytes());
    let companions = [
        (
            "srv",
            PathBuf::from(format!("{}.server", olean_path.display())),
        ),
        (
            "priv",
            PathBuf::from(format!("{}.private", olean_path.display())),
        ),
        ("ilean", olean_path.with_extension("ilean")),
        ("ir", olean_path.with_extension("ir")),
        (
            "ir_sig",
            PathBuf::from(format!("{}.sig", olean_path.with_extension("ir").display())),
        ),
    ];
    for (tag, comp_path) in companions {
        h.update(b"|");
        h.update(tag.as_bytes());
        match fs::metadata(&comp_path) {
            Ok(cm) if cm.is_file() => {
                let comp_bytes = fs::read(&comp_path).ok()?;
                h.update(&[1u8]);
                h.update(blake3::hash(&comp_bytes).as_bytes());
            }
            Ok(_) => return None,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                h.update(&[0u8]);
            }
            Err(_) => return None,
        }
    }
    Some((h.finalize().to_hex().to_string(), olean_deps))
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
    let content = fs::read_to_string(path).ok()?;
    let hdr = crate::module_builder::parse_header_info(&content);
    if hdr.header_error.is_some() {
        return None;
    }
    Some(hdr.imports)
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
        let rel_slash = crate::module_builder::module_name_to_rel_slash(&mod_name);
        let rel_olean = format!("{}.olean", rel_slash);
        let sub_lean_opt = resolve_project_lean_source(project_dir, &rel_slash);
        let src_digest_opt = sub_lean_opt
            .as_deref()
            .and_then(compute_cached_source_blake3);
        let mut olean_digest_opt = None;
        let mut olean_sub_mods = Vec::new();
        for dir in &search_dirs {
            let cand = dir.join(&rel_olean);
            if let Some((digest, sub_deps)) = compute_single_olean_digest_and_imports(&cand) {
                olean_digest_opt = Some(digest);
                olean_sub_mods = sub_deps;
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
            (None, _)
                if !search_dirs.is_empty()
                    && mod_name != "Init"
                    && !mod_name.starts_with("Init.")
                    && mod_name != "Lean"
                    && !mod_name.starts_with("Lean.") =>
            {
                out.push(format!("{}:missing", mod_name));
            }
            _ => {}
        }
        for sub_mod in olean_sub_mods {
            if !visited.contains(&sub_mod)
                && sub_mod != "Init"
                && !sub_mod.starts_with("Init.")
                && sub_mod != "Lean"
                && !sub_mod.starts_with("Lean.")
            {
                worklist.push(sub_mod);
            }
        }
        if let Some(ref sub_lean) = sub_lean_opt {
            if let Some(sub_mods) = read_header_imports_from_file(sub_lean) {
                for sub_mod in sub_mods {
                    if !visited.contains(&sub_mod) {
                        worklist.push(sub_mod);
                    }
                }
            } else {
                out.push(format!("{}:invalid_header", mod_name));
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

pub(crate) type SourceFileSplit = (PathBuf, String, splitter::SplitResult);
pub(crate) type FileSplitsWithCacheHits = (Vec<SourceFileSplit>, usize);

/// Zero-read stat-backed file split loader: checks `(path_key, mtime_sec, mtime_nsec, size_bytes)`
/// in `/dev/shm` or `file_stat_cache` joined with `file_split_cache` first, and only reads/hashes/splits files
/// that miss the stat cache. On stat cache hit, the returned `String` source is empty (`""`) and
/// can be lazily loaded if a theorem shard miss requires source reconstruction.
pub(crate) fn load_and_split_files_cached(
    store: &TurboStore,
    paths: &[PathBuf],
) -> Result<FileSplitsWithCacheHits> {
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
) -> Result<FileSplitsWithCacheHits> {
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
        .join(".turbo_verified_sources.json")
}

pub(crate) fn load_verified_project_manifest(
    canon_dir: &Path,
) -> Option<crate::module_builder::VerifiedDepManifest> {
    let manifest_path = verified_sources_manifest_path(canon_dir);
    let bytes = fs::read(&manifest_path).ok()?;
    let manifest: crate::module_builder::VerifiedDepManifest =
        serde_json::from_slice(&bytes).ok()?;
    let cfg = crate::module_builder::resolve_project_config(canon_dir).ok()?;
    if manifest.pkg_name != cfg.root_pkg.name
        || manifest.toolchain != cfg.toolchain
        || manifest.lean_githash != cfg.lean_githash
        || manifest.pkg_config_digest != cfg.root_pkg.config_digest
        || manifest.workspace_config_digest != cfg.canonical_config_digest
        || manifest.allowed_axioms != crate::splitter::allowed_axioms()
    {
        return None;
    }
    Some(manifest)
}

fn verify_project_module_entry_and_sidecars(
    canon_dir: &Path,
    rel_src: &str,
    expected_src_blake3: &str,
    manifest: &crate::module_builder::VerifiedDepManifest,
) -> bool {
    let Some(entry) = manifest.modules.get(rel_src) else {
        return false;
    };
    if !entry.kernel_audited || entry.src_blake3 != expected_src_blake3 {
        return false;
    }
    let olean_path = resolve_project_olean_for_rel_path(canon_dir, rel_src);
    if !olean_path.is_file() {
        return false;
    }
    let Ok(actual_art_dig) = crate::module_builder::compute_olean_artifact_set_digest(&olean_path)
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
    let hdr = crate::module_builder::parse_header_info(&src_raw);
    if hdr.header_error.is_some() {
        return false;
    }
    let lib_lean_dir = canon_dir.join(".lake/build/lib/lean");
    let rel_slash = olean_path
        .strip_prefix(&lib_lean_dir)
        .unwrap_or(&olean_path)
        .with_extension("")
        .to_string_lossy()
        .replace('\\', "/");
    let ir_dir = canon_dir.join(".lake/build/ir");
    crate::module_builder::verify_module_lake_sidecars(
        &olean_path,
        Some(&ir_dir),
        &rel_slash,
        &src_raw,
        hdr.is_module,
        false,
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
        let src_path = canon_dir.join(rel_path);
        let src_mtime = fs::metadata(&src_path).and_then(|m| m.modified()).ok();
        let olean_mtime = olean_meta.modified().ok();
        let is_mtime_fresh = match (src_mtime, olean_mtime) {
            (Some(sm), Some(om)) if om >= sm => lakefile_mtime.map_or(true, |lm| om >= lm),
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

    checked_oleans > 0
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
        let pkg_root = canon_project_dir
            .join(".lake")
            .join("packages")
            .join(pkg_name);
        return resolve_prebuilt_module_import(&pkg_root, canon_file);
    }
    let lib_lean_dir = canon_project_dir
        .join(".lake")
        .join("build")
        .join("lib")
        .join("lean");
    let direct_olean = lib_lean_dir.join(&rel_no_ext).with_extension("olean");
    let (_olean_path, mod_parts) = if direct_olean.is_file() {
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
    Some(crate::module_builder::format_lean_module_name_from_parts(
        mod_parts.iter().map(String::as_str),
    ))
}

fn remove_module_build_artifacts(canon_dir: &Path, rel_slash: &str) {
    let lib_lean_dir = canon_dir.join(".lake/build/lib/lean");
    let ir_dir = canon_dir.join(".lake/build/ir");
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
        let _ = fs::remove_file(p);
    }
    for suffix in [
        ".c",
        ".c.hash",
        ".setup.json",
        ".ilean",
        ".ilean.hash",
        ".trace",
    ] {
        let p = ir_dir.join(format!("{}{}", rel_slash, suffix));
        let _ = fs::remove_file(p);
    }
}

/// Inspect all transitive project-local imports of `target_files` in `canon_dir`.
/// If any imported project-local module `<M>` has a stale `.olean` on disk (older than `<M>.lean`,
/// older than one of its transitive dependencies, or mismatched against `.turbo_verified_sources.json`),
/// bring it up to date with Lake when the project has a Lake config (failing if Lake cannot),
/// or else purge the stale `.olean` artifacts, so `lean` / `ZygoteWorker` never elaborates against a stale `.olean`.
/// With the worktree opt-out, report stale modules before changing any artifacts or manifests.
pub(crate) fn ensure_project_imports_fresh_for_check(
    canon_dir: &Path,
    target_files: &[PathBuf],
) -> Result<usize> {
    let lib_lean_dir = canon_dir.join(".lake/build/lib/lean");
    if !lib_lean_dir.is_dir() {
        return Ok(0);
    }
    let manifest_path = verified_sources_manifest_path(canon_dir);
    let manifest_opt = load_verified_project_manifest(canon_dir);

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
        let imp_slash = crate::module_builder::module_name_to_rel_slash(&mod_name);
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

        let manifest_stale = match (&manifest_opt, &cur_hash) {
            (Some(m), Some(ch)) => m
                .modules
                .get(&dep_rel)
                .is_some_and(|e| !e.kernel_audited || e.src_blake3 != *ch),
            _ => false,
        };
        let mtime_stale = match (&olean_meta, &src_meta) {
            (Some(om), Some(sm)) => match (om.modified(), sm.modified()) {
                (Ok(ot), Ok(st)) => ot < st,
                _ => true,
            },
            (Some(_), None) => true,
            (None, _) => false,
        };
        let trace_corrupt = if olean_meta.as_ref().is_some_and(|m| m.is_file()) {
            let trace_path = dep_olean.with_extension("trace");
            trace_path.is_file()
                && fs::read(&trace_path)
                    .ok()
                    .and_then(|b| serde_json::from_slice::<serde_json::Value>(&b).ok())
                    .is_none()
        } else {
            false
        };
        if manifest_stale || mtime_stale || trace_corrupt {
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
                    let ch_slash = crate::module_builder::module_name_to_rel_slash(ch);
                    if let Some(ch_src) = resolve_project_lean_source(canon_dir, &ch_slash) {
                        let ch_olean = lib_lean_dir.join(format!("{}.olean", ch_slash));
                        let ch_om = fs::metadata(&ch_olean).and_then(|m| m.modified()).ok();
                        let ch_sm = fs::metadata(&ch_src).and_then(|m| m.modified()).ok();
                        if let (Some(som), Some(com)) = (self_om, ch_om) {
                            if som < com {
                                stale_mods.insert(mod_name.clone());
                                changed = true;
                                break;
                            }
                        }
                        if let (Some(som), Some(csm)) = (self_om, ch_sm) {
                            if som < csm {
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
    let mut targets: Vec<String> = stale_mods.iter().cloned().collect();
    targets.sort();
    if worktree_auto_link_disabled(canon_dir) {
        anyhow::bail!(
            "Worktree opt-out prevents refreshing stale imports: {}. Rebuild explicitly with Lake (`lake build {}`), then retry.",
            targets.join(", "),
            targets.join(" ")
        );
    }
    if has_lake_config(canon_dir) {
        // Lake owns `.lake/build` (whose files may be hard links into its artifact cache):
        // let Lake bring the stale imports up to date instead of deleting or rewriting them.
        lake_build_modules(canon_dir, &targets, None)?;
        if let Some(mut manifest) = manifest_opt {
            for (_, _, dep_src) in &ordered_imports {
                if targets.iter().any(|t| {
                    let s = crate::module_builder::module_name_to_rel_slash(t);
                    resolve_project_lean_source(canon_dir, &s).as_ref() == Some(dep_src)
                }) {
                    let dep_rel = dep_src
                        .strip_prefix(canon_dir)
                        .unwrap_or(dep_src)
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
        }
        return Ok(targets.len());
    }

    if let Some(mut manifest) = manifest_opt {
        for (mod_name, _, dep_src) in &ordered_imports {
            if stale_mods.contains(mod_name) {
                let dep_rel = dep_src
                    .strip_prefix(canon_dir)
                    .unwrap_or(dep_src)
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
    for (mod_name, imp_slash, _) in &ordered_imports {
        if stale_mods.contains(mod_name) {
            remove_module_build_artifacts(canon_dir, imp_slash);
        }
    }
    for t_slash in &target_rel_slashes {
        remove_module_build_artifacts(canon_dir, t_slash);
    }

    Ok(stale_mods.len())
}

/// Build `modules` with `lake build`, or with the command in `[lake] build_command` of the
/// project's `turbo-lean.toml` (read at git revision `rev` when given), e.g. a memory-aware
/// scheduler. Lake restores what it can from its artifact cache. Fails closed.
pub(crate) fn lake_build_modules(
    canon_dir: &Path,
    modules: &[String],
    rev: Option<&str>,
) -> Result<()> {
    if worktree_auto_link_disabled(canon_dir) {
        anyhow::bail!(
            "Worktree opt-out prevents automatic Lake rebuild of modules: {}. Rebuild explicitly with Lake (`lake build {}`), then retry.",
            modules.join(", "),
            modules.join(" ")
        );
    }
    let configured = crate::splitter::read_project_config(canon_dir, rev)
        .and_then(|t| crate::accelerators::toml_string_array(&t, "lake", "build_command"))
        .filter(|c| !c.is_empty())
        .unwrap_or_else(|| vec!["lake".to_string(), "build".to_string()]);
    let out = Command::new(&configured[0])
        .args(&configured[1..])
        .args(modules)
        .current_dir(canon_dir)
        .output()
        .map_err(|e| anyhow::anyhow!("failed to run `{}`: {}", configured.join(" "), e))?;
    if !out.status.success() {
        let log = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let tail: Vec<&str> = log.lines().rev().take(40).collect();
        anyhow::bail!(
            "`{} <{} modules>` failed:\n{}",
            configured.join(" "),
            modules.len(),
            tail.into_iter().rev().collect::<Vec<_>>().join("\n")
        );
    }
    Ok(())
}

pub(crate) fn has_lake_config(canon_dir: &Path) -> bool {
    canon_dir.join("lakefile.lean").is_file() || canon_dir.join("lakefile.toml").is_file()
}

/// The files of `files` whose edit against git revision `rev` is not local, i.e. changes more than
/// theorem proof bodies (proof irrelevance makes those invisible to other declarations). Files
/// new since `rev` are not local. Outside a git repository nothing is reported.
pub(crate) fn nonlocal_edits(files: &[PathBuf], rev: &str) -> Vec<String> {
    let is_nonlocal = |f: &PathBuf| {
        let Ok(cur) = fs::read_to_string(f) else {
            return false;
        };
        let name = f.file_name().unwrap_or_default().to_string_lossy();
        let base = Command::new("git")
            .arg("-C")
            .arg(f.parent().unwrap_or(Path::new(".")))
            .args(["show", &format!("{}:./{}", rev, name)])
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).into_owned());
        let Some(base) = base else {
            // New since `rev` (inside a repository); outside git there is no edit to classify.
            return Command::new("git")
                .arg("-C")
                .arg(f.parent().unwrap_or(Path::new(".")))
                .args(["rev-parse", "--is-inside-work-tree"])
                .output()
                .is_ok_and(|o| o.status.success());
        };
        if base == cur {
            return false;
        }
        let (c, b) = (
            splitter::split_lean_source(&cur, &[]),
            splitter::split_lean_source(&base, &[]),
        );
        c.interface_hash != b.interface_hash || c.shards.len() != b.shards.len()
    };
    files
        .iter()
        .filter(|f| is_nonlocal(f))
        .map(|f| f.display().to_string())
        .collect()
}

pub(crate) fn dependent_closure_modules(
    canon_dir: &Path,
    edits: &[String],
    is_untrusted: bool,
) -> Result<(Vec<String>, Option<Vec<String>>)> {
    let cfg = crate::module_builder::resolve_project_config_with_trust(canon_dir, is_untrusted)?;
    let mut seeds: Vec<String> = cfg.root_pkg.libs.iter().map(|l| l.name.clone()).collect();
    for exe in &cfg.root_pkg.exes {
        let root_mod = exe.root.trim();
        let target = if !root_mod.is_empty() {
            root_mod.to_string()
        } else {
            exe.name.clone()
        };
        if !seeds.contains(&target) {
            seeds.push(target);
        }
    }
    let closure = crate::module_builder::build_module_dag_with_trust(&cfg, &seeds, is_untrusted)
        .ok()
        .map(|dag| {
            let edited: HashSet<PathBuf> = edits
                .iter()
                .map(|e| canon_dir.join(e))
                .map(|p| p.canonicalize().unwrap_or(p))
                .collect();
            let mut closure: std::collections::BTreeSet<String> = dag
                .nodes
                .iter()
                .filter(|(_, n)| {
                    edited.contains(&n.src_path.canonicalize().unwrap_or(n.src_path.clone()))
                })
                .map(|(m, _)| m.clone())
                .collect();
            let deleted: Vec<String> = edited
                .iter()
                .filter(|e| !e.exists())
                .filter_map(|e| e.strip_prefix(canon_dir).ok())
                .map(|r| r.with_extension("").to_string_lossy().replace('/', "."))
                .collect();
            let mut changed = true;
            while changed {
                changed = false;
                for (m, n) in &dag.nodes {
                    if !closure.contains(m)
                        && n.direct_dag_deps.iter().any(|d| {
                            closure.contains(d)
                                || deleted
                                    .iter()
                                    .any(|x| d == x || x.ends_with(&format!(".{}", d)))
                        })
                    {
                        closure.insert(m.clone());
                        changed = true;
                    }
                }
            }
            closure.into_iter().collect::<Vec<_>>()
        });
    Ok((seeds, closure))
}

/// After a non-local edit, re-check with Lake the edited modules and every project module that
/// imports them, directly or not (Lake replays unchanged imports from its build or artifact
/// cache). Without a module graph it re-checks every `lean_lib`; without a Lake config it
/// refuses to pass. Returns the number of modules re-checked (0: all libraries).
pub(crate) fn recheck_dependents_if_nonlocal(canon_dir: &Path, target: &Path) -> Result<()> {
    let lake_root = target.canonicalize().ok().and_then(|f| {
        f.ancestors()
            .find(|a| has_lake_config(a))
            .map(PathBuf::from)
    });
    let dir = if has_lake_config(canon_dir) {
        canon_dir.to_path_buf()
    } else {
        lake_root.unwrap_or_else(|| canon_dir.to_path_buf())
    };
    let dir = dir.canonicalize().unwrap_or(dir);
    let file = Some(dir.join(target))
        .filter(|f| f.exists())
        .unwrap_or_else(|| target.to_path_buf());
    let files = collect_project_lean_files(&dir, false, Some(&file));
    let edits = nonlocal_edits(&files, "HEAD");
    if !edits.is_empty() {
        eprintln!(
            "[turbo-lean] non-local edit in {}: re-checking dependents with Lake",
            edits.join(", ")
        );
        let n = lake_recheck_dependents(&dir, &edits, None)?;
        eprintln!(
            "[turbo-lean] Lake re-checked {} modules (0: all libraries)",
            n
        );
    }
    Ok(())
}

pub(crate) fn lake_recheck_dependents(
    canon_dir: &Path,
    edits: &[String],
    rev: Option<&str>,
) -> Result<usize> {
    if !has_lake_config(canon_dir) {
        anyhow::bail!(
            "non-local edit in {} needs its dependents re-checked, but {} has no Lake config: refusing to pass",
            edits.join(", "),
            canon_dir.display()
        );
    }
    let (libs, closure) = dependent_closure_modules(canon_dir, edits, false)?;
    match closure {
        Some(mods) if !mods.is_empty() => {
            lake_build_modules(canon_dir, &mods, rev)?;
            Ok(mods.len())
        }
        _ => lake_build_modules(canon_dir, &libs, rev).map(|_| 0),
    }
}

pub(crate) fn untrusted_recheck_dependents(
    store: &mut TurboStore,
    canon_dir: &Path,
    edits: &[String],
    trust_domain: &str,
    json: bool,
) -> Result<usize> {
    if !has_lake_config(canon_dir) {
        anyhow::bail!(
            "non-local edit in {} needs its dependents re-checked, but {} has no Lake config: refusing to pass",
            edits.join(", "),
            canon_dir.display()
        );
    }
    let (libs, closure) = dependent_closure_modules(canon_dir, edits, true)?;
    let (targets, count) = match closure {
        Some(mods) if !mods.is_empty() => {
            let n = mods.len();
            (mods, n)
        }
        _ => (libs, 0),
    };
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
    Ok(count)
}

/// Project modules imported by `files` (Lake brings them up to date before per-theorem checks).
pub(crate) fn project_imports_of(canon_dir: &Path, files: &[PathBuf]) -> Vec<String> {
    let mut mods: Vec<String> = files
        .iter()
        .flat_map(|f| read_header_imports_from_file(f).unwrap_or_default())
        .filter(|m| resolve_project_lean_source(canon_dir, &m.replace('.', "/")).is_some())
        .collect();
    mods.sort();
    mods.dedup();
    mods
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

    let pkg_cfg_opt = crate::module_builder::optional_package_config(canon_dir)?;
    for (lf, _src, split) in split_entries {
        if require_olean && resolve_prebuilt_module_import(canon_dir, lf).is_none() {
            continue;
        }
        if split.shards.is_empty() {
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
    let preserve_lake = worktree_auto_link_disabled(project_dir);
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
        let kind = if file_name == ".turbo_verified_sources.json" {
            "manifest"
        } else if file_name.ends_with(".olean.server") {
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
                "hash" => "hash",
                "trace" => "trace",
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

    let mut entries: Vec<BlobEntry> = fs::read(&ingest_cache_path)
        .ok()
        .and_then(|b| serde_json::from_slice::<Vec<BlobEntry>>(&b).ok())
        .filter(|v| v.len() == candidates.len())
        .unwrap_or_default();

    let entries = if entries.len() == candidates.len() {
        // Revalidate mutable sidecars (`trace`, `hash`, `c`, `manifest`) directly from bytes rather than trusting stat metadata.
        for (entry, (path, kind, _, _, _, _, _, _)) in entries.iter_mut().zip(candidates.iter()) {
            if matches!(*kind, "trace" | "hash" | "c" | "manifest") {
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

    for (entry, (path, _, _, _, _, _, mode, _cand_ino)) in entries.iter().zip(candidates.iter()) {
        // Never hardlink `.lake/build` artifacts into CAS or mark them read-only (`0o444`):
        // in-place `lake build` / `lean -o` writes must never mutate CAS blobs (`nlink == 1`, `0o644`).
        #[cfg(unix)]
        {
            let nlink = fs::metadata(path)?.nlink();
            if !preserve_lake && ((*mode & 0o200) == 0 || nlink > 1) {
                let bytes = fs::read(path)?;
                let tmp_detach = path.with_extension(format!(
                    "detach_tmp.{}.{}",
                    std::process::id(),
                    pack::next_tmp_id()
                ));
                fs::write(&tmp_detach, &bytes)?;
                fs::set_permissions(&tmp_detach, fs::Permissions::from_mode(0o644))?;
                fs::rename(&tmp_detach, path)?;
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
        let ino = if fs::hard_link(&shared_p, &dest).is_ok()
            || (has_distinct_fallback && fs::hard_link(&fallback_p, &dest).is_ok())
        {
            sync_shared(&dest);
            dest_ino(&dest)
        } else if dest.exists() {
            dest_ino(&dest)
        } else {
            let staging_dir = store.root.join("staging");
            fs::create_dir_all(&staging_dir)?;
            let tmp_dest = staging_dir.join(format!(
                "{}.{}.{}.tmp",
                entry.blob_hash,
                std::process::id(),
                pack::next_tmp_id()
            ));
            let bytes = fs::read(path)?;
            if blake3::hash(&bytes).to_hex().as_str() != entry.blob_hash {
                anyhow::bail!(
                    "Concurrent mutation detected while staging `{}` into CAS",
                    path.display()
                );
            }
            fs::write(&tmp_dest, &bytes)?;
            #[cfg(unix)]
            fs::set_permissions(&tmp_dest, fs::Permissions::from_mode(0o444))?;
            fs::rename(&tmp_dest, &dest)?;
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

    let emit_build_telemetry = |ev: serde_json::Value| {
        crate::mcp::emit_cli_telemetry_event(
            Some(&canon_dir),
            trust_domain == "trusted",
            ev,
            "turbo_lean_events.jsonl",
        );
    };
    match store.acquire_singleflight(&action_key, &toolchain, "module_full", &trust_domain)? {
        SingleflightOutcome::CacheHit { outputs, coalesced } => {
            let linked = store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
            let seeded_shards = if seed_shards {
                seed_project_theorem_shards(store, &canon_dir, &toolchain, &trust_domain, false)?.1
            } else {
                0
            };
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
            if !crate::zygote::daemon_disabled() {
                if let Some((ref env_vars, _)) = resolved_env {
                    pack::warm_local_zygote_daemon_nonblocking(store, env_vars);
                }
            }
            let seeded_shards = if seed_shards {
                seed_project_theorem_shards(store, &canon_dir, &toolchain, &trust_domain, false)?.1
            } else {
                0
            };
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

    #[cfg(unix)]
    #[test]
    fn test_optout_path_toolchain_env_child() -> Result<()> {
        use crate::worktree_test_support::snapshot;
        let Some(root) = std::env::var_os("TURBO_TEST_ENV_ROOT").map(PathBuf::from) else {
            return Ok(());
        };
        let project = root.join("project");
        let before = snapshot(&project)?;
        let store = TurboStore::open(Some(&root.join("env-cache")))?;
        if std::env::var_os("TURBO_TEST_MISSING_LEAN").is_some() {
            for err in [
                resolve_lake_env(&store, &project).unwrap_err(),
                resolve_or_share_lake_env(&store, &project, "uncached-share").unwrap_err(),
            ] {
                assert!(
                    err.to_string()
                        .contains("Worktree opt-out prevents loading Lake configuration"),
                    "{err:#}"
                );
                assert!(err.to_string().contains("PATH or ELAN_HOME"), "{err:#}");
            }
        } else {
            let (env, cached) = resolve_lake_env(&store, &project)?;
            assert!(!cached, "fixture must miss both environment caches");
            let shared = resolve_or_share_lake_env(&store, &project, "uncached-share")?
                .unwrap()
                .0;
            let prefix = fs::read_to_string(root.join("prefix"))?;
            for env in [&env, &shared] {
                assert_eq!(env["LAKE"], format!("{}/bin/lake", prefix.trim()));
                let lean_paths: Vec<_> = std::env::split_paths(&env["LEAN_PATH"]).collect();
                assert!(lean_paths.contains(&project.join(".lake/build/lib/lean")));
                assert!(lean_paths.contains(&PathBuf::from(prefix.trim()).join("lib/lean")));
            }
            assert!(resolve_lake_env(&store, &project)?.1);
        }
        assert!(
            !root.join("lake-invoked").exists(),
            "environment resolution invoked Lake"
        );
        assert_eq!(
            before,
            snapshot(&project)?,
            "environment resolution changed .lake"
        );
        fs::write(root.join("done"), b"")?;
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_optout_path_toolchain_preserves_missing_and_stale_lean_config() -> Result<()> {
        use crate::worktree_test_support::{snapshot, LakeTree, TestChild};
        use std::os::unix::fs::PermissionsExt;
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for state in ["missing", "stale", "missing-compiler"] {
            let tree = LakeTree::new("path_toolchain", &[("P/A.lean", "def value : Nat := 1\n")])?;
            fs::remove_file(tree.project.join("lakefile.toml"))?;
            let config = tree.project.join("lakefile.lean");
            fs::write(&config, "import Lake\nopen Lake DSL\npackage fixture where\nlean_lib P where\n  globs := #[.submodules `P]\n")?;
            tree.lake(&["build", "P"])?;
            let env = spawn_lake_env(&tree.project)?;
            let lean = PathBuf::from(lean_bin_from_env(&env));
            let prefix = Command::new(&lean).arg("--print-prefix").output()?;
            anyhow::ensure!(prefix.status.success(), "fixture Lean prefix query failed");
            fs::write(tree.root.join("prefix"), prefix.stdout)?;
            let bin = tree.root.join("path/bin");
            fs::create_dir_all(&bin)?;
            if state != "missing-compiler" {
                std::os::unix::fs::symlink(&lean, bin.join("lean"))?;
            }
            // Instrument the real Lake executable: a regression must also fail if loading
            // a config happens to preserve identical artifact bytes.
            let lake = bin.join("lake");
            let quote =
                |p: &Path| format!("'{}'", p.display().to_string().replace('\'', "'\"'\"'"));
            fs::write(
                &lake,
                format!(
                    "#!/bin/sh\nprintf invoked > {}\nexec {} \"$@\"\n",
                    quote(&tree.root.join("lake-invoked")),
                    quote(Path::new(&env["LAKE"]))
                ),
            )?;
            fs::set_permissions(&lake, fs::Permissions::from_mode(0o755))?;
            if state == "stale" {
                fs::write(
                    &config,
                    format!(
                        "{}\n-- stale compiled Lake config\n",
                        fs::read_to_string(&config)?
                    ),
                )?;
                fs::File::options()
                    .write(true)
                    .open(&config)?
                    .set_modified(
                        std::time::SystemTime::now() + std::time::Duration::from_secs(2),
                    )?;
            } else {
                let compiled = WalkDir::new(tree.project.join(".lake"))
                    .into_iter()
                    .collect::<std::result::Result<Vec<_>, _>>()?
                    .into_iter()
                    .find(|e| e.file_name() == "lakefile.olean")
                    .expect("real compiled Lean Lake config");
                fs::remove_file(compiled.path())?;
            }
            tree.opt_out()?;
            tree.prepare_snapshot(".lake/build/lib/lean/P/A.olean")?;
            let before = snapshot(&tree.project)?;
            let mut command =
                TestChild::command("lake_build::tests::test_optout_path_toolchain_env_child")?;
            command
                .env("TURBO_TEST_ENV_ROOT", &tree.root)
                .env("PATH", &bin)
                .env("HOME", tree.root.join("isolated/a/b/home"))
                .env("ELAN_HOME", tree.root.join("empty-elan"))
                .env("TURBO_LEAN_HOME", tree.root.join("cache"))
                .env("TURBO_LEAN_STAGING_DIR", tree.root.join("staging"))
                .env("TURBO_LEAN_ALLOW_TOOLCHAIN_FALLBACK", "0")
                .env_remove("LEAN_PATH");
            if state == "missing-compiler" {
                command.env("TURBO_TEST_MISSING_LEAN", "1");
            }
            let mut child = TestChild::spawn(&mut command)?;
            child.finish(&tree.root.join("done"))?;
            assert_eq!(
                before,
                snapshot(&tree.project)?,
                "{state} config changed .lake"
            );
        }
        Ok(())
    }

    #[test]
    fn seeding_rejects_invalid_config_before_publishing() -> Result<()> {
        let dir =
            std::env::temp_dir().join(format!("turbo_seed_options_{}", crate::pack::next_tmp_id()));
        let project = dir.join("project");
        fs::create_dir_all(&project)?;
        let file = project.join("Demo.lean");
        let source = "theorem seed_options : True := by trivial\n";
        fs::write(&file, source)?;
        let split = split_lean_source(source, &[]);
        assert_eq!(split.shards.len(), 1);
        let key = compute_shard_key("test", &split.shards[0]);
        let splits = vec![(file, source.to_string(), split)];
        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        for config in [
            "name = [",
            "name = \"bad\"\nmoreLeanArgs = [\"--plugin=bad.so\"]\n",
        ] {
            fs::write(project.join("lakefile.toml"), config)?;
            let err = seed_project_theorem_shards_from_splits(
                &mut store, &project, "test", "trusted", false, &splits,
            )
            .unwrap_err();
            assert!(format!("{err:#}").contains("Failed to resolve Lean options"));
            assert!(store
                .batch_get_theorem_shards_readonly(std::slice::from_ref(&key), "trusted")?
                .is_empty());
            let count: i64 = store
                .conn
                .query_row("SELECT COUNT(*) FROM actions", [], |r| r.get(0))?;
            assert_eq!(count, 0, "invalid configuration must publish no entries");
        }
        // Standalone projects with no Lake config still have known empty options.
        fs::remove_file(project.join("lakefile.toml"))?;
        assert_eq!(
            seed_project_theorem_shards_from_splits(
                &mut store, &project, "test", "trusted", false, &splits,
            )?,
            (1, 1)
        );
        assert!(store.has_cached_action_readonly(&key, "trusted")?);
        fs::remove_dir_all(dir)?;
        Ok(())
    }

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
    fn test_check_freshens_stale_lake_imports_with_lake_without_deleting() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir =
            std::env::temp_dir().join(format!("turbo_lean_lake_fresh_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(dir.join("P"))?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"p\"\n[[lean_lib]]\nname = \"P\"\n",
        )?;
        fs::write(dir.join("P/A.lean"), "def a : Nat := 1\n")?;
        fs::write(
            dir.join("P/B.lean"),
            "import P.A\ntheorem b : a = 1 := rfl\n",
        )?;
        let lake = |args: &[&str]| Command::new("lake").args(args).current_dir(&dir).output();
        assert!(
            lake(&["build", "P.B"])?.status.success(),
            "Lake fixture must build"
        );
        assert!(!worktree_auto_link_disabled(&dir));
        let old_olean = fs::read(dir.join(".lake/build/lib/lean/P/A.olean"))?;
        std::thread::sleep(std::time::Duration::from_millis(1100));
        fs::write(
            dir.join("P/A.lean"),
            "def a : Nat := 1\ndef a2 : Nat := 2\n",
        )?;
        let olean = |m: &str| dir.join(format!(".lake/build/lib/lean/P/{}.olean", m));
        assert_eq!(
            ensure_project_imports_fresh_for_check(&dir, &[dir.join("P/B.lean")])?,
            1
        );
        assert_ne!(
            fs::read(olean("A"))?,
            old_olean,
            "default must actually rebuild the import"
        );
        // Lake rebuilt the stale import in place of deleting it; nothing else was removed.
        assert!(olean("A").is_file() && olean("B").is_file());
        assert!(lake(&["build", "--no-build", "P.A"])?.status.success());
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_optout_stale_import_check_preserves_lake_tree_with_and_without_config() -> Result<()> {
        use crate::worktree_test_support::{assert_stale_error, snapshot, LakeTree};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for lake_config in [true, false] {
            let tree = LakeTree::imports("stale_check")?;
            tree.opt_out()?;
            tree.stale_import()?;
            // A valid manifest exercises the rewrite branch, as well as stale artifact removal.
            let cfg = crate::module_builder::resolve_project_config(&tree.project)?;
            let manifest = crate::module_builder::VerifiedDepManifest {
                pkg_name: cfg.root_pkg.name.clone(),
                toolchain: cfg.toolchain.clone(),
                lean_githash: cfg.lean_githash.clone(),
                pkg_config_digest: cfg.root_pkg.config_digest.clone(),
                workspace_config_digest: cfg.canonical_config_digest.clone(),
                allowed_axioms: crate::splitter::allowed_axioms(),
                modules: std::collections::BTreeMap::from([(
                    "P/A.lean".into(),
                    crate::module_builder::VerifiedDepModuleEntry {
                        src_blake3: "previous source".into(),
                        olean_artifact_digest: "previous artifact".into(),
                        kernel_audited: true,
                    },
                )]),
            };
            fs::write(
                verified_sources_manifest_path(&tree.project),
                serde_json::to_vec(&manifest)?,
            )?;
            assert!(load_verified_project_manifest(&tree.project).is_some());
            if !lake_config {
                fs::remove_file(tree.project.join("lakefile.toml"))?;
            }
            tree.prepare_snapshot(".lake/build/lib/lean/P/A.olean")?;
            let before = snapshot(&tree.project)?;
            let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
            // Cover both the single-file and directory check callers.
            for target in [tree.project.join("P/Target.lean"), tree.project.join("P")] {
                let err = crate::check::run_check_command(
                    &mut store,
                    false,
                    true,
                    target,
                    None,
                    tree.project.clone(),
                    None,
                    false,
                    None,
                )
                .unwrap_err();
                assert_stale_error(&err);
                assert_eq!(
                    snapshot(&tree.project)?,
                    before,
                    "check mutated Lake tree (config={lake_config})"
                );
            }
        }
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_optout_preserves_preexisting_lake_inodes_modes_and_links() -> Result<()> {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let root = std::env::temp_dir().join(format!(
            "turbo_lake_preserve_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let project = root.join("project");
        let mut store = TurboStore::open(Some(&root.join("cache")))?;
        for (rel, mode) in [
            ("build/lib/lean/Readonly.olean", 0o444),
            ("build/lib/lean/Linked.ilean", 0o640),
            ("packages/pkg/A.olean", 0o644),
            ("packages/pkg/B.olean", 0o600),
            ("packages/pkg/.git/objects/pack/keep.pack", 0o640),
            ("cache/keep.barrel", 0o640),
        ] {
            let path = project.join(".lake").join(rel);
            fs::create_dir_all(path.parent().unwrap())?;
            fs::write(&path, b"preexisting artifact")?;
            fs::set_permissions(&path, fs::Permissions::from_mode(mode))?;
        }
        fs::hard_link(
            project.join(".lake/build/lib/lean/Linked.ilean"),
            root.join("external-link"),
        )?;
        let snapshot = || -> Result<Vec<_>> {
            let mut rows = Vec::new();
            for e in WalkDir::new(project.join(".lake")) {
                let e = e?;
                let m = e.metadata()?;
                rows.push((
                    e.path().to_path_buf(),
                    m.ino(),
                    m.mode(),
                    m.nlink(),
                    if m.is_file() {
                        fs::read(e.path())?
                    } else {
                        Vec::new()
                    },
                ));
            }
            rows.sort_by(|a, b| a.0.cmp(&b.0));
            Ok(rows)
        };
        let before = snapshot()?;
        let saved = std::env::var_os("TURBO_LEAN_NO_WORKTREE_LINK");
        for source in ["toml", "env", "cli"] {
            std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
            fs::write(
                project.join("turbo-lean.toml"),
                if source == "toml" {
                    "[worktree]\nauto_link = false\n"
                } else {
                    "[worktree]\nauto_link = true\n"
                },
            )?;
            if source == "env" {
                std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", "1");
            }
            if source == "cli" {
                use clap::Parser;
                let cli =
                    crate::Cli::try_parse_from(["turbo-lean", "--no-auto-worktree-link", "build"])?;
                crate::apply_global_cli_env(&cli);
            }
            assert_eq!(auto_hardlink_worktree_oleans_from_main_repo(&project), 0);
            // Same staging function used by build and pr-verify. It still ingests CAS bytes.
            let (outputs, blobs) = stage_lake_build_outputs(&store, &project)?;
            assert_eq!(outputs.len(), 2);
            assert_eq!(blobs.len(), 1);
            // Shared CAS restore used by build, ci-verify and module builds.
            let mut restore_outputs = outputs.clone();
            restore_outputs.push(BlobEntry {
                rel_path: ".lake/packages/pkg/A.olean".to_string(),
                ..outputs[0].clone()
            });
            assert_eq!(
                store.materialize_into_worktree(&project, "project", &restore_outputs)?,
                0
            );
            for rel_path in [
                ".lake/build/lib/lean/Missing.olean",
                ".lake/build/lib/lean/Readonly.olean",
            ] {
                let mut invalid = outputs.clone();
                invalid[0].rel_path = rel_path.to_string();
                invalid[0].blob_hash = blake3::hash(b"different artifact").to_hex().to_string();
                assert!(store
                    .materialize_into_worktree(&project, "project", &invalid)
                    .is_err());
            }
            assert_eq!(
                dedup_worktree_packages(&store, &project)?["status"],
                "worktree_link_disabled"
            );
            assert_eq!(
                snapshot()?,
                before,
                "{source} opt-out changed the existing .lake tree"
            );
        }
        match &saved {
            Some(v) => std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", v),
            None => std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK"),
        }
        // CAS ingest must still detach read-only/shared build artifacts when enabled.
        fs::write(
            project.join("turbo-lean.toml"),
            "[worktree]\nauto_link = true\n",
        )?;
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
        stage_lake_build_outputs(&store, &project)?;
        for rel in ["Readonly.olean", "Linked.ilean"] {
            let m = fs::metadata(project.join(".lake/build/lib/lean").join(rel))?;
            assert_eq!(m.nlink(), 1);
            assert_eq!(m.mode() & 0o777, 0o644);
        }
        match &saved {
            Some(v) => std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", v),
            None => std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK"),
        }
        drop(store);
        fs::remove_dir_all(root)?;
        Ok(())
    }

    #[test]
    fn test_dedup_worktree_packages_hardlinks_and_purges_barrels() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let saved_wt_env = std::env::var("TURBO_LEAN_NO_WORKTREE_LINK").ok();
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
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
        let wt_main_olean = wt_auto.join(".lake/build/lib/lean/MainMod.olean");
        assert_ne!(
            fs::metadata(&main_olean)?.ino(),
            fs::metadata(&wt_main_olean)?.ino(),
            "worktree `.lake/build` artifacts must be copied with distinct inode (`nlink == 1`), never hardlinked"
        );
        assert_eq!(fs::metadata(&wt_main_olean)?.nlink(), 1);
        assert_eq!(fs::read(&wt_main_olean)?, fs::read(&main_olean)?);

        // Now verify that when a module or its transitive import differs in the worktree,
        // `auto_hardlink_worktree_oleans_from_main_repo` skips copying that module's `.olean`
        // and never copies `.turbo_verified_sources.json` or `.turbo_lean_verified_sources.json`.
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
        fs::write(
            main_repo.join(".lake/build/.turbo_verified_sources.json"),
            b"{\"modules\":{}}",
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
        let main_pkg = main_repo.join(".lake/packages/mathlib/Basic.olean");
        fs::create_dir_all(main_pkg.parent().unwrap())?;
        fs::write(&main_pkg, b"pkg-olean")?;
        #[cfg(unix)]
        let (main_pkg_mode, main_olean_mode) = {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&main_pkg, fs::Permissions::from_mode(0o640))?;
            fs::set_permissions(&main_olean, fs::Permissions::from_mode(0o640))?;
            (0o640u32, 0o640u32)
        };
        let mut main_lake_bytes: Vec<(PathBuf, Vec<u8>)> = Vec::new();
        for entry in WalkDir::new(main_repo.join(".lake")) {
            let entry = entry?;
            if entry.file_type().is_file() {
                main_lake_bytes.push((entry.path().to_path_buf(), fs::read(entry.path())?));
            }
        }
        let wt_opt = tmp_dir.join("wt_optout");
        fs::create_dir_all(&wt_opt)?;
        fs::write(
            wt_opt.join(".git"),
            format!("gitdir: {}\n", main_git.display()),
        )?;
        fs::write(
            wt_opt.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
        assert_eq!(auto_hardlink_worktree_oleans_from_main_repo(&wt_opt), 0);
        assert!(
            !wt_opt.join(".lake").exists(),
            "toml opt-out must not create or copy `.lake`"
        );
        let wt_env = tmp_dir.join("wt_env");
        fs::create_dir_all(&wt_env)?;
        fs::write(
            wt_env.join(".git"),
            format!("gitdir: {}\n", main_git.display()),
        )?;
        std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", "1");
        let _ = resolve_lake_env(&store, &wt_env)?;
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
        assert!(
            !wt_env.join(".lake").exists(),
            "env opt-out must not create or copy `.lake` during resolve_lake_env"
        );
        let wt_cli = tmp_dir.join("wt_cli");
        fs::create_dir_all(&wt_cli)?;
        fs::write(
            wt_cli.join(".git"),
            format!("gitdir: {}\n", main_git.display()),
        )?;
        let wt_local = wt_cli.join(".lake/local_state");
        fs::create_dir_all(wt_local.parent().unwrap())?;
        fs::write(&wt_local, b"preexisting")?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&wt_local, fs::Permissions::from_mode(0o600))?;
        }
        use clap::Parser;
        let cli = crate::Cli::try_parse_from([
            "turbo-lean",
            "check",
            "--no-auto-worktree-link",
            "MainMod.lean",
        ])
        .expect("global --no-auto-worktree-link parses after the subcommand");
        crate::apply_global_cli_env(&cli);
        let _ = resolve_lake_env(&store, &wt_cli)?;
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
        assert!(
            !wt_cli.join(".lake/build").exists() && !wt_cli.join(".lake/packages").exists(),
            "CLI opt-out must not link or copy `.lake` from the main clone"
        );
        assert_eq!(fs::read(&wt_local)?, b"preexisting");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(fs::metadata(&wt_local)?.permissions().mode() & 0o777, 0o600);
        }
        for (path, bytes) in &main_lake_bytes {
            assert_eq!(&fs::read(path)?, bytes, "opt-out must not copy or rewrite main `.lake`");
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(
                fs::metadata(&main_pkg)?.permissions().mode() & 0o777,
                main_pkg_mode
            );
            assert_eq!(
                fs::metadata(&main_olean)?.permissions().mode() & 0o777,
                main_olean_mode
            );
        }
        assert!(
            !wt_diff
                .join(".lake/build/lib/lean/Guest/Ast.olean")
                .exists(),
            "modified Guest/Ast.olean must not be copied into worktree"
        );
        assert!(
            !wt_diff
                .join(".lake/build/lib/lean/InitECandidate/Solver/GuestStepBound.olean")
                .exists(),
            "downstream GuestStepBound.olean with modified transitive import must not be copied into worktree"
        );
        assert!(
            !wt_diff
                .join(".lake/build/.turbo_lean_verified_sources.json")
                .exists(),
            ".turbo_lean_verified_sources.json must not be copied into worktree"
        );
        assert!(
            !wt_diff
                .join(".lake/build/.turbo_verified_sources.json")
                .exists(),
            ".turbo_verified_sources.json must not be copied into worktree"
        );

        match saved_wt_env {
            Some(v) => std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", v),
            None => std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK"),
        }
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }
}
