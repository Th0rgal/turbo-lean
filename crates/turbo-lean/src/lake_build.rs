//! Lake environment resolution, `/dev/shm` file-split & project-summary stat caching,
//! `.olean` freshness tracking, CAS artifact staging, and `turbo-lean build` execution.

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
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
            || dir.join("lake-manifest.json").exists()
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
    let tools = crate::module_builder::ToolchainExecutables::resolve(project_dir, &tc)?;
    let tc_root = tools
        .lean
        .parent()
        .and_then(Path::parent)
        .context("Missing toolchain prefix")?;
    let canon_proj = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let tc_lib_lean = tc_root.join("lib/lean");
    let tc_lib = tc_root.join("lib");

    let mut lean_path_parts = Vec::new();
    for dir in collect_project_lean_lib_dirs(&canon_proj) {
        let s = dir.to_string_lossy().to_string();
        if !lean_path_parts.contains(&s) {
            lean_path_parts.push(s);
        }
    }
    let mut ld_parts = vec![canon_proj
        .join(".lake/build/lib")
        .to_string_lossy()
        .to_string()];
    let pkgs_dir = canon_proj.join(".lake").join("packages");
    if let Ok(entries) = fs::read_dir(&pkgs_dir) {
        let mut pkg_dirs: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
        pkg_dirs.sort();
        for pkg_dir in pkg_dirs {
            let pkg_lib = pkg_dir.join(".lake/build/lib");
            if pkg_lib.is_dir() {
                ld_parts.push(pkg_lib.to_string_lossy().to_string());
            }
        }
    }
    if let Ok((_, manifest_pkgs, _)) =
        crate::module_builder::parse_lake_manifest(&canon_proj, false)
    {
        for mp in manifest_pkgs {
            let pkg_lib = mp
                .dir
                .canonicalize()
                .unwrap_or(mp.dir)
                .join(".lake/build/lib");
            if pkg_lib.is_dir() {
                let s = pkg_lib.to_string_lossy().to_string();
                if !ld_parts.contains(&s) {
                    ld_parts.push(s);
                }
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
    env_map.insert("LEAN_PATH".to_string(), lean_path_parts.join(":"));
    env_map.insert(
        "LEAN_SRC_PATH".to_string(),
        format!("{}:{}/src/lean", canon_proj.display(), tc_root.display()),
    );
    env_map.insert("LD_LIBRARY_PATH".to_string(), ld_parts.join(":"));
    tools.apply_env(&mut env_map);
    env_map.insert(
        "LEAN_STACK_SIZE_KB".to_string(),
        std::env::var("LEAN_STACK_SIZE_KB").unwrap_or_else(|_| "262144".to_string()),
    );
    Ok(env_map)
}

pub(crate) fn merge_caller_lean_path(env_map: &mut HashMap<String, String>) {
    if let Ok(caller_lp) = std::env::var("LEAN_PATH") {
        let trimmed = caller_lp.trim();
        if !trimmed.is_empty() {
            let tc_lib = env_map
                .get("LEAN")
                .map(PathBuf::from)
                .and_then(|b| b.parent()?.parent().map(|r| r.join("lib/lean")));
            let entry = env_map.entry("LEAN_PATH".to_string()).or_default();
            let mut merged: Vec<String> = Vec::new();
            let mut tc_tail: Vec<String> = Vec::new();
            for p in entry.split(':') {
                let p_trim = p.trim();
                if p_trim.is_empty() {
                    continue;
                }
                if tc_lib.as_deref().is_some_and(|tc| {
                    crate::zygote::is_toolchain_dir_match(Path::new(p_trim), Some(tc))
                }) {
                    if !tc_tail.iter().any(|e| e == p_trim) {
                        tc_tail.push(p_trim.to_string());
                    }
                } else if !merged.iter().any(|e| e == p_trim) {
                    merged.push(p_trim.to_string());
                }
            }
            for p in trimmed.split(':').chain(tc_tail.iter().map(String::as_str)) {
                let p_trim = p.trim();
                if !p_trim.is_empty() && !merged.iter().any(|e| e == p_trim) {
                    merged.push(p_trim.to_string());
                }
            }
            *entry = merged.join(":");
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
        } else if path.is_file()
            && !target.exists()
            && (fs::hard_link(&path, &target).is_ok() || fs::copy(&path, &target).is_ok())
        {
            count += 1;
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

#[allow(clippy::type_complexity)]
static WORKTREE_AUTO_LINK_DISABLED_MEMO: std::sync::OnceLock<
    std::sync::Mutex<
        HashMap<
            PathBuf,
            (
                u64,
                Option<(PathBuf, crate::module_builder::FileStatFingerprint)>,
                bool,
            ),
        >,
    >,
> = std::sync::OnceLock::new();

pub(crate) fn clear_worktree_auto_link_memo() {
    if let Some(m) = WORKTREE_AUTO_LINK_DISABLED_MEMO.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
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
    let window = crate::module_builder::current_memo_window();
    let memo =
        WORKTREE_AUTO_LINK_DISABLED_MEMO.get_or_init(|| std::sync::Mutex::new(HashMap::new()));
    let toml_path = crate::shm_cache::find_nearest_project_toml(Some(project_dir));
    let toml_stat = toml_path.as_deref().map(|tp| {
        (
            tp.to_path_buf(),
            crate::module_builder::path_stat_fingerprint(tp),
        )
    });
    if let Ok(g) = memo.lock() {
        if let Some((w, cached_toml, res)) = g.get(project_dir) {
            if *w == window && *cached_toml == toml_stat {
                return *res;
            }
        }
    }
    let res = toml_path
        .as_deref()
        .and_then(|p| fs::read_to_string(p).ok())
        .and_then(|t| crate::accelerators::toml_value(&t, "worktree", "auto_link"))
        .and_then(|v| crate::shm_cache::parse_relaxed_bool(&v))
        == Some(false);
    if let Ok(mut g) = memo.lock() {
        if crate::module_builder::current_memo_window() == window {
            if g.len() >= 1024 {
                g.clear();
            }
            g.insert(project_dir.to_path_buf(), (window, toml_stat, res));
        }
    }
    res
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
        match (m_cfg.is_file(), w_cfg.is_file()) {
            (true, true) => {
                if fs::read(&m_cfg).ok() != fs::read(&w_cfg).ok() {
                    return 0;
                }
            }
            (false, false) => {}
            _ => return 0,
        }
    }
    let (Ok(m_cands), Ok(w_cands)) = (
        crate::module_builder::workspace_lake_config_candidates(&main_project_dir),
        crate::module_builder::workspace_lake_config_candidates(project_dir),
    ) else {
        return 0;
    };
    let rel_cands = |base: &Path, cands: &[PathBuf]| -> Option<Vec<(PathBuf, Vec<u8>)>> {
        let canon_base = base.canonicalize().unwrap_or_else(|_| base.to_path_buf());
        let mut out = Vec::with_capacity(cands.len());
        for c in cands {
            let canon_c = c.canonicalize().ok()?;
            let rel = canon_c.strip_prefix(&canon_base).ok()?.to_path_buf();
            let bytes = fs::read(&canon_c).ok()?;
            out.push((rel, bytes));
        }
        out.sort_by(|a, b| a.0.cmp(&b.0));
        Some(out)
    };
    match (
        rel_cands(&main_project_dir, &m_cands),
        rel_cands(project_dir, &w_cands),
    ) {
        (Some(mc), Some(wc)) if mc == wc => {}
        _ => return 0,
    }
    let may_have_inputs =
        crate::module_builder::workspace_may_declare_lake_inputs(&main_project_dir)
            || crate::module_builder::workspace_may_declare_lake_inputs(project_dir);
    let mut main_inputs_verified = true;
    if may_have_inputs {
        let (Ok(m_cfg), Ok(w_cfg)) = (
            crate::module_builder::resolve_project_config(&main_project_dir),
            crate::module_builder::resolve_project_config(project_dir),
        ) else {
            return 0;
        };
        let (Ok(m_dig), Ok(w_dig)) = (
            crate::module_builder::workspace_lake_inputs_digest(&m_cfg),
            crate::module_builder::workspace_lake_inputs_digest(&w_cfg),
        ) else {
            return 0;
        };
        if m_dig != w_dig || m_cfg.canonical_config_digest != w_cfg.canonical_config_digest {
            return 0;
        }
        if !m_dig.is_empty() {
            // Only link `.olean` artifacts from `main_project_dir` when its verified manifest
            // proves those `.olean`s were built against `m_dig` (preventing stale `.olean`s from
            // an un-rebuilt dirty main repo from being copied into a worktree with matching bytes).
            main_inputs_verified = load_verified_project_manifest(&main_project_dir).is_some()
                && m_cfg.dep_pkgs.iter().all(|dp| {
                    let dp_build = dp.pkg_root.join(&dp.build_dir);
                    if !dp_build.is_dir() {
                        return true;
                    }
                    fs::read(dp_build.join(".turbo_verified_sources.json"))
                        .ok()
                        .and_then(|b| {
                            serde_json::from_slice::<crate::module_builder::VerifiedDepManifest>(&b)
                                .ok()
                        })
                        .is_some_and(|m| m.lake_inputs_digest == m_dig)
                });
            if !main_inputs_verified {
                return 0;
            }
        }
    }
    let _ = main_inputs_verified;
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
/// shared `/dev/shm/turbo-lean-staging/lake_env_v1_<key>.json`, or static installed-toolchain paths.
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
        sanitize_toolchain_env(&canon_dir, &mut cached)?;
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
                sanitize_toolchain_env(&canon_dir, &mut env_map)?;
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
    sanitize_toolchain_env(&canon_dir, &mut env_map)?;
    merge_caller_lean_path(&mut env_map);
    Ok((env_map, false))
}

pub(crate) fn resolve_or_share_lake_env(
    store: &TurboStore,
    canon_dir: &Path,
    env_key: &str,
) -> Result<Option<(HashMap<String, String>, bool)>> {
    if let Some(mut m) = store.get_lake_env(env_key)? {
        sanitize_toolchain_env(canon_dir, &mut m)?;
        merge_caller_lean_path(&mut m);
        return Ok(Some((m, false)));
    }
    let shm_env_path = store
        .fast_staging_dir()
        .join(format!("lake_env_v1_{}.json", env_key));
    if let Ok(bytes) = fs::read(&shm_env_path) {
        if let Ok(mut env_map) = serde_json::from_slice::<HashMap<String, String>>(&bytes) {
            if !env_map.is_empty() {
                sanitize_toolchain_env(canon_dir, &mut env_map)?;
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
        sanitize_toolchain_env(canon_dir, &mut env_map)?;
        merge_caller_lean_path(&mut env_map);
        return Ok(Some((env_map, true)));
    }
    Ok(None)
}

/// Ignore executable/PATH values from cached or project-provided Lake environments.
pub(crate) fn resolve_lean_bin(project: &Path) -> Result<String> {
    Ok(
        crate::module_builder::ToolchainExecutables::resolve(project, &detect_toolchain(project))?
            .lean
            .to_string_lossy()
            .into_owned(),
    )
}

fn sanitize_toolchain_env(project: &Path, env: &mut HashMap<String, String>) -> Result<()> {
    crate::module_builder::ToolchainExecutables::resolve(project, &detect_toolchain(project))?
        .apply_env(env);
    Ok(())
}

fn collect_project_lean_lib_dirs(project_dir: &Path) -> Vec<PathBuf> {
    if project_dir.as_os_str().is_empty() {
        return Vec::new();
    }
    let mut dirs = Vec::new();
    let mut push = |p: PathBuf| {
        if !dirs.contains(&p) {
            dirs.push(p);
        }
    };
    let root_pkg = crate::module_builder::resolve_package_config(project_dir, false).ok();
    push(
        root_pkg
            .as_ref()
            .map(|c| project_dir.join(&c.build_dir).join(&c.lean_lib_dir))
            .unwrap_or_else(|| project_dir.join(".lake/build/lib/lean")),
    );
    push(project_dir.join(".lake/build/lib/lean"));
    if let Ok((_, manifest_pkgs, manifest_hash_opt)) =
        crate::module_builder::parse_lake_manifest(project_dir, false)
    {
        for mp in manifest_pkgs {
            let pkg_root = mp.dir.canonicalize().unwrap_or(mp.dir);
            push(crate::module_builder::resolve_package_lean_lib_dir(
                &pkg_root,
                mp.config_file.as_deref(),
            ));
        }
        if manifest_hash_opt.is_none() {
            let pkgs_rel = root_pkg
                .as_ref()
                .map(|c| c.packages_dir.as_path())
                .unwrap_or_else(|| Path::new(".lake/packages"));
            if let Ok(entries) = fs::read_dir(project_dir.join(pkgs_rel)) {
                let mut pkg_dirs: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
                pkg_dirs.sort();
                for pkg_dir in pkg_dirs {
                    let lib = crate::module_builder::resolve_package_lean_lib_dir(&pkg_dir, None);
                    if lib.is_dir() {
                        push(lib);
                    }
                }
            }
        }
    }
    if let Ok(entries) = fs::read_dir(project_dir.join(".lake/packages")) {
        let mut pkg_libs: Vec<PathBuf> = entries
            .flatten()
            .map(|e| crate::module_builder::resolve_package_lean_lib_dir(&e.path(), None))
            .filter(|p| p.is_dir())
            .collect();
        pkg_libs.sort();
        for p in pkg_libs {
            push(p);
        }
    }
    dirs
}

pub(crate) fn resolve_remote_lean_path(
    canon_dir: &Path,
    env_vars: Option<&HashMap<String, String>>,
) -> String {
    let mut parts = Vec::new();
    let mut push_part = |pb: PathBuf, require_exists: bool| {
        if require_exists && !pb.exists() {
            return;
        }
        let s = pb.to_string_lossy().to_string();
        if !parts.contains(&s) {
            parts.push(s);
        }
    };
    let push_lp = |lp: &str, require_exists: bool, push_part: &mut dyn FnMut(PathBuf, bool)| {
        for p in lp.split(':') {
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
            push_part(abs, require_exists);
        }
    };
    for dir in collect_project_lean_lib_dirs(canon_dir) {
        push_part(dir, true);
    }
    if let Ok(caller_lp) = std::env::var("LEAN_PATH") {
        push_lp(&caller_lp, true, &mut push_part);
    }
    if let Some(lp) = env_vars.and_then(|e| e.get("LEAN_PATH")) {
        push_lp(lp, false, &mut push_part);
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
    // v8: replay-audited verdicts + 3-byte `/--` and `/-!` docstring/module-doc opener fix.
    // The verifier provenance versions are bound too, so pre-replay receipts never match
    // and any later scanner/replay bump retires every older receipt.
    key_hasher.update(b"theorem-shard-v8:");
    key_hasher.update(&crate::zygote::ZYGOTE_SCANNER_VERSION.to_le_bytes());
    key_hasher.update(&crate::zygote::ZYGOTE_REPLAY_VERSION.to_le_bytes());
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
    for (tag, env_key) in [
        ("csimp", "TURBO_LEAN_ALLOWED_CSIMP"),
        ("unsafe", "TURBO_LEAN_ALLOWED_UNSAFE"),
        ("impl_by", "TURBO_LEAN_ALLOWED_IMPLEMENTED_BY"),
    ] {
        if let Ok(val) = std::env::var(env_key) {
            let trimmed = val.trim();
            if !trimmed.is_empty() {
                key_hasher.update(b":");
                key_hasher.update(tag.as_bytes());
                key_hasher.update(b":");
                key_hasher.update(trimmed.as_bytes());
            }
        }
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
    let start_dir = if path.is_file() {
        path.parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."))
    } else if path.as_os_str().is_empty() {
        Path::new(".")
    } else {
        path
    };
    let mut cur = Some(start_dir);
    while let Some(dir) = cur {
        if dir.join("lakefile.lean").exists()
            || dir.join("lakefile.toml").exists()
            || dir.join("lake-manifest.json").exists()
            || dir.join("lean-toolchain").exists()
            || dir.join(".lake").is_dir()
        {
            return dir.to_path_buf();
        }
        cur = dir.parent().filter(|p| !p.as_os_str().is_empty());
    }
    start_dir.to_path_buf()
}

#[allow(clippy::type_complexity)]
static SINGLE_OLEAN_DIGEST_MEMO: std::sync::OnceLock<
    std::sync::Mutex<
        HashMap<
            PathBuf,
            (
                u64,
                [Option<crate::zygote::OleanFileStatSig>; 6],
                [u8; 32],
                String,
                Vec<String>,
            ),
        >,
    >,
> = std::sync::OnceLock::new();

#[allow(clippy::type_complexity)]
struct InterfaceClosureMemoEntry {
    window: u64,
    self_stats: std::sync::Arc<Vec<(PathBuf, Option<crate::zygote::OleanFileStatSig>)>>,
    sample_check: Option<(
        PathBuf,
        [PathBuf; 5],
        [Option<crate::zygote::OleanFileStatSig>; 6],
        [u8; 32],
    )>,
    pkg_dir_presence: std::sync::Arc<Vec<(PathBuf, bool)>>,
    self_entries: std::sync::Arc<Vec<String>>,
    children: std::sync::Arc<Vec<String>>,
}

#[allow(clippy::type_complexity)]
static MODULE_INTERFACE_CLOSURE_MEMO: std::sync::OnceLock<
    std::sync::Mutex<HashMap<(PathBuf, String, String), InterfaceClosureMemoEntry>>,
> = std::sync::OnceLock::new();

#[derive(serde::Serialize, serde::Deserialize)]
struct ShmSingleOleanDigestEntry {
    stats: [Option<crate::zygote::OleanFileStatSig>; 6],
    sample_key: [u8; 32],
    digest: String,
    deps: Vec<String>,
}

fn shm_single_olean_cache_file_name(olean_path: &Path) -> String {
    let key = blake3::hash(olean_path.to_string_lossy().as_bytes())
        .to_hex()
        .to_string();
    format!("oi_{}.json", &key[..28])
}

fn compute_olean_bundle_sample_key(
    olean_path: &Path,
    comp_paths: &[PathBuf; 5],
    stats: &[Option<crate::zygote::OleanFileStatSig>; 6],
) -> Option<[u8; 32]> {
    stats[0]?;
    let mut sample_hasher = blake3::Hasher::new();
    sample_hasher.update(b"olean-bundle-sample-v1\n");
    let mut hash_one = |p: &Path, st: Option<crate::zygote::OleanFileStatSig>| -> Option<()> {
        match st {
            None => {
                sample_hasher.update(&[0u8]);
                Some(())
            }
            Some(sig) => {
                let sz = sig.size;
                sample_hasher.update(&[1u8]);
                sample_hasher.update(&sz.to_le_bytes());
                let mut f = fs::File::open(p).ok()?;
                use std::io::{Read, Seek, SeekFrom};
                let mut buf = [0u8; 4096];
                let n = f.read(&mut buf).ok()?;
                sample_hasher.update(&buf[..n]);
                if sz > 8192 && f.seek(SeekFrom::End(-4096)).is_ok() {
                    if let Ok(n2) = f.read(&mut buf) {
                        sample_hasher.update(&buf[..n2]);
                    }
                }
                Some(())
            }
        }
    };
    hash_one(olean_path, stats[0])?;
    for i in 0..5 {
        hash_one(&comp_paths[i], stats[i + 1])?;
    }
    Some(*sample_hasher.finalize().as_bytes())
}

pub(crate) fn clear_olean_interface_memo() {
    if let Some(m) = SINGLE_OLEAN_DIGEST_MEMO.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
    if let Some(m) = MODULE_INTERFACE_CLOSURE_MEMO.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
    if let Some(m) = PROJECT_SOURCE_BLAKE3_MEMO.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
}

pub(crate) fn single_olean_companion_paths(olean_path: &Path) -> [PathBuf; 5] {
    [
        PathBuf::from(format!("{}.server", olean_path.display())),
        PathBuf::from(format!("{}.private", olean_path.display())),
        olean_path.with_extension("ilean"),
        olean_path.with_extension("ir"),
        PathBuf::from(format!("{}.sig", olean_path.with_extension("ir").display())),
    ]
}

pub(crate) fn single_olean_stat_bundle(
    olean_path: &Path,
    comp_paths: &[PathBuf; 5],
) -> [Option<crate::zygote::OleanFileStatSig>; 6] {
    [
        crate::module_builder::path_olean_stat_sig(olean_path),
        crate::module_builder::path_olean_stat_sig(&comp_paths[0]),
        crate::module_builder::path_olean_stat_sig(&comp_paths[1]),
        crate::module_builder::path_olean_stat_sig(&comp_paths[2]),
        crate::module_builder::path_olean_stat_sig(&comp_paths[3]),
        crate::module_builder::path_olean_stat_sig(&comp_paths[4]),
    ]
}

pub(crate) fn compute_single_olean_digest_and_imports_with_stats(
    olean_path: &Path,
    comp_paths: &[PathBuf; 5],
    cur_stats: [Option<crate::zygote::OleanFileStatSig>; 6],
) -> Option<(String, Vec<String>, [u8; 32])> {
    let window = crate::module_builder::current_memo_window();
    cur_stats[0]?;
    let sample_key = compute_olean_bundle_sample_key(olean_path, comp_paths, &cur_stats)?;
    let memo = SINGLE_OLEAN_DIGEST_MEMO.get_or_init(|| std::sync::Mutex::new(HashMap::new()));
    let can_reuse = crate::module_builder::olean_stat_bundle6_trusted_for_reuse(&cur_stats);
    if can_reuse {
        if let Ok(g) = memo.lock() {
            if let Some((w, cached_stats, cached_sample, dig, deps)) = g.get(olean_path) {
                if *w == window && *cached_stats == cur_stats && *cached_sample == sample_key {
                    return Some((dig.clone(), deps.clone(), sample_key));
                }
            }
        }
    }
    let use_shm = can_reuse && cur_stats[0].is_some_and(|s| s.size > 65536);
    let shm_file_opt = cur_stats[0]
        .is_some_and(|s| s.size > 65536)
        .then(|| shm_single_olean_cache_file_name(olean_path));
    if use_shm {
        if let Some(ref shm_file_name) = shm_file_opt {
            if let Some(shm_bytes) =
                crate::shm_cache::read_verified_private_shm_file("olean_iface_v2", shm_file_name)
            {
                if let Ok(entry) = serde_json::from_slice::<ShmSingleOleanDigestEntry>(&shm_bytes) {
                    if entry.stats == cur_stats && entry.sample_key == sample_key {
                        if let Ok(mut g) = memo.lock() {
                            if crate::module_builder::current_memo_window() == window {
                                if g.len() >= 65536 {
                                    g.clear();
                                }
                                g.insert(
                                    olean_path.to_path_buf(),
                                    (
                                        window,
                                        cur_stats,
                                        sample_key,
                                        entry.digest.clone(),
                                        entry.deps.clone(),
                                    ),
                                );
                            }
                        }
                        return Some((entry.digest, entry.deps, sample_key));
                    }
                }
            }
        }
    }
    let read_started_ns = crate::zygote::wall_clock_ns();
    let (pre0, bytes, post0) =
        crate::module_builder::read_regular_file_bound_stat(olean_path).ok()?;
    let mut fd_stats = [Some(post0), None, None, None, None, None];
    let mut fd_stable = pre0 == post0;
    let olean_deps = crate::module_builder::parse_olean_binary_imports(&bytes)
        .map(|(imps, _)| imps.into_iter().map(|i| i.module).collect::<Vec<String>>())
        .unwrap_or_default();
    let mut h = blake3::Hasher::new();
    h.update(b"olean-full:v3:");
    h.update(blake3::hash(&bytes).as_bytes());
    let tags = ["srv", "priv", "ilean", "ir", "ir_sig"];
    for (idx, (tag, comp_path)) in tags.iter().zip(comp_paths.iter()).enumerate() {
        h.update(b"|");
        h.update(tag.as_bytes());
        match crate::module_builder::read_regular_file_bound_stat(comp_path) {
            Ok((cpre, comp_bytes, cpost)) => {
                if cpre != cpost {
                    fd_stable = false;
                }
                fd_stats[idx + 1] = Some(cpost);
                h.update(&[1u8]);
                h.update(blake3::hash(&comp_bytes).as_bytes());
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                h.update(&[0u8]);
            }
            Err(_) => return None,
        }
    }
    let dig = h.finalize().to_hex().to_string();
    let post_stats = single_olean_stat_bundle(olean_path, comp_paths);
    let post_sample_opt = compute_olean_bundle_sample_key(olean_path, comp_paths, &post_stats);
    if let Some(post_sample) = post_sample_opt {
        if fd_stable
            && fd_stats == cur_stats
            && post_stats == cur_stats
            && post_sample == sample_key
            && crate::module_builder::olean_stat_bundle6_trusted_to_store(
                &post_stats,
                read_started_ns,
            )
        {
            if let Ok(mut g) = memo.lock() {
                if crate::module_builder::current_memo_window() == window {
                    if g.len() >= 65536 {
                        g.clear();
                    }
                    g.insert(
                        olean_path.to_path_buf(),
                        (
                            window,
                            post_stats,
                            post_sample,
                            dig.clone(),
                            olean_deps.clone(),
                        ),
                    );
                }
            }
            if let Some(shm_file_name) = shm_file_opt {
                let shm_entry = ShmSingleOleanDigestEntry {
                    stats: post_stats,
                    sample_key: post_sample,
                    digest: dig.clone(),
                    deps: olean_deps.clone(),
                };
                if let Ok(shm_bytes) = serde_json::to_vec(&shm_entry) {
                    let _ = crate::shm_cache::write_verified_private_shm_file(
                        "olean_iface_v2",
                        &shm_file_name,
                        &shm_bytes,
                    );
                }
            }
        }
    }
    Some((dig, olean_deps, post_sample_opt.unwrap_or(sample_key)))
}

#[allow(clippy::type_complexity)]
static PROJECT_SOURCE_BLAKE3_MEMO: std::sync::OnceLock<
    std::sync::Mutex<HashMap<(PathBuf, crate::zygote::OleanFileStatSig, [u8; 32]), (u64, String)>>,
> = std::sync::OnceLock::new();

pub(crate) fn compute_cached_source_blake3(path: &Path) -> Option<String> {
    let cur_sig = crate::module_builder::path_olean_stat_sig(path)?;
    if cur_sig.size <= 65536 {
        let (_, bytes, _) = crate::module_builder::read_regular_file_bound_stat(path).ok()?;
        return Some(blake3::hash(&bytes).to_hex().to_string());
    }
    let window = crate::module_builder::current_memo_window();
    let mut sample_hasher = blake3::Hasher::new();
    if let Ok(mut f) = fs::File::open(path) {
        use std::io::{Read, Seek, SeekFrom};
        let mut buf = [0u8; 4096];
        if let Ok(n) = f.read(&mut buf) {
            sample_hasher.update(&buf[..n]);
        }
        if cur_sig.size > 8192 && f.seek(SeekFrom::End(-4096)).is_ok() {
            if let Ok(n) = f.read(&mut buf) {
                sample_hasher.update(&buf[..n]);
            }
        }
    }
    let sample_key = *sample_hasher.finalize().as_bytes();
    let memo_key = (path.to_path_buf(), cur_sig, sample_key);
    let cache = PROJECT_SOURCE_BLAKE3_MEMO.get_or_init(|| std::sync::Mutex::new(HashMap::new()));
    if crate::zygote::dev_records_subsecond_timestamps(&cur_sig) {
        if let Ok(guard) = cache.lock() {
            if let Some((w, hit)) = guard.get(&memo_key) {
                if *w == window {
                    return Some(hit.clone());
                }
            }
        }
    }
    let read_started_ns = crate::zygote::wall_clock_ns();
    let (fd_pre, bytes, fd_post) =
        crate::module_builder::read_regular_file_bound_stat(path).ok()?;
    let hex = blake3::hash(&bytes).to_hex().to_string();
    if fd_pre == fd_post
        && fd_pre == cur_sig
        && crate::module_builder::path_olean_stat_sig(path) == Some(fd_post)
        && crate::module_builder::olean_stat_sig_trusted_at(&fd_post, read_started_ns)
    {
        if let Ok(mut guard) = cache.lock() {
            if crate::module_builder::current_memo_window() == window {
                if guard.len() > 8192 {
                    guard.clear();
                }
                guard.insert(memo_key, (window, hex.clone()));
            }
        }
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
/// Searches `project_dir/.lake/build/lib/lean`, `project_dir/.lake/packages/*/.lake/build/lib/lean`,
/// and then `lean_path` (or `LEAN_PATH`).
/// Returns a sorted `Vec<String>` of `"<ModName>:<blake3_hex>"`.
///
/// Also carries [`crate::module_builder::project_lake_inputs_tag`] when the workspace declares
/// Lake file inputs: those bytes are read while `src` elaborates but belong to no imported module,
/// so without the extra entry every cache keyed on this list -- file splits, `prefix_env_hash` and
/// so the theorem-shard and proof-fission keys -- would hit on a result computed against the old
/// input. Every caller feeds the list to the same two consumers (seed a split, or re-derive it to
/// validate a cached one), so one entry here invalidates readers and writers together. Absent for
/// every workspace without inputs, which keeps their keys byte-identical.
pub fn compute_imported_olean_interface_hashes(
    src: &str,
    project_dir: &Path,
    lean_path: Option<&str>,
) -> Vec<String> {
    let lake_inputs_tag = crate::module_builder::project_lake_inputs_tag(project_dir);
    compute_imported_olean_interface_hashes_with_tag(src, project_dir, lean_path, lake_inputs_tag)
}

fn resolve_olean_search_dirs_and_tc(
    project_dir: &Path,
    lean_path: Option<&str>,
) -> (Vec<PathBuf>, String, Option<(PathBuf, String)>) {
    let resolved_tc: Option<(PathBuf, String)> = if !project_dir.as_os_str().is_empty() {
        let tc = detect_toolchain(project_dir);
        crate::module_builder::resolve_toolchain_compiler_with_trust(project_dir, &tc, true)
            .ok()
            .map(|(_, gh, tc_lib_lean, _)| (tc_lib_lean, gh))
    } else {
        None
    };
    let resolved_tc_lib: Option<PathBuf> = resolved_tc.as_ref().map(|(tc_lib, _)| tc_lib.clone());

    let mut search_dirs: Vec<PathBuf> = Vec::new();
    let push_search_dir = |search_dirs: &mut Vec<PathBuf>, pb: PathBuf| {
        if !pb.is_dir() || crate::zygote::is_toolchain_dir_match(&pb, resolved_tc_lib.as_deref()) {
            return;
        }
        let canon_pb = fs::canonicalize(&pb).ok();
        let already = search_dirs.iter().any(|existing| {
            existing == &pb
                || match (&canon_pb, fs::canonicalize(existing).ok()) {
                    (Some(a), Some(b)) => a == &b,
                    _ => false,
                }
        });
        if !already {
            search_dirs.push(pb);
        }
    };
    let push_lean_path = |search_dirs: &mut Vec<PathBuf>, lp: &str| {
        for part in lp.split(':') {
            let trimmed = part.trim();
            if trimmed.is_empty() {
                continue;
            }
            let p = Path::new(trimmed);
            push_search_dir(
                search_dirs,
                if p.is_absolute() || project_dir.as_os_str().is_empty() {
                    p.to_path_buf()
                } else {
                    project_dir.join(p)
                },
            );
        }
    };
    for dir in collect_project_lean_lib_dirs(project_dir) {
        push_search_dir(&mut search_dirs, dir);
    }
    let lp_owned: Option<String> = lean_path
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .or_else(|| std::env::var("LEAN_PATH").ok().filter(|s| !s.is_empty()));
    if let Some(ref lp) = lp_owned {
        push_lean_path(&mut search_dirs, lp);
    }
    let search_key = search_dirs
        .iter()
        .map(|d| d.to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join(":");
    (search_dirs, search_key, resolved_tc)
}

#[derive(Default)]
#[allow(clippy::type_complexity)]
pub(crate) struct OleanInterfaceBatchSession {
    stat_memo: HashMap<PathBuf, Option<crate::zygote::OleanFileStatSig>>,
    valid_closures: HashSet<(PathBuf, String, String)>,
    project_env_memo:
        HashMap<(PathBuf, Option<String>), (Vec<PathBuf>, String, Option<(PathBuf, String)>)>,
    project_lake_tag_memo: HashMap<PathBuf, Option<String>>,
}

impl OleanInterfaceBatchSession {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn compute_hashes(
        &mut self,
        src: &str,
        project_dir: &Path,
        lean_path: Option<&str>,
    ) -> Vec<String> {
        let tag = if let Some(cached) = self.project_lake_tag_memo.get(project_dir) {
            cached.clone()
        } else {
            let t = crate::module_builder::project_lake_inputs_tag(project_dir);
            self.project_lake_tag_memo
                .insert(project_dir.to_path_buf(), t.clone());
            t
        };
        self.compute_hashes_with_tag(src, project_dir, lean_path, tag)
    }

    pub(crate) fn compute_hashes_with_tag(
        &mut self,
        src: &str,
        project_dir: &Path,
        lean_path: Option<&str>,
        lake_inputs_tag: Option<String>,
    ) -> Vec<String> {
        self.stat_memo.clear();
        self.valid_closures.clear();
        let env_key = (project_dir.to_path_buf(), lean_path.map(|s| s.to_string()));
        let (search_dirs, search_key, resolved_tc) = self
            .project_env_memo
            .entry(env_key)
            .or_insert_with(|| resolve_olean_search_dirs_and_tc(project_dir, lean_path))
            .clone();
        compute_imported_olean_interface_hashes_with_precomputed_env(
            src,
            project_dir,
            &search_dirs,
            &search_key,
            &resolved_tc,
            lake_inputs_tag,
            &mut self.stat_memo,
            &mut self.valid_closures,
        )
    }
}

fn closure_self_stats_valid(
    entry: &InterfaceClosureMemoEntry,
    window: u64,
    stat_memo: &mut HashMap<PathBuf, Option<crate::zygote::OleanFileStatSig>>,
) -> bool {
    if entry.window != window {
        return false;
    }
    entry.self_stats.iter().all(|(p, expected_st)| {
        let cur = *stat_memo
            .entry(p.clone())
            .or_insert_with(|| crate::module_builder::path_olean_stat_sig(p));
        cur == *expected_st
            && cur.is_none_or(|ref sig| crate::zygote::dev_records_subsecond_timestamps(sig))
    }) && entry
        .pkg_dir_presence
        .iter()
        .all(|(p, expected_dir)| p.is_dir() == *expected_dir)
        && entry
            .sample_check
            .as_ref()
            .is_none_or(|(cand, comp_paths, stats, expected_sample)| {
                crate::module_builder::olean_stat_bundle6_trusted_for_reuse(stats)
                    && compute_olean_bundle_sample_key(cand, comp_paths, stats).as_ref()
                        == Some(expected_sample)
            })
}

#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn compute_imported_olean_interface_hashes_with_precomputed_env(
    src: &str,
    project_dir: &Path,
    search_dirs: &[PathBuf],
    search_key: &str,
    resolved_tc: &Option<(PathBuf, String)>,
    lake_inputs_tag: Option<String>,
    stat_memo: &mut HashMap<PathBuf, Option<crate::zygote::OleanFileStatSig>>,
    valid_closures: &mut HashSet<(PathBuf, String, String)>,
) -> Vec<String> {
    let mut worklist = parse_header_imports(src);
    if worklist.is_empty() {
        return lake_inputs_tag.into_iter().collect();
    }

    if search_dirs.is_empty() && project_dir.as_os_str().is_empty() {
        return lake_inputs_tag.into_iter().collect();
    }

    let window = crate::module_builder::current_memo_window();
    let closure_memo =
        MODULE_INTERFACE_CLOSURE_MEMO.get_or_init(|| std::sync::Mutex::new(HashMap::new()));

    let stat_of = |p: &Path,
                   sm: &mut HashMap<PathBuf, Option<crate::zygote::OleanFileStatSig>>|
     -> Option<crate::zygote::OleanFileStatSig> {
        if let Some(&st) = sm.get(p) {
            st
        } else {
            let st = crate::module_builder::path_olean_stat_sig(p);
            sm.insert(p.to_path_buf(), st);
            st
        }
    };

    worklist.sort();
    worklist.dedup();

    let mut visited_mods: HashSet<String> = HashSet::new();
    let mut stack: Vec<String> = worklist;
    let search_refs: Vec<&Path> = search_dirs.iter().map(PathBuf::as_path).collect();
    let tc_ref = resolved_tc.as_ref().map(|(tc_lib, _)| tc_lib.as_path());
    let tc_gh_ref = resolved_tc.as_ref().map(|(_, gh)| gh.as_str());
    let mut out: Vec<String> = Vec::new();
    let mut uncached_oleans: Vec<(
        String,
        PathBuf,
        [PathBuf; 5],
        [Option<crate::zygote::OleanFileStatSig>; 6],
        Option<PathBuf>,
        Option<String>,
        Vec<(PathBuf, Option<crate::zygote::OleanFileStatSig>)>,
        Vec<(PathBuf, bool)>,
    )> = Vec::new();

    loop {
        while let Some(cur_mod) = stack.pop() {
            if !visited_mods.insert(cur_mod.clone()) {
                continue;
            }
            let cur_key = (
                project_dir.to_path_buf(),
                search_key.to_string(),
                cur_mod.clone(),
            );
            let cached_node = if let Ok(g) = closure_memo.lock() {
                if let Some(entry) = g.get(&cur_key) {
                    if entry.window == window
                        && (valid_closures.contains(&cur_key)
                            || closure_self_stats_valid(entry, window, stat_memo))
                    {
                        valid_closures.insert(cur_key.clone());
                        Some((entry.self_entries.clone(), entry.children.clone()))
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            };
            if let Some((self_entries, children)) = cached_node {
                out.extend(self_entries.iter().cloned());
                for ch in children.iter() {
                    if !visited_mods.contains(ch) {
                        stack.push(ch.clone());
                    }
                }
                continue;
            }

            let rel_slash = crate::module_builder::module_name_to_rel_slash(&cur_mod);
            let rel_olean = format!("{}.olean", rel_slash);
            let mut self_stats: Vec<(PathBuf, Option<crate::zygote::OleanFileStatSig>)> =
                Vec::new();
            let sub_lean_opt = resolve_project_lean_source(project_dir, &rel_slash);
            if let Some(ref lp) = sub_lean_opt {
                let st = stat_of(lp, stat_memo);
                self_stats.push((lp.clone(), st));
            }
            let src_digest_opt = sub_lean_opt
                .as_deref()
                .and_then(compute_cached_source_blake3);

            let pkg = rel_slash.split('/').next().unwrap_or_default();
            let pkg_olean = format!("{}.olean", pkg);
            let mut pkg_dir_presence: Vec<(PathBuf, bool)> = Vec::new();
            let mut owner_root: Option<&Path> = None;
            for dir in search_dirs {
                let pkg_dir = dir.join(pkg);
                let has_pkg_dir = pkg_dir.is_dir();
                pkg_dir_presence.push((pkg_dir, has_pkg_dir));
                let pkg_olean_path = dir.join(&pkg_olean);
                let st_pkg_olean = stat_of(&pkg_olean_path, stat_memo);
                self_stats.push((pkg_olean_path.clone(), st_pkg_olean));
                if has_pkg_dir || st_pkg_olean.is_some() || pkg_olean_path.exists() {
                    owner_root = Some(dir.as_path());
                    break;
                }
            }
            if crate::zygote::is_resolved_toolchain_builtin(&search_refs, &cur_mod, tc_ref)
                && owner_root.is_none_or(|d| crate::zygote::is_toolchain_dir_match(d, tc_ref))
            {
                owner_root = None;
            }

            let mut matched_olean: Option<(
                PathBuf,
                [PathBuf; 5],
                [Option<crate::zygote::OleanFileStatSig>; 6],
            )> = None;
            if let Some(dir) = owner_root {
                let cand = dir.join(&rel_olean);
                let st0 = stat_of(&cand, stat_memo);
                self_stats.push((cand.clone(), st0));
                if st0.is_some() {
                    let comp_paths = single_olean_companion_paths(&cand);
                    let cur_stats = [
                        st0,
                        stat_of(&comp_paths[0], stat_memo),
                        stat_of(&comp_paths[1], stat_memo),
                        stat_of(&comp_paths[2], stat_memo),
                        stat_of(&comp_paths[3], stat_memo),
                        stat_of(&comp_paths[4], stat_memo),
                    ];
                    let companions_valid = comp_paths
                        .iter()
                        .zip(cur_stats[1..].iter().copied())
                        .all(|(cp, cst)| cst.is_some() || !cp.exists());
                    for (cp, cst) in comp_paths.iter().zip(cur_stats[1..].iter().copied()) {
                        self_stats.push((cp.clone(), cst));
                    }
                    if companions_valid {
                        matched_olean = Some((cand, comp_paths, cur_stats));
                    }
                }
            }

            if let Some((cand, comp_paths, cur_stats)) = matched_olean {
                let sample_opt =
                    crate::module_builder::olean_stat_bundle6_trusted_for_reuse(&cur_stats)
                        .then(|| compute_olean_bundle_sample_key(&cand, &comp_paths, &cur_stats))
                        .flatten();
                let fast_hit = sample_opt.and_then(|sample_key| {
                    let memo = SINGLE_OLEAN_DIGEST_MEMO
                        .get_or_init(|| std::sync::Mutex::new(HashMap::new()));
                    let mut hit = None;
                    if let Ok(g) = memo.lock() {
                        if let Some((w, cached_stats, cached_sample, dig, deps)) = g.get(&cand) {
                            if *w == window
                                && *cached_stats == cur_stats
                                && *cached_sample == sample_key
                            {
                                hit = Some((dig.clone(), deps.clone(), sample_key));
                            }
                        }
                    }
                    hit
                });
                if let Some((od, olean_sub_mods, sample_key)) = fast_hit {
                    let mut self_entries = Vec::new();
                    match src_digest_opt {
                        Some(sd) => self_entries.push(format!("{}:{}:src={}", cur_mod, od, sd)),
                        None => self_entries.push(format!("{}:{}", cur_mod, od)),
                    }
                    let mut children: Vec<String> = olean_sub_mods
                        .into_iter()
                        .filter(|sub_mod| {
                            crate::zygote::resolve_closure_module(&search_refs, sub_mod, tc_ref)
                                .is_some()
                        })
                        .collect();
                    if let Some(ref sub_lean) = sub_lean_opt {
                        if let Some(sub_mods) = read_header_imports_from_file(sub_lean) {
                            children.extend(sub_mods);
                        } else {
                            self_entries.push(format!("{}:invalid_header", cur_mod));
                        }
                    }
                    children.sort();
                    children.dedup();
                    out.extend(self_entries.iter().cloned());
                    for ch in &children {
                        if !visited_mods.contains(ch) {
                            stack.push(ch.clone());
                        }
                    }
                    let fast_closure_started_ns = crate::zygote::wall_clock_ns();
                    if self_stats
                        .iter()
                        .filter_map(|(_, st)| st.as_ref())
                        .all(|sig| {
                            crate::module_builder::olean_stat_sig_trusted_at(
                                sig,
                                fast_closure_started_ns,
                            )
                        })
                    {
                        let entry = InterfaceClosureMemoEntry {
                            window,
                            self_stats: std::sync::Arc::new(self_stats),
                            sample_check: Some((cand, comp_paths, cur_stats, sample_key)),
                            pkg_dir_presence: std::sync::Arc::new(pkg_dir_presence),
                            self_entries: std::sync::Arc::new(self_entries),
                            children: std::sync::Arc::new(children),
                        };
                        if let Ok(mut g) = closure_memo.lock() {
                            if crate::module_builder::current_memo_window() == window {
                                if g.len() >= 32768 {
                                    g.clear();
                                    valid_closures.clear();
                                }
                                g.insert(cur_key.clone(), entry);
                                valid_closures.insert(cur_key);
                            }
                        }
                    }
                } else {
                    uncached_oleans.push((
                        cur_mod,
                        cand,
                        comp_paths,
                        cur_stats,
                        sub_lean_opt,
                        src_digest_opt,
                        self_stats,
                        pkg_dir_presence,
                    ));
                }
                continue;
            }

            let mut self_entries = Vec::new();
            match src_digest_opt {
                Some(sd) if !search_dirs.is_empty() => {
                    self_entries.push(format!("{}:unbuilt:src={}", cur_mod, sd));
                }
                None if !search_dirs.is_empty() => {
                    let tc_exempt = crate::zygote::is_resolved_toolchain_builtin(
                        &search_refs,
                        &cur_mod,
                        tc_ref,
                    ) && match (tc_ref, tc_gh_ref) {
                        (Some(tc_lib_lean), Some(gh)) => {
                            crate::module_builder::is_builtin_toolchain_module(
                                tc_lib_lean,
                                Some(gh),
                                &cur_mod,
                            )
                        }
                        _ => true,
                    };
                    if !tc_exempt {
                        self_entries.push(format!("{}:missing", cur_mod));
                    }
                }
                _ => {}
            }
            let mut children = Vec::new();
            if let Some(ref sub_lean) = sub_lean_opt {
                if let Some(sub_mods) = read_header_imports_from_file(sub_lean) {
                    children.extend(sub_mods);
                } else {
                    self_entries.push(format!("{}:invalid_header", cur_mod));
                }
            }
            children.sort();
            children.dedup();
            out.extend(self_entries.iter().cloned());
            for ch in &children {
                if !visited_mods.contains(ch) {
                    stack.push(ch.clone());
                }
            }
            let src_closure_started_ns = crate::zygote::wall_clock_ns();
            if self_stats
                .iter()
                .filter_map(|(_, st)| st.as_ref())
                .all(|sig| {
                    crate::module_builder::olean_stat_sig_trusted_at(sig, src_closure_started_ns)
                })
            {
                let entry = InterfaceClosureMemoEntry {
                    window,
                    self_stats: std::sync::Arc::new(self_stats),
                    sample_check: None,
                    pkg_dir_presence: std::sync::Arc::new(pkg_dir_presence),
                    self_entries: std::sync::Arc::new(self_entries),
                    children: std::sync::Arc::new(children),
                };
                if let Ok(mut g) = closure_memo.lock() {
                    if crate::module_builder::current_memo_window() == window {
                        if g.len() >= 32768 {
                            g.clear();
                            valid_closures.clear();
                        }
                        g.insert(cur_key.clone(), entry);
                        valid_closures.insert(cur_key);
                    }
                }
            }
        }

        if uncached_oleans.is_empty() {
            break;
        }

        let batch = std::mem::take(&mut uncached_oleans);
        let workers = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4);
        let computed: Vec<Option<(String, Vec<String>, [u8; 32])>> = if batch.len() >= 2
            && workers > 1
        {
            par_map_indexed(batch.len(), 1, workers, |idx| {
                let (_, ref cand, ref comp_paths, cur_stats, _, _, _, _) = batch[idx];
                compute_single_olean_digest_and_imports_with_stats(cand, comp_paths, cur_stats)
            })
        } else {
            batch
                .iter()
                .map(|(_, cand, comp_paths, cur_stats, _, _, _, _)| {
                    compute_single_olean_digest_and_imports_with_stats(cand, comp_paths, *cur_stats)
                })
                .collect()
        };

        for (
            (
                cur_mod,
                cand,
                comp_paths,
                cur_stats,
                sub_lean_opt,
                src_digest_opt,
                self_stats,
                pkg_dir_presence,
            ),
            res_opt,
        ) in batch.into_iter().zip(computed)
        {
            let mut self_entries = Vec::new();
            let mut children = Vec::new();
            let mut sample_check = None;
            match (res_opt, src_digest_opt) {
                (Some((od, olean_sub_mods, sample_key)), Some(sd)) => {
                    sample_check = Some((cand, comp_paths, cur_stats, sample_key));
                    self_entries.push(format!("{}:{}:src={}", cur_mod, od, sd));
                    children.extend(olean_sub_mods.into_iter().filter(|sub_mod| {
                        crate::zygote::resolve_closure_module(&search_refs, sub_mod, tc_ref)
                            .is_some()
                    }));
                }
                (Some((od, olean_sub_mods, sample_key)), None) => {
                    sample_check = Some((cand, comp_paths, cur_stats, sample_key));
                    self_entries.push(format!("{}:{}", cur_mod, od));
                    children.extend(olean_sub_mods.into_iter().filter(|sub_mod| {
                        crate::zygote::resolve_closure_module(&search_refs, sub_mod, tc_ref)
                            .is_some()
                    }));
                }
                (None, Some(sd)) if !search_dirs.is_empty() => {
                    self_entries.push(format!("{}:unbuilt:src={}", cur_mod, sd));
                }
                (None, None) if !search_dirs.is_empty() => {
                    let tc_exempt = crate::zygote::is_resolved_toolchain_builtin(
                        &search_refs,
                        &cur_mod,
                        tc_ref,
                    ) && match (tc_ref, tc_gh_ref) {
                        (Some(tc_lib_lean), Some(gh)) => {
                            crate::module_builder::is_builtin_toolchain_module(
                                tc_lib_lean,
                                Some(gh),
                                &cur_mod,
                            )
                        }
                        _ => true,
                    };
                    if !tc_exempt {
                        self_entries.push(format!("{}:missing", cur_mod));
                    }
                }
                _ => {}
            }
            if let Some(ref sub_lean) = sub_lean_opt {
                if let Some(sub_mods) = read_header_imports_from_file(sub_lean) {
                    children.extend(sub_mods);
                } else {
                    self_entries.push(format!("{}:invalid_header", cur_mod));
                }
            }
            children.sort();
            children.dedup();
            out.extend(self_entries.iter().cloned());
            for ch in &children {
                if !visited_mods.contains(ch) {
                    stack.push(ch.clone());
                }
            }
            let closure_started_ns = crate::zygote::wall_clock_ns();
            let closure_trusted_to_store =
                self_stats
                    .iter()
                    .filter_map(|(_, st)| st.as_ref())
                    .all(|sig| {
                        crate::module_builder::olean_stat_sig_trusted_at(sig, closure_started_ns)
                    });
            if closure_trusted_to_store {
                let cur_key = (project_dir.to_path_buf(), search_key.to_string(), cur_mod);
                let entry = InterfaceClosureMemoEntry {
                    window,
                    self_stats: std::sync::Arc::new(self_stats),
                    sample_check,
                    pkg_dir_presence: std::sync::Arc::new(pkg_dir_presence),
                    self_entries: std::sync::Arc::new(self_entries),
                    children: std::sync::Arc::new(children),
                };
                if let Ok(mut g) = closure_memo.lock() {
                    if crate::module_builder::current_memo_window() == window {
                        if g.len() >= 32768 {
                            g.clear();
                            valid_closures.clear();
                        }
                        g.insert(cur_key.clone(), entry);
                        valid_closures.insert(cur_key);
                    }
                }
            }
        }
    }

    if let Some(tag) = lake_inputs_tag {
        out.push(tag);
    }
    out.sort();
    out.dedup();
    out
}

pub(crate) fn compute_imported_olean_interface_hashes_with_tag(
    src: &str,
    project_dir: &Path,
    lean_path: Option<&str>,
    lake_inputs_tag: Option<String>,
) -> Vec<String> {
    let mut session = OleanInterfaceBatchSession::new();
    session.compute_hashes_with_tag(src, project_dir, lean_path, lake_inputs_tag)
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
    let dir = store.fast_staging_dir().join("file_splits_v11");
    let _ = crate::shm_cache::ensure_private_dir_all(&dir);
    dir
}

pub(crate) fn compute_single_stat_hash(pk: &str, ms: i64, mn: i64, sz: i64) -> String {
    let mut h = blake3::Hasher::new();
    // v9 invalidates declaration scopes computed before lossless dotted-component canonicalization.
    // v10 includes checking-weakening hygiene fields in cached file splits.
    // v11 invalidates splits computed before 3-byte `/--`/`/-!` docstring & raw/interp lexing fixes.
    // v12-v15 include nested `/--` inside outer block comments/literals fix and retroactive attribute_targets.
    h.update(b"single-stat-split:v15\n");
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
    h.update(b"project-stat-splits:v13\n");
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

    let lake_inputs_tag = crate::module_builder::try_project_lake_inputs_tag(project_dir)?;
    let cfg_candidates = crate::module_builder::workspace_lake_config_candidates(project_dir)?;

    let summary_path = if paths.len() <= 2048 && valid_stats.len() == paths.len() {
        let mut key_h = blake3::Hasher::new();
        key_h.update(b"project-stat-summary-v5\n");
        key_h.update(compute_stat_slice_hash(&valid_stats).as_bytes());
        key_h.update(b"\n");
        if let Some(ref tag) = lake_inputs_tag {
            key_h.update(tag.as_bytes());
            key_h.update(b"\n");
        }
        for cand in &cfg_candidates {
            if let Ok(bytes) = fs::read(cand) {
                key_h.update(cand.to_string_lossy().as_bytes());
                key_h.update(b":");
                key_h.update(blake3::hash(&bytes).as_bytes());
                key_h.update(b"\n");
            }
        }
        if let Ok(bytes) = fs::read(project_dir.join("lake-manifest.json")) {
            key_h.update(b"lake-manifest.json:");
            key_h.update(blake3::hash(&bytes).as_bytes());
            key_h.update(b"\n");
        }
        let stat_hash = key_h.finalize().to_hex().to_string();
        let p = store.fast_staging_dir().join(format!(
            "project_stat_summary_v10_{}.json",
            &stat_hash[..24]
        ));
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

/// Folds the workspace's `input_file` / `input_dir` digests into a whole-project action key
/// (`build`, `ci-verify`): those files are read during elaboration, so a changed input must never
/// reuse a cached whole-project verdict. Unlike the per-module key this ignores `needs`, because a
/// project-wide action covers every library.
///
/// Dependency packages are included. A dependency's `input_dir` is read while its own modules
/// elaborate, and a project-wide `build` / `ci-verify` builds those modules too, so a key that
/// only named the root package's inputs would hand back a green verdict after an edit under
/// `.lake/packages/<dep>/`.
///
/// Projects whose Lake config declares no file inputs are not touched at all (their keys stay
/// byte-identical); a config that does declare them but cannot be resolved statically fails
/// closed rather than yielding a key that silently drops the inputs.
pub(crate) fn update_with_lake_input_digests(
    hasher: &mut blake3::Hasher,
    project_dir: &Path,
) -> Result<()> {
    if !crate::module_builder::workspace_may_declare_lake_inputs(project_dir) {
        return Ok(());
    }
    let cfg = crate::module_builder::resolve_project_config(project_dir).with_context(|| {
        format!(
            "Lake config of {} declares file inputs but does not resolve statically: fail-closed static Lake config gate",
            project_dir.display()
        )
    })?;
    let digest = crate::module_builder::workspace_lake_inputs_digest(&cfg)?;
    hasher.update(b"lake-inputs-v2\n");
    hasher.update(digest.as_bytes());
    Ok(())
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
    // v3: `module_full` outputs must come from kernel-replayed (non-toolchain) modules; v2
    // outputs predate the replay. The provenance versions retire outputs across later bumps.
    // v7: bind canonical workspace Lake config digest, global C-emission flags, custom CC env,
    // and full native/package `.lake/build` outputs.
    hasher.update(b"turbo-lean-build-v7\n");

    hasher.update(&crate::zygote::ZYGOTE_SCANNER_VERSION.to_le_bytes());
    hasher.update(&crate::zygote::ZYGOTE_REPLAY_VERSION.to_le_bytes());
    hasher.update(toolchain.as_bytes());
    hasher.update(b"\n");
    hasher.update(trust_domain.as_bytes());
    hasher.update(b"\n");
    hasher.update(if crate::module_builder::global_emit_c_enabled() {
        b"emit_c:1\n"
    } else {
        b"emit_c:0\n"
    });
    let cc_tag = crate::module_builder::custom_cc_env_digest_tag();
    if !cc_tag.is_empty() {
        hasher.update(b"cc:");
        hasher.update(cc_tag.as_bytes());
        hasher.update(b"\n");
    }
    let effective_targets: Vec<String>;
    let targets_for_hash: &[String] = if has_lake_config(project_dir) {
        let cfg = crate::module_builder::resolve_project_config_with_trust(
            project_dir,
            trust_domain.starts_with("untrusted"),
        )
        .with_context(|| {
            format!(
                "Static Lake config validation failed for {}",
                project_dir.display()
            )
        })?;
        hasher.update(b"ws_cfg:");
        hasher.update(cfg.canonical_config_digest.as_bytes());
        hasher.update(b"\n");
        let inputs_digest = crate::module_builder::workspace_lake_inputs_digest(&cfg)?;
        if !inputs_digest.is_empty() {
            hasher.update(b"ws_inputs:");
            hasher.update(inputs_digest.as_bytes());
        }
        effective_targets = crate::module_builder::normalize_build_targets(&cfg, targets);
        if !trust_domain.starts_with("untrusted") {
            let (exe_targets, _) =
                crate::module_builder::resolve_requested_exe_link_targets(&cfg, &effective_targets);
            if !exe_targets.is_empty() {
                hasher.update(b"exe_link:v1\n");
                for exe_t in &exe_targets {
                    hasher.update(exe_t.lake_spec.as_bytes());
                    hasher.update(b"->");
                    let rel_bin = exe_t
                        .binary_path
                        .strip_prefix(project_dir)
                        .unwrap_or(&exe_t.binary_path);
                    hasher.update(rel_bin.to_string_lossy().as_bytes());
                    hasher.update(b"\n");
                }
            }
        }
        &effective_targets
    } else {
        targets
    };

    for t in targets_for_hash {
        hasher.update(t.as_bytes());
        hasher.update(b",");
    }
    hasher.update(b"\n");

    for cfg_name in ["lakefile.toml", "lakefile.lean", "lake-manifest.json"] {
        if let Ok(bytes) = fs::read(project_dir.join(cfg_name)) {
            let cfg_hash = blake3::hash(&bytes);
            hasher.update(cfg_name.as_bytes());
            hasher.update(b":");
            hasher.update(cfg_hash.as_bytes());
            hasher.update(b"\n");
        }
    }
    for cand in crate::module_builder::workspace_lake_config_candidates(project_dir)? {
        if let Ok(bytes) = fs::read(&cand) {
            let rel = cand.strip_prefix(project_dir).unwrap_or(&cand);
            hasher.update(b"cand:");
            hasher.update(rel.to_string_lossy().as_bytes());
            hasher.update(b":");
            hasher.update(blake3::hash(&bytes).as_bytes());
            hasher.update(b"\n");
        }
    }
    hasher.update(std::env::consts::OS.as_bytes());
    hasher.update(b"-");
    hasher.update(std::env::consts::ARCH.as_bytes());
    hasher.update(b"\n");
    let allowed = splitter::allowed_axioms();
    if allowed.len() > splitter::STANDARD_AXIOMS.len() {
        hasher.update(b":axioms:");
        hasher.update(allowed.join(",").as_bytes());
        hasher.update(b"\n");
    }
    for (tag, env_key) in [
        ("csimp", "TURBO_LEAN_ALLOWED_CSIMP"),
        ("unsafe", "TURBO_LEAN_ALLOWED_UNSAFE"),
        ("implemented_by", "TURBO_LEAN_ALLOWED_IMPLEMENTED_BY"),
    ] {
        if let Ok(val) = std::env::var(env_key) {
            let trimmed = val.trim();
            if !trimmed.is_empty() {
                hasher.update(format!(":{tag}:{trimmed}\n").as_bytes());
            }
        }
    }
    update_with_lake_input_digests(&mut hasher, project_dir)?;

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

    if !targets.is_empty() {
        let mut selected_dep_names: HashSet<String> = HashSet::new();
        if let Ok(cfg) = crate::module_builder::resolve_project_config(project_dir) {
            for raw_t in targets {
                let mut t = raw_t.trim();
                if let Some(rest) = t.strip_prefix('@') {
                    t = rest;
                } else if let Some(rest) = t.strip_prefix('+') {
                    t = rest;
                }
                if let Some((base, _)) = t.rsplit_once(':') {
                    t = base;
                }
                if let Some((pkg_part, _)) = t.split_once('/') {
                    let clean_p = crate::module_builder::clean_lake_ident(pkg_part);
                    if cfg.dep_pkgs.iter().any(|d| d.name == clean_p) {
                        selected_dep_names.insert(clean_p);
                    }
                } else {
                    let clean_item = crate::module_builder::clean_lake_ident(t);
                    for dp in &cfg.dep_pkgs {
                        if dp.libs.iter().any(|l| l.name == clean_item) {
                            selected_dep_names.insert(dp.name.clone());
                        }
                    }
                }
            }
            if !selected_dep_names.is_empty() {
                for dp in &cfg.dep_pkgs {
                    if !selected_dep_names.contains(&dp.name) || !dp.pkg_root.is_dir() {
                        continue;
                    }
                    let dep_files = collect_project_lean_files(&dp.pkg_root, true, None);
                    if dep_files.is_empty() {
                        continue;
                    }
                    let dep_summary =
                        load_project_stat_summary_cached(store, &dp.pkg_root, &dep_files)?;
                    for lf in &dep_files {
                        let rel = lf.strip_prefix(&dp.pkg_root).unwrap_or(lf);
                        let rel_str = rel.to_string_lossy().replace('\\', "/");
                        let scoped_key = format!("dep:{}:{}", dp.name, rel_str);
                        if let Some(src_hash_hex) = dep_summary.file_hashes.get(&rel_str) {
                            hasher.update(scoped_key.as_bytes());
                            hasher.update(b":");
                            if let Ok(raw) = blake3::Hash::from_hex(src_hash_hex.as_bytes()) {
                                hasher.update(raw.as_bytes());
                            } else {
                                hasher.update(src_hash_hex.as_bytes());
                            }
                            hasher.update(b"\n");
                        }
                        if let Some(ih) = dep_summary.per_file_interfaces.get(&rel_str) {
                            interface_hasher.update(scoped_key.as_bytes());
                            interface_hasher.update(b":");
                            interface_hasher.update(ih.as_bytes());
                            interface_hasher.update(b"\n");
                        }
                    }
                }
            }
        }
    }

    Ok((
        hasher.finalize().to_hex().to_string(),
        interface_hasher.finalize().to_hex().to_string(),
        summary.file_hashes,
    ))
}

/// Zero-read stat-backed file split loader returning `(path, src_blake3_hex, optional_src, SplitResult)`.
#[allow(clippy::type_complexity)]
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

    let mut batch_session = OleanInterfaceBatchSession::new();
    let shm_stat_path = if paths.len() <= 2048 && valid_stats.len() == paths.len() {
        let stat_hash = compute_stat_slice_hash(&valid_stats);
        let p = store
            .fast_staging_dir()
            .join(format!("project_stat_splits_v11_{}.json", &stat_hash[..24]));
        if let Ok(bytes) = fs::read(&p) {
            if let Ok(cached_entries) = serde_json::from_slice::<Vec<ShmCachedFileSplit>>(&bytes) {
                if cached_entries.len() == paths.len()
                    && cached_entries.iter().zip(paths.iter()).all(|(c, path)| {
                        let proj_dir = infer_project_dir_from_lean_file(path);
                        batch_session.compute_hashes(&c.split.imports_header, &proj_dir, None)
                            == c.dep_hashes
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
                        let cur_deps =
                            batch_session.compute_hashes(&c.split.imports_header, &proj_dir, None);
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
            let dep_hashes = batch_session.compute_hashes(&split.imports_header, &proj_dir, None);
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

#[allow(clippy::type_complexity)]
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

    let mut batch_session = OleanInterfaceBatchSession::new();
    let file_deps: Vec<Vec<String>> = files
        .iter()
        .map(|(path, src)| {
            let proj_dir = infer_project_dir_from_lean_file(path);
            batch_session.compute_hashes(src, &proj_dir, None)
        })
        .collect();

    let file_keys: Vec<(String, String)> = par_map_indexed(files.len(), 8, default_workers, |i| {
        let sb = blake3::hash(files[i].1.as_bytes()).to_hex().to_string();
        let fk = compute_file_split_key_with_deps(&sb, &file_deps[i]);
        (sb, fk)
    });

    let shm_proj_path = if files.len() <= 128 {
        let mut ch = blake3::Hasher::new();
        ch.update(b"project-content-splits:v12\n");
        for (_, fk) in &file_keys {
            ch.update(fk.as_bytes());
            ch.update(b"\n");
        }
        let p = store.fast_staging_dir().join(format!(
            "project_splits_v12_{}.json",
            &ch.finalize().to_hex()[..24]
        ));
        if let Ok(bytes) = fs::read(&p) {
            if let Ok(cached_splits) = serde_json::from_slice::<Vec<splitter::SplitResult>>(&bytes)
            {
                if cached_splits.len() == files.len() {
                    let out: Vec<(PathBuf, String, String, splitter::SplitResult)> = files
                        .iter()
                        .cloned()
                        .zip(file_keys)
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
            .join(format!("project_stat_splits_v11_{}.json", &stat_hash[..24]));
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
fn entry_import_pins_current(
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

fn entry_import_pins_fresh_for_build(
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

fn verify_project_module_entry_and_sidecars(
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
    if crate::splitter::source_may_execute_elab_host_effects(&src_raw, false) {
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
    let lib_lean_dir = canon_dir.join(".lake/build/lib/lean");
    let rel_slash = olean_path
        .strip_prefix(&lib_lean_dir)
        .unwrap_or(&olean_path)
        .with_extension("")
        .to_string_lossy()
        .replace('\\', "/");
    let mod_name = rel_slash.replace('/', ".");
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
            if !replay_batch.is_replayed_in_store(store, &cfg, &lean_path, &olean_path) {
                return false;
            }
            if let Ok((imps, _)) =
                crate::module_builder::read_olean_binary_imports_cached(&olean_path)
            {
                worklist.extend(imps.into_iter().map(|i| i.module));
            }
        }
    }
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
        if !replay_batch.is_replayed_in_store(store, &cfg, &lean_path, &path) {
            return false;
        }
        let Ok((imps, _)) = crate::module_builder::read_olean_binary_imports_cached(&path) else {
            return false;
        };
        worklist.extend(imps.into_iter().map(|i| i.module));
    }
    true
}

fn infer_module_name_from_olean_path(
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

fn ensure_olean_roots_and_imports_replayed_in_store(
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

fn ensure_materialized_outputs_replayed_in_store(
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
            let fname = p.file_name().and_then(|s| s.to_str()).unwrap_or("");
            if p.extension().and_then(|s| s.to_str()) == Some("lean")
                && !fname.starts_with(".turbo_statement_dump_")
                && (include_lakefile || fname != "lakefile.lean")
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

#[cfg(test)]
pub(crate) fn resolve_prebuilt_module_import(
    canon_project_dir: &Path,
    canon_file: &Path,
) -> Option<String> {
    resolve_prebuilt_module_import_with_path(canon_project_dir, canon_file).map(|(m, _)| m)
}

fn resolve_prebuilt_module_import_with_path(
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

fn verify_module_olean_and_imports_replayed_in_store(
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

fn remove_module_node_artifacts(node: &crate::module_builder::ModuleNode) {
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

fn collect_workspace_sorry_taint(
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

fn purge_workspace_sorry_artifacts_and_manifest(
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

fn remove_file_if_present_checked(path: &Path) -> Result<()> {
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

fn remove_build_artifacts_in_dirs_checked(
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

fn remove_module_build_artifacts_checked(canon_dir: &Path, rel_slash: &str) -> Result<()> {
    let lib_lean_dir = canon_dir.join(".lake/build/lib/lean");
    let ir_dir = canon_dir.join(".lake/build/ir");
    remove_build_artifacts_in_dirs_checked(&lib_lean_dir, &ir_dir, rel_slash)
}

fn remove_module_build_artifacts(canon_dir: &Path, rel_slash: &str) {
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
    let Ok(cfg) = crate::module_builder::resolve_project_config(canon_dir) else {
        return modules.to_vec();
    };
    let any_inputs =
        !cfg.root_pkg.inputs.is_empty() || cfg.dep_pkgs.iter().any(|dp| !dp.inputs.is_empty());
    let any_matching_exe = modules
        .iter()
        .any(|m| !crate::module_builder::exe_targets_for_module(&cfg, m).is_empty());
    if !any_inputs && !any_matching_exe {
        return modules.to_vec();
    }
    let mut input_lib_targets: Vec<String> = Vec::new();
    let mut other_targets: Vec<String> = Vec::new();
    for m in modules {
        let libs = if any_inputs {
            crate::module_builder::input_bearing_libs_for_module(&cfg, m)
        } else {
            Vec::new()
        };
        let exes = crate::module_builder::exe_targets_for_module(&cfg, m);
        input_lib_targets.extend(libs.iter().cloned());
        if libs.is_empty() && exes.is_empty() {
            other_targets.push(m.clone());
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

struct DiscoveredRootImportMod {
    mod_name: String,
    imp_slash: String,
    dep_src: PathBuf,
    dep_olean: PathBuf,
    is_lake_target: bool,
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

fn ensure_project_imports_fresh_inner(
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
        let src_elab_host_effects_stale = !verify_only
            && olean_meta.is_some()
            && fs::read_to_string(&info.dep_src)
                .map(|s| crate::splitter::source_may_execute_elab_host_effects(&s, false))
                .unwrap_or(true);

        let pkg_inputs_stale = !verify_only
            && root_lake_inputs_stale
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
                            || m.lake_inputs_digest != expected_lake_inputs
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
                            || e.lake_inputs_digest != expected_lake_inputs
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
                                    entry_import_pins_fresh_for_build(m, e, hdr, &mut closure_cache)
                                })))
                    }
                    None => {
                        !verify_only
                            && has_lake_inputs
                            && (olean_meta.is_some()
                                || (info.is_lake_target && root_pkg_has_inputs))
                    }
                },
                (None, _) => !verify_only && info.is_lake_target && root_pkg_has_inputs,
                _ => false,
            };
        let lake_root_stale = info.is_lake_target
            && !has_manifest_entry
            && olean_meta.is_some()
            && root_cfg.as_ref().is_some_and(|cfg| {
                crate::module_builder::root_pkg_lake_module_stale(
                    cfg,
                    &mut closure_cache,
                    &info.mod_name,
                )
            });
        let opt_out = worktree_auto_link_disabled(canon_dir);
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
        if src_elab_host_effects_stale
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
            lake_build_modules_opts(
                canon_dir,
                &lake_refresh_targets(canon_dir, &lake_targets),
                rev,
                bypass_lake_cache,
            )?;
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

fn lake_build_modules_opts(
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

/// The files of `files` whose edit against git revision `rev` is not local, i.e. changes more than
/// theorem proof bodies (proof irrelevance makes those invisible to other declarations). Files
/// new since `rev` are not local. Outside a git repository nothing is reported.
pub(crate) fn nonlocal_edits(files: &[PathBuf], rev: &str) -> Vec<String> {
    let is_nonlocal = |f: &PathBuf| {
        let Ok(cur) = fs::read_to_string(f) else {
            return false;
        };
        let name = f.file_name().unwrap_or_default().to_string_lossy();
        let parent = f.parent().unwrap_or(Path::new("."));
        let Ok(mut git) = crate::trusted_tools::git(parent) else {
            return true; // A missing trusted Git must invalidate reuse.
        };
        let base = git
            .arg("-C")
            .arg(f.parent().unwrap_or(Path::new(".")))
            .args(["show", "--no-textconv", "--no-ext-diff"])
            .arg(format!("{}:./{}", rev, name))
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).into_owned());
        let Some(base) = base else {
            // New since `rev` (inside a repository); outside git there is no edit to classify.
            return crate::trusted_tools::git(parent)
                .map(|mut git| {
                    git.arg("-C")
                        .arg(parent)
                        .args(["rev-parse", "--is-inside-work-tree"])
                        .output()
                        .is_ok_and(|o| o.status.success())
                })
                .unwrap_or(true);
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

#[derive(Clone, Debug)]
struct StandaloneModuleSpec {
    module_name: String,
    src_path: PathBuf,
    src_root: PathBuf,
    is_module: bool,
    imports: Vec<String>,
    import_visibilities: HashMap<String, crate::module_builder::DepImportVisibility>,
}

struct ProjectDependentClosure {
    cfg: crate::module_builder::ProjectConfig,
    dag: Option<crate::module_builder::ModuleDag>,
    dag_seeds: Vec<String>,
    lake_seeds: Vec<String>,
    edited_dag_modules: Vec<String>,
    deleted_modules: Vec<String>,
    dag_modules: Option<Vec<String>>,
    dag_files: Option<Vec<PathBuf>>,
    standalone_all: BTreeMap<String, StandaloneModuleSpec>,
    standalone_modules: Vec<StandaloneModuleSpec>,
}

fn package_source_roots(
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

fn discover_standalone_project_modules(
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

fn compute_project_dependent_closure(
    canon_dir: &Path,
    edits: &[String],
    is_untrusted: bool,
) -> Result<ProjectDependentClosure> {
    compute_project_dependent_closure_inner(canon_dir, edits, is_untrusted, is_untrusted)
}

fn compute_project_dependent_closure_inner(
    canon_dir: &Path,
    edits: &[String],
    is_untrusted: bool,
    strict_graph: bool,
) -> Result<ProjectDependentClosure> {
    let cfg = crate::module_builder::resolve_project_config_with_trust(canon_dir, is_untrusted)?;
    let roots = package_source_roots(canon_dir, &cfg.root_pkg);
    let root_base = crate::module_builder::pkg_target_base_name(&cfg.root_pkg);
    let mut dag_seeds: Vec<String> = cfg
        .root_pkg
        .libs
        .iter()
        .map(|l| format!("@{}/{}", root_base, l.name))
        .collect();
    let mut lake_seeds: Vec<String> = cfg.root_pkg.libs.iter().map(|l| l.name.clone()).collect();
    for exe in &cfg.root_pkg.exes {
        let exe_dag_target = format!("@{}/{}:default", root_base, exe.name);
        if !dag_seeds.contains(&exe_dag_target) {
            dag_seeds.push(exe_dag_target);
        }
        let exe_lake_target = format!("@{}/{}:exe", root_base, exe.name);
        if !lake_seeds.contains(&exe_lake_target) {
            lake_seeds.push(exe_lake_target);
        }
    }
    let edited: HashSet<PathBuf> = edits
        .iter()
        .map(|e| canon_dir.join(e))
        .map(|p| p.canonicalize().unwrap_or(p))
        .collect();
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
    let standalone_all = discover_standalone_project_modules(
        canon_dir,
        &cfg,
        dag_opt.as_ref(),
        &edited,
        is_untrusted,
        strict_graph,
    )?;

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

fn topologically_order_standalone_modules(
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
    _scratch: crate::check::PrivateScratchDir,
}

#[allow(clippy::too_many_arguments)]
fn check_and_audit_standalone_modules(
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
                        let rs = r.to_string_lossy();
                        rs.strip_suffix(".olean.server")
                            .or_else(|| rs.strip_suffix(".olean.private"))
                            .or_else(|| rs.strip_suffix(".olean"))
                            .or_else(|| rs.strip_suffix(".ilean"))
                            .map(String::from)
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
                    if pkg_preserve_lake || fs::hard_link(&p, &dst_p).is_err() {
                        fs::copy(&p, &dst_p)?;
                    }
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
                std::time::Duration::from_secs(300),
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
        for spec in standalone_modules {
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
                std::time::Duration::from_secs(300),
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
            .map(|s| s.module_name.clone())
            .collect();
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
        eprintln!(
            "[turbo-lean] non-local edit in {}: re-checking dependents with Lake",
            edits.join(", ")
        );
        let (n, rechecked_files, rechecked_mods, _overlay) = if allow_sorry {
            lake_recheck_dependents_with_store_and_options(None, &dir, &edits, None, false, true)?
        } else {
            lake_recheck_dependents_with_store(Some(store), &dir, &edits, None, false)?
        };
        if allow_sorry {
            // Replay only clean modules; purge Lake `.olean` / `.ir` / `.c` artifacts and manifest
            // entries for any module whose source contains `sorry` (or transitively imports a
            // sorry-bearing module across the full DAG + standalone graph, including non-root `srcDir`).
            let mut seed_files = rechecked_files.clone();
            seed_files.push(file.clone());
            for e in &edits {
                seed_files.push(dir.join(e));
            }
            let sorry_mod_set =
                purge_workspace_sorry_artifacts_and_manifest(&dir, &seed_files, &rechecked_mods);
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
            ensure_modules_and_imports_replayed(store, &dir, &rechecked_files, &rechecked_mods)?;
        }
        eprintln!(
            "[turbo-lean] Lake re-checked {} modules (0: all libraries)",
            n
        );
    } else if lake_inputs_changed_since_manifest(&dir) {
        if let Ok(cfg) = crate::module_builder::resolve_project_config(&dir) {
            let root_base = crate::module_builder::pkg_target_base_name(&cfg.root_pkg);
            let mut input_libs: Vec<String> = Vec::new();
            let mut input_exes: Vec<String> = Vec::new();
            let mut input_exe_dag_seeds: Vec<String> = Vec::new();
            if !cfg.root_pkg.inputs.is_empty() {
                input_libs.extend(
                    cfg.root_pkg
                        .libs
                        .iter()
                        .filter(|l| !l.needs.is_empty())
                        .map(|l| l.name.clone()),
                );
                for e in cfg.root_pkg.exes.iter().filter(|e| !e.needs.is_empty()) {
                    input_exes.push(format!("@{}/{}:exe", root_base, e.name));
                    input_exe_dag_seeds.push(format!("@{}/{}:default", root_base, e.name));
                }
            }
            for dp in &cfg.dep_pkgs {
                if !dp.inputs.is_empty() {
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
            if (!input_libs.is_empty() || !input_exes.is_empty()) && has_lake_config(&dir) {
                let mut lib_seeds: Vec<String> =
                    cfg.root_pkg.libs.iter().map(|l| l.name.clone()).collect();
                lib_seeds.extend(input_libs.iter().cloned());
                lib_seeds.sort();
                lib_seeds.dedup();

                let mut dag_seeds: Vec<String> = cfg
                    .root_pkg
                    .libs
                    .iter()
                    .map(|l| format!("@{}/{}", root_base, l.name))
                    .collect();
                dag_seeds.extend(input_libs.iter().cloned());
                dag_seeds.extend(
                    cfg.root_pkg
                        .exes
                        .iter()
                        .map(|e| format!("@{}/{}:default", root_base, e.name)),
                );
                dag_seeds.extend(input_exe_dag_seeds);
                dag_seeds.sort();
                dag_seeds.dedup();

                let mut lake_exe_seeds: Vec<String> = cfg
                    .root_pkg
                    .exes
                    .iter()
                    .map(|e| format!("@{}/{}:exe", root_base, e.name))
                    .collect();
                lake_exe_seeds.extend(input_exes.iter().cloned());
                lake_exe_seeds.sort();
                lake_exe_seeds.dedup();

                let mut ordered_targets = input_libs.clone();
                let closure_files: Vec<PathBuf>;
                let closure_mods: Vec<String>;
                if let Ok(dag) =
                    crate::module_builder::build_module_dag_with_trust(&cfg, &dag_seeds, false)
                {
                    let mut closure: std::collections::BTreeSet<String> = dag
                        .nodes
                        .keys()
                        .filter(|m| {
                            !crate::module_builder::input_bearing_libs_for_module(&cfg, m)
                                .is_empty()
                                || !crate::module_builder::input_bearing_exes_for_module(&cfg, m)
                                    .is_empty()
                        })
                        .cloned()
                        .collect();
                    let mut changed = !closure.is_empty();
                    while changed {
                        changed = false;
                        for (m, n) in &dag.nodes {
                            if !closure.contains(m)
                                && n.direct_dag_deps.iter().any(|d| closure.contains(d))
                            {
                                closure.insert(m.clone());
                                changed = true;
                            }
                        }
                    }
                    closure_files = closure
                        .iter()
                        .filter_map(|m| dag.nodes.get(m).map(|n| n.src_path.clone()))
                        .collect();
                    closure_mods = closure.into_iter().collect();
                    for t in lake_refresh_targets(&dir, &closure_mods) {
                        if !ordered_targets.contains(&t) {
                            ordered_targets.push(t);
                        }
                    }
                    for t in input_exes {
                        if !ordered_targets.contains(&t) {
                            ordered_targets.push(t);
                        }
                    }
                } else {
                    for t in lib_seeds.into_iter().chain(lake_exe_seeds) {
                        if !ordered_targets.contains(&t) {
                            ordered_targets.push(t);
                        }
                    }
                    closure_files = collect_project_lean_files(&dir, false, None);
                    closure_mods = closure_files
                        .iter()
                        .filter_map(|f| f.strip_prefix(&dir).ok())
                        .map(|r| r.with_extension("").to_string_lossy().replace('/', "."))
                        .collect();
                }

                eprintln!(
                    "[turbo-lean] Lake file inputs changed: re-checking input-bearing targets and dependents ({}) with Lake",
                    ordered_targets.join(", ")
                );
                lake_build_modules(&dir, &ordered_targets, None)?;
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
                } else {
                    ensure_modules_and_imports_replayed(
                        store,
                        &dir,
                        &closure_files,
                        &closure_mods,
                    )?;
                }
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
    } else if allow_sorry && !worktree_auto_link_disabled(&dir) {
        // Even when `nonlocal_edits` is empty (e.g. a sorry-bearing upstream import was
        // already committed at `HEAD` and refreshed by `ensure_project_imports_fresh_for_check`),
        // purge any sorry-tainted workspace `.olean` / `.ir` / `.c` artifacts and manifest entries.
        let _ =
            purge_workspace_sorry_artifacts_and_manifest(&dir, std::slice::from_ref(&file), &[]);
    }
    Ok(())
}

fn read_git_baseline_source(src_path: &Path, rev: &str) -> Option<String> {
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

fn read_git_baseline_source_checked(
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
struct PreRebuildModuleBaseline {
    full_dig: String,
    export_dig: String,
    meta_dig: String,
    lake_export_info: Option<crate::module_builder::LakeModuleExportInfo>,
    ir_pair_dig: Option<([u8; 32], Option<[u8; 32]>)>,
    olean_pub_sig: crate::zygote::OleanPublicSignatureReply,
    base_pub_sig_digest: Option<String>,
    base_meta_sig_digest: Option<String>,
    cur_pub_sig_digest: String,
    cur_meta_sig_digest: String,
}

fn read_module_ir_pair_digest(olean_path: &Path) -> Option<([u8; 32], Option<[u8; 32]>)> {
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
struct ModuleCutoffVerdict {
    cuts_off_public: bool,
    cuts_off_meta: bool,
}

fn capture_pre_rebuild_module_baselines(
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

fn evaluate_post_rebuild_module_cutoffs(
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

fn load_pre_rebuild_root_manifest(
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
fn compute_stage2_dependent_closure_after_cutoff(
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
    let mut closure_cache = LakeClosureCache::default();
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
fn refresh_cutoff_shielded_manifest_and_traces(
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

fn stamp_manifest_after_lake_cutoff_rebuild(
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
        if hygiene.has_sorry
            || hygiene.has_axiom
            || hygiene.native_violation()
            || hygiene.has_trust_compiler
            || hygiene.has_checking_weakening
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

fn node_is_kernel_audited_in_untrusted(
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
            let cutoff_attempted = if !allow_sorry {
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
    let (_standalone_files, overlay) = check_and_audit_standalone_modules(
        store_opt,
        canon_dir,
        &effective_standalone,
        false,
        None,
        rev,
        retain_standalone_oleans,
        allow_sorry,
    )?;
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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImpactReport {
    pub file: String,
    pub module_name: Option<String>,
    pub base_rev: Option<String>,
    pub is_module: bool,
    pub edit_class: String,
    pub public_signature_changed: bool,
    pub meta_signature_changed: bool,
    pub public_signature_digest: String,
    pub meta_signature_digest: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub baseline_public_signature_digest: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub baseline_meta_signature_digest: Option<String>,
    pub direct_dependents: Vec<String>,
    pub transitive_dependents: Vec<String>,
    pub pruned_dependents: Vec<String>,
    pub affected_modules: Vec<String>,
    pub affected_files: Vec<String>,
    pub estimated_declarations: usize,
    pub total_downstream_declarations: usize,
}

pub fn compute_impact_report(
    file: PathBuf,
    project_dir: Option<PathBuf>,
    rev: Option<String>,
) -> Result<ImpactReport> {
    let target_canon = file
        .canonicalize()
        .with_context(|| format!("Target file does not exist: {}", file.display()))?;
    anyhow::ensure!(
        target_canon.is_file(),
        "`turbo-lean impact` expects a `.lean` file path, got directory: {}",
        target_canon.display()
    );
    let root_guess = match project_dir {
        Some(p) => p,
        None => find_project_root(&target_canon),
    };
    let canon_dir = root_guess
        .canonicalize()
        .unwrap_or_else(|_| root_guess.clone());
    let rel_file = target_canon
        .strip_prefix(&canon_dir)
        .map(|p| p.to_string_lossy().replace('\\', "/"))
        .unwrap_or_else(|_| target_canon.to_string_lossy().replace('\\', "/"));

    let cur_src = fs::read_to_string(&target_canon)
        .with_context(|| format!("Failed to read {}", target_canon.display()))?;
    let cur_sig = splitter::extract_public_signature(&cur_src);
    let cur_split = split_lean_source(&cur_src, &[]);

    let explicit_rev = rev.is_some();
    let effective_rev = match rev {
        Some(r) => Some(r),
        None => {
            if canon_dir.join(".git").exists()
                || target_canon.ancestors().any(|a| a.join(".git").exists())
            {
                Some("HEAD".to_string())
            } else {
                None
            }
        }
    };
    let baseline_src = match effective_rev.as_deref() {
        Some(r) => read_git_baseline_source_checked(&target_canon, r, explicit_rev)?,
        None => None,
    };

    let (
        edit_class,
        pub_changed,
        meta_changed,
        base_pub_dig,
        base_meta_dig,
        cuts_off_pub,
        cuts_off_meta,
    ) = if let Some(ref b_src) = baseline_src {
        if b_src == &cur_src {
            (
                "unchanged".to_string(),
                false,
                false,
                Some(cur_sig.public_signature_digest.clone()),
                Some(cur_sig.meta_signature_digest.clone()),
                true,
                true,
            )
        } else {
            let base_split = split_lean_source(b_src, &[]);
            let base_sig = splitter::extract_public_signature(b_src);
            let proof_body_only = base_split.interface_hash == cur_split.interface_hash
                && base_split.shards.len() == cur_split.shards.len()
                && base_split
                    .shards
                    .iter()
                    .zip(cur_split.shards.iter())
                    .all(|(a, b)| a.decl_name() == b.decl_name() && a.stmt_hash == b.stmt_hash)
                && !cur_sig
                    .public_signature_digest
                    .starts_with("pubsig-invalid:")
                && !base_sig
                    .public_signature_digest
                    .starts_with("pubsig-invalid:")
                && cur_sig.public_signature_digest == base_sig.public_signature_digest
                && cur_sig.meta_signature_digest == base_sig.meta_signature_digest;
            if proof_body_only {
                (
                    "proof_body_only".to_string(),
                    false,
                    false,
                    Some(base_sig.public_signature_digest),
                    Some(base_sig.meta_signature_digest),
                    true,
                    true,
                )
            } else if cur_sig.is_module
                && base_sig.is_module
                && !cur_sig
                    .public_signature_digest
                    .starts_with("pubsig-invalid:")
                && !base_sig
                    .public_signature_digest
                    .starts_with("pubsig-invalid:")
                && cur_sig.public_signature_digest == base_sig.public_signature_digest
            {
                let meta_same = cur_sig.meta_signature_digest == base_sig.meta_signature_digest;
                let cls = if meta_same {
                    "private_module_edit"
                } else {
                    "meta_only_module_edit"
                };
                (
                    cls.to_string(),
                    false,
                    !meta_same,
                    Some(base_sig.public_signature_digest),
                    Some(base_sig.meta_signature_digest),
                    true,
                    meta_same,
                )
            } else {
                let pub_diff = cur_sig.public_signature_digest != base_sig.public_signature_digest;
                let meta_diff = cur_sig.meta_signature_digest != base_sig.meta_signature_digest;
                let cls = if cur_sig.is_module {
                    "public_signature_edit"
                } else {
                    "non_module_interface_edit"
                };
                (
                    cls.to_string(),
                    pub_diff || !cur_sig.is_module,
                    meta_diff || !cur_sig.is_module,
                    Some(base_sig.public_signature_digest),
                    Some(base_sig.meta_signature_digest),
                    false,
                    false,
                )
            }
        }
    } else {
        let cls = if cur_sig.is_module {
            "unbaselined_module"
        } else {
            "unbaselined_non_module"
        };
        (cls.to_string(), true, true, None, None, false, false)
    };

    let mut module_name: Option<String> = None;
    let mut direct_dependents: Vec<String> = Vec::new();
    let mut full_dependents: Vec<String> = Vec::new();
    let mut active_dependents: Vec<String> = Vec::new();
    let mut pruned_dependents: Vec<String> = Vec::new();
    let mut affected_modules: Vec<String> = Vec::new();
    let mut affected_files: Vec<String> = Vec::new();
    let mut mod_to_path: HashMap<String, PathBuf> = HashMap::new();

    if has_lake_config(&canon_dir) {
        let closure = compute_project_dependent_closure_inner(
            &canon_dir,
            std::slice::from_ref(&rel_file),
            false,
            true,
        )?;
        if let Some(m) = closure.edited_dag_modules.first() {
            module_name = Some(m.clone());
        } else {
            for (m, s) in &closure.standalone_all {
                if s.src_path == target_canon {
                    module_name = Some(m.clone());
                    break;
                }
            }
        }
        if let Some(ref dag) = closure.dag {
            for (m, n) in &dag.nodes {
                mod_to_path.insert(m.clone(), n.src_path.clone());
            }
        }
        for (m, s) in &closure.standalone_all {
            mod_to_path
                .entry(m.clone())
                .or_insert_with(|| s.src_path.clone());
        }

        let target_mod_opt = module_name.clone();
        if let Some(ref target_mod) = target_mod_opt {
            if let Some(ref dag) = closure.dag {
                for (m, n) in &dag.nodes {
                    if m != target_mod && n.direct_dag_deps.iter().any(|d| d == target_mod) {
                        direct_dependents.push(m.clone());
                    }
                }
            }
            for (m, s) in &closure.standalone_all {
                if m != target_mod && s.imports.iter().any(|d| d == target_mod) {
                    direct_dependents.push(m.clone());
                }
            }
            direct_dependents.sort();
            direct_dependents.dedup();
        }

        let mut full_set: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        if let Some(ref mods) = closure.dag_modules {
            for m in mods {
                if module_name.as_deref() != Some(m.as_str()) {
                    full_set.insert(m.clone());
                }
            }
        }
        for s in &closure.standalone_modules {
            if module_name.as_deref() != Some(s.module_name.as_str()) {
                full_set.insert(s.module_name.clone());
            }
        }
        full_dependents = full_set.iter().cloned().collect();

        if edit_class == "unchanged" {
            pruned_dependents = full_dependents.clone();
        } else if edit_class == "proof_body_only" {
            if let Some(ref tm) = target_mod_opt {
                affected_modules.push(tm.clone());
            }
            affected_files.push(rel_file.clone());
            pruned_dependents = full_dependents.clone();
        } else if let Some(dag) = closure
            .dag
            .as_ref()
            .filter(|_| cuts_off_pub && !closure.edited_dag_modules.is_empty())
        {
            let mut verdicts = HashMap::new();
            for m in &closure.edited_dag_modules {
                verdicts.insert(
                    m.clone(),
                    ModuleCutoffVerdict {
                        cuts_off_public: cuts_off_pub,
                        cuts_off_meta,
                    },
                );
            }
            // For static blast-radius prediction in `impact`, evaluate import-visibility graph
            // pruning purely from source headers (without requiring prebuilt on-disk `.olean`s).
            let shared_lib_mods: HashSet<&str> = dag
                .shared_libs
                .iter()
                .flat_map(|sl| sl.local_modules.iter().map(String::as_str))
                .collect();
            let edited_dag_set: HashSet<&str> = closure
                .edited_dag_modules
                .iter()
                .map(String::as_str)
                .collect();
            let mut dag_dirty: std::collections::BTreeSet<String> =
                closure.edited_dag_modules.iter().cloned().collect();
            let mut standalone_dirty: std::collections::BTreeSet<String> =
                std::collections::BTreeSet::new();
            let mut changed = true;
            while changed {
                changed = false;
                for (m, n) in &dag.nodes {
                    if dag_dirty.contains(m) {
                        continue;
                    }
                    let (vis_map, _) = crate::module_builder::compute_node_dep_visibility_map(
                        &closure.cfg,
                        dag,
                        n,
                    );
                    let trig = n.direct_dag_deps.iter().any(|d| {
                        if standalone_dirty.contains(d) {
                            return true;
                        }
                        if !dag_dirty.contains(d) {
                            return false;
                        }
                        let vis = if !n.is_module
                            || n.precompile_modules
                            || n.is_exe_target
                            || n.needs_dynlib
                            || shared_lib_mods.contains(m.as_str())
                        {
                            crate::module_builder::DepImportVisibility::All
                        } else {
                            vis_map
                                .get(d)
                                .copied()
                                .unwrap_or(crate::module_builder::DepImportVisibility::All)
                        };
                        if edited_dag_set.contains(d.as_str()) {
                            if let Some(v) = verdicts.get(d) {
                                return match vis {
                                    crate::module_builder::DepImportVisibility::PublicExport => {
                                        !v.cuts_off_public
                                    }
                                    crate::module_builder::DepImportVisibility::MetaExport => {
                                        !v.cuts_off_meta
                                    }
                                    crate::module_builder::DepImportVisibility::All => true,
                                };
                            }
                        }
                        true
                    });
                    if trig {
                        dag_dirty.insert(m.clone());
                        changed = true;
                    }
                }
                for (m, s) in &closure.standalone_all {
                    if standalone_dirty.contains(m) {
                        continue;
                    }
                    let trig = s.imports.iter().any(|d| {
                        if standalone_dirty.contains(d) {
                            return true;
                        }
                        if !dag_dirty.contains(d) {
                            return false;
                        }
                        let vis = if !s.is_module {
                            crate::module_builder::DepImportVisibility::All
                        } else {
                            s.import_visibilities
                                .get(d)
                                .copied()
                                .unwrap_or(crate::module_builder::DepImportVisibility::All)
                        };
                        if edited_dag_set.contains(d.as_str()) {
                            if let Some(v) = verdicts.get(d) {
                                return match vis {
                                    crate::module_builder::DepImportVisibility::PublicExport => {
                                        !v.cuts_off_public
                                    }
                                    crate::module_builder::DepImportVisibility::MetaExport => {
                                        !v.cuts_off_meta
                                    }
                                    crate::module_builder::DepImportVisibility::All => true,
                                };
                            }
                        }
                        true
                    });
                    if trig {
                        standalone_dirty.insert(m.clone());
                        changed = true;
                    }
                }
            }
            let mut active_set: std::collections::BTreeSet<String> =
                std::collections::BTreeSet::new();
            for m in dag_dirty.into_iter().chain(standalone_dirty) {
                affected_modules.push(m.clone());
                if module_name.as_deref() != Some(m.as_str()) {
                    active_set.insert(m);
                }
            }
            affected_modules.sort();
            affected_modules.dedup();
            active_dependents = active_set.iter().cloned().collect();
            pruned_dependents = full_set.difference(&active_set).cloned().collect();
        } else {
            if let Some(ref tm) = target_mod_opt {
                affected_modules.push(tm.clone());
            }
            for d in &full_dependents {
                affected_modules.push(d.clone());
            }
            affected_modules.sort();
            affected_modules.dedup();
            active_dependents = full_dependents.clone();
        }
    } else if edit_class != "unchanged" {
        affected_files.push(rel_file.clone());
    }

    if affected_files.is_empty() && !affected_modules.is_empty() {
        for m in &affected_modules {
            if let Some(p) = mod_to_path.get(m) {
                let rel = p
                    .strip_prefix(&canon_dir)
                    .map(|r| r.to_string_lossy().replace('\\', "/"))
                    .unwrap_or_else(|_| p.to_string_lossy().replace('\\', "/"));
                affected_files.push(rel);
            }
        }
        affected_files.sort();
        affected_files.dedup();
    }

    let count_decls_in_path = |p: &Path| -> usize {
        fs::read_to_string(p)
            .ok()
            .map(|s| split_lean_source(&s, &[]).shards.len())
            .unwrap_or(0)
    };
    let mut total_downstream_declarations = 0usize;
    for m in &full_dependents {
        if let Some(p) = mod_to_path.get(m) {
            total_downstream_declarations += count_decls_in_path(p);
        }
    }
    let estimated_declarations = if edit_class == "unchanged" {
        0
    } else if edit_class == "proof_body_only" {
        if let Some(ref b_src) = baseline_src {
            let base_split = split_lean_source(b_src, &[]);
            base_split
                .shards
                .iter()
                .zip(cur_split.shards.iter())
                .filter(|(a, b)| a.proof_hash != b.proof_hash)
                .count()
        } else {
            cur_split.shards.len()
        }
    } else if !affected_modules.is_empty() {
        affected_modules
            .iter()
            .filter_map(|m| mod_to_path.get(m))
            .map(|p| count_decls_in_path(p))
            .sum()
    } else {
        cur_split.shards.len()
    };

    Ok(ImpactReport {
        file: rel_file,
        module_name,
        base_rev: effective_rev,
        is_module: cur_sig.is_module,
        edit_class,
        public_signature_changed: pub_changed,
        meta_signature_changed: meta_changed,
        public_signature_digest: cur_sig.public_signature_digest,
        meta_signature_digest: cur_sig.meta_signature_digest,
        baseline_public_signature_digest: base_pub_dig,
        baseline_meta_signature_digest: base_meta_dig,
        direct_dependents,
        transitive_dependents: active_dependents,
        pruned_dependents,
        affected_modules,
        affected_files,
        estimated_declarations,
        total_downstream_declarations,
    })
}

/// Strictly read-only blast-radius and public-signature impact analyzer (`turbo-lean impact <file>`).
/// Never mutates the worktree, `.lake/build`, or `TurboStore`.
pub fn run_impact_command(
    json: bool,
    file: PathBuf,
    project_dir: Option<PathBuf>,
    rev: Option<String>,
) -> Result<()> {
    let report = compute_impact_report(file, project_dir, rev)?;
    if json {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        println!(
            "[turbo-lean] impact: {} (module: {}, edit_class: {})",
            report.file,
            report.module_name.as_deref().unwrap_or("<standalone>"),
            report.edit_class
        );
        println!(
            "  public_signature_changed: {} | meta_signature_changed: {} | is_module: {}",
            report.public_signature_changed, report.meta_signature_changed, report.is_module
        );
        println!(
            "  dependents: {} direct, {} active transitive ({} pruned by cutoff), ~{} declarations affected ({} total downstream)",
            report.direct_dependents.len(),
            report.transitive_dependents.len(),
            report.pruned_dependents.len(),
            report.estimated_declarations,
            report.total_downstream_declarations
        );
    }
    Ok(())
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

fn classify_lake_build_artifact(
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

fn collect_workspace_bin_dirs(canon_proj: &Path) -> Vec<PathBuf> {
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
fn stage_build_candidates(
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
    sh.update(b"lake-build-ingest:v2\n");
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
            let dur_ms = t0.elapsed().as_millis() as i64;
            let cache_hit = build_report.modules_compiled == 0
                && (build_report.modules_cached > 0 || build_report.modules_up_to_date_reused > 0);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn cached_lake_environments_cannot_supply_verifier_executables() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo-cached-tools-{}-{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        let store = TurboStore::open(Some(&dir.join("store")))?;
        let key = TurboStore::compute_lake_env_key(&dir);
        let poisoned = HashMap::from([
            (
                "PATH".into(),
                dir.join(".lake/build/bin").to_string_lossy().into_owned(),
            ),
            (
                "LAKE".into(),
                dir.join("lake").to_string_lossy().into_owned(),
            ),
            ("LEAN".into(), "lean".into()),
            ("LEANC".into(), "leanc".into()),
        ]);
        store.put_lake_env(&key, &poisoned)?;
        let tools =
            crate::module_builder::ToolchainExecutables::resolve(&dir, &detect_toolchain(&dir))?;
        let (cached, hit) = resolve_lake_env(&store, &dir)?;
        assert!(hit);
        let shared = resolve_or_share_lake_env(&store, &dir, &key)?.unwrap().0;
        for env in [cached, shared] {
            assert_eq!(env["PATH"], tools.path());
            for (name, path) in [
                ("LEAN", &tools.lean),
                ("LAKE", &tools.lake),
                ("LEANC", &tools.leanc),
            ] {
                assert_eq!(env[name], path.to_string_lossy());
            }
        }
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_optout_installed_toolchain_env_child() -> Result<()> {
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
                    err.to_string().contains("fail-closed toolchain gate"),
                    "{err:#}"
                );
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
    fn test_optout_installed_toolchain_preserves_missing_and_stale_lean_config() -> Result<()> {
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
            let lean = PathBuf::from(resolve_lean_bin(&tree.project)?);
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
            if state == "missing-compiler" {
                fs::write(
                    tree.project.join("lean-toolchain"),
                    "leanprover/lean4:v99.99.99\n",
                )?;
            }
            tree.prepare_snapshot(".lake/build/lib/lean/P/A.olean")?;
            let before = snapshot(&tree.project)?;
            let mut command =
                TestChild::command("lake_build::tests::test_optout_installed_toolchain_env_child")?;
            command
                .env("TURBO_TEST_ENV_ROOT", &tree.root)
                .env("PATH", &bin)
                .env("HOME", tree.root.join("isolated/a/b/home"))
                // Register the installed toolchain explicitly; verification never trusts PATH discovery.
                .env(
                    "ELAN_HOME",
                    lean.ancestors().nth(4).expect("installed Elan toolchain"),
                )
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
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let prev_lp = std::env::var_os("LEAN_PATH");
        std::env::remove_var("LEAN_PATH");
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

        let user_tc_dir = tmp_dir.join("toolchains/ext/lib/lean");
        let sysroot_root = tmp_dir.join("fake_lean_prefix");
        let sysroot_lib = sysroot_root.join("lib/lean");
        fs::create_dir_all(user_tc_dir.join("UserPkg")).unwrap();
        fs::create_dir_all(sysroot_root.join("bin")).unwrap();
        fs::create_dir_all(sysroot_lib.join("Init")).unwrap();
        fs::write(sysroot_root.join("bin/lean"), b"stub").unwrap();
        let user_olean = user_tc_dir.join("UserPkg/Mod.olean");
        fs::write(&user_olean, [0x11u8; 128]).unwrap();
        fs::write(sysroot_lib.join("Init/Core.olean"), [0x22u8; 128]).unwrap();
        let mixed_lp = format!("{}:{}", user_tc_dir.display(), sysroot_lib.display());
        let mixed_src = "import UserPkg.Mod\nimport Init.Core\ntheorem t : True := trivial\n";
        let mixed_h1 =
            compute_imported_olean_interface_hashes(mixed_src, Path::new(""), Some(&mixed_lp));
        assert!(mixed_h1.iter().any(|e| e.starts_with("UserPkg.Mod:")));
        assert!(!mixed_h1.iter().any(|e| e.starts_with("Init.Core:")));
        fs::write(&user_olean, [0x33u8; 128]).unwrap();
        let mixed_h2 =
            compute_imported_olean_interface_hashes(mixed_src, Path::new(""), Some(&mixed_lp));
        assert_ne!(mixed_h1, mixed_h2);

        let local_lean_lib = tmp_dir.join(".lake/build/lib/lean");
        fs::create_dir_all(local_lean_lib.join("UserPkg")).unwrap();
        fs::write(local_lean_lib.join("UserPkg/Mod.olean"), [0x77u8; 128]).unwrap();
        let project_first = compute_imported_olean_interface_hashes(mixed_src, &tmp_dir, None);
        assert_ne!(project_first, mixed_h2);
        let project_user_mod = project_first
            .iter()
            .find(|x| x.starts_with("UserPkg.Mod:"))
            .unwrap()
            .clone();
        assert!(!mixed_h2.contains(&project_user_mod));
        let explicit_lp_with_project =
            compute_imported_olean_interface_hashes(mixed_src, &tmp_dir, Some(&mixed_lp));
        assert!(explicit_lp_with_project.contains(&project_user_mod));

        std::env::set_var("LEAN_PATH", &mixed_lp);
        let caller_env_with_project =
            compute_imported_olean_interface_hashes(mixed_src, &tmp_dir, None);
        assert_eq!(caller_env_with_project, explicit_lp_with_project);
        let remote_lp = resolve_remote_lean_path(&tmp_dir, None);
        assert!(remote_lp.starts_with(local_lean_lib.to_string_lossy().as_ref()));
        assert!(remote_lp.contains(user_tc_dir.to_string_lossy().as_ref()));
        assert_eq!(
            compute_imported_olean_interface_hashes(mixed_src, &tmp_dir, Some(&remote_lp)),
            explicit_lp_with_project
        );
        let mut lake_ev = HashMap::new();
        lake_ev.insert(
            "LEAN".to_string(),
            sysroot_root.join("bin/lean").to_string_lossy().to_string(),
        );
        lake_ev.insert(
            "LEAN_PATH".to_string(),
            format!("{}:{}", local_lean_lib.display(), sysroot_lib.display()),
        );
        merge_caller_lean_path(&mut lake_ev);
        assert_eq!(
            lake_ev["LEAN_PATH"],
            format!(
                "{}:{}:{}",
                local_lean_lib.display(),
                user_tc_dir.display(),
                sysroot_lib.display()
            )
        );

        let second_tc_root = tmp_dir.join("second_toolchain");
        let second_tc_lib = second_tc_root.join("lib/lean");
        fs::create_dir_all(second_tc_root.join("bin")).unwrap();
        fs::create_dir_all(second_tc_lib.join("ExtraTc")).unwrap();
        fs::write(second_tc_root.join("bin/lean"), b"stub").unwrap();
        let extra_tc_olean = second_tc_lib.join("ExtraTc/Mod.olean");
        fs::write(&extra_tc_olean, [0x91u8; 128]).unwrap();
        let extra_src = "import ExtraTc.Mod\ntheorem t : True := trivial\n";
        let extra_lp = second_tc_lib.to_string_lossy().to_string();
        let extra_h1 =
            compute_imported_olean_interface_hashes(extra_src, &tmp_dir, Some(&extra_lp));
        assert!(extra_h1.iter().any(|e| e.starts_with("ExtraTc.Mod:")));
        fs::write(&extra_tc_olean, [0x92u8; 128]).unwrap();
        let extra_h2 =
            compute_imported_olean_interface_hashes(extra_src, &tmp_dir, Some(&extra_lp));
        assert_ne!(extra_h1, extra_h2);

        let pkg_root_first = tmp_dir.join("pkg_root_first");
        let pkg_root_second = tmp_dir.join("pkg_root_second");
        fs::create_dir_all(pkg_root_first.join("ShadowPkg")).unwrap();
        fs::create_dir_all(pkg_root_second.join("ShadowPkg")).unwrap();
        let shadowed_olean = pkg_root_second.join("ShadowPkg/Sub.olean");
        fs::write(&shadowed_olean, [0xA1u8; 128]).unwrap();
        let shadow_lp = format!("{}:{}", pkg_root_first.display(), pkg_root_second.display());
        let shadow_src = "import ShadowPkg.Sub\ntheorem t : True := trivial\n";
        let shadow_h1 =
            compute_imported_olean_interface_hashes(shadow_src, &tmp_dir, Some(&shadow_lp));
        assert_eq!(shadow_h1, vec!["ShadowPkg.Sub:missing".to_string()]);
        fs::write(&shadowed_olean, [0xA2u8; 128]).unwrap();
        let shadow_h2 =
            compute_imported_olean_interface_hashes(shadow_src, &tmp_dir, Some(&shadow_lp));
        assert_eq!(shadow_h1, shadow_h2);
        let first_olean = pkg_root_first.join("ShadowPkg/Sub.olean");
        fs::write(&first_olean, [0xB1u8; 128]).unwrap();
        let shadow_h3 =
            compute_imported_olean_interface_hashes(shadow_src, &tmp_dir, Some(&shadow_lp));
        assert_ne!(shadow_h3, shadow_h1);
        assert!(shadow_h3[0].starts_with("ShadowPkg.Sub:"));
        assert!(!shadow_h3[0].ends_with(":missing"));

        match prev_lp {
            Some(v) => std::env::set_var("LEAN_PATH", v),
            None => std::env::remove_var("LEAN_PATH"),
        }
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
                lake_inputs_digest: crate::module_builder::workspace_lake_inputs_digest(&cfg)?,
                workspace_config_digest: cfg.canonical_config_digest.clone(),
                allowed_axioms: crate::splitter::allowed_axioms(),
                kernel_policy_digest: crate::splitter::current_kernel_policy_digest(),
                modules: std::collections::BTreeMap::from([(
                    "P/A.lean".into(),
                    crate::module_builder::VerifiedDepModuleEntry {
                        src_blake3: "previous source".into(),
                        olean_artifact_digest: "previous artifact".into(),
                        lake_inputs_digest: crate::module_builder::workspace_lake_inputs_digest(
                            &cfg,
                        )?,
                        kernel_audited: true,
                        import_olean_digests: Default::default(),
                        artifact_stat_fingerprint: String::new(),
                        ..Default::default()
                    },
                )]),
                ..Default::default()
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
        for manifest_backed in [false, true] {
            let tree = LakeTree::imports("missing_trace")?;
            let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
            if manifest_backed {
                crate::module_builder::build_project_modules_native(
                    &mut store,
                    &tree.project,
                    &["P.Middle".into()],
                    "trusted-internal",
                    1,
                    false,
                    true,
                    None,
                )?;
                assert!(verified_sources_manifest_path(&tree.project).is_file());
            } else {
                assert!(!verified_sources_manifest_path(&tree.project).exists());
            }
            fs::remove_file(tree.project.join(".lake/build/lib/lean/P/A.trace"))?;
            tree.opt_out()?;
            tree.prepare_snapshot(".lake/build/lib/lean/P/A.olean")?;
            let before = snapshot(&tree.project)?;
            let err = crate::check::run_check_command(
                &mut store,
                false,
                true,
                tree.project.join("P/Target.lean"),
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
                "missing-trace check mutated Lake tree (manifest={manifest_backed})"
            );
        }
        Ok(())
    }

    /// A project with Lake file inputs, laid out by hand because `LakeTree` uses a `lakefile.toml`
    /// (which cannot declare inputs). `Smoke.Shared` is deliberately buildable by two libraries.
    fn input_bearing_tree(tag: &str) -> Result<PathBuf> {
        let proj = std::env::temp_dir().join(format!(
            "turbo_lake_inputs_{tag}_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&proj);
        fs::create_dir_all(proj.join("Smoke"))?;
        fs::create_dir_all(proj.join("Data"))?;
        fs::create_dir_all(proj.join(".lake/build/lib/lean/Smoke"))?;
        fs::write(
            proj.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )?;
        fs::write(
            proj.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n@[default_target]\nlean_lib «Smoke» where\n  globs := #[.one `Smoke.A, .one `Smoke.Shared]\n  needs := #[smokeSources]\nlean_lib Other where\n  roots := #[`Other]\nlean_lib Later where\n  globs := #[.one `Smoke.Shared]\n",
        )?;
        fs::write(proj.join("Smoke/A.lean"), "def a : Nat := 1\n")?;
        fs::write(proj.join("Smoke/Shared.lean"), "def s : Nat := 1\n")?;
        fs::write(proj.join("Other.lean"), "def o : Nat := 1\n")?;
        fs::write(proj.join("Data/a.sol"), "contract A {}")?;
        Ok(proj)
    }

    /// `lake build <Mod>` builds the module under Lake's own attribution -- the **last** library
    /// that can build it -- and that library's `extraDep` may carry none of the `needs` naming the
    /// input the module reads. Lake then finds the dep trace unchanged by an input edit and reports
    /// the module up to date, so the "refresh" leaves the stale `.olean` in place and the caller
    /// goes on to check against it. Deleting the artifacts first is not enough either: Lake can
    /// restore one from its artifact cache keyed on that same input-blind trace. The refresh must
    /// ask for the library instead.
    #[test]
    fn test_lake_refresh_targets_substitutes_the_input_bearing_library() -> Result<()> {
        let proj = input_bearing_tree("refresh_targets")?;
        if crate::module_builder::resolve_project_config(&proj).is_err() {
            let _ = fs::remove_dir_all(&proj);
            return Ok(());
        }
        let cfg = crate::module_builder::resolve_project_config(&proj)?;
        // The hazard is real: Lake attributes `Smoke.Shared` to `Later`, which has no `needs`.
        assert_eq!(
            crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, "Smoke.Shared")
                .expect("Smoke.Shared resolves")
                .target_name,
            "Later"
        );
        assert_eq!(
            lake_refresh_targets(&proj, &["Smoke.Shared".to_string()]),
            vec!["Smoke".to_string()],
            "a module an input-bearing library can build must be refreshed by library name"
        );
        assert_eq!(
            lake_refresh_targets(&proj, &["Smoke.A".to_string()]),
            vec!["Smoke".to_string()]
        );
        // A module no input-bearing library can build is passed through untouched, so the refresh
        // stays as narrow as it was for everything the inputs cannot reach.
        assert_eq!(
            lake_refresh_targets(&proj, &["Other".to_string()]),
            vec!["Other".to_string()]
        );
        assert_eq!(
            lake_refresh_targets(
                &proj,
                &[
                    "Smoke.A".to_string(),
                    "Smoke.Shared".to_string(),
                    "Other".to_string()
                ]
            ),
            vec!["Smoke".to_string(), "Other".to_string()]
        );
        // A project without inputs keeps the exact module list it had before.
        let plain = std::env::temp_dir().join(format!(
            "turbo_lake_plain_targets_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        fs::create_dir_all(&plain)?;
        fs::write(
            plain.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )?;
        fs::write(
            plain.join("lakefile.toml"),
            "name = \"plain\"\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n[[lean_exe]]\nname = \"runner\"\nroot = \"Main\"\n",
        )?;
        let mods = vec!["P.A".to_string(), "P.B".to_string()];
        assert_eq!(lake_refresh_targets(&plain, &mods), mods);
        assert_eq!(
            lake_refresh_targets(&plain, &["P.A".to_string(), "Main".to_string()]),
            vec!["@plain/runner:exe".to_string(), "P.A".to_string()],
            "a lean_exe root module must translate to @<pkg>/<exe>:exe so Lake relinks the binary"
        );
        let _ = fs::remove_dir_all(&plain);
        let _ = fs::remove_dir_all(&proj);
        Ok(())
    }

    /// A manifest entry has to name the input bytes it was recorded against, and a *missing* entry
    /// has to read as stale once the package declares inputs.
    ///
    /// `build <OneLib>` re-stamps the manifest header for the whole package, and the lake-delegated
    /// refresh *deletes* the entries it hands to Lake, so "header current, entry absent" is exactly
    /// the state a partial rebuild leaves behind for the library it did not touch. Every other
    /// signal `ensure_project_imports_fresh_for_check` has -- the `.lean` source hash, the `.olean`
    /// mtime -- is unmoved by a `.sol` edit, so treating an absent entry as fresh accepted an
    /// `.olean` elaborated against bytes that are gone.
    ///
    /// The worktree opt-out turns the verdict into an error naming the stale modules, which is what
    /// lets this assert "stale" without running Lake.
    #[test]
    fn test_check_treats_absent_and_input_stale_manifest_entries_as_stale() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let proj = input_bearing_tree("manifest_entries")?;
        if crate::module_builder::resolve_project_config(&proj).is_err() {
            let _ = fs::remove_dir_all(&proj);
            return Ok(());
        }
        fs::write(
            proj.join("Smoke/B.lean"),
            "import Smoke.A\ntheorem b : a = 1 := rfl\n",
        )?;
        fs::write(
            proj.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        // A plausible warm `.lake/build`: the `.olean` exists and is newer than its source, so
        // every mtime check below reports fresh and only the manifest can object.
        let olean = proj.join(".lake/build/lib/lean/Smoke/A.olean");
        let mut store = TurboStore::open(Some(&proj.join(".turbo-test-store")))?;
        fs::remove_file(proj.join("turbo-lean.toml"))?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.A".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )?;
        fs::write(
            proj.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        fs::File::options()
            .write(true)
            .open(&olean)?
            .set_modified(std::time::SystemTime::now() + std::time::Duration::from_secs(2))?;
        let olean_digest = crate::module_builder::compute_olean_artifact_set_digest(&olean)?;

        let a_src = fs::read_to_string(proj.join("Smoke/A.lean"))?;
        type Entry = crate::module_builder::VerifiedDepModuleEntry;
        let write_manifest = |entry: Option<Entry>| -> Result<()> {
            let cfg = crate::module_builder::resolve_project_config(&proj)?;
            let manifest = crate::module_builder::VerifiedDepManifest {
                pkg_name: cfg.root_pkg.name.clone(),
                toolchain: cfg.toolchain.clone(),
                lean_githash: cfg.lean_githash.clone(),
                pkg_config_digest: cfg.root_pkg.config_digest.clone(),
                // Always the *current* digest: the point is that a current header must not vouch
                // for an entry that is absent or was recorded against older bytes.
                lake_inputs_digest: crate::module_builder::workspace_lake_inputs_digest(&cfg)?,
                workspace_config_digest: cfg.canonical_config_digest.clone(),
                allowed_axioms: crate::splitter::allowed_axioms(),
                kernel_policy_digest: crate::splitter::current_kernel_policy_digest(),
                modules: entry
                    .into_iter()
                    .map(|e| ("Smoke/A.lean".to_string(), e))
                    .collect(),
                ..Default::default()
            };
            fs::write(
                verified_sources_manifest_path(&proj),
                serde_json::to_vec(&manifest)?,
            )?;
            assert!(
                load_verified_project_manifest(&proj).is_some(),
                "the fixture manifest must be accepted, or the assertions below prove nothing"
            );
            assert!(
                !lake_inputs_changed_since_manifest(&proj),
                "the header must read as current, so only the entry is under test"
            );
            Ok(())
        };
        let fresh_entry = |inputs_digest: String| Entry {
            src_blake3: blake3::hash(a_src.as_bytes()).to_hex().to_string(),
            olean_artifact_digest: olean_digest.clone(),
            lake_inputs_digest: inputs_digest,
            kernel_audited: true,
            import_olean_digests: BTreeMap::new(),
            artifact_stat_fingerprint: String::new(),
            ..Default::default()
        };
        let verdict = || {
            crate::module_builder::reset_lake_inputs_tag_memo();
            ensure_project_imports_fresh_for_check(&proj, &[proj.join("Smoke/B.lean")])
                .map_err(|e| e.to_string())
        };
        let current = crate::module_builder::workspace_lake_inputs_digest(
            &crate::module_builder::resolve_project_config(&proj)?,
        )?;
        assert!(!current.is_empty(), "the fixture must declare inputs");

        // 1. A complete, current entry is fresh: this is not a blanket refusal.
        write_manifest(Some(fresh_entry(current.clone())))?;
        assert_eq!(verdict(), Ok(0), "a current entry must stay fresh");

        // 2. Entry recorded against older input bytes while the header is current.
        write_manifest(Some(fresh_entry("stale-digest".to_string())))?;
        let err = verdict().expect_err("an entry from older input bytes must be stale");
        assert!(err.contains("Smoke.A"), "{err}");

        // 3. Entry absent entirely, which is what a partial rebuild leaves behind.
        write_manifest(None)?;
        let err =
            verdict().expect_err("an absent entry must be stale for an input-bearing package");
        assert!(err.contains("Smoke.A"), "{err}");

        // 4. The same absent entry stays *fresh* once the package declares no inputs: there the
        // source hashes, sidecars, and mtimes are a complete signal and nothing changes for existing projects.
        fs::write(
            proj.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\n@[default_target]\nlean_lib «Smoke» where\n  globs := #[.submodules `Smoke]\n",
        )?;
        fs::remove_file(proj.join("turbo-lean.toml"))?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.A".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )?;
        fs::write(
            proj.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        fs::File::options()
            .write(true)
            .open(&olean)?
            .set_modified(std::time::SystemTime::now() + std::time::Duration::from_secs(2))?;
        write_manifest(None)?;
        assert_eq!(
            verdict(),
            Ok(0),
            "a project without Lake inputs must keep its previous behaviour"
        );
        let _ = fs::remove_dir_all(&proj);
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
            assert_eq!(
                &fs::read(path)?,
                bytes,
                "opt-out must not copy or rewrite main `.lake`"
            );
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

    #[test]
    fn test_workspace_olean_precedes_caller_lean_path_preventing_shadow_cas_poisoning() -> Result<()>
    {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let prev_lp = std::env::var_os("LEAN_PATH");
        let root = std::env::temp_dir().join(format!(
            "turbo_ws_precedes_caller_lp_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&root);
        let ws = root.join("ws");
        let shadow = root.join("shadow");
        for (dir, val) in [(&ws, 1u32), (&shadow, 2u32)] {
            fs::create_dir_all(dir.join("P"))?;
            fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
            fs::write(
                dir.join("lakefile.toml"),
                "name = \"p\"\ndefaultTargets = [\"P\"]\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n",
            )?;
            fs::write(dir.join("P/A.lean"), format!("def k : Nat := {val}\n"))?;
        }
        fs::write(
            ws.join("P/B.lean"),
            "import P.A\ntheorem b_ok : k = 1 := rfl\n",
        )?;
        assert!(Command::new("lake")
            .args(["build", "P.B"])
            .current_dir(&ws)
            .status()?
            .success());
        assert!(Command::new("lake")
            .args(["build", "P.A"])
            .current_dir(&shadow)
            .status()?
            .success());

        let canon_ws = ws.canonicalize()?;
        let shadow_lib = shadow.canonicalize()?.join(".lake/build/lib/lean");
        let shadow_lp = shadow_lib.to_string_lossy().to_string();
        let b_src = fs::read_to_string(canon_ws.join("P/B.lean"))?;

        std::env::remove_var("LEAN_PATH");
        let clean_hashes = compute_imported_olean_interface_hashes(&b_src, &canon_ws, None);
        let shadow_only_hashes =
            compute_imported_olean_interface_hashes(&b_src, Path::new(""), Some(&shadow_lp));
        assert_ne!(clean_hashes, shadow_only_hashes);

        // Caller `LEAN_PATH` carries incompatible `P/A.olean` (`k := 2`), while workspace `ws`
        // has fresh `P/A.olean` (`k := 1`) and `P/B.olean`. Workspace `P/A.olean` must win
        // everywhere (`compute_imported_olean_interface_hashes`, `resolve_remote_lean_path`,
        // `resolve_lake_env`), and fast `.olean` certification in `ws` must NOT populate CAS
        // under `shadow_only_hashes`.
        std::env::set_var("LEAN_PATH", &shadow_lp);
        assert_eq!(
            compute_imported_olean_interface_hashes(&b_src, &canon_ws, None),
            clean_hashes
        );
        assert_eq!(
            compute_imported_olean_interface_hashes(&b_src, &canon_ws, Some(&shadow_lp)),
            clean_hashes
        );
        let resolved_lp = resolve_remote_lean_path(&canon_ws, None);
        assert!(resolved_lp.starts_with(
            canon_ws
                .join(".lake/build/lib/lean")
                .to_string_lossy()
                .as_ref()
        ));

        let mut store = TurboStore::open(Some(&root.join("cache")))?;
        let (lake_ev, _) = resolve_lake_env(&store, &canon_ws)?;
        assert!(lake_ev["LEAN_PATH"].starts_with(
            canon_ws
                .join(".lake/build/lib/lean")
                .to_string_lossy()
                .as_ref()
        ));
        crate::check::run_check_command(
            &mut store,
            false,
            true,
            canon_ws.join("P/B.lean"),
            None,
            canon_ws.clone(),
            None,
            false,
            None,
        )?;
        let shadow_split = split_lean_source(&b_src, &shadow_only_hashes);
        let shadow_key = compute_shard_key("leanprover/lean4:v4.35.0", &shadow_split.shards[0]);
        assert!(
            store.get_cached_action(&shadow_key, "trusted")?.is_none(),
            "fast workspace `.olean` check poisoned CAS under shadowed caller `LEAN_PATH` digest"
        );
        let clean_split = split_lean_source(&b_src, &clean_hashes);
        let clean_key = compute_shard_key("leanprover/lean4:v4.35.0", &clean_split.shards[0]);
        assert!(store.get_cached_action(&clean_key, "trusted")?.is_some());

        // When `P.A` is only on caller `LEAN_PATH = shadow_lp` (`k = 2`) in a project without
        // workspace `P/A`, `theorem b_ok : k = 1 := rfl` must fail rather than hitting a poisoned CAS entry!
        let consumer = root.join("consumer");
        fs::create_dir_all(&consumer)?;
        fs::write(
            consumer.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            consumer.join("lakefile.toml"),
            "name = \"consumer\"\n[[lean_lib]]\nname = \"Use\"\n",
        )?;
        let consumer_b = consumer.join("Use.lean");
        fs::write(&consumer_b, &b_src)?;
        assert!(
            crate::check::run_check_command(
                &mut store, false, true, consumer_b, None, consumer, None, false, None,
            )
            .is_err(),
            "consumer check with `LEAN_PATH` = shadow (`k = 2`) falsely succeeded"
        );
        // Also test uncached elaboration inside `ws` when `b_ok` is edited (`k + 0 = 1`):
        // elaboration must resolve workspace `P/A.olean` (`k = 1`), not `shadow_lp` (`k = 2`).
        fs::write(
            canon_ws.join("P/B.lean"),
            "import P.A\ntheorem b_edited : k + 0 = 1 := rfl\n",
        )?;
        crate::check::run_check_command(
            &mut store,
            false,
            true,
            canon_ws.join("P/B.lean"),
            None,
            canon_ws,
            None,
            false,
            None,
        )?;

        match prev_lp {
            Some(v) => std::env::set_var("LEAN_PATH", v),
            None => std::env::remove_var("LEAN_PATH"),
        }
        drop(store);
        let _ = fs::remove_dir_all(&root);
        Ok(())
    }

    #[test]
    fn test_dedup_worktree_packages_verifies_cas_digest_and_stages_exact_bytes() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let saved_wt_env = std::env::var("TURBO_LEAN_NO_WORKTREE_LINK").ok();
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
        #[cfg(unix)]
        use std::os::unix::fs::{MetadataExt, PermissionsExt};

        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_dedup_digest_test_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let cache_dir = tmp_dir.join("cache");
        let wt = tmp_dir.join("wt");
        let pkg_dir = wt.join(".lake/packages/dep/.lake/build/lib/lean/Dep");
        fs::create_dir_all(&pkg_dir)?;

        let store = TurboStore::open(Some(&cache_dir))?;
        let good_bytes = vec![0x5Au8; 1024];
        let good_hash = blake3::hash(&good_bytes).to_hex().to_string();
        let cas_file = store
            .root
            .join("pkg_cas")
            .join(&good_hash[..2])
            .join(&good_hash);
        fs::create_dir_all(cas_file.parent().unwrap())?;
        // Pre-seed a corrupt `pkg_cas` entry with the EXACT same byte length (1024 bytes).
        fs::write(&cas_file, vec![0xFFu8; 1024])?;

        let olean_a = pkg_dir.join("A.olean");
        let olean_b = pkg_dir.join("B.olean");
        fs::write(&olean_a, &good_bytes)?;
        fs::write(&olean_b, &good_bytes)?;

        // Also place two hardlinked files sharing an inode (`C.olean` and `D.olean`), keep an
        // already-open writable descriptor on `C.olean` BEFORE setting mode `0o444`, and mutate
        // `C.olean` in-place (same byte length!) via that pre-opened writable fd. Permissions do
        // not revoke an open writable fd: `dedup_worktree_packages` must never reuse a stale hash
        // from `(dev, ino, len, 0o444)` alone, and must stage the true mutated bytes.
        let orig_shared_bytes = vec![0x3Cu8; 768];
        let olean_c = pkg_dir.join("C.olean");
        let olean_d = pkg_dir.join("D.olean");
        let mut pre_open_rw = fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .truncate(true)
            .open(&olean_c)?;
        std::io::Write::write_all(&mut pre_open_rw, &orig_shared_bytes)?;
        fs::hard_link(&olean_c, &olean_d)?;
        #[cfg(unix)]
        {
            let mut ro = fs::metadata(&olean_c)?.permissions();
            ro.set_mode(0o444);
            fs::set_permissions(&olean_c, ro)?;
        }
        // First dedup pass records `orig_shared_bytes` into `pkg_cas`.
        let rep0 = dedup_worktree_packages(&store, &wt)?;
        assert_eq!(rep0["status"], "worktree_packages_deduped");
        // Now mutate `pre_open_rw` (or re-create a hardlinked `0o444` pair with open writable fd)
        // to prove a `0o444` hardlinked pair mutated via an open writable descriptor between or
        // during dedup is hashed from live bytes rather than cached inode metadata.
        let olean_e = pkg_dir.join("E.olean");
        let olean_f = pkg_dir.join("F.olean");
        let mut rw_ef = fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .truncate(true)
            .open(&olean_e)?;
        std::io::Write::write_all(&mut rw_ef, &orig_shared_bytes)?;
        fs::hard_link(&olean_e, &olean_f)?;
        #[cfg(unix)]
        {
            let mut ro = fs::metadata(&olean_e)?.permissions();
            ro.set_mode(0o444);
            fs::set_permissions(&olean_e, ro)?;
        }
        // Mutate same-length `0o444` inode through the already-open writable descriptor!
        let mutated_shared_bytes = vec![0x99u8; 768];
        use std::io::Seek;
        rw_ef.seek(std::io::SeekFrom::Start(0))?;
        std::io::Write::write_all(&mut rw_ef, &mutated_shared_bytes)?;
        drop(rw_ef);
        drop(pre_open_rw);

        let rep = dedup_worktree_packages(&store, &wt)?;
        assert_eq!(rep["status"], "worktree_packages_deduped");
        assert_eq!(
            fs::read(&cas_file)?,
            good_bytes,
            "same-size corrupt pkg_cas entry must be replaced with digest-verified bytes, never linked over worktree files"
        );
        assert_eq!(fs::read(&olean_a)?, good_bytes);
        assert_eq!(fs::read(&olean_b)?, good_bytes);
        assert_eq!(fs::read(&olean_c)?, orig_shared_bytes);
        assert_eq!(fs::read(&olean_d)?, orig_shared_bytes);
        assert_eq!(
            fs::read(&olean_e)?,
            mutated_shared_bytes,
            "0o444 inode mutated via open writable fd must hash actual bytes, never reuse orig_shared_bytes CAS blob"
        );
        assert_eq!(fs::read(&olean_f)?, mutated_shared_bytes);
        let mutated_hash = blake3::hash(&mutated_shared_bytes).to_hex().to_string();
        let mutated_cas = store
            .root
            .join("pkg_cas")
            .join(&mutated_hash[..2])
            .join(&mutated_hash);
        assert_eq!(fs::read(&mutated_cas)?, mutated_shared_bytes);
        #[cfg(unix)]
        {
            assert_eq!(
                fs::metadata(&olean_a)?.ino(),
                fs::metadata(&cas_file)?.ino()
            );
            assert_eq!(
                fs::metadata(&olean_b)?.ino(),
                fs::metadata(&cas_file)?.ino()
            );
            assert_eq!(fs::metadata(&cas_file)?.permissions().mode() & 0o222, 0);
            assert_eq!(fs::metadata(&olean_c)?.ino(), fs::metadata(&olean_d)?.ino());
            assert_eq!(fs::metadata(&olean_c)?.permissions().mode() & 0o222, 0);
            assert_eq!(
                fs::metadata(&olean_e)?.ino(),
                fs::metadata(&mutated_cas)?.ino()
            );
            assert_eq!(
                fs::metadata(&olean_f)?.ino(),
                fs::metadata(&mutated_cas)?.ino()
            );

            // Also verify `dedup_worktree_packages` isolates against a pre-existing unstamped
            // `pkg_cas` inode that has a retained open writable descriptor: dedup must replace
            // `pkg_cas` with a fresh store-owned inode so post-dedup writes to the retained fd
            // cannot corrupt either `pkg_cas` or deduplicated package artifacts!
            let leaked_bytes = vec![0x77u8; 640];
            let leaked_hash = blake3::hash(&leaked_bytes).to_hex().to_string();
            let leaked_cas = store
                .root
                .join("pkg_cas")
                .join(&leaked_hash[..2])
                .join(&leaked_hash);
            fs::create_dir_all(leaked_cas.parent().unwrap())?;
            let mut retained_cas_rw = fs::OpenOptions::new()
                .create(true)
                .truncate(true)
                .read(true)
                .write(true)
                .open(&leaked_cas)?;
            std::io::Write::write_all(&mut retained_cas_rw, &leaked_bytes)?;
            let old_cas_ino = retained_cas_rw.metadata()?.ino();
            let olean_g = pkg_dir.join("G.olean");
            let olean_h = pkg_dir.join("H.olean");
            fs::write(&olean_g, &leaked_bytes)?;
            fs::write(&olean_h, &leaked_bytes)?;
            dedup_worktree_packages(&store, &wt)?;
            assert_ne!(fs::metadata(&leaked_cas)?.ino(), old_cas_ino);
            retained_cas_rw.seek(std::io::SeekFrom::Start(0))?;
            std::io::Write::write_all(&mut retained_cas_rw, &vec![0xEEu8; 640])?;
            drop(retained_cas_rw);
            assert_eq!(fs::read(&leaked_cas)?, leaked_bytes);
            assert_eq!(fs::read(&olean_g)?, leaked_bytes);
            assert_eq!(fs::read(&olean_h)?, leaked_bytes);
        }

        match saved_wt_env {
            Some(v) => std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", v),
            None => std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK"),
        }
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_optout_lakeless_nonroot_import_child() -> Result<()> {
        let Some(root) = std::env::var_os("TURBO_TEST_LAKELESS_OPTOUT_ROOT").map(PathBuf::from)
        else {
            return Ok(());
        };
        let dir = root.join("lakeless").canonicalize()?;
        let target = dir.join("Main.lean").canonicalize()?;
        let err = ensure_project_imports_fresh_for_check(&dir, &[target]).unwrap_err();
        let msg = format!("{err:#}");
        assert!(
            msg.contains("Cannot verify standalone import `Ext.NonRoot`")
                && msg.contains("fail-closed toolchain gate"),
            "unexpected error: {msg}"
        );
        assert!(
            !root.join("ambient-lean-invoked").exists(),
            "ensure_project_imports_fresh executed ambient PATH `lean`"
        );
        fs::write(root.join("done"), b"")?;
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_optout_lakeless_nonroot_import_never_executes_ambient_path_lean() -> Result<()> {
        use crate::worktree_test_support::TestChild;
        use std::os::unix::fs::PermissionsExt;
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let root = std::env::temp_dir().join(format!(
            "turbo_lakeless_optout_nopath_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&root);
        let dir = root.join("lakeless");
        let bin = root.join("path/bin");
        let fake_prefix = root.join("fake_prefix");
        fs::create_dir_all(&dir)?;
        fs::create_dir_all(&bin)?;
        fs::create_dir_all(fake_prefix.join("lib/lean/Ext"))?;
        // Fake `.olean` that would have satisfied the old `Command::new("lean") --print-prefix` fallback!
        fs::write(fake_prefix.join("lib/lean/Ext/NonRoot.olean"), [0x55u8; 64])?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v99.99.99\n")?;
        fs::write(
            dir.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        fs::write(
            dir.join("Main.lean"),
            "import Ext.NonRoot\ntheorem t : True := trivial\n",
        )?;
        let shim_lean = bin.join("lean");
        fs::write(
            &shim_lean,
            format!(
                "#!/bin/sh\nprintf invoked > '{}'\nprintf '%s\\n' '{}'\n",
                root.join("ambient-lean-invoked").display(),
                fake_prefix.display()
            ),
        )?;
        fs::set_permissions(&shim_lean, fs::Permissions::from_mode(0o755))?;

        let mut command =
            TestChild::command("lake_build::tests::test_optout_lakeless_nonroot_import_child")?;
        command
            .env("TURBO_TEST_LAKELESS_OPTOUT_ROOT", &root)
            .env("PATH", format!("{}:/usr/bin:/bin", bin.display()))
            .env("HOME", root.join("isolated/a/b/home"))
            .env("ELAN_HOME", root.join("empty_elan"))
            .env("TURBO_LEAN_HOME", root.join("cache"))
            .env("TURBO_LEAN_STAGING_DIR", root.join("staging"))
            .env_remove("LEAN_PATH");
        let mut child = TestChild::spawn(&mut command)?;
        child.finish(&root.join("done"))?;
        assert!(
            !root.join("ambient-lean-invoked").exists(),
            "ambient PATH `lean` shim was executed"
        );
        crate::zygote::purge_snapshot_dir(&root);
        Ok(())
    }

    #[test]
    fn test_auto_hardlink_worktree_oleans_rejects_divergent_lake_inputs_manifest_and_config(
    ) -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let saved_wt_env = std::env::var("TURBO_LEAN_NO_WORKTREE_LINK").ok();
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");

        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_wt_lake_inputs_parity_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);

        let main_repo = tmp_dir.join("main_repo");
        fs::create_dir_all(main_repo.join("Smoke"))?;
        fs::create_dir_all(main_repo.join("Data"))?;
        fs::create_dir_all(main_repo.join(".lake/build/lib/lean/Smoke"))?;
        fs::write(
            main_repo.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )?;
        let lakefile_lean = "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[smokeSources]\n";
        fs::write(main_repo.join("lakefile.lean"), lakefile_lean)?;
        fs::write(main_repo.join("Smoke/A.lean"), "def a : Nat := 1\n")?;
        fs::write(main_repo.join("Data/a.sol"), "contract A {}\n")?;
        let manifest_v1 =
            "{\"version\": 7, \"packagesDir\": \".lake/packages\", \"packages\": []}\n";
        fs::write(main_repo.join("lake-manifest.json"), manifest_v1)?;
        fs::write(
            main_repo.join(".lake/build/lib/lean/Smoke/A.olean"),
            b"smoke-a-olean-v1",
        )?;

        if crate::module_builder::resolve_project_config(&main_repo).is_err() {
            match saved_wt_env {
                Some(v) => std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", v),
                None => std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK"),
            }
            let _ = fs::remove_dir_all(&tmp_dir);
            return Ok(());
        }

        let cfg = crate::module_builder::resolve_project_config(&main_repo)?;
        let cur_inputs_digest = crate::module_builder::workspace_lake_inputs_digest(&cfg)?;
        let write_main_verified_manifest = |inputs_digest: &str| -> Result<()> {
            let m = crate::module_builder::VerifiedDepManifest {
                pkg_name: cfg.root_pkg.name.clone(),
                toolchain: cfg.toolchain.clone(),
                lean_githash: cfg.lean_githash.clone(),
                pkg_config_digest: cfg.root_pkg.config_digest.clone(),
                lake_inputs_digest: inputs_digest.to_string(),
                workspace_config_digest: cfg.canonical_config_digest.clone(),
                allowed_axioms: crate::splitter::allowed_axioms(),
                kernel_policy_digest: crate::splitter::current_kernel_policy_digest(),
                modules: std::collections::BTreeMap::from([(
                    "Smoke/A.lean".to_string(),
                    crate::module_builder::VerifiedDepModuleEntry {
                        src_blake3: blake3::hash(b"def a : Nat := 1\n").to_hex().to_string(),
                        olean_artifact_digest: "art".to_string(),
                        lake_inputs_digest: inputs_digest.to_string(),
                        kernel_audited: true,
                        import_olean_digests: Default::default(),
                        artifact_stat_fingerprint: String::new(),
                        ..Default::default()
                    },
                )]),
                ..Default::default()
            };
            fs::write(
                verified_sources_manifest_path(&main_repo),
                serde_json::to_vec(&m)?,
            )?;
            Ok(())
        };
        write_main_verified_manifest(&cur_inputs_digest)?;

        let make_wt = |name: &str| -> Result<PathBuf> {
            let main_git = main_repo.join(".git/worktrees").join(name);
            fs::create_dir_all(&main_git)?;
            fs::write(main_git.join("commondir"), "../..\n")?;
            let wt = tmp_dir.join(name);
            let _ = fs::remove_dir_all(&wt);
            fs::create_dir_all(wt.join("Smoke"))?;
            fs::create_dir_all(wt.join("Data"))?;
            fs::write(wt.join(".git"), format!("gitdir: {}\n", main_git.display()))?;
            fs::write(
                wt.join("lean-toolchain"),
                include_str!("../../../lean/lean-toolchain"),
            )?;
            fs::write(wt.join("lakefile.lean"), lakefile_lean)?;
            fs::write(wt.join("Smoke/A.lean"), "def a : Nat := 1\n")?;
            fs::write(wt.join("Data/a.sol"), "contract A {}\n")?;
            fs::write(wt.join("lake-manifest.json"), manifest_v1)?;
            Ok(wt)
        };

        // 1. Identical inputs + manifest + config + verified manifest => copies Smoke/A.olean.
        let wt_same = make_wt("wt_same")?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        assert_eq!(auto_hardlink_worktree_oleans_from_main_repo(&wt_same), 1);
        assert!(wt_same.join(".lake/build/lib/lean/Smoke/A.olean").exists());

        // 2. Divergent matched `input_dir` file => must refuse copying `.olean`s.
        let wt_input_diff = make_wt("wt_input_diff")?;
        fs::write(wt_input_diff.join("Data/a.sol"), "contract AChanged {}\n")?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        assert_eq!(
            auto_hardlink_worktree_oleans_from_main_repo(&wt_input_diff),
            0,
            "divergent matched input_dir file must block worktree .olean copy"
        );
        assert!(!wt_input_diff
            .join(".lake/build/lib/lean/Smoke/A.olean")
            .exists());

        // 3. Divergent `lake-manifest.json` => must refuse copying `.olean`s.
        let wt_manifest_diff = make_wt("wt_manifest_diff")?;
        fs::write(
            wt_manifest_diff.join("lake-manifest.json"),
            "{\"version\": 7, \"packagesDir\": \".lake/packages_alt\", \"packages\": []}\n",
        )?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        assert_eq!(
            auto_hardlink_worktree_oleans_from_main_repo(&wt_manifest_diff),
            0,
            "divergent lake-manifest.json must block worktree .olean copy"
        );

        // 4. Stale main verified manifest (`lake_inputs_digest` mismatch) => must refuse copying.
        write_main_verified_manifest("stale_digest_from_earlier_input")?;
        let wt_stale_main = make_wt("wt_stale_main")?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        assert_eq!(
            auto_hardlink_worktree_oleans_from_main_repo(&wt_stale_main),
            0,
            "main repo with stale verified manifest must not seed worktree .olean files"
        );

        match saved_wt_env {
            Some(v) => std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", v),
            None => std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK"),
        }
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_speed4_public_signature_early_cutoff_and_readonly_impact() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_speed4_pubsig_impact_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let proj = tmp_dir.join("proj");
        let cache = tmp_dir.join("cache");
        fs::create_dir_all(proj.join("Smoke"))?;
        fs::write(
            proj.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"smoke\"\n[[lean_lib]]\nname = \"Smoke\"\nglobs = [\"Smoke.+\"]\n",
        )?;

        let a_v1 = "\
module
private def privHelper (n : Nat) : Nat := n + 1
@[noinline] public def pubApi (n : Nat) : Nat := privHelper n
public theorem pub_thm (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n
";
        let b_src = "\
module
public import Smoke.A
public theorem downstream_b (n : Nat) : n + 0 = n := pub_thm n
";
        let c_src = "\
module
import Smoke.B
public theorem downstream_c (n : Nat) : n + 0 = n := downstream_b n
";
        fs::write(proj.join("Smoke/A.lean"), a_v1)?;
        fs::write(proj.join("Smoke/B.lean"), b_src)?;
        fs::write(proj.join("Smoke/C.lean"), c_src)?;

        let git_bin = std::env::var("TURBO_LEAN_GIT").unwrap_or_else(|_| "git".to_string());
        let run_git = |args: &[&str]| -> Result<()> {
            let st = Command::new(&git_bin)
                .current_dir(&proj)
                .args(args)
                .env("GIT_AUTHOR_NAME", "Test")
                .env("GIT_AUTHOR_EMAIL", "test@example.com")
                .env("GIT_COMMITTER_NAME", "Test")
                .env("GIT_COMMITTER_EMAIL", "test@example.com")
                .status()?;
            anyhow::ensure!(st.success(), "git {:?} failed", args);
            Ok(())
        };
        run_git(&["init"])?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-m", "init"])?;

        // 1. `compute_impact_report` BEFORE any build or store open: strictly read-only, no `.lake` or `.turbo-lean` created.
        let rep_unchanged = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_unchanged.edit_class, "unchanged");
        assert!(!rep_unchanged.public_signature_changed);
        assert_eq!(rep_unchanged.direct_dependents, vec!["Smoke.B".to_string()]);
        assert!(rep_unchanged.transitive_dependents.is_empty());
        assert_eq!(
            rep_unchanged.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(!proj.join(".lake").exists());
        assert!(!proj.join(".turbo-lean").exists());

        // Initial native build of the DAG so `Smoke.A`, `Smoke.B`, and `Smoke.C` have verified `.olean` baselines.
        let mut store = TurboStore::open(Some(&cache))?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let canon_proj = proj.canonicalize().unwrap_or_else(|_| proj.clone());

        // 2. Private theorem + proof-only edit on `pub_thm` (preserving exported axiom footprint `[]`):
        //    - `.ir` and `.ir.sig` remain byte-identical and `dumpPublicSignatureJson` matches -> cuts off at `Smoke.A` (1 module, NOT 3!).
        let a_proof_only_edit = "\
module
private def privHelper (n : Nat) : Nat := n + 1
@[noinline] public def pubApi (n : Nat) : Nat := privHelper n
public theorem pub_thm (n : Nat) : n + 0 = n := by
  have _unused : 1 + 1 = 2 := rfl
  exact Nat.add_zero n
private theorem priv_extra_lemma : 1 + 1 = 2 := rfl
";
        fs::write(proj.join("Smoke/A.lean"), a_proof_only_edit)?;
        let rep_priv = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_priv.edit_class, "private_module_edit");
        assert!(!rep_priv.public_signature_changed);
        assert!(!rep_priv.meta_signature_changed);
        assert!(rep_priv.transitive_dependents.is_empty());
        assert_eq!(
            rep_priv.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        let (rechecked_n, _files, rechecked_mods, _) = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        )?;
        assert_eq!(
            rechecked_n, 1,
            "public-signature early cutoff must stop at Smoke.A on theorem proof / private theorem edit, got {:?}",
            rechecked_mods
        );
        assert_eq!(rechecked_mods, vec!["Smoke.A".to_string()]);

        // 2a. Blocking 2 regression: proof-only edit that introduces `propext`/`Quot.sound` via `omega`
        //     mutates `exportedAxiomsExt` in `Smoke/A.olean`, so Stage-2 cutoff MUST recheck `Smoke.B`/`Smoke.C`!
        let a_axiom_footprint_edit = "\
module
private def privHelper (n : Nat) : Nat := n + 1
@[noinline] public def pubApi (n : Nat) : Nat := privHelper n
public theorem pub_thm (n : Nat) : n + 0 = n := by
  omega
";
        fs::write(proj.join("Smoke/A.lean"), a_axiom_footprint_edit)?;
        let (rechecked_ax_n, _ax_files, mut rechecked_ax_mods, _) =
            lake_recheck_dependents_with_store(
                Some(&store),
                &canon_proj,
                &["Smoke/A.lean".to_string()],
                Some("HEAD"),
                false,
            )?;
        rechecked_ax_mods.sort();
        assert_eq!(
            rechecked_ax_n, 3,
            "proof edit changing exportedAxiomsExt footprint (`[]` -> `[propext, Quot.sound]`) must not cut off downstream modules"
        );

        // 2b. Blocking 1 regression: mutating a `private def` body alters `Smoke/A.ir` (which Lean 4.35
        //     `PublicExport` passes via `importArts`), so Stage-2 cutoff MUST NOT skip `Smoke.B`/`Smoke.C`
        //     and must recheck all 3 modules so downstream `.trace` input hashes stay synchronized!
        let a_ir_mutating_edit = "\
module
private def privHelper (n : Nat) : Nat := n + 42
@[noinline] public def pubApi (n : Nat) : Nat := privHelper n
public theorem pub_thm (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n
";
        fs::write(proj.join("Smoke/A.lean"), a_ir_mutating_edit)?;
        let (rechecked_ir_n, _ir_files, mut rechecked_ir_mods, _) =
            lake_recheck_dependents_with_store(
                Some(&store),
                &canon_proj,
                &["Smoke/A.lean".to_string()],
                Some("HEAD"),
                false,
            )?;
        rechecked_ir_mods.sort();
        assert_eq!(
            rechecked_ir_n, 3,
            "`.ir`-mutating private def edit must not unsoundly cut off downstream modules in Lean 4.35 PublicExport"
        );
        assert_eq!(
            rechecked_ir_mods,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );

        // 3. Public theorem type / attribute edit (`@[simp]` added on `pub_thm`):
        //    - `impact` classifies `public_signature_edit`, `public_signature_changed == true`, lists full downstream cone `Smoke.B` & `Smoke.C`.
        //    - `lake_recheck_dependents_with_store` does NOT cut off and rechecks all 3 modules (`Smoke.A`, `Smoke.B`, `Smoke.C`).
        let a_pub_edit = a_v1.replace("public theorem pub_thm", "@[simp] public theorem pub_thm");
        fs::write(proj.join("Smoke/A.lean"), &a_pub_edit)?;
        let rep_pub = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_pub.edit_class, "public_signature_edit");
        assert!(rep_pub.public_signature_changed);
        assert_eq!(
            rep_pub.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_pub.pruned_dependents.is_empty());

        let (rechecked_pub_n, _pub_files, mut rechecked_pub_mods, _) =
            lake_recheck_dependents_with_store(
                Some(&store),
                &canon_proj,
                &["Smoke/A.lean".to_string()],
                Some("HEAD"),
                false,
            )?;
        rechecked_pub_mods.sort();
        assert_eq!(rechecked_pub_n, 3);
        assert_eq!(
            rechecked_pub_mods,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );

        // 4. Blocking 2 regressions on `dumpPublicSignatureJson` (`olean-pubsig:v2`):
        //    (a) Instance priority change (`@[instance 100]` vs `@[instance 200]`) MUST alter `public_sig_digest`.
        //    (b) Non-whitelisted persistent extension (`register_simp_attr` custom ext) MUST set `has_opaque_ext = true`
        //        so Stage-2 cutoff fails closed instead of trusting partial metadata projection!
        let inst_v1 = "\
module
namespace SmokeA
public class MyTag (α : Type) where
  tag : Nat
public def mkTag100 : MyTag Nat := { tag := 1 }
attribute [instance 100] mkTag100
end SmokeA
";
        let inst_v2 = "\
module
namespace SmokeA
public class MyTag (α : Type) where
  tag : Nat
public def mkTag100 : MyTag Nat := { tag := 1 }
attribute [instance 200] mkTag100
end SmokeA
";
        fs::write(proj.join("Smoke/A.lean"), inst_v1)?;
        lake_build_modules(&canon_proj, &["Smoke.A".to_string()], None)?;
        let cfg = crate::module_builder::resolve_project_config(&canon_proj)?;
        let replay_lp = format!(
            "{}:{}",
            resolve_remote_lean_path(&canon_proj, None),
            cfg.toolchain_lib_lean.display()
        );
        let sig_inst_100 = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.A",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(!sig_inst_100.has_opaque_ext);
        assert!(!sig_inst_100.instance_entries.is_empty());

        fs::write(proj.join("Smoke/A.lean"), inst_v2)?;
        lake_build_modules(&canon_proj, &["Smoke.A".to_string()], None)?;
        let sig_inst_200 = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.A",
            &replay_lp,
            &[],
            false,
        )?;
        assert_ne!(
            sig_inst_100.public_sig_digest, sig_inst_200.public_sig_digest,
            "instance priority change in Meta.instanceExtension must alter olean public_sig_digest"
        );

        //    (b) Exporting an alias for an imported declaration (`export SmokeA (mkTag100)`)
        //        where `origName` is NOT in `Smoke.B`'s `md.constants` MUST alter `Smoke.B`'s
        //        `public_sig_digest` when added or removed.
        let b_no_export = "\
module
public import Smoke.A
public def bVal : Nat := 1
";
        let b_with_imported_export = "\
module
public import Smoke.A
export SmokeA (mkTag100)
public def bVal : Nat := 1
";
        fs::write(proj.join("Smoke/B.lean"), b_no_export)?;
        lake_build_modules(&canon_proj, &["Smoke.B".to_string()], None)?;
        let sig_b_no_export = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.B",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(!sig_b_no_export.has_opaque_ext);

        fs::write(proj.join("Smoke/B.lean"), b_with_imported_export)?;
        lake_build_modules(&canon_proj, &["Smoke.B".to_string()], None)?;
        let sig_b_with_export = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.B",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(!sig_b_with_export.has_opaque_ext);
        assert_ne!(
            sig_b_no_export.public_sig_digest, sig_b_with_export.public_sig_digest,
            "re-exporting an imported declaration via `export N (foo)` must alter olean public_sig_digest"
        );

        //    (c) Adding an entry to a whitelisted attribute/tag extension (`Lean.matchPatternAttr` /
        //        `Lean.Compiler.specializeAttr`) targeting an IMPORTED declaration from `Smoke.A`
        //        (so `Smoke.B`'s `md.constants` does NOT contain `SmokeA.mkTag100`) MUST alter
        //        `Smoke.B`'s `public_sig_digest` without setting `has_opaque_ext = true`.
        let b_imported_match_pat = "\
module
public import Smoke.A
meta import Lean
run_cmd Lean.Elab.Command.liftCoreM <| Lean.modifyEnv (fun env => Lean.matchPatternAttr.ext.addEntry env `SmokeA.mkTag100)
public def bVal : Nat := 1
";
        fs::write(proj.join("Smoke/B.lean"), b_imported_match_pat)?;
        lake_build_modules(&canon_proj, &["Smoke.B".to_string()], None)?;
        let sig_b_imported_match_pat = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.B",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(
            !sig_b_imported_match_pat.has_opaque_ext,
            "whitelisted matchPatternAttr entry must not set has_opaque_ext"
        );
        assert_ne!(
            sig_b_no_export.public_sig_digest, sig_b_imported_match_pat.public_sig_digest,
            "whitelisted tag/attribute extension entry targeting an imported declaration outside md.constants must alter public_sig_digest"
        );

        let b_spec_arg1 = "\
module
public def polyFn (f : Nat → Nat) (g : Nat → Nat) (x : Nat) : Nat := f (g x)
attribute [specialize 1] polyFn
";
        let b_spec_arg2 = "\
module
public def polyFn (f : Nat → Nat) (g : Nat → Nat) (x : Nat) : Nat := f (g x)
attribute [specialize 2] polyFn
";
        fs::write(proj.join("Smoke/B.lean"), b_spec_arg1)?;
        lake_build_modules(&canon_proj, &["Smoke.B".to_string()], None)?;
        let sig_b_spec_arg1 = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.B",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(
            !sig_b_spec_arg1.has_opaque_ext,
            "`@[specialize 1]` (`Lean.Compiler.specializeAttr`) must be whitelisted and decoded"
        );
        fs::write(proj.join("Smoke/B.lean"), b_spec_arg2)?;
        lake_build_modules(&canon_proj, &["Smoke.B".to_string()], None)?;
        let sig_b_spec_arg2 = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.B",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(!sig_b_spec_arg2.has_opaque_ext);
        assert_ne!(
            sig_b_spec_arg1.public_sig_digest, sig_b_spec_arg2.public_sig_digest,
            "changing `@[specialize 1]` to `@[specialize 2]` must alter public_sig_digest"
        );

        let opaque_ext_src = "\
module
public meta import Lean
public meta initialize myOpaqueExt : Lean.SimplePersistentEnvExtension Lean.Name (Array Lean.Name) ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun _ => #[]
    addEntryFn := Array.push
  }
";
        let opaque_user_src = "\
module
public meta import Smoke.A
run_cmd Lean.Elab.Command.liftCoreM <| Lean.modifyEnv (fun env => myOpaqueExt.addEntry env `hello)
public theorem trivial_ok : 1 + 1 = 2 := rfl
";
        fs::write(proj.join("Smoke/A.lean"), opaque_ext_src)?;
        fs::write(proj.join("Smoke/B.lean"), opaque_user_src)?;
        lake_build_modules(
            &canon_proj,
            &["Smoke.A".to_string(), "Smoke.B".to_string()],
            None,
        )?;
        let sig_opaque = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.B",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(
            sig_opaque.has_opaque_ext,
            "unrecognized persistent environment extension entry must trip `has_opaque_ext = true` fail-closed guard"
        );

        //    (d) End-to-end `compute_impact_report` check for `local notation`: editing a `local notation`
        //        before a public declaration whose type uses that notation MUST mark
        //        `public_signature_changed = true` and classify as `public_signature_edit`.
        let a_local_not_v1 = "\
module
local notation \"MYTYPE\" => Nat
public def localNotVal : MYTYPE := 0
";
        let a_local_not_v2 = "\
module
local notation \"MYTYPE\" => Bool
public def localNotVal : MYTYPE := true
";
        fs::write(proj.join("Smoke/A.lean"), a_local_not_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useIt := localNotVal\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useItC := useIt\n",
        )?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-m", "local notation baseline"])?;
        fs::write(proj.join("Smoke/A.lean"), a_local_not_v2)?;
        let rep_local_not = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_local_not.edit_class, "public_signature_edit");
        assert!(
            rep_local_not.public_signature_changed,
            "`local notation` edit before a public declaration must mark `public_signature_changed = true`"
        );
        assert_eq!(
            rep_local_not.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/Provider1.lean"),
            "module\npublic def foo : Nat := 0\n",
        )?;
        fs::write(
            proj.join("Smoke/Provider2.lean"),
            "module\npublic def foo : Bool := true\n",
        )?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\nimport Smoke.Provider1\npublic def api := foo\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useApi := api\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useApiC := useApi\n",
        )?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-m", "non-exported import baseline"])?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\nimport Smoke.Provider2\npublic def api := foo\n",
        )?;
        let rep_nonexp_imp = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_nonexp_imp.edit_class, "public_signature_edit");
        assert!(
            rep_nonexp_imp.public_signature_changed,
            "non-exported import change before a public declaration must mark `public_signature_changed = true`"
        );
        assert_eq!(
            rep_nonexp_imp.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_nonexp_imp.pruned_dependents.is_empty());

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\nprivate def helper := (0 : Nat)\npublic def api := helper\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useApi := api\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useApiC := useApi\n",
        )?;
        run_git(&["add", "."])?;
        run_git(&[
            "commit",
            "-m",
            "private helper inferred public def baseline",
        ])?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\nprivate def helper := true\npublic def api := helper\n",
        )?;
        let rep_priv_helper = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_priv_helper.edit_class, "public_signature_edit");
        assert!(
            rep_priv_helper.public_signature_changed,
            "private helper edit before `public def api := helper` must mark `public_signature_changed = true`"
        );
        assert_eq!(
            rep_priv_helper.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_priv_helper.pruned_dependents.is_empty());

        for (commit_msg, base_a, edited_a) in [
            (
                "private abbrev in public theorem baseline",
                "module\nprivate abbrev MyProp := (1 = 1)\npublic theorem apiThm : MyProp := rfl\n",
                "module\nprivate abbrev MyProp := (2 = 2)\npublic theorem apiThm : MyProp := rfl\n",
            ),
            (
                "private def in public theorem baseline",
                "module\nprivate def targetVal : Nat := 1\npublic theorem apiThm : targetVal = targetVal := rfl\n",
                "module\nprivate def targetVal : Nat := 2\npublic theorem apiThm : targetVal = targetVal := rfl\n",
            ),
        ] {
            fs::write(proj.join("Smoke/A.lean"), base_a)?;
            fs::write(
                proj.join("Smoke/B.lean"),
                "module\npublic import Smoke.A\npublic theorem useThm : True := trivial\n",
            )?;
            fs::write(
                proj.join("Smoke/C.lean"),
                "module\nimport Smoke.B\npublic theorem useThmC : True := useThm\n",
            )?;
            run_git(&["add", "."])?;
            run_git(&["commit", "-m", commit_msg])?;
            fs::write(proj.join("Smoke/A.lean"), edited_a)?;
            let rep_thm_priv = compute_impact_report(
                proj.join("Smoke/A.lean"),
                Some(proj.clone()),
                Some("HEAD".to_string()),
            )?;
            assert_eq!(rep_thm_priv.edit_class, "public_signature_edit");
            assert!(rep_thm_priv.public_signature_changed);
            assert_eq!(
                rep_thm_priv.transitive_dependents,
                vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
            );
            assert!(rep_thm_priv.pruned_dependents.is_empty());
        }

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic def api : Nat := 1\nprivate def trailingHelper := (0 : Nat)\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useApi := api\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useApiC := useApi\n",
        )?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-m", "trailing private helper baseline"])?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic def api : Nat := 1\nprivate def trailingHelper := true\n",
        )?;
        let rep_trailing_priv = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_trailing_priv.edit_class, "private_module_edit");
        assert!(!rep_trailing_priv.public_signature_changed);
        assert!(rep_trailing_priv.transitive_dependents.is_empty());
        assert_eq!(
            rep_trailing_priv.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/Provider1.lean"),
            "module\npublic def p1 : Nat := 1\n",
        )?;
        fs::write(
            proj.join("Smoke/Provider2.lean"),
            "module\npublic def p2 : Nat := 2\n",
        )?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic import Smoke.Provider1\npublic import Smoke.Provider2\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useReexport : Nat := p1 + p2\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useReexportC : Nat := useReexport\n",
        )?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-m", "public import order baseline"])?;

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic import Smoke.Provider2\npublic import Smoke.Provider1\n",
        )?;
        let rep_pub_imp_swap = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_pub_imp_swap.edit_class, "public_signature_edit");
        assert!(
            rep_pub_imp_swap.public_signature_changed,
            "swapping `public import` order must mark `public_signature_changed = true`"
        );
        assert!(rep_pub_imp_swap.meta_signature_changed);
        assert_ne!(
            Some(rep_pub_imp_swap.public_signature_digest.as_str()),
            rep_pub_imp_swap.baseline_public_signature_digest.as_deref()
        );
        assert_eq!(
            rep_pub_imp_swap.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(
            rep_pub_imp_swap.pruned_dependents.is_empty(),
            "downstream importers must not be pruned when `public import` order changes"
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "-- header note\nmodule /- cmt -/\n\n  public   import   Smoke.Provider1 -- first\n  /- between -/\n  public   import   Smoke.Provider2\n",
        )?;
        let rep_pub_imp_ws_pure = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert!(!rep_pub_imp_ws_pure.public_signature_changed);
        assert!(!rep_pub_imp_ws_pure.meta_signature_changed);
        assert_eq!(
            Some(rep_pub_imp_ws_pure.public_signature_digest.as_str()),
            rep_pub_imp_ws_pure
                .baseline_public_signature_digest
                .as_deref()
        );
        assert!(rep_pub_imp_ws_pure.transitive_dependents.is_empty());
        assert_eq!(
            rep_pub_imp_ws_pure.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "-- header note\nmodule /- cmt -/\n\n  public   import   Smoke.Provider1 -- first\n  /- between -/\n  public   import   Smoke.Provider2\nprivate def trailingOnly : Nat := 9\n",
        )?;
        let rep_pub_imp_ws = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_pub_imp_ws.edit_class, "private_module_edit");
        assert!(!rep_pub_imp_ws.public_signature_changed);
        assert!(!rep_pub_imp_ws.meta_signature_changed);
        assert_eq!(
            Some(rep_pub_imp_ws.public_signature_digest.as_str()),
            rep_pub_imp_ws.baseline_public_signature_digest.as_deref()
        );
        assert_eq!(
            Some(rep_pub_imp_ws.meta_signature_digest.as_str()),
            rep_pub_imp_ws.baseline_meta_signature_digest.as_deref()
        );
        assert!(rep_pub_imp_ws.transitive_dependents.is_empty());
        assert_eq!(
            rep_pub_imp_ws.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic meta import Smoke.Provider1\npublic meta import Smoke.Provider2\npublic meta def metaConst : Nat := 1\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def usePubOnly : Nat := 1\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def usePubOnlyC : Nat := usePubOnly\n",
        )?;
        fs::write(
            proj.join("Smoke/M.lean"),
            "module\nmeta import Smoke.A\nmeta def useMeta : Nat := p1 + p2 + metaConst\n",
        )?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-m", "public meta import order baseline"])?;

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic meta import Smoke.Provider2\npublic meta import Smoke.Provider1\npublic meta def metaConst : Nat := 1\n",
        )?;
        let rep_meta_imp_swap = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_meta_imp_swap.edit_class, "meta_only_module_edit");
        assert!(!rep_meta_imp_swap.public_signature_changed);
        assert!(
            rep_meta_imp_swap.meta_signature_changed,
            "swapping `public meta import` order must mark `meta_signature_changed = true`"
        );
        assert_eq!(
            Some(rep_meta_imp_swap.public_signature_digest.as_str()),
            rep_meta_imp_swap
                .baseline_public_signature_digest
                .as_deref()
        );
        assert_ne!(
            Some(rep_meta_imp_swap.meta_signature_digest.as_str()),
            rep_meta_imp_swap.baseline_meta_signature_digest.as_deref()
        );
        assert_eq!(
            rep_meta_imp_swap.transitive_dependents,
            vec!["Smoke.M".to_string()]
        );
        assert_eq!(
            rep_meta_imp_swap.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\n  /- meta cmt -/ public  meta  import  Smoke.Provider1 -- m1\n  public  meta  import  Smoke.Provider2\npublic meta def metaConst : Nat := 1\n",
        )?;
        let rep_meta_imp_ws = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert!(!rep_meta_imp_ws.public_signature_changed);
        assert!(!rep_meta_imp_ws.meta_signature_changed);
        assert_eq!(
            Some(rep_meta_imp_ws.meta_signature_digest.as_str()),
            rep_meta_imp_ws.baseline_meta_signature_digest.as_deref()
        );
        assert!(rep_meta_imp_ws.transitive_dependents.is_empty());
        assert_eq!(
            rep_meta_imp_ws.pruned_dependents,
            vec![
                "Smoke.B".to_string(),
                "Smoke.C".to_string(),
                "Smoke.M".to_string()
            ]
        );

        fs::write(
            proj.join("Smoke/Provider1.lean"),
            "module\nsyntax \"makeVal\" : term\nmacro_rules | `(makeVal) => `((0 : Nat))\n",
        )?;
        fs::write(
            proj.join("Smoke/Provider2.lean"),
            "module\nsyntax \"makeVal\" : term\nmacro_rules | `(makeVal) => `(true)\n",
        )?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic meta import Smoke.Provider1\npublic def api := makeVal\npublic meta def helperMeta : Nat := 1\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useApi : Nat := api + 1\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useApiC : Nat := useApi\n",
        )?;
        fs::write(
            proj.join("Smoke/M.lean"),
            "module\nmeta import Smoke.A\nmeta def useMeta : Nat := helperMeta\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "public meta import macro provider baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string(), "Smoke.M".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic meta import Smoke.Provider1\npublic def api := makeVal\npublic meta def helperMeta : Nat := 2\n",
        )?;
        let rep_meta_def_only = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_meta_def_only.edit_class, "meta_only_module_edit");
        assert!(!rep_meta_def_only.public_signature_changed);
        assert!(rep_meta_def_only.meta_signature_changed);
        assert_eq!(
            rep_meta_def_only.transitive_dependents,
            vec!["Smoke.M".to_string()]
        );
        assert_eq!(
            rep_meta_def_only.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic meta import Smoke.Provider2\npublic def api := makeVal\npublic meta def helperMeta : Nat := 1\n",
        )?;
        let rep_pub_meta_macro = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_pub_meta_macro.edit_class, "public_signature_edit");
        assert!(rep_pub_meta_macro.public_signature_changed);
        assert!(rep_pub_meta_macro.meta_signature_changed);
        assert_eq!(
            rep_pub_meta_macro.transitive_dependents,
            vec![
                "Smoke.B".to_string(),
                "Smoke.C".to_string(),
                "Smoke.M".to_string()
            ]
        );
        assert!(rep_pub_meta_macro.pruned_dependents.is_empty());
        let err_pub_meta_macro = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(err_pub_meta_macro.is_err());

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic meta import all Smoke.Provider2\npublic def api := makeVal\npublic meta def helperMeta : Nat := 1\n",
        )?;
        let err_pub_meta_all = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("invalid `public meta import all` header must fail closed in impact");
        assert!(
            format!("{err_pub_meta_all:#}").contains("cannot use `all` with `public import`"),
            "unexpected header error: {err_pub_meta_all:#}"
        );

        let a_pub_meta_ctx_v1 = "\
module
public meta def useNat : Bool := true
macro \"makeVal\" : term => if useNat then `((0 : Nat)) else `(true)
public def api := makeVal
";
        let a_pub_meta_ctx_v2 = "\
module
public meta def useNat : Bool := false
macro \"makeVal\" : term => if useNat then `((0 : Nat)) else `(true)
public def api := makeVal
";
        fs::write(proj.join("Smoke/A.lean"), a_pub_meta_ctx_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useApi : Nat := api + 1\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useApiC : Nat := useApi\n",
        )?;
        fs::write(
            proj.join("Smoke/M.lean"),
            "module\nmeta import Smoke.A\nmeta def useMeta : Bool := useNat\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "public meta def macro context baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string(), "Smoke.M".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_pub_meta_ctx_v2)?;
        let rep_pub_meta_ctx = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_pub_meta_ctx.edit_class, "public_signature_edit");
        assert!(
            rep_pub_meta_ctx.public_signature_changed,
            "preceding `public meta def` controlling macro before `public def` must mark `public_signature_changed = true`"
        );
        assert!(rep_pub_meta_ctx.meta_signature_changed);
        assert_eq!(
            rep_pub_meta_ctx.transitive_dependents,
            vec![
                "Smoke.B".to_string(),
                "Smoke.C".to_string(),
                "Smoke.M".to_string()
            ]
        );
        assert!(
            rep_pub_meta_ctx.pruned_dependents.is_empty(),
            "ordinary public importers must NOT be pruned when preceding `public meta def` changes `api` from `Nat` to `Bool`"
        );
        let err_pub_meta_ctx = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_pub_meta_ctx.is_err(),
            "downstream ordinary consumer Smoke.B must be rechecked and fail when `useNat` flips `api` from `Nat` to `Bool`"
        );

        let a_trail_attr_v1 = "\
module
namespace SmokeA
public class MyTag (α : Type) where
  tag : Nat
@[expose, instance_reducible] public def mkTag100 : MyTag Nat := { tag := 1 }
@[expose, instance_reducible] public def mkTag150 : MyTag Nat := { tag := 2 }
attribute [instance 150] mkTag150
attribute [instance 100] mkTag100
end SmokeA
";
        let a_trail_attr_v2 = "\
module
namespace SmokeA
public class MyTag (α : Type) where
  tag : Nat
@[expose, instance_reducible] public def mkTag100 : MyTag Nat := { tag := 1 }
@[expose, instance_reducible] public def mkTag150 : MyTag Nat := { tag := 2 }
attribute [instance 150] mkTag150
attribute [instance 200] mkTag100
end SmokeA
";
        fs::write(proj.join("Smoke/A.lean"), a_trail_attr_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic theorem useTag : (inferInstance : SmokeA.MyTag Nat).tag = 2 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic theorem useTagC : (inferInstance : SmokeA.MyTag Nat).tag = 2 := useTag\n",
        )?;
        let _ = fs::remove_file(proj.join("Smoke/M.lean"));
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "trailing non-local attribute baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;

        fs::write(proj.join("Smoke/A.lean"), a_trail_attr_v2)?;
        let rep_trail_attr = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_trail_attr.edit_class, "public_signature_edit");
        assert!(
            rep_trail_attr.public_signature_changed,
            "trailing `attribute [instance 100]` -> `200` outside `public section` must mark `public_signature_changed = true`"
        );
        assert!(rep_trail_attr.meta_signature_changed);
        assert_eq!(
            rep_trail_attr.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(
            rep_trail_attr.pruned_dependents.is_empty(),
            "downstream consumers must not be pruned on trailing non-local attribute edit"
        );
        // Consumer `Smoke.B` actually fails to elaborate when `mkTag100` priority rises from 100 to 200 (`tag = 1` != `2`),
        // proving `lake_recheck_dependents_with_store` does NOT cut off at `Smoke.A` and rechecks `Smoke.B`.
        let err_recheck = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_recheck.is_err(),
            "downstream consumer Smoke.B must be rechecked (and fail typechecking) when trailing `attribute [instance 100]` changes to `200`"
        );

        let a_trail_local_attr_v1 =
            format!("{a_trail_attr_v1}attribute [local instance 300] SmokeA.mkTag100\n");
        let a_trail_local_attr_v2 =
            format!("{a_trail_attr_v1}attribute [local instance 400] SmokeA.mkTag100\n");
        fs::write(proj.join("Smoke/A.lean"), &a_trail_local_attr_v1)?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "trailing local attribute baseline"])?;
        fs::write(proj.join("Smoke/A.lean"), &a_trail_local_attr_v2)?;
        let rep_trail_local_attr = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_trail_local_attr.edit_class, "private_module_edit");
        assert!(
            !rep_trail_local_attr.public_signature_changed,
            "trailing `attribute [local ...]` edit after all public declarations must stay `private_module_edit`"
        );
        assert!(!rep_trail_local_attr.meta_signature_changed);
        assert!(rep_trail_local_attr.transitive_dependents.is_empty());
        assert_eq!(
            rep_trail_local_attr.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        // Command-bearing diagnostic wrappers (`#time`, `#guard_msgs`, `#info_trees`, `#with_exporting`,
        // `open ... in #time`, `#eval`, `assert_not_exists`, `#exit`) must NEVER be discarded as pure
        // diagnostics in `compute_impact_report`: exported signature/body/directive edits under them
        // must mark `public_signature_changed = true` and retain downstream dependents (`Smoke.B`, `Smoke.C`).
        let a_time_v1 = "module\n#time\n@[expose] public def timedApi : Nat := 1\n";
        let a_time_v2 = "module\n#time\n@[expose] public def timedApi : Nat := 2\n";
        fs::write(proj.join("Smoke/A.lean"), a_time_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic theorem useTimed : timedApi = 1 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic theorem useTimedC : timedApi = 1 := useTimed\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "time wrapper baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;

        fs::write(proj.join("Smoke/A.lean"), a_time_v2)?;
        let rep_time = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_time.edit_class, "public_signature_edit");
        assert!(
            rep_time.public_signature_changed,
            "`#time` wrapping `@[expose] public def` edit must mark `public_signature_changed = true`"
        );
        assert!(rep_time.meta_signature_changed);
        assert_eq!(
            rep_time.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(
            rep_time.pruned_dependents.is_empty(),
            "downstream consumers must NOT be pruned when `#time`-wrapped public declaration changes"
        );
        let err_time_recheck = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_time_recheck.is_err(),
            "downstream consumer Smoke.B (`timedApi = 1`) must be rechecked and fail when `timedApi` changes to `2` under `#time`"
        );

        let a_guard_msgs_v1 = "module\n#guard_msgs (drop info) in\npublic def gmApi : Nat := 1\n";
        let a_guard_msgs_v2 =
            "module\n#guard_msgs (drop info) in\npublic def gmApi : Bool := true\n";
        fs::write(proj.join("Smoke/A.lean"), a_guard_msgs_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useGm : Nat := gmApi\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic def useGmC : Nat := useGm\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "guard_msgs wrapper baseline"])?;
        fs::write(proj.join("Smoke/A.lean"), a_guard_msgs_v2)?;
        let rep_gm = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_gm.edit_class, "public_signature_edit");
        assert!(rep_gm.public_signature_changed);
        assert_eq!(
            rep_gm.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_gm.pruned_dependents.is_empty());

        // Moving a scope boundary (`end`) before vs after a `public def` (changing whether
        // section-local `variable (x : Nat)` / `open` applies to `public def`) must mark
        // `public_signature_changed = true`, retain downstream consumers in `compute_impact_report`,
        // and refuse early cutoff in `lake_recheck_dependents_with_store` (catching real downstream breakage).
        let a_sec_v1 = "module\nsection\nvariable (x : Nat)\npublic def secApi : Nat := x\nend\n";
        let a_sec_v2 = "module\nsection\nvariable (x : Nat)\nend\npublic def secApi : Nat := 0\n";
        fs::write(proj.join("Smoke/A.lean"), a_sec_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useSec : Nat := secApi 42\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic def useSecC : Nat := useSec\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "section boundary baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_sec_v2)?;
        let rep_sec = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_sec.edit_class, "public_signature_edit");
        assert!(
            rep_sec.public_signature_changed,
            "moving `end` before `public def` must mark `public_signature_changed = true`"
        );
        assert!(rep_sec.meta_signature_changed);
        assert_eq!(
            rep_sec.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(
            rep_sec.pruned_dependents.is_empty(),
            "downstream consumers must NOT be pruned when `section ... end` boundary shifts across `public def`"
        );
        let err_sec_recheck = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_sec_recheck.is_err(),
            "downstream consumer Smoke.B (`secApi 42`) must be rechecked and fail when `end` moves before `secApi` (0-ary `Nat`)"
        );

        // Moving `end` before vs after an exported `attribute [instance ...]` directive where a
        // section-scoped `open` selects which candidate receives `[instance 200]` must mark
        // `public_signature_changed = true` and fail downstream recheck instead of falsely cutting off.
        let a_dir_sec_v1 = "\
module
public class Tag (α : Type) where val : Nat
@[expose, instance_reducible] public def instTag : Tag Nat := { val := 22 }
namespace Foo
@[expose, instance_reducible] public def instTag : Tag Nat := { val := 11 }
attribute [instance 200] instTag
end Foo
";
        let a_dir_sec_v2 = "\
module
public class Tag (α : Type) where val : Nat
@[expose, instance_reducible] public def instTag : Tag Nat := { val := 22 }
namespace Foo
@[expose, instance_reducible] public def instTag : Tag Nat := { val := 11 }
end Foo
attribute [instance 200] instTag
";
        fs::write(proj.join("Smoke/A.lean"), a_dir_sec_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\nattribute [instance 150] _root_.instTag\npublic theorem useDirSec : (inferInstance : Tag Nat).val = 11 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic theorem useDirSecC : (inferInstance : Tag Nat).val = 11 := useDirSec\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "directive section boundary baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_dir_sec_v2)?;
        let rep_dir_sec = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_dir_sec.edit_class, "public_signature_edit");
        assert!(
            rep_dir_sec.public_signature_changed,
            "moving `end` before exported `notation` must mark `public_signature_changed = true`"
        );
        assert_eq!(
            rep_dir_sec.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_dir_sec.pruned_dependents.is_empty());
        let err_dir_sec_recheck = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_dir_sec_recheck.is_err(),
            "downstream consumer Smoke.B must be rechecked and fail when `end` moves before `attribute [instance 200] instTag`"
        );

        // Moving `end` before vs after an exported `macro` directive where a section-scoped
        // `set_option hygiene false` governs macro hygiene must mark `public_signature_changed = true`
        // and fail downstream recheck instead of falsely cutting off.
        let a_sec_macro_v1 = "\
module
section
set_option hygiene false
macro \"SEC_VAL\" : term => `(macVal)
end
";
        let a_sec_macro_v2 = "\
module
section
set_option hygiene false
end
macro \"SEC_VAL\" : term => `(macVal)
";
        fs::write(proj.join("Smoke/A.lean"), a_sec_macro_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\n@[expose] public def macVal : Nat := 11\npublic theorem useSecMacro : SEC_VAL = 11 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic theorem useSecMacroC : SEC_VAL = 11 := useSecMacro\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "section macro boundary baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_sec_macro_v2)?;
        let rep_sec_macro = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_sec_macro.edit_class, "public_signature_edit");
        assert!(
            rep_sec_macro.public_signature_changed,
            "moving unnamed `section ... end` before exported `macro` must mark `public_signature_changed = true`"
        );
        assert_eq!(
            rep_sec_macro.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_sec_macro.pruned_dependents.is_empty());
        let err_sec_macro_recheck = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_sec_macro_recheck.is_err(),
            "downstream consumer Smoke.B (`SEC_VAL = 11`) must be rechecked and fail when unnamed `end` moves before `macro \"SEC_VAL\"`"
        );

        // Editing or renaming a trailing private `section ... end` containing private theorems
        // after all public declarations must classify as `private_module_edit`
        // (`public_signature_changed = false`), prune downstream dependents `Smoke.B` and `Smoke.C`
        // in `compute_impact_report`, and cut off Stage-2 native recheck after `Smoke.A` (since
        // `.ir`/`.ir.sig` and `dumpPublicSignatureJson` stay unchanged).
        let a_trail_sec_v1 =
            "module\npublic def apiStable : Nat := 7\nsection Priv1\nvariable (k : Nat)\nprivate theorem p : k = k := rfl\nend Priv1\n";
        let a_trail_sec_v2 =
            "module\npublic def apiStable : Nat := 7\nsection Priv2\nvariable (b : Bool)\nprivate theorem p2 : b = b := rfl\nend Priv2\n";
        fs::write(proj.join("Smoke/A.lean"), a_trail_sec_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useStable : Nat := apiStable\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic def useStableC : Nat := useStable\n",
        )?;
        let _ = fs::remove_file(proj.join("Smoke/Provider1.lean"));
        let _ = fs::remove_file(proj.join("Smoke/Provider2.lean"));
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "trailing private section baseline"])?;
        fs::write(proj.join("Smoke/A.lean"), a_trail_sec_v2)?;
        let rep_trail_sec = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_trail_sec.edit_class, "private_module_edit");
        assert!(
            !rep_trail_sec.public_signature_changed,
            "trailing private `section ... end` edit must NOT mark `public_signature_changed = true`"
        );
        assert!(!rep_trail_sec.meta_signature_changed);
        assert!(rep_trail_sec.transitive_dependents.is_empty());
        assert_eq!(
            rep_trail_sec.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        let (n_trail_sec, _, mods_trail_sec, _) = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        )?;
        assert_eq!(n_trail_sec, 1);
        assert_eq!(mods_trail_sec, vec!["Smoke.A".to_string()]);

        // Also verify compute_impact_report prunes downstream dependents even when the trailing
        // private section contains `private def` items.
        let a_trail_priv_def =
            "module\npublic def apiStable : Nat := 7\nsection Priv3\nvariable (m : Nat)\nprivate def pDef : Nat := m + 1\nend Priv3\n";
        fs::write(proj.join("Smoke/A.lean"), a_trail_priv_def)?;
        let rep_trail_priv_def = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_trail_priv_def.edit_class, "private_module_edit");
        assert!(!rep_trail_priv_def.public_signature_changed);
        assert!(!rep_trail_priv_def.meta_signature_changed);
        assert!(rep_trail_priv_def.transitive_dependents.is_empty());
        assert_eq!(
            rep_trail_priv_def.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        // Placeholder return-type / binder-type / unannotated-binder declarations MUST classify
        // body edits as `public_signature_edit` (NOT `private_module_edit` or `proof_body_only`)
        // and retain downstream dependents (`Smoke.B`, `Smoke.C`), while fully annotated public
        // definitions and theorems preserve `private_module_edit` / `proof_body_only` cutoff.
        for (commit_msg, base_a, edited_a) in [
            (
                "placeholder return type `_` baseline",
                "module\npublic def api : _ := (0 : Nat)\n",
                "module\npublic def api : _ := true\n",
            ),
            (
                "partial placeholder return type `List _` baseline",
                "module\npublic def api : List _ := [0]\n",
                "module\npublic def api : List _ := [true]\n",
            ),
            (
                "named hole return type `?_` baseline",
                "module\npublic def api : ?_ := 0\n",
                "module\npublic def api : ?_ := true\n",
            ),
            (
                "placeholder theorem statement `: _` baseline",
                "module\npublic theorem thm : _ := True.intro\n",
                "module\npublic theorem thm : _ := (rfl : 0 = 0)\n",
            ),
            (
                "placeholder binder `(x : _)` baseline",
                "module\npublic def api (x : _) : Nat := x + 1\n",
                "module\npublic def api (x : _) : Nat := if x then 1 else 0\n",
            ),
            (
                "unannotated binder `(x)` baseline",
                "module\npublic def api (x) : Nat := x + 1\n",
                "module\npublic def api (x) : Nat := if x then 1 else 0\n",
            ),
            (
                "bare binder `x` baseline",
                "module\npublic def api x : Nat := x + 1\n",
                "module\npublic def api x : Nat := if x then 1 else 0\n",
            ),
            (
                "unannotated implicit binder `{x}` baseline",
                "module\npublic def api {x} : Nat := x + 1\n",
                "module\npublic def api {x} : Nat := if x then 1 else 0\n",
            ),
            (
                "placeholder strict-implicit binder `⦃x : _⦄` baseline",
                "module\npublic def api ⦃x : _⦄ : Nat := x + 1\n",
                "module\npublic def api ⦃x : _⦄ : Nat := if x then 1 else 0\n",
            ),
            (
                "strict-implicit binder `⦃x : Nat⦄` without top-level return type baseline",
                "module\npublic def api ⦃x : Nat⦄ := x + 1\n",
                "module\npublic def api ⦃x : Nat⦄ := true\n",
            ),
        ] {
            fs::write(proj.join("Smoke/A.lean"), base_a)?;
            fs::write(
                proj.join("Smoke/B.lean"),
                "module\npublic import Smoke.A\npublic def useB : Nat := 1\n",
            )?;
            fs::write(
                proj.join("Smoke/C.lean"),
                "module\npublic import Smoke.B\npublic def useC : Nat := useB\n",
            )?;
            run_git(&["add", "-A"])?;
            run_git(&["commit", "-m", commit_msg])?;
            fs::write(proj.join("Smoke/A.lean"), edited_a)?;
            let rep_hole = compute_impact_report(
                proj.join("Smoke/A.lean"),
                Some(proj.clone()),
                Some("HEAD".to_string()),
            )?;
            assert_eq!(
                rep_hole.edit_class, "public_signature_edit",
                "{commit_msg}: body edit on placeholder/unannotated-binder decl must be public_signature_edit"
            );
            assert!(
                rep_hole.public_signature_changed,
                "{commit_msg}: public_signature_changed must be true"
            );
            assert_eq!(
                rep_hole.transitive_dependents,
                vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
            );
            assert!(rep_hole.pruned_dependents.is_empty());
        }

        // Fully annotated `public theorem thm (x_1 : Nat) : x_1 = x_1` BEFORE `public def api.{u} (x_1 : _root_.Nat) : Nat`
        // keeps `proof_body_only` (theorem proof edit before public def) and `private_module_edit`
        // (trailing unexposed public def body edit) cutoff intact.
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic theorem thm (x_1 : Nat) : x_1 = x_1 := rfl\npublic def api.{u} (x_1 : _root_.Nat) : Nat := x_1 + 1\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "fully annotated thm before def baseline"])?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic theorem thm (x_1 : Nat) : x_1 = x_1 := rfl\npublic def api.{u} (x_1 : _root_.Nat) : Nat := 1 + x_1\n",
        )?;
        let rep_annot_def = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_annot_def.edit_class, "private_module_edit");
        assert!(!rep_annot_def.public_signature_changed);
        assert!(rep_annot_def.transitive_dependents.is_empty());
        assert_eq!(
            rep_annot_def.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic theorem thm (x_1 : Nat) : x_1 = x_1 := Eq.refl x_1\npublic def api.{u} (x_1 : _root_.Nat) : Nat := x_1 + 1\n",
        )?;
        let rep_annot_thm = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_annot_thm.edit_class, "proof_body_only");
        assert!(!rep_annot_thm.public_signature_changed);
        assert!(rep_annot_thm.transitive_dependents.is_empty());
        assert_eq!(
            rep_annot_thm.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        // P2 4481733184 regression: within a `module`, an unexposed `public def flag : Bool := true`
        // is reducible to subsequent declarations inside the same module! Flipping `flag` from `true`
        // to `false` changes `api`'s elaborated type from `Nat` to `Bool`, so `compute_impact_report`
        // MUST classify as `public_signature_edit` (`public_signature_changed == true`) and retain
        // `Smoke.B` and `Smoke.C` (and Stage-2 native recheck must fail on broken `Smoke.B`).
        let a_p2_intra_v1 = "\
module
public def flag : Bool := true
public def api := by
  first
  | have h : flag = true := rfl
    exact (0 : Nat)
  | exact false
";
        let a_p2_intra_v2 = "\
module
public def flag : Bool := false
public def api := by
  first
  | have h : flag = true := rfl
    exact (0 : Nat)
  | exact false
";
        fs::write(proj.join("Smoke/A.lean"), a_p2_intra_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useB : Nat := api + 1\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic def useC : Nat := useB\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&[
            "commit",
            "-m",
            "intra-module public def reducibility baseline",
        ])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_p2_intra_v2)?;
        let rep_p2_intra = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_p2_intra.edit_class, "public_signature_edit");
        assert!(
            rep_p2_intra.public_signature_changed,
            "preceding unexposed `public def flag : Bool` edit before `public def api := ...` must mark `public_signature_changed = true`"
        );
        assert!(rep_p2_intra.meta_signature_changed);
        assert_eq!(
            rep_p2_intra.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_p2_intra.pruned_dependents.is_empty());
        let err_p2_intra_recheck = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_p2_intra_recheck.is_err(),
            "downstream consumer Smoke.B (`api + 1`) must be rechecked and fail when `flag` flips `api` from `Nat` to `Bool`"
        );

        for (commit_msg, base_a, edited_a) in [
            (
                "preceding public def type alias baseline",
                "module\npublic def ty : Type := Nat\npublic def useTy (x : ty) : ty := x\n",
                "module\npublic def ty : Type := Bool\npublic def useTy (x : ty) : ty := x\n",
            ),
            (
                "preceding public section def baseline",
                "module\npublic section\ndef flag : Bool := true\ndef api := flag\nend\n",
                "module\npublic section\ndef flag : Bool := false\ndef api := flag\nend\n",
            ),
            (
                "mutual public def sibling baseline",
                "module\nmutual\n  public def a := b\n  public def b : Bool := true\nend\n",
                "module\nmutual\n  public def a := b\n  public def b : Bool := false\nend\n",
            ),
            (
                "preceding public def before exported notation baseline",
                "module\npublic def flag : Bool := true\nnotation \"PUB_FLAG\" => flag\n",
                "module\npublic def flag : Bool := false\nnotation \"PUB_FLAG\" => flag\n",
            ),
        ] {
            fs::write(proj.join("Smoke/A.lean"), base_a)?;
            fs::write(
                proj.join("Smoke/B.lean"),
                "module\npublic import Smoke.A\npublic def useB : Nat := 1\n",
            )?;
            fs::write(
                proj.join("Smoke/C.lean"),
                "module\npublic import Smoke.B\npublic def useC : Nat := useB\n",
            )?;
            run_git(&["add", "-A"])?;
            run_git(&["commit", "-m", commit_msg])?;
            fs::write(proj.join("Smoke/A.lean"), edited_a)?;
            let rep_sub = compute_impact_report(
                proj.join("Smoke/A.lean"),
                Some(proj.clone()),
                Some("HEAD".to_string()),
            )?;
            assert_eq!(
                rep_sub.edit_class, "public_signature_edit",
                "{commit_msg}: preceding public def body edit must be public_signature_edit"
            );
            assert!(rep_sub.public_signature_changed);
            assert_eq!(
                rep_sub.transitive_dependents,
                vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
            );
            assert!(rep_sub.pruned_dependents.is_empty());
        }

        // Preceding unexposed `public def` edit followed ONLY by `public meta def` classifies as
        // `meta_only_module_edit`, retaining `Smoke.M` (`meta import Smoke.A`) while pruning
        // ordinary importers `Smoke.B` and `Smoke.C`!
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic def flag : Bool := true\npublic meta def metaApi : Bool := flag\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useB : Bool := flag\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic def useC : Bool := useB\n",
        )?;
        fs::write(
            proj.join("Smoke/M.lean"),
            "module\nmeta import Smoke.A\nmeta def useMeta : Bool := metaApi\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&[
            "commit",
            "-m",
            "preceding public def before public meta def baseline",
        ])?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic def flag : Bool := false\npublic meta def metaApi : Bool := flag\n",
        )?;
        let rep_pub_before_meta = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_pub_before_meta.edit_class, "meta_only_module_edit");
        assert!(!rep_pub_before_meta.public_signature_changed);
        assert!(rep_pub_before_meta.meta_signature_changed);
        assert_eq!(
            rep_pub_before_meta.transitive_dependents,
            vec!["Smoke.M".to_string()]
        );
        assert_eq!(
            rep_pub_before_meta.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_speed4_cutoff_shielded_fails_closed_on_stale_non_cutoff_dependencies() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_speed4_cutoff_non_cutoff_deps_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let proj = tmp_dir.join("proj");
        let dep_dir = proj.join(".lake/packages/dep_pkg");
        let pb_pkg = tmp_dir.join("pb_pkg");
        let cache = tmp_dir.join("cache");
        fs::create_dir_all(proj.join("Smoke"))?;
        fs::create_dir_all(dep_dir.join("DepPkg"))?;
        fs::create_dir_all(pb_pkg.join("Prebuilt"))?;
        fs::create_dir_all(&cache)?;

        let tc = "leanprover/lean4:v4.35.0\n";
        fs::write(proj.join("lean-toolchain"), tc)?;
        fs::write(dep_dir.join("lean-toolchain"), tc)?;
        fs::write(pb_pkg.join("lean-toolchain"), tc)?;

        fs::write(
            pb_pkg.join("lakefile.toml"),
            "name = \"pb_pkg\"\ndefaultTargets = [\"Prebuilt\"]\n[[lean_lib]]\nname = \"Prebuilt\"\nglobs = [\"Prebuilt.+\"]\n",
        )?;
        let pb_v1 = "module\n@[expose] public def pbVal : Nat := 100\n";
        let pb_v2 = "module\n@[expose] public def pbVal : Nat := 200\n";
        fs::write(pb_pkg.join("Prebuilt/Ext.lean"), pb_v1)?;

        let mut store = TurboStore::open(Some(&cache))?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &pb_pkg,
            &["Prebuilt.Ext".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let pb_lib_dir = pb_pkg
            .join(".lake/build/lib/lean")
            .canonicalize()
            .unwrap_or_else(|_| pb_pkg.join(".lake/build/lib/lean"));

        struct LeanPathEnvGuard(Option<std::ffi::OsString>);
        impl Drop for LeanPathEnvGuard {
            fn drop(&mut self) {
                match &self.0 {
                    Some(v) => std::env::set_var("LEAN_PATH", v),
                    None => std::env::remove_var("LEAN_PATH"),
                }
            }
        }
        let _lp_guard = LeanPathEnvGuard(std::env::var_os("LEAN_PATH"));
        std::env::set_var("LEAN_PATH", &pb_lib_dir);

        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepPkg\"\nroots = [\"DepPkg.Base\"]\n",
        )?;
        let dep_v1 = "module\n@[expose] public def depVal : Nat := 10\n";
        let dep_v2 = "module\n@[expose] public def depVal : Nat := 20\n";
        fs::write(dep_dir.join("DepPkg/Base.lean"), dep_v1)?;

        let manifest_json = r#"{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {
      "type": "path",
      "name": "dep_pkg",
      "dir": ".lake/packages/dep_pkg",
      "configFile": "lakefile.toml",
      "inherited": false
    }
  ],
  "name": "cutoff_pin_smoke",
  "lakeDir": ".lake",
  "fixedToolchain": false
}"#;
        fs::write(proj.join("lake-manifest.json"), manifest_json)?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"cutoff_pin_smoke\"\ndefaultTargets = [\"Smoke\"]\n[[lean_lib]]\nname = \"Smoke\"\nroots = [\"Smoke.A\", \"Smoke.U\", \"Smoke.B\", \"Smoke.C\"]\n",
        )?;

        let a_base = "module\n@[expose] public def pubA : Nat := 1\npublic theorem a_thm (n : Nat) : n + 0 = n := by\n  exact Nat.add_zero n\n";
        let a_priv_v1 = "module\n@[expose] public def pubA : Nat := 1\npublic theorem a_thm (n : Nat) : n + 0 = n := by\n  have _h1 : 1 + 1 = 2 := rfl\n  exact Nat.add_zero n\nprivate theorem extra_priv_1 : 2 + 2 = 4 := rfl\n";
        let a_priv_v2 = "module\n@[expose] public def pubA : Nat := 1\npublic theorem a_thm (n : Nat) : n + 0 = n := by\n  have _h2 : 3 + 3 = 6 := rfl\n  exact Nat.add_zero n\nprivate theorem extra_priv_2 : 4 + 4 = 8 := rfl\n";
        let a_priv_v3 = "module\n@[expose] public def pubA : Nat := 1\npublic theorem a_thm (n : Nat) : n + 0 = n := by\n  have _h3 : 5 + 5 = 10 := rfl\n  exact Nat.add_zero n\nprivate theorem extra_priv_3 : 6 + 6 = 12 := rfl\n";
        let a_priv_v4 = "module\n@[expose] public def pubA : Nat := 1\npublic theorem a_thm (n : Nat) : n + 0 = n := by\n  have _h4 : 7 + 7 = 14 := rfl\n  exact Nat.add_zero n\nprivate theorem extra_priv_4 : 8 + 8 = 16 := rfl\n";
        let a_priv_v5 = "module\n@[expose] public def pubA : Nat := 1\npublic theorem a_thm (n : Nat) : n + 0 = n := by\n  have _h5 : 9 + 9 = 18 := rfl\n  exact Nat.add_zero n\nprivate theorem extra_priv_5 : 10 + 10 = 20 := rfl\n";

        let u_v1 = "module\n@[expose] public def uVal : Nat := 5\n";
        let u_v2 = "module\n@[expose] public def uVal : Nat := 6\n";
        let b_src = "module\npublic import Smoke.A\npublic import Smoke.U\npublic import DepPkg.Base\npublic import Prebuilt.Ext\n@[expose] public def bVal : Nat := pubA + uVal + depVal + pbVal\n";
        let c_src = "module\npublic import Smoke.B\n@[expose] public def cVal : Nat := bVal + 1\n";
        let s_ok = "module\nimport Smoke.B\nimport Smoke.U\ntheorem s_thm : bVal = 116 := rfl\n";

        fs::write(proj.join("Smoke/A.lean"), a_base)?;
        fs::write(proj.join("Smoke/U.lean"), u_v1)?;
        fs::write(proj.join("Smoke/B.lean"), b_src)?;
        fs::write(proj.join("Smoke/C.lean"), c_src)?;
        fs::write(proj.join("Smoke/StandaloneCheck.lean"), s_ok)?;

        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let canon_proj = proj.canonicalize().unwrap_or_else(|_| proj.clone());

        fs::write(proj.join("Smoke/A.lean"), a_priv_v1)?;
        let (n_clean, _, mods_clean, _) = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            None,
            false,
        )?;
        assert_eq!(n_clean, 1);
        assert_eq!(mods_clean, vec!["Smoke.A".to_string()]);

        fs::write(proj.join("Smoke/U.lean"), u_v2)?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.U".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(
            proj.join("Smoke/StandaloneCheck.lean"),
            "module\nimport Smoke.B\nimport Smoke.U\ntheorem s_thm : bVal = 117 := rfl\n",
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_priv_v2)?;
        let (n_stale_local, _, mut mods_stale_local, _) = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            None,
            false,
        )?;
        mods_stale_local.sort();
        assert_eq!(
            mods_stale_local,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(n_stale_local, 4);
        assert!(load_verified_project_manifest(&canon_proj)
            .is_some_and(|m| m.modules.contains_key("Smoke/B.lean")
                && m.modules.contains_key("Smoke/C.lean")));

        fs::write(dep_dir.join("DepPkg/Base.lean"), dep_v2)?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &dep_dir,
            &["DepPkg.Base".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(
            proj.join("Smoke/StandaloneCheck.lean"),
            "module\nimport Smoke.B\nimport Smoke.U\ntheorem s_thm : bVal = 127 := rfl\n",
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_priv_v3)?;
        let (n_stale_dep_pkg, _, mut mods_stale_dep_pkg, _) = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            None,
            false,
        )?;
        mods_stale_dep_pkg.sort();
        assert_eq!(
            mods_stale_dep_pkg,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(n_stale_dep_pkg, 4);

        fs::write(pb_pkg.join("Prebuilt/Ext.lean"), pb_v2)?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &pb_pkg,
            &["Prebuilt.Ext".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(
            proj.join("Smoke/StandaloneCheck.lean"),
            "module\nimport Smoke.B\nimport Smoke.U\ntheorem s_thm : bVal = 227 := rfl\n",
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_priv_v4)?;
        let (n_stale_prebuilt, _, mut mods_stale_prebuilt, _) = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            None,
            false,
        )?;
        mods_stale_prebuilt.sort();
        assert_eq!(
            mods_stale_prebuilt,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(n_stale_prebuilt, 4);

        let manifest_path = verified_sources_manifest_path(&canon_proj);
        fs::remove_file(&manifest_path)?;
        fs::remove_file(canon_proj.join(".lake/build/lib/lean/Smoke/U.olean"))?;
        fs::write(
            proj.join("Smoke/StandaloneCheck.lean"),
            "module\nimport Smoke.A\nimport Smoke.U\ntheorem s_thm : pubA + uVal = 7 := rfl\n",
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_priv_v5)?;
        let (n_lake_only_stale, _, mut mods_lake_only_stale, _) =
            lake_recheck_dependents_with_store(
                Some(&store),
                &canon_proj,
                &["Smoke/A.lean".to_string()],
                None,
                false,
            )?;
        mods_lake_only_stale.sort();
        assert_eq!(
            mods_lake_only_stale,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(n_lake_only_stale, 4);
        assert!(canon_proj
            .join(".lake/build/lib/lean/Smoke/U.olean")
            .is_file());

        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic import Smoke.U\npublic import DepPkg.Base\n@[expose] public def bVal : Nat := pubA + uVal + depVal\n",
        )?;
        fs::write(
            proj.join("Smoke/StandaloneCheck.lean"),
            "module\nimport Smoke.B\nimport Smoke.U\ntheorem s_thm : bVal = 27 := rfl\n",
        )?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "untrusted",
            1,
            false,
            true,
            None,
        )?;
        let closure_strict =
            compute_project_dependent_closure(&canon_proj, &["Smoke/A.lean".to_string()], true)?;
        let dag_strict = closure_strict.dag.as_ref().unwrap();
        let baselines_strict = capture_pre_rebuild_module_baselines(
            &store.root,
            &closure_strict.cfg,
            dag_strict,
            &closure_strict.edited_dag_modules,
            None,
            false,
        )
        .unwrap();
        let (pre_raw_strict, pre_man_strict) = load_pre_rebuild_root_manifest(&canon_proj);
        let mut verdicts_strict = HashMap::new();
        verdicts_strict.insert(
            "Smoke.A".to_string(),
            ModuleCutoffVerdict {
                cuts_off_public: true,
                cuts_off_meta: true,
            },
        );
        let edited_standalone_empty = std::collections::BTreeSet::new();
        let (rechecked_strict_clean, _, standalone_strict_clean, memo_strict_clean) =
            compute_stage2_dependent_closure_after_cutoff(
                &canon_proj,
                &closure_strict,
                dag_strict,
                &edited_standalone_empty,
                &baselines_strict,
                &verdicts_strict,
                &pre_raw_strict,
                pre_man_strict.as_ref(),
                Some(&store),
            )?;
        assert_eq!(rechecked_strict_clean, vec!["Smoke.A".to_string()]);
        assert!(standalone_strict_clean.is_empty());
        assert_eq!(memo_strict_clean.get("Smoke.B"), Some(&true));

        let mut tampered_man = pre_man_strict.clone().unwrap();
        if let Some(ent_b) = tampered_man.modules.get_mut("Smoke/B.lean") {
            ent_b.import_olean_digests.insert(
                "Smoke.U".to_string(),
                "0000000000000000000000000000000000000000000000000000000000000000".to_string(),
            );
            ent_b.import_export_digests.insert(
                "Smoke.U".to_string(),
                "0000000000000000000000000000000000000000000000000000000000000000".to_string(),
            );
            ent_b.import_meta_digests.insert(
                "Smoke.U".to_string(),
                "0000000000000000000000000000000000000000000000000000000000000000".to_string(),
            );
        }
        let (mut rechecked_strict_tampered, _, standalone_strict_tampered, memo_strict_tampered) =
            compute_stage2_dependent_closure_after_cutoff(
                &canon_proj,
                &closure_strict,
                dag_strict,
                &edited_standalone_empty,
                &baselines_strict,
                &verdicts_strict,
                &pre_raw_strict,
                Some(&tampered_man),
                Some(&store),
            )?;
        rechecked_strict_tampered.sort();
        assert_eq!(
            rechecked_strict_tampered,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(memo_strict_tampered.get("Smoke.B"), Some(&false));
        assert_eq!(standalone_strict_tampered.len(), 1);

        let mut tampered_man_standalone = pre_man_strict.clone().unwrap();
        fs::write(
            proj.join("Smoke/StandaloneCheck.lean"),
            "module\nimport Smoke.A\nimport Smoke.U\ntheorem s_thm : pubA + uVal = 7 := rfl\n",
        )?;
        let closure_strict_sa =
            compute_project_dependent_closure(&canon_proj, &["Smoke/A.lean".to_string()], true)?;
        let dag_strict_sa = closure_strict_sa.dag.as_ref().unwrap();
        let (rechecked_sa_clean, _, standalone_sa_clean, _) =
            compute_stage2_dependent_closure_after_cutoff(
                &canon_proj,
                &closure_strict_sa,
                dag_strict_sa,
                &edited_standalone_empty,
                &baselines_strict,
                &verdicts_strict,
                &pre_raw_strict,
                Some(&tampered_man_standalone),
                Some(&store),
            )?;
        assert_eq!(rechecked_sa_clean, vec!["Smoke.A".to_string()]);
        assert!(standalone_sa_clean.is_empty());

        tampered_man_standalone.modules.remove("Smoke/U.lean");
        let (_, _, standalone_sa_u_unverified, _) = compute_stage2_dependent_closure_after_cutoff(
            &canon_proj,
            &closure_strict_sa,
            dag_strict_sa,
            &edited_standalone_empty,
            &baselines_strict,
            &verdicts_strict,
            &pre_raw_strict,
            Some(&tampered_man_standalone),
            Some(&store),
        )?;
        assert_eq!(standalone_sa_u_unverified.len(), 1);

        let (mut rechecked_strict_no_man, _, _, memo_strict_no_man) =
            compute_stage2_dependent_closure_after_cutoff(
                &canon_proj,
                &closure_strict,
                dag_strict,
                &edited_standalone_empty,
                &baselines_strict,
                &verdicts_strict,
                &None,
                None,
                Some(&store),
            )?;
        rechecked_strict_no_man.sort();
        assert_eq!(
            rechecked_strict_no_man,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(memo_strict_no_man.get("Smoke.B"), Some(&false));

        let canon_dep = dep_dir.canonicalize().unwrap_or_else(|_| dep_dir.clone());
        fs::remove_file(verified_sources_manifest_path(&canon_dep))?;
        let (mut rechecked_strict_dep_unverified, _, _, memo_strict_dep_unverified) =
            compute_stage2_dependent_closure_after_cutoff(
                &canon_proj,
                &closure_strict,
                dag_strict,
                &edited_standalone_empty,
                &baselines_strict,
                &verdicts_strict,
                &pre_raw_strict,
                pre_man_strict.as_ref(),
                Some(&store),
            )?;
        rechecked_strict_dep_unverified.sort();
        assert_eq!(
            rechecked_strict_dep_unverified,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(memo_strict_dep_unverified.get("Smoke.B"), Some(&false));

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_speed4_impact_report_fails_closed_on_invalid_config_dag_and_rev() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_speed4_impact_fail_closed_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let proj = tmp_dir.join("proj");
        let solo_dir = tmp_dir.join("solo");
        fs::create_dir_all(proj.join("Smoke"))?;
        fs::create_dir_all(&solo_dir)?;

        let tc = include_str!("../../../lean/lean-toolchain");
        fs::write(proj.join("lean-toolchain"), tc)?;
        let valid_lakefile =
            "name = \"smoke\"\n[[lean_lib]]\nname = \"Smoke\"\nglobs = [\"Smoke.+\"]\n";
        fs::write(proj.join("lakefile.toml"), valid_lakefile)?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic theorem a_thm : 1 + 1 = 2 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic theorem b_thm : 1 + 1 = 2 := a_thm\n",
        )?;

        let git_bin = std::env::var("TURBO_LEAN_GIT").unwrap_or_else(|_| "git".to_string());
        let run_git = |args: &[&str]| -> Result<()> {
            let st = Command::new(&git_bin)
                .current_dir(&proj)
                .args(args)
                .env("GIT_AUTHOR_NAME", "Test")
                .env("GIT_AUTHOR_EMAIL", "test@example.com")
                .env("GIT_COMMITTER_NAME", "Test")
                .env("GIT_COMMITTER_EMAIL", "test@example.com")
                .status()?;
            anyhow::ensure!(st.success(), "git {:?} failed", args);
            Ok(())
        };
        run_git(&["init", "-q"])?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-qm", "init"])?;

        // 0. Sanity: valid project succeeds and reports `Smoke.B` as dependent;
        //    newly added untracked file at valid `HEAD` and valid explicit `--rev HEAD` succeeds as unbaselined;
        //    non-Lake standalone file succeeds.
        let ok_rep = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(ok_rep.direct_dependents, vec!["Smoke.B".to_string()]);

        let new_file = proj.join("Smoke/NewMod.lean");
        fs::write(&new_file, "module\npublic def newVal : Nat := 42\n")?;
        let new_rep_default = compute_impact_report(new_file.clone(), Some(proj.clone()), None)?;
        assert_eq!(new_rep_default.edit_class, "unbaselined_module");
        assert_eq!(new_rep_default.module_name.as_deref(), Some("Smoke.NewMod"));
        let new_rep_explicit = compute_impact_report(
            new_file.clone(),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(new_rep_explicit.edit_class, "unbaselined_module");
        fs::remove_file(&new_file)?;

        let solo_file = solo_dir.join("Solo.lean");
        fs::write(&solo_file, "module\npublic def soloVal : Nat := 7\n")?;
        let solo_rep = compute_impact_report(solo_file.clone(), None, None)?;
        assert_eq!(solo_rep.edit_class, "unbaselined_module");
        assert!(solo_rep.module_name.is_none());

        // 1. Corrupt `lake-manifest.json` must fail closed (`Err`), never silently return empty dependents.
        fs::write(proj.join("lake-manifest.json"), "{ invalid json ")?;
        let err_manifest = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("corrupt lake-manifest.json must fail closed");
        assert!(
            format!("{err_manifest:#}").contains("lake-manifest.json"),
            "unexpected manifest error: {err_manifest:#}"
        );
        fs::remove_file(proj.join("lake-manifest.json"))?;

        // 2. Corrupt `lakefile.toml` must fail closed (`Err`).
        fs::write(proj.join("lakefile.toml"), "name = [unterminated\n")?;
        let err_lakefile = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("corrupt lakefile.toml must fail closed");
        assert!(
            format!("{err_lakefile:#}").contains("lakefile.toml"),
            "unexpected lakefile error: {err_lakefile:#}"
        );
        fs::write(proj.join("lakefile.toml"), valid_lakefile)?;

        // 3. Missing toolchain with `TURBO_LEAN_STRICT_TOOLCHAIN=1` must fail closed (`Err`).
        struct StrictToolchainGuard(Option<std::ffi::OsString>);
        impl Drop for StrictToolchainGuard {
            fn drop(&mut self) {
                match &self.0 {
                    Some(v) => std::env::set_var("TURBO_LEAN_STRICT_TOOLCHAIN", v),
                    None => std::env::remove_var("TURBO_LEAN_STRICT_TOOLCHAIN"),
                }
            }
        }
        let _strict_tc_guard =
            StrictToolchainGuard(std::env::var_os("TURBO_LEAN_STRICT_TOOLCHAIN"));
        std::env::set_var("TURBO_LEAN_STRICT_TOOLCHAIN", "1");
        fs::write(
            proj.join("lean-toolchain"),
            "leanprover/lean4:v4.99.0-nonexistent-impact-test\n",
        )?;
        let err_tc = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("strict missing toolchain must fail closed");
        assert!(
            format!("{err_tc:#}").contains("fail-closed toolchain gate"),
            "unexpected strict toolchain error: {err_tc:#}"
        );
        drop(_strict_tc_guard);
        fs::write(proj.join("lean-toolchain"), tc)?;

        // 4. DAG construction errors (missing imported module & import cycle) must fail closed (`Err`).
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\nimport Smoke.DoesNotExistAnywhere\npublic theorem b_thm : 1 + 1 = 2 := a_thm\n",
        )?;
        let err_missing_imp = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("missing DAG import must fail closed");
        assert!(
            format!("{err_missing_imp:#}").contains("DoesNotExistAnywhere"),
            "unexpected missing import error: {err_missing_imp:#}"
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\nimport Smoke.B\npublic theorem a_thm : 1 + 1 = 2 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\nimport Smoke.A\npublic theorem b_thm : 1 + 1 = 2 := rfl\n",
        )?;
        let err_cycle = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("DAG import cycle must fail closed");
        assert!(
            format!("{err_cycle:#}").contains("cycle"),
            "unexpected cycle error: {err_cycle:#}"
        );
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic theorem a_thm : 1 + 1 = 2 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic theorem b_thm : 1 + 1 = 2 := a_thm\n",
        )?;

        // 5. Invalid standalone module header in project must fail closed (`Err`).
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"smoke\"\n[[lean_lib]]\nname = \"Smoke\"\nroots = [\"Smoke.A\", \"Smoke.B\"]\n",
        )?;
        let bad_standalone = proj.join("StandaloneBad.lean");
        fs::write(&bad_standalone, "public import Smoke.A\n")?;
        let err_standalone = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("invalid standalone header must fail closed");
        assert!(
            format!("{err_standalone:#}").contains("StandaloneBad.lean"),
            "unexpected standalone error: {err_standalone:#}"
        );
        fs::remove_file(&bad_standalone)?;
        fs::write(proj.join("lakefile.toml"), valid_lakefile)?;

        // 6. Invalid explicit `--rev` (nonexistent ref, flag-like ref, or outside a git repo) must fail closed (`Err`).
        compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("refs/heads/definitely-does-not-exist-impact".to_string()),
        )
        .expect_err("nonexistent explicit --rev must fail closed");
        compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("--invalid-flag-rev".to_string()),
        )
        .expect_err("flag-like explicit --rev must fail closed");
        compute_impact_report(solo_file, None, Some("HEAD".to_string()))
            .expect_err("explicit --rev outside git repo must fail closed");
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_worktree_auto_link_disabled_invalidates_negative_memo_when_toml_created() -> Result<()>
    {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_wt_neg_memo_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos()
        ));
        let proj = tmp_dir.join("sub/proj");
        fs::create_dir_all(&proj)?;
        assert!(
            !worktree_auto_link_disabled(&proj),
            "default without turbo-lean.toml must allow worktree auto-link"
        );
        fs::write(
            tmp_dir.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        assert!(
            worktree_auto_link_disabled(&proj),
            "creating ancestor turbo-lean.toml within same memo window must invalidate negative lookup"
        );
        fs::write(
            tmp_dir.join("turbo-lean.toml"),
            "[worktree]\nauto_link = true\n",
        )?;
        assert!(
            !worktree_auto_link_disabled(&proj),
            "updating ancestor turbo-lean.toml to auto_link = true must re-enable auto-link"
        );
        fs::write(
            tmp_dir.join("sub/turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        assert!(
            worktree_auto_link_disabled(&proj),
            "creating closer intermediate sub/turbo-lean.toml must override outer turbo-lean.toml within same memo window"
        );
        let _ = fs::remove_file(tmp_dir.join("sub/turbo-lean.toml"));
        assert!(
            !worktree_auto_link_disabled(&proj),
            "removing closer sub/turbo-lean.toml must fall back to outer turbo-lean.toml immediately"
        );
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }
}
