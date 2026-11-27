use anyhow::{Context, Result};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use crate::db::TurboStore;
use crate::splitter;

use super::*;

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

pub(super) fn hardlink_tree_recursive(src: &Path, dst: &Path) -> usize {
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

pub(super) fn strip_module_artifact_rel_slash(rel_path: &Path) -> Option<String> {
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

pub(super) fn is_worktree_module_identical_to_main(
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

pub(super) fn hardlink_worktree_build_tree_verified(
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
pub(super) static WORKTREE_AUTO_LINK_DISABLED_MEMO: std::sync::OnceLock<
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
    let computed: Option<bool> = match toml_path.as_deref() {
        None => Some(false),
        Some(p) => fs::read_to_string(p).ok().map(|t| {
            crate::accelerators::toml_value(&t, "worktree", "auto_link")
                .and_then(|v| crate::shm_cache::parse_relaxed_bool(&v))
                == Some(false)
        }),
    };
    let res = match computed {
        Some(v) => v,
        None => return true,
    };
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

    let shm_env_path = store.fast_staging_dir().join(format!(
        "lake_env_v2_{}_{}.json",
        crate::build_epoch_short(),
        project_key
    ));
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
    let shm_env_path = store.fast_staging_dir().join(format!(
        "lake_env_v2_{}_{}.json",
        crate::build_epoch_short(),
        env_key
    ));
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

pub(super) fn sanitize_toolchain_env(project: &Path, env: &mut HashMap<String, String>) -> Result<()> {
    crate::module_builder::ToolchainExecutables::resolve(project, &detect_toolchain(project))?
        .apply_env(env);
    Ok(())
}

pub(super) fn collect_project_lean_lib_dirs(project_dir: &Path) -> Vec<PathBuf> {
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
    compute_shard_key_with_args(toolchain, shard, &[], None)
}

pub(crate) fn compute_shard_key_with_args(
    toolchain: &str,
    shard: &splitter::TheoremShard,
    lean_args: &[String],
    kernel_audit_digest: Option<&str>,
) -> String {
    let mut key_hasher = blake3::Hasher::new();
    // v10: the non-standard kernel-audit digest is bound into the key (roadmap G1a), so a verdict
    // from one kernel engine is never served to a run that selected another; the bump retires
    // rows a con-leche-only run cached under the standard-kernel domain.
    // The verifier provenance versions are bound too, so pre-replay receipts never match
    // and any later scanner/replay bump retires every older receipt.
    key_hasher.update(b"theorem-shard-v10:");
    key_hasher.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    key_hasher.update(b":");
    key_hasher.update(&crate::zygote::ZYGOTE_SCANNER_VERSION.to_le_bytes());
    key_hasher.update(&crate::zygote::ZYGOTE_REPLAY_VERSION.to_le_bytes());
    key_hasher.update(toolchain.as_bytes());
    key_hasher.update(b":");
    key_hasher.update(shard.prefix_env_hash.as_bytes());
    key_hasher.update(b":");
    key_hasher.update(shard.stmt_hash.as_bytes());
    key_hasher.update(b":");
    key_hasher.update(shard.proof_hash.as_bytes());
    if let Some(d) = kernel_audit_digest {
        key_hasher.update(b":kernel_audit:");
        key_hasher.update(d.as_bytes());
    }
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
        ("ffi", "TURBO_LEAN_ALLOWED_FFI"),
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

pub(super) fn par_map_indexed<T: Send, F: Fn(usize) -> T + Sync>(
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

