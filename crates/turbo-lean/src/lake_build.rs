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

#[allow(clippy::type_complexity)]
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

pub(crate) fn compute_imported_olean_interface_hashes_with_tag(
    src: &str,
    project_dir: &Path,
    lean_path: Option<&str>,
    lake_inputs_tag: Option<String>,
) -> Vec<String> {
    let mut worklist = parse_header_imports(src);
    if worklist.is_empty() {
        return lake_inputs_tag.into_iter().collect();
    }

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

    if search_dirs.is_empty() && project_dir.as_os_str().is_empty() {
        return lake_inputs_tag.into_iter().collect();
    }

    let search_refs: Vec<&Path> = search_dirs.iter().map(PathBuf::as_path).collect();
    let tc_ref = resolved_tc_lib.as_deref();
    let tc_gh_ref = resolved_tc.as_ref().map(|(_, gh)| gh.as_str());
    let mut visited = std::collections::HashSet::new();
    let mut out = Vec::new();

    while let Some(mod_name) = worklist.pop() {
        if !visited.insert(mod_name.clone()) {
            continue;
        }
        let rel_slash = crate::module_builder::module_name_to_rel_slash(&mod_name);
        let sub_lean_opt = resolve_project_lean_source(project_dir, &rel_slash);
        let src_digest_opt = sub_lean_opt
            .as_deref()
            .and_then(compute_cached_source_blake3);
        let mut olean_digest_opt = None;
        let mut olean_sub_mods = Vec::new();
        if let Some(cand) = crate::zygote::resolve_closure_module(&search_refs, &mod_name, tc_ref) {
            if let Some((digest, sub_deps)) = compute_single_olean_digest_and_imports(&cand) {
                olean_digest_opt = Some(digest);
                olean_sub_mods = sub_deps;
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
                    && !(crate::zygote::is_resolved_toolchain_builtin(
                        &search_refs,
                        &mod_name,
                        tc_ref,
                    ) && match (tc_ref, tc_gh_ref) {
                        (Some(tc_lib), Some(gh)) => {
                            crate::module_builder::is_builtin_toolchain_module(
                                tc_lib,
                                Some(gh),
                                &mod_name,
                            )
                        }
                        _ => true,
                    }) =>
            {
                out.push(format!("{}:missing", mod_name));
            }
            _ => {}
        }
        for sub_mod in olean_sub_mods {
            if !visited.contains(&sub_mod)
                && crate::zygote::resolve_closure_module(&search_refs, &sub_mod, tc_ref).is_some()
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

    out.extend(lake_inputs_tag);
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
    let dir = store.fast_staging_dir().join("file_splits_v8");
    let _ = fs::create_dir_all(&dir);
    dir
}

pub(crate) fn compute_single_stat_hash(pk: &str, ms: i64, mn: i64, sz: i64) -> String {
    let mut h = blake3::Hasher::new();
    // v4 rebuilds legacy shards without qualified declaration identities.
    // v9 invalidates declaration scopes computed before lossless dotted-component canonicalization.
    // v10 includes checking-weakening hygiene fields in cached file splits.
    // v11 invalidates splits computed before 3-byte `/--`/`/-!` docstring & raw/interp lexing fixes.
    h.update(b"single-stat-split:v11\n");
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
    h.update(b"project-stat-splits:v9\n");
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

    let summary_path = if paths.len() <= 128 && valid_stats.len() == paths.len() {
        let mut key_h = blake3::Hasher::new();
        key_h.update(b"project-stat-summary-v3\n");
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
        let p = store
            .fast_staging_dir()
            .join(format!("project_stat_summary_v8_{}.json", &stat_hash[..24]));
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

    let shm_stat_path = if paths.len() <= 128 && valid_stats.len() == paths.len() {
        let stat_hash = compute_stat_slice_hash(&valid_stats);
        let p = store
            .fast_staging_dir()
            .join(format!("project_stat_splits_v9_{}.json", &stat_hash[..24]));
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
        ch.update(b"project-content-splits:v8\n");
        for (_, fk) in &file_keys {
            ch.update(fk.as_bytes());
            ch.update(b"\n");
        }
        let p = store.fast_staging_dir().join(format!(
            "project_splits_v8_{}.json",
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
            .join(format!("project_stat_splits_v9_{}.json", &stat_hash[..24]));
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
    imports: &[String],
) -> bool {
    let Some(cfg) = manifest.cfg.as_ref() else {
        return false;
    };
    crate::module_builder::verified_entry_imports_current(entry, imports, |imp, pin| {
        crate::module_builder::import_pin_current(cfg, &manifest.dep_import_memo, imp, pin)
    })
}

fn entry_import_pins_fresh_for_build(
    manifest: &crate::module_builder::VerifiedDepManifest,
    entry: &crate::module_builder::VerifiedDepModuleEntry,
    imports: &[String],
    cache: &mut crate::module_builder::LakeClosureCache,
) -> bool {
    let Some(cfg) = manifest.cfg.as_ref() else {
        return false;
    };
    crate::module_builder::verified_entry_imports_current(entry, imports, |imp, pin| {
        crate::module_builder::import_pin_fresh_for_build(cfg, cache, imp, pin)
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
        entry_import_pins_current(manifest, entry, &hdr.imports),
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
        if opt_out {
            let src_path = canon_dir.join(rel_path);
            let src_mtime = fs::metadata(&src_path).and_then(|m| m.modified()).ok();
            let olean_mtime = olean_meta.modified().ok();
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
    let lean_path = resolve_remote_lean_path(canon_dir, None);
    let mut dirs: Vec<PathBuf> = std::env::split_paths(&lean_path).collect();
    if !cfg.toolchain_lib_lean.as_os_str().is_empty() && !dirs.contains(&cfg.toolchain_lib_lean) {
        dirs.push(cfg.toolchain_lib_lean.clone());
    }
    let mut worklist = Vec::new();
    for rel_path in file_hashes.keys() {
        if rel_path == "lakefile.lean" || rel_path.ends_with("/lakefile.lean") {
            continue;
        }
        let olean_path = resolve_project_olean_for_rel_path(canon_dir, rel_path);
        if olean_path.is_file() {
            if !crate::module_builder::is_olean_replayed_in_store(
                store,
                &cfg,
                &lean_path,
                &olean_path,
            ) {
                return false;
            }
            if let Ok(bytes) = fs::read(&olean_path) {
                if let Some((imps, _)) = crate::module_builder::parse_olean_binary_imports(&bytes) {
                    worklist.extend(imps.into_iter().map(|i| i.module));
                }
            }
        }
    }
    let mut seen = HashSet::new();
    while let Some(m) = worklist.pop() {
        if !seen.insert(m.clone()) {
            continue;
        }
        let rel = format!(
            "{}.olean",
            crate::module_builder::module_name_to_rel_slash(&m)
        );
        let Some(path) = dirs.iter().map(|d| d.join(&rel)).find(|p| p.is_file()) else {
            return false;
        };
        if crate::module_builder::is_verified_toolchain_olean_file(
            &cfg.toolchain_lib_lean,
            Some(&cfg.lean_githash),
            &path,
        ) {
            continue;
        }
        if !crate::module_builder::is_olean_replayed_in_store(store, &cfg, &lean_path, &path) {
            return false;
        }
        let Ok(bytes) = fs::read(&path) else {
            return false;
        };
        if let Some((imps, _)) = crate::module_builder::parse_olean_binary_imports(&bytes) {
            worklist.extend(imps.into_iter().map(|i| i.module));
        }
    }
    true
}

pub(crate) fn ensure_project_and_imported_oleans_replayed_in_store(
    store: &TurboStore,
    canon_dir: &Path,
    file_hashes: &BTreeMap<String, String>,
) -> Result<()> {
    let cfg = crate::module_builder::resolve_project_config(canon_dir).context(
        "Cannot kernel-replay project `.olean`s without a resolvable project configuration: fail-closed",
    )?;
    let lean_path = resolve_remote_lean_path(canon_dir, None);
    let mut dirs: Vec<PathBuf> = std::env::split_paths(&lean_path).collect();
    let mut root_mods: Vec<(String, PathBuf)> = Vec::new();
    let mut worklist = Vec::new();
    for rel_path in file_hashes.keys() {
        if rel_path == "lakefile.lean" || rel_path.ends_with("/lakefile.lean") {
            continue;
        }
        let olean_path = resolve_project_olean_for_rel_path(canon_dir, rel_path);
        if olean_path.is_file() {
            let lib_lean_dir = canon_dir.join(".lake/build/lib/lean");
            let rel_no_ext = olean_path
                .strip_prefix(&lib_lean_dir)
                .unwrap_or(&olean_path)
                .with_extension("");
            let parts: Vec<String> = rel_no_ext
                .components()
                .filter_map(|c| c.as_os_str().to_str().map(|s| s.to_string()))
                .collect();
            if !parts.is_empty() {
                let mod_name = crate::module_builder::format_lean_module_name_from_parts(
                    parts.iter().map(String::as_str),
                );
                let bytes = fs::read(&olean_path)?;
                if let Some((imps, _)) = crate::module_builder::parse_olean_binary_imports(&bytes) {
                    worklist.extend(imps.into_iter().map(|i| i.module));
                }
                root_mods.push((mod_name, olean_path));
            }
        }
    }
    let mut seen: HashSet<String> = root_mods.iter().map(|(m, _)| m.clone()).collect();
    let mut dep_mods: Vec<(String, PathBuf)> = Vec::new();
    if !cfg.toolchain_lib_lean.as_os_str().is_empty() && !dirs.contains(&cfg.toolchain_lib_lean) {
        dirs.push(cfg.toolchain_lib_lean.clone());
    }
    while let Some(m) = worklist.pop() {
        if !seen.insert(m.clone()) {
            continue;
        }
        let rel = format!(
            "{}.olean",
            crate::module_builder::module_name_to_rel_slash(&m)
        );
        let Some(path) = dirs.iter().map(|d| d.join(&rel)).find(|p| p.is_file()) else {
            continue;
        };
        if crate::module_builder::is_verified_toolchain_olean_file(
            &cfg.toolchain_lib_lean,
            Some(&cfg.lean_githash),
            &path,
        ) {
            continue;
        }
        let bytes = fs::read(&path)?;
        let (imps, _) =
            crate::module_builder::parse_olean_binary_imports(&bytes).ok_or_else(|| {
                anyhow::anyhow!(
                    "Failed to parse binary `.olean` header of imported `{m}` (`{}`): fail-closed",
                    path.display()
                )
            })?;
        worklist.extend(imps.into_iter().map(|i| i.module));
        dep_mods.push((m, path));
    }
    let allowed_axioms = crate::splitter::allowed_axioms();
    let replay_lp = format!("{}:{}", lean_path, cfg.toolchain_lib_lean.display());
    let mut pending_deps = Vec::new();
    for (m, path) in &dep_mods {
        crate::module_builder::verify_imported_package_module_source_hygiene(
            &cfg,
            m,
            path,
            &allowed_axioms,
        )?;
        if !crate::module_builder::is_olean_replayed_in_store(store, &cfg, &replay_lp, path) {
            pending_deps.push(m.clone());
        }
    }
    if !pending_deps.is_empty() {
        crate::zygote::kernel_replay_modules_with_zygote(store, &cfg, &pending_deps, &replay_lp)
            .context("Imported `.olean` failed independent kernel replay")?;
    }
    let mut pending_roots = Vec::new();
    for (m, path) in &root_mods {
        if !crate::module_builder::is_olean_replayed_in_store(store, &cfg, &replay_lp, path) {
            pending_roots.push(m.clone());
        }
    }
    if !pending_roots.is_empty() {
        crate::zygote::audit_compiled_modules_with_zygote(
            store,
            &cfg,
            &pending_roots,
            &replay_lp,
            &[],
            false,
        )
        .context("Project `.olean` failed in-kernel soundness & replay audit")?;
    }
    Ok(())
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
    let cfg = crate::module_builder::resolve_project_config(canon_project_dir).ok()?;
    let lean_path = resolve_remote_lean_path(canon_project_dir, None);
    if !crate::module_builder::is_olean_replayed_in_store(store, &cfg, &lean_path, &olean_path) {
        return None;
    }
    let mut dirs: Vec<PathBuf> = std::env::split_paths(&lean_path).collect();
    if !cfg.toolchain_lib_lean.as_os_str().is_empty() && !dirs.contains(&cfg.toolchain_lib_lean) {
        dirs.push(cfg.toolchain_lib_lean.clone());
    }
    let bytes = fs::read(&olean_path).ok()?;
    let (imps, _) = crate::module_builder::parse_olean_binary_imports(&bytes)?;
    let mut worklist: Vec<String> = imps.into_iter().map(|i| i.module).collect();
    let mut seen = HashSet::new();
    while let Some(m) = worklist.pop() {
        if !seen.insert(m.clone()) {
            continue;
        }
        let rel = format!(
            "{}.olean",
            crate::module_builder::module_name_to_rel_slash(&m)
        );
        let path = dirs.iter().map(|d| d.join(&rel)).find(|p| p.is_file())?;
        if crate::module_builder::is_verified_toolchain_olean_file(
            &cfg.toolchain_lib_lean,
            Some(&cfg.lean_githash),
            &path,
        ) {
            continue;
        }
        if !crate::module_builder::is_olean_replayed_in_store(store, &cfg, &lean_path, &path) {
            return None;
        }
        let sub_bytes = fs::read(&path).ok()?;
        let (sub_imps, _) = crate::module_builder::parse_olean_binary_imports(&sub_bytes)?;
        worklist.extend(sub_imps.into_iter().map(|i| i.module));
    }
    Some(mod_name)
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
        let _ = fs::remove_file(p);
    }
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
    let mut non_root_imports: Vec<String> = Vec::new();
    let mut standalone_tc_lib_lean: Option<PathBuf> = None;
    while let Some(mod_name) = worklist.pop() {
        if !visited.insert(mod_name.clone()) {
            continue;
        }
        let imp_slash = crate::module_builder::module_name_to_rel_slash(&mod_name);
        if let Some(info) = resolve_root_import(&mod_name, &imp_slash) {
            let sub_imps = read_header_imports_from_file(&info.dep_src).ok_or_else(|| {
                anyhow::anyhow!(
                    "Unparseable or unreadable import header in `{}`: fail-closed import freshness gate",
                    info.dep_src.display()
                )
            })?;
            for sub_imp in &sub_imps {
                if !visited.contains(sub_imp) {
                    worklist.push(sub_imp.clone());
                }
            }
            adj.insert(mod_name.clone(), sub_imps);
            mod_index.insert(mod_name, ordered_imports.len());
            ordered_imports.push(info);
        } else if let Some(cfg) = root_cfg.as_ref() {
            if !matches!(
                crate::module_builder::resolve_import_site(cfg, &mod_name),
                crate::module_builder::ImportSite::Toolchain
            ) {
                non_root_imports.push(mod_name);
            }
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
                                }) && entry_import_pins_fresh_for_build(
                                    m,
                                    e,
                                    adj.get(&info.mod_name).map_or(&[][..], Vec::as_slice),
                                    &mut closure_cache,
                                )))
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
        if pkg_inputs_stale
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
        }
    }

    stale_mods.extend(stale_dep_mods.iter().cloned());
    let opt_out_for_prop = worktree_auto_link_disabled(canon_dir);
    // Propagate staleness downstream across the imported workspace subgraph.
    let mut changed = !stale_mods.is_empty();
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
                && (manifest_opt
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
            lake_build_modules(
                canon_dir,
                &lake_refresh_targets(canon_dir, &lake_targets),
                rev,
            )?;
        }
        for mod_name in &non_target_stale {
            let imp_slash = crate::module_builder::module_name_to_rel_slash(mod_name);
            remove_module_build_artifacts(canon_dir, &imp_slash);
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

pub(crate) fn ensure_project_imports_fresh_for_check(
    canon_dir: &Path,
    target_files: &[PathBuf],
) -> Result<usize> {
    ensure_project_imports_fresh(canon_dir, target_files, None, false)
}

/// Verification rebuilds always use stock Lake. Project build_command wrappers may
/// otherwise substitute the compiler whose artifacts support the verdict.
pub(crate) fn lake_build_modules(
    canon_dir: &Path,
    modules: &[String],
    _rev: Option<&str>,
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
    let out = Command::new(&tools.lake)
        .env("PATH", tools.path())
        .env("LEAN", &tools.lean)
        .env("LAKE", &tools.lake)
        .env("LEANC", &tools.leanc)
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
    imports: Vec<String>,
}

struct ProjectDependentClosure {
    dag_seeds: Vec<String>,
    lake_seeds: Vec<String>,
    dag_modules: Option<Vec<String>>,
    dag_files: Option<Vec<PathBuf>>,
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
            Err(e) if is_untrusted || is_edited => {
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
            if is_untrusted || is_edited {
                anyhow::bail!(
                    "Invalid module header in standalone Lean file `{}`: {}",
                    source.display(),
                    err
                );
            }
            continue;
        }
        if let Some(prev) = out.insert(
            mod_name.clone(),
            StandaloneModuleSpec {
                module_name: mod_name.clone(),
                src_path: canon_src,
                src_root: root,
                imports: hdr.imports,
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

    let dag_opt = if is_untrusted {
        Some(crate::module_builder::build_module_dag_with_trust(
            &cfg, &dag_seeds, true,
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
    )?;

    if let Some(dag) = dag_opt {
        let mut dag_closure: std::collections::BTreeSet<String> = dag
            .nodes
            .iter()
            .filter(|(_, n)| {
                edited.contains(&n.src_path.canonicalize().unwrap_or(n.src_path.clone()))
            })
            .map(|(m, _)| m.clone())
            .collect();
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
            dag_seeds,
            lake_seeds,
            dag_modules: Some(dag_closure.into_iter().collect()),
            dag_files: Some(files),
            standalone_modules: standalone_specs,
        })
    } else {
        let standalone_closure: std::collections::BTreeSet<String> =
            standalone_all.keys().cloned().collect();
        let standalone_specs =
            topologically_order_standalone_modules(&standalone_all, &standalone_closure)?;
        Ok(ProjectDependentClosure {
            dag_seeds,
            lake_seeds,
            dag_modules: None,
            dag_files: None,
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

fn check_and_audit_standalone_modules(
    store_opt: Option<&TurboStore>,
    canon_dir: &Path,
    standalone_modules: &[StandaloneModuleSpec],
    is_untrusted: bool,
    verified_target_modules: Option<&HashSet<String>>,
    rev: Option<&str>,
    retain_oleans: bool,
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
        ensure_modules_and_imports_replayed(store, canon_dir, &standalone_files, &target_imports)?;
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

    // Populate `olean_out_dir` with hard links (falling back to copies) of target-owned `.olean`
    // files from root/dependency `.lake/build/lib/lean` directories so `olean_out_dir` can sit
    // FIRST on `LEAN_PATH`. In Lean 4's `SearchPath.findWithExt`, a matching top-level subdirectory
    // (e.g. `TurboLean/` in `.lake/build/lib/lean`) pins module resolution (`TurboLean.olean` AND
    // `TurboLean.Spec`) to the first directory containing either `TurboLean/` or `TurboLean.olean`.
    // Merging target-owned `.olean`s into `olean_out_dir` lets both `TurboLean.olean` and
    // `TurboLean/Spec.olean` resolve cleanly without touching `.lake` (preserving
    // `--no-auto-worktree-link` snapshots) while never copying unverified non-target `.olean`s.
    let merge_pkg_oleans = |pkg: &crate::module_builder::PackageConfig,
                            is_root: bool,
                            dst_dir: &Path|
     -> Result<()> {
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
                    if fs::hard_link(&p, &dst_p).is_err() {
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
            cmd.arg("-Dwarn.sorry=true")
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
            if stdout_str.contains("declaration uses ") || stderr_str.contains("declaration uses ")
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
        crate::zygote::audit_compiled_modules_with_zygote(
            store,
            &cfg,
            &mod_names,
            &combined_lp,
            std::slice::from_ref(&olean_out_dir),
            false,
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
        let (n, rechecked_files, rechecked_mods, _overlay) =
            lake_recheck_dependents_with_store(Some(store), &dir, &edits, None, false)?;
        ensure_modules_and_imports_replayed(store, &dir, &rechecked_files, &rechecked_mods)?;
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
                ensure_modules_and_imports_replayed(store, &dir, &closure_files, &closure_mods)?;
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
    Ok(())
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
    if !has_lake_config(canon_dir) {
        anyhow::bail!(
            "non-local edit in {} needs its dependents re-checked, but {} has no Lake config: refusing to pass",
            edits.join(", "),
            canon_dir.display()
        );
    }
    let closure = compute_project_dependent_closure(canon_dir, edits, false)?;
    let (dag_count, files, mods) = match (closure.dag_modules, closure.dag_files) {
        // As in `ensure_project_imports_fresh_for_check`: a module whose input-bearing library is
        // not the one Lake attributes it to has to be asked for by library name, or Lake compares
        // an input-blind trace and reports it up to date.
        (Some(mods), Some(files)) if !mods.is_empty() => {
            lake_build_modules(canon_dir, &lake_refresh_targets(canon_dir, &mods), rev)?;
            (mods.len(), files, mods)
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
    let (_standalone_files, _overlay) = check_and_audit_standalone_modules(
        store_opt,
        canon_dir,
        &closure.standalone_modules,
        false,
        None,
        rev,
        false,
    )?;
    let _ = retain_standalone_oleans;
    let standalone_count = closure.standalone_modules.len();
    Ok((dag_count + standalone_count, files, mods, None))
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
    let standalone_names: HashSet<&str> = closure
        .standalone_modules
        .iter()
        .map(|s| s.module_name.as_str())
        .collect();
    let cfg = crate::module_builder::resolve_project_config_with_trust(canon_dir, true)?;
    let mut standalone_target_imports: Vec<String> = Vec::new();
    for spec in &closure.standalone_modules {
        for imp in &spec.imports {
            if standalone_names.contains(imp.as_str()) {
                continue;
            }
            if crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, imp).is_some()
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
    let mut verified_targets = HashSet::new();
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
        let built_dag = crate::module_builder::build_module_dag_with_trust(&cfg, &targets, true)?;
        verified_targets.extend(built_dag.nodes.into_keys());
    }
    let (_standalone_files, _overlay) = check_and_audit_standalone_modules(
        Some(store),
        canon_dir,
        &closure.standalone_modules,
        true,
        Some(&verified_targets),
        None,
        false,
    )?;
    Ok((
        dag_count + closure.standalone_modules.len(),
        built_all,
        None,
    ))
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

fn classify_lake_build_artifact(path: &Path, build_dir: &Path) -> Option<&'static str> {
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
        "exe" => Some("exe"),
        "" if path
            .strip_prefix(build_dir)
            .ok()
            .and_then(|r| r.components().next())
            .is_some_and(|c| c.as_os_str() == "bin") =>
        {
            Some("exe")
        }
        _ => None,
    }
}

/// Stage compiled `.olean`, `.ilean`, `.c`, native `.c.o*`/`.so`/`.dylib`/`.dll`/`.rsp`, and Lake sidecars
/// from workspace `.lake/build` directories into the immutable CAS blobs directory without opening a SQLite
/// transaction, returning `(outputs, reg_blobs)`.
#[allow(clippy::type_complexity)]
pub(crate) fn stage_lake_build_outputs(
    store: &TurboStore,
    project_dir: &Path,
) -> Result<(Vec<BlobEntry>, Vec<(String, String, i64, i64)>)> {
    let preserve_lake = worktree_auto_link_disabled(project_dir);
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

    let mut candidates: Vec<(PathBuf, &'static str, String, i64, i64, u64, u32, i64)> = Vec::new();
    for build_dir in &build_dirs {
        for entry in WalkDir::new(build_dir).into_iter().flatten() {
            if !entry.file_type().is_file() {
                continue;
            }
            let path = entry.path();
            let Some(kind) = classify_lake_build_artifact(path, build_dir) else {
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

    if candidates.is_empty() {
        return Ok((Vec::new(), Vec::new()));
    }
    candidates.sort_by(|a, b| a.2.cmp(&b.2));
    candidates.dedup_by(|a, b| a.2 == b.2);

    let mut sh = blake3::Hasher::new();
    sh.update(b"lake-build-ingest:v2\n");
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

    for (entry, (path, _, _, _, _, _, mode, _cand_ino)) in entries.iter().zip(candidates.iter()) {
        // Never hardlink `.lake/build` artifacts into CAS or mark them read-only (`0o444`):
        // in-place `lake build` / `lean -o` writes must never mutate CAS blobs (`nlink == 1`, `0o644`).
        #[cfg(unix)]
        {
            let nlink = fs::metadata(path)?.nlink();
            if !preserve_lake && ((*mode & 0o200) == 0 || nlink > 1) {
                let bytes = fs::read(path)?;
                crate::db::write_bytes_durable(path, &bytes, &[])?;
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
    if !targets.is_empty() && has_lake_config(&canon_dir) {
        let cfg = crate::module_builder::resolve_project_config_with_trust(
            &canon_dir,
            trust_domain.starts_with("untrusted"),
        )
        .with_context(|| {
            format!(
                "Static Lake config validation failed for {}",
                canon_dir.display()
            )
        })?;
        let _ = crate::module_builder::workspace_lake_inputs_digest(&cfg)?;
        if !crate::module_builder::targets_include_exe_link_target(&cfg, &targets) {
            let build_report = crate::module_builder::build_project_modules_native(
                store,
                &canon_dir,
                &targets,
                &trust_domain,
                pin_level,
                trust_domain.starts_with("untrusted"),
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
    match outcome {
        Some(SingleflightOutcome::CacheHit { outputs, coalesced }) => {
            let linked = store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
            ensure_project_and_imported_oleans_replayed_in_store(store, &canon_dir, &file_hashes)?;
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
            let mut build_report = crate::module_builder::NativeBuildReport::default();
            if !targets.is_empty()
                || !are_all_project_oleans_up_to_date(&canon_dir, &file_hashes)
                || !are_all_project_oleans_replayed_in_store(store, &canon_dir, &file_hashes)
            {
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
            let (outputs, manifest_hash, linked) = if has_out_of_tree_dep_build_dir(&canon_dir) {
                (Vec::new(), String::new(), 0usize)
            } else {
                let _pub_guard = crate::db::acquire_cas_publication_guard(&store.root)?;
                let (outputs, reg_blobs) = stage_lake_build_outputs(store, &canon_dir)?;
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
        let _ = fs::remove_dir_all(&root);
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
                modules: std::collections::BTreeMap::from([(
                    "Smoke/A.lean".to_string(),
                    crate::module_builder::VerifiedDepModuleEntry {
                        src_blake3: blake3::hash(b"def a : Nat := 1\n").to_hex().to_string(),
                        olean_artifact_digest: "art".to_string(),
                        lake_inputs_digest: inputs_digest.to_string(),
                        kernel_audited: true,
                        import_olean_digests: Default::default(),
                        artifact_stat_fingerprint: String::new(),
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
}
