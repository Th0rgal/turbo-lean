use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

use crate::db::TurboStore;
use crate::splitter::{self, split_lean_source};

use super::*;

#[allow(clippy::type_complexity)]
pub(super) static SINGLE_OLEAN_DIGEST_MEMO: std::sync::OnceLock<
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
pub(super) struct InterfaceClosureMemoEntry {
    pub(super) window: u64,
    pub(super) self_stats: std::sync::Arc<Vec<(PathBuf, Option<crate::zygote::OleanFileStatSig>)>>,
    pub(super) sample_check: Option<(
        PathBuf,
        [PathBuf; 5],
        [Option<crate::zygote::OleanFileStatSig>; 6],
        [u8; 32],
    )>,
    pub(super) pkg_dir_presence: std::sync::Arc<Vec<(PathBuf, bool)>>,
    pub(super) self_entries: std::sync::Arc<Vec<String>>,
    pub(super) children: std::sync::Arc<Vec<String>>,
}

#[allow(clippy::type_complexity)]
pub(super) static MODULE_INTERFACE_CLOSURE_MEMO: std::sync::OnceLock<
    std::sync::Mutex<HashMap<(PathBuf, String, String), InterfaceClosureMemoEntry>>,
> = std::sync::OnceLock::new();

#[derive(serde::Serialize, serde::Deserialize)]
pub(super) struct ShmSingleOleanDigestEntry {
    pub(super) stats: [Option<crate::zygote::OleanFileStatSig>; 6],
    pub(super) sample_key: [u8; 32],
    pub(super) digest: String,
    pub(super) deps: Vec<String>,
    #[serde(default)]
    pub(super) epoch: String,
}

pub(super) fn shm_single_olean_cache_file_name(olean_path: &Path) -> String {
    let key = blake3::hash(olean_path.to_string_lossy().as_bytes())
        .to_hex()
        .to_string();
    format!("oi_{}.json", &key[..28])
}

pub(super) fn compute_olean_bundle_sample_key(
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
                    if entry.epoch == crate::TURBO_LEAN_BUILD_EPOCH
                        && entry.stats == cur_stats
                        && entry.sample_key == sample_key
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
                    epoch: crate::TURBO_LEAN_BUILD_EPOCH.to_string(),
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
pub(super) static PROJECT_SOURCE_BLAKE3_MEMO: std::sync::OnceLock<
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

pub(super) fn read_header_imports_from_file(path: &Path) -> Option<Vec<String>> {
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

pub(super) fn resolve_olean_search_dirs_and_tc(
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
    pub(super) stat_memo: HashMap<PathBuf, Option<crate::zygote::OleanFileStatSig>>,
    pub(super) valid_closures: HashSet<(PathBuf, String, String)>,
    pub(super) project_env_memo:
        HashMap<(PathBuf, Option<String>), (Vec<PathBuf>, String, Option<(PathBuf, String)>)>,
    pub(super) project_lake_tag_memo: HashMap<PathBuf, Option<String>>,
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

pub(super) fn closure_self_stats_valid(
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
pub(super) fn compute_imported_olean_interface_hashes_with_precomputed_env(
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
    h.update(b"single-stat-split:v16\n");
    h.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    h.update(b"\n");
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
    h.update(b"project-stat-splits:v14\n");
    h.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    h.update(b"\n");
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
        key_h.update(b"project-stat-summary-v6\n");
        key_h.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
        key_h.update(b"\n");
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
    hasher.update(b"turbo-lean-build-v8\n");
    hasher.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    hasher.update(b"\n");

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
        ("ffi", "TURBO_LEAN_ALLOWED_FFI"),
    ] {
        if let Ok(val) = std::env::var(env_key) {
            let trimmed = val.trim();
            if !trimmed.is_empty() {
                hasher.update(format!(":{tag}:{trimmed}\n").as_bytes());
            }
        }
    }
    let active_excludes = crate::splitter::active_exclude_patterns();
    if !active_excludes.is_empty() {
        hasher.update(format!(":exclude:{}\n", active_excludes.join(",")).as_bytes());
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
        ch.update(b"project-content-splits:v13\n");
        ch.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
        ch.update(b"\n");
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

/// Recursively discover `.lean` source files inside `root` (or optional `scope` subdirectory),
/// excluding all hidden directories (`.*` such as `.benchmark-tools`, `.lake`, `.git`, `.elan`),
/// `target`, and `node_modules`.
pub(crate) fn collect_project_lean_files(
    root: &Path,
    include_lakefile: bool,
    scope: Option<&Path>,
) -> Vec<PathBuf> {
    let canon_root = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());
    let apply_excludes = !crate::splitter::active_exclude_patterns().is_empty()
        && !canon_root
            .components()
            .any(|c| c.as_os_str() == "packages" || c.as_os_str() == ".lake")
        && match std::env::var(crate::splitter::EXCLUDE_ROOT_ENV) {
            Ok(er) if !er.trim().is_empty() => {
                let canon_er = Path::new(er.trim())
                    .canonicalize()
                    .unwrap_or_else(|_| PathBuf::from(er.trim()));
                canon_root == canon_er || (scope.is_none() && canon_root.starts_with(&canon_er))
            }
            _ => true,
        };
    let exclude_base = match std::env::var(crate::splitter::EXCLUDE_ROOT_ENV) {
        Ok(er) if !er.trim().is_empty() => {
            let canon_er = Path::new(er.trim())
                .canonicalize()
                .unwrap_or_else(|_| PathBuf::from(er.trim()));
            if canon_root.starts_with(&canon_er) {
                canon_er
            } else {
                canon_root.clone()
            }
        }
        _ => canon_root.clone(),
    };
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
                if apply_excludes && fname != "lakefile.lean" {
                    let canon_p = p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
                    let rel = canon_p
                        .strip_prefix(&exclude_base)
                        .or_else(|_| p.strip_prefix(root))
                        .ok()
                        .map(|r| r.to_string_lossy().replace('\\', "/"));
                    if rel
                        .as_deref()
                        .is_some_and(crate::splitter::rel_path_excluded)
                    {
                        continue;
                    }
                }
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

/// The files of `files` whose edit against git revision `rev` is not local, i.e. changes more than
/// theorem proof bodies (proof irrelevance makes those invisible to other declarations). Files
/// new since `rev` are not local. Outside a git repository nothing is reported.
pub(crate) fn nonlocal_edits(files: &[PathBuf], rev: &str) -> Vec<String> {
    let has_git_ancestor_or_env = |dir: &Path| {
        if std::env::var_os("GIT_DIR").is_some() || std::env::var_os("GIT_WORK_TREE").is_some() {
            return true;
        }
        let canon = fs::canonicalize(dir).unwrap_or_else(|_| dir.to_path_buf());
        canon
            .ancestors()
            .any(|a| fs::symlink_metadata(a.join(".git")).is_ok())
    };
    let is_nonlocal = |f: &PathBuf| {
        let Ok(cur) = fs::read_to_string(f) else {
            return false;
        };
        let name = f.file_name().unwrap_or_default().to_string_lossy();
        let parent = f.parent().unwrap_or(Path::new("."));
        if !has_git_ancestor_or_env(parent) {
            return false;
        }
        let Ok(mut git) = crate::trusted_tools::git(parent) else {
            return true; // A missing trusted Git inside a repository must invalidate reuse.
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
                        .args([
                            "rev-parse",
                            "--verify",
                            "-q",
                            "--end-of-options",
                            &format!("{}^0", rev),
                        ])
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

