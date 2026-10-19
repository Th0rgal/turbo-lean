//! Git tree-aware incremental PR verification (`git-head-tree:v5:`), prefix-pread splitting,
//! and BLAKE3 cryptographic verification receipts.

use crate::db::TurboStore;
use crate::splitter::{self, split_lean_source};
use crate::{compute_shard_key, load_and_split_files_cached};
use anyhow::{Context, Result};
use walkdir::WalkDir;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct PrClassification {
    pub total_files: usize,
    pub modified_files: Vec<String>,
    pub altered_interface_files: Vec<String>,
    pub interface_drift: bool,
    pub baseline_interface_hash: String,
    pub current_interface_hash: String,
    pub unchanged_theorems: Vec<String>,
    pub proof_edited_theorems: Vec<String>,
    pub statement_edited_theorems: Vec<String>,
    pub per_file_interfaces: std::collections::BTreeMap<String, String>,
}

pub(crate) fn resolve_git_toplevel(dir: &Path) -> Result<PathBuf> {
    let canon = dir.canonicalize().unwrap_or_else(|_| dir.to_path_buf());
    for anc in canon.ancestors() {
        if anc.join(".git").exists() {
            return Ok(anc.to_path_buf());
        }
    }
    let out = Command::new("git")
        .args(["-C", &dir.to_string_lossy(), "rev-parse", "--show-toplevel"])
        .output()
        .context("Failed to execute `git rev-parse --show-toplevel`")?;
    if !out.status.success() {
        anyhow::bail!(
            "Not a git repository ({}): {}",
            dir.display(),
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    let p = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
    Ok(p.canonicalize().unwrap_or(p))
}

pub(crate) fn resolve_git_head_sha(repo_root: &Path, base_ref: &str) -> Option<String> {
    if base_ref.len() == 40 && base_ref.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Some(base_ref.to_ascii_lowercase());
    }
    if base_ref.is_empty()
        || base_ref.contains(['~', '^', ':', '@', '*', '?', '['])
        || base_ref.contains("..")
    {
        return None;
    }
    let dot_git = repo_root.join(".git");
    let (git_dir, common_dir) = if dot_git.is_dir() {
        (dot_git.clone(), dot_git)
    } else if dot_git.is_file() {
        let content = fs::read_to_string(&dot_git).ok()?;
        let gitdir_str = content.trim().strip_prefix("gitdir:")?.trim();
        let gdir = if Path::new(gitdir_str).is_absolute() {
            PathBuf::from(gitdir_str)
        } else {
            repo_root.join(gitdir_str)
        };
        let cdir = if let Ok(cd_str) = fs::read_to_string(gdir.join("commondir")) {
            let cd_trimmed = cd_str.trim();
            if Path::new(cd_trimmed).is_absolute() {
                PathBuf::from(cd_trimmed)
            } else {
                gdir.join(cd_trimmed)
            }
        } else {
            gdir.clone()
        };
        (gdir, cdir)
    } else {
        return None;
    };

    let lookup_ref = |ref_rel: &str| -> Option<String> {
        for base in [&git_dir, &common_dir] {
            if let Ok(sha) = fs::read_to_string(base.join(ref_rel)) {
                let s = sha.trim();
                if s.len() == 40 && s.bytes().all(|b| b.is_ascii_hexdigit()) {
                    return Some(s.to_ascii_lowercase());
                }
            }
        }
        if let Ok(packed) = fs::read_to_string(common_dir.join("packed-refs")) {
            for line in packed.lines() {
                if line.starts_with('#') || line.starts_with('^') {
                    continue;
                }
                if let Some((sha, rname)) = line.split_once(' ') {
                    if rname.trim() == ref_rel
                        && sha.len() == 40
                        && sha.bytes().all(|b| b.is_ascii_hexdigit())
                    {
                        return Some(sha.to_ascii_lowercase());
                    }
                }
            }
        }
        None
    };

    if base_ref == "HEAD" {
        let head_content = fs::read_to_string(git_dir.join("HEAD")).ok()?;
        let head_trimmed = head_content.trim();
        if let Some(ref_path) = head_trimmed.strip_prefix("ref:") {
            lookup_ref(ref_path.trim())
        } else if head_trimmed.len() == 40 && head_trimmed.bytes().all(|b| b.is_ascii_hexdigit()) {
            Some(head_trimmed.to_ascii_lowercase())
        } else {
            None
        }
    } else if base_ref.starts_with("refs/") {
        lookup_ref(base_ref)
    } else {
        for prefix in ["refs/heads/", "refs/remotes/", "refs/tags/"] {
            if let Some(sha) = lookup_ref(&format!("{}{}", prefix, base_ref)) {
                return Some(sha);
            }
        }
        None
    }
}

pub(crate) fn fetch_git_blobs_batch(
    repo_root: &Path,
    base_ref: &str,
    repo_rels: &[String],
) -> Result<std::collections::HashMap<String, String>> {
    let mut out_map = std::collections::HashMap::with_capacity(repo_rels.len());
    if repo_rels.is_empty() {
        return Ok(out_map);
    }
    if repo_rels.len() == 1 {
        let repo_rel = &repo_rels[0];
        let show_out = Command::new("git")
            .args([
                "-C",
                &repo_root.to_string_lossy(),
                "show",
                &format!("{}:{}", base_ref, repo_rel),
            ])
            .output()
            .context("Failed to execute `git show`")?;
        if show_out.status.success() {
            out_map.insert(
                repo_rel.clone(),
                String::from_utf8_lossy(&show_out.stdout).to_string(),
            );
        }
        return Ok(out_map);
    }

    let mut child = Command::new("git")
        .args(["-C", &repo_root.to_string_lossy(), "cat-file", "--batch"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .context("Failed to spawn `git cat-file --batch`")?;

    if let Some(mut stdin) = child.stdin.take() {
        use std::io::Write;
        let mut req_buf = String::new();
        for r in repo_rels {
            req_buf.push_str(base_ref);
            req_buf.push(':');
            req_buf.push_str(r);
            req_buf.push('\n');
        }
        let _ = stdin.write_all(req_buf.as_bytes());
    }

    let out = child
        .wait_with_output()
        .context("Failed waiting on `git cat-file --batch`")?;
    if out.status.success() {
        let bytes = &out.stdout;
        let mut pos = 0usize;
        for repo_rel in repo_rels {
            let Some(nl_rel) = bytes[pos..].iter().position(|&b| b == b'\n') else {
                break;
            };
            let header = String::from_utf8_lossy(&bytes[pos..pos + nl_rel]);
            pos += nl_rel + 1;
            let parts: Vec<&str> = header.split_whitespace().collect();
            if parts.len() >= 3 && parts[1] == "blob" {
                if let Ok(sz) = parts[2].parse::<usize>() {
                    if pos + sz <= bytes.len() {
                        let content = String::from_utf8_lossy(&bytes[pos..pos + sz]).to_string();
                        out_map.insert(repo_rel.clone(), content);
                        pos += sz;
                        if pos < bytes.len() && bytes[pos] == b'\n' {
                            pos += 1;
                        }
                    } else {
                        break;
                    }
                }
            }
        }
    }
    Ok(out_map)
}

#[derive(serde::Serialize, serde::Deserialize, Clone)]
pub(crate) struct CachedBaseShard {
    name: String,
    stmt_hash: String,
    prefix_env_hash: String,
    #[serde(default)]
    proof_hash: String,
    shard_key: String,
}

#[derive(serde::Serialize, serde::Deserialize, Clone)]
pub(crate) struct CachedHeadFileEntry {
    src_len: usize,
    prefix_byte_len: usize,
    prefix_src: String,
    prefix_interface_hash: String,
    suffix_blake3: String,
    interface_hash: String,
    shards: Vec<CachedBaseShard>,
    #[serde(default)]
    hygiene: splitter::HygieneReport,
    #[serde(default)]
    head_mtime_sec: i64,
    #[serde(default)]
    head_mtime_nsec: i64,
    #[serde(default)]
    head_size_bytes: i64,
}

pub(crate) fn file_stat_tuple(path: &Path) -> Option<(i64, i64, i64)> {
    let m = fs::metadata(path).ok()?;
    Some(TurboStore::extract_file_stat_tuple(&m))
}

pub(crate) fn stable_file_stat_for_head(path: &Path) -> Option<(i64, i64, i64)> {
    let (m_sec, m_nsec, f_sz) = file_stat_tuple(path)?;
    if m_sec <= 0 || f_sz <= 0 {
        return None;
    }
    Some((m_sec, m_nsec, f_sz))
}

pub(crate) fn compute_suffix_fast_fingerprint(suffix: &[u8]) -> String {
    let mut h = blake3::Hasher::new();
    h.update(&(suffix.len() as u64).to_le_bytes());
    if suffix.len() <= 768 {
        h.update(suffix);
    } else {
        let mid = suffix.len() / 2;
        h.update(&suffix[..256]);
        h.update(&suffix[mid..mid + 256]);
        h.update(&suffix[suffix.len() - 256..]);
    }
    h.finalize().to_hex().to_string()
}

pub(crate) fn try_read_prefix_if_suffix_matches(
    path: &Path,
    f_sz: i64,
    base_entry: &CachedHeadFileEntry,
) -> Option<String> {
    if f_sz <= 0
        || base_entry.prefix_byte_len == 0
        || base_entry.prefix_byte_len >= base_entry.src_len
        || base_entry.suffix_blake3.is_empty()
    {
        return None;
    }
    let suffix_len = base_entry.src_len - base_entry.prefix_byte_len;
    if suffix_len <= 768 {
        return None;
    }
    let total_len = f_sz as usize;
    if total_len <= suffix_len || total_len > suffix_len + base_entry.prefix_byte_len + 65_536 {
        return None;
    }
    let cur_prefix_len = total_len - suffix_len;
    let file = fs::File::open(path).ok()?;
    use std::os::unix::fs::FileExt;
    let head_read_len = cur_prefix_len + 256;
    let mut buf = vec![0u8; head_read_len];
    file.read_exact_at(&mut buf, 0).ok()?;
    let mut mid_tail = [0u8; 512];
    let mid_off = (cur_prefix_len + suffix_len / 2) as u64;
    let tail_off = (total_len - 256) as u64;
    file.read_exact_at(&mut mid_tail[..256], mid_off).ok()?;
    file.read_exact_at(&mut mid_tail[256..], tail_off).ok()?;
    let mut h = blake3::Hasher::new();
    h.update(&(suffix_len as u64).to_le_bytes());
    h.update(&buf[cur_prefix_len..cur_prefix_len + 256]);
    h.update(&mid_tail[..256]);
    h.update(&mid_tail[256..]);
    if h.finalize().to_hex().as_str() != base_entry.suffix_blake3 {
        return None;
    }
    buf.truncate(cur_prefix_len);
    String::from_utf8(buf).ok()
}

pub(crate) fn build_cached_head_file_entry(
    base_src: &str,
    sp: &splitter::SplitResult,
    toolchain: &str,
    head_stat: Option<(i64, i64, i64)>,
) -> CachedHeadFileEntry {
    let (head_mtime_sec, head_mtime_nsec, head_size_bytes) = head_stat.unwrap_or((0, 0, 0));
    let src_len = base_src.len();
    let shards: Vec<CachedBaseShard> = sp
        .shards
        .iter()
        .map(|sh| CachedBaseShard {
            name: sh.name.clone(),
            stmt_hash: sh.stmt_hash.clone(),
            prefix_env_hash: sh.prefix_env_hash.clone(),
            proof_hash: sh.proof_hash.clone(),
            shard_key: compute_shard_key(toolchain, sh),
        })
        .collect();

    if src_len > 16_384 && !sp.shards.is_empty() {
        let max_end_line = sp.shards.iter().map(|s| s.end_line).max().unwrap_or(0);
        if max_end_line > 0 {
            let bytes = base_src.as_bytes();
            let mut lines_seen = 0usize;
            let mut p_len = 0usize;
            for (idx, &b) in bytes.iter().enumerate() {
                if b == b'\n' {
                    lines_seen += 1;
                    if lines_seen == max_end_line {
                        p_len = idx + 1;
                        break;
                    }
                }
            }
            if p_len > 0 && p_len + 4096 < src_len {
                let prefix_slice = &base_src[..p_len];
                let suffix_slice = &base_src[p_len..];
                let prefix_sp = split_lean_source(prefix_slice, &[]);
                if prefix_sp.shards.len() == sp.shards.len() {
                    let suffix_blake3 = compute_suffix_fast_fingerprint(suffix_slice.as_bytes());
                    return CachedHeadFileEntry {
                        src_len,
                        prefix_byte_len: p_len,
                        prefix_src: prefix_slice.to_string(),
                        prefix_interface_hash: prefix_sp.interface_hash,
                        suffix_blake3,
                        interface_hash: sp.interface_hash.clone(),
                        shards,
                        hygiene: sp.hygiene.clone(),
                        head_mtime_sec,
                        head_mtime_nsec,
                        head_size_bytes,
                    };
                }
            }
        }
    }

    CachedHeadFileEntry {
        src_len,
        prefix_byte_len: src_len,
        prefix_src: base_src.to_string(),
        prefix_interface_hash: sp.interface_hash.clone(),
        suffix_blake3: String::new(),
        interface_hash: sp.interface_hash.clone(),
        shards,
        hygiene: sp.hygiene.clone(),
        head_mtime_sec,
        head_mtime_nsec,
        head_size_bytes,
    }
}

pub(crate) fn is_unchanged_against_head_entry(cur_src: &str, base_entry: &CachedHeadFileEntry) -> bool {
    if cur_src.len() != base_entry.src_len {
        return false;
    }
    if base_entry.prefix_byte_len == base_entry.src_len {
        cur_src == base_entry.prefix_src
    } else {
        cur_src.starts_with(&base_entry.prefix_src)
            && compute_suffix_fast_fingerprint(&cur_src.as_bytes()[base_entry.prefix_byte_len..])
                == base_entry.suffix_blake3
    }
}

pub(crate) fn split_modified_against_head_entry(
    cur_src: &str,
    base_entry: &CachedHeadFileEntry,
) -> (splitter::SplitResult, Option<usize>) {
    if base_entry.prefix_byte_len < base_entry.src_len && !base_entry.suffix_blake3.is_empty() {
        let suffix_len = base_entry.src_len - base_entry.prefix_byte_len;
        if cur_src.len() > suffix_len && cur_src.is_char_boundary(cur_src.len() - suffix_len) {
            let cur_prefix_len = cur_src.len() - suffix_len;
            if compute_suffix_fast_fingerprint(&cur_src.as_bytes()[cur_prefix_len..])
                == base_entry.suffix_blake3
            {
                let mut prefix_sp = split_lean_source(&cur_src[..cur_prefix_len], &[]);
                if prefix_sp.interface_hash == base_entry.prefix_interface_hash
                    && prefix_sp.shards.len() == base_entry.shards.len()
                    && prefix_sp.hygiene.is_clean_for_certification()
                {
                    prefix_sp.interface_hash = base_entry.interface_hash.clone();
                    return (prefix_sp, Some(cur_prefix_len));
                }
            }
        }
    }
    (split_lean_source(cur_src, &[]), None)
}

pub(crate) fn try_fast_split_single_file_from_path(
    store: &TurboStore,
    canon_dir: &Path,
    canon_file: &Path,
    f_sz: i64,
    toolchain: &str,
) -> Option<(String, splitter::SplitResult, usize)> {
    let repo_root = resolve_git_toplevel(canon_dir).ok()?;
    let sha = resolve_git_head_sha(&repo_root, "HEAD")?;
    let mut h = blake3::Hasher::new();
    h.update(b"git-head-tree:v5:");
    h.update(repo_root.to_string_lossy().as_bytes());
    h.update(b":");
    h.update(canon_dir.to_string_lossy().as_bytes());
    h.update(b":");
    h.update(sha.as_bytes());
    h.update(b":");
    h.update(toolchain.as_bytes());
    let cache_file = store
        .fast_staging_dir()
        .join(format!("git_head_tree_v5_{}.json", &h.finalize().to_hex()[..24]));
    let bytes = fs::read(&cache_file).ok()?;
    let cached_map =
        serde_json::from_slice::<std::collections::HashMap<String, CachedHeadFileEntry>>(&bytes)
            .ok()?;
    let rel = canon_file
        .strip_prefix(canon_dir)
        .unwrap_or(canon_file)
        .to_string_lossy()
        .replace('\\', "/");
    let base_entry = cached_map.get(&rel)?;
    let prefix_src = try_read_prefix_if_suffix_matches(canon_file, f_sz, base_entry)?;
    let mut prefix_sp = split_lean_source(&prefix_src, &[]);
    if prefix_sp.interface_hash == base_entry.prefix_interface_hash
        && prefix_sp.shards.len() == base_entry.shards.len()
        && prefix_sp.hygiene.is_clean_for_certification()
    {
        let unchanged = prefix_src.len() == base_entry.prefix_byte_len
            && prefix_src == base_entry.prefix_src;
        prefix_sp.interface_hash = base_entry.interface_hash.clone();
        return Some((prefix_src, prefix_sp, usize::from(unchanged)));
    }
    None
}

pub(crate) fn try_fast_split_single_file(
    store: &TurboStore,
    canon_dir: &Path,
    canon_file: &Path,
    src: &str,
    toolchain: &str,
) -> Option<(splitter::SplitResult, usize, usize)> {
    let repo_root = resolve_git_toplevel(canon_dir).ok()?;
    let sha = resolve_git_head_sha(&repo_root, "HEAD")?;
    let mut h = blake3::Hasher::new();
    h.update(b"git-head-tree:v5:");
    h.update(repo_root.to_string_lossy().as_bytes());
    h.update(b":");
    h.update(canon_dir.to_string_lossy().as_bytes());
    h.update(b":");
    h.update(sha.as_bytes());
    h.update(b":");
    h.update(toolchain.as_bytes());
    let cache_file = store
        .fast_staging_dir()
        .join(format!("git_head_tree_v5_{}.json", &h.finalize().to_hex()[..24]));
    let bytes = fs::read(&cache_file).ok()?;
    let cached_map =
        serde_json::from_slice::<std::collections::HashMap<String, CachedHeadFileEntry>>(&bytes)
            .ok()?;
    let rel = canon_file
        .strip_prefix(canon_dir)
        .unwrap_or(canon_file)
        .to_string_lossy()
        .replace('\\', "/");
    let base_entry = cached_map.get(&rel)?;
    if base_entry.prefix_byte_len < base_entry.src_len && !base_entry.suffix_blake3.is_empty() {
        let suffix_len = base_entry.src_len - base_entry.prefix_byte_len;
        if src.len() > suffix_len && src.is_char_boundary(src.len() - suffix_len) {
            let cur_prefix_len = src.len() - suffix_len;
            if compute_suffix_fast_fingerprint(&src.as_bytes()[cur_prefix_len..])
                == base_entry.suffix_blake3
            {
                let mut prefix_sp = split_lean_source(&src[..cur_prefix_len], &[]);
                if prefix_sp.interface_hash == base_entry.prefix_interface_hash
                    && prefix_sp.shards.len() == base_entry.shards.len()
                    && prefix_sp.hygiene.is_clean_for_certification()
                {
                    let unchanged = cur_prefix_len == base_entry.prefix_byte_len
                        && src.starts_with(&base_entry.prefix_src);
                    prefix_sp.interface_hash = base_entry.interface_hash.clone();
                    return Some((prefix_sp, usize::from(unchanged), cur_prefix_len));
                }
            }
        }
    }
    None
}

pub(crate) fn warm_git_head_tree_cache(
    store: &TurboStore,
    canon_dir: &Path,
    lean_paths: &[PathBuf],
    toolchain: &str,
    precomputed_splits: Option<&[(PathBuf, String, splitter::SplitResult)]>,
) {
    if lean_paths.is_empty() || lean_paths.len() > 32 {
        return;
    }
    let Ok(repo_root) = resolve_git_toplevel(canon_dir) else {
        return;
    };
    let Some(sha) = resolve_git_head_sha(&repo_root, "HEAD") else {
        return;
    };
    let mut h = blake3::Hasher::new();
    h.update(b"git-head-tree:v5:");
    h.update(repo_root.to_string_lossy().as_bytes());
    h.update(b":");
    h.update(canon_dir.to_string_lossy().as_bytes());
    h.update(b":");
    h.update(sha.as_bytes());
    h.update(b":");
    h.update(toolchain.as_bytes());
    let cache_file = store
        .fast_staging_dir()
        .join(format!("git_head_tree_v5_{}.json", &h.finalize().to_hex()[..24]));
    if cache_file.exists() {
        if let Ok(bytes) = fs::read(&cache_file) {
            if let Ok(mut head_tree_map) =
                serde_json::from_slice::<std::collections::HashMap<String, CachedHeadFileEntry>>(
                    &bytes,
                )
            {
                let mut updated = false;
                for p in lean_paths {
                    let rel = p
                        .strip_prefix(canon_dir)
                        .unwrap_or(p)
                        .to_string_lossy()
                        .replace('\\', "/");
                    if let Some(entry) = head_tree_map.get_mut(&rel) {
                        if let Some((m_sec, m_nsec, f_sz)) = file_stat_tuple(p) {
                            let stat_ok = entry.head_size_bytes > 0
                                && entry.head_mtime_sec == m_sec
                                && entry.head_mtime_nsec == m_nsec
                                && entry.head_size_bytes == f_sz;
                            if !stat_ok {
                                let is_unchanged = if let Some(prefix_only) =
                                    try_read_prefix_if_suffix_matches(p, f_sz, entry)
                                {
                                    prefix_only == entry.prefix_src
                                } else if let Ok(cur_src) = fs::read_to_string(p) {
                                    is_unchanged_against_head_entry(&cur_src, entry)
                                } else {
                                    false
                                };
                                if is_unchanged {
                                    if let Some((s_sec, s_nsec, s_sz)) =
                                        stable_file_stat_for_head(p)
                                    {
                                        entry.head_mtime_sec = s_sec;
                                        entry.head_mtime_nsec = s_nsec;
                                        entry.head_size_bytes = s_sz;
                                        updated = true;
                                    }
                                }
                            }
                        }
                    }
                }
                if updated {
                    if let Ok(json_bytes) = serde_json::to_vec(&head_tree_map) {
                        let _ = fs::write(&cache_file, json_bytes);
                    }
                }
            }
        }
        return;
    }
    let proj_prefix = canon_dir
        .strip_prefix(&repo_root)
        .unwrap_or(Path::new(""))
        .to_string_lossy()
        .replace('\\', "/");
    let all_lean_repo_rels: Vec<String> = lean_paths
        .iter()
        .map(|p| {
            let rel = p
                .strip_prefix(canon_dir)
                .unwrap_or(p)
                .to_string_lossy()
                .replace('\\', "/");
            if proj_prefix.is_empty() {
                rel
            } else {
                format!("{}/{}", proj_prefix.trim_end_matches('/'), rel)
            }
        })
        .collect();
    if let Ok(fetched_blobs) = fetch_git_blobs_batch(&repo_root, "HEAD", &all_lean_repo_rels) {
        if fetched_blobs.len() == lean_paths.len() {
            let mut split_by_path = std::collections::HashMap::new();
            if let Some(splits) = precomputed_splits {
                for (p, s, sp) in splits {
                    split_by_path.insert(p.as_path(), (s.as_str(), sp));
                }
            }
            let mut rel_blob_map = std::collections::HashMap::with_capacity(lean_paths.len());
            for p in lean_paths {
                let rel = p
                    .strip_prefix(canon_dir)
                    .unwrap_or(p)
                    .to_string_lossy()
                    .replace('\\', "/");
                let repo_rel = if proj_prefix.is_empty() {
                    rel.clone()
                } else {
                    format!("{}/{}", proj_prefix.trim_end_matches('/'), rel)
                };
                if let Some(bs) = fetched_blobs.get(&repo_rel) {
                    let (sp, matches_worktree): (std::borrow::Cow<'_, splitter::SplitResult>, bool) =
                        if let Some((cur_src, sp)) = split_by_path.get(p.as_path()) {
                            if *cur_src == bs.as_str() {
                                (std::borrow::Cow::Borrowed(*sp), true)
                            } else if cur_src.is_empty()
                                && fs::read_to_string(p).ok().as_deref() == Some(bs.as_str())
                            {
                                (std::borrow::Cow::Borrowed(*sp), true)
                            } else {
                                (std::borrow::Cow::Owned(split_lean_source(bs, &[])), false)
                            }
                        } else {
                            let wt_matches =
                                fs::read_to_string(p).ok().as_deref() == Some(bs.as_str());
                            (std::borrow::Cow::Owned(split_lean_source(bs, &[])), wt_matches)
                        };
                    let head_stat = if matches_worktree {
                        stable_file_stat_for_head(p)
                    } else {
                        None
                    };
                    rel_blob_map.insert(
                        rel,
                        build_cached_head_file_entry(bs, &sp, toolchain, head_stat),
                    );
                }
            }
            if rel_blob_map.len() == lean_paths.len() {
                if let Ok(json_bytes) = serde_json::to_vec(&rel_blob_map) {
                    let _ = fs::write(&cache_file, json_bytes);
                }
            }
        }
    }
}

pub(crate) fn load_and_classify_pr_from_git(
    store: &TurboStore,
    canon_dir: &Path,
    base_ref: &str,
    toolchain: &str,
) -> Result<(
    PrClassification,
    std::collections::BTreeMap<String, Vec<(String, splitter::TheoremShard, bool)>>,
    std::collections::BTreeMap<String, String>,
    std::collections::BTreeMap<String, splitter::SplitResult>,
)> {
    let repo_root = resolve_git_toplevel(canon_dir)?;
    let proj_prefix = canon_dir
        .strip_prefix(&repo_root)
        .unwrap_or(Path::new(""))
        .to_string_lossy()
        .replace('\\', "/");

    let mut lean_paths: Vec<PathBuf> = Vec::new();
    for entry in WalkDir::new(canon_dir)
        .into_iter()
        .filter_entry(|e| {
            let n = e.file_name().to_string_lossy();
            n != ".git" && n != ".lake" && n != "target"
        })
        .flatten()
    {
        if entry.file_type().is_file()
            && entry.path().extension().and_then(|s| s.to_str()) == Some("lean")
        {
            lean_paths.push(entry.path().to_path_buf());
        }
    }
    lean_paths.sort();

    enum PrFileEntry {
        Unchanged(splitter::SplitResult),
        Changed {
            base_src: Option<String>,
            cur_src: Option<String>,
            cur_split: Option<splitter::SplitResult>,
        },
    }

    let head_sha_opt = resolve_git_head_sha(&repo_root, base_ref);
    let head_tree_cache_file = head_sha_opt.as_ref().map(|sha| {
        let mut h = blake3::Hasher::new();
        h.update(b"git-head-tree:v5:");
        h.update(repo_root.to_string_lossy().as_bytes());
        h.update(b":");
        h.update(canon_dir.to_string_lossy().as_bytes());
        h.update(b":");
        h.update(sha.as_bytes());
        h.update(b":");
        h.update(toolchain.as_bytes());
        store
            .fast_staging_dir()
            .join(format!("git_head_tree_v5_{}.json", &h.finalize().to_hex()[..24]))
    });

    let mut entries_by_rel_path: std::collections::HashMap<String, PrFileEntry> =
        std::collections::HashMap::with_capacity(lean_paths.len());
    let mut changed_current_files = std::collections::BTreeMap::new();
    let mut changed_current_splits = std::collections::BTreeMap::new();
    let mut current_files_count = 0usize;
    let used_head_tree_cache = false;

    if let Some(ref cache_file) = head_tree_cache_file {
        if let Ok(bytes) = fs::read(cache_file) {
            if let Ok(mut head_tree_map) =
                serde_json::from_slice::<std::collections::HashMap<String, CachedHeadFileEntry>>(
                    &bytes,
                )
            {
                let all_known = lean_paths.len() == head_tree_map.len()
                    && lean_paths.iter().all(|p| {
                        let rel = p
                            .strip_prefix(canon_dir)
                            .unwrap_or(p)
                            .to_string_lossy()
                            .replace('\\', "/");
                        head_tree_map.contains_key(&rel)
                    });
                if all_known {
                    enum FastCachedFile {
                        Unchanged(CachedHeadFileEntry),
                        Modified {
                            base_entry: CachedHeadFileEntry,
                            cur_split: splitter::SplitResult,
                        },
                    }

                    let mut unchanged_map: std::collections::HashMap<String, CachedHeadFileEntry> =
                        std::collections::HashMap::with_capacity(lean_paths.len());
                    let mut stat_missed: Vec<(PathBuf, String, CachedHeadFileEntry, i64)> =
                        Vec::new();
                    let mut all_paths: Vec<String> = Vec::with_capacity(lean_paths.len());
                    let mut updated_stats = false;

                    for path in &lean_paths {
                        let rel_path = path
                            .strip_prefix(canon_dir)
                            .unwrap_or(path)
                            .to_string_lossy()
                            .replace('\\', "/");
                        if let Some(base_entry) = head_tree_map.remove(&rel_path) {
                            all_paths.push(rel_path.clone());
                            let stat_tuple = file_stat_tuple(path);
                            let stat_unchanged = if base_entry.head_size_bytes > 0 {
                                if let Some((m_sec, m_nsec, f_sz)) = stat_tuple {
                                    m_sec == base_entry.head_mtime_sec
                                        && m_nsec == base_entry.head_mtime_nsec
                                        && f_sz == base_entry.head_size_bytes
                                } else {
                                    false
                                }
                            } else {
                                false
                            };
                            if stat_unchanged {
                                unchanged_map.insert(rel_path, base_entry);
                            } else {
                                let f_sz = stat_tuple.map(|(_, _, sz)| sz).unwrap_or(0);
                                stat_missed.push((path.clone(), rel_path, base_entry, f_sz));
                            }
                        }
                    }

                    enum StatMissedOutcome {
                        Unchanged {
                            rel_path: String,
                            base_entry: CachedHeadFileEntry,
                            stat_updated: bool,
                        },
                        Modified {
                            rel_path: String,
                            cur_src: String,
                            base_entry: CachedHeadFileEntry,
                            cur_split: splitter::SplitResult,
                        },
                    }

                    let evaluate_stat_missed =
                        |(path, rel_path, mut base_entry, f_sz): (
                            PathBuf,
                            String,
                            CachedHeadFileEntry,
                            i64,
                        )|
                         -> StatMissedOutcome {
                            if let Some(prefix_only) =
                                try_read_prefix_if_suffix_matches(&path, f_sz, &base_entry)
                            {
                                if prefix_only == base_entry.prefix_src {
                                    let mut stat_updated = false;
                                    if let Some((m_sec, m_nsec, s_sz)) =
                                        stable_file_stat_for_head(&path)
                                    {
                                        if base_entry.head_mtime_sec != m_sec
                                            || base_entry.head_mtime_nsec != m_nsec
                                            || base_entry.head_size_bytes != s_sz
                                        {
                                            base_entry.head_mtime_sec = m_sec;
                                            base_entry.head_mtime_nsec = m_nsec;
                                            base_entry.head_size_bytes = s_sz;
                                            stat_updated = true;
                                        }
                                    }
                                    return StatMissedOutcome::Unchanged {
                                        rel_path,
                                        base_entry,
                                        stat_updated,
                                    };
                                }
                                let mut prefix_sp = split_lean_source(&prefix_only, &[]);
                                if prefix_sp.interface_hash == base_entry.prefix_interface_hash
                                    && prefix_sp.shards.len() == base_entry.shards.len()
                                    && prefix_sp.hygiene.is_clean_for_certification()
                                {
                                    prefix_sp.interface_hash = base_entry.interface_hash.clone();
                                    return StatMissedOutcome::Modified {
                                        rel_path,
                                        cur_src: prefix_only,
                                        base_entry,
                                        cur_split: prefix_sp,
                                    };
                                }
                            }
                            let mut cur_src = fs::read_to_string(&path).unwrap_or_default();
                            if is_unchanged_against_head_entry(&cur_src, &base_entry) {
                                let mut stat_updated = false;
                                if let Some((m_sec, m_nsec, f_sz)) =
                                    stable_file_stat_for_head(&path)
                                {
                                    if base_entry.head_mtime_sec != m_sec
                                        || base_entry.head_mtime_nsec != m_nsec
                                        || base_entry.head_size_bytes != f_sz
                                    {
                                        base_entry.head_mtime_sec = m_sec;
                                        base_entry.head_mtime_nsec = m_nsec;
                                        base_entry.head_size_bytes = f_sz;
                                        stat_updated = true;
                                    }
                                }
                                StatMissedOutcome::Unchanged {
                                    rel_path,
                                    base_entry,
                                    stat_updated,
                                }
                            } else {
                                let (cur_split, prefix_len_opt) =
                                    split_modified_against_head_entry(&cur_src, &base_entry);
                                if let Some(plen) = prefix_len_opt {
                                    cur_src.truncate(plen);
                                }
                                StatMissedOutcome::Modified {
                                    rel_path,
                                    cur_src,
                                    base_entry,
                                    cur_split,
                                }
                            }
                        };

                    let outcomes: Vec<StatMissedOutcome> = if stat_missed.len() >= 2
                        && stat_missed
                            .iter()
                            .map(|(_, _, b, _)| b.prefix_byte_len)
                            .sum::<usize>()
                            > 32_768
                    {
                        std::thread::scope(|s| {
                            let handles: Vec<_> = stat_missed
                                .into_iter()
                                .map(|item| s.spawn(move || evaluate_stat_missed(item)))
                                .collect();
                            handles
                                .into_iter()
                                .map(|h| h.join().expect("pr-verify stat_missed thread panicked"))
                                .collect()
                        })
                    } else {
                        stat_missed
                            .into_iter()
                            .map(evaluate_stat_missed)
                            .collect()
                    };

                    let mut split_modified: Vec<(
                        String,
                        CachedHeadFileEntry,
                        splitter::SplitResult,
                    )> = Vec::new();
                    for outcome in outcomes {
                        match outcome {
                            StatMissedOutcome::Unchanged {
                                rel_path,
                                base_entry,
                                stat_updated,
                            } => {
                                if stat_updated {
                                    updated_stats = true;
                                }
                                unchanged_map.insert(rel_path, base_entry);
                            }
                            StatMissedOutcome::Modified {
                                rel_path,
                                cur_src,
                                base_entry,
                                cur_split,
                            } => {
                                changed_current_files.insert(rel_path.clone(), cur_src);
                                split_modified.push((rel_path, base_entry, cur_split));
                            }
                        }
                    }

                    if updated_stats {
                        if split_modified.is_empty() {
                            if let Ok(json_bytes) = serde_json::to_vec(&unchanged_map) {
                                let _ = fs::write(cache_file, json_bytes);
                            }
                        } else {
                            let mut full_map = unchanged_map.clone();
                            for (rel_path, base_entry, _) in &split_modified {
                                full_map.insert(rel_path.clone(), base_entry.clone());
                            }
                            if let Ok(json_bytes) = serde_json::to_vec(&full_map) {
                                let _ = fs::write(cache_file, json_bytes);
                            }
                        }
                    }

                    let mut fast_entries: std::collections::HashMap<String, FastCachedFile> =
                        std::collections::HashMap::with_capacity(all_paths.len());
                    for (rel_path, base_entry) in unchanged_map {
                        fast_entries.insert(rel_path, FastCachedFile::Unchanged(base_entry));
                    }
                    for (rel_path, base_entry, cur_split) in split_modified {
                        fast_entries.insert(
                            rel_path,
                            FastCachedFile::Modified {
                                base_entry,
                                cur_split,
                            },
                        );
                    }

                    all_paths.sort_by(|a, b| Path::new(a.as_str()).cmp(Path::new(b.as_str())));

                    let mut baseline_ih_hasher = blake3::Hasher::new();
                    baseline_ih_hasher.update(toolchain.as_bytes());
                    let mut current_ih_hasher = blake3::Hasher::new();
                    current_ih_hasher.update(toolchain.as_bytes());

                    let mut modified_files = Vec::new();
                    let mut altered_interface_files = Vec::new();
                    let mut unchanged_theorems = Vec::new();
                    let mut proof_edited_theorems = Vec::new();
                    let mut statement_edited_theorems = Vec::new();
                    let mut per_file_interfaces = std::collections::BTreeMap::new();
                    let mut shards_to_verify_by_file = std::collections::BTreeMap::new();
                    let mut flagged_files = Vec::new();

                    for rel_path in all_paths {
                        let Some(entry) = fast_entries.remove(&rel_path) else {
                            continue;
                        };
                        match entry {
                            FastCachedFile::Unchanged(base_entry) => {
                                baseline_ih_hasher.update(rel_path.as_bytes());
                                baseline_ih_hasher.update(b":");
                                baseline_ih_hasher.update(base_entry.interface_hash.as_bytes());
                                baseline_ih_hasher.update(b"\n");

                                current_ih_hasher.update(rel_path.as_bytes());
                                current_ih_hasher.update(b":");
                                current_ih_hasher.update(base_entry.interface_hash.as_bytes());
                                current_ih_hasher.update(b"\n");

                                per_file_interfaces
                                    .insert(rel_path.clone(), base_entry.interface_hash);
                                for s in base_entry.shards {
                                    unchanged_theorems.push(format!("{}::{}", rel_path, s.name));
                                }
                            }
                            FastCachedFile::Modified {
                                base_entry,
                                cur_split,
                            } => {
                                modified_files.push(rel_path.clone());
                                changed_current_splits.insert(rel_path.clone(), cur_split.clone());
                                let reg =
                                    cur_split.hygiene.regression_items_against(&base_entry.hygiene);
                                if !reg.is_empty() {
                                    flagged_files.push((rel_path.clone(), reg));
                                }

                                baseline_ih_hasher.update(rel_path.as_bytes());
                                baseline_ih_hasher.update(b":");
                                baseline_ih_hasher.update(base_entry.interface_hash.as_bytes());
                                baseline_ih_hasher.update(b"\n");

                                current_ih_hasher.update(rel_path.as_bytes());
                                current_ih_hasher.update(b":");
                                current_ih_hasher.update(cur_split.interface_hash.as_bytes());
                                current_ih_hasher.update(b"\n");

                                per_file_interfaces
                                    .insert(rel_path.clone(), cur_split.interface_hash.clone());

                                let file_interface_same =
                                    cur_split.interface_hash == base_entry.interface_hash
                                        && cur_split.shards.len() == base_entry.shards.len();
                                let mut file_has_stmt_change = !file_interface_same;

                                let mut base_by_name = std::collections::HashMap::new();
                                for bs in &base_entry.shards {
                                    base_by_name.insert(bs.name.as_str(), bs);
                                }
                                let cur_names: std::collections::HashSet<&str> = cur_split
                                    .shards
                                    .iter()
                                    .map(|s| s.name.as_str())
                                    .collect();
                                for bs in &base_entry.shards {
                                    if !cur_names.contains(bs.name.as_str()) {
                                        file_has_stmt_change = true;
                                        statement_edited_theorems
                                            .push(format!("{}::{} (deleted)", rel_path, bs.name));
                                    }
                                }

                                let mut file_verify_list = Vec::new();
                                for s in cur_split.shards {
                                    let qualified = format!("{}::{}", rel_path, s.name);
                                    if let Some(bs) = base_by_name.get(s.name.as_str()) {
                                        if !bs.proof_hash.is_empty()
                                            && s.proof_hash == bs.proof_hash
                                            && s.stmt_hash == bs.stmt_hash
                                            && s.prefix_env_hash == bs.prefix_env_hash
                                        {
                                            unchanged_theorems.push(qualified);
                                            continue;
                                        }
                                        let k = compute_shard_key(toolchain, &s);
                                        if k == bs.shard_key {
                                            unchanged_theorems.push(qualified);
                                        } else if s.stmt_hash == bs.stmt_hash
                                            && s.prefix_env_hash == bs.prefix_env_hash
                                            && file_interface_same
                                        {
                                            proof_edited_theorems.push(qualified);
                                            file_verify_list.push((k, s, true));
                                        } else {
                                            file_has_stmt_change = true;
                                            statement_edited_theorems.push(qualified);
                                            file_verify_list.push((k, s, false));
                                        }
                                    } else {
                                        let k = compute_shard_key(toolchain, &s);
                                        file_has_stmt_change = true;
                                        statement_edited_theorems.push(qualified);
                                        file_verify_list.push((k, s, false));
                                    }
                                }

                                if file_has_stmt_change {
                                    altered_interface_files.push(rel_path.clone());
                                }
                                if !file_verify_list.is_empty() {
                                    shards_to_verify_by_file.insert(rel_path, file_verify_list);
                                }
                            }
                        }
                    }

                    if !flagged_files.is_empty() {
                        anyhow::bail!(
                            "PR Hygiene & Axiom Gate FAILED on {} files: {:?}",
                            flagged_files.len(),
                            flagged_files
                        );
                    }

                    let baseline_interface_hash =
                        baseline_ih_hasher.finalize().to_hex().to_string();
                    let current_interface_hash = current_ih_hasher.finalize().to_hex().to_string();
                    let interface_drift = baseline_interface_hash != current_interface_hash
                        || !altered_interface_files.is_empty();

                    return Ok((
                        PrClassification {
                            total_files: lean_paths.len(),
                            modified_files,
                            altered_interface_files,
                            interface_drift,
                            baseline_interface_hash,
                            current_interface_hash,
                            unchanged_theorems,
                            proof_edited_theorems,
                            statement_edited_theorems,
                            per_file_interfaces,
                        },
                        shards_to_verify_by_file,
                        changed_current_files,
                        changed_current_splits,
                    ));
                }
            }
        }
    }

    if !used_head_tree_cache {
        let mut changed_repo_paths: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        let mut untracked_repo_paths: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        let mut prefetched_blobs: Option<std::collections::HashMap<String, String>> = None;

        let all_lean_repo_rels: Vec<String> = lean_paths
            .iter()
            .map(|p| {
                let rel = p
                    .strip_prefix(canon_dir)
                    .unwrap_or(p)
                    .to_string_lossy()
                    .replace('\\', "/");
                if proj_prefix.is_empty() {
                    rel
                } else {
                    format!("{}/{}", proj_prefix.trim_end_matches('/'), rel)
                }
            })
            .collect();

        let preloaded_res = if base_ref == "HEAD" {
            let (status_res, blobs_res, preloaded) = std::thread::scope(|s| {
                let repo_ref = &repo_root;
                let all_rels_ref = &all_lean_repo_rels;
                let status_h = s.spawn(move || {
                    Command::new("git")
                        .args([
                            "--no-optional-locks",
                            "-C",
                            &repo_ref.to_string_lossy(),
                            "status",
                            "--porcelain",
                            "-uall",
                            "--",
                            &canon_dir.to_string_lossy(),
                        ])
                        .output()
                        .context("Failed to execute `git status --porcelain`")
                });
                let blobs_h = if all_rels_ref.len() <= 32 && !all_rels_ref.is_empty() {
                    Some(s.spawn(move || fetch_git_blobs_batch(repo_ref, "HEAD", all_rels_ref)))
                } else {
                    None
                };

                let preloaded = load_and_split_files_cached(store, &lean_paths);
                (
                    status_h
                        .join()
                        .unwrap_or_else(|_| Err(anyhow::anyhow!("status thread panicked"))),
                    blobs_h.and_then(|h| h.join().ok().and_then(|r| r.ok())),
                    preloaded,
                )
            });
            prefetched_blobs = blobs_res;
            let status_out = status_res?;
            if !status_out.status.success() {
                anyhow::bail!(
                    "Invalid git base ref `{}`: {}",
                    base_ref,
                    String::from_utf8_lossy(&status_out.stderr).trim()
                );
            }
            for line in String::from_utf8_lossy(&status_out.stdout).lines() {
                if line.len() < 4 {
                    continue;
                }
                let status_code = &line[..2];
                let path_part = line[3..].trim();
                if status_code == "??" {
                    let p = path_part.trim_matches('"').replace('\\', "/");
                    if !p.is_empty() {
                        untracked_repo_paths.insert(p.clone());
                        changed_repo_paths.insert(p);
                    }
                } else if let Some((old_p, new_p)) = path_part.split_once(" -> ") {
                    changed_repo_paths.insert(old_p.trim().trim_matches('"').replace('\\', "/"));
                    changed_repo_paths.insert(new_p.trim().trim_matches('"').replace('\\', "/"));
                } else {
                    let p = path_part.trim_matches('"').replace('\\', "/");
                    if !p.is_empty() {
                        changed_repo_paths.insert(p);
                    }
                }
            }
            preloaded
        } else {
            let (diff_res, untracked_res, preloaded) = std::thread::scope(|s| {
                let repo_ref = &repo_root;
                let diff_h = s.spawn(move || {
                    Command::new("git")
                        .args([
                            "--no-optional-locks",
                            "-C",
                            &repo_ref.to_string_lossy(),
                            "diff",
                            "--name-only",
                            base_ref,
                            "--",
                            &canon_dir.to_string_lossy(),
                        ])
                        .output()
                        .context("Failed to execute `git diff --name-only`")
                });
                let untracked_h = s.spawn(move || {
                    Command::new("git")
                        .args([
                            "--no-optional-locks",
                            "-C",
                            &repo_ref.to_string_lossy(),
                            "ls-files",
                            "--others",
                            "--exclude-standard",
                            "--",
                            &canon_dir.to_string_lossy(),
                        ])
                        .output()
                        .context("Failed to execute `git ls-files --others`")
                });

                let preloaded = load_and_split_files_cached(store, &lean_paths);
                (
                    diff_h
                        .join()
                        .unwrap_or_else(|_| Err(anyhow::anyhow!("diff thread panicked"))),
                    untracked_h
                        .join()
                        .unwrap_or_else(|_| Err(anyhow::anyhow!("untracked thread panicked"))),
                    preloaded,
                )
            });

            let diff_out = diff_res?;
            if !diff_out.status.success() {
                anyhow::bail!(
                    "Invalid git base ref `{}`: {}",
                    base_ref,
                    String::from_utf8_lossy(&diff_out.stderr).trim()
                );
            }
            changed_repo_paths = String::from_utf8_lossy(&diff_out.stdout)
                .lines()
                .map(|l| l.trim().replace('\\', "/"))
                .filter(|l| !l.is_empty())
                .collect();

            let untracked_out = untracked_res?;
            untracked_repo_paths = String::from_utf8_lossy(&untracked_out.stdout)
                .lines()
                .map(|l| l.trim().replace('\\', "/"))
                .filter(|l| !l.is_empty())
                .collect();
            changed_repo_paths.extend(untracked_repo_paths.iter().cloned());
            preloaded
        };

        let (preloaded_splits, _) = preloaded_res?;

        let mut repo_rels_to_fetch: Vec<String> = Vec::new();
        let mut rel_to_repo_rel: Vec<(String, String, String, splitter::SplitResult)> = Vec::new();

        for (path, cached_src, split) in preloaded_splits {
            current_files_count += 1;
            let rel_path = path
                .strip_prefix(canon_dir)
                .unwrap_or(&path)
                .to_string_lossy()
                .replace('\\', "/");

            let repo_rel = if proj_prefix.is_empty() {
                rel_path.clone()
            } else {
                format!("{}/{}", proj_prefix.trim_end_matches('/'), rel_path)
            };

            if !changed_repo_paths.contains(&repo_rel) {
                entries_by_rel_path.insert(rel_path, PrFileEntry::Unchanged(split));
            } else {
                let cur_src = if cached_src.is_empty() {
                    fs::read_to_string(&path).unwrap_or_default()
                } else {
                    cached_src
                };
                changed_current_files.insert(rel_path.clone(), cur_src.clone());
                if !untracked_repo_paths.contains(&repo_rel) {
                    if !prefetched_blobs
                        .as_ref()
                        .map(|m| m.contains_key(&repo_rel))
                        .unwrap_or(false)
                    {
                        repo_rels_to_fetch.push(repo_rel.clone());
                    }
                }
                rel_to_repo_rel.push((rel_path, repo_rel, cur_src, split));
            }
        }

        let mut deleted_to_fetch: Vec<(String, String)> = Vec::new();
        for repo_rel in &changed_repo_paths {
            if !repo_rel.ends_with(".lean") || untracked_repo_paths.contains(repo_rel) {
                continue;
            }
            let rel_path = if proj_prefix.is_empty() {
                repo_rel.clone()
            } else if let Some(stripped) =
                repo_rel.strip_prefix(&format!("{}/", proj_prefix.trim_end_matches('/')))
            {
                stripped.to_string()
            } else {
                continue;
            }
            ;
            if !entries_by_rel_path.contains_key(&rel_path)
                && !rel_to_repo_rel.iter().any(|(r, _, _, _)| r == &rel_path)
            {
                if !prefetched_blobs
                    .as_ref()
                    .map(|m| m.contains_key(repo_rel))
                    .unwrap_or(false)
                {
                    repo_rels_to_fetch.push(repo_rel.clone());
                }
                deleted_to_fetch.push((rel_path, repo_rel.clone()));
            }
        }

        let mut fetched_blobs = prefetched_blobs.unwrap_or_default();
        if !repo_rels_to_fetch.is_empty() {
            let extra = fetch_git_blobs_batch(&repo_root, base_ref, &repo_rels_to_fetch)?;
            fetched_blobs.extend(extra);
        }

        if let Some(ref cache_file) = head_tree_cache_file {
            if untracked_repo_paths.is_empty()
                && deleted_to_fetch.is_empty()
                && fetched_blobs.len() == lean_paths.len()
            {
                let mut rel_blob_map = std::collections::HashMap::with_capacity(lean_paths.len());
                for p in &lean_paths {
                    let rel = p
                        .strip_prefix(canon_dir)
                        .unwrap_or(p)
                        .to_string_lossy()
                        .replace('\\', "/");
                    let repo_rel = if proj_prefix.is_empty() {
                        rel.clone()
                    } else {
                        format!("{}/{}", proj_prefix.trim_end_matches('/'), rel)
                    };
                    if let Some(bs) = fetched_blobs.get(&repo_rel) {
                        let sp = split_lean_source(bs, &[]);
                        let head_stat = if !changed_repo_paths.contains(&repo_rel) {
                            stable_file_stat_for_head(p)
                        } else {
                            None
                        };
                        rel_blob_map.insert(
                            rel,
                            build_cached_head_file_entry(bs, &sp, toolchain, head_stat),
                        );
                    }
                }
                if rel_blob_map.len() == lean_paths.len() {
                    if let Ok(json_bytes) = serde_json::to_vec(&rel_blob_map) {
                        let _ = fs::write(cache_file, json_bytes);
                    }
                }
            }
        }

        for (rel_path, repo_rel, cur_src, split) in rel_to_repo_rel {
            let base_src = fetched_blobs.remove(&repo_rel);
            entries_by_rel_path.insert(
                rel_path,
                PrFileEntry::Changed {
                    base_src,
                    cur_src: Some(cur_src),
                    cur_split: Some(split),
                },
            );
        }

        for (rel_path, repo_rel) in deleted_to_fetch {
            if let Some(base_src) = fetched_blobs.remove(&repo_rel) {
                entries_by_rel_path.insert(
                    rel_path,
                    PrFileEntry::Changed {
                        base_src: Some(base_src),
                        cur_src: None,
                        cur_split: None,
                    },
                );
            }
        }
    }

    let mut all_paths: Vec<String> = entries_by_rel_path.keys().cloned().collect();
    all_paths.sort_by(|a, b| Path::new(a.as_str()).cmp(Path::new(b.as_str())));

    let mut base_split_keys = Vec::new();
    for entry in entries_by_rel_path.values() {
        if let PrFileEntry::Changed {
            base_src: Some(ref bs),
            ..
        } = entry
        {
            base_split_keys.push(TurboStore::compute_file_split_key(bs.as_bytes()));
        }
    }
    let mut cached_base_splits = if !base_split_keys.is_empty() {
        store
            .batch_get_file_splits(&base_split_keys)
            .unwrap_or_default()
    } else {
        std::collections::HashMap::new()
    };

    let mut resolve_cached_or_split = |src: &str| -> splitter::SplitResult {
        let fk = TurboStore::compute_file_split_key(src.as_bytes());
        if let Some(sp) = cached_base_splits.remove(&fk) {
            return sp;
        }
        if let Ok(mut map) = store.batch_get_file_splits(std::slice::from_ref(&fk)) {
            if let Some(sp) = map.remove(&fk) {
                return sp;
            }
        }
        let sp = split_lean_source(src, &[]);
        let _ = store.batch_put_file_splits(&[(fk, &sp)]);
        sp
    };

    let mut baseline_ih_hasher = blake3::Hasher::new();
    baseline_ih_hasher.update(toolchain.as_bytes());
    let mut current_ih_hasher = blake3::Hasher::new();
    current_ih_hasher.update(toolchain.as_bytes());

    let mut modified_files = Vec::new();
    let mut altered_interface_files = Vec::new();
    let mut unchanged_theorems = Vec::new();
    let mut proof_edited_theorems = Vec::new();
    let mut statement_edited_theorems = Vec::new();
    let mut per_file_interfaces = std::collections::BTreeMap::new();
    let mut shards_to_verify_by_file = std::collections::BTreeMap::new();
    let mut flagged_files = Vec::new();

    for rel_path in all_paths {
        let Some(entry) = entries_by_rel_path.remove(&rel_path) else {
            continue;
        };
        match entry {
            PrFileEntry::Unchanged(split) => {
                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), split.interface_hash);
                for s in split.shards {
                    unchanged_theorems.push(format!("{}::{}", rel_path, s.name));
                }
            }
            PrFileEntry::Changed {
                base_src: Some(base_src),
                cur_src: Some(cur_src),
                cur_split,
            } if base_src == cur_src => {
                let split = cur_split.unwrap_or_else(|| resolve_cached_or_split(&cur_src));
                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), split.interface_hash);
                for s in split.shards {
                    unchanged_theorems.push(format!("{}::{}", rel_path, s.name));
                }
            }
            PrFileEntry::Changed {
                base_src: Some(base_src),
                cur_src: Some(cur_src),
                cur_split,
            } => {
                modified_files.push(rel_path.clone());
                let cur_split = cur_split.unwrap_or_else(|| resolve_cached_or_split(&cur_src));
                changed_current_splits.insert(rel_path.clone(), cur_split.clone());
                let base_split = resolve_cached_or_split(&base_src);
                let reg = cur_split.hygiene.regression_items_against(&base_split.hygiene);
                if !reg.is_empty() {
                    flagged_files.push((rel_path.clone(), reg));
                }

                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(base_split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(cur_split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), cur_split.interface_hash.clone());

                let file_interface_same = cur_split.interface_hash == base_split.interface_hash
                    && cur_split.shards.len() == base_split.shards.len();
                let mut file_has_stmt_change = !file_interface_same;

                let mut base_by_name = std::collections::HashMap::new();
                for bs in &base_split.shards {
                    base_by_name.insert(bs.name.as_str(), (bs, compute_shard_key(toolchain, bs)));
                }
                let cur_names: std::collections::HashSet<&str> =
                    cur_split.shards.iter().map(|s| s.name.as_str()).collect();
                for bs in &base_split.shards {
                    if !cur_names.contains(bs.name.as_str()) {
                        file_has_stmt_change = true;
                        statement_edited_theorems
                            .push(format!("{}::{} (deleted)", rel_path, bs.name));
                    }
                }

                let mut file_verify_list = Vec::new();
                for s in cur_split.shards {
                    let k = compute_shard_key(toolchain, &s);
                    let qualified = format!("{}::{}", rel_path, s.name);
                    if let Some((bs, bk)) = base_by_name.get(s.name.as_str()) {
                        if k == *bk {
                            unchanged_theorems.push(qualified);
                        } else if s.stmt_hash == bs.stmt_hash
                            && s.prefix_env_hash == bs.prefix_env_hash
                            && file_interface_same
                        {
                            proof_edited_theorems.push(qualified);
                            file_verify_list.push((k, s, true));
                        } else {
                            file_has_stmt_change = true;
                            statement_edited_theorems.push(qualified);
                            file_verify_list.push((k, s, false));
                        }
                    } else {
                        file_has_stmt_change = true;
                        statement_edited_theorems.push(qualified);
                        file_verify_list.push((k, s, false));
                    }
                }

                if file_has_stmt_change {
                    altered_interface_files.push(rel_path.clone());
                }
                if !file_verify_list.is_empty() {
                    shards_to_verify_by_file.insert(rel_path, file_verify_list);
                }
            }
            PrFileEntry::Changed {
                base_src: None,
                cur_src: Some(cur_src),
                cur_split,
            } => {
                modified_files.push(rel_path.clone());
                altered_interface_files.push(rel_path.clone());
                let cur_split = cur_split.unwrap_or_else(|| resolve_cached_or_split(&cur_src));
                changed_current_splits.insert(rel_path.clone(), cur_split.clone());
                if !cur_split.hygiene.is_clean_for_certification() {
                    flagged_files.push((rel_path.clone(), cur_split.hygiene.flagged_items));
                }
                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(cur_split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), cur_split.interface_hash);
                let mut file_verify_list = Vec::new();
                for s in cur_split.shards {
                    let k = compute_shard_key(toolchain, &s);
                    statement_edited_theorems.push(format!("{}::{}", rel_path, s.name));
                    file_verify_list.push((k, s, false));
                }
                if !file_verify_list.is_empty() {
                    shards_to_verify_by_file.insert(rel_path, file_verify_list);
                }
            }
            PrFileEntry::Changed {
                base_src: Some(base_src),
                cur_src: None,
                cur_split: _,
            } => {
                modified_files.push(rel_path.clone());
                altered_interface_files.push(rel_path.clone());
                let base_split = resolve_cached_or_split(&base_src);
                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(base_split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                for bs in base_split.shards {
                    statement_edited_theorems
                        .push(format!("{}::{} (deleted)", rel_path, bs.name));
                }
            }
            PrFileEntry::Changed {
                base_src: None,
                cur_src: None,
                cur_split: _,
            } => {}
        }
    }

    if !flagged_files.is_empty() {
        anyhow::bail!(
            "PR Hygiene & Axiom Gate FAILED on {} files: {:?}",
            flagged_files.len(),
            flagged_files
        );
    }

    let baseline_interface_hash = baseline_ih_hasher.finalize().to_hex().to_string();
    let current_interface_hash = current_ih_hasher.finalize().to_hex().to_string();
    let interface_drift =
        baseline_interface_hash != current_interface_hash || !altered_interface_files.is_empty();

    Ok((
        PrClassification {
            total_files: current_files_count,
            modified_files,
            altered_interface_files,
            interface_drift,
            baseline_interface_hash,
            current_interface_hash,
            unchanged_theorems,
            proof_edited_theorems,
            statement_edited_theorems,
            per_file_interfaces,
        },
        shards_to_verify_by_file,
        changed_current_files,
        changed_current_splits,
    ))
}

pub fn classify_pr_changes(
    toolchain: &str,
    current_files: &std::collections::BTreeMap<String, String>,
    base_files: &std::collections::BTreeMap<String, String>,
) -> Result<(
    PrClassification,
    std::collections::BTreeMap<String, Vec<(String, splitter::TheoremShard, bool)>>,
)> {
    classify_pr_changes_with_store(None, toolchain, current_files, base_files)
}

pub fn classify_pr_changes_with_store(
    store: Option<&TurboStore>,
    toolchain: &str,
    current_files: &std::collections::BTreeMap<String, String>,
    base_files: &std::collections::BTreeMap<String, String>,
) -> Result<(
    PrClassification,
    std::collections::BTreeMap<String, Vec<(String, splitter::TheoremShard, bool)>>,
)> {
    let mut baseline_ih_hasher = blake3::Hasher::new();
    baseline_ih_hasher.update(toolchain.as_bytes());
    let mut current_ih_hasher = blake3::Hasher::new();
    current_ih_hasher.update(toolchain.as_bytes());

    let mut all_paths_set: std::collections::BTreeSet<&String> = current_files.keys().collect();
    all_paths_set.extend(base_files.keys());
    let mut all_paths: Vec<&String> = all_paths_set.into_iter().collect();
    all_paths.sort_by(|a, b| Path::new(a.as_str()).cmp(Path::new(b.as_str())));

    let default_workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);

    // Collect unchanged (rel_path, cur_src) pairs
    let mut unchanged_srcs: Vec<(&str, &str)> = Vec::new();
    for path in &all_paths {
        let rel_path = path.as_str();
        if let (Some(base_src), Some(cur_src)) =
            (base_files.get(rel_path), current_files.get(rel_path))
        {
            if base_src == cur_src {
                unchanged_srcs.push((rel_path, cur_src.as_str()));
            }
        }
    }

    let unchanged_split_keys: Vec<String> = if unchanged_srcs.len() < 8 {
        unchanged_srcs
            .iter()
            .map(|(_, src)| TurboStore::compute_file_split_key(src.as_bytes()))
            .collect()
    } else {
        let workers = default_workers.min(unchanged_srcs.len());
        let next_idx = std::sync::atomic::AtomicUsize::new(0);
        let srcs_ref = &unchanged_srcs;
        let chunks: Vec<Vec<(usize, String)>> = std::thread::scope(|s| {
            let mut handles = Vec::with_capacity(workers);
            for _ in 0..workers {
                let next_ref = &next_idx;
                handles.push(s.spawn(move || {
                    let mut local = Vec::new();
                    loop {
                        let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if i >= srcs_ref.len() {
                            break;
                        }
                        let fk = TurboStore::compute_file_split_key(srcs_ref[i].1.as_bytes());
                        local.push((i, fk));
                    }
                    local
                }));
            }
            handles
                .into_iter()
                .map(|h| h.join().unwrap_or_default())
                .collect()
        });
        let mut indexed: Vec<(usize, String)> = chunks.into_iter().flatten().collect();
        indexed.sort_unstable_by_key(|(i, _)| *i);
        indexed.into_iter().map(|(_, fk)| fk).collect()
    };

    let mut cached_splits = if let Some(st) = store {
        st.batch_get_file_splits(&unchanged_split_keys).unwrap_or_default()
    } else {
        std::collections::HashMap::new()
    };

    // Map rel_path -> file_split_key for unchanged files, and pre-split any cache misses in parallel
    let mut unchanged_key_by_path: std::collections::HashMap<&str, String> =
        std::collections::HashMap::with_capacity(unchanged_srcs.len());
    let mut miss_unchanged: Vec<(usize, &str, &str)> = Vec::new();
    for (idx, &(rel_path, cur_src)) in unchanged_srcs.iter().enumerate() {
        let fk = &unchanged_split_keys[idx];
        unchanged_key_by_path.insert(rel_path, fk.clone());
        if !cached_splits.contains_key(fk) {
            miss_unchanged.push((idx, fk.as_str(), cur_src));
        }
    }

    let mut new_splits_to_cache: Vec<(String, splitter::SplitResult)> =
        Vec::with_capacity(miss_unchanged.len());
    if !miss_unchanged.is_empty() {
        let computed: Vec<(usize, String, splitter::SplitResult)> = if miss_unchanged.len() < 2 {
            miss_unchanged
                .iter()
                .map(|&(idx, fk, src)| (idx, fk.to_string(), split_lean_source(src, &[])))
                .collect()
        } else {
            let workers = default_workers.min(miss_unchanged.len());
            let next_m = std::sync::atomic::AtomicUsize::new(0);
            let miss_ref = &miss_unchanged;
            let chunks: Vec<Vec<(usize, String, splitter::SplitResult)>> = std::thread::scope(|s| {
                let mut handles = Vec::with_capacity(workers);
                for _ in 0..workers {
                    let next_ref = &next_m;
                    handles.push(s.spawn(move || {
                        let mut local = Vec::new();
                        loop {
                            let pos = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            if pos >= miss_ref.len() {
                                break;
                            }
                            let (orig_idx, fk, src) = miss_ref[pos];
                            let sp = split_lean_source(src, &[]);
                            local.push((orig_idx, fk.to_string(), sp));
                        }
                        local
                    }));
                }
                handles
                    .into_iter()
                    .map(|h| h.join().unwrap_or_default())
                    .collect()
            });
            let mut flat: Vec<(usize, String, splitter::SplitResult)> =
                chunks.into_iter().flatten().collect();
            flat.sort_unstable_by_key(|(idx, _, _)| *idx);
            flat
        };

        for (_idx, fk, sp) in computed {
            if store.is_some() {
                new_splits_to_cache.push((fk.clone(), sp.clone()));
            }
            cached_splits.insert(fk, sp);
        }
    }

    let mut modified_files = Vec::new();
    let mut altered_interface_files = Vec::new();
    let mut unchanged_theorems = Vec::new();
    let mut proof_edited_theorems = Vec::new();
    let mut statement_edited_theorems = Vec::new();
    let mut per_file_interfaces = std::collections::BTreeMap::new();
    let mut shards_to_verify_by_file = std::collections::BTreeMap::new();
    let mut flagged_files = Vec::new();

    for path in all_paths {
        let rel_path = (*path).clone();
        match (base_files.get(&rel_path), current_files.get(&rel_path)) {
            (Some(base_src), Some(cur_src)) if base_src == cur_src => {
                let split = if let Some(fk) = unchanged_key_by_path.get(rel_path.as_str()) {
                    cached_splits
                        .remove(fk)
                        .unwrap_or_else(|| split_lean_source(cur_src, &[]))
                } else {
                    split_lean_source(cur_src, &[])
                };
                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), split.interface_hash);
                for s in split.shards {
                    unchanged_theorems.push(format!("{}::{}", rel_path, s.name));
                }
            }
            (Some(base_src), Some(cur_src)) => {
                modified_files.push(rel_path.clone());
                let cur_split = split_lean_source(cur_src, &[]);
                let base_split = split_lean_source(base_src, &[]);
                let reg = cur_split.hygiene.regression_items_against(&base_split.hygiene);
                if !reg.is_empty() {
                    flagged_files.push((rel_path.clone(), reg));
                }

                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(base_split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(cur_split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), cur_split.interface_hash.clone());

                let file_interface_same = cur_split.interface_hash == base_split.interface_hash
                    && cur_split.shards.len() == base_split.shards.len();
                let mut file_has_stmt_change = !file_interface_same;

                let mut base_by_name = std::collections::HashMap::new();
                for bs in &base_split.shards {
                    base_by_name.insert(bs.name.as_str(), (bs, compute_shard_key(toolchain, bs)));
                }
                let cur_names: std::collections::HashSet<&str> =
                    cur_split.shards.iter().map(|s| s.name.as_str()).collect();
                for bs in &base_split.shards {
                    if !cur_names.contains(bs.name.as_str()) {
                        file_has_stmt_change = true;
                        statement_edited_theorems
                            .push(format!("{}::{} (deleted)", rel_path, bs.name));
                    }
                }

                let mut file_verify_list = Vec::new();
                for s in cur_split.shards {
                    let k = compute_shard_key(toolchain, &s);
                    let qualified = format!("{}::{}", rel_path, s.name);
                    if let Some((bs, bk)) = base_by_name.get(s.name.as_str()) {
                        if k == *bk {
                            unchanged_theorems.push(qualified);
                        } else if s.stmt_hash == bs.stmt_hash
                            && s.prefix_env_hash == bs.prefix_env_hash
                            && file_interface_same
                        {
                            proof_edited_theorems.push(qualified);
                            file_verify_list.push((k, s, true));
                        } else {
                            file_has_stmt_change = true;
                            statement_edited_theorems.push(qualified);
                            file_verify_list.push((k, s, false));
                        }
                    } else {
                        file_has_stmt_change = true;
                        statement_edited_theorems.push(qualified);
                        file_verify_list.push((k, s, false));
                    }
                }

                if file_has_stmt_change {
                    altered_interface_files.push(rel_path.clone());
                }
                if !file_verify_list.is_empty() {
                    shards_to_verify_by_file.insert(rel_path, file_verify_list);
                }
            }
            (None, Some(cur_src)) => {
                modified_files.push(rel_path.clone());
                altered_interface_files.push(rel_path.clone());
                let cur_split = split_lean_source(cur_src, &[]);
                if !cur_split.hygiene.is_clean_for_certification() {
                    flagged_files.push((rel_path.clone(), cur_split.hygiene.flagged_items));
                }
                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(cur_split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), cur_split.interface_hash);
                let mut file_verify_list = Vec::new();
                for s in cur_split.shards {
                    let k = compute_shard_key(toolchain, &s);
                    statement_edited_theorems.push(format!("{}::{}", rel_path, s.name));
                    file_verify_list.push((k, s, false));
                }
                if !file_verify_list.is_empty() {
                    shards_to_verify_by_file.insert(rel_path, file_verify_list);
                }
            }
            (Some(base_src), None) => {
                modified_files.push(rel_path.clone());
                altered_interface_files.push(rel_path.clone());
                let base_split = split_lean_source(base_src, &[]);
                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(base_split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                for bs in base_split.shards {
                    statement_edited_theorems
                        .push(format!("{}::{} (deleted)", rel_path, bs.name));
                }
            }
            (None, None) => {}
        }
    }

    if let Some(st) = store {
        if !new_splits_to_cache.is_empty() {
            let refs: Vec<(String, &splitter::SplitResult)> = new_splits_to_cache
                .iter()
                .map(|(h, sp)| (h.clone(), sp))
                .collect();
            let _ = st.batch_put_file_splits(&refs);
        }
    }

    if !flagged_files.is_empty() {
        anyhow::bail!(
            "PR Hygiene & Axiom Gate FAILED on {} files: {:?}",
            flagged_files.len(),
            flagged_files
        );
    }

    let baseline_interface_hash = baseline_ih_hasher.finalize().to_hex().to_string();
    let current_interface_hash = current_ih_hasher.finalize().to_hex().to_string();
    let interface_drift =
        baseline_interface_hash != current_interface_hash || !altered_interface_files.is_empty();

    Ok((
        PrClassification {
            total_files: current_files.len(),
            modified_files,
            altered_interface_files,
            interface_drift,
            baseline_interface_hash,
            current_interface_hash,
            unchanged_theorems,
            proof_edited_theorems,
            statement_edited_theorems,
            per_file_interfaces,
        },
        shards_to_verify_by_file,
    ))
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct VerificationReceipt {
    pub schema_version: u32,
    pub mode: String,
    pub interface_hash: String,
    pub action_key: String,
    pub files_audited: usize,
    pub theorem_shards: usize,
    pub forbidden_constructs_found: usize,
    pub per_file_interfaces: std::collections::BTreeMap<String, String>,
    pub receipt_blake3: String,
}

pub fn compute_receipt_blake3(
    schema_version: u32,
    mode: &str,
    interface_hash: &str,
    action_key: &str,
    files_audited: usize,
    theorem_shards: usize,
    forbidden_constructs_found: usize,
    per_file_interfaces: &std::collections::BTreeMap<String, String>,
) -> String {
    use std::fmt::Write;
    let mut hasher = blake3::Hasher::new();
    let mut header = String::with_capacity(256);
    let _ = writeln!(
        header,
        "turbo-lean-verification-receipt-v1\nschema_version:{}\nmode:{}\ninterface_hash:{}\naction_key:{}\nfiles_audited:{}\ntheorem_shards:{}\nforbidden_constructs_found:{}",
        schema_version,
        mode,
        interface_hash,
        action_key,
        files_audited,
        theorem_shards,
        forbidden_constructs_found
    );
    hasher.update(header.as_bytes());
    for (rel_path, file_ih) in per_file_interfaces {
        hasher.update(b"file:");
        hasher.update(rel_path.as_bytes());
        hasher.update(b"=");
        hasher.update(file_ih.as_bytes());
        hasher.update(b"\n");
    }
    hasher.finalize().to_hex().to_string()
}

pub fn build_verification_receipt(
    mode: &str,
    interface_hash: &str,
    action_key: &str,
    files_audited: usize,
    theorem_shards: usize,
    forbidden_constructs_found: usize,
    per_file_interfaces: std::collections::BTreeMap<String, String>,
) -> VerificationReceipt {
    let schema_version = 1u32;
    let receipt_blake3 = compute_receipt_blake3(
        schema_version,
        mode,
        interface_hash,
        action_key,
        files_audited,
        theorem_shards,
        forbidden_constructs_found,
        &per_file_interfaces,
    );
    VerificationReceipt {
        schema_version,
        mode: mode.to_string(),
        interface_hash: interface_hash.to_string(),
        action_key: action_key.to_string(),
        files_audited,
        theorem_shards,
        forbidden_constructs_found,
        per_file_interfaces,
        receipt_blake3,
    }
}

pub fn verify_receipt_data(
    receipt: &VerificationReceipt,
    expected_interface_hash: Option<&str>,
    baseline: Option<&VerificationReceipt>,
) -> Result<Vec<String>> {
    if receipt.schema_version != 1 {
        anyhow::bail!(
            "Unsupported receipt schema_version {} (expected 1)",
            receipt.schema_version
        );
    }
    let expected_blake3 = compute_receipt_blake3(
        receipt.schema_version,
        &receipt.mode,
        &receipt.interface_hash,
        &receipt.action_key,
        receipt.files_audited,
        receipt.theorem_shards,
        receipt.forbidden_constructs_found,
        &receipt.per_file_interfaces,
    );
    if receipt.receipt_blake3 != expected_blake3 {
        anyhow::bail!(
            "Cryptographic receipt BLAKE3 integrity check FAILED: expected {}, got {}",
            expected_blake3,
            receipt.receipt_blake3
        );
    }
    if receipt.forbidden_constructs_found != 0 {
        anyhow::bail!(
            "Receipt certification gate FAILED: forbidden_constructs_found = {} (must be 0)",
            receipt.forbidden_constructs_found
        );
    }
    if let Some(exp_ih) = expected_interface_hash {
        if receipt.interface_hash != exp_ih {
            anyhow::bail!(
                "Project InterfaceHash mismatch: expected {}, got {}",
                exp_ih,
                receipt.interface_hash
            );
        }
    }
    let mut altered_files = Vec::new();
    if let Some(base) = baseline {
        let base_blake3 = compute_receipt_blake3(
            base.schema_version,
            &base.mode,
            &base.interface_hash,
            &base.action_key,
            base.files_audited,
            base.theorem_shards,
            base.forbidden_constructs_found,
            &base.per_file_interfaces,
        );
        if base.receipt_blake3 != base_blake3 {
            anyhow::bail!(
                "Baseline receipt BLAKE3 integrity check FAILED: expected {}, got {}",
                base_blake3,
                base.receipt_blake3
            );
        }
        let mut all_paths: std::collections::BTreeSet<&String> =
            receipt.per_file_interfaces.keys().collect();
        all_paths.extend(base.per_file_interfaces.keys());
        for path in all_paths {
            match (
                base.per_file_interfaces.get(path),
                receipt.per_file_interfaces.get(path),
            ) {
                (Some(b_ih), Some(r_ih)) if b_ih == r_ih => {}
                _ => altered_files.push(path.clone()),
            }
        }
        if !altered_files.is_empty() || receipt.interface_hash != base.interface_hash {
            anyhow::bail!(
                "Theorem interface drift detected against baseline receipt (altered files: {:?}, baseline interface_hash={}, current interface_hash={})",
                altered_files,
                base.interface_hash,
                receipt.interface_hash
            );
        }
    }
    Ok(altered_files)
}
