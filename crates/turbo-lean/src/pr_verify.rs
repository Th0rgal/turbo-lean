//! Git tree-aware incremental PR verification (`git-head-tree:v5:`), prefix-pread splitting,
//! BLAKE3 cryptographic verification receipts, and CI / PR command handlers.

use crate::db::{SingleflightOutcome, TurboStore};
use crate::lake_build::{
    are_all_project_oleans_up_to_date, compute_shard_key, detect_toolchain, lean_bin_from_env,
    load_and_split_files_cached, load_and_split_files_with_hashes_cached,
    load_project_stat_summary_cached, resolve_lake_env, resolve_or_share_lake_env,
    resolve_prebuilt_module_import, resolve_remote_lean_path, seed_project_theorem_shards,
    seed_project_theorem_shards_from_splits, stage_lake_build_outputs,
};
use crate::pack;
use crate::splitter::{self, split_lean_source, split_lean_source_fast_no_cone};
use anyhow::{Context, Result};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

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
    h.update(suffix);
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
    let mut buf = fs::read(path).ok()?;
    if buf.len() != total_len {
        return None;
    }
    if compute_suffix_fast_fingerprint(&buf[cur_prefix_len..]) != base_entry.suffix_blake3 {
        return None;
    }
    buf.truncate(cur_prefix_len);
    String::from_utf8(buf).ok()
}

fn git_head_tree_cache_paths(
    store: &TurboStore,
    repo_root: &Path,
    canon_dir: &Path,
    sha: &str,
    toolchain: &str,
) -> (PathBuf, PathBuf) {
    let mut h = blake3::Hasher::new();
    h.update(b"git-head-tree:v7:");
    h.update(repo_root.to_string_lossy().as_bytes());
    h.update(b":");
    h.update(canon_dir.to_string_lossy().as_bytes());
    h.update(b":");
    h.update(sha.as_bytes());
    h.update(b":");
    h.update(toolchain.as_bytes());
    let key_hex = h.finalize().to_hex();
    let short_key = &key_hex[..24];
    let staging = store.fast_staging_dir();
    (
        staging.join(format!("git_head_tree_v7_{}.json", short_key)),
        staging.join(format!("git_head_tree_stats_v7_{}.json", short_key)),
    )
}

trait BaseShardRef {
    fn name(&self) -> &str;
    fn stmt_hash(&self) -> &str;
    fn prefix_env_hash(&self) -> &str;
    fn proof_hash(&self) -> &str;
    fn shard_key(&self, toolchain: &str) -> std::borrow::Cow<'_, str>;
}

impl BaseShardRef for CachedBaseShard {
    fn name(&self) -> &str {
        &self.name
    }
    fn stmt_hash(&self) -> &str {
        &self.stmt_hash
    }
    fn prefix_env_hash(&self) -> &str {
        &self.prefix_env_hash
    }
    fn proof_hash(&self) -> &str {
        &self.proof_hash
    }
    fn shard_key(&self, _toolchain: &str) -> std::borrow::Cow<'_, str> {
        std::borrow::Cow::Borrowed(&self.shard_key)
    }
}

impl BaseShardRef for splitter::TheoremShard {
    fn name(&self) -> &str {
        &self.name
    }
    fn stmt_hash(&self) -> &str {
        &self.stmt_hash
    }
    fn prefix_env_hash(&self) -> &str {
        &self.prefix_env_hash
    }
    fn proof_hash(&self) -> &str {
        &self.proof_hash
    }
    fn shard_key(&self, toolchain: &str) -> std::borrow::Cow<'_, str> {
        std::borrow::Cow::Owned(compute_shard_key(toolchain, self))
    }
}

struct PrClassificationAccum {
    toolchain: String,
    total_files: usize,
    baseline_ih_hasher: blake3::Hasher,
    current_ih_hasher: blake3::Hasher,
    modified_files: Vec<String>,
    altered_interface_files: Vec<String>,
    unchanged_theorems: Vec<String>,
    proof_edited_theorems: Vec<String>,
    statement_edited_theorems: Vec<String>,
    per_file_interfaces: std::collections::BTreeMap<String, String>,
    shards_to_verify_by_file:
        std::collections::BTreeMap<String, Vec<(String, splitter::TheoremShard, bool)>>,
    flagged_files: Vec<(String, Vec<String>)>,
}

impl PrClassificationAccum {
    fn new(toolchain: &str, total_files: usize) -> Self {
        let mut baseline_ih_hasher = blake3::Hasher::new();
        baseline_ih_hasher.update(toolchain.as_bytes());
        let mut current_ih_hasher = blake3::Hasher::new();
        current_ih_hasher.update(toolchain.as_bytes());
        Self {
            toolchain: toolchain.to_string(),
            total_files,
            baseline_ih_hasher,
            current_ih_hasher,
            modified_files: Vec::new(),
            altered_interface_files: Vec::new(),
            unchanged_theorems: Vec::new(),
            proof_edited_theorems: Vec::new(),
            statement_edited_theorems: Vec::new(),
            per_file_interfaces: std::collections::BTreeMap::new(),
            shards_to_verify_by_file: std::collections::BTreeMap::new(),
            flagged_files: Vec::new(),
        }
    }

    fn record_unchanged<S: BaseShardRef>(
        &mut self,
        rel_path: String,
        interface_hash: String,
        shards: &[S],
    ) {
        self.baseline_ih_hasher.update(rel_path.as_bytes());
        self.baseline_ih_hasher.update(b":");
        self.baseline_ih_hasher.update(interface_hash.as_bytes());
        self.baseline_ih_hasher.update(b"\n");

        self.current_ih_hasher.update(rel_path.as_bytes());
        self.current_ih_hasher.update(b":");
        self.current_ih_hasher.update(interface_hash.as_bytes());
        self.current_ih_hasher.update(b"\n");

        self.per_file_interfaces
            .insert(rel_path.clone(), interface_hash);
        for s in shards {
            self.unchanged_theorems
                .push(format!("{}::{}", rel_path, s.name()));
        }
    }

    fn record_modified<S: BaseShardRef>(
        &mut self,
        rel_path: String,
        base_interface_hash: &str,
        base_hygiene: &splitter::HygieneReport,
        base_shards: &[S],
        cur_split: splitter::SplitResult,
    ) {
        self.modified_files.push(rel_path.clone());
        let reg = cur_split.hygiene.regression_items_against(base_hygiene);
        if !reg.is_empty() {
            self.flagged_files.push((rel_path.clone(), reg));
        }

        self.baseline_ih_hasher.update(rel_path.as_bytes());
        self.baseline_ih_hasher.update(b":");
        self.baseline_ih_hasher
            .update(base_interface_hash.as_bytes());
        self.baseline_ih_hasher.update(b"\n");

        self.current_ih_hasher.update(rel_path.as_bytes());
        self.current_ih_hasher.update(b":");
        self.current_ih_hasher
            .update(cur_split.interface_hash.as_bytes());
        self.current_ih_hasher.update(b"\n");

        self.per_file_interfaces
            .insert(rel_path.clone(), cur_split.interface_hash.clone());

        let file_interface_same = cur_split.interface_hash == base_interface_hash
            && cur_split.shards.len() == base_shards.len();
        let mut file_has_stmt_change = !file_interface_same;

        let mut base_by_name = std::collections::HashMap::with_capacity(base_shards.len());
        for bs in base_shards {
            base_by_name.insert(bs.name(), bs);
        }
        let cur_names: std::collections::HashSet<&str> =
            cur_split.shards.iter().map(|s| s.name.as_str()).collect();
        for bs in base_shards {
            if !cur_names.contains(bs.name()) {
                file_has_stmt_change = true;
                self.statement_edited_theorems.push(format!(
                    "{}::{} (deleted)",
                    rel_path,
                    bs.name()
                ));
            }
        }

        let mut file_verify_list = Vec::new();
        for s in cur_split.shards {
            let qualified = format!("{}::{}", rel_path, s.name);
            if let Some(bs) = base_by_name.get(s.name.as_str()) {
                if !bs.proof_hash().is_empty()
                    && s.proof_hash == bs.proof_hash()
                    && s.stmt_hash == bs.stmt_hash()
                    && s.prefix_env_hash == bs.prefix_env_hash()
                {
                    self.unchanged_theorems.push(qualified);
                    continue;
                }
                let k = compute_shard_key(&self.toolchain, &s);
                if k == bs.shard_key(&self.toolchain).as_ref() {
                    self.unchanged_theorems.push(qualified);
                } else if s.stmt_hash == bs.stmt_hash()
                    && s.prefix_env_hash == bs.prefix_env_hash()
                    && file_interface_same
                {
                    self.proof_edited_theorems.push(qualified);
                    file_verify_list.push((k, s, true));
                } else {
                    file_has_stmt_change = true;
                    self.statement_edited_theorems.push(qualified);
                    file_verify_list.push((k, s, false));
                }
            } else {
                let k = compute_shard_key(&self.toolchain, &s);
                file_has_stmt_change = true;
                self.statement_edited_theorems.push(qualified);
                file_verify_list.push((k, s, false));
            }
        }

        if file_has_stmt_change {
            self.altered_interface_files.push(rel_path.clone());
        }
        if !file_verify_list.is_empty() {
            self.shards_to_verify_by_file
                .insert(rel_path, file_verify_list);
        }
    }

    fn record_added(&mut self, rel_path: String, cur_split: splitter::SplitResult) {
        self.modified_files.push(rel_path.clone());
        self.altered_interface_files.push(rel_path.clone());
        if !cur_split.hygiene.is_clean_for_certification() {
            self.flagged_files
                .push((rel_path.clone(), cur_split.hygiene.flagged_items));
        }
        self.current_ih_hasher.update(rel_path.as_bytes());
        self.current_ih_hasher.update(b":");
        self.current_ih_hasher
            .update(cur_split.interface_hash.as_bytes());
        self.current_ih_hasher.update(b"\n");

        self.per_file_interfaces
            .insert(rel_path.clone(), cur_split.interface_hash);
        let mut file_verify_list = Vec::new();
        for s in cur_split.shards {
            let k = compute_shard_key(&self.toolchain, &s);
            self.statement_edited_theorems
                .push(format!("{}::{}", rel_path, s.name));
            file_verify_list.push((k, s, false));
        }
        if !file_verify_list.is_empty() {
            self.shards_to_verify_by_file
                .insert(rel_path, file_verify_list);
        }
    }

    fn record_deleted<S: BaseShardRef>(
        &mut self,
        rel_path: String,
        base_interface_hash: &str,
        base_shards: &[S],
    ) {
        self.modified_files.push(rel_path.clone());
        self.altered_interface_files.push(rel_path.clone());
        self.baseline_ih_hasher.update(rel_path.as_bytes());
        self.baseline_ih_hasher.update(b":");
        self.baseline_ih_hasher
            .update(base_interface_hash.as_bytes());
        self.baseline_ih_hasher.update(b"\n");

        for bs in base_shards {
            self.statement_edited_theorems
                .push(format!("{}::{} (deleted)", rel_path, bs.name()));
        }
    }

    fn finish(
        self,
    ) -> Result<(
        PrClassification,
        std::collections::BTreeMap<String, Vec<(String, splitter::TheoremShard, bool)>>,
    )> {
        if !self.flagged_files.is_empty() {
            anyhow::bail!(
                "PR Hygiene & Axiom Gate FAILED on {} files: {:?}",
                self.flagged_files.len(),
                self.flagged_files
            );
        }

        let baseline_interface_hash = self.baseline_ih_hasher.finalize().to_hex().to_string();
        let current_interface_hash = self.current_ih_hasher.finalize().to_hex().to_string();
        let interface_drift = baseline_interface_hash != current_interface_hash
            || !self.altered_interface_files.is_empty();

        Ok((
            PrClassification {
                total_files: self.total_files,
                modified_files: self.modified_files,
                altered_interface_files: self.altered_interface_files,
                interface_drift,
                baseline_interface_hash,
                current_interface_hash,
                unchanged_theorems: self.unchanged_theorems,
                proof_edited_theorems: self.proof_edited_theorems,
                statement_edited_theorems: self.statement_edited_theorems,
                per_file_interfaces: self.per_file_interfaces,
            },
            self.shards_to_verify_by_file,
        ))
    }
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

    if src_len > 2_048 && !sp.shards.is_empty() {
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
            if p_len > 0 && p_len + 1024 < src_len {
                let prefix_slice = &base_src[..p_len];
                let suffix_slice = &base_src[p_len..];
                let prefix_sp = split_lean_source_fast_no_cone(prefix_slice, &[]);
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

pub(crate) fn is_unchanged_against_head_entry(
    cur_src: &str,
    base_entry: &CachedHeadFileEntry,
) -> bool {
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

pub(crate) fn rel_path_from_dir(path: &Path, canon_dir: &Path) -> String {
    path.strip_prefix(canon_dir)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

pub(crate) fn join_proj_prefix(proj_prefix: &str, rel_path: &str) -> String {
    if proj_prefix.is_empty() {
        rel_path.to_string()
    } else {
        format!("{}/{}", proj_prefix.trim_end_matches('/'), rel_path)
    }
}

pub(crate) fn update_entry_stat_if_changed(entry: &mut CachedHeadFileEntry, path: &Path) -> bool {
    if let Some((m_sec, m_nsec, s_sz)) = stable_file_stat_for_head(path) {
        if entry.head_mtime_sec != m_sec
            || entry.head_mtime_nsec != m_nsec
            || entry.head_size_bytes != s_sz
        {
            entry.head_mtime_sec = m_sec;
            entry.head_mtime_nsec = m_nsec;
            entry.head_size_bytes = s_sz;
            return true;
        }
    }
    false
}

fn load_cached_head_entry(
    store: &TurboStore,
    canon_dir: &Path,
    canon_file: &Path,
    toolchain: &str,
) -> Option<CachedHeadFileEntry> {
    let repo_root = resolve_git_toplevel(canon_dir).ok()?;
    let sha = resolve_git_head_sha(&repo_root, "HEAD")?;
    let (cache_file, _) = git_head_tree_cache_paths(store, &repo_root, canon_dir, &sha, toolchain);
    let bytes = fs::read(&cache_file).ok()?;
    let mut cached_map =
        serde_json::from_slice::<std::collections::HashMap<String, CachedHeadFileEntry>>(&bytes)
            .ok()?;
    cached_map.remove(&rel_path_from_dir(canon_file, canon_dir))
}

fn try_split_prefix_against_base(
    prefix_src: &str,
    base_entry: &CachedHeadFileEntry,
) -> Option<splitter::SplitResult> {
    let mut prefix_sp = split_lean_source_fast_no_cone(prefix_src, &[]);
    if prefix_sp.interface_hash == base_entry.prefix_interface_hash
        && prefix_sp.shards.len() == base_entry.shards.len()
        && prefix_sp.hygiene.is_clean_for_certification()
    {
        prefix_sp.interface_hash = base_entry.interface_hash.clone();
        Some(prefix_sp)
    } else {
        None
    }
}

fn try_extract_and_split_prefix(
    src: &str,
    base_entry: &CachedHeadFileEntry,
) -> Option<(splitter::SplitResult, usize)> {
    if base_entry.prefix_byte_len < base_entry.src_len && !base_entry.suffix_blake3.is_empty() {
        let suffix_len = base_entry.src_len - base_entry.prefix_byte_len;
        if src.len() > suffix_len && src.is_char_boundary(src.len() - suffix_len) {
            let cur_prefix_len = src.len() - suffix_len;
            if compute_suffix_fast_fingerprint(&src.as_bytes()[cur_prefix_len..])
                == base_entry.suffix_blake3
            {
                if let Some(prefix_sp) =
                    try_split_prefix_against_base(&src[..cur_prefix_len], base_entry)
                {
                    return Some((prefix_sp, cur_prefix_len));
                }
            }
        }
    }
    None
}

pub(crate) fn split_modified_against_head_entry(
    cur_src: &str,
    base_entry: &CachedHeadFileEntry,
) -> (splitter::SplitResult, Option<usize>) {
    if let Some((prefix_sp, cur_prefix_len)) = try_extract_and_split_prefix(cur_src, base_entry) {
        return (prefix_sp, Some(cur_prefix_len));
    }
    (split_lean_source_fast_no_cone(cur_src, &[]), None)
}

pub(crate) fn try_fast_split_single_file_from_path(
    store: &TurboStore,
    canon_dir: &Path,
    canon_file: &Path,
    f_sz: i64,
    toolchain: &str,
) -> Option<(String, splitter::SplitResult, usize)> {
    let base_entry = load_cached_head_entry(store, canon_dir, canon_file, toolchain)?;
    let prefix_src = try_read_prefix_if_suffix_matches(canon_file, f_sz, &base_entry)?;
    let prefix_sp = try_split_prefix_against_base(&prefix_src, &base_entry)?;
    let unchanged =
        prefix_src.len() == base_entry.prefix_byte_len && prefix_src == base_entry.prefix_src;
    Some((prefix_src, prefix_sp, usize::from(unchanged)))
}

pub(crate) fn try_fast_split_single_file(
    store: &TurboStore,
    canon_dir: &Path,
    canon_file: &Path,
    src: &str,
    toolchain: &str,
) -> Option<(splitter::SplitResult, usize, usize)> {
    let base_entry = load_cached_head_entry(store, canon_dir, canon_file, toolchain)?;
    let (prefix_sp, cur_prefix_len) = try_extract_and_split_prefix(src, &base_entry)?;
    let unchanged =
        cur_prefix_len == base_entry.prefix_byte_len && src.starts_with(&base_entry.prefix_src);
    Some((prefix_sp, usize::from(unchanged), cur_prefix_len))
}

fn write_head_tree_stats_cache(
    stats_file: &Path,
    head_tree_map: &std::collections::HashMap<String, CachedHeadFileEntry>,
) {
    let stat_map: std::collections::HashMap<String, (i64, i64, i64)> = head_tree_map
        .iter()
        .map(|(k, e)| {
            (
                k.clone(),
                (e.head_mtime_sec, e.head_mtime_nsec, e.head_size_bytes),
            )
        })
        .collect();
    if let Ok(stat_bytes) = serde_json::to_vec(&stat_map) {
        let _ = crate::shm_cache::atomic_write_shm(stats_file, &stat_bytes);
    }
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
    let (cache_file, stats_file) =
        git_head_tree_cache_paths(store, &repo_root, canon_dir, &sha, toolchain);
    if cache_file.exists() {
        if let Ok(stat_bytes) = fs::read(&stats_file) {
            if let Ok(stat_map) = serde_json::from_slice::<
                std::collections::HashMap<String, (i64, i64, i64)>,
            >(&stat_bytes)
            {
                if stat_map.len() == lean_paths.len()
                    && lean_paths.iter().all(|p| {
                        let rel = rel_path_from_dir(p, canon_dir);
                        match (stat_map.get(&rel), file_stat_tuple(p)) {
                            (Some(&(hs_sec, hs_nsec, hs_sz)), Some((m_sec, m_nsec, f_sz))) => {
                                hs_sz > 0 && hs_sec == m_sec && hs_nsec == m_nsec && hs_sz == f_sz
                            }
                            _ => false,
                        }
                    })
                {
                    return;
                }
            }
        }
        if let Ok(bytes) = fs::read(&cache_file) {
            if let Ok(mut head_tree_map) = serde_json::from_slice::<
                std::collections::HashMap<String, CachedHeadFileEntry>,
            >(&bytes)
            {
                let mut updated = false;
                for p in lean_paths {
                    let rel = rel_path_from_dir(p, canon_dir);
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
                                if is_unchanged && update_entry_stat_if_changed(entry, p) {
                                    updated = true;
                                }
                            }
                        }
                    }
                }
                if updated {
                    if let Ok(json_bytes) = serde_json::to_vec(&head_tree_map) {
                        let _ = crate::shm_cache::atomic_write_shm(&cache_file, &json_bytes);
                    }
                }
                write_head_tree_stats_cache(&stats_file, &head_tree_map);
            }
        }
        return;
    }
    let proj_prefix = rel_path_from_dir(canon_dir, &repo_root);
    let all_lean_repo_rels: Vec<String> = lean_paths
        .iter()
        .map(|p| join_proj_prefix(&proj_prefix, &rel_path_from_dir(p, canon_dir)))
        .collect();
    if let Ok(fetched_blobs) = fetch_git_blobs_batch(&repo_root, "HEAD", &all_lean_repo_rels) {
        if fetched_blobs.len() == lean_paths.len() {
            let fallback_splits = if precomputed_splits.is_none() {
                load_and_split_files_cached(store, lean_paths)
                    .ok()
                    .map(|(s, _)| s)
            } else {
                None
            };
            let mut split_by_path = std::collections::HashMap::new();
            if let Some(splits) = precomputed_splits.or(fallback_splits.as_deref()) {
                for (p, s, sp) in splits {
                    split_by_path.insert(p.as_path(), (s.as_str(), sp));
                }
            }
            let entries: Vec<(String, CachedHeadFileEntry)> = std::thread::scope(|s| {
                let handles: Vec<_> = lean_paths
                    .iter()
                    .map(|p| {
                        let split_by_path_ref = &split_by_path;
                        let fetched_ref = &fetched_blobs;
                        let proj_prefix_ref = &proj_prefix;
                        s.spawn(move || -> Option<(String, CachedHeadFileEntry)> {
                            let rel = rel_path_from_dir(p, canon_dir);
                            let repo_rel = join_proj_prefix(proj_prefix_ref, &rel);
                            let bs = fetched_ref.get(&repo_rel)?;
                            let (sp, matches_worktree): (
                                std::borrow::Cow<'_, splitter::SplitResult>,
                                bool,
                            ) = if let Some((cur_src, sp)) = split_by_path_ref.get(p.as_path()) {
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
                                (
                                    std::borrow::Cow::Owned(split_lean_source(bs, &[])),
                                    wt_matches,
                                )
                            };
                            let head_stat = if matches_worktree {
                                stable_file_stat_for_head(p)
                            } else {
                                None
                            };
                            Some((
                                rel,
                                build_cached_head_file_entry(bs, &sp, toolchain, head_stat),
                            ))
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .filter_map(|h| h.join().ok().flatten())
                    .collect()
            });
            let rel_blob_map: std::collections::HashMap<String, CachedHeadFileEntry> =
                entries.into_iter().collect();
            if rel_blob_map.len() == lean_paths.len() {
                if let Ok(json_bytes) = serde_json::to_vec(&rel_blob_map) {
                    let _ = crate::shm_cache::atomic_write_shm(&cache_file, &json_bytes);
                }
                write_head_tree_stats_cache(&stats_file, &rel_blob_map);
            }
        }
    }
}

#[allow(dead_code)]
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
    load_and_classify_pr_from_git_scoped(store, canon_dir, base_ref, toolchain, None)
}

pub(crate) fn load_and_classify_pr_from_git_scoped(
    store: &TurboStore,
    canon_dir: &Path,
    base_ref: &str,
    toolchain: &str,
    scope: Option<&Path>,
) -> Result<(
    PrClassification,
    std::collections::BTreeMap<String, Vec<(String, splitter::TheoremShard, bool)>>,
    std::collections::BTreeMap<String, String>,
    std::collections::BTreeMap<String, splitter::SplitResult>,
)> {
    let repo_root = resolve_git_toplevel(canon_dir)?;
    let proj_prefix = rel_path_from_dir(canon_dir, &repo_root);

    let lean_paths = crate::lake_build::collect_project_lean_files(canon_dir, true, scope);

    enum PrFileEntry {
        Unchanged(splitter::SplitResult),
        Changed {
            base_src: Option<String>,
            cur_src: Option<String>,
            cur_split: Option<splitter::SplitResult>,
        },
    }

    let head_sha_opt = resolve_git_head_sha(&repo_root, base_ref);
    let head_tree_cache_file = head_sha_opt
        .as_ref()
        .map(|sha| git_head_tree_cache_paths(store, &repo_root, canon_dir, sha, toolchain).0);

    let mut entries_by_rel_path: std::collections::HashMap<String, PrFileEntry> =
        std::collections::HashMap::with_capacity(lean_paths.len());
    let mut changed_current_files = std::collections::BTreeMap::new();
    let mut changed_current_splits = std::collections::BTreeMap::new();
    let mut current_files_count = 0usize;

    if let Some(ref cache_file) = head_tree_cache_file {
        let stats_file_opt = head_sha_opt
            .as_ref()
            .map(|sha| git_head_tree_cache_paths(store, &repo_root, canon_dir, sha, toolchain).1);
        let prechecked_stats = stats_file_opt
            .as_ref()
            .and_then(|sf| fs::read(sf).ok())
            .and_then(|sb| {
                serde_json::from_slice::<std::collections::HashMap<String, (i64, i64, i64)>>(&sb)
                    .ok()
            });
        if let Ok(bytes) = fs::read(cache_file) {
            if let Ok(mut head_tree_map) = serde_json::from_slice::<
                std::collections::HashMap<String, CachedHeadFileEntry>,
            >(&bytes)
            {
                let all_known = lean_paths.len() == head_tree_map.len()
                    && lean_paths
                        .iter()
                        .all(|p| head_tree_map.contains_key(&rel_path_from_dir(p, canon_dir)));
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
                        let rel_path = rel_path_from_dir(path, canon_dir);
                        if let Some(mut base_entry) = head_tree_map.remove(&rel_path) {
                            if let Some(ref sm) = prechecked_stats {
                                if let Some(&(hs_sec, hs_nsec, hs_sz)) = sm.get(&rel_path) {
                                    if hs_sz > 0 {
                                        base_entry.head_mtime_sec = hs_sec;
                                        base_entry.head_mtime_nsec = hs_nsec;
                                        base_entry.head_size_bytes = hs_sz;
                                    }
                                }
                            }
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

                    let evaluate_stat_missed = |(path, rel_path, mut base_entry, f_sz): (
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
                                let stat_updated =
                                    update_entry_stat_if_changed(&mut base_entry, &path);
                                return StatMissedOutcome::Unchanged {
                                    rel_path,
                                    base_entry,
                                    stat_updated,
                                };
                            }
                            if let Some(prefix_sp) =
                                try_split_prefix_against_base(&prefix_only, &base_entry)
                            {
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
                            let stat_updated = update_entry_stat_if_changed(&mut base_entry, &path);
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

                    let outcomes: Vec<StatMissedOutcome> = if stat_missed.len() >= 2 {
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
                        stat_missed.into_iter().map(evaluate_stat_missed).collect()
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
                        let mut stat_map: std::collections::HashMap<String, (i64, i64, i64)> =
                            unchanged_map
                                .iter()
                                .map(|(k, e)| {
                                    (
                                        k.clone(),
                                        (e.head_mtime_sec, e.head_mtime_nsec, e.head_size_bytes),
                                    )
                                })
                                .collect();
                        for (rel_path, base_entry, _) in &split_modified {
                            stat_map.insert(
                                rel_path.clone(),
                                (
                                    base_entry.head_mtime_sec,
                                    base_entry.head_mtime_nsec,
                                    base_entry.head_size_bytes,
                                ),
                            );
                        }
                        if let Some(ref sf) = stats_file_opt {
                            if let Ok(stat_bytes) = serde_json::to_vec(&stat_map) {
                                let _ = crate::shm_cache::atomic_write_shm(sf, &stat_bytes);
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

                    let mut accum = PrClassificationAccum::new(toolchain, lean_paths.len());
                    for rel_path in all_paths {
                        let Some(entry) = fast_entries.remove(&rel_path) else {
                            continue;
                        };
                        match entry {
                            FastCachedFile::Unchanged(base_entry) => {
                                accum.record_unchanged(
                                    rel_path,
                                    base_entry.interface_hash,
                                    &base_entry.shards,
                                );
                            }
                            FastCachedFile::Modified {
                                base_entry,
                                cur_split,
                            } => {
                                changed_current_splits.insert(rel_path.clone(), cur_split.clone());
                                accum.record_modified(
                                    rel_path,
                                    &base_entry.interface_hash,
                                    &base_entry.hygiene,
                                    &base_entry.shards,
                                    cur_split,
                                );
                            }
                        }
                    }

                    let (cls, shards_to_verify_by_file) = accum.finish()?;
                    return Ok((
                        cls,
                        shards_to_verify_by_file,
                        changed_current_files,
                        changed_current_splits,
                    ));
                }
            }
        }
    }

    let mut changed_repo_paths: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    let mut untracked_repo_paths: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    let mut prefetched_blobs: Option<std::collections::HashMap<String, String>> = None;

    let all_lean_repo_rels: Vec<String> = lean_paths
        .iter()
        .map(|p| join_proj_prefix(&proj_prefix, &rel_path_from_dir(p, canon_dir)))
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
        let rel_path = rel_path_from_dir(&path, canon_dir);
        let repo_rel = join_proj_prefix(&proj_prefix, &rel_path);

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
        };
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
                let rel = rel_path_from_dir(p, canon_dir);
                let repo_rel = join_proj_prefix(&proj_prefix, &rel);
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
                    let _ = crate::shm_cache::atomic_write_shm(cache_file, &json_bytes);
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

    let mut accum = PrClassificationAccum::new(toolchain, current_files_count);
    for rel_path in all_paths {
        let Some(entry) = entries_by_rel_path.remove(&rel_path) else {
            continue;
        };
        match entry {
            PrFileEntry::Unchanged(split) => {
                accum.record_unchanged(rel_path, split.interface_hash, &split.shards);
            }
            PrFileEntry::Changed {
                base_src: Some(base_src),
                cur_src: Some(cur_src),
                cur_split,
            } if base_src == cur_src => {
                let split = cur_split.unwrap_or_else(|| resolve_cached_or_split(&cur_src));
                accum.record_unchanged(rel_path, split.interface_hash, &split.shards);
            }
            PrFileEntry::Changed {
                base_src: Some(base_src),
                cur_src: Some(cur_src),
                cur_split,
            } => {
                let cur_split = cur_split.unwrap_or_else(|| resolve_cached_or_split(&cur_src));
                changed_current_splits.insert(rel_path.clone(), cur_split.clone());
                let base_split = resolve_cached_or_split(&base_src);
                accum.record_modified(
                    rel_path,
                    &base_split.interface_hash,
                    &base_split.hygiene,
                    &base_split.shards,
                    cur_split,
                );
            }
            PrFileEntry::Changed {
                base_src: None,
                cur_src: Some(cur_src),
                cur_split,
            } => {
                let cur_split = cur_split.unwrap_or_else(|| resolve_cached_or_split(&cur_src));
                changed_current_splits.insert(rel_path.clone(), cur_split.clone());
                accum.record_added(rel_path, cur_split);
            }
            PrFileEntry::Changed {
                base_src: Some(base_src),
                cur_src: None,
                cur_split: _,
            } => {
                let base_split = resolve_cached_or_split(&base_src);
                accum.record_deleted(rel_path, &base_split.interface_hash, &base_split.shards);
            }
            PrFileEntry::Changed {
                base_src: None,
                cur_src: None,
                cur_split: _,
            } => {}
        }
    }

    let (cls, shards_to_verify_by_file) = accum.finish()?;
    Ok((
        cls,
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
    let mut all_paths_set: std::collections::BTreeSet<&String> = current_files.keys().collect();
    all_paths_set.extend(base_files.keys());
    let mut all_paths: Vec<&String> = all_paths_set.into_iter().collect();
    all_paths.sort_by(|a, b| Path::new(a.as_str()).cmp(Path::new(b.as_str())));

    let par_map_indexed = |len: usize, threshold: usize, f: &(dyn Fn(usize) + Send + Sync)| {
        if len < threshold {
            for i in 0..len {
                f(i);
            }
            return;
        }
        let workers = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .min(len);
        let next_idx = std::sync::atomic::AtomicUsize::new(0);
        std::thread::scope(|s| {
            for _ in 0..workers {
                let next_ref = &next_idx;
                s.spawn(move || loop {
                    let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if i >= len {
                        break;
                    }
                    f(i);
                });
            }
        });
    };

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

    let split_key_slots: Vec<std::sync::Mutex<String>> = (0..unchanged_srcs.len())
        .map(|_| std::sync::Mutex::new(String::new()))
        .collect();
    par_map_indexed(unchanged_srcs.len(), 8, &|i| {
        let fk = TurboStore::compute_file_split_key(unchanged_srcs[i].1.as_bytes());
        *split_key_slots[i].lock().unwrap() = fk;
    });
    let unchanged_split_keys: Vec<String> = split_key_slots
        .into_iter()
        .map(|m| m.into_inner().unwrap_or_default())
        .collect();

    let mut cached_splits = if let Some(st) = store {
        st.batch_get_file_splits(&unchanged_split_keys)
            .unwrap_or_default()
    } else {
        std::collections::HashMap::new()
    };

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
        let computed_slots: Vec<std::sync::Mutex<Option<(String, splitter::SplitResult)>>> = (0
            ..miss_unchanged.len())
            .map(|_| std::sync::Mutex::new(None))
            .collect();
        par_map_indexed(miss_unchanged.len(), 2, &|pos| {
            let (_orig_idx, fk, src) = miss_unchanged[pos];
            *computed_slots[pos].lock().unwrap() =
                Some((fk.to_string(), split_lean_source(src, &[])));
        });
        for slot in computed_slots {
            if let Some((fk, sp)) = slot.into_inner().unwrap_or(None) {
                if store.is_some() {
                    new_splits_to_cache.push((fk.clone(), sp.clone()));
                }
                cached_splits.insert(fk, sp);
            }
        }
    }

    let mut accum = PrClassificationAccum::new(toolchain, current_files.len());
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
                accum.record_unchanged(rel_path, split.interface_hash, &split.shards);
            }
            (Some(base_src), Some(cur_src)) => {
                let cur_split = split_lean_source(cur_src, &[]);
                let base_split = split_lean_source(base_src, &[]);
                accum.record_modified(
                    rel_path,
                    &base_split.interface_hash,
                    &base_split.hygiene,
                    &base_split.shards,
                    cur_split,
                );
            }
            (None, Some(cur_src)) => accum.record_added(rel_path, split_lean_source(cur_src, &[])),
            (Some(base_src), None) => {
                let base_split = split_lean_source(base_src, &[]);
                accum.record_deleted(rel_path, &base_split.interface_hash, &base_split.shards);
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

    accum.finish()
}

pub use crate::receipt::*;

const SENSITIVE_ENV_KEYS: &[&str] = &[
    "GH_TOKEN",
    "GITHUB_TOKEN",
    "OPENAI_API_KEY",
    "ANTHROPIC_API_KEY",
    "AWS_SECRET_ACCESS_KEY",
    "AWS_SESSION_TOKEN",
    "NPM_TOKEN",
    "CARGO_REGISTRY_TOKEN",
];

fn scrub_sensitive_env_map(env_vars: &mut std::collections::HashMap<String, String>) {
    for k in SENSITIVE_ENV_KEYS {
        env_vars.remove(*k);
    }
}

fn scrub_sensitive_env_cmd(cmd: &mut Command) {
    for k in SENSITIVE_ENV_KEYS {
        cmd.env_remove(k);
    }
}

fn to_batch_req_item((k, sh): &(String, splitter::TheoremShard)) -> pack::CheckShardBatchItem {
    pack::CheckShardBatchItem {
        shard_key: k.clone(),
        decl_name: sh.name.clone(),
        prefix_env_hash: sh.prefix_env_hash.clone(),
        stmt_hash: sh.stmt_hash.clone(),
        proof_hash: sh.proof_hash.clone(),
    }
}

fn make_batch_zreq(
    shard_key: String,
    shard_source: String,
    toolchain: &str,
    lean_path: &str,
) -> pack::CheckShardHttpRequest {
    pack::CheckShardHttpRequest {
        decl: "__batch__".to_string(),
        shard_key,
        shard_source,
        interface_hash: String::new(),
        prefix_env_hash: String::new(),
        stmt_hash: String::new(),
        proof_hash: String::new(),
        toolchain: toolchain.to_string(),
        lean_path: lean_path.to_string(),
        skip_cas_lock: true,
    }
}

fn run_lean_temp_file(
    lean_bin: &str,
    tmp_path: &Path,
    src: &str,
    canon_dir: &Path,
    env_vars: &std::collections::HashMap<String, String>,
    is_untrusted: bool,
) -> Result<std::process::Output> {
    fs::write(tmp_path, src.as_bytes())?;
    let mut cmd = Command::new(lean_bin);
    cmd.arg(tmp_path).current_dir(canon_dir).envs(env_vars);
    if is_untrusted {
        scrub_sensitive_env_cmd(&mut cmd);
    }
    let out = cmd.output()?;
    let _ = fs::remove_file(tmp_path);
    Ok(out)
}

/// Execute `turbo-lean seed-shards`.
pub fn run_seed_shards_command(
    store: &mut TurboStore,
    json: bool,
    project_dir: PathBuf,
    trust_domain: String,
    require_olean: bool,
) -> Result<()> {
    let t0 = Instant::now();
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.clone());
    let toolchain = detect_toolchain(&canon_dir);
    let (files_seeded, shards_seeded, split_cache_hits) =
        seed_project_theorem_shards(store, &canon_dir, &toolchain, &trust_domain, require_olean)?;
    let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
    if json {
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
                "status": "shards_seeded",
                "project_dir": canon_dir.display().to_string(),
                "files_seeded": files_seeded,
                "shards_seeded": shards_seeded,
                "file_split_cache_hits": split_cache_hits,
                "trust_domain": trust_domain,
                "elapsed_ms": (elapsed_ms * 1000.0).round() / 1000.0
            }))?
        );
    } else {
        println!(
            "[turbo-lean] SEEDED {} THEOREM SHARDS across {} files in {} ({:.2} ms)",
            shards_seeded,
            files_seeded,
            canon_dir.display(),
            elapsed_ms
        );
    }
    Ok(())
}

/// Execute `turbo-lean ci-verify`.
pub fn run_ci_verify_command(
    store: &mut TurboStore,
    json: bool,
    mode: String,
    project_dir: PathBuf,
    receipt: Option<PathBuf>,
    seed_shards: bool,
    scope: Option<PathBuf>,
) -> Result<()> {
    let t0 = Instant::now();
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.clone());
    let is_untrusted = mode == "untrusted";
    let trust_domain = if is_untrusted {
        "untrusted:ci".to_string()
    } else {
        "trusted".to_string()
    };

    let mut flagged_files = Vec::new();
    let mut total_files = 0usize;
    let mut total_shards = 0usize;
    let mut per_file_interfaces = BTreeMap::new();
    let lean_paths =
        crate::lake_build::collect_project_lean_files(&canon_dir, true, scope.as_deref());
    let toolchain = detect_toolchain(&canon_dir);
    let mut hasher = blake3::Hasher::new();
    hasher.update(format!("turbo-lean-build-v1\n{}\n{}\n\n", toolchain, trust_domain).as_bytes());

    let mut interface_hasher = blake3::Hasher::new();
    interface_hasher.update(toolchain.as_bytes());

    let mut file_hashes = BTreeMap::new();
    let mut full_splits_opt: Option<Vec<(PathBuf, String, splitter::SplitResult)>> = None;

    if !seed_shards {
        if let Ok(summary) = load_project_stat_summary_cached(store, &canon_dir, &lean_paths) {
            total_files = summary.total_files;
            total_shards = summary.total_shards;
            flagged_files = summary.flagged_files;
            for path in &lean_paths {
                let rel_path = rel_path_from_dir(path, &canon_dir);
                if let Some(src_blake3) = summary.file_hashes.get(&rel_path) {
                    if let Ok(raw_bytes) = blake3::Hash::from_hex(src_blake3.as_bytes()) {
                        hasher.update(rel_path.as_bytes());
                        hasher.update(b":");
                        hasher.update(raw_bytes.as_bytes());
                        hasher.update(b"\n");
                    }
                }
                if let Some(iface_hash) = summary.per_file_interfaces.get(&rel_path) {
                    interface_hasher.update(format!("{}:{}\n", rel_path, iface_hash).as_bytes());
                }
            }
            file_hashes = summary.file_hashes;
            per_file_interfaces = summary.per_file_interfaces;
        }
    }

    if total_files == 0 {
        let (splits_with_hashes, _split_hits) =
            load_and_split_files_with_hashes_cached(store, &lean_paths)?;
        let mut splits = Vec::with_capacity(splits_with_hashes.len());
        for (path, src_blake3, src, split) in splits_with_hashes {
            total_files += 1;
            total_shards += split.shards.len();
            let rel_path = rel_path_from_dir(&path, &canon_dir);
            if let Ok(raw_bytes) = blake3::Hash::from_hex(src_blake3.as_bytes()) {
                hasher.update(rel_path.as_bytes());
                hasher.update(b":");
                hasher.update(raw_bytes.as_bytes());
                hasher.update(b"\n");
                file_hashes.insert(rel_path.clone(), src_blake3);
            } else {
                let src_hash = blake3::hash(src.as_bytes());
                hasher.update(rel_path.as_bytes());
                hasher.update(b":");
                hasher.update(src_hash.as_bytes());
                hasher.update(b"\n");
                file_hashes.insert(rel_path.clone(), src_hash.to_hex().to_string());
            }
            interface_hasher.update(format!("{}:{}\n", rel_path, split.interface_hash).as_bytes());
            per_file_interfaces.insert(rel_path.clone(), split.interface_hash.clone());
            if !split.hygiene.is_clean_for_certification() {
                flagged_files.push((rel_path, split.hygiene.flagged_items.clone()));
            }
            splits.push((path, src, split));
        }
        full_splits_opt = Some(splits);
    }

    if !flagged_files.is_empty() {
        anyhow::bail!(
            "CI Hygiene & Axiom Gate FAILED on {} files: {:?}",
            flagged_files.len(),
            flagged_files
        );
    }

    let action_key = hasher.finalize().to_hex().to_string();
    let interface_hash = interface_hasher.finalize().to_hex().to_string();
    let project_name = canon_dir
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "ci-project".to_string());

    let mut bwrap_used = false;
    let ci_axioms = [
        "propext".to_string(),
        "Quot.sound".to_string(),
        "Classical.choice".to_string(),
    ];

    let (build_status, _resolved_env_opt) = if let Some(outputs) =
        store.get_cached_action(&action_key, &trust_domain)?
    {
        store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
        store.record_attestation(
            &action_key,
            "turbo-lean-ci-gate",
            env!("CARGO_PKG_VERSION"),
            &ci_axioms,
            None,
        )?;
        let resolved_env = if std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
            resolve_lake_env(store, &canon_dir).ok()
        } else {
            None
        };
        ("cache_hit(coalesced=false)".to_string(), resolved_env)
    } else {
        let oleans_up_to_date = are_all_project_oleans_up_to_date(&canon_dir, &file_hashes);
        let mut singleflight_hit_status: Option<String> = None;
        let lease_opt = if oleans_up_to_date {
            None
        } else {
            match store.acquire_singleflight(
                &action_key,
                &toolchain,
                "module_full",
                &trust_domain,
            )? {
                SingleflightOutcome::CacheHit { outputs, coalesced } => {
                    store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
                    store.record_attestation(
                        &action_key,
                        "turbo-lean-ci-gate",
                        env!("CARGO_PKG_VERSION"),
                        &ci_axioms,
                        None,
                    )?;
                    singleflight_hit_status = Some(format!("cache_hit(coalesced={})", coalesced));
                    None
                }
                SingleflightOutcome::Leader(lease) => Some(lease),
            }
        };

        if let Some(hit_status) = singleflight_hit_status {
            (hit_status, None)
        } else {
            if !oleans_up_to_date {
                let build_rep = crate::module_builder::build_project_modules_native(
                    store,
                    &canon_dir,
                    &[],
                    &trust_domain,
                    1,
                    is_untrusted,
                    json,
                    Some(&file_hashes),
                )
                .context("CI native module build failed")?;
                bwrap_used = build_rep.bwrap_used;
            }

            let env_key = TurboStore::compute_lake_env_key(&canon_dir);
            let resolved_env = if std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
                resolve_or_share_lake_env(store, &canon_dir, &env_key)?
            } else {
                store.get_lake_env(&env_key)?.map(|m| (m, false))
            };
            let lake_env_to_put = resolved_env
                .as_ref()
                .filter(|(_, is_new)| *is_new)
                .map(|(m, _)| (env_key.as_str(), m));

            let dur_ms = t0.elapsed().as_millis() as i64;
            let (outputs, reg_blobs) = stage_lake_build_outputs(store, &canon_dir)?;
            store.publish_ingested_worktree_action(
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
                1,
                lake_env_to_put,
                Some((
                    "turbo-lean-ci-gate",
                    env!("CARGO_PKG_VERSION"),
                    &ci_axioms,
                    None,
                )),
            )?;
            ("built_and_verified".to_string(), resolved_env)
        }
    };

    warm_git_head_tree_cache(
        store,
        &canon_dir,
        &lean_paths,
        &toolchain,
        full_splits_opt.as_deref(),
    );

    let seeded_shards = if seed_shards {
        if let Some(ref sp) = full_splits_opt {
            seed_project_theorem_shards_from_splits(
                store,
                &canon_dir,
                &toolchain,
                &trust_domain,
                false,
                sp,
            )?
            .1
        } else {
            seed_project_theorem_shards(store, &canon_dir, &toolchain, &trust_domain, false)?.1
        }
    } else {
        0
    };

    let ver_receipt = build_verification_receipt(
        &mode,
        &interface_hash,
        &action_key,
        total_files,
        total_shards,
        0,
        per_file_interfaces,
    );
    emit_verification_receipt_if_requested(receipt.as_deref(), &ver_receipt)?;

    let elapsed_ms = t0.elapsed().as_millis();
    if json {
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
                "status": "ci_verified",
                "mode": mode,
                "trust_domain": trust_domain,
                "env_scrubbed": is_untrusted,
                "bwrap_net_isolated": bwrap_used,
                "bwrap_sandbox_used": bwrap_used,
                "build_status": build_status,
                "action_key": action_key,
                "interface_hash": interface_hash,
                "receipt_blake3": ver_receipt.receipt_blake3,
                "receipt_path": receipt.as_ref().map(|p| p.display().to_string()),
                "files_audited": total_files,
                "files_checked": total_files,
                "theorem_shards": total_shards,
                "shards_seeded": seeded_shards,
                "zero_sorry": true,
                "zero_native_decide": true,
                "elapsed_ms": elapsed_ms
            }))?
        );
    } else {
        println!(
            "[turbo-lean] CI-VERIFY PASSED (mode={}, env_scrubbed={}, status={}, {} files, {} theorems, receipt_blake3={}.., {} ms)",
            mode, is_untrusted, build_status, total_files, total_shards, &ver_receipt.receipt_blake3[..12], elapsed_ms
        );
    }
    if is_untrusted && std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
        let ev = _resolved_env_opt
            .map(|(m, _)| m)
            .or_else(|| resolve_lake_env(store, &canon_dir).ok().map(|(m, _)| m))
            .unwrap_or_default();
        pack::warm_local_zygote_daemon_nonblocking(store, &ev);
    }
    Ok(())
}

fn build_pr_verification_receipt(
    mode: &str,
    base: &str,
    classification: &PrClassification,
) -> VerificationReceipt {
    let total_theorems = classification.unchanged_theorems.len()
        + classification.proof_edited_theorems.len()
        + classification.statement_edited_theorems.len();
    let action_key = format!(
        "pr-verify:{}:{}",
        base,
        &classification.current_interface_hash
            [..16.min(classification.current_interface_hash.len())]
    );
    build_verification_receipt(
        mode,
        &classification.current_interface_hash,
        &action_key,
        classification.total_files,
        total_theorems,
        0,
        classification.per_file_interfaces.clone(),
    )
}

fn serialize_shard_receipt_bytes(sh: &splitter::TheoremShard, now: i64) -> Result<Vec<u8>> {
    crate::check::make_shard_receipt_bytes(
        &sh.name,
        &sh.prefix_env_hash,
        &sh.stmt_hash,
        &sh.proof_hash,
        now,
    )
}

fn finalize_batch_publish_entries(
    publish: &mut Vec<(String, String, Vec<u8>, i64)>,
    shards: &[(String, splitter::TheoremShard)],
    dur_ms: i64,
) -> Result<usize> {
    if publish.len() == shards.len() {
        for entry in publish.iter_mut() {
            entry.3 = dur_ms;
        }
    } else {
        publish.clear();
        let now = crate::db::now_unix();
        for (k, sh) in shards {
            let r_bytes = serialize_shard_receipt_bytes(sh, now)?;
            publish.push((k.clone(), sh.name.clone(), r_bytes, dur_ms));
        }
    }
    Ok(shards.len())
}

/// Execute `turbo-lean pr-verify`.
#[allow(clippy::too_many_arguments)]
pub fn run_pr_verify_command(
    store: &mut TurboStore,
    json: bool,
    project_dir: PathBuf,
    base: String,
    mode: String,
    disallow_statement_changes: bool,
    receipt: Option<PathBuf>,
    remote_http: Option<String>,
    scope: Option<PathBuf>,
    cone_stats: bool,
    max_cone_jobs: usize,
    nanoda_bin: Option<PathBuf>,
) -> Result<()> {
    let t0 = Instant::now();
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.clone());
    let is_untrusted = mode == "untrusted";
    let trust_domain = if is_untrusted {
        "untrusted:ci".to_string()
    } else {
        "trusted".to_string()
    };
    let toolchain = detect_toolchain(&canon_dir);

    let (classification, shards_by_file, current_files, current_splits) =
        load_and_classify_pr_from_git_scoped(
            store,
            &canon_dir,
            &base,
            &toolchain,
            scope.as_deref(),
        )?;

    if disallow_statement_changes
        && (classification.interface_drift || !classification.statement_edited_theorems.is_empty())
    {
        anyhow::bail!(
            "PR statement/interface change gate FAILED (--disallow-statement-changes, mode={}): interface_drift={}, altered_files={:?}, statement_edited_theorems={:?}",
            mode,
            classification.interface_drift,
            classification.altered_interface_files,
            classification.statement_edited_theorems
        );
    }

    let mut all_edited_keys = Vec::new();
    for (_rel_path, file_shards) in &shards_by_file {
        for (k, _sh, _fast_ok) in file_shards {
            all_edited_keys.push(k.clone());
        }
    }

    let cached_set = store.batch_completed_action_keys(&all_edited_keys, &trust_domain)?;

    let mut shard_cache_hits = 0usize;
    let mut shards_verified = 0usize;
    let mut fast_olean_used = false;
    let mut cross_file_coalesced = false;
    let mut batch_to_publish = Vec::new();
    let mut inflight_tx_open = false;
    let mut prebuilt_ver_receipt: Option<VerificationReceipt> = None;

    let mut uncached_by_file = Vec::new();
    let mut raw_uncached_jobs = 0usize;
    for (rel_path, file_shards) in shards_by_file {
        let mut uncached = Vec::new();
        let mut can_fast_olean = true;
        for (k, sh, fast_ok) in file_shards {
            if cached_set.contains(&k) {
                shard_cache_hits += 1;
            } else {
                if !fast_ok {
                    can_fast_olean = false;
                }
                raw_uncached_jobs += 1;
                uncached.push((k, sh));
            }
        }
        if !uncached.is_empty() {
            uncached_by_file.push((rel_path, uncached, can_fast_olean));
        }
    }

    let effective_job_cap = unsafe {
        crate::cluster::c_abi::turbo_spec_effective_cone_job_cap(
            raw_uncached_jobs as u64,
            max_cone_jobs as u64,
        ) as usize
    };
    if max_cone_jobs > 0 && raw_uncached_jobs > effective_job_cap {
        let mut remaining = effective_job_cap;
        let mut capped_by_file = Vec::new();
        for (rel_path, mut uncached, can_fast_olean) in uncached_by_file {
            if remaining == 0 {
                break;
            }
            if uncached.len() > remaining {
                uncached.truncate(remaining);
            }
            remaining = remaining.saturating_sub(uncached.len());
            capped_by_file.push((rel_path, uncached, can_fast_olean));
        }
        uncached_by_file = capped_by_file;
    }

    if !uncached_by_file.is_empty() {
        let fast_lib_dir = canon_dir.join(".lake/build/lib/lean");
        let fast_local_zygote_url = if remote_http.is_none() {
            let mut fast_ev = std::collections::HashMap::new();
            if fast_lib_dir.exists() {
                fast_ev.insert(
                    "LEAN_PATH".to_string(),
                    resolve_remote_lean_path(&canon_dir, None),
                );
            }
            pack::ensure_local_zygote_daemon(store, &fast_ev)
        } else {
            None
        };
        let (mut env_vars, lean_bin, lean_path_str) =
            if fast_local_zygote_url.is_some() && fast_lib_dir.exists() {
                let lp = resolve_remote_lean_path(&canon_dir, None);
                let mut fast_ev = std::collections::HashMap::new();
                fast_ev.insert("LEAN_PATH".to_string(), lp.clone());
                (fast_ev, "lean".to_string(), lp)
            } else {
                let (mut ev, _) = resolve_lake_env(store, &canon_dir)?;
                let lb = lean_bin_from_env(&ev);
                if is_untrusted {
                    scrub_sensitive_env_map(&mut ev);
                }
                let lp = resolve_remote_lean_path(&canon_dir, Some(&ev));
                (ev, lb, lp)
            };

        let staging_dir = store.fast_staging_dir();
        let pid = std::process::id();

        let mut cross_eligible = Vec::new();
        if uncached_by_file.len() > 1 {
            for (rel_path, file_uncached, can_fast_olean) in &uncached_by_file {
                if !*can_fast_olean {
                    break;
                }
                let src = current_files
                    .get(rel_path)
                    .map(|s| s.as_str())
                    .unwrap_or("");
                let abs_file = canon_dir.join(rel_path);
                let uncached_names: std::collections::HashSet<String> = file_uncached
                    .iter()
                    .map(|(_, sh)| sh.name.clone())
                    .collect();
                if let Some(mod_imp) = resolve_prebuilt_module_import(&canon_dir, &abs_file) {
                    let fast_ok = if let Some(sp) = current_splits.get(rel_path) {
                        splitter::can_use_fast_olean_import_with_split(sp, &uncached_names)
                    } else {
                        splitter::can_use_fast_olean_import(src, &uncached_names)
                    };
                    if fast_ok {
                        cross_eligible.push((mod_imp, src, file_uncached));
                    }
                }
            }
        }

        let mut cross_batch_done = false;
        if uncached_by_file.len() > 1 && cross_eligible.len() == uncached_by_file.len() {
            let total_uncached: usize = uncached_by_file.iter().map(|(_, u, _)| u.len()).sum();
            let shard_ref_vecs: Vec<Vec<&splitter::TheoremShard>> = cross_eligible
                .iter()
                .map(|(_, _, fu)| fu.iter().map(|(_, sh)| sh).collect())
                .collect();
            let cross_inputs: Vec<(&str, &str, &[&splitter::TheoremShard])> = cross_eligible
                .iter()
                .enumerate()
                .map(|(i, (m, s, _))| (m.as_str(), *s, shard_ref_vecs[i].as_slice()))
                .collect();
            let cross_src = splitter::build_cross_file_coalesced_shard(&cross_inputs);
            if let Some(ref remote_url) = remote_http {
                let req_items: Vec<pack::CheckShardBatchItem> = uncached_by_file
                    .iter()
                    .flat_map(|(_, fu, _)| fu.iter().map(to_batch_req_item))
                    .collect();
                if let Ok(resp) = pack::offload_check_shards_batch_http(
                    store,
                    remote_url,
                    &req_items,
                    &cross_src,
                    &trust_domain,
                    &toolchain,
                    &lean_path_str,
                ) {
                    if resp.ok {
                        cross_batch_done = true;
                        cross_file_coalesced = true;
                        fast_olean_used = true;
                        shard_cache_hits += resp.cache_hits;
                        shards_verified += resp.verified_count;
                    }
                }
            }

            if !cross_batch_done {
                let cross_t0 = Instant::now();
                let zreq = make_batch_zreq(
                    format!("pr_verify_cross_{}", pid),
                    cross_src.clone(),
                    &toolchain,
                    &lean_path_str,
                );
                let mut cross_ok = if let Some(ref z_url) = fast_local_zygote_url {
                    pack::try_zygote_url_check_shard_with_inflight(z_url, &zreq, || {
                        let now = crate::db::now_unix();
                        batch_to_publish.reserve(total_uncached);
                        for (_rel_path, file_uncached, _) in &uncached_by_file {
                            for (k, sh) in file_uncached {
                                if let Ok(r_bytes) = serialize_shard_receipt_bytes(sh, now) {
                                    batch_to_publish.push((
                                        k.clone(),
                                        sh.name.clone(),
                                        r_bytes,
                                        1i64,
                                    ));
                                }
                            }
                        }
                        let _ = store.prestage_theorem_shard_blobs(&batch_to_publish);
                        if store
                            .begin_inflight_publish_theorem_shards(
                                &toolchain,
                                &trust_domain,
                                &batch_to_publish,
                            )
                            .is_ok()
                        {
                            inflight_tx_open = true;
                        }
                        if prebuilt_ver_receipt.is_none() {
                            prebuilt_ver_receipt =
                                Some(build_pr_verification_receipt(&mode, &base, &classification));
                        }
                    })
                    .is_some()
                } else {
                    pack::try_local_zygote_check_shard(store, &env_vars, &zreq).is_some()
                };
                if !cross_ok {
                    if inflight_tx_open {
                        store.rollback_inflight_publish();
                        inflight_tx_open = false;
                    }
                    batch_to_publish.clear();
                    if env_vars.is_empty() {
                        if let Ok((mut ev, _)) = resolve_lake_env(store, &canon_dir) {
                            if is_untrusted {
                                scrub_sensitive_env_map(&mut ev);
                            }
                            env_vars = ev;
                        }
                    }
                    let lb = if env_vars.is_empty() {
                        lean_bin.clone()
                    } else {
                        lean_bin_from_env(&env_vars)
                    };
                    let tmp_cross = staging_dir.join(format!("pr_verify_cross_{}.lean", pid));
                    cross_ok = run_lean_temp_file(
                        &lb,
                        &tmp_cross,
                        &cross_src,
                        &canon_dir,
                        &env_vars,
                        is_untrusted,
                    )?
                    .status
                    .success();
                }
                if cross_ok {
                    cross_batch_done = true;
                    cross_file_coalesced = true;
                    fast_olean_used = true;
                    let dur_ms = (cross_t0.elapsed().as_millis() as i64
                        / (total_uncached as i64).max(1))
                    .max(1);
                    let flat_shards: Vec<(String, splitter::TheoremShard)> = uncached_by_file
                        .iter()
                        .flat_map(|(_, fu, _)| fu.iter().cloned())
                        .collect();
                    shards_verified += finalize_batch_publish_entries(
                        &mut batch_to_publish,
                        &flat_shards,
                        dur_ms,
                    )?;
                }
            }
        }

        if !cross_batch_done {
            if let Some(ref remote_url) = remote_http {
                for (rel_path, file_uncached, can_fast_olean) in uncached_by_file {
                    let src = current_files.get(&rel_path).cloned().unwrap_or_default();
                    let abs_file = canon_dir.join(&rel_path);
                    let canon_lf = abs_file.canonicalize().unwrap_or(abs_file);
                    let uncached_names: std::collections::HashSet<String> = file_uncached
                        .iter()
                        .map(|(_, sh)| sh.name.clone())
                        .collect();
                    let req_items: Vec<pack::CheckShardBatchItem> =
                        file_uncached.iter().map(to_batch_req_item).collect();

                    let mut remote_ok = false;
                    if can_fast_olean {
                        if let Some(mod_imp) = resolve_prebuilt_module_import(&canon_dir, &canon_lf)
                        {
                            let fast_src_opt = if let Some(sp) = current_splits.get(&rel_path) {
                                splitter::build_fast_olean_shard_source_with_split(
                                    &src,
                                    sp,
                                    &mod_imp,
                                    &uncached_names,
                                )
                            } else {
                                splitter::build_fast_olean_shard_source(
                                    &src,
                                    &mod_imp,
                                    &uncached_names,
                                )
                            };
                            if let Some(fast_src) = fast_src_opt {
                                if let Ok(resp) = pack::offload_check_shards_batch_http(
                                    store,
                                    remote_url,
                                    &req_items,
                                    &fast_src,
                                    &trust_domain,
                                    &toolchain,
                                    &lean_path_str,
                                ) {
                                    if resp.ok {
                                        remote_ok = true;
                                        fast_olean_used = true;
                                        shard_cache_hits += resp.cache_hits;
                                        shards_verified += resp.verified_count;
                                    }
                                }
                            }
                        }
                    }
                    if !remote_ok {
                        let coal_src =
                            splitter::build_coalesced_shard_source(&src, &uncached_names);
                        let resp = pack::offload_check_shards_batch_http(
                            store,
                            remote_url,
                            &req_items,
                            &coal_src,
                            &trust_domain,
                            &toolchain,
                            &lean_path_str,
                        )?;
                        if !resp.ok {
                            anyhow::bail!(
                                "Remote PR shard verification failed in {} on {}: {}",
                                rel_path,
                                remote_url,
                                resp.error.unwrap_or_else(|| resp.stderr)
                            );
                        }
                        shard_cache_hits += resp.cache_hits;
                        shards_verified += resp.verified_count;
                    }
                }
            } else {
                let local_zygote_url = fast_local_zygote_url
                    .or_else(|| pack::ensure_local_zygote_daemon(store, &env_vars));
                if local_zygote_url.is_none() && env_vars.is_empty() {
                    if let Ok((mut ev, _)) = resolve_lake_env(store, &canon_dir) {
                        if is_untrusted {
                            scrub_sensitive_env_map(&mut ev);
                        }
                        env_vars = ev;
                    }
                }
                let store_root = store.root.as_path();
                type PrFileVerifyResult = Result<(
                    usize,
                    bool,
                    bool,
                    Option<VerificationReceipt>,
                    Vec<(String, String, Vec<u8>, i64)>,
                )>;
                let verify_one_file = |f_idx: usize,
                                       inflight_store: Option<&TurboStore>|
                 -> PrFileVerifyResult {
                    let mut local_verified = 0usize;
                    let mut local_fast_olean = false;
                    let mut local_tx_open = false;
                    let mut local_receipt: Option<VerificationReceipt> = None;
                    let mut local_publish = Vec::new();
                    let (ref rel_path, ref file_uncached, can_fast_olean) = uncached_by_file[f_idx];
                    let abs_file = canon_dir.join(rel_path);
                    let src: std::borrow::Cow<'_, str> = if let Some(s) =
                        current_files.get(rel_path)
                    {
                        std::borrow::Cow::Borrowed(s.as_str())
                    } else {
                        std::borrow::Cow::Owned(fs::read_to_string(&abs_file).unwrap_or_default())
                    };
                    let uncached_names: std::collections::HashSet<String> = file_uncached
                        .iter()
                        .map(|(_, sh)| sh.name.clone())
                        .collect();
                    let tmp_batch = staging_dir.join(format!("pr_verify_{}_{}.lean", pid, f_idx));
                    let f_t0 = Instant::now();

                    let mut verified_ok = false;
                    if can_fast_olean {
                        if let Some(mod_imp) = resolve_prebuilt_module_import(&canon_dir, &abs_file)
                        {
                            let fast_src_opt = if let Some(sp) = current_splits.get(rel_path) {
                                splitter::build_fast_olean_shard_source_with_split(
                                    &src,
                                    sp,
                                    &mod_imp,
                                    &uncached_names,
                                )
                            } else {
                                splitter::build_fast_olean_shard_source(
                                    &src,
                                    &mod_imp,
                                    &uncached_names,
                                )
                            };
                            if let Some(fast_src) = fast_src_opt {
                                if let Some(z_url) = local_zygote_url.as_deref() {
                                    let zreq = make_batch_zreq(
                                        format!("pr_verify_fast_{}_{}", pid, f_idx),
                                        fast_src.clone(),
                                        &toolchain,
                                        &lean_path_str,
                                    );
                                    if pack::try_zygote_url_check_shard_with_inflight(
                                        z_url,
                                        &zreq,
                                        || {
                                            let now = crate::db::now_unix();
                                            local_publish.reserve(file_uncached.len());
                                            for (k, sh) in file_uncached {
                                                if let Ok(r_bytes) =
                                                    serialize_shard_receipt_bytes(sh, now)
                                                {
                                                    local_publish.push((
                                                        k.clone(),
                                                        sh.name.clone(),
                                                        r_bytes,
                                                        1i64,
                                                    ));
                                                }
                                            }
                                            let _ = crate::db::prestage_theorem_shard_blobs_at(
                                                store_root,
                                                &local_publish,
                                            );
                                            if let Some(st) = inflight_store {
                                                if st
                                                    .begin_inflight_publish_theorem_shards(
                                                        &toolchain,
                                                        &trust_domain,
                                                        &local_publish,
                                                    )
                                                    .is_ok()
                                                {
                                                    local_tx_open = true;
                                                }
                                                local_receipt =
                                                    Some(build_pr_verification_receipt(
                                                        &mode,
                                                        &base,
                                                        &classification,
                                                    ));
                                            }
                                        },
                                    )
                                    .is_some()
                                    {
                                        verified_ok = true;
                                        local_fast_olean = true;
                                    } else {
                                        if local_tx_open {
                                            if let Some(st) = inflight_store {
                                                st.rollback_inflight_publish();
                                            }
                                            local_tx_open = false;
                                        }
                                        local_publish.clear();
                                    }
                                }
                                if !verified_ok {
                                    if run_lean_temp_file(
                                        &lean_bin,
                                        &tmp_batch,
                                        &fast_src,
                                        &canon_dir,
                                        &env_vars,
                                        is_untrusted,
                                    )?
                                    .status
                                    .success()
                                    {
                                        verified_ok = true;
                                        local_fast_olean = true;
                                    }
                                }
                            }
                        }
                    }

                    let try_zygote_or_cli_batch =
                        |src_to_check: &str, zreq_key: String| -> Result<bool> {
                            if let Some(z_url) = local_zygote_url.as_deref() {
                                let zreq = make_batch_zreq(
                                    zreq_key,
                                    src_to_check.to_string(),
                                    &toolchain,
                                    &lean_path_str,
                                );
                                if pack::try_zygote_url_check_shard(z_url, &zreq).is_some() {
                                    return Ok(true);
                                }
                            }
                            Ok(run_lean_temp_file(
                                &lean_bin,
                                &tmp_batch,
                                src_to_check,
                                &canon_dir,
                                &env_vars,
                                is_untrusted,
                            )?
                            .status
                            .success())
                        };

                    if !verified_ok {
                        if let Some(pruned_src) =
                            splitter::build_pruned_imports_shard_source(&src, &uncached_names)
                        {
                            if try_zygote_or_cli_batch(
                                &pruned_src,
                                format!("pr_verify_{}_{}", pid, f_idx),
                            )? {
                                verified_ok = true;
                                local_fast_olean = true;
                            }
                        }
                    }

                    if !verified_ok && file_uncached.len() > 1 {
                        let coal_src =
                            splitter::build_coalesced_shard_source(&src, &uncached_names);
                        if try_zygote_or_cli_batch(
                            &coal_src,
                            format!("pr_verify_coal_{}_{}", pid, f_idx),
                        )? {
                            verified_ok = true;
                        }
                    }

                    if verified_ok {
                        let dur_ms = (f_t0.elapsed().as_millis() as i64
                            / (file_uncached.len() as i64).max(1))
                        .max(1);
                        local_verified = finalize_batch_publish_entries(
                            &mut local_publish,
                            file_uncached,
                            dur_ms,
                        )?;
                    } else {
                        let now = crate::db::now_unix();
                        for (s_idx, (k, sh)) in file_uncached.iter().enumerate() {
                            let tmp_single = staging_dir
                                .join(format!("pr_verify_single_{}_{}_{}.lean", pid, f_idx, s_idx));
                            let s_t0 = Instant::now();
                            let single_src: std::borrow::Cow<'_, str> =
                                if sh.shard_source.is_empty() {
                                    let reconstructed =
                                        splitter::reconstruct_single_shard_source(&src, &sh.name)
                                            .unwrap_or_else(|| {
                                                let mut single_set =
                                                    std::collections::HashSet::with_capacity(1);
                                                single_set.insert(sh.name.clone());
                                                splitter::build_coalesced_shard_source(
                                                    &src,
                                                    &single_set,
                                                )
                                            });
                                    std::borrow::Cow::Owned(reconstructed)
                                } else {
                                    std::borrow::Cow::Borrowed(sh.shard_source.as_str())
                                };
                            let mut single_ok = false;
                            if let Some(z_url) = local_zygote_url.as_deref() {
                                let zreq = pack::CheckShardHttpRequest {
                                    decl: sh.name.clone(),
                                    shard_key: k.clone(),
                                    shard_source: single_src.to_string(),
                                    interface_hash: String::new(),
                                    prefix_env_hash: sh.prefix_env_hash.clone(),
                                    stmt_hash: sh.stmt_hash.clone(),
                                    proof_hash: sh.proof_hash.clone(),
                                    toolchain: toolchain.clone(),
                                    lean_path: lean_path_str.clone(),
                                    skip_cas_lock: true,
                                };
                                if pack::try_zygote_url_check_shard_with_inflight(
                                    z_url,
                                    &zreq,
                                    || {
                                        if file_uncached.len() == 1 {
                                            if let Ok(r_bytes) =
                                                serialize_shard_receipt_bytes(sh, now)
                                            {
                                                local_publish.push((
                                                    k.clone(),
                                                    sh.name.clone(),
                                                    r_bytes,
                                                    1i64,
                                                ));
                                                let _ = crate::db::prestage_theorem_shard_blobs_at(
                                                    store_root,
                                                    &local_publish,
                                                );
                                                if let Some(st) = inflight_store {
                                                    if st
                                                        .begin_inflight_publish_theorem_shards(
                                                            &toolchain,
                                                            &trust_domain,
                                                            &local_publish,
                                                        )
                                                        .is_ok()
                                                    {
                                                        local_tx_open = true;
                                                    }
                                                    local_receipt =
                                                        Some(build_pr_verification_receipt(
                                                            &mode,
                                                            &base,
                                                            &classification,
                                                        ));
                                                }
                                            }
                                        }
                                    },
                                )
                                .is_some()
                                {
                                    single_ok = true;
                                } else if local_tx_open {
                                    if let Some(st) = inflight_store {
                                        st.rollback_inflight_publish();
                                    }
                                    local_tx_open = false;
                                    local_publish.clear();
                                }
                            }
                            if !single_ok {
                                let out = run_lean_temp_file(
                                    &lean_bin,
                                    &tmp_single,
                                    &single_src,
                                    &canon_dir,
                                    &env_vars,
                                    is_untrusted,
                                )?;
                                if !out.status.success() {
                                    anyhow::bail!(
                                        "PR shard verification failed for `{}` in {}:\n{}\n{}",
                                        sh.name,
                                        rel_path,
                                        String::from_utf8_lossy(&out.stdout),
                                        String::from_utf8_lossy(&out.stderr)
                                    );
                                }
                            }
                            let dur_ms = (s_t0.elapsed().as_millis() as i64).max(1);
                            local_verified += 1;
                            if local_publish.len() == 1 && file_uncached.len() == 1 {
                                local_publish[0].3 = dur_ms;
                            } else {
                                let r_bytes = serialize_shard_receipt_bytes(sh, now)?;
                                local_publish.push((k.clone(), sh.name.clone(), r_bytes, dur_ms));
                            }
                        }
                    }
                    Ok((
                        local_verified,
                        local_fast_olean,
                        local_tx_open,
                        local_receipt,
                        local_publish,
                    ))
                };

                let worker_results: Vec<PrFileVerifyResult> = if uncached_by_file.len() == 1 {
                    vec![verify_one_file(0, Some(store))]
                } else {
                    let default_jobs = std::thread::available_parallelism()
                        .map(|n| n.get())
                        .unwrap_or(4);
                    let jobs = default_jobs.max(1).min(uncached_by_file.len());
                    let next_f = std::sync::atomic::AtomicUsize::new(0);
                    let total_f = uncached_by_file.len();
                    let verify_ref = &verify_one_file;
                    std::thread::scope(|s| {
                        let mut handles = Vec::with_capacity(jobs);
                        for _ in 0..jobs {
                            let next_ref = &next_f;
                            handles.push(s.spawn(move || -> PrFileVerifyResult {
                                let mut acc_verified = 0usize;
                                let mut acc_fast = false;
                                let mut acc_pub = Vec::new();
                                loop {
                                    let f_idx =
                                        next_ref.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                                    if f_idx >= total_f {
                                        break;
                                    }
                                    let (v, f, _, _, p) = verify_ref(f_idx, None)?;
                                    acc_verified += v;
                                    if f {
                                        acc_fast = true;
                                    }
                                    acc_pub.extend(p);
                                }
                                Ok((acc_verified, acc_fast, false, None, acc_pub))
                            }));
                        }
                        handles
                            .into_iter()
                            .map(|h| {
                                h.join().unwrap_or_else(|_| {
                                    Err(anyhow::anyhow!("PR verification worker panicked"))
                                })
                            })
                            .collect()
                    })
                };

                for res in worker_results {
                    let (v_cnt, used_fast, tx_open, rec_opt, items) = res?;
                    shards_verified += v_cnt;
                    if used_fast {
                        fast_olean_used = true;
                    }
                    if tx_open {
                        inflight_tx_open = true;
                    }
                    if let Some(rec) = rec_opt {
                        prebuilt_ver_receipt = Some(rec);
                    }
                    batch_to_publish.extend(items);
                }
            }
        }

        if inflight_tx_open {
            store.commit_inflight_publish()?;
        } else {
            store.batch_publish_theorem_shards(&toolchain, &trust_domain, &batch_to_publish)?;
        }
    } else if remote_http.is_none() && std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
        let mut fast_ev = std::collections::HashMap::new();
        if canon_dir.join(".lake/build/lib/lean").exists() {
            fast_ev.insert(
                "LEAN_PATH".to_string(),
                resolve_remote_lean_path(&canon_dir, None),
            );
        }
        pack::warm_local_zygote_daemon_nonblocking(store, &fast_ev);
    }

    let ver_receipt = prebuilt_ver_receipt
        .unwrap_or_else(|| build_pr_verification_receipt(&mode, &base, &classification));
    emit_verification_receipt_if_requested(receipt.as_deref(), &ver_receipt)?;

    let mut nanoda_verified = false;
    if let Some(ref nanoda_path) = nanoda_bin {
        if !nanoda_path.exists() {
            anyhow::bail!(
                "External kernel checker `--nanoda-bin {}` does not exist",
                nanoda_path.display()
            );
        }
        let st = Command::new(nanoda_path)
            .arg(&canon_dir)
            .current_dir(&canon_dir)
            .status()
            .with_context(|| {
                format!(
                    "Failed to invoke external kernel checker `{}`",
                    nanoda_path.display()
                )
            })?;
        if !st.success() {
            anyhow::bail!(
                "External kernel checker `{}` rejected the environment (exit status: {})",
                nanoda_path.display(),
                st
            );
        }
        nanoda_verified = true;
    }

    let dirty_cone_theorems =
        classification.proof_edited_theorems.len() + classification.statement_edited_theorems.len();
    let total_project_theorems = classification.unchanged_theorems.len() + dirty_cone_theorems;
    let pruned_theorems = total_project_theorems.saturating_sub(dirty_cone_theorems);
    let pruned_percentage = if total_project_theorems == 0 {
        100.0
    } else {
        ((pruned_theorems as f64 / total_project_theorems as f64) * 10000.0).round() / 100.0
    };
    let estimated_lake_build_saved_ms = (pruned_theorems as u64) * 120;

    let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 100.0).round() / 100.0;
    if json {
        let mut out_json = serde_json::json!({
            "status": "pr_verified",
            "base": base,
            "mode": mode,
            "trust_domain": trust_domain,
            "env_scrubbed": is_untrusted,
            "interface_drift": classification.interface_drift,
            "baseline_interface_hash": classification.baseline_interface_hash,
            "interface_hash": classification.current_interface_hash,
            "receipt_blake3": ver_receipt.receipt_blake3,
            "receipt_path": receipt.as_ref().map(|p| p.display().to_string()),
            "total_files": classification.total_files,
            "modified_files": classification.modified_files,
            "altered_interface_files": classification.altered_interface_files,
            "unchanged_theorems_count": classification.unchanged_theorems.len(),
            "unchanged_theorems": classification.unchanged_theorems,
            "proof_edited_theorems_count": classification.proof_edited_theorems.len(),
            "proof_edited_theorems": classification.proof_edited_theorems,
            "statement_edited_theorems_count": classification.statement_edited_theorems.len(),
            "statement_edited_theorems": classification.statement_edited_theorems,
            "shard_cache_hits": shard_cache_hits,
            "shards_verified": shards_verified,
            "effective_cone_job_cap": effective_job_cap,
            "nanoda_verified": nanoda_verified,
            "fast_olean_used": fast_olean_used,
            "cross_file_coalesced": cross_file_coalesced,
            "zero_sorry": true,
            "zero_native_decide": true,
            "elapsed_ms": elapsed_ms
        });
        if cone_stats {
            out_json["cone_stats"] = serde_json::json!({
                "total_project_theorems": total_project_theorems,
                "dirty_cone_theorems": dirty_cone_theorems,
                "pruned_theorems": pruned_theorems,
                "pruned_percentage": pruned_percentage,
                "estimated_lake_build_saved_ms": estimated_lake_build_saved_ms,
                "effective_cone_job_cap": effective_job_cap,
            });
        }
        println!("{}", serde_json::to_string_pretty(&out_json)?);
    } else {
        println!(
            "[turbo-lean] PR-VERIFY PASSED vs {} ({} unchanged, {} proof-edited, {} stmt-edited, interface_drift={}, fast_olean={}, cross_file={}, {:.2} ms)",
            base,
            classification.unchanged_theorems.len(),
            classification.proof_edited_theorems.len(),
            classification.statement_edited_theorems.len(),
            classification.interface_drift,
            fast_olean_used,
            cross_file_coalesced,
            elapsed_ms
        );
        if cone_stats {
            println!(
                "[turbo-lean] CONE-STATS: total_theorems={} dirty_cone={} pruned={}% est_saved={}ms job_cap={}",
                total_project_theorems,
                dirty_cone_theorems,
                pruned_percentage,
                estimated_lake_build_saved_ms,
                effective_job_cap
            );
        }
    }
    Ok(())
}

#[cfg(test)]
mod pr_verify_tests {
    use super::*;
    use crate::lake_build::is_file_verified_in_lake_build;

    #[test]
    fn test_pr_verify_classification_proof_vs_statement_and_hygiene() {
        let base_refl = "namespace Demo\ndef addOne (n : Nat) : Nat := n + 1\ntheorem thm_unchanged (n : Nat) : addOne n = n + 1 := by\n  rfl\ntheorem thm_edited (n : Nat) : addOne n = n + 1 := by\n  rfl\nend Demo\n";
        let cur_refl_proof_only = "namespace Demo\ndef addOne (n : Nat) : Nat := n + 1\ntheorem thm_unchanged (n : Nat) : addOne n = n + 1 := by\n  rfl\ntheorem thm_edited (n : Nat) : addOne n = n + 1 := by\n  unfold addOne\n  rfl\nend Demo\n";
        let cur_refl_stmt_edit = "namespace Demo\ndef addOne (n : Nat) : Nat := n + 1\ntheorem thm_unchanged (n : Nat) : addOne n = n + 1 := by\n  rfl\ntheorem thm_edited (n : Nat) : addOne n = 1 + n := by\n  omega\nend Demo\n";
        let tc = "leanprover/lean4:v4.35.0";
        let base_map = BTreeMap::from([("Demo/Basic.lean".to_string(), base_refl.to_string())]);
        let cur_map = BTreeMap::from([(
            "Demo/Basic.lean".to_string(),
            cur_refl_proof_only.to_string(),
        )]);
        let (cls, to_verify) = classify_pr_changes(tc, &cur_map, &base_map).unwrap();
        assert!(!cls.interface_drift && cls.baseline_interface_hash == cls.current_interface_hash);
        assert_eq!(
            cls.unchanged_theorems,
            vec!["Demo/Basic.lean::thm_unchanged"]
        );
        assert_eq!(
            cls.proof_edited_theorems,
            vec!["Demo/Basic.lean::thm_edited"]
        );
        assert!(
            cls.statement_edited_theorems.is_empty()
                && to_verify["Demo/Basic.lean"].len() == 1
                && to_verify["Demo/Basic.lean"][0].2
        );

        let cur_stmt_map = BTreeMap::from([(
            "Demo/Basic.lean".to_string(),
            cur_refl_stmt_edit.to_string(),
        )]);
        let (cls_stmt, _) = classify_pr_changes(tc, &cur_stmt_map, &base_map).unwrap();
        assert!(
            cls_stmt.interface_drift
                && cls_stmt.baseline_interface_hash != cls_stmt.current_interface_hash
        );
        assert_eq!(
            cls_stmt.statement_edited_theorems,
            vec!["Demo/Basic.lean::thm_edited"]
        );

        let cur_sorry_map = BTreeMap::from([(
            "Demo/Basic.lean".to_string(),
            cur_refl_proof_only.replace("unfold addOne\n  rfl", "sorry"),
        )]);
        assert!(classify_pr_changes(tc, &cur_sorry_map, &base_map)
            .unwrap_err()
            .to_string()
            .contains("PR Hygiene & Axiom Gate FAILED"));
    }

    #[test]
    fn test_seed_project_theorem_shards_and_hygiene_filtering() -> Result<()> {
        let tmp_dir =
            std::env::temp_dir().join(format!("turbo_lean_seed_test_{}", std::process::id()));
        let proj_dir = tmp_dir.join("proj");
        fs::create_dir_all(proj_dir.join("Mod"))?;
        let clean_src =
            "namespace Mod\ntheorem t1 : 1 = 1 := rfl\ntheorem t2 : 2 = 2 := rfl\nend Mod\n";
        let dirty_src = "namespace Mod\ntheorem bad : False := sorry\nend Mod\n";
        fs::write(proj_dir.join("Mod/Clean.lean"), clean_src)?;
        fs::write(proj_dir.join("Mod/Dirty.lean"), dirty_src)?;

        let mut store = TurboStore::open(Some(&tmp_dir.join("cache")))?;
        let tc = "leanprover/lean4:v4.35.0";
        assert_eq!(
            seed_project_theorem_shards(&mut store, &proj_dir, tc, "trusted", false)
                .map(|(f, s, _)| (f, s))?,
            (1, 2)
        );

        let clean_keys: Vec<String> = split_lean_source(clean_src, &[])
            .shards
            .iter()
            .map(|s| compute_shard_key(tc, s))
            .collect();
        let dirty_keys: Vec<String> = split_lean_source(dirty_src, &[])
            .shards
            .iter()
            .map(|s| compute_shard_key(tc, s))
            .collect();
        assert_eq!(
            store
                .batch_get_theorem_shards(&clean_keys, "trusted")?
                .len(),
            2
        );
        assert!(store
            .batch_get_theorem_shards(&dirty_keys, "trusted")?
            .is_empty());
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_project_olean_freshness_and_source_hash_invalidation() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_olean_fresh_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let proj_dir = tmp_dir.join("proj");
        fs::create_dir_all(proj_dir.join("Demo"))?;
        let src_v1 = "namespace Demo\ntheorem t1 : 1 = 1 := rfl\nend Demo\n";
        let demo_file = proj_dir.join("Demo/Basic.lean");
        fs::write(&demo_file, src_v1)?;

        let hashes_v1 = BTreeMap::from([(
            "Demo/Basic.lean".to_string(),
            blake3::hash(src_v1.as_bytes()).to_hex().to_string(),
        )]);
        assert!(
            !are_all_project_oleans_up_to_date(&proj_dir, &hashes_v1)
                && !is_file_verified_in_lake_build(&proj_dir, &demo_file, src_v1)
        );

        let olean_path = proj_dir.join(".lake/build/lib/lean/Demo/Basic.olean");
        fs::create_dir_all(olean_path.parent().unwrap())?;
        fs::write(&olean_path, b"olean-dummy-bytes")?;
        assert!(
            are_all_project_oleans_up_to_date(&proj_dir, &hashes_v1)
                && is_file_verified_in_lake_build(&proj_dir, &demo_file, src_v1)
        );

        let src_v2 = "namespace Demo\ntheorem t1 : 1 = 1 := by rfl\nend Demo\n";
        let hashes_v2 = BTreeMap::from([(
            "Demo/Basic.lean".to_string(),
            blake3::hash(src_v2.as_bytes()).to_hex().to_string(),
        )]);
        assert!(
            !are_all_project_oleans_up_to_date(&proj_dir, &hashes_v2)
                && !is_file_verified_in_lake_build(&proj_dir, &demo_file, src_v2)
        );
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_warm_git_head_tree_cache_and_fast_pr_classification() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_git_head_v2_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let repo_dir = tmp_dir.join("repo");
        fs::create_dir_all(repo_dir.join("Demo"))?;

        let large_suffix = format!(
            "end Demo\n{}",
            "-- padding comment line for suffix fingerprint test\n".repeat(1400)
        );
        let f1_src = format!("namespace Demo\n@[simp] def idNat (n : Nat) : Nat := n\ntheorem t_a (n : Nat) : idNat n = n := by\n  rfl\n{}", large_suffix);
        fs::write(repo_dir.join("Demo/A.lean"), &f1_src)?;
        fs::write(
            repo_dir.join("Demo/B.lean"),
            "namespace Demo\ntheorem t_b : 2 + 2 = 4 := by\n  rfl\nend Demo\n",
        )?;

        for args in [
            &["init", "-q"][..],
            &["config", "user.email", "test@example.com"],
            &["config", "user.name", "Test"],
            &["add", "."],
            &["commit", "-q", "--no-gpg-sign", "-m", "init"],
        ] {
            assert!(Command::new("git")
                .args(args)
                .current_dir(&repo_dir)
                .status()?
                .success());
        }

        let canon_dir = fs::canonicalize(&repo_dir)?;
        let store = TurboStore::open(Some(&tmp_dir.join("cache")))?;
        let tc = "leanprover/lean4:v4.35.0";
        let lean_paths = vec![canon_dir.join("Demo/A.lean"), canon_dir.join("Demo/B.lean")];
        let (splits, _) = load_and_split_files_cached(&store, &lean_paths)?;
        warm_git_head_tree_cache(&store, &canon_dir, &lean_paths, tc, Some(&splits));

        let canon_f1 = canon_dir.join("Demo/A.lean");
        fs::write(&canon_f1, format!("namespace Demo\n@[simp] def idNat (n : Nat) : Nat := n\ntheorem t_a (n : Nat) : idNat n = n := by\n  simp\n{}", large_suffix))?;
        let f1_sz = file_stat_tuple(&canon_f1).unwrap().2;
        let (pref_only, fast_sp, unchanged_hit) =
            try_fast_split_single_file_from_path(&store, &canon_dir, &canon_f1, f1_sz, tc)
                .expect("fast prefix pread split should succeed");
        assert!(unchanged_hit == 0 && pref_only.len() < 512 && fast_sp.shards.len() == 1);

        let (cls, to_verify, changed_files, _) =
            load_and_classify_pr_from_git(&store, &canon_dir, "HEAD", tc)?;
        assert!(
            cls.total_files == 2
                && !cls.interface_drift
                && cls.statement_edited_theorems.is_empty()
        );
        assert_eq!(cls.modified_files, vec!["Demo/A.lean"]);
        assert_eq!(cls.unchanged_theorems, vec!["Demo/B.lean::t_b"]);
        assert_eq!(cls.proof_edited_theorems, vec!["Demo/A.lean::t_a"]);
        assert!(
            to_verify["Demo/A.lean"].len() == 1
                && to_verify["Demo/A.lean"][0].2
                && changed_files.len() == 1
                && changed_files["Demo/A.lean"].len() < 512
        );
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_constant_length_mid_suffix_mutation_detected() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_mid_suffix_mutant_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(&tmp_dir)?;

        let base_src = format!(
            "namespace Demo\n@[simp] def idNat (n : Nat) : Nat := n\ntheorem t_a (n : Nat) : idNat n = n := by\n  rfl\nend Demo\n{}",
            "-- padding comment line for suffix fingerprint test\n".repeat(600)
        );
        let sp = split_lean_source(&base_src, &[]);
        let base_entry =
            build_cached_head_file_entry(&base_src, &sp, "leanprover/lean4:v4.35.0", None);
        let suffix_len = base_entry.src_len - base_entry.prefix_byte_len;
        assert!(
            base_src.len() > 25_000
                && base_entry.prefix_byte_len < base_entry.src_len
                && suffix_len > 20_000
        );

        let mut mutated_bytes = base_src.as_bytes().to_vec();
        let mutate_idx = base_entry.prefix_byte_len + (suffix_len / 4);
        mutated_bytes[mutate_idx] = if mutated_bytes[mutate_idx] == b'X' {
            b'Y'
        } else {
            b'X'
        };
        let mutated_src = String::from_utf8(mutated_bytes)?;
        assert_eq!(mutated_src.len(), base_src.len());
        assert!(!is_unchanged_against_head_entry(&mutated_src, &base_entry));

        let test_path = tmp_dir.join("Mutated.lean");
        fs::write(&test_path, &mutated_src)?;
        assert!(try_read_prefix_if_suffix_matches(
            &test_path,
            mutated_src.len() as i64,
            &base_entry
        )
        .is_none());
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }
}
