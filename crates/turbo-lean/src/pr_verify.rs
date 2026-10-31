//! Git tree-aware incremental PR verification (`git-head-tree:v5:`), prefix-pread splitting,
//! BLAKE3 cryptographic verification receipts, and CI / PR command handlers.

use crate::db::{SingleflightOutcome, TurboStore};
use crate::lake_build::{
    are_all_project_oleans_up_to_date, compute_shard_key_with_args, detect_toolchain,
    lean_bin_from_env, load_and_split_files_cached, load_and_split_files_with_hashes_cached,
    load_project_stat_summary_cached, resolve_lake_env, resolve_or_share_lake_env,
    resolve_prebuilt_module_import, resolve_remote_lean_path, seed_project_theorem_shards,
    seed_project_theorem_shards_from_splits, stage_lake_build_outputs, FileSplitsWithCacheHits,
    SourceFileSplit,
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
    /// New `native_decide`/`bv_decide` uses the axiom allowlist admits (flagged for review).
    #[serde(default)]
    pub axiom_flags: Vec<String>,
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
    #[serde(default)]
    dep_hashes: Vec<String>,
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
    h.update(b"git-head-tree:v10:");
    h.update(repo_root.to_string_lossy().as_bytes());
    h.update(b":");
    h.update(canon_dir.to_string_lossy().as_bytes());
    h.update(b":");
    h.update(sha.as_bytes());
    h.update(b":");
    h.update(toolchain.as_bytes());
    if let Ok(pkg) = crate::module_builder::resolve_package_config(canon_dir, false) {
        if !pkg.config_digest.is_empty() {
            let pkg_args = crate::module_builder::package_default_lean_args(&pkg);
            let any_target_args = pkg.libs.iter().any(|l| {
                !l.lean_options.is_empty()
                    || !l.more_lean_args.is_empty()
                    || !l.weak_lean_args.is_empty()
            }) || pkg.exes.iter().any(|e| {
                !e.lean_options.is_empty()
                    || !e.more_lean_args.is_empty()
                    || !e.weak_lean_args.is_empty()
            });
            if !pkg_args.is_empty() || any_target_args {
                h.update(b":cfg:");
                h.update(pkg.config_digest.as_bytes());
            }
        }
    }
    let key_hex = h.finalize().to_hex();
    let short_key = &key_hex[..24];
    let staging = store.fast_staging_dir();
    (
        staging.join(format!("git_head_tree_v9_{}.json", short_key)),
        staging.join(format!("git_head_tree_stats_v9_{}.json", short_key)),
    )
}

trait BaseShardRef {
    fn name(&self) -> &str;
    fn stmt_hash(&self) -> &str;
    fn prefix_env_hash(&self) -> &str;
    fn shard_key(&self, toolchain: &str, file_lean_args: &[String]) -> std::borrow::Cow<'_, str>;
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
    fn shard_key(&self, _toolchain: &str, _file_lean_args: &[String]) -> std::borrow::Cow<'_, str> {
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
    fn shard_key(&self, toolchain: &str, file_lean_args: &[String]) -> std::borrow::Cow<'_, str> {
        std::borrow::Cow::Owned(compute_shard_key_with_args(toolchain, self, file_lean_args))
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
    axiom_flags: Vec<String>,
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
            axiom_flags: Vec::new(),
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
        file_lean_args: &[String],
        base_lean_args: &[String],
    ) {
        self.modified_files.push(rel_path.clone());
        let (reg, admitted) = cur_split.hygiene.regression_items_against(base_hygiene);
        if !reg.is_empty() {
            self.flagged_files.push((rel_path.clone(), reg));
        }
        self.axiom_flags
            .extend(admitted.into_iter().map(|i| format!("{}: {}", rel_path, i)));

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
        let options_same = file_lean_args == base_lean_args;
        let mut file_has_stmt_change = !file_interface_same || !options_same;

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
                let k = compute_shard_key_with_args(&self.toolchain, &s, file_lean_args);
                if k == bs.shard_key(&self.toolchain, base_lean_args).as_ref() {
                    self.unchanged_theorems.push(qualified);
                } else if s.stmt_hash == bs.stmt_hash()
                    && s.prefix_env_hash == bs.prefix_env_hash()
                    && file_interface_same
                    && options_same
                {
                    self.proof_edited_theorems.push(qualified);
                    file_verify_list.push((k, s, options_same));
                } else {
                    file_has_stmt_change = true;
                    self.statement_edited_theorems.push(qualified);
                    file_verify_list.push((k, s, false));
                }
            } else {
                let k = compute_shard_key_with_args(&self.toolchain, &s, file_lean_args);
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

    fn record_added(
        &mut self,
        rel_path: String,
        cur_split: splitter::SplitResult,
        file_lean_args: &[String],
    ) {
        self.modified_files.push(rel_path.clone());
        self.altered_interface_files.push(rel_path.clone());
        if !cur_split.hygiene.is_clean_for_certification() {
            self.flagged_files
                .push((rel_path.clone(), cur_split.hygiene.disallowed_items()));
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
            let k = compute_shard_key_with_args(&self.toolchain, &s, file_lean_args);
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

    // Source text cannot identify macro/scoped csimp replacements reliably. If
    // base config contains a csimp policy, defer these items to the mandatory
    // ConstantInfo/environment audit, which checks the actual theorem names.
    fn defer_csimp_to_kernel_gate(&mut self, project: &Path, base: &str) {
        if StatementPolicy::at(project, base).csimp.is_empty() {
            return;
        }
        for (file, items) in &mut self.flagged_files {
            items.retain(|item| {
                if item.rsplit(": ").next() == Some("csimp") {
                    self.axiom_flags.push(format!(
                        "{file}: {item} (requires compiled csimp policy audit)"
                    ));
                    false
                } else {
                    true
                }
            });
        }
        self.flagged_files.retain(|(_, items)| !items.is_empty());
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
                axiom_flags: self.axiom_flags,
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
    dep_hashes: Vec<String>,
    file_lean_args: &[String],
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
            shard_key: compute_shard_key_with_args(toolchain, sh, file_lean_args),
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
                let prefix_sp = split_lean_source_fast_no_cone(prefix_slice, &dep_hashes);
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
                        dep_hashes,
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
        dep_hashes,
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
    let mut prefix_sp = split_lean_source_fast_no_cone(prefix_src, &base_entry.dep_hashes);
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
    (
        split_lean_source_fast_no_cone(cur_src, &base_entry.dep_hashes),
        None,
    )
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
    if lean_paths.is_empty() || lean_paths.len() > 128 {
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
            let Ok(pkg_cfg_opt) =
                base_revision_package_config(store, &repo_root, canon_dir, "HEAD")
            else {
                return;
            };
            let entries: Vec<(String, CachedHeadFileEntry)> = std::thread::scope(|s| {
                let handles: Vec<_> = lean_paths
                    .iter()
                    .map(|p| {
                        let split_by_path_ref = &split_by_path;
                        let fetched_ref = &fetched_blobs;
                        let proj_prefix_ref = &proj_prefix;
                        let pkg_ref = pkg_cfg_opt.as_ref();
                        s.spawn(move || -> Option<(String, CachedHeadFileEntry)> {
                            let rel = rel_path_from_dir(p, canon_dir);
                            let repo_rel = join_proj_prefix(proj_prefix_ref, &rel);
                            let bs = fetched_ref.get(&repo_rel)?;
                            let dep_hashes =
                                crate::lake_build::compute_imported_olean_interface_hashes(
                                    bs, canon_dir, None,
                                );
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
                                    (
                                        std::borrow::Cow::Owned(split_lean_source(bs, &dep_hashes)),
                                        false,
                                    )
                                }
                            } else {
                                let wt_matches =
                                    fs::read_to_string(p).ok().as_deref() == Some(bs.as_str());
                                (
                                    std::borrow::Cow::Owned(split_lean_source(bs, &dep_hashes)),
                                    wt_matches,
                                )
                            };
                            let head_stat = if matches_worktree {
                                stable_file_stat_for_head(p)
                            } else {
                                None
                            };
                            let file_lean_args = pkg_ref
                                .map(|pkg| {
                                    crate::module_builder::resolve_file_lean_args_in_package(pkg, p)
                                })
                                .unwrap_or_default();
                            Some((
                                rel,
                                build_cached_head_file_entry(
                                    bs,
                                    &sp,
                                    toolchain,
                                    head_stat,
                                    dep_hashes,
                                    &file_lean_args,
                                ),
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

fn compute_source_only_import_digests(
    src: &str,
    project_dir: &Path,
    cfg_opt: Option<&crate::module_builder::ProjectConfig>,
    strict_untrusted: bool,
) -> Result<Vec<String>> {
    if project_dir.as_os_str().is_empty() && cfg_opt.is_none() {
        return Ok(Vec::new());
    }
    let hdr = crate::module_builder::parse_header_info(src);
    if let Some(err) = hdr.header_error {
        if strict_untrusted {
            anyhow::bail!(
                "Untrusted import-digest header parse failed (fail-closed): {}",
                err
            );
        }
        return Ok(Vec::new());
    }
    if hdr.imports.is_empty() {
        return Ok(Vec::new());
    }
    let mut worklist = hdr.imports;
    let mut visited = std::collections::HashSet::new();
    let mut out = Vec::new();
    while let Some(mod_name) = worklist.pop() {
        if !visited.insert(mod_name.clone()) {
            continue;
        }
        let rel_slash = crate::module_builder::module_name_to_rel_slash(&mod_name);
        let resolved_src_and_pkg: Option<(PathBuf, Option<String>)> = if let Some(cfg) = cfg_opt {
            if let Some(spec) =
                crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, &mod_name)
            {
                Some((spec.src_path, Some(spec.pkg_config_digest)))
            } else {
                let mut dep_matches = Vec::new();
                for dp in &cfg.dep_pkgs {
                    if let Some(spec) =
                        crate::module_builder::resolve_module_in_package(dp, false, &mod_name)
                    {
                        dep_matches.push(spec);
                    }
                }
                if dep_matches.len() > 1 {
                    anyhow::bail!(
                        "Ambiguous dependency import `{}` in untrusted shard digest resolution",
                        mod_name
                    );
                }
                if let Some(spec) = dep_matches.into_iter().next() {
                    Some((spec.src_path, Some(spec.pkg_config_digest)))
                } else {
                    crate::lake_build::resolve_project_lean_source(project_dir, &rel_slash)
                        .map(|p| (p, None))
                }
            }
        } else {
            crate::lake_build::resolve_project_lean_source(project_dir, &rel_slash)
                .map(|p| (p, None))
        };

        if let Some((sub_lean, pkg_digest_opt)) = resolved_src_and_pkg {
            if strict_untrusted {
                let meta = fs::symlink_metadata(&sub_lean).with_context(|| {
                    format!(
                        "Failed to stat imported Lean source `{}`",
                        sub_lean.display()
                    )
                })?;
                if meta.file_type().is_symlink() {
                    anyhow::bail!(
                        "Untrusted import digest rejected symlink source `{}`",
                        sub_lean.display()
                    );
                }
            }
            let bytes = match fs::read(&sub_lean) {
                Ok(b) => b,
                Err(e) if strict_untrusted => {
                    return Err(e).with_context(|| {
                        format!(
                            "Failed to read imported Lean source `{}`",
                            sub_lean.display()
                        )
                    });
                }
                Err(_) => continue,
            };
            let sd = blake3::hash(&bytes).to_hex().to_string();
            match pkg_digest_opt {
                Some(pd) if !pd.is_empty() => {
                    out.push(format!("{}:pkg={}:src={}", mod_name, pd, sd));
                }
                _ => {
                    out.push(format!("{}:src={}", mod_name, sd));
                }
            }
            match std::str::from_utf8(&bytes) {
                Ok(sub_str) => {
                    let sub_hdr = crate::module_builder::parse_header_info(sub_str);
                    if let Some(err) = sub_hdr.header_error {
                        if strict_untrusted {
                            anyhow::bail!(
                                "Untrusted imported module `{}` header parse failed (fail-closed): {}",
                                mod_name,
                                err
                            );
                        }
                    } else {
                        for sub_imp in sub_hdr.imports {
                            if !visited.contains(&sub_imp) {
                                worklist.push(sub_imp);
                            }
                        }
                    }
                }
                Err(e) if strict_untrusted => {
                    return Err(e).with_context(|| {
                        format!("Invalid UTF-8 in imported module `{}`", sub_lean.display())
                    });
                }
                Err(_) => {}
            }
        } else if strict_untrusted {
            let is_tc = cfg_opt
                .map(|cfg| {
                    crate::module_builder::is_builtin_toolchain_module(
                        &cfg.toolchain_lib_lean,
                        &mod_name,
                    )
                })
                .unwrap_or_else(|| {
                    crate::module_builder::is_builtin_toolchain_module(Path::new(""), &mod_name)
                });
            if !is_tc {
                anyhow::bail!(
                    "Unresolved non-toolchain import `{}` in untrusted verification (fail-closed)",
                    mod_name
                );
            }
        }
    }
    out.sort();
    Ok(out)
}

fn load_and_split_files_untrusted(
    canon_dir: &Path,
    paths: &[PathBuf],
    untrusted_cfg: Option<&crate::module_builder::ProjectConfig>,
) -> Result<FileSplitsWithCacheHits> {
    let mut out = Vec::with_capacity(paths.len());
    for p in paths {
        let meta =
            fs::symlink_metadata(p).with_context(|| format!("Failed to stat `{}`", p.display()))?;
        if meta.file_type().is_symlink() {
            anyhow::bail!(
                "Untrusted PR verification rejected symlink source `{}`",
                p.display()
            );
        }
        let bytes = fs::read(p).with_context(|| format!("Failed to read `{}`", p.display()))?;
        let src = String::from_utf8(bytes)
            .with_context(|| format!("Invalid UTF-8 in `{}`", p.display()))?;
        let dep_hashes = compute_source_only_import_digests(&src, canon_dir, untrusted_cfg, true)?;
        let sp = split_lean_source(&src, &dep_hashes);
        out.push((p.clone(), src, sp));
    }
    Ok((out, 0))
}

#[cfg(test)]
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
    load_and_classify_pr_from_git_scoped(store, canon_dir, base_ref, toolchain, None, false, None)
}

/// Parse the base revision's config without executing Lake or using worktree options.
/// The parser roots module paths at the project, while config bytes come only from Git.
fn base_revision_package_config(
    store: &TurboStore,
    repo_root: &Path,
    canon_dir: &Path,
    base_ref: &str,
) -> Result<Option<crate::module_builder::PackageConfig>> {
    let sha = match resolve_git_head_sha(repo_root, base_ref) {
        Some(sha) => sha,
        None => {
            let out = Command::new("git")
                .arg("-C")
                .arg(repo_root)
                .args(["rev-parse", "--verify", "--end-of-options"])
                .arg(format!("{base_ref}^{{commit}}"))
                .output()
                .context("Failed to resolve Git base revision")?;
            anyhow::ensure!(
                out.status.success(),
                "Invalid git base ref `{base_ref}`: {}",
                String::from_utf8_lossy(&out.stderr).trim()
            );
            String::from_utf8(out.stdout)?.trim().to_string()
        }
    };
    let prefix = rel_path_from_dir(canon_dir, repo_root);
    let paths: Vec<_> = ["lakefile.toml", "lakefile.lean"]
        .iter()
        .map(|name| join_proj_prefix(&prefix, name))
        .collect();
    let mut blobs = fetch_git_blobs_batch(repo_root, &sha, &paths)?;
    for (index, path) in paths.iter().enumerate() {
        if let Some(raw) = blobs.remove(path) {
            let staged = store.fast_staging_dir().join(format!(
                "base-lakefile-{}-{}",
                std::process::id(),
                crate::pack::next_tmp_id()
            ));
            fs::write(&staged, raw)?;
            let result = if index == 0 {
                crate::module_builder::parse_lakefile_toml(canon_dir, &staged, false)
            } else {
                crate::module_builder::parse_lakefile_lean(canon_dir, &staged, false)
            };
            let _ = fs::remove_file(&staged);
            return result
                .with_context(|| {
                    format!("Failed to resolve base Lean options at {base_ref}:{path}")
                })
                .map(Some);
        }
    }
    Ok(None)
}

pub(crate) fn load_and_classify_pr_from_git_scoped(
    store: &TurboStore,
    canon_dir: &Path,
    base_ref: &str,
    toolchain: &str,
    scope: Option<&Path>,
    is_untrusted: bool,
    untrusted_cfg: Option<&crate::module_builder::ProjectConfig>,
) -> Result<(
    PrClassification,
    std::collections::BTreeMap<String, Vec<(String, splitter::TheoremShard, bool)>>,
    std::collections::BTreeMap<String, String>,
    std::collections::BTreeMap<String, splitter::SplitResult>,
)> {
    let repo_root = resolve_git_toplevel(canon_dir)?;
    let proj_prefix = rel_path_from_dir(canon_dir, &repo_root);

    let lean_paths = crate::lake_build::collect_project_lean_files(canon_dir, true, scope);
    let owned_pkg_cfg = if untrusted_cfg.is_some() {
        None
    } else {
        crate::module_builder::optional_package_config(canon_dir)?
    };
    let base_pkg_cfg = base_revision_package_config(store, &repo_root, canon_dir, base_ref)?;
    let resolve_base_lean_args = |rel: &str| -> Vec<String> {
        base_pkg_cfg
            .as_ref()
            .map(|pkg| {
                crate::module_builder::resolve_file_lean_args_in_package(pkg, &canon_dir.join(rel))
            })
            .unwrap_or_default()
    };
    let resolve_rel_lean_args = |rel: &str| -> Vec<String> {
        let abs = canon_dir.join(rel);
        if let Some(cfg) = untrusted_cfg {
            crate::module_builder::resolve_file_lean_args_in_package(&cfg.root_pkg, &abs)
        } else if let Some(ref pkg) = owned_pkg_cfg {
            crate::module_builder::resolve_file_lean_args_in_package(pkg, &abs)
        } else {
            Vec::new()
        }
    };

    let option_changed_paths: std::collections::HashSet<String> = lean_paths
        .iter()
        .map(|p| rel_path_from_dir(p, canon_dir))
        .filter(|rel| {
            rel != "lakefile.lean" && resolve_rel_lean_args(rel) != resolve_base_lean_args(rel)
        })
        .collect();

    enum PrFileEntry {
        Unchanged(splitter::SplitResult),
        Changed {
            base_src: Option<String>,
            cur_src: Option<String>,
            cur_split: Option<splitter::SplitResult>,
        },
    }

    let head_sha_opt = resolve_git_head_sha(&repo_root, base_ref);
    let head_tree_cache_file = if is_untrusted || !option_changed_paths.is_empty() {
        None
    } else {
        head_sha_opt
            .as_ref()
            .map(|sha| git_head_tree_cache_paths(store, &repo_root, canon_dir, sha, toolchain).0)
    };

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
                                let file_lean_args = resolve_rel_lean_args(&rel_path);
                                let base_lean_args = resolve_base_lean_args(&rel_path);
                                changed_current_splits.insert(rel_path.clone(), cur_split.clone());
                                accum.record_modified(
                                    rel_path,
                                    &base_entry.interface_hash,
                                    &base_entry.hygiene,
                                    &base_entry.shards,
                                    cur_split,
                                    &file_lean_args,
                                    &base_lean_args,
                                );
                            }
                        }
                    }

                    accum.defer_csimp_to_kernel_gate(canon_dir, base_ref);
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
            let blobs_h = if all_rels_ref.len() <= 128 && !all_rels_ref.is_empty() {
                Some(s.spawn(move || fetch_git_blobs_batch(repo_ref, "HEAD", all_rels_ref)))
            } else {
                None
            };

            let preloaded = if is_untrusted {
                load_and_split_files_untrusted(canon_dir, &lean_paths, untrusted_cfg)
            } else {
                load_and_split_files_cached(store, &lean_paths)
            };
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

            let preloaded = if is_untrusted {
                load_and_split_files_untrusted(canon_dir, &lean_paths, untrusted_cfg)
            } else {
                load_and_split_files_cached(store, &lean_paths)
            };
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
    changed_repo_paths.extend(
        option_changed_paths
            .iter()
            .map(|rel| join_proj_prefix(&proj_prefix, rel)),
    );

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
                    let dep_hashes = crate::lake_build::compute_imported_olean_interface_hashes(
                        bs, canon_dir, None,
                    );
                    let sp = split_lean_source(bs, &dep_hashes);
                    let head_stat = if !changed_repo_paths.contains(&repo_rel) {
                        stable_file_stat_for_head(p)
                    } else {
                        None
                    };
                    let file_lean_args = resolve_base_lean_args(&rel);
                    rel_blob_map.insert(
                        rel,
                        build_cached_head_file_entry(
                            bs,
                            &sp,
                            toolchain,
                            head_stat,
                            dep_hashes,
                            &file_lean_args,
                        ),
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
    if !is_untrusted {
        for entry in entries_by_rel_path.values() {
            if let PrFileEntry::Changed {
                base_src: Some(ref bs),
                ..
            } = entry
            {
                let dep_hashes =
                    crate::lake_build::compute_imported_olean_interface_hashes(bs, canon_dir, None);
                let sb = blake3::hash(bs.as_bytes()).to_hex().to_string();
                base_split_keys.push(crate::lake_build::compute_file_split_key_with_deps(
                    &sb,
                    &dep_hashes,
                ));
            }
        }
    }
    let mut cached_base_splits = if !base_split_keys.is_empty() {
        store
            .batch_get_file_splits(&base_split_keys)
            .unwrap_or_default()
    } else {
        std::collections::HashMap::new()
    };

    let mut resolve_cached_or_split =
        |src: &str, strict_untrusted_imports: bool| -> Result<splitter::SplitResult> {
            if is_untrusted {
                let dep_hashes = compute_source_only_import_digests(
                    src,
                    canon_dir,
                    untrusted_cfg,
                    strict_untrusted_imports,
                )?;
                return Ok(split_lean_source(src, &dep_hashes));
            }
            let dep_hashes =
                crate::lake_build::compute_imported_olean_interface_hashes(src, canon_dir, None);
            let sb = blake3::hash(src.as_bytes()).to_hex().to_string();
            let fk = crate::lake_build::compute_file_split_key_with_deps(&sb, &dep_hashes);
            if let Some(sp) = cached_base_splits.remove(&fk) {
                return Ok(sp);
            }
            if let Ok(mut map) = store.batch_get_file_splits(std::slice::from_ref(&fk)) {
                if let Some(sp) = map.remove(&fk) {
                    return Ok(sp);
                }
            }
            let sp = split_lean_source(src, &dep_hashes);
            let _ = store.batch_put_file_splits(&[(fk, &sp)]);
            Ok(sp)
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
            } if base_src == cur_src && !option_changed_paths.contains(&rel_path) => {
                let split = match cur_split {
                    Some(sp) => sp,
                    None => resolve_cached_or_split(&cur_src, true)?,
                };
                accum.record_unchanged(rel_path, split.interface_hash, &split.shards);
            }
            PrFileEntry::Changed {
                base_src: Some(base_src),
                cur_src: Some(cur_src),
                cur_split,
            } => {
                let file_lean_args = resolve_rel_lean_args(&rel_path);
                let base_lean_args = resolve_base_lean_args(&rel_path);
                let cur_split = match cur_split {
                    Some(sp) => sp,
                    None => resolve_cached_or_split(&cur_src, true)?,
                };
                changed_current_splits.insert(rel_path.clone(), cur_split.clone());
                let base_split = resolve_cached_or_split(&base_src, false)?;
                accum.record_modified(
                    rel_path,
                    &base_split.interface_hash,
                    &base_split.hygiene,
                    &base_split.shards,
                    cur_split,
                    &file_lean_args,
                    &base_lean_args,
                );
            }
            PrFileEntry::Changed {
                base_src: None,
                cur_src: Some(cur_src),
                cur_split,
            } => {
                let file_lean_args = resolve_rel_lean_args(&rel_path);
                let cur_split = match cur_split {
                    Some(sp) => sp,
                    None => resolve_cached_or_split(&cur_src, true)?,
                };
                changed_current_splits.insert(rel_path.clone(), cur_split.clone());
                accum.record_added(rel_path, cur_split, &file_lean_args);
            }
            PrFileEntry::Changed {
                base_src: Some(base_src),
                cur_src: None,
                cur_split: _,
            } => {
                let base_split = resolve_cached_or_split(&base_src, false)?;
                accum.record_deleted(rel_path, &base_split.interface_hash, &base_split.shards);
            }
            PrFileEntry::Changed {
                base_src: None,
                cur_src: None,
                cur_split: _,
            } => {}
        }
    }

    accum.defer_csimp_to_kernel_gate(canon_dir, base_ref);
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
                    &[],
                    &[],
                );
            }
            (None, Some(cur_src)) => {
                accum.record_added(rel_path, split_lean_source(cur_src, &[]), &[])
            }
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
    lean_args: Vec<String>,
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
        allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
        lean_args,
    }
}

fn resolve_untrusted_pr_project_config(
    canon_dir: &Path,
    toolchain: &str,
) -> Result<crate::module_builder::ProjectConfig> {
    if canon_dir.join("lakefile.toml").is_file() || canon_dir.join("lakefile.lean").is_file() {
        return crate::module_builder::resolve_project_config_with_trust(canon_dir, true);
    }
    let (lean_bin, lean_githash, toolchain_lib_lean, toolchain_lib) =
        crate::module_builder::resolve_toolchain_compiler_with_trust(canon_dir, toolchain, true)?;
    let pkg_name = canon_dir
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "pr-project".to_string());
    let root_pkg = crate::module_builder::PackageConfig {
        name: pkg_name,
        pkg_root: canon_dir.to_path_buf(),
        config_file_kind: "bare".to_string(),
        src_dir: PathBuf::new(),
        build_dir: PathBuf::from(".lake/build"),
        lean_lib_dir: PathBuf::from("lib/lean"),
        ir_dir: PathBuf::from("ir"),
        packages_dir: PathBuf::from(".lake/packages"),
        more_lean_args: Vec::new(),
        weak_lean_args: Vec::new(),
        lean_options: BTreeMap::new(),
        precompile_modules: false,
        default_targets: Vec::new(),
        libs: Vec::new(),
        exes: Vec::new(),
        extern_libs: Vec::new(),
        custom_targets: Vec::new(),
        config_digest: String::new(),
    };
    Ok(crate::module_builder::ProjectConfig {
        toolchain: toolchain.to_string(),
        lean_bin,
        lean_githash,
        toolchain_lib_lean,
        toolchain_lib,
        root_pkg,
        manifest_packages: Vec::new(),
        dep_pkgs: Vec::new(),
        canonical_config_digest: String::new(),
    })
}

struct PrVerificationTrust<'a> {
    is_untrusted: bool,
    untrusted_cfg: Option<&'a crate::module_builder::ProjectConfig>,
}

/// Kernel-audited fallback for a shard the zygote could not check (`run_audited_lean_shard`,
/// sandboxed with a compiled-module audit in untrusted mode). A zygote rejection never reaches it.
#[allow(clippy::too_many_arguments)]
fn run_lean_temp_file(
    store: &TurboStore,
    lean_bin: &str,
    src: &str,
    canon_dir: &Path,
    env_vars: &std::collections::HashMap<String, String>,
    trust: &PrVerificationTrust<'_>,
    audit: &std::collections::HashSet<String>,
    lean_args: &[String],
) -> Result<std::process::Output> {
    if trust.is_untrusted {
        let cfg = trust.untrusted_cfg.ok_or_else(|| {
            anyhow::anyhow!(
                "Untrusted PR shard verification requires a resolved static ProjectConfig: fail-closed sandbox gate"
            )
        })?;
        let bwrap_path = crate::module_builder::probe_bwrap_sandbox().ok_or_else(|| {
            anyhow::anyhow!(
                "Untrusted PR shard verification requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
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
        let pid = std::process::id();
        let seq = pack::next_tmp_id();
        let build_root = cfg.root_pkg.pkg_root.join(".lake/build");
        fs::create_dir_all(&build_root)?;
        let tmp_dir = build_root.join(format!(".turbo_pr_tmp_{}_{}", pid, seq));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(&tmp_dir)?;
        struct PrTempDirGuard(PathBuf);
        impl Drop for PrTempDirGuard {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let _tmp_guard = PrTempDirGuard(tmp_dir.clone());
        let mod_name = format!("TurboPrShard_{}_{}", pid, seq);
        let sandbox_lean = tmp_dir.join(format!("{}.lean", mod_name));
        let sandbox_olean = tmp_dir.join(format!("{}.olean", mod_name));
        fs::write(&sandbox_lean, src.as_bytes())?;

        let (base_lp, ld_library_path_env) =
            crate::module_builder::build_lean_search_path(cfg, true);
        let lean_path_env = if base_lp.is_empty() {
            tmp_dir.to_string_lossy().to_string()
        } else {
            format!("{}:{}", tmp_dir.display(), base_lp)
        };
        crate::module_builder::validate_untrusted_sandbox_search_paths(
            cfg,
            tc_prefix,
            &lean_path_env,
            &ld_library_path_env,
        )?;

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
            &lean_path_env,
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
        cmd.arg("--bind").arg(&tmp_dir).arg(&tmp_dir);
        cmd.arg("--chdir").arg(&cfg.root_pkg.pkg_root);
        cmd.arg(&cfg.lean_bin);
        crate::module_builder::scrub_untrusted_env(&mut cmd);
        cmd.args(["-M", "4096"]);
        // The owning target's flags (the same ones the shard key digests), already in Lake's
        // weakLeanArgs < moreLeanArgs < leanOptions order; the hardening flags come last to win.
        for arg in crate::module_builder::filter_allowed_lean_args(lean_args) {
            cmd.arg(arg);
        }
        cmd.arg("-Dwarn.sorry=true")
            .arg("-Ddebug.skipKernelTC=false")
            .arg(&sandbox_lean)
            .arg("-R")
            .arg(&tmp_dir)
            .arg("-o")
            .arg(&sandbox_olean);

        let out = crate::module_builder::run_command_with_timeout(
            &mut cmd,
            std::time::Duration::from_secs(120),
            true,
        )?;
        if !out.status.success() {
            return Ok(out);
        }
        let stdout_str = String::from_utf8_lossy(&out.stdout);
        let stderr_str = String::from_utf8_lossy(&out.stderr);
        // Match the prefix: `pp.*` options change how the `sorry` term itself prints.
        if stdout_str.contains("declaration uses ") || stderr_str.contains("declaration uses ") {
            anyhow::bail!(
                "Untrusted PR shard verification rejected `{}` due to `sorry` axiom usage",
                mod_name
            );
        }
        let olean_meta = fs::symlink_metadata(&sandbox_olean).with_context(|| {
            format!(
                "Untrusted PR shard compilation produced no `.olean` at `{}`",
                sandbox_olean.display()
            )
        })?;
        if olean_meta.file_type().is_symlink()
            || !olean_meta.file_type().is_file()
            || olean_meta.len() == 0
        {
            anyhow::bail!(
                "Untrusted PR shard `.olean` `{}` is missing, empty, or a symlink",
                sandbox_olean.display()
            );
        }
        crate::zygote::audit_compiled_modules_with_zygote(
            store,
            cfg,
            std::slice::from_ref(&mod_name),
            &lean_path_env,
            &[],
            true,
        )?;
        return Ok(out);
    }

    crate::zygote::run_audited_lean_shard(
        store,
        Path::new(lean_bin),
        env_vars,
        Some(canon_dir),
        src,
        audit,
        lean_args,
        None,
    )
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
#[allow(clippy::too_many_arguments)]
pub fn run_ci_verify_command(
    store: &mut TurboStore,
    json: bool,
    mode: String,
    project_dir: PathBuf,
    receipt: Option<PathBuf>,
    signing_key: Option<String>,
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

    if is_untrusted && crate::module_builder::probe_bwrap_sandbox().is_none() {
        anyhow::bail!(
            "Untrusted CI verification requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
        );
    }
    // Validate every package before any action lookup. The canonical digest binds
    // effective options and lakefile contents, including dependency configuration.
    let cfg = crate::module_builder::resolve_project_config_with_trust(&canon_dir, is_untrusted)
        .context("CI static Lake config validation failed")?;
    let untrusted_ci_mods = if is_untrusted {
        let dag = crate::module_builder::build_module_dag_with_trust(&cfg, &[], true)
            .context("Untrusted CI static module DAG validation failed")?;
        Some(dag.nodes.keys().cloned().collect::<Vec<String>>())
    } else {
        None
    };

    let mut flagged_files = Vec::new();
    let mut total_files = 0usize;
    let mut total_shards = 0usize;
    let mut per_file_interfaces = BTreeMap::new();
    let lean_paths =
        crate::lake_build::collect_project_lean_files(&canon_dir, true, scope.as_deref());
    let toolchain = detect_toolchain(&canon_dir);
    let ci_axioms = splitter::allowed_axioms();
    let mut hasher = blake3::Hasher::new();
    hasher.update(
        format!(
            "turbo-lean-ci-build-v2\n{}\n{}\n{}\n",
            toolchain, trust_domain, cfg.canonical_config_digest
        )
        .as_bytes(),
    );
    if ci_axioms.len() > splitter::STANDARD_AXIOMS.len() {
        hasher.update(b":axioms:");
        hasher.update(ci_axioms.join(",").as_bytes());
        hasher.update(b"\n");
    }

    let mut interface_hasher = blake3::Hasher::new();
    interface_hasher.update(toolchain.as_bytes());

    let mut file_hashes = BTreeMap::new();
    let mut full_splits_opt: Option<Vec<SourceFileSplit>> = None;

    if !seed_shards && !is_untrusted {
        if let Ok(summary) = load_project_stat_summary_cached(store, &canon_dir, &lean_paths) {
            total_files = summary.total_files;
            total_shards = summary.total_shards;
            flagged_files = summary
                .flagged_files
                .into_iter()
                .map(|(f, items)| (f, splitter::blocking_items(&items)))
                .filter(|(_, items)| !items.is_empty())
                .collect();
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
        let splits_with_hashes: Vec<(PathBuf, String, String, splitter::SplitResult)> =
            if is_untrusted {
                let mut rows = Vec::with_capacity(lean_paths.len());
                for p in &lean_paths {
                    let meta = fs::symlink_metadata(p)?;
                    if meta.file_type().is_symlink() {
                        anyhow::bail!(
                            "Untrusted CI verification rejected symlink source `{}`",
                            p.display()
                        );
                    }
                    let src = fs::read_to_string(p)?;
                    let src_blake3 = blake3::hash(src.as_bytes()).to_hex().to_string();
                    let dep_hashes =
                        compute_source_only_import_digests(&src, &canon_dir, Some(&cfg), true)?;
                    let split = split_lean_source(&src, &dep_hashes);
                    rows.push((p.clone(), src_blake3, src, split));
                }
                rows
            } else {
                load_and_split_files_with_hashes_cached(store, &lean_paths)?.0
            };
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
                flagged_files.push((rel_path, split.hygiene.disallowed_items()));
            }
            splits.push((path, src, split));
        }
        full_splits_opt = Some(splits);
    }

    // Untrusted CI always audits compiled modules, including restored artifacts.
    // Only an explicit caller policy can defer source csimp flags to that gate.
    if is_untrusted && std::env::var("TURBO_LEAN_ALLOWED_CSIMP").is_ok_and(|s| !s.trim().is_empty())
    {
        for (_, items) in &mut flagged_files {
            items.retain(|item| item.rsplit(": ").next() != Some("csimp"));
        }
        flagged_files.retain(|(_, items)| !items.is_empty());
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

    // Cached outputs (including singleflight) and existing oleans carry no
    // sandbox attestation. Report unknown rather than claiming an unsandboxed
    // build; the trust domain alone is not evidence of sandbox execution.
    let mut bwrap_used: Option<bool> = None;

    let audit_untrusted_materialized = |store_ref: &TurboStore| -> Result<()> {
        if let Some(ref mod_names) = untrusted_ci_mods {
            if !mod_names.is_empty() {
                let (lp, _ldp) = crate::module_builder::build_lean_search_path(&cfg, true);
                if let Err(err) = crate::zygote::audit_compiled_modules_with_zygote(
                    store_ref,
                    &cfg,
                    mod_names,
                    &lp,
                    &[],
                    true,
                ) {
                    if !crate::lake_build::worktree_auto_link_disabled(&canon_dir) {
                        let _ = fs::remove_dir_all(canon_dir.join(".lake/build"));
                    }
                    return Err(err);
                }
            }
        }
        Ok(())
    };

    let (build_status, _resolved_env_opt) = if let Some(outputs) =
        store.get_cached_action(&action_key, &trust_domain)?
    {
        store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
        audit_untrusted_materialized(store)?;
        store.record_attestation(
            &action_key,
            "turbo-lean-ci-gate",
            env!("CARGO_PKG_VERSION"),
            &ci_axioms,
            None,
        )?;
        let resolved_env = if !is_untrusted && !crate::zygote::daemon_disabled() {
            resolve_lake_env(store, &canon_dir).ok()
        } else {
            None
        };
        ("cache_hit(coalesced=false)".to_string(), resolved_env)
    } else {
        let oleans_up_to_date =
            !is_untrusted && are_all_project_oleans_up_to_date(&canon_dir, &file_hashes);
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
                    audit_untrusted_materialized(store)?;
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
                bwrap_used = Some(build_rep.bwrap_used);
            }

            let env_key = TurboStore::compute_lake_env_key(&canon_dir);
            let resolved_env = if is_untrusted {
                None
            } else if !crate::zygote::daemon_disabled() {
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

    if !is_untrusted {
        warm_git_head_tree_cache(
            store,
            &canon_dir,
            &lean_paths,
            &toolchain,
            full_splits_opt.as_deref(),
        );
    }

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

    let mut ver_receipt = build_verification_receipt(
        &mode,
        &interface_hash,
        &action_key,
        total_files,
        total_shards,
        0,
        per_file_interfaces,
    );
    emit_verification_receipt_with_signing_key(
        receipt.as_deref(),
        &mut ver_receipt,
        signing_key.as_deref(),
    )?;

    let elapsed_ms = t0.elapsed().as_millis();
    crate::mcp::emit_cli_telemetry_event(
        Some(&canon_dir),
        !is_untrusted,
        serde_json::json!({
            "schema": "turbo-lean.telemetry.v1",
            "tool_name": "ci_verify",
            "command": "ci-verify",
            "decl_name": project_name,
            "status": "ci_verified",
            "mode": mode,
            "trust_domain": trust_domain,
            "env_scrubbed": is_untrusted,
            "bwrap_net_isolated": bwrap_used,
            "bwrap_sandbox_used": bwrap_used,
            "build_status": build_status,
            "cache_hit": build_status.starts_with("cache_hit"),
            "accepted": true,
            "action_key": action_key,
            "interface_hash": interface_hash,
            "receipt_blake3": ver_receipt.receipt_blake3,
            "files_audited": total_files,
            "files_checked": total_files,
            "theorem_shards": total_shards,
            "shards_seeded": seeded_shards,
            "zero_sorry": true,
            "zero_native_decide": !splitter::native_decide_allowed(),
            "elapsed_ms": elapsed_ms,
        }),
        "turbo_lean_events.jsonl",
    );
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
                "zero_native_decide": !splitter::native_decide_allowed(),
                "allowed_axioms": splitter::allowed_axioms(),
                "elapsed_ms": elapsed_ms
            }))?
        );
    } else {
        println!(
            "[turbo-lean] CI-VERIFY PASSED (mode={}, env_scrubbed={}, status={}, {} files, {} theorems, receipt_blake3={}.., {} ms)",
            mode, is_untrusted, build_status, total_files, total_shards, &ver_receipt.receipt_blake3[..12], elapsed_ms
        );
    }
    if !is_untrusted && !crate::zygote::daemon_disabled() {
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

/// Statement digests are deliberately separate from source shard/cache keys. They
/// classify reports only: none of these hashes grant a kernel-check cache hit.
#[derive(Debug, Clone, serde::Deserialize)]
struct KernelConstant {
    #[serde(skip)]
    interface: String,
    deps: Vec<String>,
}

#[derive(Debug, Clone, serde::Deserialize)]
struct KernelTheorem {
    #[serde(skip)]
    statement: String,
    deps: Vec<String>,
}

#[derive(Debug, Clone, serde::Deserialize)]
struct KernelAudit {
    audit: String,
    axioms: Vec<String>,
}

#[derive(Default)]
struct KernelStatementReport {
    statements: BTreeMap<String, String>,
    audits: Vec<KernelAudit>,
    csimp: Vec<String>,
}

struct StatementPolicy {
    axioms: Vec<String>,
    csimp: Vec<String>,
}

impl StatementPolicy {
    fn at(project: &Path, base: &str) -> Self {
        let config = splitter::read_project_config(project, Some(base)).unwrap_or_default();
        Self {
            axioms: splitter::allowed_axioms_with_extra(
                &crate::accelerators::toml_string_array(&config, "axioms", "allow")
                    .unwrap_or_default(),
            ),
            csimp: crate::accelerators::toml_string_array(&config, "csimp", "allow")
                .unwrap_or_default(),
        }
    }

    fn audit(&self, report: &KernelStatementReport) -> Result<()> {
        for row in &report.audits {
            for axiom in &row.axioms {
                anyhow::ensure!(splitter::axiom_allowed_under(axiom, &self.axioms),
                    "[TurboLean.KernelGate] declaration `{}` depends on disallowed axiom `{axiom}` (policy resolved at --base)", row.audit);
            }
        }
        for theorem in &report.csimp {
            anyhow::ensure!(splitter::axiom_allowed_under(theorem, &self.csimp),
                "[TurboLean.KernelGate] csimp replacement `{theorem}` requires [csimp] allow in turbo-lean.toml at --base");
        }
        Ok(())
    }
}

// Deserialize only routing metadata. Payload numbers may exceed even f64's range.
#[derive(serde::Deserialize)]
struct KernelDumpRow {
    constant: Option<String>,
    theorem: Option<String>,
    audit: Option<String>,
    module: Option<String>,
    complete: Option<bool>,
    csimp: Option<Vec<String>>,
}

// Borrow the exact JSON value emitted by Lean. IgnoredAny scans the value without
// converting numeric tokens to f64 (or imposing any machine-integer bound).
fn raw_statement_payload<'a>(line: &'a str, field: &str) -> Result<&'a str> {
    let mut rest = line.trim_start().strip_prefix('{').context("Expected JSON object")?;
    loop {
        rest = rest.trim_start();
        let mut keys = serde_json::Deserializer::from_str(rest).into_iter::<String>();
        let key = keys.next().context("Missing JSON key")??;
        rest = rest[keys.byte_offset()..].trim_start()
            .strip_prefix(':').context("Missing JSON colon")?.trim_start();
        let mut values = serde_json::Deserializer::from_str(rest)
            .into_iter::<serde::de::IgnoredAny>();
        values.next().context("Missing JSON value")??;
        let end = values.byte_offset();
        if key == field {
            return Ok(&rest[..end]);
        }
        rest = rest[end..].trim_start().strip_prefix(',')
            .with_context(|| format!("Missing kernel statement payload {field}"))?;
    }
}

fn parse_kernel_statement_dump(raw: &[u8], module: &str) -> Result<BTreeMap<String, String>> {
    let mut constants = BTreeMap::<String, KernelConstant>::new();
    let mut theorems = BTreeMap::<String, KernelTheorem>::new();
    let mut complete = false;
    for line in std::str::from_utf8(raw)
        .context("Non-UTF8 kernel statement dump")?
        .lines()
        .filter(|l| !l.is_empty())
    {
        anyhow::ensure!(!complete, "Kernel statement rows after module completion");
        let row: KernelDumpRow =
            serde_json::from_str(line).context("Invalid kernel statement dump (expected JSONL)")?;
        if let Some(name) = row.constant.as_deref() {
            let mut constant: KernelConstant = serde_json::from_str(line)?;
            constant.interface = raw_statement_payload(line, "interface")?.to_owned();
            anyhow::ensure!(
                constants
                    .insert(name.to_string(), constant)
                    .is_none(),
                "Duplicate constant in kernel statement dump: {name}"
            );
        } else if let Some(name) = row.theorem.as_deref() {
            let mut theorem: KernelTheorem = serde_json::from_str(line)?;
            theorem.statement = raw_statement_payload(line, "statement")?.to_owned();
            anyhow::ensure!(
                theorems
                    .insert(name.to_string(), theorem)
                    .is_none(),
                "Duplicate theorem in kernel statement dump: {name}"
            );
        } else if row.audit.is_some() {
            let _: KernelAudit = serde_json::from_str(line)?;
        } else {
            anyhow::ensure!(
                row.module.as_deref() == Some(module)
                    && row.complete == Some(true)
                    && !complete,
                "Incomplete or unexpected kernel statement dump for {module}"
            );
            complete = true;
        }
    }
    anyhow::ensure!(complete, "Missing kernel statement dump for {module}");
    let constant_hashes: BTreeMap<_, _> = constants
        .iter()
        .map(|(name, constant)| (name.clone(), blake3::hash(constant.interface.as_bytes())))
        .collect();
    let mut result = BTreeMap::new();
    for (name, theorem) in theorems {
        let mut pending = theorem.deps;
        let mut closure = std::collections::BTreeSet::new();
        while let Some(dep) = pending.pop() {
            if !closure.insert(dep.clone()) {
                continue;
            }
            let constant = constants
                .get(&dep)
                .with_context(|| format!("Missing IF-closure constant {dep} for {name}"))?;
            pending.extend(constant.deps.iter().cloned());
        }
        // Flat, name-sorted closure records handle mutual recursion without an
        // order-sensitive DFS hash or a cycle sentinel that could hide a change.
        let mut closure_hash = blake3::Hasher::new();
        closure_hash.update(b"turbo-lean:statement-if-closure:v1\0");
        for dep in closure {
            closure_hash.update(&(dep.len() as u64).to_le_bytes());
            closure_hash.update(dep.as_bytes());
            closure_hash.update(constant_hashes[&dep].as_bytes());
        }
        let type_hash = blake3::hash(theorem.statement.as_bytes());
        let mut digest = blake3::Hasher::new();
        digest.update(b"turbo-lean:kernel-statement:v1\0");
        digest.update(type_hash.as_bytes());
        digest.update(closure_hash.finalize().as_bytes());
        result.insert(name, digest.finalize().to_hex().to_string());
    }
    Ok(result)
}

struct StatementWorktree {
    repo: PathBuf,
    path: PathBuf,
}

impl StatementWorktree {
    fn at(repo: &Path, rev: &str) -> Result<Self> {
        let path = std::env::temp_dir().join(format!(
            "turbo-statements-{}-{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let out = Command::new("git")
            .arg("-C")
            .arg(repo)
            .args(["worktree", "add", "--detach", "--force"])
            .arg(&path)
            .arg(rev)
            .output()?;
        anyhow::ensure!(
            out.status.success(),
            "Cannot create statement baseline worktree: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        Ok(Self {
            repo: repo.to_path_buf(),
            path,
        })
    }
}

impl Drop for StatementWorktree {
    fn drop(&mut self) {
        let _ = Command::new("git")
            .arg("-C")
            .arg(&self.repo)
            .args(["worktree", "remove", "--force"])
            .arg(&self.path)
            .output();
    }
}

// Stock toolchain commands run inside bwrap for untrusted inputs. The Lake configuration
// and any build scripts are untrusted executable code; no host environment or
// network is inherited. The writable root is a disposable source snapshot.
fn statement_lake_command(project: &Path, is_untrusted: bool) -> Result<Command> {
    statement_toolchain_command(project, is_untrusted, "lake", None)
}

pub(crate) fn statement_lean_command(project: &Path, is_untrusted: bool) -> Result<Command> {
    // Static package paths only: never ask project code to supply PATH/LEAN_PATH.
    let cfg = crate::module_builder::resolve_project_config_with_trust(project, true)?;
    let (lean_path, _) = crate::module_builder::build_lean_search_path(&cfg, true);
    statement_toolchain_command(project, is_untrusted, "lean", Some(&lean_path))
}

fn statement_toolchain_command(
    project: &Path,
    is_untrusted: bool,
    tool: &str,
    lean_path: Option<&str>,
) -> Result<Command> {
    let (lean, _, _, lib) = crate::module_builder::resolve_toolchain_compiler_with_trust(
        project,
        &detect_toolchain(project),
        true, // Resolve installed toolchains only, even for trusted statement builds.
    )?;
    let executable = lean.with_file_name(tool);
    if !is_untrusted {
        let mut command = Command::new(&executable);
        command
            .current_dir(project)
            .env_remove("LEAN_PATH")
            .env_remove("LEAN_SRC_PATH")
            .env(
                "LEAN_STACK_SIZE_KB",
                std::env::var("LEAN_STACK_SIZE_KB").unwrap_or_else(|_| "262144".into()),
            );
        if let Some(path) = lean_path {
            command.env("LEAN_PATH", path);
        }
        return Ok(command);
    }
    let bwrap = crate::module_builder::probe_bwrap_sandbox()
        .context("Kernel statement builds require a working bubblewrap sandbox")?;
    let prefix = lib.parent().context("Missing stock toolchain prefix")?;
    let mut command = Command::new(bwrap);
    command
        .args([
            "--unshare-all",
            "--new-session",
            "--die-with-parent",
            "--clearenv",
            "--setenv",
            "HOME",
            "/tmp",
            "--setenv",
            "LEAN_NUM_THREADS",
            "4",
            "--setenv",
            "LEAN_STACK_SIZE_KB",
            "262144",
            "--setenv",
            "PATH",
        ])
        .arg(format!(
            "{}:/usr/bin:/bin",
            lean.parent().context("Missing toolchain bin")?.display()
        ))
        .args(["--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp"]);
    for path in [
        "/usr",
        "/bin",
        "/lib",
        "/lib64",
        "/etc/alternatives",
        "/etc/ld.so.cache",
        "/etc/localtime",
    ] {
        command.args(["--ro-bind-try", path, path]);
    }
    if let Some(path) = lean_path {
        command.args(["--setenv", "LEAN_PATH", path]);
    }
    command
        .arg("--ro-bind")
        .arg(prefix)
        .arg(prefix)
        .arg("--bind")
        .arg(project)
        .arg(project)
        .arg("--chdir")
        .arg(project)
        .arg(executable);
    Ok(command)
}

fn ensure_statement_snapshot_path(root: &Path, target: &Path) -> Result<()> {
    let mut path = root.to_path_buf();
    for part in target.strip_prefix(root)?.components() {
        anyhow::ensure!(
            matches!(part, std::path::Component::Normal(_)),
            "Invalid statement snapshot path"
        );
        path.push(part);
        anyhow::ensure!(
            !path.is_symlink(),
            "Symlink in statement snapshot output path: {}",
            path.display()
        );
    }
    Ok(())
}

// Overlay only Git's tracked/unignored source files on a clean HEAD snapshot.
// Never bring across .olean files, traces, or native build products from head.
fn overlay_statement_sources(repo: &Path, snapshot: &Path) -> Result<()> {
    let out = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args([
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
        ])
        .output()?;
    anyhow::ensure!(
        out.status.success(),
        "Cannot enumerate head statement sources"
    );
    for entry in out.stdout.split(|&b| b == 0).filter(|e| !e.is_empty()) {
        let rel = Path::new(std::str::from_utf8(entry)?);
        if rel.components().any(|c| c.as_os_str() == ".lake") {
            continue;
        }
        anyhow::ensure!(
            !rel.is_absolute()
                && !rel
                    .components()
                    .any(|c| matches!(c, std::path::Component::ParentDir)),
            "Invalid Git source path in statement snapshot"
        );
        let source = repo.join(rel);
        let target = snapshot.join(rel);
        ensure_statement_snapshot_path(snapshot, &target)?;
        if !source.exists() {
            if target.is_file() {
                fs::remove_file(target)?;
            }
            continue;
        }
        let meta = fs::symlink_metadata(&source)?;
        anyhow::ensure!(
            meta.is_file() && !meta.file_type().is_symlink(),
            "Statement snapshots require regular source files: {}",
            source.display()
        );
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::copy(source, target)?;
    }
    Ok(())
}

fn clear_untrusted_statement_build_products(project: &Path) -> Result<()> {
    let pkg = crate::module_builder::resolve_package_config(project, true)?;
    for output in [project.join(".lake"), project.join(&pkg.build_dir)] {
        anyhow::ensure!(
            output != project && output.starts_with(project),
            "Statement build directory must be inside its snapshot"
        );
        ensure_statement_snapshot_path(project, &output)?;
        if output.is_dir() {
            fs::remove_dir_all(output)?;
        }
    }
    Ok(())
}

// Seed an offline sandbox with independent Git clones of already resolved
// dependencies, never with shared/hard-linked worktree build outputs.
fn seed_statement_dependencies(
    project: &Path,
    cfg: &crate::module_builder::ProjectConfig,
) -> Result<()> {
    for dep in &cfg.dep_pkgs {
        let rel = dep.pkg_root.strip_prefix(&cfg.root_pkg.pkg_root).context(
            "External path dependencies are unavailable to sandboxed stock statement builds",
        )?;
        let target = project.join(rel);
        ensure_statement_snapshot_path(project, &target)?;
        if target.exists() {
            continue;
        }
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent)?;
        }
        let out = Command::new("git")
            .args(["clone", "--quiet", "--no-hardlinks"])
            .arg(&dep.pkg_root)
            .arg(&target)
            .output()?;
        anyhow::ensure!(
            out.status.success(),
            "Cannot seed offline statement dependency {}: {}",
            dep.name,
            String::from_utf8_lossy(&out.stderr)
        );
    }
    Ok(())
}

// Share source-root resolution between stock compilation and digest reporting.
fn statement_source_modules(
    project: &Path,
    pkg: &crate::module_builder::PackageConfig,
) -> Result<BTreeMap<String, (PathBuf, PathBuf)>> {
    let base = project.join(&pkg.src_dir);
    let mut roots = vec![base.clone()];
    roots.extend(
        pkg.libs
            .iter()
            .filter_map(|lib| lib.src_dir.as_ref())
            .map(|dir| base.join(dir)),
    );
    roots.extend(
        pkg.exes
            .iter()
            .filter_map(|exe| exe.src_dir.as_ref())
            .map(|dir| base.join(dir)),
    );
    roots.sort_by_key(|root| std::cmp::Reverse(root.components().count()));
    roots.dedup();
    let mut modules = BTreeMap::new();
    for source in crate::lake_build::collect_project_lean_files(project, false, None) {
        let root = roots
            .iter()
            .find(|root| source.starts_with(root))
            .with_context(|| format!("No source root for {}", source.display()))?;
        let name = source
            .strip_prefix(root)?
            .with_extension("")
            .to_string_lossy()
            .replace('/', ".");
        anyhow::ensure!(
            modules
                .insert(name.clone(), (source, root.clone()))
                .is_none(),
            "Ambiguous statement module {name}"
        );
    }
    Ok(modules)
}

#[cfg(test)]
fn stock_statement_build(project: &Path) -> Result<()> {
    stock_statement_build_with_trust(project, false)
}

fn stock_statement_build_with_trust(project: &Path, is_untrusted: bool) -> Result<()> {
    let mut command = statement_lake_command(project, is_untrusted)?;
    command.arg("build");
    let out = crate::module_builder::run_command_with_timeout(
        &mut command,
        std::time::Duration::from_secs(1800),
        is_untrusted,
    )?;
    anyhow::ensure!(
        out.status.success(),
        "Stock lake build for kernel statement digests failed in {}:\n{}\n{}",
        project.display(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let pkg = crate::module_builder::resolve_package_config(project, true)?;
    let lib_dir = project.join(&pkg.build_dir).join(&pkg.lean_lib_dir);
    let modules = statement_source_modules(project, &pkg)?;
    let mut lake_targets = Vec::new();
    let mut standalone = BTreeMap::new();
    for (name, (source, root)) in modules {
        let owned = pkg.libs.iter().any(|lib| {
            let lib_root = project
                .join(&pkg.src_dir)
                .join(lib.src_dir.as_deref().unwrap_or(Path::new("")));
            lib_root == root
                && lib.globs.iter().any(|glob| {
                    use crate::module_builder::GlobSpec;
                    match glob {
                        GlobSpec::One(n) => name == *n,
                        GlobSpec::Submodules(n) => name.starts_with(&format!("{n}.")),
                        GlobSpec::AndSubmodules(n) => {
                            name == *n || name.starts_with(&format!("{n}."))
                        }
                    }
                })
        }) || pkg.exes.iter().any(|exe| exe.root == name);
        if owned {
            lake_targets.push(format!("+{name}"));
        } else {
            standalone.insert(name, (source, root));
        }
    }
    // Ask Lake to refresh every registered module, including non-default targets.
    if !lake_targets.is_empty() {
        let mut command = statement_lake_command(project, is_untrusted)?;
        command.arg("build").args(&lake_targets);
        let out = crate::module_builder::run_command_with_timeout(
            &mut command,
            std::time::Duration::from_secs(1800),
            is_untrusted,
        )?;
        anyhow::ensure!(
            out.status.success(),
            "Stock lake build of statement modules failed:\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    // Lake cannot address sources excluded by its globs (e.g. `TurboLean.lean`
    // with a `TurboLean.+` glob). Compile these with absolute stock Lean,
    // even when an older artifact exists, in import order.
    while !standalone.is_empty() {
        let mut ready = Vec::new();
        for (name, (source, _)) in &standalone {
            let header = crate::module_builder::parse_header_info(&fs::read_to_string(source)?);
            anyhow::ensure!(
                header.header_error.is_none(),
                "Invalid statement module header: {name}"
            );
            if !header
                .imports
                .iter()
                .any(|dep| standalone.contains_key(dep))
            {
                ready.push(name.clone());
            }
        }
        anyhow::ensure!(
            !ready.is_empty(),
            "Import cycle in standalone statement modules"
        );
        for name in ready {
            let (source, root) = standalone.remove(&name).unwrap();
            let output = lib_dir
                .join(source.strip_prefix(&root)?)
                .with_extension("olean");
            fs::create_dir_all(
                output
                    .parent()
                    .context("Missing statement output directory")?,
            )?;
            let mut command = statement_lean_command(project, is_untrusted)?;
            command
                .args(&pkg.more_lean_args)
                .args(&pkg.weak_lean_args);
            for (key, value) in &pkg.lean_options {
                command.arg(format!("-D{key}={value}"));
            }
            command
                .arg(&source)
                .arg("-R")
                .arg(&root)
                .arg("-o")
                .arg(&output);
            let out = crate::module_builder::run_command_with_timeout(
                &mut command,
                std::time::Duration::from_secs(1800),
                is_untrusted,
            )?;
            anyhow::ensure!(
                out.status.success(),
                "Stock Lean statement module {name} failed:\n{}\n{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
        }
    }
    Ok(())
}

#[cfg(test)]
fn built_kernel_statements(
    project: &Path,
    scope: Option<&Path>,
) -> Result<BTreeMap<String, String>> {
    built_kernel_statements_with_trust(project, scope, false)
}

fn built_kernel_statements_with_trust(
    project: &Path,
    scope: Option<&Path>,
    is_untrusted: bool,
) -> Result<BTreeMap<String, String>> {
    Ok(built_kernel_statement_report(project, scope, is_untrusted)?.statements)
}

fn built_kernel_statement_report(
    project: &Path,
    scope: Option<&Path>,
    is_untrusted: bool,
) -> Result<KernelStatementReport> {
    let helper = project.join(format!(
        ".turbo_statement_dump_{}.lean",
        pack::next_tmp_id()
    ));
    fs::write(
        &helper,
        include_str!("../../../lean/TurboLean/StatementHash.lean"),
    )?;
    struct HelperGuard(PathBuf);
    impl Drop for HelperGuard {
        fn drop(&mut self) {
            let _ = fs::remove_file(&self.0);
        }
    }
    let _guard = HelperGuard(helper.clone());
    let pkg = crate::module_builder::resolve_package_config(project, true)?;
    let lib_dir = project.join(&pkg.build_dir).join(&pkg.lean_lib_dir);
    let mut modules = BTreeMap::new();
    for (module, (source, root)) in statement_source_modules(project, &pkg)? {
        let relative = source.strip_prefix(&root)?;
        anyhow::ensure!(
            lib_dir.join(relative).with_extension("olean").is_file(),
            "No built .olean for {} after stock checking (statement pinning fails closed)",
            source.display()
        );
        modules.insert(
            module,
            source.strip_prefix(project)?.to_string_lossy().to_string(),
        );
    }
    if modules.is_empty() {
        return Ok(KernelStatementReport::default());
    }
    // Distinct executables may define the same constant (`main`). Compatible
    // modules share one import, while incompatible groups split into fresh OS
    // processes. Never re-import oleans into a process with old mapped regions.
    let mut batches = vec![modules.keys().cloned().collect::<Vec<_>>()];
    let mut dump = Vec::new();
    while let Some(mut batch) = batches.pop() {
        let mut command = statement_lean_command(project, is_untrusted)?;
        command
            .arg("--run")
            .arg(&helper)
            .args(&batch);
        let out = crate::module_builder::run_command_with_timeout(
            &mut command,
            std::time::Duration::from_secs(600),
            is_untrusted,
        )?;
        if !out.status.success() && batch.len() > 1 {
            let right = batch.split_off(batch.len() / 2);
            batches.push(right);
            batches.push(batch);
            continue;
        }
        anyhow::ensure!(
            out.status.success(),
            "Cannot dump kernel statements for {batch:?}:\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        dump.extend(out.stdout);
    }
    let mut report = KernelStatementReport::default();
    let mut chunk = Vec::new();
    let mut remaining = modules.clone();
    for line in dump.split_inclusive(|&c| c == b'\n') {
        chunk.extend_from_slice(line);
        let row: KernelDumpRow =
            serde_json::from_slice(line).context("Invalid kernel statement JSONL")?;
        if row.audit.is_some() {
            report.audits.push(serde_json::from_slice(line)?);
        }
        if let Some(module) = row.module.as_deref() {
            let rel = remaining
                .remove(module)
                .with_context(|| format!("Unexpected kernel statement module {module}"))?;
            report.csimp.extend(row.csimp.context("Missing csimp audit")?);
            let in_scope = scope.is_none_or(|p| Path::new(&rel).starts_with(p));
            for (name, digest) in parse_kernel_statement_dump(&chunk, module)? {
                if in_scope {
                    report.statements.insert(format!("{rel}::{name}"), digest);
                }
            }
            chunk.clear();
        }
    }
    anyhow::ensure!(
        remaining.is_empty() && chunk.is_empty(),
        "Incomplete kernel statement dump"
    );
    Ok(report)
}

#[cfg(test)]
fn kernel_statement_changes(
    project: &Path,
    base: &str,
    scope: Option<&Path>,
) -> Result<Vec<String>> {
    kernel_statement_changes_with_trust(project, base, scope, None)
}

fn ensure_statement_lake_project(project: &Path) -> Result<()> {
    if crate::lake_build::has_lake_config(project) {
        return Ok(());
    }
    let roots: Vec<_> = crate::lake_build::collect_project_lean_files(project, false, None)
        .iter()
        .map(|file| {
            file.strip_prefix(project)
                .map(|rel| rel.with_extension("").to_string_lossy().replace('/', "."))
        })
        .collect::<std::result::Result<_, _>>()?;
    let mut config = "name = \"turbo-statement-snapshot\"\n".to_string();
    if !roots.is_empty() {
        let modules = serde_json::to_string(&roots)?;
        config.push_str(&format!("defaultTargets = [\"TurboStatementSnapshot\"]\n[[lean_lib]]\nname = \"TurboStatementSnapshot\"\nroots = {modules}\nglobs = {modules}\n"));
    }
    fs::write(project.join("lakefile.toml"), config)?;
    Ok(())
}

fn kernel_statement_changes_with_trust(
    project: &Path,
    base: &str,
    scope: Option<&Path>,
    untrusted_cfg: Option<&crate::module_builder::ProjectConfig>,
) -> Result<Vec<String>> {
    let repo = resolve_git_toplevel(project)?;
    let baseline = StatementWorktree::at(&repo, base)?;
    let base_project = baseline.path.join(project.strip_prefix(&repo)?);
    let relative_scope = scope
        .map(|p| -> Result<PathBuf> {
            let joined = if p.is_absolute() {
                p.to_path_buf()
            } else {
                project.join(p)
            };
            let joined = joined.canonicalize().unwrap_or(joined);
            let relative = joined
                .strip_prefix(project)
                .context("Statement scope must be inside the project")?;
            anyhow::ensure!(
                !relative
                    .components()
                    .any(|c| matches!(c, std::path::Component::ParentDir)),
                "Statement scope must be inside the project"
            );
            Ok(relative
                .components()
                .filter(|c| !matches!(c, std::path::Component::CurDir))
                .collect())
        })
        .transpose()?;
    let is_untrusted = untrusted_cfg.is_some();
    ensure_statement_lake_project(&base_project)?;
    if let Some(cfg) = untrusted_cfg {
        clear_untrusted_statement_build_products(&base_project)?;
        seed_statement_dependencies(&base_project, cfg)?;
    }
    let head_snapshot = if is_untrusted || !crate::lake_build::has_lake_config(project) {
        let snapshot = StatementWorktree::at(&repo, "HEAD")?;
        overlay_statement_sources(&repo, &snapshot.path)?;
        let snapshot_project = snapshot.path.join(project.strip_prefix(&repo)?);
        ensure_statement_lake_project(&snapshot_project)?;
        if let Some(cfg) = untrusted_cfg {
            clear_untrusted_statement_build_products(&snapshot_project)?;
            seed_statement_dependencies(&snapshot_project, cfg)?;
        }
        Some(snapshot)
    } else {
        None
    };
    let head_project = head_snapshot
        .as_ref()
        .map(|s| s.path.join(project.strip_prefix(&repo).unwrap()))
        .unwrap_or_else(|| project.to_path_buf());
    stock_statement_build_with_trust(&base_project, is_untrusted)?;
    let before =
        built_kernel_statements_with_trust(&base_project, relative_scope.as_deref(), is_untrusted)?;
    stock_statement_build_with_trust(&head_project, is_untrusted)?;
    let after =
        built_kernel_statement_report(&head_project, relative_scope.as_deref(), is_untrusted)?;
    StatementPolicy::at(project, base).audit(&after)?;
    Ok(compare_kernel_statements(&before, &after.statements))
}

fn compare_kernel_statements(
    before: &BTreeMap<String, String>,
    after: &BTreeMap<String, String>,
) -> Vec<String> {
    before
        .iter()
        .filter_map(|(name, digest)| match after.get(name) {
            None => Some(format!("{name} (deleted)")),
            Some(current) if current != digest => Some(name.clone()),
            _ => None,
        })
        .collect()
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
    signing_key: Option<String>,
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

    let untrusted_pr_cfg = if is_untrusted {
        if crate::module_builder::probe_bwrap_sandbox().is_none() {
            anyhow::bail!(
                "Untrusted PR verification requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
            );
        }
        Some(resolve_untrusted_pr_project_config(&canon_dir, &toolchain)?)
    } else {
        None
    };
    let verification_trust = PrVerificationTrust {
        is_untrusted,
        untrusted_cfg: untrusted_pr_cfg.as_ref(),
    };

    let (mut classification, shards_by_file, current_files, current_splits) =
        load_and_classify_pr_from_git_scoped(
            store,
            &canon_dir,
            &base,
            &toolchain,
            scope.as_deref(),
            is_untrusted,
            untrusted_pr_cfg.as_ref(),
        )?;

    for (file, split) in &current_splits {
        anyhow::ensure!(!split.hygiene.native_violation(),
            "[TurboLean.KernelGate] native_decide/bv_decide in {file} requires the base project's axiom allowlist");
    }

    // Only a theorem whose proof body alone changed is a local edit (proof irrelevance). Anything
    // else (statement, definition, instance, attribute, option, import, added or deleted file)
    // can break other modules: re-check them and their dependents before per-theorem checks
    // count. In `--mode untrusted`, never invoke unsandboxed `lake build` or `[lake] build_command`;
    // compile inside `bwrap` with Stage 1C `--audit-modules` instead.
    let lake_t0 = Instant::now();
    let mut lake_rechecked_modules = 0usize;
    let mut untrusted_deps_built = false;
    if !classification.altered_interface_files.is_empty() {
        if is_untrusted {
            lake_rechecked_modules = crate::lake_build::untrusted_recheck_dependents(
                store,
                &canon_dir,
                &classification.altered_interface_files,
                &trust_domain,
                json,
            )?;
            untrusted_deps_built = true;
        } else {
            lake_rechecked_modules = crate::lake_build::lake_recheck_dependents(
                &canon_dir,
                &classification.altered_interface_files,
                Some(&base),
            )?;
        }
    } else if !is_untrusted {
        let edited: Vec<PathBuf> = shards_by_file.keys().map(|f| canon_dir.join(f)).collect();
        if crate::lake_build::worktree_auto_link_disabled(&canon_dir) {
            crate::lake_build::ensure_project_imports_fresh_for_check(&canon_dir, &edited)?;
        } else if crate::lake_build::has_lake_config(&canon_dir) {
            let imports = crate::lake_build::project_imports_of(&canon_dir, &edited);
            if !imports.is_empty() {
                crate::lake_build::lake_build_modules(&canon_dir, &imports, Some(&base))?;
            }
        }
    }
    let lake_recheck_ms = lake_t0.elapsed().as_millis();

    let mut all_edited_keys = Vec::new();
    for (_rel_path, file_shards) in &shards_by_file {
        for (k, _sh, _fast_ok) in file_shards {
            all_edited_keys.push(k.clone());
        }
    }

    let cached_set = store.batch_completed_action_keys(&all_edited_keys, &trust_domain)?;
    let raw_uncached_jobs = all_edited_keys.iter().filter(|key| !cached_set.contains(*key)).count();
    let effective_job_cap = unsafe {
        crate::cluster::c_abi::turbo_spec_effective_cone_job_cap(
            raw_uncached_jobs as u64,
            max_cone_jobs as u64,
        ) as usize
    };
    if max_cone_jobs > 0 && raw_uncached_jobs > effective_job_cap {
        anyhow::bail!(
            "PR verification cone budget exceeded (fail-closed): {} uncached theorem shards exceed --max-cone-jobs {} (refusing to truncate unverified shards)",
            raw_uncached_jobs,
            effective_job_cap
        );
    }

    // Identity elaboration needs the same compiled imports as shard checking,
    // including when the only verification results would otherwise be cache hits.
    if let Some(ref cfg) = untrusted_pr_cfg {
        let needs_project_imports = shards_by_file.keys().any(|rel_path| {
            let src = current_files
                .get(rel_path)
                .map(|s| s.as_str())
                .unwrap_or("");
            let hdr = crate::module_builder::parse_header_info(src);
            hdr.header_error.is_some()
                || hdr.imports.iter().any(|m| {
                    let rel_slash = crate::module_builder::module_name_to_rel_slash(m);
                    let in_pkg_or_project = crate::module_builder::resolve_module_in_package(
                        &cfg.root_pkg,
                        true,
                        m,
                    )
                    .is_some()
                        || cfg.dep_pkgs.iter().any(|dp| {
                            crate::module_builder::resolve_module_in_package(dp, false, m)
                                .is_some()
                        })
                        || crate::lake_build::resolve_project_lean_source(
                            &canon_dir, &rel_slash,
                        )
                        .is_some();
                    in_pkg_or_project
                        || !crate::module_builder::is_builtin_toolchain_module(
                            &cfg.toolchain_lib_lean,
                            m,
                        )
                })
        });
        if needs_project_imports && !untrusted_deps_built {
            if !canon_dir.join("lakefile.toml").is_file()
                && !canon_dir.join("lakefile.lean").is_file()
            {
                anyhow::bail!(
                    "Untrusted PR verification requires a static `lakefile.toml` or `lakefile.lean` to build project imports"
                );
            }
            crate::module_builder::build_project_modules_native(
                store,
                &canon_dir,
                &[],
                &trust_domain,
                1,
                true,
                json,
                None,
            )
            .context("Untrusted PR dependency build failed")?;
        }
    }

    // Per-shard names must be attested by Lean before cache hits or verification
    // can be attributed to them, including the single-theorem PR case.
    for (rel_path, file_shards) in &shards_by_file {
        let src = current_files
            .get(rel_path)
            .context("Missing source for declaration identity confirmation")?;
        for (_, shard, _) in file_shards {
            crate::check::confirm_decl_identity_with_trust(
                src,
                shard,
                &canon_dir,
                &canon_dir.join(rel_path),
                is_untrusted,
            )?;
        }
    }


    let mut shard_cache_hits = 0usize;
    let mut shards_verified = 0usize;
    let mut fast_olean_used = false;
    let mut cross_file_coalesced = false;
    let mut batch_to_publish = Vec::new();
    let mut inflight_tx_open = false;

    let mut uncached_by_file = Vec::new();
    for (rel_path, file_shards) in shards_by_file {
        let mut uncached = Vec::new();
        let mut can_fast_olean = !is_untrusted;
        for (k, sh, fast_ok) in file_shards {
            if cached_set.contains(&k) {
                shard_cache_hits += 1;
            } else {
                if !fast_ok {
                    can_fast_olean = false;
                }
                uncached.push((k, sh));
            }
        }
        if !uncached.is_empty() {
            uncached_by_file.push((rel_path, uncached, can_fast_olean));
        }
    }

    // Keep source interfaces and verification jobs intact. Only the report/gate uses
    // built kernel statements, so an equal digest can never bypass stock checking.
    let statement_digest_t0 = Instant::now();
    let source_statement_edit = !classification.statement_edited_theorems.is_empty();
    classification.statement_edited_theorems = kernel_statement_changes_with_trust(
        &canon_dir,
        &base,
        scope.as_deref(),
        untrusted_pr_cfg.as_ref(),
    )?;
    let statement_digest_ms = statement_digest_t0.elapsed().as_millis();
    let is_statement_edit = |source_name: &String| {
        classification
            .statement_edited_theorems
            .iter()
            .any(|kernel_name| {
                let (Some((file, name)), Some((kernel_file, kernel_decl))) =
                    (source_name.split_once("::"), kernel_name.split_once("::"))
                else {
                    return false;
                };
                file == kernel_file
                    && (kernel_decl == name || kernel_decl.ends_with(&format!(".{name}")))
            })
    };
    classification
        .unchanged_theorems
        .retain(|n| !is_statement_edit(n));
    classification
        .proof_edited_theorems
        .retain(|n| !is_statement_edit(n));

    // Preserve every source-based restriction enforced before kernel reporting.
    if disallow_statement_changes
        && (classification.interface_drift || source_statement_edit
            || !classification.statement_edited_theorems.is_empty())
    {
        anyhow::bail!(
            "PR statement/interface change gate FAILED (--disallow-statement-changes, mode={}): interface_drift={}, source_statement_edit={}, altered_files={:?}, statement_edited_theorems={:?}",
            mode,
            classification.interface_drift,
            source_statement_edit,
            classification.altered_interface_files,
            classification.statement_edited_theorems
        );
    }

    if !uncached_by_file.is_empty() {
        let fast_lib_dir = canon_dir.join(".lake/build/lib/lean");
        let fast_local_zygote_url = if !is_untrusted && remote_http.is_none() {
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
        let (mut env_vars, lean_bin, lean_path_str) = if let Some(ref cfg) = untrusted_pr_cfg {
            let (lp, ldp) = crate::module_builder::build_lean_search_path(cfg, true);
            let mut ev = std::collections::HashMap::new();
            if !lp.is_empty() {
                ev.insert("LEAN_PATH".to_string(), lp.clone());
            }
            if !ldp.is_empty() {
                ev.insert("LD_LIBRARY_PATH".to_string(), ldp);
            }
            (ev, cfg.lean_bin.to_string_lossy().to_string(), lp)
        } else if fast_local_zygote_url.is_some() && fast_lib_dir.exists() {
            let lp = resolve_remote_lean_path(&canon_dir, None);
            let mut fast_ev = std::collections::HashMap::new();
            fast_ev.insert("LEAN_PATH".to_string(), lp.clone());
            (fast_ev, "lean".to_string(), lp)
        } else {
            let (ev, _) = resolve_lake_env(store, &canon_dir)?;
            let lb = lean_bin_from_env(&ev);
            let lp = resolve_remote_lean_path(&canon_dir, Some(&ev));
            (ev, lb, lp)
        };

        let pid = std::process::id();
        let trusted_pkg_cfg = if is_untrusted {
            None
        } else {
            crate::module_builder::optional_package_config(&canon_dir)?
        };
        let resolve_file_args = |abs_file: &Path| -> Vec<String> {
            if let Some(ref cfg) = untrusted_pr_cfg {
                crate::module_builder::resolve_file_lean_args_in_package(&cfg.root_pkg, abs_file)
            } else if let Some(ref pkg) = trusted_pkg_cfg {
                crate::module_builder::resolve_file_lean_args_in_package(pkg, abs_file)
            } else {
                Vec::new()
            }
        };

        let mut cross_eligible = Vec::new();
        let mut cross_shared_args: Option<Vec<String>> = None;
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
                let file_args = resolve_file_args(&abs_file);
                match &cross_shared_args {
                    None => cross_shared_args = Some(file_args),
                    Some(prev) if *prev != file_args => break,
                    Some(_) => {}
                }
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
            let cross_args = cross_shared_args.unwrap_or_default();
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
                    &cross_args,
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
                    cross_args.clone(),
                );
                let cross_res = if let Some(ref z_url) = fast_local_zygote_url {
                    pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
                        z_url,
                        &zreq,
                        || {
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
                        },
                    )
                } else if !is_untrusted {
                    pack::try_local_zygote_check_shard_detailed(store, &env_vars, &zreq)
                } else {
                    Ok(None)
                };
                let mut cross_ok = matches!(cross_res, Ok(Some(_)));
                if !cross_ok {
                    if inflight_tx_open {
                        store.rollback_inflight_publish();
                        inflight_tx_open = false;
                    }
                    batch_to_publish.clear();
                    cross_res
                        .context("Zygote kernel gate rejected the cross-file PR shard batch")?;
                    if !is_untrusted && env_vars.is_empty() {
                        if let Ok((ev, _)) = resolve_lake_env(store, &canon_dir) {
                            env_vars = ev;
                        }
                    }
                    let lb = if env_vars.is_empty() {
                        lean_bin.clone()
                    } else {
                        lean_bin_from_env(&env_vars)
                    };
                    let cross_names: std::collections::HashSet<String> = uncached_by_file
                        .iter()
                        .flat_map(|(_, fu, _)| fu.iter().map(|(_, sh)| sh.name.clone()))
                        .collect();
                    cross_ok = run_lean_temp_file(
                        store,
                        &lb,
                        &cross_src,
                        &canon_dir,
                        &env_vars,
                        &verification_trust,
                        &cross_names,
                        &cross_args,
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
                    let file_lean_args = resolve_file_args(&canon_lf);
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
                                    &file_lean_args,
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
                        let coal_src = if is_untrusted {
                            src.clone()
                        } else {
                            splitter::build_coalesced_shard_source(&src, &uncached_names)
                        };
                        let resp = pack::offload_check_shards_batch_http(
                            store,
                            remote_url,
                            &req_items,
                            &coal_src,
                            &trust_domain,
                            &toolchain,
                            &lean_path_str,
                            &file_lean_args,
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
                let local_zygote_url = if is_untrusted {
                    None
                } else {
                    fast_local_zygote_url
                        .or_else(|| pack::ensure_local_zygote_daemon(store, &env_vars))
                };
                if !is_untrusted && local_zygote_url.is_none() && env_vars.is_empty() {
                    if let Ok((ev, _)) = resolve_lake_env(store, &canon_dir) {
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
                    let owned_store_opt = if inflight_store.is_none() {
                        Some(TurboStore::open(Some(store_root))?)
                    } else {
                        None
                    };
                    let worker_store = inflight_store
                        .or(owned_store_opt.as_ref())
                        .expect("worker_store initialized");
                    let mut local_verified = 0usize;
                    let mut local_fast_olean = false;
                    let mut local_tx_open = false;
                    let local_receipt: Option<VerificationReceipt> = None;
                    let mut local_publish = Vec::new();
                    let (ref rel_path, ref file_uncached, can_fast_olean) = uncached_by_file[f_idx];
                    let abs_file = canon_dir.join(rel_path);
                    let file_lean_args = resolve_file_args(&abs_file);
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
                                        file_lean_args.clone(),
                                    );
                                    let fast_res =
                                        pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
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
                                            }
                                        },
                                    );
                                    if matches!(fast_res, Ok(Some(_))) {
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
                                        fast_res.with_context(|| {
                                            format!(
                                                "Zygote kernel gate rejected PR shards in {}",
                                                rel_path
                                            )
                                        })?;
                                    }
                                }
                                if !verified_ok {
                                    if run_lean_temp_file(
                                        worker_store,
                                        &lean_bin,
                                        &fast_src,
                                        &canon_dir,
                                        &env_vars,
                                        &verification_trust,
                                        &uncached_names,
                                        &file_lean_args,
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
                                    file_lean_args.clone(),
                                );
                                if pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
                                    z_url,
                                    &zreq,
                                    || {},
                                )
                                .with_context(|| {
                                    format!("Zygote kernel gate rejected PR shards in {}", rel_path)
                                })?
                                .is_some()
                                {
                                    return Ok(true);
                                }
                            }
                            Ok(run_lean_temp_file(
                                worker_store,
                                &lean_bin,
                                src_to_check,
                                &canon_dir,
                                &env_vars,
                                &verification_trust,
                                &uncached_names,
                                &file_lean_args,
                            )?
                            .status
                            .success())
                        };

                    if !verified_ok && is_untrusted {
                        let out = run_lean_temp_file(
                            worker_store,
                            &lean_bin,
                            &src,
                            &canon_dir,
                            &env_vars,
                            &verification_trust,
                            &uncached_names,
                            &file_lean_args,
                        )?;
                        if !out.status.success() {
                            anyhow::bail!(
                                "PR file verification failed in {}:\n{}\n{}",
                                rel_path,
                                String::from_utf8_lossy(&out.stdout),
                                String::from_utf8_lossy(&out.stderr)
                            );
                        }
                        verified_ok = true;
                    }

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
                        for (k, sh) in file_uncached.iter() {
                            let s_t0 = Instant::now();
                            let single_src: std::borrow::Cow<'_, str> =
                                if sh.shard_source.is_empty() {
                                    let reconstructed =
                                        splitter::reconstruct_single_shard_source(&src, sh.decl_name())?
                                            .unwrap_or_else(|| {
                                                let mut single_set =
                                                    std::collections::HashSet::with_capacity(1);
                                                single_set.insert(sh.decl_name().to_string());
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
                                    allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
                                    lean_args: file_lean_args.clone(),
                                };
                                let single_res =
                                    pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
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
                                                    let _ =
                                                        crate::db::prestage_theorem_shard_blobs_at(
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
                                                    }
                                                }
                                            }
                                        },
                                    );
                                if matches!(single_res, Ok(Some(_))) {
                                    single_ok = true;
                                } else {
                                    if local_tx_open {
                                        if let Some(st) = inflight_store {
                                            st.rollback_inflight_publish();
                                        }
                                        local_tx_open = false;
                                        local_publish.clear();
                                    }
                                    single_res.with_context(|| {
                                        format!(
                                            "Zygote kernel gate rejected PR shard `{}` in {}",
                                            sh.name, rel_path
                                        )
                                    })?;
                                }
                            }
                            if !single_ok {
                                let out = run_lean_temp_file(
                                    worker_store,
                                    &lean_bin,
                                    &single_src,
                                    &canon_dir,
                                    &env_vars,
                                    &verification_trust,
                                    &std::iter::once(sh.name.clone()).collect(),
                                    &file_lean_args,
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
                    let (v_cnt, used_fast, tx_open, _rec_opt, items) = res?;
                    shards_verified += v_cnt;
                    if used_fast {
                        fast_olean_used = true;
                    }
                    if tx_open {
                        inflight_tx_open = true;
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
    } else if !is_untrusted
        && remote_http.is_none()
        && !crate::zygote::daemon_disabled()
    {
        let mut fast_ev = std::collections::HashMap::new();
        if canon_dir.join(".lake/build/lib/lean").exists() {
            fast_ev.insert(
                "LEAN_PATH".to_string(),
                resolve_remote_lean_path(&canon_dir, None),
            );
        }
        pack::warm_local_zygote_daemon_nonblocking(store, &fast_ev);
    }

    let mut nanoda_verified = false;
    if let Some(ref nanoda_path) = nanoda_bin {
        if !nanoda_path.exists() {
            anyhow::bail!(
                "External kernel checker `--nanoda-bin {}` does not exist",
                nanoda_path.display()
            );
        }
        let mut nanoda_cmd = Command::new(nanoda_path);
        nanoda_cmd.arg(&canon_dir).current_dir(&canon_dir);
        if is_untrusted {
            scrub_sensitive_env_cmd(&mut nanoda_cmd);
        }
        let st = nanoda_cmd.status().with_context(|| {
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

    let mut ver_receipt = build_pr_verification_receipt(&mode, &base, &classification);
    emit_verification_receipt_with_signing_key(
        receipt.as_deref(),
        &mut ver_receipt,
        signing_key.as_deref(),
    )?;

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
    let project_name = canon_dir
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "pr-project".to_string());
    crate::mcp::emit_cli_telemetry_event(
        Some(&canon_dir),
        !is_untrusted,
        serde_json::json!({
            "schema": "turbo-lean.telemetry.v1",
            "tool_name": "pr_verify",
            "command": "pr-verify",
            "decl_name": project_name,
            "status": "pr_verified",
            "base": base,
            "mode": mode,
            "trust_domain": trust_domain,
            "interface_drift": classification.interface_drift,
            "interface_hash": classification.current_interface_hash,
            "receipt_blake3": ver_receipt.receipt_blake3,
            "total_files": classification.total_files,
            "modified_files_count": classification.modified_files.len(),
            "unchanged_theorems_count": classification.unchanged_theorems.len(),
            "proof_edited_theorems_count": classification.proof_edited_theorems.len(),
            "statement_edited_theorems_count": classification.statement_edited_theorems.len(),
            "shard_cache_hits": shard_cache_hits,
            "shards_verified": shards_verified,
            "cache_hit": shards_verified == 0,
            "accepted": true,
            "nanoda_verified": nanoda_verified,
            "fast_olean_used": fast_olean_used,
            "cross_file_coalesced": cross_file_coalesced,
            "zero_sorry": true,
            "zero_native_decide": !splitter::native_decide_allowed(),
            "elapsed_ms": elapsed_ms,
        }),
        "turbo_lean_events.jsonl",
    );
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
            "zero_native_decide": !splitter::native_decide_allowed(),
            "allowed_axioms": splitter::allowed_axioms(),
            "lake_recheck_ms": lake_recheck_ms,
            "statement_digest_ms": statement_digest_ms,
            "statement_digest_kind": "constant-info+if-closure:v1",
            "lake_rechecked_modules": lake_rechecked_modules,
            "axiom_flags": classification.axiom_flags,
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
    use crate::lake_build::{
        compute_imported_olean_interface_hashes, compute_shard_key, is_file_verified_in_lake_build,
    };

    #[cfg(unix)]
    #[test]
    fn test_optout_trusted_pr_stale_imports_preserve_lake_tree() -> Result<()> {
        use crate::worktree_test_support::{assert_stale_error, snapshot, LakeTree};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::imports("stale_pr")?;
        tree.opt_out()?;
        git_init_and_commit(&tree.project, "base")?;
        tree.stale_import()?;
        fs::write(
            tree.project.join("P/Target.lean"),
            "import P.Middle\ntheorem target : a = 1 := by\n  rfl\n",
        )?;
        tree.prepare_snapshot(".lake/build/lib/lean/P/A.olean")?;
        let before = snapshot(&tree.project)?;
        let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
        let err = run_pr_verify_command(
            &mut store,
            true,
            tree.project.clone(),
            "HEAD".into(),
            "trusted".into(),
            false,
            None,
            None,
            None,
            None,
            false,
            0,
            None,
        )
        .unwrap_err();
        assert_stale_error(&err);
        assert_eq!(snapshot(&tree.project)?, before);
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_optout_untrusted_ci_cached_audit_failure_preserves_lake_tree() -> Result<()> {
        use crate::worktree_test_support::{snapshot, LakeTree};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        // Lake compiles this macro-expanded axiom; source hygiene cannot see the generated name.
        let source = concat!(
            "import Lean\nopen Lean Elab Tactic in\n",
            "elab \"concealed\" : tactic => do\n  let g ← getMainGoal\n  let t ← g.getType\n",
            "  let s := String.mk ['s', 'o', 'r', 'r', 'y', 'A', 'x']\n",
            "  let e ← Meta.mkAppM (Name.mkSimple s) #[t, mkConst ``false]\n  g.assign e\n",
            "theorem hidden : 1 + 1 = 2 := by concealed\n"
        );
        let tree = LakeTree::new("ci_audit", &[("P/A.lean", source)])?;
        tree.opt_out()?;
        let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
        let toolchain = detect_toolchain(&tree.project);
        let axioms = splitter::allowed_axioms();
        let split = split_lean_source(source, &[]);
        assert!(split.hygiene.is_clean_for_certification());
        let mut hasher = blake3::Hasher::new();
        let cfg = crate::module_builder::resolve_project_config(&tree.project)?;
        hasher.update(
            format!(
                "turbo-lean-ci-build-v2\n{toolchain}\nuntrusted:ci\n{}\n",
                cfg.canonical_config_digest
            )
            .as_bytes(),
        );
        if axioms.len() > splitter::STANDARD_AXIOMS.len() {
            hasher.update(b":axioms:");
            hasher.update(axioms.join(",").as_bytes());
            hasher.update(b"\n");
        }
        hasher.update(b"P/A.lean:");
        hasher.update(blake3::hash(source.as_bytes()).as_bytes());
        hasher.update(b"\n");
        let key = hasher.finalize().to_hex().to_string();
        let (outputs, blobs) = crate::lake_build::stage_lake_build_outputs(&store, &tree.project)?;
        store.batch_register_linked_blobs(&blobs, "untrusted:ci", 1)?;
        let lease =
            match store.acquire_singleflight(&key, &toolchain, "lake_build", "untrusted:ci")? {
                crate::db::SingleflightOutcome::Leader(lease) => lease,
                _ => anyhow::bail!("expected empty test cache"),
            };
        store.publish_action(&lease, &outputs, 0, 0, 0, "untrusted:ci")?;
        drop(lease);
        assert!(store.get_cached_action(&key, "untrusted:ci")?.is_some());
        tree.prepare_snapshot(".lake/build/lib/lean/P/A.olean")?;
        let before = snapshot(&tree.project)?;
        let fake_bwrap =
            crate::module_builder::ScopedTestBwrapOverride::write_fake_bwrap_script(&tree.root)?;
        let _bwrap =
            crate::module_builder::ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy());
        let err = run_ci_verify_command(
            &mut store,
            true,
            "untrusted".into(),
            tree.project.clone(),
            None,
            None,
            false,
            None,
        )
        .unwrap_err()
        .to_string();
        assert!(
            err.contains("soundness audit rejected compiled artifact(s)")
                && err.contains("sorryAx"),
            "{err}"
        );
        assert_eq!(
            snapshot(&tree.project)?,
            before,
            "CI rejection wiped the pre-existing build tree"
        );
        Ok(())
    }

    #[test]
    fn kernel_statement_fixtures() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo-kernel-statements-{}-{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        fs::create_dir_all(dir.join("Demo"))?;
        fs::create_dir_all(dir.join("Other"))?;
        fs::write(
            dir.join("Other/Keep.lean"),
            "theorem keep : True := trivial\n",
        )?;
        fs::write(dir.join(".gitignore"), ".lake/\n")?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            r#"name = "statement-fixture"
defaultTargets = ["Demo"]
[[lean_lib]]
name = "Demo"
globs = ["Demo.+"]
"#,
        )?;
        let source = "namespace Demo\ndef value : Nat := 1\ntheorem pinned : value = value := rfl\ntheorem independent : True := trivial\nend Demo\n";
        let file = dir.join("Demo/Main.lean");
        fs::write(&file, source)?;
        git_init_and_commit(&dir, "baseline")?;
        stock_statement_build(&dir)?;
        let before = built_kernel_statements(&dir, None)?;
        assert!(before.contains_key("Demo/Main.lean::Demo.pinned"));
        // A source interface restriction still applies when no old theorem type changes.
        fs::write(&file, format!("{source}\ndef unrelated : Nat := 42\n"))?;
        stock_statement_build(&dir)?;
        assert_eq!(before, built_kernel_statements(&dir, None)?);
        let mut store = TurboStore::open(Some(&dir.join(".lake/gate-cache")))?;
        let error = run_pr_verify_command(
            &mut store, true, dir.clone(), "HEAD".into(), "trusted".into(),
            true, None, None, None, None, false, 0, None,
        ).unwrap_err().to_string();
        assert!(error.contains("statement/interface change gate FAILED")
            && error.contains("interface_drift=true"), "{error}");
        for (label, current) in [
            ("import-only", format!("import Lean\n{source}")),
            (
                "whitespace",
                source.replace("value = value", "value  =  value"),
            ),
            ("comment", format!("-- a harmless comment\n{source}")),
        ] {
            fs::write(&file, current)?;
            stock_statement_build(&dir)?;
            let changed = compare_kernel_statements(&before, &built_kernel_statements(&dir, None)?);
            assert!(changed.is_empty(), "{label}: {changed:?}");
            println!("kernel statement fixture {label}: 0 reports");
        }
        fs::write(&file, source.replace("Nat := 1", "Nat := 2"))?;
        stock_statement_build(&dir)?;
        assert_eq!(
            compare_kernel_statements(&before, &built_kernel_statements(&dir, None)?),
            vec!["Demo/Main.lean::Demo.pinned"]
        );
        println!("kernel statement fixture referenced-def: Demo.pinned reported");
        fs::write(&file, source.replace("value = value", "value + 0 = value"))?;
        stock_statement_build(&dir)?;
        assert_eq!(
            compare_kernel_statements(&before, &built_kernel_statements(&dir, None)?),
            vec!["Demo/Main.lean::Demo.pinned"]
        );
        println!("kernel statement fixture theorem-type: Demo.pinned reported");
        fs::write(&file, source.replace("pinned", "renamed"))?;
        stock_statement_build(&dir)?;
        assert_eq!(
            compare_kernel_statements(&before, &built_kernel_statements(&dir, None)?),
            vec!["Demo/Main.lean::Demo.pinned (deleted)"]
        );
        println!("kernel statement fixture rename: old theorem reported deleted");
        fs::write(
            &file,
            source.replace("theorem pinned : value = value := rfl\n", ""),
        )?;
        stock_statement_build(&dir)?;
        assert_eq!(
            compare_kernel_statements(&before, &built_kernel_statements(&dir, None)?),
            vec!["Demo/Main.lean::Demo.pinned (deleted)"]
        );
        println!("kernel statement fixture deletion: old theorem reported deleted");
        assert!(kernel_statement_changes(&dir, "HEAD", Some(Path::new("Other")))?.is_empty());
        println!("kernel statement fixture scope: 0 out-of-scope reports");

        // A definition's value may reach other definitions across module boundaries.
        fs::write(dir.join("Demo/Value.lean"), "def underlying : Nat := 1\n")?;
        let indirect = format!(
            "import Demo.Value\n{}",
            source.replace("Nat := 1", "Nat := underlying")
        );
        fs::write(&file, &indirect)?;
        stock_statement_build(&dir)?;
        let indirect_before = built_kernel_statements(&dir, None)?;
        fs::write(dir.join("Demo/Value.lean"), "def underlying : Nat := 2\n")?;
        stock_statement_build(&dir)?;
        assert_eq!(
            compare_kernel_statements(&indirect_before, &built_kernel_statements(&dir, None)?),
            vec!["Demo/Main.lean::Demo.pinned"]
        );
        fs::write(&file, indirect.replace(":= rfl", ":= by rfl"))?;
        stock_statement_build(&dir)?;
        let proof_before = built_kernel_statements(&dir, None)?;
        fs::write(&file, &indirect)?;
        stock_statement_build(&dir)?;
        assert_eq!(proof_before, built_kernel_statements(&dir, None)?);
        println!("kernel statement fixture transitive imported definition: reported; proof-only edit: 0 reports");
        // `Demo.+` excludes the root and unrelated source modules. These still
        // need fresh stock artifacts, with imports compiled before importers.
        fs::write(
            dir.join("Outside.lean"),
            "theorem outside : True := trivial\n",
        )?;
        let root = dir.join("Demo.lean");
        fs::write(
            &root,
            "import Outside\nimport Demo.Main\ntheorem outer : Demo.value = Demo.value := rfl\n",
        )?;
        stock_statement_build(&dir)?;
        let standalone_before = built_kernel_statements(&dir, None)?;
        assert!(standalone_before.contains_key("Demo.lean::outer"));
        fs::write(
            &root,
            "import Outside\nimport Demo.Main\ntheorem outer : True := trivial\n",
        )?;
        stock_statement_build(&dir)?;
        assert_eq!(
            compare_kernel_statements(&standalone_before, &built_kernel_statements(&dir, None)?),
            vec!["Demo.lean::outer"]
        );
        fs::write(
            dir.join("Outside.lean"),
            "theorem outside : True := by exact (0 : Nat)\n",
        )?;
        assert!(
            stock_statement_build(&dir).is_err(),
            "an old standalone artifact must never bypass stock checking"
        );
        println!("kernel statement fixture excluded modules: import order, stale-artifact refresh, and broken-proof rejection pass");
        fs::write(
            dir.join("Outside.lean"),
            "theorem outside : True := trivial\n",
        )?;
        for (module, theorem) in [("ToolA", "first"), ("ToolB", "second")] {
            fs::write(
                dir.join(format!("{module}.lean")),
                format!("theorem {theorem} : True := trivial\ndef main : IO Unit := pure ()\n"),
            )?;
        }
        stock_statement_build(&dir)?;
        let executable_statements = built_kernel_statements(&dir, None)?;
        assert!(executable_statements.contains_key("ToolA.lean::first"));
        assert!(executable_statements.contains_key("ToolB.lean::second"));
        println!("kernel statement fixture executable roots: duplicate main declarations isolated successfully");
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn kernel_statement_large_literals_remain_exact() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo-statement-naturals-{}-{}", std::process::id(), pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(dir.join("lakefile.toml"),
            "name = \"natural-fixture\"\ndefaultTargets = [\"Demo\"]\n[[lean_lib]]\nname = \"Demo\"\n")?;
        for (old, new) in [
            ("1180591620717411303424", "1180591620717411303425"),
            ("10000000000000000000000000000000000000000000000000000000000000000000000000000",
             "10000000000000000000000000000000000000000000000000000000000000000000000000001"),
        ] {
            let source = |n: &str| format!(
                "def large : Nat := {n}\ntheorem pinned : ({n} : Nat) = {n} := rfl\ntheorem indirect : large = large := rfl\n");
            fs::write(dir.join("Demo.lean"), source(old))?;
            stock_statement_build(&dir)?;
            let before = built_kernel_statements(&dir, None)?;
            fs::write(dir.join("Demo.lean"), source(new))?;
            stock_statement_build(&dir)?;
            assert_eq!(compare_kernel_statements(&before, &built_kernel_statements(&dir, None)?),
                vec!["Demo.lean::indirect", "Demo.lean::pinned"]);
        }
        // The parser must also preserve payloads larger than f64's maximum.
        let huge = "9".repeat(400);
        let row = format!("{{\"statement\":[\"nat\",{huge}],\"theorem\":\"t\",\"deps\":[]}}\n{{\"module\":\"Demo\",\"complete\":true}}\n");
        assert_ne!(parse_kernel_statement_dump(row.as_bytes(), "Demo")?,
            parse_kernel_statement_dump(row.replace(&huge, &(huge.clone() + "1")).as_bytes(), "Demo")?);
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn project_lean_executable_cannot_replay_statement_dumps() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo-statement-spoof-{}-{}", std::process::id(), pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(dir.join("lakefile.toml"), r#"name = "spoof-fixture"
defaultTargets = ["Demo", "lean"]
[[lean_lib]]
name = "Demo"
[[lean_exe]]
name = "lean"
root = "Spoof"
"#)?;
        let theorem = "theorem pinned : (1 : Nat) = 1 := rfl\n";
        fs::write(dir.join("Demo.lean"), theorem)?;
        fs::write(dir.join("Outside.lean"), theorem.replace("pinned", "outside"))?;
        fs::write(dir.join("Spoof.lean"), "def main : IO Unit := pure ()\n")?;
        stock_statement_build(&dir)?;
        let before = built_kernel_statements(&dir, None)?;
        // Capture an actual old dump, then make the default project `lean` replay it.
        let helper = dir.join("Dump.lean");
        fs::write(&helper, include_str!("../../../lean/TurboLean/StatementHash.lean"))?;
        let stale = statement_lean_command(&dir, false)?
            .arg("--run").arg(&helper).args(["Demo", "Outside", "Spoof"]).output()?;
        assert!(stale.status.success());
        fs::remove_file(helper)?;
        fs::write(dir.join("Spoof.lean"), format!(
            "def main : IO Unit := IO.print {}\n",
            serde_json::to_string(std::str::from_utf8(&stale.stdout)?)?
        ))?;
        fs::write(dir.join("Demo.lean"), theorem.replace("1", "2"))?;
        fs::write(dir.join("Outside.lean"), theorem.replace("pinned", "outside").replace("1", "2"))?;
        stock_statement_build(&dir)?;
        // Confirm that the vulnerable invocation really does replay the old JSONL.
        let replay = statement_lake_command(&dir, false)?
            .args(["env", "lean", "--run", "unused.lean", "Demo"]).output()?;
        assert!(replay.status.success());
        assert_eq!(replay.stdout, stale.stdout);
        assert_eq!(compare_kernel_statements(&before, &built_kernel_statements(&dir, None)?),
            vec!["Demo.lean::pinned", "Outside.lean::outside"]);
        fs::write(dir.join("Outside.lean"), "theorem outside : False := by trivial\n")?;
        assert!(stock_statement_build(&dir).is_err(),
            "the project lean executable must not bypass standalone stock compilation");
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn kernel_policy_is_resolved_at_base_and_never_admits_forbidden_axioms() -> Result<()> {
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo-kernel-policy-{}-{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        let config = "[axioms]\nallow = [\"*._native.native_decide.ax_*\"]\n[csimp]\nallow = [\"Fixture.fast_eq\"]\n";
        fs::write(
            dir.join("turbo-lean.toml"),
            config.replace("*._native.native_decide.ax_*", ""),
        )?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(dir.join(".gitignore"), ".lake/\n")?;
        fs::write(dir.join("lakefile.toml"), "name = \"policy-fixture\"\ndefaultTargets = [\"Fixture\"]\n[[lean_lib]]\nname = \"Fixture\"\n")?;
        fs::write(
            dir.join("Fixture.lean"),
            r#"import Lean
namespace Fixture
@[noinline] def slow (n : Nat) : Nat := n + 0
@[noinline] def fast (n : Nat) : Nat := n
@[csimp] theorem fast_eq : @slow = @fast := by
  funext n
  simp [slow, fast]
def callSlow (n : Nat) : Nat := slow n
theorem witness : (1 + 1 : Nat) = 2 := by native_decide
end Fixture
"#,
        )?;
        git_init_and_commit(&dir, "deny native, allow csimp")?;
        // The remaining bases keep native permission; isolate csimp rejection from axiom rejection.
        for (permission, label) in [
            ("", "deny"),
            ("Fixture.other_eq", "wrong name"),
            ("Fixture.fast_eq", "allow"),
        ] {
            fs::write(
                dir.join("turbo-lean.toml"),
                config.replace("Fixture.fast_eq", permission),
            )?;
            git_init_and_commit(&dir, label)?;
        }
        stock_statement_build(&dir)?;
        if crate::module_builder::probe_bwrap_sandbox().is_some() {
            fs::write(dir.join("fixture.c"), "int fixture(void) { return 0; }\n")?;
            let mut command = statement_lake_command(&dir, true)?;
            command.args(["env", "cc", "-c", "fixture.c", "-o", "fixture.o"]);
            let out = crate::module_builder::run_command_with_timeout(
                &mut command,
                std::time::Duration::from_secs(30),
                true,
            )?;
            assert!(
                out.status.success(),
                "sandboxed stock Lake must resolve the system C compiler: {}",
                String::from_utf8_lossy(&out.stderr)
            );
            fs::remove_file(dir.join("fixture.c"))?;
            fs::remove_file(dir.join("fixture.o"))?;
        }
        let mut report = built_kernel_statement_report(&dir, None, false)?;
        assert_eq!(report.csimp, vec!["Fixture.fast_eq"]);
        assert!(report
            .audits
            .iter()
            .flat_map(|row| &row.axioms)
            .any(|axiom| axiom.starts_with("Fixture.witness._native.native_decide.ax_")));
        let allowed = StatementPolicy::at(&dir, "HEAD");
        allowed.audit(&report)?;
        let cfg = crate::module_builder::resolve_project_config_with_trust(&dir, true)?;
        let store = TurboStore::open(Some(&dir.join(".lake/auditor-cache")))?;
        let env = std::collections::HashMap::from([
            (
                "LEAN_PATH".into(),
                cfg.toolchain_lib_lean.to_string_lossy().into_owned(),
            ),
            (
                "LD_LIBRARY_PATH".into(),
                cfg.toolchain_lib.to_string_lossy().into_owned(),
            ),
        ]);
        let auditor = crate::zygote::ensure_zygote_binary(&store, &cfg.lean_bin, &env)?;
        let (lp, _) = crate::module_builder::build_lean_search_path(&cfg, true);
        for (permission, expected) in [
            ("Fixture.fast_eq", true),
            ("Fixture.other_eq", false),
            ("", false),
        ] {
            let out = Command::new(&auditor)
                .args(["--audit-modules", "Fixture"])
                .envs(&env)
                .env("LEAN_PATH", &lp)
                .env(splitter::ALLOWED_AXIOMS_ENV, "*._native.native_decide.ax_*")
                .env("TURBO_LEAN_ALLOWED_CSIMP", permission)
                .output()?;
            assert_eq!(
                out.status.success(),
                expected,
                "compiled auditor csimp policy {permission:?}: {}\n{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
        }
        println!("kernel policy compiled auditor: exact csimp permission admitted; wrong/absent permission rejected");
        let cli = std::env::current_exe()?
            .parent()
            .and_then(Path::parent)
            .map(|path| path.join("turbo-lean"))
            .filter(|path| path.is_file());
        let verify = |command: &str, mode: &str, base: &str| -> Result<std::process::Output> {
            let mut cmd = Command::new(
                cli.as_ref()
                    .context("Build the release CLI before the policy fixture")?,
            );
            cmd.args(["--no-telemetry", "--json", command, "--project-dir"])
                .arg(&dir)
                // A policy inherited from another checkout must not override --base.
                .env("TURBO_LEAN_ALLOWED_CSIMP", "*")
                .env("TURBO_LEAN_ALLOWED_CSIMP_FROM_CONFIG", "1")
                .env(splitter::ALLOWED_AXIOMS_ENV, "*")
                .env(splitter::ALLOWED_AXIOMS_FROM_CONFIG_ENV, "1")
                .env("TURBO_LEAN_HOME", dir.join(".lake/turbo-policy-cache"))
                .env("TURBO_LEAN_NO_DAEMON", "1");
            // Exercise ci-verify's default trusted mode, too.
            if mode != "trusted" {
                cmd.args(["--mode", mode]);
            }
            if !base.is_empty() {
                cmd.args(["--base", base]);
            }
            if command == "pr-verify" {
                cmd.arg("--disallow-statement-changes");
            }
            Ok(cmd.output()?)
        };
        let verify_default_policy = |mode: &str| -> Result<()> {
            let out = verify("ci-verify", mode, "")?;
            let diagnostic = format!("{}{}",
                String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
            assert!(!out.status.success()
                && diagnostic.contains("restrictive default policy")
                && diagnostic.contains("native_decide"),
                "{mode} ci-verify without --base must reject checkout/inherited allowlists and explain defaults: {diagnostic}");
            println!("kernel policy {mode} ci-verify: checkout/inherited config ignored without --base");
            Ok(())
        };
        if cli.is_some() {
            verify_default_policy("trusted")?;
            let sandbox = crate::module_builder::probe_bwrap_sandbox().is_some();
            for (command, mode) in [
                ("pr-verify", "trusted"),
                ("pr-verify", "untrusted"),
                ("ci-verify", "untrusted"),
            ] {
                if mode == "untrusted" && !sandbox {
                    println!(
                        "kernel policy {mode} {command} fixtures skipped: no working bubblewrap"
                    );
                    continue;
                }
                let out = verify(command, mode, "HEAD")?;
                assert!(
                    out.status.success(),
                    "base-allowlisted csimp/native must pass {mode} {command}: {}\n{}",
                    String::from_utf8_lossy(&out.stdout),
                    String::from_utf8_lossy(&out.stderr)
                );
                println!(
                    "kernel policy {mode} {command}: base-allowlisted csimp/native_decide admitted"
                );
                let out = verify(command, mode, "HEAD^^^")?;
                let diagnostic = format!(
                    "{}{}",
                    String::from_utf8_lossy(&out.stdout),
                    String::from_utf8_lossy(&out.stderr)
                );
                assert!(!out.status.success() && diagnostic.contains("native_decide"),
                    "{mode} {command} must reject native_decide without base axiom permission: {diagnostic}");
                println!("kernel policy {mode} {command}: unallowed native_decide rejected");
                // Reuse the cache: a pass under one policy must not authorize another.
                for base in ["HEAD^", "HEAD^^"] {
                    let out = verify(command, mode, base)?;
                    let diagnostic = format!(
                        "{}{}",
                        String::from_utf8_lossy(&out.stdout),
                        String::from_utf8_lossy(&out.stderr)
                    );
                    assert!(!out.status.success() && diagnostic.contains("csimp"),
                        "{mode} {command} must reject non-allowlisted/head-only csimp under {base}: {diagnostic}");
                    println!("kernel policy {mode} {command}: non-allowlisted/head-only csimp rejected ({base})");
                }
                if command == "ci-verify" {
                    verify_default_policy(mode)?;
                }
            }
        }
        fs::write(
            dir.join("turbo-lean.toml"),
            "[axioms]\nallow = []\n[csimp]\nallow = []\n",
        )?;
        StatementPolicy::at(&dir, "HEAD").audit(&report)?;
        git_init_and_commit(&dir, "remove audited policy")?;
        fs::write(dir.join("turbo-lean.toml"), config)?;
        if cli.is_some() {
            assert!(
                !verify("pr-verify", "trusted", "HEAD")?.status.success(),
                "head-only policy must fail pr-verify"
            );
        }
        assert!(
            StatementPolicy::at(&dir, "HEAD").audit(&report).is_err(),
            "head policy must not authorize native_decide"
        );
        report.audits.clear();
        assert!(
            StatementPolicy::at(&dir, "HEAD").audit(&report).is_err(),
            "head policy must not authorize csimp"
        );
        let wildcard = StatementPolicy {
            axioms: vec!["*".into()],
            csimp: vec!["*".into()],
        };
        report.csimp.clear();
        for forbidden in ["sorryAx", "Lean.trustCompiler"] {
            report.audits = vec![KernelAudit {
                audit: "Fixture.bad".into(),
                axioms: vec![forbidden.into()],
            }];
            assert!(
                wildcard.audit(&report).is_err(),
                "{forbidden} must fail even under wildcard policy"
            );
        }
        report.audits = vec![KernelAudit {
            audit: "Fixture.bad".into(),
            axioms: vec!["Fixture.unreviewed".into()],
        }];
        assert!(
            allowed.audit(&report).is_err(),
            "unallowed custom axioms must fail"
        );
        println!("kernel policy fixtures: base-only csimp/native_decide allow and deny pass; sorryAx/trustCompiler/unallowed axioms rejected");
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn lakefile_only_option_change_classifies_affected_theorems() -> Result<()> {
        let dir = std::env::temp_dir().join(format!("turbo_pr_options_{}", pack::next_tmp_id()));
        let repo = dir.join("repo");
        fs::create_dir_all(repo.join("Demo"))?;
        fs::create_dir_all(repo.join("Other"))?;
        fs::write(
            repo.join("Demo/A.lean"),
            "theorem affected : True := by trivial\n",
        )?;
        fs::write(
            repo.join("Other/B.lean"),
            "theorem unaffected : True := by trivial\n",
        )?;
        let config = |heartbeats| {
            format!(
            "name = \"demo\"\n[[lean_lib]]\nname = \"Demo\"\nmoreLeanArgs = [\"-DmaxHeartbeats={heartbeats}\"]\n[[lean_lib]]\nname = \"Other\"\n"
        )
        };
        fs::write(repo.join("lakefile.toml"), config(4_000_000))?;
        git_init_and_commit(&repo, "base options")?;
        let repo = repo.canonicalize()?;
        let tc = "leanprover/lean4:v4.35.0";
        let base = resolve_git_head_sha(&repo, "HEAD").unwrap();
        let store = TurboStore::open(Some(&dir.join("store")))?;
        let paths = vec![repo.join("Demo/A.lean"), repo.join("Other/B.lean")];
        warm_git_head_tree_cache(&store, &repo, &paths, tc, None);
        assert_eq!(
            load_and_classify_pr_from_git(&store, &repo, "HEAD", tc)?
                .0
                .unchanged_theorems
                .len(),
            2
        );
        fs::write(repo.join("lakefile.toml"), config(200_000))?;
        for base_ref in ["HEAD", base.as_str()] {
            let (cls, changed, _, _) = load_and_classify_pr_from_git(&store, &repo, base_ref, tc)?;
            assert_eq!(cls.unchanged_theorems, vec!["Other/B.lean::unaffected"]);
            assert_eq!(cls.statement_edited_theorems, vec!["Demo/A.lean::affected"]);
            assert_eq!(cls.altered_interface_files, vec!["Demo/A.lean"]);
            assert_eq!(changed["Demo/A.lean"].len(), 1);
            assert!(!changed["Demo/A.lean"][0].2);
        }
        git_init_and_commit(&repo, "head options")?;
        for base_ref in [base.as_str(), "HEAD~1", "HEAD^", &base[..12]] {
            assert_eq!(
                load_and_classify_pr_from_git(&store, &repo, base_ref, tc)?
                    .0
                    .statement_edited_theorems,
                vec!["Demo/A.lean::affected"]
            );
        }
        assert!(load_and_classify_pr_from_git(&store, &repo, "invalid-base-ref", tc).is_err());
        fs::write(
            repo.join("lakefile.toml"),
            "name = \"bad\"\nmoreLeanArgs = [\"--plugin=bad.so\"]\n",
        )?;
        let err = load_and_classify_pr_from_git(&store, &repo, &base, tc).unwrap_err();
        assert!(format!("{err:#}").contains("Failed to resolve Lean options"));
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

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

    fn git_init_and_commit(repo_dir: &Path, msg: &str) -> Result<()> {
        for args in [
            &["init", "-q"][..],
            &["config", "user.email", "test@example.com"],
            &["config", "user.name", "Test"],
            &["add", "."],
            &["commit", "-q", "--no-gpg-sign", "-m", msg],
        ] {
            assert!(Command::new("git").args(args).current_dir(repo_dir).status()?.success());
        }
        Ok(())
    }

    fn write_mock_verified_module_sidecars(
        proj_dir: &Path,
        rel_src: &str,
        rel_olean_slash: &str,
        src_raw: &str,
        tag: &[u8],
    ) -> Result<()> {
        let cfg = crate::module_builder::resolve_project_config(proj_dir)?;
        let olean_path = proj_dir
            .join(".lake/build/lib/lean")
            .join(format!("{}.olean", rel_olean_slash));
        fs::create_dir_all(olean_path.parent().unwrap())?;
        let mut olean_bytes = b"olean-mock-v4.35.0-padding-00000000-".to_vec();
        olean_bytes.extend_from_slice(tag);
        let ilean_bytes = b"{}";
        fs::write(&olean_path, &olean_bytes)?;
        fs::write(
            format!("{}.hash", olean_path.display()),
            format!(
                "{:016x}\n",
                crate::module_builder::lake_hash_bytes(&olean_bytes)
            ),
        )?;
        let ilean_path = olean_path.with_extension("ilean");
        fs::write(&ilean_path, ilean_bytes)?;
        fs::write(
            format!("{}.hash", ilean_path.display()),
            format!(
                "{:016x}\n",
                crate::module_builder::lake_hash_bytes(ilean_bytes)
            ),
        )?;
        let olean_h = crate::module_builder::lake_hash_bytes(&olean_bytes);
        let ilean_h = crate::module_builder::lake_hash_bytes(ilean_bytes);
        let src_h = crate::module_builder::lake_hash_text(src_raw);
        let z = 0u64;
        let dep_h = crate::module_builder::lake_mix_hash(
            crate::module_builder::lake_mix_hash(
                crate::module_builder::lake_mix_hash(
                    crate::module_builder::lake_mix_hash(1723, z),
                    z,
                ),
                z,
            ),
            src_h,
        );
        let trace_json = serde_json::json!({
            "schemaVersion": "2025-09-10",
            "depHash": format!("{:016x}", dep_h),
            "inputs": [
                ["a", format!("{:016x}", z)],
                ["b", format!("{:016x}", z)],
                ["c", format!("{:016x}", z)],
                ["src", format!("{:016x}", src_h)]
            ],
            "outputs": {
                "m": false,
                "o": [format!("{:016x}.olean", olean_h)],
                "i": format!("{:016x}.ilean", ilean_h)
            }
        });
        fs::write(
            olean_path.with_extension("trace"),
            serde_json::to_vec(&trace_json)?,
        )?;
        let art_dig = crate::module_builder::compute_olean_artifact_set_digest(&olean_path)?;
        let manifest_path = proj_dir.join(".lake/build/.turbo_verified_sources.json");
        let mut manifest: crate::module_builder::VerifiedDepManifest = fs::read(&manifest_path)
            .ok()
            .and_then(|b| serde_json::from_slice(&b).ok())
            .unwrap_or_else(|| crate::module_builder::VerifiedDepManifest {
                pkg_name: cfg.root_pkg.name.clone(),
                toolchain: cfg.toolchain.clone(),
                lean_githash: cfg.lean_githash.clone(),
                pkg_config_digest: cfg.root_pkg.config_digest.clone(),
                workspace_config_digest: cfg.canonical_config_digest.clone(),
                allowed_axioms: crate::splitter::allowed_axioms(),
                modules: BTreeMap::new(),
            });
        manifest.modules.insert(
            rel_src.to_string(),
            crate::module_builder::VerifiedDepModuleEntry {
                src_blake3: blake3::hash(src_raw.as_bytes()).to_hex().to_string(),
                olean_artifact_digest: art_dig,
                kernel_audited: true,
            },
        );
        fs::write(&manifest_path, serde_json::to_vec(&manifest)?)?;
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
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"demo_pkg\"\n[[lean_lib]]\nname = \"Demo\"\nroots = [\"Demo.Basic\"]\n",
        )?;
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

        write_mock_verified_module_sidecars(
            &proj_dir,
            "Demo/Basic.lean",
            "Demo/Basic",
            src_v1,
            b"v1",
        )?;
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
    fn test_rebase_with_trace_and_transitive_import_staleness_invalidation() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_rebase_trace_stale_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let proj_dir = tmp_dir.join("repo");
        fs::create_dir_all(proj_dir.join("Guest"))?;
        fs::create_dir_all(proj_dir.join("submission/InitECandidate/Solver"))?;
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"rebase_pkg\"\n[[lean_lib]]\nname = \"Guest\"\nroots = [\"Guest.Ast\"]\n[[lean_lib]]\nname = \"InitECandidate\"\nsrcDir = \"submission\"\nroots = [\"InitECandidate.Solver.GuestStepBound\"]\n",
        )?;

        let ast_v1 = "namespace Guest\ndef totalCols : Nat := 928\nend Guest\n";
        let bound_v1 = "import Guest.Ast\nnamespace InitECandidate.Solver\ntheorem col_eq : Guest.totalCols = 928 := rfl\nend InitECandidate.Solver\n";
        let ast_file = proj_dir.join("Guest/Ast.lean");
        let bound_file = proj_dir.join("submission/InitECandidate/Solver/GuestStepBound.lean");
        fs::write(&ast_file, ast_v1)?;
        fs::write(&bound_file, bound_v1)?;
        git_init_and_commit(&proj_dir, "v1")?;

        let ast_olean = proj_dir.join(".lake/build/lib/lean/Guest/Ast.olean");
        let bound_olean =
            proj_dir.join(".lake/build/lib/lean/InitECandidate/Solver/GuestStepBound.olean");
        write_mock_verified_module_sidecars(
            &proj_dir,
            "Guest/Ast.lean",
            "Guest/Ast",
            ast_v1,
            b"ast-v1",
        )?;
        write_mock_verified_module_sidecars(
            &proj_dir,
            "submission/InitECandidate/Solver/GuestStepBound.lean",
            "InitECandidate/Solver/GuestStepBound",
            bound_v1,
            b"bound-v1",
        )?;

        let hashes_v1 = BTreeMap::from([
            (
                "Guest/Ast.lean".to_string(),
                blake3::hash(ast_v1.as_bytes()).to_hex().to_string(),
            ),
            (
                "submission/InitECandidate/Solver/GuestStepBound.lean".to_string(),
                blake3::hash(bound_v1.as_bytes()).to_hex().to_string(),
            ),
        ]);
        assert!(are_all_project_oleans_up_to_date(&proj_dir, &hashes_v1));
        assert!(is_file_verified_in_lake_build(
            &proj_dir,
            &bound_file,
            bound_v1
        ));
        assert_eq!(
            crate::lake_build::resolve_prebuilt_module_import(&proj_dir, &bound_file).as_deref(),
            Some("InitECandidate.Solver.GuestStepBound")
        );

        let dep_hashes_v1 = compute_imported_olean_interface_hashes(bound_v1, &proj_dir, None);

        // Simulate `git rebase` onto upstream where `Guest/Ast.lean` changed (928 -> 934),
        // `git status` is clean, `.trace` files exist, and `Ast.olean` has NOT been rebuilt.
        let ast_v2 = "namespace Guest\ndef totalCols : Nat := 934\nend Guest\n";
        fs::write(&ast_file, ast_v2)?;
        for args in [
            &["add", "Guest/Ast.lean"][..],
            &["commit", "-q", "--no-gpg-sign", "-m", "upstream ast 934"],
        ] {
            assert!(Command::new("git")
                .args(args)
                .current_dir(&proj_dir)
                .status()?
                .success());
        }

        // 1. `compute_imported_olean_interface_hashes` must change immediately even when `Ast.olean` on disk is untouched!
        let dep_hashes_v2 = compute_imported_olean_interface_hashes(bound_v1, &proj_dir, None);
        assert_ne!(dep_hashes_v1, dep_hashes_v2);

        // 2. Even before `are_all_project_oleans_up_to_date` runs, `is_file_verified_in_lake_build` and
        // `resolve_prebuilt_module_import` on the unchanged downstream `GuestStepBound.lean` must return false/None
        // because its transitive import `Guest/Ast.lean` no longer matches `.turbo_lean_verified_sources.json`!
        assert!(!is_file_verified_in_lake_build(
            &proj_dir,
            &bound_file,
            bound_v1
        ));
        assert!(
            crate::lake_build::resolve_prebuilt_module_import(&proj_dir, &bound_file).is_none()
        );

        // 3. `are_all_project_oleans_up_to_date` must return `false` despite clean git status and `.trace` files!
        let hashes_v2 = BTreeMap::from([
            (
                "Guest/Ast.lean".to_string(),
                blake3::hash(ast_v2.as_bytes()).to_hex().to_string(),
            ),
            (
                "submission/InitECandidate/Solver/GuestStepBound.lean".to_string(),
                blake3::hash(bound_v1.as_bytes()).to_hex().to_string(),
            ),
        ]);
        assert!(!are_all_project_oleans_up_to_date(&proj_dir, &hashes_v2));

        // 4. `ensure_project_imports_fresh_for_check` must refresh the stale `Guest/Ast.olean` via Lake
        // against `ast_v2` (not the mock `b"ast-v1"` bytes) without deleting `GuestStepBound.olean`.
        let refreshed = crate::lake_build::ensure_project_imports_fresh_for_check(
            &proj_dir,
            std::slice::from_ref(&bound_file),
        )?;
        assert_eq!(refreshed, 1);
        assert!(ast_olean.is_file() && bound_olean.is_file());
        assert!(!fs::read(&ast_olean)?.ends_with(b"ast-v1"));

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
        git_init_and_commit(&repo_dir, "init")?;

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

    #[cfg(unix)]
    #[test]
    fn test_ci_lakefile_only_edit_rejects_stale_build_and_shard_seeding() -> Result<()> {
        use crate::worktree_test_support::LakeTree;
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let source = "theorem ident (x : α) : x = x := rfl\n";
        for (kind, dependency) in [("toml", false), ("lean", false), ("toml", true)] {
            let tree = LakeTree::new("ci_config", &[("P/A.lean", source)])?;
            let pkg_root = if dependency {
                let dep = tree.project.join(".lake/packages/Dep");
                fs::create_dir_all(&dep)?;
                fs::write(dep.join("Dep.lean"), source)?;
                fs::write(tree.project.join("P/A.lean"), "import Dep\n")?;
                fs::write(
                    tree.project.join("lake-manifest.json"),
                    serde_json::to_vec(&serde_json::json!({
                        "version": "1.2.0", "packagesDir": ".lake/packages", "name": "fixture",
                        "packages": [{ "type": "path", "name": "dep", "dir": ".lake/packages/Dep", "configFile": "lakefile.toml", "inherited": false }]
                    }))?,
                )?;
                dep
            } else {
                fs::remove_file(tree.project.join("lakefile.toml"))?;
                tree.project.clone()
            };
            let lakefile = pkg_root.join(format!("lakefile.{kind}"));
            let config = |implicit: bool| {
                if dependency {
                    format!("name = \"dep\"\nmoreLeanArgs = [\"-DautoImplicit={implicit}\"]\n[[lean_lib]]\nname = \"Dep\"\n")
                } else if kind == "toml" {
                    format!("name = \"fixture\"\nmoreLeanArgs = [\"-DautoImplicit={implicit}\"]\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n")
                } else {
                    format!("import Lake\nopen Lake DSL\npackage fixture where\n  moreLeanArgs := #[\"-DautoImplicit={implicit}\"]\nlean_lib P where\n  globs := #[.submodules `P]\n")
                }
            };
            fs::write(&lakefile, config(true))?;
            let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
            let run = |store: &mut TurboStore, seed| {
                run_ci_verify_command(
                    store,
                    true,
                    "trusted".into(),
                    tree.project.clone(),
                    None,
                    None,
                    seed,
                    None,
                )
            };
            let module_keys = |store: &TurboStore| -> Result<Vec<String>> {
                let mut stmt = store.conn.prepare(
                    "SELECT action_key FROM actions WHERE kind = 'module_full' AND status = 'completed' ORDER BY action_key")?;
                let rows = stmt.query_map([], |row| row.get(0))?;
                Ok(rows.collect::<std::result::Result<_, _>>()?)
            };
            run(&mut store, false)?;
            let warm_keys = module_keys(&store)?;
            assert_eq!(warm_keys.len(), 1);
            run(&mut store, false)?;
            assert_eq!(
                module_keys(&store)?,
                warm_keys,
                "unchanged config must reuse its identity"
            );

            // Raw lakefile contents also bind the key, even when effective options agree.
            let comment = if kind == "toml" {
                "# comment\n"
            } else {
                "-- comment\n"
            };
            fs::write(&lakefile, format!("{comment}{}", config(true)))?;
            run(&mut store, false)?;
            let valid_keys = module_keys(&store)?;
            assert_eq!(
                valid_keys.len(),
                2,
                "lakefile content digest must bind module_full"
            );

            let config_mtime = fs::metadata(&lakefile)?.modified()?;
            if dependency {
                let hashes = BTreeMap::from([(
                    "P/A.lean".into(),
                    blake3::hash(b"import Dep\n").to_hex().to_string(),
                )]);
                assert!(
                    crate::lake_build::are_all_project_oleans_up_to_date(&tree.project, &hashes),
                    "fixture must exercise the fresh-build shortcut"
                );
                // Even identical dependency config contents must obey freshness ordering.
                fs::File::options()
                    .write(true)
                    .open(&lakefile)?
                    .set_modified(
                        std::time::SystemTime::now() + std::time::Duration::from_secs(2),
                    )?;
                assert!(!crate::lake_build::are_all_project_oleans_up_to_date(
                    &tree.project,
                    &hashes
                ));
                fs::File::options()
                    .write(true)
                    .open(&lakefile)?
                    .set_modified(config_mtime)?;
            }

            // Only the lakefile changes. A cache hit would falsely certify the theorem,
            // and --seed-shards would publish it into the new option namespace.
            fs::write(&lakefile, config(false))?;
            if dependency {
                // Backdate the edit: the workspace digest must catch it independently of mtime.
                fs::File::options()
                    .write(true)
                    .open(&lakefile)?
                    .set_modified(config_mtime)?;
            }
            for seed in [false, true] {
                let err = run(&mut store, seed).unwrap_err();
                let diagnostic = format!("{err:#}");
                assert!(
                    diagnostic.contains("CI native module build failed")
                        && diagnostic.to_lowercase().contains("unknown identifier")
                        && diagnostic.contains('α'),
                    "{kind}, seed={seed}: {diagnostic}"
                );
                assert_eq!(
                    module_keys(&store)?,
                    valid_keys,
                    "failed verification published module_full"
                );
                let shards: i64 = store.conn.query_row(
                    "SELECT COUNT(*) FROM actions WHERE kind = 'theorem_shard'",
                    [],
                    |row| row.get(0),
                )?;
                assert_eq!(shards, 0, "failed CI must not seed stale shards");
                assert_eq!(
                    fs::read_to_string(pkg_root.join(if dependency {
                        "Dep.lean"
                    } else {
                        "P/A.lean"
                    }))?,
                    source
                );
            }

            // Validation must precede cache lookup in trusted mode, too.
            fs::write(&lakefile, "invalid [")?;
            assert!(format!("{:#}", run(&mut store, false).unwrap_err())
                .contains("CI static Lake config validation failed"));
        }
        Ok(())
    }
    #[test]
    fn test_lakefile_option_edit_reverifies_reconfigured_files() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_lakefile_option_edit_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let repo_dir = tmp_dir.join("repo");
        fs::create_dir_all(repo_dir.join("Fast"))?;
        fs::create_dir_all(repo_dir.join("Heavy"))?;
        let lakefile = |heavy_extra: &str| {
            format!(
                "name = \"demo\"\n\n[[lean_lib]]\nname = \"Fast\"\nroots = [\"Fast\"]\n\n[[lean_lib]]\nname = \"Heavy\"\nroots = [\"Heavy\"]\n{}",
                heavy_extra
            )
        };
        fs::write(repo_dir.join("lakefile.toml"), lakefile(""))?;
        fs::write(
            repo_dir.join("Fast/A.lean"),
            "theorem t_a : 1 + 1 = 2 := by\n  rfl\n",
        )?;
        fs::write(
            repo_dir.join("Heavy/B.lean"),
            "theorem t_b : 2 + 2 = 4 := by\n  rfl\n",
        )?;
        git_init_and_commit(&repo_dir, "init")?;

        let canon_dir = fs::canonicalize(&repo_dir)?;
        let store = TurboStore::open(Some(&tmp_dir.join("cache")))?;
        let tc = "leanprover/lean4:v4.35.0";
        let lean_paths = vec![
            canon_dir.join("Fast/A.lean"),
            canon_dir.join("Heavy/B.lean"),
        ];
        let (splits, _) = load_and_split_files_cached(&store, &lean_paths)?;
        warm_git_head_tree_cache(&store, &canon_dir, &lean_paths, tc, Some(&splits));

        // Formatting-only lakefile edit: same effective args, nothing to re-verify.
        fs::write(
            canon_dir.join("lakefile.toml"),
            format!("# comment\n{}", lakefile("")),
        )?;
        let (cls, to_verify, _, _) = load_and_classify_pr_from_git(&store, &canon_dir, "HEAD", tc)?;
        assert!(cls.modified_files.is_empty() && to_verify.is_empty());

        // Only `Heavy`'s args change: its unchanged source is re-verified (dependents too).
        fs::write(
            canon_dir.join("lakefile.toml"),
            lakefile("moreLeanArgs = [\"-DmaxHeartbeats=4000000\"]\n"),
        )?;
        let (cls, to_verify, changed_files, _) =
            load_and_classify_pr_from_git(&store, &canon_dir, "HEAD", tc)?;
        assert_eq!(cls.modified_files, vec!["Heavy/B.lean"]);
        assert_eq!(cls.altered_interface_files, vec!["Heavy/B.lean"]);
        assert_eq!(cls.unchanged_theorems, vec!["Fast/A.lean::t_a"]);
        assert_eq!(to_verify.keys().collect::<Vec<_>>(), ["Heavy/B.lean"]);
        assert!(changed_files["Heavy/B.lean"].contains("theorem t_b"));
        let heavy_key = &to_verify["Heavy/B.lean"][0].0;
        let plain_key = compute_shard_key(
            tc,
            &split_lean_source(&changed_files["Heavy/B.lean"], &[]).shards[0],
        );
        assert_ne!(heavy_key, &plain_key);

        // A source edit in a reconfigured file still re-verifies every shard, not just edited ones.
        fs::write(
            canon_dir.join("Heavy/B.lean"),
            "theorem t_b : 2 + 2 = 4 := by\n  rfl\ntheorem t_c : 3 = 3 := rfl\n",
        )?;
        let (cls, to_verify, _, _) = load_and_classify_pr_from_git(&store, &canon_dir, "HEAD", tc)?;
        assert_eq!(cls.altered_interface_files, vec!["Heavy/B.lean"]);
        assert_eq!(to_verify["Heavy/B.lean"].len(), 2);
        assert!(!cls
            .unchanged_theorems
            .iter()
            .any(|t| t.starts_with("Heavy/")));

        // Invalid current or base configuration must stop classification with an error.
        fs::write(
            canon_dir.join("lakefile.toml"),
            "name = \"demo\"\nmoreLeanArgs = [\"--plugin=evil.so\"]\n",
        )?;
        assert!(load_and_classify_pr_from_git(&store, &canon_dir, "HEAD", tc).is_err());
        fs::write(
            canon_dir.join("Heavy/B.lean"),
            "theorem t_b : 2 + 2 = 4 := by\n  rfl\n",
        )?;

        // Reject an unparsable base independently of the now-valid working tree.
        fs::write(
            canon_dir.join("lakefile.toml"),
            "name = \"demo\"\nmoreLeanArgs = [\"--plugin=evil.so\"]\n",
        )?;
        git_init_and_commit(&repo_dir, "unparsable base")?;
        fs::write(canon_dir.join("lakefile.toml"), lakefile(""))?;
        let err = load_and_classify_pr_from_git(&store, &canon_dir, "HEAD", tc).unwrap_err();
        assert!(format!("{err:#}").contains("Failed to resolve base Lean options"));
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
        let base_entry = build_cached_head_file_entry(
            &base_src,
            &sp,
            "leanprover/lean4:v4.35.0",
            None,
            Vec::new(),
            &[],
        );
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

    #[test]
    fn test_untrusted_ci_and_pr_verify_fail_closed_and_kernel_audit() -> Result<()> {
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_untrusted_pr_ci_test_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let repo_dir = tmp_dir.join("repo");
        fs::create_dir_all(repo_dir.join("Demo"))?;
        fs::write(
            repo_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;

        // 1. Dynamic `lakefile.lean` in untrusted mode must fail closed without running `lake env`.
        fs::write(
            repo_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\nrun_cmd IO.FS.writeFile \"pwned.txt\" \"1\"\npackage demo\nlean_lib Demo\n",
        )?;
        fs::write(
            repo_dir.join("Demo/Basic.lean"),
            "namespace Demo\ntheorem t_ok : 1 + 1 = 2 := rfl\nend Demo\n",
        )?;
        let fake_bwrap = crate::module_builder::ScopedTestBwrapOverride::write_fake_bwrap_script(&tmp_dir)?;
        let mut store = TurboStore::open(Some(&tmp_dir.join("store")))?;
        let run_ci = |st: &mut TurboStore, mode: &str| {
            run_ci_verify_command(st, true, mode.to_string(), repo_dir.clone(), None, None, false, None)
        };
        let run_pr = |st: &mut TurboStore, disallow_stmt: bool, max_cone: usize, rcpt: Option<PathBuf>| {
            run_pr_verify_command(
                st, true, repo_dir.clone(), "HEAD".to_string(), "untrusted".to_string(),
                disallow_stmt, rcpt, None, None, None, false, max_cone, None,
            )
        };
        let dyn_ci_err = {
            let _bwrap_guard = crate::module_builder::ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy().into_owned());
            run_ci(&mut store, "untrusted").unwrap_err().to_string()
        };
        assert!(!repo_dir.join("pwned.txt").exists());
        assert!(dyn_ci_err.contains("static") || dyn_ci_err.contains("run_cmd"), "got: {dyn_ci_err}");

        // Replace with valid static `lakefile.toml` and initialize git history.
        fs::remove_file(repo_dir.join("lakefile.lean"))?;
        fs::write(
            repo_dir.join("lakefile.toml"),
            "name = \"demo_pkg\"\ndefaultTargets = [\"Demo\"]\n[[lean_lib]]\nname = \"Demo\"\nroots = [\"Demo.Basic\"]\n",
        )?;
        git_init_and_commit(&repo_dir, "base")?;

        // 2. Missing `bwrap` (`__NONE__`) in untrusted mode must fail closed on both `ci-verify` and `pr-verify`.
        let (no_bwrap_ci, no_bwrap_pr) = {
            let _bwrap_guard = crate::module_builder::ScopedTestBwrapOverride::set("__NONE__");
            (run_ci(&mut store, "untrusted").unwrap_err().to_string(), run_pr(&mut store, false, 0, None).unwrap_err().to_string())
        };
        assert!(no_bwrap_ci.contains("requires a working bubblewrap") && no_bwrap_pr.contains("requires a working bubblewrap"));

        // 3. Same-size/same-mtime stat-cache poisoning must be bypassed in untrusted `ci-verify`.
        let demo_path = repo_dir.join("Demo/Basic.lean");
        let clean_same_len = "namespace Demo\ntheorem t_ok : 2 + 2 = 4 := rfl  \nend Demo\n";
        let sorry_padded = "namespace Demo\ntheorem t_ok : 2 + 2 = 5 := sorry\nend Demo\n";
        assert_eq!(clean_same_len.len(), sorry_padded.len());
        fs::write(&demo_path, clean_same_len)?;
        let canon_repo = fs::canonicalize(&repo_dir)?;
        let canon_demo = canon_repo.join("Demo/Basic.lean");
        let _ = load_project_stat_summary_cached(&store, &canon_repo, std::slice::from_ref(&canon_demo))?;
        #[cfg(unix)]
        let orig_mtime = {
            use std::os::unix::fs::MetadataExt;
            let m = fs::metadata(&canon_demo)?;
            (m.mtime(), m.mtime_nsec())
        };
        fs::write(&canon_demo, sorry_padded)?;
        #[cfg(unix)]
        {
            let tv = [libc::timespec { tv_sec: orig_mtime.0, tv_nsec: orig_mtime.1 }; 2];
            let c_path = std::ffi::CString::new(canon_demo.to_string_lossy().as_bytes())?;
            unsafe {
                libc::utimensat(libc::AT_FDCWD, c_path.as_ptr(), tv.as_ptr(), 0);
            }
        }
        let sorry_ci_err = {
            let _bwrap_guard = crate::module_builder::ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy().into_owned());
            run_ci(&mut store, "untrusted").unwrap_err().to_string()
        };
        assert!(sorry_ci_err.contains("Hygiene & Axiom Gate FAILED"), "got: {sorry_ci_err}");

        // 4. Clean proof edit in untrusted `pr-verify` compiles inside sandbox and passes `--audit-modules` kernel audit,
        // while a hidden macro-expanded `sorry` or false proof fails closed.
        fs::write(&canon_demo, "namespace Demo\ntheorem t_ok : 1 + 1 = 2 := by\n  decide\nend Demo\n")?;
        {
            let _bwrap_guard = crate::module_builder::ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy().into_owned());
            run_pr(&mut store, true, 0, None).expect("valid untrusted pr-verify proof edit should pass");
        }

        let hidden_ax_src = "import Lean\nopen Lean Elab Tactic in\nelab \"sneak_ax\" : tactic => do\n  let g ← getMainGoal\n  let t ← g.getType\n  let s := String.mk ['s', 'o', 'r', 'r', 'y', 'A', 'x']\n  let e ← Meta.mkAppM (Name.mkSimple s) #[t, mkConst ``false]\n  g.assign e\nnamespace Demo\ntheorem t_ok : 1 + 1 = 2 := by\n  sneak_ax\nend Demo\n";
        fs::write(&canon_demo, hidden_ax_src)?;
        {
            let _bwrap_guard = crate::module_builder::ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy().into_owned());
            assert!(run_pr(&mut store, false, 0, None).is_err());
        }

        // 5. Macro-synthesized `@[csimp]`, `@[extern]`, `@[implemented_by]`, and `_unsafe_rec` spoof attempts fail closed.
        for (case_label, bad_src) in [
            (
                "macro_csimp",
                concat!(
                    "import Lean\nopen Lean in\nsyntax (name := sneakCsimp) \"sneak_csimp_attr\" : attr\n",
                    "initialize registerBuiltinAttribute {\n  name := `sneakCsimp\n  descr := \"\"\n",
                    "  add := fun decl _ kind => Lean.Compiler.CSimp.add decl kind\n}\nnamespace Demo\n",
                    "def slowFn (x : Nat) : Nat := x\ndef fastFn (x : Nat) : Nat := x\n",
                    "@[sneakCsimp] theorem eq_fn : @slowFn = @fastFn := rfl\ntheorem t_ok : 1 + 1 = 2 := rfl\nend Demo\n",
                ),
            ),
            (
                "macro_extern",
                concat!(
                    "import Lean\nopen Lean in\nelab \"sneak_ext_decl\" : command => do\n",
                    "  let attrName := Name.mkSimple (String.mk ['e', 'x', 't', 'e', 'r', 'n'])\n",
                    "  let stx ← `( @[$(mkIdent attrName):ident \"c_puts\"] def sneakExt (x : UInt64) : UInt64 := x )\n",
                    "  Elab.Command.elabCommand stx\nnamespace Demo\nsneak_ext_decl\ntheorem t_ok : 1 + 1 = 2 := rfl\nend Demo\n",
                ),
            ),
            (
                "macro_implemented_by",
                concat!(
                    "import Lean\nopen Lean in\nelab \"sneak_impl_decl\" : command => do\n",
                    "  let attrName := Name.mkSimple (String.mk ['i', 'm', 'p', 'l', 'e', 'm', 'e', 'n', 't', 'e', 'd', '_', 'b', 'y'])\n",
                    "  let stx ← `( def fastImpl (x : Nat) : Nat := x\n               @[$(mkIdent attrName):ident fastImpl] def slowSpec (x : Nat) : Nat := x )\n",
                    "  Elab.Command.elabCommand stx\nnamespace Demo\nsneak_impl_decl\ntheorem t_ok : 1 + 1 = 2 := rfl\nend Demo\n",
                ),
            ),
            (
                "unsafe_rec_spoof",
                concat!(
                    "import Lean\nopen Lean in\nelab \"sneak_unsf_decl\" : command => do\n",
                    "  let d : Declaration := .defnDecl {\n    name := `Demo.spoofFn._unsafe_rec\n",
                    "    levelParams := []\n    type := mkConst ``Nat\n    value := mkNatLit 0\n",
                    "    hints := .opaque\n    safety := .unsafe\n  }\n  Elab.Command.liftCoreM (addDecl d)\n",
                    "namespace Demo\nsneak_unsf_decl\ntheorem t_ok : 1 + 1 = 2 := rfl\nend Demo\n",
                ),
            ),
        ] {
            fs::write(&canon_demo, bad_src)?;
            let _bwrap_guard = crate::module_builder::ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy().into_owned());
            assert!(run_ci(&mut store, "untrusted").is_err(), "ci-verify must reject {case_label}");
            assert!(run_pr(&mut store, false, 0, None).is_err(), "pr-verify must reject {case_label}");
        }

        // 6. Corrupt `.trace` / `.hash` Lake sidecar artifacts must fail closed in freshness checks.
        fs::write(&canon_demo, "namespace Demo\ntheorem t_ok : 1 + 1 = 2 := rfl\nend Demo\n")?;
        run_ci(&mut store, "trusted")?;
        let init_hashes = BTreeMap::from([(
            "Demo/Basic.lean".to_string(),
            blake3::hash(fs::read(&canon_demo)?.as_slice()).to_hex().to_string(),
        )]);
        assert!(are_all_project_oleans_up_to_date(&canon_repo, &init_hashes));
        let trace_path = canon_repo.join(".lake/build/lib/lean/Demo/Basic.trace");
        let saved_trace = fs::read(&trace_path)?;
        fs::write(&trace_path, b"corrupt-non-json-trace")?;
        assert!(!are_all_project_oleans_up_to_date(&canon_repo, &init_hashes));
        fs::write(&trace_path, &saved_trace)?;
        let hash_path = canon_repo.join(".lake/build/lib/lean/Demo/Basic.olean.hash");
        if hash_path.exists() {
            let saved_hash = fs::read(&hash_path)?;
            fs::write(&hash_path, b"0")?;
            assert!(!are_all_project_oleans_up_to_date(&canon_repo, &init_hashes));
            fs::write(&hash_path, &saved_hash)?;
        }

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_untrusted_pr_verify_multi_theorem_file_checks_full_source() -> Result<()> {
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_untrusted_pr_multi_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let repo_dir = tmp_dir.join("repo");
        fs::create_dir_all(repo_dir.join("Demo"))?;
        fs::write(repo_dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            repo_dir.join("lakefile.toml"),
            "name = \"demo_pkg\"\ndefaultTargets = [\"Demo\"]\n[[lean_lib]]\nname = \"Demo\"\nroots = [\"Demo.Basic\"]\n",
        )?;
        fs::write(
            repo_dir.join("Demo/Basic.lean"),
            "namespace Demo\ntheorem t_keep : 3 + 3 = 6 := rfl\ntheorem t_a : 1 + 1 = 2 := rfl\ntheorem t_b : 2 + 2 = 4 := rfl\nend Demo\n",
        )?;
        let fake_bwrap = crate::module_builder::ScopedTestBwrapOverride::write_fake_bwrap_script(&tmp_dir)?;
        git_init_and_commit(&repo_dir, "base")?;
        let demo_path = fs::canonicalize(&repo_dir)?.join("Demo/Basic.lean");
        let mut store = TurboStore::open(Some(&tmp_dir.join("store")))?;
        let mut run_untrusted = |src: &str| -> Result<()> {
            fs::write(&demo_path, src)?;
            let _bwrap_guard = crate::module_builder::ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy().into_owned());
            run_pr_verify_command(
                &mut store, true, repo_dir.clone(), "HEAD".to_string(), "untrusted".to_string(),
                false, None, None, None, None, false, 0, None,
            )
        };

        run_untrusted("namespace Demo\ntheorem t_keep : 3 + 3 = 6 := rfl\ntheorem t_a : 1 + 1 = 2 := by\n  decide\ntheorem t_b : 2 + 2 = 4 := rfl\nend Demo\n")?;
        run_untrusted("namespace Demo\ntheorem t_keep : 3 + 3 = 6 := rfl\ntheorem t_a : 1 + 1 = 2 := by\n  simp\ntheorem t_b : 2 + 2 = 4 := by\n  decide\nend Demo\n")?;
        assert!(run_untrusted(
            "import Lean\nopen Lean Elab Tactic in\nelab \"sneak_ax\" : tactic => do\n  let g ← getMainGoal\n  let t ← g.getType\n  let s := String.mk ['s', 'o', 'r', 'r', 'y', 'A', 'x']\n  let e ← Meta.mkAppM (Name.mkSimple s) #[t, mkConst ``false]\n  g.assign e\nnamespace Demo\ntheorem t_keep : 3 + 3 = 6 := rfl\ntheorem t_a : 1 + 1 = 2 := by\n  sneak_ax\ntheorem t_b : 2 + 2 = 4 := rfl\nend Demo\n",
        ).is_err());

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_pr_verify_rejects_native_decide_proof_edit_in_both_modes() -> Result<()> {
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let repo_dir = std::env::temp_dir().join(format!(
            "turbo_lean_pr_nd_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&repo_dir);
        fs::create_dir_all(&repo_dir)?;
        let fake_bwrap_dir = std::env::temp_dir().join(format!(
            "turbo_lean_pr_nd_bwrap_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&fake_bwrap_dir);
        fs::create_dir_all(&fake_bwrap_dir)?;
        let fake_bwrap = crate::module_builder::ScopedTestBwrapOverride::write_fake_bwrap_script(
            &fake_bwrap_dir,
        )?;
        fs::write(repo_dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(repo_dir.join("A.lean"), "theorem t : 2 ^ 3 = 8 := by native_decide\n")?;
        git_init_and_commit(&repo_dir, "base")?;
        // A proof-only edit of a `native_decide` proof (no new hygiene token) must fail in both
        // modes, even when the zygote rejection falls back to a plain `lean` run.
        fs::write(
            repo_dir.join("A.lean"),
            "theorem t : 2 ^ 3 = 8 := by (native_decide)\n",
        )?;
        for mode in ["untrusted", "trusted"] {
            let mut store = TurboStore::open(Some(&repo_dir.join(format!(".cache-{}", mode))))?;
            let _override = crate::module_builder::ScopedTestBwrapOverride::set(
                fake_bwrap.to_string_lossy().into_owned(),
            );
            let err = run_pr_verify_command(
                &mut store,
                true,
                repo_dir.clone(),
                "HEAD".into(),
                mode.into(),
                false,
                None,
                None,
                None,
                None,
                false,
                0,
                None,
            )
            .unwrap_err();
            assert!(
                err.to_string().contains("native_decide")
                    || err.to_string().contains("reduceBool")
                    || err.to_string().contains("trustCompiler"),
                "{}: {}",
                mode,
                err
            );
        }
        let _ = fs::remove_dir_all(&repo_dir);
        let _ = fs::remove_dir_all(&fake_bwrap_dir);
        Ok(())
    }

    #[test]
    fn test_trusted_pr_verify_rejects_metaprogram_sorry_proof_edits() -> Result<()> {
        // Proof-only edits that close the goal with `sorryAx` without any `sorry`/`admit` token, in
        // a file that spoofs `#print axioms`, are rejected end to end in trusted mode (by the
        // statement-policy audit, a final zygote rejection, or the audited fallback).
        let repo_dir = std::env::temp_dir().join(format!(
            "turbo_lean_pr_meta_sorry_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&repo_dir);
        fs::create_dir_all(&repo_dir)?;
        fs::write(
            repo_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        let spoof = "macro_rules\n  | `(#print axioms $i:ident) => `(#eval IO.println s!\"'{$(Lean.quote i.getId.toString)}' does not depend on any axioms\")\n";
        let base = format!("import Lean\n{}theorem t : 2 + 2 = 4 := rfl\n", spoof);
        fs::write(repo_dir.join("A.lean"), &base)?;
        git_init_and_commit(&repo_dir, "base")?;
        let proofs = [
            "run_tac Lean.Elab.admitGoal (← Lean.Elab.Tactic.getMainGoal)",
            "run_tac do\n    let g ← Lean.Elab.Tactic.getMainGoal\n    g.assign (← Lean.Meta.mkSorry (← g.getType) false)",
            "run_tac do\n    let g ← Lean.Elab.Tactic.getMainGoal\n    g.assign (Lean.mkApp2 (Lean.mkConst (Lean.Name.mkSimple (\"sor\" ++ \"ryAx\")) [Lean.levelZero]) (← g.getType) (Lean.mkConst ``Bool.false))",
        ];
        for (i, proof) in proofs.iter().enumerate() {
            let src = format!(
                "import Lean\n{}theorem t : 2 + 2 = 4 := by\n  {}\n",
                spoof, proof
            );
            fs::write(repo_dir.join("A.lean"), src)?;
            let mut store = TurboStore::open(Some(&repo_dir.join(format!(".cache-{}", i))))?;
            let res = run_pr_verify_command(
                &mut store,
                true,
                repo_dir.clone(),
                "HEAD".into(),
                "trusted".into(),
                false,
                None,
                None,
                None,
                None,
                false,
                0,
                None,
            );
            let err = res.expect_err(&format!("metaprogram sorry #{} was accepted", i));
            assert!(
                format!("{:#}", err).contains("sorryAx"),
                "#{}: {:#}",
                i,
                err
            );
        }
        let _ = fs::remove_dir_all(&repo_dir);
        Ok(())
    }

    #[test]
    fn test_pr_verify_rechecks_dependents_of_nonlocal_edits_with_lake() -> Result<()> {
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_lean_pr_lake_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(dir.join("P"))?;
        let fake_bwrap_dir = std::env::temp_dir().join(format!(
            "turbo_lean_pr_lake_bwrap_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&fake_bwrap_dir);
        fs::create_dir_all(&fake_bwrap_dir)?;
        let fake_bwrap = crate::module_builder::ScopedTestBwrapOverride::write_fake_bwrap_script(
            &fake_bwrap_dir,
        )?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        let rce_marker = dir.join("rce_build_cmd_ran");
        fs::write(
            dir.join("turbo-lean.toml"),
            format!(
                "[lake]\nbuild_command = [\"sh\", \"-c\", \"touch '{}' && lake build \\\"$@\\\"\", \"sh\"]\n",
                rce_marker.display()
            ),
        )?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"p\"\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n",
        )?;
        let a = "theorem t (n : Nat) : n + 0 = n := by\n  simp\n";
        fs::write(dir.join("P/A.lean"), a)?;
        fs::write(
            dir.join("P/B.lean"),
            "import P.A\ntheorem u (m : Nat) : m + 0 = m := t m\n",
        )?;
        fs::write(dir.join("P/C.lean"), "theorem c : True := trivial\n")?;
        let ok = |c: &mut Command| c.current_dir(&dir).output().map(|o| o.status.success());
        if !ok(Command::new("lake").args(["build", "P"])).unwrap_or(false) {
            let _ = fs::remove_dir_all(&fake_bwrap_dir);
            return Ok(());
        }
        git_init_and_commit(&dir, "base")?;
        let pr_verify_mode = |mode: &str| {
            let mut store = TurboStore::open(Some(&dir.join(format!(".cache-{}", mode))))?;
            let _override = crate::module_builder::ScopedTestBwrapOverride::set(
                fake_bwrap.to_string_lossy().into_owned(),
            );
            run_pr_verify_command(
                &mut store,
                true,
                dir.clone(),
                "HEAD".into(),
                mode.into(),
                false,
                None,
                None,
                None,
                None,
                false,
                0,
                None,
            )
        };
        let a_file = [dir.join("P/A.lean")];
        // Proof-only edit: local, checked per theorem; untrusted mode never executes `[lake] build_command`.
        fs::write(&a_file[0], a.replace("simp", "omega"))?;
        assert!(crate::lake_build::nonlocal_edits(&a_file, "HEAD").is_empty());
        pr_verify_mode("untrusted")?;
        assert!(
            !rce_marker.exists(),
            "untrusted pr-verify must never run [lake] build_command"
        );
        // Statement edit that breaks `P.B`: not local; untrusted re-check catches `P.B` inside `bwrap` without running `[lake] build_command`.
        fs::write(
            &a_file[0],
            a.replace("n + 0 = n", "0 + n = n").replace("simp", "omega"),
        )?;
        assert_eq!(crate::lake_build::nonlocal_edits(&a_file, "HEAD").len(), 1);
        let untrusted_err = format!("{:#}", pr_verify_mode("untrusted").unwrap_err());
        assert!(
            !rce_marker.exists(),
            "untrusted dependent recheck must never run [lake] build_command"
        );
        assert!(
            untrusted_err.contains("P.B") || untrusted_err.contains("P/B.lean"),
            "{}",
            untrusted_err
        );
        // Trusted mode uses `[lake] build_command` (read at `--base`) and catches `P.B` too.
        let trusted_err = pr_verify_mode("trusted").unwrap_err().to_string();
        assert!(
            rce_marker.exists(),
            "trusted dependent recheck should honor [lake] build_command at --base"
        );
        assert!(
            trusted_err.contains("P.B") || trusted_err.contains("P/B.lean"),
            "{}",
            trusted_err
        );
        let _ = fs::remove_file(&rce_marker);
        // Lake re-checks the edited module and its importers only (`P.A`, `P.B`, not `P.C`).
        fs::write(
            &a_file[0],
            a.replace("(n : Nat)", "(n : Nat) (_h : True := trivial)"),
        )?;
        let edits = crate::lake_build::nonlocal_edits(&a_file, "HEAD");
        assert_eq!(
            crate::lake_build::lake_recheck_dependents(&dir, &edits, None)?,
            2
        );
        // Non-local edit introducing an unallowed axiom (`native_decide` hidden via macro) is rejected by Stage 1C in untrusted mode.
        fs::write(
            &a_file[0],
            "macro \"nd_hide\" : tactic => `(tactic| native_decide)\ntheorem t (n : Nat) : n + 0 = n := by omega\ntheorem sneaky_nd : 2 ^ 3 = 8 := by nd_hide\n",
        )?;
        let _ = fs::remove_file(&rce_marker);
        let nd_err = format!("{:#}", pr_verify_mode("untrusted").unwrap_err());
        assert!(
            !rce_marker.exists(),
            "untrusted dependent recheck must never run [lake] build_command"
        );
        assert!(
            nd_err.contains("native_decide")
                || nd_err.contains("ofReduceBool")
                || nd_err.contains("trustCompiler"),
            "{}",
            nd_err
        );
        // `ci-verify --mode untrusted` via CLI ignores `[axioms] allow` in an untrusted `turbo-lean.toml`.
        fs::write(dir.join("turbo-lean.toml"), "[axioms]\nallow = [\"*\"]\n")?;
        let exe = std::env::current_exe()?;
        let bin_candidate = exe
            .parent()
            .and_then(|p| p.parent())
            .map(|p| p.join("turbo-lean"))
            .filter(|p| p.exists());
        if let Some(bin) = bin_candidate {
            let ci_out = Command::new(&bin)
                .args(["ci-verify", "--mode", "untrusted"])
                .arg(&dir)
                .env_remove(crate::splitter::ALLOWED_AXIOMS_ENV)
                .output()?;
            assert!(
                !ci_out.status.success(),
                "ci-verify --mode untrusted must ignore untrusted turbo-lean.toml [axioms] allow"
            );
        }
        let _ = fs::remove_dir_all(&dir);
        let _ = fs::remove_dir_all(&fake_bwrap_dir);
        Ok(())
    }

    #[test]
    fn test_pr_verify_cone_budget_overflow_fails_closed_without_emitting_receipt() -> Result<()> {
        let tmp_dir =
            std::env::temp_dir().join(format!("turbo_lean_pr_cone_overflow_{}", std::process::id()));
        let _ = fs::remove_dir_all(&tmp_dir);
        let repo_dir = tmp_dir.join("repo");
        fs::create_dir_all(repo_dir.join("Demo"))?;
        fs::write(repo_dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            repo_dir.join("Demo/A.lean"),
            "theorem t1 : 1 = 1 := rfl\ntheorem t2 : 2 = 2 := rfl\n",
        )?;
        git_init_and_commit(&repo_dir, "base")?;

        fs::write(
            repo_dir.join("Demo/A.lean"),
            "theorem t1 : 1 = 1 := by rfl\ntheorem t2 : 2 = 2 := by rfl\n",
        )?;
        let fake_bwrap =
            crate::module_builder::ScopedTestBwrapOverride::write_fake_bwrap_script(&tmp_dir)?;
        let mut store = TurboStore::open(Some(&tmp_dir.join("cache")))?;
        let receipt_path = tmp_dir.join("should_not_exist_receipt.json");
        let err = {
            let _bwrap_guard = crate::module_builder::ScopedTestBwrapOverride::set(
                fake_bwrap.to_string_lossy().into_owned(),
            );
            run_pr_verify_command(
                &mut store,
                true,
                repo_dir.clone(),
                "HEAD".to_string(),
                "untrusted".to_string(),
                false,
                Some(receipt_path.clone()),
                None,
                None,
                None,
                false,
                1,
                None,
            )
            .unwrap_err()
        };
        assert!(err.to_string().contains("cone budget exceeded") && !receipt_path.exists());
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_untrusted_import_digests_invalidate_on_dependency_package_edit() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_untrusted_dep_digests_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let repo_dir = tmp_dir.join("repo");
        let dep_dir = repo_dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("Shared"))?;
        fs::create_dir_all(repo_dir.join("Demo"))?;
        fs::write(
            repo_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"Shared\"\nroots = [\"Shared.Util\"]\n",
        )?;
        fs::write(
            dep_dir.join("Shared/Util.lean"),
            "namespace Shared\ndef val : Nat := 1\nend Shared\n",
        )?;
        fs::write(
            repo_dir.join("lake-manifest.json"),
            r#"{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [
    { "type": "path", "name": "dep_pkg", "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml", "inherited": false }
  ],
  "name": "demo_pkg",
  "lakeDir": ".lake",
  "fixedToolchain": false
}"#,
        )?;
        fs::write(
            repo_dir.join("lakefile.toml"),
            "name = \"demo_pkg\"\ndefaultTargets = [\"Demo\"]\n[[lean_lib]]\nname = \"Demo\"\nroots = [\"Demo.Basic\"]\n",
        )?;
        let demo_src = "import Shared.Util\ntheorem t : Shared.val = 1 := rfl\n";
        fs::write(repo_dir.join("Demo/Basic.lean"), demo_src)?;

        let canon_dir = fs::canonicalize(&repo_dir)?;
        let Ok(cfg1) = resolve_untrusted_pr_project_config(&canon_dir, "leanprover/lean4:v4.35.0")
        else {
            let _ = fs::remove_dir_all(&tmp_dir);
            return Ok(());
        };
        let d1 = compute_source_only_import_digests(demo_src, &canon_dir, Some(&cfg1), true)?;
        assert_eq!(d1.len(), 1);
        assert!(d1[0].starts_with("Shared.Util:pkg="));
        let sp1 = split_lean_source(demo_src, &d1);

        fs::write(
            dep_dir.join("Shared/Util.lean"),
            "namespace Shared\ndef val : Nat := 2\nend Shared\n",
        )?;
        let cfg2 = resolve_untrusted_pr_project_config(&canon_dir, "leanprover/lean4:v4.35.0")?;
        let d2 = compute_source_only_import_digests(demo_src, &canon_dir, Some(&cfg2), true)?;
        assert_ne!(d1, d2);
        let sp2 = split_lean_source(demo_src, &d2);
        assert_ne!(sp1.shards[0].prefix_env_hash, sp2.shards[0].prefix_env_hash);
        assert_ne!(
            crate::lake_build::compute_shard_key("leanprover/lean4:v4.35.0", &sp1.shards[0]),
            crate::lake_build::compute_shard_key("leanprover/lean4:v4.35.0", &sp2.shards[0])
        );

        let bad = compute_source_only_import_digests(
            "import GhostPkg.Missing\ntheorem t : 1 = 1 := rfl\n",
            &canon_dir,
            Some(&cfg2),
            true,
        );
        assert!(bad.is_err());

        // Regression test for package-defined `Lean.*` modules: an edited file whose ONLY
        // import is a root-package module under `Lean.Local` must NOT be skipped as a builtin
        // toolchain exemption (`needs_project_imports` must classify it as a project import).
        fs::create_dir_all(repo_dir.join("Lean"))?;
        fs::write(
            repo_dir.join("Lean/Local.lean"),
            "namespace Lean.Local\ndef shadowVal : Nat := 2\nend Lean.Local\n",
        )?;
        fs::write(
            repo_dir.join("lakefile.toml"),
            "name = \"demo_pkg\"\ndefaultTargets = [\"Demo\"]\n[[lean_lib]]\nname = \"Demo\"\nroots = [\"Demo.Basic\", \"Lean.Local\"]\n",
        )?;
        let cfg_lean_local =
            resolve_untrusted_pr_project_config(&canon_dir, "leanprover/lean4:v4.35.0")?;
        assert!(
            crate::module_builder::resolve_module_in_package(
                &cfg_lean_local.root_pkg,
                true,
                "Lean.Local"
            )
            .is_some(),
            "root_pkg must resolve Lean.Local before builtin toolchain check"
        );
        let d_local = compute_source_only_import_digests(
            "import Lean.Local\ntheorem t_loc : Lean.Local.shadowVal = 2 := rfl\n",
            &canon_dir,
            Some(&cfg_lean_local),
            true,
        )?;
        assert_eq!(d_local.len(), 1);
        assert!(d_local[0].starts_with("Lean.Local:pkg="));

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }
}
