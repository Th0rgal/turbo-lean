//! Git tree-aware incremental PR verification (`git-head-tree:v5:`), prefix-pread splitting,
//! BLAKE3 cryptographic verification receipts, and CI / PR command handlers.

use crate::db::{SingleflightOutcome, TurboStore};
use crate::lake_build::{
    are_all_project_oleans_replayed_in_store, are_all_project_oleans_up_to_date,
    compute_shard_key_with_args, detect_toolchain,
    ensure_project_and_imported_oleans_replayed_in_store, load_and_split_files_cached,
    load_and_split_files_with_hashes_cached, load_project_stat_summary_cached, resolve_lake_env,
    resolve_lean_bin, resolve_or_share_lake_env, resolve_remote_lean_path,
    resolve_replayed_prebuilt_module_import, resolve_replayed_proof_only_module_import,
    seed_project_theorem_shards, seed_project_theorem_shards_from_splits, stage_lake_build_outputs,
    FileSplitsWithCacheHits, SourceFileSplit,
};
use crate::pack;
use crate::splitter::{self, split_lean_source, split_lean_source_fast_no_cone};
use anyhow::{Context, Result};
use std::collections::{BTreeMap, BTreeSet};
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
    let out = crate::trusted_tools::git(dir)?
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

/// Contents at `base_ref` of each path in `repo_rels` present in that revision's tree.
/// Paths are resolved to object ids from the tree first, so an absent path (new file) is
/// distinguishable from a missing object (e.g. a promised blob in a partial clone, which
/// the trusted Git wrapper never lazily fetches): the latter is a hard error.
pub(crate) fn fetch_git_blobs_batch(
    repo_root: &Path,
    base_ref: &str,
    repo_rels: &[String],
) -> Result<std::collections::HashMap<String, String>> {
    use std::io::{BufRead, BufReader, Read, Write};
    let mut out_map = std::collections::HashMap::with_capacity(repo_rels.len());
    if repo_rels.is_empty() {
        return Ok(out_map);
    }
    anyhow::ensure!(
        !base_ref.starts_with('-'),
        "Invalid git revision `{base_ref}`"
    );
    let wanted: std::collections::HashSet<&str> = repo_rels.iter().map(String::as_str).collect();
    let tree = crate::trusted_tools::git(repo_root)?
        .arg("-C")
        .arg(repo_root)
        .args(["ls-tree", "-r", "-z", "--full-tree", base_ref, "--"])
        .output()
        .context("Failed to execute `git ls-tree`")?;
    anyhow::ensure!(
        tree.status.success(),
        "Cannot read Git tree at `{base_ref}`: {}",
        String::from_utf8_lossy(&tree.stderr).trim()
    );
    let mut blobs = Vec::new();
    for entry in tree.stdout.split(|&b| b == 0).filter(|e| !e.is_empty()) {
        let Some(tab) = entry.iter().position(|&b| b == b'\t') else {
            anyhow::bail!("Invalid Git tree entry at `{base_ref}`");
        };
        let path = String::from_utf8_lossy(&entry[tab + 1..]);
        if !wanted.contains(path.as_ref()) {
            continue;
        }
        let header = std::str::from_utf8(&entry[..tab])?;
        let fields: Vec<_> = header.split(' ').collect();
        anyhow::ensure!(fields.len() == 3, "Invalid Git tree header: {header}");
        if fields[1] == "blob" {
            blobs.push((path.into_owned(), fields[2].to_owned()));
        }
    }
    if blobs.is_empty() {
        return Ok(out_map);
    }
    let mut git = crate::trusted_tools::git(repo_root)?;
    let mut child = git
        .arg("-C")
        .arg(repo_root)
        .args(["cat-file", "--batch"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .context("Failed to spawn `git cat-file --batch`")?;
    let mut input = child.stdin.take().context("Missing Git batch stdin")?;
    let request: String = blobs.iter().map(|(_, oid)| format!("{oid}\n")).collect();
    let writer = std::thread::spawn(move || input.write_all(request.as_bytes()));
    let result = (|| -> Result<()> {
        let mut output = BufReader::new(child.stdout.take().context("Missing Git batch stdout")?);
        for (path, oid) in &blobs {
            let mut header = String::new();
            output.read_line(&mut header)?;
            let fields: Vec<_> = header.trim_end().split(' ').collect();
            anyhow::ensure!(
                fields.len() == 3 && fields[0] == oid && fields[1] == "blob",
                "Git object {oid} for `{path}` at `{base_ref}` is missing or invalid \
                 (lazy fetching is disabled): fail-closed"
            );
            let size: usize = fields[2].parse()?;
            let mut bytes = vec![0; size + 1];
            output.read_exact(&mut bytes)?;
            anyhow::ensure!(bytes.pop() == Some(b'\n'), "Invalid Git batch terminator");
            out_map.insert(path.clone(), String::from_utf8_lossy(&bytes).into_owned());
        }
        Ok(())
    })();
    if result.is_err() {
        let _ = child.kill();
    }
    let status = child.wait()?;
    let _ = writer.join();
    result?;
    anyhow::ensure!(status.success(), "Git batch object read failed");
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
) -> Option<(PathBuf, PathBuf)> {
    let lake_inputs_tag = crate::module_builder::try_project_lake_inputs_tag(canon_dir).ok()?;
    let mut h = blake3::Hasher::new();
    // v16: folds verifier provenance versions (`ZYGOTE_SCANNER_VERSION`, `ZYGOTE_REPLAY_VERSION`),
    // `theorem-shard-v8` keys, 3-byte docstring/module-doc split hashes, workspace config digest,
    // and Lake declarative input tag unconditionally.
    h.update(b"git-head-tree:v17:");
    h.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    h.update(b":");
    h.update(&crate::zygote::ZYGOTE_SCANNER_VERSION.to_le_bytes());
    h.update(&crate::zygote::ZYGOTE_REPLAY_VERSION.to_le_bytes());
    h.update(repo_root.to_string_lossy().as_bytes());
    h.update(b":");
    h.update(canon_dir.to_string_lossy().as_bytes());
    h.update(b":");
    h.update(sha.as_bytes());
    h.update(b":");
    h.update(toolchain.as_bytes());
    if let Ok(cfg) = crate::module_builder::resolve_project_config(canon_dir) {
        h.update(b":wscfg:");
        h.update(cfg.canonical_config_digest.as_bytes());
    } else if let Ok(pkg) = crate::module_builder::resolve_package_config(canon_dir, false) {
        if !pkg.config_digest.is_empty() {
            h.update(b":cfg:");
            h.update(pkg.config_digest.as_bytes());
        }
    }
    if let Some(ref tag) = lake_inputs_tag {
        h.update(b":inputs:");
        h.update(tag.as_bytes());
    }
    let key_hex = h.finalize().to_hex();
    let short_key = &key_hex[..24];
    let staging = store.fast_staging_dir();
    Some((
        staging.join(format!("git_head_tree_v16_{}.json", short_key)),
        staging.join(format!("git_head_tree_stats_v16_{}.json", short_key)),
    ))
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

    #[allow(clippy::too_many_arguments)]
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

    // Source text cannot identify macro/scoped csimp replacements or resolved
    // namespace/private names of `axiom` / `unsafe` / `@[implemented_by]` declarations reliably.
    // If `--base` config contains a policy for that category, defer those items to the
    // mandatory ConstantInfo/environment audit, which checks the exact declaration names.
    fn defer_csimp_to_kernel_gate(&mut self, project: &Path, base: &str) {
        let policy = StatementPolicy::at(project, base);
        let custom_axioms = splitter::HygieneReport::has_custom_axiom_policy_under(&policy.axioms);
        if !custom_axioms
            && policy.csimp.is_empty()
            && policy.unsafe_decls.is_empty()
            && policy.implemented_by.is_empty()
        {
            return;
        }
        for (file, items) in &mut self.flagged_files {
            items.retain(|item| {
                let kind = item.rsplit(": ").next();
                if kind == Some("axiom") && custom_axioms {
                    self.axiom_flags.push(format!(
                        "{file}: {item} (requires compiled axiom policy audit)"
                    ));
                    false
                } else if kind == Some("csimp") && !policy.csimp.is_empty() {
                    self.axiom_flags.push(format!(
                        "{file}: {item} (requires compiled csimp policy audit)"
                    ));
                    false
                } else if kind == Some("unsafe declaration") && !policy.unsafe_decls.is_empty() {
                    self.axiom_flags.push(format!(
                        "{file}: {item} (requires compiled unsafe policy audit)"
                    ));
                    false
                } else if kind == Some("implemented_by") && !policy.implemented_by.is_empty() {
                    self.axiom_flags.push(format!(
                        "{file}: {item} (requires compiled implemented_by policy audit)"
                    ));
                    false
                } else {
                    true
                }
            });
        }
        self.flagged_files.retain(|(_, items)| !items.is_empty());
    }

    #[allow(clippy::type_complexity)]
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
    let (cache_file, _) = git_head_tree_cache_paths(store, &repo_root, canon_dir, &sha, toolchain)?;
    let bytes = fs::read(&cache_file).ok()?;
    let mut cached_map =
        serde_json::from_slice::<std::collections::HashMap<String, CachedHeadFileEntry>>(&bytes)
            .ok()?;
    let entry = cached_map.remove(&rel_path_from_dir(canon_file, canon_dir))?;
    let cur_deps = crate::lake_build::compute_imported_olean_interface_hashes(
        &entry.prefix_src,
        canon_dir,
        None,
    );
    if cur_deps != entry.dep_hashes {
        return None;
    }
    Some(entry)
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
    cur_dep_hashes: &[String],
) -> (splitter::SplitResult, Option<usize>) {
    if cur_dep_hashes == base_entry.dep_hashes.as_slice() {
        if let Some((prefix_sp, cur_prefix_len)) = try_extract_and_split_prefix(cur_src, base_entry)
        {
            return (prefix_sp, Some(cur_prefix_len));
        }
    }
    (
        split_lean_source_fast_no_cone(cur_src, cur_dep_hashes),
        None,
    )
}

pub(crate) fn try_fast_split_single_file_from_path(
    store: &TurboStore,
    canon_dir: &Path,
    canon_file: &Path,
    f_sz: i64,
    toolchain: &str,
) -> Option<(String, splitter::SplitResult, usize, Vec<String>)> {
    let base_entry = load_cached_head_entry(store, canon_dir, canon_file, toolchain)?;
    let prefix_src = try_read_prefix_if_suffix_matches(canon_file, f_sz, &base_entry)?;
    let cur_deps =
        crate::lake_build::compute_imported_olean_interface_hashes(&prefix_src, canon_dir, None);
    if cur_deps != base_entry.dep_hashes {
        return None;
    }
    let prefix_sp = try_split_prefix_against_base(&prefix_src, &base_entry)?;
    let unchanged =
        prefix_src.len() == base_entry.prefix_byte_len && prefix_src == base_entry.prefix_src;
    Some((prefix_src, prefix_sp, usize::from(unchanged), cur_deps))
}

pub(crate) fn try_fast_split_single_file(
    store: &TurboStore,
    canon_dir: &Path,
    canon_file: &Path,
    src: &str,
    toolchain: &str,
    cur_dep_hashes: &[String],
) -> Option<(splitter::SplitResult, usize, usize)> {
    let base_entry = load_cached_head_entry(store, canon_dir, canon_file, toolchain)?;
    if cur_dep_hashes != base_entry.dep_hashes.as_slice() {
        return None;
    }
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
    let Some((cache_file, stats_file)) =
        git_head_tree_cache_paths(store, &repo_root, canon_dir, &sha, toolchain)
    else {
        return;
    };
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
                                if *cur_src == bs.as_str()
                                    || (cur_src.is_empty()
                                        && fs::read_to_string(p).ok().as_deref()
                                            == Some(bs.as_str()))
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
    compute_source_only_import_digests_with_tag_override(
        src,
        project_dir,
        cfg_opt,
        strict_untrusted,
        None,
    )
}

fn compute_source_only_import_digests_with_tag_override(
    src: &str,
    project_dir: &Path,
    cfg_opt: Option<&crate::module_builder::ProjectConfig>,
    strict_untrusted: bool,
    tag_override: Option<Option<String>>,
) -> Result<Vec<String>> {
    // Same synthetic entry `compute_imported_olean_interface_hashes` adds on the trusted path, so
    // an untrusted re-verification cannot reuse a split or a shard computed against older input
    // bytes either. Taken from the already-resolved config when there is one, which keeps the
    // untrusted mode's "never trust a stat, re-read the bytes" rule intact -- and, deliberately,
    // bypasses `project_lake_inputs_tag`'s per-command memo entirely: untrusted verification reads
    // its digests out of the config this run resolved, never out of a cache.
    let lake_inputs_tag = match tag_override {
        Some(tag) => tag,
        None => match cfg_opt {
            Some(cfg) => crate::module_builder::lake_inputs_tag_from_digest(
                &crate::module_builder::workspace_lake_inputs_digest(cfg)?,
            ),
            None => crate::module_builder::try_project_lake_inputs_tag(project_dir)?,
        },
    };
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
        return Ok(lake_inputs_tag.into_iter().collect());
    }
    if hdr.imports.is_empty() {
        return Ok(lake_inputs_tag.into_iter().collect());
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
            if let Some(spec) = crate::module_builder::resolve_importable_module_in_package(
                &cfg.root_pkg,
                true,
                &mod_name,
            ) {
                Some((spec.src_path, Some(spec.pkg_config_digest)))
            } else {
                let mut dep_matches = Vec::new();
                for dp in &cfg.dep_pkgs {
                    if let Some(spec) = crate::module_builder::resolve_importable_module_in_package(
                        dp, false, &mod_name,
                    ) {
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
            let is_tc = cfg_opt.is_some_and(|cfg| {
                crate::module_builder::is_builtin_toolchain_module(
                    &cfg.toolchain_lib_lean,
                    Some(&cfg.lean_githash),
                    &mod_name,
                )
            });
            if !is_tc {
                anyhow::bail!(
                    "Unresolved non-toolchain import `{}` in untrusted verification (fail-closed)",
                    mod_name
                );
            }
        }
    }
    out.extend(lake_inputs_tag);
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
#[allow(clippy::type_complexity)]
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

/// Whether any file one of the package's `input_file` / `input_dir` targets selects differs from
/// `base_ref`, or is new and untracked. Those files reach elaboration through a library's `needs`
/// without being `.lean` files, so a change must re-verify the project like a lakefile edit would.
/// A package without file inputs costs nothing here, and a git failure counts as changed.
///
/// Two deliberate over-approximations, both fail-closed:
///
/// - The git query is scoped to the declared `path`, not to the `filter`, so an edit to a file the
///   filter excludes also counts as changed.
/// - A `true` here marks *every* `.lean` file of the project as `reconfigured`, not just the
///   modules of the libraries that actually `needs` the changed input. Narrowing it would mean
///   mapping each source back to its library and that library's `needs` set; the digests in
///   [`crate::module_builder::module_lake_input_digest`] already do that precisely for the cache
///   keys, so the only cost of being coarse here is re-splitting some unaffected files.
///
/// One thing it cannot see: a symlink under `path` whose target lives outside the repository. Such
/// a symlink now fails the config resolve outright (`hash_input_target` refuses an input symlink
/// Return `true` when any file matching any package's `input_file` / `input_dir` has changed
/// (added, deleted, or modified — including git-ignored or untracked files on disk, symlinks, or
/// packages outside the git repository) relative to `base_ref`.
///
/// Reconstructs the `--base` tree per input via `git ls-tree -r -t -z --full-tree <base_ref> -- <path>`
/// and compares matched blob contents directly against the current on-disk tree via a single batched
/// `git cat-file --batch`, rejecting symlinks (`120000`) and non-blobs (`040000` is traversed only
/// for `input_dir` trees; `160000` submodules fail closed) before applying `filter := .extension ...`.
/// Every failure mode conservatively returns `true` (forcing re-verification), and `try_project_lake_inputs_tag`
/// additionally fails closed (`Err`) on out-of-package symlinks so there is no case where this
/// returns `false` for a changed input whose bytes Lake would read.
fn is_full_hex_git_oid(s: &str) -> bool {
    s.len() == 40 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

pub(crate) fn package_input_files_changed_in_git_repo(
    git_repo_root: &Path,
    pkg_prefix: &str,
    p: &crate::module_builder::PackageConfig,
    canon_pkg_root: &Path,
    git_ref: &str,
) -> bool {
    if git_ref.is_empty() || git_ref.starts_with('-') {
        return true;
    }
    let mut disk_blobs: std::collections::BTreeMap<String, Vec<u8>> =
        std::collections::BTreeMap::new();
    let mut base_blobs_to_check: std::collections::BTreeMap<String, String> =
        std::collections::BTreeMap::new();

    for inp in &p.inputs {
        if inp.path.is_absolute()
            || inp
                .path
                .components()
                .any(|c| !matches!(c, std::path::Component::Normal(_)))
        {
            return true;
        }
        // Reject symlinks on any ancestor segment inside `pkg_root -> inp.path`.
        let mut cur_anc = canon_pkg_root.to_path_buf();
        for comp in inp.path.components() {
            cur_anc.push(comp);
            match fs::symlink_metadata(&cur_anc) {
                Ok(m) if m.file_type().is_symlink() => return true,
                Err(_) => return true,
                _ => {}
            }
        }
        let inp_root = canon_pkg_root.join(&inp.path);
        let mut cur_rel_paths = std::collections::BTreeSet::new();
        if inp.is_dir {
            if !inp_root.is_dir() {
                return true;
            }
            for entry in walkdir::WalkDir::new(&inp_root).follow_links(false) {
                let Ok(e) = entry else {
                    return true;
                };
                if e.file_type().is_symlink() {
                    return true;
                }
                let ext = e.path().extension();
                if !inp.matches_extension(ext) {
                    continue;
                }
                if e.file_type().is_dir() {
                    continue;
                }
                if !e.file_type().is_file() {
                    return true;
                }
                let Ok(rel_to_repo) = e.path().strip_prefix(git_repo_root) else {
                    return true;
                };
                let Some(rel_str) = rel_to_repo.to_str() else {
                    return true;
                };
                let repo_rel = rel_str.replace('\\', "/");
                let Ok(bytes) = fs::read(e.path()) else {
                    return true;
                };
                cur_rel_paths.insert(repo_rel.clone());
                disk_blobs.insert(repo_rel, bytes);
            }
        } else {
            let Ok(meta) = fs::symlink_metadata(&inp_root) else {
                return true;
            };
            if !meta.file_type().is_file() {
                return true;
            }
            let Ok(rel_to_repo) = inp_root.strip_prefix(git_repo_root) else {
                return true;
            };
            let Some(rel_str) = rel_to_repo.to_str() else {
                return true;
            };
            let repo_rel = rel_str.replace('\\', "/");
            let Ok(bytes) = fs::read(&inp_root) else {
                return true;
            };
            cur_rel_paths.insert(repo_rel.clone());
            disk_blobs.insert(repo_rel, bytes);
        }

        let inp_repo_rel =
            join_proj_prefix(pkg_prefix, &inp.path.to_string_lossy().replace('\\', "/"));
        let inp_repo_norm = inp_repo_rel.trim_matches('/');
        if inp_repo_norm.is_empty() {
            return true;
        }
        let Ok(ls_out) = crate::trusted_tools::git(git_repo_root).and_then(|mut git| {
            git.arg("-C")
                .arg(git_repo_root)
                .args([
                    "ls-tree",
                    "-r",
                    "-t",
                    "-z",
                    "--full-tree",
                    git_ref,
                    "--",
                    inp_repo_norm,
                ])
                .output()
                .map_err(Into::into)
        }) else {
            return true;
        };
        if !ls_out.status.success() {
            return true;
        }
        let inp_dir_prefix = format!("{inp_repo_norm}/");
        let mut saw_dir_tree = false;
        let mut base_rel_paths = std::collections::BTreeSet::new();
        for rec in ls_out.stdout.split(|&b| b == 0).filter(|r| !r.is_empty()) {
            let Some(tab_pos) = rec.iter().position(|&b| b == b'\t') else {
                return true;
            };
            let Ok(meta_str) = std::str::from_utf8(&rec[..tab_pos]) else {
                return true;
            };
            let Ok(path_str) = std::str::from_utf8(&rec[tab_pos + 1..]) else {
                return true;
            };
            let mut parts = meta_str.split_whitespace();
            let (Some(mode), Some(obj_type), Some(oid)) =
                (parts.next(), parts.next(), parts.next())
            else {
                return true;
            };
            if mode == "160000" || obj_type == "commit" {
                return true;
            }
            let is_ancestor = inp_repo_norm
                .strip_prefix(path_str)
                .is_some_and(|rest| rest.starts_with('/'));
            if is_ancestor {
                if mode == "120000" || obj_type != "tree" {
                    return true;
                }
                continue;
            }
            if path_str == inp_repo_norm {
                if inp.is_dir {
                    if mode == "120000" || obj_type != "tree" {
                        return true;
                    }
                    saw_dir_tree = true;
                    continue;
                }
                if mode == "120000" || obj_type != "blob" {
                    return true;
                }
                base_rel_paths.insert(path_str.to_string());
                base_blobs_to_check.insert(path_str.to_string(), oid.to_string());
                continue;
            }
            if inp.is_dir && path_str.starts_with(&inp_dir_prefix) {
                if mode == "040000" && obj_type == "tree" {
                    continue;
                }
                if mode == "120000" || obj_type != "blob" {
                    return true;
                }
                let ext = Path::new(path_str).extension();
                if !inp.matches_extension(ext) {
                    continue;
                }
                base_rel_paths.insert(path_str.to_string());
                base_blobs_to_check.insert(path_str.to_string(), oid.to_string());
            }
        }
        if (inp.is_dir && !saw_dir_tree) || cur_rel_paths != base_rel_paths {
            return true;
        }
    }

    if base_blobs_to_check.is_empty() {
        return !disk_blobs.is_empty();
    }

    let Ok(mut git_cmd) = crate::trusted_tools::git(git_repo_root) else {
        return true;
    };
    let mut child = match git_cmd
        .arg("-C")
        .arg(git_repo_root)
        .args(["cat-file", "--batch"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
    {
        Ok(c) => c,
        Err(_) => return true,
    };
    let ordered_reqs: Vec<(&String, &String)> = base_blobs_to_check.iter().collect();
    if let Some(mut stdin) = child.stdin.take() {
        use std::io::Write;
        let mut req_buf = String::new();
        for (_, oid) in &ordered_reqs {
            req_buf.push_str(oid);
            req_buf.push('\n');
        }
        if stdin.write_all(req_buf.as_bytes()).is_err() {
            return true;
        }
    }
    let Ok(out) = child.wait_with_output() else {
        return true;
    };
    if !out.status.success() {
        return true;
    }
    let bytes = &out.stdout;
    let mut pos = 0usize;
    for (repo_rel, _) in ordered_reqs {
        let Some(nl_rel) = bytes[pos..].iter().position(|&b| b == b'\n') else {
            return true;
        };
        let Ok(header) = std::str::from_utf8(&bytes[pos..pos + nl_rel]) else {
            return true;
        };
        pos += nl_rel + 1;
        let parts: Vec<&str> = header.split_whitespace().collect();
        if parts.len() < 3 || parts[1] != "blob" {
            return true;
        }
        let Ok(sz) = parts[2].parse::<usize>() else {
            return true;
        };
        if pos + sz > bytes.len() {
            return true;
        }
        let Some(disk_bytes) = disk_blobs.get(repo_rel) else {
            return true;
        };
        if &bytes[pos..pos + sz] != disk_bytes.as_slice() {
            return true;
        }
        pos += sz;
        if pos < bytes.len() && bytes[pos] == b'\n' {
            pos += 1;
        }
    }
    false
}

fn pinned_manifest_git_dep_revs(
    canon_repo_root: &Path,
    proj_prefix: &str,
    canon_proj_dir: &Path,
    base_ref: &str,
) -> std::collections::HashMap<String, (PathBuf, String)> {
    let mut out = std::collections::HashMap::new();
    let Ok(sha) = resolve_git_commit_sha(canon_repo_root, base_ref) else {
        return out;
    };
    let manifest_repo_rel = join_proj_prefix(proj_prefix, "lake-manifest.json");
    let Ok(mut blobs) = fetch_git_blobs_batch(
        canon_repo_root,
        &sha,
        std::slice::from_ref(&manifest_repo_rel),
    ) else {
        return out;
    };
    let Some(raw_base) = blobs.remove(&manifest_repo_rel) else {
        return out;
    };
    let Ok((_, base_entries, _)) = crate::module_builder::parse_lake_manifest_str(
        canon_proj_dir,
        &canon_proj_dir.join("lake-manifest.json"),
        &raw_base,
        false,
    ) else {
        return out;
    };
    let Ok((cur_pkgs_dir, cur_entries, _)) =
        crate::module_builder::parse_lake_manifest(canon_proj_dir, false)
    else {
        return out;
    };
    let cur_by_name: std::collections::HashMap<
        String,
        crate::module_builder::ManifestPackageEntry,
    > = cur_entries
        .into_iter()
        .map(|e| (e.name.clone(), e))
        .collect();

    for base_mp in base_entries {
        if base_mp.pkg_type == "path" {
            continue;
        }
        let Some(ref rev) = base_mp.rev else {
            continue;
        };
        if !is_full_hex_git_oid(rev) {
            continue;
        }
        let Some(cur_mp) = cur_by_name.get(&base_mp.name) else {
            continue;
        };
        if cur_mp.pkg_type != "path" && cur_mp.rev.as_deref() == Some(rev.as_str()) {
            let repo_dir = canon_proj_dir.join(&cur_pkgs_dir).join(&cur_mp.name);
            out.insert(base_mp.name, (repo_dir, rev.clone()));
        }
    }
    out
}

fn parse_staged_base_package_config(
    store: &TurboStore,
    pkg_root: &Path,
    raw: &str,
    is_toml: bool,
    is_root_pkg: bool,
) -> Result<crate::module_builder::PackageConfig> {
    let staged = crate::shm_cache::StagedTempFile::write(
        store.fast_staging_dir().join(format!(
            "base-lakefile-{}-{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        )),
        raw,
    )?;
    let result = if is_toml {
        crate::module_builder::parse_lakefile_toml_without_disk_inputs(
            pkg_root,
            &staged,
            is_root_pkg,
        )
    } else {
        crate::module_builder::parse_lakefile_lean_without_disk_inputs(
            pkg_root,
            &staged,
            is_root_pkg,
        )
    };
    drop(staged);
    result
}

fn lake_input_files_changed_since_base(
    repo_root: &Path,
    proj_prefix: &str,
    pkg: &crate::module_builder::PackageConfig,
    dep_pkgs: &[crate::module_builder::PackageConfig],
    base_ref: &str,
) -> bool {
    let Ok(canon_repo_root) = fs::canonicalize(repo_root) else {
        return true;
    };
    let all_pkgs: Vec<(bool, &crate::module_builder::PackageConfig)> = std::iter::once((true, pkg))
        .chain(dep_pkgs.iter().map(|d| (false, d)))
        .collect();
    if all_pkgs.iter().all(|(_, p)| p.inputs.is_empty()) {
        return false;
    }

    let canon_proj_dir = if proj_prefix.trim_matches('/').is_empty() {
        canon_repo_root.clone()
    } else {
        match fs::canonicalize(canon_repo_root.join(proj_prefix.trim_matches('/'))) {
            Ok(d) => d,
            Err(_) => return true,
        }
    };
    let pinned_git_deps = if dep_pkgs.iter().any(|d| !d.inputs.is_empty()) {
        pinned_manifest_git_dep_revs(&canon_repo_root, proj_prefix, &canon_proj_dir, base_ref)
    } else {
        std::collections::HashMap::new()
    };

    for (is_root, p) in all_pkgs {
        if p.unsupported.is_some() || p.inputs.iter().any(|i| i.unsupported.is_some()) {
            return true;
        }
        if p.inputs.is_empty() {
            continue;
        }
        let Ok(canon_pkg_root) = fs::canonicalize(&p.pkg_root) else {
            return true;
        };
        if !is_root {
            if let Some((dep_git_dir, dep_rev)) = pinned_git_deps.get(&p.name) {
                let Ok(canon_dep_git_root) = fs::canonicalize(dep_git_dir) else {
                    return true;
                };
                if !canon_dep_git_root.join(".git").exists()
                    || !canon_pkg_root.starts_with(&canon_dep_git_root)
                {
                    return true;
                }
                // Reject symlinks between the dependency's git root and `subDir` (if any), while
                // permitting a worktree symlink at `.lake/packages` above `dep_git_dir`.
                if let Ok(rel_sub) = canon_pkg_root.strip_prefix(&canon_dep_git_root) {
                    let mut cur = canon_dep_git_root.clone();
                    for comp in rel_sub.components() {
                        cur.push(comp);
                        if fs::symlink_metadata(&cur)
                            .map(|m| m.file_type().is_symlink())
                            .unwrap_or(true)
                        {
                            return true;
                        }
                    }
                    let dep_prefix = rel_sub.to_string_lossy().replace('\\', "/");
                    if package_input_files_changed_in_git_repo(
                        &canon_dep_git_root,
                        &dep_prefix,
                        p,
                        &canon_pkg_root,
                        dep_rev,
                    ) {
                        return true;
                    }
                    continue;
                }
                return true;
            }
        }

        if !canon_pkg_root.starts_with(&canon_repo_root) {
            return true;
        }
        // Reject symlinks anywhere along `repo_root -> pkg_root`.
        if let Ok(rel_pkg) = p.pkg_root.strip_prefix(repo_root) {
            let mut cur = repo_root.to_path_buf();
            for comp in rel_pkg.components() {
                cur.push(comp);
                if fs::symlink_metadata(&cur)
                    .map(|m| m.file_type().is_symlink())
                    .unwrap_or(true)
                {
                    return true;
                }
            }
        }
        let Ok(pkg_repo_rel) = canon_pkg_root.strip_prefix(&canon_repo_root) else {
            return true;
        };
        let pkg_prefix = pkg_repo_rel.to_string_lossy().replace('\\', "/");
        if package_input_files_changed_in_git_repo(
            &canon_repo_root,
            &pkg_prefix,
            p,
            &canon_pkg_root,
            base_ref,
        ) {
            return true;
        }
    }

    false
}

fn resolve_git_commit_sha(repo_root: &Path, base_ref: &str) -> Result<String> {
    if let Some(sha) = resolve_git_head_sha(repo_root, base_ref) {
        return Ok(sha);
    }
    let out = crate::trusted_tools::git(repo_root)?
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
    Ok(String::from_utf8(out.stdout)?.trim().to_string())
}

fn hash_package_inputs_from_git_tree(
    canon_repo_root: &Path,
    sha: &str,
    pkg: &mut crate::module_builder::PackageConfig,
) -> Option<()> {
    if pkg.unsupported.is_some() || pkg.inputs.iter().any(|i| i.unsupported.is_some()) {
        return None;
    }
    if pkg.inputs.is_empty() {
        return Some(());
    }
    let pkg_repo_rel = pkg.pkg_root.strip_prefix(canon_repo_root).ok()?;
    if pkg_repo_rel
        .components()
        .any(|c| !matches!(c, std::path::Component::Normal(_)))
    {
        return None;
    }
    let pkg_prefix = pkg_repo_rel.to_string_lossy().replace('\\', "/");

    let mut oids_to_fetch: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut per_input_files: Vec<Vec<(String, String)>> = Vec::with_capacity(pkg.inputs.len());

    for inp in &pkg.inputs {
        if inp.path.is_absolute()
            || inp
                .path
                .components()
                .any(|c| !matches!(c, std::path::Component::Normal(_)))
        {
            return None;
        }
        let inp_rel_str = inp.path.to_string_lossy().replace('\\', "/");
        let inp_repo_rel = join_proj_prefix(&pkg_prefix, &inp_rel_str);
        let inp_repo_norm = inp_repo_rel.trim_matches('/');
        if inp_repo_norm.is_empty() {
            return None;
        }
        let ls_out = crate::trusted_tools::git(canon_repo_root)
            .and_then(|mut git| {
                git.arg("-C")
                    .arg(canon_repo_root)
                    .args([
                        "ls-tree",
                        "-r",
                        "-t",
                        "-z",
                        "--full-tree",
                        sha,
                        "--",
                        inp_repo_norm,
                    ])
                    .output()
                    .map_err(Into::into)
            })
            .ok()?;
        if !ls_out.status.success() {
            return None;
        }
        let inp_dir_prefix = format!("{inp_repo_norm}/");
        let mut matched: Vec<(String, String)> = Vec::new();
        let mut saw_dir_tree = false;
        for rec in ls_out.stdout.split(|&b| b == 0).filter(|r| !r.is_empty()) {
            let tab_pos = rec.iter().position(|&b| b == b'\t')?;
            let meta_str = std::str::from_utf8(&rec[..tab_pos]).ok()?;
            let path_str = std::str::from_utf8(&rec[tab_pos + 1..]).ok()?;
            let mut parts = meta_str.split_whitespace();
            let (mode, obj_type, oid) = (parts.next()?, parts.next()?, parts.next()?);
            if mode == "160000" || obj_type == "commit" {
                return None;
            }
            let is_ancestor = inp_repo_norm
                .strip_prefix(path_str)
                .is_some_and(|rest| rest.starts_with('/'));
            if is_ancestor {
                if mode == "120000" || obj_type != "tree" {
                    return None;
                }
                continue;
            }
            if path_str == inp_repo_norm {
                if inp.is_dir {
                    if mode == "120000" || obj_type != "tree" {
                        return None;
                    }
                    saw_dir_tree = true;
                    continue;
                }
                if mode == "120000" || obj_type != "blob" {
                    return None;
                }
                let pkg_rel = if pkg_prefix.is_empty() {
                    path_str.to_string()
                } else {
                    path_str
                        .strip_prefix(&format!("{}/", pkg_prefix.trim_end_matches('/')))?
                        .to_string()
                };
                oids_to_fetch.insert(oid.to_string());
                matched.push((pkg_rel, oid.to_string()));
                continue;
            }
            if inp.is_dir && path_str.starts_with(&inp_dir_prefix) {
                if mode == "040000" && obj_type == "tree" {
                    continue;
                }
                if mode == "120000" || obj_type != "blob" {
                    return None;
                }
                let pkg_rel = if pkg_prefix.is_empty() {
                    path_str
                } else {
                    path_str.strip_prefix(&format!("{}/", pkg_prefix.trim_end_matches('/')))?
                };
                let ext = Path::new(path_str).extension();
                if !inp.matches_extension(ext) {
                    continue;
                }
                oids_to_fetch.insert(oid.to_string());
                matched.push((pkg_rel.to_string(), oid.to_string()));
            }
        }
        if !inp.is_dir && matched.len() != 1 {
            return None;
        }
        if inp.is_dir && !saw_dir_tree {
            return None;
        }
        matched.sort_by(|(a, _), (b, _)| a.as_bytes().cmp(b.as_bytes()));
        per_input_files.push(matched);
    }

    let mut blob_by_oid: std::collections::HashMap<String, Vec<u8>> =
        std::collections::HashMap::with_capacity(oids_to_fetch.len());
    if !oids_to_fetch.is_empty() {
        let mut git_cmd = crate::trusted_tools::git(canon_repo_root).ok()?;
        let mut child = git_cmd
            .arg("-C")
            .arg(canon_repo_root)
            .args(["cat-file", "--batch"])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null())
            .spawn()
            .ok()?;
        let ordered_oids: Vec<&String> = oids_to_fetch.iter().collect();
        if let Some(mut stdin) = child.stdin.take() {
            use std::io::Write;
            let mut req_buf = String::new();
            for oid in &ordered_oids {
                req_buf.push_str(oid);
                req_buf.push('\n');
            }
            stdin.write_all(req_buf.as_bytes()).ok()?;
        }
        let out = child.wait_with_output().ok()?;
        if !out.status.success() {
            return None;
        }
        let bytes = &out.stdout;
        let mut pos = 0usize;
        for oid in ordered_oids {
            let nl_rel = bytes[pos..].iter().position(|&b| b == b'\n')?;
            let header = std::str::from_utf8(&bytes[pos..pos + nl_rel]).ok()?;
            pos += nl_rel + 1;
            let parts: Vec<&str> = header.split_whitespace().collect();
            if parts.len() < 3 || parts[1] != "blob" {
                return None;
            }
            let sz = parts[2].parse::<usize>().ok()?;
            if pos + sz > bytes.len() {
                return None;
            }
            blob_by_oid.insert(oid.clone(), bytes[pos..pos + sz].to_vec());
            pos += sz;
            if pos < bytes.len() && bytes[pos] == b'\n' {
                pos += 1;
            }
        }
    }

    for (inp, files) in pkg.inputs.iter_mut().zip(per_input_files.iter()) {
        let mut entry_refs: Vec<(&[u8], &[u8])> = Vec::with_capacity(files.len());
        for (pkg_rel, oid) in files {
            let b = blob_by_oid.get(oid)?;
            entry_refs.push((pkg_rel.as_bytes(), b.as_slice()));
        }
        let (blake3, lake_hash) =
            crate::module_builder::hash_input_target_entries(inp, entry_refs).ok()?;
        inp.blake3 = blake3;
        inp.lake_hash = lake_hash;
    }
    Some(())
}

/// Resolve the `--base` revision's workspace Lake-inputs tag purely from Git (`base_ref`) for
/// tracked packages (and materialized `.lake/packages` git dependencies pinned at the exact same
/// `rev` in both `--base` and current `lake-manifest.json`), never substituting working-tree input
/// bytes for `--base` inputs. When any `--base` package or input cannot be reconstructed cleanly
/// from Git, falls back to a fresh uncacheable sentinel tag so `base_split` keys cannot collide
/// with `cur_split` keys.
fn resolve_base_lake_inputs_tag(
    store: &TurboStore,
    repo_root: &Path,
    canon_dir: &Path,
    base_ref: &str,
    base_pkg_cfg: Option<&crate::module_builder::PackageConfig>,
    cur_dep_pkgs: &[crate::module_builder::PackageConfig],
    is_untrusted: bool,
) -> Result<Option<String>> {
    let Some(mut root_pkg) = base_pkg_cfg.cloned() else {
        return Ok(None);
    };
    let Ok(canon_repo_root) = fs::canonicalize(repo_root) else {
        return Ok(Some(
            crate::module_builder::fresh_unresolved_lake_inputs_tag(
                "base-repo-root-uncanonicalizable",
            ),
        ));
    };
    let sha = resolve_git_commit_sha(&canon_repo_root, base_ref)?;
    let prefix = rel_path_from_dir(canon_dir, &canon_repo_root);
    let manifest_repo_rel = join_proj_prefix(&prefix, "lake-manifest.json");
    let mut blobs = fetch_git_blobs_batch(
        &canon_repo_root,
        &sha,
        std::slice::from_ref(&manifest_repo_rel),
    )?;
    let base_manifest_opt = if let Some(raw_manifest) = blobs.remove(&manifest_repo_rel) {
        Some(
            crate::module_builder::parse_lake_manifest_str(
                canon_dir,
                &canon_dir.join("lake-manifest.json"),
                &raw_manifest,
                is_untrusted,
            )
            .with_context(|| {
                format!("Failed to parse base Lake manifest at {base_ref}:{manifest_repo_rel}")
            })?,
        )
    } else {
        None
    };

    if hash_package_inputs_from_git_tree(&canon_repo_root, &sha, &mut root_pkg).is_none() {
        return Ok(Some(
            crate::module_builder::fresh_unresolved_lake_inputs_tag(
                "base-root-inputs-unresolvable",
            ),
        ));
    }

    let cur_manifest_revs: std::collections::HashMap<String, (PathBuf, Option<String>)> =
        crate::module_builder::parse_lake_manifest(canon_dir, is_untrusted)
            .map(|(pkgs_dir, entries, _)| {
                entries
                    .into_iter()
                    .map(|e| {
                        let repo_dir = canon_dir.join(&pkgs_dir).join(&e.name);
                        (e.name, (repo_dir, e.rev))
                    })
                    .collect()
            })
            .unwrap_or_default();

    let mut base_dep_pkgs: Vec<crate::module_builder::PackageConfig> = Vec::new();
    if let Some((_, manifest_packages, _)) = base_manifest_opt {
        for mp in manifest_packages {
            let in_repo = mp.dir.starts_with(&canon_repo_root)
                && mp
                    .dir
                    .strip_prefix(&canon_repo_root)
                    .ok()
                    .is_some_and(|rel| {
                        !rel.components().any(|c| {
                            matches!(c, std::path::Component::ParentDir) || c.as_os_str() == ".lake"
                        })
                    });
            if in_repo {
                let dep_prefix = rel_path_from_dir(&mp.dir, &canon_repo_root);
                let cfg_rel = mp.config_file.as_deref().unwrap_or("lakefile");
                let cand_paths: Vec<(String, bool)> = if Path::new(cfg_rel).extension().is_some() {
                    let is_toml =
                        Path::new(cfg_rel).extension().and_then(|e| e.to_str()) == Some("toml");
                    vec![(join_proj_prefix(&dep_prefix, cfg_rel), is_toml)]
                } else {
                    vec![
                        (
                            join_proj_prefix(&dep_prefix, &format!("{cfg_rel}.lean")),
                            false,
                        ),
                        (
                            join_proj_prefix(&dep_prefix, &format!("{cfg_rel}.toml")),
                            true,
                        ),
                    ]
                };
                let fetch_keys: Vec<String> = cand_paths.iter().map(|(p, _)| p.clone()).collect();
                let mut dep_blobs = fetch_git_blobs_batch(&canon_repo_root, &sha, &fetch_keys)?;
                let mut parsed_dep = None;
                for (cand_p, is_toml) in cand_paths {
                    if let Some(raw_dep) = dep_blobs.remove(&cand_p) {
                        let mut dep_cfg =
                            parse_staged_base_package_config(store, &mp.dir, &raw_dep, is_toml, false)
                                .with_context(|| {
                                    format!(
                                        "Failed to parse base dependency Lake config at {base_ref}:{cand_p}"
                                    )
                                })?;
                        if hash_package_inputs_from_git_tree(&canon_repo_root, &sha, &mut dep_cfg)
                            .is_none()
                        {
                            return Ok(Some(
                                crate::module_builder::fresh_unresolved_lake_inputs_tag(
                                    "base-dep-inputs-unresolvable",
                                ),
                            ));
                        }
                        parsed_dep = Some(dep_cfg);
                        break;
                    }
                }
                if let Some(dep_cfg) = parsed_dep {
                    base_dep_pkgs.push(dep_cfg);
                } else {
                    return Ok(Some(
                        crate::module_builder::fresh_unresolved_lake_inputs_tag(
                            "base-in-repo-dep-missing-config",
                        ),
                    ));
                }
            } else if mp.pkg_type != "path"
                && mp.rev.as_deref().is_some_and(is_full_hex_git_oid)
                && cur_manifest_revs
                    .get(&mp.name)
                    .is_some_and(|(_, r)| r == &mp.rev)
            {
                let dep_rev = mp.rev.as_deref().unwrap();
                let (dep_git_dir, _) = cur_manifest_revs.get(&mp.name).unwrap();
                if let Some(cur_dep) = cur_dep_pkgs.iter().find(|d| d.name == mp.name) {
                    if cur_dep.unsupported.is_some()
                        || cur_dep.inputs.iter().any(|i| i.unsupported.is_some())
                    {
                        return Ok(Some(
                            crate::module_builder::fresh_unresolved_lake_inputs_tag(
                                "base-git-dep-unsupported-inputs",
                            ),
                        ));
                    }
                    let mut base_dep = cur_dep.clone();
                    if !base_dep.inputs.is_empty() {
                        let (Ok(canon_dep_git_root), Ok(canon_dep_pkg_root)) = (
                            fs::canonicalize(dep_git_dir),
                            fs::canonicalize(&base_dep.pkg_root),
                        ) else {
                            return Ok(Some(
                                crate::module_builder::fresh_unresolved_lake_inputs_tag(
                                    "base-git-dep-uncanonicalizable",
                                ),
                            ));
                        };
                        if !canon_dep_git_root.join(".git").exists()
                            || !canon_dep_pkg_root.starts_with(&canon_dep_git_root)
                        {
                            return Ok(Some(
                                crate::module_builder::fresh_unresolved_lake_inputs_tag(
                                    "base-git-dep-missing-git-checkout",
                                ),
                            ));
                        }
                        base_dep.pkg_root = canon_dep_pkg_root;
                        if hash_package_inputs_from_git_tree(
                            &canon_dep_git_root,
                            dep_rev,
                            &mut base_dep,
                        )
                        .is_none()
                        {
                            return Ok(Some(
                                crate::module_builder::fresh_unresolved_lake_inputs_tag(
                                    "base-git-dep-inputs-unresolvable",
                                ),
                            ));
                        }
                    }
                    base_dep_pkgs.push(base_dep);
                } else if !cur_dep_pkgs.is_empty() {
                    return Ok(Some(
                        crate::module_builder::fresh_unresolved_lake_inputs_tag(
                            "base-git-dep-not-materialized",
                        ),
                    ));
                }
            } else {
                // Unpinned `type: path` dependency under `.lake/packages/...` or outside the git
                // repository: if the materialized dependency declares no Lake inputs (and no
                // unsupported Lake constructs), it contributes nothing to the workspace Lake-inputs
                // digest; otherwise we cannot reconstruct its `base_ref` inputs from git and return
                // the uncacheable sentinel.
                if let Some(cur_dep) = cur_dep_pkgs.iter().find(|d| d.name == mp.name) {
                    if cur_dep.unsupported.is_none() && cur_dep.inputs.is_empty() {
                        continue;
                    }
                }
                return Ok(Some(
                    crate::module_builder::fresh_unresolved_lake_inputs_tag(
                        "base-external-dep-unpinned",
                    ),
                ));
            }
        }
    } else if !cur_dep_pkgs.is_empty() && cur_dep_pkgs.iter().any(|d| !d.inputs.is_empty()) {
        return Ok(Some(
            crate::module_builder::fresh_unresolved_lake_inputs_tag(
                "base-no-manifest-with-dep-inputs",
            ),
        ));
    }

    let mut digest = String::new();
    for p in std::iter::once(&root_pkg)
        .chain(base_dep_pkgs.iter())
        .filter(|p| !p.inputs.is_empty())
    {
        for i in &p.inputs {
            if let Some(ref why) = i.unsupported {
                anyhow::bail!(
                    "Unsupported base Lake input `{}/{}` at {base_ref}: {}: fail-closed static Lake config gate",
                    p.name,
                    i.name,
                    why
                );
            }
            digest.push_str(&format!("{}/{}:{}\n", p.name, i.name, i.blake3));
        }
    }
    Ok(crate::module_builder::lake_inputs_tag_from_digest(&digest))
}

/// Parse the base revision's config without executing Lake or using worktree options/inputs.
/// The parser roots module paths at the project, while config bytes come only from Git.
fn base_revision_package_config(
    store: &TurboStore,
    repo_root: &Path,
    canon_dir: &Path,
    base_ref: &str,
) -> Result<Option<crate::module_builder::PackageConfig>> {
    let sha = resolve_git_commit_sha(repo_root, base_ref)?;
    let prefix = rel_path_from_dir(canon_dir, repo_root);
    // Match Lake's precedence (`package_config_path`): `lakefile.lean` takes precedence over `lakefile.toml`.
    let paths: Vec<(_, bool)> = [("lakefile.lean", false), ("lakefile.toml", true)]
        .iter()
        .map(|(name, is_toml)| (join_proj_prefix(&prefix, name), *is_toml))
        .collect();
    let fetch_keys: Vec<String> = paths.iter().map(|(p, _)| p.clone()).collect();
    let mut blobs = fetch_git_blobs_batch(repo_root, &sha, &fetch_keys)?;
    for (path, is_toml) in paths {
        if let Some(raw) = blobs.remove(&path) {
            return parse_staged_base_package_config(store, canon_dir, &raw, is_toml, false)
                .with_context(|| {
                    format!("Failed to resolve base Lean options at {base_ref}:{path}")
                })
                .map(Some);
        }
    }
    Ok(None)
}

#[allow(clippy::type_complexity)]
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
    let proj_rel_in_repo = canon_dir
        .strip_prefix(&repo_root)
        .unwrap_or(Path::new(""))
        .to_path_buf();
    let head_pkg_for_gitlinks = untrusted_cfg
        .map(|cfg| &cfg.root_pkg)
        .or(owned_pkg_cfg.as_ref());
    // Change discovery never enters submodules (their config and filters are unvetted), so a
    // gitlink's contents inside Lean/Lake build paths would silently read as unchanged: fail closed
    // whenever either base or head lacks a static package config or maps the gitlink into Lean/Lake
    // paths, while ignoring pure non-Lean submodules (e.g. Foundry `lib/forge-std`).
    let revs: &[&str] = if base_ref == "HEAD" {
        &["HEAD"]
    } else {
        &[base_ref, "HEAD"]
    };
    crate::trusted_tools::reject_gitlinks_filtered(&repo_root, revs, canon_dir, |repo_rel| {
        let Ok(proj_rel) = repo_rel.strip_prefix(&proj_rel_in_repo) else {
            return true;
        };
        let head_touches =
            head_pkg_for_gitlinks.is_none_or(|pkg| package_gitlink_touches_lean(proj_rel, pkg));
        let base_touches = base_pkg_cfg
            .as_ref()
            .is_none_or(|pkg| package_gitlink_touches_lean(proj_rel, pkg));
        head_touches || base_touches
    })?;
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

    // A changed declarative Lake file input (`input_file` / `input_dir` reached through a
    // library's `needs`) is read during elaboration just like a source file, but it is not a
    // `.lean` file, so the diff below would ignore it. Treat it like a lakefile edit instead.
    // Resolved as a whole workspace so a dependency package's inputs are covered too.
    if !is_untrusted {
        crate::module_builder::try_project_lake_inputs_tag(canon_dir)?;
    }
    let owned_project_cfg = if is_untrusted || owned_pkg_cfg.is_none() {
        None
    } else if crate::module_builder::workspace_may_declare_lake_inputs(canon_dir) {
        Some(crate::module_builder::resolve_project_config(canon_dir)?)
    } else {
        crate::module_builder::resolve_project_config(canon_dir).ok()
    };
    let cur_dep_pkgs: &[crate::module_builder::PackageConfig] = untrusted_cfg
        .or(owned_project_cfg.as_ref())
        .map(|cfg| cfg.dep_pkgs.as_slice())
        .unwrap_or(&[]);
    let mut base_lake_inputs_tag = resolve_base_lake_inputs_tag(
        store,
        &repo_root,
        canon_dir,
        base_ref,
        base_pkg_cfg.as_ref(),
        cur_dep_pkgs,
        is_untrusted,
    )?;
    let cur_lake_inputs_tag = match untrusted_cfg.or(owned_project_cfg.as_ref()) {
        Some(cfg) => crate::module_builder::lake_inputs_tag_from_digest(
            &crate::module_builder::workspace_lake_inputs_digest(cfg)?,
        ),
        None if !is_untrusted => crate::module_builder::try_project_lake_inputs_tag(canon_dir)?,
        None => None,
    };
    let lake_inputs_changed = base_lake_inputs_tag != cur_lake_inputs_tag
        || untrusted_cfg
            .or(owned_project_cfg.as_ref())
            .is_some_and(|cfg| {
                lake_input_files_changed_since_base(
                    &repo_root,
                    &proj_prefix,
                    &cfg.root_pkg,
                    &cfg.dep_pkgs,
                    base_ref,
                )
            })
        || (!is_untrusted
            && owned_project_cfg.is_none()
            && (owned_pkg_cfg
                .as_ref()
                .is_some_and(|pkg| !pkg.inputs.is_empty())
                || crate::module_builder::workspace_may_declare_lake_inputs(canon_dir)));
    if lake_inputs_changed && base_lake_inputs_tag == cur_lake_inputs_tag {
        base_lake_inputs_tag = Some(crate::module_builder::fresh_unresolved_lake_inputs_tag(
            "base-lake-inputs-changed-conservative",
        ));
    }

    // A changed input reconfigures *every* module (the deliberate over-approximation documented
    // on `lake_input_files_changed_since_base`), so it widens this set instead of filtering it.
    // An unparseable head config needs no case of its own: `optional_package_config` above
    // propagates that error rather than reporting empty args.
    let option_changed_paths: std::collections::HashSet<String> = lean_paths
        .iter()
        .map(|p| rel_path_from_dir(p, canon_dir))
        .filter(|rel| {
            rel != "lakefile.lean"
                && (lake_inputs_changed
                    || resolve_rel_lean_args(rel) != resolve_base_lean_args(rel))
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
    let head_tree_cache_paths_opt = if is_untrusted || !option_changed_paths.is_empty() {
        None
    } else {
        head_sha_opt
            .as_ref()
            .and_then(|sha| git_head_tree_cache_paths(store, &repo_root, canon_dir, sha, toolchain))
    };
    let head_tree_cache_file = head_tree_cache_paths_opt.as_ref().map(|(cf, _)| cf.clone());

    let mut entries_by_rel_path: std::collections::HashMap<String, PrFileEntry> =
        std::collections::HashMap::with_capacity(lean_paths.len());
    let mut changed_current_files = std::collections::BTreeMap::new();
    let mut changed_current_splits = std::collections::BTreeMap::new();
    let mut current_files_count = 0usize;

    if let Some(ref cache_file) = head_tree_cache_file {
        let stats_file_opt = head_tree_cache_paths_opt.as_ref().map(|(_, sf)| sf.clone());
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
                let mut fast_batch_session = crate::lake_build::OleanInterfaceBatchSession::new();
                let all_known = lean_paths.len() == head_tree_map.len()
                    && lean_paths.iter().all(|p| {
                        head_tree_map
                            .get(&rel_path_from_dir(p, canon_dir))
                            .is_some_and(|e| {
                                fast_batch_session.compute_hashes(&e.prefix_src, canon_dir, None)
                                    == e.dep_hashes
                            })
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
                            cur_split: Box<splitter::SplitResult>,
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
                                    cur_split: Box::new(prefix_sp),
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
                            let cur_dep_hashes =
                                crate::lake_build::compute_imported_olean_interface_hashes(
                                    &cur_src, canon_dir, None,
                                );
                            let (cur_split, prefix_len_opt) = split_modified_against_head_entry(
                                &cur_src,
                                &base_entry,
                                &cur_dep_hashes,
                            );
                            if let Some(plen) = prefix_len_opt {
                                cur_src.truncate(plen);
                            }
                            StatMissedOutcome::Modified {
                                rel_path,
                                cur_src,
                                base_entry,
                                cur_split: Box::new(cur_split),
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
                                split_modified.push((rel_path, base_entry, *cur_split));
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
                crate::trusted_tools::git(repo_ref)?
                    .args([
                        "--no-optional-locks",
                        "-C",
                        &repo_ref.to_string_lossy(),
                        "status",
                        "--porcelain",
                        "-uall",
                        crate::trusted_tools::NO_SUBMODULES,
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
                crate::trusted_tools::git(repo_ref)?
                    .args([
                        "--no-optional-locks",
                        "-C",
                        &repo_ref.to_string_lossy(),
                        "diff",
                        "--no-ext-diff",
                        "--no-textconv",
                        crate::trusted_tools::NO_SUBMODULES,
                        "--name-only",
                        base_ref,
                        "--",
                        &canon_dir.to_string_lossy(),
                    ])
                    .output()
                    .context("Failed to execute `git diff --name-only`")
            });
            let untracked_h = s.spawn(move || {
                crate::trusted_tools::git(repo_ref)?
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
            if !untracked_repo_paths.contains(&repo_rel)
                && !prefetched_blobs
                    .as_ref()
                    .map(|m| m.contains_key(&repo_rel))
                    .unwrap_or(false)
            {
                repo_rels_to_fetch.push(repo_rel.clone());
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

    let mut classify_batch_session = crate::lake_build::OleanInterfaceBatchSession::new();
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
                    let dep_hashes = classify_batch_session.compute_hashes_with_tag(
                        bs,
                        canon_dir,
                        None,
                        base_lake_inputs_tag.clone(),
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
                let dep_hashes = classify_batch_session.compute_hashes_with_tag(
                    bs,
                    canon_dir,
                    None,
                    base_lake_inputs_tag.clone(),
                );
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

    let mut resolve_cached_or_split = |src: &str,
                                       strict_untrusted_imports: bool,
                                       is_base_src: bool|
     -> Result<splitter::SplitResult> {
        if is_untrusted {
            let dep_hashes = compute_source_only_import_digests_with_tag_override(
                src,
                canon_dir,
                untrusted_cfg,
                strict_untrusted_imports,
                is_base_src.then(|| base_lake_inputs_tag.clone()),
            )?;
            return Ok(split_lean_source(src, &dep_hashes));
        }
        let dep_hashes = if is_base_src {
            classify_batch_session.compute_hashes_with_tag(
                src,
                canon_dir,
                None,
                base_lake_inputs_tag.clone(),
            )
        } else {
            classify_batch_session.compute_hashes(src, canon_dir, None)
        };
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
                    None => resolve_cached_or_split(&cur_src, true, false)?,
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
                    None => resolve_cached_or_split(&cur_src, true, false)?,
                };
                changed_current_splits.insert(rel_path.clone(), cur_split.clone());
                let base_split = resolve_cached_or_split(&base_src, false, true)?;
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
                    None => resolve_cached_or_split(&cur_src, true, false)?,
                };
                changed_current_splits.insert(rel_path.clone(), cur_split.clone());
                accum.record_added(rel_path, cur_split, &file_lean_args);
            }
            PrFileEntry::Changed {
                base_src: Some(base_src),
                cur_src: None,
                cur_split: _,
            } => {
                let base_split = resolve_cached_or_split(&base_src, false, true)?;
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

#[allow(clippy::type_complexity)]
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

#[allow(clippy::type_complexity)]
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

fn to_batch_req_item(
    (k, sh, kth): &(String, splitter::TheoremShard, String),
) -> pack::CheckShardBatchItem {
    pack::CheckShardBatchItem {
        shard_key: k.clone(),
        decl_name: sh.rooted_name(),
        prefix_env_hash: sh.prefix_env_hash.clone(),
        stmt_hash: sh.stmt_hash.clone(),
        proof_hash: sh.proof_hash.clone(),
        expected_kernel_type_hash: Some(kth.clone()),
    }
}

fn verify_zygote_reply_decl_types(
    reply: &serde_json::Value,
    expected_types: &[(String, String)],
) -> Result<()> {
    if expected_types.len() == 1 {
        let (exp_decl, exp_hash) = &expected_types[0];
        if reply.get("kernel_type_hash").and_then(|v| v.as_str()) == Some(exp_hash.as_str()) {
            return Ok(());
        }
        let _ = exp_decl;
    }
    let dt_val = reply.get("decl_types").ok_or_else(|| {
        anyhow::anyhow!(
            "[TurboLean.KernelGate] daemon reply missing `decl_types` for canonical kernel-type verification"
        )
    })?;
    let decl_types: std::collections::BTreeMap<String, String> =
        serde_json::from_value(dt_val.clone())
            .context("[TurboLean.KernelGate] malformed `decl_types` in daemon reply")?;
    crate::zygote::verify_attested_decl_types(&decl_types, expected_types)
}

fn make_batch_zreq(
    shard_key: String,
    shard_source: String,
    toolchain: &str,
    lean_path: &str,
    lean_args: Vec<String>,
    targets: Vec<String>,
) -> pack::CheckShardHttpRequest {
    pack::CheckShardHttpRequest {
        decl: "__batch__".to_string(),
        shard_key,
        shard_source,
        interface_hash: String::new(),
        prefix_env_hash: String::new(),
        stmt_hash: String::new(),
        proof_hash: String::new(),
        expected_kernel_type_hash: None,
        toolchain: toolchain.to_string(),
        lean_path: lean_path.to_string(),
        skip_cas_lock: true,
        allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
        lean_args,
        targets,
    }
}

/// Resolve a project's static Lake config when `lakefile.toml` or `lakefile.lean` is present,
/// or synthesize a bare single-file `ProjectConfig` when neither exists.
pub(crate) fn resolve_static_or_bare_project_config(
    canon_dir: &Path,
    toolchain: &str,
) -> Result<crate::module_builder::ProjectConfig> {
    resolve_untrusted_pr_project_config(canon_dir, toolchain)
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
        base_name: pkg_name.clone(),
        name: pkg_name,
        pkg_root: canon_dir.to_path_buf(),
        config_file_kind: "bare".to_string(),
        src_dir: PathBuf::new(),
        build_dir: PathBuf::from(".lake/build"),
        bin_dir: PathBuf::from("bin"),
        lean_lib_dir: PathBuf::from("lib/lean"),
        native_lib_dir: PathBuf::from("lib"),
        ir_dir: PathBuf::from("ir"),
        packages_dir: PathBuf::from(".lake/packages"),
        more_lean_args: Vec::new(),
        weak_lean_args: Vec::new(),
        lean_options: BTreeMap::new(),
        precompile_modules: false,
        platform_independent: None,
        default_targets: Vec::new(),
        libs: Vec::new(),
        exes: Vec::new(),
        extern_libs: Vec::new(),
        custom_targets: Vec::new(),
        inputs: Vec::new(),
        config_digest: String::new(),
        unsupported: None,
        native_unsupported: None,
        link_unsupported: None,
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
        is_untrusted: true,
    })
}

struct PrVerificationTrust<'a> {
    is_untrusted: bool,
    untrusted_cfg: Option<&'a crate::module_builder::ProjectConfig>,
    extra_ro_olean_dirs: Vec<PathBuf>,
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
    expected_types: &[(String, String)],
    lean_args: &[String],
) -> Result<std::process::Output> {
    crate::module_builder::validate_lean_args(lean_args).context("PR/CI shard Lean options")?;
    if trust.is_untrusted {
        let cfg = trust.untrusted_cfg.ok_or_else(|| {
            anyhow::anyhow!(
                "Untrusted PR shard verification requires a resolved static ProjectConfig: fail-closed sandbox gate"
            )
        })?;
        let bwrap_path = crate::module_builder::probe_bwrap_sandbox(canon_dir).ok_or_else(|| {
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
        let nonce = format!("pr_{}_{}", pid, seq);
        let scratch_base = crate::check::verified_private_temp_scratch_base()?;
        let src_dir = crate::check::PrivateScratchDir::create_with_nonce(
            &scratch_base,
            "turbo_pr_src",
            nonce.clone(),
        )?;
        let out_dir = crate::check::PrivateScratchDir::create_with_nonce(
            &scratch_base,
            "turbo_pr_out",
            nonce.clone(),
        )?;
        let reader_dir = crate::check::PrivateScratchDir::create_with_nonce(
            &scratch_base,
            "turbo_pr_rdr",
            nonce.clone(),
        )?;
        let mod_name = format!("TurboPrShard_{}_{}", pid, seq);
        let sandbox_lean = src_dir.path.join(format!("{}.lean", mod_name));
        let sandbox_olean = out_dir.path.join(format!("{}.olean", mod_name));
        crate::check::create_readonly_private_file(&sandbox_lean, src.as_bytes())?;
        crate::check::freeze_private_dir(&src_dir.path)?;

        let (base_lp, ld_library_path_env) =
            crate::module_builder::build_lean_search_path(cfg, true);
        crate::module_builder::validate_untrusted_sandbox_search_paths(
            cfg,
            tc_prefix,
            &base_lp,
            &ld_library_path_env,
        )?;
        let mut compile_lp_parts = Vec::with_capacity(trust.extra_ro_olean_dirs.len() + 1);
        for dir in &trust.extra_ro_olean_dirs {
            compile_lp_parts.push(dir.to_string_lossy().to_string());
        }
        if !base_lp.is_empty() {
            compile_lp_parts.push(base_lp.clone());
        }
        let compile_lean_path_env = compile_lp_parts.join(":");

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
            &compile_lean_path_env,
            "--setenv",
            "LEAN_NUM_THREADS",
            "4",
            "--setenv",
            "LEAN_STACK_SIZE_KB",
            "262144",
            "--setenv",
            "TURBO_LEAN_PROBE_NONCE",
            &nonce,
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
        for dir in &trust.extra_ro_olean_dirs {
            cmd.arg("--ro-bind").arg(dir).arg(dir);
        }
        cmd.arg("--ro-bind").arg(&src_dir.path).arg(&src_dir.path);
        cmd.arg("--bind").arg(&out_dir.path).arg(&out_dir.path);
        cmd.arg("--chdir").arg(&cfg.root_pkg.pkg_root);
        cmd.arg(&cfg.lean_bin);
        crate::module_builder::scrub_untrusted_env(&mut cmd);
        cmd.args(["-M", "4096", "-j", "4"]);
        // The owning target's flags (the same ones the shard key digests), already in Lake's
        // weakLeanArgs < moreLeanArgs < leanOptions order; the hardening flags come last to win.
        for arg in crate::module_builder::filter_allowed_lean_args(lean_args) {
            cmd.arg(arg);
        }
        cmd.arg("-Dwarn.sorry=true")
            .arg("-Ddebug.skipKernelTC=false")
            .arg(&sandbox_lean)
            .arg("-R")
            .arg(&src_dir.path)
            .arg("-o")
            .arg(&sandbox_olean);

        let out_res = crate::module_builder::run_command_with_timeout(
            &mut cmd,
            std::time::Duration::from_secs(crate::module_builder::module_compile_timeout_secs(
                true,
            )),
            true,
        );
        crate::zygote::reap_processes_with_nonce(&nonce);
        let out = out_res?;
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
        crate::check::freeze_private_dir(&out_dir.path)?;
        crate::check::stage_isolated_module_artifacts(&out_dir.path, &reader_dir.path, &mod_name)?;
        crate::check::freeze_private_dir(&reader_dir.path)?;
        let mut reader_lp_parts = vec![reader_dir.path.to_string_lossy().to_string()];
        for dir in &trust.extra_ro_olean_dirs {
            reader_lp_parts.push(dir.to_string_lossy().to_string());
        }
        if !base_lp.is_empty() {
            reader_lp_parts.push(base_lp);
        }
        let reader_lean_path_env = reader_lp_parts.join(":");
        let mut stub_ok = Vec::new();
        for sh in crate::splitter::split_lean_source(src, &[]).shards {
            if crate::splitter::strip_lean_comments(&sh.proof_text).trim() == "sorry"
                && !crate::splitter::matches_uncached_or_fast_verify_name(sh.decl_name(), audit)
            {
                stub_ok.push(sh.decl_name().to_string());
            }
        }
        let mut audit_ro_binds = vec![reader_dir.path.clone()];
        audit_ro_binds.extend(trust.extra_ro_olean_dirs.iter().cloned());
        crate::zygote::audit_compiled_shard_module_with_zygote(
            store,
            cfg,
            &mod_name,
            &reader_lean_path_env,
            &audit_ro_binds,
            &stub_ok,
            audit,
            expected_types,
            true,
        )?;
        return Ok(out);
    }

    crate::zygote::run_audited_lean_shard_with_types(
        store,
        Path::new(lean_bin),
        env_vars,
        Some(canon_dir),
        src,
        audit,
        expected_types,
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
    // One top-level command, one Lake-input memo window.
    crate::module_builder::reset_lake_inputs_tag_memo();
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
    let kernel_prov = crate::kernel::resolve_kernel_engine(
        crate::kernel::resolve_kernel_selection_from_env(None)?,
        &toolchain,
    )?;

    if is_untrusted && crate::module_builder::probe_bwrap_sandbox(&canon_dir).is_none() {
        anyhow::bail!(
            "Untrusted CI verification requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
        );
    }
    // Validate every package before any action lookup. The canonical digest binds
    // effective options and lakefile contents, including dependency configuration.
    let cfg = crate::module_builder::resolve_project_config_with_trust(&canon_dir, is_untrusted)
        .context("CI static Lake config validation failed")?;
    let ci_dag = crate::module_builder::build_module_dag_with_trust(&cfg, &[], is_untrusted)
        .context("CI static module DAG validation failed")?;
    let dag_root_rel_paths: BTreeSet<String> = ci_dag
        .nodes
        .values()
        .filter(|n| n.is_root_pkg)
        .map(|n| rel_path_from_dir(&n.src_path, &canon_dir))
        .collect();
    let untrusted_ci_mods = is_untrusted.then(|| ci_dag.nodes.keys().cloned().collect::<Vec<_>>());

    let mut flagged_files = Vec::new();
    let mut total_files = 0usize;
    let mut total_shards = 0usize;
    let mut per_file_interfaces = BTreeMap::new();
    let lean_paths =
        crate::lake_build::collect_project_lean_files(&canon_dir, true, scope.as_deref());
    let ci_axioms = splitter::allowed_axioms();
    let mut hasher = blake3::Hasher::new();
    // v5: bind global C-emission flags, custom CC env, and full native/package `.lake/build` outputs.
    hasher.update(
        format!(
            "turbo-lean-ci-build-v6\n{}\n{}\n{}\n{}\n{}:{}\n:kernel:{}:{}\n",
            crate::TURBO_LEAN_BUILD_EPOCH,
            toolchain,
            trust_domain,
            cfg.canonical_config_digest,
            crate::zygote::ZYGOTE_SCANNER_VERSION,
            crate::zygote::ZYGOTE_REPLAY_VERSION,
            kernel_prov.kernel_engine.as_str(),
            kernel_prov.con_leche_rev.as_deref().unwrap_or("none"),
        )
        .as_bytes(),
    );
    if crate::module_builder::global_emit_c_enabled() {
        hasher.update(b":emit_c:1\n");
    }
    let cc_tag = crate::module_builder::custom_cc_env_digest_tag();
    if !cc_tag.is_empty() {
        hasher.update(b":cc:");
        hasher.update(cc_tag.as_bytes());
        hasher.update(b"\n");
    }
    if ci_axioms.len() > splitter::STANDARD_AXIOMS.len() {
        hasher.update(b":axioms:");
        hasher.update(ci_axioms.join(",").as_bytes());
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
    crate::lake_build::update_with_lake_input_digests(&mut hasher, &canon_dir)?;

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

    // Compiled modules are always audited against policy (`audit_compiled_modules_with_zygote`).
    // Only an explicit caller policy (via `--base` or env) can defer source flags to that gate.
    let custom_axiom_policy = splitter::HygieneReport::has_custom_axiom_policy_under(&ci_axioms);
    let csimp_policy_nonempty =
        std::env::var("TURBO_LEAN_ALLOWED_CSIMP").is_ok_and(|s| !s.trim().is_empty());
    let unsafe_policy_nonempty =
        std::env::var("TURBO_LEAN_ALLOWED_UNSAFE").is_ok_and(|s| !s.trim().is_empty());
    let impl_by_policy_nonempty =
        std::env::var("TURBO_LEAN_ALLOWED_IMPLEMENTED_BY").is_ok_and(|s| !s.trim().is_empty());
    if custom_axiom_policy
        || csimp_policy_nonempty
        || unsafe_policy_nonempty
        || impl_by_policy_nonempty
    {
        for (rel_path, items) in &mut flagged_files {
            if !dag_root_rel_paths.contains(rel_path) {
                continue;
            }
            items.retain(|item| match item.rsplit(": ").next() {
                Some("axiom") if custom_axiom_policy => false,
                Some("csimp") if csimp_policy_nonempty => false,
                Some("unsafe declaration") if unsafe_policy_nonempty => false,
                Some("implemented_by") if impl_by_policy_nonempty => false,
                _ => true,
            });
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

    let has_external_dep_build = crate::lake_build::has_out_of_tree_dep_build_dir(&canon_dir);
    let cached_outputs = if has_external_dep_build {
        None
    } else {
        store.get_cached_action(&action_key, &trust_domain)?
    };
    let (build_status, _resolved_env_opt) = if let Some(outputs) = cached_outputs {
        store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
        if is_untrusted {
            audit_untrusted_materialized(store)?;
        } else {
            ensure_project_and_imported_oleans_replayed_in_store(store, &canon_dir, &file_hashes)?;
        }
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
        let oleans_up_to_date = !is_untrusted
            && are_all_project_oleans_up_to_date(&canon_dir, &file_hashes)
            && are_all_project_oleans_replayed_in_store(store, &canon_dir, &file_hashes);
        let mut singleflight_hit_status: Option<String> = None;
        let lease_opt = if oleans_up_to_date || has_external_dep_build {
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
                    if is_untrusted {
                        audit_untrusted_materialized(store)?;
                    } else {
                        ensure_project_and_imported_oleans_replayed_in_store(
                            store,
                            &canon_dir,
                            &file_hashes,
                        )?;
                    }
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
            if !is_untrusted {
                ensure_project_and_imported_oleans_replayed_in_store(
                    store,
                    &canon_dir,
                    &file_hashes,
                )?;
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
            if !crate::lake_build::has_out_of_tree_dep_build_dir(&canon_dir) {
                let _pub_guard = crate::db::acquire_cas_publication_guard(&store.root)?;
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
                drop(_pub_guard);
            }
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

    let mut ver_receipt = build_verification_receipt_with_provenance(
        &mode,
        kernel_prov.kernel_engine.as_str(),
        &kernel_prov.lean_toolchain,
        kernel_prov.con_leche_rev.as_deref(),
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
    let mut telemetry_json = serde_json::json!({
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
    });
    kernel_prov.insert_json_fields(&mut telemetry_json);
    crate::mcp::emit_cli_telemetry_event(
        Some(&canon_dir),
        !is_untrusted,
        telemetry_json,
        "turbo_lean_events.jsonl",
    );
    if json {
        let mut out_json = serde_json::json!({
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
        });
        kernel_prov.insert_json_fields(&mut out_json);
        println!("{}", serde_json::to_string_pretty(&out_json)?);
    } else {
        println!(
            "[turbo-lean] CI-VERIFY PASSED (mode={}, kernel={}, env_scrubbed={}, status={}, {} files, {} theorems, receipt_blake3={}.., {} ms)",
            mode, kernel_prov.kernel_engine, is_untrusted, build_status, total_files, total_shards, &ver_receipt.receipt_blake3[..12], elapsed_ms
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
    kernel_prov: &crate::kernel::KernelProvenance,
    base: &str,
    classification: &PrClassification,
) -> VerificationReceipt {
    let total_theorems = classification.unchanged_theorems.len()
        + classification.proof_edited_theorems.len()
        + classification.statement_edited_theorems.len();
    let action_key = format!(
        "pr-verify:{}:{}:{}",
        base,
        kernel_prov.kernel_engine.as_str(),
        &classification.current_interface_hash
            [..16.min(classification.current_interface_hash.len())]
    );
    build_verification_receipt_with_provenance(
        mode,
        kernel_prov.kernel_engine.as_str(),
        &kernel_prov.lean_toolchain,
        kernel_prov.con_leche_rev.as_deref(),
        &classification.current_interface_hash,
        &action_key,
        classification.total_files,
        total_theorems,
        0,
        classification.per_file_interfaces.clone(),
    )
}

fn serialize_shard_receipt_bytes(
    sh: &splitter::TheoremShard,
    kernel_type_hash: &str,
    now: i64,
) -> Result<Vec<u8>> {
    crate::check::make_attested_shard_receipt_bytes(
        sh.decl_name(),
        &sh.prefix_env_hash,
        &sh.stmt_hash,
        &sh.proof_hash,
        now,
        Some(kernel_type_hash),
    )
}

fn finalize_batch_publish_entries(
    publish: &mut Vec<(String, String, Vec<u8>, i64)>,
    shards: &[(String, splitter::TheoremShard, String)],
    dur_ms: i64,
) -> Result<usize> {
    if publish.len() == shards.len() {
        for entry in publish.iter_mut() {
            entry.3 = dur_ms;
        }
    } else {
        publish.clear();
        let now = crate::db::now_unix();
        for (k, sh, kth) in shards {
            let r_bytes = serialize_shard_receipt_bytes(sh, kth, now)?;
            publish.push((k.clone(), sh.decl_name().to_string(), r_bytes, dur_ms));
        }
    }
    Ok(shards.len())
}

/// Statement digests are deliberately separate from source shard/cache keys. They
/// classify reports only: none of these hashes grant a kernel-check cache hit.
#[derive(Debug, Clone, serde::Deserialize)]
struct KernelConstant {
    deps: Vec<String>,
}

#[derive(Debug, Clone, serde::Deserialize)]
struct KernelTheorem {
    #[serde(skip)]
    statement: String,
    deps: Vec<String>,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct KernelAudit {
    audit: String,
    axioms: Vec<String>,
}

#[derive(Debug, Default, serde::Serialize, serde::Deserialize)]
struct KernelStatementReport {
    statements: BTreeMap<String, String>,
    audits: Vec<KernelAudit>,
    axiom_decls: Vec<String>,
    csimp: Vec<String>,
    unsafe_decls: Vec<(String, String)>,
    unsafe_inductives: Vec<String>,
    implemented_by: Vec<(String, String)>,
    extern_decls: Vec<String>,
}

struct StatementPolicy {
    axioms: Vec<String>,
    csimp: Vec<String>,
    unsafe_decls: Vec<String>,
    implemented_by: Vec<String>,
}

impl StatementPolicy {
    fn at(project: &Path, base: &str) -> Self {
        // An unreadable base config falls back to the restrictive default; the CLI has already
        // rejected it while loading the same policy at startup.
        let config = splitter::read_project_config(project, Some(base))
            .ok()
            .flatten()
            .unwrap_or_default();
        Self {
            axioms: splitter::allowed_axioms_with_extra(
                &crate::accelerators::toml_string_array(&config, "axioms", "allow")
                    .unwrap_or_default(),
            ),
            csimp: crate::accelerators::toml_string_array(&config, "csimp", "allow")
                .unwrap_or_default(),
            unsafe_decls: crate::accelerators::toml_string_array(&config, "unsafe", "allow")
                .unwrap_or_default(),
            implemented_by: crate::accelerators::toml_string_array(
                &config,
                "implemented_by",
                "allow",
            )
            .unwrap_or_default(),
        }
    }

    fn decl_allowed(raw: &str, user: &str, patterns: &[String]) -> bool {
        patterns
            .iter()
            .map(|p| p.trim())
            .filter(|p| !p.is_empty())
            .any(|p| splitter::glob_match(p, raw) || splitter::glob_match(p, user))
    }

    fn audit(&self, report: &KernelStatementReport) -> Result<()> {
        for axiom in &report.axiom_decls {
            anyhow::ensure!(
                splitter::axiom_allowed_under(axiom, &self.axioms),
                "[TurboLean.KernelGate] custom axiom `{axiom}` requires [axioms] allow in turbo-lean.toml at --base"
            );
        }
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
        if let Some(ind) = report.unsafe_inductives.first() {
            anyhow::bail!("[TurboLean.KernelGate] unsafe inductive `{ind}` is forbidden");
        }
        if let Some(ext) = report.extern_decls.first() {
            anyhow::bail!("[TurboLean.KernelGate] extern bypass on `{ext}` is forbidden");
        }
        for (raw, user) in &report.unsafe_decls {
            anyhow::ensure!(
                Self::decl_allowed(raw, user, &self.unsafe_decls),
                "[TurboLean.KernelGate] unsafe declaration `{user}` (`{raw}`) requires [unsafe] allow in turbo-lean.toml at --base"
            );
        }
        for (raw, user) in &report.implemented_by {
            anyhow::ensure!(
                Self::decl_allowed(raw, user, &self.implemented_by),
                "[TurboLean.KernelGate] implemented_by bypass on `{user}` (`{raw}`) requires [implemented_by] allow in turbo-lean.toml at --base"
            );
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
    #[serde(default)]
    axiom_decls: Vec<String>,
    #[serde(default)]
    unsafe_decls: Vec<(String, String)>,
    #[serde(default)]
    unsafe_inductives: Vec<String>,
    #[serde(default)]
    implemented_by: Vec<(String, String)>,
    #[serde(default)]
    extern_decls: Vec<String>,
}

// Borrow the exact JSON value emitted by Lean. IgnoredAny scans the value without
// converting numeric tokens to f64 (or imposing any machine-integer bound).
fn raw_statement_payload<'a>(line: &'a str, field: &str) -> Result<&'a str> {
    let mut rest = line
        .trim_start()
        .strip_prefix('{')
        .context("Expected JSON object")?;
    loop {
        rest = rest.trim_start();
        let mut keys = serde_json::Deserializer::from_str(rest).into_iter::<String>();
        let key = keys.next().context("Missing JSON key")??;
        rest = rest[keys.byte_offset()..]
            .trim_start()
            .strip_prefix(':')
            .context("Missing JSON colon")?
            .trim_start();
        let mut values =
            serde_json::Deserializer::from_str(rest).into_iter::<serde::de::IgnoredAny>();
        values.next().context("Missing JSON value")??;
        let end = values.byte_offset();
        if key == field {
            return Ok(&rest[..end]);
        }
        rest = rest[end..]
            .trim_start()
            .strip_prefix(',')
            .with_context(|| format!("Missing kernel statement payload {field}"))?;
    }
}

struct SharedKernelConstantEntry {
    interface_hash: blake3::Hash,
    deps: Vec<String>,
}

#[cfg(test)]
fn parse_kernel_statement_dump(raw: &[u8], module: &str) -> Result<BTreeMap<String, String>> {
    let mut shared = BTreeMap::new();
    parse_kernel_statement_dump_with_shared(raw, module, &mut shared)
}

fn parse_kernel_statement_dump_with_shared(
    raw: &[u8],
    module: &str,
    shared_constants: &mut BTreeMap<String, SharedKernelConstantEntry>,
) -> Result<BTreeMap<String, String>> {
    let mut seen_in_chunk = std::collections::BTreeSet::<String>::new();
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
            let constant: KernelConstant = serde_json::from_str(line)?;
            let interface_raw = raw_statement_payload(line, "interface")?;
            let interface_hash = blake3::hash(interface_raw.as_bytes());
            anyhow::ensure!(
                seen_in_chunk.insert(name.to_string()),
                "Duplicate constant in kernel statement dump: {name}"
            );
            anyhow::ensure!(
                shared_constants
                    .insert(
                        name.to_string(),
                        SharedKernelConstantEntry {
                            interface_hash,
                            deps: constant.deps,
                        },
                    )
                    .is_none(),
                "Duplicate constant across shared kernel statement dump: {name}"
            );
        } else if let Some(name) = row.theorem.as_deref() {
            let mut theorem: KernelTheorem = serde_json::from_str(line)?;
            theorem.statement = raw_statement_payload(line, "statement")?.to_owned();
            anyhow::ensure!(
                theorems.insert(name.to_string(), theorem).is_none(),
                "Duplicate theorem in kernel statement dump: {name}"
            );
        } else if row.audit.is_some() {
            let _: KernelAudit = serde_json::from_str(line)?;
        } else {
            anyhow::ensure!(
                row.module.as_deref() == Some(module) && row.complete == Some(true) && !complete,
                "Incomplete or unexpected kernel statement dump for {module}"
            );
            complete = true;
        }
    }
    anyhow::ensure!(complete, "Missing kernel statement dump for {module}");
    let mut result = BTreeMap::new();
    for (name, theorem) in theorems {
        let mut pending = theorem.deps;
        let mut closure = std::collections::BTreeSet::new();
        while let Some(dep) = pending.pop() {
            if !closure.insert(dep.clone()) {
                continue;
            }
            let constant = shared_constants
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
            closure_hash.update(shared_constants[&dep].interface_hash.as_bytes());
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

// A source snapshot has no Git worktree registration and never runs checkout
// conversion (attributes, smudge/process filters, or EOL rewriting).
struct StatementSnapshot {
    path: PathBuf,
}

impl StatementSnapshot {
    #[cfg(test)]
    fn at(repo: &Path, rev: &str) -> Result<Self> {
        Self::at_scoped(repo, rev, Path::new(""), None)
    }

    fn at_scoped(
        repo: &Path,
        rev: &str,
        pkg_prefix: &Path,
        pkg_cfg: Option<&crate::module_builder::PackageConfig>,
    ) -> Result<Self> {
        use std::os::unix::fs::DirBuilderExt;
        let snapshot = loop {
            let path = Path::new("/tmp").join(format!(
                "turbo-statements-{}-{}",
                std::process::id(),
                pack::next_tmp_id()
            ));
            match fs::DirBuilder::new().mode(0o700).create(&path) {
                Ok(()) => break Self { path },
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(e.into()),
            }
        };
        materialize_statement_tree(repo, rev, &snapshot.path, None, pkg_prefix, pkg_cfg)?;
        Ok(snapshot)
    }
}

impl Drop for StatementSnapshot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn package_gitlink_touches_lean(rel: &Path, pkg: &crate::module_builder::PackageConfig) -> bool {
    let norm = |p: &Path| -> PathBuf {
        p.components()
            .filter(|c| !matches!(c, std::path::Component::CurDir))
            .collect()
    };
    let rel = norm(rel);
    if pkg.unsupported.is_some()
        || !pkg.custom_targets.is_empty()
        || rel.extension().is_some_and(|e| e == "lean")
    {
        return true;
    }
    if let Some(name) = rel.file_name().and_then(|n| n.to_str()) {
        if matches!(
            name,
            "lakefile.lean" | "lakefile.toml" | "lake-manifest.json" | "lean-toolchain"
        ) || (rel.parent().is_some_and(|p| p.as_os_str().is_empty())
            && matches!(rel.file_stem().and_then(|s| s.to_str()), Some("lakefile")))
        {
            return true;
        }
    }
    let overlaps = |a: &Path, b: &Path| a.starts_with(b) || b.starts_with(a);
    let base = norm(&pkg.src_dir);
    for path in [&pkg.build_dir, &pkg.packages_dir] {
        let np = norm(path);
        let rel_np = np.strip_prefix(&pkg.pkg_root).unwrap_or(&np);
        if overlaps(&rel, rel_np) {
            return true;
        }
    }
    for inp in &pkg.inputs {
        let np = norm(&inp.path);
        let rel_np = np.strip_prefix(&pkg.pkg_root).unwrap_or(&np);
        if overlaps(&rel, rel_np) {
            return true;
        }
    }
    if pkg.libs.is_empty() && pkg.exes.is_empty() {
        return overlaps(&rel, &base);
    }
    let module_prefix = |root: &Path, module: &str| {
        let first = module.split('.').next().unwrap_or(module);
        norm(&root.join(first))
    };
    for lib in &pkg.libs {
        let root = match &lib.src_dir {
            Some(dir) => norm(&base.join(dir)),
            None => base.clone(),
        };
        if lib.globs.is_empty() && lib.roots.is_empty() && overlaps(&rel, &root) {
            return true;
        }
        let names = lib
            .roots
            .iter()
            .map(String::as_str)
            .chain(lib.globs.iter().map(|g| {
                use crate::module_builder::GlobSpec;
                match g {
                    GlobSpec::One(n) | GlobSpec::Submodules(n) | GlobSpec::AndSubmodules(n) => {
                        n.as_str()
                    }
                }
            }));
        for name in names {
            let prefix = module_prefix(&root, name);
            if overlaps(&rel, &prefix) || overlaps(&rel, &prefix.with_extension("lean")) {
                return true;
            }
        }
    }
    for exe in &pkg.exes {
        let root = match &exe.src_dir {
            Some(dir) => norm(&base.join(dir)),
            None => base.clone(),
        };
        let prefix = module_prefix(&root, &exe.root);
        if overlaps(&rel, &prefix) || overlaps(&rel, &prefix.with_extension("lean")) {
            return true;
        }
    }
    false
}

#[derive(Clone, Copy)]
struct StatementDependencySpec<'a> {
    dep: Option<&'a crate::module_builder::PackageConfig>,
    config_file: Option<&'a str>,
}

fn dependency_symlink_touches_build(
    rel: &Path,
    dep: &crate::module_builder::PackageConfig,
) -> bool {
    !dep.extern_libs.is_empty() || package_gitlink_touches_lean(rel, dep)
}

fn materialize_statement_tree(
    repo: &Path,
    rev: &str,
    root: &Path,
    dep_spec: Option<StatementDependencySpec<'_>>,
    pkg_prefix: &Path,
    pkg_for_gitlinks: Option<&crate::module_builder::PackageConfig>,
) -> Result<()> {
    use std::io::{BufRead, BufReader, Read, Write};
    use std::os::unix::{
        ffi::OsStrExt,
        fs::{symlink, PermissionsExt},
    };
    use std::process::Stdio;

    anyhow::ensure!(!rev.starts_with('-'), "Invalid statement snapshot revision");
    let tree = crate::trusted_tools::git(repo)?
        .arg("-C")
        .arg(repo)
        .args(["ls-tree", "-r", "-z", "--full-tree", rev, "--"])
        .output()?;
    anyhow::ensure!(
        tree.status.success(),
        "Cannot enumerate statement snapshot: {}",
        String::from_utf8_lossy(&tree.stderr)
    );
    let effective_gitlink_pkg = dep_spec.and_then(|s| s.dep).or(pkg_for_gitlinks);
    let mut entries = Vec::new();
    for entry in tree.stdout.split(|&b| b == 0).filter(|e| !e.is_empty()) {
        let (header, path) = entry.split_at(
            entry
                .iter()
                .position(|&b| b == b'\t')
                .context("Invalid Git tree entry")?,
        );
        let fields: Vec<_> = std::str::from_utf8(header)?.split(' ').collect();
        anyhow::ensure!(fields.len() == 3, "Invalid Git tree header");
        let rel = Path::new(std::ffi::OsStr::from_bytes(&path[1..]));
        anyhow::ensure!(!rel.as_os_str().is_empty() && rel.components().all(|c|
            matches!(c, std::path::Component::Normal(p) if !p.eq_ignore_ascii_case(".git"))),
            "Invalid statement snapshot path: {}", rel.display());
        if fields[0] == "160000" {
            let touches = match (effective_gitlink_pkg, rel.strip_prefix(pkg_prefix)) {
                (Some(pkg), Ok(pkg_rel)) => package_gitlink_touches_lean(pkg_rel, pkg),
                _ => true,
            };
            anyhow::ensure!(
                !touches,
                "Statement snapshots do not support submodule gitlinks: {}",
                rel.display()
            );
            continue;
        }
        anyhow::ensure!(
            fields[1] == "blob"
                && matches!(fields[0], "100644" | "100755" | "120000")
                && matches!(fields[2].len(), 40 | 64)
                && fields[2].bytes().all(|b| b.is_ascii_hexdigit()),
            "Unsupported Git tree entry: {}",
            rel.display()
        );
        entries.push((
            fields[0].to_owned(),
            fields[2].to_owned(),
            rel.to_path_buf(),
            root.join(rel),
        ));
    }
    let mut git = crate::trusted_tools::git(repo)?;
    let mut child = git
        .arg("-C")
        .arg(repo)
        .args(["cat-file", "--batch"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    let result = (|| -> Result<()> {
        let mut input = child.stdin.take().context("Missing Git batch stdin")?;
        let mut output = BufReader::new(child.stdout.take().context("Missing Git batch stdout")?);
        let mut links = Vec::new();
        for (mode, oid, rel, target) in entries {
            ensure_statement_snapshot_path(root, &target)?;
            fs::create_dir_all(target.parent().context("Missing snapshot parent")?)?;
            writeln!(input, "{oid}")?;
            input.flush()?;
            let mut header = String::new();
            output.read_line(&mut header)?;
            let fields: Vec<_> = header.trim_end().split(' ').collect();
            anyhow::ensure!(
                fields.len() == 3 && fields[0] == oid && fields[1] == "blob",
                "Invalid Git batch blob header: {header}"
            );
            let size: u64 = fields[2].parse()?;
            let mut blob = output.by_ref().take(size);
            if mode == "120000" {
                let mut bytes = Vec::new();
                blob.read_to_end(&mut bytes)?;
                anyhow::ensure!(bytes.len() as u64 == size, "Truncated Git symlink blob");
                let link = PathBuf::from(std::ffi::OsStr::from_bytes(&bytes));
                links.push((rel, target, link));
            } else {
                let mut file = fs::OpenOptions::new()
                    .write(true)
                    .create_new(true)
                    .open(&target)?;
                anyhow::ensure!(
                    std::io::copy(&mut blob, &mut file)? == size,
                    "Truncated Git blob"
                );
                file.set_permissions(fs::Permissions::from_mode(if mode == "100755" {
                    0o755
                } else {
                    0o644
                }))?;
            }
            let mut newline = [0];
            output.read_exact(&mut newline)?;
            anyhow::ensure!(newline == *b"\n", "Invalid Git batch blob terminator");
        }
        let mut dep_config = None;
        if let Some(spec) = dep_spec.filter(|spec| spec.dep.is_none()) {
            let cfg_path = crate::module_builder::package_config_path(root, spec.config_file)?;
            dep_config = Some(
                match cfg_path
                    .as_ref()
                    .and_then(|p| p.extension())
                    .and_then(|e| e.to_str())
                {
                    Some("lean") => crate::module_builder::parse_lakefile_lean(
                        root,
                        cfg_path.as_ref().unwrap(),
                        false,
                    )?,
                    Some("toml") => crate::module_builder::parse_lakefile_toml(
                        root,
                        cfg_path.as_ref().unwrap(),
                        false,
                    )?,
                    _ => anyhow::bail!(
                        "No static Lake configuration (`{}.lean` or `.toml`) found in {}: fail-closed static Lake config gate",
                        spec.config_file.unwrap_or("lakefile"),
                        root.display()
                    ),
                },
            );
        }
        let dep = dep_spec.and_then(|spec| spec.dep).or(dep_config.as_ref());
        // Create links only after every regular file has been written, so even
        // malformed trees cannot redirect writes. Validate actual resolution,
        // including link chains and `..` traversing another symlink.
        for (rel, target, link) in &links {
            if link.is_absolute() {
                if dep.is_none_or(|d| dependency_symlink_touches_build(rel, d)) {
                    anyhow::bail!(
                        "Absolute symlink in statement snapshot: {}",
                        target.display()
                    );
                }
                continue;
            }
            ensure_statement_snapshot_path(root, target)?;
            symlink(link, target)?;
        }
        let canonical_root = root.canonicalize()?;
        loop {
            let mut removed = false;
            for (rel, target, _) in &links {
                if !target.is_symlink() {
                    continue;
                }
                match target.canonicalize() {
                    Ok(resolved) if resolved.starts_with(&canonical_root) => {}
                    res => {
                        let _ = fs::remove_file(target);
                        removed = true;
                        if dep.is_none_or(|d| dependency_symlink_touches_build(rel, d)) {
                            match res {
                                Ok(_) => anyhow::bail!(
                                    "Symlink escapes statement snapshot: {}",
                                    target.display()
                                ),
                                Err(e) => {
                                    return Err(e).with_context(|| {
                                        format!(
                                            "Unresolvable statement snapshot symlink: {}",
                                            target.display()
                                        )
                                    });
                                }
                            }
                        }
                    }
                }
            }
            if !removed {
                break;
            }
        }
        Ok(())
    })();
    if result.is_err() {
        let _ = child.kill();
    }
    let status = child.wait()?;
    result?;
    anyhow::ensure!(status.success(), "Git batch object read failed");
    Ok(())
}

// Stock toolchain commands run inside bwrap for untrusted inputs. The Lake configuration
// and any build scripts are untrusted executable code; no host environment or
// network is inherited. The writable root is a disposable source snapshot.
fn statement_lake_command(project: &Path, is_untrusted: bool) -> Result<Command> {
    statement_toolchain_command(project, is_untrusted, "lake", None, &[])
}

pub(crate) fn statement_lean_command(project: &Path, is_untrusted: bool) -> Result<Command> {
    statement_lean_command_with_binds(project, is_untrusted, &[])
}

/// Like `statement_lean_command`, additionally binding `writable` private scratch dirs
/// (at the same path) into the untrusted sandbox.
pub(crate) fn statement_lean_command_with_binds(
    project: &Path,
    is_untrusted: bool,
    writable: &[&Path],
) -> Result<Command> {
    // Static package paths only: never ask project code to supply PATH/LEAN_PATH.
    let mut cfg = crate::module_builder::resolve_project_config_with_trust(project, is_untrusted)?;
    if !is_untrusted && cfg.lean_bin.as_os_str().is_empty() {
        let (lean_bin, lean_githash, toolchain_lib_lean, toolchain_lib) =
            crate::module_builder::resolve_toolchain_compiler_with_trust(
                project,
                &cfg.toolchain,
                true,
            )?;
        cfg.lean_bin = lean_bin;
        cfg.lean_githash = lean_githash;
        cfg.toolchain_lib_lean = toolchain_lib_lean;
        cfg.toolchain_lib = toolchain_lib;
    }
    let (lean_path, _) = crate::module_builder::build_lean_search_path(&cfg, true);
    statement_toolchain_command(project, is_untrusted, "lean", Some(&lean_path), writable)
}

/// Build a bubblewrap-isolated `lean` command where the project root, dependency packages,
/// toolchain, and `ro_binds` are mounted strictly read-only (`--ro-bind`), and ONLY `rw_binds`
/// are mounted writable (`--bind`). When `require_sandbox` is true, fails closed if `bwrap` or
/// static project config resolution is unavailable; when false, returns `Ok(None)` if `bwrap`
/// is unavailable on the host so trusted callers can fall back to DAC `0o400`/`0o500` isolation.
pub(crate) fn probe_lean_ro_bwrap_command(
    project: &Path,
    require_sandbox: bool,
    ro_binds: &[&Path],
    rw_binds: &[&Path],
    probe_nonce: &str,
) -> Result<Option<Command>> {
    let Some(bwrap) = crate::module_builder::probe_bwrap_sandbox(project) else {
        if require_sandbox {
            anyhow::bail!(
                "Declaration-identity probe requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
            );
        }
        return Ok(None);
    };
    let toolchain = detect_toolchain(project);
    let cfg = match resolve_static_or_bare_project_config(project, &toolchain) {
        Ok(c) => c,
        Err(e) if require_sandbox => return Err(e),
        Err(_) => return Ok(None),
    };
    let tc_prefix = cfg
        .toolchain_lib
        .parent()
        .filter(|p| p.is_dir() && p.is_absolute() && *p != Path::new("/"))
        .ok_or_else(|| {
            anyhow::anyhow!(
                "Invalid toolchain prefix `{}` for bubblewrap probe sandbox",
                cfg.toolchain_lib.display()
            )
        })?;
    let (base_lean_path_env, ld_library_path_env) =
        crate::module_builder::build_lean_search_path(&cfg, require_sandbox);
    // `ro_binds[0]` is the probe's source scratch directory (`src_scratch`); any subsequent
    // `ro_binds` entries are extra read-only `.olean` overlay directories (such as standalone
    // project modules) needed by the probe compiler.
    let mut lp_parts: Vec<String> = ro_binds
        .iter()
        .skip(1)
        .map(|d| d.to_string_lossy().to_string())
        .collect();
    if !base_lean_path_env.is_empty() {
        lp_parts.push(base_lean_path_env.clone());
    }
    let lean_path_env = lp_parts.join(":");
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
            "TURBO_LEAN_PROBE_NONCE",
            probe_nonce,
            "--setenv",
            "PATH",
        ])
        .arg(format!(
            "{}:/usr/bin:/bin",
            cfg.lean_bin
                .parent()
                .context("Missing toolchain bin")?
                .display()
        ))
        .args(["--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp"]);
    for sys_p in [
        "/usr",
        "/bin",
        "/lib",
        "/lib64",
        "/etc/alternatives",
        "/etc/ld.so.cache",
        "/etc/localtime",
    ] {
        command.args(["--ro-bind-try", sys_p, sys_p]);
    }
    if !lean_path_env.is_empty() {
        command.args(["--setenv", "LEAN_PATH", &lean_path_env]);
    }
    if !ld_library_path_env.is_empty() {
        command.args(["--setenv", "LD_LIBRARY_PATH", &ld_library_path_env]);
    }
    let mut mounted_ro: Vec<PathBuf> = Vec::new();
    let mut ro_bind_once = |cmd: &mut Command, p: &Path| {
        if !p.is_absolute() || p == Path::new("/") {
            return;
        }
        if mounted_ro.iter().any(|m| p.starts_with(m)) {
            return;
        }
        mounted_ro.push(p.to_path_buf());
        cmd.arg("--ro-bind").arg(p).arg(p);
    };
    ro_bind_once(&mut command, tc_prefix);
    ro_bind_once(&mut command, &cfg.root_pkg.pkg_root);
    for dp in &cfg.dep_pkgs {
        ro_bind_once(&mut command, &dp.pkg_root);
    }
    if !require_sandbox {
        for raw in lean_path_env
            .split(':')
            .chain(ld_library_path_env.split(':'))
        {
            let trimmed = raw.trim();
            if trimmed.is_empty() {
                continue;
            }
            let p = Path::new(trimmed);
            let abs = if p.is_absolute() {
                p.to_path_buf()
            } else {
                project.join(p)
            };
            if abs.exists() {
                ro_bind_once(&mut command, &abs);
                if let Ok(canon) = abs.canonicalize() {
                    ro_bind_once(&mut command, &canon);
                }
            }
        }
    }
    for dir in ro_binds {
        ro_bind_once(&mut command, dir);
    }
    for dir in rw_binds {
        command.arg("--bind").arg(dir).arg(dir);
    }
    command
        .arg("--chdir")
        .arg(&cfg.root_pkg.pkg_root)
        .arg(&cfg.lean_bin);
    crate::module_builder::scrub_untrusted_env(&mut command);
    Ok(Some(command))
}

fn statement_toolchain_command(
    project: &Path,
    is_untrusted: bool,
    tool: &str,
    lean_path: Option<&str>,
    writable: &[&Path],
) -> Result<Command> {
    let tools =
        crate::module_builder::ToolchainExecutables::resolve(project, &detect_toolchain(project))?;
    let executable = match tool {
        "lean" => &tools.lean,
        "lake" => &tools.lake,
        "leanc" => &tools.leanc,
        _ => anyhow::bail!("Unknown verifier tool `{tool}`"),
    };
    let lib = tools
        .lean
        .parent()
        .and_then(Path::parent)
        .context("Missing stock toolchain prefix")?
        .join("lib");
    if !is_untrusted {
        let mut command = Command::new(executable);
        command
            .current_dir(project)
            .env("PATH", tools.path())
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
    let bwrap = crate::module_builder::probe_bwrap_sandbox(project)
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
            "2",
            "--setenv",
            "LEAN_STACK_SIZE_KB",
            "65536",
            "--setenv",
            "PATH",
        ])
        .arg(tools.path())
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
        .arg(project);
    for dir in writable {
        command.arg("--bind").arg(dir).arg(dir);
    }
    command.arg("--chdir").arg(project).arg(executable);
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
    let out = crate::trusted_tools::git(repo)?
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

// Seed offline dependencies without checkout conversion or shared build outputs.
// Keep independent Git metadata for Lake revision checks; write sources as raw blobs.
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
        // Local object copy only: a canonical absolute directory (never a URL or remote
        // helper); `file` is the only transport this one command may use.
        let source = dep.pkg_root.canonicalize()?;
        anyhow::ensure!(
            source.is_absolute() && source.is_dir(),
            "Statement dependency {} is not a local directory",
            dep.name
        );
        let out = crate::trusted_tools::git(project)?
            .env("GIT_ALLOW_PROTOCOL", "file")
            .args(["clone", "--local"])
            .args(["--quiet", "--no-hardlinks", "--no-checkout", "--template="])
            .arg("--")
            .arg(&source)
            .arg(&target)
            .current_dir("/")
            .output()?;
        anyhow::ensure!(
            out.status.success(),
            "Cannot seed offline statement dependency {}: {}",
            dep.name,
            String::from_utf8_lossy(&out.stderr)
        );
        materialize_statement_tree(
            &target,
            "HEAD",
            &target,
            Some(StatementDependencySpec {
                dep: Some(dep),
                config_file: None,
            }),
            Path::new(""),
            None,
        )?;
    }
    Ok(())
}

fn seed_base_statement_dependencies(
    base_project: &Path,
    head_project: &Path,
    head_cfg: &crate::module_builder::ProjectConfig,
) -> Result<()> {
    use std::os::unix::fs::DirBuilderExt;

    seed_statement_dependencies(base_project, head_cfg)?;
    let (_, manifest_packages, _) = crate::module_builder::parse_lake_manifest(base_project, true)?;
    let canon_head = head_project
        .canonicalize()
        .unwrap_or_else(|_| head_project.to_path_buf());
    for mp in manifest_packages {
        let target = mp.dir;
        ensure_statement_snapshot_path(base_project, &target)?;
        if target.exists() {
            continue;
        }
        let rel = target.strip_prefix(base_project)?;
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent)?;
        }
        let local_cand = head_project.join(rel);
        if fs::symlink_metadata(&local_cand)
            .map(|m| m.is_dir() && !m.file_type().is_symlink())
            .unwrap_or(false)
        {
            let source = local_cand.canonicalize()?;
            anyhow::ensure!(
                source.is_absolute() && source.is_dir() && source.starts_with(&canon_head),
                "Statement dependency {} resolves outside head project",
                mp.name
            );
            let clone_rev = match mp.rev.as_deref().filter(|r| !r.is_empty()) {
                Some(rev) => {
                    anyhow::ensure!(
                        !rev.starts_with('-'),
                        "Invalid base manifest dependency revision for {}",
                        mp.name
                    );
                    rev
                }
                None => "HEAD",
            };
            let out = crate::trusted_tools::git(base_project)?
                .env("GIT_ALLOW_PROTOCOL", "file")
                .args(["clone", "--local"])
                .args(["--quiet", "--no-hardlinks", "--no-checkout", "--template="])
                .arg("--")
                .arg(&source)
                .arg(&target)
                .current_dir("/")
                .output()?;
            anyhow::ensure!(
                out.status.success(),
                "Cannot seed offline base statement dependency {}: {}",
                mp.name,
                String::from_utf8_lossy(&out.stderr)
            );
            materialize_statement_tree(
                &target,
                clone_rev,
                &target,
                Some(StatementDependencySpec {
                    dep: None,
                    config_file: mp.config_file.as_deref(),
                }),
                Path::new(""),
                None,
            )?;
            continue;
        }
        if mp.pkg_type == "git" {
            let rev = mp.rev.as_deref().unwrap_or("");
            anyhow::ensure!(
                !rev.is_empty()
                    && !rev.starts_with('-')
                    && matches!(rev.len(), 40 | 64)
                    && rev.bytes().all(|b| b.is_ascii_hexdigit()),
                "Base manifest git dependency {} lacks a pinned hex commit SHA: {:?}",
                mp.name,
                mp.rev
            );
            let url = mp.url.as_deref().unwrap_or("");
            let protocol = if url.starts_with("https://") {
                "https"
            } else if url.starts_with("file://") {
                "file"
            } else {
                anyhow::bail!(
                    "Unsupported base manifest git dependency URL for {}: {:?}",
                    mp.name,
                    mp.url
                );
            };
            anyhow::ensure!(
                !url.starts_with('-'),
                "Invalid base manifest git dependency URL for {}",
                mp.name
            );
            struct ScratchRepoGuard(PathBuf);
            impl Drop for ScratchRepoGuard {
                fn drop(&mut self) {
                    let _ = fs::remove_dir_all(&self.0);
                }
            }
            let scratch = loop {
                let path = Path::new("/tmp").join(format!(
                    "turbo-base-dep-{}-{}",
                    std::process::id(),
                    pack::next_tmp_id()
                ));
                match fs::DirBuilder::new().mode(0o700).create(&path) {
                    Ok(()) => break ScratchRepoGuard(path),
                    Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(e) => return Err(e.into()),
                }
            };
            let init = crate::trusted_tools::git(base_project)?
                .args(["init", "--bare", "--quiet"])
                .arg(&scratch.0)
                .current_dir("/")
                .output()?;
            anyhow::ensure!(
                init.status.success(),
                "Cannot initialize scratch repo for base dependency {}: {}",
                mp.name,
                String::from_utf8_lossy(&init.stderr)
            );
            let fetch = crate::trusted_tools::git(base_project)?
                .env("GIT_ALLOW_PROTOCOL", protocol)
                .arg("-C")
                .arg(&scratch.0)
                .args(["fetch", "--quiet", "--depth=1", "--no-tags", "--", url, rev])
                .current_dir("/")
                .output()?;
            anyhow::ensure!(
                fetch.status.success(),
                "Cannot fetch pinned base statement dependency {} ({rev}): {}",
                mp.name,
                String::from_utf8_lossy(&fetch.stderr)
            );
            let parsed = crate::trusted_tools::git(base_project)?
                .arg("-C")
                .arg(&scratch.0)
                .args(["rev-parse", "FETCH_HEAD"])
                .current_dir("/")
                .output()?;
            anyhow::ensure!(
                parsed.status.success(),
                "Cannot verify fetched commit for base statement dependency {}: {}",
                mp.name,
                String::from_utf8_lossy(&parsed.stderr)
            );
            let fetched_rev = std::str::from_utf8(&parsed.stdout)?.trim();
            anyhow::ensure!(
                fetched_rev.eq_ignore_ascii_case(rev),
                "Fetched commit mismatch for base statement dependency {}: expected {rev}, got {fetched_rev}",
                mp.name
            );
            let update_head = crate::trusted_tools::git(base_project)?
                .arg("-C")
                .arg(&scratch.0)
                .args(["update-ref", "--no-deref", "HEAD", fetched_rev])
                .current_dir("/")
                .output()?;
            anyhow::ensure!(
                update_head.status.success(),
                "Cannot pin HEAD in scratch repo for base statement dependency {}: {}",
                mp.name,
                String::from_utf8_lossy(&update_head.stderr)
            );
            let clone_out = crate::trusted_tools::git(base_project)?
                .env("GIT_ALLOW_PROTOCOL", "file")
                .args(["clone", "--local"])
                .args(["--quiet", "--no-hardlinks", "--no-checkout", "--template="])
                .arg("--")
                .arg(&scratch.0)
                .arg(&target)
                .current_dir("/")
                .output()?;
            anyhow::ensure!(
                clone_out.status.success(),
                "Cannot clone offline base statement dependency {}: {}",
                mp.name,
                String::from_utf8_lossy(&clone_out.stderr)
            );
            materialize_statement_tree(
                &target,
                fetched_rev,
                &target,
                Some(StatementDependencySpec {
                    dep: None,
                    config_file: mp.config_file.as_deref(),
                }),
                Path::new(""),
                None,
            )?;
        }
    }
    Ok(())
}

fn normal_rel_path(rel: &Path) -> Option<PathBuf> {
    let mut out = PathBuf::new();
    for c in rel.components() {
        match c {
            std::path::Component::CurDir => {}
            std::path::Component::Normal(p) if !p.eq_ignore_ascii_case(".git") => out.push(p),
            _ => return None,
        }
    }
    (!out.as_os_str().is_empty()).then_some(out)
}

fn trusted_dep_snapshot_rel_path(
    cfg: &crate::module_builder::ProjectConfig,
    dep: &crate::module_builder::PackageConfig,
) -> Option<PathBuf> {
    if let Ok(rel) = dep.pkg_root.strip_prefix(&cfg.root_pkg.pkg_root) {
        if let Some(clean) = normal_rel_path(rel) {
            return Some(clean);
        }
    }
    for mp in &cfg.manifest_packages {
        let same_target = mp.dir == dep.pkg_root
            || mp
                .dir
                .canonicalize()
                .ok()
                .zip(dep.pkg_root.canonicalize().ok())
                .is_some_and(|(a, b)| a == b);
        if same_target {
            if let Ok(rel) = mp.dir.strip_prefix(&cfg.root_pkg.pkg_root) {
                if let Some(clean) = normal_rel_path(rel) {
                    return Some(clean);
                }
            }
        }
    }
    let pkgs_abs = cfg.root_pkg.pkg_root.join(&cfg.root_pkg.packages_dir);
    if let Ok(canon_pkgs) = pkgs_abs.canonicalize() {
        if let Ok(sub) = dep.pkg_root.strip_prefix(&canon_pkgs) {
            let pkgs_rel = cfg
                .root_pkg
                .packages_dir
                .strip_prefix(&cfg.root_pkg.pkg_root)
                .unwrap_or(&cfg.root_pkg.packages_dir);
            if let Some(clean) = normal_rel_path(&pkgs_rel.join(sub)) {
                return Some(clean);
            }
        }
    }
    None
}

fn package_has_lean_elab_host_effects(pkg: &crate::module_builder::PackageConfig) -> bool {
    let Ok(dep_root) = pkg.pkg_root.canonicalize() else {
        return true;
    };
    let build_abs = dep_root.join(&pkg.build_dir);
    let pkgs_abs = dep_root.join(&pkg.packages_dir);
    let lake_abs = dep_root.join(".lake");
    let mut stack = vec![dep_root];
    while let Some(dir) = stack.pop() {
        let Ok(rd) = fs::read_dir(&dir) else {
            return true;
        };
        for ent in rd {
            let Ok(ent) = ent else {
                return true;
            };
            let p = ent.path();
            let name = p.file_name().and_then(|s| s.to_str()).unwrap_or("");
            if name == ".git" || p == build_abs || p == pkgs_abs || p == lake_abs {
                continue;
            }
            let Ok(st) = fs::symlink_metadata(&p) else {
                return true;
            };
            if st.file_type().is_symlink() {
                continue;
            }
            if st.is_dir() {
                stack.push(p);
            } else if st.is_file() && name.ends_with(".lean") {
                let Ok(src) = fs::read_to_string(&p) else {
                    return true;
                };
                if splitter::source_may_execute_elab_host_effects(&src, false) {
                    return true;
                }
            }
        }
    }
    false
}

fn package_may_read_host_state(pkg: &crate::module_builder::PackageConfig) -> bool {
    let Ok(dep_root) = pkg.pkg_root.canonicalize() else {
        return true;
    };
    let build_abs = dep_root.join(&pkg.build_dir);
    let pkgs_abs = dep_root.join(&pkg.packages_dir);
    let lake_abs = dep_root.join(".lake");
    let build_lean_abs = build_abs.join(&pkg.lean_lib_dir);
    let has_any_built_olean = build_lean_abs.is_dir();
    let norm_sub = |p: &Path| -> PathBuf {
        let mut out = PathBuf::new();
        for c in p.components() {
            match c {
                std::path::Component::CurDir => {}
                std::path::Component::ParentDir => {
                    out.pop();
                }
                other => out.push(other),
            }
        }
        out
    };
    let pkg_src_base = norm_sub(&dep_root.join(&pkg.src_dir));
    let mut lib_roots: Vec<PathBuf> = pkg
        .libs
        .iter()
        .map(|l| match &l.src_dir {
            Some(sd) => norm_sub(&pkg_src_base.join(sd)),
            None => pkg_src_base.clone(),
        })
        .collect();
    if lib_roots.is_empty() {
        lib_roots.push(pkg_src_base);
    }
    lib_roots.sort();
    lib_roots.dedup();
    let mut stack = vec![dep_root.clone()];
    while let Some(dir) = stack.pop() {
        let Ok(rd) = fs::read_dir(&dir) else {
            return true;
        };
        for ent in rd {
            let Ok(ent) = ent else {
                return true;
            };
            let p = ent.path();
            let name = p.file_name().and_then(|s| s.to_str()).unwrap_or("");
            if name == ".git" || p == build_abs || p == pkgs_abs || p == lake_abs {
                continue;
            }
            let Ok(st) = fs::symlink_metadata(&p) else {
                return true;
            };
            if st.file_type().is_symlink() {
                continue;
            }
            if st.is_dir() {
                stack.push(p);
            } else if st.is_file() && name.ends_with(".lean") {
                if p == dep_root.join("lakefile.lean") {
                    continue;
                }
                let built_olean_exists = lib_roots.iter().any(|lr| {
                    p.strip_prefix(lr).ok().is_some_and(|rel| {
                        build_lean_abs.join(rel.with_extension("olean")).is_file()
                    })
                });
                if has_any_built_olean && !built_olean_exists {
                    continue;
                }
                let Ok(src) = fs::read_to_string(&p) else {
                    return true;
                };
                if splitter::source_may_read_host_state(&src) {
                    return true;
                }
            }
        }
    }
    false
}

fn pinned_git_manifest_dep_rev<'a>(
    cfg: &'a crate::module_builder::ProjectConfig,
    dep: &crate::module_builder::PackageConfig,
) -> Option<&'a str> {
    crate::module_builder::manifest_pinned_git_rev_for_pkg(
        cfg,
        &dep.name,
        &dep.base_name,
        &dep.pkg_root,
    )
    .filter(|rev| crate::module_builder::is_clean_pinned_git_checkout(&dep.pkg_root, rev))
}

fn is_pinned_git_manifest_dep(
    cfg: &crate::module_builder::ProjectConfig,
    dep: &crate::module_builder::PackageConfig,
) -> bool {
    pinned_git_manifest_dep_rev(cfg, dep).is_some()
}

fn dep_package_has_disallowed_elab_host_effects(
    cfg: &crate::module_builder::ProjectConfig,
    dep: &crate::module_builder::PackageConfig,
) -> bool {
    if is_pinned_git_manifest_dep(cfg, dep) {
        package_may_read_host_state(dep)
    } else {
        package_has_lean_elab_host_effects(dep)
    }
}

fn strip_snapshot_build_products_and_oleans(dir: &Path) -> Result<()> {
    if !dir.exists() {
        return Ok(());
    }
    for ent in fs::read_dir(dir)? {
        let ent = ent?;
        let p = ent.path();
        let st = fs::symlink_metadata(&p)?;
        if st.file_type().is_symlink() {
            continue;
        }
        let name = ent.file_name();
        if name.to_str() == Some(".git") || name.to_str() == Some(".lake") {
            if st.is_dir() {
                fs::remove_dir_all(&p)?;
            } else {
                fs::remove_file(&p)?;
            }
            continue;
        }
        if st.is_dir() {
            strip_snapshot_build_products_and_oleans(&p)?;
        } else if st.is_file() {
            let ext = p.extension().and_then(|e| e.to_str()).unwrap_or("");
            let fname = name.to_str().unwrap_or("");
            if matches!(ext, "olean" | "ilean" | "trace")
                || fname.contains(".olean.")
                || fname == ".turbo_verified_sources.json"
            {
                fs::remove_file(&p)?;
            }
        }
    }
    Ok(())
}

fn copy_dep_sources_without_build_products(
    src_root: &Path,
    dst_root: &Path,
    build_abs: &Path,
) -> Result<()> {
    fs::create_dir_all(dst_root)?;
    for ent in fs::read_dir(src_root)? {
        let ent = ent?;
        let p = ent.path();
        if p == build_abs {
            continue;
        }
        let name = ent.file_name();
        if matches!(name.to_str(), Some(".git" | ".lake")) {
            continue;
        }
        let dst = dst_root.join(&name);
        let st = fs::symlink_metadata(&p)?;
        if st.file_type().is_symlink() {
            #[cfg(unix)]
            {
                let target = fs::read_link(&p)?;
                let resolved = if target.is_absolute() {
                    target
                } else {
                    src_root.join(target)
                };
                std::os::unix::fs::symlink(resolved, &dst)?;
            }
        } else if st.is_dir() {
            copy_dep_sources_without_build_products(&p, &dst, build_abs)?;
        } else if st.is_file() {
            let ext = p.extension().and_then(|e| e.to_str()).unwrap_or("");
            let fname = name.to_str().unwrap_or("");
            if matches!(ext, "olean" | "ilean" | "trace")
                || fname.contains(".olean.")
                || fname == ".turbo_verified_sources.json"
            {
                continue;
            }
            fs::copy(&p, &dst)?;
        }
    }
    Ok(())
}

fn seed_trusted_statement_dependencies(
    project: &Path,
    cfg: &crate::module_builder::ProjectConfig,
) -> Result<()> {
    use std::os::unix::fs::DirBuilderExt;

    for dep in &cfg.dep_pkgs {
        let Some(rel) = trusted_dep_snapshot_rel_path(cfg, dep) else {
            continue;
        };
        let target = project.join(rel);
        ensure_statement_snapshot_path(project, &target)?;
        if target.exists() {
            continue;
        }
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent)?;
        }
        let source = dep.pkg_root.canonicalize()?;
        if source.is_absolute() && source.is_dir() {
            if dep_package_has_disallowed_elab_host_effects(cfg, dep) {
                if let Some(pinned_rev) =
                    pinned_git_manifest_dep_rev(cfg, dep).filter(|_| source.join(".git").exists())
                {
                    struct ScratchCloneGuard(PathBuf);
                    impl Drop for ScratchCloneGuard {
                        fn drop(&mut self) {
                            let _ = fs::remove_dir_all(&self.0);
                        }
                    }
                    let scratch = loop {
                        let path = Path::new("/tmp").join(format!(
                            "turbo-trusted-dep-{}-{}",
                            std::process::id(),
                            pack::next_tmp_id()
                        ));
                        match fs::DirBuilder::new().mode(0o700).create(&path) {
                            Ok(()) => break ScratchCloneGuard(path),
                            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                            Err(e) => return Err(e.into()),
                        }
                    };
                    let clone_repo = scratch.0.join("repo.git");
                    let out = crate::trusted_tools::git(project)?
                        .env("GIT_ALLOW_PROTOCOL", "file")
                        .args([
                            "clone",
                            "--local",
                            "--bare",
                            "--quiet",
                            "--no-hardlinks",
                            "--template=",
                        ])
                        .arg("--")
                        .arg(&source)
                        .arg(&clone_repo)
                        .current_dir("/")
                        .output()?;
                    anyhow::ensure!(
                        out.status.success(),
                        "Cannot seed offline trusted statement dependency {}: {}",
                        dep.name,
                        String::from_utf8_lossy(&out.stderr)
                    );
                    fs::create_dir_all(&target)?;
                    materialize_statement_tree(
                        &clone_repo,
                        pinned_rev,
                        &target,
                        Some(StatementDependencySpec {
                            dep: Some(dep),
                            config_file: None,
                        }),
                        Path::new(""),
                        None,
                    )?;
                    let build_in_target = target.join(&dep.build_dir);
                    if build_in_target.starts_with(&target)
                        && build_in_target != target
                        && build_in_target.exists()
                    {
                        if build_in_target.is_dir() {
                            fs::remove_dir_all(&build_in_target)?;
                        } else {
                            fs::remove_file(&build_in_target)?;
                        }
                    }
                    strip_snapshot_build_products_and_oleans(&target)?;
                } else {
                    let build_abs = source.join(&dep.build_dir);
                    copy_dep_sources_without_build_products(&source, &target, &build_abs)?;
                }
            } else {
                #[cfg(unix)]
                {
                    std::os::unix::fs::symlink(&source, &target)?;
                }
            }
        }
    }
    #[cfg(unix)]
    {
        let root_lake = cfg.root_pkg.pkg_root.join(".lake");
        if let Ok(entries) = fs::read_dir(&root_lake) {
            let dst_lake = project.join(".lake");
            fs::create_dir_all(&dst_lake)?;
            for entry in entries.flatten() {
                let name = entry.file_name();
                let Some(s) = name.to_str() else {
                    continue;
                };
                if matches!(s, "build" | "packages" | "config") || s.starts_with('.') {
                    continue;
                }
                let src = entry.path();
                let dst = dst_lake.join(&name);
                if dst.exists() {
                    continue;
                }
                if let Ok(canon_src) = src.canonicalize() {
                    if canon_src.is_dir() {
                        let _ = std::os::unix::fs::symlink(&canon_src, &dst);
                    }
                }
            }
        }
    }
    Ok(())
}

// Share source-root resolution between stock compilation and digest reporting.
fn statement_source_modules_with_trust(
    project: &Path,
    pkg: &crate::module_builder::PackageConfig,
    scope: Option<&Path>,
    is_untrusted: bool,
) -> Result<BTreeMap<String, (PathBuf, PathBuf)>> {
    let (_, manifest_packages, _) = crate::module_builder::parse_lake_manifest(project, false)?;
    let canon_project = project
        .canonicalize()
        .unwrap_or_else(|_| project.to_path_buf());
    let assurance_mods = if !is_untrusted && scope.is_none() {
        let allowed = splitter::allowed_axioms();
        crate::module_builder::discover_trusted_assurance_surface(project, pkg, &allowed).mod_names
    } else {
        std::collections::HashSet::new()
    };
    let mut dep_roots: Vec<PathBuf> = manifest_packages
        .into_iter()
        .filter_map(|mp| {
            let canon = mp.dir.canonicalize().unwrap_or_else(|_| mp.dir.clone());
            (canon != canon_project && mp.dir != project).then_some(canon)
        })
        .collect();
    dep_roots.sort();
    dep_roots.dedup();
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
    for source in crate::lake_build::collect_project_lean_files(project, false, scope) {
        let canon_source = source.canonicalize().unwrap_or_else(|_| source.clone());
        if dep_roots.iter().any(|dr| canon_source.starts_with(dr)) {
            continue;
        }
        let root = roots
            .iter()
            .find(|root| source.starts_with(root))
            .with_context(|| format!("No source root for {}", source.display()))?;
        let name = source
            .strip_prefix(root)?
            .with_extension("")
            .to_string_lossy()
            .replace('/', ".");
        if assurance_mods.contains(&name) {
            continue;
        }
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
    stock_statement_build_with_trust(project, None, false)
}

fn stock_statement_build_with_trust(
    project: &Path,
    scope: Option<&Path>,
    is_untrusted: bool,
) -> Result<()> {
    let pkg = crate::module_builder::resolve_package_config(project, true)?;
    let assurance_libs = if !is_untrusted && scope.is_none() {
        let allowed = splitter::allowed_axioms();
        crate::module_builder::discover_trusted_assurance_surface(project, &pkg, &allowed).lib_names
    } else {
        std::collections::HashSet::new()
    };
    if scope.is_none() && (is_untrusted || assurance_libs.is_empty()) {
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
    }
    let lib_dir = project.join(&pkg.build_dir).join(&pkg.lean_lib_dir);
    let mut modules = statement_source_modules_with_trust(project, &pkg, scope, is_untrusted)?;
    if scope.is_some() && !modules.is_empty() {
        // Expand `scope` with transitive project-local `.lean` imports so standalone or
        // unbuilt local imports compile before scoped statement modules.
        let all_project_modules =
            statement_source_modules_with_trust(project, &pkg, None, is_untrusted)?;
        let mut queue: Vec<String> = modules.keys().cloned().collect();
        while let Some(cur) = queue.pop() {
            let Some((src_path, _)) = modules.get(&cur) else {
                continue;
            };
            let header = crate::module_builder::parse_header_info(&fs::read_to_string(src_path)?);
            for imp in header.imports {
                if !modules.contains_key(&imp) {
                    if let Some(entry) = all_project_modules.get(&imp) {
                        modules.insert(imp.clone(), entry.clone());
                        queue.push(imp);
                    }
                }
            }
        }
    }
    let mut input_targets = Vec::new();
    let mut olean_targets = Vec::new();
    let mut standalone = BTreeMap::new();
    for (name, (source, root)) in modules {
        let owned = pkg.libs.iter().any(|lib| {
            let lib_root = project
                .join(&pkg.src_dir)
                .join(lib.src_dir.as_deref().unwrap_or(Path::new("")));
            lib_root == root && crate::module_builder::lib_can_build_module(lib, &name)
        }) || pkg.exes.iter().any(|exe| exe.root == name);
        if owned {
            // `+<Mod>:olean` builds the module under Lake's own attribution (the last library that
            // can build it, or the executable whose root it is), whose `extraDep` may carry none of
            // the `needs` that names the input the module reads. Lake memoizes each module's build
            // job under the *first* target that schedules it, so input-bearing library and
            // executable targets must run **before** `+<Mod>:olean`!
            for lib in pkg
                .libs
                .iter()
                .filter(|lib| !lib.needs.is_empty() && !assurance_libs.contains(&lib.name))
                .filter(|lib| crate::module_builder::lib_can_build_module(lib, &name))
            {
                if !input_targets.contains(&lib.name) {
                    input_targets.push(lib.name.clone());
                }
            }
            let pkg_base = crate::module_builder::pkg_target_base_name(&pkg);
            for exe in pkg
                .exes
                .iter()
                .filter(|exe| !exe.needs.is_empty() && exe.root == name)
            {
                let exe_target = format!("@{}/{}:exe", pkg_base, exe.name);
                if !input_targets.contains(&exe_target) {
                    input_targets.push(exe_target);
                }
            }
            olean_targets.push(format!("+{name}:olean"));
        } else {
            standalone.insert(name, (source, root));
        }
    }
    let mut lake_targets = input_targets;
    lake_targets.extend(olean_targets);
    // Ask Lake to refresh every registered module `.olean`, including non-default targets.
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
    compile_standalone_statement_modules(project, &pkg, &lib_dir, standalone, is_untrusted, None)
}

fn standalone_source_has_host_effects(src_text: &str) -> bool {
    splitter::source_may_execute_elab_host_effects(src_text, true)
        || splitter::contains_lean_word(&splitter::strip_lean_comments(src_text), "include_str")
}

fn imported_module_source_for_standalone(
    cfg: &crate::module_builder::ProjectConfig,
    mod_name: &str,
) -> Option<PathBuf> {
    let mut specs = Vec::new();
    if let Some(root_spec) =
        crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, mod_name)
    {
        specs.push(root_spec.src_path);
    }
    for dp in &cfg.dep_pkgs {
        if let Some(dep_spec) =
            crate::module_builder::resolve_module_in_package(dp, false, mod_name)
        {
            specs.push(dep_spec.src_path);
        }
    }
    if specs.len() == 1 {
        return specs.into_iter().next();
    }
    if specs.len() > 1 {
        return None;
    }
    let rel_slash = crate::module_builder::module_name_to_rel_slash(mod_name);
    let base = cfg.root_pkg.pkg_root.join(&cfg.root_pkg.src_dir);
    let mut roots = vec![base.clone()];
    roots.extend(
        cfg.root_pkg
            .libs
            .iter()
            .filter_map(|l| l.src_dir.as_ref())
            .map(|d| base.join(d)),
    );
    roots.extend(
        cfg.root_pkg
            .exes
            .iter()
            .filter_map(|e| e.src_dir.as_ref())
            .map(|d| base.join(d)),
    );
    roots.sort();
    roots.dedup();
    let mut cands: Vec<PathBuf> = roots
        .into_iter()
        .map(|r| r.join(format!("{rel_slash}.lean")))
        .filter(|p| p.is_file())
        .collect();
    (cands.len() == 1).then(|| cands.pop()).flatten()
}

fn standalone_statement_olean_action_key(
    cfg: &crate::module_builder::ProjectConfig,
    pkg: &crate::module_builder::PackageConfig,
    name: &str,
    rel_source: &Path,
    src_text: &str,
    imports: &[String],
    overlay_lib_dir: Option<&Path>,
) -> Option<String> {
    if standalone_source_has_host_effects(src_text) {
        return None;
    }
    let ws_inputs_digest = crate::module_builder::workspace_lake_inputs_digest(cfg).ok()?;
    let (lean_path, _) = crate::module_builder::build_lean_search_path(cfg, true);
    let mut dirs: Vec<PathBuf> = overlay_lib_dir.iter().map(|p| (*p).to_path_buf()).collect();
    dirs.extend(std::env::split_paths(&lean_path));
    if !cfg.toolchain_lib_lean.as_os_str().is_empty() && !dirs.contains(&cfg.toolchain_lib_lean) {
        dirs.push(cfg.toolchain_lib_lean.clone());
    }
    let mut worklist: Vec<String> = imports.to_vec();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut dep_digests: BTreeMap<String, String> = BTreeMap::new();
    while let Some(m) = worklist.pop() {
        if !seen.insert(m.clone()) {
            continue;
        }
        let path = crate::module_builder::resolve_olean_along_search_dirs(&dirs, &m)?;
        if crate::module_builder::is_verified_toolchain_olean_file(
            &cfg.toolchain_lib_lean,
            Some(&cfg.lean_githash),
            &path,
        ) {
            continue;
        }
        let dep_src_path = imported_module_source_for_standalone(cfg, &m)?;
        let dep_src = fs::read_to_string(&dep_src_path).ok()?;
        if standalone_source_has_host_effects(&dep_src) {
            return None;
        }
        let (imps, _) = crate::module_builder::read_olean_binary_imports_cached(&path).ok()?;
        let art_dig =
            crate::module_builder::compute_olean_artifact_set_digest_preserve_lake(&path).ok()?;
        dep_digests.insert(m, art_dig);
        worklist.extend(imps.into_iter().map(|i| i.module));
    }
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean:standalone-stmt-olean:v6\0");
    h.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    h.update(b"\0");
    h.update(cfg.lean_githash.as_bytes());
    h.update(b"\0");
    h.update(pkg.config_digest.as_bytes());
    h.update(b"\0");
    h.update(ws_inputs_digest.as_bytes());
    h.update(b"\0");
    for arg in &pkg.more_lean_args {
        h.update(arg.as_bytes());
        h.update(b"\0");
    }
    h.update(b"\x01");
    for arg in &pkg.weak_lean_args {
        h.update(arg.as_bytes());
        h.update(b"\0");
    }
    h.update(b"\x01");
    for (k, v) in &pkg.lean_options {
        let ks = k.to_lean_string();
        let vs = v.as_cli_flag_value();
        h.update(ks.as_bytes());
        h.update(b"=");
        h.update(vs.as_bytes());
        h.update(b"\0");
    }
    h.update(b"\x01");
    h.update(name.as_bytes());
    h.update(b"\0");
    h.update(rel_source.to_string_lossy().as_bytes());
    h.update(b"\0");
    h.update(blake3::hash(src_text.as_bytes()).as_bytes());
    h.update(b"\x01");
    for (m, dig) in &dep_digests {
        h.update(m.as_bytes());
        h.update(b":");
        h.update(dig.as_bytes());
        h.update(b"\n");
    }
    Some(h.finalize().to_hex().to_string())
}

fn is_regular_nonempty_standalone_artifact(p: &Path) -> bool {
    fs::symlink_metadata(p)
        .is_ok_and(|m| !m.file_type().is_symlink() && m.file_type().is_file() && m.len() > 0)
}

fn validate_standalone_artifact_outputs(
    outputs: &[crate::db::BlobEntry],
    lib_dir: &Path,
    rel_source: &Path,
    is_module: bool,
) -> Option<std::collections::BTreeMap<String, PathBuf>> {
    let output = lib_dir.join(rel_source).with_extension("olean");
    let expected: std::collections::BTreeMap<String, (&'static str, PathBuf)> =
        crate::module_builder::olean_artifact_paths(&output)
            .into_iter()
            .filter_map(|(kind, abs)| {
                let rel = abs
                    .strip_prefix(lib_dir)
                    .ok()?
                    .to_string_lossy()
                    .replace('\\', "/");
                Some((rel, (kind, abs)))
            })
            .collect();
    if outputs.is_empty() {
        return None;
    }
    let mut mapped = std::collections::BTreeMap::new();
    let mut has_olean = false;
    let mut has_srv = false;
    let mut has_priv = false;
    for entry in outputs {
        if entry.size_bytes == 0 {
            return None;
        }
        let &(exp_kind, ref abs) = expected.get(&entry.rel_path)?;
        if entry.kind != exp_kind {
            return None;
        }
        match exp_kind {
            "olean" => has_olean = true,
            "srv" => has_srv = true,
            "priv" => has_priv = true,
            _ => {}
        }
        if mapped.insert(entry.rel_path.clone(), abs.clone()).is_some() {
            return None;
        }
    }
    if !has_olean || (is_module && (!has_srv || !has_priv)) {
        return None;
    }
    Some(mapped)
}

fn standalone_artifacts_present_on_disk(olean_path: &Path, is_module: bool) -> bool {
    if !is_regular_nonempty_standalone_artifact(olean_path) {
        return false;
    }
    if is_module {
        let srv = PathBuf::from(format!("{}.server", olean_path.display()));
        let prv = PathBuf::from(format!("{}.private", olean_path.display()));
        if !is_regular_nonempty_standalone_artifact(&srv)
            || !is_regular_nonempty_standalone_artifact(&prv)
        {
            return false;
        }
    }
    crate::module_builder::olean_artifact_paths(olean_path)
        .into_iter()
        .all(|(_, p)| fs::symlink_metadata(&p).map_or(true, |m| !m.file_type().is_symlink()))
}

fn compile_standalone_statement_modules(
    project: &Path,
    pkg: &crate::module_builder::PackageConfig,
    lib_dir: &Path,
    mut standalone: BTreeMap<String, (PathBuf, PathBuf)>,
    is_untrusted: bool,
    mut store: Option<&mut TurboStore>,
) -> Result<()> {
    // Lake cannot address sources excluded by its globs (e.g. `TurboLean.lean`
    // with a `TurboLean.+` glob). Compile these with absolute stock Lean,
    // even when an older artifact exists, in import order.
    let trusted_cfg = if !is_untrusted && store.is_some() {
        crate::module_builder::resolve_project_config_with_trust(project, false).ok()
    } else {
        None
    };
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
            let rel_source = source.strip_prefix(&root)?;
            let output = lib_dir.join(rel_source).with_extension("olean");
            fs::create_dir_all(
                output
                    .parent()
                    .context("Missing statement output directory")?,
            )?;
            let src_text = fs::read_to_string(&source)?;
            let header = crate::module_builder::parse_header_info(&src_text);
            let cache_key = trusted_cfg.as_ref().and_then(|cfg| {
                standalone_statement_olean_action_key(
                    cfg,
                    pkg,
                    &name,
                    rel_source,
                    &src_text,
                    &header.imports,
                    None,
                )
            });
            let mut pending_lease = None;
            if let (Some(ref key), Some(ref cfg), Some(st)) =
                (&cache_key, &trusted_cfg, store.as_deref_mut())
            {
                if let Ok(outcome) =
                    st.acquire_singleflight(key, &cfg.toolchain, "standalone_stmt_olean", "trusted")
                {
                    match outcome {
                        crate::db::SingleflightOutcome::CacheHit { outputs, .. } => {
                            if let Some(mapped) = validate_standalone_artifact_outputs(
                                &outputs,
                                lib_dir,
                                rel_source,
                                header.is_module,
                            ) {
                                for (_, cand) in
                                    crate::module_builder::olean_artifact_paths(&output)
                                {
                                    if !mapped.values().any(|p| p == &cand)
                                        && fs::symlink_metadata(&cand).is_ok()
                                    {
                                        let _ = fs::remove_file(&cand);
                                    }
                                }
                                let restored_all = outputs.iter().all(|entry| {
                                    mapped.get(&entry.rel_path).is_some_and(|dest| {
                                        st.restore_blob_to_path(&entry.blob_hash, dest).is_ok()
                                    })
                                }) && standalone_artifacts_present_on_disk(
                                    &output,
                                    header.is_module,
                                );
                                if restored_all {
                                    continue;
                                }
                                for (_, cand) in
                                    crate::module_builder::olean_artifact_paths(&output)
                                {
                                    if fs::symlink_metadata(&cand).is_ok() {
                                        let _ = fs::remove_file(&cand);
                                    }
                                }
                            }
                        }
                        crate::db::SingleflightOutcome::Leader(lease) => {
                            pending_lease = Some(lease);
                        }
                    }
                }
            }
            for (_, cand) in crate::module_builder::olean_artifact_paths(&output) {
                if fs::symlink_metadata(&cand).is_ok() {
                    let _ = fs::remove_file(&cand);
                }
            }
            let t0 = std::time::Instant::now();
            let mut command = statement_lean_command(project, is_untrusted)?;
            command.args(&pkg.weak_lean_args).args(&pkg.more_lean_args);
            for (key, value) in &pkg.lean_options {
                command.arg(format!(
                    "-D{}={}",
                    key.to_lean_string(),
                    value.raw_cli_value()
                ));
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
            let artifacts_valid = out.status.success()
                && standalone_artifacts_present_on_disk(&output, header.is_module);
            if !artifacts_valid {
                if let (Some(lease), Some(st)) = (pending_lease.take(), store.as_deref_mut()) {
                    st.remove_singleflight_done(&lease.action_key);
                    drop(lease);
                }
            }
            anyhow::ensure!(
                out.status.success(),
                "Stock Lean statement module {name} failed:\n{}\n{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
            anyhow::ensure!(
                artifacts_valid,
                "Stock Lean statement module {name} produced incomplete artifact set (is_module={})",
                header.is_module
            );
            if let (Some(lease), Some(st)) = (pending_lease.take(), store.as_deref_mut()) {
                let dur_ms = t0.elapsed().as_millis() as i64;
                let mut blob_items = Vec::new();
                let mut read_ok = true;
                for (kind, abs_path) in crate::module_builder::olean_artifact_paths(&output) {
                    if is_regular_nonempty_standalone_artifact(&abs_path) {
                        match (fs::read(&abs_path), abs_path.strip_prefix(lib_dir)) {
                            (Ok(bytes), Ok(rel_p)) => {
                                let sz = bytes.len() as u64;
                                let rel_str = rel_p.to_string_lossy().replace('\\', "/");
                                blob_items.push((
                                    String::new(),
                                    bytes,
                                    kind.to_string(),
                                    rel_str,
                                    sz,
                                ));
                            }
                            _ => {
                                read_ok = false;
                                break;
                            }
                        }
                    }
                }
                if read_ok && !blob_items.is_empty() {
                    let pub_res: Result<()> = (|| {
                        let _pub_guard = crate::db::acquire_cas_publication_guard(&st.root)?;
                        let entries = st.batch_store_immutable_blobs(&blob_items, "trusted", 0)?;
                        st.publish_action(&lease, &entries, dur_ms, 0, 0, "trusted")?;
                        Ok(())
                    })();
                    if pub_res.is_err() {
                        st.remove_singleflight_done(&lease.action_key);
                    }
                } else {
                    st.remove_singleflight_done(&lease.action_key);
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
fn built_kernel_statements(
    project: &Path,
    scope: Option<&Path>,
) -> Result<BTreeMap<String, String>> {
    built_kernel_statements_with_trust(project, scope, false, None, None)
}

fn built_kernel_statements_with_trust(
    project: &Path,
    scope: Option<&Path>,
    is_untrusted: bool,
    store_root: Option<&Path>,
    overlay_lib_dir: Option<&Path>,
) -> Result<BTreeMap<String, String>> {
    Ok(
        built_kernel_statement_report(project, scope, is_untrusted, store_root, overlay_lib_dir)?
            .statements,
    )
}

fn built_kernel_statement_report(
    project: &Path,
    scope: Option<&Path>,
    is_untrusted: bool,
    store_root: Option<&Path>,
    overlay_lib_dir: Option<&Path>,
) -> Result<KernelStatementReport> {
    built_kernel_statement_report_bound(
        project,
        scope,
        is_untrusted,
        store_root,
        overlay_lib_dir,
        None,
    )
}

fn built_kernel_statement_report_bound(
    project: &Path,
    scope: Option<&Path>,
    is_untrusted: bool,
    store_root: Option<&Path>,
    overlay_lib_dir: Option<&Path>,
    bound_snap: Option<&crate::zygote::ClosureSnapshot>,
) -> Result<KernelStatementReport> {
    let pkg = crate::module_builder::resolve_package_config(project, true)?;
    let lib_dir = project.join(&pkg.build_dir).join(&pkg.lean_lib_dir);
    let mut modules = BTreeMap::new();
    for (module, (source, root)) in
        statement_source_modules_with_trust(project, &pkg, scope, is_untrusted)?
    {
        if let Some(snap) = bound_snap {
            anyhow::ensure!(
                snap.entries.get(&module).and_then(|e| e.as_ref()).is_some(),
                "Statement module `{module}` missing from certified closure snapshot: fail-closed"
            );
        } else {
            let relative = source.strip_prefix(&root)?;
            let has_olean = overlay_lib_dir
                .is_some_and(|ov| ov.join(relative).with_extension("olean").is_file())
                || lib_dir.join(relative).with_extension("olean").is_file();
            anyhow::ensure!(
                has_olean,
                "No built .olean for {} after stock checking (statement pinning fails closed)",
                source.display()
            );
        }
        modules.insert(
            module,
            source.strip_prefix(project)?.to_string_lossy().to_string(),
        );
    }
    if modules.is_empty() {
        return Ok(KernelStatementReport::default());
    }
    let zygote_cfg = if let Some(snap) = bound_snap {
        let sr = store_root
            .context("Bound closure snapshot statement dump requires `store_root`: fail-closed")?;
        let cfg = crate::module_builder::resolve_project_config_with_trust(project, is_untrusted)
            .context("Failed to resolve project config for snapshot-bound statement dump")?;
        let (snap_lp, snap_dir) =
            crate::zygote::ensure_bound_audit_closure(snap, "stmt_report_before_dump")?;
        let pinned_fd = crate::zygote::snapshot_pinned_dir_raw_fd(snap);
        let parent_snap_lp =
            crate::zygote::snapshot_parent_search_path(snap).unwrap_or_else(|| snap_lp.clone());
        let (full_lp, extra_ro, cmd_pinned_fd) = if is_untrusted {
            (snap_lp, vec![snap_dir], None)
        } else {
            (parent_snap_lp, Vec::new(), pinned_fd)
        };
        let _ = crate::zygote::kernel_reader_command(sr, &cfg, &full_lp, &extra_ro, is_untrusted)?;
        Some((sr.to_path_buf(), cfg, full_lp, extra_ro, cmd_pinned_fd))
    } else if let Some(sr) = store_root {
        crate::module_builder::resolve_project_config_with_trust(project, is_untrusted)
            .ok()
            .and_then(|cfg| {
                let (base_lp, _) = crate::module_builder::build_lean_search_path(&cfg, true);
                let with_tc = if cfg.toolchain_lib_lean.as_os_str().is_empty() {
                    base_lp
                } else {
                    format!("{base_lp}:{}", cfg.toolchain_lib_lean.display())
                };
                let full_lp = if let Some(ov) = overlay_lib_dir {
                    format!("{}:{with_tc}", ov.display())
                } else {
                    with_tc
                };
                let extra_ro: Vec<PathBuf> =
                    overlay_lib_dir.iter().map(|p| (*p).to_path_buf()).collect();
                crate::zygote::kernel_reader_command(sr, &cfg, &full_lp, &extra_ro, is_untrusted)
                    .ok()
                    .map(|_| (sr.to_path_buf(), cfg, full_lp, extra_ro, None))
            })
    } else {
        None
    };
    struct HelperGuard(Option<PathBuf>);
    impl Drop for HelperGuard {
        fn drop(&mut self) {
            if let Some(ref p) = self.0 {
                let _ = fs::remove_file(p);
            }
        }
    }
    let helper_opt = if zygote_cfg.is_none() {
        let lake_dir = project.join(".lake");
        let helper_parent = if lake_dir.is_dir() {
            lake_dir
        } else {
            project.to_path_buf()
        };
        let helper = helper_parent.join(format!(
            ".turbo_statement_dump_{}.lean",
            pack::next_tmp_id()
        ));
        fs::write(
            &helper,
            format!(
                "{}\ndef main := statementHashCliMain\n",
                include_str!("../../../lean/TurboLean/StatementHash.lean")
            ),
        )?;
        Some(helper)
    } else {
        None
    };
    let _guard = HelperGuard(helper_opt.clone());
    // Distinct executables may define the same constant (`main`). Compatible
    // modules share one import, while incompatible groups split into fresh OS
    // processes. Never re-import oleans into a process with old mapped regions.
    let mut batches = vec![modules.keys().cloned().collect::<Vec<_>>()];
    let mut report = KernelStatementReport::default();
    let mut remaining = modules.clone();
    while let Some(mut batch) = batches.pop() {
        if let Some(snap) = bound_snap {
            let _ = crate::zygote::ensure_bound_audit_closure(snap, "stmt_report_before_batch")?;
        }
        let (mut command, batch_pinned_fd) =
            if let Some((ref sr, ref cfg, ref full_lp, ref extra_ro, pinned_fd)) = zygote_cfg {
                let (mut cmd, _) =
                    crate::zygote::kernel_reader_command(sr, cfg, full_lp, extra_ro, is_untrusted)?;
                cmd.arg("--statement-dump").args(&batch);
                (cmd, pinned_fd)
            } else {
                let helper = helper_opt
                    .as_ref()
                    .context("Missing statement dump helper script")?;
                let mut cmd = statement_lean_command(project, is_untrusted)?;
                if let Some(ov) = overlay_lib_dir {
                    let (base_lp, _) = crate::module_builder::resolve_project_config_with_trust(
                        project,
                        is_untrusted,
                    )
                    .map(|c| crate::module_builder::build_lean_search_path(&c, true))
                    .unwrap_or_default();
                    let new_lp = if base_lp.is_empty() {
                        ov.display().to_string()
                    } else {
                        format!("{}:{base_lp}", ov.display())
                    };
                    cmd.env("LEAN_PATH", new_lp);
                }
                cmd.arg("--run").arg(helper).args(&batch);
                (cmd, None)
            };
        let out = crate::module_builder::run_command_with_timeout_pinned_fd(
            &mut command,
            std::time::Duration::from_secs(600),
            is_untrusted,
            batch_pinned_fd,
        )?;
        if let Some(snap) = bound_snap {
            let _ = crate::zygote::ensure_bound_audit_closure(snap, "stmt_report_after_batch")?;
        }
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
        let mut shared_constants = BTreeMap::<String, SharedKernelConstantEntry>::new();
        let mut chunk = Vec::new();
        let mut seen_in_batch = std::collections::BTreeSet::<String>::new();
        for line in out.stdout.split_inclusive(|&c| c == b'\n') {
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
                seen_in_batch.insert(module.to_string());
                report
                    .csimp
                    .extend(row.csimp.context("Missing csimp audit")?);
                report.axiom_decls.extend(row.axiom_decls);
                report.unsafe_decls.extend(row.unsafe_decls);
                report.unsafe_inductives.extend(row.unsafe_inductives);
                report.implemented_by.extend(row.implemented_by);
                report.extern_decls.extend(row.extern_decls);
                let in_scope = scope.is_none_or(|p| Path::new(&rel).starts_with(p));
                for (name, digest) in
                    parse_kernel_statement_dump_with_shared(&chunk, module, &mut shared_constants)?
                {
                    if in_scope {
                        report.statements.insert(format!("{rel}::{name}"), digest);
                    }
                }
                chunk.clear();
            }
        }
        anyhow::ensure!(
            chunk.is_empty() && seen_in_batch.len() == batch.len(),
            "Incomplete kernel statement dump for batch {batch:?}"
        );
    }
    anyhow::ensure!(remaining.is_empty(), "Incomplete kernel statement dump");
    if let Some(snap) = bound_snap {
        crate::zygote::ensure_live_closure_matches_snapshot(snap, "stmt_report_complete")?;
    }
    Ok(report)
}

#[cfg(test)]
fn kernel_statement_changes(
    project: &Path,
    base: &str,
    scope: Option<&Path>,
) -> Result<Vec<String>> {
    let store_dir = std::env::temp_dir().join(format!(
        "turbo-stmt-store-{}-{}",
        std::process::id(),
        pack::next_tmp_id()
    ));
    struct StoreDirGuard(PathBuf);
    impl Drop for StoreDirGuard {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let _guard = StoreDirGuard(store_dir.clone());
    let store = TurboStore::open(Some(&store_dir))?;
    kernel_statement_changes_with_trust(&store, project, base, scope, None, &[])
}

struct StatementPolicyEnvGuard(
    Option<String>,
    Option<String>,
    Option<String>,
    Option<String>,
);

impl StatementPolicyEnvGuard {
    fn enter(policy: &StatementPolicy) -> Self {
        let guard = Self(
            std::env::var(splitter::ALLOWED_AXIOMS_ENV).ok(),
            std::env::var("TURBO_LEAN_ALLOWED_CSIMP").ok(),
            std::env::var("TURBO_LEAN_ALLOWED_UNSAFE").ok(),
            std::env::var("TURBO_LEAN_ALLOWED_IMPLEMENTED_BY").ok(),
        );
        std::env::set_var(splitter::ALLOWED_AXIOMS_ENV, policy.axioms.join(","));
        std::env::set_var("TURBO_LEAN_ALLOWED_CSIMP", policy.csimp.join(","));
        std::env::set_var("TURBO_LEAN_ALLOWED_UNSAFE", policy.unsafe_decls.join(","));
        std::env::set_var(
            "TURBO_LEAN_ALLOWED_IMPLEMENTED_BY",
            policy.implemented_by.join(","),
        );
        guard
    }
}

impl Drop for StatementPolicyEnvGuard {
    fn drop(&mut self) {
        for (k, val) in [
            (splitter::ALLOWED_AXIOMS_ENV, &self.0),
            ("TURBO_LEAN_ALLOWED_CSIMP", &self.1),
            ("TURBO_LEAN_ALLOWED_UNSAFE", &self.2),
            ("TURBO_LEAN_ALLOWED_IMPLEMENTED_BY", &self.3),
        ] {
            match val {
                Some(v) => std::env::set_var(k, v),
                None => std::env::remove_var(k),
            }
        }
    }
}

#[cfg(test)]
static HEAD_OVERLAY_HITS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

#[allow(clippy::too_many_arguments)]
fn certify_head_statement_modules_and_replay(
    store: &TurboStore,
    head_project: &Path,
    scope: Option<&Path>,
    policy: &StatementPolicy,
    is_untrusted: bool,
    overlay_lib_dir: Option<&Path>,
    overlay_rebuilt_hint: Option<&std::collections::HashSet<String>>,
    pre_resolved_cfg: Option<&crate::module_builder::ProjectConfig>,
) -> Result<(
    Option<std::collections::HashSet<String>>,
    Option<crate::zygote::ClosureSnapshot>,
)> {
    let owned_cfg;
    let cfg = if let Some(c) = pre_resolved_cfg {
        c
    } else {
        owned_cfg =
            crate::module_builder::resolve_project_config_with_trust(head_project, is_untrusted)?;
        &owned_cfg
    };
    let lib_dir = head_project
        .join(&cfg.root_pkg.build_dir)
        .join(&cfg.root_pkg.lean_lib_dir);
    let statement_modules =
        statement_source_modules_with_trust(head_project, &cfg.root_pkg, scope, is_untrusted)?;
    if statement_modules.is_empty() {
        return Ok((None, None));
    }
    let mut head_root_mods: Vec<(String, PathBuf)> = Vec::with_capacity(statement_modules.len());
    for (mod_name, (source, root)) in &statement_modules {
        let rel = source.strip_prefix(head_project)?.to_string_lossy();
        let hygiene = crate::module_builder::load_source_hygiene_cached(source)?;
        anyhow::ensure!(
            !hygiene.has_checking_weakening,
            "Soundness hygiene violation in {rel}: {:?}",
            hygiene.disallowed_items_under(&policy.axioms)
        );
        anyhow::ensure!(
            !hygiene.native_violation_under(&policy.axioms),
            "[TurboLean.KernelGate] native_decide/bv_decide in {rel} requires the base project's axiom allowlist"
        );
        let mut disallowed = hygiene.disallowed_items_under(&policy.axioms);
        if splitter::HygieneReport::has_custom_axiom_policy_under(&policy.axioms) {
            disallowed.retain(|item| item.rsplit(": ").next() != Some("axiom"));
        }
        if !policy.csimp.is_empty() {
            disallowed.retain(|item| item.rsplit(": ").next() != Some("csimp"));
        }
        if !policy.unsafe_decls.is_empty() {
            disallowed.retain(|item| item.rsplit(": ").next() != Some("unsafe declaration"));
        }
        if !policy.implemented_by.is_empty() {
            disallowed.retain(|item| item.rsplit(": ").next() != Some("implemented_by"));
        }
        anyhow::ensure!(
            disallowed.is_empty(),
            "PR Hygiene & Axiom Gate FAILED on {rel}: {disallowed:?}"
        );
        let rel_mod_path = source.strip_prefix(root)?;
        let olean_path = overlay_lib_dir
            .map(|ov| ov.join(rel_mod_path).with_extension("olean"))
            .filter(|p| p.is_file())
            .unwrap_or_else(|| lib_dir.join(rel_mod_path).with_extension("olean"));
        anyhow::ensure!(
            olean_path.is_file(),
            "No built .olean for {} after stock checking (statement pinning fails closed)",
            source.display()
        );
        head_root_mods.push((mod_name.clone(), olean_path));
    }

    let (lean_path, _) = crate::module_builder::build_lean_search_path(cfg, true);
    let mut dirs: Vec<PathBuf> = Vec::new();
    if let Some(ov) = overlay_lib_dir {
        dirs.push(ov.to_path_buf());
    }
    dirs.extend(std::env::split_paths(&lean_path));
    if !cfg.toolchain_lib_lean.as_os_str().is_empty() && !dirs.contains(&cfg.toolchain_lib_lean) {
        dirs.push(cfg.toolchain_lib_lean.clone());
    }
    let base_replay_lp = if cfg.toolchain_lib_lean.as_os_str().is_empty() {
        lean_path.clone()
    } else {
        format!("{lean_path}:{}", cfg.toolchain_lib_lean.display())
    };
    let replay_lp = if let Some(ov) = overlay_lib_dir {
        format!("{}:{base_replay_lp}", ov.display())
    } else {
        base_replay_lp.clone()
    };

    let mut worklist: Vec<String> = Vec::new();
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    for (mod_name, olean_path) in &head_root_mods {
        seen.insert(mod_name.clone());
        let (imps, _) = crate::module_builder::read_olean_binary_imports_cached(olean_path)
            .map_err(|_| {
                anyhow::anyhow!(
                    "Failed to parse binary `.olean` header of `{}`: fail-closed",
                    olean_path.display()
                )
            })?;
        worklist.extend(imps.into_iter().map(|i| i.module));
    }
    let mut dep_mods: Vec<(String, PathBuf)> = Vec::new();
    while let Some(m) = worklist.pop() {
        if !seen.insert(m.clone()) {
            continue;
        }
        let path = crate::module_builder::resolve_olean_along_search_dirs(&dirs, &m)
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "Unresolvable binary import `{m}` required by head statement build along LEAN_PATH: fail-closed"
                )
            })?;
        if crate::module_builder::is_verified_toolchain_olean_file(
            &cfg.toolchain_lib_lean,
            Some(&cfg.lean_githash),
            &path,
        ) {
            continue;
        }
        let (imps, _) =
            crate::module_builder::read_olean_binary_imports_cached(&path).map_err(|_| {
                anyhow::anyhow!(
                    "Failed to parse binary `.olean` header of imported `{m}` (`{}`): fail-closed",
                    path.display()
                )
            })?;
        worklist.extend(imps.into_iter().map(|i| i.module));
        dep_mods.push((m, path));
    }
    let mut dep_audit_mods: std::collections::HashSet<String> = std::collections::HashSet::new();
    for (m, path) in &dep_mods {
        let needs_audit = crate::module_builder::verify_imported_package_module_source_hygiene(
            cfg,
            m,
            path,
            &policy.axioms,
        )?;
        if needs_audit {
            dep_audit_mods.insert(m.clone());
        }
    }

    let _env_guard = StatementPolicyEnvGuard::enter(policy);

    let mut all_mods: Vec<String> = dep_mods
        .iter()
        .chain(head_root_mods.iter())
        .map(|(m, _)| m.clone())
        .collect();
    all_mods.sort();
    all_mods.dedup();

    if is_untrusted {
        let snap = crate::zygote::audit_compiled_modules_with_zygote_snapshot(
            store,
            cfg,
            &all_mods,
            &replay_lp,
            &[],
            true,
            false,
        )
        .context(
            "Head statement build `.olean` failed untrusted in-kernel soundness & replay audit",
        )?;
        Ok((None, snap))
    } else {
        let head_root_set: std::collections::HashSet<&str> =
            head_root_mods.iter().map(|(m, _)| m.as_str()).collect();
        let bind_and_certify_closure = |closure_lp: &str,
                                        extra_lib: Option<&Path>,
                                        required_mods: &[(&String, bool)],
                                        err_ctx: &'static str|
         -> Result<crate::zygote::ClosureSnapshot> {
            let mut snap =
                crate::zygote::materialize_bound_audit_closure(cfg, &all_mods, closure_lp)?;
            let check_pending =
                |snap_ref: &crate::zygote::ClosureSnapshot| -> Result<(Vec<String>, Vec<String>)> {
                    let (snap_lp, _) = crate::zygote::ensure_bound_audit_closure(
                        snap_ref,
                        "head_stmt_certify_lookup",
                    )?;
                    let parent_snap_lp =
                        crate::zygote::snapshot_parent_search_path(snap_ref).unwrap_or(snap_lp);
                    let live_batch =
                        crate::module_builder::ReplayLookupBatchCache::new_with_extra_root_lib(
                            store, cfg, closure_lp, extra_lib,
                        );
                    let mut snap_batch =
                        crate::module_builder::ReplayLookupBatchCache::new_with_extra_root_lib(
                            store,
                            cfg,
                            &parent_snap_lp,
                            extra_lib,
                        );
                    let mut pending_audit = Vec::new();
                    let mut pending_replay = Vec::new();
                    for &(m, needs_audit) in required_mods {
                        let Some(snap_olean) = snap_batch.resolve_module_olean(m) else {
                            anyhow::bail!(
                                    "Head statement module `{m}` missing `.olean` in bound closure snapshot: fail-closed"
                                );
                        };
                        let Some((ref orig_olean, _)) =
                            snap_ref.entries.get(m).and_then(|e| e.as_ref())
                        else {
                            anyhow::bail!(
                                    "Head statement module `{m}` missing origin entry in bound closure snapshot: fail-closed"
                                );
                        };
                        let binds_policy = live_batch.is_root_module_olean(orig_olean);
                        if needs_audit {
                            if !snap_batch.is_audited_in_store_with_binds_policy(
                                store,
                                cfg,
                                m,
                                &snap_olean,
                                binds_policy,
                            ) {
                                pending_audit.push(m.clone());
                            }
                        } else if !snap_batch.is_replayed_in_store_with_binds_policy(
                            store,
                            cfg,
                            &snap_olean,
                            binds_policy,
                        ) {
                            pending_replay.push(m.clone());
                        }
                    }
                    Ok((pending_audit, pending_replay))
                };
            let (pending_audit, pending_replay) = check_pending(&snap)?;
            if !pending_audit.is_empty() || !pending_replay.is_empty() {
                let sub_snap = crate::zygote::replay_and_audit_modules_with_zygote_snapshot(
                    store,
                    cfg,
                    &pending_audit,
                    &pending_replay,
                    closure_lp,
                    extra_lib,
                )
                .context(err_ctx)?;
                if pending_audit.len() + pending_replay.len() == all_mods.len() {
                    if let Some(full_snap) = sub_snap {
                        snap = full_snap;
                    }
                } else {
                    snap =
                        crate::zygote::materialize_bound_audit_closure(cfg, &all_mods, closure_lp)?;
                }
                let (rem_audit, rem_replay) = check_pending(&snap)?;
                anyhow::ensure!(
                        rem_audit.is_empty() && rem_replay.is_empty(),
                        "Head statement closure snapshot failed post-audit store authority re-verification (`audit={rem_audit:?}`, `replay={rem_replay:?}`): fail-closed"
                    );
            }
            crate::zygote::ensure_live_closure_matches_snapshot(
                &snap,
                "head_stmt_certify_complete",
            )?;
            Ok(snap)
        };

        let full_reqs: Vec<(&String, bool)> = dep_mods
            .iter()
            .chain(head_root_mods.iter())
            .map(|(m, _)| {
                (
                    m,
                    head_root_set.contains(m.as_str()) || dep_audit_mods.contains(m),
                )
            })
            .collect();

        if let Some(ov) = overlay_lib_dir {
            let mut rebuilt_overlay_mods: std::collections::HashSet<String> =
                std::collections::HashSet::new();
            let mut all_have_base = true;
            for (m, path) in dep_mods.iter().chain(head_root_mods.iter()) {
                let is_symlink = path
                    .symlink_metadata()
                    .map(|md| md.file_type().is_symlink())
                    .unwrap_or(false);
                let is_rebuilt = path.starts_with(ov)
                    && !is_symlink
                    && overlay_rebuilt_hint.is_none_or(|h| h.contains(m));
                if is_rebuilt {
                    let Ok(rel) = path.strip_prefix(ov) else {
                        all_have_base = false;
                        break;
                    };
                    if !lib_dir.join(rel).is_file() {
                        all_have_base = false;
                        break;
                    }
                    rebuilt_overlay_mods.insert(m.clone());
                }
            }
            if all_have_base && !rebuilt_overlay_mods.is_empty() {
                let base_reqs: Vec<(&String, bool)> = dep_mods
                    .iter()
                    .chain(head_root_mods.iter())
                    .map(|(m, _)| {
                        let needs_audit = !rebuilt_overlay_mods.contains(m)
                            && (head_root_set.contains(m.as_str()) || dep_audit_mods.contains(m));
                        (m, needs_audit)
                    })
                    .collect();
                if let Ok(base_snap) = bind_and_certify_closure(
                    &base_replay_lp,
                    None,
                    &base_reqs,
                    "Base statement build `.olean` failed in-kernel soundness & replay audit",
                ) {
                    let ov_reqs: Vec<(&String, bool)> = dep_mods
                        .iter()
                        .chain(head_root_mods.iter())
                        .filter(|(m, _)| rebuilt_overlay_mods.contains(m))
                        .map(|(m, _)| {
                            (
                                m,
                                head_root_set.contains(m.as_str()) || dep_audit_mods.contains(m),
                            )
                        })
                        .collect();
                    if let Ok(head_snap) = bind_and_certify_closure(
                        &replay_lp,
                        overlay_lib_dir,
                        &ov_reqs,
                        "Head overlay statement build `.olean` failed in-kernel soundness & replay audit",
                    ) {
                        let mut sealed_ok = crate::zygote::ensure_bound_audit_closure(
                            &base_snap,
                            "ov_equiv_base_pre",
                        )
                        .ok()
                        .zip(
                            crate::zygote::ensure_bound_audit_closure(
                                &head_snap,
                                "ov_equiv_head_pre",
                            )
                            .ok(),
                        )
                        .is_some();
                        if sealed_ok {
                            for m in &all_mods {
                                if !rebuilt_overlay_mods.contains(m)
                                    && crate::zygote::snapshot_module_artifact_set_digest(
                                        &base_snap, m,
                                    ) != crate::zygote::snapshot_module_artifact_set_digest(
                                        &head_snap, m,
                                    )
                                {
                                    sealed_ok = false;
                                    break;
                                }
                            }
                        }
                        if sealed_ok {
                            if let (Ok((base_snap_lp, base_dir)), Ok((_, head_dir))) = (
                                crate::zygote::ensure_bound_audit_closure(
                                    &base_snap,
                                    "ov_equiv_paths",
                                ),
                                crate::zygote::ensure_bound_audit_closure(
                                    &head_snap,
                                    "ov_equiv_paths_head",
                                ),
                            ) {
                                let extra_ro = [base_dir.clone(), head_dir.clone()];
                                for m in &rebuilt_overlay_mods {
                                    let rel_olean = format!(
                                        "{}.olean",
                                        crate::module_builder::module_name_to_rel_slash(m)
                                    );
                                    let old_p = base_dir.join(&rel_olean);
                                    let new_p = head_dir.join(&rel_olean);
                                    if !crate::zygote::verify_proof_irrelevant_olean_update_exec(
                                        &store.root,
                                        cfg,
                                        m,
                                        &old_p,
                                        &new_p,
                                        &base_snap_lp,
                                        &extra_ro,
                                    )
                                    .unwrap_or(false)
                                    {
                                        sealed_ok = false;
                                        break;
                                    }
                                }
                            } else {
                                sealed_ok = false;
                            }
                        }
                        if sealed_ok
                            && crate::zygote::ensure_bound_audit_closure(
                                &base_snap,
                                "ov_equiv_base_post",
                            )
                            .is_ok()
                            && crate::zygote::ensure_live_closure_matches_snapshot(
                                &head_snap,
                                "ov_equiv_head_post",
                            )
                            .is_ok()
                        {
                            return Ok((Some(rebuilt_overlay_mods), Some(head_snap)));
                        }
                    }
                }
            }
        }

        let head_snap = bind_and_certify_closure(
            &replay_lp,
            overlay_lib_dir,
            &full_reqs,
            "Head statement build `.olean` failed in-kernel soundness & replay audit",
        )?;
        Ok((None, Some(head_snap)))
    }
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

fn update_lp_bytes(h: &mut blake3::Hasher, tag: &[u8], bytes: &[u8]) {
    h.update(&(tag.len() as u64).to_le_bytes());
    h.update(tag);
    h.update(&(bytes.len() as u64).to_le_bytes());
    h.update(bytes);
}

fn hash_deterministic_file_tree(
    h: &mut blake3::Hasher,
    root: &Path,
    skip_dirs: &[PathBuf],
    only_exts: Option<&[&str]>,
    reject_lean_elab_host_effects: bool,
) -> Option<()> {
    let meta = match fs::symlink_metadata(root) {
        Ok(m) => m,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            update_lp_bytes(h, b"tree_absent", b"");
            return Some(());
        }
        Err(_) => return None,
    };
    if meta.file_type().is_symlink() || !meta.is_dir() {
        return None;
    }
    let mut stack = vec![root.to_path_buf()];
    let mut files: Vec<(String, PathBuf)> = Vec::new();
    while let Some(dir) = stack.pop() {
        let rd = fs::read_dir(&dir).ok()?;
        let mut children = Vec::new();
        for ent in rd {
            let ent = ent.ok()?;
            children.push(ent.path());
        }
        children.sort();
        for p in children {
            let name = p.file_name().and_then(|s| s.to_str()).unwrap_or("");
            if name == ".git" {
                continue;
            }
            if skip_dirs.contains(&p) {
                continue;
            }
            let st = fs::symlink_metadata(&p).ok()?;
            if st.file_type().is_symlink() {
                return None;
            }
            if st.is_dir() {
                stack.push(p);
            } else if st.is_file() {
                if let Some(exts) = only_exts {
                    let matched = exts.iter().any(|ext| {
                        p.file_name()
                            .and_then(|n| n.to_str())
                            .is_some_and(|n| n.ends_with(ext))
                    });
                    if !matched {
                        continue;
                    }
                }
                let rel = p.strip_prefix(root).ok()?.to_string_lossy().into_owned();
                files.push((rel, p));
            } else {
                return None;
            }
        }
    }
    files.sort_by(|a, b| a.0.cmp(&b.0));
    h.update(&(files.len() as u64).to_le_bytes());
    for (rel, path) in files {
        let bytes = fs::read(&path).ok()?;
        if reject_lean_elab_host_effects && rel.ends_with(".lean") {
            let src = std::str::from_utf8(&bytes).ok()?;
            if splitter::source_may_execute_elab_host_effects(src, false) {
                return None;
            }
        }
        update_lp_bytes(h, b"rel", rel.as_bytes());
        update_lp_bytes(h, b"blake3", blake3::hash(&bytes).as_bytes());
    }
    Some(())
}

fn git_tree_has_no_elab_host_effects(repo: &Path, tree_oid: &str) -> Option<()> {
    use std::io::{BufRead, BufReader, Read, Write};
    let ls = crate::trusted_tools::git(repo)
        .ok()?
        .arg("-C")
        .arg(repo)
        .args(["ls-tree", "-r", "-z", tree_oid])
        .output()
        .ok()?;
    if !ls.status.success() {
        return None;
    }
    let mut oids = Vec::new();
    for entry in ls.stdout.split(|&b| b == 0).filter(|e| !e.is_empty()) {
        let tab = entry.iter().position(|&b| b == b'\t')?;
        let rel = std::str::from_utf8(&entry[tab + 1..]).ok()?;
        if !rel.ends_with(".lean")
            || rel.starts_with(".lake/build/")
            || rel.starts_with(".lake/packages/")
        {
            continue;
        }
        let header = std::str::from_utf8(&entry[..tab]).ok()?;
        let mut fields = header.split(' ');
        let _mode = fields.next()?;
        let kind = fields.next()?;
        let oid = fields.next()?;
        if fields.next().is_some() {
            return None;
        }
        if kind == "blob" {
            oids.push(oid.to_owned());
        }
    }
    if oids.is_empty() {
        return Some(());
    }
    let mut git = crate::trusted_tools::git(repo).ok()?;
    let mut child = git
        .arg("-C")
        .arg(repo)
        .args(["cat-file", "--batch"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .ok()?;
    let mut input = child.stdin.take()?;
    let request: String = oids.iter().map(|oid| format!("{oid}\n")).collect();
    let writer = std::thread::spawn(move || input.write_all(request.as_bytes()));
    let scan_res = (|| -> Option<()> {
        let mut output = BufReader::new(child.stdout.take()?);
        for oid in &oids {
            let mut header = String::new();
            output.read_line(&mut header).ok()?;
            let fields: Vec<_> = header.trim_end().split(' ').collect();
            if fields.len() != 3 || fields[0] != oid || fields[1] != "blob" {
                return None;
            }
            let size: usize = fields[2].parse().ok()?;
            let mut bytes = vec![0; size + 1];
            output.read_exact(&mut bytes).ok()?;
            if bytes.pop() != Some(b'\n') {
                return None;
            }
            let src = std::str::from_utf8(&bytes).ok()?;
            if splitter::source_may_execute_elab_host_effects(src, false) {
                return None;
            }
        }
        Some(())
    })();
    if scan_res.is_none() {
        let _ = child.kill();
    }
    let status = child.wait().ok()?;
    let _ = writer.join();
    scan_res?;
    status.success().then_some(())
}

fn base_statement_config_files_match_live(
    repo: &Path,
    base: &str,
    proj_rel_in_repo: &Path,
    live_proj: &Path,
) -> Option<()> {
    if base.starts_with('-') {
        return None;
    }
    let prefix = proj_rel_in_repo.to_string_lossy().replace('\\', "/");
    let names = [
        "lean-toolchain",
        "lakefile.lean",
        "lakefile.toml",
        "lake-manifest.json",
    ];
    let repo_rels: Vec<String> = names.iter().map(|n| join_proj_prefix(&prefix, n)).collect();
    let ls_out = crate::trusted_tools::git(repo)
        .ok()?
        .arg("-C")
        .arg(repo)
        .args(["ls-tree", "-z", "--full-tree", base, "--"])
        .args(&repo_rels)
        .output()
        .ok()?;
    if !ls_out.status.success() {
        return None;
    }
    let mut base_oids: std::collections::HashMap<String, String> =
        std::collections::HashMap::with_capacity(names.len());
    for entry in ls_out.stdout.split(|&b| b == 0).filter(|e| !e.is_empty()) {
        let tab = entry.iter().position(|&b| b == b'\t')?;
        let header = std::str::from_utf8(&entry[..tab]).ok()?;
        let path_str = std::str::from_utf8(&entry[tab + 1..]).ok()?;
        let mut fields = header.split(' ');
        let (mode, obj_type, oid) = (fields.next()?, fields.next()?, fields.next()?);
        if fields.next().is_some() || !matches!(mode, "100644" | "100755") || obj_type != "blob" {
            return None;
        }
        base_oids.insert(path_str.to_string(), oid.to_string());
    }
    for (name, repo_rel) in names.iter().zip(repo_rels.iter()) {
        let live_path = live_proj.join(name);
        match (base_oids.get(repo_rel), fs::symlink_metadata(&live_path)) {
            (None, Err(e)) if e.kind() == std::io::ErrorKind::NotFound => continue,
            (Some(oid), Ok(meta)) if meta.is_file() && !meta.file_type().is_symlink() => {
                let live_bytes = fs::read(&live_path).ok()?;
                let cat_out = crate::trusted_tools::git(repo)
                    .ok()?
                    .arg("-C")
                    .arg(repo)
                    .args(["cat-file", "blob", oid])
                    .output()
                    .ok()?;
                if !cat_out.status.success() || cat_out.stdout != live_bytes {
                    return None;
                }
            }
            _ => return None,
        }
    }
    if !base_oids.contains_key(&repo_rels[0]) && repo != live_proj {
        let root_tc = repo.join("lean-toolchain");
        let ls_root = crate::trusted_tools::git(repo)
            .ok()?
            .arg("-C")
            .arg(repo)
            .args(["ls-tree", "-z", "--full-tree", base, "--", "lean-toolchain"])
            .output()
            .ok()?;
        if !ls_root.status.success() {
            return None;
        }
        let mut root_oid = None;
        for entry in ls_root.stdout.split(|&b| b == 0).filter(|e| !e.is_empty()) {
            let tab = entry.iter().position(|&b| b == b'\t')?;
            let header = std::str::from_utf8(&entry[..tab]).ok()?;
            let mut fields = header.split(' ');
            let (mode, obj_type, oid) = (fields.next()?, fields.next()?, fields.next()?);
            if fields.next().is_some() || !matches!(mode, "100644" | "100755") || obj_type != "blob"
            {
                return None;
            }
            root_oid = Some(oid.to_string());
        }
        match (root_oid, fs::symlink_metadata(&root_tc)) {
            (None, Err(e)) if e.kind() == std::io::ErrorKind::NotFound => {}
            (Some(oid), Ok(meta)) if meta.is_file() && !meta.file_type().is_symlink() => {
                let live_bytes = fs::read(&root_tc).ok()?;
                let cat_out = crate::trusted_tools::git(repo)
                    .ok()?
                    .arg("-C")
                    .arg(repo)
                    .args(["cat-file", "blob", &oid])
                    .output()
                    .ok()?;
                if !cat_out.status.success() || cat_out.stdout != live_bytes {
                    return None;
                }
            }
            _ => return None,
        }
    }
    Some(())
}

fn base_statement_cache_action_key(
    repo: &Path,
    base: &str,
    proj_rel_in_repo: &Path,
    relative_scope: Option<&Path>,
    cfg: &crate::module_builder::ProjectConfig,
) -> Option<String> {
    base_statement_config_files_match_live(repo, base, proj_rel_in_repo, &cfg.root_pkg.pkg_root)?;
    let ws_inputs_digest = crate::module_builder::workspace_lake_inputs_digest(cfg).ok()?;
    let spec = if proj_rel_in_repo.as_os_str().is_empty() {
        format!("{base}^{{tree}}")
    } else {
        format!("{base}:{}", proj_rel_in_repo.to_string_lossy())
    };
    let out = crate::trusted_tools::git(repo)
        .ok()?
        .arg("-C")
        .arg(repo)
        .args(["rev-parse", "--verify", &spec])
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let tree_oid = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if tree_oid.len() < 40 || !tree_oid.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    git_tree_has_no_elab_host_effects(repo, &tree_oid)?;
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean:base-stmt-map:v6\0");
    update_lp_bytes(
        &mut h,
        b"build_epoch",
        crate::TURBO_LEAN_BUILD_EPOCH.as_bytes(),
    );
    update_lp_bytes(&mut h, b"githash", cfg.lean_githash.as_bytes());
    update_lp_bytes(
        &mut h,
        b"stmt_hash_src",
        blake3::hash(include_str!("../../../lean/TurboLean/StatementHash.lean").as_bytes())
            .as_bytes(),
    );
    update_lp_bytes(&mut h, b"tree_oid", tree_oid.as_bytes());
    update_lp_bytes(&mut h, b"canon_cfg", cfg.canonical_config_digest.as_bytes());
    update_lp_bytes(&mut h, b"ws_inputs", ws_inputs_digest.as_bytes());
    let root_lake = cfg.root_pkg.pkg_root.join(".lake");
    if let Ok(entries) = fs::read_dir(&root_lake) {
        let mut extra_lake_dirs = Vec::new();
        for entry in entries {
            let entry = entry.ok()?;
            let name_os = entry.file_name();
            let s = name_os.to_str()?;
            if matches!(s, "build" | "packages" | "config") || s.starts_with('.') {
                continue;
            }
            let p = entry.path();
            let st = fs::symlink_metadata(&p).ok()?;
            if st.file_type().is_symlink() {
                return None;
            }
            if st.is_dir() {
                extra_lake_dirs.push((s.to_string(), p));
            }
        }
        extra_lake_dirs.sort_by(|a, b| a.0.cmp(&b.0));
        h.update(&(extra_lake_dirs.len() as u64).to_le_bytes());
        for (name, dir_path) in extra_lake_dirs {
            update_lp_bytes(&mut h, b"root_lake_dir", name.as_bytes());
            hash_deterministic_file_tree(&mut h, &dir_path, &[], None, true)?;
        }
    } else {
        h.update(&0u64.to_le_bytes());
    }
    h.update(&(cfg.dep_pkgs.len() as u64).to_le_bytes());
    for dp in &cfg.dep_pkgs {
        if dp.unsupported.is_some()
            || dp.native_unsupported.is_some()
            || dp.link_unsupported.is_some()
            || !dp.custom_targets.is_empty()
            || dp.libs.iter().any(|l| {
                l.unsupported.is_some()
                    || l.native_unsupported.is_some()
                    || l.link_unsupported.is_some()
            })
            || dp.exes.iter().any(|e| {
                e.unsupported.is_some()
                    || e.native_unsupported.is_some()
                    || e.link_unsupported.is_some()
            })
            || trusted_dep_snapshot_rel_path(cfg, dp).is_none()
        {
            return None;
        }
        if dep_package_has_disallowed_elab_host_effects(cfg, dp) {
            return None;
        }
        let reject_dep_elab_effects = !is_pinned_git_manifest_dep(cfg, dp);
        let dep_root = dp.pkg_root.canonicalize().ok()?;
        update_lp_bytes(&mut h, b"dep_name", dp.name.as_bytes());
        update_lp_bytes(&mut h, b"dep_base_name", dp.base_name.as_bytes());
        update_lp_bytes(&mut h, b"dep_cfg", dp.config_digest.as_bytes());
        let build_abs = dep_root.join(&dp.build_dir);
        let pkgs_abs = dep_root.join(&dp.packages_dir);
        let lake_abs = dep_root.join(".lake");
        let norm_dep_sub = |p: &Path| -> PathBuf {
            let mut out = PathBuf::new();
            for c in p.components() {
                match c {
                    std::path::Component::CurDir => {}
                    std::path::Component::ParentDir => {
                        out.pop();
                    }
                    other => out.push(other),
                }
            }
            out
        };
        let pkg_src_abs = norm_dep_sub(&dep_root.join(&dp.src_dir));
        let mut src_roots: Vec<PathBuf> = vec![pkg_src_abs.clone()];
        for lib in &dp.libs {
            if let Some(ref s) = lib.src_dir {
                src_roots.push(norm_dep_sub(&pkg_src_abs.join(s)));
            }
        }
        for exe in &dp.exes {
            if let Some(ref s) = exe.src_dir {
                src_roots.push(norm_dep_sub(&pkg_src_abs.join(s)));
            }
        }
        src_roots.sort();
        src_roots.dedup();
        h.update(&(src_roots.len() as u64).to_le_bytes());
        for sr in &src_roots {
            let sr_rel = sr.strip_prefix(&dep_root).ok()?;
            update_lp_bytes(&mut h, b"dep_src_root", sr_rel.to_string_lossy().as_bytes());
            hash_deterministic_file_tree(
                &mut h,
                sr,
                std::slice::from_ref(&pkgs_abs),
                Some(&[".lean"]),
                reject_dep_elab_effects,
            )?;
        }
        hash_deterministic_file_tree(
            &mut h,
            &dep_root,
            &[build_abs.clone(), pkgs_abs, lake_abs],
            Some(&[".lean"]),
            reject_dep_elab_effects,
        )?;
        hash_deterministic_file_tree(
            &mut h,
            &build_abs,
            &[],
            Some(&[
                ".olean",
                ".ilean",
                ".olean.server",
                ".olean.private",
                ".ir",
                ".c",
                ".a",
                ".so",
                ".dylib",
            ]),
            false,
        )?;
    }
    match relative_scope {
        Some(sc) => update_lp_bytes(&mut h, b"scope", sc.to_string_lossy().as_bytes()),
        None => update_lp_bytes(&mut h, b"no_scope", b""),
    }
    update_lp_bytes(
        &mut h,
        b"kernel_policy",
        crate::splitter::current_kernel_policy_digest().as_bytes(),
    );
    Some(h.finalize().to_hex().to_string())
}

fn head_statement_report_cache_action_key(
    head_project: &Path,
    scope: Option<&Path>,
    cfg: &crate::module_builder::ProjectConfig,
    snap: &crate::zygote::ClosureSnapshot,
) -> Option<String> {
    let _ = crate::zygote::ensure_bound_audit_closure(snap, "head_stmt_report_cache_key").ok()?;
    let mods =
        statement_source_modules_with_trust(head_project, &cfg.root_pkg, scope, false).ok()?;
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean:head-stmt-report:v2\0");
    h.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    h.update(b"\0");
    h.update(cfg.lean_githash.as_bytes());
    h.update(b"\0");
    h.update(
        blake3::hash(include_str!("../../../lean/TurboLean/StatementHash.lean").as_bytes())
            .as_bytes(),
    );
    h.update(b"\0");
    if let Some(sc) = scope {
        h.update(sc.to_string_lossy().as_bytes());
    }
    h.update(b"\x01");
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    for (module, (source, _)) in &mods {
        let olean_dig = crate::zygote::snapshot_module_artifact_set_digest(snap, module)?;
        let rel_src = source.strip_prefix(head_project).ok()?.to_string_lossy();
        h.update(module.as_bytes());
        h.update(b"\0");
        h.update(rel_src.as_bytes());
        h.update(b"\0");
        h.update(olean_dig.as_bytes());
        h.update(b"\n");
        seen.insert(module.clone());
    }
    h.update(b"\x01");
    let mut dep_digests: BTreeMap<String, String> = BTreeMap::new();
    for (m, entry_opt) in &snap.entries {
        if seen.contains(m) {
            continue;
        }
        let Some((ref orig_path, _)) = entry_opt.as_ref() else {
            // `snap.complete` is already enforced by `ensure_bound_audit_closure`, which permits
            // `None` entries exclusively for verified toolchain builtins (e.g., `Init`).
            continue;
        };
        if crate::module_builder::is_verified_toolchain_olean_file(
            &cfg.toolchain_lib_lean,
            Some(&cfg.lean_githash),
            orig_path,
        ) {
            continue;
        }
        let dig = crate::zygote::snapshot_module_artifact_set_digest(snap, m)?;
        dep_digests.insert(m.clone(), dig);
    }
    for (m, dig) in &dep_digests {
        h.update(m.as_bytes());
        h.update(b":");
        h.update(dig.as_bytes());
        h.update(b"\n");
    }
    let _ =
        crate::zygote::ensure_bound_audit_closure(snap, "head_stmt_report_cache_key_post").ok()?;
    Some(h.finalize().to_hex().to_string())
}

fn read_cached_json_blob<T: serde::de::DeserializeOwned>(
    store: &TurboStore,
    action_key: &str,
) -> Option<T> {
    let entries = store.get_cached_action(action_key, "trusted").ok()??;
    let entry = entries.first()?;
    let src = store.ensure_blob_uncompressed(&entry.blob_hash).ok()?;
    let bytes = fs::read(&src).ok()?;
    if blake3::hash(&bytes).to_hex().as_str() != entry.blob_hash {
        return None;
    }
    serde_json::from_slice(&bytes).ok()
}

fn write_cached_json_blob<T: serde::Serialize>(
    store_root: &Path,
    action_key: &str,
    toolchain: &str,
    action_kind: &str,
    rel_path: &str,
    value: &T,
    dur_ms: i64,
) {
    let Ok(bytes) = serde_json::to_vec(value) else {
        return;
    };
    let Ok(mut st) = TurboStore::open(Some(store_root)) else {
        return;
    };
    if let Ok(crate::db::SingleflightOutcome::Leader(lease)) =
        st.acquire_singleflight(action_key, toolchain, action_kind, "trusted")
    {
        if st
            .publish_action_with_blob(&lease, &bytes, "stmt_report", rel_path, dur_ms, "trusted")
            .is_err()
        {
            st.remove_singleflight_done(&lease.action_key);
        }
    }
}

fn kernel_statement_changes_with_trust(
    store: &TurboStore,
    project: &Path,
    base: &str,
    scope: Option<&Path>,
    untrusted_cfg: Option<&crate::module_builder::ProjectConfig>,
    proof_only_project_rel_files: &[String],
) -> Result<Vec<String>> {
    let repo = resolve_git_toplevel(project)?;
    let proj_rel_in_repo = project.strip_prefix(&repo)?.to_path_buf();
    let relative_scope = scope
        .map(|p| -> Result<PathBuf> {
            let joined = if p.is_absolute() {
                p.to_path_buf()
            } else {
                project.join(p)
            };
            let canon_project = project
                .canonicalize()
                .unwrap_or_else(|_| project.to_path_buf());
            let joined_canon = joined.canonicalize().ok();
            let relative = joined
                .strip_prefix(project)
                .ok()
                .or_else(|| {
                    joined_canon
                        .as_deref()
                        .and_then(|j| j.strip_prefix(&canon_project).ok())
                })
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
    let trusted_cfg = if is_untrusted {
        None
    } else {
        crate::module_builder::resolve_project_config(project).ok()
    };
    let policy = StatementPolicy::at(project, base);
    let _policy_env_guard = StatementPolicyEnvGuard::enter(&policy);
    let statement_scope = relative_scope.as_deref();
    let trusted_statement_build = |proj: &Path, is_disposable_snapshot: bool| -> Result<()> {
        let pkg = crate::module_builder::resolve_package_config(proj, true)?;
        let lib_dir = proj.join(&pkg.build_dir).join(&pkg.lean_lib_dir);
        let mut mods = statement_source_modules_with_trust(proj, &pkg, statement_scope, false)?;
        if statement_scope.is_some() && !mods.is_empty() {
            let all_project_modules = statement_source_modules_with_trust(proj, &pkg, None, false)?;
            let mut queue: Vec<String> = mods.keys().cloned().collect();
            while let Some(cur) = queue.pop() {
                let Some((src_path, _)) = mods.get(&cur) else {
                    continue;
                };
                let header =
                    crate::module_builder::parse_header_info(&fs::read_to_string(src_path)?);
                for imp in header.imports {
                    if !mods.contains_key(&imp) {
                        if let Some(entry) = all_project_modules.get(&imp) {
                            mods.insert(imp.clone(), entry.clone());
                            queue.push(imp);
                        }
                    }
                }
            }
        }
        let mut owned_targets: Vec<String> = Vec::new();
        let mut standalone = BTreeMap::new();
        for (name, (source, root)) in &mods {
            let owned = pkg.libs.iter().any(|lib| {
                let lib_root = proj
                    .join(&pkg.src_dir)
                    .join(lib.src_dir.as_deref().unwrap_or(Path::new("")));
                lib_root == *root && crate::module_builder::lib_can_build_module(lib, name)
            }) || pkg.exes.iter().any(|exe| exe.root == *name);
            if owned {
                owned_targets.push(format!("+{name}:olean"));
            } else {
                standalone.insert(name.clone(), (source.clone(), root.clone()));
            }
        }
        if !standalone.is_empty() && statement_scope.is_none() {
            let all_project_modules = &mods;
            for (source, _) in standalone.values() {
                for imp in
                    crate::module_builder::parse_header_info(&fs::read_to_string(source)?).imports
                {
                    if let Some((_, root)) = all_project_modules.get(&imp) {
                        let imp_owned = pkg.libs.iter().any(|lib| {
                            let lib_root = proj
                                .join(&pkg.src_dir)
                                .join(lib.src_dir.as_deref().unwrap_or(Path::new("")));
                            lib_root == *root
                                && crate::module_builder::lib_can_build_module(lib, &imp)
                        }) || pkg.exes.iter().any(|exe| exe.root == imp);
                        if imp_owned {
                            owned_targets.push(format!("+{imp}:olean"));
                        }
                    }
                }
            }
        }
        owned_targets.sort();
        owned_targets.dedup();
        let mut temp_store = TurboStore::open(Some(&store.root))?;
        if is_disposable_snapshot {
            if let Some(ref src_cfg) = trusted_cfg {
                let _ = crate::module_builder::seed_verified_fresh_modules_into_disposable_snapshot(
                    src_cfg,
                    proj,
                    &owned_targets,
                );
            }
        }
        let mut snapshot_incremental_ok = false;
        if is_disposable_snapshot && !owned_targets.is_empty() {
            if let Ok(proj_cfg) =
                crate::module_builder::resolve_project_config_with_trust(proj, false)
            {
                if let Ok(dag) = crate::module_builder::build_module_dag_for_trusted_statement(
                    &proj_cfg,
                    &owned_targets,
                ) {
                    let empty_proof_only = std::collections::HashSet::new();
                    if let Some(dirty_mods) =
                        crate::module_builder::find_dirty_modules_in_otherwise_fresh_dag(
                            &proj_cfg,
                            &dag,
                            16,
                            &empty_proof_only,
                        )
                    {
                        if dirty_mods.is_empty()
                            || crate::module_builder::compile_disposable_snapshot_dirty_modules_direct(
                                &proj_cfg,
                                &dag,
                                &dirty_mods,
                            )
                            .is_ok()
                        {
                            snapshot_incremental_ok = true;
                        }
                    }
                }
            }
        }
        let already_fresh = snapshot_incremental_ok
            || (!is_disposable_snapshot
                && (owned_targets.is_empty()
                    || crate::module_builder::resolve_project_config_with_trust(proj, false)
                        .and_then(|proj_cfg| {
                            let dag =
                                crate::module_builder::build_module_dag_for_trusted_statement(
                                    &proj_cfg,
                                    &owned_targets,
                                )?;
                            Ok(crate::module_builder::are_dag_modules_fresh_by_lake_trace(
                                &proj_cfg, &dag,
                            ))
                        })
                        .unwrap_or(false)));
        let mut native_ok = already_fresh
            || owned_targets.is_empty()
            || (is_disposable_snapshot
                && crate::module_builder::build_project_modules_native_with_options(
                    &mut temp_store,
                    proj,
                    &owned_targets,
                    "trusted",
                    0,
                    false,
                    true,
                    None,
                    false,
                )
                .is_ok());
        if native_ok && !standalone.is_empty() {
            native_ok = compile_standalone_statement_modules(
                proj,
                &pkg,
                &lib_dir,
                standalone,
                false,
                Some(&mut temp_store),
            )
            .is_ok();
        }
        let all_built = native_ok
            && statement_source_modules_with_trust(proj, &pkg, statement_scope, false)?
                .values()
                .all(|(source, root)| {
                    let is_mod = fs::read_to_string(source)
                        .map(|s| crate::module_builder::parse_header_info(&s).is_module)
                        .unwrap_or(false);
                    source
                        .strip_prefix(root)
                        .map(|rel| {
                            standalone_artifacts_present_on_disk(
                                &lib_dir.join(rel).with_extension("olean"),
                                is_mod,
                            )
                        })
                        .unwrap_or(false)
                });
        if !all_built {
            stock_statement_build_with_trust(proj, statement_scope, false)?;
        }
        Ok(())
    };
    let base_cache_key = trusted_cfg.as_ref().and_then(|cfg| {
        base_statement_cache_action_key(&repo, base, &proj_rel_in_repo, statement_scope, cfg)
    });
    let before: BTreeMap<String, String> = if let Some(cached) = base_cache_key
        .as_deref()
        .and_then(|k| read_cached_json_blob::<BTreeMap<String, String>>(store, k))
    {
        cached
    } else {
        let base_t0 = std::time::Instant::now();
        let base_pkg_cfg = base_revision_package_config(store, &repo, project, base)?;
        let baseline =
            StatementSnapshot::at_scoped(&repo, base, &proj_rel_in_repo, base_pkg_cfg.as_ref())?;
        let base_project = baseline.path.join(&proj_rel_in_repo);
        ensure_statement_lake_project(&base_project)?;
        if let Some(cfg) = untrusted_cfg {
            clear_untrusted_statement_build_products(&base_project)?;
            seed_base_statement_dependencies(&base_project, project, cfg)?;
            stock_statement_build_with_trust(&base_project, statement_scope, true)?;
        } else {
            if let Some(ref cfg) = trusted_cfg {
                seed_trusted_statement_dependencies(&base_project, cfg)?;
            }
            trusted_statement_build(&base_project, true)?;
        }
        let computed = built_kernel_statements_with_trust(
            &base_project,
            statement_scope,
            is_untrusted,
            Some(&store.root),
            None,
        )?;
        if let Some(ref pre_key) = base_cache_key {
            if let Ok(post_cfg) = crate::module_builder::resolve_project_config(project) {
                if base_statement_cache_action_key(
                    &repo,
                    base,
                    &proj_rel_in_repo,
                    statement_scope,
                    &post_cfg,
                )
                .as_deref()
                    == Some(pre_key.as_str())
                {
                    write_cached_json_blob(
                        &store.root,
                        pre_key,
                        &post_cfg.toolchain,
                        "base_stmt_map",
                        "base_statements.json",
                        &computed,
                        base_t0.elapsed().as_millis() as i64,
                    );
                }
            }
        }
        computed
    };
    let make_head_snapshot = || -> Result<StatementSnapshot> {
        let head_pkg_for_gitlinks = untrusted_cfg
            .map(|cfg| &cfg.root_pkg)
            .or_else(|| trusted_cfg.as_ref().map(|cfg| &cfg.root_pkg));
        let snapshot =
            StatementSnapshot::at_scoped(&repo, "HEAD", &proj_rel_in_repo, head_pkg_for_gitlinks)?;
        overlay_statement_sources(&repo, &snapshot.path)?;
        let snapshot_project = snapshot.path.join(&proj_rel_in_repo);
        ensure_statement_lake_project(&snapshot_project)?;
        if let Some(cfg) = untrusted_cfg {
            clear_untrusted_statement_build_products(&snapshot_project)?;
            seed_statement_dependencies(&snapshot_project, cfg)?;
        } else if let Some(ref cfg) = trusted_cfg {
            seed_trusted_statement_dependencies(&snapshot_project, cfg)?;
        }
        Ok(snapshot)
    };
    let mut head_snapshot = if is_untrusted || !crate::lake_build::has_lake_config(project) {
        Some(make_head_snapshot()?)
    } else {
        None
    };
    let head_project = head_snapshot
        .as_ref()
        .map(|s| s.path.join(&proj_rel_in_repo))
        .unwrap_or_else(|| project.to_path_buf());
    let try_head_overlay =
        || -> Option<(crate::check::PrivateScratchDir, KernelStatementReport)> {
            if is_untrusted || head_snapshot.is_some() {
                return None;
            }
            let cfg = trusted_cfg.as_ref()?;
            if cfg
                .dep_pkgs
                .iter()
                .any(|dp| dep_package_has_disallowed_elab_host_effects(cfg, dp))
            {
                return None;
            }
            let pkg = crate::module_builder::resolve_package_config(&head_project, true).ok()?;
            let mut mods =
                statement_source_modules_with_trust(&head_project, &pkg, statement_scope, false)
                    .ok()?;
            if statement_scope.is_some() && !mods.is_empty() {
                let all_project_modules =
                    statement_source_modules_with_trust(&head_project, &pkg, None, false).ok()?;
                let mut queue: Vec<String> = mods.keys().cloned().collect();
                while let Some(cur) = queue.pop() {
                    let Some((src_path, _)) = mods.get(&cur) else {
                        continue;
                    };
                    let src_str = fs::read_to_string(src_path).ok()?;
                    let header = crate::module_builder::parse_header_info(&src_str);
                    for imp in header.imports {
                        if !mods.contains_key(&imp) {
                            if let Some(entry) = all_project_modules.get(&imp) {
                                mods.insert(imp.clone(), entry.clone());
                                queue.push(imp);
                            }
                        }
                    }
                }
            }
            let mut owned_targets: Vec<String> = Vec::new();
            let mut standalone = BTreeMap::new();
            for (name, (source, root)) in &mods {
                let owned = pkg.libs.iter().any(|lib| {
                    let lib_root = head_project
                        .join(&pkg.src_dir)
                        .join(lib.src_dir.as_deref().unwrap_or(Path::new("")));
                    lib_root == *root && crate::module_builder::lib_can_build_module(lib, name)
                }) || pkg.exes.iter().any(|exe| exe.root == *name);
                if owned {
                    owned_targets.push(format!("+{name}:olean"));
                } else {
                    standalone.insert(name.clone(), (source.clone(), root.clone()));
                }
            }
            owned_targets.sort();
            owned_targets.dedup();
            if owned_targets.is_empty() {
                return None;
            }
            let dag =
                crate::module_builder::build_module_dag_for_trusted_statement(cfg, &owned_targets)
                    .ok()?;
            let mut proof_only_base_trace_src_hashes = std::collections::HashSet::new();
            if !proof_only_project_rel_files.is_empty() {
                let proj_prefix = proj_rel_in_repo.to_string_lossy().replace('\\', "/");
                let mut repo_rels = Vec::with_capacity(proof_only_project_rel_files.len());
                let mut repo_rel_to_proj_rel =
                    std::collections::HashMap::with_capacity(proof_only_project_rel_files.len());
                for pf in proof_only_project_rel_files {
                    let rr = join_proj_prefix(&proj_prefix, pf);
                    repo_rel_to_proj_rel.insert(rr.clone(), pf.clone());
                    repo_rels.push(rr);
                }
                if let Ok(base_blobs) = fetch_git_blobs_batch(&repo, base, &repo_rels) {
                    let mut proj_rel_to_base_src_h =
                        std::collections::HashMap::with_capacity(base_blobs.len());
                    for (rr, base_src) in base_blobs {
                        if let Some(pf) = repo_rel_to_proj_rel.get(&rr) {
                            proj_rel_to_base_src_h.insert(
                                pf.clone(),
                                format!(
                                    "{:016x}",
                                    crate::module_builder::lake_hash_text(&base_src)
                                ),
                            );
                        }
                    }
                    let canon_proj = head_project
                        .canonicalize()
                        .unwrap_or_else(|_| head_project.clone());
                    for (mod_name, node) in &dag.nodes {
                        let node_canon = node
                            .src_path
                            .canonicalize()
                            .unwrap_or_else(|_| node.src_path.clone());
                        let rel_pf = node
                            .src_path
                            .strip_prefix(&head_project)
                            .ok()
                            .or_else(|| node_canon.strip_prefix(&canon_proj).ok())
                            .map(|r| r.to_string_lossy().replace('\\', "/"));
                        if let Some(pf) = rel_pf {
                            let normalized_pf = Path::new(&pf)
                                .components()
                                .filter(|c| !matches!(c, std::path::Component::CurDir))
                                .collect::<PathBuf>()
                                .to_string_lossy()
                                .replace('\\', "/");
                            if let Some(base_src_h) = proj_rel_to_base_src_h
                                .get(&normalized_pf)
                                .or_else(|| proj_rel_to_base_src_h.get(&pf))
                            {
                                proof_only_base_trace_src_hashes
                                    .insert((mod_name.clone(), base_src_h.clone()));
                            }
                        }
                    }
                }
            }
            let dirty_mods = crate::module_builder::find_dirty_modules_in_otherwise_fresh_dag(
                cfg,
                &dag,
                16,
                &proof_only_base_trace_src_hashes,
            )?;
            if dirty_mods.is_empty() {
                return None;
            }
            let scratch_base = crate::check::verified_private_temp_scratch_base().ok()?;
            let ov_guard =
                crate::check::PrivateScratchDir::create(&scratch_base, "turbo_head_stmt_ov")
                    .ok()?;
            let ov_lib = crate::module_builder::compile_overlay_modules_direct(
                cfg,
                &dag,
                &dirty_mods,
                &ov_guard.path,
            )
            .ok()?;
            let mut rebuilt_hint: std::collections::HashSet<String> =
                dirty_mods.iter().cloned().collect();
            if !standalone.is_empty() {
                let base_lib_dir = head_project.join(&pkg.build_dir).join(&pkg.lean_lib_dir);
                let (base_lp, _) = crate::module_builder::build_lean_search_path(cfg, true);
                let ov_lp = format!("{}:{base_lp}", ov_lib.display());
                let mut pending: BTreeMap<String, (PathBuf, PathBuf, String, Vec<String>, bool)> =
                    BTreeMap::new();
                for (name, (source, root)) in standalone {
                    let src_str = fs::read_to_string(&source).ok()?;
                    let header = crate::module_builder::parse_header_info(&src_str);
                    pending.insert(
                        name,
                        (source, root, src_str, header.imports, header.is_module),
                    );
                }
                while !pending.is_empty() {
                    let ready: Vec<String> = pending
                        .iter()
                        .filter(|(_, (_, _, _, imps, _))| {
                            imps.iter().all(|m| !pending.contains_key(m))
                        })
                        .map(|(name, _)| name.clone())
                        .collect();
                    if ready.is_empty() {
                        return None;
                    }
                    for name in ready {
                        let (source, root, src_str, imps, is_mod) = pending.remove(&name)?;
                        let rel = source.strip_prefix(&root).ok()?;
                        let existing_olean = base_lib_dir.join(rel).with_extension("olean");
                        let touches_rebuilt =
                            imps.iter().any(|m| rebuilt_hint.contains(m.as_str()));
                        let fresh_unchanged = !touches_rebuilt
                            && standalone_artifacts_present_on_disk(&existing_olean, is_mod)
                            && standalone_statement_olean_action_key(
                                cfg,
                                &pkg,
                                &name,
                                rel,
                                &src_str,
                                &imps,
                                Some(&ov_lib),
                            )
                            .and_then(|key| store.get_cached_action(&key, "trusted").ok().flatten())
                            .is_some_and(|outs| {
                                let Some(mapped) = validate_standalone_artifact_outputs(
                                    &outs,
                                    &base_lib_dir,
                                    rel,
                                    is_mod,
                                ) else {
                                    return false;
                                };
                                crate::module_builder::olean_artifact_paths(&existing_olean)
                                    .into_iter()
                                    .all(|(_, cand)| {
                                        mapped.values().any(|p| p == &cand)
                                            || fs::symlink_metadata(&cand).is_err()
                                    })
                                    && outs.iter().all(|entry| {
                                        mapped
                                            .get(&entry.rel_path)
                                            .and_then(|p| fs::read(p).ok())
                                            .is_some_and(|b| {
                                                blake3::hash(&b).to_hex().as_str()
                                                    == entry.blob_hash
                                            })
                                    })
                            });
                        if fresh_unchanged {
                            let dst_olean = ov_lib.join(rel).with_extension("olean");
                            for (_, src_art) in
                                crate::module_builder::olean_artifact_paths(&existing_olean)
                            {
                                if src_art.is_file() {
                                    let file_name = src_art.file_name()?;
                                    let dst_art = dst_olean
                                        .parent()
                                        .map(|p| p.join(file_name))
                                        .unwrap_or_else(|| ov_lib.join(file_name));
                                    if let Some(parent) = dst_art.parent() {
                                        fs::create_dir_all(parent).ok()?;
                                    }
                                    if !dst_art.exists() {
                                        crate::zygote::copy_file_reflink(&src_art, &dst_art)
                                            .ok()?;
                                    }
                                }
                            }
                        } else {
                            rebuilt_hint.insert(name);
                            let output = ov_lib.join(rel).with_extension("olean");
                            if let Some(parent) = output.parent() {
                                fs::create_dir_all(parent).ok()?;
                            }
                            let mut cmd = statement_lean_command(&head_project, false).ok()?;
                            cmd.env("LEAN_PATH", &ov_lp);
                            cmd.args(&pkg.weak_lean_args).args(&pkg.more_lean_args);
                            for (k, v) in &pkg.lean_options {
                                cmd.arg(format!("-D{}={}", k.to_lean_string(), v.raw_cli_value()));
                            }
                            cmd.arg(&source).arg("-R").arg(&root).arg("-o").arg(&output);
                            let out = crate::module_builder::run_command_with_timeout(
                                &mut cmd,
                                std::time::Duration::from_secs(300),
                                false,
                            )
                            .ok()?;
                            if !out.status.success()
                                || !standalone_artifacts_present_on_disk(&output, is_mod)
                            {
                                return None;
                            }
                        }
                    }
                }
            }
            let (_proof_irrelevant_mods, ov_cert_snap) = certify_head_statement_modules_and_replay(
                store,
                &head_project,
                statement_scope,
                &policy,
                false,
                Some(&ov_lib),
                Some(&rebuilt_hint),
                Some(cfg),
            )
            .ok()?;
            let head_key = ov_cert_snap.as_ref().and_then(|snap| {
                head_statement_report_cache_action_key(&head_project, statement_scope, cfg, snap)
            });
            let rep = if let Some(cached) = head_key
                .as_deref()
                .and_then(|k| read_cached_json_blob::<KernelStatementReport>(store, k))
            {
                if let Some(ref snap) = ov_cert_snap {
                    crate::zygote::ensure_live_closure_matches_snapshot(
                        snap,
                        "ov_head_stmt_cache_hit",
                    )
                    .ok()?;
                }
                cached
            } else {
                let head_t0 = std::time::Instant::now();
                let computed = built_kernel_statement_report_bound(
                    &head_project,
                    statement_scope,
                    false,
                    Some(&store.root),
                    Some(&ov_lib),
                    ov_cert_snap.as_ref(),
                )
                .ok()?;
                if let (Some(ref key), Some(ref snap)) = (&head_key, &ov_cert_snap) {
                    crate::zygote::ensure_live_closure_matches_snapshot(
                        snap,
                        "ov_head_stmt_cache_write",
                    )
                    .ok()?;
                    write_cached_json_blob(
                        &store.root,
                        key,
                        &cfg.toolchain,
                        "head_stmt_report",
                        "head_statement_report.json",
                        &computed,
                        head_t0.elapsed().as_millis() as i64,
                    );
                }
                computed
            };
            Some((ov_guard, rep))
        };
    let after: KernelStatementReport = if let Some((_ov_guard, rep)) = try_head_overlay() {
        #[cfg(test)]
        HEAD_OVERLAY_HITS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        rep
    } else {
        let head_project = if head_snapshot.is_none() {
            let snap = make_head_snapshot()?;
            let p = snap.path.join(&proj_rel_in_repo);
            head_snapshot = Some(snap);
            p
        } else {
            head_project
        };
        if is_untrusted {
            stock_statement_build_with_trust(&head_project, statement_scope, true)?;
        } else {
            trusted_statement_build(&head_project, head_snapshot.is_some())?;
        }
        let snapshot_cfg = if head_snapshot.is_some() {
            None
        } else {
            trusted_cfg.as_ref()
        };
        let (_, head_cert_snap) = certify_head_statement_modules_and_replay(
            store,
            &head_project,
            statement_scope,
            &policy,
            is_untrusted,
            None,
            None,
            snapshot_cfg,
        )?;
        let snapshot_resolved_cfg = if head_snapshot.is_some() && !is_untrusted {
            crate::module_builder::resolve_project_config_with_trust(&head_project, false).ok()
        } else {
            None
        };
        let eff_cfg = snapshot_resolved_cfg.as_ref().or(snapshot_cfg);
        let head_cache_key = if !is_untrusted {
            eff_cfg
                .zip(head_cert_snap.as_ref())
                .and_then(|(cfg, snap)| {
                    head_statement_report_cache_action_key(
                        &head_project,
                        statement_scope,
                        cfg,
                        snap,
                    )
                })
        } else {
            None
        };
        if let Some(cached) = head_cache_key
            .as_deref()
            .and_then(|k| read_cached_json_blob::<KernelStatementReport>(store, k))
        {
            if let Some(ref snap) = head_cert_snap {
                crate::zygote::ensure_live_closure_matches_snapshot(snap, "head_stmt_cache_hit")?;
            }
            cached
        } else {
            let head_t0 = std::time::Instant::now();
            let computed = built_kernel_statement_report_bound(
                &head_project,
                statement_scope,
                is_untrusted,
                Some(&store.root),
                None,
                head_cert_snap.as_ref(),
            )?;
            if let (Some(ref key), Some(cfg), Some(ref snap)) =
                (&head_cache_key, eff_cfg, &head_cert_snap)
            {
                crate::zygote::ensure_live_closure_matches_snapshot(snap, "head_stmt_cache_write")?;
                write_cached_json_blob(
                    &store.root,
                    key,
                    &cfg.toolchain,
                    "head_stmt_report",
                    "head_statement_report.json",
                    &computed,
                    head_t0.elapsed().as_millis() as i64,
                );
            }
            computed
        }
    };
    policy.audit(&after)?;
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

fn pr_verify_file_worker_jobs(
    is_untrusted: bool,
    available_cpus: usize,
    files_len: usize,
) -> usize {
    let base = available_cpus.max(1);
    let capped = if is_untrusted { base.min(2) } else { base };
    capped.min(files_len.max(1))
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
    // One top-level command, one Lake-input memo window.
    crate::module_builder::reset_lake_inputs_tag_memo();
    let t0 = Instant::now();
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.clone());
    let toolchain = detect_toolchain(&canon_dir);
    let kernel_prov = crate::kernel::resolve_kernel_engine(
        crate::kernel::resolve_kernel_selection_from_env(None)?,
        &toolchain,
    )?;
    let is_untrusted = mode == "untrusted";
    if !is_untrusted
        && (canon_dir.join("lakefile.lean").is_file() || canon_dir.join("lakefile.toml").is_file())
    {
        crate::module_builder::resolve_project_config(&canon_dir)
            .context("PR static Lean option validation failed")?;
    }
    let trust_domain = if is_untrusted {
        "untrusted:ci".to_string()
    } else {
        "trusted".to_string()
    };

    let untrusted_pr_cfg = if is_untrusted {
        if crate::module_builder::probe_bwrap_sandbox(&canon_dir).is_none() {
            anyhow::bail!(
                "Untrusted PR verification requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
            );
        }
        Some(resolve_untrusted_pr_project_config(&canon_dir, &toolchain)?)
    } else {
        None
    };
    let mut verification_trust = PrVerificationTrust {
        is_untrusted,
        untrusted_cfg: untrusted_pr_cfg.as_ref(),
        extra_ro_olean_dirs: Vec::new(),
    };

    let classify_t0 = Instant::now();
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
    let _ = classify_t0;

    let base_policy = StatementPolicy::at(&canon_dir, &base);
    let trusted_assurance = if !is_untrusted && scope.is_none() {
        crate::module_builder::optional_package_config(&canon_dir)
            .ok()
            .flatten()
            .map(|pkg| {
                crate::module_builder::discover_trusted_assurance_surface(
                    &canon_dir,
                    &pkg,
                    &base_policy.axioms,
                )
            })
            .unwrap_or_default()
    } else {
        crate::module_builder::TrustedAssuranceSurface::default()
    };

    for (file, split) in &current_splits {
        let canon_file = canon_dir
            .join(file)
            .canonicalize()
            .unwrap_or_else(|_| canon_dir.join(file));
        let is_trusted_assurance_script = !is_untrusted
            && scope.is_none()
            && !split.hygiene.has_checking_weakening_option
            && split.shards.is_empty()
            && trusted_assurance.canon_paths.contains(&canon_file);
        anyhow::ensure!(
            !split.hygiene.has_checking_weakening || is_trusted_assurance_script,
            "Soundness hygiene violation in {file}: {:?}",
            split.hygiene.disallowed_items_under(&base_policy.axioms)
        );
        anyhow::ensure!(!split.hygiene.native_violation_under(&base_policy.axioms),
            "[TurboLean.KernelGate] native_decide/bv_decide in {file} requires the base project's axiom allowlist");
    }

    let source_statement_edit = !classification.statement_edited_theorems.is_empty();
    if disallow_statement_changes && (classification.interface_drift || source_statement_edit) {
        anyhow::bail!(
            "PR statement/interface change gate FAILED (--disallow-statement-changes, mode={}): interface_drift={}, source_statement_edit={}, altered_files={:?}, statement_edited_theorems={:?}",
            mode,
            classification.interface_drift,
            source_statement_edit,
            classification.altered_interface_files,
            classification.statement_edited_theorems
        );
    }

    // Only a theorem whose proof body alone changed is a local edit (proof irrelevance). Anything
    // else (statement, definition, instance, attribute, option, import, added or deleted file)
    // can break other modules: re-check them and their dependents before per-theorem checks
    // count. In `--mode untrusted`, never invoke unsandboxed `lake build` or `[lake] build_command`;
    // compile inside `bwrap` with Stage 1C `--audit-modules` instead.
    let lake_t0 = Instant::now();
    let mut lake_rechecked_modules = 0usize;
    let mut untrusted_deps_built = false;
    let mut standalone_overlays: Vec<crate::lake_build::StandaloneOleanOverlay> = Vec::new();
    let is_assurance_rel = |rel: &String| -> bool {
        let p = canon_dir.join(rel);
        trusted_assurance
            .canon_paths
            .contains(&p.canonicalize().unwrap_or(p))
    };
    let mut trusted_replay_targets: Vec<PathBuf> = shards_by_file
        .keys()
        .chain(classification.modified_files.iter())
        .chain(classification.altered_interface_files.iter())
        .filter(|f| !is_assurance_rel(f))
        .map(|f| canon_dir.join(f))
        .collect();
    let mut trusted_replay_mods: Vec<String> = Vec::new();
    if !classification.altered_interface_files.is_empty() {
        if is_untrusted {
            let (rechecked_count, built_all, overlay) =
                crate::lake_build::untrusted_recheck_dependents(
                    store,
                    &canon_dir,
                    &classification.altered_interface_files,
                    &trust_domain,
                    json,
                )?;
            lake_rechecked_modules = rechecked_count;
            untrusted_deps_built = built_all;
            if let Some(ov) = overlay {
                verification_trust
                    .extra_ro_olean_dirs
                    .push(ov.olean_dir.clone());
                standalone_overlays.push(ov);
            }
        } else {
            let mut certifiable_altered = Vec::new();
            let mut assurance_altered = Vec::new();
            for f in &classification.altered_interface_files {
                if is_assurance_rel(f) {
                    assurance_altered.push(f.clone());
                } else {
                    certifiable_altered.push(f.clone());
                }
            }
            if !certifiable_altered.is_empty() {
                let (rechecked_count, rechecked_files, rechecked_mods, overlay) =
                    crate::lake_build::lake_recheck_dependents_with_store(
                        Some(store),
                        &canon_dir,
                        &certifiable_altered,
                        Some(&base),
                        true,
                    )?;
                lake_rechecked_modules = rechecked_count;
                trusted_replay_targets.extend(rechecked_files);
                trusted_replay_mods.extend(rechecked_mods);
                if let Some(ov) = overlay {
                    verification_trust
                        .extra_ro_olean_dirs
                        .push(ov.olean_dir.clone());
                    standalone_overlays.push(ov);
                }
            }
            let modified_assurance: Vec<String> = assurance_altered
                .into_iter()
                .filter(|f| classification.modified_files.contains(f))
                .collect();
            if !modified_assurance.is_empty() {
                let (assur_count, _, _, _) = crate::lake_build::lake_recheck_dependents_with_store(
                    Some(store),
                    &canon_dir,
                    &modified_assurance,
                    Some(&base),
                    false,
                )?;
                lake_rechecked_modules += assur_count;
            }
        }
    }
    if !is_untrusted {
        let build_missing = !crate::lake_build::worktree_auto_link_disabled(&canon_dir)
            && crate::lake_build::has_lake_config(&canon_dir);
        crate::lake_build::ensure_project_imports_fresh(
            &canon_dir,
            &trusted_replay_targets,
            Some(&base),
            build_missing,
        )?;
        trusted_replay_targets.sort();
        trusted_replay_targets.dedup();
        trusted_replay_mods.sort();
        trusted_replay_mods.dedup();
        crate::lake_build::ensure_modules_and_imports_replayed(
            store,
            &canon_dir,
            &trusted_replay_targets,
            &trusted_replay_mods,
        )?;
    }
    let lake_recheck_ms = lake_t0.elapsed().as_millis();

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
                    let in_pkg_or_project =
                        crate::module_builder::resolve_importable_module_in_package(
                            &cfg.root_pkg,
                            true,
                            m,
                        )
                        .is_some()
                            || cfg.dep_pkgs.iter().any(|dp| {
                                crate::module_builder::resolve_importable_module_in_package(
                                    dp, false, m,
                                )
                                .is_some()
                            })
                            || crate::lake_build::resolve_project_lean_source(
                                &canon_dir, &rel_slash,
                            )
                            .is_some();
                    in_pkg_or_project
                        || !crate::module_builder::is_builtin_toolchain_module(
                            &cfg.toolchain_lib_lean,
                            Some(&cfg.lean_githash),
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

    if !shards_by_file.is_empty() {
        let shard_target_files: Vec<PathBuf> = shards_by_file
            .keys()
            .map(|rel_path| canon_dir.join(rel_path))
            .collect();
        if let Some(ov) = crate::lake_build::build_imported_standalone_modules_overlay(
            store,
            &canon_dir,
            &shard_target_files,
            is_untrusted,
            &trust_domain,
            json,
            Some(&base),
        )? {
            if !verification_trust
                .extra_ro_olean_dirs
                .contains(&ov.olean_dir)
            {
                verification_trust
                    .extra_ro_olean_dirs
                    .push(ov.olean_dir.clone());
            }
            standalone_overlays.push(ov);
        }
    }

    // Per-shard names and canonical kernel types must be attested by Lean before
    // cache hits or verification can be attributed to them.
    let attest_t0 = Instant::now();
    let mut all_edited_keys = Vec::new();
    let mut attested_shards_by_file = Vec::with_capacity(shards_by_file.len());
    for (rel_path, file_shards) in shards_by_file {
        let src = current_files
            .get(&rel_path)
            .context("Missing source for declaration identity confirmation")?;
        let abs_file = canon_dir.join(&rel_path);
        let shard_refs: Vec<&splitter::TheoremShard> =
            file_shards.iter().map(|(_, sh, _)| sh).collect();
        let attested = crate::check::confirm_file_decl_identities_with_extra_dirs(
            src,
            &shard_refs,
            &canon_dir,
            &abs_file,
            is_untrusted,
            &verification_trust.extra_ro_olean_dirs,
            None,
        )?;
        let mut attested_file_shards = Vec::with_capacity(file_shards.len());
        for ((k, shard, fast_ok), att) in file_shards.into_iter().zip(attested) {
            all_edited_keys.push(k.clone());
            all_edited_keys.push(pack::client_attested_receipt_key(&k));
            attested_file_shards.push((k, shard, fast_ok, att.kernel_type_hash));
        }
        attested_shards_by_file.push((rel_path, attested_file_shards));
    }
    let _ = (lake_recheck_ms, attest_t0);

    let cached_set = store.batch_completed_action_keys(&all_edited_keys, &trust_domain)?;
    let mut shard_cache_hits = 0usize;
    let mut shards_verified = 0usize;
    let mut fast_olean_used = false;
    let mut cross_file_coalesced = false;
    let mut batch_to_publish = Vec::new();
    let mut inflight_tx_open = false;

    let file_hygiene_strictly_clean = |rel_path: &str| -> bool {
        current_splits
            .get(rel_path)
            .is_some_and(|sp| sp.hygiene.is_clean_for_certification())
    };
    let mut uncached_by_file = Vec::new();
    let mut raw_uncached_jobs = 0usize;
    for (rel_path, file_shards) in attested_shards_by_file {
        let strictly_clean = file_hygiene_strictly_clean(&rel_path);
        let mut uncached = Vec::new();
        let mut can_fast_olean = !is_untrusted && strictly_clean;
        for (k, sh, fast_ok, kth) in file_shards {
            let client_att_k = pack::client_attested_receipt_key(&k);
            let raw_present = cached_set.contains(&k);
            let client_att_present = cached_set.contains(&client_att_k);
            let raw_attested = strictly_clean
                && raw_present
                && store.has_attested_decl_receipt(&k, &trust_domain, sh.decl_name(), &kth);
            let client_attested = strictly_clean
                && client_att_present
                && store.has_attested_decl_receipt(
                    &client_att_k,
                    &trust_domain,
                    sh.decl_name(),
                    &kth,
                );
            if raw_present && !raw_attested {
                store.invalidate_action_for_reattestation(&k)?;
            }
            if client_att_present && !client_attested {
                store.invalidate_action_for_reattestation(&client_att_k)?;
            }
            if raw_attested || client_attested {
                shard_cache_hits += 1;
            } else {
                if !fast_ok {
                    can_fast_olean = false;
                }
                raw_uncached_jobs += 1;
                uncached.push((k, sh, kth));
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
        anyhow::bail!(
            "PR verification cone budget exceeded (fail-closed): {} uncached theorem shards exceed --max-cone-jobs {} (refusing to truncate unverified shards)",
            raw_uncached_jobs,
            effective_job_cap
        );
    }

    // Keep source interfaces and verification jobs intact. Only the report/gate uses
    // built kernel statements, so an equal digest can never bypass stock checking.
    let statement_digest_t0 = Instant::now();
    let proof_only_rel_files: Vec<String> = classification
        .modified_files
        .iter()
        .filter(|f| !classification.altered_interface_files.contains(f))
        .cloned()
        .collect();
    classification.statement_edited_theorems = kernel_statement_changes_with_trust(
        store,
        &canon_dir,
        &base,
        scope.as_deref(),
        untrusted_pr_cfg.as_ref(),
        &proof_only_rel_files,
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
        && (classification.interface_drift
            || source_statement_edit
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
        let proof_only_rel_set: std::collections::HashSet<&str> =
            proof_only_rel_files.iter().map(String::as_str).collect();
        let proof_only_base_blobs: std::collections::HashMap<String, String> =
            if !is_untrusted && !proof_only_rel_files.is_empty() {
                resolve_git_toplevel(&canon_dir)
                    .ok()
                    .and_then(|repo_root| {
                        let proj_rel = canon_dir.strip_prefix(&repo_root).ok()?;
                        let proj_prefix = proj_rel.to_string_lossy().replace('\\', "/");
                        let mut repo_rels = Vec::with_capacity(proof_only_rel_files.len());
                        let mut repo_to_proj =
                            std::collections::HashMap::with_capacity(proof_only_rel_files.len());
                        for pf in &proof_only_rel_files {
                            let rr = join_proj_prefix(&proj_prefix, pf);
                            repo_to_proj.insert(rr.clone(), pf.clone());
                            repo_rels.push(rr);
                        }
                        let blobs = fetch_git_blobs_batch(&repo_root, &base, &repo_rels).ok()?;
                        let mut out = std::collections::HashMap::with_capacity(blobs.len());
                        for (rr, src) in blobs {
                            if let Some(pf) = repo_to_proj.remove(&rr) {
                                out.insert(pf, src);
                            }
                        }
                        Some(out)
                    })
                    .unwrap_or_default()
            } else {
                std::collections::HashMap::new()
            };
        let has_stmt_edit_in_file = |rel_path: &str| {
            classification
                .statement_edited_theorems
                .iter()
                .any(|kname| {
                    kname
                        .split_once("::")
                        .is_some_and(|(kfile, _)| kfile == rel_path)
                })
        };
        let resolve_fast_olean_mod_imp = |st: &TurboStore,
                                          rel_path: &str,
                                          abs_f: &Path|
         -> Option<String> {
            resolve_replayed_prebuilt_module_import(st, &canon_dir, abs_f).or_else(|| {
                if !is_untrusted
                    && proof_only_rel_set.contains(rel_path)
                    && !has_stmt_edit_in_file(rel_path)
                {
                    let head_or_base = current_files
                        .get(rel_path)
                        .and_then(|h_src| {
                            resolve_replayed_proof_only_module_import(st, &canon_dir, abs_f, h_src)
                        })
                        .or_else(|| {
                            proof_only_base_blobs.get(rel_path).and_then(|b_src| {
                                resolve_replayed_proof_only_module_import(
                                    st, &canon_dir, abs_f, b_src,
                                )
                            })
                        });
                    head_or_base
                } else {
                    None
                }
            })
        };
        let prepend_standalone_dirs = |lp: String, dirs: &[PathBuf]| -> String {
            if dirs.is_empty() {
                return lp;
            }
            let prefix = dirs
                .iter()
                .map(|d| d.to_string_lossy().to_string())
                .collect::<Vec<_>>()
                .join(":");
            if lp.is_empty() {
                prefix
            } else {
                format!("{}:{}", prefix, lp)
            }
        };
        let fast_lib_dir = canon_dir.join(".lake/build/lib/lean");
        let fast_local_zygote_url = if !is_untrusted && remote_http.is_none() {
            let mut fast_ev = std::collections::HashMap::new();
            if fast_lib_dir.exists() || !verification_trust.extra_ro_olean_dirs.is_empty() {
                let lp = prepend_standalone_dirs(
                    resolve_remote_lean_path(&canon_dir, None),
                    &verification_trust.extra_ro_olean_dirs,
                );
                fast_ev.insert("LEAN_PATH".to_string(), lp);
            }
            pack::ensure_local_zygote_daemon(store, &fast_ev)
        } else {
            None
        };
        let (mut env_vars, lean_bin, lean_path_str) = if let Some(ref cfg) = untrusted_pr_cfg {
            let (base_lp, ldp) = crate::module_builder::build_lean_search_path(cfg, true);
            let lp = prepend_standalone_dirs(base_lp, &verification_trust.extra_ro_olean_dirs);
            let mut ev = std::collections::HashMap::new();
            if !lp.is_empty() {
                ev.insert("LEAN_PATH".to_string(), lp.clone());
            }
            if !ldp.is_empty() {
                ev.insert("LD_LIBRARY_PATH".to_string(), ldp);
            }
            (ev, cfg.lean_bin.to_string_lossy().to_string(), lp)
        } else if fast_local_zygote_url.is_some() && fast_lib_dir.exists() {
            let lp = prepend_standalone_dirs(
                resolve_remote_lean_path(&canon_dir, None),
                &verification_trust.extra_ro_olean_dirs,
            );
            let mut fast_ev = std::collections::HashMap::new();
            fast_ev.insert("LEAN_PATH".to_string(), lp.clone());
            (fast_ev, resolve_lean_bin(&canon_dir)?, lp)
        } else {
            let (mut ev, _) = resolve_lake_env(store, &canon_dir)?;
            let lb = resolve_lean_bin(&canon_dir)?;
            let lp = prepend_standalone_dirs(
                resolve_remote_lean_path(&canon_dir, Some(&ev)),
                &verification_trust.extra_ro_olean_dirs,
            );
            if !verification_trust.extra_ro_olean_dirs.is_empty() {
                ev.insert("LEAN_PATH".to_string(), lp.clone());
            }
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
                    .map(|(_, sh, _)| sh.rooted_name())
                    .collect();
                if let Some(mod_imp) = resolve_fast_olean_mod_imp(store, rel_path, &abs_file) {
                    let fast_ok =
                        !splitter::source_has_attribute_command_for_uncached(src, &uncached_names)
                            && if let Some(sp) = current_splits.get(rel_path) {
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

        let _shard_pub_guard = crate::db::acquire_cas_publication_guard(&store.root)?;
        let mut cross_batch_done = false;
        let cross_names_all: Vec<String> = uncached_by_file
            .iter()
            .flat_map(|(_, fu, _)| fu.iter().map(|(_, sh, _)| sh.decl_name().to_string()))
            .collect();
        let cross_unique_names: std::collections::HashSet<&str> =
            cross_names_all.iter().map(|s| s.as_str()).collect();
        if uncached_by_file.len() > 1
            && cross_eligible.len() == uncached_by_file.len()
            && cross_unique_names.len() == cross_names_all.len()
        {
            let cross_args = cross_shared_args.unwrap_or_default();
            let total_uncached: usize = uncached_by_file.iter().map(|(_, u, _)| u.len()).sum();
            let shard_ref_vecs: Vec<Vec<&splitter::TheoremShard>> = cross_eligible
                .iter()
                .map(|(_, _, fu)| fu.iter().map(|(_, sh, _)| sh).collect())
                .collect();
            let cross_inputs: Vec<(&str, &str, &[&splitter::TheoremShard])> = cross_eligible
                .iter()
                .enumerate()
                .map(|(i, (m, s, _))| (m.as_str(), *s, shard_ref_vecs[i].as_slice()))
                .collect();
            let cross_src = splitter::build_cross_file_coalesced_shard(&cross_inputs);
            let cross_expected_types: Vec<(String, String)> = uncached_by_file
                .iter()
                .flat_map(|(_, fu, _)| {
                    fu.iter()
                        .map(|(_, sh, kth)| (sh.decl_name().to_string(), kth.clone()))
                })
                .collect();
            if classification.axiom_flags.is_empty()
                && uncached_by_file
                    .iter()
                    .all(|(rp, _, _)| file_hygiene_strictly_clean(rp))
            {
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
            }

            if !cross_batch_done {
                let cross_t0 = Instant::now();
                let zreq = make_batch_zreq(
                    format!("pr_verify_cross_{}", pid),
                    cross_src.clone(),
                    &toolchain,
                    &lean_path_str,
                    cross_args.clone(),
                    uncached_by_file
                        .iter()
                        .flat_map(|(_, fu, _)| fu.iter().map(|(_, sh, _)| sh.rooted_name()))
                        .collect(),
                );
                let cross_res = if let Some(ref z_url) = fast_local_zygote_url {
                    pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
                        z_url,
                        &zreq,
                        || {
                            let now = crate::db::now_unix();
                            batch_to_publish.reserve(total_uncached);
                            for (_rel_path, file_uncached, _) in &uncached_by_file {
                                for (k, sh, kth) in file_uncached {
                                    if let Ok(r_bytes) = serialize_shard_receipt_bytes(sh, kth, now)
                                    {
                                        batch_to_publish.push((
                                            k.clone(),
                                            sh.decl_name().to_string(),
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
                let cross_res = match cross_res {
                    Ok(Some(reply)) => {
                        verify_zygote_reply_decl_types(&reply, &cross_expected_types)
                            .map(|()| Some(reply))
                    }
                    other => other,
                };
                let mut cross_ok = matches!(cross_res, Ok(Some(_)));
                if !cross_ok {
                    if inflight_tx_open {
                        store.rollback_inflight_publish();
                        inflight_tx_open = false;
                    }
                    batch_to_publish.clear();
                    if matches!(cross_res, Ok(None)) {
                        if !is_untrusted && env_vars.is_empty() {
                            if let Ok((ev, _)) = resolve_lake_env(store, &canon_dir) {
                                env_vars = ev;
                            }
                        }
                        let lb = if env_vars.is_empty() {
                            lean_bin.clone()
                        } else {
                            resolve_lean_bin(&canon_dir)?
                        };
                        let cross_names: std::collections::HashSet<String> = uncached_by_file
                            .iter()
                            .flat_map(|(_, fu, _)| fu.iter().map(|(_, sh, _)| sh.rooted_name()))
                            .collect();
                        cross_ok = run_lean_temp_file(
                            store,
                            &lb,
                            &cross_src,
                            &canon_dir,
                            &env_vars,
                            &verification_trust,
                            &cross_names,
                            &cross_expected_types,
                            &cross_args,
                        )?
                        .status
                        .success();
                    }
                }
                if cross_ok {
                    cross_batch_done = true;
                    cross_file_coalesced = true;
                    fast_olean_used = true;
                    let dur_ms = (cross_t0.elapsed().as_millis() as i64
                        / (total_uncached as i64).max(1))
                    .max(1);
                    let flat_shards: Vec<(String, splitter::TheoremShard, String)> =
                        uncached_by_file
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
            let mut remaining_local = Vec::new();
            if let Some(ref remote_url) = remote_http {
                for (rel_path, file_uncached, can_fast_olean) in uncached_by_file {
                    if !classification.axiom_flags.is_empty()
                        || !file_hygiene_strictly_clean(&rel_path)
                    {
                        remaining_local.push((rel_path, file_uncached, false));
                        continue;
                    }
                    let src = current_files.get(&rel_path).cloned().unwrap_or_default();
                    let abs_file = canon_dir.join(&rel_path);
                    let canon_lf = abs_file.canonicalize().unwrap_or(abs_file);
                    let file_lean_args = resolve_file_args(&canon_lf);
                    let uncached_names: std::collections::HashSet<String> = file_uncached
                        .iter()
                        .map(|(_, sh, _)| sh.rooted_name())
                        .collect();
                    let req_items: Vec<pack::CheckShardBatchItem> =
                        file_uncached.iter().map(to_batch_req_item).collect();

                    let mut remote_ok = false;
                    if can_fast_olean {
                        if let Some(mod_imp) =
                            resolve_fast_olean_mod_imp(store, &rel_path, &canon_lf)
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
                                resp.error.unwrap_or(resp.stderr)
                            );
                        }
                        shard_cache_hits += resp.cache_hits;
                        shards_verified += resp.verified_count;
                    }
                }
            } else {
                remaining_local = uncached_by_file;
            }

            if !remaining_local.is_empty() {
                let uncached_by_file = remaining_local;
                let local_zygote_url = if is_untrusted {
                    None
                } else {
                    fast_local_zygote_url
                        .or_else(|| pack::ensure_local_zygote_daemon(store, &env_vars))
                };
                if !is_untrusted && local_zygote_url.is_none() && env_vars.is_empty() {
                    if let Ok((mut ev, _)) = resolve_lake_env(store, &canon_dir) {
                        if !verification_trust.extra_ro_olean_dirs.is_empty() {
                            let lp = prepend_standalone_dirs(
                                resolve_remote_lean_path(&canon_dir, Some(&ev)),
                                &verification_trust.extra_ro_olean_dirs,
                            );
                            ev.insert("LEAN_PATH".to_string(), lp);
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
                        .map(|(_, sh, _)| sh.rooted_name())
                        .collect();
                    let file_expected_types: Vec<(String, String)> = file_uncached
                        .iter()
                        .map(|(_, sh, kth)| (sh.decl_name().to_string(), kth.clone()))
                        .collect();
                    let f_t0 = Instant::now();

                    let mut verified_ok = false;
                    if can_fast_olean {
                        if let Some(mod_imp) =
                            resolve_fast_olean_mod_imp(worker_store, rel_path, &abs_file)
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
                                let mut fast_unavailable = true;
                                if let Some(z_url) = local_zygote_url.as_deref() {
                                    let zreq = make_batch_zreq(
                                        format!("pr_verify_fast_{}_{}", pid, f_idx),
                                        fast_src.clone(),
                                        &toolchain,
                                        &lean_path_str,
                                        file_lean_args.clone(),
                                        uncached_names.iter().cloned().collect(),
                                    );
                                    let fast_res =
                                        pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
                                        z_url,
                                        &zreq,
                                        || {
                                            let now = crate::db::now_unix();
                                            local_publish.reserve(file_uncached.len());
                                            for (k, sh, kth) in file_uncached {
                                                if let Ok(r_bytes) =
                                                    serialize_shard_receipt_bytes(sh, kth, now)
                                                {
                                                    local_publish.push((
                                                        k.clone(),
                                                        sh.decl_name().to_string(),
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
                                    let fast_res = match fast_res {
                                        Ok(Some(reply)) => verify_zygote_reply_decl_types(
                                            &reply,
                                            &file_expected_types,
                                        )
                                        .map(|()| Some(reply)),
                                        other => other,
                                    };
                                    if matches!(fast_res, Ok(Some(_))) {
                                        verified_ok = true;
                                        local_fast_olean = true;
                                        fast_unavailable = false;
                                    } else {
                                        if local_tx_open {
                                            if let Some(st) = inflight_store {
                                                st.rollback_inflight_publish();
                                            }
                                            local_tx_open = false;
                                        }
                                        local_publish.clear();
                                        if fast_res.is_err() {
                                            fast_unavailable = false;
                                        }
                                    }
                                }
                                if !verified_ok
                                    && fast_unavailable
                                    && run_lean_temp_file(
                                        worker_store,
                                        &lean_bin,
                                        &fast_src,
                                        &canon_dir,
                                        &env_vars,
                                        &verification_trust,
                                        &uncached_names,
                                        &file_expected_types,
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

                    let try_zygote_or_cli_batch = |src_to_check: &str,
                                                   zreq_key: String|
                     -> Result<bool> {
                        if let Some(z_url) = local_zygote_url.as_deref() {
                            let zreq = make_batch_zreq(
                                zreq_key,
                                src_to_check.to_string(),
                                &toolchain,
                                &lean_path_str,
                                file_lean_args.clone(),
                                uncached_names.iter().cloned().collect(),
                            );
                            if let Some(reply) =
                                pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
                                    z_url,
                                    &zreq,
                                    || {},
                                )
                                .with_context(|| {
                                    format!("Zygote kernel gate rejected PR shards in {}", rel_path)
                                })?
                            {
                                verify_zygote_reply_decl_types(&reply, &file_expected_types)
                                    .with_context(|| {
                                        format!(
                                            "Zygote kernel gate rejected PR shards in {}",
                                            rel_path
                                        )
                                    })?;
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
                            &file_expected_types,
                            &file_lean_args,
                        )?
                        .status
                        .success())
                    };

                    let strictly_clean_file = file_hygiene_strictly_clean(rel_path);
                    if !verified_ok && (is_untrusted || !strictly_clean_file) {
                        let out = if is_untrusted {
                            run_lean_temp_file(
                                worker_store,
                                &lean_bin,
                                &src,
                                &canon_dir,
                                &env_vars,
                                &verification_trust,
                                &uncached_names,
                                &file_expected_types,
                                &file_lean_args,
                            )?
                        } else {
                            let (out, _) =
                                crate::zygote::run_audited_lean_shard_at_with_types_report(
                                    &worker_store.root,
                                    &worker_store.fast_staging_dir(),
                                    Path::new(&lean_bin),
                                    &env_vars,
                                    Some(&canon_dir),
                                    None,
                                    &src,
                                    &uncached_names,
                                    false,
                                    &file_expected_types,
                                    &file_lean_args,
                                    None,
                                )?;
                            out
                        };
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
                            if let Ok(true) = try_zygote_or_cli_batch(
                                &pruned_src,
                                format!("pr_verify_{}_{}", pid, f_idx),
                            ) {
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
                        if strictly_clean_file {
                            local_verified = finalize_batch_publish_entries(
                                &mut local_publish,
                                file_uncached,
                                dur_ms,
                            )?;
                        } else {
                            local_verified = file_uncached.len();
                        }
                    } else {
                        let now = crate::db::now_unix();
                        for (k, sh, kth) in file_uncached.iter() {
                            let s_t0 = Instant::now();
                            let rooted_target = sh.rooted_name();
                            let single_src: std::borrow::Cow<'_, str> = if sh
                                .shard_source
                                .is_empty()
                            {
                                let reconstructed = splitter::reconstruct_single_shard_source(
                                    &src,
                                    &rooted_target,
                                )?
                                .unwrap_or_else(|| {
                                    let single_set =
                                        std::collections::HashSet::from([rooted_target.clone()]);
                                    splitter::build_coalesced_shard_source(&src, &single_set)
                                });
                                std::borrow::Cow::Owned(reconstructed)
                            } else {
                                std::borrow::Cow::Borrowed(sh.shard_source.as_str())
                            };
                            let single_expected_types = [(sh.decl_name().to_string(), kth.clone())];
                            let mut single_ok = false;
                            if let Some(z_url) = local_zygote_url.as_deref() {
                                let zreq = pack::CheckShardHttpRequest {
                                    decl: sh.decl_name().to_string(),
                                    shard_key: k.clone(),
                                    shard_source: single_src.to_string(),
                                    interface_hash: String::new(),
                                    prefix_env_hash: sh.prefix_env_hash.clone(),
                                    stmt_hash: sh.stmt_hash.clone(),
                                    proof_hash: sh.proof_hash.clone(),
                                    expected_kernel_type_hash: Some(kth.clone()),
                                    toolchain: toolchain.clone(),
                                    lean_path: lean_path_str.clone(),
                                    skip_cas_lock: true,
                                    allowed_axioms: Some(splitter::extra_allowed_axiom_patterns()),
                                    lean_args: file_lean_args.clone(),
                                    targets: vec![rooted_target.clone()],
                                };
                                let single_res =
                                    pack::try_zygote_url_check_shard_inner_with_inflight_detailed(
                                        z_url,
                                        &zreq,
                                        || {
                                            if file_uncached.len() == 1 {
                                                if let Ok(r_bytes) =
                                                    serialize_shard_receipt_bytes(sh, kth, now)
                                                {
                                                    local_publish.push((
                                                        k.clone(),
                                                        sh.decl_name().to_string(),
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
                                let single_res = match single_res {
                                    Ok(Some(reply)) => verify_zygote_reply_decl_types(
                                        &reply,
                                        &single_expected_types,
                                    )
                                    .map(|()| Some(reply)),
                                    other => other,
                                };
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
                                    &std::collections::HashSet::from([rooted_target]),
                                    &single_expected_types,
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
                                let r_bytes = serialize_shard_receipt_bytes(sh, kth, now)?;
                                local_publish.push((
                                    k.clone(),
                                    sh.decl_name().to_string(),
                                    r_bytes,
                                    dur_ms,
                                ));
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
                    let jobs = pr_verify_file_worker_jobs(
                        is_untrusted,
                        default_jobs,
                        uncached_by_file.len(),
                    );
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
        drop(_shard_pub_guard);
    } else if !is_untrusted && remote_http.is_none() && !crate::zygote::daemon_disabled() {
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
        let nanoda_path = crate::trusted_tools::outside_checkout(nanoda_path, &canon_dir)
            .context("--nanoda-bin must be an absolute executable outside the project/checkout")?;
        let mut nanoda_cmd = Command::new(&nanoda_path);
        nanoda_cmd
            .env_clear()
            .env("PATH", "/usr/bin:/bin")
            .arg(&canon_dir)
            .current_dir(&canon_dir);
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

    let mut ver_receipt =
        build_pr_verification_receipt(&mode, &kernel_prov, &base, &classification);
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
    let mut pr_telemetry_json = serde_json::json!({
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
    });
    kernel_prov.insert_json_fields(&mut pr_telemetry_json);
    crate::mcp::emit_cli_telemetry_event(
        Some(&canon_dir),
        !is_untrusted,
        pr_telemetry_json,
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
        kernel_prov.insert_json_fields(&mut out_json);
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
            "[turbo-lean] PR-VERIFY PASSED vs {} (kernel={}, {} unchanged, {} proof-edited, {} stmt-edited, interface_drift={}, fast_olean={}, cross_file={}, {:.2} ms)",
            base,
            kernel_prov.kernel_engine,
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

    /// P0-4: a proof-only edit that imports a stale dependency-package `.olean` is refreshed when
    /// linking is on, and fails closed without touching `.lake` when it is off.
    #[test]
    fn test_trusted_pr_verify_refreshes_stale_dep_import() -> Result<()> {
        use crate::worktree_test_support::snapshot;
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_lean_pr_dep_fresh_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let proj = dir.join("proj");
        let dep = dir.join("dep_pkg");
        fs::create_dir_all(dep.join("DepPkg"))?;
        fs::create_dir_all(proj.join("custom_src/P"))?;
        for d in [&proj, &dep] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        }
        fs::write(
            dep.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepPkg\"\nglobs = [\"DepPkg.+\"]\n",
        )?;
        fs::write(dep.join("DepPkg/Z.lean"), "def z : Nat := 1\n")?;
        fs::write(
            dep.join("DepPkg/A.lean"),
            "import DepPkg.Z\ndef g : Nat := z\n",
        )?;
        fs::write(
            proj.join("lakefile.toml"),
            format!(
                "name = \"p\"\nsrcDir = \"custom_src\"\n[[require]]\nname = \"dep_pkg\"\npath = \"{}\"\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n",
                dep.display()
            ),
        )?;
        let marker = dir.join("build_cmd_ran");
        fs::write(
            proj.join("turbo-lean.toml"),
            format!(
                "[lake]\nbuild_command = [\"sh\", \"-c\", \"touch '{}' && exit 1\", \"sh\"]\n",
                marker.display()
            ),
        )?;
        fs::write(proj.join(".gitignore"), ".lake/\n")?;
        fs::write(proj.join("custom_src/P/Local.lean"), "def k : Nat := 1\n")?;
        let target = "import DepPkg.A\nimport P.Local\ntheorem t : g = k := by\n  rfl\n";
        fs::write(proj.join("custom_src/P/T.lean"), target)?;
        let lake = |args: &[&str]| Command::new("lake").args(args).current_dir(&proj).output();
        let built = lake(&["build", "P.T"])?;
        assert!(
            built.status.success(),
            "lake build P.T failed: {}\n{}",
            String::from_utf8_lossy(&built.stdout),
            String::from_utf8_lossy(&built.stderr)
        );
        git_init_and_commit(&proj, "base")?;
        let dep_manifest = dep.join(".lake/build/.turbo_verified_sources.json");
        let mut store = TurboStore::open(Some(&dir.join("cache")))?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )?;
        assert!(
            dep_manifest.is_file(),
            "dependency manifest was not recorded"
        );
        let good = fs::read(&dep_manifest)?;
        let mut partial: serde_json::Value = serde_json::from_slice(&good)?;
        partial["modules"]["DepPkg/A.lean"]["import_olean_digests"]
            .as_object_mut()
            .unwrap()
            .insert(
                "DepPkg.Z".into(),
                serde_json::json!("not-the-recorded-digest"),
            );
        fs::write(&dep_manifest, serde_json::to_vec(&partial)?)?;
        let local_olean = proj.join(".lake/build/lib/lean/P/Local.olean");
        fs::remove_file(&local_olean)?;
        fs::write(
            proj.join("turbo-lean.toml"),
            format!(
                "[lake]\nbuild_command = [\"sh\", \"-c\", \"touch '{}' && exit 1\", \"sh\"]\n",
                marker.display()
            ),
        )?;
        fs::write(
            proj.join("custom_src/P/T.lean"),
            target.replace("rfl", "exact rfl"),
        )?;
        let pr = |store: &mut TurboStore| {
            run_pr_verify_command(
                store,
                true,
                proj.clone(),
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
        };
        pr(&mut store)?;
        assert!(
            !marker.exists(),
            "executed project [lake] build_command instead of stock Lake"
        );
        assert!(
            local_olean.is_file(),
            "did not build missing custom-srcDir root import"
        );
        let restored: serde_json::Value = serde_json::from_slice(&fs::read(&dep_manifest)?)?;
        assert!(
            restored["modules"].get("DepPkg/A.lean").is_none(),
            "linking-on pr-verify left the stale dependency entry in place: {restored}"
        );
        fs::write(&dep_manifest, &good)?;
        fs::write(
            proj.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        fs::write(
            proj.join("custom_src/P/T.lean"),
            target.replace("rfl", "simpa"),
        )?;
        let mut partial: serde_json::Value = serde_json::from_slice(&good)?;
        partial["modules"]["DepPkg/A.lean"]["import_olean_digests"]
            .as_object_mut()
            .unwrap()
            .insert(
                "DepPkg.Z".into(),
                serde_json::json!("not-the-recorded-digest"),
            );
        fs::write(&dep_manifest, serde_json::to_vec(&partial)?)?;
        let before = snapshot(&proj)?;
        let before_dep = snapshot(&dep)?;
        let err = pr(&mut store).unwrap_err().to_string();
        assert!(
            err.contains("Worktree opt-out prevents refreshing stale imports: DepPkg.A"),
            "{err}"
        );
        assert_eq!(snapshot(&proj)?, before, "opt-out pr-verify mutated .lake");
        assert_eq!(
            snapshot(&dep)?,
            before_dep,
            "opt-out pr-verify mutated dep .lake"
        );
        fs::write(&dep_manifest, &good)?;
        fs::write(
            proj.join("turbo-lean.toml"),
            "[worktree]\nauto_link = true\n",
        )?;
        fs::write(proj.join("custom_src/P/T.lean"), target)?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )?;
        let root_manifest = proj.join(".lake/build/.turbo_verified_sources.json");
        let stale_root_manifest = fs::read(&root_manifest)?;
        fs::write(
            proj.join("lakefile.toml"),
            format!(
                "name = \"p\"\nsrcDir = \"custom_src\"\nleanOptions = {{ autoImplicit = false }}\n[[require]]\nname = \"dep_pkg\"\npath = \"{}\"\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n",
                dep.display()
            ),
        )?;
        git_init_and_commit(&proj, "shift root leanOptions")?;
        fs::write(&root_manifest, &stale_root_manifest)?;
        fs::write(
            proj.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        fs::write(
            proj.join("custom_src/P/T.lean"),
            target.replace("rfl", "exact Eq.refl _"),
        )?;
        let before_root_cfg = snapshot(&proj)?;
        let err_root_cfg = pr(&mut store).unwrap_err().to_string();
        assert!(
            err_root_cfg.contains("Worktree opt-out prevents refreshing stale imports: P.Local"),
            "{err_root_cfg}"
        );
        assert_eq!(
            snapshot(&proj)?,
            before_root_cfg,
            "opt-out pr-verify mutated .lake on root config drift"
        );
        fs::write(
            proj.join("turbo-lean.toml"),
            "[worktree]\nauto_link = true\n",
        )?;
        pr(&mut store)?;
        let post_root: serde_json::Value = serde_json::from_slice(&fs::read(&root_manifest)?)?;
        assert!(
            post_root["modules"]
                .get("custom_src/P/Local.lean")
                .is_none(),
            "linking-on pr-verify left stale-config root entry in place: {post_root}"
        );
        let _ = fs::remove_dir_all(&dir);
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
                "turbo-lean-ci-build-v6\n{}\n{toolchain}\nuntrusted:ci\n{}\n{}:{}\n:kernel:standard:none\n",
                crate::TURBO_LEAN_BUILD_EPOCH,
                cfg.canonical_config_digest,
                crate::zygote::ZYGOTE_SCANNER_VERSION,
                crate::zygote::ZYGOTE_REPLAY_VERSION
            )
            .as_bytes(),
        );
        if crate::module_builder::global_emit_c_enabled() {
            hasher.update(b":emit_c:1\n");
        }
        let cc_tag = crate::module_builder::custom_cc_env_digest_tag();
        if !cc_tag.is_empty() {
            hasher.update(b":cc:");
            hasher.update(cc_tag.as_bytes());
            hasher.update(b"\n");
        }
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
    fn statement_snapshots_preserve_raw_blobs_and_reject_unsafe_entries() -> Result<()> {
        use std::os::unix::{
            ffi::OsStrExt,
            fs::{symlink, PermissionsExt},
        };
        let dir = Path::new("/tmp").join(format!(
            "turbo-raw-tree-{}-{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        fs::create_dir_all(dir.join("dir"))?;
        let raw = b"raw\r\nbytes\0\xff\n";
        let name = std::ffi::OsStr::from_bytes(b"dir/odd\t\n\xff");
        fs::write(dir.join(name), raw)?;
        fs::write(dir.join("script"), b"#!/bin/sh\nexit 0\n")?;
        fs::set_permissions(dir.join("script"), fs::Permissions::from_mode(0o755))?;
        symlink(name, dir.join("link"))?;
        git_init_and_commit(&dir, "raw tree")?;
        let snapshot = StatementSnapshot::at(&dir, "HEAD")?;
        assert_eq!(fs::read(snapshot.path.join(name))?, raw);
        assert_eq!(fs::read(snapshot.path.join("link"))?, raw);
        assert_eq!(
            fs::metadata(snapshot.path.join("script"))?
                .permissions()
                .mode()
                & 0o777,
            0o755
        );
        assert_eq!(
            fs::metadata(snapshot.path.join(name))?.permissions().mode() & 0o777,
            0o644
        );
        assert!(!snapshot.path.join(".git").exists());
        let path = snapshot.path.clone();
        drop(snapshot);
        assert!(!path.exists());
        for target in ["../../etc/passwd", "/etc/passwd", "missing"] {
            fs::remove_file(dir.join("link"))?;
            symlink(target, dir.join("link"))?;
            git_init_and_commit(&dir, "unsafe link")?;
            assert!(StatementSnapshot::at(&dir, "HEAD").is_err(), "{target}");
        }
        let oid = crate::trusted_tools::git(&dir)?
            .arg("-C")
            .arg(&dir)
            .args(["rev-parse", "HEAD"])
            .output()?;
        let oid = std::str::from_utf8(&oid.stdout)?.trim();
        let out = Command::new("/usr/bin/git")
            .arg("-C")
            .arg(&dir)
            .args([
                "update-index",
                "--add",
                "--cacheinfo",
                &format!("160000,{oid},submodule"),
            ])
            .output()?;
        assert!(out.status.success());
        let tree = Command::new("/usr/bin/git")
            .arg("-C")
            .arg(&dir)
            .arg("write-tree")
            .output()?;
        assert!(tree.status.success());
        let error = StatementSnapshot::at(&dir, std::str::from_utf8(&tree.stdout)?.trim())
            .err()
            .unwrap();
        assert!(
            error.to_string().contains("submodule gitlinks: submodule"),
            "{error}"
        );
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn seed_statement_dependencies_omits_non_lean_broken_symlinks_and_fails_closed_on_build_paths(
    ) -> Result<()> {
        use std::os::unix::fs::symlink;
        let dir = Path::new("/tmp").join(format!(
            "turbo-dep-symlinks-{}-{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let root_proj = dir.join("root");
        let dep_repo = root_proj.join(".lake/packages/fv");
        fs::create_dir_all(dep_repo.join("FV"))?;
        fs::create_dir_all(dep_repo.join("corpus/dsl/Corpus"))?;
        fs::create_dir_all(dep_repo.join("docs"))?;
        fs::write(
            root_proj.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            root_proj.join("lakefile.toml"),
            "name = \"root_pkg\"\ndefaultTargets = [\"Root\"]\n[[lean_lib]]\nname = \"Root\"\n",
        )?;
        fs::write(
            root_proj.join("Root.lean"),
            "import FV.Basic\ntheorem ok : FV.val = 1 := rfl\n",
        )?;
        fs::write(
            root_proj.join("lake-manifest.json"),
            r#"{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [
    { "type": "git", "name": "fv", "rev": "HEAD", "url": "https://example.invalid/fv.git", "inherited": false }
  ],
  "name": "root_pkg",
  "lakeDir": ".lake",
  "fixedToolchain": false
}"#,
        )?;
        fs::write(
            dep_repo.join("lakefile.toml"),
            r#"name = "fv"
defaultTargets = ["FV"]
[[lean_lib]]
name = "FV"
globs = ["FV.+"]
[[lean_lib]]
name = "Corpus"
srcDir = "corpus/dsl"
globs = ["Corpus.+"]
"#,
        )?;
        fs::write(
            dep_repo.join("FV/Basic.lean"),
            "namespace FV\ndef val : Nat := 1\nend FV\n",
        )?;
        fs::write(
            dep_repo.join("corpus/dsl/Corpus/Spec.lean"),
            "namespace Corpus\ndef c : Nat := 2\nend Corpus\n",
        )?;
        fs::write(dep_repo.join("docs/real.txt"), "kept\n")?;
        symlink(
            "/nonexistent/upstream-worktree/lnsym-upstream",
            dep_repo.join("lnsym-upstream"),
        )?;
        symlink("../../../etc/passwd", dep_repo.join("docs/escape-link"))?;
        symlink("nonexistent-target", dep_repo.join("docs/dangling-link"))?;
        symlink("dangling-link", dep_repo.join("docs/chained-dangling"))?;
        symlink("real.txt", dep_repo.join("docs/valid-link"))?;
        git_init_and_commit(&dep_repo, "dep with non-lean broken symlinks")?;

        let cfg = crate::module_builder::resolve_project_config_with_trust(&root_proj, true)?;
        let snap = dir.join("snap-ok");
        fs::create_dir_all(&snap)?;
        seed_statement_dependencies(&snap, &cfg)?;
        let seeded = snap.join(".lake/packages/fv");
        assert!(seeded.join("FV/Basic.lean").is_file());
        assert_eq!(
            fs::read_to_string(seeded.join("docs/valid-link"))?,
            "kept\n"
        );
        for bad in [
            "lnsym-upstream",
            "docs/escape-link",
            "docs/dangling-link",
            "docs/chained-dangling",
        ] {
            assert!(
                fs::symlink_metadata(seeded.join(bad)).is_err(),
                "unsafe non-build symlink `{bad}` must not exist on disk"
            );
        }

        for (bad_rel, bad_target) in [
            ("FV/Bad.lean", "/etc/passwd"),
            ("FV/Sub", "../../../etc"),
            ("corpus/dsl/Corpus/Bad", "missing"),
            ("lakefile.lean", "/etc/passwd"),
            ("lean-toolchain", "missing"),
        ] {
            let full = dep_repo.join(bad_rel);
            if let Some(p) = full.parent() {
                fs::create_dir_all(p)?;
            }
            symlink(bad_target, &full)?;
            git_init_and_commit(&dep_repo, &format!("bad symlink {bad_rel}"))?;
            let snap_bad = dir.join(format!("snap-bad-{}", pack::next_tmp_id()));
            fs::create_dir_all(&snap_bad)?;
            assert!(
                seed_statement_dependencies(&snap_bad, &cfg).is_err(),
                "dependency symlink at `{bad_rel}` -> `{bad_target}` must fail closed"
            );
            fs::remove_file(&full)?;
            git_init_and_commit(&dep_repo, &format!("cleanup {bad_rel}"))?;
        }
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn untrusted_kernel_statements_materialize_removed_base_manifest_git_dependencies() -> Result<()>
    {
        use std::os::unix::fs::symlink;
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        if crate::module_builder::probe_bwrap_sandbox(Path::new(".")).is_none() {
            println!("untrusted removed base dependency fixture skipped: no working bubblewrap");
            return Ok(());
        }
        let dir = Path::new("/tmp").join(format!(
            "turbo-removed-base-dep-{}-{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        struct DirGuard(PathBuf);
        impl Drop for DirGuard {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let _guard = DirGuard(dir.clone());

        let upstream_fv = dir.join("upstream-fv");
        fs::create_dir_all(upstream_fv.join("FV"))?;
        fs::create_dir_all(upstream_fv.join("docs"))?;
        fs::write(
            upstream_fv.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            upstream_fv.join("lakefile.toml"),
            r#"name = "fv"
defaultTargets = ["FV"]
[[lean_lib]]
name = "FV"
globs = ["FV.+"]
"#,
        )?;
        fs::write(
            upstream_fv.join("FV/Basic.lean"),
            "namespace FV\ndef val : Nat := 1\nend FV\n",
        )?;
        fs::write(upstream_fv.join("docs/real.txt"), "kept\n")?;
        symlink(
            "/nonexistent/upstream-worktree/lnsym-upstream",
            upstream_fv.join("lnsym-upstream"),
        )?;
        symlink("nonexistent-target", upstream_fv.join("docs/dangling-link"))?;
        symlink("../../../etc/passwd", upstream_fv.join("docs/escape-link"))?;
        git_init_and_commit(&upstream_fv, "fv release with non-build broken symlinks")?;
        let fv_rev_out = crate::trusted_tools::git(&upstream_fv)?
            .arg("-C")
            .arg(&upstream_fv)
            .args(["rev-parse", "HEAD"])
            .output()?;
        assert!(fv_rev_out.status.success());
        let fv_rev = std::str::from_utf8(&fv_rev_out.stdout)?.trim().to_string();
        let fv_url = format!("file://{}", upstream_fv.canonicalize()?.display());

        let repo = dir.join("repo");
        let proj = repo.join("lean");
        fs::create_dir_all(proj.join("Demo"))?;
        fs::write(repo.join(".gitignore"), "lean/.lake/\n")?;
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            proj.join("lakefile.lean"),
            format!(
                r#"import Lake
open Lake DSL

package «demo-pkg»

require fv from git
  "{fv_url}" @ "{fv_rev}"

@[default_target]
lean_lib Demo where
  globs := #[.submodules `Demo]
"#
            ),
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            format!(
                r#"{{
  "version": "1.3.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {{
      "url": "{fv_url}",
      "type": "git",
      "subDir": null,
      "scope": "",
      "rev": "{fv_rev}",
      "name": "fv",
      "manifestFile": "lake-manifest.json",
      "inputRev": "{fv_rev}",
      "inherited": false,
      "configFile": "lakefile.toml"
    }}
  ],
  "name": "«demo-pkg»",
  "lakeDir": ".lake",
  "fixedToolchain": false
}}"#
            ),
        )?;
        fs::write(
            proj.join("Demo/Keep.lean"),
            "theorem keep : (1 : Nat) = 1 := rfl\n",
        )?;
        fs::write(
            proj.join("Demo/OldFv.lean"),
            "import FV.Basic\ntheorem old_fv : FV.val = 1 := rfl\n",
        )?;
        git_init_and_commit(&repo, "base with fv dependency")?;
        let base_rev_out = crate::trusted_tools::git(&repo)?
            .arg("-C")
            .arg(&repo)
            .args(["rev-parse", "HEAD"])
            .output()?;
        assert!(base_rev_out.status.success());
        let base_rev = std::str::from_utf8(&base_rev_out.stdout)?
            .trim()
            .to_string();

        fs::remove_file(proj.join("Demo/OldFv.lean"))?;
        fs::write(
            proj.join("lakefile.lean"),
            r#"import Lake
open Lake DSL

package «demo-pkg»

@[default_target]
lean_lib Demo where
  globs := #[.submodules `Demo]
"#,
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            r#"{
  "version": "1.3.0",
  "packagesDir": ".lake/packages",
  "packages": [],
  "name": "«demo-pkg»",
  "lakeDir": ".lake",
  "fixedToolchain": false
}"#,
        )?;
        git_commit_all(&repo, "remove fv dependency in HEAD")?;
        assert!(!proj.join(".lake/packages/fv").exists());

        let head_cfg = crate::module_builder::resolve_project_config_with_trust(&proj, true)?;
        assert!(head_cfg.dep_pkgs.is_empty());
        let store = TurboStore::open(Some(&dir.join("store")))?;
        let changed = kernel_statement_changes_with_trust(
            &store,
            &proj,
            &base_rev,
            None,
            Some(&head_cfg),
            &[],
        )?;
        assert_eq!(changed, vec!["Demo/OldFv.lean::old_fv (deleted)"]);
        Ok(())
    }

    #[test]
    fn non_lean_gitlink_allowed_and_lean_overlapping_gitlink_rejected() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo-gitlink-filter-{}-{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let proj = dir.join("repo");
        let sub_src = dir.join("forge-std-upstream");
        fs::create_dir_all(proj.join("Demo"))?;
        fs::create_dir_all(&sub_src)?;
        fs::write(sub_src.join("Std.sol"), "// solidity helper\n")?;
        git_init_and_commit(&sub_src, "init forge-std")?;
        let sub_sha = String::from_utf8(
            Command::new("git")
                .current_dir(&sub_src)
                .args(["rev-parse", "HEAD"])
                .output()?
                .stdout,
        )?
        .trim()
        .to_string();

        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            proj.join("lakefile.toml"),
            r#"name = "gitlink-demo"
defaultTargets = ["Demo"]
[[lean_lib]]
name = "Demo"
globs = ["Demo.+"]
"#,
        )?;
        fs::write(
            proj.join("Demo/Basic.lean"),
            "namespace Demo\ntheorem ok : 1 + 1 = 2 := rfl\nend Demo\n",
        )?;
        git_init_and_commit(&proj, "baseline")?;
        let add_gitlink = |repo: &Path, gitlink_rel: &str| -> Result<()> {
            let status = Command::new("git")
                .current_dir(repo)
                .args([
                    "update-index",
                    "--add",
                    "--cacheinfo",
                    &format!("160000,{sub_sha},{gitlink_rel}"),
                ])
                .status()?;
            anyhow::ensure!(status.success(), "git update-index failed");
            Ok(())
        };

        // 1. Non-Lean Foundry submodule (`lib/forge-std`) at both base and HEAD is ignored cleanly.
        add_gitlink(&proj, "lib/forge-std")?;
        let st = Command::new("git")
            .current_dir(&proj)
            .args([
                "commit",
                "-q",
                "--no-gpg-sign",
                "-m",
                "add non-lean submodule",
            ])
            .status()?;
        assert!(st.success());

        let pkg = crate::module_builder::resolve_package_config(&proj, true)?;
        assert!(!package_gitlink_touches_lean(
            Path::new("lib/forge-std"),
            &pkg
        ));
        assert!(package_gitlink_touches_lean(Path::new("Demo/Sub"), &pkg));
        assert!(package_gitlink_touches_lean(
            Path::new(".lake/packages/foo"),
            &pkg
        ));

        let snap = StatementSnapshot::at_scoped(&proj, "HEAD", Path::new(""), Some(&pkg))?;
        assert!(snap.path.join("Demo/Basic.lean").is_file());
        assert!(!snap.path.join("lib/forge-std").exists());
        drop(snap);

        // Without a resolved static PackageConfig, StatementSnapshot fails closed on any gitlink.
        let err_no_pkg = StatementSnapshot::at_scoped(&proj, "HEAD", Path::new(""), None)
            .err()
            .expect("must fail closed without PackageConfig")
            .to_string();
        assert!(err_no_pkg.contains("submodule gitlink"), "{err_no_pkg}");

        fs::write(
            proj.join("Demo/Basic.lean"),
            "namespace Demo\ntheorem ok : 1 + 1 = 2 := by decide\nend Demo\n",
        )?;
        let mut store = TurboStore::open(Some(&proj.join(".lake/test-cache")))?;
        run_pr_verify_command(
            &mut store,
            true,
            proj.clone(),
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
        )?;

        // 2. Gitlink overlapping a Lean library path (`Demo/Submod`) fails closed immediately.
        add_gitlink(&proj, "Demo/Submod")?;
        let err_lean_gitlink = run_pr_verify_command(
            &mut store,
            true,
            proj.clone(),
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
        .unwrap_err()
        .to_string();
        assert!(
            err_lean_gitlink.contains("gitlink") || err_lean_gitlink.contains("Demo/Submod"),
            "{err_lean_gitlink}"
        );

        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn kernel_statement_fixtures() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
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
            &mut store,
            true,
            dir.clone(),
            "HEAD".into(),
            "trusted".into(),
            true,
            None,
            None,
            None,
            None,
            false,
            0,
            None,
        )
        .unwrap_err()
        .to_string();
        assert!(
            error.contains("statement/interface change gate FAILED")
                && error.contains("interface_drift=true"),
            "{error}"
        );
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
            "turbo-statement-naturals-{}-{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(dir.join("lakefile.toml"),
            "name = \"natural-fixture\"\ndefaultTargets = [\"Demo\"]\n[[lean_lib]]\nname = \"Demo\"\n")?;
        for (old, new) in [
            ("1180591620717411303424", "1180591620717411303425"),
            (
                "10000000000000000000000000000000000000000000000000000000000000000000000000000",
                "10000000000000000000000000000000000000000000000000000000000000000000000000001",
            ),
        ] {
            let source = |n: &str| {
                format!(
                "def large : Nat := {n}\ntheorem pinned : ({n} : Nat) = {n} := rfl\ntheorem indirect : large = large := rfl\n")
            };
            fs::write(dir.join("Demo.lean"), source(old))?;
            stock_statement_build(&dir)?;
            let before = built_kernel_statements(&dir, None)?;
            fs::write(dir.join("Demo.lean"), source(new))?;
            stock_statement_build(&dir)?;
            assert_eq!(
                compare_kernel_statements(&before, &built_kernel_statements(&dir, None)?),
                vec!["Demo.lean::indirect", "Demo.lean::pinned"]
            );
        }
        // The parser must also preserve payloads larger than f64's maximum.
        let huge = "9".repeat(400);
        let row = format!("{{\"statement\":[\"nat\",{huge}],\"theorem\":\"t\",\"deps\":[]}}\n{{\"module\":\"Demo\",\"complete\":true}}\n");
        assert_ne!(
            parse_kernel_statement_dump(row.as_bytes(), "Demo")?,
            parse_kernel_statement_dump(
                row.replace(&huge, &(huge.clone() + "1")).as_bytes(),
                "Demo"
            )?
        );
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn project_lean_executable_cannot_replay_statement_dumps() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo-statement-spoof-{}-{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            r#"name = "spoof-fixture"
defaultTargets = ["Demo", "lean"]
[[lean_lib]]
name = "Demo"
[[lean_exe]]
name = "lean"
root = "Spoof"
"#,
        )?;
        let theorem = "theorem pinned : (1 : Nat) = 1 := rfl\n";
        fs::write(dir.join("Demo.lean"), theorem)?;
        fs::write(
            dir.join("Outside.lean"),
            theorem.replace("pinned", "outside"),
        )?;
        fs::write(dir.join("Spoof.lean"), "def main : IO Unit := pure ()\n")?;
        stock_statement_build(&dir)?;
        let before = built_kernel_statements(&dir, None)?;
        // Capture an actual old dump, then make the default project `lean` replay it.
        let helper = dir.join("Dump.lean");
        fs::write(
            &helper,
            format!(
                "{}\ndef main := statementHashCliMain\n",
                include_str!("../../../lean/TurboLean/StatementHash.lean")
            ),
        )?;
        let stale = statement_lean_command(&dir, false)?
            .arg("--run")
            .arg(&helper)
            .args(["Demo", "Outside", "Spoof"])
            .output()?;
        assert!(stale.status.success());
        fs::remove_file(helper)?;
        fs::write(
            dir.join("Spoof.lean"),
            format!(
                "def main : IO Unit := IO.print {}\n",
                serde_json::to_string(std::str::from_utf8(&stale.stdout)?)?
            ),
        )?;
        fs::write(dir.join("Demo.lean"), theorem.replace("1", "2"))?;
        fs::write(
            dir.join("Outside.lean"),
            theorem.replace("pinned", "outside").replace("1", "2"),
        )?;
        stock_statement_build(&dir)?;
        // Confirm that the vulnerable invocation really does replay the old JSONL.
        let replay = statement_lake_command(&dir, false)?
            .args(["env", "lean", "--run", "unused.lean", "Demo"])
            .output()?;
        assert!(replay.status.success());
        assert_eq!(replay.stdout, stale.stdout);
        assert_eq!(
            compare_kernel_statements(&before, &built_kernel_statements(&dir, None)?),
            vec!["Demo.lean::pinned", "Outside.lean::outside"]
        );
        fs::write(
            dir.join("Outside.lean"),
            "theorem outside : False := by trivial\n",
        )?;
        assert!(
            stock_statement_build(&dir).is_err(),
            "the project lean executable must not bypass standalone stock compilation"
        );
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn kernel_policy_is_resolved_at_base_and_never_admits_forbidden_axioms() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo-kernel-policy-{}-{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        let Some(git_bin) = crate::trusted_tools::discover_or_skip_trusted_git_for_test(&dir)?
        else {
            let _ = fs::remove_dir_all(&dir);
            return Ok(());
        };
        if std::env::var_os("TURBO_LEAN_GIT").is_none() {
            std::env::set_var("TURBO_LEAN_GIT", &git_bin);
        }
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
        if crate::module_builder::probe_bwrap_sandbox(std::path::Path::new(".")).is_some() {
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
        let mut report = built_kernel_statement_report(&dir, None, false, None, None)?;
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
                .current_dir(&dir)
                .args(["--audit-modules", "Fixture"])
                .envs(&env)
                .env("LEAN_PATH", &lp)
                .env("TURBO_LEAN_LEAN_BIN", &cfg.lean_bin)
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
            let diagnostic = format!(
                "{}{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
            assert!(!out.status.success()
                && diagnostic.contains("restrictive default policy")
                && diagnostic.contains("native_decide"),
                "{mode} ci-verify without --base must reject checkout/inherited allowlists and explain defaults: {diagnostic}");
            println!(
                "kernel policy {mode} ci-verify: checkout/inherited config ignored without --base"
            );
            Ok(())
        };
        if cli.is_some() {
            verify_default_policy("trusted")?;
            let sandbox =
                crate::module_builder::probe_bwrap_sandbox(std::path::Path::new(".")).is_some();
            for (command, mode) in [
                ("pr-verify", "trusted"),
                ("pr-verify", "untrusted"),
                ("ci-verify", "trusted"),
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
            unsafe_decls: vec!["*".into()],
            implemented_by: vec!["*".into()],
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
        crate::zygote::purge_snapshot_dir(&dir);
        Ok(())
    }

    #[test]
    fn unsafe_and_implemented_by_policy_and_replay_isolation() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!("turbo_unsafe_policy_{}", pack::next_tmp_id()));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(dir.join(".gitignore"), ".lake/\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"unsafe-fixture\"\ndefaultTargets = [\"Fixture\"]\n[[lean_lib]]\nname = \"Fixture\"\n",
        )?;
        fs::write(
            dir.join("Fixture.lean"),
            r#"namespace Fixture
private unsafe def rawHelper (x : Nat) : Nat := x + 1
private opaque safeModel (x : Nat) : Nat := x
@[implemented_by rawHelper]
def publicBridge (x : Nat) : Nat := x
@[implemented_by rawHelper]
private opaque privBridge (x : Nat) : Nat := safeModel x
def safeWrapper (x : Nat) : Nat :=
  unsafe rawHelper (privBridge x)
theorem ok : True := trivial
end Fixture
"#,
        )?;
        let full_config = r#"[unsafe]
allow = [
  "Fixture.rawHelper",
  "Fixture.safeWrapper",
]
[implemented_by]
allow = [
  "Fixture.publicBridge",
  "Fixture.privBridge",
]
"#;
        // Commit 1: empty policy
        fs::write(
            dir.join("turbo-lean.toml"),
            "[unsafe]\nallow = []\n[implemented_by]\nallow = []\n",
        )?;
        git_init_and_commit(&dir, "deny unsafe and implemented_by")?;
        // Commit 2: allow unsafe only (missing implemented_by)
        fs::write(
            dir.join("turbo-lean.toml"),
            "[unsafe]\nallow = [\"Fixture.rawHelper\", \"Fixture.safeWrapper\"]\n[implemented_by]\nallow = []\n",
        )?;
        git_init_and_commit(&dir, "allow unsafe only")?;
        // Commit 3: allow full policy
        fs::write(dir.join("turbo-lean.toml"), full_config)?;
        git_init_and_commit(&dir, "allow unsafe and implemented_by")?;

        stock_statement_build(&dir)?;
        let report = built_kernel_statement_report(&dir, None, false, None, None)?;
        let allowed = StatementPolicy::at(&dir, "HEAD");
        allowed.audit(&report)?;
        assert!(
            StatementPolicy::at(&dir, "HEAD^").audit(&report).is_err(),
            "missing implemented_by allowlist must fail StatementPolicy"
        );
        assert!(
            StatementPolicy::at(&dir, "HEAD^^").audit(&report).is_err(),
            "missing unsafe allowlist must fail StatementPolicy"
        );

        let cli = std::env::current_exe()?
            .parent()
            .and_then(Path::parent)
            .map(|path| path.join("turbo-lean"))
            .filter(|path| path.is_file());
        if let Some(ref cli_bin) = cli {
            let shared_home = dir.join(".lake/turbo-shared-policy-home");
            // 1. Run `turbo-lean build` using checkout `turbo-lean.toml` (permissive policy) populating shared TurboStore.
            let build_out = Command::new(cli_bin)
                .args(["--no-telemetry", "build"])
                .current_dir(&dir)
                .env("TURBO_LEAN_HOME", &shared_home)
                .env("TURBO_LEAN_NO_DAEMON", "1")
                .output()?;
            assert!(
                build_out.status.success(),
                "turbo-lean build under checkout policy must pass: {}\n{}",
                String::from_utf8_lossy(&build_out.stdout),
                String::from_utf8_lossy(&build_out.stderr)
            );
            // 2. Run `ci-verify` WITHOUT `--base` sharing the exact same `TURBO_LEAN_HOME` and `.lake/build`:
            // replay rows recorded under permissive policy MUST NOT bypass strict empty policy!
            let ci_default = Command::new(cli_bin)
                .args(["--no-telemetry", "--json", "ci-verify", "--project-dir"])
                .arg(&dir)
                .env("TURBO_LEAN_HOME", &shared_home)
                .env("TURBO_LEAN_NO_DAEMON", "1")
                // Inherited env vars must also be scrubbed when `--base` is omitted.
                .env("TURBO_LEAN_ALLOWED_UNSAFE", "*")
                .env("TURBO_LEAN_ALLOWED_UNSAFE_FROM_CONFIG", "1")
                .env("TURBO_LEAN_ALLOWED_IMPLEMENTED_BY", "*")
                .env("TURBO_LEAN_ALLOWED_IMPLEMENTED_BY_FROM_CONFIG", "1")
                .output()?;
            assert!(
                !ci_default.status.success(),
                "ci-verify without --base must reject permissive build replay rows: {}\n{}",
                String::from_utf8_lossy(&ci_default.stdout),
                String::from_utf8_lossy(&ci_default.stderr)
            );
            // 3. `ci-verify --base HEAD` must succeed using `--base` policy.
            let ci_base = Command::new(cli_bin)
                .args(["--no-telemetry", "--json", "ci-verify", "--project-dir"])
                .arg(&dir)
                .args(["--base", "HEAD"])
                .env("TURBO_LEAN_HOME", &shared_home)
                .env("TURBO_LEAN_NO_DAEMON", "1")
                .output()?;
            assert!(
                ci_base.status.success(),
                "ci-verify --base HEAD must pass: {}\n{}",
                String::from_utf8_lossy(&ci_base.stdout),
                String::from_utf8_lossy(&ci_base.stderr)
            );
            // 4. `pr-verify --base HEAD^` (missing implemented_by) and `HEAD^^` (missing unsafe) must fail even after `ci-verify --base HEAD` succeeded!
            for stricter_base in ["HEAD^", "HEAD^^"] {
                let pr_strict = Command::new(cli_bin)
                    .args(["--no-telemetry", "--json", "pr-verify", "--project-dir"])
                    .arg(&dir)
                    .args(["--base", stricter_base, "--disallow-statement-changes"])
                    .env("TURBO_LEAN_HOME", &shared_home)
                    .env("TURBO_LEAN_NO_DAEMON", "1")
                    .output()?;
                assert!(
                    !pr_strict.status.success(),
                    "pr-verify --base {stricter_base} must reject permissive replay rows: {}\n{}",
                    String::from_utf8_lossy(&pr_strict.stdout),
                    String::from_utf8_lossy(&pr_strict.stderr)
                );
            }
            // 5. `pr-verify --base HEAD` must pass.
            let pr_ok = Command::new(cli_bin)
                .args(["--no-telemetry", "--json", "pr-verify", "--project-dir"])
                .arg(&dir)
                .args(["--base", "HEAD", "--disallow-statement-changes"])
                .env("TURBO_LEAN_HOME", &shared_home)
                .env("TURBO_LEAN_NO_DAEMON", "1")
                .output()?;
            assert!(
                pr_ok.status.success(),
                "pr-verify --base HEAD must pass: {}\n{}",
                String::from_utf8_lossy(&pr_ok.stdout),
                String::from_utf8_lossy(&pr_ok.stderr)
            );
        }
        crate::zygote::purge_snapshot_dir(&dir);
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
    fn test_shard_subprocess_revalidates_options_before_execution() -> Result<()> {
        use crate::module_builder::option_cases::*;
        let dir = std::env::temp_dir().join(format!(
            "turbo_shard_options_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        let mut cfg = resolve_untrusted_pr_project_config(&dir, "leanprover/lean4:v4.35.0")?;
        let store = TurboStore::open(Some(&dir.join("cache")))?;
        let mut failures = Vec::new();
        for &(name, value) in ORIGINAL_OPTIONS.iter().chain(RESTRICTED_OPTIONS) {
            for prefix in PREFIXES {
                if original_case_allowed(name, value, prefix) {
                    continue;
                }
                let key = format!("{prefix}{name}");
                for field in FIELDS {
                    cfg.root_pkg.more_lean_args.clear();
                    cfg.root_pkg.weak_lean_args.clear();
                    cfg.root_pkg.lean_options.clear();
                    match *field {
                        "moreLeanArgs" => {
                            cfg.root_pkg.more_lean_args.push(format!("-D{key}={value}"))
                        }
                        "weakLeanArgs" => {
                            cfg.root_pkg.weak_lean_args.push(format!("-D{key}={value}"))
                        }
                        _ => {
                            let opt_val = match value {
                                "true" => crate::module_builder::LeanOptionValue::Bool(true),
                                "false" => crate::module_builder::LeanOptionValue::Bool(false),
                                s => s
                                    .parse::<u64>()
                                    .map(crate::module_builder::LeanOptionValue::Nat)
                                    .unwrap_or_else(|_| {
                                        crate::module_builder::LeanOptionValue::Str(s.to_string())
                                    }),
                            };
                            cfg.root_pkg.lean_options.insert(
                                crate::module_builder::LeanName::from_str_to_name(&key)?,
                                opt_val,
                            );
                        }
                    }
                    // Deliberately bypass config parsing: the process boundary must gate too.
                    let args: Vec<_> = cfg
                        .root_pkg
                        .weak_lean_args
                        .iter()
                        .chain(&cfg.root_pkg.more_lean_args)
                        .cloned()
                        .chain(cfg.root_pkg.lean_options.iter().map(|(k, v)| {
                            format!("-D{}={}", k.to_lean_string(), v.raw_cli_value())
                        }))
                        .collect();
                    for is_untrusted in [false, true] {
                        let result = run_lean_temp_file(
                            &store,
                            "must-not-execute",
                            "theorem good : True := True.intro",
                            &dir,
                            &Default::default(),
                            &PrVerificationTrust {
                                is_untrusted,
                                untrusted_cfg: Some(&cfg),
                                extra_ro_olean_dirs: Vec::new(),
                            },
                            &Default::default(),
                            &[],
                            &args,
                        );
                        match result {
                            Err(error) if format!("{error:#}").contains(&key) => {}
                            result => {
                                failures.push(format!("{field}/{is_untrusted}/{key}: {result:?}"))
                            }
                        }
                    }
                }
            }
        }
        fs::remove_dir_all(dir)?;
        assert!(
            failures.is_empty(),
            "shard options were not rejected: {}",
            failures.join("\n")
        );
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
            assert!(Command::new("git")
                .args(args)
                .current_dir(repo_dir)
                .status()?
                .success());
        }
        Ok(())
    }

    fn git_commit_all(repo_dir: &Path, msg: &str) -> Result<()> {
        for args in [
            &["add", "."][..],
            &["commit", "-q", "--no-gpg-sign", "-m", msg],
        ] {
            assert!(Command::new("git")
                .args(args)
                .current_dir(repo_dir)
                .status()?
                .success());
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
        let src_h = crate::module_builder::lake_hash_text(src_raw);
        let z = 0u64;
        let dep_h = crate::module_builder::lake_mix_hash(
            crate::module_builder::lake_mix_hash(
                crate::module_builder::lake_mix_hash(
                    crate::module_builder::lake_mix_hash(crate::module_builder::LAKE_NIL_HASH, z),
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
            "outputs": serde_json::Value::Null
        });
        fs::write(
            olean_path.with_extension("trace"),
            serde_json::to_vec(&trace_json)?,
        )?;
        let art_dig = crate::module_builder::compute_olean_artifact_set_digest(&olean_path)?;
        let manifest_path = proj_dir.join(".lake/build/.turbo_verified_sources.json");
        let ws_inputs_digest = crate::module_builder::workspace_lake_inputs_digest(&cfg)?;
        let mut manifest: crate::module_builder::VerifiedDepManifest = fs::read(&manifest_path)
            .ok()
            .and_then(|b| serde_json::from_slice(&b).ok())
            .unwrap_or_else(|| crate::module_builder::VerifiedDepManifest {
                pkg_name: cfg.root_pkg.name.clone(),
                toolchain: cfg.toolchain.clone(),
                lean_githash: cfg.lean_githash.clone(),
                pkg_config_digest: cfg.root_pkg.config_digest.clone(),
                lake_inputs_digest: ws_inputs_digest.clone(),
                workspace_config_digest: cfg.canonical_config_digest.clone(),
                allowed_axioms: crate::splitter::allowed_axioms(),
                kernel_policy_digest: crate::splitter::current_kernel_policy_digest(),
                modules: BTreeMap::new(),
                ..Default::default()
            });
        // Pin project-local imports to their (already recorded) entries, like a real build.
        let import_olean_digests = crate::module_builder::parse_header_info(src_raw)
            .imports
            .into_iter()
            .filter_map(|imp| {
                let rel_slash = crate::module_builder::module_name_to_rel_slash(&imp);
                let dep_src = crate::lake_build::resolve_project_lean_source(proj_dir, &rel_slash)?;
                let dep_rel = dep_src
                    .strip_prefix(proj_dir)
                    .ok()?
                    .to_string_lossy()
                    .into_owned();
                let dig = manifest
                    .modules
                    .get(&dep_rel)?
                    .olean_artifact_digest
                    .clone();
                Some((imp, dig))
            })
            .collect();
        manifest.modules.insert(
            rel_src.to_string(),
            crate::module_builder::VerifiedDepModuleEntry {
                src_blake3: blake3::hash(src_raw.as_bytes()).to_hex().to_string(),
                olean_artifact_digest: art_dig,
                lake_inputs_digest: ws_inputs_digest,
                kernel_audited: true,
                import_olean_digests,
                artifact_stat_fingerprint: String::new(),
                ..Default::default()
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
        let (pref_only, fast_sp, unchanged_hit, _) =
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

        // Literal whitespace edit inside theorem statement must classify as statement edit + interface drift.
        fs::write(
            canon_dir.join("Demo/B.lean"),
            "namespace Demo\ntheorem t_b : \"a b\" = \"a b\" := by\n  rfl\nend Demo\n",
        )?;
        git_init_and_commit(&repo_dir, "add string theorem")?;
        let (splits2, _) = load_and_split_files_cached(&store, &lean_paths)?;
        warm_git_head_tree_cache(&store, &canon_dir, &lean_paths, tc, Some(&splits2));
        fs::write(
            canon_dir.join("Demo/B.lean"),
            "namespace Demo\ntheorem t_b : \"a  b\" = \"a b\" := by\n  rfl\nend Demo\n",
        )?;
        let (cls_lit, to_verify_lit, _, _) =
            load_and_classify_pr_from_git(&store, &canon_dir, "HEAD", tc)?;
        assert!(cls_lit.interface_drift);
        assert_eq!(cls_lit.statement_edited_theorems, vec!["Demo/B.lean::t_b"]);
        assert_eq!(to_verify_lit["Demo/B.lean"].len(), 1);
        assert!(!to_verify_lit["Demo/B.lean"][0].2);

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
    fn test_lake_input_dir_edit_reverifies_sources() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_lake_input_edit_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let repo_dir = tmp_dir.join("repo");
        fs::create_dir_all(repo_dir.join("Smoke"))?;
        fs::create_dir_all(repo_dir.join("Data"))?;
        fs::write(
            repo_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n  text := true\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[smokeSources]\n",
        )?;
        fs::write(
            repo_dir.join("Smoke/A.lean"),
            "theorem t_a : 1 + 1 = 2 := by\n  rfl\n",
        )?;
        fs::write(repo_dir.join("Data/a.sol"), "contract A {}\n")?;
        git_init_and_commit(&repo_dir, "init")?;

        let canon_dir = fs::canonicalize(&repo_dir)?;
        let store = TurboStore::open(Some(&tmp_dir.join("cache")))?;
        let tc = "leanprover/lean4:v4.35.0";
        let classify =
            || load_and_classify_pr_from_git(&store, &canon_dir, "HEAD", tc).map(|(c, _, _, _)| c);

        // Nothing changed: the `.sol` input does not re-verify anything on its own.
        assert!(classify()?.modified_files.is_empty());
        // A matched input edit is read by `solidity_import` during elaboration, so the sources of
        // the library that `needs` it are re-verified even though no `.lean` file changed.
        fs::write(canon_dir.join("Data/a.sol"), "contract A2 {}\n")?;
        assert_eq!(classify()?.modified_files, vec!["Smoke/A.lean"]);
        fs::write(canon_dir.join("Data/a.sol"), "contract A {}\n")?;
        assert!(classify()?.modified_files.is_empty());
        // A new, still untracked input file counts too.
        fs::write(canon_dir.join("Data/b.sol"), "contract B {}\n")?;
        assert_eq!(classify()?.modified_files, vec!["Smoke/A.lean"]);
        fs::remove_file(canon_dir.join("Data/b.sol"))?;
        assert!(classify()?.modified_files.is_empty());

        // Git-ignored matched input files inside `input_dir` are read by Lake on disk even though
        // `git status --untracked-files=all` hides them without `--ignored`: `pr-verify` must detect
        // their presence/edits against `base_ref`.
        fs::write(canon_dir.join(".gitignore"), "Data/ignored.sol\n")?;
        git_commit_all(&canon_dir, "ignore rule")?;
        assert!(classify()?.modified_files.is_empty());
        fs::write(canon_dir.join("Data/ignored.sol"), "contract Ignored {}\n")?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        assert_eq!(
            classify()?.modified_files,
            vec!["Smoke/A.lean"],
            "git-ignored matched input_dir file on disk must trigger re-verification"
        );
        fs::remove_file(canon_dir.join("Data/ignored.sol"))?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        assert!(classify()?.modified_files.is_empty());

        // Symlinks inside `input_dir`:
        // - In-package symlink (`Data/link.sol -> a.sol`, even if committed as mode 120000 in git)
        //   causes `lake_input_files_changed_since_base` to conservatively mark inputs changed
        //   (`modified_files == ["Smoke/A.lean"]`), because git stores the link target path at
        //   120000 rather than the dereferenced target bytes.
        // - Out-of-package symlink fails closed (`Err`) during `try_project_lake_inputs_tag`.
        #[cfg(unix)]
        {
            std::os::unix::fs::symlink("a.sol", canon_dir.join("Data/link.sol"))?;
            git_commit_all(&canon_dir, "commit in-package symlink")?;
            crate::module_builder::reset_lake_inputs_tag_memo();
            assert_eq!(
                classify()?.modified_files,
                vec!["Smoke/A.lean"],
                "committed symlink inside input_dir must conservatively re-verify against base_ref"
            );
            fs::remove_file(canon_dir.join("Data/link.sol"))?;
            git_commit_all(&canon_dir, "remove in-package symlink")?;

            let outside_sol = tmp_dir.join("outside.sol");
            fs::write(&outside_sol, "contract Outside {}\n")?;
            std::os::unix::fs::symlink(&outside_sol, canon_dir.join("Data/escape.sol"))?;
            crate::module_builder::reset_lake_inputs_tag_memo();
            assert!(
                classify().is_err(),
                "escaping symlink inside input_dir must fail closed during pr-verify classification"
            );
            fs::remove_file(canon_dir.join("Data/escape.sol"))?;
        }

        // External `type: path` dependency package outside the git repo: if it declares Lake inputs,
        // `pr-verify` cannot reconstruct its `base_ref` tree from git and must conservatively mark
        // `lake_input_files_changed_since_base == true` (and fail closed if unsupported).
        let ext_dep = tmp_dir.join("ext_dep");
        fs::create_dir_all(ext_dep.join("DepMod"))?;
        fs::create_dir_all(ext_dep.join("ExtData"))?;
        fs::write(
            ext_dep.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage ext_dep\ninput_dir extSources where\n  path := \"ExtData\"\n  filter := .extension \"sol\"\n@[default_target]\nlean_lib DepMod where\n  globs := #[.one `DepMod.D]\n  needs := #[extSources]\n",
        )?;
        fs::write(ext_dep.join("DepMod/D.lean"), "def d : Nat := 1\n")?;
        fs::write(ext_dep.join("ExtData/ext.sol"), "contract Ext {}\n")?;
        let manifest_ext = serde_json::json!({
            "version": 7,
            "packagesDir": ".lake/packages",
            "packages": [{
                "type": "path",
                "name": "ext_dep",
                "dir": ext_dep.to_string_lossy(),
                "inherited": false,
                "configFile": "lakefile.lean"
            }]
        });
        fs::write(
            canon_dir.join("lake-manifest.json"),
            serde_json::to_vec_pretty(&manifest_ext)?,
        )?;
        git_commit_all(&canon_dir, "add external path dep")?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        let cfg_ext = crate::module_builder::resolve_project_config(&canon_dir)?;
        assert!(
            lake_input_files_changed_since_base(
                &canon_dir,
                "",
                &cfg_ext.root_pkg,
                &cfg_ext.dep_pkgs,
                "HEAD",
            ),
            "external out-of-repo path dependency with Lake inputs must conservatively report changed against base_ref"
        );

        // Materialized `.lake/packages/<dep>` git dependency declaring `input_file` / `input_dir`
        // (e.g. Mathlib's `proofwidgets`): `.lake/` is git-ignored in the root repository, so
        // `pr-verify` must verify the dependency's Lake inputs against the manifest-pinned `rev`
        // inside `.lake/packages/<dep>`'s own git repository.
        fs::write(canon_dir.join(".gitignore"), ".lake/\nData/ignored.sol\n")?;
        let git_dep = canon_dir.join(".lake/packages/pw_dep");
        fs::create_dir_all(git_dep.join("PwMod"))?;
        fs::create_dir_all(git_dep.join("widget/src"))?;
        fs::write(
            git_dep.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage pw_dep\ndef widgetDir : System.FilePath := \"widget\"\ninput_file widgetPkgJson where\n  path := widgetDir / \"package.json\"\n  text := true\ninput_dir widgetSrcs where\n  path := widgetDir / \"src\"\n  filter := .extension \"tsx\"\n  text := true\n@[default_target]\nlean_lib PwMod where\n  globs := #[.one `PwMod.P]\n  needs := #[widgetPkgJson, widgetSrcs]\n",
        )?;
        fs::write(git_dep.join("PwMod/P.lean"), "def p : Nat := 1\n")?;
        fs::write(
            git_dep.join("widget/package.json"),
            "{\"name\":\"pw\",\"version\":\"1.0.0\"}\n",
        )?;
        fs::write(git_dep.join("widget/src/app.tsx"), "export const x = 1;\n")?;
        git_init_and_commit(&git_dep, "pw_dep v1")?;
        let dep_rev1 = resolve_git_commit_sha(&git_dep, "HEAD")?;
        fs::write(git_dep.join("widget/src/app.tsx"), "export const x = 2;\n")?;
        git_commit_all(&git_dep, "pw_dep v2")?;
        let dep_rev2 = resolve_git_commit_sha(&git_dep, "HEAD")?;
        // Check out `dep_rev1` cleanly in `.lake/packages/pw_dep`.
        let checkout_status = crate::trusted_tools::git(&git_dep)?
            .arg("-C")
            .arg(&git_dep)
            .args(["checkout", "--quiet", &dep_rev1])
            .status()?;
        assert!(checkout_status.success());

        let write_git_manifest = |rev: &str| -> Result<()> {
            let m = serde_json::json!({
                "version": 7,
                "packagesDir": ".lake/packages",
                "packages": [{
                    "type": "git",
                    "name": "pw_dep",
                    "url": "https://example.invalid/pw_dep.git",
                    "rev": rev,
                    "inherited": false,
                    "configFile": "lakefile.lean"
                }]
            });
            fs::write(
                canon_dir.join("lake-manifest.json"),
                serde_json::to_vec_pretty(&m)?,
            )?;
            Ok(())
        };
        write_git_manifest(&dep_rev1)?;
        git_commit_all(&canon_dir, "pin pw_dep rev1")?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        let cfg_pw = crate::module_builder::resolve_project_config(&canon_dir)?;
        assert!(
            !lake_input_files_changed_since_base(
                &canon_dir,
                "",
                &cfg_pw.root_pkg,
                &cfg_pw.dep_pkgs,
                "HEAD",
            ),
            "clean materialized git dependency with input_file/input_dir must report unchanged"
        );
        assert!(
            classify()?.modified_files.is_empty(),
            "clean materialized git dependency must not mark root modules modified"
        );

        // Dirtying a tracked file inside `.lake/packages/pw_dep/widget/src` without changing
        // `lake-manifest.json` must fail closed (`changed == true`, root modules re-verified).
        fs::write(
            git_dep.join("widget/src/app.tsx"),
            "export const x = 999;\n",
        )?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        let cfg_pw_dirty = crate::module_builder::resolve_project_config(&canon_dir)?;
        assert!(
            lake_input_files_changed_since_base(
                &canon_dir,
                "",
                &cfg_pw_dirty.root_pkg,
                &cfg_pw_dirty.dep_pkgs,
                "HEAD",
            ),
            "dirty input file inside materialized git dependency must report changed"
        );
        assert_eq!(
            classify()?.modified_files,
            vec!["Smoke/A.lean"],
            "dirty materialized git dependency input must trigger root module re-verification"
        );
        // Restore clean `dep_rev1` checkout.
        let restore_status = crate::trusted_tools::git(&git_dep)?
            .arg("-C")
            .arg(&git_dep)
            .args(["checkout", "--quiet", "--", "widget/src/app.tsx"])
            .status()?;
        assert!(restore_status.success());
        crate::module_builder::reset_lake_inputs_tag_memo();
        assert!(classify()?.modified_files.is_empty());

        // Bumping `pw_dep`'s `rev` in `lake-manifest.json` (and checking out `dep_rev2`) against
        // `base_ref` (`HEAD~0` before commit) must detect the Lake-input digest change.
        let base_before_bump = resolve_git_commit_sha(&canon_dir, "HEAD")?;
        let bump_co = crate::trusted_tools::git(&git_dep)?
            .arg("-C")
            .arg(&git_dep)
            .args(["checkout", "--quiet", &dep_rev2])
            .status()?;
        assert!(bump_co.success());
        write_git_manifest(&dep_rev2)?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        let (classified_bump, _, _, _) =
            load_and_classify_pr_from_git(&store, &canon_dir, &base_before_bump, tc)?;
        assert_eq!(
            classified_bump.modified_files,
            vec!["Smoke/A.lean"],
            "manifest rev bump changing git dependency inputs must re-verify root modules"
        );

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_base_lake_input_symlinks_fail_closed_before_extension_filter() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_base_input_symlinks_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let store = TurboStore::open(Some(&tmp_dir.join("cache")))?;
        let tc = "leanprover/lean4:v4.35.0";

        // 1. Symlinked subdirectory `Data/sub -> ../Shared` inside `input_dir` with
        //    `filter := .extension "sol"` in `base_ref`, replaced by empty `Data/.keep` in PR HEAD.
        let repo1 = tmp_dir.join("repo_sub_symlink");
        fs::create_dir_all(repo1.join("Smoke"))?;
        fs::create_dir_all(repo1.join("Shared"))?;
        fs::create_dir_all(repo1.join("Data"))?;
        let lf_sub = "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[smokeSources]\n";
        fs::write(repo1.join("lakefile.lean"), lf_sub)?;
        fs::write(
            repo1.join("Smoke/A.lean"),
            "theorem t_a : 1 + 1 = 2 := by\n  rfl\n",
        )?;
        fs::write(repo1.join("Shared/A.sol"), "contract A {}\n")?;
        std::os::unix::fs::symlink("../Shared", repo1.join("Data/sub"))?;
        git_init_and_commit(&repo1, "base with symlinked subdir")?;
        let canon1 = fs::canonicalize(&repo1)?;
        let base1 = resolve_git_commit_sha(&canon1, "HEAD")?;

        fs::remove_file(canon1.join("Data/sub"))?;
        fs::write(canon1.join("Data/.keep"), "")?;
        git_commit_all(&canon1, "pr replaces symlinked subdir with .keep")?;
        crate::module_builder::reset_lake_inputs_tag_memo();

        let cur_cfg1 = crate::module_builder::resolve_project_config(&canon1)?;
        assert!(
            lake_input_files_changed_since_base(
                &canon1,
                "",
                &cur_cfg1.root_pkg,
                &cur_cfg1.dep_pkgs,
                &base1,
            ),
            "removing Data/sub -> ../Shared must report changed even when Data/sub lacks .sol extension"
        );
        let mut base_pkg1 = parse_staged_base_package_config(&store, &canon1, lf_sub, false, true)?;
        assert!(
            hash_package_inputs_from_git_tree(&canon1, &base1, &mut base_pkg1).is_none(),
            "hash_package_inputs_from_git_tree must fail closed on symlinked subdir Data/sub"
        );
        let base_tag1 = resolve_base_lake_inputs_tag(
            &store,
            &canon1,
            &canon1,
            &base1,
            Some(&base_pkg1),
            &cur_cfg1.dep_pkgs,
            false,
        )?
        .expect("base lake inputs tag");
        assert!(
            base_tag1.starts_with("\u{0}lake-inputs-uncacheable:"),
            "resolve_base_lake_inputs_tag must return uncacheable sentinel, got {base_tag1:?}"
        );
        let cur_tag1 = crate::module_builder::try_project_lake_inputs_tag(&canon1)?
            .expect("current empty Data/.keep still produces a concrete lake_inputs tag");
        assert_ne!(base_tag1, cur_tag1);
        let (classified1, _, _, _) = load_and_classify_pr_from_git(&store, &canon1, &base1, tc)?;
        assert_eq!(classified1.modified_files, vec!["Smoke/A.lean"]);

        // 2. `Data` itself being a symlink in `base_ref` (`Data -> Shared`), replaced by real
        //    `Data/.keep` in PR HEAD.
        let repo2 = tmp_dir.join("repo_direct_symlink");
        fs::create_dir_all(repo2.join("Smoke"))?;
        fs::create_dir_all(repo2.join("Shared"))?;
        fs::write(repo2.join("lakefile.lean"), lf_sub)?;
        fs::write(
            repo2.join("Smoke/A.lean"),
            "theorem t_a : 1 + 1 = 2 := by\n  rfl\n",
        )?;
        fs::write(repo2.join("Shared/A.sol"), "contract A {}\n")?;
        std::os::unix::fs::symlink("Shared", repo2.join("Data"))?;
        git_init_and_commit(&repo2, "base with symlinked Data")?;
        let canon2 = fs::canonicalize(&repo2)?;
        let base2 = resolve_git_commit_sha(&canon2, "HEAD")?;

        fs::remove_file(canon2.join("Data"))?;
        fs::create_dir_all(canon2.join("Data"))?;
        fs::write(canon2.join("Data/.keep"), "")?;
        git_commit_all(&canon2, "pr replaces symlink Data with real dir")?;
        crate::module_builder::reset_lake_inputs_tag_memo();

        let cur_cfg2 = crate::module_builder::resolve_project_config(&canon2)?;
        assert!(
            lake_input_files_changed_since_base(
                &canon2,
                "",
                &cur_cfg2.root_pkg,
                &cur_cfg2.dep_pkgs,
                &base2,
            ),
            "replacing symlink Data -> Shared with real empty Data/.keep must report changed"
        );
        let mut base_pkg2 = parse_staged_base_package_config(&store, &canon2, lf_sub, false, true)?;
        assert!(
            hash_package_inputs_from_git_tree(&canon2, &base2, &mut base_pkg2).is_none(),
            "hash_package_inputs_from_git_tree must fail closed when input_dir root Data is a symlink"
        );
        let base_tag2 = resolve_base_lake_inputs_tag(
            &store,
            &canon2,
            &canon2,
            &base2,
            Some(&base_pkg2),
            &cur_cfg2.dep_pkgs,
            false,
        )?
        .expect("base lake inputs tag");
        assert!(
            base_tag2.starts_with("\u{0}lake-inputs-uncacheable:"),
            "got {base_tag2:?}"
        );

        // 3. Ancestor directory of both `input_dir` (`Anc/Sub`) and `input_file` (`Anc/spec.sol`)
        //    being a symlink (`Anc -> SharedParent`) in `base_ref`, replaced by real directory in PR HEAD.
        let repo3 = tmp_dir.join("repo_ancestor_symlink");
        fs::create_dir_all(repo3.join("Smoke"))?;
        fs::create_dir_all(repo3.join("SharedParent/Sub"))?;
        let lf_anc = "import Lake\nopen Lake DSL\npackage demo\ninput_dir dirInAnc where\n  path := \"Anc/Sub\"\n  filter := .extension \"sol\"\ninput_file fileInAnc where\n  path := \"Anc/spec.sol\"\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[dirInAnc, fileInAnc]\n";
        fs::write(repo3.join("lakefile.lean"), lf_anc)?;
        fs::write(
            repo3.join("Smoke/A.lean"),
            "theorem t_a : 1 + 1 = 2 := by\n  rfl\n",
        )?;
        fs::write(repo3.join("SharedParent/Sub/A.sol"), "contract A {}\n")?;
        fs::write(repo3.join("SharedParent/spec.sol"), "contract Spec {}\n")?;
        std::os::unix::fs::symlink("SharedParent", repo3.join("Anc"))?;
        git_init_and_commit(&repo3, "base with symlinked ancestor Anc")?;
        let canon3 = fs::canonicalize(&repo3)?;
        let base3 = resolve_git_commit_sha(&canon3, "HEAD")?;

        fs::remove_file(canon3.join("Anc"))?;
        fs::create_dir_all(canon3.join("Anc/Sub"))?;
        fs::write(canon3.join("Anc/Sub/.keep"), "")?;
        fs::write(canon3.join("Anc/spec.sol"), "contract Spec {}\n")?;
        git_commit_all(&canon3, "pr materializes real Anc directory")?;
        crate::module_builder::reset_lake_inputs_tag_memo();

        let cur_cfg3 = crate::module_builder::resolve_project_config(&canon3)?;
        assert!(
            lake_input_files_changed_since_base(
                &canon3,
                "",
                &cur_cfg3.root_pkg,
                &cur_cfg3.dep_pkgs,
                &base3,
            ),
            "symlinked ancestor Anc in base_ref must report changed"
        );
        for (only_lf, label) in [
            (
                "import Lake\nopen Lake DSL\npackage demo\ninput_dir dirInAnc where\n  path := \"Anc/Sub\"\n  filter := .extension \"sol\"\nlean_lib Smoke where\n  needs := #[dirInAnc]\n",
                "input_dir under symlinked ancestor",
            ),
            (
                "import Lake\nopen Lake DSL\npackage demo\ninput_file fileInAnc where\n  path := \"Anc/spec.sol\"\nlean_lib Smoke where\n  needs := #[fileInAnc]\n",
                "input_file under symlinked ancestor",
            ),
        ] {
            let mut single_base_pkg =
                parse_staged_base_package_config(&store, &canon3, only_lf, false, true)?;
            assert!(
                hash_package_inputs_from_git_tree(&canon3, &base3, &mut single_base_pkg).is_none(),
                "{label} must fail closed in hash_package_inputs_from_git_tree"
            );
            fs::write(canon3.join("lakefile.lean"), only_lf)?;
            crate::module_builder::reset_lake_inputs_tag_memo();
            let resolved_single = crate::module_builder::resolve_project_config(&canon3)?;
            assert!(
                lake_input_files_changed_since_base(
                    &canon3,
                    "",
                    &resolved_single.root_pkg,
                    &[],
                    &base3,
                ),
                "{label} must report changed in lake_input_files_changed_since_base"
            );
        }

        let _ = fs::remove_dir_all(&tmp_dir);
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
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
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
        let fake_bwrap =
            crate::module_builder::ScopedTestBwrapOverride::write_fake_bwrap_script(&tmp_dir)?;
        let mut store = TurboStore::open(Some(&tmp_dir.join("store")))?;
        let run_ci = |st: &mut TurboStore, mode: &str| {
            run_ci_verify_command(
                st,
                true,
                mode.to_string(),
                repo_dir.clone(),
                None,
                None,
                false,
                None,
            )
        };
        let run_pr =
            |st: &mut TurboStore, disallow_stmt: bool, max_cone: usize, rcpt: Option<PathBuf>| {
                run_pr_verify_command(
                    st,
                    true,
                    repo_dir.clone(),
                    "HEAD".to_string(),
                    "untrusted".to_string(),
                    disallow_stmt,
                    rcpt,
                    None,
                    None,
                    None,
                    false,
                    max_cone,
                    None,
                )
            };
        let dyn_ci_err = {
            let _bwrap_guard = crate::module_builder::ScopedTestBwrapOverride::set(
                fake_bwrap.to_string_lossy().into_owned(),
            );
            run_ci(&mut store, "untrusted").unwrap_err().to_string()
        };
        assert!(!repo_dir.join("pwned.txt").exists());
        assert!(
            dyn_ci_err.contains("static") || dyn_ci_err.contains("run_cmd"),
            "got: {dyn_ci_err}"
        );

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
            (
                run_ci(&mut store, "untrusted").unwrap_err().to_string(),
                run_pr(&mut store, false, 0, None).unwrap_err().to_string(),
            )
        };
        assert!(
            no_bwrap_ci.contains("requires a working bubblewrap")
                && no_bwrap_pr.contains("requires a working bubblewrap")
        );

        // 3. Same-size/same-mtime stat-cache poisoning must be bypassed in untrusted `ci-verify`.
        let demo_path = repo_dir.join("Demo/Basic.lean");
        let clean_same_len = "namespace Demo\ntheorem t_ok : 2 + 2 = 4 := rfl  \nend Demo\n";
        let sorry_padded = "namespace Demo\ntheorem t_ok : 2 + 2 = 5 := sorry\nend Demo\n";
        assert_eq!(clean_same_len.len(), sorry_padded.len());
        fs::write(&demo_path, clean_same_len)?;
        let canon_repo = fs::canonicalize(&repo_dir)?;
        let canon_demo = canon_repo.join("Demo/Basic.lean");
        let _ = load_project_stat_summary_cached(
            &store,
            &canon_repo,
            std::slice::from_ref(&canon_demo),
        )?;
        #[cfg(unix)]
        let orig_mtime = {
            use std::os::unix::fs::MetadataExt;
            let m = fs::metadata(&canon_demo)?;
            (m.mtime(), m.mtime_nsec())
        };
        fs::write(&canon_demo, sorry_padded)?;
        #[cfg(unix)]
        {
            let tv = [libc::timespec {
                tv_sec: orig_mtime.0,
                tv_nsec: orig_mtime.1,
            }; 2];
            let c_path = std::ffi::CString::new(canon_demo.to_string_lossy().as_bytes())?;
            unsafe {
                libc::utimensat(libc::AT_FDCWD, c_path.as_ptr(), tv.as_ptr(), 0);
            }
        }
        let sorry_ci_err = {
            let _bwrap_guard = crate::module_builder::ScopedTestBwrapOverride::set(
                fake_bwrap.to_string_lossy().into_owned(),
            );
            run_ci(&mut store, "untrusted").unwrap_err().to_string()
        };
        assert!(
            sorry_ci_err.contains("Hygiene & Axiom Gate FAILED"),
            "got: {sorry_ci_err}"
        );

        // 4. Clean proof edit in untrusted `pr-verify` compiles inside sandbox and passes `--audit-modules` kernel audit,
        // while a hidden macro-expanded `sorry` or false proof fails closed.
        fs::write(
            &canon_demo,
            "namespace Demo\ntheorem t_ok : 1 + 1 = 2 := by\n  decide\nend Demo\n",
        )?;
        {
            let _bwrap_guard = crate::module_builder::ScopedTestBwrapOverride::set(
                fake_bwrap.to_string_lossy().into_owned(),
            );
            run_pr(&mut store, true, 0, None)
                .expect("valid untrusted pr-verify proof edit should pass");
        }

        let hidden_ax_src = "import Lean\nopen Lean Elab Tactic in\nelab \"sneak_ax\" : tactic => do\n  let g ← getMainGoal\n  let t ← g.getType\n  let s := String.mk ['s', 'o', 'r', 'r', 'y', 'A', 'x']\n  let e ← Meta.mkAppM (Name.mkSimple s) #[t, mkConst ``false]\n  g.assign e\nnamespace Demo\ntheorem t_ok : 1 + 1 = 2 := by\n  sneak_ax\nend Demo\n";
        fs::write(&canon_demo, hidden_ax_src)?;
        {
            let _bwrap_guard = crate::module_builder::ScopedTestBwrapOverride::set(
                fake_bwrap.to_string_lossy().into_owned(),
            );
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
        fs::write(
            &canon_demo,
            "namespace Demo\ntheorem t_ok : 1 + 1 = 2 := rfl\nend Demo\n",
        )?;
        run_ci(&mut store, "trusted")?;
        let init_hashes = BTreeMap::from([(
            "Demo/Basic.lean".to_string(),
            blake3::hash(fs::read(&canon_demo)?.as_slice())
                .to_hex()
                .to_string(),
        )]);
        assert!(are_all_project_oleans_up_to_date(&canon_repo, &init_hashes));
        let trace_path = canon_repo.join(".lake/build/lib/lean/Demo/Basic.trace");
        let saved_trace = fs::read(&trace_path)?;
        fs::write(&trace_path, b"corrupt-non-json-trace")?;
        assert!(!are_all_project_oleans_up_to_date(
            &canon_repo,
            &init_hashes
        ));
        fs::write(&trace_path, &saved_trace)?;
        let hash_path = canon_repo.join(".lake/build/lib/lean/Demo/Basic.olean.hash");
        if hash_path.exists() {
            let saved_hash = fs::read(&hash_path)?;
            fs::write(&hash_path, b"0")?;
            assert!(!are_all_project_oleans_up_to_date(
                &canon_repo,
                &init_hashes
            ));
            fs::write(&hash_path, &saved_hash)?;
        }

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_untrusted_pr_verify_multi_theorem_file_checks_full_source() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
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
        fs::write(
            repo_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            repo_dir.join("lakefile.toml"),
            "name = \"demo_pkg\"\ndefaultTargets = [\"Demo\"]\n[[lean_lib]]\nname = \"Demo\"\nroots = [\"Demo.Basic\"]\n",
        )?;
        fs::write(
            repo_dir.join("Demo/Basic.lean"),
            "namespace Demo\ntheorem t_keep : 3 + 3 = 6 := rfl\ntheorem t_a : 1 + 1 = 2 := rfl\ntheorem t_b : 2 + 2 = 4 := rfl\nend Demo\n",
        )?;
        let fake_bwrap =
            crate::module_builder::ScopedTestBwrapOverride::write_fake_bwrap_script(&tmp_dir)?;
        git_init_and_commit(&repo_dir, "base")?;
        let demo_path = fs::canonicalize(&repo_dir)?.join("Demo/Basic.lean");
        let mut store = TurboStore::open(Some(&tmp_dir.join("store")))?;
        let mut run_untrusted = |src: &str| -> Result<()> {
            fs::write(&demo_path, src)?;
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
                None,
                None,
                None,
                None,
                false,
                0,
                None,
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
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
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
        fs::write(
            repo_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            repo_dir.join("A.lean"),
            "theorem t : 2 ^ 3 = 8 := by native_decide\n",
        )?;
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
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
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
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
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
        // Trusted mode also uses stock Lake and catches P.B without executing the wrapper.
        let trusted_err = pr_verify_mode("trusted").unwrap_err().to_string();
        assert!(
            !rce_marker.exists(),
            "trusted dependent recheck must use stock Lake instead of [lake] build_command"
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
            crate::lake_build::lake_recheck_dependents(&dir, &edits, None)?.0,
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
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_pr_cone_overflow_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let repo_dir = tmp_dir.join("repo");
        fs::create_dir_all(repo_dir.join("Demo"))?;
        fs::write(
            repo_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
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

    /// Recursive file copy, so a test can snapshot a warm `.lake/build` and hand an identical one
    /// to each entry point it measures. Lake's own files there may be hard links into its artifact
    /// cache; this materializes them, which is what a restored baseline wants anyway.
    fn copy_tree(src: &Path, dst: &Path) -> Result<()> {
        if src.is_dir() {
            fs::create_dir_all(dst)?;
            for entry in fs::read_dir(src)? {
                let entry = entry?;
                copy_tree(&entry.path(), &dst.join(entry.file_name()))?;
            }
        } else if src.is_file() {
            if let Some(parent) = dst.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::copy(src, dst)?;
        }
        Ok(())
    }

    /// A warm `.lake/build` must not vouch for `.olean` files elaborated against Lake file inputs
    /// that have since changed.
    ///
    /// `build`, `ci-verify` and `check` all have a fast path that accepts the `.olean` files listed
    /// in `.lake/build/.turbo_verified_sources.json` without ever computing a module cache key:
    /// `are_all_project_oleans_up_to_date` and `ensure_project_imports_fresh_for_check` compare
    /// `pkg_config_digest`, `.lean` source hashes and mtimes, none of which move when an
    /// `input_dir` file is edited. A `.sol` edit *does* miss the action key, so the build is the
    /// leader and reaches exactly that fast path, with the stale artifacts still on disk.
    ///
    /// The module here pins the input's length with `include_str` and a kernel `rfl`, so reusing
    /// the previous `.olean` is observable as a **passing** build of a now-false theorem rather
    /// than as a mere performance artifact. Every step below keeps `.lake/build` in place; the
    /// existing differential test in `module_builder` deletes it and so cannot see this.
    #[test]
    fn test_warm_build_dir_rejects_oleans_stale_against_edited_lake_input() -> Result<()> {
        // Drives `build` / `ci-verify` / `check` end to end, so it reads process-global state
        // (`TURBO_LEAN_NO_WORKTREE_LINK` via `worktree_auto_link_disabled`, the zygote warm-up).
        // Serialize with the other env-mutating tests the way they serialize with each other.
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_warm_lake_input_test_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let repo_dir = tmp_dir.join("repo");
        fs::create_dir_all(repo_dir.join("Smoke"))?;
        fs::create_dir_all(repo_dir.join("Data"))?;
        fs::write(
            repo_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            repo_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n  text := true\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A, .one `Smoke.B]\n  needs := #[smokeSources]\n",
        )?;
        let v1 = "contract A {}\n";
        let v2 = "contract AMuchLongerName {}\n";
        assert_ne!(v1.len(), v2.len(), "the pinned length must actually move");
        // `include_str` resolves relative to the importing file's directory, and `rfl` forces the
        // kernel to evaluate the literal that elaboration baked in.
        fs::write(
            repo_dir.join("Smoke/A.lean"),
            format!(
                "def solText : String := include_str \"../Data/a.sol\"\ntheorem solLen : solText.length = {} := by rfl\n",
                v1.len()
            ),
        )?;
        // `B` only reaches the input through its import of `A`, which is what exercises the
        // `check` path's `ensure_project_imports_fresh_for_check`.
        fs::write(
            repo_dir.join("Smoke/B.lean"),
            format!(
                "import Smoke.A\ntheorem useLen : solText.length = {} := solLen\n",
                v1.len()
            ),
        )?;
        fs::write(repo_dir.join("Data/a.sol"), v1)?;

        // Needs a real toolchain, like the other end-to-end tests in this module.
        if crate::module_builder::resolve_project_config(&repo_dir).is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return Ok(());
        }
        git_init_and_commit(&repo_dir, "base")?;
        let canon_repo = fs::canonicalize(&repo_dir)?;
        let mut store = TurboStore::open(Some(&tmp_dir.join("store")))?;

        let olean_a = canon_repo.join(".lake/build/lib/lean/Smoke/A.olean");
        let inputs_digest = || -> String {
            crate::module_builder::resolve_project_config(&canon_repo)
                .and_then(|cfg| crate::module_builder::workspace_lake_inputs_digest(&cfg))
                .unwrap_or_default()
        };
        let manifest_inputs_digest = || -> Option<String> {
            let path = crate::lake_build::verified_sources_manifest_path(&canon_repo);
            fs::read(path)
                .ok()
                .and_then(|b| {
                    serde_json::from_slice::<crate::module_builder::VerifiedDepManifest>(&b).ok()
                })
                .map(|m| m.lake_inputs_digest)
        };
        // Empty `targets` is what makes `build` consult the warm-directory fast path at all.
        // All three discard their success value so step 3 can hold them in one `&dyn Fn` list and
        // give each an independently restored warm baseline.
        let build = |st: &mut TurboStore| -> Result<()> {
            crate::lake_build::run_build_command(
                st,
                true,
                Vec::new(),
                canon_repo.clone(),
                "trusted".to_string(),
                0,
                false,
            )
            .map(|_| ())
        };
        let ci_verify = |st: &mut TurboStore| -> Result<()> {
            run_ci_verify_command(
                st,
                true,
                "trusted".to_string(),
                canon_repo.clone(),
                None,
                None,
                false,
                None,
            )
            .map(|_| ())
        };
        let check_b = |st: &mut TurboStore| -> Result<()> {
            crate::check::run_check_command(
                st,
                false,
                true,
                canon_repo.join("Smoke/B.lean"),
                None,
                canon_repo.clone(),
                None,
                false,
                None,
            )
            .map(|_| ())
        };

        // 1. Cold build of the consistent tree, then record what the warm directory vouches for.
        build(&mut store).expect("initial build of a consistent tree must succeed");
        assert!(
            olean_a.is_file(),
            "initial build must produce Smoke/A.olean"
        );
        let v1_olean = fs::read(&olean_a)?;
        let v1_digest = inputs_digest();
        assert!(
            !v1_digest.is_empty(),
            "a package with inputs must digest them"
        );
        assert_eq!(
            manifest_inputs_digest().as_deref(),
            Some(v1_digest.as_str()),
            "the recorded manifest must pin the input contents it was built against"
        );
        // Warm no-op: the fast path is genuinely reached and still accepts a consistent tree.
        build(&mut store).expect("warm rebuild of an unchanged tree must stay green");
        ci_verify(&mut store).expect("warm ci-verify of an unchanged tree must stay green");
        check_b(&mut store).expect("warm check of an unchanged tree must stay green");
        assert_eq!(
            fs::read(&olean_a)?,
            v1_olean,
            "an unchanged tree must not re-elaborate"
        );

        // 2. Snapshot the warm directory -- artifacts *and*
        // `.lake/build/.turbo_verified_sources.json` both live under `.lake/build` -- so each
        // entry point below can be given its own copy of it.
        let warm_snapshot = tmp_dir.join("warm_lake_build");
        let lake_build_dir = canon_repo.join(".lake/build");
        copy_tree(&lake_build_dir, &warm_snapshot)?;
        assert!(
            warm_snapshot.join(".turbo_verified_sources.json").is_file(),
            "the warm snapshot must capture the manifest the fast paths read"
        );

        // 3. Each entry point must re-elaborate against the new bytes, which makes the pinned
        // length false. Before the fix the warm `.olean` was accepted and all three passed, so
        // collect all three outcomes rather than short-circuiting: a regression in any one of them
        // should name itself.
        //
        // Each gets an independently restored warm baseline. `build`, `ci-verify` and `check` all
        // rewrite or purge `.lake/build` and the manifest on their way to a verdict, so running
        // them in sequence would hand the second and third a directory the first had already
        // invalidated: their verdicts would say nothing about the *warm* fast path, which is the
        // only thing this test is about. Restore the snapshot, then re-apply the edit, so every
        // run starts from the same "warm directory, consistent manifest, edited input" state.
        let restore_warm = |label: &str| -> Result<()> {
            let _ = fs::remove_dir_all(&lake_build_dir);
            copy_tree(&warm_snapshot, &lake_build_dir)
                .with_context(|| format!("restoring the warm baseline for `{label}`"))?;
            fs::write(canon_repo.join("Data/a.sol"), v2)?;
            assert_ne!(
                inputs_digest(),
                v1_digest,
                "`{label}` must start from the edited input"
            );
            assert!(
                crate::lake_build::lake_inputs_changed_since_manifest(&canon_repo),
                "the restored manifest must read as stale for `{label}`"
            );
            assert!(
                olean_a.is_file(),
                "`{label}` must start from a populated warm build directory"
            );
            Ok(())
        };
        let mut false_greens: Vec<&str> = Vec::new();
        for (label, run) in [
            ("build", &build as &dyn Fn(&mut TurboStore) -> Result<()>),
            ("ci-verify", &ci_verify),
            ("check", &check_b),
        ] {
            restore_warm(label)?;
            if run(&mut store).is_ok() {
                false_greens.push(label);
            }
        }
        assert!(
            false_greens.is_empty(),
            "{:?} accepted .oleans elaborated against the old `input_dir` contents, so a false \
             theorem passed: the warm-build-directory fast path is input-blind",
            false_greens
        );

        // 4. The failure is content-driven, not a blanket "inputs declared => always fail":
        // restoring the original bytes makes the same warm directory green again.
        fs::write(canon_repo.join("Data/a.sol"), v1)?;
        assert_eq!(inputs_digest(), v1_digest);
        build(&mut store).expect("restoring the original input bytes must rebuild green");
        ci_verify(&mut store).expect("restoring the original input bytes must re-attest green");
        check_b(&mut store).expect("restoring the original input bytes must re-check green");

        // 5. And the new bytes are really what elaboration saw: re-pin the length to `v2` and the
        // same edit that failed in step 3 now passes, with a different `.olean`.
        for (rel, src) in [
            (
                "Smoke/A.lean",
                format!(
                    "def solText : String := include_str \"../Data/a.sol\"\ntheorem solLen : solText.length = {} := by rfl\n",
                    v2.len()
                ),
            ),
            (
                "Smoke/B.lean",
                format!(
                    "import Smoke.A\ntheorem useLen : solText.length = {} := solLen\n",
                    v2.len()
                ),
            ),
        ] {
            fs::write(canon_repo.join(rel), src)?;
        }
        fs::write(canon_repo.join("Data/a.sol"), v2)?;
        build(&mut store).expect("a tree consistent with the new input bytes must build");
        ci_verify(&mut store).expect("a tree consistent with the new input bytes must attest");
        check_b(&mut store).expect("a tree consistent with the new input bytes must check");
        assert_ne!(
            fs::read(&olean_a)?,
            v1_olean,
            "the rebuilt .olean must differ from the one elaborated against the old input"
        );
        assert_eq!(
            manifest_inputs_digest(),
            Some(inputs_digest()),
            "the manifest must now pin the new input contents"
        );

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    /// Round-4 regression suite covering:
    /// - Finding 1: `evaluate_agent_step_value` (`agent-step` / `turbo_agent_step`) refreshes stale
    ///   imported `.olean`s after a matched `input_dir` edit and invalidates `st_*.json` SHM splits.
    /// - Finding 2: `git_head_tree` (`pr-verify` + `check` fast-prefix split) invalidates when a
    ///   matched `input_dir` file changes or when Lake input config becomes unsupported.
    /// - Finding 4: Unsupported `filter := .text` or missing `input_file` fails closed across
    ///   `check`, `pr-verify`, `ci-verify`, `agent-step`, and `eval`.
    /// - Finding 5: Dependency package (`dep_pkgs` in `lake-manifest.json`) `input_dir` edit
    ///   refreshes stale dependency `.olean`s in `ensure_project_imports_fresh_for_check` so
    ///   `check` and `agent-step` never reuse stale dependency `.olean` bytes.
    #[test]
    fn test_round4_agent_step_head_tree_dep_inputs_and_fail_closed_gates() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let saved_staging = std::env::var("TURBO_LEAN_STAGING_DIR").ok();
        let saved_cache = std::env::var("TURBO_LEAN_CACHE_DIR").ok();

        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_round4_lake_inputs_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let staging_dir = tmp_dir.join("staging");
        let cache_dir = tmp_dir.join("store");
        fs::create_dir_all(&staging_dir)?;
        std::env::set_var("TURBO_LEAN_STAGING_DIR", &staging_dir);
        std::env::set_var("TURBO_LEAN_CACHE_DIR", &cache_dir);

        let restore_env = |saved_staging: &Option<String>, saved_cache: &Option<String>| {
            match saved_staging {
                Some(v) => std::env::set_var("TURBO_LEAN_STAGING_DIR", v),
                None => std::env::remove_var("TURBO_LEAN_STAGING_DIR"),
            }
            match saved_cache {
                Some(v) => std::env::set_var("TURBO_LEAN_CACHE_DIR", v),
                None => std::env::remove_var("TURBO_LEAN_CACHE_DIR"),
            }
        };

        let res = (|| -> Result<()> {
            let repo_dir = tmp_dir.join("repo");
            let dep_dir = repo_dir.join(".lake/packages/dep_pkg");
            fs::create_dir_all(repo_dir.join("Smoke"))?;
            fs::create_dir_all(repo_dir.join("Data"))?;
            fs::create_dir_all(dep_dir.join("DepMod"))?;
            fs::create_dir_all(dep_dir.join("DepData"))?;

            fs::write(
                repo_dir.join("lean-toolchain"),
                include_str!("../../../lean/lean-toolchain"),
            )?;
            fs::write(
                dep_dir.join("lean-toolchain"),
                include_str!("../../../lean/lean-toolchain"),
            )?;
            let dep_lakefile = "import Lake\nopen Lake DSL\npackage dep_pkg\ninput_dir depSources where\n  path := \"DepData\"\n  filter := .extension \"sol\"\n  text := true\n@[default_target]\nlean_lib DepMod where\n  globs := #[.one `DepMod.D]\n  needs := #[depSources]\n";
            fs::write(dep_dir.join("lakefile.lean"), dep_lakefile)?;

            let root_lakefile = "import Lake\nopen Lake DSL\npackage demo\nrequire dep_pkg from \".lake/packages/dep_pkg\"\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n  text := true\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A, .one `Smoke.B]\n  needs := #[smokeSources]\n";
            fs::write(repo_dir.join("lakefile.lean"), root_lakefile)?;
            let manifest_json = serde_json::json!({
                "version": 7,
                "packagesDir": ".lake/packages",
                "packages": [{
                    "type": "path",
                    "name": "dep_pkg",
                    "dir": ".lake/packages/dep_pkg",
                    "inherited": false,
                    "configFile": "lakefile.lean"
                }]
            });
            fs::write(
                repo_dir.join("lake-manifest.json"),
                serde_json::to_vec_pretty(&manifest_json)?,
            )?;

            let root_v1 = "contract RootA {}\n";
            let root_v2 = "contract RootAMuchLonger {}\n";
            let dep_v1 = "contract DepD {}\n";
            let dep_v2 = "contract DepDMuchLonger {}\n";

            fs::write(repo_dir.join("Data/a.sol"), root_v1)?;
            fs::write(dep_dir.join("DepData/d.sol"), dep_v1)?;
            fs::write(
                dep_dir.join("DepMod/D.lean"),
                "def depSol : String := include_str \"../DepData/d.sol\"\n",
            )?;
            fs::write(
                repo_dir.join("Smoke/A.lean"),
                "import DepMod.D\ndef rootSol : String := include_str \"../Data/a.sol\"\n",
            )?;
            fs::write(
                repo_dir.join("Smoke/B.lean"),
                format!(
                    "import Smoke.A\ntheorem useRoot : rootSol.length = {} := by rfl\ntheorem useDep : depSol.length = {} := by rfl\n",
                    root_v1.len(),
                    dep_v1.len()
                ),
            )?;

            if crate::module_builder::resolve_project_config(&repo_dir).is_err() {
                return Ok(());
            }

            git_init_and_commit(&repo_dir, "base")?;
            let canon_repo = fs::canonicalize(&repo_dir)?;
            let mut store = TurboStore::open(Some(&cache_dir))?;
            let tc = crate::lake_build::detect_toolchain(&canon_repo);

            // Initial build so both root `Smoke.A` and dependency `DepMod.D` have warm `.olean`s.
            crate::module_builder::reset_lake_inputs_tag_memo();
            crate::lake_build::run_build_command(
                &mut store,
                true,
                Vec::new(),
                canon_repo.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;

            let file_b = canon_repo.join("Smoke/B.lean");
            let head_sha = String::from_utf8(
                Command::new("git")
                    .args(["rev-parse", "HEAD"])
                    .current_dir(&canon_repo)
                    .output()?
                    .stdout,
            )?
            .trim()
            .to_string();

            // Warm `agent-step` and `git_head_tree` on consistent `v1` inputs.
            crate::module_builder::reset_lake_inputs_tag_memo();
            let step_ok = crate::gpu_fastcheck::evaluate_agent_step_value(
                &mut store,
                &file_b,
                None,
                Some(&canon_repo),
                false,
                false,
            )?;
            assert_eq!(
                step_ok["verified"],
                serde_json::json!(true),
                "warm agent-step v1: {step_ok}"
            );

            let lean_paths = vec![canon_repo.join("Smoke/A.lean"), file_b.clone()];
            let (splits, _) = crate::lake_build::load_and_split_files_cached(&store, &lean_paths)?;
            warm_git_head_tree_cache(&store, &canon_repo, &lean_paths, &tc, Some(&splits));
            assert!(
                git_head_tree_cache_paths(&store, &canon_repo, &canon_repo, &head_sha, &tc)
                    .is_some(),
                "supported workspace must produce git_head_tree_v11 cache path"
            );
            let head_key_v1 =
                git_head_tree_cache_paths(&store, &canon_repo, &canon_repo, &head_sha, &tc)
                    .unwrap()
                    .0;
            assert!(
                head_key_v1.exists(),
                "git_head_tree cache must be written on v1"
            );

            // Finding 1 & Finding 2: Edit root `Data/a.sol` -> `git_head_tree` cache key must move,
            // and `evaluate_agent_step_value` on `Smoke/B.lean` must refresh `Smoke.A` and FAIL
            // (`verified == false`) rather than reusing the stale `Smoke/A.olean` or `st_*.json` split!
            fs::write(canon_repo.join("Data/a.sol"), root_v2)?;
            crate::module_builder::reset_lake_inputs_tag_memo();
            let head_key_v2 =
                git_head_tree_cache_paths(&store, &canon_repo, &canon_repo, &head_sha, &tc)
                    .expect("head_tree key v2")
                    .0;
            assert_ne!(
                head_key_v1, head_key_v2,
                "editing matched input_dir file must move git_head_tree_v11 cache key"
            );
            assert!(
                crate::gpu_fastcheck::evaluate_agent_step_value(
                    &mut store,
                    &file_b,
                    None,
                    Some(&canon_repo),
                    false,
                    false,
                )
                .is_err(),
                "agent-step must refresh Smoke.A after root input_dir edit and reject now-false theorem"
            );

            // Also verify the case where `Smoke` builds only `Smoke.A`, while `Smoke.B` belongs to
            // a separate library `Downstream` without `needs`, so `lake build Smoke` succeeds and
            // `evaluate_agent_step_value` returns `Ok(val)` with `verified == false`!
            let split_lib_lakefile = "import Lake\nopen Lake DSL\npackage demo\nrequire dep_pkg from \".lake/packages/dep_pkg\"\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n  text := true\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[smokeSources]\n@[default_target]\nlean_lib Downstream where\n  globs := #[.one `Smoke.B]\n";
            fs::write(canon_repo.join("lakefile.lean"), split_lib_lakefile)?;

            // Restore root input, re-warm, then test both root and dependency package (`dep_pkgs`)
            // `input_dir` edits under the split-library layout!
            fs::write(canon_repo.join("Data/a.sol"), root_v1)?;
            crate::module_builder::reset_lake_inputs_tag_memo();
            crate::lake_build::run_build_command(
                &mut store,
                true,
                Vec::new(),
                canon_repo.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;
            let step_restored = crate::gpu_fastcheck::evaluate_agent_step_value(
                &mut store,
                &file_b,
                None,
                Some(&canon_repo),
                false,
                false,
            )?;
            assert_eq!(step_restored["verified"], serde_json::json!(true));

            fs::write(canon_repo.join("Data/a.sol"), root_v2)?;
            crate::module_builder::reset_lake_inputs_tag_memo();
            assert!(
                crate::gpu_fastcheck::evaluate_agent_step_value(
                    &mut store,
                    &file_b,
                    None,
                    Some(&canon_repo),
                    false,
                    false,
                )
                .is_err(),
                "agent-step on Downstream/Smoke.B must refresh Smoke.A and fail closed on now-false theorem"
            );
            fs::write(canon_repo.join("Data/a.sol"), root_v1)?;
            crate::module_builder::reset_lake_inputs_tag_memo();
            crate::lake_build::run_build_command(
                &mut store,
                true,
                Vec::new(),
                canon_repo.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;

            fs::write(dep_dir.join("DepData/d.sol"), dep_v2)?;
            crate::module_builder::reset_lake_inputs_tag_memo();
            assert!(
                crate::gpu_fastcheck::evaluate_agent_step_value(
                    &mut store,
                    &file_b,
                    None,
                    Some(&canon_repo),
                    false,
                    false,
                )
                .is_err(),
                "agent-step must refresh dependency package DepMod after dep input_dir edit and fail closed"
            );
            crate::module_builder::reset_lake_inputs_tag_memo();
            assert!(
                crate::check::run_check_command(
                    &mut store,
                    false,
                    true,
                    file_b.clone(),
                    None,
                    canon_repo.clone(),
                    None,
                    false,
                    None,
                )
                .is_err(),
                "check must refresh dependency package DepMod and reject stale theorem"
            );

            // Finding 4: Unsupported `filter := .text` and missing `input_file` must fail closed
            // (`Err` / non-zero exit) across `agent-step`, `check`, `pr-verify`, `ci-verify`, and
            // `turbo-lean eval` CLI!
            fs::write(dep_dir.join("DepData/d.sol"), dep_v1)?;
            for bad_cfg in [
                "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .text\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A, .one `Smoke.B]\n  needs := #[smokeSources]\n",
                "import Lake\nopen Lake DSL\npackage demo\ninput_file missingCfg where\n  path := \"Data/does_not_exist.sol\"\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A, .one `Smoke.B]\n  needs := #[missingCfg]\n",
            ] {
                fs::write(canon_repo.join("lakefile.lean"), bad_cfg)?;
                crate::module_builder::reset_lake_inputs_tag_memo();
                assert!(
                    git_head_tree_cache_paths(&store, &canon_repo, &canon_repo, &head_sha, &tc)
                        .is_none(),
                    "git_head_tree_cache_paths must return None on unsupported/missing Lake input"
                );
                crate::module_builder::reset_lake_inputs_tag_memo();
                assert!(
                    crate::gpu_fastcheck::evaluate_agent_step_value(
                        &mut store,
                        &file_b,
                        None,
                        Some(&canon_repo),
                        false,
                        false,
                    )
                    .is_err(),
                    "agent-step must fail closed on unsupported/missing Lake input"
                );
                crate::module_builder::reset_lake_inputs_tag_memo();
                assert!(
                    crate::check::run_check_command(
                        &mut store,
                        false,
                        true,
                        file_b.clone(),
                        None,
                        canon_repo.clone(),
                        None,
                        false,
                        None,
                    )
                    .is_err(),
                    "check must fail closed on unsupported/missing Lake input"
                );
                crate::module_builder::reset_lake_inputs_tag_memo();
                assert!(
                    run_pr_verify_command(
                        &mut store,
                        true,
                        canon_repo.clone(),
                        "HEAD".to_string(),
                        "trusted".to_string(),
                        false,
                        None,
                        None,
                        None,
                        None,
                        false,
                        0,
                        None,
                    )
                    .is_err(),
                    "pr-verify must fail closed on unsupported/missing Lake input"
                );
                crate::module_builder::reset_lake_inputs_tag_memo();
                assert!(
                    run_ci_verify_command(
                        &mut store,
                        true,
                        "trusted".to_string(),
                        canon_repo.clone(),
                        None,
                        None,
                        false,
                        None,
                    )
                    .is_err(),
                    "ci-verify must fail closed on unsupported/missing Lake input"
                );
                if let Ok(exe) = std::env::current_exe() {
                    let turbo_bin = exe
                        .parent()
                        .and_then(|p| p.parent())
                        .map(|p| p.join("turbo-lean"))
                        .filter(|p| p.is_file());
                    if let Some(bin) = turbo_bin {
                        let eval_file = canon_repo.join("Smoke/PureEval.lean");
                        fs::write(&eval_file, "#eval 1 + 1\n")?;
                        let out = Command::new(bin)
                            .arg("--cache-dir")
                            .arg(&cache_dir)
                            .arg("eval")
                            .arg(&eval_file)
                            .arg("--project-dir")
                            .arg(&canon_repo)
                            .env("TURBO_LEAN_STAGING_DIR", &staging_dir)
                            .output()?;
                        assert!(
                            !out.status.success(),
                            "turbo-lean eval must fail closed on unsupported/missing Lake input: stdout={} stderr={}",
                            String::from_utf8_lossy(&out.stdout),
                            String::from_utf8_lossy(&out.stderr)
                        );
                    }
                }
            }

            Ok(())
        })();

        restore_env(&saved_staging, &saved_cache);
        let _ = fs::remove_dir_all(&tmp_dir);
        res
    }

    /// Round-5 regression suite covering:
    /// - Finding 1 ([P0]): `try_stateless_remote_check` refreshes stale imported `.olean`s on
    ///   Lake `input_dir` edits and fails closed (`Err`) on unsupported/missing Lake inputs.
    /// - Finding 2 ([P1]): `check` refreshes reverse dependents (`Downstream` `.olean`) after
    ///   an `input_dir` edit and after a directory-scoped `check <subdir>` nonlocal edit.
    /// - Finding 3 ([P1]): `evaluate_agent_step_value(..., project_dir = None)` walks up via
    ///   `find_project_root` from nested `Smoke/B.lean`, refreshes stale `Smoke.A`, and fails closed.
    /// - Finding 4 ([P2]): `pr-verify --base` resolves historical `input_file` / `input_dir`
    ///   from git at `--base` (including when a base `input_file` was deleted/renamed in HEAD
    ///   and when an `input_dir` edit leaves `.lean` sources byte-identical).
    #[test]
    fn test_round5_stateless_remote_reverse_deps_nested_agent_step_and_base_inputs() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let saved_staging = std::env::var("TURBO_LEAN_STAGING_DIR").ok();
        let saved_cache = std::env::var("TURBO_LEAN_CACHE_DIR").ok();
        let saved_token = std::env::var("TURBO_LEAN_API_TOKEN").ok();

        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_round5_lake_inputs_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let staging_dir = tmp_dir.join("staging");
        let cache_dir = tmp_dir.join("store");
        let remote_srv_dir = tmp_dir.join("remote_srv");
        fs::create_dir_all(&staging_dir)?;
        let api_tok = "round5-lake-inputs-token";
        std::env::set_var("TURBO_LEAN_STAGING_DIR", &staging_dir);
        std::env::set_var("TURBO_LEAN_CACHE_DIR", &cache_dir);
        std::env::set_var("TURBO_LEAN_API_TOKEN", api_tok);

        let restore_env = |saved_staging: &Option<String>,
                           saved_cache: &Option<String>,
                           saved_token: &Option<String>| {
            match saved_staging {
                Some(v) => std::env::set_var("TURBO_LEAN_STAGING_DIR", v),
                None => std::env::remove_var("TURBO_LEAN_STAGING_DIR"),
            }
            match saved_cache {
                Some(v) => std::env::set_var("TURBO_LEAN_CACHE_DIR", v),
                None => std::env::remove_var("TURBO_LEAN_CACHE_DIR"),
            }
            match saved_token {
                Some(v) => std::env::set_var("TURBO_LEAN_API_TOKEN", v),
                None => std::env::remove_var("TURBO_LEAN_API_TOKEN"),
            }
        };

        let res = (|| -> Result<()> {
            let repo_dir = tmp_dir.join("repo");
            fs::create_dir_all(repo_dir.join("Smoke"))?;
            fs::create_dir_all(repo_dir.join("Data"))?;
            fs::write(
                repo_dir.join("lean-toolchain"),
                include_str!("../../../lean/lean-toolchain"),
            )?;

            let split_lib_lakefile = "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n  text := true\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[smokeSources]\n@[default_target]\nlean_lib Downstream where\n  globs := #[.one `Smoke.B]\n";
            fs::write(repo_dir.join("lakefile.lean"), split_lib_lakefile)?;

            let v1 = "contract A {}\n";
            let v2 = "contract AMuchLonger {}\n";
            fs::write(repo_dir.join("Data/a.sol"), v1)?;
            fs::write(
                repo_dir.join("Smoke/A.lean"),
                "def solText : String := include_str \"../Data/a.sol\"\n",
            )?;
            fs::write(
                    repo_dir.join("Smoke/B.lean"),
                    format!(
                        "import Smoke.A\ntheorem useLen1 : solText.length = {} := by rfl\ntheorem useLen2 : solText.length + 0 = {} := by rfl\n",
                        v1.len(),
                        v1.len()
                    ),
                )?;

            if crate::module_builder::resolve_project_config(&repo_dir).is_err() {
                return Ok(());
            }

            git_init_and_commit(&repo_dir, "base")?;
            let canon_repo = fs::canonicalize(&repo_dir)?;
            let mut store = TurboStore::open(Some(&cache_dir))?;
            let _ = TurboStore::open(Some(&remote_srv_dir))?;
            let remote_url = format!(
                "http://{}",
                crate::pack::tests::spawn_authed_test_server(&remote_srv_dir, api_tok)?
            );

            // Warm build on v1.
            crate::module_builder::reset_lake_inputs_tag_memo();
            crate::lake_build::run_build_command(
                &mut store,
                true,
                Vec::new(),
                canon_repo.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;
            let file_a = canon_repo.join("Smoke/A.lean");
            let file_b = canon_repo.join("Smoke/B.lean");
            let olean_b = canon_repo.join(".lake/build/lib/lean/Smoke/B.olean");
            assert!(
                olean_b.is_file(),
                "Smoke/B.olean must exist after initial build"
            );

            // Warm stateless remote check on v1.
            let remote_v1_ok = crate::check::try_stateless_remote_check(
                &cache_dir,
                true,
                &file_b,
                None,
                &canon_repo,
                Some(2),
                &remote_url,
            )?;
            assert!(
                remote_v1_ok,
                "try_stateless_remote_check should verify eligible file on consistent v1 inputs"
            );

            // Finding 1 ([P0]) & Finding 3 ([P1]): Edit `Data/a.sol` -> `v2` while `Smoke/B.lean`
            // still expects `v1.len()`.
            // - `try_stateless_remote_check` must refresh `Smoke.A` and NOT return `Ok(true)`!
            // - `evaluate_agent_step_value(..., None, ...)` (omitted `--project-dir` on nested
            //   `Smoke/B.lean`) must discover `canon_repo`, refresh `Smoke.A`, and reject!
            fs::write(canon_repo.join("Data/a.sol"), v2)?;
            let remote_v2_res = crate::check::try_stateless_remote_check(
                &cache_dir,
                true,
                &file_b,
                None,
                &canon_repo,
                Some(2),
                &remote_url,
            );
            assert!(
                    !matches!(remote_v2_res, Ok(true)),
                    "try_stateless_remote_check must never report false green against stale Smoke/A.olean after input_dir edit: {remote_v2_res:?}"
                );
            let remote_single_v2_res = crate::check::try_stateless_remote_check(
                &cache_dir,
                true,
                &file_b,
                Some("useLen1"),
                &canon_repo,
                Some(1),
                &remote_url,
            );
            assert!(
                    !matches!(remote_single_v2_res, Ok(true)),
                    "try_stateless_remote_check (--decl) must never report false green after input_dir edit: {remote_single_v2_res:?}"
                );

            let nested_step_res = crate::gpu_fastcheck::evaluate_agent_step_value(
                &mut store, &file_b, None, None, false, false,
            );
            let nested_step_green = nested_step_res
                .as_ref()
                .is_ok_and(|v| v["verified"] == serde_json::json!(true));
            assert!(
                    !nested_step_green,
                    "agent-step with project_dir=None on nested Smoke/B.lean must walk up to project root, refresh Smoke.A, and reject stale theorem: {nested_step_res:?}"
                );

            // Finding 2a ([P1]): Update `Smoke/B.lean` to match `v2.len()`, then run
            // `check Smoke/A.lean`. Because `Data/a.sol` changed since the build manifest,
            // `recheck_dependents_if_nonlocal` must rebuild reverse dependent `Smoke/B.olean`!
            let olean_b_v1_bytes = fs::read(&olean_b)?;
            fs::write(
                    &file_b,
                    format!(
                        "import Smoke.A\ntheorem useLen1 : solText.length = {} := by rfl\ntheorem useLen2 : solText.length + 0 = {} := by rfl\n",
                        v2.len(),
                        v2.len()
                    ),
                )?;
            crate::check::run_check_command(
                &mut store,
                false,
                true,
                file_a.clone(),
                None,
                canon_repo.clone(),
                None,
                false,
                None,
            )?;
            assert_ne!(
                    fs::read(&olean_b)?,
                    olean_b_v1_bytes,
                    "checking Smoke/A.lean after input_dir edit must rebuild reverse-dependent Smoke/B.olean"
                );

            // Finding 2b ([P1]): Commit the consistent `v2` state, build warm, then make a
            // nonlocal declaration edit in `Smoke/A.lean` that breaks `Smoke/B.lean`, and run
            // directory-scoped `check Smoke` (only `Smoke/A.lean` is inside `Smoke/` if we move
            // `B` to `Other/C.lean`).
            fs::create_dir_all(canon_repo.join("Other"))?;
            fs::write(
                canon_repo.join("Other/C.lean"),
                format!(
                    "import Smoke.A\ntheorem downstreamC : solText.length = {} := by rfl\n",
                    v2.len()
                ),
            )?;
            let subdir_lakefile = "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n  text := true\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[smokeSources]\n@[default_target]\nlean_lib Downstream where\n  globs := #[.one `Smoke.B, .one `Other.C]\n";
            fs::write(canon_repo.join("lakefile.lean"), subdir_lakefile)?;
            let git_bin = crate::trusted_tools::git(&canon_repo)?;
            let _ = git_bin;
            let run_git = |args: &[&str]| -> Result<()> {
                let mut c = crate::trusted_tools::git(&canon_repo)?;
                let out = c.args(args).current_dir(&canon_repo).output()?;
                anyhow::ensure!(
                    out.status.success(),
                    "git {:?} failed: {}",
                    args,
                    String::from_utf8_lossy(&out.stderr)
                );
                Ok(())
            };
            run_git(&["add", "-A"])?;
            run_git(&["commit", "-m", "v2-with-other-c"])?;
            crate::module_builder::reset_lake_inputs_tag_memo();
            crate::lake_build::run_build_command(
                &mut store,
                true,
                Vec::new(),
                canon_repo.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;

            // Nonlocal edit in `Smoke/A.lean` (redefines `solText` to `"x"`), breaking `Other/C.lean`.
            // Directory-scoped `check Smoke` must invoke `recheck_dependents_if_nonlocal` and fail!
            fs::write(&file_a, "def solText : String := \"x\"\n")?;
            assert!(
                    crate::check::run_check_command(
                        &mut store,
                        false,
                        true,
                        canon_repo.join("Smoke"),
                        None,
                        canon_repo.clone(),
                        None,
                        false,
                        None,
                    )
                    .is_err(),
                    "directory-scoped `check Smoke` must recheck reverse dependents (Other/C.lean) on nonlocal edit in Smoke/A.lean"
                );
            // Restore `Smoke/A.lean` to HEAD.
            run_git(&["checkout", "--", "Smoke/A.lean"])?;

            // Finding 4 ([P2]) Case A: Pure `Data/a.sol` edit (`v2` -> `v1`) with `.lean` files
            // untouched since HEAD (`v2`). `pr-verify --base HEAD` must fail closed because
            // `Smoke/B.lean` & `Other/C.lean` assert `v2.len()`, not `v1.len()`!
            fs::write(canon_repo.join("Data/a.sol"), v1)?;
            assert!(
                    run_pr_verify_command(
                        &mut store,
                        true,
                        canon_repo.clone(),
                        "HEAD".to_string(),
                        "trusted".to_string(),
                        false,
                        None,
                        None,
                        None,
                        None,
                        false,
                        0,
                        None,
                    )
                    .is_err(),
                    "pr-verify --base HEAD must re-verify unchanged .lean files and fail when Data/a.sol edit breaks theorem"
                );

            // Finding 4 ([P2]) Case B: Base commit declares `input_file oldInput` (`Data/old.sol`),
            // and PR commit renames it to `input_file newInput` (`Data/new.sol`) and deletes
            // `Data/old.sol` from the working tree! `pr-verify --base HEAD~1` must read `Data/old.sol`
            // from `--base`'s git tree instead of failing with missing `Data/old.sol` on disk!
            fs::write(canon_repo.join("Data/a.sol"), v2)?;
            fs::write(canon_repo.join("Data/old.sol"), "old_payload\n")?;
            let base_input_file_lakefile = "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n  text := true\ninput_file oldInput where\n  path := \"Data/old.sol\"\n  text := true\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[smokeSources, oldInput]\n@[default_target]\nlean_lib Downstream where\n  globs := #[.one `Smoke.B, .one `Other.C]\n";
            fs::write(canon_repo.join("lakefile.lean"), base_input_file_lakefile)?;
            run_git(&["add", "-A"])?;
            run_git(&["commit", "-m", "base-with-old-input-file"])?;

            fs::remove_file(canon_repo.join("Data/old.sol"))?;
            fs::write(canon_repo.join("Data/new.sol"), "new_payload\n")?;
            let head_input_file_lakefile = "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n  text := true\ninput_file newInput where\n  path := \"Data/new.sol\"\n  text := true\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[smokeSources, newInput]\n@[default_target]\nlean_lib Downstream where\n  globs := #[.one `Smoke.B, .one `Other.C]\n";
            fs::write(canon_repo.join("lakefile.lean"), head_input_file_lakefile)?;
            run_git(&["add", "-A"])?;
            run_git(&["commit", "-m", "rename-old-input-file-to-new"])?;

            run_pr_verify_command(
                &mut store,
                true,
                canon_repo.clone(),
                "HEAD~1".to_string(),
                "trusted".to_string(),
                false,
                None,
                None,
                None,
                None,
                false,
                0,
                None,
            )
            .context(
                "pr-verify --base HEAD~1 must resolve deleted base input_file from git tree",
            )?;

            // Finding 1 ([P0]) & Finding 3 ([P1]) fail-closed check on unsupported Lake input:
            let bad_lakefile = "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .text\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[smokeSources]\n";
            fs::write(canon_repo.join("lakefile.lean"), bad_lakefile)?;
            assert!(
                crate::check::try_stateless_remote_check(
                    &cache_dir,
                    true,
                    &file_b,
                    None,
                    &canon_repo,
                    Some(2),
                    &remote_url,
                )
                .is_err(),
                "try_stateless_remote_check must propagate Err on unsupported filter := .text"
            );
            assert!(
                    crate::gpu_fastcheck::evaluate_agent_step_value(
                        &mut store,
                        &file_b,
                        None,
                        None,
                        false,
                        false,
                    )
                    .is_err(),
                    "evaluate_agent_step_value(..., project_dir=None) must propagate Err on unsupported filter := .text"
                );

            Ok(())
        })();

        restore_env(&saved_staging, &saved_cache, &saved_token);
        let _ = fs::remove_dir_all(&tmp_dir);
        res
    }

    /// Round 6 regression suite for `lean_exe` targets with `input_dir` / `needs` and downstream
    /// executable linking:
    /// 1. Direct `needs` on `lean_exe` (`lean_exe «my-driver» where root := `Main; needs := #[smokeSources]`):
    ///    - `turbo-lean build` + `lake build` links `.lake/build/bin/custom-driver` (`exeName`),
    ///      producing `"len=13\n"`.
    ///    - Editing `Data/a.sol` (13 -> 25 bytes) and running `turbo-lean check Other.lean`
    ///      (an unrelated theorem module in the same package) triggers
    ///      `recheck_dependents_if_nonlocal`, which rebuilds AND relinks `@my-pkg/my-driver:exe`
    ///      so executing `.lake/build/bin/custom-driver` immediately prints `"len=25\n"`!
    /// 2. Downstream `lean_exe` importing an input-bearing `lean_lib` (`Smoke.A`) AND sharing its
    ///    root module with an input-bearing `lean_lib` (`SharedMainLib` with `needs := #[smokeSources]`
    ///    vs `lean_exe «sub-exe»` without `needs`):
    ///    - Input edit in `Data/a.sol` followed by `turbo-lean check` refreshes `SharedMainLib`
    ///      **before** `@my-pkg/sub-exe:exe` (preventing Lake's job-memoization under an input-blind
    ///      `extraDep`) and relinks `.lake/build/bin/sub-exe` so running it prints the updated length!
    ///    - Nonlocal edit in `Smoke/A.lean` followed by `turbo-lean check Smoke/A.lean` relinks
    ///      downstream `.lake/build/bin/sub-exe` so running it reflects the nonlocal change!
    #[test]
    fn test_round6_lean_exe_needs_and_downstream_relink_regressions() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());

        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_round6_exe_regressions_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(&tmp_dir)?;

        let repo_dir = tmp_dir.join("repo");
        let cache_dir = tmp_dir.join("cache");
        let staging_dir = tmp_dir.join("staging");
        fs::create_dir_all(&repo_dir)?;
        fs::create_dir_all(&cache_dir)?;
        fs::create_dir_all(&staging_dir)?;

        let saved_staging = std::env::var("TURBO_LEAN_FAST_STAGING_DIR").ok();
        let saved_cache = std::env::var("TURBO_LEAN_CACHE_DIR").ok();
        let restore_env = |st: &Option<String>, ca: &Option<String>| {
            match st {
                Some(v) => std::env::set_var("TURBO_LEAN_FAST_STAGING_DIR", v),
                None => std::env::remove_var("TURBO_LEAN_FAST_STAGING_DIR"),
            }
            match ca {
                Some(v) => std::env::set_var("TURBO_LEAN_CACHE_DIR", v),
                None => std::env::remove_var("TURBO_LEAN_CACHE_DIR"),
            }
        };
        std::env::set_var("TURBO_LEAN_FAST_STAGING_DIR", &staging_dir);
        std::env::set_var("TURBO_LEAN_CACHE_DIR", &cache_dir);

        let res = (|| -> Result<()> {
            fs::create_dir_all(repo_dir.join("Data"))?;
            fs::create_dir_all(repo_dir.join("Smoke"))?;
            fs::write(
                repo_dir.join("lean-toolchain"),
                include_str!("../../../lean/lean-toolchain"),
            )?;

            // Hyphenated package name + hyphenated exe names + custom `exeName` + shared module
            // between input-bearing `SharedMainLib` (`needs := #[smokeSources]`) and `sub-exe`
            // (no `needs`, exercising the Lake job-memoization ordering hazard).
            let lakefile = r#"import Lake
open Lake DSL
package «my-pkg»

input_dir smokeSources where
  path := "Data"
  filter := .extension "sol"
  text := true

@[default_target]
lean_lib Smoke where
  globs := #[.one `Smoke.A]
  needs := #[smokeSources]

@[default_target]
lean_lib Other where
  globs := #[.one `Other]

@[default_target]
lean_lib SharedMainLib where
  globs := #[.one `SubMain]
  needs := #[smokeSources]

@[default_target]
lean_exe «my-driver» where
  root := `DriverMain
  exeName := "custom-driver"
  needs := #[smokeSources]

@[default_target]
lean_exe «sub-exe» where
  root := `SubMain
"#;
            fs::write(repo_dir.join("lakefile.lean"), lakefile)?;

            let v1 = "contract A {}";
            let v2 = "contract AMuchLongerName {}";
            assert_ne!(v1.len(), v2.len());
            fs::write(repo_dir.join("Data/a.sol"), v1)?;
            fs::write(
                repo_dir.join("Smoke/A.lean"),
                "def solA : String := include_str \"..\" / \"Data\" / \"a.sol\"\n",
            )?;
            fs::write(
                repo_dir.join("Other.lean"),
                "theorem otherOk : 1 + 1 = 2 := by rfl\n",
            )?;
            fs::write(
                repo_dir.join("DriverMain.lean"),
                "def directSol : String := include_str \"Data\" / \"a.sol\"\ndef main : IO Unit := IO.println s!\"direct={directSol.length}\"\n",
            )?;
            fs::write(
                repo_dir.join("SubMain.lean"),
                "import Smoke.A\ndef sharedSol : String := include_str \"Data\" / \"a.sol\"\ndef main : IO Unit := IO.println s!\"lib={solA.length},shared={sharedSol.length}\"\n",
            )?;

            git_init_and_commit(&repo_dir, "base")?;
            let canon_repo = repo_dir.canonicalize()?;
            if crate::module_builder::resolve_project_config(&canon_repo).is_err() {
                return Ok(());
            }

            // Initial Lake build to materialize `.lake/build/bin/custom-driver` and
            // `.lake/build/bin/sub-exe`, followed by `turbo-lean build` to stamp
            // `.turbo_verified_sources.json`.
            crate::lake_build::lake_build_modules(
                &canon_repo,
                &[
                    "Smoke".to_string(),
                    "Other".to_string(),
                    "SharedMainLib".to_string(),
                    "@my-pkg/my-driver:exe".to_string(),
                    "@my-pkg/sub-exe:exe".to_string(),
                ],
                None,
            )?;

            let mut store = TurboStore::open(Some(&cache_dir))?;
            crate::module_builder::reset_lake_inputs_tag_memo();
            crate::lake_build::run_build_command(
                &mut store,
                true,
                Vec::new(),
                canon_repo.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;

            let driver_bin = canon_repo.join(".lake/build/bin/custom-driver");
            let sub_bin = canon_repo.join(".lake/build/bin/sub-exe");
            assert!(driver_bin.is_file(), "custom-driver binary must exist");
            assert!(sub_bin.is_file(), "sub-exe binary must exist");

            let run_bin = |bin: &Path| -> Result<String> {
                let out = std::process::Command::new(bin)
                    .current_dir(&canon_repo)
                    .output()?;
                anyhow::ensure!(
                    out.status.success(),
                    "binary {} failed: {}",
                    bin.display(),
                    String::from_utf8_lossy(&out.stderr)
                );
                Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
            };

            assert_eq!(run_bin(&driver_bin)?, format!("direct={}", v1.len()));
            assert_eq!(
                run_bin(&sub_bin)?,
                format!("lib={},shared={}", v1.len(), v1.len())
            );

            // Case 1 & 2a: Edit `Data/a.sol` (`v1` -> `v2`) and run `turbo-lean check Other.lean`.
            // Even though `Other.lean` does not import `Smoke.A` or `DriverMain`, the workspace
            // Lake input changed since `.turbo_verified_sources.json`, so
            // `recheck_dependents_if_nonlocal` must rebuild AND relink both `custom-driver`
            // (direct `needs` on `lean_exe`) and `sub-exe` (downstream of `Smoke.A` + shared root
            // with `SharedMainLib` ordered before `@my-pkg/sub-exe:exe`).
            fs::write(canon_repo.join("Data/a.sol"), v2)?;
            crate::check::run_check_command(
                &mut store,
                false,
                true,
                canon_repo.join("Other.lean"),
                None,
                canon_repo.clone(),
                None,
                false,
                None,
            )?;
            assert_eq!(
                run_bin(&driver_bin)?,
                format!("direct={}", v2.len()),
                "direct-needs lean_exe binary custom-driver must be relinked after input_dir edit"
            );
            assert_eq!(
                run_bin(&sub_bin)?,
                format!("lib={},shared={}", v2.len(), v2.len()),
                "downstream + shared-root lean_exe binary sub-exe must be relinked with fresh SharedMainLib extraDep after input_dir edit"
            );

            // Commit the `v2` state and re-stamp `turbo-lean build`.
            let run_git = |args: &[&str]| -> Result<()> {
                let mut c = crate::trusted_tools::git(&canon_repo)?;
                let out = c.args(args).current_dir(&canon_repo).output()?;
                anyhow::ensure!(
                    out.status.success(),
                    "git {:?} failed: {}",
                    args,
                    String::from_utf8_lossy(&out.stderr)
                );
                Ok(())
            };
            run_git(&["add", "-A"])?;
            run_git(&["commit", "-m", "v2-state"])?;
            crate::module_builder::reset_lake_inputs_tag_memo();
            crate::lake_build::run_build_command(
                &mut store,
                true,
                Vec::new(),
                canon_repo.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;

            // Case 2b: Nonlocal edit in `Smoke/A.lean` (`solA := "hi"`) without touching `Data/a.sol`.
            // Running `turbo-lean check Smoke/A.lean` must recheck reverse dependents via
            // `lake_recheck_dependents` -> `lake_refresh_targets`, translating `SubMain` to
            // `@my-pkg/sub-exe:exe` (after `SharedMainLib`) so `.lake/build/bin/sub-exe` is relinked!
            fs::write(
                canon_repo.join("Smoke/A.lean"),
                "def solA : String := \"hi\"\n",
            )?;
            crate::check::run_check_command(
                &mut store,
                false,
                true,
                canon_repo.join("Smoke/A.lean"),
                None,
                canon_repo.clone(),
                None,
                false,
                None,
            )?;
            assert_eq!(
                run_bin(&sub_bin)?,
                format!("lib=2,shared={}", v2.len()),
                "downstream lean_exe binary sub-exe must be relinked after nonlocal edit in Smoke/A.lean"
            );

            // Case 3: Broken compilation inside `DriverMain.lean` after `Data/a.sol` edit causes
            // `turbo-lean check Other.lean` to fail closed!
            run_git(&["checkout", "--", "Smoke/A.lean"])?;
            fs::write(
                canon_repo.join("DriverMain.lean"),
                format!(
                    "def directSol : String := include_str \"Data\" / \"a.sol\"\ntheorem pinDriverLen : directSol.length = {} := by rfl\ndef main : IO Unit := IO.println s!\"direct={{directSol.length}}\"\n",
                    v2.len()
                ),
            )?;
            run_git(&["add", "-A"])?;
            run_git(&["commit", "-m", "pin-driver-v2"])?;
            crate::lake_build::lake_build_modules(
                &canon_repo,
                &["@my-pkg/my-driver:exe".to_string()],
                None,
            )?;
            crate::module_builder::reset_lake_inputs_tag_memo();
            crate::lake_build::run_build_command(
                &mut store,
                true,
                Vec::new(),
                canon_repo.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;

            // Mutate `Data/a.sol` back to `v1`, breaking `DriverMain.lean`'s `pinDriverLen`.
            // Both `check Other.lean` and `pr-verify --base HEAD` must fail closed!
            fs::write(canon_repo.join("Data/a.sol"), v1)?;
            assert!(
                crate::check::run_check_command(
                    &mut store,
                    false,
                    true,
                    canon_repo.join("Other.lean"),
                    None,
                    canon_repo.clone(),
                    None,
                    false,
                    None,
                )
                .is_err(),
                "check Other.lean must fail closed when input_dir edit breaks direct-needs lean_exe DriverMain"
            );
            assert!(
                run_pr_verify_command(
                    &mut store,
                    true,
                    canon_repo.clone(),
                    "HEAD".to_string(),
                    "trusted".to_string(),
                    false,
                    None,
                    None,
                    None,
                    None,
                    false,
                    0,
                    None,
                )
                .is_err(),
                "pr-verify --base HEAD must fail closed when input_dir edit breaks direct-needs lean_exe DriverMain"
            );

            Ok(())
        })();

        restore_env(&saved_staging, &saved_cache);
        let _ = fs::remove_dir_all(&tmp_dir);
        res
    }

    #[test]
    fn test_trusted_pr_verify_interface_change_replays_dependent_consumer_imports() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_pr_verify_trusted_closure_replay_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let proj = dir.join("proj");
        let dep_pkg = proj.join(".lake/packages/dep_pkg");
        fs::create_dir_all(proj.join("P"))?;
        fs::create_dir_all(dep_pkg.join("Dep"))?;
        let toolchain = include_str!("../../../lean/lean-toolchain");
        fs::write(proj.join("lean-toolchain"), toolchain)?;
        fs::write(dep_pkg.join("lean-toolchain"), toolchain)?;
        fs::write(dep_pkg.join("Dep/Bad.lean"), "import Init\n")?;
        fs::write(
            dep_pkg.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"Dep\"\nroots = [\"Dep.Bad\"]\n",
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep_pkg", "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml", "inherited": false}], "name": "proj", "lakeDir": ".lake", "fixedToolchain": false}"#,
        )?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"proj\"\ndefaultTargets = [\"P\"]\n[[require]]\nname = \"dep_pkg\"\npath = \".lake/packages/dep_pkg\"\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n",
        )?;
        fs::write(proj.join("P/A.lean"), "def k : Nat := 1\n")?;
        fs::write(
            proj.join("P/B.lean"),
            "import P.A\nimport Dep.Bad\ntheorem b_uses_dep : False := dep_forged_false\n",
        )?;

        let cfg = crate::module_builder::resolve_project_config(&proj)?;
        let lake_bin = cfg.lean_bin.parent().expect("lean bin parent").join("lake");
        let lake_dep = Command::new(&lake_bin)
            .args(["build", "Dep.Bad"])
            .current_dir(&dep_pkg)
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .output()?;
        anyhow::ensure!(
            lake_dep.status.success(),
            "lake build Dep.Bad: {} {}",
            String::from_utf8_lossy(&lake_dep.stdout),
            String::from_utf8_lossy(&lake_dep.stderr)
        );

        let maker_path = dir.join("Maker.lean");
        fs::write(
            &maker_path,
            "import Lean\nopen Lean\ndef main (args : List String) : IO Unit := do\n  searchPathRef.set [System.FilePath.mk args[1]!]\n  let env ← importModules #[{ module := `Init }] {} 0\n  let env := env.setMainModule `Dep.Bad\n  let decl : Declaration := .thmDecl {\n    name := `dep_forged_false,\n    levelParams := [],\n    type := mkConst ``False,\n    value := mkConst ``True.intro\n  }\n  match env.addDeclCore 0 0 decl none false with\n  | Except.ok env2 => writeModule env2 args[0]! false\n  | Except.error _ => throw <| IO.userError \"addDecl failed\"\n",
        )?;
        let forged_olean = dir.join("Bad.forged.olean");
        let compile_forged = Command::new(&cfg.lean_bin)
            .arg("--run")
            .arg(&maker_path)
            .arg(&forged_olean)
            .arg(&cfg.toolchain_lib_lean)
            .env("LEAN_PATH", &cfg.toolchain_lib_lean)
            .output()?;
        anyhow::ensure!(
            compile_forged.status.success(),
            "Maker.lean failed: {} {}",
            String::from_utf8_lossy(&compile_forged.stdout),
            String::from_utf8_lossy(&compile_forged.stderr)
        );
        let dep_lib_lean = dep_pkg.join(".lake/build/lib/lean");
        fs::copy(&forged_olean, dep_lib_lean.join("Dep/Bad.olean"))?;
        let new_h =
            crate::module_builder::lake_hash_bytes(&fs::read(dep_lib_lean.join("Dep/Bad.olean"))?);
        fs::write(
            dep_lib_lean.join("Dep/Bad.olean.hash"),
            format!("{:016x}\n", new_h),
        )?;
        let dep_trace_path = dep_lib_lean.join("Dep/Bad.trace");
        let mut dep_tv: serde_json::Value = serde_json::from_slice(&fs::read(&dep_trace_path)?)?;
        dep_tv["outputs"]["o"][0] = serde_json::Value::String(format!("{:016x}.olean", new_h));
        fs::write(&dep_trace_path, serde_json::to_vec(&dep_tv)?)?;

        let lake_proj = Command::new(&lake_bin)
            .args(["build", "P.A", "P.B"])
            .current_dir(&proj)
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .output()?;
        anyhow::ensure!(
            lake_proj.status.success(),
            "lake build P.A P.B: {} {}",
            String::from_utf8_lossy(&lake_proj.stdout),
            String::from_utf8_lossy(&lake_proj.stderr)
        );

        for args in [
            vec!["init"],
            vec!["config", "user.email", "test@example.com"],
            vec!["config", "user.name", "Test"],
            vec![
                "add",
                "lean-toolchain",
                "lakefile.toml",
                "lake-manifest.json",
                "P/A.lean",
                "P/B.lean",
            ],
            vec!["commit", "-m", "base"],
        ] {
            let g = Command::new("git")
                .args(&args)
                .current_dir(&proj)
                .output()?;
            anyhow::ensure!(
                g.status.success(),
                "git {:?}: {}",
                args,
                String::from_utf8_lossy(&g.stderr)
            );
        }

        // Interface change in `P/A.lean` (zero theorem shards in `P/A.lean`, `P/B.lean` untouched
        // in the diff): `lake_recheck_dependents` rebuilds `P.A` and consumer `P.B`, which imports
        // the forged Lake-built dependency `Dep.Bad`. Trusted `pr-verify` MUST kernel-replay the
        // closure's imported `.olean`s and reject `Dep.Bad` (`KernelReplay`), rather than skipping
        // `ensure_imported_oleans_replayed` on the `altered_interface_files` branch.
        fs::write(proj.join("P/A.lean"), "def k : Nat := 2\n")?;
        let mut store = TurboStore::open(Some(&dir.join("cache")))?;
        let pr_err = run_pr_verify_command(
            &mut store,
            true,
            proj.clone(),
            "HEAD".to_string(),
            "trusted".to_string(),
            false,
            None,
            None,
            None,
            None,
            false,
            1,
            None,
        )
        .unwrap_err();
        let err_msg = format!("{pr_err:#}");
        assert!(
            err_msg.contains("KernelReplay"),
            "trusted pr-verify on interface change with forged consumer dependency must fail KernelReplay, got: {err_msg}"
        );

        // Also test when the interface change itself has a theorem shard AND imports `Dep.Bad`:
        // `altered_interface_files` is non-empty, and trusted `pr-verify` must still reject via
        // `KernelReplay` before shard cache or statement checks.
        fs::write(
            proj.join("P/A.lean"),
            "import Dep.Bad\ndef k : Nat := 3\ntheorem a_thm : False := dep_forged_false\n",
        )?;
        let pr_err_direct = run_pr_verify_command(
            &mut store,
            true,
            proj.clone(),
            "HEAD".to_string(),
            "trusted".to_string(),
            false,
            None,
            None,
            None,
            None,
            false,
            1,
            None,
        )
        .unwrap_err();
        let err_direct_msg = format!("{pr_err_direct:#}");
        assert!(
            err_direct_msg.contains("KernelReplay"),
            "trusted pr-verify on interface change directly importing forged dependency must fail KernelReplay, got: {err_direct_msg}"
        );

        drop(store);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_statement_hash_lean_and_zygote_worker_statement_v1_parity() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_stmt_v1_parity_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        fs::write(
            dir.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"stmt_parity\"\ndefaultTargets = [\"ParityMod\"]\n[[lean_lib]]\nname = \"ParityMod\"\n",
        )?;
        let src = r#"namespace ParityNs
structure PairBox (α : Type u) where
  fst : α
  snd : Nat

theorem poly_proj_let.{u} {α : Type u} [Inhabited α] (b : PairBox α) :
    (let m : Nat := b.snd + 42; (m, "hello")) = (b.snd + 42, "hello") := rfl

private def localHidden : Nat := 7

theorem uses_local_private : localHidden = localHidden := rfl

theorem «a.b» : True := True.intro
namespace a
theorem b : False → True := fun h => False.elim h
end a
end ParityNs
"#;
        let mod_file = dir.join("ParityMod.lean");
        fs::write(&mod_file, src)?;
        stock_statement_build(&dir)?;

        // 1. Run `StatementHash.lean` against built `ParityMod.olean` and hash the `statement-v1` JSON.
        let helper = dir.join("DumpStmt.lean");
        fs::write(
            &helper,
            format!(
                "{}\ndef main := statementHashCliMain\n",
                include_str!("../../../lean/TurboLean/StatementHash.lean")
            ),
        )?;
        let dump_out = statement_lean_command(&dir, false)?
            .arg("--run")
            .arg(&helper)
            .arg("ParityMod")
            .output()?;
        assert!(
            dump_out.status.success(),
            "StatementHash.lean failed: {}",
            String::from_utf8_lossy(&dump_out.stderr)
        );
        fs::remove_file(&helper)?;
        let dump_str = std::str::from_utf8(&dump_out.stdout)?;
        let mut stmt_hash_from_dump = None;
        for line in dump_str.lines().filter(|l| !l.is_empty()) {
            let row: KernelDumpRow = serde_json::from_str(line)?;
            if row.theorem.as_deref() == Some("ParityNs.poly_proj_let") {
                let raw_stmt = raw_statement_payload(line, "statement")?;
                stmt_hash_from_dump = Some(blake3::hash(raw_stmt.as_bytes()).to_hex().to_string());
            }
        }
        let expected_hash =
            stmt_hash_from_dump.expect("theorem statement row in StatementHash.lean");

        // 2. Confirm `confirm_decl_identity_with_trust` (`ZygoteWorker.lean --decl-identity`)
        //    produces the exact same `statement-v1` BLAKE3 digest.
        let split = splitter::split_lean_source(src, &[]);
        let shard = split
            .shards
            .iter()
            .find(|s| s.decl_name().ends_with("poly_proj_let"))
            .expect("shard for poly_proj_let");
        let att =
            crate::check::confirm_decl_identity_with_trust(src, shard, &dir, &mod_file, false)?;
        assert_eq!(att.decl_name, "ParityNs.poly_proj_let");
        assert_eq!(att.kernel_type_hash, expected_hash);

        // 3. Private constant statement-hash parity across fresh probe nonces, single-decl check,
        //    and `.olean` shard audit (`4434869304`), plus lossless dotted guillemet `«a.b»` vs `a.b`
        //    separation (`4435128239`).
        let priv_shard = split
            .shards
            .iter()
            .find(|s| s.decl_name() == "ParityNs.uses_local_private")
            .expect("shard for uses_local_private");
        let att_priv_1 = crate::check::confirm_decl_identity_with_trust(
            src, priv_shard, &dir, &mod_file, false,
        )?;
        let att_priv_2 = crate::check::confirm_decl_identity_with_trust(
            src, priv_shard, &dir, &mod_file, false,
        )?;
        assert_eq!(
            att_priv_1.kernel_type_hash, att_priv_2.kernel_type_hash,
            "local private constant statement hash must be invariant across probe nonces"
        );
        let cache_dir = dir.join("cache");
        let mut store = TurboStore::open(Some(&cache_dir))?;
        let check_priv = crate::check::evaluate_check_command_value(
            &mut store,
            mod_file.clone(),
            Some("ParityNs.uses_local_private".to_string()),
            dir.clone(),
        )?;
        assert_eq!(check_priv["status"], "theorem_verified");

        let guil_shard = split
            .shards
            .iter()
            .find(|s| s.decl_name() == "ParityNs.«a.b»")
            .expect("shard for «a.b»");
        let plain_shard = split
            .shards
            .iter()
            .find(|s| s.decl_name() == "ParityNs.a.b")
            .expect("shard for a.b");
        let att_guil = crate::check::confirm_decl_identity_with_trust(
            src, guil_shard, &dir, &mod_file, false,
        )?;
        let att_plain = crate::check::confirm_decl_identity_with_trust(
            src,
            plain_shard,
            &dir,
            &mod_file,
            false,
        )?;
        assert_eq!(att_guil.decl_name, "ParityNs.«a.b»");
        assert_eq!(att_plain.decl_name, "ParityNs.a.b");
        assert_ne!(att_guil.kernel_type_hash, att_plain.kernel_type_hash);
        let check_guil = crate::check::evaluate_check_command_value(
            &mut store,
            mod_file.clone(),
            Some("ParityNs.«a.b»".to_string()),
            dir.clone(),
        )?;
        assert_eq!(check_guil["status"], "theorem_verified");

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_pr_verify_rejects_unchanged_non_default_zero_shard_forged_module_and_emits_no_receipt(
    ) -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_pr_verify_unchanged_nondefault_forged_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let proj = dir.join("proj");
        fs::create_dir_all(&proj)?;
        let toolchain = include_str!("../../../lean/lean-toolchain");
        fs::write(proj.join("lean-toolchain"), toolchain)?;
        fs::write(proj.join(".gitignore"), ".lake/\n")?;
        fs::write(
            proj.join("lakefile.toml"),
            concat!(
                "name = \"proj\"\n",
                "defaultTargets = [\"MainLib\"]\n",
                "[[lean_lib]]\nname = \"MainLib\"\nroots = [\"MainLib\"]\n",
                "[[lean_lib]]\nname = \"HiddenLib\"\nroots = [\"HiddenLib\"]\n",
            ),
        )?;
        fs::write(
            proj.join("MainLib.lean"),
            "theorem main_ok : (1 : Nat) = 1 := rfl\n",
        )?;
        fs::write(
            proj.join("HiddenLib.lean"),
            concat!(
                "import Lean\n",
                "open Lean Elab Command in\n",
                "elab \"forge_bad\" : command => do\n",
                "  let d : Declaration := .defnDecl {\n",
                "    name := `HiddenLib.forged_false,\n",
                "    levelParams := [],\n",
                "    type := mkConst ``False,\n",
                "    value := mkConst ``True.intro,\n",
                "    hints := .opaque,\n",
                "    safety := .safe\n",
                "  }\n",
                "  liftCoreM do\n",
                "    match (← getEnv).addDeclCore 0 0 d none false with\n",
                "    | .ok env' => setEnv env'\n",
                "    | .error _ => throwError \"addDeclCore failed\"\n",
                "forge_bad\n",
            ),
        )?;
        git_init_and_commit(&proj, "base with unchanged non-default 0-shard forged lib")?;
        fs::write(
            proj.join("MainLib.lean"),
            "theorem main_ok : (1 : Nat) = 1 := by rfl\n",
        )?;

        let receipt_path = dir.join("receipt.json");
        let mut store = TurboStore::open(Some(&dir.join("cache")))?;
        let err = run_pr_verify_command(
            &mut store,
            true,
            proj.clone(),
            "HEAD".to_string(),
            "trusted".to_string(),
            false,
            Some(receipt_path.clone()),
            None,
            None,
            None,
            false,
            1,
            None,
        )
        .unwrap_err();
        let err_msg = format!("{err:#}");
        assert!(
            err_msg.contains("KernelReplay") || err_msg.contains("kernel replay"),
            "trusted pr-verify must fail-closed on unchanged non-default 0-shard forged module, got: {err_msg}"
        );
        assert!(
            !receipt_path.exists(),
            "pr-verify must not emit a receipt when unchanged non-default module fails kernel replay"
        );

        fs::write(
            proj.join("HiddenLib.lean"),
            "set_option debug.skipKernelTC true\ndef bad_def : True := True.intro\n",
        )?;
        fs::write(
            proj.join("MainLib.lean"),
            "theorem main_ok : (1 : Nat) = 1 := rfl\n",
        )?;
        git_init_and_commit(&proj, "base with unchanged non-default skipKernelTC")?;
        fs::write(
            proj.join("MainLib.lean"),
            "theorem main_ok : (1 : Nat) = 1 := by rfl\n",
        )?;
        let err_hyg = run_pr_verify_command(
            &mut store,
            true,
            proj.clone(),
            "HEAD".to_string(),
            "trusted".to_string(),
            false,
            Some(receipt_path.clone()),
            None,
            None,
            None,
            false,
            1,
            None,
        )
        .unwrap_err();
        let err_hyg_msg = format!("{err_hyg:#}");
        assert!(
            err_hyg_msg.contains("Soundness hygiene violation")
                && err_hyg_msg.contains("HiddenLib.lean"),
            "trusted pr-verify must fail-closed on unchanged non-default checking-weakening directive, got: {err_hyg_msg}"
        );
        assert!(
            !receipt_path.exists(),
            "pr-verify must not emit a receipt when unchanged non-default module fails source hygiene"
        );

        drop(store);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_pr_verify_and_check_reject_kernel_type_mismatch_fail_closed() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_kth_mismatch_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        let cache_dir = dir.join("cache");
        let mut store = TurboStore::open(Some(&cache_dir))?;
        fs::write(
            dir.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"kth_mismatch\"\ndefaultTargets = [\"Demo\"]\n[[lean_lib]]\nname = \"Demo\"\n",
        )?;
        fs::write(dir.join(".gitignore"), ".lake/\ncache/\n")?;

        let base_src =
            "namespace Demo\ntheorem thm (n : Nat) : n = n := by\n  exact rfl\nend Demo\n";
        let edited_src = "namespace Demo\ntheorem thm (n : Nat) : n = n := by\n  rfl\nend Demo\n";
        let demo_file = dir.join("Demo.lean");
        fs::write(&demo_file, base_src)?;
        git_init_and_commit(&dir, "base")?;
        let base_rev = String::from_utf8(
            Command::new("git")
                .arg("-C")
                .arg(&dir)
                .args(["rev-parse", "HEAD"])
                .output()?
                .stdout,
        )?
        .trim()
        .to_string();

        fs::write(&demo_file, edited_src)?;
        let toolchain = detect_toolchain(&dir);
        let split = splitter::split_lean_source(edited_src, &[]);
        let shard = &split.shards[0];
        let shard_key = crate::lake_build::compute_shard_key(&toolchain, shard);

        // 1. Direct `verify_attested_decl_types` and `verify_zygote_reply_decl_types` fail closed
        //    on mismatched kernel type hash, missing declaration, or cross-namespace `_turbo_verify_`.
        let mut fake_types = std::collections::BTreeMap::new();
        fake_types.insert("Demo.thm".to_string(), "1111".to_string());
        assert!(crate::zygote::verify_attested_decl_types(
            &fake_types,
            &[("Demo.thm".to_string(), "2222".to_string())]
        )
        .is_err());
        let mut cross_ns_types = std::collections::BTreeMap::new();
        cross_ns_types.insert("Other._turbo_verify_0_thm".to_string(), "2222".to_string());
        assert!(crate::zygote::verify_attested_decl_types(
            &cross_ns_types,
            &[("Demo.thm".to_string(), "2222".to_string())]
        )
        .is_err());
        let mut valid_fast_types = std::collections::BTreeMap::new();
        valid_fast_types.insert("Demo._turbo_verify_0_thm".to_string(), "2222".to_string());
        assert!(crate::zygote::verify_attested_decl_types(
            &valid_fast_types,
            &[("Demo.thm".to_string(), "2222".to_string())]
        )
        .is_ok());

        // 2. Poison the CAS under `shard_key` with a wrong `kernel_type_hash` receipt and assert
        //    `has_attested_decl_receipt` rejects it and `pr-verify` invalidates + re-verifies
        //    instead of trusting the poisoned cache entry.
        let wrong_receipt = crate::check::make_attested_shard_receipt_bytes(
            "Demo.thm",
            &shard.prefix_env_hash,
            &shard.stmt_hash,
            &shard.proof_hash,
            1,
            Some("deadbeef"),
        )?;
        store.batch_publish_theorem_shards(
            &toolchain,
            "trusted",
            &[(shard_key.clone(), "Demo.thm".to_string(), wrong_receipt, 1)],
        )?;
        let real_att = crate::check::confirm_decl_identity_with_trust(
            edited_src, shard, &dir, &demo_file, false,
        )?;
        assert!(!store.has_attested_decl_receipt(
            &shard_key,
            "trusted",
            "Demo.thm",
            &real_att.kernel_type_hash
        ));

        let receipt_path = dir.join("receipt.json");
        let cap_err = run_pr_verify_command(
            &mut store,
            true,
            dir.clone(),
            base_rev.clone(),
            "trusted".to_string(),
            true,
            Some(receipt_path.clone()),
            None,
            None,
            None,
            false,
            0,
            None,
        );
        cap_err?;
        assert!(
            store.has_attested_decl_receipt(
                &shard_key,
                "trusted",
                "Demo.thm",
                &real_att.kernel_type_hash
            ),
            "pr-verify must invalidate the poisoned receipt and publish a freshly attested receipt"
        );
        assert!(!store.has_attested_decl_receipt(&shard_key, "trusted", "Demo.thm", "deadbeef"));

        // 3. `to_batch_req_item` preserves the full root-anchored namespace-qualified declaration name.
        let ns_split = splitter::split_lean_source(
            "namespace Outer.Inner\ntheorem same_name : True := True.intro\nend Outer.Inner\n",
            &[],
        );
        let ns_item = to_batch_req_item(&(
            "ns-key".to_string(),
            ns_split.shards[0].clone(),
            "abcd".repeat(16),
        ));
        assert_eq!(ns_item.decl_name, "_root_.Outer.Inner.same_name");

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_pr_verify_standalone_dependents_and_sibling_imports_across_modes() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_pr_verify_standalone_and_sibling_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let proj = dir.join("proj");
        fs::create_dir_all(proj.join("P"))?;
        let toolchain = include_str!("../../../lean/lean-toolchain");
        fs::write(proj.join("lean-toolchain"), toolchain)?;
        fs::write(proj.join(".gitignore"), ".lake/\n")?;
        // Library `P` uses submodules glob `P.*`, so root-level `Standalone.lean` is NOT a Lake target.
        fs::write(
            proj.join("lakefile.lean"),
            concat!(
                "import Lake\nopen Lake DSL\n",
                "package «proj»\n",
                "@[default_target]\n",
                "lean_lib «P» where\n",
                "  globs := #[.submodules `P]\n",
            ),
        )?;
        fs::write(proj.join("P/A.lean"), "def k : Nat := 1\n")?;
        fs::write(proj.join("P/C.lean"), "def c_val : Nat := 7\n")?;
        fs::write(
            proj.join("P/D.lean"),
            "import P.C\ntheorem d_thm : c_val = 7 := by decide\n",
        )?;
        fs::write(
            proj.join("Standalone.lean"),
            "import P.A\ndef use_k : Nat := k + 1\ntheorem standalone_ok : use_k = 2 := rfl\n",
        )?;
        // Umbrella root `P.lean` is ALSO standalone (`globs := #[.submodules `P]`) and shares top-level
        // module prefix `P` with target submodule `P/A.lean` (`SearchPath.findWithExt` prefix-pinning case).
        fs::write(
            proj.join("P.lean"),
            "import P.A\nimport P.C\ndef root_sum : Nat := k + c_val\n",
        )?;
        git_init_and_commit(&proj, "base with standalone module and sibling modules")?;

        let fake_bwrap =
            crate::module_builder::ScopedTestBwrapOverride::write_fake_bwrap_script(&dir)?;
        let _bwrap =
            crate::module_builder::ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy());
        let mut store = TurboStore::open(Some(&dir.join("cache")))?;

        let run_mode = |store: &mut TurboStore, mode: &str| {
            run_pr_verify_command(
                store,
                true,
                proj.clone(),
                "HEAD".to_string(),
                mode.to_string(),
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

        // 1. Non-local interface edit in `P/A.lean` (`k : Nat := 2`) breaks untouched `Standalone.lean`
        // (`use_k = 2` fails `rfl`) while sibling `P/D.lean` has a local proof edit importing `P.C`.
        // Both trusted and untrusted modes must reject because `Standalone.lean` is in the dependent closure.
        fs::write(proj.join("P/A.lean"), "def k : Nat := 2\n")?;
        fs::write(
            proj.join("P/D.lean"),
            "import P.C\ntheorem d_thm : c_val = 7 := rfl\n",
        )?;
        for mode in ["trusted", "untrusted"] {
            let err = format!("{:#}", run_mode(&mut store, mode).unwrap_err());
            assert!(
                err.contains("Standalone") || err.contains("standalone_ok"),
                "{mode} pr-verify must reject broken untouched standalone dependent: {err}"
            );
        }

        // 2. Fix `Standalone.lean` so the closure is valid, while `P/A.lean` still has a non-local edit
        // AND `P/D.lean` has a local proof edit importing unbuilt sibling `P.C` (outside `P.A`'s closure).
        // Both modes must build `P.C` and pass cleanly!
        let _ = fs::remove_dir_all(proj.join(".lake/build"));
        fs::write(
            proj.join("Standalone.lean"),
            "import P.A\ndef use_k : Nat := k + 1\ntheorem standalone_ok : use_k = 3 := rfl\n",
        )?;
        for mode in ["untrusted", "trusted"] {
            let _ = fs::remove_dir_all(proj.join(".lake/build"));
            let mut fresh_store = TurboStore::open(Some(&dir.join(format!("cache_pass_{mode}"))))?;
            run_mode(&mut fresh_store, mode).unwrap_or_else(|e| {
                panic!(
                    "{mode} pr-verify must build sibling import P.C alongside non-local edit in P/A.lean: {e:#}"
                )
            });
        }

        // 3. Direct 0-shard non-local broken edit in `Standalone.lean` alone (e.g. ill-typed `def` or forged `addDeclCore`)
        // must be rejected in both trusted and untrusted modes even though `Standalone.lean` has 0 theorem shards.
        fs::write(proj.join("P/A.lean"), "def k : Nat := 1\n")?;
        fs::write(
            proj.join("P/D.lean"),
            "import P.C\ntheorem d_thm : c_val = 7 := by decide\n",
        )?;
        fs::write(
            proj.join("Standalone.lean"),
            "import P.A\ndef broken_standalone : Nat := \"not a nat\"\n",
        )?;
        for mode in ["trusted", "untrusted"] {
            let err = format!("{:#}", run_mode(&mut store, mode).unwrap_err());
            assert!(
                err.contains("Standalone"),
                "{mode} pr-verify must reject 0-shard broken standalone edit: {err}"
            );
        }

        // Forged 0-shard standalone declaration via `addDeclCore` must be caught by kernel replay / audit.
        fs::write(
            proj.join("Standalone.lean"),
            concat!(
                "import Lean\nopen Lean Elab Command in\n",
                "elab \"forge_standalone\" : command => do\n",
                "  let d : Declaration := .defnDecl {\n",
                "    name := `Standalone.forged_false,\n",
                "    levelParams := [],\n",
                "    type := mkConst ``False,\n",
                "    value := mkConst ``True.intro,\n",
                "    hints := .opaque,\n",
                "    safety := .safe\n",
                "  }\n",
                "  liftCoreM do\n",
                "    match (← getEnv).addDeclCore 0 0 d none false with\n",
                "    | .ok env' => setEnv env'\n",
                "    | .error _ => throwError \"addDeclCore failed\"\n",
                "forge_standalone\n",
            ),
        )?;
        for mode in ["trusted", "untrusted"] {
            let err = format!("{:#}", run_mode(&mut store, mode).unwrap_err());
            assert!(
                err.contains("KernelReplay")
                    || err.contains("kernel replay")
                    || err.contains("forged_false"),
                "{mode} pr-verify must reject 0-shard forged standalone module: {err}"
            );
        }

        // 4. Standalone module `Consumer.lean` importing standalone root umbrella `P.lean` (`import P`)
        // alongside target submodule `P/A.lean` (`P.olean` + `P/A.olean` prefix-pinning case).
        fs::write(
            proj.join("Standalone.lean"),
            "import P.A\ndef use_k : Nat := k + 1\ntheorem standalone_ok : use_k = 2 := rfl\n",
        )?;
        fs::write(
            proj.join("Consumer.lean"),
            "import P\ntheorem consumer_thm : root_sum = 8 := rfl\n",
        )?;
        for mode in ["trusted", "untrusted"] {
            let _ = fs::remove_dir_all(proj.join(".lake/build"));
            let mut fresh_store =
                TurboStore::open(Some(&dir.join(format!("cache_umbrella_{mode}"))))?;
            run_mode(&mut fresh_store, mode).unwrap_or_else(|e| {
                panic!(
                    "{mode} pr-verify must resolve standalone umbrella `P.lean` alongside `P/A.lean` and `P/C.lean`: {e:#}"
                )
            });
        }

        drop(store);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_optout_trusted_pr_verify_with_nonlocal_leaf_still_rejects_stale_sibling_import(
    ) -> Result<()> {
        use crate::worktree_test_support::{assert_stale_error, snapshot, LakeTree};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::new(
            "stale_pr_with_nonlocal",
            &[
                ("P/A.lean", "def a : Nat := 1\n"),
                ("P/Middle.lean", "import P.A\ndef mid : Nat := a\n"),
                (
                    "P/Target.lean",
                    "import P.Middle\ntheorem target : a = 1 := rfl\n",
                ),
                ("StandaloneLeaf.lean", "def leaf : Nat := 10\n"),
            ],
        )?;
        // Restrict `P` to submodules `P.*` so `StandaloneLeaf.lean` is standalone (zero Lake targets in closure),
        // ensuring `altered_interface_files` is non-empty without failing `lake_build_modules` first,
        // and verify `ensure_project_imports_fresh_for_check` still catches stale `P.A` while preserving `.lake`.
        fs::write(
            tree.project.join("lakefile.lean"),
            concat!(
                "import Lake\nopen Lake DSL\n",
                "package «p»\n",
                "@[default_target]\n",
                "lean_lib «P» where\n",
                "  globs := #[.submodules `P]\n",
            ),
        )?;
        tree.opt_out()?;
        git_init_and_commit(&tree.project, "base")?;
        tree.stale_import()?;
        fs::write(
            tree.project.join("StandaloneLeaf.lean"),
            "def leaf : Nat := 11\n",
        )?;
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
    fn test_untrusted_pr_verify_altered_interface_with_lean_exe_and_manifest_renamed_dep(
    ) -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_pr_verify_exe_and_renamed_dep_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let proj = dir.join("proj");
        let dep_dir = proj.join("deps/dep_orig_dir");
        fs::create_dir_all(proj.join("App"))?;
        fs::create_dir_all(dep_dir.join("DepLib"))?;
        fs::create_dir_all(dep_dir.join("Data"))?;

        let toolchain = include_str!("../../../lean/lean-toolchain");
        fs::write(proj.join("lean-toolchain"), toolchain)?;
        fs::write(proj.join(".gitignore"), ".lake/\n")?;

        fs::write(dep_dir.join("Data/info.txt"), "v1\n")?;
        fs::write(
            dep_dir.join("lakefile.lean"),
            concat!(
                "import Lake\nopen Lake DSL\n",
                "package «dep_orig»\n",
                "input_dir depData where\n  path := \"Data\"\n",
                "lean_lib «DepLib» where\n  globs := #[.submodules `DepLib]\n  needs := #[depData]\n",
                "lean_exe «dep-tool» where\n  root := `DepMain\n  needs := #[depData]\n",
            ),
        )?;
        fs::write(dep_dir.join("DepLib/Core.lean"), "def depVal : Nat := 10\n")?;
        fs::write(
            dep_dir.join("DepMain.lean"),
            "import DepLib.Core\ndef main : IO Unit := IO.println s!\"{depVal}\"\n",
        )?;

        fs::write(
            proj.join("lake-manifest.json"),
            r#"{
  "version": "1.1.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {"type": "path", "scope": "", "name": "«dep-alias»", "inherited": false, "dir": "deps/dep_orig_dir", "configFile": "lakefile.lean"}
  ]
}
"#,
        )?;
        fs::write(
            proj.join("lakefile.lean"),
            concat!(
                "import Lake\nopen Lake DSL\n",
                "package «my-proofs»\n",
                "require «dep-alias» from \"deps\" / \"dep_orig_dir\"\n",
                "@[default_target]\n",
                "lean_lib «App» where\n",
                "  globs := #[.submodules `App]\n",
                "@[default_target]\n",
                "lean_exe «turbo-zygote» where\n",
                "  root := `ZygoteMain\n",
            ),
        )?;
        fs::write(
            proj.join("App/Base.lean"),
            "import DepLib.Core\ndef baseVal : Nat := depVal + 1\ntheorem base_ok : baseVal = 11 := rfl\n",
        )?;
        fs::write(
            proj.join("ZygoteMain.lean"),
            "import App.Base\ndef main : IO Unit := IO.println s!\"{baseVal}\"\n",
        )?;
        git_init_and_commit(&proj, "base with lean_exe and manifest-renamed dep")?;

        let canon_proj = proj.canonicalize()?;
        let cfg = crate::module_builder::resolve_project_config_with_trust(&canon_proj, true)?;
        assert_eq!(cfg.dep_pkgs.len(), 1);
        assert_eq!(cfg.dep_pkgs[0].name, "dep_orig");
        assert_eq!(cfg.dep_pkgs[0].base_name, "dep-alias");
        assert_eq!(
            crate::module_builder::input_bearing_libs_for_module(&cfg, "DepLib.Core"),
            vec!["dep-alias/DepLib".to_string()]
        );
        assert_eq!(
            crate::module_builder::exe_targets_for_module(&cfg, "DepMain"),
            vec!["@dep-alias/dep-tool:exe".to_string()]
        );
        assert_eq!(
            crate::module_builder::input_bearing_exes_for_module(&cfg, "DepMain"),
            vec!["@dep-alias/dep-tool:exe".to_string()]
        );
        assert_eq!(
            crate::module_builder::exe_targets_for_module(&cfg, "ZygoteMain"),
            vec!["@my-proofs/turbo-zygote:exe".to_string()]
        );
        crate::module_builder::build_module_dag_with_trust(
            &cfg,
            &[
                "dep-alias/DepLib".to_string(),
                "@dep-alias/dep-tool:default".to_string(),
                "@my-proofs/turbo-zygote:default".to_string(),
            ],
            true,
        )?;

        let fake_bwrap =
            crate::module_builder::ScopedTestBwrapOverride::write_fake_bwrap_script(&dir)?;
        let _bwrap =
            crate::module_builder::ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy());
        let mut store = TurboStore::open(Some(&dir.join("cache")))?;

        let exe_err = crate::module_builder::build_project_modules_native(
            &mut store,
            &canon_proj,
            &["turbo-zygote:exe".to_string()],
            "untrusted-pr",
            1,
            true,
            true,
            None,
        )
        .unwrap_err()
        .to_string();
        assert!(
            exe_err.contains("fail-closed"),
            "direct `:exe` facet on build_project_modules_native must still fail closed: {exe_err}"
        );

        fs::write(
            proj.join("App/Base.lean"),
            "import DepLib.Core\ndef baseVal : Nat := depVal + 1\ndef extraHelper : Nat := baseVal + 2\ntheorem base_ok : baseVal = 11 := rfl\ntheorem extra_ok : extraHelper = 13 := rfl\n",
        )?;
        run_pr_verify_command(
            &mut store,
            true,
            proj.clone(),
            "HEAD".to_string(),
            "untrusted".to_string(),
            false,
            None,
            None,
            None,
            None,
            false,
            0,
            None,
        )?;

        drop(store);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_pr_verify_proof_only_edit_on_stock_olean_build_uses_fast_olean_without_lake_mutation(
    ) -> Result<()> {
        use crate::worktree_test_support::{snapshot, LakeTree};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::new(
            "pr_verify_proof_only_stock_olean",
            &[
                ("P/Dep.lean", "def baseVal : Nat := 7\n"),
                (
                    "P/Target.lean",
                    "import P.Dep\ntheorem first_thm : baseVal = 7 := rfl\ntheorem edited_thm : baseVal + 0 = 7 := by\n  exact rfl\n",
                ),
            ],
        )?;
        let _ = fs::remove_dir_all(tree.project.join(".lake/build"));
        git_init_and_commit(&tree.project, "base")?;
        // Build artifacts with stock Lake and strip `.c` sidecars (emulating `:olean`-only CI cache without `.c` or `.turbo_verified_sources.json`).
        tree.lake(&["build", "P"])?;
        let _ = fs::remove_dir_all(tree.project.join(".lake/build/ir"));
        assert!(!tree
            .project
            .join(".lake/build/.turbo_verified_sources.json")
            .exists());
        assert!(!tree
            .project
            .join(".lake/build/.turbo_publish.lock")
            .exists());
        assert!(!tree.project.join(".lake/build/ir/P/Target.c").exists());

        // Apply a pure proof edit in P/Target.lean.
        fs::write(
            tree.project.join("P/Target.lean"),
            "import P.Dep\ntheorem first_thm : baseVal = 7 := rfl\ntheorem edited_thm : baseVal + 0 = 7 := by\n  have _noop : True := trivial\n  exact rfl\n",
        )?;
        let before_lake = snapshot(&tree.project)?;
        let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
        let hits0 = HEAD_OVERLAY_HITS.load(std::sync::atomic::Ordering::SeqCst);
        run_pr_verify_command(
            &mut store,
            true,
            tree.project.clone(),
            "HEAD".into(),
            "trusted".into(),
            true,
            None,
            None,
            None,
            None,
            false,
            0,
            None,
        )?;
        assert_eq!(
            HEAD_OVERLAY_HITS.load(std::sync::atomic::Ordering::SeqCst),
            hits0 + 1,
            "first proof-only edit on multi-module package must succeed via try_head_overlay without falling back to make_head_snapshot"
        );
        // `.lake` must remain completely untouched (including zero `.turbo_publish.lock` creation).
        assert_eq!(snapshot(&tree.project)?, before_lake);
        // Base replay authority must now be persisted so `resolve_replayed_proof_only_module_import` resolves `P.Target` ONLY for the base source (not mismatched source).
        let base_target_src =
            "import P.Dep\ntheorem first_thm : baseVal = 7 := rfl\ntheorem edited_thm : baseVal + 0 = 7 := by\n  exact rfl\n";
        assert_eq!(
            crate::lake_build::resolve_replayed_proof_only_module_import(
                &store,
                &tree.project,
                &tree.project.join("P/Target.lean"),
                base_target_src,
            )
            .as_deref(),
            Some("P.Target")
        );
        assert_eq!(
            crate::lake_build::resolve_replayed_proof_only_module_import(
                &store,
                &tree.project,
                &tree.project.join("P/Target.lean"),
                "import P.Dep\ntheorem tampered : baseVal = 7 := rfl\n",
            ),
            None
        );

        // Apply a second pure proof edit to exercise the warm base-report + fast_olean path.
        fs::write(
            tree.project.join("P/Target.lean"),
            "import P.Dep\ntheorem first_thm : baseVal = 7 := rfl\ntheorem edited_thm : baseVal + 0 = 7 := by\n  have _noop2 : True := trivial\n  exact rfl\n",
        )?;
        run_pr_verify_command(
            &mut store,
            true,
            tree.project.clone(),
            "HEAD".into(),
            "trusted".into(),
            true,
            None,
            None,
            None,
            None,
            false,
            0,
            None,
        )?;
        assert_eq!(
            HEAD_OVERLAY_HITS.load(std::sync::atomic::Ordering::SeqCst),
            hits0 + 2,
            "second warm proof-only edit must also succeed via try_head_overlay"
        );
        assert_eq!(snapshot(&tree.project)?, before_lake);
        Ok(())
    }

    #[test]
    fn test_pr_verify_proof_only_edit_removing_base_sorry_clears_stale_audit() -> Result<()> {
        use crate::worktree_test_support::{snapshot, LakeTree};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::new(
            "pr_verify_proof_only_clear_sorry",
            &[
                ("P/Dep.lean", "def baseVal : Nat := 7\n"),
                (
                    "P/Target.lean",
                    "import P.Dep\ntheorem fixed_thm : baseVal = 7 := by\n  sorry\n",
                ),
            ],
        )?;
        let _ = fs::remove_dir_all(tree.project.join(".lake/build"));
        git_init_and_commit(&tree.project, "base_with_sorry")?;
        tree.lake(&["build", "P"])?;
        let _ = fs::remove_dir_all(tree.project.join(".lake/build/ir"));

        // Replace `sorry` with a real proof (`exact rfl`) without rebuilding `.lake/build` on disk.
        fs::write(
            tree.project.join("P/Target.lean"),
            "import P.Dep\ntheorem fixed_thm : baseVal = 7 := by\n  exact rfl\n",
        )?;
        let before_lake = snapshot(&tree.project)?;
        let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
        let hits0 = HEAD_OVERLAY_HITS.load(std::sync::atomic::Ordering::SeqCst);
        run_pr_verify_command(
            &mut store,
            true,
            tree.project.clone(),
            "HEAD".into(),
            "trusted".into(),
            true,
            None,
            None,
            None,
            None,
            false,
            0,
            None,
        )?;
        assert_eq!(
            HEAD_OVERLAY_HITS.load(std::sync::atomic::Ordering::SeqCst),
            hits0 + 1,
            "sorry-removal proof edit must succeed via try_head_overlay without falling back to make_head_snapshot"
        );
        assert_eq!(
            snapshot(&tree.project)?,
            before_lake,
            "try_head_overlay must verify sorry-removal proof edit without mutating on-disk .lake/build or retaining stale base sorryAx audit"
        );
        Ok(())
    }

    #[test]
    fn test_pr_verify_overlay_propagates_transitive_standalone_invalidation() -> Result<()> {
        use crate::worktree_test_support::{snapshot, LakeTree};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::new(
            "pr_verify_transitive_standalone",
            &[
                ("P.lean", "import P.A\n"),
                ("P/A.lean", "theorem dag_thm : 1 + 1 = 2 := by\n  omega\n"),
                (
                    "P/StandMid.lean",
                    "import P.A\nmacro \"stand_ty\" : term => `(Nat)\n",
                ),
                (
                    "P/StandLeaf.lean",
                    "import P.StandMid\ntheorem leaf_thm (x : stand_ty) : x = x := rfl\n",
                ),
            ],
        )?;
        let _ = fs::remove_dir_all(tree.project.join(".lake/build"));
        git_init_and_commit(&tree.project, "base_standalone_chain")?;
        tree.lake(&["build", "P"])?;
        let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
        run_pr_verify_command(
            &mut store,
            true,
            tree.project.clone(),
            "HEAD".into(),
            "trusted".into(),
            true,
            None,
            None,
            None,
            None,
            false,
            0,
            None,
        )?;
        fs::write(
            tree.project.join("P/A.lean"),
            "theorem dag_thm : 1 + 1 = 2 := by\n  exact rfl\n",
        )?;
        fs::write(
            tree.project.join("P/StandMid.lean"),
            "import P.A\nmacro \"stand_ty\" : term => `(Bool)\n",
        )?;
        let before_lake = snapshot(&tree.project)?;
        let err = run_pr_verify_command(
            &mut store,
            true,
            tree.project.clone(),
            "HEAD".into(),
            "trusted".into(),
            true,
            None,
            None,
            None,
            None,
            false,
            0,
            None,
        )
        .expect_err("transitive standalone macro change altering StandLeaf statement must fail strict statement pinning");
        assert!(
            err.to_string().contains("leaf_thm") || err.to_string().contains("statement"),
            "unexpected error: {err:#}"
        );
        assert_eq!(snapshot(&tree.project)?, before_lake);
        Ok(())
    }

    #[test]
    fn test_ci_verify_rejects_deferred_hygiene_violations_in_non_dag_files() -> Result<()> {
        use crate::worktree_test_support::LakeTree;
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::new(
            "ci_verify_non_dag_deferred_hygiene",
            &[
                (
                    "P/Ok.lean",
                    "axiom allowedAx : True\ntheorem ok_thm : True := allowedAx\n",
                ),
                (
                    "Extra/Sneak.lean",
                    "axiom sneakForbidden : False\ntheorem bad_thm : False := sneakForbidden\n",
                ),
            ],
        )?;
        let fake_bwrap =
            crate::module_builder::ScopedTestBwrapOverride::write_fake_bwrap_script(&tree.root)?;
        let _bwrap =
            crate::module_builder::ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy());
        let prev_ax = std::env::var_os(crate::splitter::ALLOWED_AXIOMS_ENV);
        std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, "allowedAx");
        let run_res = (|| -> Result<()> {
            let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
            for mode in ["trusted", "untrusted"] {
                let err = run_ci_verify_command(
                    &mut store,
                    true,
                    mode.into(),
                    tree.project.clone(),
                    None,
                    None,
                    false,
                    None,
                )
                .expect_err("ci-verify must reject non-DAG file containing disallowed axiom");
                let msg = format!("{err:#}");
                assert!(
                    msg.contains("Extra/Sneak.lean") && msg.contains("axiom"),
                    "mode={mode} unexpected error: {msg}"
                );
            }
            fs::remove_file(tree.project.join("Extra/Sneak.lean"))?;
            for mode in ["trusted", "untrusted"] {
                run_ci_verify_command(
                    &mut store,
                    true,
                    mode.into(),
                    tree.project.clone(),
                    None,
                    None,
                    false,
                    None,
                )
                .with_context(|| format!("ci-verify mode={mode} should accept DAG allowedAx"))?;
            }
            Ok(())
        })();
        match prev_ax {
            Some(v) => std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, v),
            None => std::env::remove_var(crate::splitter::ALLOWED_AXIOMS_ENV),
        }
        run_res
    }

    #[test]
    fn test_pr_verify_deferred_hygiene_blocks_fast_olean_remote_http_and_audits_trailing_axioms(
    ) -> Result<()> {
        use crate::worktree_test_support::LakeTree;
        use std::io::{Read, Write};
        use std::net::TcpListener;
        use std::sync::{
            atomic::{AtomicBool, AtomicUsize, Ordering},
            Arc,
        };

        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::new(
            "pr_verify_deferred_trailing_ax",
            &[
                ("P/Dep.lean", "def baseVal : Nat := 7\n"),
                (
                    "P/Target.lean",
                    "import P.Dep\ntheorem edited_thm : baseVal = 7 := by\n  exact Eq.refl baseVal\naxiom trailingForbidden : False\n",
                ),
                (
                    "P/Allowed.lean",
                    "import P.Dep\naxiom allowedPrAx : True\ntheorem ok_thm : baseVal = 7 := by\n  exact Eq.refl baseVal\n",
                ),
            ],
        )?;
        fs::write(
            tree.project.join("turbo-lean.toml"),
            "[axioms]\nallow = [\"allowedPrAx\"]\n",
        )?;
        let _ = fs::remove_dir_all(tree.project.join(".lake/build"));
        git_init_and_commit(&tree.project, "base_with_axioms")?;
        tree.lake(&["build", "P"])?;
        let _ = fs::remove_dir_all(tree.project.join(".lake/build/ir"));

        // Proof-only edit on `edited_thm` in `P/Target.lean` (trailing disallowed axiom remains)
        // and proof-only edit on `ok_thm` in `P/Allowed.lean` (only `allowedPrAx` present).
        fs::write(
            tree.project.join("P/Target.lean"),
            "import P.Dep\ntheorem edited_thm : baseVal = 7 := by\n  exact rfl\naxiom trailingForbidden : False\n",
        )?;

        let listener = TcpListener::bind("127.0.0.1:0")?;
        listener.set_nonblocking(true)?;
        let addr = listener.local_addr()?;
        let remote_url = format!("http://{addr}");
        let hits = Arc::new(AtomicUsize::new(0));
        let stop = Arc::new(AtomicBool::new(false));
        let hits_bg = Arc::clone(&hits);
        let stop_bg = Arc::clone(&stop);
        let server_handle = std::thread::spawn(move || {
            while !stop_bg.load(Ordering::Acquire) {
                match listener.accept() {
                    Ok((mut stream, _)) => {
                        let _ =
                            stream.set_read_timeout(Some(std::time::Duration::from_millis(200)));
                        let mut buf = [0u8; 8192];
                        let _ = stream.read(&mut buf);
                        hits_bg.fetch_add(1, Ordering::SeqCst);
                        let body = r#"{"ok":true,"status":"shard_verified","cache_hit":false,"cache_hits":0,"verified_count":1,"stdout":"","stderr":"","verified_decl_types":{}}"#;
                        let resp = format!(
                            "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
                            body.len(),
                            body
                        );
                        let _ = stream.write_all(resp.as_bytes());
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                        std::thread::sleep(std::time::Duration::from_millis(5));
                    }
                    Err(_) => break,
                }
            }
        });

        let prev_ax = std::env::var_os(crate::splitter::ALLOWED_AXIOMS_ENV);
        std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, "allowedPrAx");
        let run_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> Result<()> {
            let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
            // 1. `P/Target.lean` has a proof-only edit AND a trailing disallowed axiom:
            //    must NEVER hit `remote_http`, must NOT skip via `fast_olean`, and must fail closed!
            let err = run_pr_verify_command(
                &mut store,
                true,
                tree.project.clone(),
                "HEAD".into(),
                "trusted".into(),
                true,
                None,
                None,
                Some(remote_url.clone()),
                None,
                false,
                0,
                None,
            )
            .expect_err("pr-verify must reject trailing disallowed axiom even on proof-only edit with remote_http");
            let msg = format!("{err:#}");
            assert_eq!(
                hits.load(Ordering::SeqCst),
                0,
                "pr-verify must never offload deferred-hygiene file to remote_http"
            );
            assert!(
                msg.contains("trailingForbidden"),
                "expected kernel gate error naming trailingForbidden, got: {msg}"
            );

            // 2. Revert `P/Target.lean` and remove `trailingForbidden` in a fresh commit, then
            //    proof-edit `P/Allowed.lean`: must pass locally via zero-stub whole-file audit
            //    with zero `remote_http` hits!
            fs::write(
                tree.project.join("P/Target.lean"),
                "import P.Dep\ntheorem edited_thm : baseVal = 7 := by\n  exact Eq.refl baseVal\n",
            )?;
            git_init_and_commit(&tree.project, "clean_target")?;
            tree.lake(&["build", "P"])?;
            let _ = fs::remove_dir_all(tree.project.join(".lake/build/ir"));
            fs::write(
                tree.project.join("P/Allowed.lean"),
                "import P.Dep\naxiom allowedPrAx : True\ntheorem ok_thm : baseVal = 7 := by\n  exact rfl\n",
            )?;
            let receipt_path = tree.root.join("allowed_receipt.json");
            run_pr_verify_command(
                &mut store,
                true,
                tree.project.clone(),
                "HEAD".into(),
                "trusted".into(),
                true,
                Some(receipt_path.clone()),
                None,
                Some(remote_url.clone()),
                None,
                false,
                0,
                None,
            )?;
            assert_eq!(
                hits.load(Ordering::SeqCst),
                0,
                "pr-verify must never offload allowedPrAx deferred-hygiene file to remote_http"
            );
            assert!(
                receipt_path.is_file(),
                "expected verification receipt at {}",
                receipt_path.display()
            );
            let receipt: serde_json::Value = serde_json::from_slice(&fs::read(&receipt_path)?)?;
            assert!(
                receipt["receipt_blake3"]
                    .as_str()
                    .is_some_and(|h| !h.is_empty()),
                "expected non-empty receipt_blake3 in receipt: {receipt}"
            );
            // Also verify shard receipt was NOT published into TurboStore for deferred-hygiene file,
            // so a second run still does NOT hit `remote_http` and re-verifies locally.
            run_pr_verify_command(
                &mut store,
                true,
                tree.project.clone(),
                "HEAD".into(),
                "trusted".into(),
                true,
                None,
                None,
                Some(remote_url.clone()),
                None,
                false,
                0,
                None,
            )?;
            assert_eq!(
                hits.load(Ordering::SeqCst),
                0,
                "warm pr-verify must still never offload allowedPrAx deferred-hygiene file to remote_http"
            );
            Ok(())
        }));
        stop.store(true, Ordering::Release);
        let _ = server_handle.join();
        match prev_ax {
            Some(v) => std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, v),
            None => std::env::remove_var(crate::splitter::ALLOWED_AXIOMS_ENV),
        }
        match run_res {
            Ok(r) => r,
            Err(p) => std::panic::resume_unwind(p),
        }
    }

    #[test]
    fn test_head_statement_report_snapshot_bound_rejects_post_audit_live_olean_swap() -> Result<()>
    {
        use crate::worktree_test_support::LakeTree;
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::new(
            "stmt_snap_swap",
            &[("P/A.lean", "theorem a_thm : 1 + 1 = 2 := rfl\n")],
        )?;
        let git_ok = |args: &[&str]| -> Result<()> {
            let out = Command::new("git")
                .args(args)
                .current_dir(&tree.project)
                .output()?;
            anyhow::ensure!(
                out.status.success(),
                "git {args:?} failed: {}",
                String::from_utf8_lossy(&out.stderr)
            );
            Ok(())
        };
        git_ok(&["init", "-q"])?;
        git_ok(&["config", "user.email", "test@example.com"])?;
        git_ok(&["config", "user.name", "Test"])?;
        git_ok(&["add", "."])?;
        git_ok(&["commit", "-q", "-m", "base"])?;

        let aux = LakeTree::new(
            "stmt_snap_swap_aux",
            &[("P/A.lean", "theorem a_thm : 1 + 1 = 3 := by sorry\n")],
        )?;
        let swapped_olean = fs::read(aux.project.join(".lake/build/lib/lean/P/A.olean"))?;
        let live_olean = tree.project.join(".lake/build/lib/lean/P/A.olean");
        let clean_olean = fs::read(&live_olean)?;

        let store = TurboStore::open(Some(&tree.root.join("cache")))?;
        let policy = StatementPolicy::at(&tree.project, "HEAD");
        let (_, cert_snap_opt) = certify_head_statement_modules_and_replay(
            &store,
            &tree.project,
            None,
            &policy,
            false,
            None,
            None,
            None,
        )?;
        let cert_snap = cert_snap_opt.expect("certified head closure snapshot");
        let cfg = crate::module_builder::resolve_project_config_with_trust(&tree.project, false)?;
        let key_before =
            head_statement_report_cache_action_key(&tree.project, None, &cfg, &cert_snap)
                .expect("snapshot-bound head statement cache key");

        let rep = built_kernel_statement_report_bound(
            &tree.project,
            None,
            false,
            Some(&store.root),
            None,
            Some(&cert_snap),
        )?;
        assert!(
            rep.statements.keys().any(|k| k.ends_with("::a_thm")),
            "expected a_thm in snapshot-bound statement report: {:?}",
            rep.statements
        );

        fs::write(&live_olean, &swapped_olean)?;
        let key_after =
            head_statement_report_cache_action_key(&tree.project, None, &cfg, &cert_snap)
                .expect("snapshot-bound head statement cache key after live swap");
        assert_eq!(
            key_before, key_after,
            "head_statement_report_cache_action_key must read sealed snapshot digests, never live .olean"
        );
        let dump_err = built_kernel_statement_report_bound(
            &tree.project,
            None,
            false,
            Some(&store.root),
            None,
            Some(&cert_snap),
        )
        .expect_err("snapshot-bound statement report must reject post-audit live .olean swap");
        assert!(
            format!("{dump_err:#}").contains("closure"),
            "expected closure mismatch error, got: {dump_err:#}"
        );
        fs::write(&live_olean, &clean_olean)?;

        // Also verify proof-irrelevant overlay certification binds unchanged base modules
        // and modified overlay modules across sealed `base_snap` and `head_snap` snapshots.
        let aux_proof = LakeTree::new(
            "stmt_snap_ov_proof",
            &[("P/A.lean", "theorem a_thm : 1 + 1 = 2 := by decide\n")],
        )?;
        let ov_dir = tree.root.join("ov_lib");
        fs::create_dir_all(ov_dir.join("P"))?;
        fs::copy(
            aux_proof.project.join(".lake/build/lib/lean/P/A.olean"),
            ov_dir.join("P/A.olean"),
        )?;
        let (rebuilt_opt, ov_snap_opt) = certify_head_statement_modules_and_replay(
            &store,
            &tree.project,
            None,
            &policy,
            false,
            Some(&ov_dir),
            None,
            Some(&cfg),
        )?;
        assert_eq!(
            rebuilt_opt,
            Some(std::collections::HashSet::from(["P.A".to_string()])),
            "proof-irrelevant overlay update must take sealed overlay fast path"
        );
        let ov_snap = ov_snap_opt.expect("certified overlay closure snapshot");
        let ov_key = head_statement_report_cache_action_key(&tree.project, None, &cfg, &ov_snap)
            .expect("snapshot-bound overlay head statement cache key");
        assert_ne!(
            ov_key, key_before,
            "overlay .olean digest change must rotate head statement report cache key"
        );
        Ok(())
    }

    #[test]
    fn base_statement_cache_key_binds_local_dep_sources_artifacts_and_lake_inputs() -> Result<()> {
        if Command::new("lean").arg("--version").output().is_err()
            || Command::new("lake").arg("--version").output().is_err()
        {
            return Ok(());
        }
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let root = std::env::temp_dir().join(format!(
            "turbo_base_stmt_dep_bind_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&root);
        let proj = root.join("proj");
        let dep_dir = proj.join(".lake/packages/dep");
        let ext_dep = root.join("ext_dep");
        fs::create_dir_all(dep_dir.join("target"))?;
        fs::create_dir_all(dep_dir.join(".lake/gen"))?;
        fs::create_dir_all(&ext_dep)?;
        fs::create_dir_all(&proj)?;
        let tc = include_str!("../../../lean/lean-toolchain");
        fs::write(dep_dir.join("lean-toolchain"), tc)?;
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep\"\ndefaultTargets = [\"Dep\", \"Gen\"]\n[[lean_lib]]\nname = \"Dep\"\nsrcDir = \"target\"\nroots = [\"Dep\"]\n[[lean_lib]]\nname = \"Gen\"\nsrcDir = \".lake/gen\"\nroots = [\"Gen\"]\n",
        )?;
        fs::write(dep_dir.join("target/Dep.lean"), "def depConst : Nat := 1\n")?;
        fs::write(
            dep_dir.join(".lake/gen/Gen.lean"),
            "def genConst : Nat := 1\n",
        )?;
        fs::write(ext_dep.join("lean-toolchain"), tc)?;
        fs::write(
            ext_dep.join("lakefile.toml"),
            "name = \"ext_dep\"\ndefaultTargets = [\"Ext\"]\n[[lean_lib]]\nname = \"Ext\"\nroots = [\"Ext\"]\n",
        )?;
        fs::write(ext_dep.join("Ext.lean"), "def extConst : Nat := 1\n")?;
        fs::write(proj.join("lean-toolchain"), tc)?;
        let root_lakefile = "import Lake\nopen Lake DSL\npackage app\nrequire dep from \".lake/packages/dep\"\ninput_file SpecCfg where\n  path := \"spec.txt\"\n  text := true\n@[default_target]\nlean_lib App where\n  roots := #[`App]\n  needs := #[SpecCfg]\n";
        fs::write(proj.join("lakefile.lean"), root_lakefile)?;
        fs::write(proj.join("spec.txt"), "v1\n")?;
        fs::write(
            proj.join("lake-manifest.json"),
            r#"{"version": "1.1.0", "packagesDir": ".lake/packages", "lakeDir": ".lake", "packages": [{"type": "path", "scope": "", "name": "dep", "manifestFile": "lake-manifest.json", "inherited": false, "dir": ".lake/packages/dep", "configFile": "lakefile.toml"}]}"#,
        )?;
        fs::write(
            proj.join("App.lean"),
            "import Dep\nimport Gen\ntheorem app_thm : depConst + genConst = depConst + genConst := rfl\n",
        )?;
        fs::write(proj.join(".gitignore"), ".lake/\n")?;
        git_init_and_commit(&proj, "base")?;

        let b1 = Command::new("lake")
            .args(["build", "App"])
            .current_dir(&proj)
            .output()?;
        anyhow::ensure!(
            b1.status.success(),
            "lake build App v1 failed: {}",
            String::from_utf8_lossy(&b1.stderr)
        );

        let warm_store = TurboStore::open(Some(&root.join("warm_store")))?;
        let changes1 =
            kernel_statement_changes_with_trust(&warm_store, &proj, "HEAD", None, None, &[])?;
        assert!(
            changes1.is_empty(),
            "initial clean run should have 0 changes"
        );
        let cfg1 = crate::module_builder::resolve_project_config(&proj)?;
        let key1 = base_statement_cache_action_key(&proj, "HEAD", Path::new(""), None, &cfg1)
            .expect("base statement cache key v1");

        // 1. Mutate `spec.txt` (Lake `input_file` tracked at `v1` in `HEAD`, modified in working tree)
        // without touching `lakefile.lean`: `base_statement_cache_action_key` MUST rotate via `workspace_lake_inputs_digest`.
        fs::write(proj.join("spec.txt"), "v2\n")?;
        let cfg_inp = crate::module_builder::resolve_project_config(&proj)?;
        let key_inp = base_statement_cache_action_key(&proj, "HEAD", Path::new(""), None, &cfg_inp)
            .expect("base statement cache key after input_file change");
        assert_ne!(
            key_inp, key1,
            "Lake input_file content change must rotate base_statement_cache_action_key"
        );

        // 2. Uncommitted `lakefile.lean` drift from `base` must return `None` (fail-closed miss).
        fs::write(
            proj.join("lakefile.lean"),
            format!("{root_lakefile}\n-- drift\n"),
        )?;
        let cfg_drift = crate::module_builder::resolve_project_config(&proj)?;
        assert!(
            base_statement_cache_action_key(&proj, "HEAD", Path::new(""), None, &cfg_drift)
                .is_none(),
            "live lakefile.lean drift relative to base commit must disable baseline statement cache"
        );
        fs::write(proj.join("lakefile.lean"), root_lakefile)?;

        // 3. Sibling external path dependency (`../ext_dep`) must not panic/bail on `..` in
        // `trusted_dep_snapshot_rel_path` and must return `None` from `base_statement_cache_action_key`.
        let orig_manifest = fs::read_to_string(proj.join("lake-manifest.json"))?;
        fs::write(
            proj.join("lake-manifest.json"),
            r#"{"version": "1.1.0", "packagesDir": ".lake/packages", "lakeDir": ".lake", "packages": [{"type": "path", "scope": "", "name": "ext_dep", "manifestFile": "lake-manifest.json", "inherited": false, "dir": "../ext_dep", "configFile": "lakefile.toml"}]}"#,
        )?;
        let cfg_ext = crate::module_builder::resolve_project_config(&proj)?;
        assert!(
            trusted_dep_snapshot_rel_path(&cfg_ext, &cfg_ext.dep_pkgs[0]).is_none(),
            "external `../ext_dep` path dependency must never yield a `..` snapshot path"
        );
        git_commit_all(&proj, "ext_dep_manifest")?;
        assert!(
            base_statement_cache_action_key(&proj, "HEAD", Path::new(""), None, &cfg_ext).is_none(),
            "external `../ext_dep` path dependency must disable base_statement_cache_action_key even when lake-manifest.json matches HEAD"
        );
        fs::write(proj.join("lake-manifest.json"), &orig_manifest)?;

        // 4. Mutate path dependency `target/Dep.lean` macro and overlapping `.lake/gen/Gen.lean`:
        fs::write(
            dep_dir.join("target/Dep.lean"),
            "macro \"dep_ty\" : term => `(Nat)\n",
        )?;
        fs::write(
            proj.join("App.lean"),
            "import Dep\nimport Gen\ntheorem app_thm : dep_ty = dep_ty ∧ genConst = genConst := ⟨rfl, rfl⟩\n",
        )?;
        git_commit_all(&proj, "base_dep_macro")?;
        let b2 = Command::new("lake")
            .args(["build", "App"])
            .current_dir(&proj)
            .output()?;
        anyhow::ensure!(b2.status.success(), "lake build App v2 failed");
        let warm_v1 =
            kernel_statement_changes_with_trust(&warm_store, &proj, "HEAD", None, None, &[])?;
        assert!(warm_v1.is_empty());
        let cfg_v2 = crate::module_builder::resolve_project_config(&proj)?;
        let key_v2 = base_statement_cache_action_key(&proj, "HEAD", Path::new(""), None, &cfg_v2)
            .expect("base statement cache key v2");

        // Source-only edit inside overlapping `.lake/gen/Gen.lean` BEFORE artifact rebuild must rotate key!
        fs::write(
            dep_dir.join(".lake/gen/Gen.lean"),
            "def genConst : Nat := 2\n",
        )?;
        let cfg_gen_src_only = crate::module_builder::resolve_project_config(&proj)?;
        let key_gen_src_only =
            base_statement_cache_action_key(&proj, "HEAD", Path::new(""), None, &cfg_gen_src_only)
                .expect("base statement cache key after .lake/gen/Gen.lean source-only change");
        assert_ne!(
            key_gen_src_only, key_v2,
            "dependency source edit inside `.lake/gen` must rotate base_statement_cache_action_key"
        );
        fs::write(
            dep_dir.join(".lake/gen/Gen.lean"),
            "def genConst : Nat := 1\n",
        )?;

        // Source-only edit under `dep/target/Dep.lean` BEFORE rebuilding artifacts must rotate key!
        fs::write(
            dep_dir.join("target/Dep.lean"),
            "macro \"dep_ty\" : term => `(Bool)\n",
        )?;
        let cfg_dep_src_only = crate::module_builder::resolve_project_config(&proj)?;
        let key_dep_src_only =
            base_statement_cache_action_key(&proj, "HEAD", Path::new(""), None, &cfg_dep_src_only)
                .expect("base statement cache key after dep/target/Dep.lean source-only change");
        assert_ne!(
            key_dep_src_only, key_v2,
            "dependency source edit under `srcDir = \"target\"` must rotate base_statement_cache_action_key even before artifact rebuild"
        );
        fs::write(
            proj.join("App.lean"),
            "import Dep\nimport Gen\ntheorem app_thm : Bool = Bool ∧ genConst = genConst := ⟨rfl, rfl⟩\n",
        )?;
        let b3 = Command::new("lake")
            .args(["build", "App"])
            .current_dir(&proj)
            .output()?;
        anyhow::ensure!(b3.status.success(), "lake build App v3 failed");
        let cfg_dep = crate::module_builder::resolve_project_config(&proj)?;
        let key_dep = base_statement_cache_action_key(&proj, "HEAD", Path::new(""), None, &cfg_dep)
            .expect("base statement cache key after dep source/artifact change");
        assert_ne!(
            key_dep, key_v2,
            "dependency source/build change must rotate base_statement_cache_action_key"
        );

        let cold_store = TurboStore::open(Some(&root.join("cold_store")))?;
        let warm_res =
            kernel_statement_changes_with_trust(&warm_store, &proj, "HEAD", None, None, &[])?;
        let cold_res =
            kernel_statement_changes_with_trust(&cold_store, &proj, "HEAD", None, None, &[])?;
        assert!(
            warm_res.is_empty(),
            "stale Nat baseline cache entry must not be reused after dependency macro changed to Bool"
        );
        assert_eq!(
            warm_res, cold_res,
            "warm and cold statement deltas must agree after dependency-only mutation"
        );

        let _ = fs::remove_dir_all(&root);
        Ok(())
    }

    #[test]
    fn test_standalone_module_format_cache_preserves_private_sidecars_and_cold_warm_parity(
    ) -> Result<()> {
        if Command::new("lean").arg("--version").output().is_err()
            || Command::new("lake").arg("--version").output().is_err()
        {
            return Ok(());
        }
        use crate::worktree_test_support::LakeTree;
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::new(
            "standalone_module_private_cache",
            &[
                (
                    "P/A.lean",
                    "module\npublic theorem dag_thm : 1 + 1 = 2 := by\n  omega\n",
                ),
                (
                    "Extra/StandMod.lean",
                    "module\npublic import P.A\npublic theorem pub_thm : True := trivial\nprivate theorem priv_thm : 1 + 1 = 2 := rfl\n",
                ),
            ],
        )?;
        let _ = fs::remove_file(tree.project.join("lakefile.toml"));
        fs::write(
            tree.project.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage fixture\ninput_file SpecCfg where\n  path := \"spec.txt\"\n  text := true\n@[default_target]\nlean_lib P where\n  globs := #[.submodules `P]\n  needs := #[SpecCfg]\n",
        )?;
        fs::write(tree.project.join("spec.txt"), "v1\n")?;
        tree.lake(&["build", "P"])?;
        git_init_and_commit(&tree.project, "base_standalone_module")?;
        let pkg = crate::module_builder::resolve_package_config(&tree.project, true)?;
        let lib_dir = tree.project.join(&pkg.build_dir).join(&pkg.lean_lib_dir);
        let standalone = BTreeMap::from([(
            "Extra.StandMod".to_string(),
            (
                tree.project.join("Extra/StandMod.lean"),
                tree.project.clone(),
            ),
        )]);

        let mut warm_store = TurboStore::open(Some(&tree.root.join("warm_store")))?;
        compile_standalone_statement_modules(
            &tree.project,
            &pkg,
            &lib_dir,
            standalone.clone(),
            false,
            Some(&mut warm_store),
        )?;
        let olean_p = lib_dir.join("Extra/StandMod.olean");
        let srv_p = PathBuf::from(format!("{}.server", olean_p.display()));
        let priv_p = PathBuf::from(format!("{}.private", olean_p.display()));
        assert!(
            olean_p.is_file() && srv_p.is_file() && priv_p.is_file(),
            "cold standalone `module` build must emit .olean, .olean.server, and .olean.private"
        );
        let cfg1 = crate::module_builder::resolve_project_config(&tree.project)?;
        let stand_src1 = fs::read_to_string(tree.project.join("Extra/StandMod.lean"))?;
        let stand_hdr1 = crate::module_builder::parse_header_info(&stand_src1);
        let stand_key1 = standalone_statement_olean_action_key(
            &cfg1,
            &pkg,
            "Extra.StandMod",
            Path::new("Extra/StandMod.lean"),
            &stand_src1,
            &stand_hdr1.imports,
            None,
        )
        .expect("standalone action key v1");
        fs::write(tree.project.join("spec.txt"), "v2\n")?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        let cfg2 = crate::module_builder::resolve_project_config(&tree.project)?;
        let stand_key2 = standalone_statement_olean_action_key(
            &cfg2,
            &pkg,
            "Extra.StandMod",
            Path::new("Extra/StandMod.lean"),
            &stand_src1,
            &stand_hdr1.imports,
            None,
        )
        .expect("standalone action key v2");
        assert_ne!(
            stand_key2, stand_key1,
            "workspace Lake input_file content change must rotate standalone_statement_olean_action_key"
        );
        fs::write(tree.project.join("spec.txt"), "v1\n")?;
        crate::module_builder::reset_lake_inputs_tag_memo();

        let cold_rep = built_kernel_statement_report(&tree.project, None, false, None, None)?;
        assert!(
            cold_rep.statements.keys().any(|k| k.ends_with("pub_thm")),
            "cold report must contain public theorem"
        );
        assert!(
            cold_rep.statements.keys().any(|k| k.contains("priv_thm")),
            "cold report must contain private theorem from .olean.private, got keys: {:?}",
            cold_rep.statements.keys().collect::<Vec<_>>()
        );

        // Wipe `Extra/` build outputs and restore via warm `compile_standalone_statement_modules` hit.
        fs::remove_dir_all(lib_dir.join("Extra"))?;
        compile_standalone_statement_modules(
            &tree.project,
            &pkg,
            &lib_dir,
            standalone.clone(),
            false,
            Some(&mut warm_store),
        )?;
        assert!(
            olean_p.is_file() && srv_p.is_file() && priv_p.is_file(),
            "warm standalone `module` cache hit must restore .olean, .olean.server, and .olean.private"
        );
        let warm_rep = built_kernel_statement_report(&tree.project, None, false, None, None)?;
        assert_eq!(
            warm_rep.statements, cold_rep.statements,
            "warm standalone `module` cache hit must preserve exact kernel statement parity with cold build"
        );

        // Corrupt the cached action outputs in SQLite to drop `.olean.private`: warm hit must reject
        // the incomplete entry and fall back to recompiling the full artifact set.
        warm_store.conn.execute(
            "DELETE FROM action_outputs WHERE rel_path LIKE '%.private'",
            [],
        )?;
        for f in warm_store
            .root
            .join("locks")
            .read_dir()
            .into_iter()
            .flatten()
            .flatten()
        {
            if f.path().extension().and_then(|e| e.to_str()) == Some("done") {
                let _ = fs::remove_file(f.path());
            }
        }
        fs::remove_dir_all(lib_dir.join("Extra"))?;
        compile_standalone_statement_modules(
            &tree.project,
            &pkg,
            &lib_dir,
            standalone,
            false,
            Some(&mut warm_store),
        )?;
        assert!(
            priv_p.is_file(),
            "incomplete cached standalone `module` entry missing .olean.private must be rejected and recompiled"
        );

        // End-to-end warm vs cold `pr-verify` parity when a private theorem statement changes in `Extra/StandMod.lean`.
        run_pr_verify_command(
            &mut warm_store,
            true,
            tree.project.clone(),
            "HEAD".into(),
            "trusted".into(),
            true,
            None,
            None,
            None,
            None,
            false,
            0,
            None,
        )?;
        fs::write(
            tree.project.join("P/A.lean"),
            "module\npublic theorem dag_thm : 1 + 1 = 2 := by\n  exact rfl\n",
        )?;
        fs::write(
            tree.project.join("Extra/StandMod.lean"),
            "module\npublic import P.A\npublic theorem pub_thm : True := trivial\nprivate theorem priv_thm : 2 + 2 = 4 := rfl\n",
        )?;
        let mut cold_store = TurboStore::open(Some(&tree.root.join("cold_store")))?;
        let warm_err = run_pr_verify_command(
            &mut warm_store,
            true,
            tree.project.clone(),
            "HEAD".into(),
            "trusted".into(),
            true,
            None,
            None,
            None,
            None,
            false,
            0,
            None,
        )
        .expect_err(
            "warm pr-verify must reject private theorem statement edit in standalone module",
        );
        let cold_err = run_pr_verify_command(
            &mut cold_store,
            true,
            tree.project.clone(),
            "HEAD".into(),
            "trusted".into(),
            true,
            None,
            None,
            None,
            None,
            false,
            0,
            None,
        )
        .expect_err(
            "cold pr-verify must reject private theorem statement edit in standalone module",
        );
        assert!(
            warm_err.to_string().contains("priv_thm") && cold_err.to_string().contains("priv_thm"),
            "both warm ({warm_err:#}) and cold ({cold_err:#}) must detect private statement change"
        );

        // Imported elaborator reading an untracked file under `open IO` (`FS.readFile`) must bypass
        // standalone caching (`None`) so `pr-verify` never reuses a stale standalone `.olean`.
        fs::write(
            tree.project.join("P/A.lean"),
            "module\npublic meta import Lean\npublic meta section\nopen IO Lean Elab Term\nelab \"ext_val\" : term => do\n  let s ← FS.readFile \"spec.txt\"\n  return mkNatLit s.trimAscii.toString.length\nend\npublic theorem dag_thm : 1 + 1 = 2 := by\n  omega\n",
        )?;
        fs::write(
            tree.project.join("Extra/StandMod.lean"),
            "module\npublic import P.A\npublic theorem pub_thm : ext_val = ext_val := rfl\n",
        )?;
        tree.lake(&["build", "P"])?;
        let cfg_eff = crate::module_builder::resolve_project_config(&tree.project)?;
        let stand_eff_src = fs::read_to_string(tree.project.join("Extra/StandMod.lean"))?;
        let stand_eff_hdr = crate::module_builder::parse_header_info(&stand_eff_src);
        assert!(
            standalone_statement_olean_action_key(
                &cfg_eff,
                &pkg,
                "Extra.StandMod",
                Path::new("Extra/StandMod.lean"),
                &stand_eff_src,
                &stand_eff_hdr.imports,
                None,
            )
            .is_none(),
            "imported module with host IO.FS effects under `open IO` must disable standalone statement caching"
        );

        let _ = fs::remove_dir_all(&tree.root);
        Ok(())
    }

    #[test]
    fn test_open_io_getenv_elaborator_bypasses_base_statement_cache_and_freshness_parity(
    ) -> Result<()> {
        if Command::new("lean").arg("--version").output().is_err()
            || Command::new("lake").arg("--version").output().is_err()
        {
            return Ok(());
        }
        use crate::worktree_test_support::LakeTree;
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        const ENV_KEY: &str = "TURBO_TEST_ELAB_STMT_ENV";
        let prev_env = std::env::var_os(ENV_KEY);
        let prev_lake_cache_dir = std::env::var_os("LAKE_CACHE_DIR");
        let prev_lake_art_cache = std::env::var_os("LAKE_ARTIFACT_CACHE");
        std::env::set_var(ENV_KEY, "alpha");

        let run = || -> Result<()> {
            let src_v1 = "import Lean\nopen IO Lean Elab Term in\nelab \"env_ty\" : term => do\n  match (← getEnv \"TURBO_TEST_ELAB_STMT_ENV\") with\n  | some \"beta\" => return mkConst ``Bool\n  | _ => return mkConst ``Nat\ntheorem env_thm (x : env_ty) : x = x := rfl\n";
            let tree = LakeTree::new("open_io_getenv_stmt_parity", &[("P/EnvMod.lean", src_v1)])?;
            git_init_and_commit(&tree.project, "base_env_alpha")?;

            let cfg = crate::module_builder::resolve_project_config(&tree.project)?;
            assert!(
                base_statement_cache_action_key(&tree.project, "HEAD", Path::new(""), None, &cfg)
                    .is_none(),
                "baseline git tree with `elab` / `open IO` host effects must bypass base_statement_cache_action_key"
            );

            let mut warm_store = TurboStore::open(Some(&tree.root.join("warm_store")))?;
            // Seed warm caches under `TURBO_TEST_ELAB_STMT_ENV=alpha`.
            run_pr_verify_command(
                &mut warm_store,
                true,
                tree.project.clone(),
                "HEAD".into(),
                "trusted".into(),
                true,
                None,
                None,
                None,
                None,
                false,
                0,
                None,
            )?;

            // Proof-only edit on `P/EnvMod.lean` while rotating `TURBO_TEST_ELAB_STMT_ENV` to `beta`
            // (so `HEAD` at `beta` has `Bool` if evaluated cleanly, or we keep `P/EnvMod.lean` statement
            // pinned to `Nat` in working tree while `HEAD` elaborates to `Bool` under `beta`!).
            std::env::set_var(ENV_KEY, "beta");
            fs::write(
                tree.project.join("P/EnvMod.lean"),
                "import Lean\nopen IO Lean Elab Term in\nelab \"env_ty\" : term => do\n  let _ ← getEnv \"TURBO_TEST_ELAB_STMT_ENV\"\n  return mkConst ``Nat\ntheorem env_thm (x : env_ty) : x = x := rfl\n",
            )?;
            let mut cold_store = TurboStore::open(Some(&tree.root.join("cold_store")))?;
            let warm_err = run_pr_verify_command(
                &mut warm_store,
                true,
                tree.project.clone(),
                "HEAD".into(),
                "trusted".into(),
                true,
                None,
                None,
                None,
                None,
                false,
                0,
                None,
            )
            .expect_err(
                "warm pr-verify must not reuse stale alpha baseline statement report when env=beta",
            );
            let cold_err = run_pr_verify_command(
                &mut cold_store,
                true,
                tree.project.clone(),
                "HEAD".into(),
                "trusted".into(),
                true,
                None,
                None,
                None,
                None,
                false,
                0,
                None,
            )
            .expect_err(
                "cold pr-verify must detect statement delta between HEAD(beta=Bool) and WT(Nat)",
            );
            assert!(
                warm_err.to_string().contains("env_thm")
                    && cold_err.to_string().contains("env_thm"),
                "warm ({warm_err:#}) and cold ({cold_err:#}) must both reject env-driven statement delta"
            );

            // Second case: even with zero working-tree edits to `P/EnvMod.lean` (say, a proof-only edit
            // on a sibling module `P/Other.lean` while `P/EnvMod.lean` has identical source & Lake trace
            // on disk from the `alpha` build), rotating `TURBO_TEST_ELAB_STMT_ENV=beta` while `P/EnvMod.lean`
            // on disk still holds `alpha` (`Nat`) `.olean`s must NOT let Lake-trace freshness reuse the
            // stale on-disk `.olean` against a freshly rebuilt baseline (`Bool`) — or vice versa!
            std::env::set_var(ENV_KEY, "alpha");
            let tree2 = LakeTree::new(
                "open_io_getenv_dag_freshness",
                &[
                    (
                        "P/EnvDep.lean",
                        "import Lean\nopen IO Lean Elab Term in\nelab \"env_dep_ty\" : term => do\n  match (← getEnv \"TURBO_TEST_ELAB_STMT_ENV\") with\n  | some \"beta\" => return mkConst ``Bool\n  | _ => return mkConst ``Nat\ndef depWitness (x : env_dep_ty) : env_dep_ty := x\n",
                    ),
                    (
                        "P/Consumer.lean",
                        "import P.EnvDep\ntheorem consumer_thm (x : _) : depWitness x = depWitness x := by\n  rfl\n",
                    ),
                ],
            )?;
            git_init_and_commit(&tree2.project, "base_dag_alpha")?;
            let cfg2 = crate::module_builder::resolve_project_config(&tree2.project)?;
            let targets2 = vec!["P.EnvDep".to_string(), "P.Consumer".to_string()];
            let dag2 =
                crate::module_builder::build_module_dag_for_trusted_statement(&cfg2, &targets2)?;
            assert!(
                !crate::module_builder::are_dag_modules_fresh_by_lake_trace(&cfg2, &dag2),
                "DAG containing an elaborator module (`P.EnvDep`) must never report fresh-by-Lake-trace alone"
            );
            let dirty2 = crate::module_builder::find_dirty_modules_in_otherwise_fresh_dag(
                &cfg2,
                &dag2,
                4,
                &std::collections::HashSet::new(),
            )
            .expect("dirty module scan on otherwise-fresh DAG");
            assert!(
                dirty2.iter().any(|m| m == "P.EnvDep") && dirty2.iter().any(|m| m == "P.Consumer"),
                "elaboration host-effect module `P.EnvDep` must cascade dirtiness to downstream `P.Consumer`, got: {dirty2:?}"
            );

            // Third case (`sol` Finding 1): `by run_tac` in a theorem type without `elab`/`macro`
            // must also bypass caches and fail warm/cold parity when `TURBO_TEST_ELAB_STMT_ENV` rotates.
            std::env::set_var(ENV_KEY, "alpha");
            let rt_src_v1 = "import Lean\nopen IO Lean Elab Tactic in\ntheorem rt_thm (x : show Type from by\n  run_tac do\n    match (← getEnv \"TURBO_TEST_ELAB_STMT_ENV\") with\n    | some \"beta\" => evalTactic (← `(tactic| exact Bool))\n    | _ => evalTactic (← `(tactic| exact Nat))) : x = x := by\n  rfl\n";
            let tree_rt =
                LakeTree::new("run_tac_getenv_stmt_parity", &[("P/RtMod.lean", rt_src_v1)])?;
            git_init_and_commit(&tree_rt.project, "base_rt_alpha")?;
            let mut rt_warm_store = TurboStore::open(Some(&tree_rt.root.join("warm_store")))?;
            run_pr_verify_command(
                &mut rt_warm_store,
                true,
                tree_rt.project.clone(),
                "HEAD".into(),
                "trusted".into(),
                true,
                None,
                None,
                None,
                None,
                false,
                0,
                None,
            )?;
            let rt_src_v2 = "import Lean\nopen IO Lean Elab Tactic in\ntheorem rt_thm (x : show Type from by\n  run_tac do\n    let _ ← getEnv \"TURBO_TEST_ELAB_STMT_ENV\"\n    evalTactic (← `(tactic| exact Nat))) : x = x := by\n  exact rfl\n";
            fs::write(tree_rt.project.join("P/RtMod.lean"), rt_src_v2)?;
            std::env::set_var(ENV_KEY, "beta");
            let mut rt_cold_store = TurboStore::open(Some(&tree_rt.root.join("cold_store")))?;
            let rt_warm_err = run_pr_verify_command(
                &mut rt_warm_store,
                true,
                tree_rt.project.clone(),
                "HEAD".into(),
                "trusted".into(),
                true,
                None,
                None,
                None,
                None,
                false,
                0,
                None,
            )
            .expect_err(
                "warm pr-verify must not reuse stale alpha baseline for `by run_tac` when env=beta",
            );
            let rt_cold_err = run_pr_verify_command(
                &mut rt_cold_store,
                true,
                tree_rt.project.clone(),
                "HEAD".into(),
                "trusted".into(),
                true,
                None,
                None,
                None,
                None,
                false,
                0,
                None,
            )
            .expect_err("cold pr-verify must detect `by run_tac` statement delta between HEAD(Bool) and WT(Nat)");
            assert!(
                rt_warm_err.to_string().contains("rt_thm")
                    && rt_cold_err.to_string().contains("rt_thm"),
                "warm ({rt_warm_err:#}) and cold ({rt_cold_err:#}) must both pinpoint `rt_thm`"
            );

            // Fourth case (`astra` Finding 1 + `argon` Finding 2): transitive import `P.EnvDep -> P.Consumer`
            // where `P.Consumer` has NO `elab`/`macro` tokens (`x : _` inferred from `depWitness`) must NOT
            // be served from Module CAS or warm-probe when `TURBO_TEST_ELAB_STMT_ENV` rotates (`alpha` -> `beta` -> `alpha`).
            std::env::set_var(ENV_KEY, "alpha");
            let mut trans_store = TurboStore::open(Some(&tree2.root.join("trans_store")))?;
            run_pr_verify_command(
                &mut trans_store,
                true,
                tree2.project.clone(),
                "HEAD".into(),
                "trusted".into(),
                true,
                None,
                None,
                None,
                None,
                false,
                0,
                None,
            )?;
            fs::write(
                tree2.project.join("P/Consumer.lean"),
                "import P.EnvDep\ntheorem consumer_thm (x : Nat) : depWitness x = depWitness x := by\n  exact rfl\n",
            )?;
            std::env::set_var(ENV_KEY, "beta");
            let trans_beta_err = run_pr_verify_command(
                &mut trans_store,
                true,
                tree2.project.clone(),
                "HEAD".into(),
                "trusted".into(),
                true,
                None,
                None,
                None,
                None,
                false,
                0,
                None,
            )
            .expect_err("transitive consumer of `P.EnvDep` must detect HEAD(Bool) vs WT(Nat) or reject stale type when env=beta");
            assert!(
                trans_beta_err.to_string().contains("consumer_thm")
                    || trans_beta_err.to_string().contains("depWitness")
                    || trans_beta_err
                        .to_string()
                        .contains("Application type mismatch")
                    || trans_beta_err.to_string().contains("type mismatch"),
                "unexpected transitive beta error: {trans_beta_err:#}"
            );
            // Restore original `P/Consumer.lean` (`x : _`), build under `beta` so `P.EnvDep(Bool)` &
            // `P.Consumer(Bool)` exist on disk & in CAS (if unblocked), then switch back to
            // `alpha` and verify neither Module CAS nor warm-probe serves a stale `P.Consumer` artifact!
            fs::write(
                tree2.project.join("P/Consumer.lean"),
                "import P.EnvDep\ntheorem consumer_thm (x : _) : depWitness x = depWitness x := by\n  rfl\n",
            )?;
            crate::module_builder::build_project_modules_native(
                &mut trans_store,
                &tree2.project,
                &[],
                "trusted",
                1,
                false,
                true,
                None,
            )?;
            std::env::set_var(ENV_KEY, "alpha");
            let rep_alpha = crate::module_builder::build_project_modules_native(
                &mut trans_store,
                &tree2.project,
                &[],
                "trusted",
                1,
                false,
                true,
                None,
            )?;
            assert_eq!(
                rep_alpha.modules_cached, 0,
                "neither P.EnvDep nor transitive P.Consumer may hit Module CAS"
            );
            assert_eq!(
                rep_alpha.modules_up_to_date_reused, 0,
                "neither P.EnvDep nor transitive P.Consumer may warm-adopt across env rotation"
            );
            let canon_tree2 = tree2.project.canonicalize()?;
            let canon_consumer = tree2.project.join("P/Consumer.lean").canonicalize()?;
            let root_env_olean = tree2.project.join(".lake/build/lib/lean/P/EnvDep.olean");
            let root_alpha_bytes = fs::read(&root_env_olean)?;
            let root_fake_cache = tree2.root.join("populated_lake_cache");
            fs::create_dir_all(&root_fake_cache)?;
            let seed_cache_st = Command::new("lake")
                .arg("build")
                .env("LAKE_CACHE_DIR", &root_fake_cache)
                .env("LAKE_ARTIFACT_CACHE", "true")
                .current_dir(&canon_tree2)
                .status()?;
            anyhow::ensure!(seed_cache_st.success(), "seed lake artifact cache failed");
            std::env::set_var("LAKE_CACHE_DIR", &root_fake_cache);
            std::env::set_var("LAKE_ARTIFACT_CACHE", "true");
            std::env::set_var(ENV_KEY, "beta");
            let refreshed_root_res = crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon_tree2,
                std::slice::from_ref(&canon_consumer),
            );
            std::env::remove_var("LAKE_CACHE_DIR");
            std::env::remove_var("LAKE_ARTIFACT_CACHE");
            let refreshed_root = refreshed_root_res?;
            assert!(
                refreshed_root >= 1,
                "ensure_project_imports_fresh_for_check must refresh root host-effect import P.EnvDep via Lake and verify post-refresh"
            );
            assert_ne!(
                fs::read(&root_env_olean)?,
                root_alpha_bytes,
                "ensure_project_imports_fresh_for_check must bypass LAKE_ARTIFACT_CACHE and force Lake to re-elaborate P.EnvDep across untracked env rotation"
            );

            // Fifth case (`astra` Finding 2 + `sol` Finding 2): path dependency AND git-pinned dependency
            // defining an elaborator (`getEnv` for path dep, `IO.FS.lines` for git-pinned dep) imported by
            // a pure root `App.lean` must NOT reuse stale `.lake/packages/dep/.lake/build` `.olean`s,
            // base/overlay caches, or Module CAS across untracked env/file rotation!
            for use_git_pin in [false, true] {
                std::env::set_var(ENV_KEY, "alpha");
                let dep_case_root = tree.root.join(if use_git_pin {
                    "git_dep_case"
                } else {
                    "path_dep_case"
                });
                let dep_pkg_src = dep_case_root.join("dep_origin");
                let app_proj = dep_case_root.join("app");
                let dep_in_pkgs = app_proj.join(".lake/packages/dep");
                let flag_file = dep_case_root.join("host_lines_flag.txt");
                fs::create_dir_all(&dep_pkg_src)?;
                fs::create_dir_all(&app_proj)?;
                fs::write(&flag_file, "alpha\n")?;
                let tc = include_str!("../../../lean/lean-toolchain");
                fs::write(dep_pkg_src.join("lean-toolchain"), tc)?;
                fs::write(
                    dep_pkg_src.join("lakefile.toml"),
                    "name = \"dep\"\ndefaultTargets = [\"Dep\"]\n[[lean_lib]]\nname = \"Dep\"\nroots = [\"Dep\"]\n",
                )?;
                let dep_lean_src = if use_git_pin {
                    let escaped_flag = flag_file.to_string_lossy().replace('\\', "\\\\");
                    format!(
                        "import Lean\nopen Lean Elab Term in\nelab \"dep_env_ty\" : term => do\n  let rows ← IO.FS.lines \"{escaped_flag}\"\n  if rows.size >= 2 then\n    return mkConst ``Bool\n  else\n    return mkConst ``Nat\ndef depWitness (x : dep_env_ty) : dep_env_ty := x\n"
                    )
                } else {
                    "import Lean\nopen IO Lean Elab Term in\nelab \"dep_env_ty\" : term => do\n  match (← getEnv \"TURBO_TEST_ELAB_STMT_ENV\") with\n  | some \"beta\" => return mkConst ``Bool\n  | _ => return mkConst ``Nat\ndef depWitness (x : dep_env_ty) : dep_env_ty := x\n".to_string()
                };
                fs::write(dep_pkg_src.join("Dep.lean"), dep_lean_src)?;
                git_init_and_commit(&dep_pkg_src, "dep_init")?;
                let dep_rev_out = Command::new("git")
                    .args(["rev-parse", "HEAD"])
                    .current_dir(&dep_pkg_src)
                    .output()?;
                let dep_rev = String::from_utf8(dep_rev_out.stdout)?.trim().to_string();
                fs::create_dir_all(dep_in_pkgs.parent().unwrap())?;
                let clone_st = Command::new("git")
                    .args(["clone", "--quiet"])
                    .arg(&dep_pkg_src)
                    .arg(&dep_in_pkgs)
                    .status()?;
                anyhow::ensure!(clone_st.success(), "git clone dep_pkg_src failed");

                fs::write(app_proj.join("lean-toolchain"), tc)?;
                let app_lakefile = if use_git_pin {
                    let escaped_dep_url = dep_pkg_src.to_string_lossy().replace('\\', "\\\\");
                    format!(
                        "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"dep\"\ngit = \"{escaped_dep_url}\"\nrev = \"{dep_rev}\"\n[[lean_lib]]\nname = \"App\"\nroots = [\"App\"]\n"
                    )
                } else {
                    "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"dep\"\npath = \".lake/packages/dep\"\n[[lean_lib]]\nname = \"App\"\nroots = [\"App\"]\n".to_string()
                };
                fs::write(app_proj.join("lakefile.toml"), app_lakefile)?;
                let manifest_json = if use_git_pin {
                    serde_json::json!({
                        "version": "1.1.0",
                        "packagesDir": ".lake/packages",
                        "lakeDir": ".lake",
                        "packages": [{
                            "type": "git",
                            "scope": "",
                            "name": "dep",
                            "manifestFile": "lake-manifest.json",
                            "inherited": false,
                            "url": dep_pkg_src.to_string_lossy(),
                            "rev": dep_rev,
                            "inputRev": null,
                            "subDir": null,
                            "configFile": "lakefile.toml"
                        }]
                    })
                    .to_string()
                } else {
                    r#"{"version": "1.1.0", "packagesDir": ".lake/packages", "lakeDir": ".lake", "packages": [{"type": "path", "scope": "", "name": "dep", "manifestFile": "lake-manifest.json", "inherited": false, "dir": ".lake/packages/dep", "configFile": "lakefile.toml"}]}"#.to_string()
                };
                fs::write(app_proj.join("lake-manifest.json"), manifest_json)?;
                fs::write(
                    app_proj.join("App.lean"),
                    "import Dep\ntheorem app_env_thm (x : dep_env_ty) : x = x := by\n  rfl\n",
                )?;
                fs::write(app_proj.join(".gitignore"), ".lake/\n")?;
                git_init_and_commit(&app_proj, "app_base")?;
                let lb = Command::new("lake")
                    .args(["build", "App"])
                    .current_dir(&app_proj)
                    .output()?;
                anyhow::ensure!(
                    lb.status.success(),
                    "lake build App failed (git={use_git_pin}): {}",
                    String::from_utf8_lossy(&lb.stderr)
                );
                let mut dep_store = TurboStore::open(Some(&dep_case_root.join("store")))?;
                run_pr_verify_command(
                    &mut dep_store,
                    true,
                    app_proj.clone(),
                    "HEAD".into(),
                    "trusted".into(),
                    true,
                    None,
                    None,
                    None,
                    None,
                    false,
                    0,
                    None,
                )?;
                let app_cfg = crate::module_builder::resolve_project_config(&app_proj)?;
                assert!(
                    base_statement_cache_action_key(&app_proj, "HEAD", Path::new(""), None, &app_cfg)
                        .is_none(),
                    "dep with host-state-reading elaborator (git={use_git_pin}) must disable base_statement_cache_action_key"
                );
                let app_dag = crate::module_builder::build_module_dag(&app_cfg, &[])?;
                assert!(
                    app_dag.nodes.contains_key("Dep"),
                    "dep with host-state-reading elaborator (git={use_git_pin}) must NOT be externalized into external_olean_deps"
                );
                std::env::set_var(ENV_KEY, "beta");
                fs::write(&flag_file, "alpha\nbeta\n")?;
                let base_oid_out = Command::new("git")
                    .args(["rev-parse", "HEAD"])
                    .current_dir(&app_proj)
                    .output()?;
                let app_base_oid = String::from_utf8(base_oid_out.stdout)?.trim().to_string();
                // Smuggle `(x : Nat) : x = x` on `App.lean` after rotating `flag_file` / `ENV_KEY`
                // to `beta` (`base` now elaborates `dep_env_ty` as `Bool`, whereas stale `alpha`
                // `.olean`s and stale `base_stmt_map` had `(x : Nat) : x = x`). Both warm (`dep_store`)
                // and cold (`cold_dep_store`) `pr-verify` must reject the smuggled statement change!
                fs::write(
                    app_proj.join("App.lean"),
                    "import Dep\ntheorem app_env_thm (x : Nat) : x = x := by\n  exact rfl\n",
                )?;
                let err_warm_dep = run_pr_verify_command(
                    &mut dep_store,
                    true,
                    app_proj.clone(),
                    app_base_oid.clone(),
                    "trusted".into(),
                    true,
                    None,
                    None,
                    None,
                    None,
                    false,
                    0,
                    None,
                )
                .expect_err(
                    "warm pr-verify must detect smuggled Nat statement delta when dep IO.FS.lines/getEnv rotated base to Bool",
                );
                assert!(
                    format!("{err_warm_dep:#}").contains("app_env_thm"),
                    "expected statement delta on app_env_thm (warm, git={use_git_pin}), got: {err_warm_dep:#}"
                );
                let mut cold_dep_store = TurboStore::open(Some(&dep_case_root.join("cold_store")))?;
                let err_cold_dep = run_pr_verify_command(
                    &mut cold_dep_store,
                    true,
                    app_proj.clone(),
                    app_base_oid,
                    "trusted".into(),
                    true,
                    None,
                    None,
                    None,
                    None,
                    false,
                    0,
                    None,
                )
                .expect_err(
                    "cold pr-verify must not seed stale alpha dep .olean and must detect smuggled Nat statement delta under beta",
                );
                assert!(
                    format!("{err_cold_dep:#}").contains("app_env_thm"),
                    "expected statement delta on app_env_thm (cold, git={use_git_pin}), got: {err_cold_dep:#}"
                );
                let dep_beta_rep = crate::module_builder::build_project_modules_native(
                    &mut dep_store,
                    &app_proj,
                    &[],
                    "trusted",
                    1,
                    false,
                    true,
                    None,
                )?;
                assert_eq!(
                    dep_beta_rep.modules_cached, 0,
                    "dep & App (git={use_git_pin}) must not hit Module CAS across env/file rotation"
                );
                assert_eq!(
                    dep_beta_rep.modules_up_to_date_reused, 0,
                    "dep & App (git={use_git_pin}) must recompile rather than warm-adopting stale alpha .olean"
                );
                let canon_app = app_proj.canonicalize()?;
                let canon_app_lean = app_proj.join("App.lean").canonicalize()?;
                let dep_olean = dep_in_pkgs.join(".lake/build/lib/lean/Dep.olean");
                let dep_beta_bytes = fs::read(&dep_olean)?;
                std::env::set_var(ENV_KEY, "alpha");
                fs::write(&flag_file, "alpha\n")?;
                let refreshed = crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon_app,
                    std::slice::from_ref(&canon_app_lean),
                )?;
                assert!(
                    refreshed >= 1,
                    "ensure_project_imports_fresh_for_check must refresh host-effect dep via Lake and verify post-refresh (git={use_git_pin})"
                );
                assert_ne!(
                    fs::read(&dep_olean)?,
                    dep_beta_bytes,
                    "ensure_project_imports_fresh_for_check must purge and force Lake to re-elaborate Dep.olean across untracked env/file rotation (git={use_git_pin})"
                );
                fs::write(
                    &canon_app_lean,
                    "import Dep\ntheorem app_check_thm : depWitness 0 = 0 := rfl\n",
                )?;
                let check_val = crate::check::run_check_command_value(
                    &mut dep_store,
                    true,
                    canon_app_lean.clone(),
                    None,
                    canon_app.clone(),
                    Some(1),
                    false,
                    None,
                )?;
                assert_eq!(
                    check_val.get("status").and_then(|v| v.as_str()),
                    Some("file_verified"),
                    "turbo-lean check must elaborate App.lean against refreshed alpha Dep.olean (Nat), got: {check_val}"
                );
                #[cfg(unix)]
                if unsafe { libc::geteuid() } != 0 {
                    use std::os::unix::fs::PermissionsExt;
                    let dep_lib_dir = dep_in_pkgs.join(".lake/build/lib/lean");
                    let orig_mode = fs::metadata(&dep_lib_dir)?.permissions().mode();
                    fs::set_permissions(&dep_lib_dir, fs::Permissions::from_mode(0o555))?;
                    let purge_err = crate::lake_build::ensure_project_imports_fresh_for_check(
                        &canon_app,
                        std::slice::from_ref(&canon_app_lean),
                    );
                    let _ =
                        fs::set_permissions(&dep_lib_dir, fs::Permissions::from_mode(orig_mode));
                    let err_msg = format!(
                        "{:#}",
                        purge_err.expect_err(
                            "non-writable dep build dir must fail closed instead of silently skipping purge"
                        )
                    );
                    assert!(
                        err_msg.contains("Failed to purge stale build artifact"),
                        "expected purge error message, got: {err_msg}"
                    );
                }
                let _ = fs::remove_dir_all(&dep_case_root);
            }

            let _ = fs::remove_dir_all(&tree_rt.root);
            let _ = fs::remove_dir_all(&tree.root);
            let _ = fs::remove_dir_all(&tree2.root);
            Ok(())
        };

        let res = run();
        match prev_env {
            Some(v) => std::env::set_var(ENV_KEY, v),
            None => std::env::remove_var(ENV_KEY),
        }
        match prev_lake_cache_dir {
            Some(v) => std::env::set_var("LAKE_CACHE_DIR", v),
            None => std::env::remove_var("LAKE_CACHE_DIR"),
        }
        match prev_lake_art_cache {
            Some(v) => std::env::set_var("LAKE_ARTIFACT_CACHE", v),
            None => std::env::remove_var("LAKE_ARTIFACT_CACHE"),
        }
        res
    }

    #[test]
    fn test_pinned_git_dep_cleanliness_and_snapshot_olean_stripping() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_pinned_git_clean_and_strip_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        let run = || -> Result<()> {
            let dep_origin = dir.join("dep_origin");
            let app_proj = dir.join("app");
            let dep_in_pkgs = app_proj.join(".lake/packages/dep");
            fs::create_dir_all(&dep_origin)?;
            fs::create_dir_all(&app_proj)?;
            fs::write(
                dep_origin.join("lean-toolchain"),
                "leanprover/lean4:v4.31.0\n",
            )?;
            fs::write(
                dep_origin.join("lakefile.toml"),
                "name = \"dep\"\ndefaultTargets = [\"Dep\"]\n[[lean_lib]]\nname = \"Dep\"\nroots = [\"Dep\"]\n",
            )?;
            fs::write(
                dep_origin.join("Dep.lean"),
                "prelude\ndef depVal : IO (Option String) := IO.getEnv \"TURBO_DUMMY_PIN_ENV\"\n",
            )?;
            // Commit a fake prebuilt `.olean` inside `.lake/build/lib/lean/` at rev1 to verify
            // `seed_trusted_statement_dependencies` strips `.git`, `.lake`, and `.olean` products.
            fs::create_dir_all(dep_origin.join(".lake/build/lib/lean"))?;
            fs::write(
                dep_origin.join(".lake/build/lib/lean/Dep.olean"),
                b"smuggled-committed-olean",
            )?;
            fs::write(
                dep_origin.join(".lake/build/.turbo_verified_sources.json"),
                b"{}",
            )?;
            git_init_and_commit(&dep_origin, "rev1_with_committed_olean")?;
            let rev1 = String::from_utf8(
                crate::trusted_tools::git(&dep_origin)?
                    .arg("-C")
                    .arg(&dep_origin)
                    .args(["rev-parse", "HEAD"])
                    .output()?
                    .stdout,
            )?
            .trim()
            .to_string();

            fs::create_dir_all(dep_in_pkgs.parent().unwrap())?;
            let clone_st = crate::trusted_tools::git(&app_proj)?
                .env("GIT_ALLOW_PROTOCOL", "file")
                .args(["clone", "--quiet", "--"])
                .arg(&dep_origin)
                .arg(&dep_in_pkgs)
                .status()?;
            anyhow::ensure!(clone_st.success(), "clone dep_origin failed");

            fs::write(
                app_proj.join("lean-toolchain"),
                "leanprover/lean4:v4.31.0\n",
            )?;
            fs::write(
                app_proj.join("lakefile.toml"),
                format!(
                    "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"dep\"\ngit = \"{}\"\nrev = \"{rev1}\"\n[[lean_lib]]\nname = \"App\"\nroots = [\"App\"]\n",
                    dep_origin.to_string_lossy().replace('\\', "\\\\")
                ),
            )?;
            fs::write(
                app_proj.join("lake-manifest.json"),
                serde_json::json!({
                    "version": "1.1.0",
                    "packagesDir": ".lake/packages",
                    "lakeDir": ".lake",
                    "packages": [{
                        "type": "git",
                        "scope": "",
                        "name": "dep",
                        "manifestFile": "lake-manifest.json",
                        "inherited": false,
                        "url": dep_origin.to_string_lossy(),
                        "rev": rev1,
                        "inputRev": rev1,
                        "subDir": null,
                        "configFile": "lakefile.toml"
                    }]
                })
                .to_string(),
            )?;
            fs::write(app_proj.join("App.lean"), "prelude\nimport Dep\n")?;

            crate::module_builder::reset_lake_inputs_tag_memo();
            let cfg_clean =
                crate::module_builder::resolve_project_config_with_trust(&app_proj, false)?;
            let dep_cfg = cfg_clean
                .dep_pkgs
                .iter()
                .find(|d| d.name == "dep")
                .expect("dep package resolved");
            assert!(
                is_pinned_git_manifest_dep(&cfg_clean, dep_cfg),
                "clean git checkout at exact manifest rev must be recognized as pinned git dep"
            );

            let snap_clean = dir.join("snap_clean");
            fs::create_dir_all(&snap_clean)?;
            seed_trusted_statement_dependencies(&snap_clean, &cfg_clean)?;
            let seeded_dep = snap_clean.join(".lake/packages/dep");
            assert!(seeded_dep.join("Dep.lean").is_file());
            assert!(
                !seeded_dep.join(".git").exists(),
                "trusted statement snapshot must not retain .git directory"
            );
            assert!(
                !seeded_dep.join(".lake").exists(),
                "trusted statement snapshot must strip committed .lake build products"
            );

            // Advance local checkout HEAD to an unpinned commit `rev2` without updating `lake-manifest.json`:
            // `is_pinned_git_manifest_dep` MUST fail closed (`false`).
            fs::write(
                dep_in_pkgs.join("Dep.lean"),
                "prelude\ndef depVal : IO (Option String) := pure (some \"tampered\")\n",
            )?;
            let add_st = crate::trusted_tools::git(&dep_in_pkgs)?
                .arg("-C")
                .arg(&dep_in_pkgs)
                .args(["add", "Dep.lean"])
                .status()?;
            assert!(add_st.success());
            let commit_st = crate::trusted_tools::git(&dep_in_pkgs)?
                .arg("-C")
                .arg(&dep_in_pkgs)
                .args([
                    "-c",
                    "user.name=t",
                    "-c",
                    "user.email=t@e",
                    "-c",
                    "commit.gpgsign=false",
                    "commit",
                    "-qm",
                    "drifted_head",
                ])
                .status()?;
            assert!(commit_st.success());
            crate::module_builder::reset_lake_inputs_tag_memo();
            assert!(
                !is_pinned_git_manifest_dep(&cfg_clean, dep_cfg),
                "HEAD-drifted git checkout must NOT be treated as clean manifest-pinned git dep"
            );

            // Reset back to `rev1`, then dirty the worktree with an untracked file: must also fail closed (`false`).
            let reset_st = crate::trusted_tools::git(&dep_in_pkgs)?
                .arg("-C")
                .arg(&dep_in_pkgs)
                .args(["reset", "--hard", "-q", &rev1])
                .status()?;
            assert!(reset_st.success());
            crate::module_builder::reset_lake_inputs_tag_memo();
            assert!(is_pinned_git_manifest_dep(&cfg_clean, dep_cfg));

            fs::write(dep_in_pkgs.join("UntrackedEvil.lean"), "prelude\n")?;
            crate::module_builder::reset_lake_inputs_tag_memo();
            assert!(
                !is_pinned_git_manifest_dep(&cfg_clean, dep_cfg),
                "dirty/untracked git checkout must NOT be treated as clean manifest-pinned git dep"
            );
            Ok(())
        };
        let res = run();
        let _ = fs::remove_dir_all(&dir);
        res
    }

    #[test]
    fn test_untrusted_pr_worker_cap_and_timeout_bounds() {
        assert_eq!(pr_verify_file_worker_jobs(true, 4, 10), 2);
        assert_eq!(pr_verify_file_worker_jobs(true, 16, 10), 2);
        assert_eq!(pr_verify_file_worker_jobs(true, 4, 1), 1);
        assert_eq!(pr_verify_file_worker_jobs(false, 4, 10), 4);
        assert_eq!(pr_verify_file_worker_jobs(false, 8, 3), 3);

        assert_eq!(
            crate::module_builder::module_compile_timeout_secs_from(None, true),
            300
        );
        assert_eq!(
            crate::module_builder::module_compile_timeout_secs_from(Some("0"), true),
            300
        );
        assert_eq!(
            crate::module_builder::module_compile_timeout_secs_from(Some("5"), true),
            15
        );
        assert_eq!(
            crate::module_builder::module_compile_timeout_secs_from(Some("1200"), true),
            600
        );
        assert_eq!(
            crate::module_builder::module_compile_timeout_secs_from(Some("1200"), false),
            1200
        );
    }

    #[test]
    fn test_pr_verify_trusted_allows_sink_assurance_targets_after_lake_input_change_and_rejects_imported_run_cmd(
    ) -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_pr_assurance_sink_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let proj = dir.join("proj");
        let run = || -> Result<()> {
            fs::create_dir_all(proj.join("scripts/.assurance_fixtures/Fixture"))?;
            fs::create_dir_all(proj.join("contracts"))?;
            fs::write(
                proj.join("lean-toolchain"),
                include_str!("../../../lean/lean-toolchain"),
            )?;
            fs::write(proj.join(".gitignore"), ".lake/\n")?;
            fs::write(proj.join("contracts/Sample.sol"), "// v1\n")?;
            fs::write(
                proj.join("lakefile.lean"),
                concat!(
                    "import Lake\nopen Lake DSL\n\npackage «proj»\n\n",
                    "input_dir solInputs where\n  path := \"contracts\"\n  filter := .extension \"sol\"\n  text := true\n\n",
                    "@[default_target]\nlean_lib «MainLib» where\n  roots := #[`MainLib]\n  needs := #[solInputs]\n\n",
                    "lean_lib «PrintAxioms» where\n  roots := #[`PrintAxioms]\n\n",
                    "lean_lib «AssuranceFixtures» where\n  srcDir := \"scripts/.assurance_fixtures\"\n  roots := #[`Fixture.Bad]\n\n",
                    "lean_lib «Assurance» where\n  srcDir := \"scripts\"\n  roots := #[`Controls]\n",
                ),
            )?;
            fs::write(
                proj.join("MainLib.lean"),
                "theorem main_ok : (1 : Nat) = 1 := rfl\n",
            )?;
            fs::write(
                proj.join("PrintAxioms.lean"),
                "import Lean\nimport MainLib\nrun_cmd Lean.logInfo \"audit ok\"\n",
            )?;
            fs::write(
                proj.join("scripts/.assurance_fixtures/Fixture/Bad.lean"),
                "theorem fixture_bad : False := sorry\n",
            )?;
            fs::write(
                proj.join("scripts/Controls.lean"),
                "import Lean\nimport Fixture.Bad\nrun_cmd Lean.logInfo \"control ok\"\n",
            )?;
            git_init_and_commit(&proj, "base with assurance targets")?;

            // Change a Lake `input_dir` file and proof-edit MainLib: `lake_inputs_changed` marks all `.lean` files.
            fs::write(proj.join("contracts/Sample.sol"), "// v2\n")?;
            fs::write(
                proj.join("MainLib.lean"),
                "theorem main_ok : (1 : Nat) = 1 := by rfl\n",
            )?;
            let mut store = TurboStore::open(Some(&dir.join("cache")))?;
            crate::check::run_check_command(
                &mut store,
                false,
                false,
                proj.join("MainLib.lean"),
                None,
                proj.clone(),
                Some(1),
                false,
                None,
            )?;
            let receipt_path = dir.join("receipt.json");
            run_pr_verify_command(
                &mut store,
                true,
                proj.clone(),
                "HEAD".to_string(),
                "trusted".to_string(),
                false,
                Some(receipt_path.clone()),
                None,
                None,
                None,
                false,
                1,
                None,
            )?;
            assert!(receipt_path.exists());

            // Now make `MainLib` import `PrintAxioms`: breaks the closed sink-cone invariant and must fail closed!
            let _ = fs::remove_file(&receipt_path);
            fs::write(
                proj.join("MainLib.lean"),
                "import PrintAxioms\ntheorem main_ok : (1 : Nat) = 1 := by rfl\n",
            )?;
            let err = run_pr_verify_command(
                &mut store,
                true,
                proj.clone(),
                "HEAD".to_string(),
                "trusted".to_string(),
                false,
                Some(receipt_path.clone()),
                None,
                None,
                None,
                false,
                1,
                None,
            )
            .unwrap_err();
            let msg = format!("{err:#}");
            assert!(
                msg.contains("Soundness hygiene violation") && msg.contains("PrintAxioms"),
                "importing a run_cmd module from a theorem module must fail closed, got: {msg}"
            );
            // Editing an assurance script so `run_cmd` fails must also fail closed in `pr-verify`.
            fs::write(
                proj.join("MainLib.lean"),
                "theorem main_ok : (1 : Nat) = 1 := by rfl\n",
            )?;
            fs::write(
                proj.join("PrintAxioms.lean"),
                "import Lean\nimport MainLib\nrun_cmd throwError \"audit regression\"\n",
            )?;
            let err_broken = run_pr_verify_command(
                &mut store,
                true,
                proj.clone(),
                "HEAD".to_string(),
                "trusted".to_string(),
                false,
                Some(receipt_path.clone()),
                None,
                None,
                None,
                false,
                1,
                None,
            )
            .unwrap_err();
            assert!(
                format!("{err_broken:#}").contains("PrintAxioms")
                    || format!("{err_broken:#}").contains("audit regression"),
                "broken edited assurance script must fail pr-verify, got: {err_broken:#}"
            );
            assert!(!receipt_path.exists());
            Ok(())
        };
        let res = run();
        let _ = fs::remove_dir_all(&dir);
        res
    }
}
