use anyhow::{Context, Result};
use rusqlite::{params, Connection, OptionalExtension};
use serde::{Deserialize, Serialize};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

pub fn now_unix() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64
}

#[allow(dead_code)]
pub fn boot_id() -> String {
    fs::read_to_string("/proc/sys/kernel/random/boot_id")
        .unwrap_or_else(|_| "unknown-boot".to_string())
        .trim()
        .to_string()
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlobEntry {
    pub blob_hash: String,
    pub kind: String,
    pub size_bytes: u64,
    pub rel_path: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ActionRecord {
    pub action_key: String,
    pub toolchain_githash: String,
    pub kind: String,
    pub status: String,
    pub fencing_token: i64,
    pub output_manifest_hash: String,
    pub duration_ms: i64,
    pub peak_pss_bytes: i64,
    pub heartbeats: i64,
    pub trust_domain: String,
    pub outputs: Vec<BlobEntry>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StorageStatus {
    pub cache_root: String,
    pub total_blobs: usize,
    pub total_actions: usize,
    pub active_worktrees: usize,
    pub active_inflight_leases: usize,
    pub total_coalesced_waits: i64,
    pub total_shard_hits: i64,
    pub saved_compute_ms: i64,
    pub fastcheck_cached_bins: usize,
    pub fastcheck_cached_bytes: u64,
    pub reclaimable_bytes: u64,
    pub worktree_retained_bytes: u64,
    pub pinned_bytes: u64,
    pub total_logical_bytes: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GcReport {
    pub pruned_worktrees: usize,
    pub evicted_actions: usize,
    pub unlinked_blobs: usize,
    pub cleaned_staging_files: usize,
    pub pruned_fastcheck_bins: usize,
    pub freed_reclaimable_bytes: u64,
    pub remaining_reclaimable_bytes: u64,
    #[serde(default)]
    pub superseded_evicted: usize,
    #[serde(default)]
    pub compressed_blobs: usize,
}

pub struct SingleflightLease {
    pub action_key: String,
    pub toolchain: String,
    pub kind: String,
    pub fencing_token: i64,
    pub lock_file: File,
}

impl Drop for SingleflightLease {
    fn drop(&mut self) {
        unsafe {
            use std::os::unix::io::AsRawFd;
            libc::flock(self.lock_file.as_raw_fd(), libc::LOCK_UN);
        }
    }
}

pub enum SingleflightOutcome {
    CacheHit {
        outputs: Vec<BlobEntry>,
        coalesced: bool,
    },
    Leader(SingleflightLease),
}

const WORKTREE_LEASES_DDL: &str = "
    CREATE TABLE IF NOT EXISTS worktree_leases (
        worktree_id TEXT PRIMARY KEY,
        worktree_path TEXT NOT NULL,
        pid INTEGER NOT NULL,
        head_commit TEXT NOT NULL DEFAULT '',
        last_seen INTEGER NOT NULL
    );
    CREATE TABLE IF NOT EXISTS worktree_file_blobs (
        worktree_id TEXT NOT NULL,
        rel_path TEXT NOT NULL,
        blob_hash TEXT NOT NULL,
        updated_at INTEGER NOT NULL,
        PRIMARY KEY (worktree_id, rel_path)
    );
    CREATE INDEX IF NOT EXISTS idx_wfb_blob ON worktree_file_blobs(blob_hash);
";

fn template_shm_path() -> (PathBuf, u32) {
    let shm_base = if Path::new("/dev/shm").is_dir() { PathBuf::from("/dev/shm") } else { std::env::temp_dir() };
    let uid = unsafe { libc::geteuid() };
    (shm_base.join(format!("turbo_lean_template_state_v4_{}.db", uid)), uid)
}

fn par_filter_map<T: Sync, R: Send, F: Fn(&T) -> Option<R> + Sync>(items: &[T], f: F) -> Vec<R> {
    if items.len() < 16 {
        return items.iter().filter_map(&f).collect();
    }
    let workers = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4).min(items.len());
    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let f_ref = &f;
    let chunks: Vec<Vec<R>> = std::thread::scope(|s| {
        (0..workers)
            .map(|_| {
                let next_ref = &next_idx;
                s.spawn(move || {
                    let mut local = Vec::new();
                    loop {
                        let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if i >= items.len() {
                            break;
                        }
                        if let Some(r) = f_ref(&items[i]) {
                            local.push(r);
                        }
                    }
                    local
                })
            })
            .collect::<Vec<_>>()
            .into_iter()
            .map(|h| h.join().unwrap_or_default())
            .collect()
    });
    chunks.into_iter().flatten().collect()
}

pub struct TurboStore {
    pub root: PathBuf,
    pub conn: Connection,
}

impl TurboStore {
    pub fn init_schema(&self) -> Result<()> {
        self.conn.execute_batch(WORKTREE_LEASES_DDL)?;
        Ok(())
    }

    pub fn open(custom_root: Option<&Path>) -> Result<Self> {
        let root = match custom_root {
            Some(p) => p.to_path_buf(),
            None => std::env::var("TURBO_LEAN_HOME").map(PathBuf::from).unwrap_or_else(|_| {
                let home = std::env::var("HOME").unwrap_or_else(|_| "/tmp".to_string());
                PathBuf::from(home).join(".cache").join("turbo-lean")
            }),
        };

        let db_path = root.join("state.db");
        let mut db_warm = fs::metadata(&db_path).map(|m| m.len() >= 4096).unwrap_or(false);
        let mut from_template = false;
        let (template_path, uid) = template_shm_path();
        if !db_warm {
            fs::create_dir_all(&root)?;
            for sub in ["blobs", "staging", "locks"] {
                let _ = fs::create_dir(root.join(sub));
            }
            if template_path.exists() && fs::copy(&template_path, &db_path).is_ok() {
                db_warm = true;
                from_template = true;
            }
        }
        let conn = Connection::open(&db_path)
            .with_context(|| format!("Failed to open SQLite DB at {}", db_path.display()))?;
        let _ = conn.set_db_config(rusqlite::config::DbConfig::SQLITE_DBCONFIG_NO_CKPT_ON_CLOSE, true);
        let _ = conn.busy_timeout(std::time::Duration::from_secs(30));

        if db_warm {
            conn.execute_batch(
                "PRAGMA synchronous = NORMAL; PRAGMA busy_timeout = 30000; PRAGMA foreign_keys = ON;
                 PRAGMA mmap_size = 268435456; PRAGMA temp_store = MEMORY; PRAGMA cache_size = -65536;",
            )?;
            if !from_template {
                let uver: i64 = conn.query_row("PRAGMA user_version", [], |r| r.get(0)).unwrap_or(0);
                if uver < 2 {
                    conn.execute_batch(&format!("{}\nPRAGMA user_version = 2;", WORKTREE_LEASES_DDL))?;
                }
            }
        } else {
            conn.execute_batch(&format!(
                "PRAGMA busy_timeout = 30000; PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL;
                 PRAGMA foreign_keys = ON; PRAGMA mmap_size = 268435456; PRAGMA temp_store = MEMORY; PRAGMA cache_size = -65536;
                 BEGIN;
                 CREATE TABLE IF NOT EXISTS meta_counters (name TEXT PRIMARY KEY, val INTEGER NOT NULL);
                 INSERT OR IGNORE INTO meta_counters (name, val) VALUES ('fencing_seq', 1), ('coalesced_waits', 0);
                 CREATE TABLE IF NOT EXISTS blobs (
                     blob_hash TEXT PRIMARY KEY, kind TEXT NOT NULL, size_bytes INTEGER NOT NULL, inode INTEGER NOT NULL,
                     created_at INTEGER NOT NULL, last_accessed INTEGER NOT NULL, pin_level INTEGER NOT NULL DEFAULT 0,
                     trust_domain TEXT NOT NULL DEFAULT 'trusted'
                 );
                 CREATE TABLE IF NOT EXISTS actions (
                     action_key TEXT PRIMARY KEY, toolchain_githash TEXT NOT NULL, kind TEXT NOT NULL, status TEXT NOT NULL,
                     fencing_token INTEGER NOT NULL, output_manifest_hash TEXT, duration_ms INTEGER NOT NULL DEFAULT 0,
                     peak_pss_bytes INTEGER NOT NULL DEFAULT 0, heartbeats INTEGER NOT NULL DEFAULT 0,
                     trust_domain TEXT NOT NULL DEFAULT 'trusted', updated_at INTEGER NOT NULL, hit_count INTEGER NOT NULL DEFAULT 0
                 );
                 CREATE INDEX IF NOT EXISTS idx_actions_kind_status_domain ON actions(kind, status, trust_domain);
                 CREATE TABLE IF NOT EXISTS action_outputs (
                     action_key TEXT NOT NULL REFERENCES actions(action_key) ON DELETE CASCADE,
                     rel_path TEXT NOT NULL, blob_hash TEXT NOT NULL REFERENCES blobs(blob_hash),
                     PRIMARY KEY (action_key, rel_path)
                 );
                 CREATE TABLE IF NOT EXISTS worktrees (
                     worktree_id TEXT PRIMARY KEY, root_path TEXT NOT NULL UNIQUE, project_name TEXT NOT NULL, last_seen INTEGER NOT NULL
                 );
                 CREATE TABLE IF NOT EXISTS worktree_installations (
                     worktree_id TEXT NOT NULL REFERENCES worktrees(worktree_id) ON DELETE CASCADE,
                     rel_path TEXT NOT NULL, blob_hash TEXT NOT NULL REFERENCES blobs(blob_hash), link_mode TEXT NOT NULL,
                     PRIMARY KEY (worktree_id, rel_path)
                 );
                 {}
                 CREATE TABLE IF NOT EXISTS inflight_leases (
                     action_key TEXT PRIMARY KEY, fencing_token INTEGER NOT NULL, worker_pid INTEGER NOT NULL,
                     boot_id TEXT NOT NULL, started_at INTEGER NOT NULL, waiter_count INTEGER NOT NULL DEFAULT 1
                 );
                 CREATE TABLE IF NOT EXISTS attestations (
                     action_key TEXT NOT NULL REFERENCES actions(action_key) ON DELETE CASCADE,
                     checker_name TEXT NOT NULL, checker_version TEXT NOT NULL, axioms_json TEXT NOT NULL,
                     signature TEXT, verified_at INTEGER NOT NULL, PRIMARY KEY (action_key, checker_name)
                 );
                 CREATE TABLE IF NOT EXISTS lake_env_cache (project_key TEXT PRIMARY KEY, env_json TEXT NOT NULL, updated_at INTEGER NOT NULL);
                 CREATE TABLE IF NOT EXISTS file_split_cache (
                     file_hash TEXT PRIMARY KEY, split_json TEXT NOT NULL, hygiene_issues_json TEXT NOT NULL, updated_at INTEGER NOT NULL
                 );
                 CREATE TABLE IF NOT EXISTS file_stat_cache (
                     path_key TEXT PRIMARY KEY, mtime_sec INTEGER NOT NULL, mtime_nsec INTEGER NOT NULL,
                     size_bytes INTEGER NOT NULL, split_key TEXT NOT NULL, updated_at INTEGER NOT NULL
                 );
                 PRAGMA user_version = 2;
                 COMMIT;
                 PRAGMA wal_checkpoint(TRUNCATE);",
                WORKTREE_LEASES_DDL
            ))?;
            if !template_path.exists() {
                if let Some(shm_base) = template_path.parent() {
                    let tmp_tpl = shm_base.join(format!("turbo_lean_tpl_tmp_{}_{}.db", uid, std::process::id()));
                    if fs::copy(&db_path, &tmp_tpl).is_ok() {
                        let _ = fs::rename(&tmp_tpl, &template_path);
                    }
                }
            }
        }

        let mut store = Self { root, conn };
        let deferred_v3 = store.root.join("locks").join("deferred_pack_v3.bin");
        if let Ok(pack_bytes) = fs::read(&deferred_v3) {
            let _ = fs::remove_file(&deferred_v3);
            if let Some(manifest) = crate::pack::try_parse_v3_header(&pack_bytes) {
                let staged_blobs: Vec<(String, String, i64, i64)> = manifest
                    .blobs
                    .iter()
                    .map(|b| (b.blob_hash.clone(), b.kind.clone(), b.size_bytes as i64, 0))
                    .collect();
                let _ = crate::pack::finish_import_from_prestaged_shared_cas(
                    &mut store,
                    &manifest,
                    &staged_blobs,
                    staged_blobs.len(),
                );
            }
        }

        Ok(store)
    }

    /// Compute the deterministic BLAKE3 cache key for `file_split_cache` from an existing
    /// hex-encoded BLAKE3 digest of the raw file bytes (`BLAKE3("file-split:v5:" + src_blake3_hex)`).
    pub fn compute_file_split_key_from_src_hash(src_blake3_hex: &str) -> String {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"file-split:v5:");
        hasher.update(src_blake3_hex.as_bytes());
        hasher.finalize().to_hex().to_string()
    }

    /// Compute the deterministic BLAKE3 cache key for `file_split_cache`.
    pub fn compute_file_split_key(raw_bytes: &[u8]) -> String {
        Self::compute_file_split_key_from_src_hash(blake3::hash(raw_bytes).to_hex().as_str())
    }

    /// Batch-lookup raw `split_json` strings from `file_split_cache` in a single SQLite transaction.
    pub fn batch_get_cached_file_splits(
        &self,
        content_hashes: &[String],
    ) -> Result<std::collections::HashMap<String, String>> {
        Ok(batch_get_file_splits(&self.conn, content_hashes)?
            .into_iter()
            .map(|(fh, (split_json, _))| (fh, split_json))
            .collect())
    }

    /// Batch-store raw `(file_hash, split_json)` pairs into `file_split_cache` in a single SQLite transaction.
    pub fn batch_put_cached_file_splits(&self, entries: &[(String, String)]) -> Result<()> {
        if entries.is_empty() {
            return Ok(());
        }
        let raw_entries: Vec<(String, String, String)> = entries
            .iter()
            .map(|(fh, sj)| (fh.clone(), sj.clone(), "[]".to_string()))
            .collect();
        batch_put_file_splits(&self.conn, &raw_entries)
    }

    /// Batch-lookup multiple file split results from `file_split_cache` in a single SQLite transaction.
    pub fn batch_get_file_splits(
        &self,
        file_hashes: &[String],
    ) -> Result<std::collections::HashMap<String, crate::splitter::SplitResult>> {
        let raw_vec: Vec<(String, String)> = batch_get_file_splits(&self.conn, file_hashes)?
            .into_iter()
            .map(|(fh, (split_json, _))| (fh, split_json))
            .collect();
        Ok(par_filter_map(&raw_vec, |(fh, split_json)| {
            serde_json::from_str::<crate::splitter::SplitResult>(split_json)
                .ok()
                .map(|split| (fh.clone(), split))
        })
        .into_iter()
        .collect())
    }

    /// Batch-store multiple parsed `SplitResult`s into `file_split_cache` in a single SQLite transaction.
    pub fn batch_put_file_splits(
        &self,
        entries: &[(String, &crate::splitter::SplitResult)],
    ) -> Result<()> {
        if entries.is_empty() {
            return Ok(());
        }
        let raw_entries = par_filter_map(entries, |(fh, split)| {
            let mut compact = (*split).clone();
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
            let split_json = serde_json::to_string(&compact).ok()?;
            let hygiene_json = serde_json::to_string(&split.hygiene.flagged_items).ok()?;
            Some((fh.clone(), split_json, hygiene_json))
        });
        batch_put_file_splits(&self.conn, &raw_entries)
    }

    /// Extract a high-resolution `(mtime_sec, mtime_nsec_mixed, size_bytes)` stat tuple from `fs::Metadata`.
    pub fn extract_file_stat_tuple(meta: &fs::Metadata) -> (i64, i64, i64) {
        let mtime_nsec = meta.mtime_nsec()
            ^ (meta.ctime_nsec().wrapping_mul(31))
            ^ ((meta.ino() as i64).wrapping_mul(131));
        (meta.mtime(), mtime_nsec, meta.len() as i64)
    }

    /// Batch-lookup `(split_key, SplitResult)` by `(path_key, mtime_sec, mtime_nsec, size_bytes)`
    /// via a single SQLite join across `file_stat_cache` and `file_split_cache` without reading file contents.
    pub fn batch_get_file_splits_by_stat(
        &self,
        stats: &[(String, i64, i64, i64)],
    ) -> Result<std::collections::HashMap<String, (String, crate::splitter::SplitResult)>> {
        let raw_vec = batch_get_raw_file_splits_by_stat(&self.conn, stats)?;
        Ok(par_filter_map(&raw_vec, |(path_key, split_key, split_json)| {
            serde_json::from_str::<crate::splitter::SplitResult>(split_json)
                .ok()
                .map(|split| (path_key.clone(), (split_key.clone(), split)))
        })
        .into_iter()
        .collect())
    }

    /// Batch-insert or update `(path_key, mtime_sec, mtime_nsec, size_bytes, split_key)` rows in `file_stat_cache`.
    pub fn batch_put_file_stats(
        &self,
        entries: &[(String, i64, i64, i64, String)],
    ) -> Result<()> {
        batch_put_file_stats(&self.conn, entries)
    }

    /// Compute the deterministic BLAKE3 cache key for `resolve_lake_env`:
    /// `BLAKE3(canon_project_dir + lean-toolchain + lakefile.lean + lake-manifest.json)`
    pub fn compute_lake_env_key(canon_project_dir: &Path) -> String {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"lake-env-cache-v1\n");
        hasher.update(canon_project_dir.to_string_lossy().as_bytes());
        hasher.update(b"\n");
        for fname in [
            "lean-toolchain",
            "lakefile.lean",
            "lakefile.toml",
            "lake-manifest.json",
        ] {
            let p = canon_project_dir.join(fname);
            hasher.update(fname.as_bytes());
            hasher.update(b":");
            if let Ok(bytes) = fs::read(&p) {
                hasher.update(&bytes);
            }
            hasher.update(b"\n");
        }
        hasher.finalize().to_hex().to_string()
    }

    pub fn get_lake_env(
        &self,
        project_key: &str,
    ) -> Result<Option<std::collections::HashMap<String, String>>> {
        let env_json: Option<String> = self
            .conn
            .query_row(
                "SELECT env_json FROM lake_env_cache WHERE project_key = ?1",
                params![project_key],
                |r| r.get(0),
            )
            .optional()?;
        match env_json {
            Some(s) => {
                let map: std::collections::HashMap<String, String> = serde_json::from_str(&s)?;
                Ok(Some(map))
            }
            None => Ok(None),
        }
    }

    pub fn put_lake_env(
        &self,
        project_key: &str,
        env_map: &std::collections::HashMap<String, String>,
    ) -> Result<()> {
        let env_json = serde_json::to_string(env_map)?;
        let now = now_unix();
        self.conn.execute(
            "INSERT INTO lake_env_cache (project_key, env_json, updated_at)
             VALUES (?1, ?2, ?3)
             ON CONFLICT(project_key) DO UPDATE SET
                env_json = excluded.env_json,
                updated_at = excluded.updated_at",
            params![project_key, env_json, now],
        )?;
        Ok(())
    }

    pub fn blob_path(&self, blob_hash: &str) -> PathBuf {
        let prefix = if blob_hash.len() >= 2 {
            &blob_hash[0..2]
        } else {
            "00"
        };
        self.root.join("blobs").join(prefix).join(blob_hash)
    }

    /// Return a RAM-backed `tmpfs` staging directory (`/dev/shm/turbo-lean-staging-<uid>`) when available,
    /// falling back to `self.root.join("staging")` so temporary `.lean` shard files never touch disk.
    pub fn fast_staging_dir(&self) -> PathBuf {
        let shm = Path::new("/dev/shm");
        if shm.is_dir() {
            #[cfg(unix)]
            let uid = unsafe { libc::geteuid() };
            #[cfg(not(unix))]
            let uid = 0u32;
            let dir = shm.join(format!("turbo-lean-staging-{}", uid));
            if fs::create_dir_all(&dir).is_ok() {
                #[cfg(unix)]
                {
                    use std::os::unix::fs::PermissionsExt;
                    let _ = fs::set_permissions(&dir, fs::Permissions::from_mode(0o700));
                }
                return dir;
            }
        }
        self.root.join("staging")
    }

    /// Batch-lookup multiple theorem shard keys in a single `BEGIN IMMEDIATE ... COMMIT` SQLite
    /// transaction, verifying that the backing CAS blobs exist on disk and atomically incrementing
    /// `hit_count` and `last_accessed`.
    pub fn batch_get_theorem_shards(
        &self,
        shard_keys: &[String],
        trust_domain: &str,
    ) -> Result<std::collections::HashMap<String, String>> {
        let raw_hits = if trust_domain == "trusted" {
            batch_get_theorem_shards(&self.conn, shard_keys)?
        } else {
            batch_get_theorem_shards_in_domain(&self.conn, shard_keys, trust_domain)?
        };
        let mut verified = std::collections::HashMap::with_capacity(raw_hits.len());
        let mut exists_cache: std::collections::HashMap<String, bool> =
            std::collections::HashMap::new();
        for (k, blob_hash) in raw_hits {
            let exists = *exists_cache
                .entry(blob_hash.clone())
                .or_insert_with(|| self.blob_path(&blob_hash).exists());
            if exists {
                verified.insert(k, blob_hash);
            }
        }
        Ok(verified)
    }

    /// Fast read-only batch check for completed action keys in `trust_domain` (or `'trusted'`).
    pub fn batch_completed_action_keys(
        &self,
        keys: &[String],
        trust_domain: &str,
    ) -> Result<std::collections::HashSet<String>> {
        if keys.is_empty() {
            return Ok(std::collections::HashSet::new());
        }
        let mut hits = std::collections::HashSet::with_capacity(keys.len());
        if trust_domain != "trusted" {
            let mut stmt = self.conn.prepare_cached(
                "SELECT 1 FROM actions
                 WHERE action_key = ?1 AND status = 'completed'
                   AND (trust_domain = 'trusted' OR trust_domain = ?2)
                 LIMIT 1",
            )?;
            for k in keys {
                let found: Option<i64> = stmt
                    .query_row(params![k, trust_domain], |r| r.get(0))
                    .optional()?;
                if found.is_some() {
                    hits.insert(k.clone());
                }
            }
        } else {
            let mut stmt = self.conn.prepare_cached(
                "SELECT 1 FROM actions
                 WHERE action_key = ?1 AND status = 'completed' AND trust_domain = 'trusted'
                 LIMIT 1",
            )?;
            for k in keys {
                let found: Option<i64> = stmt.query_row(params![k], |r| r.get(0)).optional()?;
                if found.is_some() {
                    hits.insert(k.clone());
                }
            }
        }
        if !hits.is_empty() {
            let tx = self.conn.unchecked_transaction()?;
            {
                let mut upd = tx.prepare_cached(
                    "UPDATE actions SET hit_count = hit_count + 1 WHERE action_key = ?1",
                )?;
                for k in &hits {
                    upd.execute(params![k])?;
                }
            }
            tx.commit()?;
        }
        Ok(hits)
    }

    /// Batch-insert or update imported `.tlpack` blobs, actions, and action_outputs inside a single
    /// `BEGIN IMMEDIATE ... COMMIT` SQLite transaction.
    pub fn batch_import_pack_metadata(
        &mut self,
        blobs: &[(String, String, i64, i64)],
        actions: &[ActionRecord],
    ) -> Result<(usize, usize)> {
        batch_import_pack_metadata(&self.conn, blobs, actions)
    }

    pub fn get_cached_action_no_hit_bump(
        &self,
        action_key: &str,
        trust_domain: &str,
    ) -> Result<Option<Vec<BlobEntry>>> {
        let mut stmt = self.conn.prepare_cached(
            "SELECT b.blob_hash, b.kind, b.size_bytes, ao.rel_path
             FROM actions a
             JOIN action_outputs ao ON ao.action_key = a.action_key
             JOIN blobs b ON b.blob_hash = ao.blob_hash
             WHERE a.action_key = ?1 AND a.trust_domain = ?2 AND a.status = 'completed'
             ORDER BY ao.rel_path ASC",
        )?;
        let entries: Vec<BlobEntry> = stmt
            .query_map(params![action_key, trust_domain], |row| {
                Ok(BlobEntry {
                    blob_hash: row.get(0)?,
                    kind: row.get(1)?,
                    size_bytes: row.get::<_, i64>(2)? as u64,
                    rel_path: row.get(3)?,
                })
            })?
            .collect::<std::result::Result<Vec<_>, _>>()?;
        if entries.is_empty() {
            return Ok(None);
        }
        for e in &entries {
            if !self.blob_path(&e.blob_hash).exists() {
                return Ok(None);
            }
        }
        Ok(Some(entries))
    }

    pub fn get_cached_action(&self, action_key: &str, trust_domain: &str) -> Result<Option<Vec<BlobEntry>>> {
        let mut stmt = self.conn.prepare_cached(
            "SELECT b.blob_hash, b.kind, b.size_bytes, ao.rel_path, b.last_accessed
             FROM actions a
             JOIN action_outputs ao ON ao.action_key = a.action_key
             JOIN blobs b ON b.blob_hash = ao.blob_hash
             WHERE a.action_key = ?1 AND a.trust_domain = ?2 AND a.status = 'completed'
             ORDER BY ao.rel_path ASC",
        )?;

        let mut needs_touch = false;
        let now = now_unix();
        let entries: Vec<BlobEntry> = stmt
            .query_map(params![action_key, trust_domain], |row| {
                let last_acc: i64 = row.get(4)?;
                if now - last_acc >= 60 {
                    needs_touch = true;
                }
                Ok(BlobEntry {
                    blob_hash: row.get(0)?,
                    kind: row.get(1)?,
                    size_bytes: row.get::<_, i64>(2)? as u64,
                    rel_path: row.get(3)?,
                })
            })?
            .collect::<std::result::Result<Vec<_>, _>>()?;

        if entries.is_empty() {
            return Ok(None);
        }

        // Verify all blobs actually exist on disk
        for e in &entries {
            if !self.blob_path(&e.blob_hash).exists() {
                return Ok(None);
            }
        }

        if let Ok(tx) = self.conn.unchecked_transaction() {
            let _ = tx.execute(
                "UPDATE actions SET hit_count = hit_count + 1 WHERE action_key = ?1",
                params![action_key],
            );
            if needs_touch {
                let _ = tx.execute(
                    "UPDATE blobs SET last_accessed = ?1
                     WHERE blob_hash IN (SELECT blob_hash FROM action_outputs WHERE action_key = ?2)",
                    params![now, action_key],
                );
            }
            let _ = tx.commit();
        }

        Ok(Some(entries))
    }

    /// Crash-safe Singleflight acquisition using OS kernel `flock` + monotonic fencing tokens.
    /// If another unaware agent is already computing `action_key`, this blocks on the kernel
    /// lock and returns `SingleflightOutcome::CacheHit { coalesced: true }` as soon as the
    /// leader publishes the result.
    pub fn acquire_singleflight(
        &mut self,
        action_key: &str,
        toolchain: &str,
        kind: &str,
        trust_domain: &str,
    ) -> Result<SingleflightOutcome> {
        let locks_dir = self.root.join("locks");
        let done_path = locks_dir.join(format!("{}.done", action_key));
        if trust_domain == "trusted" {
            if let Ok(done_bytes) = fs::read(&done_path) {
                if let Ok(outputs) = serde_json::from_slice::<Vec<BlobEntry>>(&done_bytes) {
                    if !outputs.is_empty()
                        && outputs.iter().all(|e| self.blob_path(&e.blob_hash).exists())
                    {
                        if let Ok(tx) = self.conn.unchecked_transaction() {
                            let _ = tx.execute(
                                "UPDATE actions SET hit_count = hit_count + 1 WHERE action_key = ?1",
                                params![action_key],
                            );
                            let _ = tx.commit();
                        }
                        return Ok(SingleflightOutcome::CacheHit {
                            outputs,
                            coalesced: false,
                        });
                    }
                }
            }
        }
        if let Some(outputs) = self.get_cached_action(action_key, trust_domain)? {
            return Ok(SingleflightOutcome::CacheHit {
                outputs,
                coalesced: false,
            });
        }

        let lock_path = locks_dir.join(format!("{}.lock", action_key));
        let waiters_path = locks_dir.join(format!("{}.waiters", action_key));
        let lock_file = OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .open(&lock_path)?;

        use std::os::unix::io::AsRawFd;
        let fd = lock_file.as_raw_fd();

        // Try non-blocking exclusive lock first
        let rc = unsafe { libc::flock(fd, libc::LOCK_EX | libc::LOCK_NB) };
        let mut waited_on_peer = false;

        if rc != 0 {
            // Another agent is currently running this exact action!
            waited_on_peer = true;
            let mut counted_by_leader = false;
            if let Ok(mut wf) = OpenOptions::new()
                .create(true)
                .read(true)
                .write(true)
                .open(&waiters_path)
            {
                let wfd = wf.as_raw_fd();
                if unsafe { libc::flock(wfd, libc::LOCK_EX) } == 0 {
                    let mut buf = Vec::new();
                    if wf.read_to_end(&mut buf).is_ok() && !buf.starts_with(b"S") {
                        if wf.write_all(b"1").is_ok() {
                            counted_by_leader = true;
                        }
                    }
                    unsafe {
                        libc::flock(wfd, libc::LOCK_UN);
                    }
                }
            }

            // Block in kernel on shared lock so all followers wake up in parallel as soon as leader finishes
            let wait_rc = unsafe { libc::flock(fd, libc::LOCK_SH) };
            if wait_rc != 0 {
                anyhow::bail!("flock wait failed for action {}", action_key);
            }

            if let Ok(done_bytes) = fs::read(&done_path) {
                if let Ok(outputs) = serde_json::from_slice::<Vec<BlobEntry>>(&done_bytes) {
                    if !outputs.is_empty() {
                        if !counted_by_leader {
                            if let Ok(tx) = self.conn.unchecked_transaction() {
                                let _ = tx.execute(
                                    "UPDATE actions SET hit_count = hit_count + 1 WHERE action_key = ?1",
                                    params![action_key],
                                );
                                let _ = tx.execute(
                                    "UPDATE meta_counters SET val = val + 1 WHERE name = 'coalesced_waits'",
                                    [],
                                );
                                let _ = tx.commit();
                            }
                        }
                        unsafe {
                            libc::flock(fd, libc::LOCK_UN);
                        }
                        return Ok(SingleflightOutcome::CacheHit {
                            outputs,
                            coalesced: true,
                        });
                    }
                }
            }

            // Leader did not write .done (e.g. crashed before publishing); upgrade to LOCK_EX for recovery
            let ex_rc = unsafe { libc::flock(fd, libc::LOCK_EX) };
            if ex_rc != 0 {
                anyhow::bail!("flock upgrade failed for action {}", action_key);
            }
        }

        // Now we hold LOCK_EX! If we waited on a peer, re-check if the prior holder completed the action
        if waited_on_peer {
            if let Some(outputs) = self.get_cached_action(action_key, trust_domain)? {
                let _ = self.conn.execute(
                    "UPDATE meta_counters SET val = val + 1 WHERE name = 'coalesced_waits'",
                    [],
                );
                unsafe {
                    libc::flock(fd, libc::LOCK_UN);
                }
                return Ok(SingleflightOutcome::CacheHit {
                    outputs,
                    coalesced: true,
                });
            }
        }

        if waited_on_peer {
            let _ = fs::remove_file(&done_path);
            let _ = fs::remove_file(&waiters_path);
        }

        Ok(SingleflightOutcome::Leader(SingleflightLease {
            action_key: action_key.to_string(),
            toolchain: toolchain.to_string(),
            kind: kind.to_string(),
            fencing_token: 0,
            lock_file,
        }))
    }

    /// Stage bytes into an immutable `0444` CAS blob and return its BLAKE3 hash.
    pub fn store_immutable_blob(&self, bytes: &[u8], kind: &str, trust_domain: &str, pin_level: i64) -> Result<String> {
        let hash = blake3::hash(bytes).to_hex().to_string();
        let dest = self.blob_path(&hash);

        let (inode, size) = if let Ok(meta) = fs::metadata(&dest) {
            (meta.ino() as i64, meta.len() as i64)
        } else {
            if let Some(parent) = dest.parent() {
                fs::create_dir_all(parent)?;
            }
            use std::os::unix::fs::OpenOptionsExt;
            let ino = match OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o444)
                .open(&dest)
            {
                Ok(mut f) => {
                    f.write_all(bytes)?;
                    f.metadata().map(|m| m.ino() as i64).unwrap_or(0)
                }
                Err(_) => {
                    let staging_path = self.root.join("staging").join(format!(
                        "{}.{}.tmp",
                        hash,
                        std::process::id()
                    ));
                    let mut f = OpenOptions::new()
                        .write(true)
                        .create(true)
                        .truncate(true)
                        .mode(0o444)
                        .open(&staging_path)?;
                    f.write_all(bytes)?;
                    let i = f.metadata().map(|m| m.ino() as i64).unwrap_or(0);
                    drop(f);
                    fs::rename(&staging_path, &dest)?;
                    i
                }
            };
            (ino, bytes.len() as i64)
        };
        let now = now_unix();

        self.conn.execute(
            "INSERT INTO blobs (blob_hash, kind, size_bytes, inode, created_at, last_accessed, pin_level, trust_domain)
             VALUES (?1, ?2, ?3, ?4, ?5, ?5, ?6, ?7)
             ON CONFLICT(blob_hash) DO UPDATE SET
                last_accessed = excluded.last_accessed,
                pin_level = MAX(blobs.pin_level, excluded.pin_level)",
            params![hash, kind, size, inode, now, pin_level, trust_domain],
        )?;

        Ok(hash)
    }

    /// Stage and insert multiple immutable `0444` CAS blobs in a single atomic SQLite transaction.
    /// Each item in `items` is `(blob_hash, bytes, kind, rel_path, size_bytes)`. If `blob_hash` is empty,
    /// it is computed via `blake3::hash(&bytes)`.
    pub fn batch_store_immutable_blobs(
        &mut self,
        items: &[(String, Vec<u8>, String, String, u64)],
        trust_domain: &str,
        pin_level: i64,
    ) -> Result<Vec<BlobEntry>> {
        if items.is_empty() {
            return Ok(Vec::new());
        }
        let now = now_unix();
        let pid = std::process::id();
        let mut entries = Vec::with_capacity(items.len());
        let mut seen_blobs: std::collections::HashMap<String, (i64, i64, String)> =
            std::collections::HashMap::with_capacity(items.len());
        let mut created_dirs: std::collections::HashSet<PathBuf> =
            std::collections::HashSet::new();

        for (pre_hash, bytes, kind, rel_path, size_bytes) in items {
            let hash = if pre_hash.is_empty() {
                blake3::hash(bytes).to_hex().to_string()
            } else {
                pre_hash.clone()
            };
            if !seen_blobs.contains_key(&hash) {
                let dest = self.blob_path(&hash);
                if !dest.exists() {
                    if let Some(parent) = dest.parent() {
                        if created_dirs.insert(parent.to_path_buf()) {
                            fs::create_dir_all(parent)?;
                        }
                    }
                    let staging_path = self
                        .root
                        .join("staging")
                        .join(format!("{}.{}.tmp", hash, pid));
                    fs::write(&staging_path, bytes)?;
                    let mut perms = fs::metadata(&staging_path)?.permissions();
                    perms.set_mode(0o444);
                    fs::set_permissions(&staging_path, perms)?;
                    fs::rename(&staging_path, &dest)?;
                }
                let meta = fs::metadata(&dest)?;
                let ino = meta.ino() as i64;
                let sz = meta.len() as i64;
                seen_blobs.insert(hash.clone(), (ino, sz, kind.clone()));
            }
            let actual_size = if *size_bytes > 0 {
                *size_bytes
            } else {
                bytes.len() as u64
            };
            entries.push(BlobEntry {
                blob_hash: hash,
                kind: kind.clone(),
                size_bytes: actual_size,
                rel_path: rel_path.clone(),
            });
        }

        let tx = self.conn.unchecked_transaction()?;
        {
            let mut ins_blob = tx.prepare_cached(
                "INSERT INTO blobs (blob_hash, kind, size_bytes, inode, created_at, last_accessed, pin_level, trust_domain)
                 VALUES (?1, ?2, ?3, ?4, ?5, ?5, ?6, ?7)
                 ON CONFLICT(blob_hash) DO UPDATE SET
                    last_accessed = excluded.last_accessed,
                    pin_level = MAX(blobs.pin_level, excluded.pin_level)",
            )?;
            for (hash, (inode, size, kind)) in &seen_blobs {
                ins_blob.execute(params![
                    hash,
                    kind,
                    size,
                    inode,
                    now,
                    pin_level,
                    trust_domain
                ])?;
            }
        }
        tx.commit()?;

        entries.sort_by(|a, b| a.rel_path.cmp(&b.rel_path));
        Ok(entries)
    }

    /// Batch-insert pre-linked immutable CAS blobs `(blob_hash, kind, size_bytes, inode)` in a single SQLite transaction.
    pub fn batch_register_linked_blobs(
        &mut self,
        blobs: &[(String, String, i64, i64)],
        trust_domain: &str,
        pin_level: i64,
    ) -> Result<()> {
        if blobs.is_empty() {
            return Ok(());
        }
        let now = now_unix();
        let tx = self.conn.unchecked_transaction()?;
        {
            let mut ins_blob = tx.prepare_cached(
                "INSERT INTO blobs (blob_hash, kind, size_bytes, inode, created_at, last_accessed, pin_level, trust_domain)
                 VALUES (?1, ?2, ?3, ?4, ?5, ?5, ?6, ?7)
                 ON CONFLICT(blob_hash) DO UPDATE SET
                    last_accessed = excluded.last_accessed,
                    pin_level = MAX(blobs.pin_level, excluded.pin_level)",
            )?;
            for (hash, kind, size, inode) in blobs {
                ins_blob.execute(params![
                    hash,
                    kind,
                    size,
                    inode,
                    now,
                    pin_level,
                    trust_domain
                ])?;
            }
        }
        tx.commit()?;
        Ok(())
    }

    /// Batch-publish multiple verified theorem shard receipts in a single atomic SQLite transaction.
    pub fn has_completed_action(&self, action_key: &str) -> bool {
        self.conn
            .query_row(
                "SELECT 1 FROM actions WHERE action_key = ?1 AND status = 'completed'",
                params![action_key],
                |_| Ok(()),
            )
            .is_ok()
    }

    pub fn has_cached_action_readonly(
        &self,
        action_key: &str,
        trust_domain: &str,
    ) -> Result<bool> {
        let mut stmt = self.conn.prepare_cached(
            "SELECT ao.blob_hash
             FROM actions a
             JOIN action_outputs ao ON ao.action_key = a.action_key
             WHERE a.action_key = ?1 AND a.trust_domain = ?2 AND a.status = 'completed'",
        )?;
        let hashes: Vec<String> = stmt
            .query_map(params![action_key, trust_domain], |row| row.get(0))?
            .collect::<std::result::Result<Vec<_>, _>>()?;
        if hashes.is_empty() {
            return Ok(false);
        }
        for h in &hashes {
            if !self.blob_path(h).exists() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn batch_get_theorem_shards_readonly(
        &self,
        shard_keys: &[String],
        trust_domain: &str,
    ) -> Result<std::collections::HashMap<String, String>> {
        if shard_keys.is_empty() {
            return Ok(std::collections::HashMap::new());
        }
        let mut verified = std::collections::HashMap::with_capacity(shard_keys.len());
        let mut exists_cache: std::collections::HashMap<String, bool> =
            std::collections::HashMap::new();
        let mut sel_stmt = self.conn.prepare_cached(
            "SELECT ao.blob_hash
             FROM actions a
             JOIN action_outputs ao ON ao.action_key = a.action_key
             WHERE a.action_key = ?1 AND a.status = 'completed' AND a.trust_domain = ?2
             LIMIT 1",
        )?;
        for key in shard_keys {
            if let Some(blob_hash) = sel_stmt
                .query_row(params![key, trust_domain], |r| r.get::<_, String>(0))
                .optional()?
            {
                let exists = *exists_cache
                    .entry(blob_hash.clone())
                    .or_insert_with(|| self.blob_path(&blob_hash).exists());
                if exists {
                    verified.insert(key.clone(), blob_hash);
                }
            }
        }
        Ok(verified)
    }

    pub fn batch_increment_action_hits(&self, action_keys: &[String]) -> Result<()> {
        if action_keys.is_empty() {
            return Ok(());
        }
        let tx = self.conn.unchecked_transaction()?;
        {
            let mut upd = tx.prepare_cached(
                "UPDATE actions SET hit_count = hit_count + 1 WHERE action_key = ?1",
            )?;
            for k in action_keys {
                let _ = upd.execute(params![k]);
            }
        }
        tx.commit()?;
        Ok(())
    }

    pub fn prestage_theorem_shard_blobs(
        &self,
        items: &[(String, String, Vec<u8>, i64)],
    ) -> Result<()> {
        prestage_theorem_shard_blobs_at(&self.root, items)
    }

    pub fn begin_inflight_publish_theorem_shards(
        &self,
        toolchain: &str,
        trust_domain: &str,
        items: &[(String, String, Vec<u8>, i64)],
    ) -> Result<()> {
        if items.is_empty() {
            return Ok(());
        }
        let now = now_unix();
        let pid = std::process::id();
        let mut staged = Vec::with_capacity(items.len());
        let mut seen_blobs: std::collections::HashMap<String, (i64, i64)> =
            std::collections::HashMap::with_capacity(items.len());
        let mut seen_prefix = [false; 256];
        let mut newly_created_prefix = [false; 256];

        for (action_key, decl_name, receipt_bytes, dur_ms) in items {
            let hash = blake3::hash(receipt_bytes).to_hex().to_string();
            let (inode, size) = if let Some(&(ino, sz)) = seen_blobs.get(&hash) {
                (ino, sz)
            } else {
                let dest = self.blob_path(&hash);
                let prefix = if hash.len() >= 2 { &hash[..2] } else { "00" };
                let p_idx = u8::from_str_radix(prefix, 16).unwrap_or(0) as usize;
                if !seen_prefix[p_idx] {
                    seen_prefix[p_idx] = true;
                    if let Some(parent) = dest.parent() {
                        if fs::create_dir(parent).is_ok() {
                            newly_created_prefix[p_idx] = true;
                        }
                    }
                }
                let (ino, sz) = if !newly_created_prefix[p_idx]
                    && fs::metadata(&dest).is_ok()
                {
                    (0i64, receipt_bytes.len() as i64)
                } else {
                    use std::os::unix::fs::OpenOptionsExt;
                    match OpenOptions::new()
                        .write(true)
                        .create_new(true)
                        .mode(0o444)
                        .open(&dest)
                    {
                        Ok(mut f) => {
                            f.write_all(receipt_bytes)?;
                        }
                        Err(_) => {
                            let staging_path = self
                                .root
                                .join("staging")
                                .join(format!("{}.{}.tmp", hash, pid));
                            let mut f = OpenOptions::new()
                                .write(true)
                                .create(true)
                                .truncate(true)
                                .mode(0o444)
                                .open(&staging_path)?;
                            f.write_all(receipt_bytes)?;
                            drop(f);
                            let _ = fs::rename(&staging_path, &dest);
                        }
                    }
                    (0i64, receipt_bytes.len() as i64)
                };
                seen_blobs.insert(hash.clone(), (ino, sz));
                (ino, sz)
            };
            staged.push((
                action_key.as_str(),
                decl_name.as_str(),
                hash,
                inode,
                size,
                *dur_ms,
            ));
        }

        self.conn.execute_batch(
            "PRAGMA foreign_keys = OFF; PRAGMA synchronous = OFF; BEGIN IMMEDIATE;",
        )?;
        let res = (|| -> Result<()> {
            let end_fencing_token: i64 = {
                let mut upd_seq = self.conn.prepare_cached(
                    "UPDATE meta_counters SET val = val + ?1 WHERE name = 'fencing_seq' RETURNING val",
                )?;
                upd_seq.query_row(params![staged.len() as i64], |r| r.get(0))?
            };
            let base_fencing_token = end_fencing_token - (staged.len() as i64);
            let mut ins_blob = self.conn.prepare_cached(
                "INSERT INTO blobs (blob_hash, kind, size_bytes, inode, created_at, last_accessed, pin_level, trust_domain)
                 VALUES (?1, 'expr_shard', ?2, ?3, ?4, ?4, 0, ?5)
                 ON CONFLICT(blob_hash) DO UPDATE SET last_accessed = excluded.last_accessed",
            )?;
            let mut ins_act = self.conn.prepare_cached(
                "INSERT INTO actions (action_key, toolchain_githash, kind, status, fencing_token,
                                      output_manifest_hash, duration_ms, peak_pss_bytes, heartbeats, trust_domain, updated_at)
                 VALUES (?1, ?2, 'theorem_shard', 'completed', ?3, ?4, ?5, 0, 0, ?6, ?7)
                 ON CONFLICT(action_key) DO UPDATE SET
                    status = 'completed',
                    fencing_token = excluded.fencing_token,
                    output_manifest_hash = excluded.output_manifest_hash,
                    duration_ms = excluded.duration_ms,
                    updated_at = excluded.updated_at",
            )?;
            let mut ins_out = self.conn.prepare_cached(
                "INSERT OR REPLACE INTO action_outputs (action_key, rel_path, blob_hash)
                 VALUES (?1, ?2, ?3)",
            )?;

            let mut inserted_blobs = std::collections::HashSet::with_capacity(seen_blobs.len());
            for (idx, (action_key, decl_name, blob_hash, inode, size, dur_ms)) in
                staged.into_iter().enumerate()
            {
                if inserted_blobs.insert(blob_hash.clone()) {
                    ins_blob.execute(params![blob_hash, size, inode, now, trust_domain])?;
                }
                let fencing_token = base_fencing_token + (idx as i64) + 1;
                let rel_path = format!("thm:{}", decl_name);
                let mut mh = blake3::Hasher::new();
                mh.update(rel_path.as_bytes());
                mh.update(b":");
                mh.update(blob_hash.as_bytes());
                mh.update(b"\n");
                let manifest_hash = mh.finalize().to_hex().to_string();

                ins_act.execute(params![
                    action_key,
                    toolchain,
                    fencing_token,
                    manifest_hash,
                    dur_ms,
                    trust_domain,
                    now
                ])?;
                ins_out.execute(params![action_key, rel_path, blob_hash])?;
            }
            Ok(())
        })();
        if res.is_err() {
            let _ = self
                .conn
                .execute_batch("ROLLBACK; PRAGMA synchronous = NORMAL; PRAGMA foreign_keys = ON;");
        }
        res
    }

    pub fn commit_inflight_publish(&self) -> Result<()> {
        let res = self.conn.execute_batch("COMMIT;");
        let _ = self
            .conn
            .execute_batch("PRAGMA synchronous = NORMAL; PRAGMA foreign_keys = ON;");
        let _ = fs::remove_file(self.root.join("locks").join("cached_portable_manifest.json"));
        res?;
        Ok(())
    }

    pub fn commit_inflight_publish_for_lease(&self, action_key: &str) -> Result<()> {
        let waiters = self.seal_singleflight_waiters(action_key);
        if waiters > 0 {
            let _ = self.conn.execute(
                "UPDATE actions SET hit_count = hit_count + ?1 WHERE action_key = ?2",
                params![waiters, action_key],
            );
            let _ = self.conn.execute(
                "UPDATE meta_counters SET val = val + ?1 WHERE name = 'coalesced_waits'",
                params![waiters],
            );
        }
        self.commit_inflight_publish()
    }

    pub fn rollback_inflight_publish(&self) {
        let _ = self
            .conn
            .execute_batch("ROLLBACK; PRAGMA synchronous = NORMAL; PRAGMA foreign_keys = ON;");
    }

    pub fn batch_publish_theorem_shards(
        &mut self,
        toolchain: &str,
        trust_domain: &str,
        items: &[(String, String, Vec<u8>, i64)],
    ) -> Result<()> {
        if items.is_empty() {
            return Ok(());
        }
        self.begin_inflight_publish_theorem_shards(toolchain, trust_domain, items)?;
        self.commit_inflight_publish()
    }

    fn seal_singleflight_waiters(&self, action_key: &str) -> i64 {
        use std::os::unix::io::AsRawFd;
        let waiters_path = self.root.join("locks").join(format!("{}.waiters", action_key));
        let mut count = 0i64;
        if let Ok(mut wf) = OpenOptions::new().read(true).write(true).open(&waiters_path) {
            let wfd = wf.as_raw_fd();
            if unsafe { libc::flock(wfd, libc::LOCK_EX) } == 0 {
                let mut buf = Vec::new();
                if wf.read_to_end(&mut buf).is_ok() && !buf.starts_with(b"S") {
                    count = buf.iter().filter(|&&b| b == b'1').count() as i64;
                }
                let _ = wf.set_len(0);
                let _ = std::io::Seek::seek(&mut wf, std::io::SeekFrom::Start(0));
                let _ = wf.write_all(b"S");
                let _ = fs::remove_file(&waiters_path);
                unsafe {
                    libc::flock(wfd, libc::LOCK_UN);
                }
            }
        }
        count
    }

    pub fn write_singleflight_done(&self, action_key: &str, outputs: &[BlobEntry]) {
        let done_path = self.root.join("locks").join(format!("{}.done", action_key));
        if let Ok(bytes) = serde_json::to_vec(outputs) {
            let _ = fs::write(&done_path, &bytes);
        }
    }

    pub fn remove_singleflight_done(&self, action_key: &str) {
        let done_path = self.root.join("locks").join(format!("{}.done", action_key));
        let _ = fs::remove_file(&done_path);
    }

    /// Fence-checked publication of all outputs for an action.
    pub fn publish_action(
        &mut self,
        lease: &SingleflightLease,
        outputs: &[BlobEntry],
        duration_ms: i64,
        peak_pss_bytes: i64,
        heartbeats: i64,
        trust_domain: &str,
    ) -> Result<String> {
        let mut manifest_hasher = blake3::Hasher::new();
        for o in outputs {
            manifest_hasher.update(o.rel_path.as_bytes());
            manifest_hasher.update(b":");
            manifest_hasher.update(o.blob_hash.as_bytes());
            manifest_hasher.update(b"\n");
        }
        let manifest_hash = manifest_hasher.finalize().to_hex().to_string();
        let waiters = self.seal_singleflight_waiters(&lease.action_key);

        let now = now_unix();
        let _ = self
            .conn
            .execute_batch("PRAGMA foreign_keys = OFF; PRAGMA synchronous = OFF;");
        let tx = self.conn.unchecked_transaction()?;
        tx.execute(
            "UPDATE meta_counters SET val = val + 1 WHERE name = 'fencing_seq'",
            [],
        )?;
        let fencing_token: i64 = tx.query_row(
            "SELECT val FROM meta_counters WHERE name = 'fencing_seq'",
            [],
            |r| r.get(0),
        )?;

        tx.execute(
            "INSERT INTO actions (action_key, toolchain_githash, kind, status, fencing_token,
                                  output_manifest_hash, duration_ms, peak_pss_bytes, heartbeats, trust_domain, updated_at, hit_count)
             VALUES (?1, ?2, ?3, 'completed', ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11)
             ON CONFLICT(action_key) DO UPDATE SET
                status = 'completed',
                fencing_token = excluded.fencing_token,
                output_manifest_hash = excluded.output_manifest_hash,
                duration_ms = excluded.duration_ms,
                peak_pss_bytes = excluded.peak_pss_bytes,
                heartbeats = excluded.heartbeats,
                trust_domain = excluded.trust_domain,
                updated_at = excluded.updated_at,
                hit_count = actions.hit_count + excluded.hit_count",
            params![
                lease.action_key,
                lease.toolchain,
                lease.kind,
                fencing_token,
                manifest_hash,
                duration_ms,
                peak_pss_bytes,
                heartbeats,
                trust_domain,
                now,
                waiters
            ],
        )?;

        tx.execute(
            "DELETE FROM action_outputs WHERE action_key = ?1",
            params![lease.action_key],
        )?;

        {
            let mut ins_out = tx.prepare_cached(
                "INSERT INTO action_outputs (action_key, rel_path, blob_hash) VALUES (?1, ?2, ?3)",
            )?;
            for o in outputs {
                ins_out.execute(params![lease.action_key, o.rel_path, o.blob_hash])?;
            }
        }

        if waiters > 0 {
            tx.execute(
                "UPDATE meta_counters SET val = val + ?1 WHERE name = 'coalesced_waits'",
                params![waiters],
            )?;
        }

        let commit_res = tx.commit();
        let _ = self
            .conn
            .execute_batch("PRAGMA synchronous = NORMAL; PRAGMA foreign_keys = ON;");
        let _ = fs::remove_file(self.root.join("locks").join("cached_portable_manifest.json"));
        commit_res?;
        self.write_singleflight_done(&lease.action_key, outputs);
        Ok(manifest_hash)
    }

    /// Stage an immutable CAS blob and fence-publish its single-output action in one atomic SQLite transaction.
    pub fn publish_action_with_blob(
        &mut self,
        lease: &SingleflightLease,
        bytes: &[u8],
        kind: &str,
        rel_path: &str,
        duration_ms: i64,
        trust_domain: &str,
    ) -> Result<String> {
        let blob_hash = blake3::hash(bytes).to_hex().to_string();
        let dest = self.blob_path(&blob_hash);
        let (inode, size) = if let Ok(meta) = fs::metadata(&dest) {
            (meta.ino() as i64, meta.len() as i64)
        } else {
            if let Some(parent) = dest.parent() {
                fs::create_dir_all(parent)?;
            }
            use std::os::unix::fs::OpenOptionsExt;
            let ino = match OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o444)
                .open(&dest)
            {
                Ok(mut f) => {
                    f.write_all(bytes)?;
                    f.metadata().map(|m| m.ino() as i64).unwrap_or(0)
                }
                Err(_) => {
                    let staging_path = self.root.join("staging").join(format!(
                        "{}.{}.tmp",
                        blob_hash,
                        std::process::id()
                    ));
                    let mut f = OpenOptions::new()
                        .write(true)
                        .create(true)
                        .truncate(true)
                        .mode(0o444)
                        .open(&staging_path)?;
                    f.write_all(bytes)?;
                    let i = f.metadata().map(|m| m.ino() as i64).unwrap_or(0);
                    drop(f);
                    fs::rename(&staging_path, &dest)?;
                    i
                }
            };
            (ino, bytes.len() as i64)
        };

        let mut manifest_hasher = blake3::Hasher::new();
        manifest_hasher.update(rel_path.as_bytes());
        manifest_hasher.update(b":");
        manifest_hasher.update(blob_hash.as_bytes());
        manifest_hasher.update(b"\n");
        let manifest_hash = manifest_hasher.finalize().to_hex().to_string();
        let waiters = self.seal_singleflight_waiters(&lease.action_key);

        let now = now_unix();
        self.conn.execute_batch(
            "PRAGMA foreign_keys = OFF; PRAGMA synchronous = OFF; BEGIN IMMEDIATE;",
        )?;
        let commit_res = (|| -> Result<()> {
            let fencing_token: i64 = {
                let mut upd_seq = self.conn.prepare_cached(
                    "UPDATE meta_counters SET val = val + 1 WHERE name = 'fencing_seq' RETURNING val",
                )?;
                upd_seq.query_row([], |r| r.get(0))?
            };

            let mut ins_blob = self.conn.prepare_cached(
                "INSERT INTO blobs (blob_hash, kind, size_bytes, inode, created_at, last_accessed, pin_level, trust_domain)
                 VALUES (?1, ?2, ?3, ?4, ?5, ?5, 0, ?6)
                 ON CONFLICT(blob_hash) DO UPDATE SET last_accessed = excluded.last_accessed",
            )?;
            ins_blob.execute(params![blob_hash, kind, size, inode, now, trust_domain])?;

            let mut ins_act = self.conn.prepare_cached(
                "INSERT INTO actions (action_key, toolchain_githash, kind, status, fencing_token,
                                      output_manifest_hash, duration_ms, peak_pss_bytes, heartbeats, trust_domain, updated_at, hit_count)
                 VALUES (?1, ?2, ?3, 'completed', ?4, ?5, ?6, 0, 0, ?7, ?8, ?9)
                 ON CONFLICT(action_key) DO UPDATE SET
                    status = 'completed',
                    fencing_token = excluded.fencing_token,
                    output_manifest_hash = excluded.output_manifest_hash,
                    duration_ms = excluded.duration_ms,
                    peak_pss_bytes = 0,
                    heartbeats = 0,
                    trust_domain = excluded.trust_domain,
                    updated_at = excluded.updated_at,
                    hit_count = actions.hit_count + excluded.hit_count",
            )?;
            ins_act.execute(params![
                lease.action_key,
                lease.toolchain,
                lease.kind,
                fencing_token,
                manifest_hash,
                duration_ms,
                trust_domain,
                now,
                waiters
            ])?;

            let mut ins_out = self.conn.prepare_cached(
                "INSERT OR REPLACE INTO action_outputs (action_key, rel_path, blob_hash) VALUES (?1, ?2, ?3)",
            )?;
            ins_out.execute(params![lease.action_key, rel_path, blob_hash])?;

            if waiters > 0 {
                let mut upd_waits = self.conn.prepare_cached(
                    "UPDATE meta_counters SET val = val + ?1 WHERE name = 'coalesced_waits'",
                )?;
                upd_waits.execute(params![waiters])?;
            }
            self.conn.execute_batch("COMMIT; PRAGMA synchronous = NORMAL; PRAGMA foreign_keys = ON;")?;
            Ok(())
        })();
        if commit_res.is_err() {
            let _ = self
                .conn
                .execute_batch("ROLLBACK; PRAGMA synchronous = NORMAL; PRAGMA foreign_keys = ON;");
        }
        let _ = fs::remove_file(self.root.join("locks").join("cached_portable_manifest.json"));
        commit_res?;
        let single_out = [BlobEntry {
            blob_hash,
            kind: kind.to_string(),
            size_bytes: size as u64,
            rel_path: rel_path.to_string(),
        }];
        self.write_singleflight_done(&lease.action_key, &single_out);
        Ok(manifest_hash)
    }

    pub fn record_attestation(
        &self,
        action_key: &str,
        checker_name: &str,
        checker_version: &str,
        axioms: &[String],
        signature: Option<&str>,
    ) -> Result<()> {
        let axioms_json = serde_json::to_string(axioms)?;
        let now = now_unix();
        self.conn.execute(
            "INSERT INTO attestations (action_key, checker_name, checker_version, axioms_json, signature, verified_at)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6)
             ON CONFLICT(action_key, checker_name) DO UPDATE SET
                checker_version = excluded.checker_version,
                axioms_json = excluded.axioms_json,
                signature = excluded.signature,
                verified_at = excluded.verified_at",
            params![action_key, checker_name, checker_version, axioms_json, signature, now],
        )?;
        Ok(())
    }

    /// Single-transaction publication of an ingested worktree build action:
    /// atomically registers `reg_blobs`, publishes `action_key` + `outputs`, records
    /// `worktrees` + `worktree_installations`, optionally caches `lake_env`, and optionally
    /// records a verification `attestation`.
    #[allow(clippy::too_many_arguments)]
    pub fn publish_ingested_worktree_action(
        &mut self,
        lease_opt: Option<&SingleflightLease>,
        action_key: &str,
        toolchain: &str,
        kind: &str,
        worktree_root: &Path,
        project_name: &str,
        reg_blobs: &[(String, String, i64, i64)],
        outputs: &[BlobEntry],
        duration_ms: i64,
        trust_domain: &str,
        pin_level: i64,
        lake_env: Option<(&str, &std::collections::HashMap<String, String>)>,
        attestation: Option<(&str, &str, &[String], Option<&str>)>,
    ) -> Result<(String, usize)> {
        let mut manifest_hasher = blake3::Hasher::new();
        for o in outputs {
            manifest_hasher.update(o.rel_path.as_bytes());
            manifest_hasher.update(b":");
            manifest_hasher.update(o.blob_hash.as_bytes());
            manifest_hasher.update(b"\n");
        }
        let manifest_hash = manifest_hasher.finalize().to_hex().to_string();
        let waiters = if lease_opt.is_some() {
            self.seal_singleflight_waiters(action_key)
        } else {
            0
        };

        let canon_root = worktree_root
            .canonicalize()
            .unwrap_or_else(|_| worktree_root.to_path_buf());
        let root_str = canon_root.to_string_lossy().to_string();
        let wt_id = blake3::hash(root_str.as_bytes()).to_hex().to_string();
        let now = now_unix();

        let _ = self
            .conn
            .execute_batch("PRAGMA foreign_keys = OFF; PRAGMA synchronous = OFF;");
        let tx = self.conn.unchecked_transaction()?;

        tx.execute(
            "UPDATE meta_counters SET val = val + 1 WHERE name = 'fencing_seq'",
            [],
        )?;
        let fencing_token: i64 = tx.query_row(
            "SELECT val FROM meta_counters WHERE name = 'fencing_seq'",
            [],
            |r| r.get(0),
        )?;

        if !reg_blobs.is_empty() {
            let mut ins_blob = tx.prepare_cached(
                "INSERT INTO blobs (blob_hash, kind, size_bytes, inode, created_at, last_accessed, pin_level, trust_domain)
                 VALUES (?1, ?2, ?3, ?4, ?5, ?5, ?6, ?7)
                 ON CONFLICT(blob_hash) DO UPDATE SET
                    last_accessed = excluded.last_accessed,
                    pin_level = MAX(blobs.pin_level, excluded.pin_level)",
            )?;
            for (hash, bkind, size, inode) in reg_blobs {
                ins_blob.execute(params![
                    hash,
                    bkind,
                    size,
                    inode,
                    now,
                    pin_level,
                    trust_domain
                ])?;
            }
        }

        tx.execute(
            "INSERT INTO actions (action_key, toolchain_githash, kind, status, fencing_token,
                                  output_manifest_hash, duration_ms, peak_pss_bytes, heartbeats, trust_domain, updated_at, hit_count)
             VALUES (?1, ?2, ?3, 'completed', ?4, ?5, ?6, 0, 0, ?7, ?8, ?9)
             ON CONFLICT(action_key) DO UPDATE SET
                status = 'completed',
                fencing_token = excluded.fencing_token,
                output_manifest_hash = excluded.output_manifest_hash,
                duration_ms = excluded.duration_ms,
                trust_domain = excluded.trust_domain,
                updated_at = excluded.updated_at,
                hit_count = actions.hit_count + excluded.hit_count",
            params![
                action_key,
                toolchain,
                kind,
                fencing_token,
                manifest_hash,
                duration_ms,
                trust_domain,
                now,
                waiters
            ],
        )?;

        tx.execute(
            "DELETE FROM action_outputs WHERE action_key = ?1",
            params![action_key],
        )?;
        {
            let mut ins_out = tx.prepare_cached(
                "INSERT INTO action_outputs (action_key, rel_path, blob_hash) VALUES (?1, ?2, ?3)",
            )?;
            for o in outputs {
                ins_out.execute(params![action_key, o.rel_path, o.blob_hash])?;
            }
        }

        if waiters > 0 {
            tx.execute(
                "UPDATE meta_counters SET val = val + ?1 WHERE name = 'coalesced_waits'",
                params![waiters],
            )?;
        }

        record_worktree_outputs_and_supersede(&tx, &wt_id, &root_str, project_name, now, outputs)?;

        let mut linked = 0usize;
        {
            let mut ins_inst = tx.prepare_cached(
                "INSERT INTO worktree_installations (worktree_id, rel_path, blob_hash, link_mode)
                 VALUES (?1, ?2, ?3, 'hardlink')
                 ON CONFLICT(worktree_id, rel_path) DO UPDATE SET
                    blob_hash = excluded.blob_hash, link_mode = excluded.link_mode",
            )?;
            for out in outputs {
                if !out.rel_path.starts_with("thm:") {
                    ins_inst.execute(params![wt_id, out.rel_path, out.blob_hash])?;
                    linked += 1;
                }
            }
        }

        if let Some((env_key, env_map)) = lake_env {
            if !env_map.is_empty() {
                let env_json = serde_json::to_string(env_map)?;
                tx.execute(
                    "INSERT INTO lake_env_cache (project_key, env_json, updated_at) VALUES (?1, ?2, ?3)
                     ON CONFLICT(project_key) DO UPDATE SET env_json = excluded.env_json, updated_at = excluded.updated_at",
                    params![env_key, env_json, now],
                )?;
            }
        }

        if let Some((checker_name, checker_version, axioms, signature)) = attestation {
            let axioms_json = serde_json::to_string(axioms)?;
            tx.execute(
                "INSERT INTO attestations (action_key, checker_name, checker_version, axioms_json, signature, verified_at)
                 VALUES (?1, ?2, ?3, ?4, ?5, ?6)
                 ON CONFLICT(action_key, checker_name) DO UPDATE SET
                    checker_version = excluded.checker_version, axioms_json = excluded.axioms_json,
                    signature = excluded.signature, verified_at = excluded.verified_at",
                params![action_key, checker_name, checker_version, axioms_json, signature, now],
            )?;
        }

        let commit_res = tx.commit();
        let _ = self.conn.execute_batch("PRAGMA synchronous = NORMAL; PRAGMA foreign_keys = ON;");
        let _ = fs::remove_file(self.root.join("locks").join("cached_portable_manifest.json"));
        commit_res?;
        self.write_singleflight_done(action_key, outputs);
        Ok((manifest_hash, linked))
    }

    /// Materialize CAS blobs into a worktree using FICLONE reflink (if supported),
    /// or safe unlink + 0444 hardlink (protecting mmap Shared_Clean inodes from SIGBUS truncation),
    /// or copy fallback across filesystems.
    pub fn materialize_into_worktree(
        &mut self,
        worktree_root: &Path,
        project_name: &str,
        outputs: &[BlobEntry],
    ) -> Result<usize> {
        let canon_root = worktree_root.canonicalize().unwrap_or_else(|_| worktree_root.to_path_buf());
        let root_str = canon_root.to_string_lossy().to_string();
        let wt_id = blake3::hash(root_str.as_bytes()).to_hex().to_string();
        let now = now_unix();

        let blobs_root = self.root.join("blobs");
        let wt_last_seen: Option<i64> = self
            .conn
            .query_row("SELECT last_seen FROM worktrees WHERE worktree_id = ?1", params![wt_id], |r| r.get(0))
            .ok();

        let mut existing_map: std::collections::HashMap<String, String> =
            std::collections::HashMap::with_capacity(outputs.len());
        {
            let mut q_stmt = self.conn.prepare_cached(
                "SELECT rel_path, blob_hash FROM worktree_installations WHERE worktree_id = ?1",
            )?;
            let rows = q_stmt.query_map(params![wt_id], |r| Ok((r.get::<_, String>(0)?, r.get::<_, String>(1)?)))?;
            for row in rows {
                let (rp, bh) = row?;
                existing_map.insert(rp, bh);
            }
        }

        let mut created_dirs: std::collections::HashSet<PathBuf> = std::collections::HashSet::new();
        let mut linked = 0usize;
        let mut db_updates: Vec<(&str, &str, &'static str)> = Vec::new();

        for out in outputs {
            if out.rel_path.starts_with("thm:") {
                continue;
            }
            let prefix = if out.blob_hash.len() >= 2 { &out.blob_hash[0..2] } else { "00" };
            let src = self
                .ensure_blob_uncompressed(&out.blob_hash)
                .unwrap_or_else(|_| blobs_root.join(prefix).join(&out.blob_hash));
            let dst = canon_root.join(&out.rel_path);

            let already_same_inode = match (fs::metadata(&src), fs::metadata(&dst)) {
                (Ok(src_meta), Ok(dst_meta)) => {
                    (src_meta.dev() == dst_meta.dev() && src_meta.ino() == dst_meta.ino())
                        || (src_meta.dev() != dst_meta.dev()
                            && src_meta.len() == dst_meta.len()
                            && (dst_meta.permissions().mode() & 0o222) == 0)
                }
                _ => false,
            };

            if already_same_inode {
                if existing_map.get(&out.rel_path) != Some(&out.blob_hash) {
                    db_updates.push((&out.rel_path, &out.blob_hash, "hardlink"));
                }
                linked += 1;
                continue;
            }

            if let Some(parent) = dst.parent() {
                if created_dirs.insert(parent.to_path_buf()) {
                    fs::create_dir_all(parent)?;
                }
            }

            let mode = try_reflink_or_hardlink(&src, &dst)?;
            if existing_map.get(&out.rel_path) != Some(&out.blob_hash) {
                db_updates.push((&out.rel_path, &out.blob_hash, mode));
            }
            linked += 1;
        }

        if db_updates.is_empty() && wt_last_seen.map(|ls| now - ls < 60).unwrap_or(false) {
            return Ok(linked);
        }

        let tx = self.conn.unchecked_transaction()?;
        record_worktree_outputs_and_supersede(&tx, &wt_id, &root_str, project_name, now, outputs)?;
        if !db_updates.is_empty() {
            let mut ins_inst = tx.prepare_cached(
                "INSERT INTO worktree_installations (worktree_id, rel_path, blob_hash, link_mode)
                 VALUES (?1, ?2, ?3, ?4)
                 ON CONFLICT(worktree_id, rel_path) DO UPDATE SET
                    blob_hash = excluded.blob_hash, link_mode = excluded.link_mode",
            )?;
            for (rel_path, blob_hash, mode) in db_updates {
                ins_inst.execute(params![wt_id, rel_path, blob_hash, mode])?;
            }
        }
        tx.commit()?;
        Ok(linked)
    }

    /// Ensure a CAS blob on disk is uncompressed (if it was cold-compressed with `TLZ1`),
    /// atomically rewriting it back to raw `0o444` bytes in the Hot tier so it can be hardlinked.
    pub fn ensure_blob_uncompressed(&self, blob_hash: &str) -> Result<PathBuf> {
        let src = self.blob_path(blob_hash);
        let mut f = match File::open(&src) {
            Ok(file) => file,
            Err(_) => return Ok(src),
        };
        let mut magic = [0u8; 4];
        if f.read_exact(&mut magic).is_ok() && &magic == b"TLZ1" {
            drop(f);
            let compressed = fs::read(&src)?;
            let raw = decompress_tlz1(&compressed)
                .ok_or_else(|| anyhow::anyhow!("Failed to decompress TLZ1 blob {}", blob_hash))?;
            let staging_dir = self.root.join("staging");
            let _ = fs::create_dir_all(&staging_dir);
            let staging_path = staging_dir.join(format!(
                "{}.{}.hot.tmp",
                blob_hash,
                std::process::id()
            ));
            {
                use std::os::unix::fs::OpenOptionsExt;
                let mut out = OpenOptions::new()
                    .write(true)
                    .create(true)
                    .truncate(true)
                    .mode(0o444)
                    .open(&staging_path)?;
                out.write_all(&raw)?;
            }
            fs::rename(&staging_path, &src)?;
            if let Ok(meta) = fs::metadata(&src) {
                let _ = self.conn.execute(
                    "UPDATE blobs SET inode = ?1, last_accessed = ?2 WHERE blob_hash = ?3",
                    params![meta.ino() as i64, now_unix(), blob_hash],
                );
            }
        }
        Ok(src)
    }

    /// Restore a CAS blob to `dest_path`, transparently re-promoting cold `TLZ1`-compressed
    /// blobs back to raw `0o444` Hot-tier bytes before hardlinking/copying.
    pub fn restore_blob_to_path(&self, blob_hash: &str, dest_path: &Path) -> Result<&'static str> {
        let src = self.ensure_blob_uncompressed(blob_hash)?;
        if let Some(parent) = dest_path.parent() {
            fs::create_dir_all(parent)?;
        }
        try_reflink_or_hardlink(&src, dest_path)
    }

    /// Record an active worktree lease and its active file->blob mappings.
    /// Marks any superseded intermediate draft blobs (no longer referenced by any active lease
    /// within the last 7200s and having `pin_level == 0`) with `pin_level = -1` for immediate GC.
    pub fn update_worktree_lease(
        &self,
        worktree_path: &Path,
        head_commit: &str,
        active_file_blobs: &[(String, String)],
    ) -> Result<usize> {
        let wt_path_str = worktree_path.to_string_lossy().to_string();
        let worktree_id = blake3::hash(wt_path_str.as_bytes()).to_hex().to_string();
        let now = now_unix();
        let pid = std::process::id() as i64;

        let tx = self.conn.unchecked_transaction()?;
        tx.execute(
            "INSERT INTO worktree_leases (worktree_id, worktree_path, pid, head_commit, last_seen)
             VALUES (?1, ?2, ?3, ?4, ?5)
             ON CONFLICT(worktree_id) DO UPDATE SET
                worktree_path = excluded.worktree_path,
                pid = excluded.pid,
                head_commit = excluded.head_commit,
                last_seen = excluded.last_seen",
            params![worktree_id, wt_path_str, pid, head_commit, now],
        )?;

        let mut superseded_candidates = std::collections::HashSet::new();
        {
            let mut q_old = tx.prepare_cached(
                "SELECT blob_hash FROM worktree_file_blobs WHERE worktree_id = ?1 AND rel_path = ?2",
            )?;
            let mut ups_wfb = tx.prepare_cached(
                "INSERT INTO worktree_file_blobs (worktree_id, rel_path, blob_hash, updated_at)
                 VALUES (?1, ?2, ?3, ?4)
                 ON CONFLICT(worktree_id, rel_path) DO UPDATE SET
                    blob_hash = excluded.blob_hash,
                    updated_at = excluded.updated_at",
            )?;
            let mut revive_blob = tx.prepare_cached(
                "UPDATE blobs SET pin_level = 0, last_accessed = ?2 WHERE blob_hash = ?1 AND pin_level < 0",
            )?;

            for (rel_path, blob_hash) in active_file_blobs {
                let old_bh: Option<String> = q_old
                    .query_row(params![worktree_id, rel_path], |r| r.get(0))
                    .optional()?;
                if let Some(prev) = old_bh {
                    if prev != *blob_hash {
                        superseded_candidates.insert(prev);
                    }
                }
                ups_wfb.execute(params![worktree_id, rel_path, blob_hash, now])?;
                let _ = revive_blob.execute(params![blob_hash, now]);
            }
        }

        let mut newly_superseded = 0usize;
        if !superseded_candidates.is_empty() {
            let mut check_active = tx.prepare_cached(
                "SELECT 1 FROM worktree_file_blobs wfb
                 JOIN worktree_leases wl ON wl.worktree_id = wfb.worktree_id
                 WHERE wfb.blob_hash = ?1 AND (?2 - wl.last_seen) <= 7200
                 LIMIT 1",
            )?;
            let mut mark_superseded = tx.prepare_cached(
                "UPDATE blobs SET pin_level = -1 WHERE blob_hash = ?1 AND pin_level = 0",
            )?;
            for old_bh in superseded_candidates {
                let still_active: Option<i64> = check_active
                    .query_row(params![old_bh, now], |r| r.get(0))
                    .optional()?;
                if still_active.is_none() {
                    let changed = mark_superseded.execute(params![old_bh])?;
                    if changed > 0 {
                        newly_superseded += 1;
                    }
                }
            }
        }

        tx.commit()?;
        Ok(newly_superseded)
    }

    pub fn gc_gdsf(&mut self, max_reclaimable_bytes: u64) -> Result<GcReport> {
        self.run_gc(max_reclaimable_bytes, 7 * 86400, true)
    }

    pub fn storage_status(&self) -> Result<StorageStatus> {
        let total_blobs: usize = self
            .conn
            .query_row("SELECT COUNT(*) FROM blobs", [], |r| r.get(0))?;
        let total_actions: usize = self
            .conn
            .query_row("SELECT COUNT(*) FROM actions WHERE status = 'completed'", [], |r| r.get(0))?;
        let active_worktrees: usize = self
            .conn
            .query_row("SELECT COUNT(*) FROM worktrees", [], |r| r.get(0))?;
        let active_inflight_leases: usize = self
            .conn
            .query_row("SELECT COUNT(*) FROM inflight_leases", [], |r| r.get(0))?;
        let total_coalesced_waits: i64 = self
            .conn
            .query_row("SELECT val FROM meta_counters WHERE name = 'coalesced_waits'", [], |r| r.get(0))
            .unwrap_or(0);
        let (total_shard_hits, saved_compute_ms): (i64, i64) = self
            .conn
            .query_row(
                "SELECT COALESCE(SUM(hit_count), 0), COALESCE(SUM(hit_count * MAX(duration_ms, 1)), 0)
                 FROM actions WHERE status = 'completed'",
                [],
                |r| Ok((r.get(0)?, r.get(1)?)),
            )
            .unwrap_or((0, 0));

        let mut fastcheck_cached_bins = 0usize;
        let mut fastcheck_cached_bytes = 0u64;
        if let Ok(entries) = fs::read_dir(self.root.join("fastcheck_bins")) {
            for entry in entries.flatten() {
                if let Ok(meta) = entry.metadata() {
                    if meta.is_file() {
                        fastcheck_cached_bins += 1;
                        fastcheck_cached_bytes += meta.len();
                    }
                }
            }
        }

        let mut stmt = self
            .conn
            .prepare("SELECT blob_hash, size_bytes, pin_level FROM blobs")?;
        let rows = stmt.query_map([], |r| {
            Ok((
                r.get::<_, String>(0)?,
                r.get::<_, i64>(1)? as u64,
                r.get::<_, i64>(2)?,
            ))
        })?;

        let mut reclaimable_bytes = 0u64;
        let mut worktree_retained_bytes = 0u64;
        let mut pinned_bytes = 0u64;
        let mut total_logical_bytes = 0u64;

        for row in rows {
            let (hash, size, pin) = row?;
            total_logical_bytes += size;
            let path = self.blob_path(&hash);
            let nlink = fs::metadata(&path).map(|m| m.nlink()).unwrap_or(1);
            if pin > 0 {
                pinned_bytes += size;
            } else if nlink > 1 {
                worktree_retained_bytes += size;
            } else {
                reclaimable_bytes += size;
            }
        }

        Ok(StorageStatus {
            cache_root: self.root.to_string_lossy().to_string(),
            total_blobs,
            total_actions,
            active_worktrees,
            active_inflight_leases,
            total_coalesced_waits,
            total_shard_hits,
            saved_compute_ms,
            fastcheck_cached_bins,
            fastcheck_cached_bytes,
            reclaimable_bytes,
            worktree_retained_bytes,
            pinned_bytes,
            total_logical_bytes,
        })
    }

    /// Smart multi-project Garbage Collector using Cost-Aware GDSF (Greedy-Dual-Size-Frequency):
    /// `KeepScore(Action) = last_accessed + alpha * (duration_ms / max(total_size_bytes, 1))`
    /// Also performs:
    /// - Step A: Immediate Supersession Eviction (`pin_level < 0` and not in any active worktree lease),
    /// - Step B: Standard GDSF Eviction to bring reclaimable bytes under `max_reclaimable_bytes`,
    /// - Step C: Cold Unlinked Blob Compression (`TLZ1`) for `nlink == 1` `.olean`/`.ilean`/`.c` blobs.
    pub fn run_gc(
        &mut self,
        max_reclaimable_bytes: u64,
        prune_worktrees_older_than_secs: i64,
        keep_pinned: bool,
    ) -> Result<GcReport> {
        let now = now_unix();
        let mut pruned_worktrees = 0usize;
        let mut cleaned_staging_files = 0usize;
        let mut pruned_fastcheck_bins = 0usize;
        let mut freed_bytes = 0u64;
        let mut superseded_evicted = 0usize;
        let mut compressed_blobs = 0usize;
        let mut evicted_actions = 0usize;
        let mut unlinked_blobs = 0usize;

        // 0. Clean orphaned temporary files in `<store>/staging` and `/dev/shm/turbo-lean-staging`
        for st_dir in [self.root.join("staging"), self.fast_staging_dir()] {
            if let Ok(entries) = fs::read_dir(&st_dir) {
                for entry in entries.flatten() {
                    let fname = entry.file_name();
                    let fname_str = fname.to_string_lossy();
                    if fname_str.starts_with("git_head_tree_")
                        || fname_str.starts_with("project_stat_splits_")
                        || fname_str.starts_with("project_splits_")
                        || fname_str.starts_with("lake_env_v1_")
                    {
                        continue;
                    }
                    if let Ok(meta) = entry.metadata() {
                        if meta.is_file() {
                            let age_secs = meta
                                .modified()
                                .ok()
                                .and_then(|t| t.elapsed().ok())
                                .map(|d| d.as_secs())
                                .unwrap_or(120);
                            if age_secs >= 30 || max_reclaimable_bytes == 0 {
                                let sz = meta.len();
                                if fs::remove_file(entry.path()).is_ok() {
                                    cleaned_staging_files += 1;
                                    freed_bytes += sz;
                                }
                            }
                        }
                    }
                }
            }
        }

        // 0b. Prune old binaries in `<store>/fastcheck_bins` when exceeding max_reclaimable_bytes
        let fc_dir = self.root.join("fastcheck_bins");
        if let Ok(entries) = fs::read_dir(&fc_dir) {
            let mut fc_bins: Vec<(PathBuf, u64, u64)> = Vec::new();
            let mut fc_total = 0u64;
            for entry in entries.flatten() {
                if let Ok(meta) = entry.metadata() {
                    if meta.is_file() {
                        let mtime = meta
                            .modified()
                            .ok()
                            .and_then(|t| t.duration_since(UNIX_EPOCH).ok())
                            .map(|d| d.as_secs())
                            .unwrap_or(0);
                        fc_total += meta.len();
                        fc_bins.push((entry.path(), meta.len(), mtime));
                    }
                }
            }
            if fc_total > max_reclaimable_bytes {
                fc_bins.sort_by_key(|(_, _, mt)| *mt);
                for (p, sz, _) in fc_bins {
                    if fc_total <= max_reclaimable_bytes {
                        break;
                    }
                    if fs::remove_file(&p).is_ok() {
                        pruned_fastcheck_bins += 1;
                        freed_bytes += sz;
                        fc_total = fc_total.saturating_sub(sz);
                    }
                }
            }
        }

        // 1. Prune worktrees whose root directory no longer exists or are older than threshold
        let wt_rows: Vec<(String, String, i64)> = {
            let mut stmt = self
                .conn
                .prepare("SELECT worktree_id, root_path, last_seen FROM worktrees")?;
            let mapped = stmt.query_map([], |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?)))?;
            mapped.collect::<std::result::Result<Vec<_>, _>>()?
        };

        for (wt_id, root_path, last_seen) in wt_rows {
            let expired = prune_worktrees_older_than_secs >= 0
                && (now - last_seen) > prune_worktrees_older_than_secs;
            if !Path::new(&root_path).exists() || expired {
                if Path::new(&root_path).exists() {
                    let mut inst_stmt = self.conn.prepare(
                        "SELECT rel_path, blob_hash FROM worktree_installations WHERE worktree_id = ?1",
                    )?;
                    let rels: Vec<(String, String)> = inst_stmt
                        .query_map(params![wt_id], |r| Ok((r.get(0)?, r.get(1)?)))?
                        .collect::<std::result::Result<Vec<_>, _>>()?;
                    for (rel, bh) in rels {
                        let wt_file = Path::new(&root_path).join(&rel);
                        let cas_file = self.blob_path(&bh);
                        if let (Ok(m1), Ok(m2)) = (fs::metadata(&wt_file), fs::metadata(&cas_file)) {
                            if m1.ino() == m2.ino() {
                                let _ = fs::remove_file(&wt_file);
                            }
                        }
                    }
                }
                self.conn.execute(
                    "DELETE FROM worktrees WHERE worktree_id = ?1",
                    params![wt_id],
                )?;
                pruned_worktrees += 1;
            }
        }

        // Step A (Immediate Supersession Eviction):
        // Always evict any blob in `blobs` with `pin_level < 0` that is not referenced in
        // `worktree_file_blobs` of any active lease (`now - last_seen <= 7200`), even before
        // checking `max_reclaimable_bytes`!
        let superseded_blobs: Vec<(String, u64)> = {
            let mut stmt = self.conn.prepare(
                "SELECT b.blob_hash, b.size_bytes
                 FROM blobs b
                 WHERE b.pin_level < 0
                   AND NOT EXISTS (
                       SELECT 1 FROM worktree_file_blobs wfb
                       JOIN worktree_leases wl ON wl.worktree_id = wfb.worktree_id
                       WHERE wfb.blob_hash = b.blob_hash AND (?1 - wl.last_seen) <= 7200
                   )",
            )?;
            let mapped = stmt.query_map(params![now], |r| {
                Ok((r.get::<_, String>(0)?, r.get::<_, i64>(1)? as u64))
            })?;
            mapped.collect::<std::result::Result<Vec<_>, _>>()?
        };

        for (bh, sz) in superseded_blobs {
            let p = self.blob_path(&bh);
            if p.exists() {
                let _ = fs::remove_file(&p);
            }
            self.conn.execute(
                "DELETE FROM actions WHERE action_key IN (SELECT action_key FROM action_outputs WHERE blob_hash = ?1)",
                params![bh],
            )?;
            self.conn.execute(
                "DELETE FROM action_outputs WHERE blob_hash = ?1",
                params![bh],
            )?;
            self.conn.execute(
                "DELETE FROM worktree_installations WHERE blob_hash = ?1",
                params![bh],
            )?;
            self.conn
                .execute("DELETE FROM blobs WHERE blob_hash = ?1", params![bh])?;
            superseded_evicted += 1;
            unlinked_blobs += 1;
            freed_bytes += sz;
        }

        // Step B (Standard GDSF Eviction):
        let initial_status = self.storage_status()?;
        let mut current_reclaimable = initial_status.reclaimable_bytes;

        if current_reclaimable > max_reclaimable_bytes {
            let candidates: Vec<String> = {
                let mut stmt = self.conn.prepare(
                    "SELECT a.action_key,
                            a.updated_at + (a.duration_ms * 1000000) / MAX(1, COALESCE(SUM(b.size_bytes), 1)) AS gdsf_score
                     FROM actions a
                     LEFT JOIN action_outputs ao ON ao.action_key = a.action_key
                     LEFT JOIN blobs b ON b.blob_hash = ao.blob_hash
                     WHERE a.status = 'completed'
                       AND NOT EXISTS (
                           SELECT 1 FROM action_outputs ao2
                           JOIN worktree_file_blobs wfb ON wfb.blob_hash = ao2.blob_hash
                           JOIN worktree_leases wl ON wl.worktree_id = wfb.worktree_id
                           WHERE ao2.action_key = a.action_key AND (?1 - wl.last_seen) <= 7200
                       )
                     GROUP BY a.action_key
                     ORDER BY gdsf_score ASC",
                )?;
                let mapped = stmt.query_map(params![now], |r| r.get::<_, String>(0))?;
                mapped.collect::<std::result::Result<Vec<_>, _>>()?
            };

            for action_key in candidates {
                if current_reclaimable <= max_reclaimable_bytes {
                    break;
                }
                self.conn.execute(
                    "DELETE FROM actions WHERE action_key = ?1",
                    params![action_key],
                )?;
                evicted_actions += 1;

                // Find orphan blobs no longer referenced by any action_outputs or active worktree leases
                let orphan_blobs: Vec<(String, u64, i64)> = {
                    let mut stmt = self.conn.prepare(
                        "SELECT b.blob_hash, b.size_bytes, b.pin_level
                         FROM blobs b
                         LEFT JOIN action_outputs ao ON ao.blob_hash = b.blob_hash
                         WHERE ao.blob_hash IS NULL
                           AND NOT EXISTS (
                               SELECT 1 FROM worktree_file_blobs wfb
                               JOIN worktree_leases wl ON wl.worktree_id = wfb.worktree_id
                               WHERE wfb.blob_hash = b.blob_hash AND (?1 - wl.last_seen) <= 7200
                           )",
                    )?;
                    let mapped = stmt.query_map(params![now], |r| {
                        Ok((
                            r.get::<_, String>(0)?,
                            r.get::<_, i64>(1)? as u64,
                            r.get::<_, i64>(2)?,
                        ))
                    })?;
                    mapped.collect::<std::result::Result<Vec<_>, _>>()?
                };

                for (bh, sz, pin) in orphan_blobs {
                    if keep_pinned && pin > 0 {
                        continue;
                    }
                    let p = self.blob_path(&bh);
                    let nlink = fs::metadata(&p).map(|m| m.nlink()).unwrap_or(1);
                    if p.exists() {
                        let _ = fs::remove_file(&p);
                    }
                    self.conn.execute(
                        "DELETE FROM worktree_installations WHERE blob_hash = ?1",
                        params![bh],
                    )?;
                    self.conn
                        .execute("DELETE FROM blobs WHERE blob_hash = ?1", params![bh])?;
                    unlinked_blobs += 1;
                    if nlink == 1 && pin <= 0 {
                        freed_bytes += sz;
                        current_reclaimable = current_reclaimable.saturating_sub(sz);
                    }
                }
            }
        }

        // Step C (Cold Unlinked Blob Compression `TLZ1`):
        // For remaining `.olean` / `.ilean` / `.c` blobs on disk whose OS hardlink count is
        // `meta.nlink() == 1` and size >= 512 bytes, compress them in-place using `TLZ1`
        // if compressed size < data.len() * 9 / 10.
        let remaining_blobs: Vec<(String, String)> = {
            let mut stmt = self.conn.prepare("SELECT blob_hash, kind FROM blobs")?;
            let mapped =
                stmt.query_map([], |r| Ok((r.get::<_, String>(0)?, r.get::<_, String>(1)?)))?;
            mapped.collect::<std::result::Result<Vec<_>, _>>()?
        };

        let staging_dir = self.root.join("staging");
        let _ = fs::create_dir_all(&staging_dir);

        for (bh, kind) in remaining_blobs {
            let k = kind.trim_start_matches('.');
            let is_compressible_kind = matches!(
                k,
                "olean" | "olean.private" | "olean.server" | "ilean" | "c" | "ir"
            ) || k.ends_with("olean")
                || k.ends_with("ilean");
            if !is_compressible_kind {
                continue;
            }
            let p = self.blob_path(&bh);
            let Ok(meta) = fs::metadata(&p) else {
                continue;
            };
            if meta.nlink() != 1 || meta.len() < 512 {
                continue;
            }
            let Ok(raw_bytes) = fs::read(&p) else {
                continue;
            };
            if raw_bytes.len() < 512 || raw_bytes.starts_with(b"TLZ1") {
                continue;
            }
            let compressed = compress_tlz1(&raw_bytes);
            if compressed.len() < (raw_bytes.len() * 9) / 10 {
                let staging_path = staging_dir.join(format!(
                    "{}.{}.tlz1.tmp",
                    bh,
                    std::process::id()
                ));
                use std::os::unix::fs::OpenOptionsExt;
                if let Ok(mut out) = OpenOptions::new()
                    .write(true)
                    .create(true)
                    .truncate(true)
                    .mode(0o444)
                    .open(&staging_path)
                {
                    if out.write_all(&compressed).is_ok() {
                        drop(out);
                        if fs::rename(&staging_path, &p).is_ok() {
                            compressed_blobs += 1;
                            let saved = (raw_bytes.len() - compressed.len()) as u64;
                            freed_bytes += saved;
                            current_reclaimable = current_reclaimable.saturating_sub(saved);
                        } else {
                            let _ = fs::remove_file(&staging_path);
                        }
                    } else {
                        let _ = fs::remove_file(&staging_path);
                    }
                }
            }
        }

        Ok(GcReport {
            pruned_worktrees,
            evicted_actions,
            unlinked_blobs,
            cleaned_staging_files,
            pruned_fastcheck_bins,
            freed_reclaimable_bytes: freed_bytes,
            remaining_reclaimable_bytes: current_reclaimable,
            superseded_evicted,
            compressed_blobs,
        })
    }
}

/// Fast pure-Rust `TLZ1` byte-run/LZ77 compressor for cold (`nlink == 1`) `.olean`/`.ilean`/`.c` blobs.
/// Format: `b"TLZ1"` (4 bytes) + `uncompressed_len: u64` LE (8 bytes) + token stream:
/// - `0x00..=0x7F`: literal run of length `(tag as usize) + 1` (1..=128) followed by literal bytes.
/// - `0x80..=0xFF`: back-reference match of length `((tag & 0x7F) as usize) + 4` (4..=131) followed by `offset: u16` LE.
pub fn compress_tlz1(data: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(12 + data.len() / 2);
    out.extend_from_slice(b"TLZ1");
    out.extend_from_slice(&(data.len() as u64).to_le_bytes());
    if data.is_empty() {
        return out;
    }

    let flush_literals = |out: &mut Vec<u8>, mut lits: &[u8]| {
        while !lits.is_empty() {
            let chunk_len = lits.len().min(128);
            out.push((chunk_len - 1) as u8);
            out.extend_from_slice(&lits[..chunk_len]);
            lits = &lits[chunk_len..];
        }
    };

    let mut ht = [usize::MAX; 4096];
    let mut lit_start = 0usize;
    let mut ip = 0usize;
    let limit = data.len().saturating_sub(4);

    while ip <= limit && data.len() >= 4 {
        let v = u32::from_le_bytes([data[ip], data[ip + 1], data[ip + 2], data[ip + 3]]);
        let h = ((v.wrapping_mul(2654435761)) >> 20) as usize;
        let ref_pos = ht[h];
        ht[h] = ip;

        if ref_pos < ip
            && ip - ref_pos <= 65535
            && data[ref_pos..ref_pos + 4] == data[ip..ip + 4]
        {
            if lit_start < ip {
                flush_literals(&mut out, &data[lit_start..ip]);
            }
            let max_match = (data.len() - ip).min(131);
            let mut m_len = 4usize;
            while m_len < max_match && data[ref_pos + m_len] == data[ip + m_len] {
                m_len += 1;
            }
            let offset = (ip - ref_pos) as u16;
            out.push(0x80 | ((m_len - 4) as u8));
            out.extend_from_slice(&offset.to_le_bytes());
            ip += m_len;
            lit_start = ip;
        } else {
            ip += 1;
        }
    }

    if lit_start < data.len() {
        flush_literals(&mut out, &data[lit_start..]);
    }
    out
}

/// Decompress a `TLZ1`-compressed cold blob back to its exact uncompressed bytes.
pub fn decompress_tlz1(data: &[u8]) -> Option<Vec<u8>> {
    if data.len() < 12 || &data[0..4] != b"TLZ1" {
        return None;
    }
    let mut len_bytes = [0u8; 8];
    len_bytes.copy_from_slice(&data[4..12]);
    let uncompressed_len = u64::from_le_bytes(len_bytes) as usize;
    let mut out = Vec::with_capacity(uncompressed_len.min(64 * 1024 * 1024));
    let mut pos = 12usize;

    while pos < data.len() {
        let tag = data[pos];
        pos += 1;
        if (tag & 0x80) == 0 {
            let lit_len = (tag as usize) + 1;
            if pos + lit_len > data.len() || out.len() + lit_len > uncompressed_len {
                return None;
            }
            out.extend_from_slice(&data[pos..pos + lit_len]);
            pos += lit_len;
        } else {
            let match_len = ((tag & 0x7F) as usize) + 4;
            if pos + 2 > data.len() {
                return None;
            }
            let offset = u16::from_le_bytes([data[pos], data[pos + 1]]) as usize;
            pos += 2;
            if offset == 0 || offset > out.len() || out.len() + match_len > uncompressed_len {
                return None;
            }
            let start = out.len() - offset;
            for i in 0..match_len {
                let b = out[start + i];
                out.push(b);
            }
        }
    }

    if out.len() == uncompressed_len {
        Some(out)
    } else {
        None
    }
}

fn record_worktree_outputs_and_supersede(
    tx: &rusqlite::Transaction<'_>,
    wt_id: &str,
    root_str: &str,
    project_name: &str,
    now: i64,
    outputs: &[BlobEntry],
) -> Result<()> {
    tx.execute(
        "INSERT INTO worktrees (worktree_id, root_path, project_name, last_seen) VALUES (?1, ?2, ?3, ?4)
         ON CONFLICT(worktree_id) DO UPDATE SET last_seen = excluded.last_seen",
        params![wt_id, root_str, project_name, now],
    )?;
    let had_existing_lease: bool = tx
        .query_row("SELECT 1 FROM worktree_leases WHERE worktree_id = ?1 LIMIT 1", params![wt_id], |_| Ok(true))
        .optional()?
        .unwrap_or(false);
    tx.execute(
        "INSERT INTO worktree_leases (worktree_id, worktree_path, pid, head_commit, last_seen)
         VALUES (?1, ?2, ?3, 'HEAD', ?4)
         ON CONFLICT(worktree_id) DO UPDATE SET
            worktree_path = excluded.worktree_path, pid = excluded.pid, last_seen = excluded.last_seen",
        params![wt_id, root_str, std::process::id() as i64, now],
    )?;

    let mut superseded_candidates = std::collections::HashSet::new();
    if had_existing_lease {
        let mut q_old = tx.prepare_cached("SELECT blob_hash FROM worktree_file_blobs WHERE worktree_id = ?1 AND rel_path = ?2")?;
        let mut ups_wfb = tx.prepare_cached(
            "INSERT INTO worktree_file_blobs (worktree_id, rel_path, blob_hash, updated_at) VALUES (?1, ?2, ?3, ?4)
             ON CONFLICT(worktree_id, rel_path) DO UPDATE SET blob_hash = excluded.blob_hash, updated_at = excluded.updated_at",
        )?;
        for out in outputs {
            if out.rel_path.starts_with("thm:") { continue; }
            if let Some(prev) = q_old.query_row(params![wt_id, out.rel_path], |r| r.get::<_, String>(0)).optional()? {
                if prev != out.blob_hash { superseded_candidates.insert(prev); }
            }
            ups_wfb.execute(params![wt_id, out.rel_path, out.blob_hash, now])?;
        }
    } else {
        let mut ins_wfb = tx.prepare_cached(
            "INSERT OR REPLACE INTO worktree_file_blobs (worktree_id, rel_path, blob_hash, updated_at) VALUES (?1, ?2, ?3, ?4)",
        )?;
        for out in outputs {
            if !out.rel_path.starts_with("thm:") {
                ins_wfb.execute(params![wt_id, out.rel_path, out.blob_hash, now])?;
            }
        }
    }
    if !superseded_candidates.is_empty() {
        let mut check_active = tx.prepare_cached(
            "SELECT 1 FROM worktree_file_blobs wfb
             JOIN worktree_leases wl ON wl.worktree_id = wfb.worktree_id
             WHERE wfb.blob_hash = ?1 AND (?2 - wl.last_seen) <= 7200 LIMIT 1",
        )?;
        let mut mark_superseded = tx.prepare_cached("UPDATE blobs SET pin_level = -1 WHERE blob_hash = ?1 AND pin_level = 0")?;
        for old_bh in superseded_candidates {
            if check_active.query_row(params![old_bh, now], |r| r.get::<_, i64>(0)).optional()?.is_none() {
                let _ = mark_superseded.execute(params![old_bh]);
            }
        }
    }
    Ok(())
}

/// Batch-query theorem shards in SQLite inside a single `BEGIN IMMEDIATE ... COMMIT` transaction,
/// incrementing `hit_count` and updating `last_accessed` in one atomic commit.
pub fn batch_get_theorem_shards(
    conn: &Connection,
    shard_keys: &[String],
) -> Result<std::collections::HashMap<String, String>> {
    batch_get_theorem_shards_in_domain(conn, shard_keys, "trusted")
}

pub fn batch_get_theorem_shards_in_domain(
    conn: &Connection,
    shard_keys: &[String],
    trust_domain: &str,
) -> Result<std::collections::HashMap<String, String>> {
    if shard_keys.is_empty() {
        return Ok(std::collections::HashMap::new());
    }
    let now = now_unix();
    let mut hits = std::collections::HashMap::with_capacity(shard_keys.len());
    if shard_keys.len() >= 128 {
        let tx = conn.unchecked_transaction()?;
        let mut db_map = std::collections::HashMap::with_capacity(shard_keys.len());
        {
            let mut scan_stmt = tx.prepare_cached(
                "SELECT a.action_key, ao.blob_hash, b.last_accessed
                 FROM actions a JOIN action_outputs ao ON ao.action_key = a.action_key
                 JOIN blobs b ON b.blob_hash = ao.blob_hash
                 WHERE a.kind = 'theorem_shard' AND a.status = 'completed' AND a.trust_domain = ?1",
            )?;
            let mut rows = scan_stmt.query(params![trust_domain])?;
            while let Some(row) = rows.next()? {
                db_map.insert(row.get::<_, String>(0)?, (row.get::<_, String>(1)?, row.get::<_, i64>(2)?));
            }
        }
        let mut touched_blobs = std::collections::HashSet::new();
        let mut hit_keys_in_order = Vec::with_capacity(shard_keys.len());
        for key in shard_keys {
            if let Some((blob_hash, last_acc)) = db_map.get(key) {
                hit_keys_in_order.push(key.as_str());
                if now - *last_acc >= 60 { touched_blobs.insert(blob_hash.clone()); }
                hits.insert(key.clone(), blob_hash.clone());
            }
        }
        if !hit_keys_in_order.is_empty() {
            if hits.len() == db_map.len() && hit_keys_in_order.len() == hits.len() {
                tx.execute(
                    "UPDATE actions SET hit_count = hit_count + 1 WHERE kind = 'theorem_shard' AND status = 'completed' AND trust_domain = ?1",
                    params![trust_domain],
                )?;
            } else {
                let mut upd_action = tx.prepare_cached("UPDATE actions SET hit_count = hit_count + 1 WHERE action_key = ?1")?;
                for k in hit_keys_in_order { upd_action.execute(params![k])?; }
            }
            if !touched_blobs.is_empty() {
                let mut upd_blob = tx.prepare_cached("UPDATE blobs SET last_accessed = ?1 WHERE blob_hash = ?2")?;
                for bh in touched_blobs { upd_blob.execute(params![now, &bh])?; }
            }
            tx.commit()?;
        }
    } else {
        let mut hit_rows: Vec<(&str, String, i64)> = Vec::new();
        {
            let mut sel_stmt = conn.prepare_cached(
                "SELECT ao.blob_hash, b.last_accessed FROM actions a
                 JOIN action_outputs ao ON ao.action_key = a.action_key
                 JOIN blobs b ON b.blob_hash = ao.blob_hash
                 WHERE a.action_key = ?1 AND a.status = 'completed' AND a.trust_domain = ?2 LIMIT 1",
            )?;
            for key in shard_keys {
                if let Some((blob_hash, last_acc)) = sel_stmt
                    .query_row(params![key, trust_domain], |r| {
                        Ok((r.get::<_, String>(0)?, r.get::<_, i64>(1)?))
                    })
                    .optional()?
                {
                    hit_rows.push((key.as_str(), blob_hash.clone(), last_acc));
                    hits.insert(key.clone(), blob_hash);
                }
            }
        }
        if !hit_rows.is_empty() {
            let tx = conn.unchecked_transaction()?;
            {
                let mut upd_action = tx.prepare_cached("UPDATE actions SET hit_count = hit_count + 1 WHERE action_key = ?1")?;
                let mut upd_blob = tx.prepare_cached("UPDATE blobs SET last_accessed = ?1 WHERE blob_hash = ?2")?;
                let mut touched_blobs = std::collections::HashSet::new();
                for (key, blob_hash, last_acc) in hit_rows {
                    upd_action.execute(params![key])?;
                    if now - last_acc >= 60 && touched_blobs.insert(blob_hash.clone()) {
                        upd_blob.execute(params![now, &blob_hash])?;
                    }
                }
            }
            tx.commit()?;
        }
    }
    Ok(hits)
}

/// Batch-insert or update imported `.tlpack` blobs, actions, and action_outputs inside a single
/// `BEGIN IMMEDIATE ... COMMIT` SQLite transaction using cached prepared statements.
pub fn batch_import_pack_metadata(
    conn: &Connection,
    blobs: &[(String, String, i64, i64)],
    actions: &[ActionRecord],
) -> Result<(usize, usize)> {
    let now = now_unix();
    conn.execute_batch("PRAGMA foreign_keys = OFF; PRAGMA synchronous = OFF; BEGIN IMMEDIATE;")?;
    let res = (|| -> Result<(usize, usize)> {
        let mut ins_blob = conn.prepare_cached(
            "INSERT OR IGNORE INTO blobs (blob_hash, kind, size_bytes, inode, created_at, last_accessed, pin_level, trust_domain)
             VALUES (?1, ?2, ?3, ?4, ?5, ?5, 0, 'trusted')",
        )?;
        for (blob_hash, kind, size_bytes, inode) in blobs {
            ins_blob.execute(params![blob_hash, kind, size_bytes, inode, now])?;
        }
        let mut ins_act = conn.prepare_cached(
            "INSERT INTO actions (action_key, toolchain_githash, kind, status, fencing_token,
                                  output_manifest_hash, duration_ms, peak_pss_bytes, heartbeats, trust_domain, updated_at)
             VALUES (?1, ?2, ?3, 'completed', ?4, ?5, ?6, ?7, ?8, 'trusted', ?9)
             ON CONFLICT(action_key) DO UPDATE SET
                status = 'completed', output_manifest_hash = excluded.output_manifest_hash, updated_at = excluded.updated_at
             WHERE status != 'completed' OR output_manifest_hash IS NOT excluded.output_manifest_hash",
        )?;
        let mut ins_out = conn.prepare_cached(
            "INSERT INTO action_outputs (action_key, rel_path, blob_hash) VALUES (?1, ?2, ?3)
             ON CONFLICT(action_key, rel_path) DO UPDATE SET blob_hash = excluded.blob_hash
             WHERE blob_hash != excluded.blob_hash",
        )?;
        for act in actions {
            ins_act.execute(params![
                act.action_key, act.toolchain_githash, act.kind, act.fencing_token,
                act.output_manifest_hash, act.duration_ms, act.peak_pss_bytes, act.heartbeats, now
            ])?;
            for out in &act.outputs {
                ins_out.execute(params![act.action_key, out.rel_path, out.blob_hash])?;
            }
        }
        Ok((actions.len(), blobs.len()))
    })();
    match res {
        Ok(counts) => {
            conn.execute_batch("COMMIT; PRAGMA synchronous = NORMAL; PRAGMA foreign_keys = ON;")?;
            Ok(counts)
        }
        Err(e) => {
            let _ = conn.execute_batch("ROLLBACK; PRAGMA synchronous = NORMAL; PRAGMA foreign_keys = ON;");
            Err(e)
        }
    }
}

/// Batch-query cached `file_split_cache` rows inside a single SQLite transaction.
pub fn batch_get_file_splits(
    conn: &Connection,
    file_hashes: &[String],
) -> Result<std::collections::HashMap<String, (String, String)>> {
    if file_hashes.is_empty() {
        return Ok(std::collections::HashMap::new());
    }
    let tx = conn.unchecked_transaction()?;
    let mut hits = std::collections::HashMap::with_capacity(file_hashes.len());
    if file_hashes.len() >= 128 {
        let wanted: std::collections::HashSet<&str> = file_hashes.iter().map(|s| s.as_str()).collect();
        let mut stmt = tx.prepare_cached("SELECT file_hash, split_json, hygiene_issues_json FROM file_split_cache")?;
        let mut rows = stmt.query([])?;
        while let Some(row) = rows.next()? {
            let fh: String = row.get(0)?;
            if wanted.contains(fh.as_str()) {
                hits.insert(fh, (row.get(1)?, row.get(2)?));
            }
        }
    } else {
        let mut stmt = tx.prepare_cached("SELECT split_json, hygiene_issues_json FROM file_split_cache WHERE file_hash = ?1")?;
        for fh in file_hashes {
            if let Some(pair) = stmt.query_row(params![fh], |r| Ok((r.get(0)?, r.get(1)?))).optional()? {
                hits.insert(fh.clone(), pair);
            }
        }
    }
    tx.commit()?;
    Ok(hits)
}

/// Batch-insert or update `file_split_cache` rows inside a single `BEGIN IMMEDIATE ... COMMIT` transaction.
pub fn batch_put_file_splits(conn: &Connection, entries: &[(String, String, String)]) -> Result<()> {
    if entries.is_empty() { return Ok(()); }
    let now = now_unix();
    let tx = conn.unchecked_transaction()?;
    {
        let mut stmt = tx.prepare_cached(
            "INSERT INTO file_split_cache (file_hash, split_json, hygiene_issues_json, updated_at) VALUES (?1, ?2, ?3, ?4)
             ON CONFLICT(file_hash) DO UPDATE SET split_json = excluded.split_json, hygiene_issues_json = excluded.hygiene_issues_json, updated_at = excluded.updated_at",
        )?;
        for (fh, split_json, hygiene_json) in entries {
            stmt.execute(params![fh, split_json, hygiene_json, now])?;
        }
    }
    tx.commit()?;
    Ok(())
}

/// Batch-query `(path_key, split_key, split_json)` by `(path_key, mtime_sec, mtime_nsec, size_bytes)`
/// via a single SQLite transaction joining `file_stat_cache` and `file_split_cache`.
pub fn batch_get_raw_file_splits_by_stat(
    conn: &Connection,
    stats: &[(String, i64, i64, i64)],
) -> Result<Vec<(String, String, String)>> {
    if stats.is_empty() { return Ok(Vec::new()); }
    let tx = conn.unchecked_transaction()?;
    let mut hits = Vec::with_capacity(stats.len());
    if stats.len() >= 64 {
        let wanted: std::collections::HashMap<&str, (i64, i64, i64)> =
            stats.iter().map(|(pk, ms, mn, sz)| (pk.as_str(), (*ms, *mn, *sz))).collect();
        let mut stmt = tx.prepare_cached(
            "SELECT s.path_key, s.mtime_sec, s.mtime_nsec, s.size_bytes, s.split_key, c.split_json
             FROM file_stat_cache s JOIN file_split_cache c ON c.file_hash = s.split_key",
        )?;
        let mut rows = stmt.query([])?;
        while let Some(row) = rows.next()? {
            let pk: String = row.get(0)?;
            if let Some(&(exp_ms, exp_mn, exp_sz)) = wanted.get(pk.as_str()) {
                if row.get::<_, i64>(1)? == exp_ms && row.get::<_, i64>(2)? == exp_mn && row.get::<_, i64>(3)? == exp_sz {
                    hits.push((pk, row.get(4)?, row.get(5)?));
                }
            }
        }
    } else {
        let mut stmt = tx.prepare_cached(
            "SELECT s.split_key, c.split_json FROM file_stat_cache s
             JOIN file_split_cache c ON c.file_hash = s.split_key
             WHERE s.path_key = ?1 AND s.mtime_sec = ?2 AND s.mtime_nsec = ?3 AND s.size_bytes = ?4",
        )?;
        for (pk, ms, mn, sz) in stats {
            if let Some((sk, sj)) = stmt.query_row(params![pk, ms, mn, sz], |r| Ok((r.get(0)?, r.get(1)?))).optional()? {
                hits.push((pk.clone(), sk, sj));
            }
        }
    }
    tx.commit()?;
    Ok(hits)
}

/// Batch-insert or update `file_stat_cache` rows inside a single SQLite transaction.
pub fn batch_put_file_stats(conn: &Connection, entries: &[(String, i64, i64, i64, String)]) -> Result<()> {
    if entries.is_empty() { return Ok(()); }
    let now = now_unix();
    let tx = conn.unchecked_transaction()?;
    {
        let mut stmt = tx.prepare_cached(
            "INSERT INTO file_stat_cache (path_key, mtime_sec, mtime_nsec, size_bytes, split_key, updated_at) VALUES (?1, ?2, ?3, ?4, ?5, ?6)
             ON CONFLICT(path_key) DO UPDATE SET mtime_sec = excluded.mtime_sec, mtime_nsec = excluded.mtime_nsec,
                size_bytes = excluded.size_bytes, split_key = excluded.split_key, updated_at = excluded.updated_at",
        )?;
        for (pk, ms, mn, sz, sk) in entries {
            stmt.execute(params![pk, ms, mn, sz, sk, now])?;
        }
    }
    tx.commit()?;
    Ok(())
}

pub fn prestage_theorem_shard_blobs_at(
    store_root: &Path,
    items: &[(String, String, Vec<u8>, i64)],
) -> Result<()> {
    if items.is_empty() { return Ok(()); }
    let pid = std::process::id();
    let mut seen_blobs = std::collections::HashSet::with_capacity(items.len());
    let mut seen_prefix = [false; 256];
    let mut newly_created_prefix = [false; 256];

    for (_action_key, _decl_name, receipt_bytes, _dur_ms) in items {
        let hash = blake3::hash(receipt_bytes).to_hex().to_string();
        if !seen_blobs.insert(hash.clone()) { continue; }
        let prefix = if hash.len() >= 2 { &hash[..2] } else { "00" };
        let dest = store_root.join("blobs").join(prefix).join(&hash);
        let p_idx = u8::from_str_radix(prefix, 16).unwrap_or(0) as usize;
        if !seen_prefix[p_idx] {
            seen_prefix[p_idx] = true;
            if let Some(parent) = dest.parent() {
                if fs::create_dir(parent).is_ok() { newly_created_prefix[p_idx] = true; }
            }
        }
        if !newly_created_prefix[p_idx] && fs::metadata(&dest).is_ok() { continue; }
        use std::os::unix::fs::OpenOptionsExt;
        match OpenOptions::new().write(true).create_new(true).mode(0o444).open(&dest) {
            Ok(mut f) => f.write_all(receipt_bytes)?,
            Err(_) => {
                let staging_path = store_root.join("staging").join(format!("{}.{}.tmp", hash, pid));
                let mut f = OpenOptions::new().write(true).create(true).truncate(true).mode(0o444).open(&staging_path)?;
                f.write_all(receipt_bytes)?;
                drop(f);
                let _ = fs::rename(&staging_path, &dest);
            }
        }
    }
    Ok(())
}

pub(crate) fn try_reflink_or_hardlink(src: &Path, dst: &Path) -> Result<&'static str> {
    let pid = std::process::id();
    let tid = format!("{:?}", std::thread::current().id())
        .chars()
        .filter(|c| c.is_ascii_digit())
        .collect::<String>();
    let fname = dst
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "artifact".to_string());
    let tmp_dst = dst.with_file_name(format!(".{}.tl_tmp.{}.{}", fname, pid, tid));
    let _ = fs::remove_file(&tmp_dst);

    // 1. Try immutable hardlink to process-private temp path + atomic rename
    // (shares OS page-cache mmap Shared_Clean across all worktrees and never races on dst)
    if fs::hard_link(src, &tmp_dst).is_ok() {
        if fs::rename(&tmp_dst, dst).is_ok() {
            return Ok("hardlink");
        }
        let _ = fs::remove_file(&tmp_dst);
    }

    // If hardlinking failed (e.g. EXDEV across bind mounts) and `dst` already exists as a
    // read-only 0o444 file with identical size and bytes, preserve `dst`'s existing inode & mtime!
    if let (Ok(src_meta), Ok(dst_meta)) = (fs::metadata(src), fs::metadata(dst)) {
        if src_meta.len() == dst_meta.len() && (dst_meta.permissions().mode() & 0o222) == 0 {
            if let (Ok(sb), Ok(db)) = (fs::read(src), fs::read(dst)) {
                if sb == db {
                    return Ok("hardlink");
                }
            }
        }
    }

    // 2. Try FICLONE ioctl reflink on CoW filesystems (Btrfs / XFS) via temp path
    #[cfg(target_os = "linux")]
    {
        use std::os::unix::io::AsRawFd;
        if let (Ok(src_file), Ok(dst_file)) = (File::open(src), File::create(&tmp_dst)) {
            const FICLONE: libc::c_ulong = 0x40049409;
            let ret = unsafe { libc::ioctl(dst_file.as_raw_fd(), FICLONE, src_file.as_raw_fd()) };
            if ret == 0 {
                let mut perms = dst_file.metadata()?.permissions();
                perms.set_mode(0o444);
                let _ = dst_file.set_permissions(perms);
                drop(dst_file);
                fs::rename(&tmp_dst, dst)?;
                return Ok("reflink");
            } else {
                drop(dst_file);
                let _ = fs::remove_file(&tmp_dst);
            }
        }
    }

    // 3. Fallback to file copy across distinct filesystems via temp path + atomic rename
    fs::copy(src, &tmp_dst)?;
    let mut perms = fs::metadata(&tmp_dst)?.permissions();
    perms.set_mode(0o444);
    let _ = fs::set_permissions(&tmp_dst, perms);
    fs::rename(&tmp_dst, dst)?;
    Ok("copy")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_lake_env_cache_roundtrip_and_invalidation() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!("turbo_lean_db_test_{}", std::process::id()));
        let proj_dir = tmp_dir.join("proj");
        fs::create_dir_all(&proj_dir)?;
        fs::write(proj_dir.join("lean-toolchain"), "leanprover/lean4:v4.31.0\n")?;
        fs::write(proj_dir.join("lakefile.lean"), "import Lake\n")?;
        fs::write(proj_dir.join("lake-manifest.json"), "{}\n")?;

        let store = TurboStore::open(Some(&tmp_dir.join("cache")))?;
        let key1 = TurboStore::compute_lake_env_key(&proj_dir);
        assert!(store.get_lake_env(&key1)?.is_none());

        let mut env_map = HashMap::new();
        env_map.insert("LEAN_PATH".to_string(), "/tmp/test/lib".to_string());
        store.put_lake_env(&key1, &env_map)?;

        let cached = store.get_lake_env(&key1)?.expect("should hit lake_env_cache");
        assert_eq!(cached.get("LEAN_PATH").map(|s| s.as_str()), Some("/tmp/test/lib"));

        // Modifying lakefile.lean changes the BLAKE3 project_key and invalidates the cache
        fs::write(proj_dir.join("lakefile.lean"), "import Lake\n-- modified\n")?;
        let key2 = TurboStore::compute_lake_env_key(&proj_dir);
        assert_ne!(key1, key2);
        assert!(store.get_lake_env(&key2)?.is_none());

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_batch_get_theorem_shards_and_hit_count() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_batch_shards_test_{}",
            std::process::id()
        ));
        let mut store = TurboStore::open(Some(&tmp_dir))?;

        let items = vec![
            (
                "shard_key_alpha".to_string(),
                "thm_alpha".to_string(),
                b"{\"decl\":\"thm_alpha\"}".to_vec(),
                12i64,
            ),
            (
                "shard_key_beta".to_string(),
                "thm_beta".to_string(),
                b"{\"decl\":\"thm_beta\"}".to_vec(),
                15i64,
            ),
        ];
        store.batch_publish_theorem_shards("leanprover/lean4:v4.31.0", "trusted", &items)?;

        let query_keys = vec![
            "shard_key_alpha".to_string(),
            "shard_key_beta".to_string(),
            "shard_key_missing".to_string(),
        ];
        let hits1 = batch_get_theorem_shards(&store.conn, &query_keys)?;
        assert_eq!(hits1.len(), 2);
        assert!(hits1.contains_key("shard_key_alpha"));
        assert!(hits1.contains_key("shard_key_beta"));
        assert!(!hits1.contains_key("shard_key_missing"));

        let hits2 = store.batch_get_theorem_shards(&query_keys, "trusted")?;
        assert_eq!(hits2.len(), 2);

        let hit_count_alpha: i64 = store.conn.query_row(
            "SELECT hit_count FROM actions WHERE action_key = 'shard_key_alpha'",
            [],
            |r| r.get(0),
        )?;
        assert_eq!(hit_count_alpha, 2);

        let completed_keys = store.batch_completed_action_keys(&query_keys, "trusted")?;
        assert_eq!(completed_keys.len(), 2);
        assert!(completed_keys.contains("shard_key_alpha"));
        assert!(completed_keys.contains("shard_key_beta"));
        assert!(!completed_keys.contains("shard_key_missing"));

        let hit_count_after: i64 = store.conn.query_row(
            "SELECT hit_count FROM actions WHERE action_key = 'shard_key_alpha'",
            [],
            |r| r.get(0),
        )?;
        assert_eq!(hit_count_after, 3);

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_file_split_cache_batch_roundtrip_and_invalidation() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_file_split_cache_test_{}",
            std::process::id()
        ));
        let store = TurboStore::open(Some(&tmp_dir))?;

        let src1 = "namespace Demo\ntheorem t1 : 1 = 1 := rfl\nend Demo\n";
        let src2 = "namespace Demo\ntheorem t2 : 2 = 2 := rfl\nend Demo\n";
        let h1 = TurboStore::compute_file_split_key(src1.as_bytes());
        let h2 = TurboStore::compute_file_split_key(src2.as_bytes());
        assert_ne!(h1, h2);

        let sp1 = crate::splitter::split_lean_source(src1, &[]);
        let sp2 = crate::splitter::split_lean_source(src2, &[]);
        store.batch_put_file_splits(&[(h1.clone(), &sp1), (h2.clone(), &sp2)])?;

        let hits = store.batch_get_file_splits(&[h1.clone(), h2.clone(), "missing".to_string()])?;
        assert_eq!(hits.len(), 2);
        assert_eq!(hits[&h1].interface_hash, sp1.interface_hash);
        assert_eq!(hits[&h1].shards.len(), 1);
        assert_eq!(hits[&h1].shards[0].name, "t1");
        assert_eq!(hits[&h2].shards[0].name, "t2");

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_multi_agent_singleflight_and_saved_compute_telemetry() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_singleflight_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);

        let mut store_leader = TurboStore::open(Some(&tmp_dir))?;
        let action_key = "thm_singleflight_key_1";

        // 1. Leader acquires Singleflight lease
        let outcome1 = store_leader.acquire_singleflight(
            action_key,
            "leanprover/lean4:v4.31.0",
            "theorem_shard",
            "trusted",
        )?;
        let lease = match outcome1 {
            SingleflightOutcome::Leader(l) => l,
            SingleflightOutcome::CacheHit { .. } => panic!("expected Leader for first caller"),
        };

        // 2. Spawn 3 concurrent follower threads that contend on the same action_key
        let mut handles = Vec::new();
        for _ in 0..3 {
            let dir_clone = tmp_dir.clone();
            handles.push(std::thread::spawn(move || -> Result<bool> {
                let mut follower_store = TurboStore::open(Some(&dir_clone))?;
                let out = follower_store.acquire_singleflight(
                    action_key,
                    "leanprover/lean4:v4.31.0",
                    "theorem_shard",
                    "trusted",
                )?;
                Ok(matches!(
                    out,
                    SingleflightOutcome::CacheHit {
                        coalesced: true,
                        ..
                    }
                ))
            }));
        }

        // Give followers a brief moment to block on the OS flock
        std::thread::sleep(std::time::Duration::from_millis(40));

        // 3. Leader publishes action (duration = 250ms) and drops the flock lease
        let receipt = b"{\"decl\":\"test_decl\"}";
        let bh = store_leader.store_immutable_blob(receipt, "expr_shard", "trusted", 0)?;
        store_leader.publish_action(
            &lease,
            &[BlobEntry {
                blob_hash: bh,
                kind: "expr_shard".to_string(),
                size_bytes: receipt.len() as u64,
                rel_path: "thm:test_decl".to_string(),
            }],
            250,
            0,
            0,
            "trusted",
        )?;
        drop(lease);

        for h in handles {
            let hit = h.join().expect("thread panicked")?;
            assert!(hit, "Follower should observe AlreadyCached after leader publishes");
        }

        // 4. Verify status telemetry: 3 hits * 250ms = 750ms saved compute, plus coalesced waits
        let st = store_leader.storage_status()?;
        assert!(
            st.total_shard_hits >= 3,
            "Expected >= 3 shard hits, got {}",
            st.total_shard_hits
        );
        assert!(
            st.saved_compute_ms >= 750,
            "Expected >= 750ms saved compute, got {}",
            st.saved_compute_ms
        );

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_materialize_into_worktree_zero_unlink_and_self_healing() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_materialize_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let cache_dir = tmp_dir.join("cache");
        let wt_dir = tmp_dir.join("worktree");
        fs::create_dir_all(&wt_dir)?;

        let mut store = TurboStore::open(Some(&cache_dir))?;
        let batch_items = vec![
            (
                String::new(),
                b"olean_payload_1".to_vec(),
                "olean".to_string(),
                ".lake/build/lib/lean/Demo.olean".to_string(),
                15u64,
            ),
            (
                String::new(),
                b"ilean_payload_1".to_vec(),
                "ilean".to_string(),
                ".lake/build/lib/lean/Demo.ilean".to_string(),
                15u64,
            ),
        ];
        let entries = store.batch_store_immutable_blobs(&batch_items, "trusted", 0)?;
        assert_eq!(entries.len(), 2);

        // 1. Initial materialization creates hardlinks in worktree
        let count1 = store.materialize_into_worktree(&wt_dir, "DemoProj", &entries)?;
        assert_eq!(count1, 2);

        let olean_dst = wt_dir.join(".lake/build/lib/lean/Demo.olean");
        let cas_src = store.blob_path(&entries[1].blob_hash);
        let ino1 = fs::metadata(&olean_dst)?.ino();
        let cas_ino = fs::metadata(&cas_src)?.ino();
        assert_eq!(ino1, cas_ino);

        // 2. Second materialization hits zero-unlink fast path and preserves exact inode
        let count2 = store.materialize_into_worktree(&wt_dir, "DemoProj", &entries)?;
        assert_eq!(count2, 2);
        let ino2 = fs::metadata(&olean_dst)?.ino();
        assert_eq!(ino1, ino2);

        // 3. If a file in the worktree is unlinked and replaced with a different inode,
        // materialize_into_worktree detects the inode mismatch and self-heals by unlinking & re-hardlinking
        fs::remove_file(&olean_dst)?;
        fs::write(&olean_dst, b"corrupted_non_cas_file")?;
        let corrupted_ino = fs::metadata(&olean_dst)?.ino();
        assert_ne!(corrupted_ino, cas_ino);

        let count3 = store.materialize_into_worktree(&wt_dir, "DemoProj", &entries)?;
        assert_eq!(count3, 2);
        let healed_ino = fs::metadata(&olean_dst)?.ino();
        assert_eq!(healed_ino, cas_ino);
        assert_eq!(fs::read(&olean_dst)?, b"olean_payload_1");

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_file_stat_cache_zero_read_hit_and_invalidation() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_stat_cache_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(&tmp_dir)?;

        let store = TurboStore::open(Some(&tmp_dir.join("cache")))?;
        let lean_file = tmp_dir.join("Sample.lean");
        let src1 = "theorem t1 : 1 = 1 := rfl\n";
        fs::write(&lean_file, src1)?;

        let meta1 = fs::metadata(&lean_file)?;
        let (ms1, mn1, sz1) = TurboStore::extract_file_stat_tuple(&meta1);
        let pk = lean_file.to_string_lossy().to_string();

        // Initially empty
        assert!(store
            .batch_get_file_splits_by_stat(&[(pk.clone(), ms1, mn1, sz1)])?
            .is_empty());

        // Populate file_split_cache + file_stat_cache
        let sk1 = TurboStore::compute_file_split_key(src1.as_bytes());
        let split1 = crate::splitter::split_lean_source(src1, &[]);
        store.batch_put_file_splits(&[(sk1.clone(), &split1)])?;
        store.batch_put_file_stats(&[(pk.clone(), ms1, mn1, sz1, sk1.clone())])?;

        // Stat lookup hits without reading file contents
        let hit_map = store.batch_get_file_splits_by_stat(&[(pk.clone(), ms1, mn1, sz1)])?;
        let (got_sk, got_split) = hit_map.get(&pk).expect("stat hit");
        assert_eq!(got_sk, &sk1);
        assert_eq!(got_split.interface_hash, split1.interface_hash);
        assert_eq!(got_split.shards.len(), 1);

        // Modifying the file invalidates the stat tuple
        let src2 = "theorem t1 : 1 = 1 := rfl\ntheorem t2 : 2 = 2 := rfl\n";
        fs::write(&lean_file, src2)?;
        let meta2 = fs::metadata(&lean_file)?;
        let (ms2, mn2, sz2) = TurboStore::extract_file_stat_tuple(&meta2);
        assert!(store
            .batch_get_file_splits_by_stat(&[(pk.clone(), ms2, mn2, sz2)])?
            .is_empty());

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_worktree_lease_supersession_gc_protects_concurrent_agent_and_evicts_superseded() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_wt_supersession_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let cache_dir = tmp_dir.join("cache");
        let wt_a = tmp_dir.join("wt_a");
        let wt_b = tmp_dir.join("wt_b");
        fs::create_dir_all(&wt_a)?;
        fs::create_dir_all(&wt_b)?;

        let mut store = TurboStore::open(Some(&cache_dir))?;

        // Agent A produces blob_v1 for Foo.olean
        let blob_v1 = store.store_immutable_blob(b"agent_a_draft_v1_olean", "olean", "trusted", 0)?;
        let sup1 = store.update_worktree_lease(
            &wt_a,
            "HEAD",
            &[(".lake/build/lib/lean/Foo.olean".to_string(), blob_v1.clone())],
        )?;
        assert_eq!(sup1, 0);

        // Agent B concurrently holds an active lease on blob_shared
        let blob_shared =
            store.store_immutable_blob(b"agent_b_active_shared_olean", "olean", "trusted", 0)?;
        let sup_b = store.update_worktree_lease(
            &wt_b,
            "HEAD",
            &[(".lake/build/lib/lean/Shared.olean".to_string(), blob_shared.clone())],
        )?;
        assert_eq!(sup_b, 0);

        // Agent A edits Foo.lean and produces blob_v2 (superseding blob_v1 in wt_a)
        let blob_v2 = store.store_immutable_blob(b"agent_a_draft_v2_olean", "olean", "trusted", 0)?;
        let sup2 = store.update_worktree_lease(
            &wt_a,
            "HEAD",
            &[(".lake/build/lib/lean/Foo.olean".to_string(), blob_v2.clone())],
        )?;
        assert_eq!(sup2, 1, "blob_v1 should be marked superseded");

        // Run gc_gdsf: blob_v1 must be immediately evicted, while blob_v2 and blob_shared are preserved
        let report = store.gc_gdsf(10 * 1024 * 1024)?;
        assert!(
            report.superseded_evicted >= 1,
            "Expected superseded_evicted >= 1, got {:?}",
            report
        );
        assert!(
            !store.blob_path(&blob_v1).exists(),
            "Superseded blob_v1 should be evicted from disk"
        );
        assert!(
            store.blob_path(&blob_v2).exists(),
            "Agent A's active blob_v2 must be preserved"
        );
        assert!(
            store.blob_path(&blob_shared).exists(),
            "Agent B's active blob_shared must be preserved"
        );

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_tlz1_cold_blob_compression_and_hot_repromotion_roundtrip() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_tlz1_roundtrip_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let cache_dir = tmp_dir.join("cache");
        let mut store = TurboStore::open(Some(&cache_dir))?;

        // Build a repetitive 4 KB .olean-like payload with nlink == 1
        let mut raw_olean = Vec::with_capacity(4096);
        for i in 0..128u32 {
            raw_olean.extend_from_slice(b"OLEAN_HEADER_SECTION_LEAN4_");
            raw_olean.extend_from_slice(&(i % 4).to_le_bytes());
            raw_olean.push(b'\n');
        }
        assert_eq!(raw_olean.len(), 4096);

        let bh = store.store_immutable_blob(&raw_olean, "olean", "trusted", 0)?;
        let blob_file = store.blob_path(&bh);
        assert_eq!(fs::metadata(&blob_file)?.nlink(), 1);
        assert_eq!(fs::metadata(&blob_file)?.len(), 4096);

        // Run gc_gdsf to trigger Step C (TLZ1 cold compression on nlink == 1 blobs)
        let report = store.gc_gdsf(10 * 1024 * 1024)?;
        assert!(
            report.compressed_blobs >= 1,
            "Expected compressed_blobs >= 1, got {:?}",
            report
        );

        let on_disk_compressed = fs::read(&blob_file)?;
        assert!(
            on_disk_compressed.starts_with(b"TLZ1"),
            "Cold blob on disk must start with TLZ1 magic header"
        );
        assert!(
            on_disk_compressed.len() < 4096,
            "Cold TLZ1 blob must be smaller than 4096 bytes, got {}",
            on_disk_compressed.len()
        );

        // Restore blob to a destination path: must transparently decompress back to Hot tier and hardlink
        let restored_path = tmp_dir.join("restored").join("Foo.olean");
        let link_mode = store.restore_blob_to_path(&bh, &restored_path)?;
        assert_eq!(link_mode, "hardlink");

        let restored_bytes = fs::read(&restored_path)?;
        assert_eq!(
            restored_bytes, raw_olean,
            "Restored blob must be byte-for-byte identical to original 4 KB blob"
        );
        assert_eq!(
            fs::metadata(&blob_file)?.ino(),
            fs::metadata(&restored_path)?.ino(),
            "Re-promoted Hot blob and restored destination must share the same inode"
        );

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }
}
