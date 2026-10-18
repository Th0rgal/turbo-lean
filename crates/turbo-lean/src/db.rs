use anyhow::{Context, Result};
use rusqlite::{params, Connection, OptionalExtension};
use serde::{Deserialize, Serialize};
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

pub fn now_unix() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64
}

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
}

pub struct SingleflightLease {
    pub action_key: String,
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

pub struct TurboStore {
    pub root: PathBuf,
    pub conn: Connection,
}

impl TurboStore {
    pub fn open(custom_root: Option<&Path>) -> Result<Self> {
        let root = match custom_root {
            Some(p) => p.to_path_buf(),
            None => {
                if let Ok(env_root) = std::env::var("TURBO_LEAN_HOME") {
                    PathBuf::from(env_root)
                } else {
                    let home = std::env::var("HOME").unwrap_or_else(|_| "/tmp".to_string());
                    PathBuf::from(home).join(".cache").join("turbo-lean")
                }
            }
        };

        let db_path = root.join("state.db");
        let db_warm = fs::metadata(&db_path)
            .map(|m| m.len() >= 4096)
            .unwrap_or(false);
        if !db_warm {
            fs::create_dir_all(&root)?;
            let _ = fs::create_dir(root.join("blobs"));
            let _ = fs::create_dir(root.join("staging"));
            let _ = fs::create_dir(root.join("locks"));
        }
        let conn = Connection::open(&db_path)
            .with_context(|| format!("Failed to open SQLite DB at {}", db_path.display()))?;

        if db_warm {
            conn.execute_batch(
                "
                PRAGMA synchronous = NORMAL;
                PRAGMA busy_timeout = 5000;
                PRAGMA foreign_keys = ON;
                PRAGMA mmap_size = 268435456;
                PRAGMA temp_store = MEMORY;
                PRAGMA cache_size = -65536;
                ",
            )?;
        } else {
            conn.execute_batch(
                "
                PRAGMA journal_mode = WAL;
                PRAGMA synchronous = NORMAL;
                PRAGMA busy_timeout = 5000;
                PRAGMA foreign_keys = ON;
                PRAGMA mmap_size = 268435456;
                PRAGMA temp_store = MEMORY;
                PRAGMA cache_size = -65536;

                BEGIN;
                CREATE TABLE IF NOT EXISTS meta_counters (
                    name TEXT PRIMARY KEY,
                    val  INTEGER NOT NULL
                );
                INSERT OR IGNORE INTO meta_counters (name, val) VALUES ('fencing_seq', 1);
                INSERT OR IGNORE INTO meta_counters (name, val) VALUES ('coalesced_waits', 0);

                CREATE TABLE IF NOT EXISTS blobs (
                    blob_hash       TEXT PRIMARY KEY,
                    kind            TEXT NOT NULL,
                    size_bytes      INTEGER NOT NULL,
                    inode           INTEGER NOT NULL,
                    created_at      INTEGER NOT NULL,
                    last_accessed   INTEGER NOT NULL,
                    pin_level       INTEGER NOT NULL DEFAULT 0,
                    trust_domain    TEXT NOT NULL DEFAULT 'trusted'
                );

                CREATE TABLE IF NOT EXISTS actions (
                    action_key           TEXT PRIMARY KEY,
                    toolchain_githash    TEXT NOT NULL,
                    kind                 TEXT NOT NULL,
                    status               TEXT NOT NULL,
                    fencing_token        INTEGER NOT NULL,
                    output_manifest_hash TEXT,
                    duration_ms          INTEGER NOT NULL DEFAULT 0,
                    peak_pss_bytes       INTEGER NOT NULL DEFAULT 0,
                    heartbeats           INTEGER NOT NULL DEFAULT 0,
                    trust_domain         TEXT NOT NULL DEFAULT 'trusted',
                    updated_at           INTEGER NOT NULL,
                    hit_count            INTEGER NOT NULL DEFAULT 0
                );
                CREATE INDEX IF NOT EXISTS idx_actions_kind_status_domain
                    ON actions(kind, status, trust_domain);

                CREATE TABLE IF NOT EXISTS action_outputs (
                    action_key      TEXT NOT NULL REFERENCES actions(action_key) ON DELETE CASCADE,
                    rel_path        TEXT NOT NULL,
                    blob_hash       TEXT NOT NULL REFERENCES blobs(blob_hash),
                    PRIMARY KEY (action_key, rel_path)
                );

                CREATE TABLE IF NOT EXISTS worktrees (
                    worktree_id     TEXT PRIMARY KEY,
                    root_path       TEXT NOT NULL UNIQUE,
                    project_name    TEXT NOT NULL,
                    last_seen       INTEGER NOT NULL
                );

                CREATE TABLE IF NOT EXISTS worktree_installations (
                    worktree_id     TEXT NOT NULL REFERENCES worktrees(worktree_id) ON DELETE CASCADE,
                    rel_path        TEXT NOT NULL,
                    blob_hash       TEXT NOT NULL REFERENCES blobs(blob_hash),
                    link_mode       TEXT NOT NULL,
                    PRIMARY KEY (worktree_id, rel_path)
                );

                CREATE TABLE IF NOT EXISTS inflight_leases (
                    action_key      TEXT PRIMARY KEY,
                    fencing_token   INTEGER NOT NULL,
                    worker_pid      INTEGER NOT NULL,
                    boot_id         TEXT NOT NULL,
                    started_at      INTEGER NOT NULL,
                    waiter_count    INTEGER NOT NULL DEFAULT 1
                );

                CREATE TABLE IF NOT EXISTS attestations (
                    action_key      TEXT NOT NULL REFERENCES actions(action_key) ON DELETE CASCADE,
                    checker_name    TEXT NOT NULL,
                    checker_version TEXT NOT NULL,
                    axioms_json     TEXT NOT NULL,
                    signature       TEXT,
                    verified_at     INTEGER NOT NULL,
                    PRIMARY KEY (action_key, checker_name)
                );

                CREATE TABLE IF NOT EXISTS lake_env_cache (
                    project_key     TEXT PRIMARY KEY,
                    env_json        TEXT NOT NULL,
                    updated_at      INTEGER NOT NULL
                );

                CREATE TABLE IF NOT EXISTS file_split_cache (
                    file_hash           TEXT PRIMARY KEY,
                    split_json          TEXT NOT NULL,
                    hygiene_issues_json TEXT NOT NULL,
                    updated_at          INTEGER NOT NULL
                );

                CREATE TABLE IF NOT EXISTS file_stat_cache (
                    path_key    TEXT PRIMARY KEY,
                    mtime_sec   INTEGER NOT NULL,
                    mtime_nsec  INTEGER NOT NULL,
                    size_bytes  INTEGER NOT NULL,
                    split_key   TEXT NOT NULL,
                    updated_at  INTEGER NOT NULL
                );
                PRAGMA user_version = 1;
                COMMIT;
                ",
            )?;
        }

        Ok(Self { root, conn })
    }

    /// Compute the deterministic BLAKE3 cache key for `file_split_cache`:
    /// `BLAKE3("file-split:v3:" + raw_file_bytes)`
    pub fn compute_file_split_key(raw_bytes: &[u8]) -> String {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"file-split:v3:");
        hasher.update(raw_bytes);
        hasher.finalize().to_hex().to_string()
    }

    /// Batch-lookup raw `split_json` strings from `file_split_cache` in a single SQLite transaction.
    pub fn batch_get_cached_file_splits(
        &self,
        content_hashes: &[String],
    ) -> Result<std::collections::HashMap<String, String>> {
        let raw_map = batch_get_file_splits(&self.conn, content_hashes)?;
        Ok(raw_map
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
        let raw_map = batch_get_file_splits(&self.conn, file_hashes)?;
        if raw_map.len() < 16 {
            let mut parsed = std::collections::HashMap::with_capacity(raw_map.len());
            for (fh, (split_json, _hygiene_json)) in raw_map {
                if let Ok(split) = serde_json::from_str::<crate::splitter::SplitResult>(&split_json)
                {
                    parsed.insert(fh, split);
                }
            }
            return Ok(parsed);
        }

        let raw_vec: Vec<(String, String)> = raw_map
            .into_iter()
            .map(|(fh, (split_json, _))| (fh, split_json))
            .collect();
        let workers = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .min(raw_vec.len());
        let next_idx = std::sync::atomic::AtomicUsize::new(0);
        let raw_ref = &raw_vec;
        let chunks: Vec<Vec<(String, crate::splitter::SplitResult)>> = std::thread::scope(|s| {
            let mut handles = Vec::with_capacity(workers);
            for _ in 0..workers {
                let next_ref = &next_idx;
                handles.push(s.spawn(move || {
                    let mut local = Vec::new();
                    loop {
                        let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if i >= raw_ref.len() {
                            break;
                        }
                        let (ref fh, ref split_json) = raw_ref[i];
                        if let Ok(split) =
                            serde_json::from_str::<crate::splitter::SplitResult>(split_json)
                        {
                            local.push((fh.clone(), split));
                        }
                    }
                    local
                }));
            }
            handles
                .into_iter()
                .map(|h| h.join().unwrap_or_default())
                .collect()
        });

        let mut parsed = std::collections::HashMap::with_capacity(raw_vec.len());
        for chunk in chunks {
            for (fh, split) in chunk {
                parsed.insert(fh, split);
            }
        }
        Ok(parsed)
    }

    /// Batch-store multiple parsed `SplitResult`s into `file_split_cache` in a single SQLite transaction.
    /// Strips redundant `skeleton_source`, `shard_source`, and `signature_text` fields before serialization
    /// so cached rows contain only hashes and metadata (~20x smaller across 691-file repositories).
    pub fn batch_put_file_splits(
        &self,
        entries: &[(String, &crate::splitter::SplitResult)],
    ) -> Result<()> {
        if entries.is_empty() {
            return Ok(());
        }
        let serialize_one = |(fh, split): &(String, &crate::splitter::SplitResult)| -> Result<(String, String, String)> {
            let mut compact = (*split).clone();
            let keep_proof_text = compact.hygiene.has_sorry;
            compact.skeleton_source.clear();
            for sh in &mut compact.shards {
                sh.shard_source.clear();
                sh.signature_text.clear();
                if !keep_proof_text {
                    sh.proof_text.clear();
                }
            }
            let split_json = serde_json::to_string(&compact)?;
            let hygiene_json = serde_json::to_string(&split.hygiene.flagged_items)?;
            Ok((fh.clone(), split_json, hygiene_json))
        };

        let raw_entries: Vec<(String, String, String)> = if entries.len() < 16 {
            let mut v = Vec::with_capacity(entries.len());
            for item in entries {
                v.push(serialize_one(item)?);
            }
            v
        } else {
            let workers = std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4)
                .min(entries.len());
            let next_idx = std::sync::atomic::AtomicUsize::new(0);
            let chunks: Vec<Vec<(String, String, String)>> = std::thread::scope(|s| {
                let mut handles = Vec::with_capacity(workers);
                for _ in 0..workers {
                    let next_ref = &next_idx;
                    handles.push(s.spawn(move || {
                        let mut local = Vec::new();
                        loop {
                            let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            if i >= entries.len() {
                                break;
                            }
                            if let Ok(row) = serialize_one(&entries[i]) {
                                local.push(row);
                            }
                        }
                        local
                    }));
                }
                handles
                    .into_iter()
                    .map(|h| h.join().unwrap_or_default())
                    .collect()
            });
            chunks.into_iter().flatten().collect()
        };
        batch_put_file_splits(&self.conn, &raw_entries)
    }

    /// Extract a high-resolution `(mtime_sec, mtime_nsec_mixed, size_bytes)` stat tuple from `fs::Metadata`.
    pub fn extract_file_stat_tuple(meta: &fs::Metadata) -> (i64, i64, i64) {
        let mtime_sec = meta.mtime();
        let mtime_nsec = meta.mtime_nsec()
            ^ (meta.ctime_nsec().wrapping_mul(31))
            ^ ((meta.ino() as i64).wrapping_mul(131));
        let size_bytes = meta.len() as i64;
        (mtime_sec, mtime_nsec, size_bytes)
    }

    /// Batch-lookup `(split_key, SplitResult)` by `(path_key, mtime_sec, mtime_nsec, size_bytes)`
    /// via a single SQLite join across `file_stat_cache` and `file_split_cache` without reading file contents.
    pub fn batch_get_file_splits_by_stat(
        &self,
        stats: &[(String, i64, i64, i64)],
    ) -> Result<std::collections::HashMap<String, (String, crate::splitter::SplitResult)>> {
        let raw_vec = batch_get_raw_file_splits_by_stat(&self.conn, stats)?;
        if raw_vec.len() < 16 {
            let mut parsed = std::collections::HashMap::with_capacity(raw_vec.len());
            for (path_key, split_key, split_json) in raw_vec {
                if let Ok(split) = serde_json::from_str::<crate::splitter::SplitResult>(&split_json)
                {
                    parsed.insert(path_key, (split_key, split));
                }
            }
            return Ok(parsed);
        }

        let workers = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .min(raw_vec.len());
        let next_idx = std::sync::atomic::AtomicUsize::new(0);
        let raw_ref = &raw_vec;
        let chunks: Vec<Vec<(String, (String, crate::splitter::SplitResult))>> =
            std::thread::scope(|s| {
                let mut handles = Vec::with_capacity(workers);
                for _ in 0..workers {
                    let next_ref = &next_idx;
                    handles.push(s.spawn(move || {
                        let mut local = Vec::new();
                        loop {
                            let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            if i >= raw_ref.len() {
                                break;
                            }
                            let (ref path_key, ref split_key, ref split_json) = raw_ref[i];
                            if let Ok(split) =
                                serde_json::from_str::<crate::splitter::SplitResult>(split_json)
                            {
                                local.push((path_key.clone(), (split_key.clone(), split)));
                            }
                        }
                        local
                    }));
                }
                handles
                    .into_iter()
                    .map(|h| h.join().unwrap_or_default())
                    .collect()
            });

        let mut parsed = std::collections::HashMap::with_capacity(raw_vec.len());
        for chunk in chunks {
            for (pk, val) in chunk {
                parsed.insert(pk, val);
            }
        }
        Ok(parsed)
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

    /// Return a RAM-backed `tmpfs` staging directory (`/dev/shm/turbo-lean-staging`) when available,
    /// falling back to `self.root.join("staging")` so temporary `.lean` shard files never touch disk.
    pub fn fast_staging_dir(&self) -> PathBuf {
        let shm = Path::new("/dev/shm");
        if shm.is_dir() {
            let dir = shm.join("turbo-lean-staging");
            if fs::create_dir_all(&dir).is_ok() {
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

    /// Batch-insert or update imported `.tlpack` blobs, actions, and action_outputs inside a single
    /// `BEGIN IMMEDIATE ... COMMIT` SQLite transaction.
    pub fn batch_import_pack_metadata(
        &mut self,
        blobs: &[(String, String, i64, i64)],
        actions: &[ActionRecord],
    ) -> Result<(usize, usize)> {
        batch_import_pack_metadata(&self.conn, blobs, actions)
    }

    pub fn get_cached_action(&self, action_key: &str, trust_domain: &str) -> Result<Option<Vec<BlobEntry>>> {
        let status: Option<String> = self
            .conn
            .query_row(
                "SELECT status FROM actions WHERE action_key = ?1 AND trust_domain = ?2",
                params![action_key, trust_domain],
                |row| row.get(0),
            )
            .optional()?;

        if status.as_deref() != Some("completed") {
            return Ok(None);
        }

        let mut stmt = self.conn.prepare(
            "SELECT b.blob_hash, b.kind, b.size_bytes, ao.rel_path
             FROM action_outputs ao
             JOIN blobs b ON b.blob_hash = ao.blob_hash
             WHERE ao.action_key = ?1
             ORDER BY ao.rel_path ASC",
        )?;

        let entries: Vec<BlobEntry> = stmt
            .query_map(params![action_key], |row| {
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

        let now = now_unix();
        let _ = self.conn.execute(
            "UPDATE actions SET hit_count = hit_count + 1 WHERE action_key = ?1",
            params![action_key],
        );
        let _ = self.conn.execute(
            "UPDATE blobs SET last_accessed = ?1
             WHERE blob_hash IN (SELECT blob_hash FROM action_outputs WHERE action_key = ?2)",
            params![now, action_key],
        );

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
        if let Some(outputs) = self.get_cached_action(action_key, trust_domain)? {
            return Ok(SingleflightOutcome::CacheHit {
                outputs,
                coalesced: false,
            });
        }

        let lock_path = self.root.join("locks").join(format!("{}.lock", action_key));
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
            // Block in kernel until the leader finishes (or crashes, which auto-releases flock)
            let wait_rc = unsafe { libc::flock(fd, libc::LOCK_EX) };
            if wait_rc != 0 {
                anyhow::bail!("flock wait failed for action {}", action_key);
            }
        }

        // Now we hold LOCK_EX! Re-check if the prior holder completed the action
        if let Some(outputs) = self.get_cached_action(action_key, trust_domain)? {
            if waited_on_peer {
                let _ = self.conn.execute(
                    "UPDATE meta_counters SET val = val + 1 WHERE name = 'coalesced_waits'",
                    [],
                );
            }
            unsafe {
                libc::flock(fd, libc::LOCK_UN);
            }
            return Ok(SingleflightOutcome::CacheHit {
                outputs,
                coalesced: waited_on_peer,
            });
        }

        // We are the Leader (either first arrival, or previous holder crashed before completing).
        // Issue a monotonic fencing token inside a short transaction.
        let tx = self.conn.transaction()?;
        tx.execute(
            "UPDATE meta_counters SET val = val + 1 WHERE name = 'fencing_seq'",
            [],
        )?;
        let fencing_token: i64 = tx.query_row(
            "SELECT val FROM meta_counters WHERE name = 'fencing_seq'",
            [],
            |r| r.get(0),
        )?;

        let now = now_unix();
        let pid = std::process::id() as i64;
        let boot = boot_id();

        tx.execute(
            "INSERT INTO actions (action_key, toolchain_githash, kind, status, fencing_token, trust_domain, updated_at)
             VALUES (?1, ?2, ?3, 'running', ?4, ?5, ?6)
             ON CONFLICT(action_key) DO UPDATE SET
                status = 'running',
                fencing_token = excluded.fencing_token,
                updated_at = excluded.updated_at",
            params![action_key, toolchain, kind, fencing_token, trust_domain, now],
        )?;

        tx.execute(
            "INSERT INTO inflight_leases (action_key, fencing_token, worker_pid, boot_id, started_at, waiter_count)
             VALUES (?1, ?2, ?3, ?4, ?5, 1)
             ON CONFLICT(action_key) DO UPDATE SET
                fencing_token = excluded.fencing_token,
                worker_pid = excluded.worker_pid,
                boot_id = excluded.boot_id,
                started_at = excluded.started_at",
            params![action_key, fencing_token, pid, boot, now],
        )?;
        tx.commit()?;

        Ok(SingleflightOutcome::Leader(SingleflightLease {
            action_key: action_key.to_string(),
            fencing_token,
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

    pub fn batch_publish_theorem_shards(
        &mut self,
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
            std::collections::HashMap::new();
        let mut created_prefixes: std::collections::HashSet<String> =
            std::collections::HashSet::new();

        for (action_key, decl_name, receipt_bytes, dur_ms) in items {
            let hash = blake3::hash(receipt_bytes).to_hex().to_string();
            let (inode, size) = if let Some(&(ino, sz)) = seen_blobs.get(&hash) {
                (ino, sz)
            } else {
                let dest = self.blob_path(&hash);
                let (ino, sz) = if let Ok(meta) = fs::metadata(&dest) {
                    (meta.ino() as i64, meta.len() as i64)
                } else {
                    let prefix = if hash.len() >= 2 { &hash[..2] } else { "00" };
                    if created_prefixes.insert(prefix.to_string()) {
                        if let Some(parent) = dest.parent() {
                            fs::create_dir_all(parent)?;
                        }
                    }
                    use std::os::unix::fs::OpenOptionsExt;
                    let ino = match OpenOptions::new()
                        .write(true)
                        .create_new(true)
                        .mode(0o444)
                        .open(&dest)
                    {
                        Ok(mut f) => {
                            f.write_all(receipt_bytes)?;
                            f.metadata().map(|m| m.ino() as i64).unwrap_or(0)
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
                            let i = f.metadata().map(|m| m.ino() as i64).unwrap_or(0);
                            drop(f);
                            fs::rename(&staging_path, &dest)?;
                            i
                        }
                    };
                    (ino, receipt_bytes.len() as i64)
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

        let tx = self.conn.unchecked_transaction()?;
        tx.execute(
            "UPDATE meta_counters SET val = val + ?1 WHERE name = 'fencing_seq'",
            params![staged.len() as i64],
        )?;
        let end_fencing_token: i64 = tx.query_row(
            "SELECT val FROM meta_counters WHERE name = 'fencing_seq'",
            [],
            |r| r.get(0),
        )?;
        let base_fencing_token = end_fencing_token - (staged.len() as i64);
        {
            let mut ins_blob = tx.prepare_cached(
                "INSERT INTO blobs (blob_hash, kind, size_bytes, inode, created_at, last_accessed, pin_level, trust_domain)
                 VALUES (?1, 'expr_shard', ?2, ?3, ?4, ?4, 0, ?5)
                 ON CONFLICT(blob_hash) DO UPDATE SET last_accessed = excluded.last_accessed",
            )?;
            let mut ins_act = tx.prepare_cached(
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
            let mut ins_out = tx.prepare_cached(
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
        }
        tx.commit()?;
        Ok(())
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

        let tx = self.conn.unchecked_transaction()?;
        let current_token: i64 = tx.query_row(
            "SELECT fencing_token FROM actions WHERE action_key = ?1",
            params![lease.action_key],
            |r| r.get(0),
        )?;

        if current_token != lease.fencing_token {
            anyhow::bail!(
                "Fencing token mismatch for {}: held {}, DB has {}",
                lease.action_key,
                lease.fencing_token,
                current_token
            );
        }

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

        let now = now_unix();
        tx.execute(
            "UPDATE actions SET
                status = 'completed',
                output_manifest_hash = ?2,
                duration_ms = ?3,
                peak_pss_bytes = ?4,
                heartbeats = ?5,
                trust_domain = ?6,
                updated_at = ?7
             WHERE action_key = ?1",
            params![
                lease.action_key,
                manifest_hash,
                duration_ms,
                peak_pss_bytes,
                heartbeats,
                trust_domain,
                now
            ],
        )?;

        tx.execute(
            "DELETE FROM inflight_leases WHERE action_key = ?1",
            params![lease.action_key],
        )?;

        tx.commit()?;
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

    /// Materialize CAS blobs into a worktree using FICLONE reflink (if supported),
    /// or safe unlink + 0444 hardlink (protecting mmap Shared_Clean inodes from SIGBUS truncation),
    /// or copy fallback across filesystems.
    /// Fast path: if destination already shares the exact same `(dev, ino)` as the CAS blob,
    /// skips unlink + hardlink completely!
    pub fn materialize_into_worktree(
        &mut self,
        worktree_root: &Path,
        project_name: &str,
        outputs: &[BlobEntry],
    ) -> Result<usize> {
        let canon_root = worktree_root
            .canonicalize()
            .unwrap_or_else(|_| worktree_root.to_path_buf());
        let root_str = canon_root.to_string_lossy().to_string();
        let wt_id = blake3::hash(root_str.as_bytes()).to_hex().to_string();
        let now = now_unix();

        let blobs_root = self.root.join("blobs");
        let tx = self.conn.unchecked_transaction()?;
        tx.execute(
            "INSERT INTO worktrees (worktree_id, root_path, project_name, last_seen)
             VALUES (?1, ?2, ?3, ?4)
             ON CONFLICT(worktree_id) DO UPDATE SET last_seen = excluded.last_seen",
            params![wt_id, root_str, project_name, now],
        )?;

        let mut existing_map: std::collections::HashMap<String, String> =
            std::collections::HashMap::with_capacity(outputs.len());
        {
            let mut q_stmt = tx.prepare_cached(
                "SELECT rel_path, blob_hash FROM worktree_installations WHERE worktree_id = ?1",
            )?;
            let rows = q_stmt.query_map(params![wt_id], |r| {
                Ok((r.get::<_, String>(0)?, r.get::<_, String>(1)?))
            })?;
            for row in rows {
                let (rp, bh) = row?;
                existing_map.insert(rp, bh);
            }
        }

        let mut created_dirs: std::collections::HashSet<PathBuf> =
            std::collections::HashSet::new();
        let mut linked = 0usize;
        {
            let mut ins_inst = tx.prepare_cached(
                "INSERT INTO worktree_installations (worktree_id, rel_path, blob_hash, link_mode)
                 VALUES (?1, ?2, ?3, ?4)
                 ON CONFLICT(worktree_id, rel_path) DO UPDATE SET
                    blob_hash = excluded.blob_hash,
                    link_mode = excluded.link_mode",
            )?;

            for out in outputs {
                // Skip internal logical shards that don't belong in the worktree filesystem
                if out.rel_path.starts_with("thm:") {
                    continue;
                }
                let prefix = if out.blob_hash.len() >= 2 {
                    &out.blob_hash[0..2]
                } else {
                    "00"
                };
                let src = blobs_root.join(prefix).join(&out.blob_hash);
                let dst = canon_root.join(&out.rel_path);

                let already_same_inode = match (fs::metadata(&src), fs::metadata(&dst)) {
                    (Ok(src_meta), Ok(dst_meta)) => {
                        src_meta.dev() == dst_meta.dev() && src_meta.ino() == dst_meta.ino()
                    }
                    _ => false,
                };

                if already_same_inode {
                    if existing_map.get(&out.rel_path) != Some(&out.blob_hash) {
                        ins_inst.execute(params![
                            wt_id,
                            out.rel_path,
                            out.blob_hash,
                            "hardlink"
                        ])?;
                    }
                    linked += 1;
                    continue;
                }

                if let Some(parent) = dst.parent() {
                    if created_dirs.insert(parent.to_path_buf()) {
                        fs::create_dir_all(parent)?;
                    }
                }

                // Always unlink destination first so we never truncate/mutate a shared inode in place!
                if dst.exists() {
                    let _ = fs::remove_file(&dst);
                }

                let mode = try_reflink_or_hardlink(&src, &dst)?;
                if existing_map.get(&out.rel_path) != Some(&out.blob_hash) {
                    ins_inst.execute(params![wt_id, out.rel_path, out.blob_hash, mode])?;
                }
                linked += 1;
            }
        }
        tx.commit()?;
        Ok(linked)
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
    /// Also detects deleted/stale worktrees, cleans orphaned staging files in `<store>/staging` and
    /// `/dev/shm/turbo-lean-staging`, and prunes old cached binaries in `<store>/fastcheck_bins`.
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

        // 0. Clean orphaned temporary files in `<store>/staging` and `/dev/shm/turbo-lean-staging`
        for st_dir in [self.root.join("staging"), self.fast_staging_dir()] {
            if let Ok(entries) = fs::read_dir(&st_dir) {
                for entry in entries.flatten() {
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
                // If expired but directory still exists, unlink materialized CAS files so st_nlink drops
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

        let initial_status = self.storage_status()?;
        if initial_status.reclaimable_bytes <= max_reclaimable_bytes {
            return Ok(GcReport {
                pruned_worktrees,
                evicted_actions: 0,
                unlinked_blobs: 0,
                cleaned_staging_files,
                pruned_fastcheck_bins,
                freed_reclaimable_bytes: freed_bytes,
                remaining_reclaimable_bytes: initial_status.reclaimable_bytes,
            });
        }

        // 2. Rank completed actions by GDSF KeepScore ascending (lowest score evicted first)
        let candidates: Vec<String> = {
            let mut stmt = self.conn.prepare(
                "SELECT a.action_key,
                        a.updated_at + (a.duration_ms * 1000000) / MAX(1, COALESCE(SUM(b.size_bytes), 1)) AS gdsf_score
                 FROM actions a
                 LEFT JOIN action_outputs ao ON ao.action_key = a.action_key
                 LEFT JOIN blobs b ON b.blob_hash = ao.blob_hash
                 WHERE a.status = 'completed'
                 GROUP BY a.action_key
                 ORDER BY gdsf_score ASC",
            )?;
            let mapped = stmt.query_map([], |r| r.get::<_, String>(0))?;
            mapped.collect::<std::result::Result<Vec<_>, _>>()?
        };

        let mut evicted_actions = 0usize;
        let mut unlinked_blobs = 0usize;
        let mut current_reclaimable = initial_status.reclaimable_bytes;

        for action_key in candidates {
            if current_reclaimable <= max_reclaimable_bytes {
                break;
            }
            self.conn.execute(
                "DELETE FROM actions WHERE action_key = ?1",
                params![action_key],
            )?;
            evicted_actions += 1;

            // Find orphan blobs no longer referenced by any action_outputs
            let orphan_blobs: Vec<(String, u64, i64)> = {
                let mut stmt = self.conn.prepare(
                    "SELECT b.blob_hash, b.size_bytes, b.pin_level
                     FROM blobs b
                     LEFT JOIN action_outputs ao ON ao.blob_hash = b.blob_hash
                     WHERE ao.blob_hash IS NULL",
                )?;
                let mapped = stmt.query_map([], |r| {
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
                self.conn
                    .execute("DELETE FROM blobs WHERE blob_hash = ?1", params![bh])?;
                unlinked_blobs += 1;
                if nlink == 1 && pin == 0 {
                    freed_bytes += sz;
                    current_reclaimable = current_reclaimable.saturating_sub(sz);
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
        })
    }
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
    let tx = conn.unchecked_transaction()?;
    let mut hits = std::collections::HashMap::with_capacity(shard_keys.len());

    if shard_keys.len() >= 128 {
        let mut db_map = std::collections::HashMap::with_capacity(shard_keys.len());
        {
            let mut scan_stmt = tx.prepare_cached(
                "SELECT a.action_key, ao.blob_hash
                 FROM actions a
                 JOIN action_outputs ao ON ao.action_key = a.action_key
                 WHERE a.status = 'completed' AND a.trust_domain = ?1",
            )?;
            let mut rows = scan_stmt.query(params![trust_domain])?;
            while let Some(row) = rows.next()? {
                let ak: String = row.get(0)?;
                let bh: String = row.get(1)?;
                db_map.insert(ak, bh);
            }
        }

        let mut touched_blobs = std::collections::HashSet::new();
        let mut hit_keys_in_order = Vec::with_capacity(shard_keys.len());
        for key in shard_keys {
            if let Some(blob_hash) = db_map.get(key) {
                hit_keys_in_order.push(key.as_str());
                touched_blobs.insert(blob_hash.clone());
                hits.insert(key.clone(), blob_hash.clone());
            }
        }

        if !hit_keys_in_order.is_empty() {
            if hits.len() == db_map.len() && hit_keys_in_order.len() == hits.len() {
                tx.execute(
                    "UPDATE actions SET hit_count = hit_count + 1 WHERE status = 'completed' AND trust_domain = ?1",
                    params![trust_domain],
                )?;
            } else {
                let mut upd_action = tx.prepare_cached(
                    "UPDATE actions SET hit_count = hit_count + 1 WHERE action_key = ?1",
                )?;
                for k in hit_keys_in_order {
                    upd_action.execute(params![k])?;
                }
            }
            let mut upd_blob = tx.prepare_cached(
                "UPDATE blobs SET last_accessed = ?1 WHERE blob_hash = ?2",
            )?;
            for bh in touched_blobs {
                upd_blob.execute(params![now, &bh])?;
            }
        }
    } else {
        let mut sel_stmt = tx.prepare_cached(
            "SELECT ao.blob_hash
             FROM actions a
             JOIN action_outputs ao ON ao.action_key = a.action_key
             WHERE a.action_key = ?1 AND a.status = 'completed' AND a.trust_domain = ?2
             LIMIT 1",
        )?;
        let mut upd_action = tx.prepare_cached(
            "UPDATE actions SET hit_count = hit_count + 1 WHERE action_key = ?1",
        )?;
        let mut upd_blob = tx.prepare_cached(
            "UPDATE blobs SET last_accessed = ?1 WHERE blob_hash = ?2",
        )?;

        let mut touched_blobs = std::collections::HashSet::new();
        for key in shard_keys {
            let found: Option<String> = sel_stmt
                .query_row(params![key, trust_domain], |r| r.get(0))
                .optional()?;
            if let Some(blob_hash) = found {
                upd_action.execute(params![key])?;
                if touched_blobs.insert(blob_hash.clone()) {
                    upd_blob.execute(params![now, &blob_hash])?;
                }
                hits.insert(key.clone(), blob_hash);
            }
        }
    }
    tx.commit()?;
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
    conn.execute_batch("BEGIN IMMEDIATE;")?;
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
                status = 'completed',
                output_manifest_hash = excluded.output_manifest_hash,
                updated_at = excluded.updated_at
             WHERE status != 'completed' OR output_manifest_hash IS NOT excluded.output_manifest_hash",
        )?;
        let mut ins_out = conn.prepare_cached(
            "INSERT INTO action_outputs (action_key, rel_path, blob_hash)
             VALUES (?1, ?2, ?3)
             ON CONFLICT(action_key, rel_path) DO UPDATE SET
                blob_hash = excluded.blob_hash
             WHERE blob_hash != excluded.blob_hash",
        )?;
        for act in actions {
            ins_act.execute(params![
                act.action_key,
                act.toolchain_githash,
                act.kind,
                act.fencing_token,
                act.output_manifest_hash,
                act.duration_ms,
                act.peak_pss_bytes,
                act.heartbeats,
                now
            ])?;
            for out in &act.outputs {
                ins_out.execute(params![act.action_key, out.rel_path, out.blob_hash])?;
            }
        }
        Ok((actions.len(), blobs.len()))
    })();
    match res {
        Ok(counts) => {
            conn.execute_batch("COMMIT;")?;
            Ok(counts)
        }
        Err(e) => {
            let _ = conn.execute_batch("ROLLBACK;");
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
        let wanted: std::collections::HashSet<&str> =
            file_hashes.iter().map(|s| s.as_str()).collect();
        let mut stmt = tx.prepare_cached(
            "SELECT file_hash, split_json, hygiene_issues_json FROM file_split_cache",
        )?;
        let mut rows = stmt.query([])?;
        while let Some(row) = rows.next()? {
            let fh: String = row.get(0)?;
            if wanted.contains(fh.as_str()) {
                let sj: String = row.get(1)?;
                let hj: String = row.get(2)?;
                hits.insert(fh, (sj, hj));
            }
        }
    } else {
        let mut stmt = tx.prepare_cached(
            "SELECT split_json, hygiene_issues_json FROM file_split_cache WHERE file_hash = ?1",
        )?;
        for fh in file_hashes {
            let row: Option<(String, String)> = stmt
                .query_row(params![fh], |r| Ok((r.get(0)?, r.get(1)?)))
                .optional()?;
            if let Some(pair) = row {
                hits.insert(fh.clone(), pair);
            }
        }
    }
    tx.commit()?;
    Ok(hits)
}

/// Batch-insert or update `file_split_cache` rows inside a single `BEGIN IMMEDIATE ... COMMIT` transaction.
pub fn batch_put_file_splits(
    conn: &Connection,
    entries: &[(String, String, String)],
) -> Result<()> {
    if entries.is_empty() {
        return Ok(());
    }
    let now = now_unix();
    let tx = conn.unchecked_transaction()?;
    {
        let mut stmt = tx.prepare_cached(
            "INSERT INTO file_split_cache (file_hash, split_json, hygiene_issues_json, updated_at)
             VALUES (?1, ?2, ?3, ?4)
             ON CONFLICT(file_hash) DO UPDATE SET
                split_json = excluded.split_json,
                hygiene_issues_json = excluded.hygiene_issues_json,
                updated_at = excluded.updated_at",
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
    if stats.is_empty() {
        return Ok(Vec::new());
    }
    let tx = conn.unchecked_transaction()?;
    let mut hits = Vec::with_capacity(stats.len());
    if stats.len() >= 64 {
        let mut wanted: std::collections::HashMap<&str, (i64, i64, i64)> =
            std::collections::HashMap::with_capacity(stats.len());
        for (pk, ms, mn, sz) in stats {
            wanted.insert(pk.as_str(), (*ms, *mn, *sz));
        }
        let mut stmt = tx.prepare_cached(
            "SELECT s.path_key, s.mtime_sec, s.mtime_nsec, s.size_bytes, s.split_key, c.split_json
             FROM file_stat_cache s
             JOIN file_split_cache c ON c.file_hash = s.split_key",
        )?;
        let mut rows = stmt.query([])?;
        while let Some(row) = rows.next()? {
            let pk: String = row.get(0)?;
            if let Some(&(exp_ms, exp_mn, exp_sz)) = wanted.get(pk.as_str()) {
                let ms: i64 = row.get(1)?;
                let mn: i64 = row.get(2)?;
                let sz: i64 = row.get(3)?;
                if ms == exp_ms && mn == exp_mn && sz == exp_sz {
                    let sk: String = row.get(4)?;
                    let sj: String = row.get(5)?;
                    hits.push((pk, sk, sj));
                }
            }
        }
    } else {
        let mut stmt = tx.prepare_cached(
            "SELECT s.split_key, c.split_json
             FROM file_stat_cache s
             JOIN file_split_cache c ON c.file_hash = s.split_key
             WHERE s.path_key = ?1 AND s.mtime_sec = ?2 AND s.mtime_nsec = ?3 AND s.size_bytes = ?4",
        )?;
        for (pk, ms, mn, sz) in stats {
            let row: Option<(String, String)> = stmt
                .query_row(params![pk, ms, mn, sz], |r| Ok((r.get(0)?, r.get(1)?)))
                .optional()?;
            if let Some((sk, sj)) = row {
                hits.push((pk.clone(), sk, sj));
            }
        }
    }
    tx.commit()?;
    Ok(hits)
}

/// Batch-insert or update `file_stat_cache` rows inside a single SQLite transaction.
pub fn batch_put_file_stats(
    conn: &Connection,
    entries: &[(String, i64, i64, i64, String)],
) -> Result<()> {
    if entries.is_empty() {
        return Ok(());
    }
    let now = now_unix();
    let tx = conn.unchecked_transaction()?;
    {
        let mut stmt = tx.prepare_cached(
            "INSERT INTO file_stat_cache (path_key, mtime_sec, mtime_nsec, size_bytes, split_key, updated_at)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6)
             ON CONFLICT(path_key) DO UPDATE SET
                mtime_sec = excluded.mtime_sec,
                mtime_nsec = excluded.mtime_nsec,
                size_bytes = excluded.size_bytes,
                split_key = excluded.split_key,
                updated_at = excluded.updated_at",
        )?;
        for (pk, ms, mn, sz, sk) in entries {
            stmt.execute(params![pk, ms, mn, sz, sk, now])?;
        }
    }
    tx.commit()?;
    Ok(())
}

fn try_reflink_or_hardlink(src: &Path, dst: &Path) -> Result<&'static str> {
    // 1. Try FICLONE ioctl reflink on CoW filesystems (Btrfs / XFS)
    #[cfg(target_os = "linux")]
    {
        use std::os::unix::io::AsRawFd;
        if let (Ok(src_file), Ok(dst_file)) = (File::open(src), File::create(dst)) {
            const FICLONE: libc::c_ulong = 0x40049409;
            let ret = unsafe { libc::ioctl(dst_file.as_raw_fd(), FICLONE, src_file.as_raw_fd()) };
            if ret == 0 {
                let mut perms = dst_file.metadata()?.permissions();
                perms.set_mode(0o444);
                let _ = dst_file.set_permissions(perms);
                return Ok("reflink");
            } else {
                drop(dst_file);
                let _ = fs::remove_file(dst);
            }
        }
    }

    // 2. Try immutable hardlink (shares OS page-cache mmap Shared_Clean across all worktrees)
    if fs::hard_link(src, dst).is_ok() {
        return Ok("hardlink");
    }

    // 3. Fallback to file copy across distinct filesystems
    fs::copy(src, dst)?;
    let mut perms = fs::metadata(dst)?.permissions();
    perms.set_mode(0o444);
    let _ = fs::set_permissions(dst, perms);
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
}
