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

        fs::create_dir_all(root.join("blobs"))?;
        fs::create_dir_all(root.join("staging"))?;
        fs::create_dir_all(root.join("locks"))?;

        let db_path = root.join("state.db");
        let conn = Connection::open(&db_path)
            .with_context(|| format!("Failed to open SQLite DB at {}", db_path.display()))?;

        conn.execute_batch(
            "
            PRAGMA journal_mode = WAL;
            PRAGMA synchronous = NORMAL;
            PRAGMA busy_timeout = 5000;
            PRAGMA foreign_keys = ON;

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
                updated_at           INTEGER NOT NULL
            );

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
            ",
        )?;

        Ok(Self { root, conn })
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
            let _ = self.conn.execute(
                "UPDATE inflight_leases SET waiter_count = waiter_count + 1 WHERE action_key = ?1",
                params![action_key],
            );
            let _ = self.conn.execute(
                "UPDATE meta_counters SET val = val + 1 WHERE name = 'coalesced_waits'",
                [],
            );

            // Block in kernel until the leader finishes (or crashes, which auto-releases flock)
            let wait_rc = unsafe { libc::flock(fd, libc::LOCK_EX) };
            if wait_rc != 0 {
                anyhow::bail!("flock wait failed for action {}", action_key);
            }
        }

        // Now we hold LOCK_EX! Re-check if the prior holder completed the action
        if let Some(outputs) = self.get_cached_action(action_key, trust_domain)? {
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

        if !dest.exists() {
            if let Some(parent) = dest.parent() {
                fs::create_dir_all(parent)?;
            }
            let staging_path = self.root.join("staging").join(format!(
                "{}.{}.tmp",
                hash,
                std::process::id()
            ));
            {
                let mut f = File::create(&staging_path)?;
                f.write_all(bytes)?;
                f.sync_all()?;
            }
            // Enforce read-only 0444 permissions before atomic rename so no hardlink consumer can mutate in-place
            let mut perms = fs::metadata(&staging_path)?.permissions();
            perms.set_mode(0o444);
            fs::set_permissions(&staging_path, perms)?;
            fs::rename(&staging_path, &dest)?;
        }

        let meta = fs::metadata(&dest)?;
        let inode = meta.ino() as i64;
        let size = meta.len() as i64;
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

        let tx = self.conn.transaction()?;
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

        for o in outputs {
            tx.execute(
                "INSERT INTO action_outputs (action_key, rel_path, blob_hash) VALUES (?1, ?2, ?3)",
                params![lease.action_key, o.rel_path, o.blob_hash],
            )?;
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
        let tx = self.conn.transaction()?;
        tx.execute(
            "INSERT INTO worktrees (worktree_id, root_path, project_name, last_seen)
             VALUES (?1, ?2, ?3, ?4)
             ON CONFLICT(worktree_id) DO UPDATE SET last_seen = excluded.last_seen",
            params![wt_id, root_str, project_name, now],
        )?;

        let mut linked = 0usize;
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
            if let Some(parent) = dst.parent() {
                fs::create_dir_all(parent)?;
            }

            // Always unlink destination first so we never truncate/mutate a shared inode in place!
            if dst.exists() {
                let _ = fs::remove_file(&dst);
            }

            let mode = try_reflink_or_hardlink(&src, &dst)?;
            tx.execute(
                "INSERT INTO worktree_installations (worktree_id, rel_path, blob_hash, link_mode)
                 VALUES (?1, ?2, ?3, ?4)
                 ON CONFLICT(worktree_id, rel_path) DO UPDATE SET
                    blob_hash = excluded.blob_hash,
                    link_mode = excluded.link_mode",
                params![wt_id, out.rel_path, out.blob_hash, mode],
            )?;
            linked += 1;
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
            reclaimable_bytes,
            worktree_retained_bytes,
            pinned_bytes,
            total_logical_bytes,
        })
    }

    /// Smart multi-project Garbage Collector using Cost-Aware GDSF (Greedy-Dual-Size-Frequency):
    /// `KeepScore(Action) = last_accessed + alpha * (duration_ms / max(total_size_bytes, 1))`
    /// Also detects deleted/stale worktrees and removes their installations so inodes become reclaimable.
    pub fn run_gc(
        &mut self,
        max_reclaimable_bytes: u64,
        prune_worktrees_older_than_secs: i64,
        keep_pinned: bool,
    ) -> Result<GcReport> {
        let now = now_unix();
        let mut pruned_worktrees = 0usize;

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
                freed_reclaimable_bytes: 0,
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
        let mut freed_bytes = 0u64;
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
            freed_reclaimable_bytes: freed_bytes,
            remaining_reclaimable_bytes: current_reclaimable,
        })
    }
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
}

