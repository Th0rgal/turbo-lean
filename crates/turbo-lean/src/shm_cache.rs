//! Unified `/dev/shm` Cache Management, Atomic Staging Writes, and LRU Quota Enforcement.
//!
//! Provides schema versioning (`SHM_CACHE_SCHEMA_VERSION`), race-free atomic write-then-rename
//! into `/dev/shm` (`atomic_write_shm`), opt-in diagnostic logging (`debug_log_cache_err`), and
//! bounded LRU quota eviction (`enforce_shm_quota_lru`).

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

/// Schema version for `/dev/shm` project stat summaries, split caches, and daemon state files.
pub const SHM_CACHE_SCHEMA_VERSION: u32 = 1;

/// Default `/dev/shm` cache quota in MiB when `TURBO_LEAN_MAX_SHM_MB` is unset.
pub const DEFAULT_MAX_SHM_MB: u64 = 512;

static SHM_TMP_SEQ: AtomicU64 = AtomicU64::new(1);

/// Emit a diagnostic warning to `stderr` when `TURBO_LEAN_DEBUG=1` is set in the environment.
pub fn debug_log_cache_err(context: &str, err: &dyn std::fmt::Display) {
    if std::env::var("TURBO_LEAN_DEBUG").as_deref() == Ok("1") {
        eprintln!("[turbo-lean:shm-debug] {}: {}", context, err);
    }
}

/// Resolve the configured maximum `/dev/shm` cache size in bytes from `TURBO_LEAN_MAX_SHM_MB`
/// (defaults to `512` MiB).
pub fn default_max_shm_bytes() -> u64 {
    std::env::var("TURBO_LEAN_MAX_SHM_MB")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .filter(|&mb| mb > 0)
        .unwrap_or(DEFAULT_MAX_SHM_MB)
        .saturating_mul(1024 * 1024)
}

/// Atomically write `bytes` to `target` by staging into a process+sequence-unique temporary file
/// in `target.parent()` and invoking `fs::rename` over `target`.
pub fn atomic_write_shm(target: &Path, bytes: &[u8]) -> std::io::Result<()> {
    let parent = target.parent().unwrap_or_else(|| Path::new("."));
    if !parent.as_os_str().is_empty() && !parent.exists() {
        fs::create_dir_all(parent)?;
    }
    let file_name = target
        .file_name()
        .map(|n| n.to_string_lossy())
        .unwrap_or_else(|| std::borrow::Cow::Borrowed("shm_entry"));
    let seq = SHM_TMP_SEQ.fetch_add(1, Ordering::Relaxed);
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let tmp_path = parent.join(format!(
        ".{}.{}.{}.{}.tmp",
        file_name,
        std::process::id(),
        seq,
        nanos
    ));

    let write_res = (|| -> std::io::Result<()> {
        let mut f = fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&tmp_path)?;
        f.write_all(bytes)?;
        Ok(())
    })();

    if let Err(e) = write_res {
        let _ = fs::remove_file(&tmp_path);
        debug_log_cache_err("atomic_write_shm(write)", &e);
        return Err(e);
    }

    if let Err(e) = fs::rename(&tmp_path, target) {
        let _ = fs::remove_file(&tmp_path);
        debug_log_cache_err("atomic_write_shm(rename)", &e);
        return Err(e);
    }

    Ok(())
}

/// Enforce an upper bound on total regular file bytes inside `shm_dir`.
///
/// If `max_bytes == 0`, uses [`default_max_shm_bytes`] (`TURBO_LEAN_MAX_SHM_MB`, default `512` MiB).
/// When `total_size > max_bytes`, regular cache files (excluding active `.lock` files) are sorted
/// by modification time ascending (oldest first) and removed until `total_size <= max_bytes * 8 / 10`.
/// Returns `(evicted_files, freed_bytes)`.
pub fn enforce_shm_quota_lru(shm_dir: &Path, max_bytes: u64) -> std::io::Result<(usize, u64)> {
    if !shm_dir.exists() {
        return Ok((0, 0));
    }
    let effective_max = if max_bytes == 0 {
        default_max_shm_bytes()
    } else {
        max_bytes
    };

    let mut files: Vec<(SystemTime, PathBuf, u64)> = Vec::new();
    let mut total_size: u64 = 0;

    for entry in walkdir::WalkDir::new(shm_dir).into_iter().flatten() {
        if !entry.file_type().is_file() {
            continue;
        }
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) == Some("lock") {
            continue;
        }
        if let Ok(meta) = entry.metadata() {
            let sz = meta.len();
            let mtime = meta.modified().unwrap_or(UNIX_EPOCH);
            total_size = total_size.saturating_add(sz);
            files.push((mtime, path.to_path_buf(), sz));
        }
    }

    if total_size <= effective_max {
        return Ok((0, 0));
    }

    let target_bytes = effective_max.saturating_mul(8) / 10;
    files.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));

    let mut evicted_files = 0usize;
    let mut freed_bytes = 0u64;

    for (_mtime, path, sz) in files {
        if total_size <= target_bytes {
            break;
        }
        match fs::remove_file(&path) {
            Ok(()) => {
                total_size = total_size.saturating_sub(sz);
                evicted_files += 1;
                freed_bytes = freed_bytes.saturating_add(sz);
            }
            Err(e) => {
                debug_log_cache_err("enforce_shm_quota_lru(remove_file)", &e);
            }
        }
    }

    Ok((evicted_files, freed_bytes))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_atomic_write_shm_creates_and_overwrites_cleanly() -> std::io::Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_lean_shm_atomic_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let target = dir.join("nested").join("entry_v1.json");

        atomic_write_shm(&target, b"{\"schema_version\":1,\"v\":10}")?;
        assert_eq!(fs::read(&target)?, b"{\"schema_version\":1,\"v\":10}");

        atomic_write_shm(&target, b"{\"schema_version\":1,\"v\":20}")?;
        assert_eq!(fs::read(&target)?, b"{\"schema_version\":1,\"v\":20}");

        // Verify no leftover .tmp files remain
        let remaining: Vec<_> = fs::read_dir(target.parent().unwrap())?
            .flatten()
            .map(|e| e.file_name().to_string_lossy().to_string())
            .collect();
        assert_eq!(remaining, vec!["entry_v1.json".to_string()]);

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_enforce_shm_quota_lru_evicts_oldest_first() -> std::io::Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_lean_shm_lru_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir)?;

        let f_old = dir.join("01_oldest.bin");
        let f_mid = dir.join("02_middle.bin");
        let f_new = dir.join("03_newest.bin");
        let f_lock = dir.join("active.lock");

        atomic_write_shm(&f_old, &[b'a'; 400])?;
        std::thread::sleep(Duration::from_millis(15));
        atomic_write_shm(&f_mid, &[b'b'; 400])?;
        std::thread::sleep(Duration::from_millis(15));
        atomic_write_shm(&f_new, &[b'c'; 400])?;
        atomic_write_shm(&f_lock, b"lock")?;

        // Total regular cache size = 1200 bytes.
        // With max_bytes = 1000, target_bytes = 800 (80% of 1000).
        // Evicting `01_oldest.bin` (400 bytes) brings total_size to 800 <= 800.
        let (evicted, freed) = enforce_shm_quota_lru(&dir, 1000)?;
        assert_eq!(evicted, 1);
        assert_eq!(freed, 400);
        assert!(!f_old.exists(), "Oldest file must be evicted first");
        assert!(f_mid.exists(), "Middle file should remain when <= 80% quota");
        assert!(f_new.exists(), "Newest file must remain");
        assert!(f_lock.exists(), "Lock files must never be evicted");

        // Calling again when already <= max_bytes is a no-op
        let (evicted2, freed2) = enforce_shm_quota_lru(&dir, 1000)?;
        assert_eq!(evicted2, 0);
        assert_eq!(freed2, 0);

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }
}
