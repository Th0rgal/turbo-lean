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
            if let Ok(meta) = entry.metadata() {
                if meta
                    .modified()
                    .ok()
                    .and_then(|m| SystemTime::now().duration_since(m).ok())
                    .map(|d| d.as_secs() > 600)
                    .unwrap_or(false)
                {
                    let _ = fs::remove_file(path);
                }
            }
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

/// Hardware-adaptive and parametrically configurable memory budget governor.
///
/// Supports arbitrary memory caps via `TURBO_LEAN_MAX_MEMORY_MB` (e.g. `256`, `512`, `2048`, `16384`)
/// or live OS telemetry (`/proc/meminfo` on Linux, `vm_stat` / `sysctl` on macOS).
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MemoryBudgetGovernor {
    pub budget_mb: u64,
}

impl Default for MemoryBudgetGovernor {
    fn default() -> Self {
        Self::detect()
    }
}

impl MemoryBudgetGovernor {
    /// Construct a `MemoryBudgetGovernor` with an explicit budget in MiB.
    pub fn new(budget_mb: u64) -> Self {
        Self {
            budget_mb: budget_mb.max(1),
        }
    }

    /// Construct a `MemoryBudgetGovernor` from `TURBO_LEAN_MAX_MEMORY_MB` if set,
    /// otherwise probing live available system memory.
    pub fn detect() -> Self {
        if let Some(env_mb) = std::env::var("TURBO_LEAN_MAX_MEMORY_MB")
            .ok()
            .and_then(|v| v.trim().parse::<u64>().ok())
            .filter(|&mb| mb > 0)
        {
            return Self::new(env_mb);
        }
        Self::new(probe_system_budget_mb())
    }

    /// True when `TURBO_LEAN_LOW_MEMORY == "1"` or `self.budget_mb <= 4096`.
    pub fn is_low_memory_mode(&self) -> bool {
        std::env::var("TURBO_LEAN_LOW_MEMORY").as_deref() == Ok("1") || self.budget_mb <= 4096
    }

    /// Clamp `self.budget_mb / est_worker_rss_mb.max(256)` into `1..=available_parallelism`.
    pub fn recommended_parallel_workers(&self, est_worker_rss_mb: u64) -> usize {
        let max_cpus = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .max(1);
        let per_worker = est_worker_rss_mb.max(256);
        let raw_workers = (self.budget_mb / per_worker) as usize;
        raw_workers.clamp(1, max_cpus)
    }

    /// Recommended `/dev/shm` quota in bytes for this memory budget:
    /// - `budget_mb <= 1024`: `0` bytes (100% out-of-core spill to disk SSD)
    /// - `budget_mb <= 4096`: `(budget_mb / 16) * 1024 * 1024` bytes
    /// - `budget_mb > 4096`: `512 * 1024 * 1024` bytes
    pub fn recommended_shm_quota_bytes(&self) -> u64 {
        if self.budget_mb <= 1024 {
            0
        } else if self.budget_mb <= 4096 {
            (self.budget_mb / 16).saturating_mul(1024 * 1024)
        } else {
            512 * 1024 * 1024
        }
    }

    /// Per-worker RSS recycling watermark in MiB (`(budget_mb * 3 / 4).max(512)`).
    pub fn worker_rss_limit_mb(&self) -> u64 {
        (self.budget_mb.saturating_mul(3) / 4).max(512)
    }
}

pub(crate) fn parse_proc_meminfo_budget_mb(meminfo: &str) -> Option<u64> {
    let mut mem_avail_kb: Option<u64> = None;
    let mut mem_total_kb: Option<u64> = None;
    for line in meminfo.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("MemAvailable:") {
            mem_avail_kb = rest
                .split_whitespace()
                .next()
                .and_then(|tok| tok.parse::<u64>().ok());
            if mem_avail_kb.is_some() {
                break;
            }
        } else if let Some(rest) = trimmed.strip_prefix("MemTotal:") {
            mem_total_kb = rest
                .split_whitespace()
                .next()
                .and_then(|tok| tok.parse::<u64>().ok());
        }
    }
    let kb = mem_avail_kb.or(mem_total_kb)?;
    let avail_mb = kb / 1024;
    Some((avail_mb.saturating_mul(3) / 4).max(1))
}

pub(crate) fn parse_macos_vm_stat_budget_mb(vm_stat_out: &str) -> Option<u64> {
    let mut page_size: u64 = 4096;
    let mut free_pages: u64 = 0;
    let mut found_any = false;

    for line in vm_stat_out.lines() {
        if let Some(idx) = line.find("page size of ") {
            let after = &line[idx + "page size of ".len()..];
            if let Some(ps) = after
                .split_whitespace()
                .next()
                .and_then(|tok| tok.parse::<u64>().ok())
                .filter(|&ps| ps > 0)
            {
                page_size = ps;
            }
        }
        for key in ["Pages free:", "Pages inactive:", "Pages speculative:"] {
            if let Some(rest) = line.trim().strip_prefix(key) {
                if let Some(pages) = rest
                    .trim()
                    .trim_end_matches('.')
                    .parse::<u64>()
                    .ok()
                {
                    free_pages = free_pages.saturating_add(pages);
                    found_any = true;
                }
            }
        }
    }

    if !found_any || free_pages == 0 {
        return None;
    }
    let avail_mb = free_pages.saturating_mul(page_size) / (1024 * 1024);
    Some((avail_mb.saturating_mul(7) / 10).max(1))
}

fn parse_cgroup_memory_limit_mb() -> Option<u64> {
    for path in [
        "/sys/fs/cgroup/memory.max",
        "/sys/fs/cgroup/memory/memory.limit_in_bytes",
    ] {
        if let Ok(raw) = fs::read_to_string(path) {
            let trimmed = raw.trim();
            if trimmed != "max" {
                if let Ok(bytes) = trimmed.parse::<u64>() {
                    if bytes > 0 && bytes < (1u64 << 50) {
                        let mb = bytes / (1024 * 1024);
                        if mb > 0 {
                            return Some((mb.saturating_mul(3) / 4).max(1));
                        }
                    }
                }
            }
        }
    }
    None
}

fn probe_system_budget_mb() -> u64 {
    let cgroup_mb = parse_cgroup_memory_limit_mb();
    if let Ok(meminfo) = fs::read_to_string("/proc/meminfo") {
        if let Some(budget_mb) = parse_proc_meminfo_budget_mb(&meminfo) {
            return match cgroup_mb {
                Some(cg) => budget_mb.min(cg),
                None => budget_mb,
            };
        }
    }
    if let Some(cg) = cgroup_mb {
        return cg;
    }

    #[cfg(target_os = "macos")]
    {
        if let Ok(out) = std::process::Command::new("vm_stat").output() {
            if out.status.success() {
                let text = String::from_utf8_lossy(&out.stdout);
                if let Some(budget_mb) = parse_macos_vm_stat_budget_mb(&text) {
                    return budget_mb;
                }
            }
        }
        if let Ok(out) = std::process::Command::new("sysctl")
            .args(["-n", "hw.memsize"])
            .output()
        {
            if out.status.success() {
                if let Ok(bytes) = String::from_utf8_lossy(&out.stdout).trim().parse::<u64>() {
                    let total_mb = bytes / (1024 * 1024);
                    if total_mb > 0 {
                        return (total_mb.saturating_mul(7) / 10).max(1);
                    }
                }
            }
        }
    }

    #[cfg(not(target_os = "macos"))]
    {
        if let Ok(out) = std::process::Command::new("vm_stat").output() {
            if out.status.success() {
                let text = String::from_utf8_lossy(&out.stdout);
                if let Some(budget_mb) = parse_macos_vm_stat_budget_mb(&text) {
                    return budget_mb;
                }
            }
        }
        if let Ok(out) = std::process::Command::new("sysctl")
            .args(["-n", "hw.memsize"])
            .output()
        {
            if out.status.success() {
                if let Ok(bytes) = String::from_utf8_lossy(&out.stdout).trim().parse::<u64>() {
                    let total_mb = bytes / (1024 * 1024);
                    if total_mb > 0 {
                        return (total_mb.saturating_mul(7) / 10).max(1);
                    }
                }
            }
        }
    }

    8192
}

/// Out-of-Core Disk Spill: when `shm_dir` total regular file bytes exceed `max_shm_bytes`,
/// instead of deleting the oldest `/dev/shm` files and losing warm cache entries, moves
/// (copies + atomically renames + unlinks from `/dev/shm`) the oldest cache files into
/// `disk_spill_dir` on disk until `shm_dir` usage is at or below `max_shm_bytes * 8 / 10`
/// (or `0` when `max_shm_bytes == 0`).
///
/// Returns `(spilled_files, spilled_bytes)`.
pub fn spill_shm_to_disk_dir(
    shm_dir: &Path,
    disk_spill_dir: &Path,
    max_shm_bytes: u64,
) -> std::io::Result<(usize, u64)> {
    if !shm_dir.exists() {
        return Ok((0, 0));
    }

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
        let fname_lossy = path
            .file_name()
            .map(|n| n.to_string_lossy())
            .unwrap_or_default();
        if fname_lossy.starts_with('.') && fname_lossy.ends_with(".tmp") {
            continue;
        }
        if let Ok(meta) = entry.metadata() {
            let sz = meta.len();
            let mtime = meta.modified().unwrap_or(UNIX_EPOCH);
            total_size = total_size.saturating_add(sz);
            files.push((mtime, path.to_path_buf(), sz));
        }
    }

    if total_size <= max_shm_bytes {
        return Ok((0, 0));
    }

    fs::create_dir_all(disk_spill_dir)?;
    let target_bytes = max_shm_bytes.saturating_mul(8) / 10;
    files.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));

    let mut spilled_files = 0usize;
    let mut spilled_bytes = 0u64;

    for (_mtime, path, sz) in files {
        if max_shm_bytes > 0 && total_size <= target_bytes {
            break;
        }
        let Some(file_name) = path.file_name() else {
            continue;
        };
        let dest_path = disk_spill_dir.join(file_name);
        let seq = SHM_TMP_SEQ.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos();
        let tmp_dest = disk_spill_dir.join(format!(
            ".{}.{}.{}.{}.tmp",
            file_name.to_string_lossy(),
            std::process::id(),
            seq,
            nanos
        ));

        let move_res = (|| -> std::io::Result<()> {
            fs::copy(&path, &tmp_dest)?;
            fs::rename(&tmp_dest, &dest_path)?;
            fs::remove_file(&path)?;
            Ok(())
        })();

        match move_res {
            Ok(()) => {
                total_size = total_size.saturating_sub(sz);
                spilled_files += 1;
                spilled_bytes = spilled_bytes.saturating_add(sz);
            }
            Err(e) => {
                let _ = fs::remove_file(&tmp_dest);
                debug_log_cache_err("spill_shm_to_disk_dir(move)", &e);
            }
        }
    }

    Ok((spilled_files, spilled_bytes))
}

/// Read a cache entry from `shm_path` in `/dev/shm` first, and if evicted under low RAM,
/// seamlessly read it from `disk_spill_dir.join(shm_path.file_name()?)` on disk.
pub fn read_shm_or_disk_spill(shm_path: &Path, disk_spill_dir: Option<&Path>) -> Option<Vec<u8>> {
    if let Ok(bytes) = fs::read(shm_path) {
        return Some(bytes);
    }
    let spill_dir = disk_spill_dir?;
    let file_name = shm_path.file_name()?;
    let spill_path = spill_dir.join(file_name);
    fs::read(spill_path).ok()
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

    #[test]
    fn test_memory_budget_governor_parametric_and_disk_spill_roundtrip() -> std::io::Result<()> {
        let max_cpus = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .max(1);

        // 1. Parametric MemoryBudgetGovernor across arbitrary MB budgets (256, 512, 2048, 16384)
        let gov_256 = MemoryBudgetGovernor::new(256);
        assert_eq!(gov_256.budget_mb, 256);
        assert!(gov_256.is_low_memory_mode());
        assert_eq!(gov_256.recommended_parallel_workers(512), 1);
        assert_eq!(gov_256.recommended_shm_quota_bytes(), 0);

        let gov_512 = MemoryBudgetGovernor::new(512);
        assert_eq!(gov_512.budget_mb, 512);
        assert!(gov_512.is_low_memory_mode());
        assert_eq!(gov_512.recommended_parallel_workers(512), 1);
        assert_eq!(gov_512.recommended_shm_quota_bytes(), 0);

        let gov_2048 = MemoryBudgetGovernor::new(2048);
        assert_eq!(gov_2048.budget_mb, 2048);
        assert!(gov_2048.is_low_memory_mode());
        assert_eq!(
            gov_2048.recommended_parallel_workers(512),
            4.min(max_cpus)
        );
        assert_eq!(
            gov_2048.recommended_shm_quota_bytes(),
            (2048 / 16) * 1024 * 1024
        );

        let gov_16384 = MemoryBudgetGovernor::new(16384);
        assert_eq!(gov_16384.budget_mb, 16384);
        assert_eq!(
            gov_16384.recommended_parallel_workers(512),
            32.min(max_cpus)
        );
        assert_eq!(gov_16384.recommended_shm_quota_bytes(), 512 * 1024 * 1024);

        // Verify Linux /proc/meminfo and macOS vm_stat parsers
        let sample_meminfo = "MemTotal:       16384000 kB\nMemFree:         2048000 kB\nMemAvailable:    8192000 kB\n";
        assert_eq!(parse_proc_meminfo_budget_mb(sample_meminfo), Some(6000));

        let sample_vm_stat = "Mach Virtual Memory Statistics: (page size of 16384 bytes)\nPages free:                               10000.\nPages active:                             50000.\nPages inactive:                           20000.\nPages speculative:                         2768.\n";
        // (10000 + 20000 + 2768) * 16384 = 32768 * 16384 = 512 MiB -> 70% = 358 MiB
        assert_eq!(parse_macos_vm_stat_budget_mb(sample_vm_stat), Some(358));

        // 2. Out-of-Core Disk Spill + read_shm_or_disk_spill roundtrip
        let base_dir = std::env::temp_dir().join(format!(
            "turbo_lean_shm_spill_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&base_dir);
        let shm_dir = base_dir.join("shm");
        let spill_dir = base_dir.join("disk_spill");
        fs::create_dir_all(&shm_dir)?;

        let f_old = shm_dir.join("entry_old.json");
        let f_mid = shm_dir.join("entry_mid.json");
        let f_new = shm_dir.join("entry_new.json");

        atomic_write_shm(&f_old, &[b'1'; 400])?;
        std::thread::sleep(Duration::from_millis(15));
        atomic_write_shm(&f_mid, &[b'2'; 400])?;
        std::thread::sleep(Duration::from_millis(15));
        atomic_write_shm(&f_new, &[b'3'; 400])?;

        // Partial spill: max_shm_bytes = 1000 -> target = 800 -> spills oldest file (400 bytes)
        let (spilled_count, spilled_bytes) = spill_shm_to_disk_dir(&shm_dir, &spill_dir, 1000)?;
        assert_eq!(spilled_count, 1);
        assert_eq!(spilled_bytes, 400);
        assert!(!f_old.exists(), "evicted file must be unlinked from shm_dir");
        assert!(
            spill_dir.join("entry_old.json").exists(),
            "evicted file must exist in disk_spill_dir"
        );
        assert!(f_mid.exists());
        assert!(f_new.exists());

        // Seamless lookup via read_shm_or_disk_spill for both spilled and resident entries
        assert_eq!(
            read_shm_or_disk_spill(&f_old, Some(&spill_dir)).as_deref(),
            Some(&[b'1'; 400][..])
        );
        assert_eq!(
            read_shm_or_disk_spill(&f_new, Some(&spill_dir)).as_deref(),
            Some(&[b'3'; 400][..])
        );

        // Full 100% spill when budget_mb <= 1024 (quota == 0 bytes)
        let (spilled_all, spilled_all_bytes) =
            spill_shm_to_disk_dir(&shm_dir, &spill_dir, gov_512.recommended_shm_quota_bytes())?;
        assert_eq!(spilled_all, 2);
        assert_eq!(spilled_all_bytes, 800);
        assert!(!f_mid.exists());
        assert!(!f_new.exists());
        assert_eq!(
            read_shm_or_disk_spill(&f_mid, Some(&spill_dir)).as_deref(),
            Some(&[b'2'; 400][..])
        );
        assert_eq!(
            read_shm_or_disk_spill(&f_new, Some(&spill_dir)).as_deref(),
            Some(&[b'3'; 400][..])
        );

        let _ = fs::remove_dir_all(&base_dir);
        Ok(())
    }
}

