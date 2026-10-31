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

/// Resolve the per-user RAM staging directory (`/dev/shm/turbo-lean-staging-<uid>`, falling back
/// to `$TMPDIR/turbo-lean-staging-<uid>`), honoring `TURBO_LEAN_STAGING_DIR` when set.
pub fn staging_shm_dir() -> PathBuf {
    if let Ok(override_dir) = std::env::var("TURBO_LEAN_STAGING_DIR") {
        let t = override_dir.trim();
        if !t.is_empty() {
            return PathBuf::from(t);
        }
    }
    #[cfg(unix)]
    let uid = unsafe { libc::geteuid() };
    #[cfg(not(unix))]
    let uid = 0u32;
    let base = if Path::new("/dev/shm").is_dir() {
        PathBuf::from("/dev/shm")
    } else {
        std::env::temp_dir()
    };
    base.join(format!("turbo-lean-staging-{}", uid))
}

/// Persistent per-user cache root for the store.
pub fn cache_root() -> PathBuf {
    std::env::var("TURBO_LEAN_HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(std::env::var("HOME").unwrap_or_else(|_| "/tmp".to_string()))
                .join(".cache/turbo-lean")
        })
}

/// Package publication protocol (independent of HOME/TURBO_LEAN_HOME): every new reader
/// and publisher first locks the existing package directory, then the legacy
/// `.lake/build/.turbo_publish.lock`. Default users create that legacy lock as before,
/// preserving exclusion with old binaries. Opted-out users open it read-only WITHOUT
/// O_CREAT. When absent, readers must validate artifact and legacy-lock snapshots:
/// old publishers can create the legacy file without taking the directory lock.
/// Lock files must never be unlinked.
pub fn acquire_publish_flock(
    pkg_root: &Path,
    exclusive: bool,
) -> std::io::Result<PublishFlockGuard> {
    let directory = flock_file(fs::File::open(pkg_root)?, exclusive, false)?;
    let lock_path = pkg_root.join(".lake/build/.turbo_publish.lock");
    let legacy = if crate::lake_build::worktree_auto_link_disabled(pkg_root) {
        match fs::File::open(&lock_path) {
            Ok(file) => flock_file(file, exclusive, false)?,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
            Err(e) => return Err(e),
        }
    } else {
        acquire_flock(&lock_path, exclusive, false)?
    };
    Ok(PublishFlockGuard {
        _legacy: legacy,
        _directory: directory,
        lock_path,
    })
}

/// Release the legacy lock before the package directory lock (field drop order).
pub struct PublishFlockGuard {
    _legacy: Option<FlockGuard>,
    _directory: Option<FlockGuard>,
    lock_path: PathBuf,
}

#[derive(PartialEq, Eq)]
struct ArtifactStamp {
    size: u64,
    modified: SystemTime,
    #[cfg(unix)]
    identity: (u64, u64, i64, i64),
}

impl ArtifactStamp {
    fn from_metadata(meta: fs::Metadata) -> std::io::Result<Self> {
        Ok(Self {
            size: meta.len(),
            modified: meta.modified()?,
            #[cfg(unix)]
            identity: {
                use std::os::unix::fs::MetadataExt;
                (meta.dev(), meta.ino(), meta.ctime(), meta.ctime_nsec())
            },
        })
    }

    fn at(path: &Path) -> std::io::Result<Option<Self>> {
        match fs::metadata(path) {
            Ok(meta) => Self::from_metadata(meta).map(Some),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(e),
        }
    }
}

impl PublishFlockGuard {
    /// Snapshot all candidates (including missing companions) before any read, then
    /// discard the entire result if an old publisher changed the set or lock inode.
    pub fn read_consistent<T>(
        &self,
        paths: &[PathBuf],
        read: impl FnOnce() -> anyhow::Result<T>,
    ) -> anyhow::Result<T> {
        let legacy = self
            ._legacy
            .as_ref()
            .map(|g| ArtifactStamp::from_metadata(g.0.metadata()?))
            .transpose()?;
        let stable_lock = || -> anyhow::Result<()> {
            anyhow::ensure!(
                ArtifactStamp::at(&self.lock_path)? == legacy,
                "Publication lock appeared or changed during artifact read: {}; retry the build",
                self.lock_path.display()
            );
            Ok(())
        };
        stable_lock()?;
        let before = paths
            .iter()
            .map(|p| ArtifactStamp::at(p))
            .collect::<std::io::Result<Vec<_>>>()?;
        let result = read();
        for (path, stamp) in paths.iter().zip(before) {
            anyhow::ensure!(
                ArtifactStamp::at(path)? == stamp,
                "Artifact changed during publication read: {}; retry the build",
                path.display()
            );
        }
        stable_lock()?;
        result
    }
}

/// RAII advisory `flock` guard that releases `LOCK_UN` on drop.
pub struct FlockGuard(pub fs::File);

impl Drop for FlockGuard {
    fn drop(&mut self) {
        #[cfg(unix)]
        unsafe {
            use std::os::unix::io::AsRawFd;
            let _ = libc::flock(self.0.as_raw_fd(), libc::LOCK_UN);
        }
    }
}

/// Acquire an advisory `flock` (`exclusive` => `LOCK_EX`, else `LOCK_SH`; `nonblocking` => `| LOCK_NB`).
/// Returns `Ok(None)` when `nonblocking` is true and another holder currently owns a conflicting lock.
pub fn acquire_flock(
    lock_path: &Path,
    exclusive: bool,
    nonblocking: bool,
) -> std::io::Result<Option<FlockGuard>> {
    if let Some(parent) = lock_path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)?;
        }
    }
    let f = fs::OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        .truncate(false)
        .open(lock_path)?;
    flock_file(f, exclusive, nonblocking)
}

fn flock_file(
    f: fs::File,
    exclusive: bool,
    nonblocking: bool,
) -> std::io::Result<Option<FlockGuard>> {
    #[cfg(unix)]
    {
        use std::os::unix::io::AsRawFd;
        let mut op = if exclusive {
            libc::LOCK_EX
        } else {
            libc::LOCK_SH
        };
        if nonblocking {
            op |= libc::LOCK_NB;
        }
        if unsafe { libc::flock(f.as_raw_fd(), op) } != 0 {
            let err = std::io::Error::last_os_error();
            if nonblocking && err.kind() == std::io::ErrorKind::WouldBlock {
                return Ok(None);
            }
            return Err(err);
        }
    }
    #[cfg(not(unix))]
    let _ = (exclusive, nonblocking);
    Ok(Some(FlockGuard(f)))
}

/// Execute `f` while holding an advisory `flock` (`LOCK_EX` or `LOCK_EX | LOCK_NB`) on `lock_path`.
/// Returns `None` only when `nonblocking` is true and the lock is currently held by another process.
pub fn with_shm_flock<F, R>(lock_path: &Path, nonblocking: bool, f: F) -> Option<R>
where
    F: FnOnce() -> R,
{
    let _guard = match acquire_flock(lock_path, true, nonblocking) {
        Ok(Some(g)) => Some(g),
        Ok(None) => return None,
        Err(_) => None,
    };
    Some(f())
}

/// Atomically load, mutate, and persist a JSON state file guarded by `lock_path` + `atomic_write_shm`.
pub fn update_locked_shm_json<T, F, R>(json_path: &Path, lock_path: &Path, pretty: bool, f: F) -> R
where
    T: serde::de::DeserializeOwned + serde::Serialize + Default,
    F: FnOnce(&mut T) -> R,
{
    with_shm_flock(lock_path, false, || {
        let mut state: T = fs::read(json_path)
            .ok()
            .and_then(|b| serde_json::from_slice(&b).ok())
            .unwrap_or_default();
        let out = f(&mut state);
        let encoded = if pretty {
            serde_json::to_vec_pretty(&state)
        } else {
            serde_json::to_vec(&state)
        };
        if let Ok(bytes) = encoded {
            let _ = atomic_write_shm(json_path, &bytes);
        }
        out
    })
    .expect("blocking with_shm_flock always returns Some")
}

/// Strip `# ...` comments from a TOML line while respecting single- and double-quoted literals.
pub fn strip_toml_comment(line: &str) -> &str {
    let bytes = line.as_bytes();
    let (mut in_double, mut in_single, mut i) = (false, false, 0);
    while i < bytes.len() {
        if in_double {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_double = false;
            }
        } else if in_single {
            if bytes[i] == b'\'' {
                in_single = false;
            }
        } else if bytes[i] == b'"' {
            in_double = true;
        } else if bytes[i] == b'\'' {
            in_single = true;
        } else if bytes[i] == b'#' {
            return &line[..i];
        }
        i += 1;
    }
    line
}

/// Unquote a TOML/JSON scalar (`"..."` or `'...'`), falling back to trimmed text.
pub fn unquote_toml_scalar(s: &str) -> String {
    let t = s.trim();
    if (t.starts_with('"') && t.ends_with('"')) || (t.starts_with('\'') && t.ends_with('\'')) {
        t[1..t.len().saturating_sub(1)].to_string()
    } else {
        t.to_string()
    }
}

/// Parse a boolean-like scalar (`1`/`true`/`yes`/`on` vs `0`/`off`/`false`/`no`/`none`/`disable`/`disabled`).
pub fn parse_relaxed_bool(s: &str) -> Option<bool> {
    match unquote_toml_scalar(s).to_ascii_lowercase().as_str() {
        "1" | "true" | "yes" | "on" => Some(true),
        "0" | "off" | "false" | "no" | "none" | "disable" | "disabled" => Some(false),
        _ => None,
    }
}

/// Parse a relaxed TOML/JSON string array (`["a", "b"]`).
pub fn parse_relaxed_toml_string_array(s: &str) -> Vec<String> {
    let t = s.trim();
    if let Ok(v) = serde_json::from_str::<Vec<String>>(t) {
        return v;
    }
    t.strip_prefix('[')
        .and_then(|x| x.strip_suffix(']'))
        .unwrap_or(t)
        .split(',')
        .map(unquote_toml_scalar)
        .filter(|x| !x.is_empty())
        .collect()
}

/// Visit `(section_header, key, raw_value)` entries across a relaxed TOML document, joining
/// multi-line `[...]` array assignments and stripping `#` comments outside quotes.
pub fn for_each_toml_entry<F>(text: &str, mut visit: F)
where
    F: FnMut(&str, &str, &str),
{
    let mut joined: Vec<String> = Vec::new();
    let mut pending: Option<String> = None;
    for raw_line in text.lines() {
        let clean = strip_toml_comment(raw_line).trim();
        if clean.is_empty() {
            continue;
        }
        if let Some(mut acc) = pending.take() {
            acc.push(' ');
            acc.push_str(clean);
            if clean.ends_with(']') {
                joined.push(acc);
            } else {
                pending = Some(acc);
            }
        } else if clean.contains('=') && clean.contains('[') && !clean.ends_with(']') {
            pending = Some(clean.to_string());
        } else {
            joined.push(clean.to_string());
        }
    }
    if let Some(acc) = pending {
        joined.push(acc);
    }
    let mut section = String::new();
    for line in joined {
        let l = line.trim();
        if l.starts_with('[') && l.ends_with(']') {
            section = l.to_string();
            visit(&section, "", "");
        } else if let Some((k, v)) = l.split_once('=') {
            visit(&section, k.trim(), v.trim());
        }
    }
}

/// Upsert `[section_name]` in a TOML document with `kv_lines`, preserving all unrelated sections/comments.
pub fn upsert_toml_section(
    existing: &str,
    section_name: &str,
    kv_lines: &[(&str, String)],
) -> String {
    let header = format!("[{}]", section_name);
    let (mut out, mut in_sec, mut replaced) = (Vec::new(), false, false);
    let emit = |dst: &mut Vec<String>| {
        dst.push(header.clone());
        for (k, v) in kv_lines {
            dst.push(format!("{} = {}", k, v));
        }
    };
    for raw_line in existing.lines() {
        let stripped = strip_toml_comment(raw_line).trim();
        if stripped.starts_with('[') && stripped.ends_with(']') {
            in_sec = false;
            if stripped == header {
                if !replaced {
                    emit(&mut out);
                    replaced = true;
                }
                in_sec = true;
                continue;
            }
        }
        if !in_sec {
            out.push(raw_line.to_string());
        }
    }
    if !replaced {
        if out.last().map(|s| !s.is_empty()).unwrap_or(false) {
            out.push(String::new());
        }
        emit(&mut out);
    }
    let mut res = out.join("\n");
    if !res.ends_with('\n') {
        res.push('\n');
    }
    res
}

/// Resolve the user-level `turbo-lean` TOML config path (`TURBO_LEAN_USER_CONFIG`, `XDG_CONFIG_HOME`, or `~/.config/turbo-lean/config.toml`).
pub fn user_config_toml_path() -> PathBuf {
    for (k, suffix) in [
        ("TURBO_LEAN_USER_CONFIG", ""),
        ("XDG_CONFIG_HOME", "turbo-lean/config.toml"),
    ] {
        if let Ok(v) = std::env::var(k) {
            let t = v.trim();
            if !t.is_empty() {
                let p = PathBuf::from(t);
                return if suffix.is_empty() { p } else { p.join(suffix) };
            }
        }
    }
    let home = std::env::var("HOME").unwrap_or_else(|_| "/tmp".to_string());
    PathBuf::from(home).join(".config/turbo-lean/config.toml")
}

/// Locate the nearest `turbo-lean.toml` or `.turbo-lean.toml` walking upward from `start_dir` (or CWD).
pub fn find_nearest_project_toml(start_dir: Option<&Path>) -> Option<PathBuf> {
    let dir = start_dir
        .map(|p| {
            if p.is_dir() {
                p.to_path_buf()
            } else {
                p.parent().unwrap_or_else(|| Path::new(".")).to_path_buf()
            }
        })
        .or_else(|| std::env::current_dir().ok())?;
    let canon = dir.canonicalize().unwrap_or(dir);
    for anc in canon.ancestors() {
        for name in ["turbo-lean.toml", ".turbo-lean.toml"] {
            let cand = anc.join(name);
            if cand.is_file() {
                return Some(cand);
            }
        }
    }
    None
}

/// Shared config loader checking an explicit path override, an inline-or-path env var, and
/// ancestor/project relative files (`turbo-lean.toml`, `.turbo-lean.toml`, etc.).
pub fn load_project_or_env_config<T, F>(
    explicit_path: Option<&Path>,
    env_key: &str,
    start_dir: Option<&Path>,
    extra_project_rels: &[&str],
    walk_ancestors: bool,
    parse: F,
) -> Option<T>
where
    F: Fn(&str) -> Option<T>,
{
    if let Some(p) = explicit_path {
        if let Ok(txt) = fs::read_to_string(p) {
            if let Some(cfg) = parse(&txt) {
                return Some(cfg);
            }
        }
    }
    if let Ok(ev) = std::env::var(env_key) {
        let t = ev.trim();
        if !t.is_empty() {
            if let Some(cfg) =
                parse(t).or_else(|| fs::read_to_string(t).ok().and_then(|s| parse(&s)))
            {
                return Some(cfg);
            }
        }
    }
    let dir = start_dir.map(|p| {
        if p.is_dir() {
            p.to_path_buf()
        } else {
            p.parent().unwrap_or_else(|| Path::new(".")).to_path_buf()
        }
    })?;
    for rel in extra_project_rels {
        if let Some(cfg) = fs::read_to_string(dir.join(rel))
            .ok()
            .and_then(|s| parse(&s))
        {
            return Some(cfg);
        }
    }
    if walk_ancestors {
        let canon = dir.canonicalize().unwrap_or(dir);
        for anc in canon.ancestors() {
            for rel in ["turbo-lean.toml", ".turbo-lean.toml"] {
                if let Some(cfg) = fs::read_to_string(anc.join(rel))
                    .ok()
                    .and_then(|s| parse(&s))
                {
                    return Some(cfg);
                }
            }
        }
    }
    None
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

fn stage_unique_tmp_path(target: &Path) -> std::io::Result<PathBuf> {
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
    Ok(parent.join(format!(
        ".{}.{}.{}.{}.tmp",
        file_name,
        std::process::id(),
        seq,
        nanos
    )))
}

/// Atomically write `bytes` to `target` by staging into a process+sequence-unique temporary file
/// in `target.parent()` and invoking `fs::rename` over `target`.
pub fn atomic_write_shm(target: &Path, bytes: &[u8]) -> std::io::Result<()> {
    let tmp_path = stage_unique_tmp_path(target)?;
    let write_res = fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&tmp_path)
        .and_then(|mut f| f.write_all(bytes));
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

fn scan_evictable_shm_files(
    shm_dir: &Path,
    reap_stale_locks: bool,
) -> (u64, Vec<(SystemTime, PathBuf, u64)>) {
    let mut files = Vec::new();
    let mut total_size = 0u64;
    for entry in walkdir::WalkDir::new(shm_dir).into_iter().flatten() {
        if !entry.file_type().is_file() {
            continue;
        }
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) == Some("lock") {
            if reap_stale_locks
                && entry
                    .metadata()
                    .ok()
                    .and_then(|m| m.modified().ok())
                    .and_then(|m| SystemTime::now().duration_since(m).ok())
                    .is_some_and(|d| d.as_secs() > 600)
            {
                let _ = fs::remove_file(path);
            }
            continue;
        }
        let fname = path
            .file_name()
            .map(|n| n.to_string_lossy())
            .unwrap_or_default();
        if (fname.starts_with('.') && fname.ends_with(".tmp"))
            || fname == "zygote_daemon.json"
            || fname == "zygote_lru_registry.json"
            || path.to_string_lossy().contains("zygote_daemon_cas_")
        {
            continue;
        }
        if let Ok(meta) = entry.metadata() {
            let sz = meta.len();
            total_size = total_size.saturating_add(sz);
            files.push((
                meta.modified().unwrap_or(UNIX_EPOCH),
                path.to_path_buf(),
                sz,
            ));
        }
    }
    (total_size, files)
}

/// Enforce an upper bound on total regular file bytes inside `shm_dir`.
pub fn enforce_shm_quota_lru(shm_dir: &Path, max_bytes: u64) -> std::io::Result<(usize, u64)> {
    if !shm_dir.exists() {
        return Ok((0, 0));
    }
    let effective_max = if max_bytes == 0 {
        default_max_shm_bytes()
    } else {
        max_bytes
    };
    let (mut total_size, mut files) = scan_evictable_shm_files(shm_dir, true);
    if total_size <= effective_max {
        return Ok((0, 0));
    }
    let target_bytes = effective_max.saturating_mul(8) / 10;
    files.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    let (mut evicted_files, mut freed_bytes) = (0usize, 0u64);
    for (_, path, sz) in files {
        if total_size <= target_bytes {
            break;
        }
        match fs::remove_file(&path) {
            Ok(()) => {
                total_size = total_size.saturating_sub(sz);
                evicted_files += 1;
                freed_bytes = freed_bytes.saturating_add(sz);
            }
            Err(e) => debug_log_cache_err("enforce_shm_quota_lru(remove_file)", &e),
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
                if let Some(pages) = rest.trim().trim_end_matches('.').parse::<u64>().ok() {
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

    8192
}

/// Out-of-Core Disk Spill: moves oldest `/dev/shm` cache entries into `disk_spill_dir` until
/// `shm_dir` usage is at or below `max_shm_bytes * 8 / 10` (or `0` when `max_shm_bytes == 0`).
pub fn spill_shm_to_disk_dir(
    shm_dir: &Path,
    disk_spill_dir: &Path,
    max_shm_bytes: u64,
) -> std::io::Result<(usize, u64)> {
    if !shm_dir.exists() {
        return Ok((0, 0));
    }
    let (mut total_size, mut files) = scan_evictable_shm_files(shm_dir, false);
    if total_size <= max_shm_bytes {
        return Ok((0, 0));
    }
    fs::create_dir_all(disk_spill_dir)?;
    let target_bytes = max_shm_bytes.saturating_mul(8) / 10;
    files.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    let (mut spilled_files, mut spilled_bytes) = (0usize, 0u64);
    for (_, path, sz) in files {
        if max_shm_bytes > 0 && total_size <= target_bytes {
            break;
        }
        let Some(file_name) = path.file_name() else {
            continue;
        };
        let dest_path = disk_spill_dir.join(file_name);
        let tmp_dest = stage_unique_tmp_path(&dest_path)?;
        let move_res = fs::copy(&path, &tmp_dest)
            .and_then(|_| fs::rename(&tmp_dest, &dest_path))
            .and_then(|_| fs::remove_file(&path));
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
    #[cfg(unix)]
    #[test]
    fn test_publication_snapshot_rejects_changed_and_new_artifacts() -> anyhow::Result<()> {
        let root = std::env::temp_dir().join(format!(
            "turbo_snapshot_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        fs::create_dir_all(&root)?;
        fs::write(
            root.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        let paths = [root.join("artifact"), root.join("missing")];
        let guard = super::acquire_publish_flock(&root, false)?;
        for change in ["inode", "mtime", "size", "presence", "lock"] {
            fs::write(&paths[0], b"old")?;
            let old_time = fs::metadata(&paths[0])?.modified()?;
            let err = guard
                .read_consistent(&paths, || {
                    match change {
                        "inode" => {
                            let tmp = root.join("replacement");
                            fs::write(&tmp, b"new")?;
                            fs::File::options()
                                .write(true)
                                .open(&tmp)?
                                .set_modified(old_time)?;
                            fs::rename(tmp, &paths[0])?;
                        }
                        "mtime" => fs::File::options()
                            .write(true)
                            .open(&paths[0])?
                            .set_modified(old_time + std::time::Duration::from_secs(2))?,
                        "size" => fs::write(&paths[0], b"longer")?,
                        "presence" => fs::write(&paths[1], b"appeared")?,
                        _ => {
                            fs::create_dir_all(root.join(".lake/build"))?;
                            fs::write(root.join(".lake/build/.turbo_publish.lock"), b"")?;
                        }
                    }
                    Ok("discard me")
                })
                .unwrap_err()
                .to_string();
            assert!(
                err.contains("changed during") || err.contains("appeared or changed"),
                "{change}: {err}"
            );
            let _ = fs::remove_file(&paths[1]);
        }
        drop(guard);
        fs::remove_dir_all(root)?;
        Ok(())
    }

    #[test]
    fn test_publication_lock_preserves_opted_out_tree_and_locks_aliases() -> anyhow::Result<()> {
        use crate::worktree_test_support::snapshot;
        use std::os::unix::fs::MetadataExt;
        let root = std::env::temp_dir().join(format!(
            "turbo_pub_lock_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let project = root.join("project");
        std::fs::create_dir_all(&project)?;
        std::fs::write(
            project.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        std::os::unix::fs::symlink(&project, root.join("alias"))?;
        for legacy in [false, true] {
            let reader = super::acquire_publish_flock(&project, false)?;
            let alias_reader = super::acquire_publish_flock(&root.join("alias"), false)?;
            assert_eq!(
                reader._directory.as_ref().unwrap().0.metadata()?.ino(),
                alias_reader
                    ._directory
                    .as_ref()
                    .unwrap()
                    .0
                    .metadata()?
                    .ino()
            );
            assert_eq!(reader._legacy.is_some(), legacy);
            assert!(super::flock_file(std::fs::File::open(&project)?, true, true)?.is_none());
            drop((reader, alias_reader));
            if !legacy {
                assert!(!project.join(".lake").exists());
                std::fs::create_dir_all(project.join(".lake/build"))?;
                // Opt-out must also preserve a populated build directory without a legacy lock.
                let before = snapshot(&project)?;
                drop(super::acquire_publish_flock(&project, true)?);
                assert_eq!(before, snapshot(&project)?);
                let lock = project.join(".lake/build/.turbo_publish.lock");
                std::fs::write(&lock, b"legacy")?;
                use std::os::unix::fs::PermissionsExt;
                std::fs::set_permissions(lock, std::fs::Permissions::from_mode(0o444))?;
            } else {
                let before = snapshot(&project)?;
                drop(super::acquire_publish_flock(&project, true)?);
                assert_eq!(before, snapshot(&project)?);
            }
        }
        std::fs::remove_dir_all(root)?;
        Ok(())
    }

    use super::*;
    use std::time::Duration;

    #[test]
    fn test_atomic_write_shm_creates_and_overwrites_cleanly() -> std::io::Result<()> {
        let dir =
            std::env::temp_dir().join(format!("turbo_lean_shm_atomic_test_{}", std::process::id()));
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
        let dir =
            std::env::temp_dir().join(format!("turbo_lean_shm_lru_test_{}", std::process::id()));
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
        assert!(
            f_mid.exists(),
            "Middle file should remain when <= 80% quota"
        );
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
        assert_eq!(gov_2048.recommended_parallel_workers(512), 4.min(max_cpus));
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
        let base_dir =
            std::env::temp_dir().join(format!("turbo_lean_shm_spill_test_{}", std::process::id()));
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
        assert!(
            !f_old.exists(),
            "evicted file must be unlinked from shm_dir"
        );
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
