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
pub const SHM_CACHE_SCHEMA_VERSION: u32 = 2;

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
    base.join(format!(
        "turbo-lean-staging-{}-{}",
        uid,
        crate::build_epoch_short()
    ))
}

pub fn configured_cache_root_env() -> Option<PathBuf> {
    let non_empty = |k: &str| {
        std::env::var(k)
            .ok()
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
    };
    non_empty("TURBO_LEAN_HOME")
        .or_else(|| non_empty("TURBO_LEAN_CACHE_DIR"))
        .map(PathBuf::from)
}

/// Persistent per-user cache root for the store.
pub fn cache_root() -> PathBuf {
    configured_cache_root_env().unwrap_or_else(|| {
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
    preserve_lake: bool,
) -> std::io::Result<PublishFlockGuard> {
    let directory = flock_file(fs::File::open(pkg_root)?, exclusive, false)?;
    let lock_path = pkg_root.join(".lake/build/.turbo_publish.lock");
    let legacy = if preserve_lake {
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

fn is_private_staging_parent(parent: &Path) -> bool {
    let base = staging_shm_dir();
    parent == base
        || parent.starts_with(&base)
        || parent.file_name().and_then(|s| s.to_str()) == Some("staging")
        || parent
            .parent()
            .and_then(|p| p.file_name())
            .and_then(|s| s.to_str())
            == Some("staging")
}

fn ensure_parent_dir_for_leaf_write(parent: &Path) -> std::io::Result<()> {
    if parent.as_os_str().is_empty() || parent == Path::new(".") {
        return Ok(());
    }
    if is_private_staging_parent(parent) {
        return ensure_private_dir_all(parent);
    }
    fs::create_dir_all(parent)?;
    if !fs::metadata(parent)?.is_dir() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("parent directory is not a directory: {}", parent.display()),
        ));
    }
    Ok(())
}

pub(crate) fn ensure_private_dir_all(dir: &Path) -> std::io::Result<()> {
    if dir.as_os_str().is_empty() || dir == Path::new(".") {
        return Ok(());
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
        if fs::symlink_metadata(dir).is_err() {
            let mut builder = fs::DirBuilder::new();
            builder.recursive(true).mode(0o700);
            match builder.create(dir) {
                Ok(()) => {
                    let mut opts = fs::OpenOptions::new();
                    opts.read(true)
                        .custom_flags(libc::O_NOFOLLOW | libc::O_DIRECTORY);
                    if let Ok(created_f) = opts.open(dir) {
                        let _ = created_f.set_permissions(fs::Permissions::from_mode(0o700));
                    }
                }
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(e) => return Err(e),
            }
        }
        let sym = fs::symlink_metadata(dir)?;
        if sym.file_type().is_symlink() || !sym.file_type().is_dir() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!(
                    "staging directory is not a plain directory: {}",
                    dir.display()
                ),
            ));
        }
        let mut opts = fs::OpenOptions::new();
        opts.read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_DIRECTORY);
        let dir_f = opts.open(dir)?;
        let meta = dir_f.metadata()?;
        if !meta.file_type().is_dir() || !inode_matches_nofollow(&dir_f, dir) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!(
                    "staging directory failed nofollow verification: {}",
                    dir.display()
                ),
            ));
        }
        let euid = unsafe { libc::geteuid() };
        if meta.uid() != euid || (meta.mode() & 0o077) != 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::PermissionDenied,
                format!(
                    "staging directory is not privately owned (0700) by current uid: {}",
                    dir.display()
                ),
            ));
        }
        Ok(())
    }
    #[cfg(not(unix))]
    {
        fs::create_dir_all(dir)
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
        ensure_parent_dir_for_leaf_write(parent)?;
    }
    let mut opts = fs::OpenOptions::new();
    opts.create(true).read(true).write(true).truncate(false);
    // A planted symlink must not make the lock create or open a file elsewhere.
    #[cfg(unix)]
    std::os::unix::fs::OpenOptionsExt::custom_flags(&mut opts, libc::O_NOFOLLOW);
    flock_file(opts.open(lock_path)?, exclusive, nonblocking)
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
        .filter(|p| !p.as_os_str().is_empty())
        .map(|p| {
            if p.is_dir() {
                p.to_path_buf()
            } else {
                p.parent()
                    .filter(|p| !p.as_os_str().is_empty())
                    .unwrap_or_else(|| Path::new("."))
                    .to_path_buf()
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
        } else if p.as_os_str().is_empty() {
            PathBuf::from(".")
        } else {
            p.parent()
                .filter(|p| !p.as_os_str().is_empty())
                .unwrap_or_else(|| Path::new("."))
                .to_path_buf()
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
    stage_unique_tmp_path_ext(target, "tmp")
}

fn stage_unique_tmp_path_ext(target: &Path, ext: &str) -> std::io::Result<PathBuf> {
    let parent = target.parent().unwrap_or_else(|| Path::new("."));
    ensure_parent_dir_for_leaf_write(parent)?;
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
        ".{}.{}.{}.{}.{}",
        file_name,
        std::process::id(),
        seq,
        nanos,
        ext
    )))
}

/// Atomically write `bytes` to `target` by staging into a process+sequence-unique temporary file
/// in `target.parent()` and invoking `fs::rename` over `target`.
pub fn atomic_write_shm(target: &Path, bytes: &[u8]) -> std::io::Result<()> {
    let (mut tmp_f, tmp_path) = match open_unique_exclusive_tmp(target, 0o600) {
        Ok(pair) => pair,
        Err(e) => {
            debug_log_cache_err("atomic_write_shm(open)", &e);
            return Err(e);
        }
    };
    if let Err(e) = tmp_f.write_all(bytes) {
        drop(tmp_f);
        let _ = fs::remove_file(&tmp_path);
        debug_log_cache_err("atomic_write_shm(write)", &e);
        return Err(e);
    }
    if let Err(e) = tmp_f.sync_all() {
        drop(tmp_f);
        let _ = fs::remove_file(&tmp_path);
        debug_log_cache_err("atomic_write_shm(sync)", &e);
        return Err(e);
    }
    drop(tmp_f);
    if let Err(e) = fs::rename(&tmp_path, target) {
        let _ = fs::remove_file(&tmp_path);
        debug_log_cache_err("atomic_write_shm(rename)", &e);
        return Err(e);
    }
    Ok(())
}

fn is_safe_single_shm_segment(seg: &str) -> bool {
    !seg.is_empty()
        && seg != "."
        && seg != ".."
        && !seg.contains('/')
        && !seg.contains('\\')
        && !seg.contains('\0')
}

#[cfg(unix)]
fn verify_or_create_private_dir_one(dir: &Path, create_if_missing: bool) -> Option<()> {
    use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};

    match fs::symlink_metadata(dir) {
        Ok(sym_meta) => {
            if sym_meta.file_type().is_symlink() || !sym_meta.file_type().is_dir() {
                return None;
            }
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound && create_if_missing => {
            let mut builder = fs::DirBuilder::new();
            builder.recursive(true).mode(0o700);
            builder.create(dir).ok()?;
            let mut opts = fs::OpenOptions::new();
            opts.read(true)
                .custom_flags(libc::O_NOFOLLOW | libc::O_DIRECTORY);
            let created_f = opts.open(dir).ok()?;
            let _ = created_f.set_permissions(fs::Permissions::from_mode(0o700));
        }
        Err(_) => return None,
    }

    let sym_meta = fs::symlink_metadata(dir).ok()?;
    if sym_meta.file_type().is_symlink() || !sym_meta.file_type().is_dir() {
        return None;
    }

    let mut opts = fs::OpenOptions::new();
    opts.read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_DIRECTORY);
    let dir_f = opts.open(dir).ok()?;
    let meta = dir_f.metadata().ok()?;
    let euid = unsafe { libc::geteuid() };
    if !meta.file_type().is_dir() || meta.uid() != euid || (meta.mode() & 0o077) != 0 {
        return None;
    }
    if !inode_matches_nofollow(&dir_f, dir) {
        return None;
    }
    Some(())
}

/// Ensure `staging_shm_dir()` (and optional single-segment `subdir`) exists as a non-symlink
/// directory owned by `geteuid()` with private `0o700` permissions (`(mode & 0o077) == 0`).
pub fn ensure_verified_private_staging_dir(subdir: Option<&str>) -> Option<PathBuf> {
    let base = staging_shm_dir();
    #[cfg(unix)]
    verify_or_create_private_dir_one(&base, true)?;
    #[cfg(not(unix))]
    fs::create_dir_all(&base).ok()?;

    let Some(sub) = subdir else {
        return Some(base);
    };
    if !is_safe_single_shm_segment(sub) {
        return None;
    }
    let sub_path = base.join(sub);
    #[cfg(unix)]
    verify_or_create_private_dir_one(&sub_path, true)?;
    #[cfg(not(unix))]
    fs::create_dir_all(&sub_path).ok()?;
    Some(sub_path)
}

/// Read a private cache file at `file_path` fail-closed WITHOUT mutating permissions:
/// verifies `file_path.parent()` (and its parent when under `staging_shm_dir()` or `<root>/staging`)
/// is a non-symlink directory owned by `geteuid()` with `0o700` permissions, and opens `file_path`
/// with `O_NOFOLLOW` verifying regular file, `nlink == 1`, `uid == geteuid()`, and `(mode & 0o077) == 0`.
pub(crate) fn read_verified_private_file_at(file_path: &Path) -> Option<Vec<u8>> {
    let sub_path = file_path.parent()?;
    if sub_path.as_os_str().is_empty() {
        return None;
    }
    #[cfg(unix)]
    {
        use std::io::Read;
        use std::os::unix::fs::{MetadataExt, OpenOptionsExt};

        let base_shm = staging_shm_dir();
        if sub_path == base_shm || sub_path.starts_with(&base_shm) {
            verify_or_create_private_dir_one(&base_shm, false)?;
        } else if let Some(parent_base) = sub_path.parent() {
            if parent_base.file_name().and_then(|s| s.to_str()) == Some("staging") {
                verify_or_create_private_dir_one(parent_base, false)?;
            }
        }
        verify_or_create_private_dir_one(sub_path, false)?;

        let sym_meta = fs::symlink_metadata(file_path).ok()?;
        if sym_meta.file_type().is_symlink() || !sym_meta.file_type().is_file() {
            return None;
        }
        let mut opts = fs::OpenOptions::new();
        opts.read(true).custom_flags(libc::O_NOFOLLOW);
        let mut f = opts.open(file_path).ok()?;
        let meta = f.metadata().ok()?;
        let euid = unsafe { libc::geteuid() };
        if !meta.file_type().is_file()
            || meta.nlink() != 1
            || meta.uid() != euid
            || (meta.mode() & 0o077) != 0
        {
            return None;
        }
        if !inode_matches_nofollow(&f, file_path) {
            return None;
        }
        let mut buf = Vec::with_capacity(meta.len() as usize);
        f.read_to_end(&mut buf).ok()?;
        Some(buf)
    }
    #[cfg(not(unix))]
    {
        fs::read(file_path).ok()
    }
}

/// Read `staging_shm_dir()/<subdir>/<file_name>` fail-closed WITHOUT mutating permissions:
/// returns `None` if `base`, `subdir`, or `file_name` is a symlink, multiply linked (`nlink != 1`),
/// not owned by `geteuid()`, or has any group/other permission bits (`(mode & 0o077) != 0`).
pub fn read_verified_private_shm_file(subdir: &str, file_name: &str) -> Option<Vec<u8>> {
    if !is_safe_single_shm_segment(subdir) || !is_safe_single_shm_segment(file_name) {
        return None;
    }
    read_verified_private_file_at(&staging_shm_dir().join(subdir).join(file_name))
}

/// Atomically write `bytes` to `staging_shm_dir()/<subdir>/<file_name>` with `0o600` permissions
/// inside verified `0o700` `euid`-owned directories, refusing symlink targets.
pub fn write_verified_private_shm_file(
    subdir: &str,
    file_name: &str,
    bytes: &[u8],
) -> std::io::Result<()> {
    if !is_safe_single_shm_segment(subdir) || !is_safe_single_shm_segment(file_name) {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "invalid private shm cache segment",
        ));
    }
    let sub_path = ensure_verified_private_staging_dir(Some(subdir)).ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            "untrusted or unowned staging_shm_dir",
        )
    })?;
    let target = sub_path.join(file_name);
    match fs::symlink_metadata(&target) {
        Ok(meta) if !meta.file_type().is_file() => {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("refusing non-regular shm cache target {}", target.display()),
            ));
        }
        Ok(_) => {}
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => return Err(e),
    }
    let (mut tmp_f, tmp_path) = open_unique_exclusive_tmp(&target, 0o600)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if let Err(e) = tmp_f.set_permissions(fs::Permissions::from_mode(0o600)) {
            drop(tmp_f);
            let _ = fs::remove_file(&tmp_path);
            return Err(e);
        }
    }
    if let Err(e) = tmp_f.write_all(bytes) {
        drop(tmp_f);
        let _ = fs::remove_file(&tmp_path);
        return Err(e);
    }
    drop(tmp_f);
    match fs::symlink_metadata(&target) {
        Ok(meta) if !meta.file_type().is_file() => {
            let _ = fs::remove_file(&tmp_path);
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("refusing non-regular shm cache target {}", target.display()),
            ));
        }
        Ok(_) => {}
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => {
            let _ = fs::remove_file(&tmp_path);
            return Err(e);
        }
    }
    if let Err(e) = fs::rename(&tmp_path, &target) {
        let _ = fs::remove_file(&tmp_path);
        return Err(e);
    }
    Ok(())
}

pub(crate) struct StagingLeaseGuard {
    lock_path: PathBuf,
    _lease: Option<FlockGuard>,
}

fn ensure_lease_or_staging_parent_dir(parent: &Path) -> std::io::Result<()> {
    ensure_parent_dir_for_leaf_write(parent)
}

impl StagingLeaseGuard {
    pub(crate) fn acquire_for_target(target: &Path) -> std::io::Result<Self> {
        if let Some(parent) = target.parent() {
            ensure_lease_or_staging_parent_dir(parent)?;
        }
        #[cfg(unix)]
        let mut dir_lease = lock_staging_parent_dir(target, false, false)?;
        let lock_path = staging_lease_lock_path(target);
        let lease = match acquire_staging_lease(&lock_path) {
            Ok(l) => l,
            Err(e) => {
                #[cfg(unix)]
                drop(dir_lease);
                return Err(e);
            }
        };
        #[cfg(unix)]
        drop(dir_lease.take());
        Ok(Self {
            lock_path,
            _lease: lease,
        })
    }
}

impl Drop for StagingLeaseGuard {
    fn drop(&mut self) {
        let _ = self._lease.take();
        let _ = reap_stale_lock_if_unheld(&self.lock_path);
    }
}

pub fn is_staging_lease_held_on_self_or_ancestor(target: &Path, root: &Path) -> bool {
    let mut cur = target;
    loop {
        if is_staging_lease_held(cur) {
            return true;
        }
        let Some(parent) = cur.parent() else {
            break;
        };
        if parent == cur || parent == root {
            break;
        }
        cur = parent;
    }
    false
}

pub struct StagedTempFile {
    path: PathBuf,
    _lease: Option<FlockGuard>,
}

impl StagedTempFile {
    pub fn write(path: PathBuf, bytes: impl AsRef<[u8]>) -> std::io::Result<Self> {
        Self::stage_with_lease(path, bytes.as_ref())
    }

    pub fn reserve(path: PathBuf) -> std::io::Result<Self> {
        Self::stage_with_lease(path, &[])
    }

    fn stage_with_lease(path: PathBuf, bytes: &[u8]) -> std::io::Result<Self> {
        if let Some(parent) = path.parent() {
            ensure_lease_or_staging_parent_dir(parent)?;
        }
        #[cfg(unix)]
        let mut dir_lease = lock_staging_parent_dir(&path, false, false)?;
        let lock_path = staging_lease_lock_path(&path);
        let lease = match acquire_staging_lease(&lock_path) {
            Ok(l) => l,
            Err(e) => {
                #[cfg(unix)]
                drop(dir_lease);
                return Err(e);
            }
        };
        #[cfg(unix)]
        drop(dir_lease.take());
        if let Err(e) = replace_staged_payload_nofollow(&path, bytes) {
            drop(lease);
            let _ = reap_stale_lock_if_unheld(&lock_path);
            return Err(e);
        }
        Ok(Self {
            path,
            _lease: lease,
        })
    }

    pub fn overwrite(&self, bytes: &[u8]) -> std::io::Result<()> {
        replace_staged_payload_nofollow(&self.path, bytes)
    }

    pub fn path(&self) -> &Path {
        &self.path
    }
}

fn replace_staged_payload_nofollow(path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    match fs::symlink_metadata(path) {
        Ok(meta) if !meta.file_type().is_file() => {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("refusing non-regular staged target path {}", path.display()),
            ));
        }
        Ok(_) => {}
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => return Err(e),
    }
    let (mut tmp_f, tmp_path) = open_unique_exclusive_tmp_ext(path, 0o600, "stgtmp")?;
    let res = (|| -> std::io::Result<()> {
        if !bytes.is_empty() {
            tmp_f.write_all(bytes)?;
        }
        match fs::symlink_metadata(path) {
            Ok(meta) if !meta.file_type().is_file() => {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    format!("refusing non-regular staged target path {}", path.display()),
                ));
            }
            Ok(_) => {}
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(e),
        }
        fs::rename(&tmp_path, path)?;
        #[cfg(unix)]
        if !inode_matches_nofollow(&tmp_f, path) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!(
                    "staged target path {} changed during atomic replacement",
                    path.display()
                ),
            ));
        }
        Ok(())
    })();
    drop(tmp_f);
    let _ = fs::remove_file(&tmp_path);
    res
}

fn open_unique_exclusive_tmp(target: &Path, mode: u32) -> std::io::Result<(fs::File, PathBuf)> {
    open_unique_exclusive_tmp_ext(target, mode, "tmp")
}

fn open_unique_exclusive_tmp_ext(
    target: &Path,
    mode: u32,
    ext: &str,
) -> std::io::Result<(fs::File, PathBuf)> {
    for _ in 0..16 {
        let tmp_path = stage_unique_tmp_path_ext(target, ext)?;
        let mut opts = fs::OpenOptions::new();
        opts.write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            opts.mode(mode).custom_flags(libc::O_NOFOLLOW);
        }
        match opts.open(&tmp_path) {
            Ok(f) => {
                #[cfg(unix)]
                {
                    use std::os::unix::fs::PermissionsExt;
                    if let Err(e) = f.set_permissions(fs::Permissions::from_mode(mode)) {
                        drop(f);
                        let _ = fs::remove_file(&tmp_path);
                        return Err(e);
                    }
                }
                return Ok((f, tmp_path));
            }
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => return Err(e),
        }
    }
    Err(std::io::Error::new(
        std::io::ErrorKind::AlreadyExists,
        format!(
            "could not allocate unique exclusive staging file for {}",
            target.display()
        ),
    ))
}

impl std::ops::Deref for StagedTempFile {
    type Target = Path;

    fn deref(&self) -> &Self::Target {
        &self.path
    }
}

impl AsRef<Path> for StagedTempFile {
    fn as_ref(&self) -> &Path {
        &self.path
    }
}

impl AsRef<std::ffi::OsStr> for StagedTempFile {
    fn as_ref(&self) -> &std::ffi::OsStr {
        self.path.as_os_str()
    }
}

impl Drop for StagedTempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
        // Drop our `LOCK_SH` fd before attempting best-effort `LOCK_EX | LOCK_NB` sidecar cleanup.
        let _ = self._lease.take();
        let _ = reap_stale_lock_if_unheld(&staging_lease_lock_path(&self.path));
    }
}

fn staging_lease_lock_path(target: &Path) -> PathBuf {
    let parent = target.parent().unwrap_or_else(|| Path::new("."));
    let fname = target
        .file_name()
        .map(|n| n.to_string_lossy())
        .unwrap_or_else(|| std::borrow::Cow::Borrowed("staged"));
    parent.join(format!(".{}.lease.lock", fname))
}

#[cfg(unix)]
fn lock_staging_parent_dir(
    child_path: &Path,
    exclusive: bool,
    nonblocking: bool,
) -> std::io::Result<Option<FlockGuard>> {
    let parent = match child_path.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    let dir_f = fs::File::open(parent)?;
    flock_file(dir_f, exclusive, nonblocking)
}

#[cfg(unix)]
fn file_inode_key(f: &fs::File) -> Option<(u64, u64)> {
    use std::os::unix::fs::MetadataExt;
    f.metadata().ok().map(|m| (m.dev(), m.ino()))
}

#[cfg(unix)]
fn path_nofollow_inode_key(path: &Path) -> Option<(u64, u64)> {
    use std::os::unix::fs::MetadataExt;
    fs::symlink_metadata(path).ok().map(|m| (m.dev(), m.ino()))
}

#[cfg(unix)]
fn inode_matches_nofollow(f: &fs::File, path: &Path) -> bool {
    matches!(
        (file_inode_key(f), path_nofollow_inode_key(path)),
        (Some(a), Some(b)) if a == b
    )
}

#[cfg(test)]
type AfterSidecarOpenHook = std::rc::Rc<dyn Fn(&Path)>;

#[cfg(test)]
thread_local! {
    static AFTER_SIDECAR_OPEN_HOOK: std::cell::RefCell<Option<AfterSidecarOpenHook>> =
        const { std::cell::RefCell::new(None) };
}

fn acquire_staging_lease(lock_path: &Path) -> std::io::Result<Option<FlockGuard>> {
    for attempt in 0..4096u32 {
        if let Some(parent) = lock_path.parent() {
            ensure_lease_or_staging_parent_dir(parent)?;
        }
        let mut opts = fs::OpenOptions::new();
        opts.create(true).read(true).write(true).truncate(false);
        #[cfg(unix)]
        std::os::unix::fs::OpenOptionsExt::custom_flags(&mut opts, libc::O_NOFOLLOW);
        let f = opts.open(lock_path)?;
        #[cfg(test)]
        if let Some(hook) = AFTER_SIDECAR_OPEN_HOOK.with(|h| h.borrow().clone()) {
            hook(lock_path);
        }
        let Some(guard) = flock_file(f, false, false)? else {
            continue;
        };
        #[cfg(unix)]
        if !inode_matches_nofollow(&guard.0, lock_path) {
            drop(guard);
            if attempt >= 4 {
                std::thread::yield_now();
            }
            continue;
        }
        #[cfg(not(unix))]
        let _ = attempt;
        return Ok(Some(guard));
    }
    Err(std::io::Error::new(
        std::io::ErrorKind::TimedOut,
        "staging lease sidecar contended during acquisition",
    ))
}

fn try_lock_sidecar(lock_path: &Path, create: bool) -> Option<FlockGuard> {
    for _ in 0..16u8 {
        let mut opts = fs::OpenOptions::new();
        opts.read(true).write(true).create(create).truncate(false);
        #[cfg(unix)]
        std::os::unix::fs::OpenOptionsExt::custom_flags(&mut opts, libc::O_NOFOLLOW);
        let f = opts.open(lock_path).ok()?;
        let guard = flock_file(f, true, true).ok()??;
        #[cfg(unix)]
        if !inode_matches_nofollow(&guard.0, lock_path) {
            drop(guard);
            if create {
                continue;
            }
            return None;
        }
        return Some(guard);
    }
    None
}

fn try_lock_unheld_sidecar(lock_path: &Path) -> Option<FlockGuard> {
    try_lock_sidecar(lock_path, false)
}

pub fn try_remove_unleased_staged_file(target: &Path) -> bool {
    if fs::symlink_metadata(target).is_err() {
        return false;
    }
    #[cfg(unix)]
    let _dir_guard = match lock_staging_parent_dir(target, true, true) {
        Ok(Some(g)) => Some(g),
        _ => return false,
    };
    let lock_path = staging_lease_lock_path(target);
    let Some(guard) = try_lock_sidecar(&lock_path, true) else {
        return false;
    };
    let removed = fs::remove_file(target).is_ok();
    if fs::symlink_metadata(target).is_err() {
        let _ = fs::remove_file(&lock_path);
    }
    drop(guard);
    removed
}

pub fn try_remove_unleased_staged_dir(target: &Path) -> bool {
    if !fs::symlink_metadata(target).is_ok_and(|m| m.file_type().is_dir()) {
        return false;
    }
    #[cfg(unix)]
    let _dir_guard = match lock_staging_parent_dir(target, true, true) {
        Ok(Some(g)) => Some(g),
        _ => return false,
    };
    let lock_path = staging_lease_lock_path(target);
    let Some(guard) = try_lock_sidecar(&lock_path, true) else {
        return false;
    };
    crate::check::thaw_private_dir_tree(target);
    let removed = fs::remove_dir_all(target).is_ok();
    if fs::symlink_metadata(target).is_err() {
        let _ = fs::remove_file(&lock_path);
    }
    drop(guard);
    removed
}

pub fn reap_stale_lock_if_unheld(lock_path: &Path) -> bool {
    #[cfg(unix)]
    let _dir_guard = match lock_staging_parent_dir(lock_path, true, true) {
        Ok(Some(g)) => Some(g),
        _ => return false,
    };
    let Some(guard) = try_lock_unheld_sidecar(lock_path) else {
        return false;
    };
    if let Some(fname) = lock_path.file_name().and_then(|n| n.to_str()) {
        if let Some(orig) = fname
            .strip_prefix('.')
            .and_then(|s| s.strip_suffix(".lease.lock"))
        {
            if fs::symlink_metadata(
                lock_path
                    .parent()
                    .unwrap_or_else(|| Path::new("."))
                    .join(orig),
            )
            .is_ok()
            {
                return false;
            }
        }
    }
    let ok = fs::remove_file(lock_path).is_ok();
    drop(guard);
    ok
}

pub fn is_staging_lease_held(target: &Path) -> bool {
    let lock_path = staging_lease_lock_path(target);
    #[cfg(unix)]
    let exists = path_nofollow_inode_key(&lock_path).is_some();
    #[cfg(not(unix))]
    let exists = lock_path.exists();
    exists && try_lock_unheld_sidecar(&lock_path).is_none()
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
                let _ = reap_stale_lock_if_unheld(path);
            }
            continue;
        }
        if is_staging_lease_held_on_self_or_ancestor(path, shm_dir) {
            continue;
        }
        let fname = path
            .file_name()
            .map(|n| n.to_string_lossy())
            .unwrap_or_default();
        if (fname.starts_with('.') && (fname.ends_with(".tmp") || fname.ends_with(".stgtmp")))
            || fname == "zygote_daemon.json"
            || fname == "zygote_lru_registry.json"
            || path.to_string_lossy().contains("zygote_daemon_cas_")
            || path.to_string_lossy().contains("fastcheck_shared_bins")
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
        if try_remove_unleased_staged_file(&path) {
            total_size = total_size.saturating_sub(sz);
            evicted_files += 1;
            freed_bytes = freed_bytes.saturating_add(sz);
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
                if let Ok(pages) = rest.trim().trim_end_matches('.').parse::<u64>() {
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

/// Default cgroup v2 unified hierarchy mount point.
pub const CGROUP_V2_ROOT: &str = "/sys/fs/cgroup";

/// Extract the cgroup v2 relative path (`0::<rel>`) from `/proc/self/cgroup` contents.
pub fn parse_proc_self_cgroup_v2_path(text: &str) -> Option<String> {
    let rel = text
        .lines()
        .find_map(|line| line.trim_end().strip_prefix("0::"))?
        .trim();
    if !rel.starts_with('/') || rel.split('/').any(|seg| seg == ".." || seg == ".") {
        return None;
    }
    Some(rel.to_string())
}

/// Extract the cgroup v1 `memory` controller relative path (e.g. `12:memory:/foo` or
/// `4:cpu,memory:/foo`) from `/proc/self/cgroup` contents.
pub fn parse_proc_self_cgroup_v1_memory_path(text: &str) -> Option<String> {
    let rel = text.lines().find_map(|line| {
        let mut parts = line.trim_end().splitn(3, ':');
        let _id = parts.next()?;
        let controllers = parts.next()?;
        let path = parts.next()?.trim();
        controllers
            .split(',')
            .any(|ctrl| ctrl == "memory")
            .then_some(path)
    })?;
    if !rel.starts_with('/') || rel.split('/').any(|seg| seg == ".." || seg == ".") {
        return None;
    }
    Some(rel.to_string())
}

/// Parse a cgroup `memory.max` / `memory.limit_in_bytes` value: `max` (or absurd sentinel
/// values) means unlimited (`None`); otherwise a positive byte count.
pub fn parse_cgroup_memory_max_bytes(raw: &str) -> Option<u64> {
    let trimmed = raw.trim();
    if trimmed == "max" {
        return None;
    }
    trimmed
        .parse::<u64>()
        .ok()
        .filter(|&bytes| bytes > 0 && bytes < (1u64 << 50))
}

/// Ancestor cgroup directories of `rel` under `cgroup_root`, leaf first, mount root last.
fn cgroup_v2_ancestor_dirs(cgroup_root: &Path, rel: &str) -> Vec<PathBuf> {
    let segs: Vec<&str> = rel
        .split('/')
        .filter(|seg| !seg.is_empty() && *seg != "." && *seg != "..")
        .collect();
    (0..=segs.len())
        .rev()
        .map(|n| {
            segs[..n]
                .iter()
                .fold(cgroup_root.to_path_buf(), |p, s| p.join(s))
        })
        .collect()
}

/// Probe `<root><rel>/memory.max` up through every ancestor to `<root>/memory.max`, returning
/// `(saw_any_v2_memory_max_file, min_numeric_limit)`.
fn resolve_cgroup_v2_memory_max_probe(cgroup_root: &Path, rel: &str) -> (bool, Option<u64>) {
    let mut saw_v2_file = false;
    let mut min_limit: Option<u64> = None;
    for dir in cgroup_v2_ancestor_dirs(cgroup_root, rel) {
        if let Ok(raw) = fs::read_to_string(dir.join("memory.max")) {
            saw_v2_file = true;
            if let Some(limit) = parse_cgroup_memory_max_bytes(&raw) {
                min_limit = Some(min_limit.map_or(limit, |cur| cur.min(limit)));
            }
        }
    }
    (saw_v2_file, min_limit)
}

/// Walk `<root><rel>/memory.max` up through every ancestor to `<root>/memory.max`, returning the
/// tightest (minimum) numeric limit, or `None` when every level is `max` / unreadable.
pub fn resolve_cgroup_v2_memory_max_bytes_at(cgroup_root: &Path, rel: &str) -> Option<u64> {
    resolve_cgroup_v2_memory_max_probe(cgroup_root, rel).1
}

/// Walk `<root>/memory<rel>/memory.limit_in_bytes` up through every ancestor to
/// `<root>/memory/memory.limit_in_bytes`, returning the tightest numeric limit.
pub fn resolve_cgroup_v1_memory_limit_bytes_at(cgroup_root: &Path, rel: &str) -> Option<u64> {
    let v1_mem_root = cgroup_root.join("memory");
    cgroup_v2_ancestor_dirs(&v1_mem_root, rel)
        .into_iter()
        .filter_map(|dir| fs::read_to_string(dir.join("memory.limit_in_bytes")).ok())
        .filter_map(|raw| parse_cgroup_memory_max_bytes(&raw))
        .min()
}

/// Resolve the effective cgroup memory limit under `cgroup_root` using `/proc/self/cgroup`
/// contents.
///
/// When cgroup v2 is active (any readable `memory.max` along the v2 ancestor chain, or a unified
/// v2 mount with `cgroup.controllers`), v2 is authoritative: an explicit `max` returns `None` and
/// never falls through to cgroup v1 `memory.limit_in_bytes`. Otherwise, falls back to the cgroup
/// v1 `memory` controller hierarchy.
pub fn resolve_effective_cgroup_memory_max_bytes_at(
    cgroup_root: &Path,
    proc_self_cgroup: Option<&str>,
) -> Option<u64> {
    let is_unified_v2_mount = cgroup_root.join("cgroup.controllers").is_file();
    if let Some(v2_rel) = proc_self_cgroup.and_then(parse_proc_self_cgroup_v2_path) {
        let (saw_v2_file, v2_limit) = resolve_cgroup_v2_memory_max_probe(cgroup_root, &v2_rel);
        if saw_v2_file || is_unified_v2_mount {
            return v2_limit;
        }
    } else if proc_self_cgroup.is_none() {
        let (saw_v2_file, v2_limit) = resolve_cgroup_v2_memory_max_probe(cgroup_root, "/");
        if saw_v2_file || is_unified_v2_mount {
            return v2_limit;
        }
    }
    let v1_rel = proc_self_cgroup.and_then(parse_proc_self_cgroup_v1_memory_path);
    resolve_cgroup_v1_memory_limit_bytes_at(cgroup_root, v1_rel.as_deref().unwrap_or("/"))
}

fn current_cgroup_v2_rel_path() -> Option<String> {
    parse_proc_self_cgroup_v2_path(&fs::read_to_string("/proc/self/cgroup").ok()?)
}

/// Effective cgroup memory limit in bytes for this process (cgroup v2 ancestor walk; falls back
/// to cgroup v1 `memory.limit_in_bytes` only when cgroup v2 is not active).
pub fn effective_cgroup_memory_max_bytes() -> Option<u64> {
    let proc_cgroup = fs::read_to_string("/proc/self/cgroup").ok();
    resolve_effective_cgroup_memory_max_bytes_at(
        Path::new(CGROUP_V2_ROOT),
        proc_cgroup.as_deref(),
    )
}

/// Compute the cgroup `oom_kill` counter delta across a run.
/// If the counter was absent before the run (`before == None`) and appears mid-run
/// (`after == Some(n)`), treat the missing baseline as `0` rather than masking the OOM event.
pub fn cgroup_oom_kill_delta(before: Option<u64>, after: Option<u64>) -> Option<u64> {
    after.map(|a| a.saturating_sub(before.unwrap_or(0)))
}

/// Parse the `oom_kill` counter from a cgroup v2 `memory.events` file.
pub fn parse_cgroup_memory_events_oom_kill(text: &str) -> Option<u64> {
    text.lines().find_map(|line| {
        let mut fields = line.split_whitespace();
        (fields.next()? == "oom_kill")
            .then(|| fields.next()?.parse::<u64>().ok())
            .flatten()
    })
}

/// Read `<root><rel>/memory.events` `oom_kill` count.
pub fn read_cgroup_oom_kill_count_at(cgroup_root: &Path, rel: &str) -> Option<u64> {
    let dir = cgroup_v2_ancestor_dirs(cgroup_root, rel)
        .into_iter()
        .next()?;
    parse_cgroup_memory_events_oom_kill(&fs::read_to_string(dir.join("memory.events")).ok()?)
}

/// `oom_kill` count of this process' own cgroup v2 (`None` when unavailable).
pub fn current_cgroup_oom_kill_count() -> Option<u64> {
    read_cgroup_oom_kill_count_at(Path::new(CGROUP_V2_ROOT), &current_cgroup_v2_rel_path()?)
}

/// Pre-flight memory guard: fail fast with an actionable diagnostic when the recorded historical
/// peak RSS (`historical_peak_rss_mb`) or the requested `--max-memory-mb` budget cannot fit under
/// the effective cgroup `memory.max` (`cgroup_max_bytes`). Unknown inputs pass.
pub fn preflight_memory_guard(
    what: &str,
    historical_peak_rss_mb: Option<u64>,
    max_memory_mb: Option<u64>,
    cgroup_max_bytes: Option<u64>,
) -> anyhow::Result<()> {
    let Some(limit_bytes) = cgroup_max_bytes else {
        return Ok(());
    };
    let limit_mb = limit_bytes / (1024 * 1024);
    if let Some(peak_mb) = historical_peak_rss_mb.filter(|&mb| mb > limit_mb) {
        anyhow::bail!(
            "[turbo-lean] pre-flight memory guard: `{what}` previously peaked at {peak_mb} MiB RSS but the effective cgroup `memory.max` is only {limit_mb} MiB; it would be OOM-killed. Run it under a larger cgroup (e.g. `systemd-run --user -p MemoryMax={}M`) or a bigger machine, reduce parallelism (`--jobs 1`), or set `TURBO_LEAN_SKIP_MEMORY_PREFLIGHT=1` to bypass (`--max-memory-mb` cannot raise a cgroup limit)",
            peak_mb.saturating_add(peak_mb / 4)
        );
    }
    if let Some(budget_mb) = max_memory_mb.filter(|&mb| mb > limit_mb) {
        anyhow::bail!(
            "[turbo-lean] pre-flight memory guard: `--max-memory-mb {budget_mb}` (`TURBO_LEAN_MAX_MEMORY_MB`) for `{what}` exceeds the effective cgroup `memory.max` of {limit_mb} MiB; the kernel would OOM-kill before the budget is reached. Pass `--max-memory-mb {}` or less, or raise the cgroup `MemoryMax`",
            (limit_mb.saturating_mul(9) / 10).max(1)
        );
    }
    Ok(())
}

/// Read an explicit historical peak RSS override in MiB from `TURBO_LEAN_HISTORICAL_PEAK_RSS_MB`.
pub fn historical_peak_rss_mb_from_env() -> Option<u64> {
    std::env::var("TURBO_LEAN_HISTORICAL_PEAK_RSS_MB")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .filter(|&mb| mb > 0)
}

/// Read `peak_rss_kib` (converted to MiB) from an existing JSON `BuildReceipt` file, if present.
pub fn read_receipt_peak_rss_mb(receipt_path: &Path) -> Option<u64> {
    let raw = fs::read(receipt_path).ok()?;
    let receipt: BuildReceipt = serde_json::from_slice(&raw).ok()?;
    receipt
        .peak_rss_kib
        .map(|kib| kib / 1024)
        .filter(|&mb| mb > 0)
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct PersistedPeakRss {
    peak_rss_kib: u64,
}

fn project_peak_rss_cache_path(project_dir: &Path) -> PathBuf {
    let canonical = fs::canonicalize(project_dir).unwrap_or_else(|_| project_dir.to_path_buf());
    let key = &blake3::hash(canonical.to_string_lossy().as_bytes())
        .to_hex()
        .to_string()[..28];
    cache_root().join("peak_rss").join(format!("{key}.json"))
}

/// Read the cached historical peak RSS in MiB for `project_dir`, if previously recorded.
pub fn read_project_peak_rss_mb(project_dir: &Path) -> Option<u64> {
    let raw = fs::read(project_peak_rss_cache_path(project_dir)).ok()?;
    let rec: PersistedPeakRss = serde_json::from_slice(&raw).ok()?;
    let mb = rec.peak_rss_kib / 1024;
    (mb > 0).then_some(mb)
}

/// Best-effort atomic persistence of the high-water peak RSS (KiB) for `project_dir` under
/// `cache_root()`: a smaller (e.g. cache-hit) run never lowers a previously recorded peak.
pub fn record_project_peak_rss_kib(project_dir: &Path, peak_rss_kib: u64) {
    let path = project_peak_rss_cache_path(project_dir);
    let existing = fs::read(&path)
        .ok()
        .and_then(|raw| serde_json::from_slice::<PersistedPeakRss>(&raw).ok())
        .map_or(0, |rec| rec.peak_rss_kib);
    if peak_rss_kib <= existing {
        return;
    }
    if let Some(parent) = path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    if let Ok(bytes) = serde_json::to_vec(&PersistedPeakRss { peak_rss_kib }) {
        let _ = atomic_write_shm(&path, &bytes);
    }
}

/// Resolve the live historical peak RSS in MiB for pre-flight checking: the explicit
/// `TURBO_LEAN_HISTORICAL_PEAK_RSS_MB` override, else the larger of the prior JSON receipt at
/// `receipt_path` (rewritten every run, so it may hold a small cache-hit peak) and the persisted
/// per-project high-water mark under `cache_root()/peak_rss/`.
pub fn resolve_historical_peak_rss_mb(
    project_dir: Option<&Path>,
    receipt_path: Option<&Path>,
) -> Option<u64> {
    historical_peak_rss_mb_from_env().or_else(|| {
        receipt_path
            .and_then(read_receipt_peak_rss_mb)
            .max(project_dir.and_then(read_project_peak_rss_mb))
    })
}

/// Live pre-flight guard: `TURBO_LEAN_MAX_MEMORY_MB` (`--max-memory-mb`) and the optional
/// historical peak (falling back to `TURBO_LEAN_HISTORICAL_PEAK_RSS_MB`) against this process'
/// effective cgroup `memory.max`. Disabled by `TURBO_LEAN_SKIP_MEMORY_PREFLIGHT=1`.
pub fn preflight_memory_guard_live(
    what: &str,
    historical_peak_rss_mb: Option<u64>,
) -> anyhow::Result<()> {
    if std::env::var("TURBO_LEAN_SKIP_MEMORY_PREFLIGHT").as_deref() == Ok("1") {
        return Ok(());
    }
    let max_memory_mb = std::env::var("TURBO_LEAN_MAX_MEMORY_MB")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .filter(|&mb| mb > 0);
    let effective_peak_mb = historical_peak_rss_mb.or_else(historical_peak_rss_mb_from_env);
    preflight_memory_guard(
        what,
        effective_peak_mb,
        max_memory_mb,
        effective_cgroup_memory_max_bytes(),
    )
}

/// Outstanding (not yet recovered) failed child `ExitStatus`es of this invocation.
static FAILED_CHILD_STATUSES: std::sync::Mutex<Vec<std::process::ExitStatus>> =
    std::sync::Mutex::new(Vec::new());

fn failed_child_statuses() -> std::sync::MutexGuard<'static, Vec<std::process::ExitStatus>> {
    FAILED_CHILD_STATUSES
        .lock()
        .unwrap_or_else(|e| e.into_inner())
}

fn child_status_severity(status: &std::process::ExitStatus) -> u8 {
    if status.success() {
        return 0;
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if status.signal() == Some(libc::SIGKILL) || status.code() == Some(128 + libc::SIGKILL) {
            return 3;
        }
        if status.signal().is_some() {
            return 2;
        }
    }
    #[cfg(not(unix))]
    if status.code() == Some(137) {
        return 3;
    }
    1
}

/// Record a failed child's `ExitStatus` for parent invocation receipt emission.
pub fn record_child_exit_status(status: std::process::ExitStatus) {
    if child_status_severity(&status) > 0 {
        failed_child_statuses().push(status);
    }
}

/// Withdraw one recorded failure equal to `status` once the caller has recovered from it (worker
/// respawn + replay, closure-to-single-module fallback, audit bisection), so a recovered
/// `SIGKILL` never bleeds into the receipt or exit code of an unrelated later failure.
pub fn forgive_child_exit_status(status: &std::process::ExitStatus) {
    let mut guard = failed_child_statuses();
    if let Some(i) = guard.iter().rposition(|s| s == status) {
        guard.remove(i);
    }
}

/// Take the highest-severity outstanding failed child `ExitStatus` (`SIGKILL` / exit `137`, then
/// other signals, then non-zero exits; latest wins ties) and clear the ledger.
pub fn take_recorded_child_exit_status() -> Option<std::process::ExitStatus> {
    std::mem::take(&mut *failed_child_statuses())
        .into_iter()
        .max_by_key(child_status_severity)
}

/// Clear any recorded child `ExitStatus` (called at invocation startup and in tests).
pub fn reset_recorded_child_exit_status() {
    failed_child_statuses().clear();
}

/// Structured JSON build / OOM receipt, emitted for every child invocation including children
/// killed by `SIGKILL` (cgroup OOM killer) or aborted with `SIGABRT`.
#[derive(Debug, Clone, Default, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct BuildReceipt {
    pub exit_code: Option<i32>,
    pub signal: Option<i32>,
    pub peak_rss_kib: Option<u64>,
    pub cgroup_oom_kill: Option<u64>,
    pub elapsed_s: f64,
    pub olean_sha256: Option<String>,
    /// `true` when the child was `SIGKILL`ed (or exited `137`) or the cgroup `oom_kill` counter advanced.
    pub oom_suspected: bool,
}

impl BuildReceipt {
    /// Build a receipt from a finished child's `ExitStatus`. `cgroup_oom_kill` is the delta of the
    /// cgroup `oom_kill` counter across the run (when known); `olean` is hashed when it exists.
    pub fn from_exit_status(
        status: &std::process::ExitStatus,
        elapsed: std::time::Duration,
        peak_rss_kib: Option<u64>,
        cgroup_oom_kill: Option<u64>,
        olean: Option<&Path>,
    ) -> Self {
        #[cfg(unix)]
        let signal = {
            use std::os::unix::process::ExitStatusExt;
            status.signal()
        };
        #[cfg(not(unix))]
        let signal: Option<i32> = None;
        let exit_code = status.code();
        #[cfg(unix)]
        let killed = signal == Some(libc::SIGKILL) || exit_code == Some(128 + libc::SIGKILL);
        #[cfg(not(unix))]
        let killed = exit_code == Some(137);
        Self {
            exit_code,
            signal,
            peak_rss_kib,
            cgroup_oom_kill,
            elapsed_s: elapsed.as_secs_f64(),
            olean_sha256: olean
                .filter(|p| p.is_file())
                .and_then(|p| sha256_file_hex(p).ok()),
            oom_suspected: killed || cgroup_oom_kill.is_some_and(|n| n > 0),
        }
    }

    /// Build a parent-invocation receipt, preferring a real child `ExitStatus` (explicit or
    /// recorded on failure) so `SIGKILL` / exit `137` and signal terminations are faithfully
    /// reported instead of collapsed to a generic `exit_code: 1, signal: None`.
    #[allow(clippy::too_many_arguments)]
    pub fn for_invocation(
        ok: bool,
        explicit_status: Option<&std::process::ExitStatus>,
        recorded_child_status: Option<&std::process::ExitStatus>,
        fallback_exit_code: Option<i32>,
        elapsed: std::time::Duration,
        peak_rss_kib: Option<u64>,
        cgroup_oom_kill: Option<u64>,
        olean: Option<&Path>,
    ) -> Self {
        if let Some(status) = explicit_status {
            return Self::from_exit_status(status, elapsed, peak_rss_kib, cgroup_oom_kill, olean);
        }
        if !ok {
            if let Some(status) = recorded_child_status {
                return Self::from_exit_status(
                    status,
                    elapsed,
                    peak_rss_kib,
                    cgroup_oom_kill,
                    olean,
                );
            }
        }
        let exit_code = Some(if ok {
            0
        } else {
            fallback_exit_code.unwrap_or(1)
        });
        Self {
            exit_code,
            signal: None,
            peak_rss_kib,
            cgroup_oom_kill,
            elapsed_s: elapsed.as_secs_f64(),
            olean_sha256: olean
                .filter(|p| p.is_file())
                .and_then(|p| sha256_file_hex(p).ok()),
            oom_suspected: exit_code == Some(137) || cgroup_oom_kill.is_some_and(|n| n > 0),
        }
    }
}

/// Lowercase hex SHA-256 of the file at `path`.
pub fn sha256_file_hex(path: &Path) -> std::io::Result<String> {
    use sha2::Digest;
    let mut hasher = sha2::Sha256::new();
    std::io::copy(&mut fs::File::open(path)?, &mut hasher)?;
    Ok(hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect())
}

#[cfg(unix)]
fn getrusage_maxrss_kib(who: libc::c_int) -> Option<u64> {
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    if unsafe { libc::getrusage(who, &mut usage) } != 0 {
        return None;
    }
    let raw = u64::try_from(usage.ru_maxrss).ok()?;
    // macOS reports bytes, Linux KiB.
    Some(if cfg!(target_os = "macos") {
        raw / 1024
    } else {
        raw
    })
}

/// Peak RSS in KiB over all waited-for children of this process (`getrusage(RUSAGE_CHILDREN)`).
pub fn children_peak_rss_kib() -> Option<u64> {
    #[cfg(unix)]
    {
        getrusage_maxrss_kib(libc::RUSAGE_CHILDREN)
    }
    #[cfg(not(unix))]
    {
        None
    }
}

/// Peak RSS in KiB of this process itself (`getrusage(RUSAGE_SELF)`).
pub fn self_peak_rss_kib() -> Option<u64> {
    #[cfg(unix)]
    {
        getrusage_maxrss_kib(libc::RUSAGE_SELF)
    }
    #[cfg(not(unix))]
    {
        None
    }
}

/// Atomically (write-then-rename) persist `receipt` as pretty JSON at `path`.
pub fn write_build_receipt_atomic(path: &Path, receipt: &BuildReceipt) -> std::io::Result<()> {
    let bytes = serde_json::to_vec_pretty(receipt).map_err(std::io::Error::other)?;
    if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
        fs::create_dir_all(parent)?;
    }
    atomic_write_shm(path, &bytes)
}

/// Spawn `cmd`, wait for it (whatever signal kills it), and atomically emit a `BuildReceipt` at
/// `receipt_path` before returning the captured output.
pub fn run_command_with_receipt(
    cmd: &mut std::process::Command,
    receipt_path: &Path,
    olean: Option<&Path>,
) -> std::io::Result<(std::process::Output, BuildReceipt)> {
    let oom_before = current_cgroup_oom_kill_count();
    let started = std::time::Instant::now();
    let output = cmd.output()?;
    if !output.status.success() {
        record_child_exit_status(output.status);
    }
    let elapsed = started.elapsed();
    let cgroup_oom_kill = cgroup_oom_kill_delta(oom_before, current_cgroup_oom_kill_count());
    let receipt = BuildReceipt::from_exit_status(
        &output.status,
        elapsed,
        children_peak_rss_kib(),
        cgroup_oom_kill,
        olean,
    );
    write_build_receipt_atomic(receipt_path, &receipt)?;
    Ok((output, receipt))
}

fn parse_cgroup_memory_limit_mb() -> Option<u64> {
    let bytes = effective_cgroup_memory_max_bytes()?;
    let mb = bytes / (1024 * 1024);
    (mb > 0).then(|| (mb.saturating_mul(3) / 4).max(1))
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

    if let Ok(out) = crate::trusted_tools::system_command("vm_stat")
        .and_then(|mut command| command.output().map_err(Into::into))
    {
        if out.status.success() {
            let text = String::from_utf8_lossy(&out.stdout);
            if let Some(budget_mb) = parse_macos_vm_stat_budget_mb(&text) {
                return budget_mb;
            }
        }
    }
    if let Ok(out) = crate::trusted_tools::system_command("sysctl").and_then(|mut command| {
        command
            .args(["-n", "hw.memsize"])
            .output()
            .map_err(Into::into)
    }) {
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
        if is_staging_lease_held_on_self_or_ancestor(&path, shm_dir) {
            continue;
        }
        let Some(file_name) = path.file_name() else {
            continue;
        };
        let dest_path = disk_spill_dir.join(file_name);
        let tmp_dest = stage_unique_tmp_path(&dest_path)?;
        let move_res = fs::copy(&path, &tmp_dest)
            .and_then(|_| fs::rename(&tmp_dest, &dest_path))
            .and_then(|_| {
                if try_remove_unleased_staged_file(&path) {
                    Ok(())
                } else {
                    Err(std::io::Error::new(
                        std::io::ErrorKind::WouldBlock,
                        "staging file leased during spill",
                    ))
                }
            });
        match move_res {
            Ok(()) => {
                total_size = total_size.saturating_sub(sz);
                spilled_files += 1;
                spilled_bytes = spilled_bytes.saturating_add(sz);
            }
            Err(e) => {
                let _ = fs::remove_file(&tmp_dest);
                if e.kind() == std::io::ErrorKind::WouldBlock {
                    let _ = fs::remove_file(&dest_path);
                }
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
    use std::os::unix::fs::PermissionsExt;

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
        let guard = super::acquire_publish_flock(&root, false, true)?;
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
            let reader = super::acquire_publish_flock(&project, false, true)?;
            let alias_reader = super::acquire_publish_flock(&root.join("alias"), false, true)?;
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
                drop(super::acquire_publish_flock(&project, true, true)?);
                assert_eq!(before, snapshot(&project)?);
                let lock = project.join(".lake/build/.turbo_publish.lock");
                std::fs::write(&lock, b"legacy")?;
                use std::os::unix::fs::PermissionsExt;
                std::fs::set_permissions(lock, std::fs::Permissions::from_mode(0o444))?;
            } else {
                let before = snapshot(&project)?;
                drop(super::acquire_publish_flock(&project, true, true)?);
                assert_eq!(before, snapshot(&project)?);
            }
        }
        std::fs::remove_dir_all(root)?;
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_publish_flock_and_atomic_write_support_symlinked_lake_build_dir() -> anyhow::Result<()>
    {
        let root = std::env::temp_dir().join(format!(
            "turbo_pub_symlink_build_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&root);
        let project = root.join("project");
        let sticky_build = root.join("sticky_build");
        let outside = root.join("outside");
        fs::create_dir_all(project.join(".lake"))?;
        fs::create_dir_all(&sticky_build)?;
        fs::create_dir_all(&outside)?;
        std::os::unix::fs::symlink(&sticky_build, project.join(".lake/build"))?;

        let pub_guard = super::acquire_publish_flock(&project, true, false)?;
        assert!(sticky_build.join(".turbo_publish.lock").is_file());
        drop(pub_guard);

        let manifest_path = project.join(".lake/build/.turbo_verified_manifest.json");
        super::atomic_write_shm(&manifest_path, b"{\"ok\":true}")?;
        assert_eq!(
            fs::read(sticky_build.join(".turbo_verified_manifest.json"))?,
            b"{\"ok\":true}"
        );

        // Leaf lockfile symlinks inside symlinked `.lake/build` still fail closed via O_NOFOLLOW.
        let planted_lock = project.join(".lake/build/.turbo_publish.lock");
        fs::remove_file(&planted_lock)?;
        std::os::unix::fs::symlink(outside.join("escaped_lock"), &planted_lock)?;
        assert!(super::acquire_publish_flock(&project, true, false).is_err());
        assert!(!outside.join("escaped_lock").exists());

        // Meanwhile, symlinked private `staging` directories still fail closed.
        let real_staging = root.join("real_staging");
        fs::create_dir_all(&real_staging)?;
        let symlink_staging = root.join("store").join("staging");
        fs::create_dir_all(symlink_staging.parent().unwrap())?;
        std::os::unix::fs::symlink(&real_staging, &symlink_staging)?;
        assert!(super::acquire_flock(&symlink_staging.join("x.lock"), true, false).is_err());
        assert!(super::atomic_write_shm(&symlink_staging.join("x.json"), b"{}").is_err());

        fs::remove_dir_all(&root)?;
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
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&base_dir, fs::Permissions::from_mode(0o700))?;
            fs::set_permissions(&shm_dir, fs::Permissions::from_mode(0o700))?;
        }

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

    #[cfg(unix)]
    #[test]
    fn test_staged_temp_file_reserve_races_cleanup_and_gc_without_orphaned_lease(
    ) -> anyhow::Result<()> {
        use std::sync::{
            atomic::{AtomicBool, Ordering},
            Arc, Barrier,
        };
        let root = std::env::temp_dir().join(format!(
            "turbo_lease_race_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&root);
        let store_root = root.join("store");
        let staging = store_root.join("staging");
        let spill = root.join("spill");
        let _ = crate::db::TurboStore::open(Some(&store_root))?;

        // 1. Deterministic step-by-step interleaving of the exact P2 #3 window:
        //    (a) Parent-directory shared lock (`lock_staging_parent_dir(..., false)`) blocks
        //        concurrent `reap_stale_lock_if_unheld` / `try_remove_unleased_staged_file`
        //        (`LOCK_EX | LOCK_NB` on the parent directory) while a writer is between
        //        `open(.lease.lock)` and `flock(LOCK_SH)` in `StagedTempFile::reserve` / `write`.
        //    (b) Even if an external unlink replaces `.lease.lock` between `open()` and `flock()`,
        //        `acquire_staging_lease` detects `!inode_matches_nofollow` and retries to re-bind
        //        to a live sidecar inode.
        let det_target = staging.join("deterministic_race.lean");
        let det_lock = staging_lease_lock_path(&det_target);
        fs::create_dir_all(&staging)?;
        fs::set_permissions(&staging, fs::Permissions::from_mode(0o700))?;
        let reaper_blocked_mid_open = std::rc::Rc::new(std::cell::Cell::new(false));
        let reaper_flag = reaper_blocked_mid_open.clone();
        let det_target_for_hook = det_target.clone();
        let store_root_for_hook = store_root.clone();
        AFTER_SIDECAR_OPEN_HOOK.with(|h| {
            *h.borrow_mut() = Some(std::rc::Rc::new(move |lp| {
                if !reaper_flag.get() {
                    reaper_flag.set(true);
                    assert!(
                        !reap_stale_lock_if_unheld(lp),
                        "reap_stale_lock_if_unheld must be blocked while writer is mid-acquisition"
                    );
                    assert!(
                        !try_remove_unleased_staged_file(&det_target_for_hook),
                        "try_remove_unleased_staged_file must be blocked while writer is mid-acquisition"
                    );
                    let lp_thread = lp.to_path_buf();
                    let gc_root = store_root_for_hook.clone();
                    std::thread::spawn(move || {
                        assert!(
                            !reap_stale_lock_if_unheld(&lp_thread),
                            "cross-thread reap_stale_lock_if_unheld must not unlink sidecar mid-acquisition"
                        );
                        let mut gc_s = crate::db::TurboStore::open(Some(&gc_root))
                            .expect("open TurboStore for mid-acquisition run_gc(0)");
                        gc_s.run_gc(0, 7 * 86400, false)
                            .expect("run_gc(0) during mid-acquisition");
                    })
                    .join()
                    .expect("join mid-acquisition GC thread");
                    assert!(
                        lp.exists(),
                        "sidecar inode must remain stable on disk while writer is mid-acquisition"
                    );
                }
            }));
        });
        let reserved_stable = StagedTempFile::reserve(det_target.clone())?;
        AFTER_SIDECAR_OPEN_HOOK.with(|h| *h.borrow_mut() = None);
        assert!(reaper_blocked_mid_open.get());
        assert!(is_staging_lease_held(&det_target) && det_lock.exists());
        drop(reserved_stable);
        assert!(!det_target.exists() && !det_lock.exists());

        let retry_triggered = std::rc::Rc::new(std::cell::Cell::new(0u32));
        let retry_counter = retry_triggered.clone();
        AFTER_SIDECAR_OPEN_HOOK.with(|h| {
            *h.borrow_mut() = Some(std::rc::Rc::new(move |lp| {
                let c = retry_counter.get();
                retry_counter.set(c + 1);
                if c == 0 {
                    fs::remove_file(lp).expect("direct unlink to exercise retry loop");
                }
            }));
        });
        let leased = StagedTempFile::write(det_target.clone(), b"-- active staged source\n")?;
        AFTER_SIDECAR_OPEN_HOOK.with(|h| *h.borrow_mut() = None);
        assert_eq!(
            retry_triggered.get(),
            2,
            "acquire_staging_lease must detect unlinked sidecar on attempt 0 and succeed on retry attempt 1"
        );
        assert!(is_staging_lease_held(&det_target));
        assert!(!reap_stale_lock_if_unheld(&det_lock));
        assert!(!try_remove_unleased_staged_file(&det_target));
        drop(leased);
        assert!(!det_target.exists() && !det_lock.exists());

        // 1b. Planted symlink protection on BOTH the staged payload target AND its `.lease.lock` sidecar:
        //     `StagedTempFile::write` and `StagedTempFile::reserve` must reject symlinks without
        //     modifying or truncating the symlink referent.
        let victim = root.join("victim_outside_staging.txt");
        fs::write(&victim, b"untouched-victim-bytes")?;
        let sym_target = staging.join("planted_symlink.lean");
        std::os::unix::fs::symlink(&victim, &sym_target)?;
        assert!(
            StagedTempFile::write(sym_target.clone(), b"attacker-overwrite").is_err(),
            "StagedTempFile::write must refuse planted payload symlink"
        );
        assert!(
            StagedTempFile::reserve(sym_target.clone()).is_err(),
            "StagedTempFile::reserve must refuse planted payload symlink"
        );
        assert_eq!(
            fs::read(&victim)?,
            b"untouched-victim-bytes",
            "planted payload symlink referent must remain untouched"
        );
        fs::remove_file(&sym_target)?;

        let clean_target = staging.join("clean_with_sym_lock.lean");
        let sym_lock = staging_lease_lock_path(&clean_target);
        std::os::unix::fs::symlink(&victim, &sym_lock)?;
        assert!(
            StagedTempFile::reserve(clean_target.clone()).is_err(),
            "StagedTempFile::reserve must refuse planted sidecar symlink"
        );
        assert_eq!(fs::read(&victim)?, b"untouched-victim-bytes");
        fs::remove_file(&sym_lock)?;

        // 1c. Hardlinked payload & retained writable descriptor isolation (`P2` regression):
        //     If a staging path `P` is a hardlink to an ordinary writable file `V` (and/or has a
        //     pre-existing open writable descriptor), `StagedTempFile::reserve`, `write`, and
        //     `overwrite` MUST allocate a fresh inode and atomically replace `P` instead of
        //     truncating `V` in place, and subsequent writes through the retained fd must not
        //     alter the staged payload.
        {
            use std::io::{Seek, Write};
            use std::os::unix::fs::MetadataExt;
            let hardlink_victim = root.join("ordinary_hardlinked_victim.lean");
            let victim_orig = b"valuable-external-file-must-not-truncate".to_vec();
            let mut retained_victim_fd = fs::OpenOptions::new()
                .create(true)
                .truncate(true)
                .read(true)
                .write(true)
                .open(&hardlink_victim)?;
            retained_victim_fd.write_all(&victim_orig)?;
            let victim_ino = retained_victim_fd.metadata()?.ino();

            let planted_hl_reserve = staging.join("planted_hardlink_reserve.lean");
            fs::hard_link(&hardlink_victim, &planted_hl_reserve)?;
            let reserved = StagedTempFile::reserve(planted_hl_reserve.clone())?;
            assert_eq!(
                fs::read(&hardlink_victim)?,
                victim_orig,
                "StagedTempFile::reserve must never truncate a hardlinked sibling file"
            );
            assert_ne!(
                fs::metadata(reserved.path())?.ino(),
                victim_ino,
                "StagedTempFile::reserve must bind a fresh isolated payload inode"
            );
            assert_eq!(fs::read(reserved.path())?, b"");
            reserved.overwrite(b"-- staged payload v1\n")?;
            assert_eq!(
                fs::read(&hardlink_victim)?,
                victim_orig,
                "StagedTempFile::overwrite must leave hardlinked sibling untouched"
            );
            retained_victim_fd.seek(std::io::SeekFrom::Start(0))?;
            retained_victim_fd.write_all(b"external-writer-mutates-old-inode!!!!!!!")?;
            assert_eq!(
                fs::read(reserved.path())?,
                b"-- staged payload v1\n",
                "retained writable fd on replaced inode must never alter leased staged payload"
            );
            drop(reserved);

            // Also verify `StagedTempFile::write` directly against a pre-existing hardlinked path.
            fs::write(&hardlink_victim, &victim_orig)?;
            let planted_hl_write = staging.join("planted_hardlink_write.lean");
            fs::hard_link(&hardlink_victim, &planted_hl_write)?;
            let written = StagedTempFile::write(planted_hl_write.clone(), b"-- direct write\n")?;
            assert_eq!(fs::read(&hardlink_victim)?, victim_orig);
            assert_eq!(fs::read(written.path())?, b"-- direct write\n");
            drop(written);
        }

        // 2. Multi-threaded stress race: writers repeatedly `reserve` + write + hold + verify
        //    against concurrent `reap_stale_lock_if_unheld`, `try_remove_unleased_staged_file`,
        //    `enforce_shm_quota_lru`, `spill_shm_to_disk_dir`, and `TurboStore::run_gc(0, ...)`.
        let slots: Arc<Vec<PathBuf>> = Arc::new(
            (0..4)
                .map(|i| staging.join(format!("slot_{i}.lean")))
                .collect(),
        );
        let stop = Arc::new(AtomicBool::new(false));
        let barrier = Arc::new(Barrier::new(7));
        let mut handles = Vec::new();

        for (wi, slot) in slots.iter().cloned().enumerate() {
            let bar = Arc::clone(&barrier);
            let stop_flag = Arc::clone(&stop);
            handles.push(std::thread::spawn(move || -> anyhow::Result<()> {
                bar.wait();
                for iter in 0..120u32 {
                    let g = StagedTempFile::reserve(slot.clone())?;
                    let lock_p = staging_lease_lock_path(g.path());
                    anyhow::ensure!(
                        is_staging_lease_held(g.path()),
                        "writer {wi} iter {iter}: lease not discoverable right after reserve"
                    );
                    let payload = format!("-- writer {wi} iter {iter}\n");
                    g.overwrite(payload.as_bytes())?;
                    std::thread::yield_now();
                    anyhow::ensure!(
                        is_staging_lease_held(g.path()) && lock_p.exists(),
                        "writer {wi} iter {iter}: sidecar unlinked while lease held"
                    );
                    let got = fs::read(g.path())?;
                    anyhow::ensure!(
                        got == payload.as_bytes(),
                        "writer {wi} iter {iter}: active staged file mutated or truncated"
                    );
                    drop(g);
                }
                stop_flag.store(true, Ordering::Release);
                Ok(())
            }));
        }

        for cleaner_id in 0..2usize {
            let bar = Arc::clone(&barrier);
            let stop_flag = Arc::clone(&stop);
            let paths = Arc::clone(&slots);
            let staging_dir = staging.clone();
            let spill_dir = spill.join(format!("c{cleaner_id}"));
            handles.push(std::thread::spawn(move || -> anyhow::Result<()> {
                bar.wait();
                while !stop_flag.load(Ordering::Acquire) {
                    for p in paths.iter() {
                        let lp = staging_lease_lock_path(p);
                        let _ = reap_stale_lock_if_unheld(&lp);
                        let _ = try_remove_unleased_staged_file(p);
                    }
                    let _ = enforce_shm_quota_lru(&staging_dir, 1);
                    let _ = spill_shm_to_disk_dir(&staging_dir, &spill_dir, 0);
                }
                Ok(())
            }));
        }

        {
            let bar = Arc::clone(&barrier);
            let stop_flag = Arc::clone(&stop);
            let gc_root = store_root.clone();
            handles.push(std::thread::spawn(move || -> anyhow::Result<()> {
                let mut gc_store = crate::db::TurboStore::open(Some(&gc_root))?;
                bar.wait();
                while !stop_flag.load(Ordering::Acquire) {
                    let _ = gc_store.run_gc(0, 7 * 86400, true);
                    std::thread::yield_now();
                }
                Ok(())
            }));
        }

        for h in handles {
            h.join().expect("race thread panicked")?;
        }

        let _ = fs::remove_dir_all(&root);
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_private_shm_trust_boundary_rejects_unverified_dirs_files_and_symlinks(
    ) -> anyhow::Result<()> {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};

        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let root = std::env::temp_dir().join(format!(
            "turbo_private_shm_boundary_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root)?;

        let prev_staging = std::env::var_os("TURBO_LEAN_STAGING_DIR");
        let run_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
            || -> anyhow::Result<()> {
                let staging = root.join("staging");
                std::env::set_var("TURBO_LEAN_STAGING_DIR", &staging);

                // 1. Normal write & read roundtrip creates `0o700` dirs and `0o600` files.
                write_verified_private_shm_file("test_sub", "ok.json", b"{\"ok\":true}")?;
                assert_eq!(
                    fs::symlink_metadata(&staging)?.mode() & 0o777,
                    0o700,
                    "staging root must be 0o700"
                );
                assert_eq!(
                    fs::symlink_metadata(staging.join("test_sub"))?.mode() & 0o777,
                    0o700,
                    "staging subdir must be 0o700"
                );
                assert_eq!(
                    fs::symlink_metadata(staging.join("test_sub/ok.json"))?.mode() & 0o777,
                    0o600,
                    "private shm file must be 0o600"
                );
                assert_eq!(
                    read_verified_private_shm_file("test_sub", "ok.json").as_deref(),
                    Some(&b"{\"ok\":true}"[..])
                );

                // Build minimal valid `.olean` bytes >64 KiB (`Init` import, `is_module = true`).
                let make_valid_large_olean = || -> Vec<u8> {
                    let mut b = vec![0u8; 70_000];
                    b[0..5].copy_from_slice(b"olean");
                    b[5] = 2;
                    let base: u64 = 0x1000_0000;
                    b[80..88].copy_from_slice(&base.to_le_bytes());
                    let root_off = 96usize;
                    let arr_off = 160usize;
                    let imp_off = 200usize;
                    let name_off = 232usize;
                    let str_off = 264usize;
                    b[88..96].copy_from_slice(&(base + root_off as u64).to_le_bytes());
                    b[root_off + 6] = 5;
                    b[root_off + 7] = 0;
                    b[root_off + 8..root_off + 16]
                        .copy_from_slice(&(base + arr_off as u64).to_le_bytes());
                    b[root_off + 48] = 1; // is_module = true
                    b[arr_off + 7] = 246;
                    b[arr_off + 8..arr_off + 16].copy_from_slice(&1u64.to_le_bytes());
                    b[arr_off + 24..arr_off + 32]
                        .copy_from_slice(&(base + imp_off as u64).to_le_bytes());
                    b[imp_off + 6] = 1;
                    b[imp_off + 7] = 0;
                    b[imp_off + 8..imp_off + 16]
                        .copy_from_slice(&(base + name_off as u64).to_le_bytes());
                    b[imp_off + 16] = 1;
                    b[imp_off + 17] = 1;
                    b[imp_off + 18] = 0;
                    b[name_off + 7] = 1;
                    b[name_off + 8..name_off + 16].copy_from_slice(&1u64.to_le_bytes());
                    b[name_off + 16..name_off + 24]
                        .copy_from_slice(&(base + str_off as u64).to_le_bytes());
                    b[str_off + 7] = 249;
                    b[str_off + 8..str_off + 16].copy_from_slice(&5u64.to_le_bytes());
                    b[str_off + 32..str_off + 36].copy_from_slice(b"Init");
                    b[str_off + 36] = 0;
                    b
                };

                // Fixture files: source with forbidden `sorry` and real >64KiB `.olean`.
                let lean_src = root.join("BadHygiene.lean");
                fs::write(&lean_src, "theorem forged_bad : False := sorry\n")?;
                let olean_path = root.join("RealMod.olean");
                fs::write(&olean_path, make_valid_large_olean())?;
                // Age past STAT_TRUST_WINDOW_NS (2s) so trusted SHM memoization persists entries.
                std::thread::sleep(std::time::Duration::from_millis(2200));

                // Populate legitimate `0o600` cache entries across all three subdirs first.
                crate::module_builder::reset_lake_inputs_tag_memo();
                crate::lake_build::clear_olean_interface_memo();
                let real_hyg = crate::module_builder::load_source_hygiene_cached(&lean_src)?;
                assert!(
                    !real_hyg.is_clean_for_certification(),
                    "real source has sorry and must not be clean"
                );
                let real_meta_dig =
                    crate::module_builder::compute_replayed_olean_ilean_digest(&olean_path)?;
                let (real_imps, real_is_mod) =
                    crate::module_builder::read_olean_binary_imports_cached(&olean_path)?;
                assert_eq!(real_imps.len(), 1);
                assert_eq!(real_imps[0].module, "Init");
                assert!(real_is_mod);
                let comp_paths = crate::lake_build::single_olean_companion_paths(&olean_path);
                let cur_stats =
                    crate::lake_build::single_olean_stat_bundle(&olean_path, &comp_paths);
                let (real_iface_dig, real_iface_deps, _) =
                    crate::lake_build::compute_single_olean_digest_and_imports_with_stats(
                        &olean_path,
                        &comp_paths,
                        cur_stats,
                    )
                    .expect("compute_single_olean_digest_and_imports_with_stats");
                assert_eq!(real_iface_deps, vec!["Init".to_string()]);

                let sh_key = &blake3::hash(lean_src.to_string_lossy().as_bytes())
                    .to_hex()
                    .to_string()[..28];
                let sh_path = staging
                    .join("src_hygiene_v2")
                    .join(format!("sh_{sh_key}.json"));
                let om_key = &blake3::hash(olean_path.to_string_lossy().as_bytes())
                    .to_hex()
                    .to_string()[..28];
                let om_path = staging
                    .join("olean_meta_v2")
                    .join(format!("om_{om_key}.json"));
                let oi_path = staging
                    .join("olean_iface_v2")
                    .join(format!("oi_{om_key}.json"));
                assert_eq!(fs::symlink_metadata(&sh_path)?.mode() & 0o777, 0o600);
                assert_eq!(fs::symlink_metadata(&om_path)?.mode() & 0o777, 0o600);
                assert_eq!(fs::symlink_metadata(&oi_path)?.mode() & 0o777, 0o600);

                // Craft forged JSON payloads preserving exact `stat`/`stats`/`sample_key` fields.
                let mut forged_sh: serde_json::Value =
                    serde_json::from_slice(&fs::read(&sh_path)?)?;
                forged_sh["hygiene"] = serde_json::to_value(crate::splitter::audit_hygiene(
                    "theorem ok : True := trivial\n",
                ))?;
                let forged_sh_bytes = serde_json::to_vec(&forged_sh)?;

                let mut forged_om: serde_json::Value =
                    serde_json::from_slice(&fs::read(&om_path)?)?;
                forged_om["digest"] = serde_json::json!("forged_meta_digest_0000");
                forged_om["imports"] = serde_json::json!([[], false]);
                let forged_om_bytes = serde_json::to_vec(&forged_om)?;

                let mut forged_oi: serde_json::Value =
                    serde_json::from_slice(&fs::read(&oi_path)?)?;
                forged_oi["digest"] = serde_json::json!("forged_iface_digest_0000");
                forged_oi["deps"] = serde_json::json!(["ForgedDep"]);
                let forged_oi_bytes = serde_json::to_vec(&forged_oi)?;

                let assert_all_caches_miss_and_recompute_truth = || -> anyhow::Result<()> {
                    crate::module_builder::reset_lake_inputs_tag_memo();
                    crate::lake_build::clear_olean_interface_memo();
                    let h = crate::module_builder::load_source_hygiene_cached(&lean_src)?;
                    anyhow::ensure!(
                        !h.is_clean_for_certification(),
                        "forged src_hygiene_v2 entry was trusted!"
                    );
                    let md =
                        crate::module_builder::compute_replayed_olean_ilean_digest(&olean_path)?;
                    anyhow::ensure!(
                        md == real_meta_dig,
                        "forged olean_meta_v2 digest was trusted: {md}"
                    );
                    crate::module_builder::reset_lake_inputs_tag_memo();
                    let (imps, is_m) =
                        crate::module_builder::read_olean_binary_imports_cached(&olean_path)?;
                    anyhow::ensure!(
                        imps.len() == 1 && imps[0].module == "Init" && is_m,
                        "forged olean_meta_v2 binary imports were trusted: {imps:?}"
                    );
                    let (idig, ideps, _) =
                        crate::lake_build::compute_single_olean_digest_and_imports_with_stats(
                            &olean_path,
                            &comp_paths,
                            cur_stats,
                        )
                        .expect("recomputed iface digest");
                    anyhow::ensure!(
                        idig == real_iface_dig && ideps == real_iface_deps,
                        "forged olean_iface_v2 entry was trusted: {idig} / {ideps:?}"
                    );
                    Ok(())
                };

                // 2. Group/world-readable cache files (`0o644`) inside `0o700` dirs must be ignored
                //    WITHOUT mutating permissions when failing closed on read, then overwritten cleanly
                //    by legitimate `0o600` atomic writes. Also verify `read_verified_private_shm_file`
                //    directly refuses `0o644` without chmodding.
                fs::write(&sh_path, &forged_sh_bytes)?;
                fs::set_permissions(&sh_path, fs::Permissions::from_mode(0o644))?;
                assert!(
                    read_verified_private_shm_file(
                        "src_hygiene_v2",
                        sh_path.file_name().unwrap().to_str().unwrap()
                    )
                    .is_none(),
                    "0o644 file must fail closed"
                );
                assert_eq!(
                    fs::symlink_metadata(&sh_path)?.mode() & 0o777,
                    0o644,
                    "read_verified_private_shm_file must not mutate permissions of rejected files"
                );
                fs::write(&om_path, &forged_om_bytes)?;
                fs::set_permissions(&om_path, fs::Permissions::from_mode(0o644))?;
                fs::write(&oi_path, &forged_oi_bytes)?;
                fs::set_permissions(&oi_path, fs::Permissions::from_mode(0o644))?;
                assert_all_caches_miss_and_recompute_truth()?;

                // 3. `0o755` subdirectory or `0o755` staging root must be rejected (without chmodding!).
                fs::write(&sh_path, &forged_sh_bytes)?;
                fs::set_permissions(&sh_path, fs::Permissions::from_mode(0o600))?;
                fs::write(&om_path, &forged_om_bytes)?;
                fs::set_permissions(&om_path, fs::Permissions::from_mode(0o600))?;
                fs::write(&oi_path, &forged_oi_bytes)?;
                fs::set_permissions(&oi_path, fs::Permissions::from_mode(0o600))?;
                for sub in ["src_hygiene_v2", "olean_meta_v2", "olean_iface_v2"] {
                    fs::set_permissions(staging.join(sub), fs::Permissions::from_mode(0o755))?;
                }
                assert!(ensure_verified_private_staging_dir(Some("src_hygiene_v2")).is_none());
                assert_eq!(
                    fs::symlink_metadata(staging.join("src_hygiene_v2"))?.mode() & 0o777,
                    0o755,
                    "verify must never chmod an untrusted 0o755 directory"
                );
                assert_all_caches_miss_and_recompute_truth()?;
                for sub in ["src_hygiene_v2", "olean_meta_v2", "olean_iface_v2"] {
                    fs::set_permissions(staging.join(sub), fs::Permissions::from_mode(0o700))?;
                }

                // Now `0o755` on staging root itself:
                fs::write(&sh_path, &forged_sh_bytes)?;
                fs::set_permissions(&sh_path, fs::Permissions::from_mode(0o600))?;
                fs::write(&om_path, &forged_om_bytes)?;
                fs::set_permissions(&om_path, fs::Permissions::from_mode(0o600))?;
                fs::write(&oi_path, &forged_oi_bytes)?;
                fs::set_permissions(&oi_path, fs::Permissions::from_mode(0o600))?;
                fs::set_permissions(&staging, fs::Permissions::from_mode(0o755))?;
                assert!(ensure_verified_private_staging_dir(None).is_none());
                assert_all_caches_miss_and_recompute_truth()?;
                fs::set_permissions(&staging, fs::Permissions::from_mode(0o700))?;

                // 4. Symlinked cache files inside `0o700` subdirs must be ignored on read and
                //    refused on write (`write_verified_private_shm_file` returns Err, target untouched).
                let ext_target = root.join("ext_forged_payload.json");
                fs::write(&ext_target, &forged_sh_bytes)?;
                fs::set_permissions(&ext_target, fs::Permissions::from_mode(0o600))?;
                for (p, payload) in [
                    (&sh_path, &forged_sh_bytes),
                    (&om_path, &forged_om_bytes),
                    (&oi_path, &forged_oi_bytes),
                ] {
                    let ext =
                        root.join(format!("ext_{}", p.file_name().unwrap().to_string_lossy()));
                    fs::write(&ext, payload)?;
                    fs::set_permissions(&ext, fs::Permissions::from_mode(0o600))?;
                    let _ = fs::remove_file(p);
                    std::os::unix::fs::symlink(&ext, p)?;
                }
                assert!(
                    write_verified_private_shm_file(
                        "src_hygiene_v2",
                        sh_path.file_name().unwrap().to_str().unwrap(),
                        b"{}"
                    )
                    .is_err(),
                    "write_verified_private_shm_file must refuse symlink target"
                );
                assert_all_caches_miss_and_recompute_truth()?;

                // 4b. Hardlinked cache files (`nlink > 1`) inside `0o700` subdirs must be rejected
                //     on read (`read_verified_private_shm_file` returns `None`) and atomically
                //     unlinked/replaced via rename on write without mutating the external hardlink.
                for (p, payload) in [
                    (&sh_path, &forged_sh_bytes),
                    (&om_path, &forged_om_bytes),
                    (&oi_path, &forged_oi_bytes),
                ] {
                    let ext_hl = root.join(format!(
                        "ext_hl_{}",
                        p.file_name().unwrap().to_string_lossy()
                    ));
                    fs::write(&ext_hl, payload)?;
                    fs::set_permissions(&ext_hl, fs::Permissions::from_mode(0o600))?;
                    let _ = fs::remove_file(p);
                    fs::hard_link(&ext_hl, p)?;
                }
                assert!(
                    read_verified_private_shm_file(
                        "src_hygiene_v2",
                        sh_path.file_name().unwrap().to_str().unwrap()
                    )
                    .is_none(),
                    "read_verified_private_shm_file must reject hardlinked file (nlink > 1)"
                );
                assert_all_caches_miss_and_recompute_truth()?;
                for (p, payload) in [
                    (&sh_path, &forged_sh_bytes),
                    (&om_path, &forged_om_bytes),
                    (&oi_path, &forged_oi_bytes),
                ] {
                    let ext_hl = root.join(format!(
                        "ext_hl_{}",
                        p.file_name().unwrap().to_string_lossy()
                    ));
                    assert_eq!(
                        fs::read(&ext_hl)?,
                        *payload,
                        "atomic rename must not mutate external hardlink target"
                    );
                }

                // 5. Symlinked `TURBO_LEAN_STAGING_DIR` must be rejected by both private SHM
                //    helpers AND `TurboStore::fast_staging_dir()` (which must fall back to
                //    `<store_root>/staging` rather than returning the symlink).
                let real_target_dir = root.join("real_target_700");
                fs::create_dir_all(&real_target_dir)?;
                fs::set_permissions(&real_target_dir, fs::Permissions::from_mode(0o700))?;
                let symlink_staging = root.join("symlink_staging");
                std::os::unix::fs::symlink(&real_target_dir, &symlink_staging)?;
                std::env::set_var("TURBO_LEAN_STAGING_DIR", &symlink_staging);
                assert!(ensure_verified_private_staging_dir(None).is_none());
                assert!(
                    write_verified_private_shm_file("src_hygiene_v2", "x.json", b"{}").is_err()
                );
                let store_root = root.join("store_fallback");
                let store = crate::db::TurboStore::open(Some(&store_root))?;
                let resolved_fast = store.fast_staging_dir();
                assert_eq!(
                    resolved_fast,
                    store_root.join("staging"),
                    "TurboStore::fast_staging_dir must fall back to store_root/staging when staging_shm_dir is a symlink"
                );
                assert_eq!(fs::symlink_metadata(&resolved_fast)?.mode() & 0o777, 0o700);

                // Also verify `0o755` `TURBO_LEAN_STAGING_DIR` causes `fast_staging_dir()` fallback,
                // and `ensure_private_dir_all` / staging `acquire_flock` / `atomic_write_shm` refuse
                // pre-created `0o755` staging directories without chmodding them.
                let perm755_staging = root.join("perm755_staging");
                fs::create_dir_all(&perm755_staging)?;
                fs::set_permissions(&perm755_staging, fs::Permissions::from_mode(0o755))?;
                std::env::set_var("TURBO_LEAN_STAGING_DIR", &perm755_staging);
                assert_eq!(store.fast_staging_dir(), store_root.join("staging"));
                assert!(ensure_private_dir_all(&perm755_staging).is_err());
                assert!(acquire_flock(&perm755_staging.join("x.lock"), true, false).is_err());
                assert!(atomic_write_shm(&perm755_staging.join("x.json"), b"{}").is_err());
                let perm755_eval_sub = perm755_staging.join("eval_shm_cache");
                fs::create_dir_all(&perm755_eval_sub)?;
                fs::set_permissions(&perm755_eval_sub, fs::Permissions::from_mode(0o755))?;
                let planted_eval = perm755_eval_sub.join("planted.json");
                fs::write(&planted_eval, b"{}")?;
                fs::set_permissions(&planted_eval, fs::Permissions::from_mode(0o600))?;
                assert!(
                    read_verified_private_file_at(&planted_eval).is_none(),
                    "read_verified_private_file_at must reject 0755 staging/subdir"
                );
                assert!(
                    StagingLeaseGuard::acquire_for_target(&perm755_staging.join("x.lean")).is_err()
                );
                assert!(StagedTempFile::write(perm755_staging.join("x.lean"), b"x").is_err());
                assert_eq!(
                    fs::symlink_metadata(&perm755_staging)?.mode() & 0o777,
                    0o755,
                    "ensure_private_dir_all must not chmod an existing 0o755 directory"
                );
                // Meanwhile, `PrivateScratchDir` under `verified_private_temp_scratch_base()`
                // and under a `0o755` non-staging temporary directory must succeed cleanly.
                let priv_scratch_base = crate::check::verified_private_temp_scratch_base()?;
                assert_eq!(
                    fs::symlink_metadata(&priv_scratch_base)?.mode() & 0o777,
                    0o700
                );
                let psd_tmp =
                    crate::check::PrivateScratchDir::create(&priv_scratch_base, "turbo_tmp_test")?;
                assert_eq!(fs::symlink_metadata(&psd_tmp.path)?.mode() & 0o777, 0o700);
                drop(psd_tmp);
                let non_staging_755 = root.join("non_staging_755");
                fs::create_dir_all(&non_staging_755)?;
                fs::set_permissions(&non_staging_755, fs::Permissions::from_mode(0o755))?;
                let psd_755 =
                    crate::check::PrivateScratchDir::create(&non_staging_755, "turbo_755_test")?;
                assert_eq!(fs::symlink_metadata(&psd_755.path)?.mode() & 0o777, 0o700);
                drop(psd_755);

                // 6. Coarse-timestamp / trust-window regression across persistent SHM & in-memory
                //    replay-authority, interface, and source-hygiene caches:
                //    a same-length rewrite within a single 1s coarse timestamp tick must NEVER
                //    return a stale replay digest, binary-import list, artifact-set digest,
                //    single-olean interface digest, or source-hygiene / source-blake3 verdict.
                let private_staging = root.join("coarse_staging");
                std::env::set_var("TURBO_LEAN_STAGING_DIR", &private_staging);
                crate::zygote::digest_test_hooks::set_forced_ts_granularity_ns(Some(1_000_000_000));
                while crate::zygote::wall_clock_ns().rem_euclid(1_000_000_000) > 250_000_000 {
                    std::thread::sleep(std::time::Duration::from_millis(5));
                }
                let coarse_olean = root.join("CoarseReplay.olean");
                let mut olean_v1 = make_valid_large_olean();
                let mut olean_v2 = olean_v1.clone();
                // Same length (70_000 bytes), interior byte edit at offset 35_000 (outside 4 KiB head/tail sample!) AND different import (`Core` vs `Init`).
                olean_v1[35_000] = 0x11;
                olean_v2[35_000] = 0x22;
                olean_v2[264 + 32..264 + 36].copy_from_slice(b"Core");
                fs::write(&coarse_olean, &olean_v1)?;
                let coarse_src = root.join("CoarseHygiene.lean");
                // Same byte length (70_000 bytes, interior edit outside 4 KiB head/tail sample): clean vs sorry!
                let pad_prefix = format!("-- {}\n", "a".repeat(34_900));
                let pad_suffix = format!("-- {}\n", "b".repeat(35_050));
                let src_v1 =
                    format!("{pad_prefix}theorem coarse_t : True := trivial \n{pad_suffix}");
                let src_v2 =
                    format!("{pad_prefix}theorem coarse_t : True := by sorry\n{pad_suffix}");
                assert_eq!(src_v1.len(), src_v2.len());
                assert!(src_v1.len() > 65536);
                fs::write(&coarse_src, &src_v1)?;

                let d_v1 =
                    crate::module_builder::compute_replayed_olean_ilean_digest(&coarse_olean)?;
                let aset_v1 =
                    crate::module_builder::compute_olean_artifact_set_digest(&coarse_olean)?;
                let (imps_v1, _) =
                    crate::module_builder::read_olean_binary_imports_cached(&coarse_olean)?;
                let coarse_comp = crate::lake_build::single_olean_companion_paths(&coarse_olean);
                let (iface_v1, _, _) =
                    crate::lake_build::compute_single_olean_digest_and_imports_with_stats(
                        &coarse_olean,
                        &coarse_comp,
                        crate::lake_build::single_olean_stat_bundle(&coarse_olean, &coarse_comp),
                    )
                    .expect("coarse iface v1");
                let sb3_v1 = crate::lake_build::compute_cached_source_blake3(&coarse_src)
                    .expect("coarse src blake3 v1");
                let hyg_v1 = crate::module_builder::load_source_hygiene_cached(&coarse_src)?;
                assert_eq!(imps_v1[0].module, "Init");
                assert!(hyg_v1.is_clean_for_certification());

                // Same-length rewrite inside the same 1s tick (and within STAT_TRUST_WINDOW_NS):
                fs::write(&coarse_olean, &olean_v2)?;
                fs::write(&coarse_src, &src_v2)?;
                // Verify both in-memory (same memo window) AND across memo-window reset (SHM):
                for reset in [false, true] {
                    if reset {
                        crate::module_builder::reset_lake_inputs_tag_memo();
                    }
                    let d_v2 =
                        crate::module_builder::compute_replayed_olean_ilean_digest(&coarse_olean)?;
                    let aset_v2 =
                        crate::module_builder::compute_olean_artifact_set_digest(&coarse_olean)?;
                    let (imps_v2, _) =
                        crate::module_builder::read_olean_binary_imports_cached(&coarse_olean)?;
                    let (iface_v2, _, _) =
                        crate::lake_build::compute_single_olean_digest_and_imports_with_stats(
                            &coarse_olean,
                            &coarse_comp,
                            crate::lake_build::single_olean_stat_bundle(
                                &coarse_olean,
                                &coarse_comp,
                            ),
                        )
                        .expect("coarse iface v2");
                    let sb3_v2 = crate::lake_build::compute_cached_source_blake3(&coarse_src)
                        .expect("coarse src blake3 v2");
                    let hyg_v2 = crate::module_builder::load_source_hygiene_cached(&coarse_src)?;
                    assert_ne!(
                        d_v1, d_v2,
                        "same-length coarse-tick rewrite must rehash replay digest (reset={reset})"
                    );
                    assert_ne!(
                        aset_v1, aset_v2,
                        "same-length coarse-tick rewrite must rehash artifact-set digest (reset={reset})"
                    );
                    assert_ne!(
                        iface_v1, iface_v2,
                        "same-length coarse-tick interior rewrite must rehash single-olean interface digest (reset={reset})"
                    );
                    assert_ne!(
                        sb3_v1, sb3_v2,
                        "same-length coarse-tick interior rewrite must rehash cached source blake3 (reset={reset})"
                    );
                    assert_eq!(
                        imps_v2[0].module, "Core",
                        "same-length coarse-tick rewrite must re-parse binary imports (reset={reset})"
                    );
                    assert!(
                        !hyg_v2.is_clean_for_certification(),
                        "same-length coarse-tick rewrite must re-audit source hygiene (reset={reset})"
                    );
                }
                crate::zygote::digest_test_hooks::clear();
                Ok(())
            },
        ));
        #[cfg(test)]
        crate::zygote::digest_test_hooks::clear();
        match prev_staging {
            Some(v) => std::env::set_var("TURBO_LEAN_STAGING_DIR", v),
            None => std::env::remove_var("TURBO_LEAN_STAGING_DIR"),
        }
        let _ = fs::remove_dir_all(&root);
        match run_res {
            Ok(r) => r,
            Err(p) => std::panic::resume_unwind(p),
        }
    }

    #[test]
    fn test_shm_schema_v2_and_epoch_mismatch_rejected() -> anyhow::Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        assert_eq!(SHM_CACHE_SCHEMA_VERSION, 2);
        let prev_staging = std::env::var_os("TURBO_LEAN_STAGING_DIR");
        std::env::remove_var("TURBO_LEAN_STAGING_DIR");
        let default_dir = staging_shm_dir();
        if let Some(ref v) = prev_staging {
            std::env::set_var("TURBO_LEAN_STAGING_DIR", v);
        }
        assert!(default_dir
            .to_string_lossy()
            .ends_with(&format!("-{}", crate::build_epoch_short())));

        let root = std::env::temp_dir().join(format!(
            "turbo_lean_shm_epoch_mismatch_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let staging = root.join("staging");
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root)?;
        std::env::set_var("TURBO_LEAN_STAGING_DIR", &staging);

        let run_res =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> anyhow::Result<()> {
                let lean_src = root.join("EpochMod.lean");
                fs::write(&lean_src, "theorem forged_epoch : False := sorry\n")?;
                std::thread::sleep(std::time::Duration::from_millis(2200));
                crate::module_builder::reset_lake_inputs_tag_memo();
                let clean = crate::module_builder::load_source_hygiene_cached(&lean_src)?;
                assert!(!clean.is_clean_for_certification());

                let sh_key = &blake3::hash(lean_src.to_string_lossy().as_bytes())
                    .to_hex()
                    .to_string()[..28];
                let sh_file = format!("sh_{sh_key}.json");
                let raw = read_verified_private_shm_file("src_hygiene_v2", &sh_file)
                    .expect("legitimate shm hygiene entry");
                let mut val: serde_json::Value = serde_json::from_slice(&raw)?;
                assert_eq!(
                    val.get("epoch").and_then(|v| v.as_str()),
                    Some(crate::TURBO_LEAN_BUILD_EPOCH)
                );
                // Forge a clean hygiene report under a mismatched epoch; load must reject it and re-scan source.
                val["epoch"] = serde_json::Value::String("0".repeat(64));
                val["hygiene"]["sorry_count"] = serde_json::json!(0);
                write_verified_private_shm_file(
                    "src_hygiene_v2",
                    &sh_file,
                    &serde_json::to_vec(&val)?,
                )?;
                crate::module_builder::reset_lake_inputs_tag_memo();
                let rescan = crate::module_builder::load_source_hygiene_cached(&lean_src)?;
                assert!(
                    !rescan.is_clean_for_certification(),
                    "mismatched SHM epoch must be rejected and trigger fresh source scan"
                );
                Ok(())
            }));
        match prev_staging {
            Some(v) => std::env::set_var("TURBO_LEAN_STAGING_DIR", v),
            None => std::env::remove_var("TURBO_LEAN_STAGING_DIR"),
        }
        let _ = fs::remove_dir_all(&root);
        match run_res {
            Ok(r) => r,
            Err(p) => std::panic::resume_unwind(p),
        }
    }

    fn cgroup_fixture_root(tag: &str) -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "turbo_cgroup_{tag}_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        root
    }

    #[test]
    fn test_parse_proc_self_cgroup_v2_path() {
        assert_eq!(
            parse_proc_self_cgroup_v2_path("0::/user.slice/user-1000.slice/app.scope\n"),
            Some("/user.slice/user-1000.slice/app.scope".to_string())
        );
        // Hybrid hierarchy: v1 controllers first, unified `0::` entry later.
        assert_eq!(
            parse_proc_self_cgroup_v2_path("12:memory:/foo\n1:name=systemd:/bar\n0::/svc.scope\n"),
            Some("/svc.scope".to_string())
        );
        assert_eq!(
            parse_proc_self_cgroup_v2_path("0::/\n"),
            Some("/".to_string())
        );
        assert_eq!(parse_proc_self_cgroup_v2_path("12:memory:/foo\n"), None);
        assert_eq!(parse_proc_self_cgroup_v2_path(""), None);
        // Path traversal must never escape the cgroup mount.
        assert_eq!(parse_proc_self_cgroup_v2_path("0::/../../etc\n"), None);
        assert_eq!(parse_proc_self_cgroup_v2_path("0::relative\n"), None);
    }

    #[test]
    fn test_parse_cgroup_memory_max_bytes() {
        assert_eq!(parse_cgroup_memory_max_bytes("max\n"), None);
        assert_eq!(parse_cgroup_memory_max_bytes(""), None);
        assert_eq!(parse_cgroup_memory_max_bytes("0"), None);
        assert_eq!(parse_cgroup_memory_max_bytes("garbage"), None);
        assert_eq!(
            parse_cgroup_memory_max_bytes("8976400384\n"),
            Some(8_976_400_384)
        );
        // cgroup v1 "unlimited" sentinel (PAGE_COUNTER_MAX * page size).
        assert_eq!(parse_cgroup_memory_max_bytes("9223372036854771712"), None);
    }

    #[test]
    fn test_resolve_cgroup_v2_memory_max_walks_ancestors_and_takes_minimum() {
        let root = cgroup_fixture_root("walk");
        let leaf = root.join("user.slice/app.slice/job.scope");
        fs::create_dir_all(&leaf).unwrap();
        fs::write(root.join("memory.max"), "max\n").unwrap();
        fs::write(root.join("user.slice/memory.max"), "8589934592\n").unwrap(); // 8 GiB
        fs::write(root.join("user.slice/app.slice/memory.max"), "max\n").unwrap();
        fs::write(leaf.join("memory.max"), "17179869184\n").unwrap(); // 16 GiB
        assert_eq!(
            resolve_cgroup_v2_memory_max_bytes_at(&root, "/user.slice/app.slice/job.scope"),
            Some(8_589_934_592),
            "the tightest ancestor limit wins"
        );
        // Missing leaf file (e.g. the root cgroup has no memory.max) still walks ancestors.
        fs::remove_file(leaf.join("memory.max")).unwrap();
        assert_eq!(
            resolve_cgroup_v2_memory_max_bytes_at(&root, "/user.slice/app.slice/job.scope"),
            Some(8_589_934_592)
        );
        fs::write(root.join("user.slice/memory.max"), "max").unwrap();
        assert_eq!(
            resolve_cgroup_v2_memory_max_bytes_at(&root, "/user.slice/app.slice/job.scope"),
            None
        );
        fs::write(root.join("memory.max"), "1073741824").unwrap();
        assert_eq!(
            resolve_cgroup_v2_memory_max_bytes_at(&root, "/user.slice/app.slice/job.scope"),
            Some(1_073_741_824),
            "the mount-root memory.max is included"
        );
        assert_eq!(
            resolve_cgroup_v2_memory_max_bytes_at(&root, "/"),
            Some(1_073_741_824)
        );
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn test_cgroup_memory_events_oom_kill() {
        let text = "low 0\nhigh 12\nmax 40\noom 3\noom_kill 2\noom_group_kill 0\n";
        assert_eq!(parse_cgroup_memory_events_oom_kill(text), Some(2));
        assert_eq!(parse_cgroup_memory_events_oom_kill("low 0\n"), None);
        let root = cgroup_fixture_root("events");
        fs::create_dir_all(root.join("a.scope")).unwrap();
        fs::write(root.join("a.scope/memory.events"), text).unwrap();
        assert_eq!(read_cgroup_oom_kill_count_at(&root, "/a.scope"), Some(2));
        assert_eq!(read_cgroup_oom_kill_count_at(&root, "/missing.scope"), None);
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn test_preflight_memory_guard_rejects_insufficient_memory_max() {
        let gib = 1024u64 * 1024 * 1024;
        // Unknown cgroup limit or unknown demand: pass.
        assert!(preflight_memory_guard("M", Some(28_000), Some(30_000), None).is_ok());
        assert!(preflight_memory_guard("M", None, None, Some(8 * gib)).is_ok());
        // Fits.
        assert!(preflight_memory_guard("M", Some(4_000), Some(6_000), Some(8 * gib)).is_ok());
        // Historical peak (27.8 GiB) exceeds an 8 GiB cgroup.
        let err = preflight_memory_guard("IdleCDOEpochVariant", Some(28_467), None, Some(8 * gib))
            .unwrap_err()
            .to_string();
        assert!(err.contains("IdleCDOEpochVariant"), "{err}");
        assert!(err.contains("memory.max"), "{err}");
        assert!(err.contains("28467"), "{err}");
        assert!(err.contains("8192"), "{err}");
        assert!(err.contains("--max-memory-mb"), "{err}");
        // `--max-memory-mb` above the cgroup limit is unsatisfiable.
        let err = preflight_memory_guard("M", None, Some(10_000), Some(8 * gib))
            .unwrap_err()
            .to_string();
        assert!(err.contains("--max-memory-mb 10000"), "{err}");
        assert!(err.contains("memory.max"), "{err}");
    }

    #[test]
    fn test_preflight_memory_guard_live_skip_env() {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let prev = std::env::var_os("TURBO_LEAN_SKIP_MEMORY_PREFLIGHT");
        std::env::set_var("TURBO_LEAN_SKIP_MEMORY_PREFLIGHT", "1");
        assert!(preflight_memory_guard_live("M", Some(u64::MAX / 2)).is_ok());
        match prev {
            Some(v) => std::env::set_var("TURBO_LEAN_SKIP_MEMORY_PREFLIGHT", v),
            None => std::env::remove_var("TURBO_LEAN_SKIP_MEMORY_PREFLIGHT"),
        }
    }

    #[cfg(unix)]
    #[test]
    fn test_build_receipt_is_emitted_for_sigkill_and_sigabrt_children() {
        let dir = cgroup_fixture_root("receipt");
        let olean = dir.join("M.olean");
        fs::write(&olean, b"olean-bytes").unwrap();
        for (sig, script) in [
            (libc::SIGKILL, "kill -KILL $$"),
            (libc::SIGABRT, "kill -ABRT $$"),
        ] {
            let receipt_path = dir.join(format!("receipt_{sig}.json"));
            let mut cmd = std::process::Command::new("/bin/sh");
            cmd.args(["-c", script]);
            let (out, receipt) =
                run_command_with_receipt(&mut cmd, &receipt_path, Some(&olean)).unwrap();
            assert!(!out.status.success());
            assert_eq!(receipt.exit_code, None);
            assert_eq!(receipt.signal, Some(sig));
            assert_eq!(receipt.oom_suspected, sig == libc::SIGKILL);
            assert!(receipt.elapsed_s >= 0.0);
            let on_disk: BuildReceipt =
                serde_json::from_slice(&fs::read(&receipt_path).unwrap()).unwrap();
            assert_eq!(on_disk, receipt);
            let raw: serde_json::Value =
                serde_json::from_slice(&fs::read(&receipt_path).unwrap()).unwrap();
            for key in [
                "exit_code",
                "signal",
                "peak_rss_kib",
                "cgroup_oom_kill",
                "elapsed_s",
                "olean_sha256",
            ] {
                assert!(raw.get(key).is_some(), "missing `{key}` in {raw}");
            }
            // No leftover staging files beside the receipt.
            let leftovers: Vec<_> = fs::read_dir(&dir)
                .unwrap()
                .filter_map(|e| e.ok())
                .filter(|e| e.file_name().to_string_lossy().contains(".tmp"))
                .collect();
            assert!(leftovers.is_empty(), "{leftovers:?}");
        }
        let receipt_path = dir.join("receipt_ok.json");
        let mut cmd = std::process::Command::new("/bin/sh");
        cmd.args(["-c", "exit 3"]);
        let (_, receipt) = run_command_with_receipt(&mut cmd, &receipt_path, Some(&olean)).unwrap();
        assert_eq!(receipt.exit_code, Some(3));
        assert_eq!(receipt.signal, None);
        assert!(!receipt.oom_suspected);
        let expected = sha256_file_hex(&olean).unwrap();
        assert_eq!(expected.len(), 64);
        assert_eq!(receipt.olean_sha256.as_deref(), Some(expected.as_str()));
        let _ = fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_build_receipt_oom_kill_delta_marks_oom() {
        use std::os::unix::process::ExitStatusExt;
        let status = std::process::ExitStatus::from_raw(0);
        let r = BuildReceipt::from_exit_status(
            &status,
            std::time::Duration::from_millis(1500),
            Some(1024),
            Some(1),
            None,
        );
        assert_eq!(r.exit_code, Some(0));
        assert!(r.oom_suspected, "a cgroup oom_kill delta marks OOM");
        assert!((r.elapsed_s - 1.5).abs() < 1e-9);
        assert_eq!(r.peak_rss_kib, Some(1024));
        assert_eq!(r.olean_sha256, None);
    }

    #[test]
    fn test_cgroup_oom_kill_delta_when_counter_appears_mid_run() {
        assert_eq!(cgroup_oom_kill_delta(None, Some(1)), Some(1));
        assert_eq!(cgroup_oom_kill_delta(None, Some(0)), Some(0));
        assert_eq!(cgroup_oom_kill_delta(Some(2), Some(5)), Some(3));
        assert_eq!(cgroup_oom_kill_delta(Some(5), Some(2)), Some(0));
        assert_eq!(cgroup_oom_kill_delta(Some(2), None), None);
        assert_eq!(cgroup_oom_kill_delta(None, None), None);
        #[cfg(unix)]
        {
            use std::os::unix::process::ExitStatusExt;
            let status = std::process::ExitStatus::from_raw(0);
            let delta = cgroup_oom_kill_delta(None, Some(1));
            let receipt = BuildReceipt::from_exit_status(
                &status,
                std::time::Duration::from_millis(250),
                Some(2048),
                delta,
                None,
            );
            assert_eq!(receipt.cgroup_oom_kill, Some(1));
            assert!(receipt.oom_suspected);
        }
    }

    #[test]
    fn test_resolve_effective_cgroup_v2_max_does_not_fall_through_to_v1() {
        // Parse v1 memory path including multi-controller lines and traversal rejection.
        assert_eq!(
            parse_proc_self_cgroup_v1_memory_path("12:memory:/app.scope\n"),
            Some("/app.scope".to_string())
        );
        assert_eq!(
            parse_proc_self_cgroup_v1_memory_path("4:cpu,memory:/sub/job\n0::/svc.scope\n"),
            Some("/sub/job".to_string())
        );
        assert_eq!(
            parse_proc_self_cgroup_v1_memory_path("12:memory:/../etc\n"),
            None
        );

        // v2 `memory.max` == `max` MUST NOT fall through to v1 `memory/memory.limit_in_bytes`.
        let root = cgroup_fixture_root("v2_max_no_v1_fallthrough");
        fs::create_dir_all(root.join("user.slice/job.scope")).unwrap();
        fs::create_dir_all(root.join("memory/app.scope")).unwrap();
        fs::write(root.join("user.slice/memory.max"), "max\n").unwrap();
        fs::write(root.join("user.slice/job.scope/memory.max"), "max\n").unwrap();
        fs::write(root.join("memory/memory.limit_in_bytes"), "1073741824\n").unwrap();
        fs::write(
            root.join("memory/app.scope/memory.limit_in_bytes"),
            "536870912\n",
        )
        .unwrap();
        assert_eq!(
            resolve_effective_cgroup_memory_max_bytes_at(
                &root,
                Some("0::/user.slice/job.scope\n"),
            ),
            None,
            "v2 memory.max=max must stay unlimited and not fall through to v1"
        );
        assert_eq!(
            resolve_effective_cgroup_memory_max_bytes_at(
                &root,
                Some("12:memory:/app.scope\n0::/user.slice/job.scope\n"),
            ),
            None,
            "hybrid /proc/self/cgroup with v2 memory.max=max must not fall through to v1"
        );

        // Pure unified v2 root (has `cgroup.controllers`, no `memory.max` at `/`) also skips v1.
        let v2_root_only = cgroup_fixture_root("v2_unified_root");
        fs::create_dir_all(v2_root_only.join("memory")).unwrap();
        fs::write(v2_root_only.join("cgroup.controllers"), "cpu memory io\n").unwrap();
        fs::write(
            v2_root_only.join("memory/memory.limit_in_bytes"),
            "1073741824\n",
        )
        .unwrap();
        assert_eq!(
            resolve_effective_cgroup_memory_max_bytes_at(&v2_root_only, Some("0::/\n")),
            None
        );

        // Pure cgroup v1 (no v2 memory.max, no cgroup.controllers) resolves v1 ancestor walk cleanly.
        let v1_root = cgroup_fixture_root("v1_only");
        fs::create_dir_all(v1_root.join("memory/app.scope")).unwrap();
        fs::write(
            v1_root.join("memory/memory.limit_in_bytes"),
            "4294967296\n",
        )
        .unwrap();
        fs::write(
            v1_root.join("memory/app.scope/memory.limit_in_bytes"),
            "2147483648\n",
        )
        .unwrap();
        assert_eq!(
            resolve_effective_cgroup_memory_max_bytes_at(&v1_root, Some("12:memory:/app.scope\n")),
            Some(2_147_483_648)
        );
        // Tighter root limit wins in v1 ancestor walk too.
        fs::write(
            v1_root.join("memory/memory.limit_in_bytes"),
            "1073741824\n",
        )
        .unwrap();
        assert_eq!(
            resolve_effective_cgroup_memory_max_bytes_at(&v1_root, Some("12:memory:/app.scope\n")),
            Some(1_073_741_824)
        );

        let _ = fs::remove_dir_all(&root);
        let _ = fs::remove_dir_all(&v2_root_only);
        let _ = fs::remove_dir_all(&v1_root);
    }

    #[test]
    fn test_resolve_historical_peak_rss_mb_env_receipt_and_project_cache() {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let prev_home = std::env::var_os("TURBO_LEAN_HOME");
        let prev_peak = std::env::var_os("TURBO_LEAN_HISTORICAL_PEAK_RSS_MB");
        let dir = cgroup_fixture_root("hist_peak");
        let project = dir.join("proj");
        let cache = dir.join("cache");
        let receipt_path = dir.join("prev_receipt.json");
        fs::create_dir_all(&project).unwrap();
        std::env::set_var("TURBO_LEAN_HOME", &cache);
        std::env::remove_var("TURBO_LEAN_HISTORICAL_PEAK_RSS_MB");

        // Initially unknown.
        assert_eq!(
            resolve_historical_peak_rss_mb(Some(&project), Some(&receipt_path)),
            None
        );

        // Persisted project cache feeds historical peak (28 GiB vs 8 GiB cgroup rejects).
        record_project_peak_rss_kib(&project, 28_467 * 1024);
        assert_eq!(
            resolve_historical_peak_rss_mb(Some(&project), Some(&receipt_path)),
            Some(28_467)
        );
        let err = preflight_memory_guard(
            "turbo-lean build (proj)",
            resolve_historical_peak_rss_mb(Some(&project), Some(&receipt_path)),
            None,
            Some(8 * 1024 * 1024 * 1024),
        )
        .unwrap_err()
        .to_string();
        assert!(err.contains("28467"), "{err}");
        assert!(err.contains("8192"), "{err}");

        // A later small (cache-hit) run never lowers the recorded high-water peak.
        record_project_peak_rss_kib(&project, 200 * 1024);
        assert_eq!(read_project_peak_rss_mb(&project), Some(28_467));
        record_project_peak_rss_kib(&project, 0);
        assert_eq!(read_project_peak_rss_mb(&project), Some(28_467));
        // A larger run raises it.
        record_project_peak_rss_kib(&project, 30_000 * 1024);
        assert_eq!(read_project_peak_rss_mb(&project), Some(30_000));

        // A prior receipt rewritten by a small cache-hit run cannot hide the project peak.
        write_build_receipt_atomic(
            &receipt_path,
            &BuildReceipt {
                exit_code: Some(0),
                peak_rss_kib: Some(200 * 1024),
                ..BuildReceipt::default()
            },
        )
        .unwrap();
        assert_eq!(
            resolve_historical_peak_rss_mb(Some(&project), Some(&receipt_path)),
            Some(30_000)
        );

        // A prior receipt with a larger peak (e.g. from another host's cache) wins.
        write_build_receipt_atomic(
            &receipt_path,
            &BuildReceipt {
                exit_code: Some(137),
                signal: None,
                peak_rss_kib: Some(40_000 * 1024),
                cgroup_oom_kill: Some(1),
                elapsed_s: 12.0,
                olean_sha256: None,
                oom_suspected: true,
            },
        )
        .unwrap();
        assert_eq!(
            resolve_historical_peak_rss_mb(Some(&project), Some(&receipt_path)),
            Some(40_000)
        );

        // Explicit env override takes highest precedence.
        std::env::set_var("TURBO_LEAN_HISTORICAL_PEAK_RSS_MB", "32000");
        assert_eq!(
            resolve_historical_peak_rss_mb(Some(&project), Some(&receipt_path)),
            Some(32_000)
        );

        match prev_home {
            Some(v) => std::env::set_var("TURBO_LEAN_HOME", v),
            None => std::env::remove_var("TURBO_LEAN_HOME"),
        }
        match prev_peak {
            Some(v) => std::env::set_var("TURBO_LEAN_HISTORICAL_PEAK_RSS_MB", v),
            None => std::env::remove_var("TURBO_LEAN_HISTORICAL_PEAK_RSS_MB"),
        }
        let _ = fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_invocation_receipt_propagates_child_sigkill_and_exit_137() {
        use std::os::unix::process::ExitStatusExt;
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        reset_recorded_child_exit_status();

        // Lower-severity exit 1 followed by SIGKILL: SIGKILL wins; subsequent exit 1 does not overwrite it.
        let sigkill_out = std::process::Command::new("/bin/sh")
            .args(["-c", "kill -KILL $$"])
            .output()
            .unwrap();
        let exit1_status = std::process::ExitStatus::from_raw(1 << 8);
        record_child_exit_status(exit1_status);
        record_child_exit_status(sigkill_out.status);
        record_child_exit_status(exit1_status);
        let recorded = take_recorded_child_exit_status().expect("SIGKILL recorded");
        assert_eq!(recorded.signal(), Some(libc::SIGKILL));

        let r_sigkill = BuildReceipt::for_invocation(
            false,
            None,
            Some(&recorded),
            None,
            std::time::Duration::from_millis(500),
            Some(4096),
            None,
            None,
        );
        assert_eq!(r_sigkill.signal, Some(libc::SIGKILL));
        assert_eq!(r_sigkill.exit_code, None);
        assert!(r_sigkill.oom_suspected, "SIGKILL must mark oom_suspected");

        // Wrapped child exiting with 137 (128 + SIGKILL) also marks oom_suspected.
        let exit137_out = std::process::Command::new("/bin/sh")
            .args(["-c", "exit 137"])
            .output()
            .unwrap();
        let r_137 = BuildReceipt::for_invocation(
            false,
            None,
            Some(&exit137_out.status),
            None,
            std::time::Duration::from_millis(500),
            Some(4096),
            None,
            None,
        );
        assert_eq!(r_137.exit_code, Some(137));
        assert_eq!(r_137.signal, None);
        assert!(r_137.oom_suspected, "exit 137 must mark oom_suspected");

        // Successful invocation does not inherit a stale child failure.
        let r_ok = BuildReceipt::for_invocation(
            true,
            None,
            Some(&recorded),
            None,
            std::time::Duration::from_millis(100),
            Some(1024),
            Some(0),
            None,
        );
        assert_eq!(r_ok.exit_code, Some(0));
        assert_eq!(r_ok.signal, None);
        assert!(!r_ok.oom_suspected);
    }

    #[cfg(unix)]
    #[test]
    fn test_recovered_child_sigkill_does_not_bleed_into_later_failure() {
        use std::os::unix::process::ExitStatusExt;
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        reset_recorded_child_exit_status();
        let sigkill = std::process::ExitStatus::from_raw(libc::SIGKILL);
        let exit1 = std::process::ExitStatus::from_raw(1 << 8);

        // A worker is SIGKILLed, respawned and the retry succeeds: the crash is withdrawn.
        record_child_exit_status(sigkill);
        forgive_child_exit_status(&sigkill);
        // Later, an unrelated ordinary elaboration failure terminates the invocation.
        record_child_exit_status(exit1);
        let recorded = take_recorded_child_exit_status().expect("exit 1 recorded");
        assert_eq!(recorded.code(), Some(1));
        let r = BuildReceipt::for_invocation(
            false,
            None,
            Some(&recorded),
            None,
            std::time::Duration::from_millis(10),
            None,
            Some(0),
            None,
        );
        assert_eq!(r.exit_code, Some(1));
        assert_eq!(r.signal, None);
        assert!(
            !r.oom_suspected,
            "a recovered SIGKILL must not mark a later failure as OOM"
        );

        // Only the recovered instance is withdrawn: an unrecovered second SIGKILL still wins.
        record_child_exit_status(sigkill);
        record_child_exit_status(sigkill);
        forgive_child_exit_status(&sigkill);
        record_child_exit_status(exit1);
        assert_eq!(
            take_recorded_child_exit_status().and_then(|s| s.signal()),
            Some(libc::SIGKILL)
        );
        // `take` drains the ledger; forgiving an unknown status is a no-op.
        forgive_child_exit_status(&exit1);
        assert_eq!(take_recorded_child_exit_status(), None);

        // A failure with no recorded child (pure elaboration error) is a plain exit 1.
        let r = BuildReceipt::for_invocation(
            false,
            None,
            None,
            None,
            std::time::Duration::from_millis(10),
            None,
            None,
            None,
        );
        assert_eq!(r.exit_code, Some(1));
        assert!(!r.oom_suspected);
    }

    #[test]
    fn test_sha256_file_hex_known_vector() {
        let dir = cgroup_fixture_root("sha");
        let p = dir.join("abc");
        fs::write(&p, b"abc").unwrap();
        assert_eq!(
            sha256_file_hex(&p).unwrap(),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_cache_root_honors_turbo_lean_home_then_cache_dir() {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let prev_home_override = std::env::var("TURBO_LEAN_HOME").ok();
        let prev_cache_dir = std::env::var("TURBO_LEAN_CACHE_DIR").ok();
        std::env::remove_var("TURBO_LEAN_HOME");
        std::env::set_var("TURBO_LEAN_CACHE_DIR", "/tmp/tl-cache-dir-fallback");
        assert_eq!(cache_root(), PathBuf::from("/tmp/tl-cache-dir-fallback"));
        std::env::set_var("TURBO_LEAN_HOME", "/tmp/tl-home-primary");
        assert_eq!(cache_root(), PathBuf::from("/tmp/tl-home-primary"));
        std::env::set_var("TURBO_LEAN_HOME", "   ");
        assert_eq!(cache_root(), PathBuf::from("/tmp/tl-cache-dir-fallback"));
        match prev_home_override {
            Some(v) => std::env::set_var("TURBO_LEAN_HOME", v),
            None => std::env::remove_var("TURBO_LEAN_HOME"),
        }
        match prev_cache_dir {
            Some(v) => std::env::set_var("TURBO_LEAN_CACHE_DIR", v),
            None => std::env::remove_var("TURBO_LEAN_CACHE_DIR"),
        }
    }
}
