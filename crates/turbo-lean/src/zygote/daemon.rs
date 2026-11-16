use crate::db::TurboStore;
use crate::pack::{next_tmp_id, CheckShardHttpRequest};
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::BufRead;
use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::process::Command;

#[cfg(not(test))]
use super::mcp_caller_policy;
use super::{
    clear_zygote_pool, invocation_timeout_ms, request_policy, MCP_RUNTIME_POLICY_KEYS,
    REQUEST_POLICY_KEYS,
};

/// One-shot staging is private even when another invocation uses the same CAS.
pub(crate) struct OneShotGuard;
pub(super) static ONE_SHOT_DIR: std::sync::OnceLock<(PathBuf, PathBuf)> = std::sync::OnceLock::new();

pub(super) extern "C" fn cleanup_one_shot() {
    clear_zygote_pool();
    if let Some((dir, _)) = ONE_SHOT_DIR.get() {
        let _ = fs::remove_dir_all(dir);
    }
}

#[cfg(unix)]
pub(super) extern "C" fn cleanup_zygote_processes() {
    clear_zygote_pool();
}

#[cfg(test)]
thread_local! {
    /// Per-test-thread `TURBO_LEAN_NO_DAEMON` (the env var is process-global).
    pub(super) static TEST_NO_DAEMON: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(crate) fn daemon_disabled() -> bool {
    #[cfg(test)]
    if TEST_NO_DAEMON.with(|c| c.get()) {
        return true;
    }
    std::env::var("TURBO_LEAN_NO_DAEMON")
        .ok()
        .and_then(|value| crate::shm_cache::parse_relaxed_bool(&value))
        .unwrap_or(false)
}

impl OneShotGuard {
    /// Persistent metrics retain their namespace while workers use disposable sibling staging.
    pub(crate) fn persistent_staging_dir() -> PathBuf {
        ONE_SHOT_DIR
            .get()
            .map(|(_, base)| base.clone())
            .unwrap_or_else(crate::shm_cache::staging_shm_dir)
    }

    pub(crate) fn new(flag: bool) -> Result<Self> {
        let enabled = flag || daemon_disabled();
        if !enabled {
            return Ok(Self);
        }
        std::env::set_var("TURBO_LEAN_NO_DAEMON", "1");
        let base = crate::shm_cache::staging_shm_dir();
        // A sibling survives cleanup of an idle daemon's shared staging directory.
        let dir = base.with_file_name(format!(
            "{}-oneshot-{}-{}",
            base.file_name()
                .context("Staging directory needs a name")?
                .to_string_lossy(),
            std::process::id(),
            next_tmp_id()
        ));
        crate::shm_cache::ensure_private_dir_all(&dir)?;
        std::env::set_var("TURBO_LEAN_STAGING_DIR", &dir);
        let _ = ONE_SHOT_DIR.set((dir, base));
        // `eval` also exits with explicit status codes, bypassing Rust Drop.
        #[cfg(unix)]
        unsafe {
            libc::atexit(cleanup_one_shot);
        }
        Ok(Self)
    }
}

impl Drop for OneShotGuard {
    fn drop(&mut self) {
        cleanup_one_shot();
    }
}

pub(super) fn is_serve_command(cmdline: &[u8]) -> bool {
    let mut args = cmdline.split(|b| *b == 0).filter(|a| !a.is_empty()).skip(1);
    while let Some(arg) = args.next() {
        match arg {
            b"--cache-dir" | b"--max-memory-mb" | b"--telemetry" => {
                args.next();
            }
            flag if flag.starts_with(b"-") => {}
            command => return command == b"serve",
        }
    }
    false
}

#[cfg(target_os = "linux")]
pub(super) fn owned_lifecycle_process(pid: u32, staging: Option<&Path>, parent: Option<u32>) -> bool {
    use std::os::unix::fs::MetadataExt;
    if pid <= 1 || pid == std::process::id() {
        return false;
    }
    let proc = PathBuf::from(format!("/proc/{pid}"));
    if fs::metadata(&proc).map(|m| m.uid()).ok() != Some(unsafe { libc::geteuid() }) {
        return false;
    }
    let exe = fs::read_link(proc.join("exe")).unwrap_or_default();
    let name = exe.file_name().and_then(|s| s.to_str()).unwrap_or("");
    let args = fs::read(proc.join("cmdline")).unwrap_or_default();
    let env = fs::read(proc.join("environ")).unwrap_or_default();
    let worker = (name.starts_with("turbo_zygote_") || name == "turbo-zygote")
        && !args.is_empty()
        && !env.is_empty()
        && !args.split(|b| *b == 0).any(|arg| {
            arg == b"--audit-modules" || arg == b"--decl-identity" || arg == b"--public-sig"
        });
    let server = name.trim_end_matches(" (deleted)") == "turbo-lean"
        && is_serve_command(&args)
        && env.split(|b| *b == 0).any(|v| v == b"TURBO_LEAN_DAEMON=1");
    if !worker && !server {
        return false;
    }
    if let Some(parent) = parent {
        let status = fs::read_to_string(proc.join("status")).unwrap_or_default();
        return status.lines().any(|l| {
            l.strip_prefix("PPid:")
                .and_then(|p| p.trim().parse::<u32>().ok())
                == Some(parent)
        });
    }
    if let Some(staging) = staging {
        let expected = format!("TURBO_LEAN_STAGING_DIR={}", staging.display());
        return env.split(|b| *b == 0).any(|v| v == expected.as_bytes());
    }
    true
}

/// Only the effective user's processes are eligible. An explicit staging directory limits
/// shutdown to that namespace, so integration tests and isolated callers cannot kill peers.
#[cfg(target_os = "linux")]
pub(super) fn lifecycle_pids(staging: Option<&Path>, parent: Option<u32>) -> Vec<u32> {
    fs::read_dir("/proc")
        .into_iter()
        .flatten()
        .flatten()
        .filter_map(|e| e.file_name().to_str()?.parse::<u32>().ok())
        .filter(|pid| owned_lifecycle_process(*pid, staging, parent))
        .collect()
}

#[cfg(not(target_os = "linux"))]
pub(super) fn lifecycle_pids(_: Option<&Path>, _: Option<u32>) -> Vec<u32> {
    Vec::new()
}

/// One user-wide lock coordinates every staging namespace, including user-wide stop.
/// Keep the inode outside staging: deleting staging must never replace the lock itself.
pub(crate) fn lifecycle_lock(exclusive: bool) -> Result<crate::shm_cache::FlockGuard> {
    #[cfg(unix)]
    let uid = unsafe { libc::geteuid() };
    #[cfg(not(unix))]
    let uid = 0u32;
    let path = PathBuf::from(format!("/tmp/turbo-lean-lifecycle-{uid}.lock"));
    let guard = crate::shm_cache::acquire_flock(&path, exclusive, false)?
        .context("Could not acquire daemon lifecycle lock")?;
    if !exclusive {
        prepare_caller_staging_dir()?;
    }
    Ok(guard)
}

pub(crate) fn ensure_staging_namespace_dir(create_if_missing: bool) -> Result<()> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
        let path = if create_if_missing {
            Some(crate::shm_cache::staging_shm_dir())
        } else {
            std::env::var("TURBO_LEAN_STAGING_DIR")
                .ok()
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .map(PathBuf::from)
        };
        if let Some(path) = path {
            let sym = match fs::symlink_metadata(&path) {
                Ok(m) => m,
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                    if create_if_missing {
                        crate::shm_cache::ensure_private_dir_all(&path)?;
                    }
                    return Ok(());
                }
                Err(e) => return Err(e.into()),
            };
            anyhow::ensure!(
                !sym.file_type().is_symlink() && sym.file_type().is_dir(),
                "Staging path must be a plain directory: {}",
                path.display()
            );
            let dir = fs::OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
                .open(&path)?;
            let meta = dir.metadata()?;
            anyhow::ensure!(
                meta.dev() == sym.dev()
                    && meta.ino() == sym.ino()
                    && meta.uid() == unsafe { libc::geteuid() }
                    && meta.mode() & 0o022 == 0,
                "Staging directory must be owned by the caller and not writable by others: {}",
                path.display()
            );
        }
    }
    #[cfg(not(unix))]
    if create_if_missing {
        fs::create_dir_all(crate::shm_cache::staging_shm_dir())?;
    }
    Ok(())
}

pub(super) fn prepare_caller_staging_dir() -> Result<()> {
    ensure_staging_namespace_dir(false)
}

/// Possession proves that staging teardown holds the user-wide flock exclusively.
pub(crate) struct ExclusiveLifecycleLock {
    pub(super) _guard: crate::shm_cache::FlockGuard,
}

pub(crate) fn lifecycle_exclusive_lock() -> Result<ExclusiveLifecycleLock> {
    Ok(ExclusiveLifecycleLock {
        _guard: lifecycle_lock(true)?,
    })
}

pub(super) fn remove_owned_staging(path: &Path) -> Result<()> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let meta = match fs::symlink_metadata(path) {
            Ok(meta) => meta,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(()),
            Err(e) => return Err(e.into()),
        };
        anyhow::ensure!(
            meta.is_dir() && meta.uid() == unsafe { libc::geteuid() },
            "Refusing to remove staging not owned by this user: {}",
            path.display()
        );
        let canonical = path.canonicalize()?;
        anyhow::ensure!(
            canonical.parent().is_some()
                && canonical != Path::new("/dev/shm")
                && canonical != std::env::temp_dir().canonicalize()?
                && std::env::var_os("HOME")
                    .map(PathBuf::from)
                    .and_then(|p| p.canonicalize().ok())
                    .as_ref()
                    != Some(&canonical),
            "Refusing unsafe staging directory: {}",
            path.display()
        );
    }
    fs::remove_dir_all(path).with_context(|| format!("Removing staging {}", path.display()))
}

/// Hold the kernel process identity across /proc validation and both shutdown signals.
#[cfg(target_os = "linux")]
pub(super) struct LifecycleProcess {
    pub(super) pid: u32,
    pub(super) pidfd: std::os::fd::OwnedFd,
    pub(super) start_time: u64,
    pub(super) identity: (PathBuf, Vec<u8>, Vec<u8>),
    pub(super) staging: Option<PathBuf>,
    pub(super) parent: Option<u32>,
}

#[cfg(target_os = "linux")]
pub(super) fn process_start_time(pid: u32) -> Option<u64> {
    // comm (field 2) can contain spaces and parentheses; field 22 is index 19 after it.
    fs::read_to_string(format!("/proc/{pid}/stat"))
        .ok()?
        .rsplit_once(") ")?
        .1
        .split_whitespace()
        .nth(19)?
        .parse()
        .ok()
}

#[cfg(target_os = "linux")]
impl LifecycleProcess {
    pub(super) fn open(pid: u32, staging: Option<&Path>, parent: Option<u32>) -> Option<Self> {
        use std::os::fd::FromRawFd;
        let fd = unsafe { libc::syscall(libc::SYS_pidfd_open, pid, 0) };
        if fd < 0 {
            return None; // Fail closed if pidfds are unavailable.
        }
        let pidfd = unsafe { std::os::fd::OwnedFd::from_raw_fd(fd as i32) };
        let start_time = process_start_time(pid)?;
        if !owned_lifecycle_process(pid, staging, parent) {
            return None;
        }
        let proc = PathBuf::from(format!("/proc/{pid}"));
        let cmdline = fs::read(proc.join("cmdline")).ok()?;
        let environ = fs::read(proc.join("environ")).ok()?;
        if cmdline.is_empty() || environ.is_empty() {
            return None;
        }
        let process = Self {
            pid,
            pidfd,
            start_time,
            identity: (fs::read_link(proc.join("exe")).ok()?, cmdline, environ),
            staging: staging.map(Path::to_path_buf),
            parent,
        };
        process.valid_identity().then_some(process)
    }

    pub(super) fn alive(&self) -> bool {
        use std::os::fd::AsRawFd;
        let mut fd = libc::pollfd {
            fd: self.pidfd.as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        };
        unsafe { libc::poll(&mut fd, 1, 0) == 0 }
    }

    pub(super) fn valid_identity(&self) -> bool {
        let proc = PathBuf::from(format!("/proc/{}", self.pid));
        self.alive()
            && process_start_time(self.pid) == Some(self.start_time)
            && owned_lifecycle_process(self.pid, self.staging.as_deref(), self.parent)
            && fs::read_link(proc.join("exe")).ok().as_ref() == Some(&self.identity.0)
            && fs::read(proc.join("cmdline")).ok().as_ref() == Some(&self.identity.1)
            && fs::read(proc.join("environ")).ok().as_ref() == Some(&self.identity.2)
            && process_start_time(self.pid) == Some(self.start_time)
    }

    pub(super) fn signal(&self, signal: i32) -> bool {
        use std::os::fd::AsRawFd;
        if !self.valid_identity() {
            return false;
        }
        // Even reuse after the last /proc read cannot redirect this signal to a new PID.
        unsafe {
            libc::syscall(
                libc::SYS_pidfd_send_signal,
                self.pidfd.as_raw_fd(),
                signal,
                std::ptr::null::<libc::siginfo_t>(),
                0,
            ) == 0
        }
    }
}

#[derive(Default)]
pub(super) struct LifecycleCleanup {
    pub(super) count: usize,
    pub(super) staging: std::collections::HashSet<PathBuf>,
    pub(super) state_files: std::collections::HashSet<PathBuf>,
}

#[cfg(target_os = "linux")]
pub(super) fn env_path(env: &[u8], key: &str) -> Option<PathBuf> {
    use std::os::unix::ffi::OsStrExt;
    env.split(|b| *b == 0)
        .find_map(|entry| entry.strip_prefix(key.as_bytes()))
        .map(|value| PathBuf::from(std::ffi::OsStr::from_bytes(value)))
}

pub(super) fn terminate_lifecycle_processes(staging: Option<&Path>, parent: Option<u32>) -> LifecycleCleanup {
    #[cfg(target_os = "linux")]
    {
        let processes: Vec<_> = lifecycle_pids(staging, parent)
            .into_iter()
            .filter_map(|pid| LifecycleProcess::open(pid, staging, parent))
            .collect();
        terminate_linux_processes(processes)
    }
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (staging, parent);
        LifecycleCleanup::default()
    }
}

#[cfg(target_os = "linux")]
pub(super) fn terminate_linux_processes(processes: Vec<LifecycleProcess>) -> LifecycleCleanup {
    let mut cleanup = LifecycleCleanup::default();
    for process in &processes {
        if process.signal(libc::SIGTERM) {
            cleanup.count += 1;
            if let Some(path) = env_path(&process.identity.2, "TURBO_LEAN_STAGING_DIR=") {
                cleanup.staging.insert(path);
            }
            for key in [
                "TURBO_LEAN_DAEMON_STATE_FILE=",
                "TURBO_LEAN_DAEMON_PARENT_STATE_FILE=",
            ] {
                if let Some(path) = env_path(&process.identity.2, key) {
                    cleanup.state_files.insert(path);
                }
            }
        }
    }
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
    while processes.iter().any(LifecycleProcess::alive) && std::time::Instant::now() < deadline {
        std::thread::sleep(std::time::Duration::from_millis(20));
    }
    for process in &processes {
        process.signal(libc::SIGKILL);
    }
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(1);
    while processes.iter().any(LifecycleProcess::alive) && std::time::Instant::now() < deadline {
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    cleanup
}

pub(super) fn owned_process_alive(pid: u32) -> bool {
    #[cfg(target_os = "linux")]
    {
        // Liveness is only a postcondition, never authority to signal. If pidfd_open
        // fails, stop must report a live process rather than silently claim success.
        fs::read_to_string(format!("/proc/{pid}/stat"))
            .ok()
            .and_then(|stat| {
                stat.rsplit_once(") ")
                    .map(|(_, rest)| !rest.starts_with('Z'))
            })
            .unwrap_or(false)
    }
    #[cfg(not(target_os = "linux"))]
    {
        portable_process_alive(pid)
    }
}

pub(super) fn staging_namespace_in_use(staging: &Path, _store_root: Option<&Path>) -> bool {
    #[cfg(target_os = "linux")]
    {
        use std::os::unix::fs::MetadataExt;
        let expected = format!("TURBO_LEAN_STAGING_DIR={}", staging.display());
        fs::read_dir("/proc")
            .into_iter()
            .flatten()
            .flatten()
            .any(|entry| {
                let Some(pid) = entry
                    .file_name()
                    .to_str()
                    .and_then(|s| s.parse::<u32>().ok())
                else {
                    return false;
                };
                pid != std::process::id()
                    && fs::metadata(entry.path()).map(|m| m.uid()).ok()
                        == Some(unsafe { libc::geteuid() })
                    && fs::read(entry.path().join("environ"))
                        .unwrap_or_default()
                        .split(|b| *b == 0)
                        .any(|v| v == expected.as_bytes())
            })
    }
    #[cfg(not(target_os = "linux"))]
    {
        // Without /proc, only the PID files and the caller's exclusive flock can
        // establish quiescence. Unknown/corrupt state conservatively retains staging.
        portable_staging_namespace_in_use(staging, _store_root)
    }
}

#[cfg(any(all(unix, not(target_os = "linux")), test))]
pub(super) fn portable_staging_namespace_in_use(staging: &Path, store_root: Option<&Path>) -> bool {
    portable_pidfile_paths(staging, store_root, true)
        .map(|paths| paths.iter().any(|path| portable_pidfile_alive(path)))
        .unwrap_or(true)
}

#[cfg(any(not(target_os = "linux"), test))]
pub(super) fn portable_process_alive(pid: u32) -> bool {
    if pid <= 1 {
        return true;
    }
    // kill(0) is a liveness check only, never authority to send a terminating signal.
    if unsafe { libc::kill(pid as i32, 0) } != 0
        && std::io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH)
    {
        return false;
    }
    // A zombie cannot use staging. On any ps failure retain it conservatively.
    crate::trusted_tools::system_command("ps")
        .and_then(|mut command| {
            command
                .args(["-p", &pid.to_string(), "-o", "stat="])
                .output()
                .map_err(Into::into)
        })
        .map(|out| {
            !out.status.success()
                || out.stdout.iter().find(|b| !b.is_ascii_whitespace()) != Some(&b'Z')
        })
        .unwrap_or(true)
}

#[cfg(any(not(target_os = "linux"), test))]
pub(super) fn portable_pidfile_alive(path: &Path) -> bool {
    match fs::read(path) {
        Ok(bytes) => serde_json::from_slice::<LocalZygoteDaemonInfo>(&bytes)
            .map(|info| portable_process_alive(info.pid))
            .unwrap_or(true),
        Err(e) => e.kind() != std::io::ErrorKind::NotFound,
    }
}

#[cfg(any(not(target_os = "linux"), test))]
#[derive(Debug, PartialEq, Eq)]
pub(super) struct PortableProcessIdentity {
    pub(super) start_time: String,
    pub(super) command: String,
}

#[cfg(any(not(target_os = "linux"), test))]
pub(super) fn portable_process_identity(pid: u32) -> Result<Option<PortableProcessIdentity>> {
    let output = crate::trusted_tools::system_command("ps")?
        .args([
            "eww",
            "-p",
            &pid.to_string(),
            "-o",
            "uid=",
            "-o",
            "lstart=",
            "-o",
            "command=",
        ])
        .env("LC_ALL", "C")
        .output()?;
    if !output.status.success() {
        return Ok(None);
    }
    let text = String::from_utf8_lossy(&output.stdout);
    let mut fields = text.split_whitespace();
    if fields.next().and_then(|s| s.parse::<u32>().ok()) != Some(unsafe { libc::geteuid() }) {
        return Ok(None);
    }
    let start_time = fields.by_ref().take(5).collect::<Vec<_>>().join(" ");
    let args: Vec<_> = fields.collect();
    let exe = args
        .first()
        .and_then(|s| Path::new(s).file_name())
        .and_then(|s| s.to_str());
    let command = args.join("\0");
    if start_time.split_whitespace().count() != 5
        || exe != Some("turbo-lean")
        || !is_serve_command(command.as_bytes())
        || !args.contains(&"TURBO_LEAN_DAEMON=1")
    {
        return Ok(None);
    }
    Ok(Some(PortableProcessIdentity {
        start_time,
        command,
    }))
}

#[cfg(any(not(target_os = "linux"), test))]
pub(super) fn signal_portable_process(
    pid: u32,
    identity: &PortableProcessIdentity,
    signal: i32,
) -> Result<bool> {
    let pid_i32 = pid as i32;
    let target = if unsafe { libc::getpgid(pid_i32) } == pid_i32 {
        -pid_i32
    } else {
        pid_i32
    };
    // Re-read UID, start time, and full command immediately before EVERY signal.
    // Portable Unix lacks pidfd_send_signal: exit/PID (or process-group) reuse can
    // still occur between this final ps snapshot and kill, and ps lstart has only
    // second resolution. This narrows, but cannot eliminate, that residual window.
    if portable_process_identity(pid)?.as_ref() != Some(identity) {
        return Ok(false);
    }
    Ok(unsafe { libc::kill(target, signal) } == 0)
}

// Compile the portable Unix fallback in Linux tests as well as on macOS.
#[cfg(any(all(unix, not(target_os = "linux")), test))]
pub(super) fn stop_pidfile_daemon(state_file: &Path) -> Result<bool> {
    use std::os::unix::fs::MetadataExt;
    let Ok(meta) = fs::symlink_metadata(state_file) else {
        return Ok(false);
    };
    if !meta.is_file() || meta.uid() != unsafe { libc::geteuid() } {
        return Ok(false);
    }
    let Ok(info) = serde_json::from_slice::<LocalZygoteDaemonInfo>(&fs::read(state_file)?) else {
        return Ok(false);
    };
    if info.pid <= 1 || info.pid == std::process::id() {
        return Ok(false);
    }
    let Some(identity) = portable_process_identity(info.pid)? else {
        return Ok(false);
    };
    if !signal_portable_process(info.pid, &identity, libc::SIGTERM)? {
        return Ok(false);
    }
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
    while portable_process_alive(info.pid) {
        anyhow::ensure!(
            std::time::Instant::now() < deadline,
            "PID-file daemon {} is still shutting down",
            info.pid
        );
        std::thread::sleep(std::time::Duration::from_millis(20));
    }
    Ok(true)
}

#[cfg(any(all(unix, not(target_os = "linux")), test))]
pub(super) fn portable_pidfile_paths(
    staging: &Path,
    store_root: Option<&Path>,
    include_legacy_root: bool,
) -> Result<std::collections::HashSet<PathBuf>> {
    let mut paths: std::collections::HashSet<PathBuf> = walkdir::WalkDir::new(staging)
        .max_depth(2)
        .into_iter()
        .filter(|e| {
            !e.as_ref().err().is_some_and(|e| {
                e.io_error()
                    .is_some_and(|e| e.kind() == std::io::ErrorKind::NotFound)
            })
        })
        .collect::<std::result::Result<Vec<_>, _>>()?
        .into_iter()
        .filter(|e| e.file_name() == "zygote_daemon.json")
        .map(|e| e.into_path())
        .collect();
    let root = store_root
        .map(Path::to_path_buf)
        .unwrap_or_else(crate::shm_cache::cache_root);
    // A legacy root entry may describe a different namespace. Explicitly scoped
    // signalling excludes it, but liveness must conservatively veto deletion
    // even when only that legacy PID file remains.
    if include_legacy_root
        || std::env::var_os("TURBO_LEAN_STAGING_DIR").is_none()
        || root.starts_with(staging)
    {
        paths.insert(root.join("zygote_daemon.json"));
    }
    Ok(paths)
}

#[cfg(any(all(unix, not(target_os = "linux")), test))]
pub(super) fn stop_pidfile_daemons(staging: &Path, store_root: Option<&Path>) -> Result<LifecycleCleanup> {
    let paths = portable_pidfile_paths(staging, store_root, false)?;
    let mut cleanup = LifecycleCleanup::default();
    for path in paths {
        if stop_pidfile_daemon(&path)? {
            cleanup.count += 1;
        }
        if !portable_pidfile_alive(&path) {
            cleanup.state_files.insert(path);
        }
    }
    cleanup.staging.insert(staging.to_path_buf());
    Ok(cleanup)
}

pub(super) fn private_staging_child(name: &str) -> Result<PathBuf> {
    ensure_staging_namespace_dir(true)?;
    let dir = crate::shm_cache::staging_shm_dir().join(name);
    crate::shm_cache::ensure_private_dir_all(&dir)?;
    Ok(dir)
}

pub(crate) fn stop_daemons(store_root: Option<&Path>) -> Result<usize> {
    let lifecycle = lifecycle_exclusive_lock()?;
    let default_root = crate::shm_cache::cache_root();
    let store_root = Some(store_root.unwrap_or(&default_root));
    clear_zygote_pool();
    let dir = crate::shm_cache::staging_shm_dir();
    let scope = std::env::var_os("TURBO_LEAN_STAGING_DIR").map(|_| dir.as_path());
    #[cfg(target_os = "linux")]
    let mut cleanup = terminate_lifecycle_processes(scope, None);
    #[cfg(all(unix, not(target_os = "linux")))]
    let mut cleanup = stop_pidfile_daemons(&dir, store_root)?;
    #[cfg(not(unix))]
    let mut cleanup = LifecycleCleanup::default();
    anyhow::ensure!(
        lifecycle_pids(scope, None)
            .iter()
            .all(|p| !owned_process_alive(*p)),
        "Daemon processes are still shutting down"
    );
    for root in [
        Some(dir.as_path()),
        store_root,
        store_root.map(|p| p.join("staging")).as_deref(),
    ]
    .into_iter()
    .flatten()
    {
        if let Ok(entries) = fs::read_dir(root) {
            for entry in entries.flatten() {
                if entry
                    .file_name()
                    .to_string_lossy()
                    .starts_with("zygote_daemon_cas_")
                {
                    cleanup.staging.insert(entry.path());
                }
            }
        }
    }
    cleanup.staging.insert(dir);
    cleanup_lifecycle_staging(cleanup, store_root, &lifecycle)
}

pub(super) fn cleanup_lifecycle_staging(
    mut cleanup: LifecycleCleanup,
    store_root: Option<&Path>,
    _lifecycle: &ExclusiveLifecycleLock,
) -> Result<usize> {
    for path in cleanup.staging {
        if staging_namespace_in_use(&path, store_root) {
            eprintln!(
                "Retained staging {}: still used by a foreground server or another process",
                path.display()
            );
        } else {
            remove_owned_staging(&path)?;
        }
    }
    if let Some(root) = store_root {
        cleanup.state_files.insert(root.join("zygote_daemon.json"));
    }
    for path in cleanup.state_files {
        #[cfg(not(target_os = "linux"))]
        if portable_pidfile_alive(&path) {
            continue;
        }
        let _ = fs::remove_file(path);
    }
    Ok(cleanup.count)
}

pub fn reap_zygote_workers_and_daemons(store_root: Option<&Path>) -> usize {
    stop_daemons(store_root).unwrap_or(0)
}

/// Idle exit is local to this server, never a machine-wide reap.
pub(crate) fn shutdown_local_daemon(_lifecycle: &ExclusiveLifecycleLock) {
    clear_zygote_pool();
    terminate_lifecycle_processes(None, Some(std::process::id()));
    let staging = crate::shm_cache::staging_shm_dir();
    if !staging_namespace_in_use(&staging, None) {
        let _ = remove_owned_staging(&staging);
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct LocalZygoteDaemonInfo {
    pub(crate) addr: String,
    pub(crate) pid: u32,
    pub(crate) exe_mtime_sec: i64,
    pub(crate) exe_mtime_nsec: i64,
    #[serde(default)]
    pub(crate) auth_token: String,
    #[serde(default)]
    pub(crate) policy: Vec<String>,
    /// Build epoch of the daemon binary; reused only when equal to `TURBO_LEAN_BUILD_EPOCH`.
    #[serde(default)]
    pub(crate) build_epoch: String,
}

pub(crate) fn daemon_policy() -> Vec<String> {
    Vec::new()
}

pub(super) fn scrub_worker_api_keys(cmd: &mut Command) {
    let keys: Vec<_> = cmd
        .get_envs()
        .map(|(key, _)| key.to_os_string())
        .chain(std::env::vars_os().map(|(key, _)| key))
        .filter(|key| key.as_encoded_bytes().ends_with(b"_API_KEY"))
        .collect();
    for key in keys {
        cmd.env_remove(key);
    }
}

pub(crate) fn unix_socket_path(path: &Path) -> Result<(PathBuf, Option<fs::File>)> {
    #[cfg(target_os = "linux")]
    {
        use std::os::unix::{ffi::OsStrExt, fs::OpenOptionsExt, io::AsRawFd};
        if path.as_os_str().as_bytes().len() >= 100 {
            let dir = fs::OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_DIRECTORY | libc::O_CLOEXEC | libc::O_NOFOLLOW)
                .open(path.parent().context("socket directory")?)?;
            let short = PathBuf::from(format!("/proc/self/fd/{}", dir.as_raw_fd()))
                .join(path.file_name().context("socket name")?);
            return Ok((short, Some(dir)));
        }
    }
    Ok((path.to_path_buf(), None))
}

pub(super) static LOCAL_DAEMON_SOCKETS: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<String, PathBuf>>,
> = std::sync::OnceLock::new();

pub(super) fn remember_daemon_socket(url: &str, state_file: &Path) {
    if let Some(parent) = state_file.parent() {
        if !parent
            .file_name()
            .is_some_and(|n| n.to_string_lossy().starts_with("zygote_daemon_cas_"))
        {
            return;
        }
        LOCAL_DAEMON_SOCKETS
            .get_or_init(Default::default)
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(url.to_string(), parent.join("daemon.sock"));
    }
}

pub(crate) struct LocalPayload(pub(super) PathBuf);

impl LocalPayload {
    pub(crate) fn create(bytes: &[u8]) -> Result<Self> {
        use std::os::unix::fs::OpenOptionsExt;
        let root = private_staging_child("transport")?;
        let path = root.join(format!("payload-{}-{}", std::process::id(), next_tmp_id()));
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)?;
        use std::io::Write;
        file.write_all(bytes)?;
        Ok(Self(path))
    }

    pub(crate) fn tag(&self) -> String {
        self.0.file_name().unwrap().to_string_lossy().into_owned()
    }

    pub(crate) fn read(tag: &str) -> Result<Vec<u8>> {
        use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
        anyhow::ensure!(
            tag.starts_with("payload-")
                && tag
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_'),
            "Invalid local payload tag"
        );
        let path = crate::shm_cache::staging_shm_dir()
            .join("transport")
            .join(tag);
        let file = fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
            .open(&path)?;
        let meta = file.metadata()?;
        anyhow::ensure!(
            meta.is_file()
                && meta.uid() == unsafe { libc::geteuid() }
                && meta.mode() & 0o077 == 0
                && meta.len() <= 64 * 1024 * 1024,
            "Invalid local payload file"
        );
        use std::io::Read;
        let mut bytes = Vec::with_capacity(meta.len() as usize);
        file.take(64 * 1024 * 1024 + 1).read_to_end(&mut bytes)?;
        anyhow::ensure!(bytes.len() as u64 == meta.len(), "Local payload changed");
        Ok(bytes)
    }
}

impl Drop for LocalPayload {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

/// Maximum accepted bytes per HTTP wire line (request/response head) on the
/// daemon socket boundary: adversarial framing beyond this is rejected
/// fail-closed instead of buffered unboundedly.
pub(crate) const MAX_WIRE_LINE_BYTES: usize = 16 * 1024;

/// Outcome of one bounded wire-line read.
pub(crate) enum BoundedLine {
    /// A complete `'\n'`-terminated line was written into the target buffer.
    Line,
    /// The line exceeded `MAX_WIRE_LINE_BYTES` (the excess input is unconsumed).
    TooLong,
    /// EOF after at least one byte without a terminating `'\n'`.
    Truncated,
    /// EOF before any byte of the line.
    Eof,
}

/// Read one `'\n'`-terminated wire line into `out` (cleared first), bounded by
/// `MAX_WIRE_LINE_BYTES`. Never buffers unbounded input: the take-wrapped read
/// stops at the cap, so a peer streaming an unterminated line cannot grow the
/// daemon's memory.
pub(crate) fn read_bounded_line(
    reader: &mut impl std::io::BufRead,
    out: &mut String,
) -> std::io::Result<BoundedLine> {
    use std::io::Read;
    out.clear();
    let mut bytes = Vec::with_capacity(128);
    reader
        .take(MAX_WIRE_LINE_BYTES as u64 + 1)
        .read_until(b'\n', &mut bytes)?;
    if bytes.len() > MAX_WIRE_LINE_BYTES {
        return Ok(BoundedLine::TooLong);
    }
    if bytes.is_empty() {
        return Ok(BoundedLine::Eof);
    }
    match String::from_utf8(bytes) {
        Ok(line) => {
            *out = line;
            Ok(if out.ends_with('\n') {
                BoundedLine::Line
            } else {
                BoundedLine::Truncated
            })
        }
        Err(error) => Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            error.utf8_error(),
        )),
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn http_request_with_timeout_and_token(
    method: &str,
    url: &str,
    content_type: &str,
    body: &[u8],
    timeout: Option<u64>,
    token: Option<&str>,
    on_inflight: impl FnOnce(),
) -> Result<Vec<u8>> {
    let socket = url
        .rsplit_once('/')
        .and_then(|(base, _)| LOCAL_DAEMON_SOCKETS.get()?.lock().ok()?.get(base).cloned());
    let Some(socket) = socket.filter(|p| p.exists()) else {
        return crate::pack::http_request_with_timeout_and_token(
            method,
            url,
            content_type,
            body,
            timeout,
            token,
            on_inflight,
        );
    };
    use std::io::{Read, Write};
    let (socket, _directory) = unix_socket_path(&socket)?;
    let mut stream = std::os::unix::net::UnixStream::connect(socket)?;
    let duration = Some(std::time::Duration::from_millis(timeout.unwrap_or(900_000)));
    stream.set_read_timeout(duration)?;
    stream.set_write_timeout(duration)?;
    let payload = (body.len() >= 64 * 1024)
        .then(|| LocalPayload::create(body))
        .transpose()?;
    let wire_body = if payload.is_some() { &[][..] } else { body };
    let path = url.rsplit_once('/').context("Invalid local URL")?.1;
    write!(
        stream,
        "{method} /{path} HTTP/1.1\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nX-Turbo-Token: {}\r\n",
        wire_body.len(),
        token.unwrap_or("")
    )?;
    if let Some(payload) = &payload {
        write!(stream, "X-Turbo-Shm: {}\r\n", payload.tag())?;
    }
    stream.write_all(b"\r\n")?;
    on_inflight();
    stream.write_all(wire_body)?;
    let mut reader = std::io::BufReader::new(stream);
    let mut line = String::new();
    match read_bounded_line(&mut reader, &mut line)? {
        BoundedLine::Line => {}
        BoundedLine::TooLong => anyhow::bail!("Local response line too large"),
        _ => anyhow::bail!("Truncated local response"),
    }
    let status: u16 = line
        .split_whitespace()
        .nth(1)
        .context("Missing local response status")?
        .parse()?;
    let mut len = 0usize;
    let mut shared = None;
    loop {
        match read_bounded_line(&mut reader, &mut line)? {
            BoundedLine::Line => {}
            BoundedLine::TooLong => anyhow::bail!("Local response line too large"),
            _ => anyhow::bail!("Truncated local response"),
        }
        if line.trim().is_empty() {
            break;
        }
        if let Some((key, value)) = line.split_once(':') {
            if key.eq_ignore_ascii_case("content-length") {
                len = value.trim().parse()?;
            }
            if key.eq_ignore_ascii_case("x-turbo-shm") {
                shared = Some(value.trim().to_string());
            }
        }
    }
    anyhow::ensure!(len <= 64 * 1024 * 1024, "Local response too large");
    let bytes = if let Some(tag) = shared {
        let bytes = LocalPayload::read(&tag)?;
        reader.get_mut().write_all(&[1])?;
        bytes
    } else {
        let mut bytes = vec![0; len];
        reader.read_exact(&mut bytes)?;
        bytes
    };
    anyhow::ensure!(
        status == 200,
        "HTTP request failed ({status}): {}",
        String::from_utf8_lossy(&bytes)
    );
    Ok(bytes)
}

pub(super) fn check_request_body(req: &CheckShardHttpRequest) -> Result<Vec<u8>> {
    let mut value = serde_json::to_value(req)?;
    value["timeout_ms"] = serde_json::to_value(invocation_timeout_ms())?;
    value["policy_tags"] = serde_json::to_value(request_policy(&Default::default()))?;
    Ok(serde_json::to_vec(&value)?)
}

pub(super) fn generate_daemon_auth_token(pid: u32, port: u16) -> String {
    let now_ns = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-daemon-token-v1:");
    h.update(&pid.to_le_bytes());
    h.update(&port.to_le_bytes());
    h.update(&now_ns.to_le_bytes());
    h.update(next_tmp_id().as_bytes());
    h.finalize().to_hex()[..32].to_string()
}

pub(super) fn write_daemon_state_file_private(path: &Path, json_bytes: &[u8]) {
    let _ = fs::write(path, json_bytes);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if let Ok(m) = fs::metadata(path) {
            let mut p = m.permissions();
            p.set_mode(0o600);
            let _ = fs::set_permissions(path, p);
        }
    }
}

pub(super) fn terminate_and_remove_daemon_state_file(state_file: &Path) {
    if let Ok(content) = fs::read_to_string(state_file) {
        if let Ok(info) = serde_json::from_str::<LocalZygoteDaemonInfo>(&content) {
            #[cfg(target_os = "linux")]
            if let Some(process) =
                LifecycleProcess::open(info.pid, Some(&crate::shm_cache::staging_shm_dir()), None)
            {
                process.signal(libc::SIGTERM);
            }
        }
    }
    #[cfg(all(unix, not(target_os = "linux")))]
    if stop_pidfile_daemon(state_file).is_err() || portable_pidfile_alive(state_file) {
        return;
    }
    let _ = fs::remove_file(state_file);
}

pub(super) fn current_exe_daemon_paths(
    store: &TurboStore,
) -> Option<(PathBuf, i64, i64, PathBuf, PathBuf)> {
    let mut current_exe = std::env::current_exe().ok()?;
    if current_exe.file_name().is_some_and(|n| n != "turbo-lean") {
        current_exe = current_exe.ancestors().skip(1).find_map(|d| {
            let p = d.join("turbo-lean");
            p.is_file().then_some(p)
        })?;
    }
    let metadata = fs::metadata(&current_exe).ok()?;
    let (exe_mtime_sec, exe_mtime_nsec, _) = TurboStore::extract_file_stat_tuple(&metadata);
    let mut exe_hasher = blake3::Hasher::new();
    exe_hasher.update(current_exe.as_os_str().as_encoded_bytes());
    exe_hasher.update(&metadata.len().to_le_bytes());
    exe_hasher.update(&exe_mtime_sec.to_le_bytes());
    exe_hasher.update(&exe_mtime_nsec.to_le_bytes());
    exe_hasher.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    exe_hasher.update(b":");
    exe_hasher.update(
        std::env::var("ELAN_TOOLCHAIN")
            .unwrap_or_else(|_| "leanprover/lean4:v4.35.0".into())
            .as_bytes(),
    );
    let exe_tag = &exe_hasher.finalize().to_hex()[..12];
    let name = format!("zygote_daemon_cas_{}", exe_tag);
    let daemon_cache_dir = private_staging_child(&name)
        .or_else(|_| {
            let dir = store.root.join("staging").join(&name);
            crate::shm_cache::ensure_private_dir_all(&dir)?;
            Ok::<_, anyhow::Error>(dir)
        })
        .ok()?;
    let state_file = daemon_cache_dir.join("zygote_daemon.json");
    Some((
        current_exe,
        exe_mtime_sec,
        exe_mtime_nsec,
        daemon_cache_dir,
        state_file,
    ))
}

pub(super) fn check_existing_daemon_state(
    path: &Path,
    exe_mtime_sec: i64,
    exe_mtime_nsec: i64,
    kill_stale: bool,
) -> Option<(String, String)> {
    let content = fs::read_to_string(path).ok()?;
    let info: LocalZygoteDaemonInfo = serde_json::from_str(&content).ok()?;
    if !cfg!(test)
        && !path
            .parent()?
            .file_name()?
            .to_string_lossy()
            .starts_with("zygote_daemon_cas_")
    {
        return None;
    }
    if info.policy != daemon_policy() {
        return None;
    }
    if info.exe_mtime_sec != exe_mtime_sec
        || info.exe_mtime_nsec != exe_mtime_nsec
        || info.build_epoch != crate::TURBO_LEAN_BUILD_EPOCH
    {
        if kill_stale {
            terminate_and_remove_daemon_state_file(path);
            if let Some(parent) = path.parent().filter(|p| {
                p.file_name()
                    .is_some_and(|n| n.to_string_lossy().starts_with("zygote_daemon_cas_"))
            }) {
                let _ = fs::remove_dir_all(parent);
                crate::shm_cache::ensure_private_dir_all(parent).ok()?;
            }
        }
        return None;
    }
    #[cfg(unix)]
    {
        if info.pid > 0 && unsafe { libc::kill(info.pid as i32, 0) == 0 } {
            remember_daemon_socket(&format!("http://{}", info.addr), path);
            return Some((format!("http://{}", info.addr), info.auth_token));
        }
        None
    }
    #[cfg(not(unix))]
    {
        let sock_addr: std::net::SocketAddr = info.addr.parse().ok()?;
        if std::net::TcpStream::connect_timeout(&sock_addr, std::time::Duration::from_millis(10))
            .is_ok()
        {
            Some((format!("http://{}", info.addr), info.auth_token))
        } else {
            None
        }
    }
}

pub(crate) fn has_active_local_zygote_daemon(store: &TurboStore) -> bool {
    if daemon_disabled() {
        return false;
    }
    let Some((_, exe_mtime_sec, exe_mtime_nsec, _, state_file)) = current_exe_daemon_paths(store)
    else {
        return false;
    };
    check_existing_daemon_state(&state_file, exe_mtime_sec, exe_mtime_nsec, false)
        .or_else(|| {
            check_existing_daemon_state(
                &store.root.join("zygote_daemon.json"),
                exe_mtime_sec,
                exe_mtime_nsec,
                false,
            )
        })
        .is_some()
}

pub(crate) fn ensure_local_zygote_daemon_with_token(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
) -> Option<(String, String)> {
    if daemon_disabled() {
        return None;
    }
    let _lifecycle = lifecycle_lock(false).ok()?;
    let (current_exe, exe_mtime_sec, exe_mtime_nsec, daemon_cache_dir, state_file) =
        current_exe_daemon_paths(store)?;

    if let Some(hit) = check_existing_daemon_state(&state_file, exe_mtime_sec, exe_mtime_nsec, true)
        .or_else(|| {
            if env_vars.contains_key("TURBO_LEAN_REQUIRE_UNIX_DAEMON") {
                return None;
            }
            check_existing_daemon_state(
                &store.root.join("zygote_daemon.json"),
                exe_mtime_sec,
                exe_mtime_nsec,
                true,
            )
        })
    {
        return Some(hit);
    }

    let lock_path = daemon_cache_dir.join("zygote_daemon.lock");
    crate::shm_cache::with_shm_flock(&lock_path, false, || {
        if let Some(hit) =
            check_existing_daemon_state(&state_file, exe_mtime_sec, exe_mtime_nsec, true)
        {
            return Some(hit);
        }
        let port = TcpListener::bind("127.0.0.1:0")
            .ok()?
            .local_addr()
            .ok()?
            .port();
        let addr = format!("127.0.0.1:{}", port);
        let auth_token = generate_daemon_auth_token(std::process::id(), port);

        let mut cmd = Command::new(&current_exe);
        cmd.arg("--cache-dir")
            .arg(&daemon_cache_dir)
            .args(["serve", "--listen", &addr]);
        for (k, v) in env_vars {
            if !matches!(
                k.as_str(),
                "LEAN_PATH" | "TURBO_LEAN_PROJECT_DIR" | "TURBO_LEAN_CALLER_CWD"
            ) {
                cmd.env(k, v);
            }
        }
        cmd.env_remove("TURBO_LEAN_TIMEOUT_MS");
        cmd.env("TURBO_LEAN_DAEMON", "1")
            .env("TURBO_LEAN_DAEMON_TOKEN", &auth_token)
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null());
        for key in REQUEST_POLICY_KEYS
            .into_iter()
            .chain(MCP_RUNTIME_POLICY_KEYS)
        {
            cmd.env_remove(key);
            cmd.env_remove(format!("{key}_FROM_CONFIG"));
        }
        cmd.env(
            "TURBO_LEAN_DAEMON_SOCKET",
            daemon_cache_dir.join("daemon.sock"),
        );
        #[cfg(unix)]
        if std::env::var("TURBO_LEAN_KEEP_PROCESS_GROUP").is_err() {
            use std::os::unix::process::CommandExt;
            cmd.process_group(0);
        }
        cmd.env(
            "TURBO_LEAN_DAEMON_PARENT_STATE_FILE",
            store.root.join("zygote_daemon.json"),
        );
        cmd.env("TURBO_LEAN_DAEMON_STATE_FILE", &state_file).env(
            "TURBO_LEAN_STAGING_DIR",
            crate::shm_cache::staging_shm_dir(),
        );
        let mut child = cmd.spawn().ok()?;
        let pid = child.id();
        let url = format!("http://{}", addr);
        remember_daemon_socket(&url, &state_file);
        let connected = wait_for_mcp_transport_child(
            &url,
            &auth_token,
            &daemon_cache_dir.join("daemon.sock"),
            Some(&mut child),
        )
        .is_ok();
        if !connected {
            let _ = child.kill();
            let _ = child.wait();
            return None;
        }
        let info = LocalZygoteDaemonInfo {
            addr: addr.clone(),
            pid,
            exe_mtime_sec,
            exe_mtime_nsec,
            auth_token: auth_token.clone(),
            policy: daemon_policy(),
            build_epoch: crate::TURBO_LEAN_BUILD_EPOCH.to_string(),
        };
        if let Ok(json_bytes) = serde_json::to_vec(&info) {
            write_daemon_state_file_private(&state_file, &json_bytes);
            write_daemon_state_file_private(&store.root.join("zygote_daemon.json"), &json_bytes);
        }
        let url = format!("http://{}", addr);
        remember_daemon_socket(&url, &state_file);
        Some((url, auth_token))
    })
    .flatten()
}

pub(super) static LAST_LOCAL_DAEMON_TOKEN: std::sync::OnceLock<std::sync::Mutex<Option<String>>> =
    std::sync::OnceLock::new();

#[cfg(not(test))]
pub(super) fn wait_for_mcp_transport(url: &str, token: &str, socket: &Path) -> Result<()> {
    wait_for_mcp_transport_child(url, token, socket, None)
}

pub(super) fn wait_for_mcp_transport_child(
    url: &str,
    token: &str,
    socket: &Path,
    mut child: Option<&mut std::process::Child>,
) -> Result<()> {
    let started = std::time::Instant::now();
    loop {
        if socket.exists() {
            if let Ok(bytes) = http_request_with_timeout_and_token(
                "GET",
                &format!("{url}/health"),
                "application/json",
                &[],
                Some(250),
                Some(token),
                || {},
            ) {
                if serde_json::from_slice::<serde_json::Value>(&bytes)
                    .ok()
                    .and_then(|v| v.get("ok").and_then(|v| v.as_bool()))
                    == Some(true)
                {
                    return Ok(());
                }
            }
        }
        anyhow::ensure!(
            started.elapsed() < std::time::Duration::from_secs(10),
            "Shared daemon HTTP startup timed out"
        );
        if let Some(c) = child.as_deref_mut() {
            if c.try_wait().ok().flatten().is_some() {
                anyhow::bail!("Shared daemon exited before ready");
            }
        }
        std::thread::sleep(std::time::Duration::from_millis(5));
    }
}

#[cfg(not(test))]
pub(crate) fn forward_mcp_request(
    req: &serde_json::Value,
    project_dir: Option<&Path>,
    cache_dir: Option<&Path>,
) -> Result<serde_json::Value> {
    let store = TurboStore::open(cache_dir)?;
    let (_, sec, nsec, _, state_file) = current_exe_daemon_paths(&store).context("daemon paths")?;
    let existing = check_existing_daemon_state(&state_file, sec, nsec, false).filter(|_| {
        state_file
            .parent()
            .is_some_and(|p| p.join("daemon.sock").exists())
    });
    let (url, token) = existing
        .or_else(|| {
            let mut env = std::collections::HashMap::new();
            env.insert("TURBO_LEAN_REQUIRE_UNIX_DAEMON".into(), "1".into());
            ensure_local_zygote_daemon_with_token(&store, &env)
        })
        .context("Shared daemon startup failed")?;
    wait_for_mcp_transport(
        &url,
        &token,
        &state_file
            .parent()
            .context("daemon directory")?
            .join("daemon.sock"),
    )?;
    let absolute = |path: &Path| -> Result<PathBuf> {
        Ok(if path.is_absolute() {
            path.to_path_buf()
        } else {
            std::env::current_dir()?.join(path)
        })
    };
    let body = serde_json::to_vec(&serde_json::json!({
        "request": req,
        "project_dir": project_dir.map(absolute).transpose()?,
        "cache_dir": absolute(&store.root)?,
        "caller_cwd": std::env::current_dir()?,
        "policy_tags": mcp_caller_policy(),
        "timeout_ms": req.get("timeout_ms").and_then(|v| v.as_u64()).or_else(invocation_timeout_ms),
    }))?;
    let timeout = req
        .get("timeout_ms")
        .and_then(|v| v.as_u64())
        .or_else(invocation_timeout_ms);
    let started = std::time::Instant::now();
    let bytes = loop {
        match http_request_with_timeout_and_token(
            "POST",
            &format!("{url}/mcp"),
            "application/json",
            &body,
            timeout,
            Some(&token),
            || {},
        ) {
            Ok(bytes) => break bytes,
            Err(error)
                if started.elapsed() < std::time::Duration::from_secs(10)
                    && (is_expired_daemon_transport_error(&error)
                        || error.to_string().contains("(404)")) =>
            {
                std::thread::sleep(std::time::Duration::from_millis(10))
            }
            Err(error) => return Err(error),
        }
    };
    Ok(serde_json::from_slice(&bytes)?)
}

pub fn ensure_local_zygote_daemon(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
) -> Option<String> {
    ensure_local_zygote_daemon_with_token(store, env_vars).map(|(url, tok)| {
        if !tok.is_empty() {
            let m = LAST_LOCAL_DAEMON_TOKEN.get_or_init(|| std::sync::Mutex::new(None));
            if let Ok(mut g) = m.lock() {
                *g = Some(tok);
            }
        }
        url
    })
}

pub fn warm_local_zygote_daemon_nonblocking(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
) {
    if daemon_disabled() {
        return;
    }
    let root = store.root.clone();
    let env_vars = env_vars.clone();
    std::thread::spawn(move || {
        if let Ok(store) = TurboStore::open(Some(&root)) {
            let _ = ensure_local_zygote_daemon_with_token(&store, &env_vars);
        }
    });
}

pub(super) fn parse_check_shard_resp(resp_bytes: &[u8]) -> Result<Option<serde_json::Value>> {
    let resp_json: serde_json::Value = serde_json::from_slice(resp_bytes)?;
    let status = resp_json
        .get("status")
        .and_then(|v| v.as_str())
        .unwrap_or("");
    if status == "remote_theorem_verified" || status == "remote_theorem_cache_hit" {
        Ok(Some(resp_json))
    } else {
        Ok(None)
    }
}

pub(super) fn is_expired_daemon_transport_error(err: &anyhow::Error) -> bool {
    err.chain().any(|cause| {
        cause.downcast_ref::<std::io::Error>().is_some_and(|e| {
            matches!(
                e.kind(),
                std::io::ErrorKind::ConnectionRefused
                    | std::io::ErrorKind::ConnectionReset
                    | std::io::ErrorKind::ConnectionAborted
                    | std::io::ErrorKind::BrokenPipe
                    | std::io::ErrorKind::UnexpectedEof
                    | std::io::ErrorKind::NotConnected
            )
        })
    })
}

pub(super) fn extract_http_error_detail(err: anyhow::Error) -> anyhow::Error {
    let s = err.to_string();
    if let Some((_, json_part)) = s.split_once("): {") {
        let candidate = format!("{{{}", json_part);
        if let Ok(val) = serde_json::from_str::<serde_json::Value>(&candidate) {
            if let Some(msg) = val.get("error").and_then(|v| v.as_str()) {
                return anyhow::anyhow!("{}", msg);
            }
        }
    }
    err
}

/// `/check-shard` error `code` for a shard the zygote could not import: unavailable, not rejected.
pub(crate) const IMPORT_UNAVAILABLE_CODE: &str = "zygote_import_unavailable";

/// The `/check-shard` error the daemon reports with `IMPORT_UNAVAILABLE_CODE`.
#[derive(Debug)]
pub(crate) struct ZygoteImportUnavailable(pub String);

impl std::fmt::Display for ZygoteImportUnavailable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Zygote import unavailable for `{}`", self.0)
    }
}

impl std::error::Error for ZygoteImportUnavailable {}

/// `/check-shard` outcome: an expired daemon (no answer) or the structured
/// `IMPORT_UNAVAILABLE_CODE` (never message text, which the shard's diagnostics can contain)
/// means the zygote is unavailable (`Ok(None)`), so only then may an audited fallback run; any
/// other error is a rejection, which is final.
pub(super) fn finish_check_shard_request(
    response: Result<Vec<u8>>,
) -> Result<Option<serde_json::Value>> {
    match response {
        Ok(bytes) => parse_check_shard_resp(&bytes),
        Err(err) if is_expired_daemon_transport_error(&err) => Ok(None),
        Err(err) => {
            let unavailable = err
                .to_string()
                .split_once("): {")
                .and_then(|(_, body)| {
                    serde_json::from_str::<serde_json::Value>(&format!("{{{}", body)).ok()
                })
                .is_some_and(|v| {
                    v.get("code").and_then(|c| c.as_str()) == Some(IMPORT_UNAVAILABLE_CODE)
                });
            if unavailable {
                Ok(None)
            } else {
                Err(extract_http_error_detail(err))
            }
        }
    }
}

pub(crate) fn try_zygote_url_check_shard_inner_with_inflight_detailed(
    base_url: &str,
    req: &CheckShardHttpRequest,
    on_inflight: impl FnOnce(),
) -> Result<Option<serde_json::Value>> {
    if daemon_disabled() {
        return Ok(None);
    }
    let endpoint = format!("{}/check-shard", base_url.trim_end_matches('/'));
    let mut local_req = req.clone();
    local_req.skip_cas_lock = true;
    let body = check_request_body(&local_req)?;
    let cached_tok = LAST_LOCAL_DAEMON_TOKEN
        .get()
        .and_then(|m| m.lock().ok().and_then(|g| g.clone()));
    finish_check_shard_request(http_request_with_timeout_and_token(
        "POST",
        &endpoint,
        "application/json",
        &body,
        None,
        cached_tok.as_deref(),
        on_inflight,
    ))
}

pub fn try_local_zygote_check_shard_detailed(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
    req: &CheckShardHttpRequest,
) -> Result<Option<serde_json::Value>> {
    crate::module_builder::validate_lean_args(&req.lean_args)?;
    crate::splitter::reject_checking_weakening(&req.shard_source)?;
    let Some((base_url, auth_token)) = ensure_local_zygote_daemon_with_token(store, env_vars)
    else {
        return Ok(None);
    };
    let endpoint = format!("{}/check-shard", base_url.trim_end_matches('/'));
    let mut local_req = req.clone();
    local_req.skip_cas_lock = true;
    let body = check_request_body(&local_req)?;
    match http_request_with_timeout_and_token(
        "POST",
        &endpoint,
        "application/json",
        &body,
        None,
        Some(&auth_token),
        || {},
    ) {
        Err(e) if is_expired_daemon_transport_error(&e) => {
            if let Some((_, _, _, _, state_file)) = current_exe_daemon_paths(store) {
                terminate_and_remove_daemon_state_file(&state_file);
            }
            let Some((retry_url, retry_token)) =
                ensure_local_zygote_daemon_with_token(store, env_vars)
            else {
                return Ok(None);
            };
            let retry_endpoint = format!("{}/check-shard", retry_url.trim_end_matches('/'));
            finish_check_shard_request(http_request_with_timeout_and_token(
                "POST",
                &retry_endpoint,
                "application/json",
                &body,
                None,
                Some(&retry_token),
                || {},
            ))
        }
        response => finish_check_shard_request(response),
    }
}
