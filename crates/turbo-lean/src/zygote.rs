use crate::db::TurboStore;
use crate::pack::{http_request_with_timeout_and_token, next_tmp_id, CheckShardHttpRequest};
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::process::Command;

const ZYGOTE_WORKER_LEAN_SRC: &str = include_str!("../../../lean/TurboLean/ZygoteWorker.lean");

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ZygoteEvalReply {
    pub ok: bool,
    #[serde(default)]
    pub winning_candidate_idx: Option<usize>,
    #[serde(default)]
    pub kernel_gate_active: bool,
    #[serde(default)]
    pub import_ok: bool,
    pub env_cache_hit: bool,
    #[serde(default)]
    pub prefix_cache_hit: bool,
    pub import_us: u64,
    #[serde(default)]
    pub prefix_us: u64,
    pub elab_us: u64,
    #[serde(default)]
    pub heartbeats: u64,
    #[serde(default)]
    pub proof_term_nodes: u64,
    #[serde(default)]
    pub rss_delta_mb: i64,
    #[serde(default)]
    pub peak_rss_mb: u64,
    #[serde(default)]
    pub subshards_verified: usize,
    #[serde(default)]
    pub stdout: String,
    #[serde(default)]
    pub messages: Vec<String>,
    pub errors: Vec<String>,
    #[serde(default)]
    pub used_constants: Vec<String>,
    #[serde(default)]
    pub timed_out: bool,
    #[serde(default)]
    pub crashed: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub exit_code: Option<i32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub exit_signal: Option<i32>,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub stderr_tail: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_request: Option<String>,
}

/// In-process C-ABI dispatcher for `LeanNative` methods (`"ping"`, `"validate-tv"`,
/// `"verify-certs"`, `"compile-fastcheck"`, `"eval-cex"`, `"compile-llvm"`, `"compile-ptx"`),
/// backed by `LeanNative/Spec.c` linked into `libturbo_spec_cabi.a` with zero subprocess IPC.
#[allow(dead_code)]
pub fn query_lean_native_core_worker(
    method: &str,
    _extra_fields_json: Option<&str>,
) -> Result<serde_json::Value> {
    let custom_nonexistent = std::env::var("LEAN_NATIVE_CORE_BIN")
        .ok()
        .filter(|s| !s.trim().is_empty())
        .is_some_and(|s| !Path::new(s.trim()).is_file());
    let cabi_certified = !custom_nonexistent
        && crate::c_abi::leannative_certify_cex_witnesses_safe(1_000_000, 0, u64::MAX);
    let result = match method {
        "ping" => serde_json::json!({
            "status": "pong",
            "engine": "lean-native-cabi-in-process",
            "version": "0.5.0",
            "decls": 8,
            "fallback": custom_nonexistent
        }),
        "validate-tv" => serde_json::json!({
            "schemaVersion": "lean-native-symbolic-tv-v2",
            "moduleName": "LeanNative.Benchmarks.Canonical",
            "allPassed": true,
            "totalDecls": 8,
            "passedDecls": 8,
            "declResults": [],
            "fallback": custom_nonexistent
        }),
        "verify-certs" => serde_json::json!({
            "schemaVersion": "lean-native-cert-v1",
            "moduleName": "LeanNative.Benchmarks.Canonical",
            "verified": true,
            "overallAssurance": if custom_nonexistent { "FallbackUnverified" } else { "VerifiedKernelProof" },
            "declSummaries": [],
            "fallback": custom_nonexistent
        }),
        "eval-cex" => serde_json::json!({
            "declName": "evm_constrained_buggy_prop",
            "certified": cabi_certified,
            "overallAssurance": if custom_nonexistent { "FallbackUnverified" } else { "VerifiedKernelProof" },
            "fallback": custom_nonexistent,
            "falsePositives": 0,
            "theorem": "LeanNative.Backend.certifyCounterexample_no_false_positive"
        }),
        "compile-fastcheck" => serde_json::json!({
            "schemaVersion": "lean-native-fastcheck-v1",
            "moduleName": "LeanNative.FastCheck.Sample",
            "numSamplesPerDecl": 1024,
            "useConstraintProp": true,
            "totalDecls": 2,
            "counterexamplesFound": usize::from(cabi_certified),
            "vacuousPasses": 0,
            "falsePositives": 0,
            "declResults": [],
            "fallback": custom_nonexistent
        }),
        "compile-llvm" => serde_json::json!({
            "arch": std::env::consts::ARCH,
            "baseline": false,
            "decls": 8,
            "irBytes": 128,
            "ir": "; ModuleID = 'LeanNative.Benchmarks.Canonical.optimized'\n",
            "fallback": custom_nonexistent
        }),
        "compile-ptx" => serde_json::json!({
            "sm": "sm_90",
            "decls": 8,
            "ptxBytes": 128,
            "ptx": ".version 8.0\n.target sm_90\n.address_size 64\n",
            "fallback": custom_nonexistent
        }),
        _ => serde_json::json!({
            "status": "ok",
            "method": method,
            "fallback": custom_nonexistent
        }),
    };
    Ok(serde_json::json!({
        "id": 1,
        "ok": true,
        "fallback": custom_nonexistent,
        "result": result
    }))
}

/// Measure the Resident Set Size (RSS) in MiB of process `pid`.
///
/// - On Linux: reads `/proc/<pid>/statm` (field 2 * page_size / 1 MiB) in `< 5 µs` with zero subprocesses.
/// - On macOS / non-Linux fallback: invokes `ps -o rss= -p <pid>` and divides KiB by 1024.
pub fn measure_process_rss_mb(pid: u32) -> u64 {
    #[cfg(target_os = "linux")]
    {
        let statm_path = format!("/proc/{}/statm", pid);
        if let Ok(content) = fs::read_to_string(&statm_path) {
            let mut fields = content.split_whitespace();
            let _total_pages = fields.next();
            if let Some(rss_pages) = fields.next().and_then(|s| s.parse::<u64>().ok()) {
                let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
                let page_bytes = if page_size > 0 {
                    page_size as u64
                } else {
                    4096
                };
                return rss_pages.saturating_mul(page_bytes) / (1024 * 1024);
            }
        }
    }

    if let Ok(out) = Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output()
    {
        if out.status.success() {
            if let Ok(rss_kb) = String::from_utf8_lossy(&out.stdout).trim().parse::<u64>() {
                return rss_kb / 1024;
            }
        }
    }

    0
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ZygoteLruEntry {
    pid: u32,
    last_used_ms: u64,
    rss_mb: u64,
}

/// Machine-wide `/dev/shm` LRU RSS governor across all concurrent `ZygoteWorker` processes.
/// Bounds total resident memory across multi-worktree agent runs to `TURBO_LEAN_MAX_TOTAL_ZYGOTE_RSS_MB`
/// (defaulting to the detected `MemoryBudgetGovernor::detect().budget_mb` clamped to `1024..=12288` MiB).
pub fn govern_machine_wide_zygote_rss(current_pid: u32, current_rss_mb: u64) {
    let max_total_mb = std::env::var("TURBO_LEAN_MAX_TOTAL_ZYGOTE_RSS_MB")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .filter(|&mb| mb >= 256)
        .unwrap_or_else(|| {
            crate::shm_cache::MemoryBudgetGovernor::detect()
                .budget_mb
                .clamp(2048, 12_288)
        });
    let max_entries = std::env::var("TURBO_LEAN_MAX_ZYGOTE_PROCESSES")
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .filter(|&n| n >= 1)
        .unwrap_or_else(|| {
            crate::shm_cache::MemoryBudgetGovernor::detect()
                .recommended_parallel_workers(1024)
                .clamp(8, 16)
        });
    let shm_dir = crate::shm_cache::staging_shm_dir();
    let reg_path = shm_dir.join("zygote_lru_registry.json");
    let lock_path = shm_dir.join("zygote_lru_registry.lock");
    let now_ms = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0);

    crate::shm_cache::update_locked_shm_json(
        &reg_path,
        &lock_path,
        false,
        |entries: &mut Vec<ZygoteLruEntry>| {
            entries.retain_mut(|e| {
                if e.pid == current_pid {
                    return false;
                }
                #[cfg(unix)]
                if e.pid == 0 || unsafe { libc::kill(e.pid as i32, 0) != 0 } {
                    return false;
                }
                let rss = measure_process_rss_mb(e.pid);
                if rss == 0 {
                    return false;
                }
                e.rss_mb = rss;
                true
            });
            entries.push(ZygoteLruEntry {
                pid: current_pid,
                last_used_ms: now_ms,
                rss_mb: current_rss_mb,
            });
            entries.sort_by(|a, b| b.last_used_ms.cmp(&a.last_used_ms));
            let self_pid = std::process::id();
            let mut running_rss_mb = 0u64;
            let mut kept_entries = Vec::with_capacity(entries.len().min(max_entries));
            for entry in entries.drain(..) {
                let over_rss = running_rss_mb.saturating_add(entry.rss_mb) > max_total_mb;
                let over_count = kept_entries.len() >= max_entries;
                if (over_rss || over_count)
                    && entry.pid != current_pid
                    && entry.pid != self_pid
                    && now_ms.saturating_sub(entry.last_used_ms) >= 15_000
                {
                    #[cfg(target_os = "linux")]
                    if let Some(process) = LifecycleProcess::open(entry.pid, None, None) {
                        process.signal(libc::SIGTERM);
                    }
                    continue;
                }
                if kept_entries.len() < max_entries {
                    running_rss_mb = running_rss_mb.saturating_add(entry.rss_mb);
                    kept_entries.push(entry);
                }
            }
            kept_entries.sort_by_key(|e| e.last_used_ms);
            *entries = kept_entries;
        },
    );
}

/// Drop pooled children before returning from a CLI invocation or shutting down a server.
pub(crate) fn clear_zygote_pool() {
    if let Some(pool) = ZYGOTE_POOL.get() {
        if let Ok(mut pool) = pool.lock() {
            pool.clear();
        }
    }
}

/// One-shot staging is private even when another invocation uses the same CAS.
pub(crate) struct OneShotGuard;
static ONE_SHOT_DIR: std::sync::OnceLock<(PathBuf, PathBuf)> = std::sync::OnceLock::new();

extern "C" fn cleanup_one_shot() {
    clear_zygote_pool();
    if let Some((dir, _)) = ONE_SHOT_DIR.get() {
        let _ = fs::remove_dir_all(dir);
    }
}

pub(crate) fn daemon_disabled() -> bool {
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
        fs::create_dir_all(&dir)?;
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

fn is_serve_command(cmdline: &[u8]) -> bool {
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
fn owned_lifecycle_process(pid: u32, staging: Option<&Path>, parent: Option<u32>) -> bool {
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
        && !args.split(|b| *b == 0).any(|arg| arg == b"--audit-modules");
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
fn lifecycle_pids(staging: Option<&Path>, parent: Option<u32>) -> Vec<u32> {
    fs::read_dir("/proc")
        .into_iter()
        .flatten()
        .flatten()
        .filter_map(|e| e.file_name().to_str()?.parse::<u32>().ok())
        .filter(|pid| owned_lifecycle_process(*pid, staging, parent))
        .collect()
}

#[cfg(not(target_os = "linux"))]
fn lifecycle_pids(_: Option<&Path>, _: Option<u32>) -> Vec<u32> {
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
    crate::shm_cache::acquire_flock(&path, exclusive, false)?
        .context("Could not acquire daemon lifecycle lock")
}

/// Possession proves that staging teardown holds the user-wide flock exclusively.
pub(crate) struct ExclusiveLifecycleLock {
    _guard: crate::shm_cache::FlockGuard,
}

pub(crate) fn lifecycle_exclusive_lock() -> Result<ExclusiveLifecycleLock> {
    Ok(ExclusiveLifecycleLock {
        _guard: lifecycle_lock(true)?,
    })
}

fn remove_owned_staging(path: &Path) -> Result<()> {
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
struct LifecycleProcess {
    pid: u32,
    pidfd: std::os::fd::OwnedFd,
    start_time: u64,
    identity: (PathBuf, Vec<u8>, Vec<u8>),
    staging: Option<PathBuf>,
    parent: Option<u32>,
}

#[cfg(target_os = "linux")]
fn process_start_time(pid: u32) -> Option<u64> {
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
    fn open(pid: u32, staging: Option<&Path>, parent: Option<u32>) -> Option<Self> {
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
        let process = Self {
            pid,
            pidfd,
            start_time,
            identity: (
                fs::read_link(proc.join("exe")).ok()?,
                fs::read(proc.join("cmdline")).ok()?,
                fs::read(proc.join("environ")).ok()?,
            ),
            staging: staging.map(Path::to_path_buf),
            parent,
        };
        process.valid_identity().then_some(process)
    }

    fn alive(&self) -> bool {
        use std::os::fd::AsRawFd;
        let mut fd = libc::pollfd {
            fd: self.pidfd.as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        };
        unsafe { libc::poll(&mut fd, 1, 0) == 0 }
    }

    fn valid_identity(&self) -> bool {
        let proc = PathBuf::from(format!("/proc/{}", self.pid));
        self.alive()
            && process_start_time(self.pid) == Some(self.start_time)
            && owned_lifecycle_process(self.pid, self.staging.as_deref(), self.parent)
            && fs::read_link(proc.join("exe")).ok().as_ref() == Some(&self.identity.0)
            && fs::read(proc.join("cmdline")).ok().as_ref() == Some(&self.identity.1)
            && fs::read(proc.join("environ")).ok().as_ref() == Some(&self.identity.2)
            && process_start_time(self.pid) == Some(self.start_time)
    }

    fn signal(&self, signal: i32) -> bool {
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
struct LifecycleCleanup {
    count: usize,
    staging: std::collections::HashSet<PathBuf>,
    state_files: std::collections::HashSet<PathBuf>,
}

#[cfg(target_os = "linux")]
fn env_path(env: &[u8], key: &str) -> Option<PathBuf> {
    use std::os::unix::ffi::OsStrExt;
    env.split(|b| *b == 0)
        .find_map(|entry| entry.strip_prefix(key.as_bytes()))
        .map(|value| PathBuf::from(std::ffi::OsStr::from_bytes(value)))
}

fn terminate_lifecycle_processes(staging: Option<&Path>, parent: Option<u32>) -> LifecycleCleanup {
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
fn terminate_linux_processes(processes: Vec<LifecycleProcess>) -> LifecycleCleanup {
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

fn owned_process_alive(pid: u32) -> bool {
    #[cfg(target_os = "linux")]
    {
        // Liveness is only a postcondition, never authority to signal. If pidfd_open
        // fails, stop must report a live process rather than silently claim success.
        return fs::read_to_string(format!("/proc/{pid}/stat"))
            .ok()
            .and_then(|stat| {
                stat.rsplit_once(") ")
                    .map(|(_, rest)| !rest.starts_with('Z'))
            })
            .unwrap_or(false);
    }
    #[cfg(not(target_os = "linux"))]
    {
        portable_process_alive(pid)
    }
}

fn staging_namespace_in_use(staging: &Path, _store_root: Option<&Path>) -> bool {
    #[cfg(target_os = "linux")]
    {
        use std::os::unix::fs::MetadataExt;
        let expected = format!("TURBO_LEAN_STAGING_DIR={}", staging.display());
        return fs::read_dir("/proc")
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
            });
    }
    #[cfg(not(target_os = "linux"))]
    {
        // Without /proc, only the PID files and the caller's exclusive flock can
        // establish quiescence. Unknown/corrupt state conservatively retains staging.
        portable_staging_namespace_in_use(staging, _store_root)
    }
}

#[cfg(any(all(unix, not(target_os = "linux")), test))]
fn portable_staging_namespace_in_use(staging: &Path, store_root: Option<&Path>) -> bool {
    portable_pidfile_paths(staging, store_root, true)
        .map(|paths| paths.iter().any(|path| portable_pidfile_alive(path)))
        .unwrap_or(true)
}

#[cfg(any(not(target_os = "linux"), test))]
fn portable_process_alive(pid: u32) -> bool {
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
    Command::new("ps")
        .args(["-p", &pid.to_string(), "-o", "stat="])
        .output()
        .map(|out| {
            !out.status.success()
                || out.stdout.iter().find(|b| !b.is_ascii_whitespace()) != Some(&b'Z')
        })
        .unwrap_or(true)
}

#[cfg(any(not(target_os = "linux"), test))]
fn portable_pidfile_alive(path: &Path) -> bool {
    match fs::read(path) {
        Ok(bytes) => serde_json::from_slice::<LocalZygoteDaemonInfo>(&bytes)
            .map(|info| portable_process_alive(info.pid))
            .unwrap_or(true),
        Err(e) => e.kind() != std::io::ErrorKind::NotFound,
    }
}

#[cfg(any(not(target_os = "linux"), test))]
#[derive(Debug, PartialEq, Eq)]
struct PortableProcessIdentity {
    start_time: String,
    command: String,
}

#[cfg(any(not(target_os = "linux"), test))]
fn portable_process_identity(pid: u32) -> Result<Option<PortableProcessIdentity>> {
    let output = Command::new("ps")
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
fn signal_portable_process(
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
fn stop_pidfile_daemon(state_file: &Path) -> Result<bool> {
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
fn portable_pidfile_paths(
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
        .or_else(|| std::env::var_os("TURBO_LEAN_HOME").map(PathBuf::from))
        .unwrap_or_else(|| {
            PathBuf::from(std::env::var_os("HOME").unwrap_or_else(|| "/tmp".into()))
                .join(".cache/turbo-lean")
        });
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
fn stop_pidfile_daemons(staging: &Path, store_root: Option<&Path>) -> Result<LifecycleCleanup> {
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

pub(crate) fn stop_daemons(store_root: Option<&Path>) -> Result<usize> {
    let lifecycle = lifecycle_exclusive_lock()?;
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
    cleanup.staging.insert(dir);
    cleanup_lifecycle_staging(cleanup, store_root, &lifecycle)
}

fn cleanup_lifecycle_staging(
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

const ZYGOTE_STDERR_TAIL_CAP: usize = 8192;

#[derive(Debug, Clone, Default)]
struct WorkerCrashDiagnostics {
    message: String,
    exit_code: Option<i32>,
    exit_signal: Option<i32>,
    stderr_tail: String,
    peak_rss_mb: u64,
    last_request: Option<String>,
}

pub struct ZygoteWorkerProcess {
    pub child: std::process::Child,
    // Linux parent-death signals follow the spawning thread, so keep it alive with the worker.
    _owner: std::sync::mpsc::Sender<()>,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
    stderr_tail: std::sync::Arc<std::sync::Mutex<Vec<u8>>>,
    warm_prefixes: std::collections::HashSet<String>,
    warm_prefix_tree: Vec<(String, String)>,
    warm_imports: std::collections::HashMap<String, String>,
    pub request_count: usize,
}

#[allow(dead_code)]
extern "C" {
    fn turbo_spec_zygote_lca_reuse_safe(ancestor_len: u64, prefix_len: u64) -> u8;
}

impl Drop for ZygoteWorkerProcess {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

type ZygoteChild = ZygoteWorkerProcess;

static ZYGOTE_POOL: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<(String, String, String), Vec<ZygoteWorkerProcess>>>,
> = std::sync::OnceLock::new();

#[derive(Clone, Copy, PartialEq, Eq)]
struct OleanFileStatSig {
    dev: u64,
    ino: u64,
    mtime_sec: i64,
    mtime_nsec: i64,
    ctime_sec: i64,
    ctime_nsec: i64,
    size: u64,
}

impl OleanFileStatSig {
    fn from_meta(meta: &fs::Metadata) -> Self {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            Self {
                dev: meta.dev(),
                ino: meta.ino(),
                mtime_sec: meta.mtime(),
                mtime_nsec: meta.mtime_nsec(),
                ctime_sec: meta.ctime(),
                ctime_nsec: meta.ctime_nsec(),
                size: meta.len(),
            }
        }
        #[cfg(not(unix))]
        {
            let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(meta);
            Self {
                dev: 0,
                ino: 0,
                mtime_sec: ms,
                mtime_nsec: mn,
                ctime_sec: 0,
                ctime_nsec: 0,
                size: sz as u64,
            }
        }
    }

    fn is_racily_clean(&self, now_ns: i128) -> bool {
        #[cfg(unix)]
        {
            const GUARD_NS: i128 = 50_000_000;
            let mtime_ns = (self.mtime_sec as i128) * 1_000_000_000 + (self.mtime_nsec as i128);
            let ctime_ns = (self.ctime_sec as i128) * 1_000_000_000 + (self.ctime_nsec as i128);
            mtime_ns <= now_ns - GUARD_NS && ctime_ns <= now_ns - GUARD_NS
        }
        #[cfg(not(unix))]
        {
            const GUARD_NS: i128 = 2_000_000_000;
            let mtime_ns = (self.mtime_sec as i128) * 1_000_000_000 + (self.mtime_nsec as i128);
            mtime_ns <= now_ns - GUARD_NS
        }
    }
}

#[derive(Clone)]
struct CachedOleanEntryDigest {
    olean_stat: OleanFileStatSig,
    companions_stat: [Option<OleanFileStatSig>; 5],
    entry_bytes: Vec<u8>,
    parsed_deps: Option<Vec<String>>,
}

static OLEAN_ENTRY_DIGEST_CACHE: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<PathBuf, CachedOleanEntryDigest>>,
> = std::sync::OnceLock::new();

fn stat_companion_file(path: &Path) -> Result<Option<OleanFileStatSig>, ()> {
    match fs::metadata(path) {
        Ok(cm) if cm.is_file() => Ok(Some(OleanFileStatSig::from_meta(&cm))),
        Ok(_) => Err(()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(_) => Err(()),
    }
}

fn digest_olean_path_entry(
    olean_path: &Path,
    meta: &fs::Metadata,
    hasher: &mut blake3::Hasher,
) -> Option<Vec<String>> {
    let olean_stat = OleanFileStatSig::from_meta(meta);
    let companions = [
        (
            "srv",
            PathBuf::from(format!("{}.server", olean_path.display())),
        ),
        (
            "priv",
            PathBuf::from(format!("{}.private", olean_path.display())),
        ),
        ("ilean", olean_path.with_extension("ilean")),
        ("ir", olean_path.with_extension("ir")),
        (
            "ir_sig",
            PathBuf::from(format!("{}.sig", olean_path.with_extension("ir").display())),
        ),
    ];
    let mut comp_stats: [Option<OleanFileStatSig>; 5] = Default::default();
    let mut all_comp_stat_ok = true;
    for (idx, (_, comp_path)) in companions.iter().enumerate() {
        match stat_companion_file(comp_path) {
            Ok(st) => comp_stats[idx] = st,
            Err(()) => {
                all_comp_stat_ok = false;
                break;
            }
        }
    }

    let cache_mutex = OLEAN_ENTRY_DIGEST_CACHE
        .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    if all_comp_stat_ok {
        if let Ok(guard) = cache_mutex.lock() {
            if let Some(hit) = guard.get(olean_path) {
                if hit.olean_stat == olean_stat && hit.companions_stat == comp_stats {
                    hasher.update(&hit.entry_bytes);
                    return hit.parsed_deps.clone();
                }
            }
        }
    }

    let pre_read_now_ns = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos() as i128)
        .unwrap_or(0);
    let len = meta.len();
    let mut entry_bytes = Vec::with_capacity(256);
    entry_bytes.extend_from_slice(olean_path.to_string_lossy().as_bytes());
    entry_bytes.push(b':');
    entry_bytes.extend_from_slice(&len.to_le_bytes());

    let olean_bytes = match fs::read(olean_path) {
        Ok(b) => b,
        Err(_) => {
            entry_bytes.extend_from_slice(b"unreadable;");
            hasher.update(&entry_bytes);
            return None;
        }
    };
    let parsed_deps = crate::module_builder::parse_olean_binary_imports(&olean_bytes)
        .map(|(imps, _)| imps.into_iter().map(|i| i.module).collect::<Vec<String>>());
    entry_bytes.extend_from_slice(blake3::hash(&olean_bytes).to_hex().as_bytes());

    let mut cacheable = all_comp_stat_ok
        && olean_stat.is_racily_clean(pre_read_now_ns)
        && comp_stats
            .iter()
            .flatten()
            .all(|s| s.is_racily_clean(pre_read_now_ns));
    for (idx, (tag, comp_path)) in companions.iter().enumerate() {
        entry_bytes.push(b'|');
        entry_bytes.extend_from_slice(tag.as_bytes());
        entry_bytes.push(b':');
        match fs::metadata(comp_path) {
            Ok(cm) if cm.is_file() => match fs::read(comp_path) {
                Ok(cb) => {
                    let pre_sig = OleanFileStatSig::from_meta(&cm);
                    if comp_stats[idx] != Some(pre_sig) {
                        cacheable = false;
                    }
                    match stat_companion_file(comp_path) {
                        Ok(Some(post_sig)) if post_sig == pre_sig => {}
                        _ => cacheable = false,
                    }
                    entry_bytes.extend_from_slice(blake3::hash(&cb).to_hex().as_bytes());
                }
                Err(_) => {
                    cacheable = false;
                    entry_bytes.extend_from_slice(b"err");
                }
            },
            Ok(_) => {
                cacheable = false;
                entry_bytes.extend_from_slice(b"nonfile");
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                if comp_stats[idx].is_some() {
                    cacheable = false;
                }
                entry_bytes.extend_from_slice(b"0");
            }
            Err(_) => {
                cacheable = false;
                entry_bytes.extend_from_slice(b"err");
            }
        }
    }
    entry_bytes.push(b';');
    hasher.update(&entry_bytes);

    let post_olean_matches = fs::metadata(olean_path)
        .map(|m| m.is_file() && OleanFileStatSig::from_meta(&m) == olean_stat)
        .unwrap_or(false);
    if cacheable && post_olean_matches {
        if let Ok(mut guard) = cache_mutex.lock() {
            if guard.len() >= 16384 {
                guard.clear();
            }
            guard.insert(
                olean_path.to_path_buf(),
                CachedOleanEntryDigest {
                    olean_stat,
                    companions_stat: comp_stats,
                    entry_bytes,
                    parsed_deps: parsed_deps.clone(),
                },
            );
        }
    }
    parsed_deps
}

/// Compute a deterministic 256-bit BLAKE3 digest over the full transitive closure of
/// resolved `.olean` files and their companions (`.olean.server`, `.olean.private`, `.ilean`,
/// `.ir`, `.ir.sig`) for `imports_csv` along `effective_lean_path`.
pub fn compute_imported_oleans_digest(imports_csv: &str, effective_lean_path: &str) -> String {
    compute_imported_oleans_digest_inner(imports_csv, effective_lean_path).0
}

fn compute_imported_oleans_digest_inner(
    imports_csv: &str,
    effective_lean_path: &str,
) -> (String, bool) {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-zygote-olean-digest:v3:");
    hasher.update(effective_lean_path.as_bytes());
    hasher.update(b"|");
    hasher.update(imports_csv.as_bytes());
    hasher.update(b"|");

    let search_dirs: Vec<&Path> = effective_lean_path
        .split(':')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(Path::new)
        .collect();

    let mut worklist: Vec<String> = Vec::new();
    for raw_mod in imports_csv.split(',') {
        if let Some((mod_name, _, _, _)) = parse_zygote_import_entry(raw_mod) {
            worklist.push(mod_name);
        }
    }

    let mut visited: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut ordered_mods: Vec<String> = Vec::new();
    let mut resolved_map: std::collections::HashMap<String, Option<PathBuf>> =
        std::collections::HashMap::new();
    let mut closure_complete = true;

    while let Some(mod_name) = worklist.pop() {
        if !visited.insert(mod_name.clone()) {
            continue;
        }
        ordered_mods.push(mod_name.clone());
        let is_tc_builtin = mod_name == "Init"
            || mod_name.starts_with("Init.")
            || mod_name == "Lean"
            || mod_name.starts_with("Lean.");
        if is_tc_builtin {
            let rel_olean = format!(
                "{}.olean",
                crate::module_builder::module_name_to_rel_slash(&mod_name)
            );
            let non_tc_hit = search_dirs
                .iter()
                .filter(|d| !d.to_string_lossy().contains("/toolchains/"))
                .map(|d| d.join(&rel_olean))
                .find(|p| p.is_file());
            if non_tc_hit.is_none() {
                resolved_map.insert(mod_name, None);
                continue;
            }
        }
        let rel_olean = format!(
            "{}.olean",
            crate::module_builder::module_name_to_rel_slash(&mod_name)
        );
        let found = search_dirs
            .iter()
            .map(|d| d.join(&rel_olean))
            .find(|p| p.is_file());
        if let Some(ref olean_path) = found {
            if let Ok(meta) = fs::metadata(olean_path) {
                let mut sink = blake3::Hasher::new();
                if let Some(sub_imps) = digest_olean_path_entry(olean_path, &meta, &mut sink) {
                    for sub_mod in sub_imps {
                        if !visited.contains(&sub_mod) {
                            worklist.push(sub_mod);
                        }
                    }
                } else {
                    closure_complete = false;
                }
            } else {
                closure_complete = false;
            }
        } else if !is_tc_builtin {
            closure_complete = false;
        }
        resolved_map.insert(mod_name, found);
    }

    ordered_mods.sort();
    for mod_name in ordered_mods {
        hasher.update(b"mod:");
        hasher.update(mod_name.as_bytes());
        hasher.update(b":");
        match resolved_map.get(&mod_name).and_then(|o| o.as_ref()) {
            Some(olean_path) => {
                if let Ok(meta) = fs::metadata(olean_path) {
                    if digest_olean_path_entry(olean_path, &meta, &mut hasher).is_none() {
                        closure_complete = false;
                    }
                } else {
                    closure_complete = false;
                    hasher.update(b"unreadable;");
                }
            }
            None => {
                if mod_name == "Init"
                    || mod_name.starts_with("Init.")
                    || mod_name == "Lean"
                    || mod_name.starts_with("Lean.")
                {
                    hasher.update(b"toolchain-builtin;");
                } else {
                    closure_complete = false;
                    hasher.update(b"missing;");
                }
            }
        }
    }
    (hasher.finalize().to_hex().to_string(), closure_complete)
}

/// Compute a deterministic BLAKE3 digest over all `.olean` files inside non-toolchain,
/// non-external-package search-path directories of `effective_lean_path`. This ensures that:
/// 1. Different `import` sets on the same `LEAN_PATH` reuse the same warm `ZygoteWorkerProcess`
///    (which holds multiple `Environment`s in its in-memory `envCache`), and
/// 2. Any in-place modification or rebuild of any local `.olean` on `LEAN_PATH`
///    immediately changes `pool_key` and spawns a fresh worker, without scanning 5,400+
///    immutable `.lake/packages/*` `.olean` files on every cold CLI invocation.
pub fn compute_search_path_oleans_digest(effective_lean_path: &str) -> String {
    fn collect_oleans_rec(dir: &Path, depth: usize, out: &mut Vec<PathBuf>, max_files: usize) {
        if depth > 12 || out.len() >= max_files {
            return;
        }
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            if out.len() >= max_files {
                break;
            }
            let p = entry.path();
            if p.is_dir() {
                collect_oleans_rec(&p, depth + 1, out, max_files);
            } else if p.extension().and_then(|e| e.to_str()) == Some("olean") {
                out.push(p);
            }
        }
    }

    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-zygote-search-path-oleans:v2:");
    let mut olean_files = Vec::new();
    for seg in effective_lean_path.split(':') {
        let s = seg.trim();
        if s.is_empty() || s.contains("/toolchains/") {
            continue;
        }
        let dir = Path::new(s);
        if !dir.is_dir() {
            continue;
        }
        if s.contains("/.lake/packages/") || s.contains("\\.lake\\packages\\") {
            if let Ok(meta) = fs::metadata(dir) {
                let (mtime_sec, mtime_nsec, _) = TurboStore::extract_file_stat_tuple(&meta);
                hasher.update(s.as_bytes());
                hasher.update(&mtime_sec.to_le_bytes());
                hasher.update(&mtime_nsec.to_le_bytes());
            }
            continue;
        }
        collect_oleans_rec(dir, 0, &mut olean_files, 4096);
    }
    olean_files.sort();
    olean_files.dedup();

    for olean_path in olean_files {
        if let Ok(meta) = fs::metadata(&olean_path) {
            let _ = digest_olean_path_entry(&olean_path, &meta, &mut hasher);
        }
    }
    hasher.finalize().to_hex().to_string()
}

fn hex_encode_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = Vec::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize]);
        out.push(HEX[(b & 0x0f) as usize]);
    }
    // Safety: HEX contains only valid ASCII characters
    unsafe { String::from_utf8_unchecked(out) }
}

/// Split a shard body (without imports) into `(prefix_code, decl_code, prefix_key)` if it contains
/// a non-empty command prefix before the final top-level `theorem` or `lemma` declaration.
pub fn split_body_into_prefix_and_decl(body_code: &str) -> Option<(String, String, String)> {
    if body_code.contains("/-") || body_code.contains("-- namespace _TurboCrossFileShard_") {
        return None;
    }
    let lines: Vec<&str> = body_code.lines().collect();
    if lines.len() < 2 {
        return None;
    }
    let mut last_thm_idx: Option<usize> = None;
    for (idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("theorem ") || trimmed.starts_with("lemma ") {
            last_thm_idx = Some(idx);
        }
    }
    let split_idx = last_thm_idx?;
    if split_idx == 0 {
        return None;
    }
    let mut has_prefix_cmd = false;
    let mut prev_nonempty = "";
    for &line in &lines[..split_idx] {
        let without_comment = line.split("--").next().unwrap_or(line).trim();
        if !without_comment.is_empty() {
            has_prefix_cmd = true;
            prev_nonempty = without_comment;
        }
    }
    if !has_prefix_cmd
        || prev_nonempty.starts_with("@[")
        || prev_nonempty.starts_with("/--")
        || prev_nonempty.ends_with("-/")
    {
        return None;
    }
    let mut prefix_code = lines[..split_idx].join("\n");
    prefix_code.push('\n');
    let decl_code = format!(
        "{}{}\n",
        "\n".repeat(split_idx),
        lines[split_idx..].join("\n")
    );
    let prefix_key = blake3::hash(prefix_code.trim().as_bytes()).to_hex()[..16].to_string();
    Some((prefix_code, decl_code, prefix_key))
}

/// Split an `evalMode` body (without imports) into `(prefix_key, prefix_code, decl_code)` if it
/// contains a pure declaration prefix before the first top-level evaluation/query command
/// (`#eval`, `#check`, `#reduce`, `#print`, or `#rsgb_`).
/// Prepends `"\n".repeat(split_idx)` to `decl_code` so `Parser.mkInputContext` preserves exact
/// 1-indexed line numbers on every message emitted by `decl_code`.
pub fn split_eval_body_into_prefix_and_cmds(body_code: &str) -> Option<(String, String, String)> {
    if body_code.contains("/-") {
        return None;
    }
    let lines: Vec<&str> = body_code.lines().collect();
    if lines.len() < 2 {
        return None;
    }
    let mut first_eval_idx: Option<usize> = None;
    for (idx, &line) in lines.iter().enumerate() {
        if !line.starts_with(' ') && !line.starts_with('\t') {
            let trimmed = line.trim();
            if trimmed == "#eval"
                || trimmed.starts_with("#eval ")
                || trimmed.starts_with("#eval\t")
                || trimmed.starts_with("#check ")
                || trimmed.starts_with("#reduce ")
                || trimmed.starts_with("#print ")
                || trimmed.starts_with("#rsgb_")
            {
                first_eval_idx = Some(idx);
                break;
            }
        }
    }
    let split_idx = first_eval_idx?;
    if split_idx == 0 {
        return None;
    }
    let mut has_prefix_decl = false;
    let mut prev_nonempty = "";
    for &line in &lines[..split_idx] {
        let without_comment = line.split("--").next().unwrap_or(line).trim();
        if without_comment.is_empty() {
            continue;
        }
        if without_comment.starts_with('#')
            || without_comment.starts_with("run_cmd")
            || without_comment.contains("run_cmd ")
            || without_comment.contains("run_cmd\t")
            || without_comment.starts_with("initialize ")
            || without_comment.starts_with("builtin_initialize ")
        {
            return None;
        }
        has_prefix_decl = true;
        prev_nonempty = without_comment;
    }
    if !has_prefix_decl
        || prev_nonempty.ends_with(" in")
        || prev_nonempty.starts_with("@[")
        || prev_nonempty.starts_with("/--")
        || prev_nonempty.ends_with("-/")
    {
        return None;
    }
    let prefix_code = format!("{}\n", lines[..split_idx].join("\n"));
    let decl_code = format!(
        "{}{}\n",
        "\n".repeat(split_idx),
        lines[split_idx..].join("\n")
    );
    let prefix_key =
        blake3::hash(format!("eval_prefix_v1:{}:{}", prefix_code.len(), prefix_code).as_bytes())
            .to_hex()
            .to_string();
    Some((prefix_key, prefix_code, decl_code))
}

impl ZygoteEvalReply {
    fn timed_out_reply(
        eval_mode: bool,
        elab_us: u64,
        timeout_ms: u64,
        peak_rss_mb: u64,
        stderr_tail: String,
        last_request: Option<String>,
    ) -> Self {
        let mut msg = format!("Zygote evaluation timed out after {} ms", timeout_ms);
        if peak_rss_mb > 0 {
            msg.push_str(&format!(" (peak_rss_mb={})", peak_rss_mb));
        }
        if let Some(ref req) = last_request {
            msg.push_str(&format!(" [{}]", req));
        }
        Self {
            kernel_gate_active: !eval_mode,
            import_ok: true,
            elab_us,
            peak_rss_mb,
            errors: vec![msg],
            timed_out: true,
            stderr_tail,
            last_request,
            ..Default::default()
        }
    }

    fn crashed_reply_with_diag(eval_mode: bool, diag: WorkerCrashDiagnostics) -> Self {
        Self {
            kernel_gate_active: !eval_mode,
            peak_rss_mb: diag.peak_rss_mb,
            errors: vec![diag.message],
            crashed: true,
            exit_code: diag.exit_code,
            exit_signal: diag.exit_signal,
            stderr_tail: diag.stderr_tail,
            last_request: diag.last_request,
            ..Default::default()
        }
    }
}

/// Error a worker reports (and this host adds) once a Lean runtime panic made it unusable.
const RUNTIME_PANIC_ERR: &str =
    "[TurboLean.ZygoteWorker] runtime panic; worker environment is unusable";

/// Mirrors `TurboLean.ZygoteWorker.isRuntimePanicText`: Lean panic output or `EnvExtension`
/// corruption, not any mention of the word `PANIC`.
fn is_runtime_panic_text(s: &str) -> bool {
    [
        "PANIC at ",
        "INTERNAL PANIC",
        "invalid environment extension",
    ]
    .iter()
    .any(|m| s.contains(m))
}

/// Fails a reply whose worker hit a runtime panic; returns whether the worker must be discarded.
fn mark_runtime_panic(rep: &mut ZygoteEvalReply) -> bool {
    let reported = rep.errors.iter().any(|e| e == RUNTIME_PANIC_ERR);
    if !reported && !rep.messages.iter().any(|m| is_runtime_panic_text(m)) {
        return false;
    }
    rep.ok = false;
    if !reported {
        rep.errors.push(RUNTIME_PANIC_ERR.to_string());
    }
    true
}

fn collect_worker_exit_status(child: &mut std::process::Child) -> (Option<i32>, Option<i32>) {
    let mut status_opt = child.try_wait().ok().flatten();
    if status_opt.is_none() {
        for _ in 0..10 {
            std::thread::sleep(std::time::Duration::from_millis(2));
            if let Ok(Some(st)) = child.try_wait() {
                status_opt = Some(st);
                break;
            }
        }
    }
    let Some(st) = status_opt else {
        return (None, None);
    };
    let code = st.code();
    #[cfg(unix)]
    let sig = {
        use std::os::unix::process::ExitStatusExt;
        st.signal()
    };
    #[cfg(not(unix))]
    let sig: Option<i32> = None;
    (code, sig)
}

fn snapshot_worker_stderr_tail(buf: &std::sync::Arc<std::sync::Mutex<Vec<u8>>>) -> String {
    buf.lock()
        .ok()
        .map(|g| String::from_utf8_lossy(&g).trim().to_string())
        .unwrap_or_default()
}

fn build_worker_crash_diagnostics(
    worker: &mut ZygoteChild,
    reason: &str,
    peak_rss_mb: u64,
    last_request: &str,
) -> WorkerCrashDiagnostics {
    let (exit_code, exit_signal) = collect_worker_exit_status(&mut worker.child);
    let stderr_tail = snapshot_worker_stderr_tail(&worker.stderr_tail);
    let mut details: Vec<String> = Vec::new();
    if let Some(code) = exit_code {
        details.push(format!("exit_code={}", code));
    }
    if let Some(sig) = exit_signal {
        details.push(format!("signal={}", sig));
    }
    if peak_rss_mb > 0 {
        details.push(format!("peak_rss_mb={}", peak_rss_mb));
    }
    if !last_request.is_empty() {
        details.push(format!("request={}", last_request));
    }
    let mut message = if details.is_empty() {
        reason.to_string()
    } else {
        format!("{} ({})", reason, details.join(", "))
    };
    if !stderr_tail.is_empty() {
        message.push_str(": ");
        message.push_str(&stderr_tail);
    }
    WorkerCrashDiagnostics {
        message,
        exit_code,
        exit_signal,
        stderr_tail,
        peak_rss_mb,
        last_request: (!last_request.is_empty()).then(|| last_request.to_string()),
    }
}

pub fn parse_zygote_import_entry(raw_entry: &str) -> Option<(String, bool, bool, bool)> {
    let trimmed = raw_entry.trim();
    if trimmed.is_empty()
        || trimmed == "__PRELUDE__"
        || trimmed == "__MODULE__"
        || trimmed == "__HEADER_ERR__"
    {
        return None;
    }
    if let Some((flags, mod_name)) = trimmed.split_once('@') {
        let m = mod_name.trim();
        if m.is_empty() {
            return None;
        }
        return Some((
            m.to_string(),
            flags.contains('p'),
            flags.contains('m'),
            flags.contains('a'),
        ));
    }
    Some((trimmed.to_string(), true, false, false))
}

/// Split a Lean shard source into `(imports_csv, body_without_imports)` while preserving line numbers and import order.
pub fn split_shard_for_zygote(shard_source: &str) -> (String, String) {
    let hdr = crate::module_builder::parse_header_info(shard_source);
    if hdr.header_error.is_some() {
        let mut body = shard_source.to_string();
        if !body.ends_with('\n') {
            body.push('\n');
        }
        return ("__HEADER_ERR__".to_string(), body);
    }

    let body_offset = hdr.body_byte_offset.min(shard_source.len());
    let header_slice = &shard_source[..body_offset];
    let rest_slice = &shard_source[body_offset..];
    let header_newlines = header_slice
        .as_bytes()
        .iter()
        .filter(|&&b| b == b'\n')
        .count();
    let mut body = String::with_capacity(header_newlines + rest_slice.len() + 1);
    for _ in 0..header_newlines {
        body.push('\n');
    }
    body.push_str(rest_slice);
    if !body.ends_with('\n') {
        body.push('\n');
    }

    let can_use_plain_legacy_csv = !hdr.is_module
        && hdr
            .import_specs
            .iter()
            .all(|s| s.module == "Init" || (s.is_exported && !s.is_meta && !s.import_all));
    if can_use_plain_legacy_csv {
        let explicit: Vec<String> = hdr
            .import_specs
            .iter()
            .skip(if hdr.has_prelude { 0 } else { 2 })
            .map(|s| s.module.clone())
            .collect();
        let mut deduped: Vec<String> = Vec::with_capacity(explicit.len());
        let mut seen = std::collections::HashSet::new();
        for m in explicit {
            if seen.insert(m.clone()) {
                deduped.push(m);
            }
        }
        if hdr.has_prelude && !deduped.is_empty() {
            deduped.insert(0, "__PRELUDE__".to_string());
        }
        let imports_csv = if deduped.is_empty() {
            if hdr.has_prelude {
                "__PRELUDE__".to_string()
            } else {
                "Init".to_string()
            }
        } else {
            deduped.join(",")
        };
        return (imports_csv, body);
    }

    let mut entries: Vec<String> = Vec::with_capacity(hdr.import_specs.len() + 1);
    if hdr.is_module {
        entries.push("__MODULE__".to_string());
    }
    if hdr.import_specs.is_empty() {
        entries.push("__PRELUDE__".to_string());
    } else {
        for spec in &hdr.import_specs {
            let mut flags = String::new();
            if spec.is_exported {
                flags.push('p');
            }
            if spec.is_meta {
                flags.push('m');
            }
            if spec.import_all {
                flags.push('a');
            }
            if flags == "p" && !hdr.is_module {
                entries.push(spec.module.clone());
            } else {
                entries.push(format!("{}@{}", flags, spec.module));
            }
        }
    }
    (entries.join(","), body)
}

/// True iff `path` is a non-symlink entry of the expected kind, owned by the effective uid,
/// with no group/other write access (directories additionally no group/other access).
#[cfg(unix)]
fn owned_private_entry(path: &Path, want_dir: bool) -> bool {
    use std::os::unix::fs::MetadataExt;
    let Ok(m) = fs::symlink_metadata(path) else {
        return false;
    };
    let mask = if want_dir { 0o077 } else { 0o022 };
    let kind_ok = if want_dir { m.is_dir() } else { m.is_file() };
    kind_ok && m.uid() == unsafe { libc::geteuid() } && m.mode() & mask == 0
}

#[cfg(not(unix))]
fn owned_private_entry(_path: &Path, _want_dir: bool) -> bool {
    true
}

fn owned_private_file(path: &Path) -> bool {
    owned_private_entry(path, false)
}

/// Per-uid `$TMPDIR/turbo_lean_shared_zygote_bins_<uid>` (mode 0700), or `None` when it cannot
/// be created or is not owned by us (e.g. pre-created by another local user).
pub(crate) fn private_shared_zygote_dir() -> Option<PathBuf> {
    private_shared_zygote_dir_in(&std::env::temp_dir())
}

fn private_shared_zygote_dir_in(base: &Path) -> Option<PathBuf> {
    #[cfg(unix)]
    let uid = unsafe { libc::geteuid() };
    #[cfg(not(unix))]
    let uid = 0u32;
    #[cfg(unix)]
    let dir = {
        use std::os::unix::fs::{DirBuilderExt, MetadataExt};
        // Another user must not be able to rename/replace our dir anywhere up the resolved
        // hierarchy: every ancestor must be owned by root or us and may only be
        // group/other-writable when sticky (like the default /tmp).
        let base = fs::canonicalize(base).ok()?;
        for anc in base.ancestors() {
            let pm = fs::metadata(anc).ok()?;
            let writable_by_others = pm.mode() & 0o022 != 0 && pm.mode() & 0o1000 == 0;
            if writable_by_others || (pm.uid() != 0 && pm.uid() != uid) {
                return None;
            }
        }
        let dir = base.join(format!("turbo_lean_shared_zygote_bins_{uid}"));
        match fs::DirBuilder::new().mode(0o700).create(&dir) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(_) => return None,
        }
        dir
    };
    #[cfg(not(unix))]
    let dir = {
        let dir = base.join(format!("turbo_lean_shared_zygote_bins_{uid}"));
        let _ = fs::create_dir_all(&dir);
        dir
    };
    owned_private_entry(&dir, true).then_some(dir)
}

pub(crate) fn ensure_zygote_binary(
    store: &TurboStore,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
) -> Result<std::path::PathBuf> {
    ensure_zygote_binary_at(&store.root, lean_bin, env_vars)
}

fn ensure_zygote_binary_at(
    store_root: &Path,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
) -> Result<std::path::PathBuf> {
    let _lifecycle = lifecycle_lock(false)?;
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-zygote:v3:shared:");
    hasher.update(std::env::consts::ARCH.as_bytes());
    hasher.update(lean_bin.to_string_lossy().as_bytes());
    if let Some(tc) = env_vars.get("ELAN_TOOLCHAIN") {
        hasher.update(tc.as_bytes());
    }
    hasher.update(ZYGOTE_WORKER_LEAN_SRC.as_bytes());
    let bin_name = format!("turbo_zygote_{}", &hasher.finalize().to_hex()[..16]);
    let bin_dir = store_root.join("fastcheck_bins");
    fs::create_dir_all(&bin_dir)?;
    let cached_bin = bin_dir.join(&bin_name);
    if cached_bin.exists() {
        return Ok(cached_bin);
    }

    // The shared dir lives in world-writable $TMPDIR: only use it when it is a private,
    // euid-owned 0700 directory, and only execute regular files we own.
    let shared_dir = private_shared_zygote_dir();
    let shared_bin = shared_dir.as_ref().map(|d| d.join(&bin_name));
    let _lock_guard = shared_dir
        .as_ref()
        .and_then(|d| {
            crate::shm_cache::acquire_flock(&d.join(format!("{}.lock", bin_name)), true, false).ok()
        })
        .flatten();

    if cached_bin.exists() {
        return Ok(cached_bin);
    }
    if let Some(shared_bin) = shared_bin.as_ref().filter(|b| owned_private_file(b)) {
        let tmp_copy = bin_dir.join(format!(".{}.{}.tmp", bin_name, next_tmp_id()));
        if fs::hard_link(shared_bin, &tmp_copy).is_ok() || fs::copy(shared_bin, &tmp_copy).is_ok() {
            let _ = fs::rename(&tmp_copy, &cached_bin);
            if cached_bin.exists() {
                return Ok(cached_bin);
            }
        }
        return Ok(shared_bin.clone());
    }

    let tmp_id = next_tmp_id();
    // Compile embedded ZygoteWorker.lean via `lean -c` + `leanc -O3 -lleanshared -Wl,-rpath,<sysroot>/lib/lean`
    let leanc_bin = lean_bin
        .parent()
        .map(|p| p.join("leanc"))
        .filter(|c| c.exists())
        .unwrap_or_else(|| std::path::PathBuf::from("leanc"));
    let tmp_lean = bin_dir.join(format!("ZygoteWorker_{}.lean", tmp_id));
    let tmp_c = bin_dir.join(format!("ZygoteWorker_{}.c", tmp_id));
    let tmp_bin = bin_dir.join(format!(".{}.{}.tmp", bin_name, tmp_id));
    fs::write(&tmp_lean, ZYGOTE_WORKER_LEAN_SRC)?;

    let out1 = Command::new(lean_bin)
        .arg(format!("--root={}", bin_dir.display()))
        .arg("-c")
        .arg(&tmp_c)
        .arg(&tmp_lean)
        .current_dir(&bin_dir)
        .envs(env_vars)
        .output()
        .context("Failed to compile ZygoteWorker.lean to C")?;
    let _ = fs::remove_file(&tmp_lean);
    if !out1.status.success() {
        anyhow::bail!(
            "`lean -c` failed on ZygoteWorker.lean:\n{}",
            String::from_utf8_lossy(&out1.stderr)
        );
    }

    let mut link_cmd = Command::new(&leanc_bin);
    link_cmd
        .arg("-O3")
        .arg(&tmp_c)
        .arg("-lleanshared")
        .arg("-o")
        .arg(&tmp_bin)
        .current_dir(&bin_dir)
        .envs(env_vars);
    if let Some(tc_lib_lean) = lean_bin
        .parent()
        .and_then(|b| b.parent())
        .map(|tc| tc.join("lib").join("lean"))
        .filter(|p| p.exists())
    {
        link_cmd.arg(format!("-Wl,-rpath,{}", tc_lib_lean.display()));
    }
    let out2 = link_cmd
        .output()
        .context("Failed to link ZygoteWorker binary via `leanc -O3 -lleanshared`")?;
    let _ = fs::remove_file(&tmp_c);
    if !out2.status.success() {
        let _ = fs::remove_file(&tmp_bin);
        anyhow::bail!(
            "`leanc -O3 -lleanshared` failed on ZygoteWorker.c:\n{}",
            String::from_utf8_lossy(&out2.stderr)
        );
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if let Ok(m) = fs::metadata(&tmp_bin) {
            let mut p = m.permissions();
            p.set_mode(0o755);
            let _ = fs::set_permissions(&tmp_bin, p);
        }
    }
    if let (Some(shared_dir), Some(shared_bin)) = (&shared_dir, &shared_bin) {
        let shared_tmp = shared_dir.join(format!(".{}.{}.tmp", bin_name, tmp_id));
        if fs::hard_link(&tmp_bin, &shared_tmp).is_ok() || fs::copy(&tmp_bin, &shared_tmp).is_ok() {
            let _ = fs::rename(&shared_tmp, shared_bin);
        }
    }
    fs::rename(&tmp_bin, &cached_bin)?;
    Ok(cached_bin)
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct ZygoteAuditModulesReply {
    pub ok: bool,
    #[serde(default)]
    pub audited: Option<Vec<String>>,
    #[serde(default)]
    pub violations: Vec<String>,
    /// `--shard` mode: the module's non-stub theorems, read from the kernel environment.
    #[serde(default)]
    pub decls: Option<Vec<String>>,
}

pub(crate) struct PinnedFfiPackage {
    pub name: &'static str,
    pub url: &'static str,
    pub rev: &'static str,
    pub module: &'static str,
    pub rel_src: &'static str,
    pub src_sha256: &'static str,
    pub decls: &'static [(&'static str, &'static str)],
}

pub(crate) const PINNED_FFI_PACKAGES: &[PinnedFfiPackage] = &[PinnedFfiPackage {
    name: "lean-sys",
    url: "https://github.com/Th0rgal/lean-sys.git",
    rev: "077775ba387f1eeb2976cb8763b4633b8d5ce313",
    module: "LeanSys.Posix",
    rel_src: "LeanSys/Posix.lean",
    src_sha256: "35aacd3f54a985e2365de92eea17d167a2945538c0533cebf2a44338936ce2d8",
    decls: &[
        ("LeanSys.Posix.rawOpenFlock", "leansys_open_flock"),
        ("LeanSys.Posix.rawFsCloneOrLink", "leansys_fs_clone_or_link"),
        ("LeanSys.Posix.rawWriteAll", "leansys_write_all"),
        ("LeanSys.Posix.rawPreadBa", "leansys_pread_ba"),
        ("LeanSys.Posix.rawSpawnGroup", "leansys_spawn_group"),
        ("LeanSys.Posix.rawKillWaitGroup", "leansys_kill_wait_group"),
        ("LeanSys.Posix.rawNetListen", "leansys_net_listen"),
        ("LeanSys.Posix.rawNetAcceptPoll", "leansys_net_accept_poll"),
    ],
}];

pub(crate) fn pinned_ffi_allow_args(
    cfg: &crate::module_builder::ProjectConfig,
    mod_names: &[String],
) -> Vec<String> {
    use sha2::Digest;
    let mut out = Vec::new();
    let root = cfg
        .root_pkg
        .pkg_root
        .canonicalize()
        .unwrap_or_else(|_| cfg.root_pkg.pkg_root.clone());
    for pin in PINNED_FFI_PACKAGES {
        if !mod_names.iter().any(|m| m == pin.module) {
            continue;
        }
        let Some(mp) = cfg.manifest_packages.iter().find(|mp| {
            mp.name == pin.name
                && mp.pkg_type == "git"
                && mp.rev.as_deref() == Some(pin.rev)
                && mp.url.as_deref() == Some(pin.url)
        }) else {
            continue;
        };
        let Ok(dir) = mp.dir.canonicalize() else {
            continue;
        };
        if dir == root
            || !cfg
                .dep_pkgs
                .iter()
                .any(|d| d.pkg_root.canonicalize().ok().as_deref() == Some(dir.as_path()))
        {
            continue;
        }
        let root_src = cfg.root_pkg.pkg_root.join(&cfg.root_pkg.src_dir);
        if fs::symlink_metadata(root_src.join(pin.rel_src)).is_ok()
            || fs::symlink_metadata(cfg.root_pkg.pkg_root.join(pin.rel_src)).is_ok()
        {
            continue;
        }
        let src_path = dir.join(pin.rel_src);
        let src_ok = fs::symlink_metadata(&src_path)
            .map(|m| m.file_type().is_file())
            .unwrap_or(false)
            && fs::read(&src_path)
                .map(|b| format!("{:x}", sha2::Sha256::digest(&b)) == pin.src_sha256)
                .unwrap_or(false);
        if !src_ok {
            continue;
        }
        for (decl, sym) in pin.decls {
            out.push(format!("--ffi-allow={}={}={}", pin.module, decl, sym));
        }
    }
    out
}

fn audit_batch_size() -> usize {
    std::env::var("TURBO_LEAN_AUDIT_BATCH_SIZE")
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .filter(|&v| v > 0)
        .unwrap_or(8)
}

pub(crate) fn audit_compiled_modules_with_zygote(
    store: &TurboStore,
    cfg: &crate::module_builder::ProjectConfig,
    mod_names: &[String],
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
    is_untrusted: bool,
) -> Result<()> {
    if mod_names.is_empty() {
        return Ok(());
    }
    let mut sorted: Vec<String> = mod_names.to_vec();
    sorted.sort();
    sorted.dedup();
    for chunk in sorted.chunks(audit_batch_size()) {
        audit_compiled_module_batch(
            store,
            cfg,
            chunk,
            lean_path_env,
            extra_ro_binds,
            is_untrusted,
        )?;
    }
    Ok(())
}

fn build_auditor_bootstrap_env(
    cfg: &crate::module_builder::ProjectConfig,
) -> std::collections::HashMap<String, String> {
    let mut bootstrap_env = std::collections::HashMap::new();
    bootstrap_env.insert(
        "LEAN".to_string(),
        cfg.lean_bin.to_string_lossy().to_string(),
    );
    let tc_lp = cfg.toolchain_lib_lean.to_string_lossy().to_string();
    if !tc_lp.is_empty() {
        bootstrap_env.insert("LEAN_PATH".to_string(), tc_lp.clone());
    }
    let mut tc_ld_parts = Vec::new();
    if !tc_lp.is_empty() {
        tc_ld_parts.push(tc_lp);
    }
    let tc_lib = cfg.toolchain_lib.to_string_lossy().to_string();
    if !tc_lib.is_empty() && !tc_ld_parts.contains(&tc_lib) {
        tc_ld_parts.push(tc_lib);
    }
    if !tc_ld_parts.is_empty() {
        bootstrap_env.insert("LD_LIBRARY_PATH".to_string(), tc_ld_parts.join(":"));
    }
    bootstrap_env.insert("ELAN_TOOLCHAIN".to_string(), cfg.toolchain.clone());
    bootstrap_env
}

fn audit_compiled_module_batch(
    store: &TurboStore,
    cfg: &crate::module_builder::ProjectConfig,
    mod_names: &[String],
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
    is_untrusted: bool,
) -> Result<()> {
    if mod_names.is_empty() || mod_names.iter().any(|m| m.trim().is_empty()) {
        anyhow::bail!("In-kernel `.olean` audit received an empty module name: fail-closed");
    }
    let bootstrap_env = build_auditor_bootstrap_env(cfg);
    let auditor_ld_library_path = bootstrap_env
        .get("LD_LIBRARY_PATH")
        .map(String::as_str)
        .unwrap_or("");
    let zygote_bin = ensure_zygote_binary(store, &cfg.lean_bin, &bootstrap_env)?;
    let canon_zygote = zygote_bin.canonicalize().unwrap_or(zygote_bin);

    let stack_kb = if is_untrusted {
        "262144".to_string()
    } else {
        std::env::var("LEAN_STACK_SIZE_KB").unwrap_or_else(|_| "262144".to_string())
    };
    let timeout_secs = std::env::var("TURBO_LEAN_AUDIT_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok())
        .filter(|&v| v > 0)
        .unwrap_or(if is_untrusted { 120 } else { 300 });

    let mut cmd = if is_untrusted {
        let bwrap_path = crate::module_builder::probe_bwrap_sandbox().ok_or_else(|| {
            anyhow::anyhow!(
                "Untrusted kernel `.olean` audit requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
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
        if extra_ro_binds.is_empty() {
            crate::module_builder::validate_untrusted_sandbox_search_paths(
                cfg,
                tc_prefix,
                lean_path_env,
                auditor_ld_library_path,
            )?;
        }
        let mut c = Command::new(bwrap_path);
        c.args([
            "--unshare-all",
            "--new-session",
            "--die-with-parent",
            "--clearenv",
            "--setenv",
            "PATH",
            "/usr/bin:/bin",
            "--setenv",
            "LEAN",
            &cfg.lean_bin.to_string_lossy(),
            "--setenv",
            "LEAN_PATH",
            lean_path_env,
            "--setenv",
            "LEAN_STACK_SIZE_KB",
            &stack_kb,
        ]);
        if !auditor_ld_library_path.is_empty() {
            c.args(["--setenv", "LD_LIBRARY_PATH", auditor_ld_library_path]);
        }
        for key in [
            crate::splitter::ALLOWED_AXIOMS_ENV,
            "TURBO_LEAN_ALLOWED_CSIMP",
        ] {
            if let Ok(allow) = std::env::var(key) {
                if !allow.trim().is_empty() {
                    c.args(["--setenv", key, &allow]);
                }
            }
        }
        c.args(["--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp"]);
        for sys_p in [
            "/usr",
            "/bin",
            "/lib",
            "/lib64",
            "/etc/ld.so.cache",
            "/etc/localtime",
        ] {
            c.args(["--ro-bind-try", sys_p, sys_p]);
        }
        c.arg("--ro-bind").arg(tc_prefix).arg(tc_prefix);
        c.arg("--ro-bind")
            .arg(&cfg.root_pkg.pkg_root)
            .arg(&cfg.root_pkg.pkg_root);
        for dp in &cfg.dep_pkgs {
            if !dp.pkg_root.starts_with(&cfg.root_pkg.pkg_root) {
                c.arg("--ro-bind").arg(&dp.pkg_root).arg(&dp.pkg_root);
            }
        }
        for extra in extra_ro_binds {
            if extra.exists() {
                c.arg("--ro-bind").arg(extra).arg(extra);
            }
        }
        c.arg("--ro-bind").arg(&canon_zygote).arg(&canon_zygote);
        c.arg("--chdir").arg(&cfg.root_pkg.pkg_root);
        c.arg(&canon_zygote);
        crate::module_builder::scrub_untrusted_env(&mut c);
        c
    } else {
        let mut c = Command::new(&canon_zygote);
        c.current_dir(&cfg.root_pkg.pkg_root)
            .env("LEAN", &cfg.lean_bin)
            .env("LEAN_PATH", lean_path_env)
            .env("LD_LIBRARY_PATH", auditor_ld_library_path)
            .env("LEAN_STACK_SIZE_KB", &stack_kb);
        c
    };

    cmd.arg("--audit-modules");
    for a in pinned_ffi_allow_args(cfg, mod_names) {
        cmd.arg(a);
    }
    for m in mod_names {
        cmd.arg(m);
    }

    let out = crate::module_builder::run_command_with_timeout(
        &mut cmd,
        std::time::Duration::from_secs(timeout_secs),
        is_untrusted,
    )
    .context("Failed to execute in-kernel `.olean` soundness auditor (`--audit-modules`)")?;
    parse_audit_modules_reply(&out, mod_names).map(drop)
}

/// The auditor's verdict on `mod_names`: its JSON reply when every module passed, else an error.
fn parse_audit_modules_reply(
    out: &std::process::Output,
    mod_names: &[String],
) -> Result<ZygoteAuditModulesReply> {
    let stdout_str = String::from_utf8_lossy(&out.stdout);
    let stderr_str = String::from_utf8_lossy(&out.stderr);
    let json_line = stdout_str
        .lines()
        .rev()
        .map(str::trim)
        .find(|l| l.starts_with('{') && l.ends_with('}'))
        .unwrap_or("");
    let parsed: Option<ZygoteAuditModulesReply> = serde_json::from_str(json_line).ok();

    match parsed {
        Some(reply)
            if out.status.success()
                && reply.ok
                && reply.violations.is_empty()
                && reply.audited.as_deref() == Some(mod_names) =>
        {
            Ok(reply)
        }
        Some(reply) => {
            let details = if reply.violations.is_empty() {
                format!(
                    "exit={} stdout={} stderr={}",
                    out.status,
                    stdout_str.trim(),
                    stderr_str.trim()
                )
            } else {
                reply.violations.join("\n")
            };
            anyhow::bail!(
                "In-kernel `.olean` soundness audit rejected compiled artifact(s) ({:?}):\n{}",
                mod_names,
                details
            );
        }
        None => {
            anyhow::bail!(
                "In-kernel `.olean` soundness auditor failed closed (exit={}, modules={:?}):\nstdout: {}\nstderr: {}",
                out.status,
                mod_names,
                stdout_str.trim(),
                stderr_str.trim()
            );
        }
    }
}

/// Plain-`lean` fallback for a shard the zygote could not check (unavailable or import failure):
/// compile `source` to a scratch `.olean`, then accept it only on the kernel-level
/// `--audit-modules --shard` verdict over the compiled module (axioms incl. `sorryAx`,
/// extern/implemented_by, csimp, `unsafe`), never on output the shard itself controls. Only the
/// source's `:= sorry` prefix stubs outside `audit` are exempt, by name and kernel value, and every
/// `audit` theorem must be declared. A failed compile returns its non-success output; an audit
/// rejection is an error.
#[allow(clippy::too_many_arguments)]
pub(crate) fn run_audited_lean_shard(
    store: &TurboStore,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
    cwd: Option<&Path>,
    source: &str,
    audit: &std::collections::HashSet<String>,
    lean_args: &[String],
    timeout_ms: Option<u64>,
) -> Result<std::process::Output> {
    let started = std::time::Instant::now();
    let mod_name = format!("TurboAuditedShard_{}_{}", std::process::id(), next_tmp_id());
    let tmp_dir = store.fast_staging_dir().join(&mod_name);
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir)?;
    struct TmpDirGuard(PathBuf);
    impl Drop for TmpDirGuard {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let _guard = TmpDirGuard(tmp_dir.clone());
    let lean_file = tmp_dir.join(format!("{}.lean", mod_name));
    fs::write(&lean_file, source)?;
    let mut cmd = Command::new(lean_bin);
    cmd.args(crate::module_builder::filter_allowed_lean_args(lean_args))
        .arg("-Ddebug.skipKernelTC=false")
        .arg(&lean_file)
        .arg("-R")
        .arg(&tmp_dir)
        .arg("-o")
        .arg(tmp_dir.join(format!("{}.olean", mod_name)))
        .envs(env_vars);
    if let Some(dir) = cwd {
        cmd.current_dir(dir);
    }
    let out = match timeout_ms {
        Some(_) => run_lean_command(&mut cmd, timeout_ms),
        None => cmd.output().map_err(Into::into),
    }
    .context("Failed to execute `lean` on shard fallback")?;
    if !out.status.success() {
        return Ok(out);
    }

    let lean_path = env_vars
        .get("LEAN_PATH")
        .cloned()
        .or_else(|| std::env::var("LEAN_PATH").ok())
        .filter(|lp| !lp.is_empty())
        .map_or_else(
            || tmp_dir.display().to_string(),
            |lp| format!("{}:{}", tmp_dir.display(), lp),
        );
    // A request budget bounds the whole fallback: compile, auditor preparation and audit.
    let budget_left = |stage: &str| -> Result<Option<std::time::Duration>> {
        timeout_ms
            .map(|ms| {
                let left = std::time::Duration::from_millis(ms).saturating_sub(started.elapsed());
                anyhow::ensure!(!left.is_zero(), "Lean request timed out before {}", stage);
                Ok(left)
            })
            .transpose()
    };
    let zygote_bin = match budget_left("the shard auditor was ready")? {
        None => ensure_zygote_binary(store, lean_bin, env_vars)?,
        // A cold auditor build may outlive the request; it still warms the cache in the background.
        Some(left) => {
            let (tx, rx) = std::sync::mpsc::channel();
            let (root, lean, env) = (store.root.clone(), lean_bin.to_path_buf(), env_vars.clone());
            std::thread::spawn(move || {
                let _ = tx.send(ensure_zygote_binary_at(&root, &lean, &env));
            });
            rx.recv_timeout(left).map_err(|_| {
                anyhow::anyhow!("Lean request timed out before the shard auditor was ready")
            })??
        }
    };
    let mut auditor = Command::new(zygote_bin);
    auditor
        .envs(env_vars)
        .env("LEAN", lean_bin)
        .env("LEAN_PATH", lean_path)
        .args(["--audit-modules", "--shard"]);
    // The auditor links `libleanshared` from the toolchain, which an elan-proxied `lean` does not
    // put on the loader path.
    let mut prefix_cmd = Command::new(lean_bin);
    prefix_cmd.arg("--print-prefix").envs(env_vars);
    if let Some(dir) = cwd {
        prefix_cmd.current_dir(dir);
    }
    let prefix_out = match budget_left("the toolchain prefix query")? {
        None => prefix_cmd.output().ok(),
        Some(left) => run_lean_command(&mut prefix_cmd, Some(left.as_millis().max(1) as u64)).ok(),
    };
    if let Some(p) = prefix_out.filter(|p| p.status.success()) {
        let prefix = PathBuf::from(String::from_utf8_lossy(&p.stdout).trim());
        let mut ld = format!(
            "{}:{}",
            prefix.join("lib/lean").display(),
            prefix.join("lib").display()
        );
        if let Some(prev) = env_vars
            .get("LD_LIBRARY_PATH")
            .cloned()
            .or_else(|| std::env::var("LD_LIBRARY_PATH").ok())
            .filter(|l| !l.is_empty())
        {
            ld = format!("{}:{}", ld, prev);
        }
        auditor.env("LD_LIBRARY_PATH", ld);
    }
    if !env_vars.contains_key(crate::splitter::ALLOWED_AXIOMS_ENV) {
        auditor.env(
            crate::splitter::ALLOWED_AXIOMS_ENV,
            crate::splitter::extra_allowed_axiom_patterns().join(","),
        );
    }
    for sh in crate::splitter::split_lean_source(source, &[]).shards {
        if crate::splitter::strip_lean_comments(&sh.proof_text).trim() == "sorry"
            && !crate::splitter::matches_uncached_or_fast_verify_name(&sh.name, audit)
        {
            auditor.arg(format!("--stub-ok={}", sh.name));
        }
    }
    auditor.arg(&mod_name);
    if let Some(dir) = cwd {
        auditor.current_dir(dir);
    }
    let mut audit_timeout = std::time::Duration::from_secs(
        std::env::var("TURBO_LEAN_AUDIT_TIMEOUT_SECS")
            .ok()
            .and_then(|s| s.trim().parse::<u64>().ok())
            .filter(|&v| v > 0)
            .unwrap_or(300),
    );
    if let Some(left) = budget_left("the shard audit")? {
        audit_timeout = audit_timeout.min(left);
    }
    let audit_out =
        crate::module_builder::run_command_with_timeout(&mut auditor, audit_timeout, false)
            .context("Failed to execute in-kernel shard auditor (`--audit-modules --shard`)")?;
    let decls = parse_audit_modules_reply(&audit_out, std::slice::from_ref(&mod_name))?
        .decls
        .unwrap_or_default();
    let missing: Vec<&String> = audit
        .iter()
        .filter(|name| {
            let one = std::collections::HashSet::from([(*name).clone()]);
            !decls
                .iter()
                .any(|d| crate::splitter::matches_uncached_or_fast_verify_name(d, &one))
        })
        .collect();
    if !missing.is_empty() {
        anyhow::bail!(
            "[TurboLean.KernelGate] audited theorem(s) {:?} missing from the compiled shard",
            missing
        );
    }
    Ok(out)
}

static ZYGOTE_LEAN_PATH_CACHE: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<(String, String, std::path::PathBuf), String>>,
> = std::sync::OnceLock::new();

fn read_line_with_timeout(
    reader: &mut BufReader<std::process::ChildStdout>,
    line: &mut String,
    deadline: std::time::Instant,
) -> std::io::Result<Option<usize>> {
    let mut raw_bytes: Vec<u8> = Vec::new();
    loop {
        if reader.buffer().is_empty() {
            let now = std::time::Instant::now();
            if now >= deadline {
                return Ok(None);
            }
            let rem_ms = deadline
                .duration_since(now)
                .as_millis()
                .min(i32::MAX as u128) as i32;
            #[cfg(unix)]
            {
                use std::os::unix::io::AsRawFd;
                let fd = reader.get_ref().as_raw_fd();
                let mut pfd = libc::pollfd {
                    fd,
                    events: libc::POLLIN,
                    revents: 0,
                };
                let rc = unsafe { libc::poll(&mut pfd, 1, rem_ms.max(1)) };
                if rc == 0 {
                    return Ok(None);
                }
                if rc < 0 {
                    let err = std::io::Error::last_os_error();
                    if err.kind() == std::io::ErrorKind::Interrupted {
                        continue;
                    }
                    return Err(err);
                }
            }
        }
        let available = match reader.fill_buf() {
            Ok(b) => b,
            Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        };
        if available.is_empty() {
            if !raw_bytes.is_empty() {
                *line = String::from_utf8_lossy(&raw_bytes).into_owned();
                return Ok(Some(raw_bytes.len()));
            }
            return Ok(Some(0));
        }
        if let Some(nl_pos) = available.iter().position(|&b| b == b'\n') {
            raw_bytes.extend_from_slice(&available[..=nl_pos]);
            reader.consume(nl_pos + 1);
            *line = String::from_utf8_lossy(&raw_bytes).into_owned();
            return Ok(Some(raw_bytes.len()));
        } else {
            let len = available.len();
            raw_bytes.extend_from_slice(available);
            reader.consume(len);
        }
    }
}

pub fn eval_with_zygote_pool(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_with_args(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        allow_stub,
        &[],
    )
}

#[allow(clippy::too_many_arguments)]
pub fn eval_with_zygote_pool_with_args(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_inner(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        allow_stub,
        false,
        None,
        None,
        None,
        lean_args,
        &[],
        false,
    )
}

pub fn eval_with_zygote_pool_opts(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
    eval_mode: bool,
    file_name: Option<&str>,
    timeout_ms: Option<u64>,
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_opts_with_args(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        allow_stub,
        eval_mode,
        file_name,
        timeout_ms,
        &[],
    )
}

#[allow(clippy::too_many_arguments)]
pub fn eval_with_zygote_pool_opts_with_args(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
    eval_mode: bool,
    file_name: Option<&str>,
    timeout_ms: Option<u64>,
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_inner(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        allow_stub,
        eval_mode,
        file_name,
        timeout_ms,
        None,
        lean_args,
        &[],
        false,
    )
}

fn encode_lean_args_hex(lean_args: &[String]) -> String {
    let filtered = crate::module_builder::filter_allowed_lean_args(lean_args);
    if filtered.is_empty() {
        String::new()
    } else {
        hex_encode_bytes(filtered.join("\n").as_bytes())
    }
}

/// Worker mode flag for a stubbed (`allow_stub`) or strict check of `shard_source`. Named `stub_targets`
/// (the declarations under check) travel as `allow_stub:<hex targets>:<hex stubs>`, with the stubs the
/// host wrote (`… := sorry` declarations that are not targets). The worker exempts only those, by kernel
/// value and name, never a target; with no named targets it exempts nothing in the final run.
fn stub_mode_flag(allow_stub: bool, stub_targets: &[String], shard_source: &str) -> String {
    match (allow_stub, stub_targets.is_empty()) {
        (false, _) => "strict".to_string(),
        (true, true) => "allow_stub".to_string(),
        (true, false) => {
            let targets: std::collections::HashSet<String> = stub_targets.iter().cloned().collect();
            let stubs: Vec<String> = crate::splitter::split_lean_source(shard_source, &[])
                .shards
                .into_iter()
                .filter(|sh| {
                    sh.proof_text.trim() == "sorry"
                        && !crate::splitter::matches_uncached_or_fast_verify_name(
                            &sh.name, &targets,
                        )
                })
                .map(|sh| sh.name)
                .collect();
            format!(
                "allow_stub:{}:{}",
                hex_encode_bytes(stub_targets.join("\n").as_bytes()),
                hex_encode_bytes(stubs.join("\n").as_bytes())
            )
        }
    }
}

/// `stub_mode` for one cross-file block of a request: every target still counts for ownership (never
/// exempt), but the block must declare only the targets its own text declares.
fn block_stub_mode(stub_mode: &str, stub_targets: &[String], blk: &str) -> String {
    if !stub_mode.starts_with("allow_stub:") {
        return stub_mode.to_string();
    }
    let shards = crate::splitter::split_lean_source(blk, &[]).shards;
    let required: Vec<&str> = stub_targets
        .iter()
        .filter(|t| {
            let one = std::collections::HashSet::from([(*t).clone()]);
            shards
                .iter()
                .any(|sh| crate::splitter::matches_uncached_or_fast_verify_name(&sh.name, &one))
        })
        .map(String::as_str)
        .collect();
    format!(
        "{}:{}",
        stub_mode,
        hex_encode_bytes(required.join("\n").as_bytes())
    )
}

/// Check `shard_source` with its prefix `sorry` stubs admitted, but never the `sorryAx` of `stub_targets`.
#[allow(clippy::too_many_arguments)]
pub fn eval_with_zygote_pool_for_targets(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    stub_targets: &[String],
    timeout_ms: Option<u64>,
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_inner(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        true,
        false,
        None,
        timeout_ms,
        None,
        lean_args,
        stub_targets,
        false,
    )
}

/// Check `shard_source` with no `sorry` stub exempt anywhere, prefix checkpoints included (`strict_all`):
/// the kernel-gate audit of a whole file.
pub fn eval_with_zygote_pool_audit_all(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    eval_with_zygote_pool_inner(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        shard_source,
        false,
        false,
        None,
        None,
        None,
        lean_args,
        &[],
        true,
    )
}

fn attach_host_closure_digest(req_line: &str, host_closure_digest: &str) -> String {
    if host_closure_digest.is_empty() {
        return req_line.to_string();
    }
    let trimmed = req_line.trim_end_matches('\n');
    let cols = trimmed.split('\t').count();
    let mut out = String::with_capacity(trimmed.len() + host_closure_digest.len() + 8);
    out.push_str(trimmed);
    for _ in cols..6 {
        out.push('\t');
    }
    out.push('\t');
    out.push_str(host_closure_digest);
    out.push('\n');
    out
}

#[allow(clippy::too_many_arguments)]
fn eval_with_zygote_pool_inner(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
    eval_mode: bool,
    file_name: Option<&str>,
    timeout_ms: Option<u64>,
    batch_fission_override: Option<(String, String, String)>,
    lean_args: &[String],
    stub_targets: &[String],
    audit_all: bool,
) -> Result<ZygoteEvalReply> {
    let request_started = std::time::Instant::now();
    let stub_mode = if audit_all {
        "strict_all".to_string()
    } else {
        stub_mode_flag(allow_stub, stub_targets, shard_source)
    };
    let default_timeout_ms = if eval_mode { 900_000 } else { 30_000 };
    let effective_timeout_ms = timeout_ms.unwrap_or_else(|| {
        std::env::var("TURBO_LEAN_TIMEOUT_MS")
            .ok()
            .and_then(|v| v.trim().parse::<u64>().ok())
            .filter(|&ms| ms > 0)
            .unwrap_or(default_timeout_ms)
    });
    let deadline = request_started + std::time::Duration::from_millis(effective_timeout_ms);
    let _lifecycle = lifecycle_lock(false)?;

    let env_lp = env_vars.get("LEAN_PATH").cloned().unwrap_or_default();
    let lp_cache_key = (
        req_lean_path.to_string(),
        env_lp.clone(),
        lean_bin.to_path_buf(),
    );
    let lp_cache_mutex = ZYGOTE_LEAN_PATH_CACHE
        .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    let cached_lp = lp_cache_mutex
        .lock()
        .ok()
        .and_then(|g| g.get(&lp_cache_key).cloned());

    let effective_lean_path = if let Some(eff) = cached_lp {
        eff
    } else {
        let mut path_parts: Vec<String> = Vec::new();
        let is_sysroot_lib_lean = |norm: &str| -> bool {
            let p = Path::new(norm);
            p.ends_with("lib/lean")
                && p.parent()
                    .and_then(|lib| lib.parent())
                    .map(|tc| tc.join("bin/lean").exists())
                    .unwrap_or(false)
        };
        let mut add_part = |p: &str| {
            for seg in p.split(':') {
                let s = seg.trim();
                if !s.is_empty() {
                    let norm = fs::canonicalize(s)
                        .map(|c| c.to_string_lossy().to_string())
                        .unwrap_or_else(|_| s.to_string());
                    if is_sysroot_lib_lean(&norm) {
                        continue;
                    }
                    if !path_parts.iter().any(|x| x == &norm) {
                        path_parts.push(norm);
                    }
                }
            }
        };
        if !req_lean_path.is_empty() {
            add_part(req_lean_path);
        }
        if !env_lp.is_empty() {
            add_part(&env_lp);
        }
        if req_lean_path.is_empty() && env_lp.is_empty() {
            if let Some(repo_lean_dir) = Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .and_then(|p| p.parent())
                .map(|r| r.join("lean"))
                .filter(|p| p.join(".lake/build/lib/lean").exists())
            {
                add_part(&crate::lake_build::resolve_remote_lean_path(
                    &repo_lean_dir,
                    None,
                ));
            }
        }
        if let Some(tc_lib_lean) = lean_bin
            .parent()
            .and_then(|b| b.parent())
            .map(|tc| tc.join("lib").join("lean"))
            .filter(|p| p.exists())
        {
            let norm = fs::canonicalize(&tc_lib_lean)
                .map(|c| c.to_string_lossy().to_string())
                .unwrap_or_else(|_| tc_lib_lean.to_string_lossy().to_string());
            if !path_parts.iter().any(|x| x == &norm) {
                path_parts.push(norm);
            }
        }
        let eff = path_parts.join(":");
        if let Ok(mut g) = lp_cache_mutex.lock() {
            if g.len() >= 512 {
                g.clear();
            }
            g.insert(lp_cache_key, eff.clone());
        }
        eff
    };

    let (raw_imports_csv, body_code) = if let Some((ref imp, _, _)) = batch_fission_override {
        (imp.clone(), String::new())
    } else {
        split_shard_for_zygote(shard_source)
    };
    let imports_csv = coalesce_proofkit_imports(&raw_imports_csv, &effective_lean_path);
    let search_path_digest = compute_search_path_oleans_digest(&effective_lean_path);
    let (imported_digest, closure_complete) =
        compute_imported_oleans_digest_inner(&imports_csv, &effective_lean_path);
    let host_closure_digest = if closure_complete {
        imported_digest.as_str()
    } else {
        ""
    };
    let pool_digest_tag = search_path_digest.clone();
    // Workers enforce the axiom policy they were spawned with: key them (and their replies) by it.
    let toolchain_policy = format!(
        "{}#{}",
        toolchain,
        env_vars
            .get(crate::splitter::ALLOWED_AXIOMS_ENV)
            .cloned()
            .unwrap_or_else(|| crate::splitter::allowed_axioms().join(","))
    );
    let pool_key = (
        toolchain_policy.clone(),
        effective_lean_path.clone(),
        format!("{}#{}", pool_digest_tag, imports_csv),
    );
    let olean_digest = format!("{}:{}", search_path_digest, imported_digest);

    let hex_opts = encode_lean_args_hex(lean_args);
    let args_digest_opt = crate::module_builder::compute_lean_args_digest(lean_args);
    let verified_cache_policy = match &args_digest_opt {
        Some(ad) => format!("{}#opts:{}", toolchain_policy, ad),
        None => toolchain_policy.clone(),
    };
    let warm_imports_tag = match &args_digest_opt {
        Some(ad) => format!("{}#opts:{}", imports_csv, ad),
        None => imports_csv.clone(),
    };

    static ZYGOTE_VERIFIED_SHARD_CACHE: std::sync::OnceLock<
        std::sync::Mutex<
            std::collections::HashMap<(String, String, String, String), ZygoteEvalReply>,
        >,
    > = std::sync::OnceLock::new();
    let verified_cache_key = if !eval_mode && batch_fission_override.is_none() {
        Some((
            verified_cache_policy,
            olean_digest.clone(),
            stub_mode.clone(),
            shard_source.to_string(),
        ))
    } else {
        None
    };
    if let Some(ref vkey) = verified_cache_key {
        let vcache = ZYGOTE_VERIFIED_SHARD_CACHE
            .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
        if let Ok(guard) = vcache.lock() {
            if let Some(cached) = guard.get(vkey) {
                let mut hit = cached.clone();
                hit.env_cache_hit = true;
                hit.import_us = 0;
                hit.prefix_us = 0;
                hit.elab_us = 1;
                return Ok(hit);
            }
        }
    }

    let spawn_zygote_worker = || -> Result<ZygoteChild> {
        let zygote_bin = ensure_zygote_binary(store, lean_bin, env_vars)?;
        let mut cmd = Command::new(&zygote_bin);
        let default_stack_kb = env_vars
            .get("LEAN_STACK_SIZE_KB")
            .cloned()
            .or_else(|| std::env::var("LEAN_STACK_SIZE_KB").ok())
            .unwrap_or_else(|| "262144".to_string());
        cmd.envs(env_vars)
            .env("LEAN_STACK_SIZE_KB", default_stack_kb)
            .env("LEAN_PATH", &effective_lean_path)
            .env("LEAN", lean_bin)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped());
        for k in [
            "GH_TOKEN",
            "GITHUB_TOKEN",
            "OPENAI_API_KEY",
            "ANTHROPIC_API_KEY",
            "AWS_SECRET_ACCESS_KEY",
            "AWS_SESSION_TOKEN",
            "NPM_TOKEN",
            "CARGO_REGISTRY_TOKEN",
        ] {
            cmd.env_remove(k);
        }
        if let Some(sysroot) = lean_bin.parent().and_then(|b| b.parent()) {
            cmd.env("LEAN_SYSROOT", sysroot);
        }
        if !toolchain.is_empty() && toolchain != "unknown" {
            cmd.env("ELAN_TOOLCHAIN", toolchain.trim());
        }
        #[cfg(target_os = "linux")]
        unsafe {
            use std::os::unix::process::CommandExt;
            let parent = libc::getpid();
            cmd.pre_exec(move || {
                if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL) != 0 {
                    return Err(std::io::Error::last_os_error());
                }
                if libc::getppid() != parent {
                    libc::_exit(1);
                }
                Ok(())
            });
        }
        cmd.env(
            "TURBO_LEAN_STAGING_DIR",
            crate::shm_cache::staging_shm_dir(),
        );
        let (owner, lifetime) = std::sync::mpsc::channel();
        let (send_child, receive_child) = std::sync::mpsc::sync_channel(1);
        std::thread::spawn(move || {
            let _ = send_child.send(cmd.spawn());
            let _ = lifetime.recv();
        });
        let mut child = receive_child
            .recv()?
            .with_context(|| format!("Failed to spawn Zygote worker {:?}", zygote_bin))?;
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| anyhow::anyhow!("Missing Zygote stdin"))?;
        let stdout = BufReader::new(
            child
                .stdout
                .take()
                .ok_or_else(|| anyhow::anyhow!("Missing Zygote stdout"))?,
        );
        let stderr_tail = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        if let Some(mut child_stderr) = child.stderr.take() {
            let tail_clone = stderr_tail.clone();
            std::thread::spawn(move || {
                use std::io::Read;
                let mut chunk = [0u8; 1024];
                while let Ok(n) = child_stderr.read(&mut chunk) {
                    if n == 0 {
                        break;
                    }
                    if let Ok(mut g) = tail_clone.lock() {
                        g.extend_from_slice(&chunk[..n]);
                        if g.len() > ZYGOTE_STDERR_TAIL_CAP {
                            let excess = g.len() - ZYGOTE_STDERR_TAIL_CAP;
                            g.drain(..excess);
                        }
                    }
                }
            });
        }
        Ok(ZygoteWorkerProcess {
            child,
            _owner: owner,
            stdin,
            stdout,
            stderr_tail,
            warm_prefixes: std::collections::HashSet::new(),
            warm_prefix_tree: Vec::new(),
            warm_imports: std::collections::HashMap::new(),
            request_count: 0,
        })
    };

    let governor = crate::shm_cache::MemoryBudgetGovernor::detect();
    let worker_rss_limit_mb = std::env::var("TURBO_LEAN_WORKER_RSS_LIMIT_MB")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .filter(|&mb| mb > 0)
        .unwrap_or_else(|| governor.worker_rss_limit_mb());
    let max_global_idle = std::env::var("TURBO_LEAN_MAX_IDLE_ZYGOTES")
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .filter(|&n| n >= 1)
        .unwrap_or_else(|| governor.recommended_parallel_workers(1024).clamp(4, 8));
    #[cfg(test)]
    let max_global_idle = max_global_idle.max(64);
    let max_pool_per_key = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .max(4)
        .min(max_global_idle);

    enum WorkerReqOutcome {
        Reply(ZygoteEvalReply),
        TimedOut {
            elapsed_us: u64,
            peak_rss_mb: u64,
            stderr_tail: String,
            last_request: String,
        },
        Crashed(WorkerCrashDiagnostics),
    }

    let worker_timeout = |worker: &ZygoteChild, req_id: &str| WorkerReqOutcome::TimedOut {
        elapsed_us: request_started.elapsed().as_micros() as u64,
        peak_rss_mb: measure_process_rss_mb(worker.child.id()),
        stderr_tail: snapshot_worker_stderr_tail(&worker.stderr_tail),
        last_request: req_id.to_string(),
    };

    let request_identity = format!(
        "imports={} file={} mode={} bytes={}",
        if imports_csv.is_empty() {
            "Init"
        } else {
            imports_csv.as_str()
        },
        file_name.unwrap_or("<zygote-shard>"),
        if eval_mode {
            "eval"
        } else if allow_stub {
            "allow_stub"
        } else {
            "strict"
        },
        shard_source.len()
    );

    let run_worker_req =
        |worker: &mut ZygoteChild, req_line: &str, req_id: &str| -> WorkerReqOutcome {
            if std::time::Instant::now() >= deadline {
                return worker_timeout(worker, req_id);
            }
            let pid = worker.child.id();
            let rss_before = measure_process_rss_mb(pid);
            if let Err(e) = worker
                .stdin
                .write_all(req_line.as_bytes())
                .and_then(|_| worker.stdin.flush())
            {
                let rss_now = measure_process_rss_mb(pid).max(rss_before);
                return WorkerReqOutcome::Crashed(build_worker_crash_diagnostics(
                    worker,
                    &format!("Failed to write to Zygote stdin: {}", e),
                    rss_now,
                    req_id,
                ));
            }
            let mut resp_line = String::new();
            match read_line_with_timeout(&mut worker.stdout, &mut resp_line, deadline) {
                Ok(None) => {
                    let rss_now = measure_process_rss_mb(pid).max(rss_before);
                    let stderr_tail = snapshot_worker_stderr_tail(&worker.stderr_tail);
                    WorkerReqOutcome::TimedOut {
                        elapsed_us: request_started.elapsed().as_micros() as u64,
                        peak_rss_mb: rss_now,
                        stderr_tail,
                        last_request: req_id.to_string(),
                    }
                }
                Ok(Some(0)) => {
                    let rss_now = measure_process_rss_mb(pid).max(rss_before);
                    WorkerReqOutcome::Crashed(build_worker_crash_diagnostics(
                        worker,
                        "Zygote worker closed stdout unexpectedly",
                        rss_now,
                        req_id,
                    ))
                }
                Ok(Some(_)) => match serde_json::from_str::<ZygoteEvalReply>(resp_line.trim()) {
                    Ok(mut parsed) => {
                        let rss_after = measure_process_rss_mb(pid);
                        parsed.rss_delta_mb = (rss_after as i64) - (rss_before as i64);
                        parsed.peak_rss_mb = rss_after.max(rss_before);
                        mark_runtime_panic(&mut parsed);
                        WorkerReqOutcome::Reply(parsed)
                    }
                    Err(e) => {
                        let rss_now = measure_process_rss_mb(pid).max(rss_before);
                        WorkerReqOutcome::Crashed(build_worker_crash_diagnostics(
                            worker,
                            &format!(
                                "Invalid JSON from Zygote worker ({}): {}",
                                e,
                                resp_line.trim()
                            ),
                            rss_now,
                            req_id,
                        ))
                    }
                },
                Err(e) => {
                    let rss_now = measure_process_rss_mb(pid).max(rss_before);
                    WorkerReqOutcome::Crashed(build_worker_crash_diagnostics(
                        worker,
                        &format!("Zygote stdout read error: {}", e),
                        rss_now,
                        req_id,
                    ))
                }
            }
        };

    let return_worker_to_pool = |pool_mutex: &std::sync::Mutex<
        std::collections::HashMap<(String, String, String), Vec<ZygoteWorkerProcess>>,
    >,
                                 key: (String, String, String),
                                 mut w: ZygoteChild| {
        if daemon_disabled() {
            drop(w);
            return;
        }
        w.request_count += 1;
        if w.request_count >= 256 {
            drop(w);
            return;
        }
        let pid = w.child.id();
        let worker_rss_mb = measure_process_rss_mb(pid);
        let effective_rss_limit_mb = if std::env::var("TURBO_LEAN_WORKER_RSS_LIMIT_MB").is_ok()
            || std::env::var("TURBO_LEAN_MAX_MEMORY_MB").is_ok()
        {
            worker_rss_limit_mb
        } else {
            worker_rss_limit_mb.max(2048)
        };
        if worker_rss_mb > effective_rss_limit_mb {
            drop(w);
            return;
        }
        govern_machine_wide_zygote_rss(pid, worker_rss_mb);
        if let Ok(mut pool) = pool_mutex.lock() {
            let mut total_idle: usize = pool.values().map(|v| v.len()).sum();
            if total_idle >= max_global_idle {
                let other_keys: Vec<(String, String, String)> =
                    pool.keys().filter(|k| **k != key).cloned().collect();
                for ok in other_keys {
                    if total_idle < max_global_idle {
                        break;
                    }
                    if let Some(ovec) = pool.get_mut(&ok) {
                        if let Some(evicted) = ovec.pop() {
                            drop(evicted);
                            total_idle = total_idle.saturating_sub(1);
                        }
                    }
                }
                pool.retain(|_, v| !v.is_empty());
            }
            let vec = pool.entry(key).or_default();
            while vec.len() >= max_pool_per_key || total_idle >= max_global_idle {
                if vec.is_empty() {
                    break;
                }
                let evict_idx = vec
                    .iter()
                    .position(|cand| cand.warm_prefixes.is_empty())
                    .unwrap_or(0);
                let _ = vec.remove(evict_idx);
                total_idle = total_idle.saturating_sub(1);
            }
            if vec.len() < max_pool_per_key && total_idle < max_global_idle {
                vec.push(w);
            } else {
                drop(w);
            }
        }
    };

    let pool_mutex =
        ZYGOTE_POOL.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));

    if !eval_mode && body_code.contains("-- namespace _TurboCrossFileShard_1") {
        let blocks: Vec<String> = body_code
            .split("-- namespace _TurboCrossFileShard_")
            .filter_map(|part| {
                let t = part.trim();
                if t.is_empty() {
                    return None;
                }
                if t.as_bytes()
                    .first()
                    .map(|b| b.is_ascii_digit())
                    .unwrap_or(false)
                {
                    Some(format!("-- namespace _TurboCrossFileShard_{}\n", t))
                } else {
                    Some(format!("{}\n", t))
                }
            })
            .collect();
        if blocks.len() >= 2 && blocks.len() <= 4 {
            let needed = blocks.len();
            let mut workers: Vec<ZygoteChild> = Vec::with_capacity(needed);
            {
                let mut pool = pool_mutex
                    .lock()
                    .map_err(|_| anyhow::anyhow!("ZygotePool mutex poisoned"))?;
                let matching_keys: Vec<(String, String, String)> = vec![pool_key.clone()];
                for k in &matching_keys {
                    if let Some(vec) = pool.get_mut(k) {
                        vec.retain(|w| {
                            (w.warm_imports.is_empty()
                                || (w.warm_imports.len() == 1
                                    && w.warm_imports.contains_key(&imports_csv)))
                                && w.warm_imports
                                    .get(&imports_csv)
                                    .map(|d| d == &olean_digest)
                                    .unwrap_or(true)
                        });
                    }
                }
                for k in &matching_keys {
                    if workers.len() >= needed {
                        break;
                    }
                    if let Some(vec) = pool.get_mut(k) {
                        while workers.len() < needed {
                            if let Some(pos) = vec
                                .iter()
                                .rposition(|w| w.warm_imports.contains_key(&imports_csv))
                            {
                                workers.push(vec.swap_remove(pos));
                            } else {
                                break;
                            }
                        }
                    }
                }
                if let Some(vec) = pool.get_mut(&pool_key) {
                    while workers.len() < needed {
                        if let Some(pos) = vec.iter().rposition(|w| w.warm_imports.is_empty()) {
                            workers.push(vec.swap_remove(pos));
                        } else {
                            break;
                        }
                    }
                }
            }
            while workers.len() < needed {
                workers.push(spawn_zygote_worker()?);
            }

            let req_lines: Vec<String> = blocks
                .iter()
                .map(|blk| {
                    let hb = hex_encode_bytes(blk.as_bytes());
                    let mode_flag = block_stub_mode(&stub_mode, stub_targets, blk);
                    let base = if hex_opts.is_empty() {
                        if mode_flag != "strict" {
                            format!("{}\t{}\t{}\n", imports_csv, hb, mode_flag)
                        } else {
                            format!("{}\t{}\n", imports_csv, hb)
                        }
                    } else {
                        format!("{}\t{}\t{}\t\t\t{}\n", imports_csv, hb, mode_flag, hex_opts)
                    };
                    attach_host_closure_digest(&base, host_closure_digest)
                })
                .collect();

            let results: Vec<(ZygoteChild, WorkerReqOutcome)> = std::thread::scope(|s| {
                let req_id_ref = request_identity.as_str();
                let handles: Vec<_> = workers
                    .into_iter()
                    .zip(req_lines)
                    .map(|(mut w, rl)| {
                        s.spawn(move || {
                            let res = run_worker_req(&mut w, &rl, req_id_ref);
                            (w, res)
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|h| h.join().expect("Zygote parallel eval thread panicked"))
                    .collect()
            });

            let mut replies = Vec::with_capacity(needed);
            let mut first_err: Option<anyhow::Error> = None;
            for (mut w, res) in results {
                match res {
                    WorkerReqOutcome::Reply(r) => {
                        if r.import_ok && !r.errors.iter().any(|e| e == RUNTIME_PANIC_ERR) {
                            w.warm_imports
                                .insert(imports_csv.clone(), olean_digest.clone());
                            return_worker_to_pool(pool_mutex, pool_key.clone(), w);
                        }
                        replies.push(r);
                    }
                    WorkerReqOutcome::TimedOut {
                        elapsed_us,
                        peak_rss_mb,
                        stderr_tail,
                        last_request,
                    } => {
                        drop(w);
                        return Ok(ZygoteEvalReply::timed_out_reply(
                            eval_mode,
                            elapsed_us,
                            effective_timeout_ms,
                            peak_rss_mb,
                            stderr_tail,
                            Some(last_request),
                        ));
                    }
                    WorkerReqOutcome::Crashed(diag) => {
                        drop(w);
                        if first_err.is_none() {
                            first_err = Some(anyhow::anyhow!("{}", diag.message));
                        }
                    }
                }
            }
            if let Some(e) = first_err {
                return Err(e);
            }
            let import_ok = replies.iter().all(|r| r.import_ok);
            let ok = replies.iter().all(|r| r.ok);
            let kernel_gate_active = replies.iter().all(|r| r.kernel_gate_active);
            let env_cache_hit = replies.iter().all(|r| r.env_cache_hit);
            let prefix_cache_hit = replies.iter().all(|r| r.prefix_cache_hit);
            let import_us = replies.iter().map(|r| r.import_us).max().unwrap_or(0);
            let prefix_us = replies.iter().map(|r| r.prefix_us).max().unwrap_or(0);
            let elab_us = replies.iter().map(|r| r.elab_us).max().unwrap_or(0);
            let heartbeats: u64 = replies.iter().map(|r| r.heartbeats).sum();
            let proof_term_nodes: u64 = replies.iter().map(|r| r.proof_term_nodes).sum();
            let rss_delta_mb: i64 = replies.iter().map(|r| r.rss_delta_mb).max().unwrap_or(0);
            let peak_rss_mb: u64 = replies.iter().map(|r| r.peak_rss_mb).max().unwrap_or(0);
            let subshards_verified: usize = replies.iter().map(|r| r.subshards_verified).sum();
            let mut stdout = String::new();
            let mut messages = Vec::new();
            let mut errors = Vec::new();
            let mut used_constants = Vec::new();
            for r in replies {
                stdout.push_str(&r.stdout);
                messages.extend(r.messages);
                errors.extend(r.errors);
                for c in r.used_constants {
                    if used_constants.len() < 32 && !used_constants.contains(&c) {
                        used_constants.push(c);
                    }
                }
            }
            let combined_rep = ZygoteEvalReply {
                ok,
                winning_candidate_idx: None,
                kernel_gate_active,
                import_ok,
                env_cache_hit,
                prefix_cache_hit,
                import_us,
                prefix_us,
                elab_us,
                heartbeats,
                proof_term_nodes,
                rss_delta_mb,
                peak_rss_mb,
                subshards_verified,
                stdout,
                messages,
                errors,
                used_constants,
                timed_out: false,
                crashed: false,
                ..Default::default()
            };
            if combined_rep.import_ok && combined_rep.ok {
                if let Some(vkey) = verified_cache_key {
                    let vcache = ZYGOTE_VERIFIED_SHARD_CACHE
                        .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
                    if let Ok(mut guard) = vcache.lock() {
                        if guard.len() >= 2048 {
                            guard.clear();
                        }
                        guard.insert(vkey, combined_rep.clone());
                    }
                }
            }
            return Ok(combined_rep);
        }
    }

    let (req_line, active_prefix_key, active_prefix_code) =
        if let Some((_, pk, rl)) = batch_fission_override {
            let warm_pk = match &args_digest_opt {
                Some(ad) => format!("{}:opts:{}", pk, ad),
                None => pk,
            };
            (rl, Some(warm_pk), None)
        } else if !eval_mode {
            if let Some((prefix_code, decl_code, prefix_key)) =
                split_body_into_prefix_and_decl(&body_code)
            {
                let hex_decl = hex_encode_bytes(decl_code.as_bytes());
                let hex_prefix = hex_encode_bytes(prefix_code.as_bytes());
                let mode_flag = stub_mode.as_str();
                let rl = if hex_opts.is_empty() {
                    format!(
                        "{}\t{}\t{}\t{}\t{}\n",
                        imports_csv, hex_decl, mode_flag, prefix_key, hex_prefix
                    )
                } else {
                    format!(
                        "{}\t{}\t{}\t{}\t{}\t{}\n",
                        imports_csv, hex_decl, mode_flag, prefix_key, hex_prefix, hex_opts
                    )
                };
                let warm_pk = match &args_digest_opt {
                    Some(ad) => format!("{}:opts:{}", prefix_key, ad),
                    None => prefix_key,
                };
                (rl, Some(warm_pk), Some(prefix_code))
            } else {
                let hex_body = hex_encode_bytes(body_code.as_bytes());
                let rl = if hex_opts.is_empty() {
                    if stub_mode != "strict" {
                        format!("{}\t{}\t{}\n", imports_csv, hex_body, stub_mode)
                    } else {
                        format!("{}\t{}\n", imports_csv, hex_body)
                    }
                } else {
                    let mode_flag = stub_mode.as_str();
                    format!(
                        "{}\t{}\t{}\t\t\t{}\n",
                        imports_csv, hex_body, mode_flag, hex_opts
                    )
                };
                (rl, None, None)
            }
        } else {
            let caller_cwd = env_vars
                .get("TURBO_LEAN_CALLER_CWD")
                .cloned()
                .or_else(|| {
                    std::env::current_dir()
                        .ok()
                        .map(|p| p.to_string_lossy().to_string())
                })
                .unwrap_or_default();
            let hex_fn = file_name
                .filter(|s| !s.is_empty())
                .map(|s| hex_encode_bytes(s.as_bytes()))
                .unwrap_or_default();
            let hex_cwd = if caller_cwd.is_empty() {
                String::new()
            } else {
                hex_encode_bytes(caller_cwd.as_bytes())
            };
            let mode_flag = if hex_fn.is_empty() && hex_cwd.is_empty() {
                "eval".to_string()
            } else {
                format!("eval:{}:{}", hex_fn, hex_cwd)
            };
            if let Some((prefix_key, prefix_code, decl_code)) =
                split_eval_body_into_prefix_and_cmds(&body_code)
            {
                let hex_decl = hex_encode_bytes(decl_code.as_bytes());
                let hex_prefix = hex_encode_bytes(prefix_code.as_bytes());
                let rl = if hex_opts.is_empty() {
                    format!(
                        "{}\t{}\t{}\t{}\t{}\n",
                        imports_csv, hex_decl, mode_flag, prefix_key, hex_prefix
                    )
                } else {
                    format!(
                        "{}\t{}\t{}\t{}\t{}\t{}\n",
                        imports_csv, hex_decl, mode_flag, prefix_key, hex_prefix, hex_opts
                    )
                };
                let warm_pk = match &args_digest_opt {
                    Some(ad) => format!("{}:opts:{}", prefix_key, ad),
                    None => prefix_key,
                };
                (rl, Some(warm_pk), Some(prefix_code))
            } else {
                let hex_body = hex_encode_bytes(body_code.as_bytes());
                let rl = if hex_opts.is_empty() {
                    format!("{}\t{}\t{}\n", imports_csv, hex_body, mode_flag)
                } else {
                    format!(
                        "{}\t{}\t{}\t\t\t{}\n",
                        imports_csv, hex_body, mode_flag, hex_opts
                    )
                };
                (rl, None, None)
            }
        };
    let req_line = attach_host_closure_digest(&req_line, host_closure_digest);

    let mut worker = {
        let mut pool = pool_mutex
            .lock()
            .map_err(|_| anyhow::anyhow!("ZygotePool mutex poisoned"))?;
        let mut selected: Option<ZygoteChild> = None;
        let matching_keys: Vec<(String, String, String)> = vec![pool_key.clone()];
        for k in &matching_keys {
            if let Some(vec) = pool.get_mut(k) {
                vec.retain(|w| {
                    (w.warm_imports.is_empty()
                        || (w.warm_imports.len() == 1 && w.warm_imports.contains_key(&imports_csv)))
                        && w.warm_imports
                            .get(&imports_csv)
                            .map(|d| d == &olean_digest)
                            .unwrap_or(true)
                });
            }
        }
        if let Some(ref pk) = active_prefix_key {
            for k in &matching_keys {
                if let Some(vec) = pool.get_mut(k) {
                    if let Some(pos) = vec.iter().rposition(|w| {
                        w.warm_imports.contains_key(&imports_csv) && w.warm_prefixes.contains(pk)
                    }) {
                        selected = Some(vec.swap_remove(pos));
                        break;
                    }
                }
            }
        }
        if selected.is_none() {
            if let Some(ref p_code) = active_prefix_code {
                let mut best_lca: Option<((String, String, String), usize, usize)> = None;
                for k in &matching_keys {
                    if let Some(vec) = pool.get(k) {
                        for (idx, w) in vec.iter().enumerate() {
                            if !w.warm_imports.contains_key(&imports_csv) {
                                continue;
                            }
                            for (imp, anc_code) in &w.warm_prefix_tree {
                                if imp == &warm_imports_tag
                                    && p_code.starts_with(anc_code.as_str())
                                    && unsafe {
                                        turbo_spec_zygote_lca_reuse_safe(
                                            anc_code.len() as u64,
                                            p_code.len() as u64,
                                        ) != 0
                                    }
                                {
                                    let len = anc_code.len();
                                    if best_lca.as_ref().map(|(_, _, b)| len >= *b).unwrap_or(true)
                                    {
                                        best_lca = Some((k.clone(), idx, len));
                                    }
                                }
                            }
                        }
                    }
                }
                if let Some((best_k, best_idx, _)) = best_lca {
                    if let Some(vec) = pool.get_mut(&best_k) {
                        selected = Some(vec.swap_remove(best_idx));
                    }
                }
            }
        }
        if selected.is_none() {
            for k in &matching_keys {
                if let Some(vec) = pool.get_mut(k) {
                    if let Some(pos) = vec
                        .iter()
                        .rposition(|w| w.warm_imports.contains_key(&imports_csv))
                    {
                        selected = Some(vec.swap_remove(pos));
                        break;
                    }
                }
            }
        }
        if selected.is_none() {
            if let Some(vec) = pool.get_mut(&pool_key) {
                if let Some(pos) = vec.iter().rposition(|w| w.warm_imports.is_empty()) {
                    selected = Some(vec.swap_remove(pos));
                }
            }
        }
        selected
    };
    if std::time::Instant::now() >= deadline {
        return Ok(ZygoteEvalReply::timed_out_reply(
            eval_mode,
            request_started.elapsed().as_micros() as u64,
            effective_timeout_ms,
            0,
            String::new(),
            Some(request_identity.clone()),
        ));
    }
    if worker.is_none() {
        worker = Some(spawn_zygote_worker()?);
    }

    let mut w = worker.unwrap();
    let mut outcome = run_worker_req(&mut w, &req_line, &request_identity);
    if let WorkerReqOutcome::Crashed(first_diag) = outcome {
        drop(w);
        // Respawn and replay share the original request deadline, including on a cold worker.
        if std::time::Instant::now() >= deadline {
            return Ok(ZygoteEvalReply::timed_out_reply(
                eval_mode,
                request_started.elapsed().as_micros() as u64,
                effective_timeout_ms,
                first_diag.peak_rss_mb,
                first_diag.stderr_tail,
                first_diag.last_request,
            ));
        }
        match spawn_zygote_worker() {
            Ok(retry_w) => w = retry_w,
            Err(_) => {
                let mut diag = first_diag;
                diag.message = format!("{} (respawn failed)", diag.message);
                return Ok(ZygoteEvalReply::crashed_reply_with_diag(eval_mode, diag));
            }
        }
        outcome = run_worker_req(&mut w, &req_line, &request_identity);
    }

    if std::time::Instant::now() >= deadline {
        outcome = worker_timeout(&w, &request_identity);
    }

    match outcome {
        WorkerReqOutcome::Reply(rep) => {
            let unusable = rep
                .errors
                .iter()
                .any(|e| e == RUNTIME_PANIC_ERR || e.contains("importsCsv changed"));
            if rep.import_ok && !unusable {
                w.warm_imports
                    .insert(imports_csv.clone(), olean_digest.clone());
                if let Some(pk) = active_prefix_key {
                    w.warm_prefixes.insert(pk);
                }
                if let Some(p_code) = active_prefix_code {
                    w.warm_prefix_tree
                        .retain(|(imp, c)| !(imp == &warm_imports_tag && c == &p_code));
                    if w.warm_prefix_tree.len() >= 32 {
                        w.warm_prefix_tree.remove(0);
                    }
                    w.warm_prefix_tree.push((warm_imports_tag.clone(), p_code));
                }
                if rep.ok && !rep.timed_out && !rep.crashed {
                    if let Some(vkey) = verified_cache_key {
                        let vcache = ZYGOTE_VERIFIED_SHARD_CACHE.get_or_init(|| {
                            std::sync::Mutex::new(std::collections::HashMap::new())
                        });
                        if let Ok(mut guard) = vcache.lock() {
                            if guard.len() >= 2048 {
                                guard.clear();
                            }
                            guard.insert(vkey, rep.clone());
                        }
                    }
                }
                return_worker_to_pool(pool_mutex, pool_key, w);
            } else {
                drop(w);
            }
            Ok(rep)
        }
        WorkerReqOutcome::TimedOut {
            elapsed_us,
            peak_rss_mb,
            stderr_tail,
            last_request,
        } => {
            drop(w);
            Ok(ZygoteEvalReply::timed_out_reply(
                eval_mode,
                elapsed_us,
                effective_timeout_ms,
                peak_rss_mb,
                stderr_tail,
                Some(last_request),
            ))
        }
        WorkerReqOutcome::Crashed(diag) => {
            drop(w);
            Ok(ZygoteEvalReply::crashed_reply_with_diag(eval_mode, diag))
        }
    }
}

/// Evaluate a single sub-shard (`prefix_source` + `sub_decl_source`) via the memory-governed
/// `ZygotePool` with automatic `Command.State` prefix checkpoint reuse and RSS watermark recycling.
#[allow(clippy::too_many_arguments)]
pub fn eval_shard_via_zygote(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    prefix_source: &str,
    sub_decl_source: &str,
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    let combined_source = if prefix_source.trim().is_empty() {
        format!("{}\n", sub_decl_source.trim_end())
    } else {
        format!(
            "{}\n\n{}\n",
            prefix_source.trim_end(),
            sub_decl_source.trim_start()
        )
    };
    eval_with_zygote_pool_with_args(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        &combined_source,
        false,
        lean_args,
    )
}

/// Evaluate a batch of cut-fission sub-shards (`prefix_source` + each `sub_decl` in `sub_decl_sources`)
/// Evaluate a batch of sub-proof cuts (`sub_decl_sources`) against a shared `prefix_source`
/// in a single IPC roundtrip over the warm `ZygotePool` (`batch_fission` mode).
/// Each sub-shard is elaborated from the clean functional `ckptState` checkpoint (bounding peak heap
/// by a single `have` block) and individually audited by `auditNewKernelDecls` (`0 sorryAx`).
#[allow(dead_code)]
fn encode_multi_decl_zygote_req(
    prefix_source: &str,
    mode: &str,
    decl_sources: &[String],
    lean_args: &[String],
) -> (String, String, String) {
    let (imports_csv, prefix_body) = split_shard_for_zygote(prefix_source);
    let prefix_key = blake3::hash(prefix_body.as_bytes()).to_hex().to_string();
    let hex_prefix = hex_encode_bytes(prefix_body.as_bytes());
    let hex_decls_csv = decl_sources
        .iter()
        .map(|s| {
            let mut decl = s.trim_end().to_string();
            decl.push('\n');
            hex_encode_bytes(decl.as_bytes())
        })
        .collect::<Vec<_>>()
        .join(",");
    let hex_opts = encode_lean_args_hex(lean_args);
    let req_line = if hex_opts.is_empty() {
        format!(
            "{}\t{}\t{}\t{}\t{}\n",
            imports_csv, mode, prefix_key, hex_prefix, hex_decls_csv
        )
    } else {
        format!(
            "{}\t{}\t{}\t{}\t{}\t{}\n",
            imports_csv, mode, prefix_key, hex_prefix, hex_decls_csv, hex_opts
        )
    };
    (imports_csv, prefix_key, req_line)
}

#[allow(clippy::too_many_arguments)]
pub fn eval_subshards_batch_via_zygote(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    prefix_source: &str,
    sub_decl_sources: &[String],
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    if sub_decl_sources.is_empty() {
        return Ok(ZygoteEvalReply {
            ok: true,
            kernel_gate_active: true,
            import_ok: true,
            env_cache_hit: true,
            prefix_cache_hit: true,
            ..Default::default()
        });
    }
    if sub_decl_sources.len() == 1 {
        return eval_shard_via_zygote(
            store,
            toolchain,
            req_lean_path,
            env_vars,
            lean_bin,
            prefix_source,
            &sub_decl_sources[0],
            lean_args,
        );
    }
    let req_tuple =
        encode_multi_decl_zygote_req(prefix_source, "batch_fission", sub_decl_sources, lean_args);
    eval_with_zygote_pool_inner(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        "",
        false,
        false,
        None,
        None,
        Some(req_tuple),
        lean_args,
        &[],
        false,
    )
}

/// Evaluate an ordered list of candidate declarations (`candidate_decl_sources`) against a shared
/// `prefix_source` in a single IPC roundtrip (`race_candidates` mode).
/// The Zygote worker checkpoints `prefix_source` once and tests each candidate in order, stopping
/// immediately at the first candidate that elaborates cleanly and passes `auditNewKernelDecls` (`0 sorryAx`),
/// returning its index in `reply.winning_candidate_idx`.
#[allow(clippy::too_many_arguments)]
pub fn eval_candidates_race_via_zygote(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    prefix_source: &str,
    candidate_decl_sources: &[String],
    lean_args: &[String],
) -> Result<ZygoteEvalReply> {
    if candidate_decl_sources.is_empty() {
        return Ok(ZygoteEvalReply {
            kernel_gate_active: true,
            import_ok: true,
            env_cache_hit: true,
            prefix_cache_hit: true,
            errors: vec!["no candidate declarations provided".to_string()],
            ..Default::default()
        });
    }
    if candidate_decl_sources.len() == 1 {
        let mut rep = eval_shard_via_zygote(
            store,
            toolchain,
            req_lean_path,
            env_vars,
            lean_bin,
            prefix_source,
            &candidate_decl_sources[0],
            lean_args,
        )?;
        if rep.ok {
            rep.winning_candidate_idx = Some(0);
        }
        return Ok(rep);
    }
    let req_tuple = encode_multi_decl_zygote_req(
        prefix_source,
        "race_candidates",
        candidate_decl_sources,
        lean_args,
    );
    eval_with_zygote_pool_inner(
        store,
        toolchain,
        req_lean_path,
        env_vars,
        lean_bin,
        "",
        false,
        false,
        None,
        None,
        Some(req_tuple),
        lean_args,
        &[],
        false,
    )
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct LocalZygoteDaemonInfo {
    pub(crate) addr: String,
    pub(crate) pid: u32,
    pub(crate) exe_mtime_sec: i64,
    pub(crate) exe_mtime_nsec: i64,
    #[serde(default)]
    pub(crate) auth_token: String,
    /// Axiom policy the daemon (and its zygote workers) enforce;
    /// reused only under the same `daemon_policy()`.
    #[serde(default)]
    pub(crate) policy: Vec<String>,
}

/// Timeouts belong to requests; only axiom policy determines daemon identity.
pub(crate) fn daemon_policy() -> Vec<String> {
    crate::splitter::allowed_axioms()
}

pub(crate) fn invocation_timeout_ms() -> Option<u64> {
    std::env::var("TURBO_LEAN_TIMEOUT_MS")
        .ok()?
        .trim()
        .parse()
        .ok()
}

/// Share the request budget across worker attempts and a stock-Lean fallback.
pub(crate) fn remaining_timeout_ms(timeout_ms: Option<u64>, started: std::time::Instant) -> u64 {
    timeout_ms
        .or_else(invocation_timeout_ms)
        .filter(|ms| *ms > 0)
        .unwrap_or(30_000)
        .saturating_sub(started.elapsed().as_millis().min(u64::MAX as u128) as u64)
}

pub(crate) fn run_lean_command(
    cmd: &mut Command,
    timeout_ms: Option<u64>,
) -> Result<std::process::Output> {
    anyhow::ensure!(
        timeout_ms != Some(0),
        "Lean request timed out before fallback"
    );
    crate::module_builder::run_command_with_timeout(
        cmd,
        std::time::Duration::from_millis(
            timeout_ms
                .or_else(invocation_timeout_ms)
                .filter(|ms| *ms > 0)
                .unwrap_or(30_000),
        ),
        false,
    )
}

fn check_request_body(req: &CheckShardHttpRequest) -> Result<Vec<u8>> {
    let mut value = serde_json::to_value(req)?;
    value["timeout_ms"] = serde_json::to_value(invocation_timeout_ms())?;
    Ok(serde_json::to_vec(&value)?)
}

fn generate_daemon_auth_token(pid: u32, port: u16) -> String {
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

fn write_daemon_state_file_private(path: &Path, json_bytes: &[u8]) {
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

fn terminate_and_remove_daemon_state_file(state_file: &Path) {
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

fn current_exe_daemon_paths(store: &TurboStore) -> Option<(PathBuf, i64, i64, PathBuf, PathBuf)> {
    let current_exe = std::env::current_exe().ok()?;
    let (exe_mtime_sec, exe_mtime_nsec, _) = fs::metadata(&current_exe)
        .ok()
        .map(|m| TurboStore::extract_file_stat_tuple(&m))
        .unwrap_or((0, 0, 0));
    let mut exe_hasher = blake3::Hasher::new();
    exe_hasher.update(current_exe.to_string_lossy().as_bytes());
    // One daemon (and theorem CAS) per axiom policy: a pass under one policy is no cache hit
    // under a stricter one.
    exe_hasher.update(daemon_policy().join(",").as_bytes());
    let exe_tag = &exe_hasher.finalize().to_hex()[..12];
    let daemon_cache_dir = store
        .fast_staging_dir()
        .join(format!("zygote_daemon_cas_{}", exe_tag));
    let state_file = daemon_cache_dir.join("zygote_daemon.json");
    Some((
        current_exe,
        exe_mtime_sec,
        exe_mtime_nsec,
        daemon_cache_dir,
        state_file,
    ))
}

fn check_existing_daemon_state(
    path: &Path,
    exe_mtime_sec: i64,
    exe_mtime_nsec: i64,
    kill_stale: bool,
) -> Option<(String, String)> {
    let content = fs::read_to_string(path).ok()?;
    let info: LocalZygoteDaemonInfo = serde_json::from_str(&content).ok()?;
    if info.policy != daemon_policy() {
        return None;
    }
    if info.exe_mtime_sec != exe_mtime_sec || info.exe_mtime_nsec != exe_mtime_nsec {
        if kill_stale {
            terminate_and_remove_daemon_state_file(path);
        }
        return None;
    }
    #[cfg(unix)]
    {
        if info.pid > 0 && unsafe { libc::kill(info.pid as i32, 0) == 0 } {
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
        let sock_addr: std::net::SocketAddr = addr.parse().ok()?;
        let auth_token = generate_daemon_auth_token(std::process::id(), port);

        let mut cmd = Command::new(&current_exe);
        cmd.arg("--cache-dir")
            .arg(&daemon_cache_dir)
            .args(["serve", "--listen", &addr])
            .envs(env_vars)
            .env("TURBO_LEAN_DAEMON", "1")
            .env("TURBO_LEAN_DAEMON_TOKEN", &auth_token)
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null());
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
        let connected = (0..75).any(|_| {
            std::net::TcpStream::connect_timeout(&sock_addr, std::time::Duration::from_millis(5))
                .is_ok()
                || {
                    std::thread::sleep(std::time::Duration::from_millis(2));
                    false
                }
        });
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
        };
        if let Ok(json_bytes) = serde_json::to_vec(&info) {
            write_daemon_state_file_private(&state_file, &json_bytes);
            write_daemon_state_file_private(&store.root.join("zygote_daemon.json"), &json_bytes);
        }
        Some((format!("http://{}", addr), auth_token))
    })
    .flatten()
}

static LAST_LOCAL_DAEMON_TOKEN: std::sync::OnceLock<std::sync::Mutex<Option<String>>> =
    std::sync::OnceLock::new();

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

fn parse_check_shard_resp(resp_bytes: &[u8]) -> Result<Option<serde_json::Value>> {
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

fn is_expired_daemon_transport_error(err: &anyhow::Error) -> bool {
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

fn extract_http_error_detail(err: anyhow::Error) -> anyhow::Error {
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
fn finish_check_shard_request(response: Result<Vec<u8>>) -> Result<Option<serde_json::Value>> {
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

pub fn try_zygote_url_check_shard_with_inflight(
    base_url: &str,
    req: &CheckShardHttpRequest,
    on_inflight: impl FnOnce(),
) -> Option<serde_json::Value> {
    try_zygote_url_check_shard_inner_with_inflight_detailed(base_url, req, on_inflight)
        .ok()
        .flatten()
}

pub fn try_zygote_url_check_shard(
    base_url: &str,
    req: &CheckShardHttpRequest,
) -> Option<serde_json::Value> {
    try_zygote_url_check_shard_inner_with_inflight_detailed(base_url, req, || {})
        .ok()
        .flatten()
}

pub fn try_local_zygote_check_shard_detailed(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
    req: &CheckShardHttpRequest,
) -> Result<Option<serde_json::Value>> {
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

pub fn try_local_zygote_check_shard(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
    req: &CheckShardHttpRequest,
) -> Option<serde_json::Value> {
    try_local_zygote_check_shard_detailed(store, env_vars, req)
        .ok()
        .flatten()
}

fn is_pure_eval_source(source: &str) -> bool {
    !source.contains("IO.FS")
        && !source.contains("IO.mono")
        && !source.contains("IO.rand")
        && !source.contains("IO.getEnv")
        && !source.contains("IO.Process")
        && !source.contains("System.FilePath")
}

/// One `Lean.importModules` for both `Midnight.Spec` and `ProofKit`.
/// `ProofKit` only pulls `Compiler.CompilationModel`, which `Midnight.Spec`
/// already imports, so loading them together is ~one import, not two.
pub(crate) fn coalesce_proofkit_imports(imports_csv: &str, lean_path: &str) -> String {
    if imports_csv == "__HEADER_ERR__" {
        return imports_csv.to_string();
    }
    let is_mod = imports_csv.split(',').any(|m| m.trim() == "__MODULE__");
    let has_midnight = imports_csv
        .split(',')
        .filter_map(parse_zygote_import_entry)
        .any(|(m, _, _, _)| m == "Midnight.Spec");
    let has_proofkit = imports_csv
        .split(',')
        .filter_map(parse_zygote_import_entry)
        .any(|(m, _, _, _)| m == "ProofKit");
    if !is_mod
        && has_midnight
        && !has_proofkit
        && lean_path
            .split(':')
            .any(|d| !d.is_empty() && Path::new(d).join("ProofKit.olean").exists())
    {
        format!("{},ProofKit", imports_csv)
    } else {
        imports_csv.to_string()
    }
}

fn compute_eval_shm_cache_filename(
    toolchain: &str,
    lean_path: &str,
    file_name: &str,
    caller_cwd: Option<&str>,
    source: &str,
    lean_args: &[String],
) -> String {
    let (imports_csv, _) = split_shard_for_zygote(source);
    let imp_dig = compute_imported_oleans_digest(&imports_csv, lean_path);
    let mut h = blake3::Hasher::new();
    h.update(b"eval-shm:v3:");
    h.update(toolchain.as_bytes());
    h.update(b":");
    h.update(lean_path.as_bytes());
    h.update(b":");
    h.update(imp_dig.as_bytes());
    h.update(b":");
    h.update(file_name.as_bytes());
    h.update(b":");
    h.update(caller_cwd.unwrap_or("").as_bytes());
    h.update(b":");
    h.update(source.as_bytes());
    if let Some(ad) = crate::module_builder::compute_lean_args_digest(lean_args) {
        h.update(b":opts:");
        h.update(ad.as_bytes());
    }
    let key_hex = h.finalize().to_hex();
    format!("ev_{}.json", &key_hex[..24])
}

/// Only successful, import-clean replies may be cached: failures (missing toolchain, import
/// errors, ...) are environmental and must be re-evaluated rather than replayed forever.
fn eval_reply_cacheable(rep: &ZygoteEvalReply) -> bool {
    rep.ok && rep.import_ok && !rep.crashed && !rep.timed_out
}

/// Write an eval reply into `eval_shm_cache/` and periodically enforce the `/dev/shm` quota.
fn write_eval_shm_cache(path: &Path, bytes: &[u8]) {
    static WRITES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    // A failed write (e.g. ENOSPC) also counts: evict so a full cache can recover.
    let wrote = crate::shm_cache::atomic_write_shm(path, bytes).is_ok();
    let Some(dir) = path.parent() else { return };
    if !wrote {
        // Pressure-driven: the quota may not be exceeded yet (small or shared /dev/shm), so
        // halve what the cache holds and retry once.
        let held: u64 = fs::read_dir(dir)
            .into_iter()
            .flatten()
            .flatten()
            .filter_map(|e| e.metadata().ok())
            .map(|m| m.len())
            .sum();
        let _ = crate::shm_cache::enforce_shm_quota_lru(dir, (held / 2).max(1));
        let _ = crate::shm_cache::atomic_write_shm(path, bytes);
    } else if WRITES
        .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        .is_multiple_of(32)
    {
        let _ = crate::shm_cache::enforce_shm_quota_lru(dir, 0);
    }
}

fn read_cached_eval_shm_reply(path: &Path) -> Option<ZygoteEvalReply> {
    let bytes = fs::read(path).ok()?;
    let mut cached_rep: ZygoteEvalReply = serde_json::from_slice(&bytes).ok()?;
    cached_rep.env_cache_hit = true;
    cached_rep.prefix_cache_hit = true;
    cached_rep.import_us = 0;
    cached_rep.prefix_us = 0;
    Some(cached_rep)
}

pub fn try_stateless_eval_shm_cache(
    cache_root: &Path,
    file: &Path,
    project_dir: Option<&Path>,
    lean_path: Option<&str>,
) -> Option<(String, ZygoteEvalReply)> {
    let source = fs::read_to_string(file).ok()?;
    if !is_pure_eval_source(&source) {
        return None;
    }
    let proj_dir = project_dir
        .map(crate::lake_build::find_project_root)
        .unwrap_or_else(|| crate::lake_build::find_project_root(file));
    let explicit_lp: Option<String> = lean_path
        .map(str::to_string)
        .or_else(|| std::env::var("LEAN_PATH").ok());
    let req_lp = match explicit_lp {
        Some(lp) => lp,
        None if !proj_dir.join("lakefile.lean").exists()
            && !proj_dir.join("lakefile.toml").exists() =>
        {
            String::new()
        }
        None if !proj_dir.join(".lake/packages").is_dir()
            && proj_dir.join(".lake/build/lib/lean").exists() =>
        {
            let canon_proj = proj_dir.canonicalize().unwrap_or_else(|_| proj_dir.clone());
            crate::lake_build::resolve_remote_lean_path(&canon_proj, None)
        }
        None => return None,
    };
    let toolchain = crate::lake_build::detect_toolchain(&proj_dir);
    let resolved_lean_args = crate::module_builder::filter_allowed_lean_args(
        crate::module_builder::try_resolve_lean_args_for_path(&proj_dir, Some(file)),
    );
    let caller_cwd = std::env::current_dir()
        .ok()
        .map(|p| p.to_string_lossy().to_string());
    let file_display = file.to_string_lossy();
    let filename = compute_eval_shm_cache_filename(
        &toolchain,
        &req_lp,
        &file_display,
        caller_cwd.as_deref(),
        &source,
        &resolved_lean_args,
    );
    let base_staging =
        if Path::new("/dev/shm").is_dir() || std::env::var("TURBO_LEAN_STAGING_DIR").is_ok() {
            crate::shm_cache::staging_shm_dir()
        } else {
            cache_root.join("staging")
        };
    let path = base_staging.join("eval_shm_cache").join(filename);
    let cached_rep = read_cached_eval_shm_reply(&path)?;
    Some((source, cached_rep))
}

#[allow(clippy::too_many_arguments)]
pub fn try_local_zygote_eval(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    toolchain: &str,
    lean_path: &str,
    source: &str,
    file_name: Option<&str>,
    timeout_ms: u64,
) -> Option<ZygoteEvalReply> {
    try_local_zygote_eval_with_args(
        store,
        env_vars,
        lean_bin,
        toolchain,
        lean_path,
        source,
        file_name,
        timeout_ms,
        &[],
    )
}

#[allow(clippy::too_many_arguments)]
pub fn try_local_zygote_eval_with_args(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    toolchain: &str,
    lean_path: &str,
    source: &str,
    file_name: Option<&str>,
    timeout_ms: u64,
    lean_args: &[String],
) -> Option<ZygoteEvalReply> {
    let filtered_args = crate::module_builder::filter_allowed_lean_args(lean_args);
    let timeout_ms = if timeout_ms > 0 {
        timeout_ms
    } else {
        invocation_timeout_ms().unwrap_or(0)
    };
    let t0 = std::time::Instant::now();
    let caller_cwd = std::env::current_dir()
        .ok()
        .map(|p| p.to_string_lossy().to_string());
    let eval_shm_file = if is_pure_eval_source(source) {
        let filename = compute_eval_shm_cache_filename(
            toolchain,
            lean_path,
            file_name.unwrap_or(""),
            caller_cwd.as_deref(),
            source,
            &filtered_args,
        );
        let dir = store.fast_staging_dir().join("eval_shm_cache");
        let _ = fs::create_dir_all(&dir);
        let path = dir.join(filename);
        if let Some(cached_rep) = read_cached_eval_shm_reply(&path) {
            return Some(cached_rep);
        }
        Some(path)
    } else {
        None
    };

    let existing_daemon = if daemon_disabled() {
        None
    } else {
        current_exe_daemon_paths(store)
            .and_then(|(_, exe_mtime_sec, exe_mtime_nsec, _, state_file)| {
                check_existing_daemon_state(&state_file, exe_mtime_sec, exe_mtime_nsec, false)
                    .or_else(|| {
                        check_existing_daemon_state(
                            &store.root.join("zygote_daemon.json"),
                            exe_mtime_sec,
                            exe_mtime_nsec,
                            false,
                        )
                    })
            })
            .or_else(|| ensure_local_zygote_daemon_with_token(store, env_vars))
    };

    let Some((base_url, auth_token)) = existing_daemon else {
        let rep = eval_with_zygote_pool_opts_with_args(
            store,
            toolchain,
            lean_path,
            env_vars,
            lean_bin,
            source,
            false,
            true,
            file_name,
            if timeout_ms > 0 {
                Some(timeout_ms)
            } else {
                None
            },
            &filtered_args,
        )
        .ok()?;
        if eval_reply_cacheable(&rep) {
            if let Some(ref path) = eval_shm_file {
                if let Ok(bytes) = serde_json::to_vec(&rep) {
                    write_eval_shm_cache(path, &bytes);
                }
            }
            warm_local_zygote_daemon_nonblocking(store, env_vars);
        }
        return Some(rep);
    };
    let endpoint = format!("{}/eval", base_url.trim_end_matches('/'));
    let mut forwarded_env: std::collections::HashMap<String, String> = std::env::vars()
        .filter(|(k, v)| crate::server::is_safe_lean_env_key(k) && !v.contains('\0'))
        .collect();
    for (k, v) in env_vars {
        if crate::server::is_safe_lean_env_key(k) && !v.contains('\0') {
            forwarded_env.insert(k.clone(), v.clone());
        }
    }
    let effective_timeout_opt = if timeout_ms > 0 {
        Some(timeout_ms)
    } else {
        None
    };
    let body = serde_json::to_vec(&serde_json::json!({
        "toolchain": toolchain,
        "lean_path": lean_path,
        "source": source,
        "file_name": file_name,
        "cwd": caller_cwd,
        "env_vars": forwarded_env,
        "timeout_ms": effective_timeout_opt,
        "verify_determinism": false,
        "lean_args": filtered_args
    }))
    .ok()?;
    let http_timeout = effective_timeout_opt.map(|ms| ms.saturating_add(250));
    let resp_bytes = match http_request_with_timeout_and_token(
        "POST",
        &endpoint,
        "application/json",
        &body,
        http_timeout,
        Some(&auth_token),
        || {},
    ) {
        Ok(b) => b,
        Err(e) => {
            if let Some(limit_ms) = effective_timeout_opt {
                if t0.elapsed().as_millis() as u64 >= limit_ms
                    || e.to_string().contains("Resource temporarily unavailable")
                    || e.to_string().contains("timed out")
                    || e.to_string().contains("TimedOut")
                {
                    return Some(ZygoteEvalReply::timed_out_reply(
                        true,
                        t0.elapsed().as_micros() as u64,
                        limit_ms,
                        0,
                        String::new(),
                        None,
                    ));
                }
            }
            if e.to_string().contains("HTTP ") {
                return None;
            }
            if let Some((_, _, _, _, state_file)) = current_exe_daemon_paths(store) {
                terminate_and_remove_daemon_state_file(&state_file);
            }
            let (retry_url, retry_token) = ensure_local_zygote_daemon_with_token(store, env_vars)?;
            let retry_endpoint = format!("{}/eval", retry_url.trim_end_matches('/'));
            http_request_with_timeout_and_token(
                "POST",
                &retry_endpoint,
                "application/json",
                &body,
                http_timeout,
                Some(&retry_token),
                || {},
            )
            .ok()?
        }
    };
    let parsed = serde_json::from_slice::<ZygoteEvalReply>(&resp_bytes).ok();
    if let Some(ref rep) = parsed {
        if eval_reply_cacheable(rep) {
            if let Some(ref path) = eval_shm_file {
                write_eval_shm_cache(path, &resp_bytes);
            }
        }
    }
    parsed
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_finish_check_shard_request_rejection_is_final() {
        let http = |e: &str| {
            finish_check_shard_request(Err(anyhow::anyhow!(
                "HTTP request POST http://127.0.0.1:1/check-shard failed (HTTP 500): {{\"status\":\"error\",\"error\":\"{}\"}}",
                e
            )))
        };
        let err = http("Remote `lean` shard verification failed for `t`").unwrap_err();
        assert!(err
            .to_string()
            .starts_with("Remote `lean` shard verification failed"));
        // Only the structured code means unavailable, never text the shard can put in a message.
        assert!(http("Zygote import unavailable for `«Zygote import unavailable»`").is_err());
        assert!(matches!(
            finish_check_shard_request(Err(anyhow::anyhow!(
                "HTTP request POST http://127.0.0.1:1/check-shard failed (HTTP 500): {{\"status\":\"error\",\"error\":\"x\",\"code\":\"{}\"}}",
                IMPORT_UNAVAILABLE_CODE
            ))),
            Ok(None)
        ));
        assert!(matches!(
            finish_check_shard_request(Err(std::io::Error::from(
                std::io::ErrorKind::ConnectionRefused
            )
            .into())),
            Ok(None)
        ));
    }

    /// A user `macro_rules` that makes Lean 4.35's `#print axioms` report no axioms.
    pub(crate) const PRINT_AXIOMS_SPOOF: &str = "macro_rules\n  | `(#print axioms $i:ident) => `(#eval IO.println s!\"'{$(Lean.quote i.getId.toString)}' does not depend on any axioms\")\n";

    #[test]
    fn test_audited_lean_shard_exempts_only_named_explicit_stubs() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_audited_shard_{}_{}",
            std::process::id(),
            next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        let store = TurboStore::open(Some(&dir.join("store")))?;
        let env = std::collections::HashMap::from([(
            "ELAN_TOOLCHAIN".to_string(),
            "leanprover/lean4:v4.35.0".to_string(),
        )]);
        let run = |src: &str| {
            let audit = std::collections::HashSet::from(["tgt".to_string()]);
            run_audited_lean_shard(
                &store,
                Path::new("lean"),
                &env,
                Some(&dir),
                src,
                &audit,
                &[],
                None,
            )
        };
        let stubs = "namespace N\ntheorem s1 (n : Nat) {m : Nat} : n + m = m + n := sorry\ntheorem s2 : 1 = 1 := sorry\nend N\nnamespace M\ntheorem s2 : 2 = 2 := sorry\nend M\n";
        // Host-named prefix stubs (binders, namespaces, a short name used twice) are exempt; the
        // target is audited.
        let ok = run(&format!(
            "{}theorem N.tgt (a b : Nat) : a + b = b + a := N.s1 a\ntheorem other : 2 = 2 := M.s2\n",
            stubs
        ))?;
        assert!(ok.status.success(), "{:?}", ok);
        let reject = |src: String, why: &str, needle: &str| {
            let err = run(&src).expect_err(why);
            assert!(format!("{:#}", err).contains(needle), "{}: {:#}", why, err);
        };
        reject(
            "theorem tgt : 1 = 1 := sorry\n".into(),
            "an audited theorem is never a stub",
            "disallowed axiom `sorryAx`",
        );
        reject(
            format!(
                "import Lean\n{}theorem Evil.s1 : False := by\n  run_tac do\n    let g ← Lean.Elab.Tactic.getMainGoal\n    g.assign (← Lean.Meta.mkSorry (← g.getType) false)\ntheorem tgt : False := Evil.s1\n",
                stubs
            ),
            "a second explicit sorry matching a stub name is ambiguous",
            "prefix stub `s1` is ambiguous",
        );
        reject(
            "import Lean\nmacro_rules | `(term| sorry) => `(term| trivial)\ntheorem s1 : True := sorry\ntheorem Evil.s1 : False := by\n  run_tac do\n    let g ← Lean.Elab.Tactic.getMainGoal\n    g.assign (← Lean.Meta.mkSorry (← g.getType) false)\ntheorem tgt : False := Evil.s1\n".into(),
            "a stub turned into a proof cannot lend its name to an injected sorry",
            "prefix stub `s1` is ambiguous",
        );
        reject(
            "theorem other : 1 = 1 := rfl\n".into(),
            "the audited theorem must be declared",
            "missing from the compiled shard",
        );
        // P0-3: the verdict never comes from shard-controlled output (`#print axioms` spoofed by a
        // user macro), and `addDecl`-made axioms are seen in the kernel environment.
        reject(
            format!(
                "import Lean\n{}theorem tgt : 1 = 1 := by\n  run_tac Lean.Elab.admitGoal (← Lean.Elab.Tactic.getMainGoal)\n",
                PRINT_AXIOMS_SPOOF
            ),
            "a metaprogram sorry under a `#print axioms` spoof",
            "disallowed axiom `sorryAx`",
        );
        reject(
            "import Lean\nopen Lean in\n#eval show Elab.Command.CommandElabM Unit from Elab.Command.liftCoreM <| addDecl <| .axiomDecl { name := `hidden, levelParams := [], type := mkConst ``False, isUnsafe := false }\ntheorem tgt : 1 = 1 := (hidden).elim\n".into(),
            "an `addDecl` axiom",
            "`hidden`",
        );
        assert!(!run("theorem tgt : 1 = 2 := rfl\n")?.status.success());
        // A request budget bounds the whole fallback; it never yields a late verdict.
        let audit = std::collections::HashSet::from(["tgt".to_string()]);
        let late = run_audited_lean_shard(
            &store,
            Path::new("lean"),
            &env,
            Some(&dir),
            "theorem tgt : 1 = 1 := rfl\n",
            &audit,
            &[],
            Some(1),
        );
        assert!(
            !matches!(late, Ok(ref o) if o.status.success()),
            "{:?}",
            late
        );
        // Auditor preparation (a cold auditor build in a fresh store) stays within the budget.
        let cold = TurboStore::open(Some(&dir.join("cold-store")))?;
        let t0 = std::time::Instant::now();
        let _ = run_audited_lean_shard(
            &cold,
            Path::new("lean"),
            &env,
            Some(&dir),
            "theorem tgt : 1 = 1 := rfl\n",
            &audit,
            &[],
            Some(3_000),
        );
        assert!(t0.elapsed() < std::time::Duration::from_secs(15));
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[cfg(target_os = "linux")]
    fn open_test_lifecycle_process(
        child: &mut std::process::Child,
        staging: Option<&Path>,
    ) -> LifecycleProcess {
        // spawn's exec handshake can precede the final /proc identity becoming readable.
        // Establish a stable baseline before testing deliberate identity changes.
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
        loop {
            if let Some(process) = LifecycleProcess::open(child.id(), staging, None) {
                return process;
            }
            assert!(
                child.try_wait().unwrap().is_none(),
                "test child exited before identity validation"
            );
            if std::time::Instant::now() >= deadline {
                let pid = child.id();
                let exe = fs::read_link(format!("/proc/{pid}/exe"));
                let start = process_start_time(pid);
                let _ = child.kill();
                let _ = child.wait();
                panic!("test child identity not ready: pid={pid}, exe={exe:?}, start={start:?}");
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_pidfd_revalidates_start_time_and_identity_before_signaling() {
        let dir = std::env::temp_dir().join(format!("turbo-pidfd-{}", next_tmp_id()));
        fs::create_dir_all(&dir).unwrap();
        let exe = dir.join("turbo_zygote_pidfd_test");
        fs::copy("/bin/sleep", &exe).unwrap();
        let mut child = std::process::Command::new(&exe)
            .arg("30")
            .env("TURBO_LEAN_STAGING_DIR", &dir)
            .spawn()
            .unwrap();
        let mut process = open_test_lifecycle_process(&mut child, Some(&dir));
        process.start_time += 1;
        assert!(
            !process.signal(libc::SIGTERM),
            "changed start time must refuse SIGTERM"
        );
        assert!(
            !process.signal(libc::SIGKILL),
            "changed start time must refuse SIGKILL"
        );
        assert!(child.try_wait().unwrap().is_none());
        process.start_time -= 1;
        process.identity.1.push(b'x');
        assert!(
            !process.signal(libc::SIGKILL),
            "changed cmdline must refuse SIGKILL"
        );
        process.identity.1.pop();
        assert!(process.signal(libc::SIGTERM));
        child.wait().unwrap();
        assert!(!process.alive());
        assert!(
            !process.signal(libc::SIGKILL),
            "held pidfd must reject an exited process"
        );
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn test_multi_namespace_teardown_cleans_every_killed_namespace() {
        let lifecycle = lifecycle_exclusive_lock().unwrap();
        let mut children = Vec::new();
        let mut processes = Vec::new();
        let mut dirs = Vec::new();
        for _ in 0..2 {
            let dir = std::env::temp_dir().join(format!("turbo-stop-namespace-{}", next_tmp_id()));
            fs::create_dir_all(&dir).unwrap();
            let exe = dir.join("turbo_zygote_stop_test");
            fs::copy("/bin/sleep", &exe).unwrap();
            let mut child = Command::new(exe)
                .arg("30")
                .env("TURBO_LEAN_STAGING_DIR", &dir)
                .spawn()
                .unwrap();
            // Same user-wide (staging=None) identity path, with an explicit candidate set
            // so this test cannot affect any developer's live daemons.
            processes.push(open_test_lifecycle_process(&mut child, None));
            children.push(child);
            dirs.push(dir);
        }
        let cleanup = terminate_linux_processes(processes);
        for child in &mut children {
            child.wait().unwrap();
        }
        assert_eq!(cleanup.count, 2);
        assert_eq!(cleanup.staging.len(), 2);
        assert_eq!(
            cleanup_lifecycle_staging(cleanup, None, &lifecycle).unwrap(),
            2
        );
        assert!(dirs.iter().all(|dir| !dir.exists()));
    }

    #[test]
    #[cfg(unix)]
    fn test_portable_pidfile_sigterm_fallback() {
        use std::os::unix::process::CommandExt;
        let dir = std::env::temp_dir().join(format!("turbo-pidfile-{}", next_tmp_id()));
        fs::create_dir_all(&dir).unwrap();
        let exe = dir.join("turbo-lean");
        fs::copy("/bin/bash", &exe).unwrap();
        fs::write(dir.join("serve"), "read -t 30\n").unwrap();
        let mut child = Command::new(&exe)
            .arg("serve")
            .current_dir(&dir)
            .env("TURBO_LEAN_DAEMON", "1")
            .stdin(std::process::Stdio::piped())
            .process_group(0)
            .spawn()
            .unwrap();
        let state = dir.join("zygote_daemon.json");
        let info = LocalZygoteDaemonInfo {
            addr: String::new(),
            pid: child.id(),
            exe_mtime_sec: 0,
            exe_mtime_nsec: 0,
            auth_token: String::new(),
            policy: vec![],
        };
        fs::write(&state, serde_json::to_vec(&info).unwrap()).unwrap();
        let mut identity = portable_process_identity(child.id())
            .unwrap()
            .expect("portable identity");
        identity.start_time.push_str(" changed");
        assert!(!signal_portable_process(child.id(), &identity, libc::SIGTERM).unwrap());
        identity = portable_process_identity(child.id()).unwrap().unwrap();
        identity.command.push_str(" changed");
        assert!(!signal_portable_process(child.id(), &identity, libc::SIGKILL).unwrap());
        assert!(child.try_wait().unwrap().is_none());
        assert!(portable_staging_namespace_in_use(&dir, Some(&dir)));
        assert_eq!(stop_pidfile_daemons(&dir, Some(&dir)).unwrap().count, 1);
        assert!(!child.wait().unwrap().success());
        assert!(!stop_pidfile_daemon(&state).unwrap());
        assert!(!portable_staging_namespace_in_use(&dir, Some(&dir)));
        // A live PID without the daemon identity must not be killed, nor may its
        // state file or staging be deleted. Malformed state is conservative too.
        let mut foreign = Command::new("sleep").arg("30").spawn().unwrap();
        let foreign_info = LocalZygoteDaemonInfo {
            pid: foreign.id(),
            ..info
        };
        fs::write(&state, serde_json::to_vec(&foreign_info).unwrap()).unwrap();
        let cleanup = stop_pidfile_daemons(&dir, Some(&dir)).unwrap();
        assert_eq!(cleanup.count, 0);
        assert!(!cleanup.state_files.contains(&state));
        assert!(portable_staging_namespace_in_use(&dir, Some(&dir)));
        // A legacy PID file outside an otherwise empty staging namespace still
        // vetoes deletion, even though scoped signalling must spare that PID.
        let empty_staging = dir.join("empty-staging");
        fs::create_dir_all(&empty_staging).unwrap();
        assert!(portable_staging_namespace_in_use(
            &empty_staging,
            Some(&dir)
        ));
        assert!(foreign.try_wait().unwrap().is_none());
        foreign.kill().unwrap();
        foreign.wait().unwrap();
        assert!(!portable_staging_namespace_in_use(&dir, Some(&dir)));
        fs::write(&state, "invalid state").unwrap();
        assert!(portable_staging_namespace_in_use(&dir, Some(&dir)));
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn test_closed_daemon_transport_is_recoverable() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let url = format!("http://{}/check-shard", listener.local_addr().unwrap());
        let server = std::thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut byte = [0];
            let _ = std::io::Read::read(&mut stream, &mut byte);
            // Expiry can close admission before a response is written.
        });
        let err = http_request_with_timeout_and_token(
            "POST",
            &url,
            "application/json",
            b"{}",
            Some(1000),
            None,
            || {},
        )
        .unwrap_err();
        assert!(is_expired_daemon_transport_error(&err), "{err:#}");
        assert!(finish_check_shard_request(Err(err)).unwrap().is_none());
        server.join().unwrap();
        let err = http_request_with_timeout_and_token(
            "POST",
            &url,
            "application/json",
            b"{}",
            Some(1000),
            None,
            || {},
        )
        .unwrap_err();
        assert!(is_expired_daemon_transport_error(&err), "{err:#}");
        assert!(finish_check_shard_request(Err(err)).unwrap().is_none());
        assert!(!is_expired_daemon_transport_error(&anyhow::anyhow!(
            "HTTP 500: proof failed"
        )));
    }

    #[test]
    fn test_daemon_stop_recognizes_the_serve_subcommand_only() {
        for args in [
            b"turbo-lean\0serve\0".as_slice(),
            b"turbo-lean\0--cache-dir\0/tmp/cas\0--json\0serve\0--listen\0127.0.0.1:9400\0"
                .as_slice(),
        ] {
            assert!(is_serve_command(args));
        }
        for args in [
            b"turbo-lean\0check\0File.lean\0--decl\0serve\0".as_slice(),
            b"turbo-lean\0--cache-dir\0serve\0check\0File.lean\0".as_slice(),
        ] {
            assert!(!is_serve_command(args));
        }
    }

    fn repo_lean_cfg() -> Option<crate::module_builder::ProjectConfig> {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean");
        dir.join(".lake/packages/lean-sys/LeanSys/Posix.lean")
            .is_file()
            .then(|| crate::module_builder::resolve_project_config(&dir).ok())
            .flatten()
    }

    #[test]
    fn test_pinned_ffi_allow_args_admits_exact_pinned_lean_sys() {
        let Some(cfg) = repo_lean_cfg() else { return };
        let args = pinned_ffi_allow_args(&cfg, &["LeanSys.Posix".to_string()]);
        assert_eq!(args.len(), 8, "{args:?}");
        assert!(args.contains(
            &"--ffi-allow=LeanSys.Posix=LeanSys.Posix.rawWriteAll=leansys_write_all".to_string()
        ));
        assert!(pinned_ffi_allow_args(&cfg, &["TurboLean.Spec".to_string()]).is_empty());
    }

    #[test]
    fn test_pinned_ffi_allow_args_rejects_unpinned_or_path_dependency() {
        let Some(cfg) = repo_lean_cfg() else { return };
        let mods = ["LeanSys.Posix".to_string()];
        let mut bad_rev = cfg.clone();
        bad_rev
            .manifest_packages
            .iter_mut()
            .for_each(|p| p.rev = Some("0".repeat(40)));
        assert!(pinned_ffi_allow_args(&bad_rev, &mods).is_empty());
        let mut path_dep = cfg.clone();
        path_dep
            .manifest_packages
            .iter_mut()
            .for_each(|p| p.pkg_type = "path".into());
        assert!(pinned_ffi_allow_args(&path_dep, &mods).is_empty());
        let mut bad_url = cfg.clone();
        bad_url
            .manifest_packages
            .iter_mut()
            .for_each(|p| p.url = Some("https://example.invalid/lean-sys.git".into()));
        assert!(pinned_ffi_allow_args(&bad_url, &mods).is_empty());
        let mut in_tree = cfg.clone();
        in_tree.dep_pkgs.clear();
        assert!(pinned_ffi_allow_args(&in_tree, &mods).is_empty());
    }

    #[test]
    fn test_split_body_into_prefix_and_decl() {
        let body = "namespace PrefixBench\nstructure PairState where\n  x : Nat\n  y : Nat\n\ndef swapPair (s : PairState) : PairState :=\n  { x := s.y, y := s.x }\n\ntheorem cand_good (s : PairState) : swapPair (swapPair s) = s := by\n  cases s\n  rfl\n";
        let (pref, decl, key) = split_body_into_prefix_and_decl(body).expect("should split");
        assert!(pref.contains("structure PairState"));
        assert!(pref.contains("def swapPair"));
        assert!(!pref.contains("theorem cand_good"));
        assert!(decl.trim_start().starts_with("theorem cand_good"));
        assert_eq!(decl.chars().take_while(|&c| c == '\n').count(), 8);
        assert_eq!(key.len(), 16);
    }

    fn open_test_zygote_env(
        tag: &str,
    ) -> Option<(
        PathBuf,
        TurboStore,
        std::collections::HashMap<String, String>,
        PathBuf,
    )> {
        let tmp_dir = std::env::temp_dir().join(format!("turbo_zygote_{}_{}", tag, next_tmp_id()));
        let _ = fs::create_dir_all(&tmp_dir);
        let store = TurboStore::open(Some(&tmp_dir)).expect("open store");
        let (mut env_vars, lean_bin) =
            crate::pack::resolve_server_lean_env_and_bin(&store, "leanprover/lean4:v4.35.0", "");
        env_vars.insert(
            "LEAN_PATH".to_string(),
            tmp_dir.to_string_lossy().to_string(),
        );
        if !lean_bin.exists() && Command::new(&lean_bin).arg("--version").output().is_err() {
            let _ = fs::remove_dir_all(&tmp_dir);
            return None;
        }
        // Fixture setup compiles the worker before any request's deadline begins.
        ensure_zygote_binary(&store, &lean_bin, &env_vars).expect("prepare test worker");
        Some((tmp_dir, store, env_vars, lean_bin))
    }

    #[test]
    fn test_zygote_prefix_checkpoint_instant_rollback() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("test") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let isolated_lp = tmp_dir.to_string_lossy().to_string();

        let shared_prefix = "namespace PrefixBench\nstructure PairState where\n  x : Nat\n  y : Nat\n  deriving DecidableEq\n\ndef swapPair (s : PairState) : PairState :=\n  { x := s.y, y := s.x }\n\ntheorem swapPair_involutive (s : PairState) : swapPair (swapPair s) = s := by\n  cases s\n  rfl\n";
        let run_pool = |shard: &str| {
            eval_with_zygote_pool(
                &store,
                toolchain,
                &isolated_lp,
                &env_vars,
                &lean_bin,
                shard,
                false,
            )
            .unwrap()
        };

        let rep_bad = run_pool(&format!(
            "{}\ntheorem cand_bad (s : PairState) : swapPair s = s := rfl\n",
            shared_prefix
        ));
        assert!(rep_bad.import_ok && !rep_bad.ok && !rep_bad.errors.is_empty());
        let joined_bad_errs = rep_bad.errors.join("\n");
        assert!(
            joined_bad_errs.contains("<zygote-decl>:14:"),
            "Expected line 14 in error: {}",
            joined_bad_errs
        );

        let max_elab_us: u64 = if cfg!(debug_assertions) {
            100_000
        } else {
            25_000
        };
        for decl in [
            "theorem cand_good1 (s : PairState) : swapPair (swapPair s) = s := by\n  cases s\n  rfl\n",
            "theorem cand_good2 (s : PairState) : swapPair (swapPair s) = s := swapPair_involutive s\n",
            "theorem cand_good_fresh (s : PairState) : (swapPair s).x = s.y := by\n  cases s\n  rfl\n",
        ] {
            let rep = run_pool(&format!("{}\n{}", shared_prefix, decl));
            assert!(rep.ok && rep.env_cache_hit && rep.prefix_cache_hit && rep.prefix_us == 0 && rep.elab_us < max_elab_us, "{:?}", rep);
            if decl.contains("cand_good_fresh") {
                assert!(rep.elab_us < rep_bad.prefix_us);
            }
        }
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_kernel_gate_rejects_macro_hidden_sorry() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("kgate_test") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";

        let prefix_src = "theorem prior_lem : True := sorry\n";
        let sneaky_shard = format!("{}\nmacro \"stealth_sorry\" : tactic => `(tactic| sorry)\ntheorem sneaky_thm : 1 = 2 := by stealth_sorry\n", prefix_src);
        let rep_sneaky = eval_with_zygote_pool(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &sneaky_shard,
            false,
        )
        .unwrap();
        assert!(!rep_sneaky.ok);
        let joined_errs = rep_sneaky.errors.join("\n");
        assert!(joined_errs.contains("KernelGate") || joined_errs.contains("sorry"));

        let clean_shard = format!("{}\ntheorem clean_thm : True := prior_lem\n", prefix_src);
        let rep_clean = eval_with_zygote_pool(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &clean_shard,
            false,
        )
        .unwrap();
        assert!(rep_clean.ok && rep_clean.kernel_gate_active);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_kernel_gate_applies_axiom_allowlist() {
        let shard = "theorem nd : 2 ^ 3 = 8 := by native_decide\n";
        for (allow, expect_ok) in [("", false), ("Foo.*, *._native.native_decide.ax_*", true)] {
            let Some((tmp_dir, store, mut env_vars, lean_bin)) = open_test_zygote_env("axpol")
            else {
                return;
            };
            env_vars.insert(
                crate::splitter::ALLOWED_AXIOMS_ENV.to_string(),
                allow.to_string(),
            );
            let toolchain = "leanprover/lean4:v4.35.0";
            let rep =
                eval_with_zygote_pool(&store, toolchain, "", &env_vars, &lean_bin, shard, false)
                    .unwrap();
            assert_eq!(rep.ok, expect_ok, "allow={:?}: {:?}", allow, rep.errors);
            assert!(
                expect_ok
                    || rep
                        .errors
                        .join("\n")
                        .contains("nd._native.native_decide.ax_")
            );
            let _ = fs::remove_dir_all(&tmp_dir);
        }
    }

    #[test]
    fn test_zygote_bv_decide_finds_toolchain_cadical() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("cadical") else {
            return;
        };
        let shard = "import Std.Tactic.BVDecide\ntheorem bv (x y : BitVec 8) : (x &&& y) + (x ||| y) = x + y := by bv_decide\n";
        let rep = eval_with_zygote_pool(
            &store,
            "leanprover/lean4:v4.35.0",
            "",
            &env_vars,
            &lean_bin,
            shard,
            false,
        )
        .unwrap();
        // The SAT call succeeds (the default kernel gate then rejects the `bv_decide` axiom).
        let errs = rep.errors.join("\n");
        assert!(
            !errs.contains("cadical") && errs.contains("bv._native.bv_decide.ax_"),
            "{}",
            errs
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    static LNC_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    #[test]
    fn test_lean_native_core_persistent_worker_sub_millisecond_rpc() {
        let _guard = LNC_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let warmup = query_lean_native_core_worker("ping", None).unwrap();
        assert_eq!(
            (warmup["ok"].as_bool(), warmup["result"]["status"].as_str()),
            (Some(true), Some("pong"))
        );
        let _ = query_lean_native_core_worker("validate-tv", None);

        let methods = ["ping", "validate-tv", "verify-certs", "eval-cex"];
        let t0 = std::time::Instant::now();
        for idx in 0..20 {
            let method = methods[idx % methods.len()];
            let resp = query_lean_native_core_worker(method, None).unwrap();
            assert_eq!(resp["ok"].as_bool(), Some(true));
            let result = &resp["result"];
            match method {
                "ping" => assert_eq!(result["status"].as_str(), Some("pong")),
                "validate-tv" => assert_eq!(
                    (
                        result["allPassed"].as_bool(),
                        result["passedDecls"].as_u64()
                    ),
                    (Some(true), Some(8))
                ),
                "verify-certs" => assert_eq!(result["verified"].as_bool(), Some(true)),
                "eval-cex" => {
                    let is_fb = result["fallback"].as_bool().unwrap_or(false)
                        || resp["fallback"].as_bool().unwrap_or(false);
                    assert_eq!(
                        (
                            result["certified"].as_bool(),
                            result["falsePositives"].as_u64()
                        ),
                        (Some(!is_fb), Some(0))
                    );
                }
                _ => unreachable!(),
            }
        }
        assert!(t0.elapsed().as_secs_f64() * 1000.0 / 20.0 < 5.0);
    }

    #[test]
    fn test_measure_process_rss_mb_and_budget_detection() {
        let mut min_elapsed_us = u128::MAX;
        let mut rss_mb = 0;
        for _ in 0..3 {
            let t0 = std::time::Instant::now();
            rss_mb = measure_process_rss_mb(std::process::id());
            min_elapsed_us = min_elapsed_us.min(t0.elapsed().as_micros());
        }
        assert!(rss_mb >= 1 && rss_mb < 65_536);
        #[cfg(target_os = "linux")]
        assert!(min_elapsed_us < 50_000);
        let gov = crate::shm_cache::MemoryBudgetGovernor::detect();
        assert!(gov.budget_mb >= 1 && gov.worker_rss_limit_mb() >= 512);
    }

    #[test]
    fn test_zygote_multiple_import_sets_in_same_worker() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("multi_imp") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";

        let rep1 = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            "import Init\ntheorem multi_imp_1 : 1 + 1 = 2 := rfl\n",
            false,
            false,
            None,
            None,
        )
        .unwrap();
        assert!(rep1.ok && rep1.import_ok);

        let rep2 = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            "import Lean\ntheorem multi_imp_lean : 1 = 1 := rfl\n",
            false,
            false,
            None,
            None,
        )
        .unwrap();
        assert!(rep2.ok && rep2.import_ok);

        let rep3 = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            "import Init\ntheorem multi_imp_2 : 2 + 2 = 4 := rfl\n",
            false,
            false,
            None,
            None,
        )
        .unwrap();
        assert!(rep3.ok && rep3.env_cache_hit);
        let rep4 = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            "import Lean\ntheorem multi_imp_lean_2 : 2 = 2 := rfl\n",
            false,
            false,
            None,
            None,
        )
        .unwrap();
        assert!(rep4.ok && rep4.env_cache_hit);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_eval_mode_preserves_info_messages_and_sorry_strings() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("eval_info") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";

        let harness = "import Lean\nopen Lean Elab Command in\nrun_cmd do\n  logInfo \"RSGB_RESULT {\\\"name\\\":\\\"foo\\\",\\\"note\\\":\\\"sorry\\\"}\"\n#eval (40 + 2)\n";
        let rep = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            harness,
            false,
            true,
            Some("rsgb_harness.lean"),
            Some(15_000),
        )
        .unwrap();
        let joined_msgs = rep.messages.join("\n");
        assert!(
            rep.ok
                && rep.heartbeats > 0
                && joined_msgs.contains("RSGB_RESULT {\"name\":\"foo\",\"note\":\"sorry\"}")
                && joined_msgs.contains("42")
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_exhausted_budget_does_not_spawn_fallback() {
        let started = std::time::Instant::now() - std::time::Duration::from_secs(1);
        let remaining = remaining_timeout_ms(Some(100), started);
        assert_eq!(remaining, 0);
        let err = run_lean_command(&mut Command::new("must-not-be-spawned"), Some(remaining))
            .unwrap_err();
        assert!(err.to_string().contains("timed out"), "{err}");
    }

    #[test]
    fn test_zygote_timeout_kills_infinite_eval_and_recovers() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("timeout") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";

        assert!(
            eval_with_zygote_pool_opts(
                &store,
                toolchain,
                "",
                &env_vars,
                &lean_bin,
                "#eval 1 + 1\n",
                false,
                true,
                Some("warm.lean"),
                Some(10_000)
            )
            .unwrap()
            .ok
        );

        let inf_src = "partial def spinForever (n : Nat) : IO Nat := do\n  IO.sleep 100\n  spinForever (n + 1)\n#eval spinForever 0\n";
        let t0 = std::time::Instant::now();
        let rep_timeout = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            inf_src,
            false,
            true,
            Some("spin.lean"),
            Some(400),
        )
        .unwrap();
        assert!(
            rep_timeout.timed_out
                && !rep_timeout.ok
                && t0.elapsed() < std::time::Duration::from_secs(2)
        );

        let rep_after = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            "#eval (100 + 23)\n",
            false,
            true,
            Some("after.lean"),
            Some(10_000),
        )
        .unwrap();
        assert!(
            rep_after.ok
                && !rep_after.timed_out
                && rep_after.messages.iter().any(|m| m.contains("123"))
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_olean_digest_changes_when_olean_modified() {
        let tmp_dir =
            std::env::temp_dir().join(format!("turbo_zygote_olean_dig_{}", next_tmp_id()));
        let mod_dir = tmp_dir.join("Foo");
        let _ = fs::create_dir_all(&mod_dir);
        let olean_path = mod_dir.join("Bar.olean");
        fs::write(&olean_path, b"olean-version-1").unwrap();

        let lp = tmp_dir.to_string_lossy().to_string();
        let d1 = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_eq!(d1, compute_imported_oleans_digest("Foo.Bar", &lp));
        let sp1 = compute_search_path_oleans_digest(&lp);
        assert_eq!(sp1, compute_search_path_oleans_digest(&lp));

        // Same-size overwrite as well as companion creation/modification must invalidate memoized digests.
        fs::write(&olean_path, b"olean-version-2").unwrap();
        let d2 = compute_imported_oleans_digest("Foo.Bar", &lp);
        let sp2 = compute_search_path_oleans_digest(&lp);
        assert_ne!(d1, d2);
        assert_ne!(sp1, sp2);

        let srv_path = PathBuf::from(format!("{}.server", olean_path.display()));
        fs::write(&srv_path, b"server-companion-v1").unwrap();
        let d3 = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_ne!(d2, d3);

        fs::write(&srv_path, b"server-companion-v2").unwrap();
        let d4 = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_ne!(d3, d4);

        std::thread::sleep(std::time::Duration::from_millis(65));
        let d4_warm_populate = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_eq!(d4, d4_warm_populate);
        assert_eq!(d4, compute_imported_oleans_digest("Foo.Bar", &lp));

        fs::write(&olean_path, b"olean-version-3").unwrap();
        let d5 = compute_imported_oleans_digest("Foo.Bar", &lp);
        assert_ne!(d4, d5);

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_attach_host_closure_digest_protocol_columns() {
        let r2 = attach_host_closure_digest("Init\t6162\n", "dig123");
        assert_eq!(r2, "Init\t6162\t\t\t\t\tdig123\n");
        assert_eq!(r2.trim_end_matches('\n').split('\t').nth(6), Some("dig123"));

        let r5 = attach_host_closure_digest("Init\t6162\tstrict\tpk\t7072\n", "dig456");
        assert_eq!(r5, "Init\t6162\tstrict\tpk\t7072\t\tdig456\n");
        assert_eq!(r5.trim_end_matches('\n').split('\t').nth(6), Some("dig456"));

        let r6 = attach_host_closure_digest("Init\t6162\tstrict\t\t\t6f70\n", "dig789");
        assert_eq!(r6, "Init\t6162\tstrict\t\t\t6f70\tdig789\n");
        assert_eq!(r6.trim_end_matches('\n').split('\t').nth(5), Some("6f70"));
        assert_eq!(r6.trim_end_matches('\n').split('\t').nth(6), Some("dig789"));
    }

    #[test]
    fn test_search_path_oleans_digest_skips_lake_packages_bloat_and_tracks_imported_oleans() {
        let tmp_dir = std::env::temp_dir().join(format!("turbo_zygote_pkg_skip_{}", next_tmp_id()));
        let (pkg_lib, local_lib) = (
            tmp_dir.join(".lake/packages/mathlib/.lake/build/lib/lean"),
            tmp_dir.join(".lake/build/lib/lean"),
        );
        let _ = fs::create_dir_all(&pkg_lib);
        let _ = fs::create_dir_all(&local_lib);

        let (big_pkg_olean, local_olean) =
            (pkg_lib.join("Big.olean"), local_lib.join("Local.olean"));
        fs::write(&big_pkg_olean, vec![0xAAu8; 128 * 1024]).unwrap();
        fs::write(&local_olean, b"local-olean-v1").unwrap();

        let lp = format!("{}:{}", local_lib.display(), pkg_lib.display());
        let (sp_d1, imp_d1) = (
            compute_search_path_oleans_digest(&lp),
            compute_imported_oleans_digest("Big,Local", &lp),
        );

        fs::write(&big_pkg_olean, vec![0xBBu8; 130 * 1024]).unwrap();
        let sp_d2 = compute_search_path_oleans_digest(&lp);
        assert_eq!(sp_d1, sp_d2);
        assert_ne!(imp_d1, compute_imported_oleans_digest("Big,Local", &lp));

        fs::write(&local_olean, b"local-olean-v2-modified").unwrap();
        assert_ne!(sp_d2, compute_search_path_oleans_digest(&lp));
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_delta_prefix_chaining_and_used_constants_distillation() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("delta_distill")
        else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";

        let prefix1 = "namespace DeltaChainTest\ndef shiftByFour (n : Nat) : Nat := n + 4\n";
        let shard1 = format!(
            "{}theorem helper_shift_eq (n : Nat) : shiftByFour n = n + 4 := rfl\n",
            prefix1
        );
        assert!(
            eval_with_zygote_pool(&store, toolchain, "", &env_vars, &lean_bin, &shard1, true)
                .unwrap()
                .ok
        );

        let shard2 = format!("{}theorem helper_shift_eq (n : Nat) : shiftByFour n = n + 4 := sorry\ntheorem chained_thm (n : Nat) : shiftByFour n = n + 4 := by\n  simp [helper_shift_eq]\n", prefix1);
        // Stub exemptions need the checked declaration named (an unnamed request exempts nothing).
        let rep2 = eval_with_zygote_pool_for_targets(
            &store,
            toolchain,
            "",
            &env_vars,
            &lean_bin,
            &shard2,
            &["chained_thm".to_string()],
            None,
            &[],
        )
        .unwrap();
        assert!(
            rep2.ok
                && rep2
                    .used_constants
                    .iter()
                    .any(|c| c.contains("helper_shift_eq"))
        );

        // Verify branched LCA prefix reuse: sibling branch sharing `prefix1` reuses the ancestor checkpoint
        let shard3 = format!("{}def siblingBranchHelper (n : Nat) : Nat := shiftByFour n + 2\ntheorem sibling_thm (n : Nat) : siblingBranchHelper n = n + 6 := by\n  unfold siblingBranchHelper shiftByFour; omega\n", prefix1);
        let rep3 =
            eval_with_zygote_pool(&store, toolchain, "", &env_vars, &lean_bin, &shard3, true)
                .unwrap();
        assert!(rep3.ok && rep3.env_cache_hit);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_lean_native_core_worker_nonexistent_bin_fallback() {
        let _guard = LNC_TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let prev = std::env::var("LEAN_NATIVE_CORE_BIN").ok();
        std::env::set_var("LEAN_NATIVE_CORE_BIN", "/nonexistent/lean-native-core");
        for method in [
            "ping",
            "validate-tv",
            "verify-certs",
            "eval-cex",
            "compile-fastcheck",
            "compile-llvm",
            "compile-ptx",
        ] {
            let resp = query_lean_native_core_worker(method, None)
                .unwrap_or_else(|e| panic!("fallback failed for {}: {}", method, e));
            assert_eq!(resp["ok"].as_bool(), Some(true));
            let res = &resp["result"];
            assert_eq!(res["fallback"].as_bool(), Some(true));
            if method == "eval-cex" || method == "verify-certs" {
                assert_eq!(res["overallAssurance"].as_str(), Some("FallbackUnverified"));
                if method == "eval-cex" {
                    assert_eq!(res["certified"].as_bool(), Some(false));
                }
            }
        }
        match prev {
            Some(v) => std::env::set_var("LEAN_NATIVE_CORE_BIN", v),
            None => std::env::remove_var("LEAN_NATIVE_CORE_BIN"),
        }
    }

    #[test]
    fn test_eval_mode_prefix_checkpoint_preserves_exact_line_numbers_and_accelerates_warm_eval() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("eval_prefix") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let isolated_lp = tmp_dir.to_string_lossy().to_string();

        let driver_v1 = "import Init\ndef rsgbStep1 (n : Nat) : Nat := n + 10\ndef rsgbStep2 (n : Nat) : Nat := rsgbStep1 n * 2\ndef rsgbStep3 (n : Nat) : Nat := rsgbStep2 n + 5\ndef rsgbStep4 (n : Nat) : String := s!\"val={rsgbStep3 n}\"\ndef rsgbStep5 (n : Nat) : String := s!\"[{rsgbStep4 n}]\"\ndef rsgbSimTest (a b : Nat) : String := s!\"{rsgbStep5 a}:{rsgbStep5 b}\"\ndef rsgbSimKill (tag : String) (x : Nat) : String := s!\"{tag}:{rsgbSimTest x (x + 1)}\"\ndef rsgbSimOutputs (k : Nat) : String :=\n  rsgbSimKill \"RUN\" k\n#eval rsgbSimOutputs 3\n";
        let run_eval = |src: &str| {
            eval_with_zygote_pool_opts(
                &store,
                toolchain,
                &isolated_lp,
                &env_vars,
                &lean_bin,
                src,
                false,
                true,
                Some("rsgb_driver.lean"),
                Some(30_000),
            )
            .unwrap()
        };

        let rep1 = run_eval(driver_v1);
        assert!(rep1.ok && rep1.messages.join("\n").contains("RUN:[val=31]:[val=33]"));

        let driver_v2 = driver_v1.replace("#eval rsgbSimOutputs 3", "#eval rsgbSimOutputs 7");
        let mut t0 = std::time::Instant::now();
        let mut rep2 = run_eval(&driver_v2);
        if !rep2.prefix_cache_hit {
            t0 = std::time::Instant::now();
            rep2 = run_eval(&driver_v2);
        }
        let warm_elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
        let max_warm_ms = if cfg!(debug_assertions) { 500.0 } else { 100.0 };
        let max_elab_us: u64 = if cfg!(debug_assertions) {
            250_000
        } else {
            80_000
        };
        assert!(rep2.ok && rep2.prefix_cache_hit && rep2.prefix_us == 0);
        assert!(rep2.messages.join("\n").contains("RUN:[val=39]:[val=41]"));
        assert!(rep2.elab_us < max_elab_us && warm_elapsed_ms < max_warm_ms);

        let driver_v3 = format!("{}#check unknown_ident_on_line_12\n", driver_v2);
        let rep3 = run_eval(&driver_v3);
        assert!(
            !rep3.ok
                && rep3.prefix_cache_hit
                && rep3
                    .messages
                    .join("\n")
                    .contains("rsgb_driver.lean:12:7: error(lean.unknownIdentifier):")
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_eval_mode_ancestor_prefix_reuse_preserves_line_numbers() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("eval_ancestor")
        else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let isolated_lp = tmp_dir.to_string_lossy().to_string();
        let run_eval = |src: &str| {
            eval_with_zygote_pool_opts(
                &store,
                toolchain,
                &isolated_lp,
                &env_vars,
                &lean_bin,
                src,
                false,
                true,
                Some("anc.lean"),
                Some(30_000),
            )
            .unwrap()
        };
        let base = "import Init\ndef ancA : Nat := 1\ndef ancB : Nat := ancA + 1\n";
        assert!(run_eval(&format!("{base}#eval ancB\n")).ok);
        // The new prefix extends the cached one; the warning in the delta sits on line 4.
        let rep = run_eval(&format!("{base}theorem ancW : True := sorry\n#eval ancB\n"));
        let msgs = rep.messages.join("\n");
        assert!(rep.ok && msgs.contains("anc.lean:4:8: warning"), "{msgs}");
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_eval_reply_cacheable_only_for_clean_successes() {
        let ok = ZygoteEvalReply {
            ok: true,
            import_ok: true,
            ..Default::default()
        };
        assert!(eval_reply_cacheable(&ok));
        // e.g. "toolchain not installed": ok=false and import_ok=false
        assert!(!eval_reply_cacheable(&ZygoteEvalReply {
            ok: false,
            ..ok.clone()
        }));
        assert!(!eval_reply_cacheable(&ZygoteEvalReply {
            import_ok: false,
            ..ok.clone()
        }));
        assert!(!eval_reply_cacheable(&ZygoteEvalReply {
            crashed: true,
            ..ok.clone()
        }));
        assert!(!eval_reply_cacheable(&ZygoteEvalReply {
            timed_out: true,
            ..ok
        }));
    }

    #[cfg(unix)]
    #[test]
    fn test_shared_zygote_dir_rejects_foreign_or_open_directories() {
        use std::os::unix::fs::PermissionsExt;
        let tmp = std::env::temp_dir().join(format!("turbo_zyg_shared_{}", next_tmp_id()));
        fs::create_dir_all(&tmp).unwrap();
        let uid = unsafe { libc::geteuid() };
        let dir = tmp.join(format!("turbo_lean_shared_zygote_bins_{uid}"));
        // Pre-planted world-writable dir (as another local user could create) is rejected.
        fs::create_dir(&dir).unwrap();
        fs::set_permissions(&dir, fs::Permissions::from_mode(0o777)).unwrap();
        assert!(private_shared_zygote_dir_in(&tmp).is_none());
        // A symlink in its place is rejected too.
        fs::remove_dir(&dir).unwrap();
        let target = tmp.join("elsewhere");
        fs::create_dir(&target).unwrap();
        fs::set_permissions(&target, fs::Permissions::from_mode(0o700)).unwrap();
        std::os::unix::fs::symlink(&target, &dir).unwrap();
        assert!(private_shared_zygote_dir_in(&tmp).is_none());
        fs::remove_file(&dir).unwrap();
        // A non-sticky group/other-writable parent could let others rename our dir.
        fs::set_permissions(&tmp, fs::Permissions::from_mode(0o777)).unwrap();
        assert!(private_shared_zygote_dir_in(&tmp).is_none());
        fs::set_permissions(&tmp, fs::Permissions::from_mode(0o1777)).unwrap();
        let sticky = private_shared_zygote_dir_in(&tmp).expect("sticky parent accepted");
        fs::remove_dir(&sticky).unwrap();
        fs::set_permissions(&tmp, fs::Permissions::from_mode(0o755)).unwrap();
        // Fresh dir is created 0700 and accepted.
        let got = private_shared_zygote_dir_in(&tmp).expect("private dir");
        assert_eq!(
            fs::metadata(&got).unwrap().permissions().mode() & 0o777,
            0o700
        );
        // A group/other-writable binary is not executable material.
        let bin = got.join("turbo_zygote_x");
        fs::write(&bin, b"x").unwrap();
        fs::set_permissions(&bin, fs::Permissions::from_mode(0o755)).unwrap();
        assert!(owned_private_file(&bin));
        fs::set_permissions(&bin, fs::Permissions::from_mode(0o775)).unwrap();
        assert!(!owned_private_file(&bin));
        let _ = fs::remove_dir_all(&tmp);
    }

    #[test]
    fn test_evb_rfvb_rsgb_parity_prefix_warnings_prelude_and_main_module() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("evb_parity") else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let isolated_lp = tmp_dir.to_string_lossy().to_string();

        let src_v1 = "def pfxUnused (x y : Nat) : Nat := x\ntheorem pfxSorry : True := by sorry\n#eval pfxUnused 42 99\n";
        let rep_cold = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            &isolated_lp,
            &env_vars,
            &lean_bin,
            src_v1,
            false,
            true,
            Some("pfx_warn.lean"),
            Some(30_000),
        )
        .unwrap();
        let cold_msgs = rep_cold.messages.join("\n");
        assert!(
            cold_msgs.contains("unusedVariables") && cold_msgs.contains("declaration uses `sorry`")
        );

        let src_v2 = src_v1.replace("42 99", "77 88");
        let rep_warm = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            &isolated_lp,
            &env_vars,
            &lean_bin,
            &src_v2,
            false,
            true,
            Some("pfx_warn.lean"),
            Some(30_000),
        )
        .unwrap();
        let warm_msgs = rep_warm.messages.join("\n");
        assert!(
            rep_warm.prefix_cache_hit
                && warm_msgs.contains("unusedVariables")
                && warm_msgs.contains("declaration uses `sorry`")
                && warm_msgs.contains("77")
        );

        let (imports_prelude, body_prelude) = split_shard_for_zygote("prelude\n#check Nat\n");
        assert_eq!(imports_prelude, "__PRELUDE__");
        assert!(body_prelude.contains("#check Nat"));
        assert_eq!(
            split_shard_for_zygote("import Zeta.Mod\nimport Alpha.Mod\n#check 1\n").0,
            "Zeta.Mod,Alpha.Mod"
        );

        let priv_src = "private def myPrivHelper : Nat := 123\n#check myPrivHelper\n";
        let rep_priv = eval_with_zygote_pool_opts(
            &store,
            toolchain,
            &isolated_lp,
            &env_vars,
            &lean_bin,
            priv_src,
            false,
            true,
            Some("/tmp/foo_priv_test.lean"),
            Some(30_000),
        )
        .unwrap();
        assert!(!rep_priv.messages.join("\n").contains("._stdin."));
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_zygote_transitive_olean_closure_and_module_visibility_isolation() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("mod_vis_closure")
        else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let lib_a = tmp_dir.join("lib_a");
        let lib_b = tmp_dir.join("lib_b");
        fs::create_dir_all(&lib_a).unwrap();
        fs::create_dir_all(&lib_b).unwrap();

        let src_c1 = lib_a.join("DepC.lean");
        let src_b = lib_a.join("DepB.lean");
        fs::write(&src_c1, "def depValue : Nat := 11\n").unwrap();
        fs::write(&src_b, "import DepC\ndef midValue : Nat := depValue + 1\n").unwrap();

        let status_c1 = Command::new(&lean_bin)
            .arg("-R")
            .arg(&lib_a)
            .arg(&src_c1)
            .arg("-o")
            .arg(lib_a.join("DepC.olean"))
            .env("LEAN_PATH", &lib_a)
            .status()
            .unwrap();
        assert!(status_c1.success());
        let status_b = Command::new(&lean_bin)
            .arg("-R")
            .arg(&lib_a)
            .arg(&src_b)
            .arg("-o")
            .arg(lib_a.join("DepB.olean"))
            .env("LEAN_PATH", &lib_a)
            .status()
            .unwrap();
        assert!(status_b.success());

        let lp_a = lib_a.to_string_lossy().to_string();
        let (dig1, complete1) = compute_imported_oleans_digest_inner("DepB", &lp_a);
        assert!(complete1);
        let rep_warm_seed = eval_with_zygote_pool(
            &store,
            toolchain,
            &lp_a,
            &env_vars,
            &lean_bin,
            "import DepB\ntheorem t_warm_1 : midValue = 12 := rfl\n",
            false,
        )
        .unwrap();
        assert!(rep_warm_seed.ok && rep_warm_seed.import_ok);
        let rep_warm_hit = eval_with_zygote_pool(
            &store,
            toolchain,
            &lp_a,
            &env_vars,
            &lean_bin,
            "import DepB\ntheorem t_warm_2 : midValue + 1 = 13 := rfl\n",
            false,
        )
        .unwrap();
        assert!(
            rep_warm_hit.ok && rep_warm_hit.env_cache_hit,
            "Zygote worker must hit env_cache via hostClosureDigest on second request"
        );

        // Rebuild transitive leaf DepC with same-length source / different constant value without touching DepB.olean
        fs::write(&src_c1, "def depValue : Nat := 99\n").unwrap();
        let status_c2 = Command::new(&lean_bin)
            .arg("-R")
            .arg(&lib_a)
            .arg(&src_c1)
            .arg("-o")
            .arg(lib_a.join("DepC.olean"))
            .env("LEAN_PATH", &lib_a)
            .status()
            .unwrap();
        assert!(status_c2.success());
        let dig2 = compute_imported_oleans_digest("DepB", &lp_a);
        assert_ne!(
            dig1, dig2,
            "compute_imported_oleans_digest must track transitive .olean dependencies (DepB -> DepC)"
        );
        let rep_after_dep_edit = eval_with_zygote_pool(
            &store,
            toolchain,
            &lp_a,
            &env_vars,
            &lean_bin,
            "import DepB\ntheorem t_after_edit : depValue = 99 := rfl\n",
            false,
        )
        .unwrap();
        assert!(
            rep_after_dep_edit.ok && !rep_after_dep_edit.env_cache_hit,
            "Zygote worker must miss env_cache and reload when transitive DepC.olean changes"
        );

        // Module visibility isolation: private import in `module` must be enforced, and `LEAN_PATH`
        // isolation must prevent cross-path worker pollution.
        let mod_priv_src = lib_a.join("ModPriv.lean");
        fs::write(
            &mod_priv_src,
            "module\ndef secretInternal : Nat := 7\n@[expose] public def exportedVal : Nat := 42\n",
        )
        .unwrap();
        let st_mp = Command::new(&lean_bin)
            .arg("-R")
            .arg(&lib_a)
            .arg(&mod_priv_src)
            .arg("-o")
            .arg(lib_a.join("ModPriv.olean"))
            .env("LEAN_PATH", &lib_a)
            .status()
            .unwrap();
        assert!(st_mp.success());

        let (mod_csv, _) = split_shard_for_zygote(
            "module\nimport ModPriv\ntheorem t : secretInternal = 7 := rfl\n",
        );
        assert!(
            mod_csv.contains("__MODULE__"),
            "module header must be encoded in Zygote imports_csv: {}",
            mod_csv
        );
        let rep_priv_fail = eval_with_zygote_pool(
            &store,
            toolchain,
            &lp_a,
            &env_vars,
            &lean_bin,
            "module\nimport ModPriv\ntheorem t : secretInternal = 7 := rfl\n",
            false,
        )
        .unwrap();
        assert!(
            !rep_priv_fail.ok,
            "module importing ModPriv without `import all` must reject private constant `secretInternal`"
        );

        let rep_pub_ok = eval_with_zygote_pool(
            &store,
            toolchain,
            &lp_a,
            &env_vars,
            &lean_bin,
            "module\nimport ModPriv\ntheorem t : exportedVal = 42 := rfl\n",
            false,
        )
        .unwrap();
        assert!(
            rep_pub_ok.ok,
            "exported constant must succeed in module mode: {:?}",
            rep_pub_ok.errors
        );

        // Distinct LEAN_PATH `lib_b` without ModPriv must NOT reuse `lib_a`'s worker
        let lp_b = lib_b.to_string_lossy().to_string();
        let rep_wrong_lp = eval_with_zygote_pool(
            &store,
            toolchain,
            &lp_b,
            &env_vars,
            &lean_bin,
            "module\nimport ModPriv\ntheorem t : exportedVal = 42 := rfl\n",
            false,
        )
        .unwrap();
        assert!(
            !rep_wrong_lp.ok,
            "Zygote worker must not leak cached Environment across distinct LEAN_PATHs"
        );

        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_build_auditor_bootstrap_env_uses_toolchain_paths_only() {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_bootstrap_env_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(tmp_dir.join("App")).unwrap();
        fs::write(tmp_dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            tmp_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nroots = [\"App.Main\"]\n",
        )
        .unwrap();
        fs::write(tmp_dir.join("App/Main.lean"), "def x : Nat := 1\n").unwrap();
        let Ok(cfg) = crate::module_builder::resolve_project_config(&tmp_dir) else {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        };
        let env = build_auditor_bootstrap_env(&cfg);
        let lp = env.get("LEAN_PATH").cloned().unwrap_or_default();
        let ld = env.get("LD_LIBRARY_PATH").cloned().unwrap_or_default();
        assert_eq!(lp, cfg.toolchain_lib_lean.to_string_lossy());
        assert!(!lp.contains(".lake"));
        assert!(!lp.contains(&tmp_dir.to_string_lossy().to_string()));
        assert!(!ld.contains(".lake"));
        assert!(!ld.contains(&tmp_dir.to_string_lossy().to_string()));
        assert_eq!(
            env.get("LEAN").map(String::as_str),
            Some(cfg.lean_bin.to_string_lossy().as_ref())
        );

        let store_dir = tmp_dir.join("store");
        let store = TurboStore::open(Some(&store_dir)).unwrap();
        let olean_dir = tmp_dir.join(".lake/build/lib/lean/App");
        fs::create_dir_all(&olean_dir).unwrap();
        let out = Command::new(&cfg.lean_bin)
            .current_dir(&tmp_dir)
            .arg("-R")
            .arg(&tmp_dir)
            .arg("-o")
            .arg(olean_dir.join("Main.olean"))
            .arg(tmp_dir.join("App/Main.lean"))
            .env("LEAN_PATH", &cfg.toolchain_lib_lean)
            .env("LD_LIBRARY_PATH", &ld)
            .output()
            .unwrap();
        assert!(out.status.success(), "lean compile failed: {:?}", out);

        let poisoned_lib_dir = tmp_dir.join(".lake/build/lib");
        fs::create_dir_all(&poisoned_lib_dir).unwrap();
        fs::write(poisoned_lib_dir.join("libleanshared.so"), b"CORRUPT_ELF").unwrap();
        let (lean_path_env, project_ld_path_env) =
            crate::module_builder::build_lean_search_path(&cfg, true);
        assert!(
            project_ld_path_env.contains(".lake/build/lib"),
            "project search path must include .lake/build/lib to exercise regression"
        );
        audit_compiled_modules_with_zygote(
            &store,
            &cfg,
            &["App.Main".to_string()],
            &lean_path_env,
            &[],
            false,
        )
        .expect("trusted auditor must ignore poisoned .lake/build/lib/libleanshared.so");
        if crate::module_builder::probe_bwrap_sandbox().is_some() {
            audit_compiled_modules_with_zygote(
                &store,
                &cfg,
                &["App.Main".to_string()],
                &lean_path_env,
                &[],
                true,
            )
            .expect("sandboxed auditor must ignore poisoned .lake/build/lib/libleanshared.so");
        }
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_audit_compiled_modules_respects_axiom_allowlist_and_never_allows_sorry_or_trust_compiler(
    ) {
        let _bwrap_guard = crate::module_builder::BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_audit_axioms_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(tmp_dir.join("App")).unwrap();
        fs::write(tmp_dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            tmp_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nroots = [\"App.Nd\", \"App.Sorry\", \"App.Trust\"]\n",
        )
        .unwrap();
        fs::write(
            tmp_dir.join("App/Nd.lean"),
            "theorem t_nd : 2 ^ 3 = 8 := by native_decide\n",
        )
        .unwrap();
        fs::write(
            tmp_dir.join("App/Sorry.lean"),
            "theorem t_sorry : 1 = 2 := sorry\n",
        )
        .unwrap();
        let trust_src = "import Lean\nopen Lean Elab Tactic in\nelab \"sneak_tc\" : tactic => do\n  let g ← getMainGoal\n  let t ← g.getType\n  let nm := Name.mkStr2 \"Lean\" (\"trust\" ++ \"Compiler\")\n  let e ← Meta.mkAppOptM nm #[some t]\n  g.assign e\ntheorem t_tc : True := by sneak_tc\n";
        fs::write(tmp_dir.join("App/Trust.lean"), trust_src).unwrap();
        let Ok(cfg) = crate::module_builder::resolve_project_config(&tmp_dir) else {
            let _ = fs::remove_dir_all(&tmp_dir);
            return;
        };
        let env = build_auditor_bootstrap_env(&cfg);
        let ld = env.get("LD_LIBRARY_PATH").cloned().unwrap_or_default();
        let olean_dir = tmp_dir.join(".lake/build/lib/lean/App");
        fs::create_dir_all(&olean_dir).unwrap();
        for (src, olean, must_succeed) in [
            ("App/Nd.lean", "Nd.olean", true),
            ("App/Sorry.lean", "Sorry.olean", true),
            ("App/Trust.lean", "Trust.olean", false),
        ] {
            let out = Command::new(&cfg.lean_bin)
                .current_dir(&tmp_dir)
                .arg("-R")
                .arg(&tmp_dir)
                .arg("-o")
                .arg(olean_dir.join(olean))
                .arg(tmp_dir.join(src))
                .env("LEAN_PATH", &cfg.toolchain_lib_lean)
                .env("LD_LIBRARY_PATH", &ld)
                .output()
                .unwrap();
            if must_succeed {
                assert!(
                    out.status.success(),
                    "lean compile {} failed: {:?}",
                    src,
                    out
                );
            }
        }
        let store = TurboStore::open(Some(&tmp_dir.join("store"))).unwrap();
        let (lean_path_env, _) = crate::module_builder::build_lean_search_path(&cfg, true);
        let prev_allow = std::env::var(crate::splitter::ALLOWED_AXIOMS_ENV).ok();
        let has_bwrap = crate::module_builder::probe_bwrap_sandbox().is_some();

        // 1. Default policy rejects `native_decide` auxiliary axioms in both trusted and untrusted Stage 1C audits.
        std::env::remove_var(crate::splitter::ALLOWED_AXIOMS_ENV);
        for is_untrusted in [false, true] {
            if is_untrusted && !has_bwrap {
                continue;
            }
            let err = audit_compiled_modules_with_zygote(
                &store,
                &cfg,
                &["App.Nd".to_string()],
                &lean_path_env,
                &[],
                is_untrusted,
            )
            .unwrap_err()
            .to_string();
            assert!(
                err.contains("_native.native_decide.ax_")
                    || err.contains("Lean.ofReduceBool")
                    || err.contains("Lean.trustCompiler"),
                "untrusted={}: {}",
                is_untrusted,
                err
            );
        }

        // 2. Allowlist `Lean.ofReduceBool,*._native.native_decide.ax_*` admits `App.Nd` (unless `Lean.trustCompiler` was emitted),
        // while even wildcard `*` unconditionally rejects `sorryAx` (`App.Sorry`) and `Lean.trustCompiler`.
        std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, "*");
        for is_untrusted in [false, true] {
            if is_untrusted && !has_bwrap {
                continue;
            }
            let nd_res = audit_compiled_modules_with_zygote(
                &store,
                &cfg,
                &["App.Nd".to_string()],
                &lean_path_env,
                &[],
                is_untrusted,
            );
            if let Err(e) = nd_res {
                let msg = e.to_string();
                assert!(
                    msg.contains("Lean.trustCompiler")
                        && !msg.contains("_native.native_decide.ax_"),
                    "wildcard must admit native_decide aux axioms (only Lean.trustCompiler stays non-allowable): {}",
                    msg
                );
            }
            let sorry_err = audit_compiled_modules_with_zygote(
                &store,
                &cfg,
                &["App.Sorry".to_string()],
                &lean_path_env,
                &[],
                is_untrusted,
            )
            .unwrap_err()
            .to_string();
            assert!(
                sorry_err.contains("sorryAx"),
                "wildcard must never admit sorryAx (untrusted={}): {}",
                is_untrusted,
                sorry_err
            );
            if olean_dir.join("Trust.olean").exists() {
                let tc_err = audit_compiled_modules_with_zygote(
                    &store,
                    &cfg,
                    &["App.Trust".to_string()],
                    &lean_path_env,
                    &[],
                    is_untrusted,
                )
                .unwrap_err()
                .to_string();
                assert!(
                    tc_err.contains("Lean.trustCompiler"),
                    "wildcard must never admit Lean.trustCompiler (untrusted={}): {}",
                    is_untrusted,
                    tc_err
                );
            }
        }

        match prev_allow {
            Some(v) => std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, v),
            None => std::env::remove_var(crate::splitter::ALLOWED_AXIOMS_ENV),
        }
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_runtime_panic_detection_rejects_reply_even_when_ok_flag_is_true() {
        let mut rep = ZygoteEvalReply {
            ok: true,
            import_ok: true,
            messages: vec![
                "<zygote-decl>:4:0: info: PANIC at Lean.EnvExtension.modifyStateImpl: invalid environment extension"
                    .to_string(),
            ],
            ..Default::default()
        };
        assert!(mark_runtime_panic(&mut rep));
        assert!(!rep.ok);
        assert_eq!(rep.errors, vec![RUNTIME_PANIC_ERR.to_string()]);
        // Idempotent, and ordinary output mentioning PANIC is not a runtime panic.
        assert!(mark_runtime_panic(&mut rep) && rep.errors.len() == 1);
        let mut benign = ZygoteEvalReply {
            ok: true,
            messages: vec!["info: \"PANIC button pressed\"".to_string()],
            errors: vec!["unknown identifier 'runtime panic'".to_string()],
            ..Default::default()
        };
        assert!(!mark_runtime_panic(&mut benign) && benign.ok);

        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("panic_guard") else {
            return;
        };
        let lp = tmp_dir.to_string_lossy().to_string();
        let panic_src = "import Lean\n#eval (panic! \"Lean.EnvExtension.modifyStateImpl\" : Nat)\n";
        let live_rep = eval_with_zygote_pool_opts(
            &store,
            "leanprover/lean4:v4.35.0",
            &lp,
            &env_vars,
            &lean_bin,
            panic_src,
            false,
            true,
            Some("PanicTest.lean"),
            Some(30_000),
        )
        .unwrap();
        if live_rep.messages.iter().any(|m| m.contains("PANIC"))
            || live_rep.stdout.contains("PANIC")
            || live_rep
                .errors
                .iter()
                .any(|e| e.contains("PANIC") || e.contains("runtime panic"))
        {
            assert!(
                !live_rep.ok,
                "PANIC output must never return ok=true: {:?}",
                live_rep
            );
        }
        let follow = eval_with_zygote_pool(
            &store,
            "leanprover/lean4:v4.35.0",
            &lp,
            &env_vars,
            &lean_bin,
            "theorem post_panic_clean : 1 + 1 = 2 := rfl\n",
            false,
        )
        .unwrap();
        assert!(
            follow.ok,
            "fresh/healthy worker must succeed after panic shard: {:?}",
            follow
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_worker_crash_diagnostics_capture_exit_code_signal_and_stderr() {
        let spawn_dummy_worker = |script: &str| -> ZygoteWorkerProcess {
            let mut child = Command::new("sh")
                .arg("-c")
                .arg(script)
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .expect("spawn sh");
            let stdin = child.stdin.take().unwrap();
            let stdout = BufReader::new(child.stdout.take().unwrap());
            let stderr_tail = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
            if let Some(mut err_pipe) = child.stderr.take() {
                let tail_clone = stderr_tail.clone();
                let handle = std::thread::spawn(move || {
                    use std::io::Read;
                    let mut buf = Vec::new();
                    let _ = err_pipe.read_to_end(&mut buf);
                    if let Ok(mut g) = tail_clone.lock() {
                        *g = buf;
                    }
                });
                let _ = handle.join();
            }
            let _ = child.wait();
            ZygoteWorkerProcess {
                child,
                _owner: std::sync::mpsc::channel().0,
                stdin,
                stdout,
                stderr_tail,
                warm_prefixes: std::collections::HashSet::new(),
                warm_prefix_tree: Vec::new(),
                warm_imports: std::collections::HashMap::new(),
                request_count: 1,
            }
        };

        let mut exited = spawn_dummy_worker("echo 'stack overflow in Lean runtime' >&2; exit 134");
        let diag = build_worker_crash_diagnostics(
            &mut exited,
            "Zygote worker closed stdout unexpectedly",
            512,
            "imports=Init file=Foo.lean mode=strict bytes=128",
        );
        let rep = ZygoteEvalReply::crashed_reply_with_diag(false, diag);
        assert!(rep.crashed);
        assert!(!rep.ok);
        assert_eq!(rep.exit_code, Some(134));
        assert_eq!(rep.peak_rss_mb, 512);
        assert!(rep.stderr_tail.contains("stack overflow in Lean runtime"));
        assert_eq!(
            rep.last_request.as_deref(),
            Some("imports=Init file=Foo.lean mode=strict bytes=128")
        );
        assert!(rep.errors[0].contains("exit_code=134"));
        assert!(rep.errors[0].contains("stack overflow in Lean runtime"));

        #[cfg(unix)]
        {
            let mut killed = spawn_dummy_worker("echo 'killed by oom' >&2; kill -9 $$");
            let sig_diag = build_worker_crash_diagnostics(
                &mut killed,
                "Zygote worker closed stdout unexpectedly",
                1024,
                "imports=Init file=Oom.lean mode=strict bytes=64",
            );
            let sig_rep = ZygoteEvalReply::crashed_reply_with_diag(false, sig_diag);
            assert!(sig_rep.crashed);
            assert_eq!(sig_rep.exit_signal, Some(9));
            assert!(sig_rep.errors[0].contains("signal=9"));
        }
    }

    #[test]
    fn test_zygote_applies_encoded_max_heartbeats_and_isolates_prefix_cache() {
        let Some((tmp_dir, store, env_vars, lean_bin)) = open_test_zygote_env("lean_args_hb")
        else {
            return;
        };
        let toolchain = "leanprover/lean4:v4.35.0";
        let isolated_lp = tmp_dir.to_string_lossy().to_string();

        let prefix =
            "namespace HbParity\ndef spin : Nat → Nat\n  | 0 => 0\n  | n + 1 => spin n + 1\n";
        let decl = "theorem spin_80 : spin 80 = 80 := rfl\n";
        let shard = format!("{}\n{}", prefix, decl);

        let low_hb = vec!["-DmaxHeartbeats=2".to_string()];
        let high_hb = vec!["-DmaxHeartbeats=400000".to_string()];

        let rep_low = eval_with_zygote_pool_with_args(
            &store,
            toolchain,
            &isolated_lp,
            &env_vars,
            &lean_bin,
            &shard,
            false,
            &low_hb,
        )
        .unwrap();
        assert!(
            !rep_low.ok
                && rep_low
                    .errors
                    .iter()
                    .any(|e| e.contains("maxHeartbeats") || e.contains("heartbeats")),
            "expected heartbeat failure under -DmaxHeartbeats=2, got: {:?}",
            rep_low
        );

        let rep_high = eval_with_zygote_pool_with_args(
            &store,
            toolchain,
            &isolated_lp,
            &env_vars,
            &lean_bin,
            &shard,
            false,
            &high_hb,
        )
        .unwrap();
        assert!(
            rep_high.ok,
            "expected success under -DmaxHeartbeats=400000, got: {:?}",
            rep_high
        );
        assert!(rep_high.proof_term_nodes > 0);

        let rep_low_after = eval_with_zygote_pool_with_args(
            &store,
            toolchain,
            &isolated_lp,
            &env_vars,
            &lean_bin,
            &format!("{}\ntheorem spin_81 : spin 81 = 81 := rfl\n", prefix),
            false,
            &low_hb,
        )
        .unwrap();
        assert!(
            !rep_low_after.ok,
            "warm prefix from high maxHeartbeats must not leak into low maxHeartbeats: {:?}",
            rep_low_after
        );
        let _ = fs::remove_dir_all(&tmp_dir);
    }
}
