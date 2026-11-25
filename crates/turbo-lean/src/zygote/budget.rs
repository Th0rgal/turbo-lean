use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;
use std::process::Command;

use super::LifecycleProcess;

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

    if let Ok(out) = crate::trusted_tools::system_command("ps").and_then(|mut command| {
        command
            .args(["-o", "rss=", "-p", &pid.to_string()])
            .output()
            .map_err(Into::into)
    }) {
        if out.status.success() {
            if let Ok(rss_kb) = String::from_utf8_lossy(&out.stdout).trim().parse::<u64>() {
                return rss_kb / 1024;
            }
        }
    }

    0
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(super) struct ZygoteLruEntry {
    pub(super) pid: u32,
    pub(super) last_used_ms: u64,
    pub(super) rss_mb: u64,
}

/// Machine-wide `/dev/shm` LRU RSS governor across all concurrent `ZygoteWorker` processes.
/// Bounds total resident memory across multi-worktree agent runs to `TURBO_LEAN_MAX_TOTAL_ZYGOTE_RSS_MB`
/// (defaulting to the detected `MemoryBudgetGovernor::detect().budget_mb` clamped to `1024..=12288` MiB).
pub(super) fn max_total_zygote_rss_mb() -> u64 {
    std::env::var("TURBO_LEAN_MAX_TOTAL_ZYGOTE_RSS_MB")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .filter(|&mb| mb >= 256)
        .unwrap_or_else(|| {
            crate::shm_cache::MemoryBudgetGovernor::detect()
                .budget_mb
                .clamp(2048, 12_288)
        })
}

pub(super) fn max_zygote_processes() -> usize {
    std::env::var("TURBO_LEAN_MAX_ZYGOTE_PROCESSES")
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .filter(|&n| n >= 1)
        .unwrap_or_else(|| {
            crate::shm_cache::MemoryBudgetGovernor::detect()
                .recommended_parallel_workers(1024)
                .clamp(8, 16)
        })
}

pub fn govern_machine_wide_zygote_rss(current_pid: u32, current_rss_mb: u64) {
    let max_total_mb = max_total_zygote_rss_mb();
    let max_entries = max_zygote_processes();
    let Some(shm_dir) = crate::shm_cache::ensure_verified_private_staging_dir(None) else {
        return;
    };
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
            entries.sort_by_key(|b| std::cmp::Reverse(b.last_used_ms));
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
                // Young or active processes still consume memory even over the limit.
                running_rss_mb = running_rss_mb.saturating_add(entry.rss_mb);
                kept_entries.push(entry);
            }
            kept_entries.sort_by_key(|e| e.last_used_ms);
            *entries = kept_entries;
        },
    );
}

/// Conservative per-process RSS estimate in MiB for a kernel replay/audit worker loading a
/// bounded `.olean` closure slice; used to clamp parallelism under an explicit memory budget.
pub(crate) const REPLAY_WORKER_EST_RSS_MB: u64 = 2048;

/// One resource budget that reaches every worker (#435): the effective job count
/// (`check --jobs`, exported as `TURBO_LEAN_JOBS`) and the memory cap (`--max-memory-mb` /
/// `TURBO_LEAN_MAX_MEMORY_MB`), carried as one object instead of ad hoc env reads at each
/// spawn site, so kernel-replay and audit workers observe the limits the CLI was given.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WorkerBudget {
    pub jobs: Option<usize>,
    pub max_memory_mb: Option<u64>,
}

impl WorkerBudget {
    pub fn from_env() -> Self {
        Self {
            jobs: std::env::var("TURBO_LEAN_JOBS")
                .ok()
                .and_then(|s| s.trim().parse::<usize>().ok())
                .filter(|&n| n > 0),
            max_memory_mb: std::env::var("TURBO_LEAN_MAX_MEMORY_MB")
                .ok()
                .and_then(|s| s.trim().parse::<u64>().ok())
                .filter(|&mb| mb > 0),
        }
    }

    /// Export `--jobs` as `TURBO_LEAN_JOBS` for the whole command so replay and audit
    /// workers spawned downstream observe it (#435). An explicit environment setting wins.
    pub fn export_effective_jobs(jobs: Option<usize>) {
        if let Some(j) = jobs.filter(|&j| j > 0) {
            if std::env::var_os("TURBO_LEAN_JOBS").is_none() {
                std::env::set_var("TURBO_LEAN_JOBS", j.to_string());
            }
        }
    }

    /// Effective worker parallelism for `work_items` units of work. An explicit job count
    /// is honored up to the memory budget's share (`budget / est_worker_rss_mb`, never
    /// silently clamped by core count: the operator already chose the width); otherwise
    /// `fallback()`, clamped under an explicit budget by the governor's core-aware
    /// recommendation. Always at least one worker, never wider than the work list.
    pub fn effective_parallelism(
        &self,
        work_items: usize,
        est_worker_rss_mb: u64,
        fallback: impl FnOnce() -> usize,
    ) -> usize {
        let clamped = match (self.jobs, self.max_memory_mb) {
            (Some(jobs), Some(mb)) => {
                let budget_cap = (mb / est_worker_rss_mb.max(256)).max(1) as usize;
                jobs.max(1).min(budget_cap)
            }
            (Some(jobs), None) => jobs.max(1),
            (None, Some(mb)) => fallback().max(1).min(
                crate::shm_cache::MemoryBudgetGovernor::new(mb)
                    .recommended_parallel_workers(est_worker_rss_mb),
            ),
            (None, None) => fallback().max(1),
        };
        clamped.clamp(1, work_items.max(1))
    }

    /// Per-worker address-space cap in MiB under an explicit budget: the budget divided
    /// across the workers, floored at 512 MiB so a wide run cannot starve every worker
    /// below a workable Lean heap.
    pub fn per_worker_rlimit_mb(&self, parallelism: usize) -> Option<u64> {
        self.max_memory_mb
            .map(|mb| (mb / parallelism.max(1) as u64).max(512))
    }

    /// Shrink the replay closure batch cap when the per-worker budget is tight: one module
    /// per replay process below 2 GiB per worker, at most 8 modules below 4 GiB, else
    /// `base_cap` unchanged.
    pub fn replay_batch_cap(&self, base_cap: usize, parallelism: usize) -> usize {
        match self.per_worker_rlimit_mb(parallelism) {
            Some(mb) if mb < 2048 => 1,
            Some(mb) if mb < 4096 => base_cap.clamp(1, 8),
            _ => base_cap.max(1),
        }
    }

    /// Apply the per-worker cap as a real `RLIMIT_DATA` on the spawned worker (#435):
    /// rlimits survive `exec`, so the cap also reaches a bwrap-wrapped worker, and it is
    /// the same limit kind the untrusted sandbox already applies. `RLIMIT_AS` is
    /// deliberately NOT capped by default: a replay worker's address space includes the
    /// mmapped `.olean` closure and the 256 MiB `LEAN_STACK_SIZE_KB` stack, so an AS cap
    /// sized from an RSS budget fails replays whose mappings exceed it even though
    /// resident memory fits. `TURBO_LEAN_WORKER_RLIMIT_AS_MULTIPLIER=<n>` opts into
    /// `RLIMIT_AS = n ×` the cap. Fail-open inside the child: a worker that cannot lower
    /// its limits still runs, and the machine-wide LRU governor remains the backstop.
    pub fn apply_worker_rlimit(cmd: &mut Command, rlimit_mb: u64) {
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            let data_bytes = rlimit_mb.saturating_mul(1024 * 1024);
            // Read the opt-in in the parent: `pre_exec` runs post-fork, where only
            // async-signal-safe calls are sound.
            let as_bytes = std::env::var("TURBO_LEAN_WORKER_RLIMIT_AS_MULTIPLIER")
                .ok()
                .and_then(|s| s.trim().parse::<u64>().ok())
                .filter(|&n| n > 0)
                .map(|n| data_bytes.saturating_mul(n));
            unsafe {
                cmd.pre_exec(move || {
                    let data_lim = libc::rlimit {
                        rlim_cur: data_bytes as libc::rlim_t,
                        rlim_max: data_bytes as libc::rlim_t,
                    };
                    let _ = libc::setrlimit(libc::RLIMIT_DATA, &data_lim);
                    if let Some(bytes) = as_bytes {
                        let as_lim = libc::rlimit {
                            rlim_cur: bytes as libc::rlim_t,
                            rlim_max: bytes as libc::rlim_t,
                        };
                        let _ = libc::setrlimit(libc::RLIMIT_AS, &as_lim);
                    }
                    Ok(())
                });
            }
        }
        #[cfg(not(unix))]
        {
            let _ = (cmd, rlimit_mb);
        }
    }

    /// A named explanation when a replay worker's failure may trace to the per-worker
    /// memory cap (#435). An `RLIMIT_DATA` breach surfaces as a failed allocation
    /// (ENOMEM / `std::bad_alloc` / "out of memory" on stderr with a plain non-zero
    /// exit) — an rlimit never SIGKILLs — so a definite attribution needs the allocation
    /// signature; a signal exit gets a "may have been", naming both possibilities.
    /// Empty when no cap was applied or nothing points at memory.
    pub fn memory_kill_note(
        status: &std::process::ExitStatus,
        stderr: &str,
        rlimit_mb: Option<u64>,
    ) -> String {
        let Some(mb) = rlimit_mb else {
            return String::new();
        };
        #[cfg(unix)]
        {
            use std::os::unix::process::ExitStatusExt;
            if let Some(sig) = status.signal() {
                return format!(
                    "\nworker died with signal {sig}; it may have been out of memory under \
                     the per-worker cap of {mb} MiB (RLIMIT_DATA from --max-memory-mb / \
                     TURBO_LEAN_MAX_MEMORY_MB), or it may have died for an unrelated \
                     reason; raise the budget or lower --jobs / TURBO_LEAN_JOBS to give \
                     each worker a larger share, then retry"
                );
            }
        }
        let lower = stderr.to_ascii_lowercase();
        let alloc_failure = !status.success()
            && [
                "out of memory",
                "bad_alloc",
                "enomem",
                "cannot allocate memory",
                "memory allocation failed",
            ]
            .iter()
            .any(|needle| lower.contains(needle));
        if alloc_failure {
            return format!(
                "\nworker failed to allocate under the per-worker memory cap of {mb} MiB \
                 (RLIMIT_DATA from --max-memory-mb / TURBO_LEAN_MAX_MEMORY_MB); raise the \
                 budget or lower --jobs / TURBO_LEAN_JOBS to give each worker a larger share"
            );
        }
        String::new()
    }
}

pub(crate) const REQUEST_POLICY_KEYS: [&str; 4] = [
    "TURBO_LEAN_ALLOWED_AXIOMS",
    "TURBO_LEAN_ALLOWED_CSIMP",
    "TURBO_LEAN_ALLOWED_UNSAFE",
    "TURBO_LEAN_ALLOWED_IMPLEMENTED_BY",
];

pub(crate) const MCP_RUNTIME_POLICY_KEYS: [&str; 5] = [
    "TURBO_LEAN_AUDIT_SPEC_CONFIG",
    "TURBO_LEAN_KERNEL_ENGINE",
    "TURBO_LEAN_TELEMETRY",
    "SANDBOXED_TELEMETRY_MODE",
    "SANDBOXED_TELEMETRY",
];

thread_local! {
    pub(super) static MCP_TIMEOUT: std::cell::Cell<Option<u64>> = const { std::cell::Cell::new(None) };
    pub(super) static INBOUND_POLICY: std::cell::RefCell<Option<std::collections::BTreeMap<String, String>>> = const { std::cell::RefCell::new(None) };
}

pub(crate) struct McpTimeoutGuard(Option<u64>);

impl McpTimeoutGuard {
    pub(crate) fn new(timeout: Option<u64>) -> Self {
        Self(MCP_TIMEOUT.with(|slot| slot.replace(timeout.or_else(invocation_timeout_ms))))
    }
}

impl Drop for McpTimeoutGuard {
    fn drop(&mut self) {
        MCP_TIMEOUT.with(|slot| slot.set(self.0));
    }
}

pub(crate) fn set_inbound_policy(policy: std::collections::BTreeMap<String, String>) {
    INBOUND_POLICY.with(|p| *p.borrow_mut() = Some(policy));
}

pub(crate) fn clear_inbound_policy() {
    INBOUND_POLICY.with(|p| *p.borrow_mut() = None);
    MCP_TIMEOUT.with(|slot| slot.set(None));
}

pub(super) fn normalize_mcp_runtime_setting(key: &str, value: String) -> String {
    let trimmed = value.trim();
    if key == "TURBO_LEAN_AUDIT_SPEC_CONFIG"
        && !trimmed.is_empty()
        && !trimmed.starts_with('{')
        && !trimmed.contains('\n')
        && !trimmed.contains('=')
        && Path::new(trimmed).is_relative()
    {
        if let Ok(cwd) = std::env::current_dir() {
            return cwd.join(trimmed).to_string_lossy().into_owned();
        }
    }
    value
}

pub(super) fn mcp_caller_policy() -> std::collections::BTreeMap<String, String> {
    let mut policy = INBOUND_POLICY
        .with(|p| p.borrow().clone())
        .unwrap_or_else(|| {
            REQUEST_POLICY_KEYS
                .into_iter()
                .chain(MCP_RUNTIME_POLICY_KEYS)
                .filter_map(|key| {
                    if std::env::var(format!("{key}_FROM_CONFIG")).as_deref() == Ok("1") {
                        None
                    } else {
                        std::env::var(key).ok().map(|value| {
                            (key.to_string(), normalize_mcp_runtime_setting(key, value))
                        })
                    }
                })
                .collect()
        });
    for key in ["SANDBOXED_TELEMETRY_MODE", "SANDBOXED_TELEMETRY"] {
        policy.entry(key.to_string()).or_default();
    }
    policy
}

pub(crate) fn has_inbound_mcp_policy() -> bool {
    INBOUND_POLICY.with(|policy| policy.borrow().is_some())
}

pub(crate) fn inbound_setting(key: &str) -> Option<String> {
    INBOUND_POLICY
        .with(|p| p.borrow().as_ref().map(|p| p.get(key).cloned()))
        .unwrap_or_else(|| std::env::var(key).ok())
}

pub(crate) fn configure_mcp_child_policy(cmd: &mut Command) {
    for key in REQUEST_POLICY_KEYS
        .into_iter()
        .chain(MCP_RUNTIME_POLICY_KEYS)
    {
        cmd.env_remove(key).env_remove(format!("{key}_FROM_CONFIG"));
    }
    cmd.envs(mcp_caller_policy());
    cmd.env_remove("TURBO_LEAN_TIMEOUT_MS");
    if let Some(timeout) = invocation_timeout_ms() {
        cmd.env("TURBO_LEAN_TIMEOUT_MS", timeout.to_string());
    }
}

pub(crate) fn request_policy(
    env: &std::collections::HashMap<String, String>,
) -> std::collections::BTreeMap<String, String> {
    REQUEST_POLICY_KEYS
        .into_iter()
        .map(|key| {
            let value = env
                .get(key)
                .cloned()
                .or_else(|| {
                    INBOUND_POLICY.with(|p| {
                        p.borrow()
                            .as_ref()
                            .map(|p| p.get(key).cloned().unwrap_or_default())
                    })
                })
                .or_else(|| std::env::var(key).ok())
                .unwrap_or_default();
            let mut tags: Vec<_> = value
                .split(',')
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .collect();
            tags.sort_unstable();
            tags.dedup();
            (key.to_string(), tags.join(","))
        })
        .collect()
}

/// Map an explicit per-request `--timeout-ms` value to the budget the fallback paths
/// understand (#443): `0` is documented as "no artificial timeout", but `Some(0)` is an
/// exhausted budget to `run_lean_command` and the shard-fallback `budget_left`, so it must
/// become `None` before it reaches them.
pub(crate) fn request_timeout_ms(timeout_ms: u64) -> Option<u64> {
    (timeout_ms > 0).then_some(timeout_ms)
}

pub(crate) fn invocation_timeout_ms() -> Option<u64> {
    MCP_TIMEOUT.with(|slot| slot.get()).or_else(|| {
        std::env::var("TURBO_LEAN_TIMEOUT_MS")
            .ok()?
            .trim()
            .parse()
            .ok()
    })
}

/// Per-audit / `.olean`-reader budget in milliseconds (`TURBO_LEAN_AUDIT_TIMEOUT_SECS`, or
/// `[audit] timeout_secs` in turbo-lean.toml; defaulting to 120 s in untrusted mode and
/// 300 s in trusted mode).
pub(crate) fn audit_timeout_ms(is_untrusted: bool) -> u64 {
    std::env::var("TURBO_LEAN_AUDIT_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok())
        .filter(|&v| v > 0)
        .unwrap_or(if is_untrusted { 120 } else { 300 })
        .saturating_mul(1000)
}

/// Per kernel-replay-worker budget in milliseconds (`TURBO_LEAN_REPLAY_TIMEOUT_SECS`, or
/// `[replay] timeout_secs` in turbo-lean.toml), defaulting to `audit_timeout_ms` (#437).
pub(crate) fn replay_timeout_ms(is_untrusted: bool) -> u64 {
    std::env::var("TURBO_LEAN_REPLAY_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok())
        .filter(|&v| v > 0)
        .map(|secs| secs.saturating_mul(1000))
        .unwrap_or_else(|| audit_timeout_ms(is_untrusted))
}

/// Effective `.olean` declaration-identity reader budget in milliseconds: aligns with
/// `audit_timeout_ms(is_untrusted)`, capped by any explicit request timeout (`TURBO_LEAN_TIMEOUT_MS`)
/// and any remaining wall-clock budget since `started`.
pub(crate) fn decl_identity_reader_budget_ms(
    is_untrusted: bool,
    started: Option<std::time::Instant>,
) -> u64 {
    let audit_ms = audit_timeout_ms(is_untrusted);
    let cap_ms = invocation_timeout_ms()
        .filter(|ms| *ms > 0)
        .map_or(audit_ms, |ms| ms.min(audit_ms));
    match started {
        Some(t0) => remaining_timeout_ms(Some(cap_ms), t0),
        None => cap_ms,
    }
}

/// Share the request budget across worker attempts and a stock-Lean fallback.
pub(crate) fn remaining_timeout_ms(timeout_ms: Option<u64>, started: std::time::Instant) -> u64 {
    timeout_ms
        .or_else(invocation_timeout_ms)
        .filter(|ms| *ms > 0)
        .unwrap_or(90_000)
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
                .unwrap_or(90_000),
        ),
        false,
    )
}
