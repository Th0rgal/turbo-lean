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

pub(crate) fn invocation_timeout_ms() -> Option<u64> {
    MCP_TIMEOUT.with(|slot| slot.get()).or_else(|| {
        std::env::var("TURBO_LEAN_TIMEOUT_MS")
            .ok()?
            .trim()
            .parse()
            .ok()
    })
}

/// Per-audit / `.olean`-reader budget in milliseconds (`TURBO_LEAN_AUDIT_TIMEOUT_SECS`,
/// defaulting to 120 s in untrusted mode and 300 s in trusted mode).
pub(crate) fn audit_timeout_ms(is_untrusted: bool) -> u64 {
    std::env::var("TURBO_LEAN_AUDIT_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok())
        .filter(|&v| v > 0)
        .unwrap_or(if is_untrusted { 120 } else { 300 })
        .saturating_mul(1000)
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

/// `eval --timeout-ms` semantics: `0` means "no artificial timeout" (`None`), never a zero budget.
pub(crate) fn eval_request_timeout_ms(timeout_ms: u64) -> Option<u64> {
    (timeout_ms > 0).then_some(timeout_ms)
}

/// Knobs that govern per-module compile and audit/replay timeouts, named in timeout errors.
pub(crate) const MODULE_TIMEOUT_KNOB_HINT: &str = "raise the per-module budget with `[build] module_timeout_secs` in turbo-lean.toml or `TURBO_LEAN_MODULE_TIMEOUT_SECS` (audit / kernel-replay readers: `TURBO_LEAN_AUDIT_TIMEOUT_SECS`; requests: `--timeout-ms` / `TURBO_LEAN_TIMEOUT_MS`)";

/// Attach `MODULE_TIMEOUT_KNOB_HINT` to any error whose chain reports a timeout (idempotent).
pub(crate) fn with_timeout_knob_hint(err: anyhow::Error) -> anyhow::Error {
    let rendered = format!("{err:#}");
    if rendered.contains("timed out") && !rendered.contains("TURBO_LEAN_MODULE_TIMEOUT_SECS") {
        err.context(format!("timeout: {MODULE_TIMEOUT_KNOB_HINT}"))
    } else {
        err
    }
}

/// Default estimated resident memory of one `--kernel-replay-closure` worker (MiB), overridable
/// with `TURBO_LEAN_REPLAY_WORKER_RSS_MB`.
pub(crate) const DEFAULT_REPLAY_WORKER_RSS_MB: u64 = 4096;

/// Effective kernel-replay worker budget derived from `--jobs` / `TURBO_LEAN_JOBS` and
/// `--max-memory-mb` / `TURBO_LEAN_MAX_MEMORY_MB` (`MemoryBudgetGovernor`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ReplayWorkerBudget {
    /// Number of concurrent replay worker processes.
    pub parallelism: usize,
    /// Per-worker memory share in MiB (`budget_mb / parallelism`) when a memory budget is set.
    pub per_worker_memory_mb: Option<u64>,
    /// Replay closure batch cap: `Some(1)` (one module per process) when the per-worker share
    /// cannot hold two estimated closures.
    pub batch_cap: Option<usize>,
}

/// Pure replay budget resolution: `jobs` (explicit `--jobs`, else `cpus`) is clamped by how many
/// `est_worker_rss_mb` workers fit in `max_memory_mb`; untrusted replay stays single-worker.
pub(crate) fn replay_worker_budget_from(
    jobs: Option<usize>,
    max_memory_mb: Option<u64>,
    cpus: usize,
    est_worker_rss_mb: u64,
    is_untrusted: bool,
) -> ReplayWorkerBudget {
    let est = est_worker_rss_mb.max(256);
    let requested = if is_untrusted {
        1
    } else {
        jobs.filter(|&n| n > 0).unwrap_or(cpus).max(1)
    };
    let Some(budget_mb) = max_memory_mb.filter(|&mb| mb > 0) else {
        return ReplayWorkerBudget {
            parallelism: requested,
            per_worker_memory_mb: None,
            batch_cap: None,
        };
    };
    let fit = usize::try_from(budget_mb / est)
        .unwrap_or(usize::MAX)
        .max(1);
    let parallelism = requested.min(fit).max(1);
    let per_worker_mb = (budget_mb / parallelism as u64).max(1);
    ReplayWorkerBudget {
        parallelism,
        per_worker_memory_mb: Some(per_worker_mb),
        batch_cap: (per_worker_mb < est.saturating_mul(2)).then_some(1),
    }
}

fn positive_env<T: std::str::FromStr + PartialOrd + Default>(key: &str) -> Option<T> {
    std::env::var(key)
        .ok()
        .and_then(|s| s.trim().parse::<T>().ok())
        .filter(|v| *v > T::default())
}

/// Worker count for memory-heavy kernel-replay / audit children: the memory-bounded
/// `TURBO_LEAN_REPLAY_JOBS` (exported by [`export_replay_worker_budget`]) else `TURBO_LEAN_JOBS`.
/// The compile scheduler keeps reading `TURBO_LEAN_JOBS` alone, so a replay clamp never
/// throttles `build` / `seed-oleans` compile parallelism.
pub(crate) fn replay_jobs_env() -> Option<usize> {
    positive_env("TURBO_LEAN_REPLAY_JOBS").or_else(|| positive_env("TURBO_LEAN_JOBS"))
}

/// Live replay budget from `jobs` (else `TURBO_LEAN_JOBS`), `TURBO_LEAN_MAX_MEMORY_MB` and
/// `TURBO_LEAN_REPLAY_WORKER_RSS_MB`.
pub(crate) fn replay_worker_budget_with_jobs(
    jobs: Option<usize>,
    is_untrusted: bool,
) -> ReplayWorkerBudget {
    let cpus = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);
    replay_worker_budget_from(
        jobs.filter(|&n| n > 0)
            .or_else(|| positive_env("TURBO_LEAN_JOBS")),
        positive_env("TURBO_LEAN_MAX_MEMORY_MB"),
        cpus,
        positive_env("TURBO_LEAN_REPLAY_WORKER_RSS_MB").unwrap_or(DEFAULT_REPLAY_WORKER_RSS_MB),
        is_untrusted,
    )
}

/// Export the effective `--jobs` / `--max-memory-mb` budget for kernel replay. `check --jobs`
/// (`export_jobs`) becomes `TURBO_LEAN_JOBS` for the whole command (#435). Under a memory budget
/// the clamped replay worker count goes to `TURBO_LEAN_REPLAY_JOBS` only (read via
/// [`replay_jobs_env`]), and the batch cap / per-worker RSS share to
/// `TURBO_LEAN_REPLAY_CLOSURE_BATCH_SIZE` / `TURBO_LEAN_WORKER_RSS_LIMIT_MB`; explicit user values
/// of those three are never overridden. `budget_jobs` (e.g. `seed-oleans --jobs`, which scopes
/// `TURBO_LEAN_JOBS` itself) only feeds the replay budget.
pub(crate) fn export_replay_worker_budget(export_jobs: Option<usize>, budget_jobs: Option<usize>) {
    if let Some(jobs) = export_jobs.filter(|&n| n > 0) {
        std::env::set_var("TURBO_LEAN_JOBS", jobs.to_string());
    }
    if positive_env::<u64>("TURBO_LEAN_MAX_MEMORY_MB").is_none() {
        return;
    }
    let budget = replay_worker_budget_with_jobs(export_jobs.or(budget_jobs), false);
    if std::env::var_os("TURBO_LEAN_REPLAY_JOBS").is_none() {
        std::env::set_var("TURBO_LEAN_REPLAY_JOBS", budget.parallelism.to_string());
    }
    if let Some(cap) = budget.batch_cap {
        if std::env::var_os("TURBO_LEAN_REPLAY_CLOSURE_BATCH_SIZE").is_none() {
            std::env::set_var("TURBO_LEAN_REPLAY_CLOSURE_BATCH_SIZE", cap.to_string());
        }
    }
    if let Some(mb) = budget.per_worker_memory_mb {
        if std::env::var_os("TURBO_LEAN_WORKER_RSS_LIMIT_MB").is_none() {
            std::env::set_var("TURBO_LEAN_WORKER_RSS_LIMIT_MB", mb.to_string());
        }
    }
}

pub(crate) fn run_lean_command(
    cmd: &mut Command,
    timeout_ms: Option<u64>,
) -> Result<std::process::Output> {
    anyhow::ensure!(
        timeout_ms != Some(0),
        "Lean request timed out before fallback (request budget exhausted; raise `--timeout-ms` / `TURBO_LEAN_TIMEOUT_MS`, or pass `--timeout-ms 0` for no artificial timeout)"
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_timeout_ms_zero_means_no_timeout() {
        assert_eq!(eval_request_timeout_ms(0), None);
        assert_eq!(eval_request_timeout_ms(1), Some(1));
        assert_eq!(eval_request_timeout_ms(3_600_000), Some(3_600_000));
    }

    #[test]
    fn test_eval_timeout_ms_zero_does_not_fail_fallback_immediately() {
        // `--timeout-ms 0` must reach `run_lean_command` as `None` (default budget), not a zero
        // budget that bails with "timed out before fallback" without spawning `lean`.
        let mut cmd = Command::new("/bin/sh");
        cmd.args(["-c", "true"]);
        let out = run_lean_command(&mut cmd, eval_request_timeout_ms(0))
            .expect("zero `--timeout-ms` must not be a zero budget");
        assert!(out.status.success());
    }

    #[test]
    fn test_replay_worker_budget_honors_jobs_and_memory() {
        // No budget: CPUs.
        let b = replay_worker_budget_from(None, None, 8, 4096, false);
        assert_eq!(b.parallelism, 8);
        assert_eq!(b.per_worker_memory_mb, None);
        assert_eq!(b.batch_cap, None);
        // `--jobs 1` reaches replay (#435).
        assert_eq!(
            replay_worker_budget_from(Some(1), None, 8, 4096, false).parallelism,
            1
        );
        assert_eq!(
            replay_worker_budget_from(Some(3), None, 8, 4096, false).parallelism,
            3
        );
        // `--max-memory-mb 10000` with 4 GiB workers on 8 cores: 2 workers, 5000 MiB each.
        let b = replay_worker_budget_from(None, Some(10_000), 8, 4096, false);
        assert_eq!(b.parallelism, 2);
        assert_eq!(b.per_worker_memory_mb, Some(5_000));
        assert_eq!(b.batch_cap, Some(1), "5000 MiB < 2 x 4096 MiB closure");
        // `--jobs 1 --max-memory-mb 4000`: one worker, whole budget, single-module batches.
        let b = replay_worker_budget_from(Some(1), Some(4_000), 8, 4096, false);
        assert_eq!(b.parallelism, 1);
        assert_eq!(b.per_worker_memory_mb, Some(4_000));
        assert_eq!(b.batch_cap, Some(1));
        // Generous budget: jobs bound, no batch shrink.
        let b = replay_worker_budget_from(Some(2), Some(64_000), 8, 4096, false);
        assert_eq!(b.parallelism, 2);
        assert_eq!(b.per_worker_memory_mb, Some(32_000));
        assert_eq!(b.batch_cap, None);
        // Untrusted replay is always single-worker.
        assert_eq!(
            replay_worker_budget_from(Some(8), Some(64_000), 8, 4096, true).parallelism,
            1
        );
        // Degenerate inputs never yield zero workers.
        assert_eq!(
            replay_worker_budget_from(Some(0), Some(1), 0, 4096, false).parallelism,
            1
        );
    }

    #[test]
    fn test_export_replay_worker_budget_sets_scheduler_env() {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        const KEYS: [&str; 6] = [
            "TURBO_LEAN_JOBS",
            "TURBO_LEAN_REPLAY_JOBS",
            "TURBO_LEAN_MAX_MEMORY_MB",
            "TURBO_LEAN_REPLAY_CLOSURE_BATCH_SIZE",
            "TURBO_LEAN_WORKER_RSS_LIMIT_MB",
            "TURBO_LEAN_REPLAY_WORKER_RSS_MB",
        ];
        let prev: Vec<_> = KEYS.iter().map(|k| (*k, std::env::var_os(k))).collect();
        let clear = || {
            for k in KEYS {
                std::env::remove_var(k);
            }
        };
        clear();

        // Neither flag: untouched.
        export_replay_worker_budget(None, None);
        for k in KEYS {
            assert!(std::env::var_os(k).is_none(), "{k} must stay unset");
        }

        // `check --jobs 1` is exported command-wide and reaches replay (#435).
        export_replay_worker_budget(Some(1), None);
        assert_eq!(std::env::var("TURBO_LEAN_JOBS").as_deref(), Ok("1"));
        assert_eq!(replay_jobs_env(), Some(1));
        assert_eq!(replay_worker_budget_with_jobs(None, false).parallelism, 1);
        assert!(std::env::var_os("TURBO_LEAN_REPLAY_JOBS").is_none());
        clear();

        // `--max-memory-mb 4000` alone: replay is clamped, compile `TURBO_LEAN_JOBS` is not.
        std::env::set_var("TURBO_LEAN_MAX_MEMORY_MB", "4000");
        export_replay_worker_budget(None, None);
        assert!(
            std::env::var_os("TURBO_LEAN_JOBS").is_none(),
            "a memory budget must not clamp `build` compile parallelism"
        );
        assert_eq!(std::env::var("TURBO_LEAN_REPLAY_JOBS").as_deref(), Ok("1"));
        assert_eq!(replay_jobs_env(), Some(1));
        assert_eq!(
            std::env::var("TURBO_LEAN_REPLAY_CLOSURE_BATCH_SIZE").as_deref(),
            Ok("1")
        );
        assert_eq!(
            std::env::var("TURBO_LEAN_WORKER_RSS_LIMIT_MB").as_deref(),
            Ok("4000")
        );
        clear();

        // `seed-oleans --jobs 4 --max-memory-mb 64000`: its own scoped `TURBO_LEAN_JOBS` is left
        // alone; the replay budget is sized from its `--jobs`.
        std::env::set_var("TURBO_LEAN_MAX_MEMORY_MB", "64000");
        export_replay_worker_budget(None, Some(4));
        assert!(std::env::var_os("TURBO_LEAN_JOBS").is_none());
        assert_eq!(std::env::var("TURBO_LEAN_REPLAY_JOBS").as_deref(), Ok("4"));
        assert_eq!(
            std::env::var("TURBO_LEAN_WORKER_RSS_LIMIT_MB").as_deref(),
            Ok("16000")
        );
        assert!(std::env::var_os("TURBO_LEAN_REPLAY_CLOSURE_BATCH_SIZE").is_none());
        // A later scoped `TURBO_LEAN_JOBS=4` (seed-oleans) stays the compile width while replay
        // keeps the memory-bounded count.
        std::env::set_var("TURBO_LEAN_JOBS", "8");
        std::env::set_var("TURBO_LEAN_REPLAY_JOBS", "2");
        assert_eq!(replay_jobs_env(), Some(2));
        clear();

        // Explicit user batch size / RSS limit / replay jobs are preserved.
        std::env::set_var("TURBO_LEAN_MAX_MEMORY_MB", "4000");
        std::env::set_var("TURBO_LEAN_REPLAY_CLOSURE_BATCH_SIZE", "4");
        std::env::set_var("TURBO_LEAN_WORKER_RSS_LIMIT_MB", "3000");
        export_replay_worker_budget(Some(2), None);
        assert_eq!(std::env::var("TURBO_LEAN_JOBS").as_deref(), Ok("2"));
        assert_eq!(std::env::var("TURBO_LEAN_REPLAY_JOBS").as_deref(), Ok("1"));
        assert_eq!(replay_jobs_env(), Some(1));
        assert_eq!(
            std::env::var("TURBO_LEAN_REPLAY_CLOSURE_BATCH_SIZE").as_deref(),
            Ok("4")
        );
        assert_eq!(
            std::env::var("TURBO_LEAN_WORKER_RSS_LIMIT_MB").as_deref(),
            Ok("3000")
        );
        clear();
        std::env::set_var("TURBO_LEAN_MAX_MEMORY_MB", "4000");
        std::env::set_var("TURBO_LEAN_REPLAY_JOBS", "3");
        export_replay_worker_budget(None, None);
        assert_eq!(std::env::var("TURBO_LEAN_REPLAY_JOBS").as_deref(), Ok("3"));

        for (k, v) in prev {
            match v {
                Some(v) => std::env::set_var(k, v),
                None => std::env::remove_var(k),
            }
        }
    }

    #[test]
    fn test_timeout_errors_name_module_timeout_knob() {
        let err = anyhow::anyhow!("`lean` command timed out after 300000ms")
            .context("Failed to invoke `lean` compiler for module `Big`");
        let hinted = format!("{:#}", with_timeout_knob_hint(err));
        assert!(hinted.contains("[build] module_timeout_secs"), "{hinted}");
        assert!(
            hinted.contains("TURBO_LEAN_MODULE_TIMEOUT_SECS"),
            "{hinted}"
        );
        assert!(hinted.contains("Big"), "{hinted}");
        // Idempotent.
        let twice = format!(
            "{:#}",
            with_timeout_knob_hint(with_timeout_knob_hint(anyhow::anyhow!("x timed out")))
        );
        assert_eq!(twice.matches("TURBO_LEAN_MODULE_TIMEOUT_SECS").count(), 1);
        // Non-timeout errors are untouched.
        let plain = format!("{:#}", with_timeout_knob_hint(anyhow::anyhow!("boom")));
        assert_eq!(plain, "boom");
    }
}
