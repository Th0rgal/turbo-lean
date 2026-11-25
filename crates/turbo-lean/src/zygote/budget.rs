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
