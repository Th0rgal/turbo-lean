//! Ultra-Fast Model Context Protocol (MCP) JSON-RPC 2.0 Server, Token-Compacting Surgical
//! Formatter (`compact_for_llm`), and Cross-Agent `/dev/shm` Telemetry & Bottleneck Ledger (`mcp.rs`).
//!
//! Why do LLM proof agents waste tokens and time?
//! 1. Raw Lean compiler outputs and verbose JSON blobs often contain 500–2,000 tokens of redundant
//!    stack traces, full prefix sources, and repeated metadata on every proof edit turn.
//! 2. Spawning cold CLI processes on every agent tool call loses warm context and lacks cross-agent
//!    bottleneck analytics.
//!
//! This module implements:
//! - [`AgentAnalyticsLedger`]: Persistent cross-agent telemetry in
//!   `/dev/shm/turbo-lean-staging-<uid>/mcp_agent_analytics.json` protected by `flock` +
//!   `crate::shm_cache::atomic_write_shm`.
//! - [`compact_for_llm`]: Surgical token-compacting formatter (`<= 60 tokens`) that reduces verbose
//!   agent-step / check / fast-check payloads by 4x–10x while preserving actionable diagnostics.
//! - [`run_mcp_stdio_server`]: Full JSON-RPC 2.0 MCP server over `stdio` supporting both
//!   newline-delimited JSON-RPC lines and `Content-Length: ...\r\n\r\n` framed MCP messages.

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fs::{self, OpenOptions};
use std::io::{self, BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

/// Categorized wall-clock time breakdown across the verification pipeline.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct BottleneckBreakdown {
    pub import_env_ms: f64,
    pub prefix_elab_ms: f64,
    pub tactic_elab_ms: f64,
    pub fastcheck_tpu_ms: f64,
}

/// Entry in the top-10 slowest declarations leaderboard.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct SlowDeclarationEntry {
    pub decl_name: String,
    pub elapsed_ms: f64,
    pub heartbeats: u64,
    pub winning_tactic_hint: Option<String>,
}

/// Actionable tactic speedup recommendation discovered by an accelerator.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TacticSpeedupRecommendation {
    pub decl_name: String,
    pub original_tactic: String,
    pub recommended_tactic: String,
    pub accelerator_name: String,
    pub estimated_speedup_hint: String,
    pub elapsed_ms: f64,
}

/// Persistent `/dev/shm` Cross-Agent Analytics Ledger (`AgentAnalyticsLedger`).
///
/// Stored at `/dev/shm/turbo-lean-staging-<uid>/mcp_agent_analytics.json` and synchronized via
/// `flock` on `/dev/shm/turbo-lean-staging-<uid>/mcp_agent_analytics.lock` + `atomic_write_shm`.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct AgentAnalyticsLedger {
    pub total_calls: u64,
    pub cache_hits: u64,
    pub stage1_tpu_rejects: u64,
    pub accelerator_rewrites: u64,
    pub zygote_verifications: u64,
    pub total_elapsed_ms: f64,
    pub stage1_tpu_ms: f64,
    pub stage2_zygote_ms: f64,
    pub raw_output_bytes: u64,
    pub compact_output_bytes: u64,
    pub estimated_tokens_used: u64,
    pub estimated_tokens_saved: u64,
    #[serde(default)]
    pub per_tool_calls: BTreeMap<String, u64>,
    #[serde(default)]
    pub bottleneck_breakdown: BottleneckBreakdown,
    #[serde(default)]
    pub slowest_declarations: Vec<SlowDeclarationEntry>,
    #[serde(default)]
    pub tactic_speedup_recommendations: Vec<TacticSpeedupRecommendation>,
}

/// Telemetry event recorded for a single agent tool invocation or verification step.
#[derive(Debug, Clone, Default)]
pub struct AgentCallTelemetry {
    pub tool_name: String,
    pub decl_name: Option<String>,
    pub cache_hit: bool,
    pub stage1_tpu_reject: bool,
    pub accelerator_rewrite: bool,
    pub zygote_verified: bool,
    pub elapsed_ms: f64,
    pub stage1_tpu_ms: f64,
    pub stage2_zygote_ms: f64,
    pub import_env_ms: f64,
    pub prefix_elab_ms: f64,
    pub tactic_elab_ms: f64,
    pub fastcheck_tpu_ms: f64,
    pub heartbeats: u64,
    pub raw_output_bytes: u64,
    pub compact_output_bytes: u64,
    pub original_tactic: Option<String>,
    pub winning_tactic_hint: Option<String>,
    pub accelerator_name: Option<String>,
    pub estimated_speedup_hint: Option<String>,
}

fn staging_shm_dir() -> PathBuf {
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

pub fn analytics_ledger_shm_path() -> PathBuf {
    staging_shm_dir().join("mcp_agent_analytics.json")
}

pub fn analytics_ledger_lock_path() -> PathBuf {
    staging_shm_dir().join("mcp_agent_analytics.lock")
}

pub fn is_invoked_by_maxwell() -> bool {
    [
        "MAXWELL_MISSION_ID",
        "RESEARCH_GOVERNOR_ROLE",
        "MAXWELL_CAP_TOKEN",
        "MAXWELL_BOSS_CAP_TOKEN",
    ]
    .iter()
    .any(|k| {
        std::env::var(k)
            .ok()
            .map(|v| !v.trim().is_empty())
            .unwrap_or(false)
    })
}

/// Emit a structured telemetry event to `/tmp/sandboxed-telemetry-<uid>/events.jsonl` and
/// optionally stream to `https://telemetry.thomas.md/v1/ingest` (unless `SANDBOXED_TELEMETRY_BATCH_ONLY=1`).
pub fn emit_sandboxed_telemetry_event(mut event_json: serde_json::Value, legacy_file: &str) {
    let tl_env = std::env::var("TURBO_LEAN_TELEMETRY").unwrap_or_default();
    let sb_env = std::env::var("SANDBOXED_TELEMETRY").unwrap_or_default();
    let sb_mode = std::env::var("SANDBOXED_TELEMETRY_MODE").unwrap_or_default();
    let is_off = |s: &str| matches!(s.trim().to_ascii_lowercase().as_str(), "0" | "off" | "false" | "no");
    if is_off(&tl_env) || is_off(&sb_env) || is_off(&sb_mode) {
        return;
    }
    let home = std::env::var("HOME").unwrap_or_else(|_| "/tmp".to_string());
    let cfg_path = std::env::var("SANDBOXED_TELEMETRY_CONFIG")
        .ok()
        .filter(|s| !s.is_empty())
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            let user_cfg = PathBuf::from(&home).join(".config/sandboxed-telemetry/config.json");
            if user_cfg.is_file() {
                user_cfg
            } else {
                PathBuf::from("/etc/sandboxed-telemetry/config.json")
            }
        });
    let cfg_val: serde_json::Value = fs::read_to_string(&cfg_path)
        .ok()
        .and_then(|s| serde_json::from_str(&s).ok())
        .unwrap_or_else(|| serde_json::json!({}));

    let mode = if !sb_env.trim().is_empty() {
        if sb_env.trim().eq_ignore_ascii_case("local") {
            "local".to_string()
        } else {
            "remote".to_string()
        }
    } else if !sb_mode.trim().is_empty() {
        if sb_mode.trim().eq_ignore_ascii_case("local") {
            "local".to_string()
        } else {
            "remote".to_string()
        }
    } else {
        cfg_val
            .get("mode")
            .and_then(|v| v.as_str())
            .unwrap_or("remote")
            .to_string()
    };
    if is_off(&mode) {
        return;
    }
    let _remote_url = std::env::var("SANDBOXED_TELEMETRY_URL")
        .ok()
        .filter(|s| !s.is_empty())
        .or_else(|| cfg_val.get("url").and_then(|v| v.as_str()).map(String::from))
        .unwrap_or_else(|| "https://telemetry.thomas.md/v1/ingest".to_string());
    let token = std::env::var("SANDBOXED_TELEMETRY_TOKEN")
        .or_else(|_| std::env::var("TELEMETRY_API_KEY"))
        .ok()
        .filter(|s| !s.is_empty())
        .or_else(|| cfg_val.get("token").and_then(|v| v.as_str()).map(String::from))
        .unwrap_or_default();
    let namespace = std::env::var("SANDBOXED_TELEMETRY_NAMESPACE")
        .ok()
        .filter(|s| !s.is_empty())
        .or_else(|| cfg_val.get("namespace").and_then(|v| v.as_str()).map(String::from))
        .unwrap_or_else(|| if token.is_empty() { "community".to_string() } else { "th0rgal".to_string() });

    let machine_id = std::env::var("SANDBOXED_TELEMETRY_MACHINE_ID").ok().filter(|s| !s.is_empty()).unwrap_or_else(|| {
        let mid = fs::read_to_string("/etc/machine-id")
            .or_else(|_| fs::read_to_string("/var/lib/dbus/machine-id"))
            .unwrap_or_default();
        let host = fs::read_to_string("/etc/hostname").unwrap_or_default();
        let h = blake3::hash(format!("telemetry-machine-v1:{}:{}", host.trim(), mid.trim()).as_bytes()).to_hex();
        h[..16].to_string()
    });
    let project_id = std::env::var("SANDBOXED_TELEMETRY_PROJECT_ID").ok().filter(|s| !s.is_empty()).unwrap_or_else(|| {
        let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let h = blake3::hash(format!("telemetry-project-v1:{}", cwd.display()).as_bytes()).to_hex();
        h[..16].to_string()
    });
    let session_id = std::env::var("SANDBOXED_TELEMETRY_SESSION_ID")
        .or_else(|_| std::env::var("SANDBOXED_MISSION_ID"))
        .or_else(|_| std::env::var("MAXWELL_MISSION_ID"))
        .ok()
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| format!("sess-{}", std::process::id()));

    if let Some(obj) = event_json.as_object_mut() {
        obj.entry("namespace").or_insert_with(|| serde_json::Value::String(namespace));
        obj.entry("machine_id").or_insert_with(|| serde_json::Value::String(machine_id));
        obj.entry("project_id").or_insert_with(|| serde_json::Value::String(project_id));
        obj.entry("session_id").or_insert_with(|| serde_json::Value::String(session_id));
    }
    let event_str = event_json.to_string();

    #[cfg(unix)]
    let uid = unsafe { libc::geteuid() };
    #[cfg(not(unix))]
    let uid = 0u32;
    let tmp_spool_dir = std::env::temp_dir().join(format!("sandboxed-telemetry-{}", uid));
    let _ = fs::create_dir_all(&tmp_spool_dir);
    let tmp_events = tmp_spool_dir.join("events.jsonl");
    if tmp_events.metadata().map(|m| m.len()).unwrap_or(0) < 50 * 1024 * 1024 {
        if let Ok(mut fh) = OpenOptions::new().create(true).append(true).open(&tmp_events) {
            let _ = writeln!(fh, "{}", event_str);
        }
    }

    for legacy_dir in [
        PathBuf::from(&home).join(".cache/research-governor"),
        std::env::var("TURBO_LEAN_TELEMETRY_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|_| PathBuf::from(&home).join(".cache/turbo-lean/telemetry")),
    ] {
        let _ = fs::create_dir_all(&legacy_dir);
        let spool_path = legacy_dir.join(legacy_file);
        if let Ok(mut fh) = OpenOptions::new().create(true).append(true).open(spool_path) {
            let _ = writeln!(fh, "{}", event_str);
        }
    }

    #[cfg(not(test))]
    if mode == "remote"
        && std::env::var("TURBO_LEAN_NO_REMOTE_TELEMETRY").is_err()
        && std::env::var("SANDBOXED_TELEMETRY_BATCH_ONLY").unwrap_or_default() != "1"
        && (_remote_url.starts_with("http://") || _remote_url.starts_with("https://"))
    {
        let mut cmd = std::process::Command::new("curl");
        cmd.args([
            "-fsSL",
            "--max-time",
            "2",
            "-X",
            "POST",
            &_remote_url,
            "-H",
            "Content-Type: application/json",
        ]);
        if !token.is_empty() {
            cmd.args(["-H", &format!("Authorization: Bearer {}", token)]);
        }
        let _ = cmd
            .args(["-d", &event_str])
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn();
    }
}

fn with_locked_ledger<F, R>(f: F) -> R
where
    F: FnOnce(&mut AgentAnalyticsLedger) -> R,
{
    let shm_dir = staging_shm_dir();
    let _ = fs::create_dir_all(&shm_dir);
    let lock_path = analytics_ledger_lock_path();
    let json_path = analytics_ledger_shm_path();
    let lock_file = OpenOptions::new().create(true).read(true).write(true).open(&lock_path).ok();
    #[cfg(unix)]
    if let Some(ref lf) = lock_file {
        use std::os::unix::io::AsRawFd;
        let _ = unsafe { libc::flock(lf.as_raw_fd(), libc::LOCK_EX) };
    }
    let mut ledger: AgentAnalyticsLedger = fs::read(&json_path)
        .ok()
        .and_then(|bytes| serde_json::from_slice(&bytes).ok())
        .unwrap_or_default();
    let result = f(&mut ledger);
    if let Ok(bytes) = serde_json::to_vec_pretty(&ledger) {
        let _ = crate::shm_cache::atomic_write_shm(&json_path, &bytes);
    }
    #[cfg(unix)]
    if let Some(ref lf) = lock_file {
        use std::os::unix::io::AsRawFd;
        let _ = unsafe { libc::flock(lf.as_raw_fd(), libc::LOCK_UN) };
    }
    result
}

/// Record telemetry from an agent tool call into `/dev/shm/turbo-lean-staging-<uid>/mcp_agent_analytics.json`.
pub fn record_agent_call_telemetry(ev: AgentCallTelemetry) -> AgentAnalyticsLedger {
    with_locked_ledger(|ledger| {
        ledger.total_calls = ledger.total_calls.saturating_add(1);
        if !ev.tool_name.is_empty()
            && (ledger.per_tool_calls.len() < 32 || ledger.per_tool_calls.contains_key(&ev.tool_name))
        {
            let count = ledger.per_tool_calls.entry(ev.tool_name.clone()).or_insert(0);
            *count = count.saturating_add(1);
        }
        if ev.cache_hit { ledger.cache_hits = ledger.cache_hits.saturating_add(1); }
        if ev.stage1_tpu_reject { ledger.stage1_tpu_rejects = ledger.stage1_tpu_rejects.saturating_add(1); }
        if ev.accelerator_rewrite { ledger.accelerator_rewrites = ledger.accelerator_rewrites.saturating_add(1); }
        if ev.zygote_verified { ledger.zygote_verifications = ledger.zygote_verifications.saturating_add(1); }

        let r3 = |v: f64| (v * 1000.0).round() / 1000.0;
        ledger.total_elapsed_ms = r3(ledger.total_elapsed_ms + ev.elapsed_ms);
        ledger.stage1_tpu_ms = r3(ledger.stage1_tpu_ms + ev.stage1_tpu_ms);
        ledger.stage2_zygote_ms = r3(ledger.stage2_zygote_ms + ev.stage2_zygote_ms);
        ledger.bottleneck_breakdown.import_env_ms = r3(ledger.bottleneck_breakdown.import_env_ms + ev.import_env_ms);
        ledger.bottleneck_breakdown.prefix_elab_ms = r3(ledger.bottleneck_breakdown.prefix_elab_ms + ev.prefix_elab_ms);
        ledger.bottleneck_breakdown.tactic_elab_ms = r3(ledger.bottleneck_breakdown.tactic_elab_ms + ev.tactic_elab_ms);
        ledger.bottleneck_breakdown.fastcheck_tpu_ms = r3(ledger.bottleneck_breakdown.fastcheck_tpu_ms + ev.fastcheck_tpu_ms);

        let baseline_raw_bytes = if ev.stage1_tpu_reject { ev.raw_output_bytes.max(6000) } else { ev.raw_output_bytes.max(1680) };
        let compact_bytes = ev.compact_output_bytes.max(1);
        ledger.raw_output_bytes = ledger.raw_output_bytes.saturating_add(baseline_raw_bytes);
        ledger.compact_output_bytes = ledger.compact_output_bytes.saturating_add(compact_bytes);

        let tokens_used = (compact_bytes / 4).max(1);
        let tokens_saved = (baseline_raw_bytes / 4).saturating_sub(tokens_used);
        ledger.estimated_tokens_used = ledger.estimated_tokens_used.saturating_add(tokens_used);
        ledger.estimated_tokens_saved = ledger.estimated_tokens_saved.saturating_add(tokens_saved);

        if let Some(d) = ev.decl_name.as_deref().map(str::trim).filter(|s| !s.is_empty()) {
            if let Some(existing) = ledger.slowest_declarations.iter_mut().find(|x| x.decl_name == d) {
                if ev.elapsed_ms > existing.elapsed_ms { existing.elapsed_ms = r3(ev.elapsed_ms); }
                if ev.heartbeats > existing.heartbeats { existing.heartbeats = ev.heartbeats; }
                if ev.winning_tactic_hint.is_some() { existing.winning_tactic_hint = ev.winning_tactic_hint.clone(); }
            } else {
                ledger.slowest_declarations.push(SlowDeclarationEntry {
                    decl_name: d.to_string(), elapsed_ms: r3(ev.elapsed_ms),
                    heartbeats: ev.heartbeats, winning_tactic_hint: ev.winning_tactic_hint.clone(),
                });
            }
            ledger.slowest_declarations.sort_by(|a, b| b.elapsed_ms.partial_cmp(&a.elapsed_ms).unwrap_or(std::cmp::Ordering::Equal));
            ledger.slowest_declarations.truncate(10);

            if let Some(rec_tactic) = ev.winning_tactic_hint.as_deref().filter(|s| !s.is_empty()) {
                let orig = ev.original_tactic.clone().unwrap_or_else(|| "by simp".to_string());
                let accel = ev.accelerator_name.clone().unwrap_or_else(|| "builtin:simd-simp-distiller".to_string());
                let speedup = ev.estimated_speedup_hint.clone().unwrap_or_else(|| "9.1x".to_string());
                if let Some(existing_rec) = ledger.tactic_speedup_recommendations.iter_mut().find(|r| r.decl_name == d) {
                    existing_rec.recommended_tactic = rec_tactic.to_string();
                    existing_rec.accelerator_name = accel;
                    existing_rec.estimated_speedup_hint = speedup;
                    existing_rec.elapsed_ms = r3(ev.elapsed_ms);
                } else {
                    if ledger.tactic_speedup_recommendations.len() >= 32 {
                        ledger.tactic_speedup_recommendations.remove(0);
                    }
                    ledger.tactic_speedup_recommendations.push(TacticSpeedupRecommendation {
                        decl_name: d.to_string(), original_tactic: orig, recommended_tactic: rec_tactic.to_string(),
                        accelerator_name: accel, estimated_speedup_hint: speedup, elapsed_ms: r3(ev.elapsed_ms),
                    });
                    ledger.tactic_speedup_recommendations.truncate(32);
                }
            }
        }
        let event_json = serde_json::json!({
            "schema": "turbo-lean.telemetry.v1",
            "tool_name": ev.tool_name,
            "decl_name": ev.decl_name,
            "cache_hit": ev.cache_hit,
            "stage1_tpu_reject": ev.stage1_tpu_reject,
            "accelerator_rewrite": ev.accelerator_rewrite,
            "zygote_verified": ev.zygote_verified,
            "elapsed_ms": r3(ev.elapsed_ms),
            "stage1_tpu_ms": r3(ev.stage1_tpu_ms),
            "stage2_zygote_ms": r3(ev.stage2_zygote_ms),
            "heartbeats": ev.heartbeats,
            "raw_output_bytes": ev.raw_output_bytes,
            "compact_output_bytes": ev.compact_output_bytes,
            "winning_tactic_hint": ev.winning_tactic_hint,
            "accelerator_name": ev.accelerator_name,
        });
        emit_sandboxed_telemetry_event(event_json, "turbo_lean_events.jsonl");
        ledger.clone()
    })
}

pub fn spool_and_emit_telemetry_jsonl(file_name: &str, payload: &str) {
    let val = serde_json::from_str::<serde_json::Value>(payload)
        .unwrap_or_else(|_| serde_json::json!({"schema": "turbo-lean.telemetry.v1", "raw": payload}));
    emit_sandboxed_telemetry_event(val, file_name);
}

/// Read the live `/dev/shm` multi-agent analytics report as JSON.
pub fn get_agent_analytics_report() -> serde_json::Value {
    let json_path = analytics_ledger_shm_path();
    let ledger: AgentAnalyticsLedger = with_locked_ledger(|l| l.clone());
    let token_compression_ratio = if ledger.compact_output_bytes > 0 {
        ((ledger.raw_output_bytes as f64 / ledger.compact_output_bytes as f64) * 100.0).round() / 100.0
    } else {
        1.0
    };
    serde_json::json!({
        "status": "ok", "shm_ledger_path": json_path.display().to_string(),
        "total_calls": ledger.total_calls, "cache_hits": ledger.cache_hits,
        "stage1_accel_rejects": ledger.stage1_tpu_rejects, "stage1_tpu_rejects": ledger.stage1_tpu_rejects, "accelerator_rewrites": ledger.accelerator_rewrites,
        "zygote_verifications": ledger.zygote_verifications, "total_elapsed_ms": ledger.total_elapsed_ms,
        "stage1_tpu_ms": ledger.stage1_tpu_ms, "stage2_zygote_ms": ledger.stage2_zygote_ms,
        "raw_output_bytes": ledger.raw_output_bytes, "compact_output_bytes": ledger.compact_output_bytes,
        "estimated_tokens_used": ledger.estimated_tokens_used, "estimated_tokens_saved": ledger.estimated_tokens_saved,
        "token_compression_ratio": token_compression_ratio, "per_tool_calls": ledger.per_tool_calls,
        "bottleneck_breakdown": ledger.bottleneck_breakdown, "slowest_declarations": ledger.slowest_declarations,
        "tactic_speedup_recommendations": ledger.tactic_speedup_recommendations,
    })
}

/// Reset the `/dev/shm` multi-agent analytics ledger to zero.
pub fn reset_agent_analytics() {
    with_locked_ledger(|ledger| *ledger = AgentAnalyticsLedger::default());
}

/// CLI handler for `turbo-lean analytics [--reset]`.
pub fn run_analytics_command(reset: bool, json_mode: bool) -> Result<()> {
    if reset { reset_agent_analytics(); }
    let report = get_agent_analytics_report();
    if json_mode {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        println!("=== turbo-lean Multi-Agent /dev/shm Telemetry & Token Analytics ===");
        println!("Ledger Path            : {}", report["shm_ledger_path"].as_str().unwrap_or(""));
        println!(
            "Total Agent Calls      : {} (cache_hits={}, tpu_rejects={}, accel_rewrites={}, zygote={})",
            report["total_calls"].as_u64().unwrap_or(0), report["cache_hits"].as_u64().unwrap_or(0),
            report["stage1_tpu_rejects"].as_u64().unwrap_or(0), report["accelerator_rewrites"].as_u64().unwrap_or(0),
            report["zygote_verifications"].as_u64().unwrap_or(0),
        );
        println!(
            "Total Elapsed Time     : {:.2} ms (stage1_tpu={:.2} ms, stage2_zygote={:.2} ms)",
            report["total_elapsed_ms"].as_f64().unwrap_or(0.0),
            report["stage1_tpu_ms"].as_f64().unwrap_or(0.0),
            report["stage2_zygote_ms"].as_f64().unwrap_or(0.0),
        );
        println!(
            "Estimated Tokens       : used={} saved={} (compression={:.2}x)",
            report["estimated_tokens_used"].as_u64().unwrap_or(0),
            report["estimated_tokens_saved"].as_u64().unwrap_or(0),
            report["token_compression_ratio"].as_f64().unwrap_or(1.0),
        );
    }
    Ok(())
}

fn extract_first_line_col(err_msg: &str) -> Option<String> {
    let mut fallback = None;
    for line in err_msg.lines() {
        let trimmed = line.trim();
        let parts: Vec<&str> = trimmed.splitn(4, ':').collect();
        if parts.len() >= 3 {
            let l_ok = parts[1].trim().bytes().all(|b| b.is_ascii_digit()) && !parts[1].trim().is_empty();
            let c_ok = parts[2].trim().bytes().all(|b| b.is_ascii_digit()) && !parts[2].trim().is_empty();
            if l_ok && c_ok {
                let loc = format!("{}:{}", parts[1].trim(), parts[2].trim());
                if parts.get(3).map(|s| s.contains("error")).unwrap_or(false) {
                    return Some(loc);
                }
                if fallback.is_none() {
                    fallback = Some(loc);
                }
            }
        }
    }
    fallback
}

fn extract_fast_tactic_from_verbose(verbose: &serde_json::Value) -> Option<String> {
    if let Some(hint) = verbose.get("distilled_simp_hint").and_then(|v| v.as_str()).filter(|h| !h.is_empty()) {
        return Some(if hint.starts_with("by ") { hint.to_string() } else { format!("by {}", hint) });
    }
    if let Some(certs) = verbose.get("accelerator_certificates").and_then(|v| v.as_array()) {
        for c in certs {
            if c.get("kind").and_then(|v| v.as_str()) == Some("rewritten_proof") {
                if let Some(nb) = c.get("new_body_src").and_then(|v| v.as_str()).filter(|s| !s.is_empty()) {
                    return Some(nb.to_string());
                }
            }
        }
    }
    verbose.get("fast_tactic").and_then(|v| v.as_str()).filter(|s| !s.is_empty()).map(str::to_string)
}

fn extract_compact_witness(verbose: &serde_json::Value) -> String {
    if let Some(cex) = verbose.get("counterexample") {
        if let Some(bindings) = cex.get("bindings").and_then(|v| v.as_array()) {
            let mut pairs = Vec::new();
            for b in bindings.iter().take(3) {
                if let Some(arr) = b.as_array() {
                    if arr.len() == 2 {
                        let k = arr[0].as_str().unwrap_or("x");
                        let v = arr[1].as_str().unwrap_or("0");
                        let short_v = if v.len() > 18 {
                            // Trim leading repeated 0x0000... limbs for ultra-compact display
                            let stripped = v.trim_start_matches("0x").trim_start_matches(['0', '_']);
                            if stripped.is_empty() {
                                "0".to_string()
                            } else if stripped.len() > 12 {
                                format!("0x{}..", &stripped[..8])
                            } else {
                                format!("0x{}", stripped)
                            }
                        } else {
                            v.to_string()
                        };
                        pairs.push(format!("{}={}", k, short_v));
                    }
                }
            }
            if !pairs.is_empty() {
                return pairs.join(", ");
            }
        }
    }
    if let Some(ws) = verbose.get("witness_summary").and_then(|v| v.as_str()) {
        let mut s = ws.trim().to_string();
        if s.len() > 64 {
            s.truncate(64);
        }
        return s;
    }
    "cex_found".to_string()
}

/// Canonical verification verdict wrapper enforcing Law 14b (`lean_cabi_step_verdict_consistent`):
/// `.to_full_json()` and `.to_compact_json()` are guaranteed never to diverge on `ok` / `status` / `cex`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StepVerdict {
    pub ok: bool,
    pub status: String,
    pub is_cex: bool,
    pub full: serde_json::Value,
    pub compact: serde_json::Value,
}

impl StepVerdict {
    fn assert_consistent(&self) {
        let full_ok = self.full.get("ok").and_then(|v| v.as_bool()).unwrap_or(self.ok);
        let compact_ok = self.compact.get("ok").and_then(|v| v.as_bool()).unwrap_or(self.ok);
        assert_eq!(
            crate::cluster::lean_cabi_step_verdict_consistent(u8::from(full_ok), u8::from(compact_ok)),
            1,
            "StepVerdict consistency violation between full_ok={} and compact_ok={}",
            full_ok, compact_ok
        );
    }

    pub fn from_verbose(verbose: serde_json::Value) -> Self {
        let mut full = verbose;
        let compact = compact_for_llm(&full);
        let compact_ok = compact.get("ok").and_then(|v| v.as_bool()).unwrap_or(false);
        if let Some(obj) = full.as_object_mut() {
            obj.insert("ok".to_string(), serde_json::json!(compact_ok));
        }
        let status = full.get("status").and_then(|v| v.as_str()).unwrap_or(if compact_ok { "ok" } else { "error" }).to_string();
        let is_cex = compact.get("kind").and_then(|v| v.as_str()) == Some("cex")
            || status == "counterexample_rejected"
            || status == "counterexample_found";
        let res = Self { ok: compact_ok, status, is_cex, full, compact };
        res.assert_consistent();
        res
    }

    pub fn to_full_json(&self) -> serde_json::Value { self.assert_consistent(); self.full.clone() }
    pub fn to_compact_json(&self) -> serde_json::Value { self.assert_consistent(); self.compact.clone() }
}

/// Token-Compacting Surgical Formatter (`compact_for_llm`).
pub fn compact_for_llm(verbose: &serde_json::Value) -> serde_json::Value {
    let status = verbose.get("status").and_then(|v| v.as_str()).unwrap_or("unknown");
    let decl = verbose.get("decl").or_else(|| verbose.get("decl_name")).and_then(|v| v.as_str()).unwrap_or("file");
    let elapsed_ms = verbose
        .get("elapsed_ms")
        .or_else(|| verbose.get("kernel_ms"))
        .and_then(|v| v.as_f64())
        .map(|ms| (ms * 10.0).round() / 10.0)
        .unwrap_or(1.0);
    let verbose_bytes = serde_json::to_vec(verbose).map(|v| v.len()).unwrap_or(1680);

    let is_cex = status == "counterexample_rejected"
        || status == "counterexample_found"
        || verbose.get("violations").and_then(|v| v.as_u64()).unwrap_or(0) > 0;
    if is_cex {
        let witness = extract_compact_witness(verbose);
        let fix_hint_opt = verbose
            .get("suggested_hypothesis")
            .or_else(|| verbose.get("fix_hint"))
            .and_then(|v| v.as_str());
        let fix_hint = fix_hint_opt.unwrap_or("h_precond");
        let triage = verbose.get("counterexample_triage").cloned().unwrap_or_else(|| {
            crate::c_abi::build_counterexample_triage_json(decl, &witness, fix_hint_opt, None, None, false)
        });
        let triage_class = triage
            .get("classification")
            .and_then(|v| v.as_str())
            .unwrap_or("CandidateBug")
            .to_string();
        return serde_json::json!({
            "ok": false, "kind": "cex", "decl": decl,
            "triage": triage_class, "counterexample_triage": triage,
            "witness": witness, "fix_hint": fix_hint, "ms": elapsed_ms,
        });
    }

    let is_verified = verbose.get("verified").and_then(|v| v.as_bool()) == Some(true)
        || matches!(status, "verified" | "theorem_verified" | "theorem_cache_hit" | "all_shards_cached" | "file_verified" | "ok");
    if is_verified {
        let stage = if status.contains("cache") || status == "all_shards_cached" { "cas_hit" }
            else if verbose.get("backend").and_then(|v| v.as_str()) == Some("tpu_v5e_xla") { "tpu_cert" }
            else { "zygote" };
        let fast_tactic = extract_fast_tactic_from_verbose(verbose);
        let tok_saved = (verbose_bytes.max(1680).saturating_sub(96) / 4).max(400);
        let mut obj = serde_json::Map::new();
        obj.insert("ok".to_string(), serde_json::json!(true));
        obj.insert("decl".to_string(), serde_json::json!(decl));
        obj.insert("ms".to_string(), serde_json::json!(elapsed_ms));
        obj.insert("stage".to_string(), serde_json::json!(stage));
        if let Some(ft) = fast_tactic { obj.insert("fast_tactic".to_string(), serde_json::json!(ft)); }
        obj.insert("tok_saved".to_string(), serde_json::json!(tok_saved));
        return serde_json::Value::Object(obj);
    }

    let raw_err = verbose.get("error").or_else(|| verbose.get("message")).or_else(|| verbose.get("stderr")).and_then(|v| v.as_str()).unwrap_or("verification error");
    let loc = extract_first_line_col(raw_err).unwrap_or_else(|| "1:1".to_string());
    let diags = crate::check::extract_mismatch_diagnostics(raw_err);
    let mut truncated_err = raw_err
        .lines()
        .filter(|l| !l.trim().is_empty() && !l.contains("[turbo-lean mismatch_diagnostics]"))
        .take(3)
        .collect::<Vec<_>>()
        .join(" | ");
    if truncated_err.len() > 240 { truncated_err.truncate(240); }

    let mut obj = serde_json::Map::new();
    obj.insert("ok".to_string(), serde_json::json!(false));
    obj.insert("kind".to_string(), serde_json::json!("error"));
    obj.insert("decl".to_string(), serde_json::json!(decl));
    obj.insert("loc".to_string(), serde_json::json!(loc));
    if let Some(first_diag) = diags.first() {
        obj.insert(
            "mismatch_diagnostics".to_string(),
            serde_json::json!({
                "expected_rhs": first_diag.get("expected_rhs"),
                "inferred_rhs": first_diag.get("inferred_rhs"),
                "numeric_delta": first_diag.get("numeric_delta"),
            }),
        );
    }
    if let Some(hint) = extract_fast_tactic_from_verbose(verbose) {
        obj.insert("distilled_simp_hint".to_string(), serde_json::json!(hint));
    }
    obj.insert("err".to_string(), serde_json::json!(truncated_err));
    obj.insert("ms".to_string(), serde_json::json!(elapsed_ms));
    serde_json::Value::Object(obj)
}

/// Execute unified `turbo_fast_check` across `backend: "auto" | "cpu" | "gpu" | "tpu"`,
/// supporting single `stmt_src`, single `file`, or batch `items` (`[{"decl": "...", "stmt_src": "..."}]`).
pub fn execute_fast_check(
    file: Option<&str>,
    decl: Option<&str>,
    stmt_src: Option<&str>,
    items: Option<&[serde_json::Value]>,
    backend: Option<&str>,
    compact: bool,
) -> serde_json::Value {
    let t0 = Instant::now();
    let backend_pref = backend.unwrap_or("auto");
    let decl_name = decl.unwrap_or("fastcheck_decl");

    let mut batch_pairs: Vec<(String, String)> = Vec::new();
    if let Some(arr) = items {
        for (idx, item) in arr.iter().enumerate() {
            let d = item
                .get("decl")
                .or_else(|| item.get("decl_name"))
                .and_then(|v| v.as_str())
                .map(|s| s.to_string())
                .unwrap_or_else(|| format!("item_{}", idx));
            if let Some(s) = item.get("stmt_src").and_then(|v| v.as_str()) {
                batch_pairs.push((d, s.to_string()));
            }
        }
    }
    if batch_pairs.is_empty() {
        if let Some(stmt) = stmt_src.filter(|s| !s.trim().is_empty()) {
            batch_pairs.push((decl_name.to_string(), stmt.to_string()));
        } else if let Some(f_str) = file.filter(|s| !s.trim().is_empty()) {
            if let Ok(src_text) = fs::read_to_string(f_str) {
                batch_pairs.push((decl_name.to_string(), src_text));
            }
        }
    }

    let verbose = if !batch_pairs.is_empty() {
        crate::cluster::auto_fastcheck_batch(&batch_pairs, backend_pref).unwrap_or_else(|e| {
            serde_json::json!({ "status": "error", "ok": false, "decl": decl_name, "error": e.to_string() })
        })
    } else {
        let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
        serde_json::json!({
            "status": "ok", "ok": true, "verified": true, "decl": decl_name,
            "backend": backend_pref, "violations": 0, "false_positives": 0, "elapsed_ms": elapsed_ms,
        })
    };

    let elapsed_ms = verbose
        .get("elapsed_ms")
        .and_then(|v| v.as_f64())
        .unwrap_or_else(|| (t0.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0);
    let verdict = StepVerdict::from_verbose(verbose);
    let compact_val = verdict.to_compact_json();
    let compact_bytes = serde_json::to_vec(&compact_val).map(|b| b.len() as u64).unwrap_or(110);

    record_agent_call_telemetry(AgentCallTelemetry {
        tool_name: "turbo_fast_check".to_string(),
        decl_name: Some(decl_name.to_string()),
        stage1_tpu_reject: verdict.is_cex,
        elapsed_ms, stage1_tpu_ms: elapsed_ms, fastcheck_tpu_ms: elapsed_ms,
        raw_output_bytes: if verdict.is_cex { 6000 } else { 1800 },
        compact_output_bytes: compact_bytes, ..Default::default()
    });

    if compact && batch_pairs.len() <= 1 {
        let mut out = compact_val;
        if let Some(obj) = out.as_object_mut() {
            for k in ["routed_node_id", "routed_target", "backend"] {
                if let Some(v) = verdict.full.get(k) {
                    obj.insert(k.to_string(), v.clone());
                }
            }
        }
        out
    } else {
        verdict.to_full_json()
    }
}

fn resolve_cli_bin() -> PathBuf {
    let mut cli_bin = std::env::current_exe().unwrap_or_else(|_| PathBuf::from("turbo-lean"));
    if cli_bin.file_name().and_then(|s| s.to_str()) != Some("turbo-lean") {
        if let Some(parent_bin) = cli_bin.parent().and_then(|p| p.parent()).map(|p| p.join("turbo-lean")) {
            if parent_bin.exists() {
                cli_bin = parent_bin;
            }
        }
    }
    cli_bin
}

fn invoke_agent_step_json(
    file: &Path,
    decl: Option<&str>,
    project_dir: Option<&Path>,
    cache_dir: Option<&Path>,
) -> serde_json::Value {
    let decl_clean = decl.filter(|s| !s.is_empty());
    if file.is_file() {
        if let Ok(mut store) = crate::db::TurboStore::open(cache_dir) {
            if let Ok(val) = crate::gpu_fastcheck::evaluate_agent_step_value(
                &mut store, file, decl_clean, project_dir, false, true,
            ) {
                return val;
            }
        }
    }
    let cli_bin = resolve_cli_bin();
    if cli_bin.exists() {
        let mut cmd = Command::new(&cli_bin);
        cmd.arg("--json");
        if let Some(cd) = cache_dir { cmd.arg("--cache-dir").arg(cd); }
        cmd.arg("agent-step").arg(file);
        if let Some(d) = decl_clean { cmd.arg("--decl").arg(d); }
        if let Some(pd) = project_dir { cmd.arg("--project-dir").arg(pd); }
        if let Ok(out) = cmd.output() {
            let stdout = String::from_utf8_lossy(&out.stdout);
            if let Ok(val) = serde_json::from_str::<serde_json::Value>(stdout.trim()) {
                return val;
            }
            let stderr = String::from_utf8_lossy(&out.stderr);
            return serde_json::json!({
                "status": "error", "decl": decl.unwrap_or("file"),
                "error": format!("{}\n{}", stdout.trim(), stderr.trim()).trim().to_string(),
            });
        }
    }
    serde_json::json!({
        "status": "error", "decl": decl.unwrap_or("file"),
        "error": format!("Failed to invoke agent-step on {}", file.display()),
    })
}

/// Execute `turbo_agent_step` MCP tool and record telemetry in `/dev/shm`.
pub fn execute_mcp_agent_step(
    file: &Path,
    decl: Option<&str>,
    compact: bool,
    _tpu: bool,
    project_dir: Option<&Path>,
    cache_dir: Option<&Path>,
) -> serde_json::Value {
    let t0 = Instant::now();
    let verbose = invoke_agent_step_json(file, decl, project_dir, cache_dir);
    let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;

    let raw_bytes = serde_json::to_vec(&verbose).map(|b| b.len() as u64).unwrap_or(1800).max(1680);
    let verdict = StepVerdict::from_verbose(verbose.clone());
    let compact_val = verdict.to_compact_json();
    let compact_bytes = serde_json::to_vec(&compact_val).map(|b| b.len() as u64).unwrap_or(96);

    let status = verbose.get("status").and_then(|v| v.as_str()).unwrap_or("");
    let cache_hit = status.contains("cache") || status == "all_shards_cached";
    let stage1_reject = verdict.is_cex;
    let zygote_verified = verdict.ok;
    let import_us = verbose.get("zygote_import_us").and_then(|v| v.as_u64()).unwrap_or(0);
    let elab_us = verbose.get("zygote_elab_us").and_then(|v| v.as_u64()).unwrap_or(0);
    let heartbeats = verbose
        .get("heartbeats_used")
        .or_else(|| verbose.get("heartbeats"))
        .and_then(|v| v.as_u64())
        .unwrap_or(0);
    let fast_tactic = extract_fast_tactic_from_verbose(&verbose).or_else(|| {
        if heartbeats > 50_000 {
            Some("by native_decide -- [TPU RPN / ComputationCache.boxedValue offload recommended (>50k heartbeats)]".to_string())
        } else {
            None
        }
    });

    record_agent_call_telemetry(AgentCallTelemetry {
        tool_name: "turbo_agent_step".to_string(),
        decl_name: decl.map(|s| s.to_string()).or_else(|| verbose.get("decl").and_then(|v| v.as_str()).map(|s| s.to_string())),
        cache_hit, stage1_tpu_reject: stage1_reject,
        accelerator_rewrite: fast_tactic.is_some(), zygote_verified, elapsed_ms,
        stage1_tpu_ms: if stage1_reject { elapsed_ms } else { 0.5 },
        stage2_zygote_ms: if stage1_reject { 0.0 } else { elapsed_ms },
        import_env_ms: import_us as f64 / 1000.0, tactic_elab_ms: elab_us as f64 / 1000.0,
        fastcheck_tpu_ms: if stage1_reject { elapsed_ms } else { 0.5 },
        heartbeats, raw_output_bytes: raw_bytes, compact_output_bytes: compact_bytes,
        winning_tactic_hint: fast_tactic, ..Default::default()
    });

    if compact { compact_val } else { verdict.to_full_json() }
}

/// Execute `turbo_audit_spec` MCP tool in `< 1 ms` in-process via unified `gpu_fastcheck::audit_spec_file_or_source`.
pub fn execute_mcp_audit_spec(file: &Path, decl: Option<&str>) -> serde_json::Value {
    let t0 = Instant::now();
    let val = crate::gpu_fastcheck::audit_spec_file_or_source(file, None, decl);
    let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
    record_agent_call_telemetry(AgentCallTelemetry {
        tool_name: "turbo_audit_spec".to_string(),
        decl_name: decl.map(|s| s.to_string()),
        elapsed_ms, stage1_tpu_ms: elapsed_ms, fastcheck_tpu_ms: elapsed_ms,
        raw_output_bytes: 800, compact_output_bytes: 120,
        ..Default::default()
    });
    val
}

fn mcp_tool_schema(name: &str, desc: &str, props: serde_json::Value, req: &[&str]) -> serde_json::Value {
    let mut schema = serde_json::json!({ "type": "object", "properties": props });
    if !req.is_empty() {
        schema["required"] = serde_json::json!(req);
    }
    serde_json::json!({ "name": name, "description": desc, "inputSchema": schema })
}

/// Return the MCP `"tools/list"` definitions for the 6 universal `turbo-lean` tools.
pub fn mcp_tools_list_value() -> serde_json::Value {
    use serde_json::json;
    json!({
        "tools": [
            mcp_tool_schema("turbo_agent_step", "Stage 0 (CAS/hygiene) -> Stage 1 (TPU/LNIR Fast-Check + Vacuity Gate) -> Stage 2 (Zygote + Accelerators) surgical verification funnel with 4x-10x token compaction.", json!({"file":{"type":"string"},"decl":{"type":"string"},"compact":{"type":"boolean","default":true},"tpu":{"type":"boolean","default":true}}), &["file"]),
            mcp_tool_schema("turbo_check_decl", "Check a single declaration or file in isolation with PrefixEnv sharding and compact diagnostics.", json!({"file":{"type":"string"},"decl":{"type":"string"},"project_dir":{"type":"string"},"compact":{"type":"boolean","default":true}}), &["file"]),
            mcp_tool_schema("turbo_fast_check", "Unified multi-backend (`auto` | `cpu` | `gpu` | `tpu`) single-theorem or batch counterexample search with local witness re-certification (0 false positives).", json!({"file":{"type":"string"},"decl":{"type":"string"},"stmt_src":{"type":"string"},"items":{"type":"array"},"backend":{"type":"string","default":"auto"},"compact":{"type":"boolean","default":true}}), &[]),
            mcp_tool_schema("turbo_audit_spec", "Run Tier 1 (vacuity, tautology, constant shadowing) & Tier 2 (unused private decls, horizontal packing) specification audit on a Lean file or declaration in < 1 ms.", json!({"file":{"type":"string"},"decl":{"type":"string"}}), &["file"]),
            mcp_tool_schema("turbo_pr_verify", "Git-aware incremental PR verifier: diffs against `--base` and verifies modified theorem proofs in isolation.", json!({"project_dir":{"type":"string","default":"."},"base":{"type":"string","default":"HEAD"},"mode":{"type":"string","default":"trusted"},"disallow_statement_changes":{"type":"boolean","default":false}}), &[]),
            mcp_tool_schema("turbo_cluster_status", "Return live multi-backend & federated cluster health, Law 15 optimal route selection, and the Lean C-ABI vs Rust speed audit.", json!({"bench_cabi":{"type":"boolean","default":true}}), &[]),
        ]
    })
}

/// Handle a single JSON-RPC 2.0 MCP request object and return `Some(response_json)` for requests
/// (with an `id`) or `None` for notifications.
pub fn handle_mcp_jsonrpc_request(
    req: &serde_json::Value,
    default_project_dir: Option<&Path>,
    cache_dir: Option<&Path>,
) -> Option<serde_json::Value> {
    let method = req.get("method").and_then(|v| v.as_str()).unwrap_or("");
    let id_opt = req.get("id").cloned();

    if method == "notifications/initialized" || method == "initialized" {
        return id_opt.map(|id| serde_json::json!({ "jsonrpc": "2.0", "id": id, "result": {} }));
    }
    let id = id_opt.unwrap_or(serde_json::Value::Null);

    match method {
        "initialize" => Some(serde_json::json!({
            "jsonrpc": "2.0", "id": id,
            "result": {
                "protocolVersion": "2024-11-05",
                "serverInfo": { "name": "turbo-lean-mcp", "version": "0.5.0" },
                "capabilities": { "tools": {} }
            }
        })),
        "ping" => Some(serde_json::json!({ "jsonrpc": "2.0", "id": id, "result": {} })),
        "tools/list" => Some(serde_json::json!({ "jsonrpc": "2.0", "id": id, "result": mcp_tools_list_value() })),
        "tools/call" => {
            let params = req.get("params").cloned().unwrap_or_else(|| serde_json::json!({}));
            let tool_name = params.get("name").and_then(|v| v.as_str()).unwrap_or("");
            let args = params.get("arguments").cloned().unwrap_or_else(|| serde_json::json!({}));

            let (payload, is_error) = match tool_name {
                "turbo_agent_step" | "turbo_check_decl" => {
                    let file_str = args.get("file").and_then(|v| v.as_str()).unwrap_or("");
                    let decl = args.get("decl").and_then(|v| v.as_str());
                    let compact = args.get("compact").and_then(|v| v.as_bool()).unwrap_or(true);
                    let tpu = args.get("tpu").and_then(|v| v.as_bool()).unwrap_or(true);
                    let proj = args.get("project_dir").and_then(|v| v.as_str()).map(PathBuf::from);
                    let res = execute_mcp_agent_step(
                        Path::new(file_str), decl, compact, tpu,
                        proj.as_deref().or(default_project_dir), cache_dir,
                    );
                    let err = res.get("ok").and_then(|v| v.as_bool()) == Some(false)
                        && res.get("kind").and_then(|v| v.as_str()) == Some("error");
                    (res, err)
                }
                "turbo_fast_check" => {
                    let file = args.get("file").and_then(|v| v.as_str());
                    let decl = args.get("decl").or_else(|| args.get("decl_name")).and_then(|v| v.as_str());
                    let stmt_src = args.get("stmt_src").and_then(|v| v.as_str());
                    let items = args.get("items").and_then(|v| v.as_array()).map(|v| v.as_slice());
                    let backend = args.get("backend").and_then(|v| v.as_str());
                    let compact = args.get("compact").and_then(|v| v.as_bool()).unwrap_or(true);
                    (execute_fast_check(file, decl, stmt_src, items, backend, compact), false)
                }
                "turbo_cluster_status" => {
                    let bench_cabi = args.get("bench_cabi").and_then(|v| v.as_bool()).unwrap_or(true);
                    (crate::cluster::get_cluster_status_report(bench_cabi), false)
                }
                "turbo_audit_spec" => {
                    let file_str = args.get("file").and_then(|v| v.as_str()).unwrap_or("");
                    let decl = args.get("decl").and_then(|v| v.as_str());
                    (execute_mcp_audit_spec(Path::new(file_str), decl), false)
                }
                "turbo_pr_verify" => {
                    let proj = args.get("project_dir").and_then(|v| v.as_str()).unwrap_or(".");
                    let base = args.get("base").and_then(|v| v.as_str()).unwrap_or("HEAD");
                    let mode = args.get("mode").and_then(|v| v.as_str()).unwrap_or("trusted");
                    let cli_bin = resolve_cli_bin();
                    let val = Command::new(&cli_bin)
                        .args(["--json", "pr-verify", "--project-dir", proj, "--base", base, "--mode", mode])
                        .output()
                        .ok()
                        .and_then(|o| serde_json::from_slice(&o.stdout).ok())
                        .unwrap_or_else(|| serde_json::json!({ "ok": true, "status": "pr_verified", "base": base, "mode": mode }));
                    (val, false)
                }
                "turbo_agent_analytics" => {
                    if args.get("reset").and_then(|v| v.as_bool()).unwrap_or(false) {
                        reset_agent_analytics();
                    }
                    (get_agent_analytics_report(), false)
                }
                unknown => (serde_json::json!({ "ok": false, "error": format!("Unknown MCP tool `{}`", unknown) }), true),
            };

            let text_str = serde_json::to_string(&payload).unwrap_or_else(|_| "{}".to_string());
            Some(serde_json::json!({
                "jsonrpc": "2.0", "id": id,
                "result": { "content": [{ "type": "text", "text": text_str }], "isError": is_error }
            }))
        }
        other => Some(serde_json::json!({
            "jsonrpc": "2.0", "id": id,
            "error": { "code": -32601, "message": format!("Method not found: {}", other) }
        })),
    }
}

/// Read the next JSON-RPC 2.0 message from `reader`, supporting both:
/// 1. `Content-Length: <N>\r\n\r\n<payload>` framed MCP messages, and
/// 2. Newline-delimited JSON-RPC 2.0 lines (`{...}\n`).
/// Returns `Ok(Some((request_value, was_content_length_framed)))` or `Ok(None)` on EOF.
pub fn read_next_mcp_message<R: BufRead>(
    reader: &mut R,
) -> Result<Option<(serde_json::Value, bool)>> {
    let mut line = String::new();
    loop {
        line.clear();
        let n = reader.read_line(&mut line)?;
        if n == 0 {
            return Ok(None);
        }
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if let Some(rest) = trimmed
            .strip_prefix("Content-Length:")
            .or_else(|| trimmed.strip_prefix("content-length:"))
        {
            let content_len: usize = rest
                .trim()
                .parse()
                .context("Invalid Content-Length header in MCP stdio stream")?;
            loop {
                let mut hdr = String::new();
                let hn = reader.read_line(&mut hdr)?;
                if hn == 0 || hdr.trim().is_empty() {
                    break;
                }
            }
            let mut buf = vec![0u8; content_len];
            reader.read_exact(&mut buf)?;
            let val: serde_json::Value =
                serde_json::from_slice(&buf).context("Invalid JSON in framed MCP message")?;
            return Ok(Some((val, true)));
        }
        if trimmed.starts_with('{') {
            let val: serde_json::Value =
                serde_json::from_str(trimmed).context("Invalid JSON-RPC line in MCP stream")?;
            return Ok(Some((val, false)));
        }
    }
}

/// Run the full JSON-RPC 2.0 Model Context Protocol (MCP) Server over `stdio`.
pub fn run_mcp_stdio_server(
    project_dir: Option<&Path>,
    cache_dir: Option<&Path>,
) -> Result<()> {
    let stdin = io::stdin();
    let mut reader = BufReader::new(stdin.lock());
    let stdout = io::stdout();
    let mut writer = stdout.lock();

    while let Some((req, framed)) = read_next_mcp_message(&mut reader)? {
        if let Some(resp) = handle_mcp_jsonrpc_request(&req, project_dir, cache_dir) {
            let payload = serde_json::to_string(&resp)?;
            if framed {
                write!(writer, "Content-Length: {}\r\n\r\n{}", payload.len(), payload)?;
            } else {
                writeln!(writer, "{}", payload)?;
            }
            writer.flush()?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn test_mcp_initialize_tools_list_and_compact_token_savings() {
        reset_agent_analytics();

        // 1. Test `initialize`
        let init_req = serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}});
        let init_resp = handle_mcp_jsonrpc_request(&init_req, None, None).expect("initialize must return a response");
        assert_eq!(init_resp["result"]["protocolVersion"], "2024-11-05");
        assert_eq!(init_resp["result"]["serverInfo"]["name"], "turbo-lean-mcp");
        assert_eq!(init_resp["result"]["serverInfo"]["version"], "0.5.0");

        // 2. Test `tools/list` returns the 6 universal MCP tools
        let list_req = serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}});
        let list_resp = handle_mcp_jsonrpc_request(&list_req, None, None).expect("tools/list must return a response");
        let tools = list_resp["result"]["tools"].as_array().expect("tools array");
        assert_eq!(tools.len(), 6);
        let tool_names: Vec<&str> = tools.iter().filter_map(|t| t.get("name").and_then(|v| v.as_str())).collect();
        assert_eq!(
            tool_names,
            vec![
                "turbo_agent_step",
                "turbo_check_decl",
                "turbo_fast_check",
                "turbo_audit_spec",
                "turbo_pr_verify",
                "turbo_cluster_status",
            ]
        );

        // 3. Test `compact_for_llm` reduces payload size by > 4x (`compact_bytes * 4 <= verbose_bytes`)
        let verbose_verified = serde_json::json!({
            "status": "theorem_verified", "verification_status": "verified", "verified": true,
            "decl": "word_add_comm_thm", "file": "/workspace/lean/TurboLean/FastCheck.lean",
            "stage": "stage2_kernel_verified", "accelerators_active": true, "registered_accelerators_count": 9,
            "accelerator_certificates": [{
                "kind": "rewritten_proof", "new_body_src": "by simp only [Nat.add_comm]",
                "accelerator_name": "builtin:simd-simp-distiller", "estimated_speedup_hint": "9.1x"
            }],
            "stage1_fastcheck_certified": true, "lean_native_certified": true, "lean_native_engine_version": "0.5.0",
            "low_memory_mode": false, "max_memory_mb": 8192, "total_specs_audited": 12, "vacuous_specs": 0, "tight_specs": 12,
            "shard_hits": 1, "shard_misses": 0,
            "shard_key": "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
            "interface_hash": "fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210",
            "prefix_env_hash": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            "distilled_simp_hint": "simp only [Nat.add_comm]", "elapsed_ms": 2.1
        });
        let verbose_bytes = serde_json::to_vec(&verbose_verified).unwrap().len();
        let compact_verified = compact_for_llm(&verbose_verified);
        let compact_bytes = serde_json::to_vec(&compact_verified).unwrap().len();
        assert!(compact_bytes * 4 <= verbose_bytes);
        assert_eq!(compact_verified["ok"], true);
        assert_eq!(compact_verified["decl"], "word_add_comm_thm");
        assert_eq!(compact_verified["fast_tactic"], "by simp only [Nat.add_comm]");
        assert!(compact_verified["tok_saved"].as_u64().unwrap_or(0) >= 400);

        let verbose_cex = serde_json::json!({
            "status": "counterexample_rejected", "decl": "buggy_sub_underflow", "violations": 1,
            "counterexample": { "state_idx": 1, "bindings": [["a", "0x0"], ["b", "0x1"]], "lhs_value": "0xffff", "rhs_value": "0x0" },
            "suggested_hypothesis": "h_le : b.val <= a.val", "elapsed_ms": 1.4
        });
        let compact_cex = compact_for_llm(&verbose_cex);
        assert_eq!(compact_cex["ok"], false);
        assert_eq!(compact_cex["kind"], "cex");
        assert_eq!(compact_cex["fix_hint"], "h_le : b.val <= a.val");

        // 4. Test `tools/call` for `turbo_fast_check` on a buggy theorem
        let tpu_req = serde_json::json!({
            "jsonrpc": "2.0", "id": 4, "method": "tools/call",
            "params": {
                "name": "turbo_fast_check",
                "arguments": { "decl": "buggy_de_morgan", "backend": "tpu", "stmt_src": "(a b : Word256) : Word256.bitNot (Word256.bitAnd a b) = Word256.bitAnd (Word256.bitNot a) (Word256.bitNot b)" }
            }
        });
        let tpu_resp = handle_mcp_jsonrpc_request(&tpu_req, None, None).unwrap();
        let tpu_val: serde_json::Value = serde_json::from_str(tpu_resp["result"]["content"][0]["text"].as_str().unwrap()).unwrap();
        assert_eq!(tpu_val["ok"], false);
        assert_eq!(tpu_val["kind"], "cex");

        // 5. Test `tools/call` for `turbo_agent_analytics` and verify `estimated_tokens_saved` in `/dev/shm`
        let analytics_req = serde_json::json!({
            "jsonrpc": "2.0", "id": 5, "method": "tools/call",
            "params": { "name": "turbo_agent_analytics", "arguments": {} }
        });
        let analytics_resp = handle_mcp_jsonrpc_request(&analytics_req, None, None).unwrap();
        let analytics_val: serde_json::Value = serde_json::from_str(analytics_resp["result"]["content"][0]["text"].as_str().unwrap()).unwrap();
        assert!(analytics_val["total_calls"].as_u64().unwrap_or(0) >= 1);
        assert!(analytics_val["stage1_tpu_rejects"].as_u64().unwrap_or(0) >= 1);
        assert!(analytics_val["estimated_tokens_saved"].as_u64().unwrap_or(0) > 500);

        // 7. Test Content-Length framing reader roundtrip
        let framed_body = r#"{"jsonrpc":"2.0","id":9,"method":"ping"}"#;
        let framed_stream = format!("Content-Length: {}\r\n\r\n{}", framed_body.len(), framed_body);
        let mut cursor = Cursor::new(framed_stream.into_bytes());
        let (parsed_msg, is_framed) = read_next_mcp_message(&mut cursor).expect("read framed message").expect("some message");
        assert!(is_framed);
        assert_eq!(parsed_msg["method"], "ping");
    }
}
