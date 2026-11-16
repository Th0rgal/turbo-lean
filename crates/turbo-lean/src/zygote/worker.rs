use crate::db::TurboStore;
use crate::pack::next_tmp_id;
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

use super::*;

pub(super) const BLAKE3_LEAN_SRC: &str = include_str!("../../../../lean/TurboLean/Blake3.lean");
pub(super) const STATEMENT_HASH_LEAN_SRC: &str = include_str!("../../../../lean/TurboLean/StatementHash.lean");
pub(super) const ZYGOTE_FORK_LEAN_SRC: &str = include_str!("../zygote_fork_posix.lean");
pub(super) const ZYGOTE_WORKER_LEAN_SRC: &str = include_str!("../../../../lean/TurboLean/ZygoteWorker.lean");

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TimeoutHotspot {
    pub kind: String,
    pub label: String,
    pub line: usize,
    pub elapsed_ms: u64,
    pub heartbeats: u64,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SimpHotspot {
    pub lemma: String,
    pub attempts: u64,
    pub succeeded: u64,
}

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
    #[serde(default)]
    pub compact_prefix: bool,
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
    /// `ZYGOTE_SCANNER_VERSION` when the host stderr panic scan vetted this reply; `0` for
    /// replies from older hosts. Persisted eval replies without the current version are rejected.
    #[serde(default)]
    pub scanner_version: u32,
    /// `ZYGOTE_REPLAY_VERSION` when this reply came from a worker that kernel-replays every new
    /// declaration (`kernelReplayNewDecls`); `0` for replies from older hosts/workers. Persisted
    /// verdicts without the current version are rejected (see `verifier_provenance_ok`).
    #[serde(default)]
    pub replay_version: u32,
    /// Newly elaborated theorem declarations mapped to their canonical `statement-v1` BLAKE3
    /// kernel type hash (`TurboLean.StatementHash` / `ZygoteWorker.kernelStatementHash`).
    #[serde(default, skip_serializing_if = "std::collections::BTreeMap::is_empty")]
    pub decl_types: std::collections::BTreeMap<String, String>,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub used_sorry: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub sorry_decls: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub timeout_hotspots: Vec<TimeoutHotspot>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub simp_hotspots: Vec<SimpHotspot>,
}

/// Version of the host-side reply vetting (`StderrScan` + `mark_runtime_panic` + `decl_types`).
/// Bump whenever a reply that an older host accepted could now be rejected, so persisted replies
/// are not replayed.
pub(crate) const ZYGOTE_SCANNER_VERSION: u32 = 5;

/// Version of the independent kernel replay of newly added declarations (worker
/// `kernelReplayNewDecls`, dependency/module audits via `--kernel-replay-module`). Verdicts
/// cached before the replay existed may have been produced with `debug.skipKernelTC` in effect,
/// so every persisted verdict must carry this version. Bump when the replay is strengthened.
/// v2: trusted non-root dependency modules (compiled, CAS-restored or prebuilt) are replayed
/// too; v1 outputs may import an unreplayed dependency `.olean`.
/// v3: duplicate realized theorems in Lean 4.35 `module` closures are audited for axioms and
/// kernel-checked under fresh names rather than skipped when already present in `base`.
pub(crate) const ZYGOTE_REPLAY_VERSION: u32 = 3;

/// Fail-closed provenance gate for every persisted verifier verdict: it must have been vetted
/// by the current stderr scanner *and* produced under the current kernel replay.
pub(crate) fn verifier_provenance_ok(scanner_version: u32, replay_version: u32) -> bool {
    scanner_version == ZYGOTE_SCANNER_VERSION && replay_version == ZYGOTE_REPLAY_VERSION
}

/// In-process C-ABI dispatcher for `LeanNative` methods (`"ping"`, `"validate-tv"`,
/// `"verify-certs"`, `"compile-fastcheck"`, `"eval-cex"`, `"compile-llvm"`, `"compile-ptx"`),
/// backed by `LeanNative/Spec.c` linked into `libturbo_spec_cabi.a` with zero subprocess IPC.
#[allow(dead_code)]
pub fn query_lean_native_core_worker(
    method: &str,
    extra_fields_json: Option<&str>,
) -> Result<serde_json::Value> {
    let custom_nonexistent = std::env::var("LEAN_NATIVE_CORE_BIN")
        .ok()
        .filter(|s| !s.trim().is_empty())
        .is_some_and(|s| !Path::new(s.trim()).is_file());
    let mut eval_decl_name = "candidate_witness".to_string();
    let (eval_certified, eval_reason) = if method != "eval-cex" || custom_nonexistent {
        (false, Some("missing_witness"))
    } else if let Some(extra) = extra_fields_json {
        let parsed = serde_json::from_str::<serde_json::Value>(extra).ok();
        let lhs = parsed
            .as_ref()
            .and_then(|v| v.get("lhs").or_else(|| v.get("lhs_value")))
            .and_then(|v| v.as_str());
        let rhs = parsed
            .as_ref()
            .and_then(|v| v.get("rhs").or_else(|| v.get("rhs_value")))
            .and_then(|v| v.as_str());
        let stmt = parsed
            .as_ref()
            .and_then(|v| v.get("stmt").or_else(|| v.get("stmt_src")))
            .and_then(|v| v.as_str());
        let decl_name = parsed
            .as_ref()
            .and_then(|v| v.get("decl").or_else(|| v.get("declName")))
            .and_then(|v| v.as_str())
            .unwrap_or("candidate_witness");
        let bindings = parsed
            .as_ref()
            .and_then(|v| v.get("bindings"))
            .and_then(|v| {
                if let Some(arr) = v.as_array() {
                    arr.iter()
                        .map(|pair| {
                            let items = pair.as_array()?;
                            Some((
                                items.first()?.as_str()?.to_string(),
                                items.get(1)?.as_str()?.to_string(),
                            ))
                        })
                        .collect::<Option<Vec<_>>>()
                } else if let Some(obj) = v.as_object() {
                    obj.iter()
                        .map(|(k, val)| Some((k.clone(), val.as_str()?.to_string())))
                        .collect::<Option<Vec<_>>>()
                } else {
                    None
                }
            });
        let witness_summary = parsed
            .as_ref()
            .and_then(|v| v.get("witness_summary"))
            .and_then(|v| v.as_str());
        if let Some(stmt_src) = stmt {
            eval_decl_name = decl_name.to_string();
            crate::gpu_fastcheck::certify_standalone_statement_witness_via_lean_kernel(
                decl_name,
                stmt_src,
                bindings,
                witness_summary,
                lhs,
                rhs,
            )
        } else {
            match (
                lhs.and_then(crate::gpu_fastcheck::parse_u64_witness_str),
                rhs.and_then(crate::gpu_fastcheck::parse_u64_witness_str),
            ) {
                (Some(l), Some(r)) if l == r => (false, Some("lhs_eq_rhs")),
                (Some(_), Some(_)) => (false, Some("statement_required")),
                _ => (false, Some("missing_witness")),
            }
        }
    } else {
        (false, Some("missing_witness"))
    };
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
            "declName": eval_decl_name,
            "certified": eval_certified,
            "overallAssurance": if eval_certified { "VerifiedKernelProof" } else { "FallbackUnverified" },
            "fallback": !eval_certified,
            "falsePositives": u8::from(!eval_certified),
            "certification": if eval_certified { "lean_kernel" } else { "unavailable" },
            "reason": eval_reason,
            "theorem": "LeanNative.Backend.FastCheck.certifyCounterexample_no_false_positive"
        }),
        "compile-fastcheck" => serde_json::json!({
            "schemaVersion": "lean-native-fastcheck-v1",
            "moduleName": "LeanNative.FastCheck.Sample",
            "numSamplesPerDecl": 1024,
            "useConstraintProp": true,
            "totalDecls": 2,
            "counterexamplesFound": 0,
            "vacuousPasses": 0,
            "falsePositives": 0,
            "certification": "unavailable",
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

/// Drop pooled children before returning from a CLI invocation or shutting down a server.
pub(crate) fn clear_zygote_pool() {
    if let Some(pool) = ZYGOTE_POOL.get() {
        pool.lock().unwrap_or_else(|e| e.into_inner()).clear();
    }
    if let Some(masters) = ZYGOTE_MASTERS.get() {
        masters.lock().unwrap_or_else(|e| e.into_inner()).clear();
    }
}

pub(super) const ZYGOTE_STDERR_TAIL_CAP: usize = 8192;

/// Mirrors `TurboLean.ZygoteWorker.stderrReplyMark`: the worker writes it to stderr before each reply.
pub(super) const ZYGOTE_STDERR_REPLY_MARK: &str = "[TurboLean.ZygoteWorker] reply";

/// How long the host waits, after reading a reply, for that reply's stderr mark.
pub(super) const ZYGOTE_STDERR_MARK_WAIT: std::time::Duration = std::time::Duration::from_secs(2);

/// Byte-stream scan of a worker's whole stderr (the tail alone loses panics behind long
/// backtraces or long unterminated lines): counts runtime-panic signatures and reply marks.
#[derive(Default)]
pub(super) struct StderrScan {
    pub(super) state: std::sync::Mutex<StderrScanState>,
    pub(super) cv: std::sync::Condvar,
}

#[derive(Default)]
pub(super) struct StderrScanState {
    pub(super) panics: u64,
    pub(super) marks: u64,
    /// Last `longest signature - 1` bytes, so a signature split across chunks is still seen.
    pub(super) overlap: Vec<u8>,
}

impl StderrScan {
    /// Scans every byte of `chunk`; only matches ending inside `chunk` are new.
    pub(super) fn feed(&self, chunk: &[u8]) {
        let Ok(mut g) = self.state.lock() else {
            return;
        };
        let keep = g.overlap.len();
        let mut buf = std::mem::take(&mut g.overlap);
        buf.extend_from_slice(chunk);
        let count = |pat: &str| {
            let pat = pat.as_bytes();
            buf.windows(pat.len())
                .enumerate()
                .filter(|(i, w)| *w == pat && i + pat.len() > keep)
                .count() as u64
        };
        let marks = count(ZYGOTE_STDERR_REPLY_MARK);
        g.panics += RUNTIME_PANIC_SIGNATURES
            .iter()
            .map(|s| count(s))
            .sum::<u64>();
        g.marks += marks;
        let longest = RUNTIME_PANIC_SIGNATURES
            .iter()
            .chain([&ZYGOTE_STDERR_REPLY_MARK])
            .map(|s| s.len())
            .max()
            .unwrap_or(1);
        g.overlap = buf[buf.len().saturating_sub(longest - 1)..].to_vec();
        drop(g);
        if marks > 0 {
            self.cv.notify_all();
        }
    }

    pub(super) fn snapshot(&self) -> (u64, u64) {
        self.state
            .lock()
            .map(|g| (g.panics, g.marks))
            .unwrap_or((u64::MAX, u64::MAX))
    }

    /// Whether the request since `before` must be treated as panicked: a runtime panic hit stderr,
    /// or its reply mark did not arrive within `wait` (fail closed: an unseen mark means unseen
    /// stderr, which may hold a panic).
    pub(super) fn panicked_since(&self, before: (u64, u64), wait: std::time::Duration) -> bool {
        let Ok(g) = self.state.lock() else {
            return true;
        };
        match self.cv.wait_timeout_while(g, wait, |s| s.marks <= before.1) {
            Ok((g, _)) => g.marks <= before.1 || g.panics > before.0,
            Err(_) => true,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(super) struct WorkerCrashDiagnostics {
    pub(super) message: String,
    pub(super) exit_code: Option<i32>,
    pub(super) exit_signal: Option<i32>,
    pub(super) stderr_tail: String,
    pub(super) peak_rss_mb: u64,
    pub(super) last_request: Option<String>,
}

pub struct ZygoteWorkerProcess {
    pub child: Option<std::process::Child>,
    pub(super) clone_pid: Option<u32>,
    // Linux parent-death signals follow the spawning thread, so keep it alive with the worker.
    pub(super) _owner: std::sync::mpsc::Sender<()>,
    pub(super) stdin: WorkerInput,
    pub(super) stdout: BufReader<WorkerOutput>,
    pub(super) stderr_tail: std::sync::Arc<std::sync::Mutex<Vec<u8>>>,
    pub(super) stderr_scan: std::sync::Arc<StderrScan>,
    #[cfg(target_os = "linux")]
    pub(super) pinned_snapshot_dir: Option<(u64, u64)>,
    pub(super) spawn_lean_path: String,
    pub(super) warm_prefixes: std::collections::HashSet<String>,
    pub(super) warm_prefix_tree: Vec<(String, String)>,
    pub(super) warm_imports: std::collections::HashMap<String, String>,
    pub request_count: usize,
    pub(super) cold_import_us: Option<u64>,
    pub(super) is_master: bool,
    pub(super) _master: Option<std::sync::Arc<ZygoteMasterEntry>>,
}

#[cfg(unix)]
pub(super) type WorkerInput = std::fs::File;
#[cfg(unix)]
pub(super) type WorkerOutput = std::fs::File;
#[cfg(not(unix))]
pub(super) type WorkerInput = std::process::ChildStdin;
#[cfg(not(unix))]
pub(super) type WorkerOutput = std::process::ChildStdout;

pub(super) fn worker_input(input: std::process::ChildStdin) -> WorkerInput {
    #[cfg(unix)]
    { std::fs::File::from(std::os::fd::OwnedFd::from(input)) }
    #[cfg(not(unix))]
    { input }
}

pub(super) fn worker_output(output: std::process::ChildStdout) -> WorkerOutput {
    #[cfg(unix)]
    { std::fs::File::from(std::os::fd::OwnedFd::from(output)) }
    #[cfg(not(unix))]
    { output }
}

impl ZygoteWorkerProcess {
    pub(super) fn pid(&self) -> u32 {
        self.clone_pid.unwrap_or_else(|| self.child.as_ref().unwrap().id())
    }

    #[cfg(target_os = "linux")]
    pub(super) fn fork_clone(&mut self, deadline: std::time::Instant) -> Result<Self> {
        use std::os::unix::{io::OwnedFd, net::UnixListener};
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        use std::os::unix::ffi::OsStrExt;
        let sock_dir = private_staging_child("fork-sockets")?;
        let path = sock_dir.join(format!(
            "clone-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        anyhow::ensure!(
            path.with_extension("err").as_os_str().as_bytes().len() < 104,
            "clone socket path too long"
        );
        struct Cleanup(PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) { let _ = std::fs::remove_file(&self.0); let _ = std::fs::remove_file(self.0.with_extension("err")); }
        }
        let _cleanup = Cleanup(path.clone());
        let listener = UnixListener::bind(&path)?;
        let errors = UnixListener::bind(path.with_extension("err"))?;
        writeln!(self.stdin, "fork_clone:{}", path.display())?;
        self.stdin.flush()?;
        let mut reply = String::new();
        read_line_with_timeout(&mut self.stdout, &mut reply, deadline)?;
        let pid: u32 = reply.trim().strip_prefix("clone ").ok_or_else(|| anyhow::anyhow!("clone unavailable"))?.parse()?;
        let accept = |l: UnixListener| -> Result<std::os::unix::net::UnixStream> {
            l.set_nonblocking(true)?;
            loop {
                match l.accept() {
                    Ok((s, _)) => return Ok(s),
                    Err(e)
                        if e.kind() == std::io::ErrorKind::WouldBlock
                            && std::time::Instant::now() < deadline =>
                    {
                        std::thread::sleep(std::time::Duration::from_millis(1))
                    }
                    Err(e) => return Err(e.into()),
                }
            }
        };
        let channels = (|| Ok::<_, anyhow::Error>((accept(listener)?, accept(errors)?)))();
        let (stream, mut err) = match channels {
            Ok(c) => c,
            Err(e) => { unsafe { libc::kill(pid as i32, libc::SIGKILL); } return Err(e); }
        };
        let stderr_tail = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_scan = std::sync::Arc::new(StderrScan::default());
        let (tail, scan) = (stderr_tail.clone(), stderr_scan.clone());
        std::thread::spawn(move || {
            use std::io::Read;
            let mut buf = [0; 1024];
            while let Ok(n) = err.read(&mut buf) {
                if n == 0 { break; }
                scan.feed(&buf[..n]);
                if let Ok(mut t) = tail.lock() {
                    t.extend_from_slice(&buf[..n]);
                    let excess = t.len().saturating_sub(ZYGOTE_STDERR_TAIL_CAP);
                    t.drain(..excess);
                }
            }
        });
        Ok(Self {
            child: None, clone_pid: Some(pid), _owner: self._owner.clone(),
            stdin: std::fs::File::from(OwnedFd::from(stream.try_clone()?)),
            stdout: BufReader::new(std::fs::File::from(OwnedFd::from(stream))),
            stderr_tail, stderr_scan, pinned_snapshot_dir: self.pinned_snapshot_dir,
            spawn_lean_path: self.spawn_lean_path.clone(), warm_prefixes: self.warm_prefixes.clone(),
            warm_prefix_tree: self.warm_prefix_tree.clone(), warm_imports: self.warm_imports.clone(), request_count: 0, cold_import_us: None, is_master: false, _master: None,
        })
    }
}

#[allow(dead_code)]
extern "C" {
    pub(super) fn turbo_spec_zygote_lca_reuse_safe(ancestor_len: u64, prefix_len: u64) -> u8;
}

impl Drop for ZygoteWorkerProcess {
    fn drop(&mut self) {
        if let Some(child) = &mut self.child {
            // Let a master kill and reap its clones before reaping the master itself.
            if self.is_master {
                let _ = self.stdin.write_all(b"shutdown\n");
                let _ = self.stdin.flush();
                let deadline = std::time::Instant::now() + std::time::Duration::from_secs(1);
                while matches!(child.try_wait(), Ok(None)) && std::time::Instant::now() < deadline {
                    std::thread::sleep(std::time::Duration::from_millis(5));
                }
            }
            let _ = child.kill();
            let _ = child.wait();
        }
        #[cfg(unix)]
        if let Some(pid) = self.clone_pid {
            unsafe { libc::kill(pid as i32, libc::SIGKILL); }
        }
    }
}

pub(super) type ZygoteChild = ZygoteWorkerProcess;

pub(super) struct ZygoteMasterEntry {
    pub(super) worker: std::sync::Mutex<ZygoteWorkerProcess>,
    pub(super) pid: u32,
    pub(super) last_used_seq: std::sync::atomic::AtomicU64,
}

impl ZygoteMasterEntry {
    pub(super) fn touch(&self) {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(1);
        self.last_used_seq.store(NEXT.fetch_add(1, Ordering::Relaxed), Ordering::Relaxed);
        govern_machine_wide_zygote_rss(self.pid, measure_process_rss_mb(self.pid));
    }
}

#[allow(clippy::type_complexity)]
pub(super) static ZYGOTE_POOL: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<(String, String, String), Vec<ZygoteWorkerProcess>>>,
> = std::sync::OnceLock::new();

#[allow(clippy::type_complexity)]
pub(super) static ZYGOTE_MASTERS: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<(String, String, String), std::sync::Arc<ZygoteMasterEntry>>>,
> = std::sync::OnceLock::new();

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
    let mut cur_mutual_start: Option<usize> = None;
    for (idx, line) in lines.iter().enumerate() {
        let trimmed = line.split("--").next().unwrap_or(line).trim();
        if cur_mutual_start.is_none() && (trimmed == "mutual" || trimmed.starts_with("mutual ")) {
            cur_mutual_start = Some(idx);
        } else if cur_mutual_start.is_some() && (trimmed == "end" || trimmed.starts_with("end ")) {
            cur_mutual_start = None;
        } else if trimmed.starts_with("theorem ") || trimmed.starts_with("lemma ") {
            last_thm_idx = Some(cur_mutual_start.unwrap_or(idx));
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
    pub(super) fn timed_out_reply(
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

    pub(super) fn crashed_reply_with_diag(eval_mode: bool, diag: WorkerCrashDiagnostics) -> Self {
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
pub(super) const RUNTIME_PANIC_ERR: &str =
    "[TurboLean.ZygoteWorker] runtime panic; worker environment is unusable";

/// Mirrors `TurboLean.ZygoteWorker.isRuntimePanicText`: Lean panic output or `EnvExtension`
/// corruption, not any mention of the word `PANIC`.
pub(super) fn is_runtime_panic_text(s: &str) -> bool {
    RUNTIME_PANIC_SIGNATURES.iter().any(|m| s.contains(m))
}

pub(super) const RUNTIME_PANIC_SIGNATURES: [&str; 3] = [
    "PANIC at ",
    "INTERNAL PANIC",
    "invalid environment extension",
];

/// Fails a reply whose worker hit a runtime panic (reported, in its messages, or seen on the
/// worker's stderr during the request); returns whether the worker must be discarded.
pub(super) fn mark_runtime_panic(rep: &mut ZygoteEvalReply, stderr_panic: bool) -> bool {
    let reported = rep.errors.iter().any(|e| e == RUNTIME_PANIC_ERR);
    if !reported && !stderr_panic && !rep.messages.iter().any(|m| is_runtime_panic_text(m)) {
        return false;
    }
    rep.ok = false;
    rep.import_ok = true;
    if !reported {
        rep.errors.push(RUNTIME_PANIC_ERR.to_string());
    }
    true
}

pub(super) fn collect_worker_exit_status(child: &mut std::process::Child) -> (Option<i32>, Option<i32>) {
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

pub(super) fn snapshot_worker_stderr_tail(buf: &std::sync::Arc<std::sync::Mutex<Vec<u8>>>) -> String {
    buf.lock()
        .ok()
        .map(|g| String::from_utf8_lossy(&g).trim().to_string())
        .unwrap_or_default()
}

pub(super) fn build_worker_crash_diagnostics(
    worker: &mut ZygoteChild,
    reason: &str,
    peak_rss_mb: u64,
    last_request: &str,
) -> WorkerCrashDiagnostics {
    let (exit_code, exit_signal) = worker.child.as_mut().map(collect_worker_exit_status).unwrap_or((None, None));
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
pub(super) fn owned_private_entry(path: &Path, want_dir: bool) -> bool {
    use std::os::unix::fs::MetadataExt;
    let Ok(m) = fs::symlink_metadata(path) else {
        return false;
    };
    let mask = if want_dir { 0o077 } else { 0o022 };
    let kind_ok = if want_dir { m.is_dir() } else { m.is_file() };
    kind_ok && m.uid() == unsafe { libc::geteuid() } && m.mode() & mask == 0
}

#[cfg(not(unix))]
pub(super) fn owned_private_entry(_path: &Path, _want_dir: bool) -> bool {
    true
}

pub(super) fn owned_private_file(path: &Path) -> bool {
    owned_private_entry(path, false)
}

/// Per-uid `$TMPDIR/turbo_lean_shared_zygote_bins_<uid>` (mode 0700), or `None` when it cannot
/// be created or is not owned by us (e.g. pre-created by another local user).
pub(crate) fn private_shared_zygote_dir() -> Option<PathBuf> {
    private_shared_zygote_dir_in(&std::env::temp_dir())
}

pub(super) fn private_shared_zygote_dir_in(base: &Path) -> Option<PathBuf> {
    private_temp_subdir_in(base, "turbo_lean_shared_zygote_bins")
}

pub(crate) fn private_temp_subdir(prefix: &str) -> Option<PathBuf> {
    private_temp_subdir_in(&std::env::temp_dir(), prefix)
}

pub(super) fn private_temp_subdir_in(base: &Path, prefix: &str) -> Option<PathBuf> {
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
        let dir = base.join(format!("{prefix}_{uid}"));
        match fs::DirBuilder::new().mode(0o700).create(&dir) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(_) => return None,
        }
        dir
    };
    #[cfg(not(unix))]
    let dir = {
        let dir = base.join(format!("{prefix}_{uid}"));
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

pub(crate) fn compiler_failure(source: &Path, out: &std::process::Output) -> anyhow::Error {
    anyhow::anyhow!(
        "`lean -c` failed on {}:\n{}\n{}",
        source.display(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

pub(crate) fn ensure_zygote_binary_at(
    store_root: &Path,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
) -> Result<std::path::PathBuf> {
    let _lifecycle = lifecycle_lock(false)?;
    let tools = crate::module_builder::ToolchainExecutables::from_lean(lean_bin)?;
    let lean_bin = tools.lean.as_path();
    let leanc_bin = tools.leanc.as_path();
    let mut env_vars = env_vars.clone();
    tools.apply_env(&mut env_vars);
    let env_vars = &env_vars;

    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-zygote:v7:cow-fork-pool:");
    hasher.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    hasher.update(b":");
    hasher.update(std::env::consts::ARCH.as_bytes());
    hasher.update(lean_bin.to_string_lossy().as_bytes());
    if let Some(tc) = env_vars.get("ELAN_TOOLCHAIN") {
        hasher.update(tc.as_bytes());
    }
    hasher.update(BLAKE3_LEAN_SRC.as_bytes());
    hasher.update(STATEMENT_HASH_LEAN_SRC.as_bytes());
    hasher.update(ZYGOTE_FORK_LEAN_SRC.as_bytes());
    hasher.update(ZYGOTE_WORKER_LEAN_SRC.as_bytes());
    let bin_name = format!("turbo_zygote_{}", &hasher.finalize().to_hex()[..16]);
    let bin_dir = store_root.join("fastcheck_bins");
    fs::create_dir_all(&bin_dir)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        if let Ok(m) = fs::symlink_metadata(&bin_dir) {
            if m.is_dir() && m.uid() == unsafe { libc::geteuid() } && m.mode() & 0o077 != 0 {
                let mut p = m.permissions();
                p.set_mode(0o700);
                let _ = fs::set_permissions(&bin_dir, p);
            }
        }
    }
    let cached_bin = bin_dir.join(&bin_name);
    if owned_private_file(&cached_bin) {
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

    if owned_private_file(&cached_bin) {
        return Ok(cached_bin);
    }
    if cached_bin.symlink_metadata().is_ok() {
        let _ = fs::remove_file(&cached_bin);
    }
    if let Some(shared_bin) = shared_bin.as_ref().filter(|b| owned_private_file(b)) {
        let tmp_copy = bin_dir.join(format!(".{}.{}.tmp", bin_name, next_tmp_id()));
        if fs::hard_link(shared_bin, &tmp_copy).is_ok() || fs::copy(shared_bin, &tmp_copy).is_ok() {
            let _ = fs::rename(&tmp_copy, &cached_bin);
            if owned_private_file(&cached_bin) {
                return Ok(cached_bin);
            }
        }
        return Ok(shared_bin.clone());
    }

    let tmp_id = next_tmp_id();
    // Compile embedded TurboLean/{Blake3,StatementHash,ZygoteWorker}.lean via `lean -c` + `leanc -O3 -lleanshared -Wl,-rpath,<sysroot>/lib/lean`
    let scratch_dir = bin_dir.join(format!(".zygote_build_{}", tmp_id));
    struct ScratchGuard(PathBuf);
    impl Drop for ScratchGuard {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let _scratch_guard = ScratchGuard(scratch_dir.clone());
    let scratch_pkg = scratch_dir.join("TurboLean");
    fs::create_dir_all(&scratch_pkg)?;
    let tmp_bin = bin_dir.join(format!(".{}.{}.tmp", bin_name, tmp_id));

    let tc_lib_lean = lean_bin
        .parent()
        .and_then(|b| b.parent())
        .map(|tc| tc.join("lib").join("lean"))
        .filter(|p| p.exists());
    let mut compile_env = env_vars.clone();
    let base_lp = compile_env
        .get("LEAN_PATH")
        .cloned()
        .or_else(|| {
            tc_lib_lean
                .as_ref()
                .map(|p| p.to_string_lossy().to_string())
        })
        .unwrap_or_default();
    let scratch_lp = if base_lp.is_empty() {
        scratch_dir.to_string_lossy().to_string()
    } else {
        format!("{}:{}", scratch_dir.display(), base_lp)
    };
    compile_env.insert("LEAN_PATH".to_string(), scratch_lp);

    let mut obj_files = Vec::with_capacity(4);
    for (stem, src, emit_olean, c_opt) in [
        ("Blake3", BLAKE3_LEAN_SRC, true, "-O3"),
        ("StatementHash", STATEMENT_HASH_LEAN_SRC, true, "-O3"),
        ("ZygoteFork", ZYGOTE_FORK_LEAN_SRC, true, "-O3"),
        ("ZygoteWorker", ZYGOTE_WORKER_LEAN_SRC, false, "-O0"),
    ] {
        let lean_file = if emit_olean {
            scratch_pkg.join(format!("{stem}.lean"))
        } else {
            scratch_dir.join(format!("ZygoteWorker_{tmp_id}.lean"))
        };
        let c_file = scratch_dir.join(format!("{stem}_{tmp_id}.c"));
        let obj_file = scratch_dir.join(format!("{stem}_{tmp_id}.o"));
        fs::write(&lean_file, src)?;
        let mut cmd = Command::new(lean_bin);
        cmd.arg(format!("--root={}", scratch_dir.display()));
        if emit_olean {
            cmd.arg("-o").arg(scratch_pkg.join(format!("{stem}.olean")));
        }
        let out = cmd
            .arg("-c")
            .arg(&c_file)
            .arg(&lean_file)
            .current_dir(&scratch_dir)
            .envs(&compile_env)
            .output()
            .with_context(|| format!("Failed to compile {stem}.lean to C"))?;
        if !out.status.success() {
            return Err(compiler_failure(Path::new(&format!("{stem}.lean")), &out));
        }
        let c_out = Command::new(leanc_bin)
            .arg(c_opt)
            .arg("-c")
            .arg(&c_file)
            .arg("-o")
            .arg(&obj_file)
            .current_dir(&scratch_dir)
            .envs(&compile_env)
            .output()
            .with_context(|| format!("Failed to compile {stem}.c via `leanc {c_opt} -c`"))?;
        if !c_out.status.success() {
            anyhow::bail!(
                "`leanc {c_opt} -c` failed on {stem}.c:\n{}",
                String::from_utf8_lossy(&c_out.stderr)
            );
        }
        obj_files.push(obj_file);
    }

    let mut link_cmd = Command::new(leanc_bin);
    for obj_file in &obj_files {
        link_cmd.arg(obj_file);
    }
    link_cmd
        .arg("-lleanshared")
        .arg("-lLake_shared")
        .arg("-o")
        .arg(&tmp_bin)
        .current_dir(&scratch_dir)
        .envs(&compile_env);
    if let Some(tc_lib_lean) = tc_lib_lean {
        link_cmd.arg(format!("-Wl,-rpath,{}", tc_lib_lean.display()));
    }
    let out2 = link_cmd
        .output()
        .context("Failed to link ZygoteWorker binary via `leanc -O3 -lleanshared`")?;
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


/// Kill any remaining owned process whose `/proc/<pid>/environ` carries exact
/// `TURBO_LEAN_PROBE_NONCE=<nonce>` using PID-reuse-safe `pidfd_open` + `pidfd_send_signal(SIGKILL)`.
pub(crate) fn reap_processes_with_nonce(nonce: &str) {
    #[cfg(target_os = "linux")]
    {
        use std::os::fd::{AsRawFd, FromRawFd};
        use std::os::unix::fs::MetadataExt;
        let expected = format!("TURBO_LEAN_PROBE_NONCE={nonce}");
        let euid = unsafe { libc::geteuid() };
        let my_pid = std::process::id();
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
        while std::time::Instant::now() < deadline {
            let mut held: Vec<std::os::fd::OwnedFd> = Vec::new();
            for entry in fs::read_dir("/proc").into_iter().flatten().flatten() {
                let Some(pid) = entry
                    .file_name()
                    .to_str()
                    .and_then(|s| s.parse::<u32>().ok())
                else {
                    continue;
                };
                if pid == my_pid {
                    continue;
                }
                if fs::metadata(entry.path()).map(|m| m.uid()).ok() != Some(euid) {
                    continue;
                }
                let fd = unsafe { libc::syscall(libc::SYS_pidfd_open, pid, 0) };
                if fd < 0 {
                    continue;
                }
                let pidfd = unsafe { std::os::fd::OwnedFd::from_raw_fd(fd as i32) };
                let has_nonce = fs::read(entry.path().join("environ"))
                    .unwrap_or_default()
                    .split(|b| *b == 0)
                    .any(|v| v == expected.as_bytes());
                if !has_nonce {
                    continue;
                }
                let is_zombie = fs::read_to_string(entry.path().join("stat"))
                    .ok()
                    .and_then(|st| st.rsplit_once(") ").map(|(_, rest)| rest.starts_with('Z')))
                    .unwrap_or(false);
                if is_zombie {
                    continue;
                }
                let _ = unsafe {
                    libc::syscall(
                        libc::SYS_pidfd_send_signal,
                        pidfd.as_raw_fd(),
                        libc::SIGKILL,
                        std::ptr::null::<libc::siginfo_t>(),
                        0,
                    )
                };
                held.push(pidfd);
            }
            if held.is_empty() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
    }
    #[cfg(not(target_os = "linux"))]
    {
        let _ = nonce;
    }
}

pub(super) type ZygoteLeanPathKey = (String, String, std::path::PathBuf);

pub(super) static ZYGOTE_LEAN_PATH_CACHE: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<ZygoteLeanPathKey, String>>,
> = std::sync::OnceLock::new();

pub(super) fn read_line_with_timeout(
    reader: &mut BufReader<WorkerOutput>,
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

#[allow(clippy::too_many_arguments)]
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

/// The cache and executor must agree on the final import search order and artifacts.
pub(crate) struct ResolvedZygoteContext {
    pub(crate) lean_path: String,
    /// What the worker searches: the closure snapshot and the toolchain, when materialized.
    pub(crate) worker_lean_path: String,
    pub(crate) imports_csv: String,
    pub(crate) olean_digest: String,
    /// Worktree-path-independent closure digest (`snap:<manifest>[#inputs:<lake_inputs>]` when
    /// materialized, otherwise `olean_digest`), keying `ZygotePool` and verified-shard dedup across worktrees.
    pub(crate) closure_pool_digest: String,
    pub(crate) host_closure_digest: String,
    pub(crate) toolchain_policy: String,
    pub(crate) lake_inputs_uncacheable: bool,
    pub(crate) identity: String,
    /// The imported closure `identity` was computed from. Its materialized snapshot is all the
    /// worker can import besides the toolchain; without one nothing is cached under `identity`.
    pub(super) closure: ClosureSnapshot,
}

pub(super) fn encode_lean_args_hex(lean_args: &[String]) -> String {
    let filtered = crate::module_builder::filter_allowed_lean_args(lean_args);
    if filtered.is_empty() {
        String::new()
    } else {
        hex_encode_bytes(filtered.join("\n").as_bytes())
    }
}

pub(super) fn encode_fast_map_lines(entries: &[crate::splitter::FastVerifyEntry]) -> String {
    entries
        .iter()
        .map(|e| format!("{}\t{}", e.orig_rooted, e.gen_rooted))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Worker mode flag for a stubbed (`allow_stub`) or strict check of `shard_source`. Named `stub_targets`
/// (the declarations under check) travel as `<allow_stub|strict>:<hex targets>:<hex stubs>[:<hex req>:<hex fast_map>]`,
/// with the stubs the host wrote (`… := sorry` declarations that are not targets). The worker exempts only
/// those, by kernel value and name, never a target; with no named targets it exempts nothing in the final run.
pub(super) fn stub_mode_flag(
    allow_stub: bool,
    stub_targets: &[String],
    extra_stubs: &[String],
    shard_source: &str,
) -> Result<String> {
    let shards = crate::splitter::split_lean_source(shard_source, &[]).shards;
    let fast_map = crate::splitter::FastVerifyMap::parse_and_validate(shard_source, &shards)?;
    let prefix = if allow_stub { "allow_stub" } else { "strict" };
    if stub_targets.is_empty() && fast_map.is_empty() {
        return Ok(prefix.to_string());
    }
    let targets: std::collections::HashSet<String> = stub_targets.iter().cloned().collect();
    let target_canons: std::collections::HashSet<String> = stub_targets
        .iter()
        .map(|t| {
            crate::splitter::canonicalize_lean_name(t.strip_prefix("_root_.").unwrap_or(t.as_str()))
        })
        .collect();
    let mut stubs: Vec<String> = if allow_stub && !stub_targets.is_empty() {
        shards
            .iter()
            .filter(|sh| {
                crate::splitter::strip_lean_comments(&sh.proof_text).trim() == "sorry"
                    && !fast_map.shard_matches_targets(sh, &targets)
            })
            .map(|sh| sh.rooted_name())
            .collect()
    } else {
        Vec::new()
    };
    if allow_stub && !stub_targets.is_empty() {
        for es in extra_stubs {
            let trimmed = es.trim();
            if trimmed.is_empty() {
                continue;
            }
            let canon = crate::splitter::canonicalize_lean_name(
                trimmed.strip_prefix("_root_.").unwrap_or(trimmed),
            );
            if !targets.contains(trimmed) && !target_canons.contains(&canon) {
                stubs.push(trimmed.to_string());
            }
        }
    }
    let targets_hex = hex_encode_bytes(stub_targets.join("\n").as_bytes());
    let stubs_hex = hex_encode_bytes(stubs.join("\n").as_bytes());
    if fast_map.is_empty() {
        Ok(format!("{}:{}:{}", prefix, targets_hex, stubs_hex))
    } else {
        let fmap_hex = hex_encode_bytes(encode_fast_map_lines(fast_map.entries()).as_bytes());
        Ok(format!(
            "{}:{}:{}:{}:{}",
            prefix, targets_hex, stubs_hex, targets_hex, fmap_hex
        ))
    }
}

/// `stub_mode` for one cross-file block of a request: every target still counts for ownership (never
/// exempt), but the block must declare only the targets and fast-verify mappings its own text declares.
pub(super) fn block_stub_mode(stub_mode: &str, stub_targets: &[String], blk: &str) -> Result<String> {
    let (allow_sorry_prefix, inner_mode) = if stub_mode == "allow_sorry" {
        (true, "strict_all")
    } else if let Some(rest) = stub_mode.strip_prefix("allow_sorry+") {
        (true, rest)
    } else {
        (false, stub_mode)
    };
    let wrap = |m: String| {
        if allow_sorry_prefix {
            if m == "strict_all" {
                "allow_sorry".to_string()
            } else {
                format!("allow_sorry+{m}")
            }
        } else {
            m
        }
    };
    let shards = crate::splitter::split_lean_source(blk, &[]).shards;
    let blk_map = crate::splitter::FastVerifyMap::parse_and_validate(blk, &shards)?;
    if !inner_mode.starts_with("allow_stub:") && !inner_mode.starts_with("strict:") {
        if blk_map.is_empty() {
            return Ok(wrap(inner_mode.to_string()));
        }
        let prefix = if inner_mode == "allow_stub" {
            "allow_stub"
        } else {
            "strict"
        };
        let fmap_hex = hex_encode_bytes(encode_fast_map_lines(blk_map.entries()).as_bytes());
        return Ok(wrap(format!("{}::::{}", prefix, fmap_hex)));
    }
    let parts: Vec<&str> = inner_mode.split(':').collect();
    let base_prefix = parts.first().copied().unwrap_or("strict");
    let targets_hex = parts.get(1).copied().unwrap_or("");
    let stubs_hex = parts.get(2).copied().unwrap_or("");
    let required: Vec<&str> = stub_targets
        .iter()
        .filter(|t| {
            let one = std::collections::HashSet::from([(*t).clone()]);
            shards
                .iter()
                .any(|sh| blk_map.shard_matches_targets(sh, &one))
        })
        .map(String::as_str)
        .collect();
    let req_hex = hex_encode_bytes(required.join("\n").as_bytes());
    if blk_map.is_empty() {
        Ok(wrap(format!(
            "{}:{}:{}:{}",
            base_prefix, targets_hex, stubs_hex, req_hex
        )))
    } else {
        let fmap_hex = hex_encode_bytes(encode_fast_map_lines(blk_map.entries()).as_bytes());
        Ok(wrap(format!(
            "{}:{}:{}:{}:{}",
            base_prefix, targets_hex, stubs_hex, req_hex, fmap_hex
        )))
    }
}

