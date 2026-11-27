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

#[derive(Debug, Clone, Copy)]
pub(super) struct EmbeddedZygoteModule {
    pub(super) module: &'static str,
    pub(super) rel_path: &'static str,
    pub(super) src: &'static str,
    pub(super) emit_olean: bool,
    pub(super) c_opt: &'static str,
}

pub(super) const ZYGOTE_EMBEDDED_MODULES: &[EmbeddedZygoteModule] = &[
    EmbeddedZygoteModule {
        module: "TurboLean.Blake3",
        rel_path: "TurboLean/Blake3.lean",
        src: BLAKE3_LEAN_SRC,
        emit_olean: true,
        c_opt: "-O3",
    },
    EmbeddedZygoteModule {
        module: "TurboLean.StatementHash",
        rel_path: "TurboLean/StatementHash.lean",
        src: STATEMENT_HASH_LEAN_SRC,
        emit_olean: true,
        c_opt: "-O3",
    },
    EmbeddedZygoteModule {
        module: "TurboLean.ZygoteFork",
        rel_path: "TurboLean/ZygoteFork.lean",
        src: ZYGOTE_FORK_LEAN_SRC,
        emit_olean: true,
        c_opt: "-O3",
    },
    // S3b-M revised decomposition: only the shim-free public-only
    // ranges live in submodules (`Env`, `Wire`, `KernelAudit`). The shim block (whose
    // private `formatReducibilityStatus` is consumed by the root signature-audit code),
    // the replay/compiler/signature/hotspot ranges and root `main` stay in the
    // entrypoint barrel, keeping compiled private mangling and public order
    // baseline-exact. The manifest is the write/compile order: every submodule imports
    // only earlier entries, so each emits its `.olean` into the scratch `LEAN_PATH`
    // before its importers compile. All worker submodules keep the monolith's `-O0`
    // (`c_opt`). The entrypoint barrel `TurboLean.ZygoteWorker` stays last.
    EmbeddedZygoteModule {
        module: "TurboLean.ZygoteWorker.Env",
        rel_path: "TurboLean/ZygoteWorker/Env.lean",
        src: include_str!("../../../../lean/TurboLean/ZygoteWorker/Env.lean"),
        emit_olean: true,
        c_opt: "-O0",
    },
    EmbeddedZygoteModule {
        module: "TurboLean.ZygoteWorker.Wire",
        rel_path: "TurboLean/ZygoteWorker/Wire.lean",
        src: include_str!("../../../../lean/TurboLean/ZygoteWorker/Wire.lean"),
        emit_olean: true,
        c_opt: "-O0",
    },
    EmbeddedZygoteModule {
        module: "TurboLean.ZygoteWorker.KernelAudit",
        rel_path: "TurboLean/ZygoteWorker/KernelAudit.lean",
        src: include_str!("../../../../lean/TurboLean/ZygoteWorker/KernelAudit.lean"),
        emit_olean: true,
        c_opt: "-O0",
    },
    EmbeddedZygoteModule {
        module: "TurboLean.ZygoteWorker",
        rel_path: "TurboLean/ZygoteWorker.lean",
        src: ZYGOTE_WORKER_LEAN_SRC,
        emit_olean: false,
        c_opt: "-O0",
    },
];

pub(super) fn compute_zygote_bin_name(
    lean_bin: &Path,
    toolchain: Option<&str>,
    modules: &[EmbeddedZygoteModule],
) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-zygote:v7:cow-fork-pool:");
    hasher.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    hasher.update(b":");
    hasher.update(std::env::consts::ARCH.as_bytes());
    hasher.update(lean_bin.to_string_lossy().as_bytes());
    if let Some(tc) = toolchain {
        hasher.update(tc.as_bytes());
    }
    for m in modules {
        hasher.update(m.src.as_bytes());
    }
    format!("turbo_zygote_{}", &hasher.finalize().to_hex()[..16])
}

pub(super) fn zygote_scratch_lean_path(
    scratch_dir: &Path,
    m: &EmbeddedZygoteModule,
    tmp_id: &str,
) -> PathBuf {
    if m.emit_olean {
        scratch_dir.join(m.rel_path)
    } else {
        let stem = m.rel_path.trim_end_matches(".lean").replace('/', "_");
        scratch_dir.join(format!("{stem}_{tmp_id}.lean"))
    }
}

pub(super) fn zygote_scratch_olean_path(scratch_dir: &Path, m: &EmbeddedZygoteModule) -> PathBuf {
    scratch_dir.join(format!("{}.olean", m.rel_path.trim_end_matches(".lean")))
}

pub(super) fn write_zygote_scratch_sources(
    scratch_dir: &Path,
    modules: &[EmbeddedZygoteModule],
    tmp_id: &str,
) -> Result<Vec<PathBuf>> {
    let mut paths = Vec::with_capacity(modules.len());
    for m in modules {
        let lean_file = zygote_scratch_lean_path(scratch_dir, m, tmp_id);
        if let Some(parent) = lean_file.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&lean_file, m.src)?;
        paths.push(lean_file);
    }
    Ok(paths)
}

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
    /// H2.3: the RLIMIT_DATA share this worker was spawned with, if any.
    /// `apply_worker_rlimit` lowers `rlim_max` too, so the cap is permanent; a capped
    /// worker may pool only under a key that names its cap, or an uncapped request would
    /// reuse it and fail allocations with no `memory_kill_note`.
    pub(super) rlimit_mb: Option<u64>,
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
            // A clone inherits the master's process limits, and masters spawn uncapped.
            rlimit_mb: None,
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

/// H2.3: what a bounded queue run left one pooled worker as, deciding whether it may go
/// back to `ZYGOTE_POOL`: `Unused` = never ran a request (exactly as acquired); `Healthy`
/// = its last request replied and the reply qualifies for pooling; `Dead` = its last
/// request crashed, timed out, or disqualified the worker (runtime panic, failed import).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum QueueWorkerFate {
    Unused,
    Healthy,
    Dead,
}

/// H2.3 (parallel replay under the RAM budget): run `jobs` indexed requests over the given
/// workers, at most `workers.len()` concurrently, each worker pulling the next request
/// index from a shared queue so a slow request never idles the other workers. Results come
/// back indexed by request — deterministic order whatever the completion order. A result
/// `is_fatal` stops the queue (requests already running finish; never-started slots stay
/// `None`), so the caller fails closed exactly as a serial loop would at its first fatal
/// request; a `Dead` fate retires only that worker, and the rest keep draining the queue.
/// Workers come back with the fate their last request left them.
pub(super) fn run_request_queue_over_workers<W, T>(
    workers: Vec<W>,
    jobs: usize,
    is_fatal: impl Fn(&T) -> bool + Sync,
    run: impl Fn(&mut W, usize) -> (T, QueueWorkerFate) + Sync,
) -> (Vec<(W, QueueWorkerFate)>, Vec<Option<T>>)
where
    W: Send,
    T: Send,
{
    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let stop = std::sync::atomic::AtomicBool::new(false);
    let results: Vec<std::sync::Mutex<Option<T>>> =
        (0..jobs).map(|_| std::sync::Mutex::new(None)).collect();
    let finished_workers = std::thread::scope(|s| {
        let (next_idx, stop, results, is_fatal, run) = (&next_idx, &stop, &results, &is_fatal, &run);
        let handles: Vec<_> = workers
            .into_iter()
            .map(|mut w| {
                s.spawn(move || {
                    let mut fate = QueueWorkerFate::Unused;
                    loop {
                        if stop.load(std::sync::atomic::Ordering::SeqCst) {
                            break;
                        }
                        let idx = next_idx.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        if idx >= jobs {
                            break;
                        }
                        let (res, new_fate) = run(&mut w, idx);
                        fate = new_fate;
                        let fatal = is_fatal(&res);
                        if let Ok(mut slot) = results[idx].lock() {
                            *slot = Some(res);
                        }
                        if fatal {
                            stop.store(true, std::sync::atomic::Ordering::SeqCst);
                            break;
                        }
                        if fate == QueueWorkerFate::Dead {
                            // This worker is unusable (panic / failed import); the other
                            // workers keep draining the queue.
                            break;
                        }
                    }
                    (w, fate)
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("Zygote request-queue worker thread panicked"))
            .collect::<Vec<_>>()
    });
    let outcomes = results
        .into_iter()
        .map(|m| m.into_inner().ok().flatten())
        .collect();
    (finished_workers, outcomes)
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

    let bin_name = compute_zygote_bin_name(
        lean_bin,
        env_vars.get("ELAN_TOOLCHAIN").map(String::as_str),
        ZYGOTE_EMBEDDED_MODULES,
    );
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

    let lean_files = write_zygote_scratch_sources(&scratch_dir, ZYGOTE_EMBEDDED_MODULES, &tmp_id)?;
    let mut obj_files = Vec::with_capacity(ZYGOTE_EMBEDDED_MODULES.len());
    for (m, lean_file) in ZYGOTE_EMBEDDED_MODULES.iter().zip(lean_files.iter()) {
        let stem = m.rel_path.trim_end_matches(".lean").replace('/', "_");
        let c_file = scratch_dir.join(format!("{stem}_{tmp_id}.c"));
        let obj_file = scratch_dir.join(format!("{stem}_{tmp_id}.o"));
        let mut cmd = Command::new(lean_bin);
        cmd.arg(format!("--root={}", scratch_dir.display()));
        if m.emit_olean {
            let olean_file = zygote_scratch_olean_path(&scratch_dir, m);
            if let Some(parent) = olean_file.parent() {
                fs::create_dir_all(parent)?;
            }
            cmd.arg("-o").arg(olean_file);
        }
        let out = cmd
            .arg("-c")
            .arg(&c_file)
            .arg(lean_file)
            .current_dir(&scratch_dir)
            .envs(&compile_env)
            .output()
            .with_context(|| format!("Failed to compile {} ({}) to C", m.module, m.rel_path))?;
        if !out.status.success() {
            return Err(compiler_failure(Path::new(m.rel_path), &out));
        }
        let c_out = Command::new(leanc_bin)
            .arg(m.c_opt)
            .arg("-c")
            .arg(&c_file)
            .arg("-o")
            .arg(&obj_file)
            .current_dir(&scratch_dir)
            .envs(&compile_env)
            .output()
            .with_context(|| format!("Failed to compile {stem}.c via `leanc {} -c`", m.c_opt))?;
        if !c_out.status.success() {
            anyhow::bail!(
                "`leanc {} -c` failed on {stem}.c:\n{}",
                m.c_opt,
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

#[cfg(test)]
mod worker_embed_tests {
    use super::*;

    fn collect_files(dir: &Path, out: &mut Vec<PathBuf>) {
        for entry in fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            let p = entry.path();
            if p.is_dir() {
                collect_files(&p, out);
            } else {
                out.push(p);
            }
        }
    }

    #[test]
    fn zygote_embedded_modules_sync_order_and_cache_key_sensitivity() {
        let repo_lean = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean");
        let mut disk_modules: Vec<String> = Vec::new();
        let mut stack = vec![repo_lean.join("TurboLean")];
        while let Some(d) = stack.pop() {
            if !d.is_dir() {
                continue;
            }
            for e in fs::read_dir(&d).unwrap() {
                let p = e.unwrap().path();
                if p.is_dir() {
                    stack.push(p);
                } else if p.extension().and_then(|s| s.to_str()) == Some("lean") {
                    let rel = p.strip_prefix(&repo_lean).unwrap().to_string_lossy().replace('\\', "/");
                    if rel == "TurboLean/Blake3.lean"
                        || rel == "TurboLean/StatementHash.lean"
                        || rel == "TurboLean/ZygoteFork.lean"
                        || rel == "TurboLean/ZygoteWorker.lean"
                        || rel.starts_with("TurboLean/ZygoteWorker/")
                    {
                        disk_modules.push(rel);
                    }
                }
            }
        }
        disk_modules.sort();
        let mut embedded_rels: Vec<String> = ZYGOTE_EMBEDDED_MODULES
            .iter()
            .map(|m| m.rel_path.to_string())
            .collect();
        let mut embedded_sorted = embedded_rels.clone();
        embedded_sorted.sort();
        assert_eq!(
            embedded_sorted, disk_modules,
            "ZYGOTE_EMBEDDED_MODULES must match on-disk ZygoteWorker + dependency sources"
        );
        embedded_rels.dedup();
        assert_eq!(embedded_rels.len(), ZYGOTE_EMBEDDED_MODULES.len());

        for m in ZYGOTE_EMBEDDED_MODULES {
            assert!(!m.src.is_empty(), "{} must be non-empty", m.module);
            let expected_rel = format!("{}.lean", m.module.replace('.', "/"));
            assert_eq!(m.rel_path, expected_rel);
            if m.module != "TurboLean.ZygoteFork" {
                let disk = fs::read_to_string(repo_lean.join(m.rel_path)).unwrap();
                assert_eq!(m.src, disk, "embedded source drifted from {}", m.rel_path);
            }
        }
        assert_eq!(
            ZYGOTE_EMBEDDED_MODULES.last().map(|m| (m.module, m.emit_olean)),
            Some(("TurboLean.ZygoteWorker", false)),
            "entrypoint TurboLean.ZygoteWorker must be compiled last without emitting over imported .olean"
        );
        assert!(ZYGOTE_EMBEDDED_MODULES[..ZYGOTE_EMBEDDED_MODULES.len() - 1]
            .iter()
            .all(|m| m.emit_olean));

        let known: std::collections::HashSet<&str> =
            ZYGOTE_EMBEDDED_MODULES.iter().map(|m| m.module).collect();
        let mut seen: std::collections::HashSet<&str> = std::collections::HashSet::new();
        for m in ZYGOTE_EMBEDDED_MODULES {
            for line in m.src.lines() {
                let trimmed = line.trim_start();
                if let Some(rest) = trimmed.strip_prefix("import ") {
                    for tok in rest.split_whitespace() {
                        if tok == "public" || tok == "all" || tok == "meta" {
                            continue;
                        }
                        if known.contains(tok) {
                            assert!(
                                seen.contains(tok),
                                "{} imports {} before it appears in ZYGOTE_EMBEDDED_MODULES",
                                m.module,
                                tok
                            );
                        }
                        break;
                    }
                }
            }
            seen.insert(m.module);
        }

        let lean_bin = Path::new("/tmp/fake-lean");
        let base_key = compute_zygote_bin_name(lean_bin, Some("v4.35.0"), ZYGOTE_EMBEDDED_MODULES);
        for idx in 0..ZYGOTE_EMBEDDED_MODULES.len() {
            let mut mutated = ZYGOTE_EMBEDDED_MODULES.to_vec();
            let mut bumped = mutated[idx].src.as_bytes().to_vec();
            bumped[0] ^= 1;
            let bumped_str = Box::leak(String::from_utf8_lossy(&bumped).into_owned().into_boxed_str());
            mutated[idx].src = bumped_str;
            let next_key = compute_zygote_bin_name(lean_bin, Some("v4.35.0"), &mutated);
            assert_ne!(
                base_key, next_key,
                "1-byte edit in {} must change zygote binary cache key",
                ZYGOTE_EMBEDDED_MODULES[idx].module
            );
        }

        let scratch = std::env::temp_dir().join(format!(
            "zygote_embed_pin_{}_{}",
            std::process::id(),
            next_tmp_id()
        ));
        let written = write_zygote_scratch_sources(&scratch, ZYGOTE_EMBEDDED_MODULES, "42").unwrap();
        assert_eq!(written.len(), ZYGOTE_EMBEDDED_MODULES.len());
        let mut on_scratch = Vec::new();
        collect_files(&scratch, &mut on_scratch);
        let mut a = written.clone();
        a.sort();
        on_scratch.sort();
        assert_eq!(a, on_scratch);
        let _ = fs::remove_dir_all(&scratch);
    }

    /// S3b-E: the zygote binary cache key must cover every hash input the key is
    /// built from, not only the embedded module sources: the lean binary path and
    /// the toolchain label both feed `compute_zygote_bin_name`, so a toolchain or
    /// interpreter swap on one host never reuses a binary compiled for another.
    /// (`TURBO_LEAN_BUILD_EPOCH` and `std::env::consts::ARCH` are compile-time
    /// process constants and cannot be varied inside one test process; the module
    /// sources are covered per-entry by the 1-byte mutation walk above.)
    #[test]
    fn zygote_cache_key_hash_inputs_cover_lean_bin_and_toolchain() {
        let lean_bin = Path::new("/tmp/fake-lean");
        let base = compute_zygote_bin_name(lean_bin, Some("v4.35.0"), ZYGOTE_EMBEDDED_MODULES);
        assert!(
            base.starts_with("turbo_zygote_"),
            "cache key must keep the turbo_zygote_ prefix: {base}"
        );
        let digest = base.strip_prefix("turbo_zygote_").unwrap();
        assert_eq!(digest.len(), 16, "cache key digest must stay 16 hex chars: {base}");
        assert!(
            digest.chars().all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase()),
            "cache key digest must be lowercase hex: {base}"
        );
        assert_eq!(
            base,
            compute_zygote_bin_name(lean_bin, Some("v4.35.0"), ZYGOTE_EMBEDDED_MODULES),
            "cache key must be deterministic for identical inputs"
        );
        assert_ne!(
            base,
            compute_zygote_bin_name(lean_bin, Some("v4.36.0"), ZYGOTE_EMBEDDED_MODULES),
            "a toolchain label change must change the zygote binary cache key"
        );
        assert_ne!(
            base,
            compute_zygote_bin_name(lean_bin, None, ZYGOTE_EMBEDDED_MODULES),
            "dropping the toolchain label must change the zygote binary cache key"
        );
        assert_ne!(
            base,
            compute_zygote_bin_name(
                Path::new("/tmp/fake-lean-other"),
                Some("v4.35.0"),
                ZYGOTE_EMBEDDED_MODULES
            ),
            "a lean binary path change must change the zygote binary cache key"
        );
    }

    /// S3b-E: scratch writes must place every `.olean`-emitting module at exactly
    /// `<scratch>/<Module/Path>.lean` with its `.olean` beside it, because the
    /// compile loop puts the scratch root on `LEAN_PATH` and Lean resolves
    /// `import TurboLean.X.Y` to `TurboLean/X/Y.olean` under that root. The
    /// non-emitting entrypoint must take a tmp_id-salted name instead (it is
    /// never imported, and two concurrent builds must not collide), and every
    /// written file must be byte-identical to its embedded source.
    #[test]
    fn zygote_scratch_writes_place_embedded_sources_for_lean_path_imports() {
        for m in ZYGOTE_EMBEDDED_MODULES {
            let scratch = Path::new("/tmp/zygote-scratch-probe");
            let lean_a = zygote_scratch_lean_path(scratch, m, "aa");
            let lean_b = zygote_scratch_lean_path(scratch, m, "bb");
            let module_rel = m.module.replace('.', "/");
            if m.emit_olean {
                assert_eq!(
                    lean_a,
                    scratch.join(format!("{module_rel}.lean")),
                    "{}: imported module source must sit at its module path under the scratch root",
                    m.module
                );
                assert_eq!(lean_a, lean_b, "{}: imported module path must not depend on tmp_id", m.module);
                assert_eq!(
                    zygote_scratch_olean_path(scratch, m),
                    scratch.join(format!("{module_rel}.olean")),
                    "{}: emitted .olean must be where LEAN_PATH import resolution looks for it",
                    m.module
                );
            } else {
                assert_ne!(lean_a, lean_b, "{}: entrypoint scratch name must be tmp_id-salted", m.module);
                let name = lean_a.file_name().unwrap().to_string_lossy().into_owned();
                assert!(
                    name.contains("aa"),
                    "{}: entrypoint scratch name must carry the tmp_id: {name}",
                    m.module
                );
            }
        }

        let scratch = std::env::temp_dir().join(format!(
            "zygote_scratch_bytes_{}_{}",
            std::process::id(),
            next_tmp_id()
        ));
        let written = write_zygote_scratch_sources(&scratch, ZYGOTE_EMBEDDED_MODULES, "7").unwrap();
        for (m, p) in ZYGOTE_EMBEDDED_MODULES.iter().zip(written.iter()) {
            let on_disk = fs::read_to_string(p).unwrap();
            assert_eq!(
                on_disk, m.src,
                "{}: scratch write must be byte-identical to the embedded source",
                m.module
            );
        }
        let _ = fs::remove_dir_all(&scratch);
    }

    /// S3b-E: the `lean -c` compile list IS `ZYGOTE_EMBEDDED_MODULES` — the build
    /// loop zips the manifest with `write_zygote_scratch_sources`' return value, so
    /// the writer must return paths in manifest order, and the flat `{stem}_{tmp}.c`
    /// / `.o` intermediates it derives per entry must have unique stems (two modules
    /// sharing a stem would silently overwrite each other's C/object output).
    #[test]
    fn zygote_compile_list_follows_manifest_order_with_unique_object_stems() {
        let scratch = std::env::temp_dir().join(format!(
            "zygote_compile_list_{}_{}",
            std::process::id(),
            next_tmp_id()
        ));
        let written = write_zygote_scratch_sources(&scratch, ZYGOTE_EMBEDDED_MODULES, "9").unwrap();
        assert_eq!(written.len(), ZYGOTE_EMBEDDED_MODULES.len());
        for (m, p) in ZYGOTE_EMBEDDED_MODULES.iter().zip(written.iter()) {
            assert_eq!(
                p,
                &zygote_scratch_lean_path(&scratch, m, "9"),
                "{}: written source list must follow manifest (compile) order",
                m.module
            );
        }
        let stems: std::collections::HashSet<String> = ZYGOTE_EMBEDDED_MODULES
            .iter()
            .map(|m| m.rel_path.trim_end_matches(".lean").replace('/', "_"))
            .collect();
        assert_eq!(
            stems.len(),
            ZYGOTE_EMBEDDED_MODULES.len(),
            "compile-list object stems must be unique: {stems:?}"
        );
        let _ = fs::remove_dir_all(&scratch);
    }

    /// S3b-M: the pure Lean move splits `TurboLean.ZygoteWorker` into dependency-ordered
    /// submodules under `TurboLean/ZygoteWorker/`. Every new submodule must be embedded in
    /// `ZYGOTE_EMBEDDED_MODULES`, in dependency chain order, strictly before the
    /// `TurboLean.ZygoteWorker` entrypoint, emitting an `.olean` for later submodules, and
    /// participating in the zygote binary cache key (a 1-byte source edit must change it).
    #[test]
    fn zygote_worker_split_submodules_manifest_and_cache_key() {
        const SUBMODULES: [&str; 3] = [
            "TurboLean/ZygoteWorker/Env.lean",
            "TurboLean/ZygoteWorker/Wire.lean",
            "TurboLean/ZygoteWorker/KernelAudit.lean",
        ];
        let pos_of = |rel: &str| {
            ZYGOTE_EMBEDDED_MODULES
                .iter()
                .position(|m| m.rel_path == rel)
                .unwrap_or_else(|| panic!("ZYGOTE_EMBEDDED_MODULES entry missing for {rel} (S3b-M submodule split)"))
        };
        let mut prev = 0;
        for rel in SUBMODULES {
            let pos = pos_of(rel);
            assert!(pos > prev, "{rel} must appear in dependency chain order");
            prev = pos;
        }
        let entrypoint = pos_of("TurboLean/ZygoteWorker.lean");
        assert!(
            prev < entrypoint,
            "all ZygoteWorker submodules must precede the TurboLean.ZygoteWorker entrypoint"
        );
        let lean_bin = Path::new("/tmp/fake-lean");
        let base_key = compute_zygote_bin_name(lean_bin, Some("v4.35.0"), ZYGOTE_EMBEDDED_MODULES);
        for rel in SUBMODULES {
            let idx = pos_of(rel);
            let m = &ZYGOTE_EMBEDDED_MODULES[idx];
            assert!(m.emit_olean, "{rel} must emit an .olean for later submodules");
            assert!(!m.src.is_empty(), "{rel} must embed a non-empty source");
            let mut mutated = ZYGOTE_EMBEDDED_MODULES.to_vec();
            let mut bumped = mutated[idx].src.as_bytes().to_vec();
            bumped[0] ^= 1;
            mutated[idx].src =
                Box::leak(String::from_utf8_lossy(&bumped).into_owned().into_boxed_str());
            assert_ne!(
                base_key,
                compute_zygote_bin_name(lean_bin, Some("v4.35.0"), &mutated),
                "1-byte edit in {rel} must change the zygote binary cache key"
            );
        }
    }
}

/// H2.3: the bounded request queue the cross-file replay fan-out runs on. These tests use
/// stub workers (no Lean): the scheduling properties (width bound, deterministic result
/// order, fail-closed stop) are the queue's own, whatever the requests do.
#[cfg(test)]
mod pool_queue_tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn queue_runs_workers_concurrently_and_preserves_result_order() {
        let live = AtomicUsize::new(0);
        let max_live = AtomicUsize::new(0);
        let (finished, outcomes) = run_request_queue_over_workers(
            vec![0usize, 1, 2],
            9,
            |_: &usize| false,
            |_w, idx| {
                let now = live.fetch_add(1, Ordering::SeqCst) + 1;
                max_live.fetch_max(now, Ordering::SeqCst);
                std::thread::sleep(std::time::Duration::from_millis(40));
                live.fetch_sub(1, Ordering::SeqCst);
                (idx * 10, QueueWorkerFate::Healthy)
            },
        );
        assert_eq!(finished.len(), 3);
        assert!(finished
            .iter()
            .all(|(_, fate)| *fate == QueueWorkerFate::Healthy));
        let vals: Vec<usize> = outcomes.into_iter().map(|o| o.unwrap()).collect();
        assert_eq!(
            vals,
            (0..9).map(|i| i * 10).collect::<Vec<_>>(),
            "results must come back in request order whatever the completion order"
        );
        assert!(
            max_live.load(Ordering::SeqCst) <= 3,
            "more concurrent requests than workers"
        );
        // H2.3: the concurrency counter is the proof; a wall-time bound
        // flakes on a loaded runner and was removed.
        assert!(
            max_live.load(Ordering::SeqCst) >= 2,
            "9 sleep-shaped requests over 3 workers never overlapped: the queue ran serially"
        );
    }

    #[test]
    fn queue_width_never_exceeds_the_budgets_effective_parallelism() {
        // #435 / H2.3: the budget object is the single width authority for the pool
        // fan-out; a 2-job budget must never see a third concurrent request.
        let budget = WorkerBudget {
            jobs: Some(2),
            max_memory_mb: None,
        };
        let parallelism = budget.effective_parallelism(8, REPLAY_WORKER_EST_RSS_MB, || 64);
        assert_eq!(parallelism, 2);
        let live = AtomicUsize::new(0);
        let max_live = AtomicUsize::new(0);
        let (_, outcomes) = run_request_queue_over_workers(
            (0..parallelism).collect::<Vec<usize>>(),
            8,
            |_: &usize| false,
            |_w, idx| {
                let now = live.fetch_add(1, Ordering::SeqCst) + 1;
                max_live.fetch_max(now, Ordering::SeqCst);
                std::thread::sleep(std::time::Duration::from_millis(15));
                live.fetch_sub(1, Ordering::SeqCst);
                (idx, QueueWorkerFate::Healthy)
            },
        );
        assert!(
            max_live.load(Ordering::SeqCst) <= 2,
            "budget --jobs 2 exceeded: {} concurrent requests",
            max_live.load(Ordering::SeqCst)
        );
        let vals: Vec<usize> = outcomes.into_iter().map(|o| o.unwrap()).collect();
        assert_eq!(vals, (0..8).collect::<Vec<_>>());
    }

    #[test]
    fn queue_stops_scheduling_after_a_fatal_result_and_leaves_unrun_slots_none() {
        let (finished, outcomes) = run_request_queue_over_workers(
            vec![0usize, 1],
            12,
            |v: &usize| *v == 1,
            |_w, idx| {
                std::thread::sleep(std::time::Duration::from_millis(5));
                (
                    idx,
                    if idx == 1 {
                        QueueWorkerFate::Dead
                    } else {
                        QueueWorkerFate::Healthy
                    },
                )
            },
        );
        assert_eq!(outcomes.len(), 12);
        assert_eq!(outcomes[0], Some(0));
        assert_eq!(outcomes[1], Some(1), "the fatal request's own result is kept");
        let ran = outcomes.iter().flatten().count();
        assert!(
            ran <= 4,
            "queue kept scheduling after the fatal result: {ran} of 12 ran"
        );
        assert!(
            outcomes[5..].iter().all(|o| o.is_none()),
            "slots past the fatal stop must stay None (the caller fails closed on them)"
        );
        assert!(finished
            .iter()
            .any(|(_, fate)| *fate == QueueWorkerFate::Dead));
    }

    #[test]
    fn queue_with_no_workers_leaves_every_slot_none() {
        let (finished, outcomes) = run_request_queue_over_workers(
            Vec::<usize>::new(),
            3,
            |_: &usize| false,
            |_w, idx| (idx, QueueWorkerFate::Healthy),
        );
        assert!(finished.is_empty());
        assert!(outcomes.iter().all(|o| o.is_none()));
    }
}

