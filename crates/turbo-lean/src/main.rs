//! `turbo-lean` CLI Entrypoint.
//!
//! Modular Architecture:
//! - [`check`]: Theorem-level & directory-level incremental verification (`turbo-lean check`)
//! - [`db`]: Machine-wide SQLite WAL coordinator, Singleflight, and hardlinked CAS (`state.db`)
//! - [`gpu_fastcheck`]: Lean 4 -> CUDA / C++ AST transpiler & Perceus/CUDA fast-check (`turbo-lean fast-check`)
//! - [`lake_build`]: Lake environment resolution, `/dev/shm` stat-summary cache, and `turbo-lean build`
//! - [`pack`]: `.tlpack` archive export/import, remote HTTP clients, and delta sync
//! - [`pr_verify`]: Git tree-aware PR classifier (`turbo-lean pr-verify`) and CI gate (`turbo-lean ci-verify`)
//! - [`receipt`]: BLAKE3 / HMAC-BLAKE3 / Ed25519 cryptographic verification receipts
//! - [`server`]: HTTP remote coordinator (`turbo-lean serve`) and endpoint handlers
//! - [`shm_cache`]: Unified `/dev/shm` atomic write, quota LRU, and debug logging helpers
//! - [`splitter`]: Stateful AST Command Splitter, Scope Tracker, and Axiom Hygiene Scanner
//! - [`zygote`]: Persistent Lean 4 Zygote daemon and Prefix-Tree `fork()` Copy-on-Write cache

mod check;
mod db;
mod gpu_fastcheck;
mod lake_build;
mod pack;
mod pr_verify;
pub mod receipt;
pub mod server;
pub mod shm_cache;
mod splitter;
mod zygote;

pub use gpu_fastcheck::*;
pub use lake_build::*;
pub use pr_verify::*;

use anyhow::Result;
use clap::{Parser, Subcommand};
use db::TurboStore;
use std::fs;
use std::path::PathBuf;

#[derive(Parser)]
#[command(
    name = "turbo-lean",
    version,
    about = "High-performance, distributed build, verification, and counterexample tooling for Lean 4"
)]
struct Cli {
    /// Optional custom CAS & SQLite directory (defaults to $TURBO_LEAN_HOME or ~/.cache/turbo-lean)
    #[arg(long, global = true)]
    cache_dir: Option<PathBuf>,

    /// Output JSON results for agent/CI consumption
    #[arg(long, global = true)]
    json: bool,

    /// Optional memory budget cap in MiB (sets TURBO_LEAN_MAX_MEMORY_MB for hardware-adaptive governor)
    #[arg(long, global = true)]
    max_memory_mb: Option<u64>,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Incremental two-level CAS build with automatic multi-agent Singleflight coalescing
    Build {
        /// Optional Lake targets to build
        targets: Vec<String>,
        /// Project root directory
        #[arg(long, default_value = ".")]
        project_dir: PathBuf,
        /// Trust domain ('trusted' or 'untrusted:<id>')
        #[arg(long, default_value = "trusted")]
        trust_domain: String,
        /// Pin built artifacts in CAS (0=normal, 1=main_branch, 2=toolchain)
        #[arg(long, default_value_t = 0)]
        pin_level: i64,
        /// Seed TheoremProofCAS with all verified theorem shards after build completes
        #[arg(long, default_value_t = false)]
        seed_shards: bool,
    },
    /// Fast theorem-level or declaration-level check using PrefixEnv sharding & direct Lean env
    Check {
        /// Path to the .lean file to check
        file: PathBuf,
        /// Optional specific theorem/lemma declaration name to check in isolation
        #[arg(long)]
        decl: Option<String>,
        /// Project root directory
        #[arg(long, default_value = ".")]
        project_dir: PathBuf,
        /// Number of parallel worker threads for multi-shard verification (defaults to available parallelism or 4)
        #[arg(short, long)]
        jobs: Option<usize>,
        /// Verify uncached theorem shards concurrently across worker threads
        #[arg(long, default_value_t = false)]
        parallel_shards: bool,
        /// Offload uncached theorem shard verification to a remote `turbo-lean serve` HTTP endpoint (e.g. http://127.0.0.1:9400)
        #[arg(long)]
        remote_http: Option<String>,
    },
    /// Run native (leanc -O3 Perceus/FBIP) or GPU (CUDA) fast counterexample search
    FastCheck {
        /// Path to a .lean or .cu fast-check harness
        file: PathBuf,
        /// Force GPU (CUDA) mode
        #[arg(long, default_value_t = false)]
        gpu: bool,
        /// Transpile a specific Lean 4 theorem declaration (or the last theorem if `--transpile-lean auto`) into a GPU CUDA / C++ counterexample kernel
        #[arg(long, visible_alias = "decl")]
        transpile_lean: Option<String>,
        /// Offload execution to a remote `turbo-lean serve` HTTP endpoint (e.g. http://127.0.0.1:9400)
        #[arg(long)]
        remote_http: Option<String>,
        /// Offload execution to a remote GPU host via SSH (e.g. dgx-spark or th0rgal@100.77.4.93)
        #[arg(long)]
        remote_ssh: Option<String>,
        /// Optional SSH jump host (e.g. agent-core) when using --remote-ssh
        #[arg(long)]
        via_jump: Option<String>,
    },
    /// Show live machine-wide CAS, SQLite WAL, and Singleflight status
    Status,
    /// Run Cost-Aware GDSF garbage collection and prune stale/deleted worktrees
    Gc {
        /// Maximum reclaimable (unlinked) bytes to keep in CAS (e.g. 10737418240 for 10 GiB)
        #[arg(long, default_value_t = 10 * 1024 * 1024 * 1024)]
        max_reclaimable_bytes: u64,
        /// Prune worktrees not seen in more than N seconds (-1 to only prune deleted directories)
        #[arg(long, default_value_t = 7 * 86400)]
        prune_worktrees_older_than_secs: i64,
        /// Preserve pinned blobs (pin_level > 0)
        #[arg(long, default_value_t = true)]
        keep_pinned: bool,
    },
    /// Export deduplicated zstd CAS bundle (.tlpack) for CI or cross-machine sync
    Export {
        /// Output .tlpack file path
        #[arg(short, long)]
        output: PathBuf,
        /// Export only architecture-independent portable artifacts (.olean, .ilean, .c, expr_shard)
        #[arg(long, default_value_t = true)]
        portable_only: bool,
    },
    /// Import and BLAKE3-verify a .tlpack CAS bundle into local SQLite & CAS
    Import {
        /// Input .tlpack file path
        input: PathBuf,
    },
    /// Bidirectional delta synchronization with another machine (via HTTP URL or SSH host:path)
    Sync {
        /// Remote endpoint (e.g., http://100.77.4.93:9400 or ssh://dgx-spark)
        remote: String,
        /// Push only missing local actions/blobs to the remote coordinator via POST /import-delta (skip pull)
        #[arg(long, default_value_t = false)]
        push: bool,
        /// Explicitly perform bidirectional pull + push delta synchronization
        #[arg(long, default_value_t = false)]
        bidirectional: bool,
    },
    /// Run remote offload & CAS synchronization server (e.g., on DGX Spark)
    Serve {
        /// Listen address (host:port)
        #[arg(long, visible_alias = "bind", default_value = "0.0.0.0:9400")]
        listen: String,
        /// Enable CUDA GPU fast-check offload
        #[arg(long, default_value_t = false)]
        gpu_enable: bool,
    },
    /// CI verification gate with Trusted vs Untrusted PR sandboxing, axiom hygiene, and kernel attestation
    CiVerify {
        /// Verification mode: 'trusted' or 'untrusted'
        #[arg(long, default_value = "trusted")]
        mode: String,
        /// Project root directory
        #[arg(long, default_value = ".")]
        project_dir: PathBuf,
        /// Optional path to write a cryptographic JSON verification receipt
        #[arg(long)]
        receipt: Option<PathBuf>,
        /// Seed TheoremProofCAS with all verified theorem shards after CI verification succeeds
        #[arg(long, default_value_t = false)]
        seed_shards: bool,
    },
    /// Seed TheoremProofCAS with theorem shards from verified/hygienic project modules in a single SQLite transaction
    SeedShards {
        /// Project root directory
        #[arg(long, default_value = ".")]
        project_dir: PathBuf,
        /// Trust domain ('trusted' or 'untrusted:<id>')
        #[arg(long, default_value = "trusted")]
        trust_domain: String,
        /// Require a pre-compiled .olean in .lake/build/lib/lean for each seeded module
        #[arg(long, default_value_t = false)]
        require_olean: bool,
    },
    /// Verify a cryptographic CI verification receipt and detect any altered theorem statements in < 1 ms
    VerifyReceipt {
        /// Path to the verification receipt JSON file (positional)
        receipt: Option<PathBuf>,
        /// Path to the verification receipt JSON file (--receipt flag)
        #[arg(long = "receipt")]
        receipt_flag: Option<PathBuf>,
        /// Optional expected project-wide InterfaceHash (BLAKE3 hex)
        #[arg(long)]
        expected_interface_hash: Option<String>,
        /// Optional baseline receipt JSON file to diff per-file theorem interfaces against
        #[arg(long)]
        baseline_receipt: Option<PathBuf>,
    },
    /// Git-aware incremental PR verifier: diffs against `--base <git-ref>` and verifies only modified theorem proofs in isolation
    PrVerify {
        /// Project root directory
        #[arg(long, default_value = ".")]
        project_dir: PathBuf,
        /// Baseline git reference to compare against (e.g. HEAD, origin/main)
        #[arg(long, default_value = "HEAD")]
        base: String,
        /// Verification mode: 'trusted' or 'untrusted'
        #[arg(long, default_value = "trusted")]
        mode: String,
        /// Fail closed immediately if any theorem statement or definition signature changed relative to --base
        #[arg(long, default_value_t = false)]
        disallow_statement_changes: bool,
        /// Optional path to write a cryptographic JSON verification receipt
        #[arg(long)]
        receipt: Option<PathBuf>,
        /// Offload uncached theorem shard verification to a remote `turbo-lean serve` HTTP endpoint (e.g. http://127.0.0.1:9400)
        #[arg(long)]
        remote_http: Option<String>,
    },
    /// Unified sub-millisecond to few-millisecond agent verification funnel:
    /// Stage 0 (hygiene & cone cache) -> Stage 1 (spec vacuity & certified fast-check with hypothesis suggestion) -> Stage 2 (Zygote kernel verification)
    AgentStep {
        /// Path to the .lean file
        file: PathBuf,
        /// Optional declaration name to verify
        #[arg(long)]
        decl: Option<String>,
        /// Optional Lean project root
        #[arg(long)]
        project_dir: Option<PathBuf>,
        /// Enable low-memory mode
        #[arg(long)]
        low_memory: bool,
    },
    /// Audit theorem specifications for vacuous preconditions and postcondition tightness
    AuditSpec {
        /// Path to the .lean file
        file: PathBuf,
        /// Optional declaration name
        #[arg(long)]
        decl: Option<String>,
    },
    /// Deterministic fast evaluation of a Lean file (preserving all info/warning/error messages and stdout, drop-in for `lean <file.lean>`)
    Eval {
        /// Path to the Lean file to evaluate
        file: PathBuf,
        /// Project root directory (defaults to file parent or current directory)
        #[arg(long)]
        project_dir: Option<PathBuf>,
        /// Optional override for LEAN_PATH (defaults to LEAN_PATH env var or lake env)
        #[arg(long)]
        lean_path: Option<String>,
        /// Per-request wall-clock timeout in milliseconds (prints RSGB_TIMEOUT and exits 124 on timeout)
        #[arg(long, default_value_t = 30000)]
        timeout_ms: u64,
        /// Self-test determinism by comparing output against a fresh `lean <file>` process and failing closed on any difference
        #[arg(long)]
        verify_determinism: bool,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    if let Some(mb) = cli.max_memory_mb {
        std::env::set_var("TURBO_LEAN_MAX_MEMORY_MB", mb.to_string());
    }

    // Fast stateless paths that do not need to open SQLite (`state.db`):
    if let Commands::AuditSpec { ref file, ref decl } = cli.command {
        return gpu_fastcheck::run_audit_spec_command(file, decl.as_deref(), cli.json);
    }
    if let Commands::Serve {
        ref listen,
        gpu_enable,
    } = cli.command
    {
        return pack::run_server(cli.cache_dir.as_deref(), listen, gpu_enable);
    }
    if let Commands::VerifyReceipt {
        receipt,
        receipt_flag,
        expected_interface_hash,
        baseline_receipt,
    } = cli.command
    {
        return pr_verify::run_verify_receipt_command(
            cli.json,
            receipt,
            receipt_flag,
            expected_interface_hash,
            baseline_receipt,
        );
    }
    if let Commands::FastCheck {
        ref file,
        gpu,
        transpile_lean: None,
        remote_http: Some(ref http_url),
        ..
    } = cli.command
    {
        return gpu_fastcheck::run_fast_check_remote_http_stateless(
            cli.json, file, gpu, http_url,
        );
    }

    let resolved_cache_root = cli
        .cache_dir
        .clone()
        .or_else(|| std::env::var("TURBO_LEAN_HOME").ok().map(PathBuf::from))
        .unwrap_or_else(|| {
            let home = std::env::var("HOME").unwrap_or_else(|_| "/tmp".to_string());
            PathBuf::from(home).join(".cache").join("turbo-lean")
        });
    let db_warm_on_open = fs::metadata(resolved_cache_root.join("state.db"))
        .map(|m| m.len() >= 4096)
        .unwrap_or(false);

    // Overlap remote HTTP export/manifest fetch with SQLite schema initialization on cold sync
    let mut prefetched_export: Option<std::thread::JoinHandle<Result<pack::PrefetchedExportItem>>> =
        None;
    let mut prefetched_manifest: Option<std::thread::JoinHandle<Option<pack::DeltaManifest>>> =
        None;
    if let Commands::Sync {
        ref remote,
        push,
        bidirectional: false,
    } = cli.command
    {
        if remote.starts_with("http://") || remote.starts_with("https://") {
            let base = remote.trim_end_matches('/').to_string();
            if push {
                prefetched_manifest = Some(std::thread::spawn(move || {
                    let url = format!("{}/manifest", base);
                    pack::http_request("GET", &url, "application/json", &[])
                        .ok()
                        .and_then(|bytes| serde_json::from_slice(&bytes).ok())
                }));
            } else if !db_warm_on_open {
                let is_loopback =
                    base.starts_with("http://127.0.0.1") || base.starts_with("http://localhost");
                let url = if is_loopback {
                    format!("{}/export-local", base)
                } else {
                    format!("{}/export", base)
                };
                let root_for_prestage = resolved_cache_root.clone();
                prefetched_export = Some(std::thread::spawn(move || {
                    let bytes = pack::http_request("GET", &url, "application/octet-stream", &[])?;
                    let prestaged = pack::try_parse_v3_header(&bytes).and_then(|manifest| {
                        pack::prestage_blobs_from_shared_cas(&root_for_prestage, &manifest)
                            .map(|(staged, n)| (manifest, staged, n))
                    });
                    Ok((bytes, prestaged))
                }));
            }
        }
    }

    let mut store = TurboStore::open(cli.cache_dir.as_deref())?;

    match cli.command {
        Commands::Build {
            targets,
            project_dir,
            trust_domain,
            pin_level,
            seed_shards,
        } => lake_build::run_build_command(
            &mut store,
            cli.json,
            targets,
            project_dir,
            trust_domain,
            pin_level,
            seed_shards,
        ),

        Commands::Check {
            file,
            decl,
            project_dir,
            jobs,
            parallel_shards,
            remote_http,
        } => check::run_check_command(
            &mut store,
            db_warm_on_open,
            cli.json,
            file,
            decl,
            project_dir,
            jobs,
            parallel_shards,
            remote_http,
        ),

        Commands::FastCheck {
            file,
            gpu,
            transpile_lean,
            remote_http,
            remote_ssh,
            via_jump,
        } => gpu_fastcheck::run_fast_check_command(
            &store,
            cli.json,
            file,
            gpu,
            transpile_lean,
            remote_http,
            remote_ssh,
            via_jump,
        ),

        Commands::Status => {
            let st = store.storage_status()?;
            if cli.json {
                println!("{}", serde_json::to_string_pretty(&st)?);
            } else {
                println!("=== turbo-lean Machine-Wide CAS & Coordinator Status ===");
                println!("Cache Root              : {}", st.cache_root);
                println!("Completed Actions       : {}", st.total_actions);
                println!("Stored Immutable Blobs  : {}", st.total_blobs);
                println!("Total Shard Cache Hits  : {}", st.total_shard_hits);
                println!("Saved Compute Time      : {} ms", st.saved_compute_ms);
                println!("Active Worktrees        : {}", st.active_worktrees);
                println!("In-Flight Singleflights : {}", st.active_inflight_leases);
                println!("Coalesced Agent Saves   : {}", st.total_coalesced_waits);
                println!(
                    "Cached FastCheck Bins   : {} ({:.2} MiB)",
                    st.fastcheck_cached_bins,
                    st.fastcheck_cached_bytes as f64 / (1024.0 * 1024.0)
                );
                println!(
                    "Total Logical Bytes     : {:.2} MiB",
                    st.total_logical_bytes as f64 / (1024.0 * 1024.0)
                );
                println!(
                    "  - Reclaimable (nlink=1): {:.2} MiB",
                    st.reclaimable_bytes as f64 / (1024.0 * 1024.0)
                );
                println!(
                    "  - Retained by Worktrees: {:.2} MiB",
                    st.worktree_retained_bytes as f64 / (1024.0 * 1024.0)
                );
                println!(
                    "  - Pinned (main/stdlib) : {:.2} MiB",
                    st.pinned_bytes as f64 / (1024.0 * 1024.0)
                );
            }
            Ok(())
        }

        Commands::Gc {
            max_reclaimable_bytes,
            prune_worktrees_older_than_secs,
            keep_pinned,
        } => {
            let report = store.run_gc(
                max_reclaimable_bytes,
                prune_worktrees_older_than_secs,
                keep_pinned,
            )?;
            if cli.json {
                println!("{}", serde_json::to_string_pretty(&report)?);
            } else {
                println!(
                    "[turbo-lean] GC complete: pruned {} worktrees, evicted {} actions ({} blobs), cleaned {} staging files, pruned {} fastcheck bins, freed {} bytes ({} bytes remaining reclaimable)",
                    report.pruned_worktrees,
                    report.evicted_actions,
                    report.unlinked_blobs,
                    report.cleaned_staging_files,
                    report.pruned_fastcheck_bins,
                    report.freed_reclaimable_bytes,
                    report.remaining_reclaimable_bytes
                );
            }
            Ok(())
        }

        Commands::Export {
            output,
            portable_only,
        } => pack::run_export_command(&store, cli.json, output, portable_only),

        Commands::Import { input } => pack::run_import_command(&mut store, cli.json, input),

        Commands::Sync {
            remote,
            push,
            bidirectional,
        } => pack::run_sync_command(
            &mut store,
            cli.json,
            remote,
            push,
            bidirectional,
            prefetched_export,
            prefetched_manifest,
        ),

        Commands::Serve { listen, gpu_enable } => {
            pack::run_server(cli.cache_dir.as_deref(), &listen, gpu_enable)
        }

        Commands::CiVerify {
            mode,
            project_dir,
            receipt,
            seed_shards,
        } => pr_verify::run_ci_verify_command(
            &mut store,
            cli.json,
            mode,
            project_dir,
            receipt,
            seed_shards,
        ),

        Commands::SeedShards {
            project_dir,
            trust_domain,
            require_olean,
        } => pr_verify::run_seed_shards_command(
            &mut store,
            cli.json,
            project_dir,
            trust_domain,
            require_olean,
        ),

        Commands::VerifyReceipt {
            receipt,
            receipt_flag,
            expected_interface_hash,
            baseline_receipt,
        } => pr_verify::run_verify_receipt_command(
            cli.json,
            receipt,
            receipt_flag,
            expected_interface_hash,
            baseline_receipt,
        ),

        Commands::PrVerify {
            project_dir,
            base,
            mode,
            disallow_statement_changes,
            receipt,
            remote_http,
        } => pr_verify::run_pr_verify_command(
            &mut store,
            cli.json,
            project_dir,
            base,
            mode,
            disallow_statement_changes,
            receipt,
            remote_http,
        ),

        Commands::AgentStep {
            file,
            decl,
            project_dir,
            low_memory,
        } => gpu_fastcheck::run_agent_step_command(
            &store,
            &file,
            decl.as_deref(),
            project_dir.as_deref(),
            low_memory,
            cli.json,
        ),

        Commands::AuditSpec { file, decl } => {
            gpu_fastcheck::run_audit_spec_command(&file, decl.as_deref(), cli.json)
        }

        Commands::Eval {
            file,
            project_dir,
            lean_path,
            timeout_ms,
            verify_determinism,
        } => {
            let source = fs::read_to_string(&file)?;
            let proj_dir = project_dir.unwrap_or_else(|| {
                file.parent()
                    .filter(|p| !p.as_os_str().is_empty())
                    .map(|p| p.to_path_buf())
                    .unwrap_or_else(|| PathBuf::from("."))
            });
            let toolchain = lake_build::detect_toolchain(&proj_dir);
            let explicit_lp = lean_path
                .or_else(|| std::env::var("LEAN_PATH").ok())
                .filter(|s| !s.trim().is_empty());

            let (env_vars, lean_bin, req_lp) = if let Some(lp) = explicit_lp {
                let (mut ev, lb) = pack::resolve_server_lean_env_and_bin(&store, &toolchain, &lp);
                ev.insert("LEAN_PATH".to_string(), lp.clone());
                (ev, lb, lp)
            } else if let Ok((ev, _)) = lake_build::resolve_lake_env(&store, &proj_dir) {
                let lp = ev.get("LEAN_PATH").cloned().unwrap_or_default();
                let (_, lb) = pack::resolve_server_lean_env_and_bin(&store, &toolchain, &lp);
                (ev, lb, lp)
            } else {
                let (ev, lb) = pack::resolve_server_lean_env_and_bin(&store, &toolchain, "");
                let lp = ev.get("LEAN_PATH").cloned().unwrap_or_default();
                (ev, lb, lp)
            };

            let file_display = file.to_string_lossy().to_string();
            let reply = if let Some(daemon_rep) = zygote::try_local_zygote_eval(
                &store,
                &env_vars,
                &toolchain,
                &req_lp,
                &source,
                Some(&file_display),
                timeout_ms,
            ) {
                daemon_rep
            } else {
                zygote::eval_with_zygote_pool_opts(
                    &store,
                    &toolchain,
                    &req_lp,
                    &env_vars,
                    &lean_bin,
                    &source,
                    false,
                    true,
                    Some(&file_display),
                    Some(timeout_ms),
                )?
            };

            if reply.timed_out {
                println!("RSGB_TIMEOUT");
                std::process::exit(124);
            }

            let check_det = verify_determinism
                || std::env::var("TURBO_LEAN_VERIFY_DETERMINISM").as_deref() == Ok("1");
            if check_det {
                let mut cmd = std::process::Command::new(&lean_bin);
                cmd.arg(&file).envs(&env_vars);
                if !req_lp.is_empty() {
                    cmd.env("LEAN_PATH", &req_lp);
                }
                let lean_out = cmd.output()?;
                let lean_ok = lean_out.status.success();
                let mut turbo_lines: Vec<String> = Vec::new();
                if !reply.stdout.is_empty() {
                    for l in reply.stdout.lines() {
                        let t = l.trim_end();
                        if !t.is_empty() {
                            turbo_lines.push(t.to_string());
                        }
                    }
                }
                for m in &reply.messages {
                    for l in m.lines() {
                        let t = l.trim_end();
                        if !t.is_empty() {
                            turbo_lines.push(t.to_string());
                        }
                    }
                }
                let mut ref_lines: Vec<String> = Vec::new();
                for l in String::from_utf8_lossy(&lean_out.stdout).lines() {
                    let t = l.trim_end();
                    if !t.is_empty() {
                        ref_lines.push(t.to_string());
                    }
                }
                for l in String::from_utf8_lossy(&lean_out.stderr).lines() {
                    let t = l.trim_end();
                    if !t.is_empty() {
                        ref_lines.push(t.to_string());
                    }
                }
                if reply.ok != lean_ok || turbo_lines != ref_lines {
                    eprintln!(
                        "[turbo-lean eval --verify-determinism] Mismatch against `lean {}`!\n  turbo ok={} lines={:?}\n  lean  ok={} lines={:?}",
                        file.display(),
                        reply.ok,
                        turbo_lines,
                        lean_ok,
                        ref_lines
                    );
                    std::process::exit(2);
                }
            }

            if cli.json {
                println!("{}", serde_json::to_string_pretty(&reply)?);
                if !reply.ok {
                    std::process::exit(1);
                }
                return Ok(());
            }

            if !reply.stdout.is_empty() {
                print!("{}", reply.stdout);
                if !reply.stdout.ends_with('\n') {
                    println!();
                }
            }
            for msg in &reply.messages {
                println!("{}", msg);
            }
            if !reply.ok && reply.messages.is_empty() {
                for err in &reply.errors {
                    println!("{}", err);
                }
            }
            if !reply.ok {
                std::process::exit(1);
            }
            Ok(())
        }
    }
}
