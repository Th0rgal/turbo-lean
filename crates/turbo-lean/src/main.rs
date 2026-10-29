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

pub mod accel_fastcheck;
pub mod accelerators;
pub mod matryoshka;
mod check;
pub mod cluster;
mod db;
mod gpu_fastcheck;
mod lake_build;
pub mod mcp;
pub mod module_builder;
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
        /// Optional verification timeout in seconds (0 = unlimited)
        #[arg(long, default_value_t = 0)]
        timeout: u64,
        /// Kernel verification engine (`standard`, `con-leche`, or `both`)
        #[arg(long, default_value = "standard")]
        kernel: String,
    },
    /// Run native (leanc -O3 Perceus/FBIP), GPU (CUDA), or Google Cloud TPU v5e (MLIR/XLA) fast counterexample search
    FastCheck {
        /// Path to a .lean or .cu fast-check harness
        file: PathBuf,
        /// Compute backend selection: `auto` (Law 15 hardware/cluster router), `cpu`, `gpu`, or `tpu`
        #[arg(long, default_value = "auto")]
        backend: String,
        /// Force GPU (CUDA) mode
        #[arg(long, default_value_t = false)]
        gpu: bool,
        /// Force Google Cloud TPU v5e (MLIR / XLA / StableHLO) fast-check mode
        #[arg(long, default_value_t = false)]
        tpu: bool,
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
    /// Inspect local & federated multi-server cluster status, Law 15 route selection, and Lean C-ABI vs Rust speed audit
    ClusterStatus {
        /// Run the empirical Lean 4 C-ABI (`@[export]`) vs Rust speed audit (1M iterations)
        #[arg(long, default_value_t = false)]
        bench_cabi: bool,
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
        /// Optional Lean project root directory
        #[arg(long)]
        project_dir: Option<PathBuf>,
    },
    /// Export deduplicated zstd CAS bundle (.tlpack) for CI or cross-machine sync
    Export {
        /// Output .tlpack file path
        #[arg(short, long)]
        output: PathBuf,
        /// Export only architecture-independent portable artifacts (.olean, .ilean, .c, expr_shard)
        #[arg(long, default_value_t = true)]
        portable_only: bool,
        /// Optional Ed25519 private signing key (32-byte hex seed; falls back to TURBO_LEAN_PACK_SIGNING_KEY)
        #[arg(long)]
        signing_key: Option<String>,
    },
    /// Import and BLAKE3-verify a .tlpack CAS bundle into local SQLite & CAS
    Import {
        /// Input .tlpack file path
        input: PathBuf,
        /// Requested trust domain ('trusted' or 'untrusted')
        #[arg(long)]
        trust_domain: Option<String>,
        /// Optional Ed25519 public key (32-byte hex) required to accept packs into 'trusted'
        #[arg(long)]
        trusted_pubkey: Option<String>,
        /// Explicitly allow unattested (unsigned) packs into 'trusted' when no public key is configured
        #[arg(long, default_value_t = false)]
        allow_unattested_trusted: bool,
        /// Optional expected SHA-256 hex digest of the .tlpack archive
        #[arg(long)]
        expected_sha256: Option<String>,
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
        /// Requested trust domain for pulled artifacts ('trusted' or 'untrusted')
        #[arg(long)]
        trust_domain: Option<String>,
        /// Optional Ed25519 public key (32-byte hex) required to accept pulled packs into 'trusted'
        #[arg(long)]
        trusted_pubkey: Option<String>,
        /// Explicitly allow unattested (unsigned) pulled packs into 'trusted' when no public key is configured
        #[arg(long, default_value_t = false)]
        allow_unattested_trusted: bool,
        /// Optional expected SHA-256 hex digest of pulled .tlpack payload
        #[arg(long)]
        expected_sha256: Option<String>,
    },
    /// Run remote offload & CAS synchronization server (e.g., on DGX Spark)
    Serve {
        /// Listen address (host:port)
        #[arg(long, visible_alias = "bind", default_value = "127.0.0.1:9400")]
        listen: String,
        /// Enable CUDA GPU fast-check offload
        #[arg(long, default_value_t = false)]
        gpu_enable: bool,
        /// Shared API token required via `X-Turbo-Token` or `Authorization: Bearer` (falls back to TURBO_LEAN_API_TOKEN)
        #[arg(long)]
        api_token: Option<String>,
        /// Explicitly allow unauthenticated HTTP requests when bound strictly to loopback (127.0.0.1 / ::1)
        #[arg(long, default_value_t = false)]
        allow_unauthenticated_local: bool,
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
        /// Optional Ed25519 signing key (32-byte hex seed; falls back to TURBO_LEAN_RECEIPT_SIGNING_KEY)
        #[arg(long)]
        signing_key: Option<String>,
        /// Seed TheoremProofCAS with all verified theorem shards after CI verification succeeds
        #[arg(long, default_value_t = false)]
        seed_shards: bool,
        /// Optional subdirectory or file scope to restrict verification to (e.g. ProximityPrize/SubmissionUpper)
        #[arg(long)]
        scope: Option<PathBuf>,
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
        /// Optional Ed25519 public key (32-byte hex; falls back to TURBO_LEAN_RECEIPT_VERIFY_PUBKEY)
        #[arg(long)]
        verify_pubkey: Option<String>,
        /// Fail closed if the receipt does not carry a valid Ed25519 signature
        #[arg(long, default_value_t = false)]
        require_signature: bool,
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
        /// Optional Ed25519 signing key (32-byte hex seed; falls back to TURBO_LEAN_RECEIPT_SIGNING_KEY)
        #[arg(long)]
        signing_key: Option<String>,
        /// Offload uncached theorem shard verification to a remote `turbo-lean serve` HTTP endpoint (e.g. http://127.0.0.1:9400)
        #[arg(long)]
        remote_http: Option<String>,
        /// Optional subdirectory or file scope to restrict verification to (e.g. ProximityPrize/SubmissionUpper)
        #[arg(long)]
        scope: Option<PathBuf>,
        /// Emit cone pruning statistics (`total_project_theorems`, `dirty_cone_theorems`, `pruned_percentage`, `estimated_lake_build_saved_ms`)
        #[arg(long, default_value_t = false)]
        cone_stats: bool,
        /// Cap the maximum number of cone verification jobs (`0` = uncapped)
        #[arg(long, default_value_t = 0)]
        max_cone_jobs: usize,
        /// Optional external kernel checker binary (`nanoda_bin` or `lean4checker`) for dual-auditor cross-checking
        #[arg(long)]
        nanoda_bin: Option<PathBuf>,
    },
    /// Unified sub-millisecond to few-millisecond agent verification funnel:
    /// Stage 0 (hygiene & cone cache) -> Stage 1 (spec vacuity & certified fast-check with hypothesis suggestion) -> Stage 2 (Zygote kernel verification)
    #[command(visible_alias = "prove-step")]
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
    /// Audit theorem specifications for vacuous preconditions, postcondition tightness, and anti-reward-hacking policy compliance
    AuditSpec {
        /// Path(s) to the .lean file(s) or directory(s)
        #[arg(required = true, num_args = 1..)]
        files: Vec<PathBuf>,
        /// Optional declaration name
        #[arg(long)]
        decl: Option<String>,
        /// Policy preset (`permissive` | `default` | `strict-proofs`)
        #[arg(long)]
        policy: Option<String>,
        /// Explicit path to `turbo-lean.toml` or JSON policy configuration
        #[arg(long)]
        config: Option<PathBuf>,
        /// Additional forbidden namespace(s) for audited files
        #[arg(long = "forbid-namespace")]
        forbid_namespaces: Vec<String>,
        /// Additional forbidden declaration kind(s) (e.g. `inductive`, `structure`, `def`)
        #[arg(long = "forbid-decl-kinds", value_delimiter = ',')]
        forbid_decl_kinds: Vec<String>,
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
        /// Per-request wall-clock timeout in milliseconds (0 = no artificial timeout; exits 124 on timeout)
        #[arg(long, default_value_t = 0)]
        timeout_ms: u64,
        /// Self-test determinism by comparing output against a fresh `lean <file>` process and failing closed on any difference
        #[arg(long)]
        verify_determinism: bool,
    },
    /// Deduplicate .lake/packages across multi-agent git worktrees via CAS hardlinks and purge .barrel/.git bloat
    WorktreeDedup {
        /// Path to the Lean project root
        #[arg(long, default_value = ".")]
        project_dir: PathBuf,
    },
    /// List or test configured tactic & SIMD accelerators (built-in and external plugins)
    Accelerators {
        /// Optional Lean project directory to load .turbo-lean/accelerators.json or turbo-lean.toml
        #[arg(long)]
        project_dir: Option<PathBuf>,
    },
    /// Run the Model Context Protocol (MCP) JSON-RPC 2.0 server over stdio with token-compacting diagnostics & live /dev/shm agent analytics
    Mcp {
        /// Optional Lean project root directory
        #[arg(long)]
        project_dir: Option<PathBuf>,
    },
    /// Inspect or reset live multi-agent /dev/shm latency, bottleneck, and token-efficiency analytics
    Analytics {
        /// Reset accumulated analytics counters
        #[arg(long, default_value_t = false)]
        reset: bool,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    if let Some(mb) = cli.max_memory_mb {
        std::env::set_var("TURBO_LEAN_MAX_MEMORY_MB", mb.to_string());
    }
    // Axiom allowlist from `turbo-lean.toml` (at `--base` for pr-verify) unless set explicitly;
    // zygote workers and daemons inherit it from this process.
    if std::env::var_os(splitter::ALLOWED_AXIOMS_ENV).is_none() {
        let here = std::path::Path::new(".");
        let (dir, rev) = match &cli.command {
            Commands::PrVerify {
                project_dir, base, ..
            } => (Some(project_dir.as_path()), Some(base.as_str())),
            Commands::CiVerify {
                project_dir, mode, ..
            } => {
                if mode == "untrusted" {
                    (None, None)
                } else {
                    (Some(project_dir.as_path()), None)
                }
            }
            Commands::Check { project_dir, .. }
            | Commands::Build { project_dir, .. }
            | Commands::SeedShards { project_dir, .. } => (Some(project_dir.as_path()), None),
            Commands::AgentStep {
                project_dir, file, ..
            } => {
                let file_dir = file.parent().filter(|p| !p.as_os_str().is_empty());
                (
                    Some(project_dir.as_deref().or(file_dir).unwrap_or(here)),
                    None,
                )
            }
            Commands::Mcp { project_dir } => (Some(project_dir.as_deref().unwrap_or(here)), None),
            _ => (None, None),
        };
        if let Some(dir) = dir {
            let allow = splitter::load_axiom_allowlist(dir, rev).join(",");
            std::env::set_var(splitter::ALLOWED_AXIOMS_ENV, allow);
        }
    }

    // Fast stateless paths that do not need to open SQLite (`state.db`):
    if let Commands::ClusterStatus { bench_cabi } = cli.command {
        return cluster::run_cluster_status_command(bench_cabi, cli.json);
    }
    if let Commands::Accelerators { ref project_dir } = cli.command {
        return accelerators::run_accelerators_command(project_dir.as_deref(), cli.json);
    }
    if let Commands::Mcp { ref project_dir } = cli.command {
        return mcp::run_mcp_stdio_server(project_dir.as_deref(), cli.cache_dir.as_deref());
    }
    if let Commands::Analytics { reset } = cli.command {
        return mcp::run_analytics_command(reset, cli.json);
    }
    if let Commands::AuditSpec {
        ref files,
        ref decl,
        ref policy,
        ref config,
        ref forbid_namespaces,
        ref forbid_decl_kinds,
    } = cli.command
    {
        return gpu_fastcheck::run_audit_spec_command_with_options(
            files,
            decl.as_deref(),
            cli.json,
            policy.as_deref(),
            config.as_deref(),
            forbid_namespaces,
            forbid_decl_kinds,
        );
    }
    if let Commands::Serve {
        ref listen,
        gpu_enable,
        ref api_token,
        allow_unauthenticated_local,
    } = cli.command
    {
        return pack::run_server_with_auth(
            cli.cache_dir.as_deref(),
            listen,
            gpu_enable,
            api_token.as_deref(),
            allow_unauthenticated_local,
        );
    }
    if let Commands::VerifyReceipt {
        receipt,
        receipt_flag,
        expected_interface_hash,
        baseline_receipt,
        verify_pubkey,
        require_signature,
    } = cli.command
    {
        return pr_verify::run_verify_receipt_command(
            cli.json,
            receipt,
            receipt_flag,
            expected_interface_hash,
            baseline_receipt,
            verify_pubkey,
            require_signature,
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
        return gpu_fastcheck::run_fast_check_remote_http_stateless(cli.json, file, gpu, http_url);
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

    if let Commands::AgentStep {
        ref file,
        ref decl,
        ref project_dir,
        low_memory,
    } = cli.command
    {
        if let Some(out_json) = gpu_fastcheck::try_stateless_agent_step_cex(
            file,
            decl.as_deref(),
            project_dir.as_deref(),
            low_memory,
        ) {
            if cli.json {
                println!("{}", serde_json::to_string_pretty(&out_json)?);
            } else {
                let decl_name = out_json
                    .get("decl")
                    .and_then(|v| v.as_str())
                    .unwrap_or("decl");
                let elapsed_ms = out_json
                    .get("elapsed_ms")
                    .and_then(|v| v.as_f64())
                    .unwrap_or(0.0);
                let violations = out_json
                    .get("violations")
                    .and_then(|v| v.as_u64())
                    .unwrap_or(1);
                let hyp = out_json
                    .get("suggested_hypothesis")
                    .and_then(|v| v.as_str())
                    .unwrap_or("none");
                println!(
                    "[turbo-lean] AGENT-STEP STAGE 1 COUNTEREXAMPLE REJECTED `{}` ({} violations in {:.3} ms) -> suggested hypothesis: `{}`",
                    decl_name, violations, elapsed_ms, hyp
                );
            }
            return Ok(());
        }
    }

    if let Commands::Eval {
        ref file,
        ref project_dir,
        ref lean_path,
        timeout_ms: 0,
        verify_determinism: false,
    } = cli.command
    {
        if std::env::var("TURBO_LEAN_VERIFY_DETERMINISM").as_deref() != Ok("1") {
            if let Some((_, reply)) = zygote::try_stateless_eval_shm_cache(
                &resolved_cache_root,
                file,
                project_dir.as_deref(),
                lean_path.as_deref(),
            ) {
                if cli.json {
                    println!("{}", serde_json::to_string_pretty(&reply)?);
                    if !reply.ok {
                        std::process::exit(1);
                    }
                    return Ok(());
                }
                if !reply.crashed && reply.import_ok {
                    let mut rendered_stdout = String::new();
                    if !reply.stdout.is_empty() {
                        rendered_stdout.push_str(&reply.stdout);
                        if !reply.stdout.ends_with('\n') {
                            rendered_stdout.push('\n');
                        }
                    }
                    for msg in &reply.messages {
                        rendered_stdout.push_str(msg);
                        if !msg.ends_with('\n') {
                            rendered_stdout.push('\n');
                        }
                    }
                    if !reply.ok && reply.messages.is_empty() {
                        for err in &reply.errors {
                            rendered_stdout.push_str(err);
                            if !err.ends_with('\n') {
                                rendered_stdout.push('\n');
                            }
                        }
                    }
                    print!("{}", rendered_stdout);
                    if !reply.ok {
                        std::process::exit(1);
                    }
                    return Ok(());
                }
            }
        }
    }

    if let Commands::Check {
        ref file,
        ref decl,
        ref project_dir,
        jobs,
        remote_http: Some(ref remote_url),
        ..
    } = cli.command
    {
        if !db_warm_on_open
            && check::try_stateless_remote_check(
                &resolved_cache_root,
                cli.json,
                file,
                decl.as_deref(),
                project_dir,
                jobs,
                remote_url,
            )?
        {
            return Ok(());
        }
    }

    // Overlap remote HTTP export/manifest fetch with SQLite schema initialization on cold sync
    let mut prefetched_export: Option<std::thread::JoinHandle<Result<pack::PrefetchedExportItem>>> =
        None;
    let mut prefetched_manifest: Option<std::thread::JoinHandle<Option<pack::DeltaManifest>>> =
        None;
    let mut prefetched_import: Option<
        std::thread::JoinHandle<
            Option<(pack::PackManifest, Vec<(String, String, i64, i64)>, usize)>,
        >,
    > = None;
    if let Commands::Import {
        ref input,
        ref trust_domain,
        ref trusted_pubkey,
        allow_unattested_trusted,
        ref expected_sha256,
    } = cli.command
    {
        let has_expected_sha = expected_sha256
            .as_deref()
            .filter(|s| !s.trim().is_empty())
            .is_some()
            || std::env::var("TURBO_LEAN_PACK_EXPECTED_SHA256")
                .ok()
                .filter(|s| !s.trim().is_empty())
                .is_some();
        if !has_expected_sha {
            if db_warm_on_open
                || resolved_cache_root
                    .join("locks")
                    .join("last_import_stamp")
                    .exists()
            {
                if let Some(counts) = pack::try_stateless_warm_import_with_domain(
                    &resolved_cache_root,
                    input,
                    trust_domain.as_deref(),
                    trusted_pubkey.as_deref(),
                    allow_unattested_trusted,
                ) {
                    if cli.json {
                        println!(
                            "{}",
                            serde_json::to_string_pretty(&serde_json::json!({
                                "imported_actions": counts.0,
                                "imported_blobs": counts.1,
                                "archive": input.display().to_string()
                            }))?
                        );
                    } else {
                        println!(
                            "[turbo-lean] Imported & BLAKE3-verified {} actions and {} blobs from {}",
                            counts.0,
                            counts.1,
                            input.display()
                        );
                    }
                    return Ok(());
                }
            } else if let Some(counts) = pack::try_stateless_cold_import_with_domain(
                &resolved_cache_root,
                input,
                trust_domain.as_deref(),
                trusted_pubkey.as_deref(),
                allow_unattested_trusted,
            ) {
                if cli.json {
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&serde_json::json!({
                            "imported_actions": counts.0,
                            "imported_blobs": counts.1,
                            "archive": input.display().to_string()
                        }))?
                    );
                } else {
                    println!(
                        "[turbo-lean] Imported & BLAKE3-verified {} actions and {} blobs from {}",
                        counts.0,
                        counts.1,
                        input.display()
                    );
                }
                return Ok(());
            }
            let inp = input.clone();
            let root_for_prestage = resolved_cache_root.clone();
            prefetched_import = Some(std::thread::spawn(move || {
                pack::try_read_and_prestage_pack(&root_for_prestage, &inp)
            }));
        }
    }
    if let Commands::Sync {
        ref remote,
        push,
        bidirectional: false,
        ref trust_domain,
        ref trusted_pubkey,
        allow_unattested_trusted,
        ref expected_sha256,
    } = cli.command
    {
        let has_expected_sha = expected_sha256
            .as_deref()
            .filter(|s| !s.trim().is_empty())
            .is_some();
        let has_strict_pull_policy = has_expected_sha
            || trust_domain.is_some()
            || trusted_pubkey.is_some()
            || std::env::var("TURBO_LEAN_PACK_TRUSTED_PUBKEY")
                .ok()
                .filter(|s| !s.trim().is_empty())
                .is_some();
        if remote.starts_with("http://") || remote.starts_with("https://") {
            let base = remote.trim_end_matches('/').to_string();
            if !push
                && !has_strict_pull_policy
                && (db_warm_on_open
                    || resolved_cache_root
                        .join("locks")
                        .join("cached_portable_manifest.json")
                        .exists())
            {
                if pack::try_stateless_noop_pull_sync(&resolved_cache_root, &base) {
                    if cli.json {
                        println!(
                            "{}",
                            serde_json::to_string_pretty(&serde_json::json!({
                                "status": "synced",
                                "mode": "bidirectional",
                                "remote": remote,
                                "pulled_actions": 0,
                                "pulled_blobs": 0,
                                "pulled_pack_bytes": 0,
                                "pushed_actions": 0,
                                "pushed_blobs": 0,
                                "pushed_raw_bytes": 0,
                                "pushed_pack_bytes": 0,
                                "delta_push_noop": true,
                                "elapsed_ms": 0
                            }))?
                        );
                    } else {
                        println!(
                            "[turbo-lean] Synced with {} in 0 ms: pulled 0 actions (0 blobs), pushed 0 actions (0 blobs)",
                            remote
                        );
                    }
                    return Ok(());
                }
            }
            if !push && !db_warm_on_open && !has_expected_sha {
                if let Some((pulled, pulled_bytes)) = pack::try_stateless_cold_pull_sync_with_domain(
                    &resolved_cache_root,
                    &base,
                    trust_domain.as_deref(),
                    trusted_pubkey.as_deref(),
                    allow_unattested_trusted,
                ) {
                    if cli.json {
                        println!(
                            "{}",
                            serde_json::to_string_pretty(&serde_json::json!({
                                "status": "synced",
                                "mode": "bidirectional",
                                "remote": remote,
                                "pulled_actions": pulled.0,
                                "pulled_blobs": pulled.1,
                                "pulled_pack_bytes": pulled_bytes,
                                "pushed_actions": 0,
                                "pushed_blobs": 0,
                                "pushed_raw_bytes": 0,
                                "pushed_pack_bytes": 0,
                                "delta_push_noop": true,
                                "elapsed_ms": 0
                            }))?
                        );
                    } else {
                        println!(
                            "[turbo-lean] Synced with {} in 0 ms: pulled {} actions ({} blobs), pushed 0 actions (0 blobs)",
                            remote, pulled.0, pulled.1
                        );
                    }
                    return Ok(());
                }
            }
            if push {
                if db_warm_on_open {
                    if let Some(((p_acts, p_blobs, p_raw, p_pack, p_noop), rem_dm)) =
                        pack::try_stateless_push_sync(&resolved_cache_root, &base)
                    {
                        if rem_dm.is_none() {
                            if cli.json {
                                println!(
                                    "{}",
                                    serde_json::to_string_pretty(&serde_json::json!({
                                        "status": "synced",
                                        "mode": "push_only",
                                        "remote": remote,
                                        "pulled_actions": 0,
                                        "pulled_blobs": 0,
                                        "pulled_pack_bytes": 0,
                                        "pushed_actions": p_acts,
                                        "pushed_blobs": p_blobs,
                                        "pushed_raw_bytes": p_raw,
                                        "pushed_pack_bytes": p_pack,
                                        "delta_push_noop": p_noop,
                                        "elapsed_ms": 0
                                    }))?
                                );
                            } else {
                                println!(
                                    "[turbo-lean] Delta-pushed to {} in 0 ms: {} actions ({} blobs, {} bytes)",
                                    remote, p_acts, p_blobs, p_pack
                                );
                            }
                            return Ok(());
                        }
                        prefetched_manifest = Some(std::thread::spawn(move || rem_dm));
                    } else {
                        prefetched_manifest = Some(std::thread::spawn(move || {
                            let url = format!("{}/manifest", base);
                            pack::http_request("GET", &url, "application/json", &[])
                                .ok()
                                .and_then(|bytes| serde_json::from_slice(&bytes).ok())
                        }));
                    }
                } else {
                    prefetched_manifest = Some(std::thread::spawn(move || {
                        let url = format!("{}/manifest", base);
                        pack::http_request("GET", &url, "application/json", &[])
                            .ok()
                            .and_then(|bytes| serde_json::from_slice(&bytes).ok())
                    }));
                }
            } else if !db_warm_on_open {
                let is_loopback = pack::is_loopback_http_url(&base);
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
            timeout,
            kernel,
        } => {
            std::env::set_var("TURBO_LEAN_KERNEL_ENGINE", &kernel);
            if timeout > 0 {
                std::env::set_var("TURBO_LEAN_EVAL_TIMEOUT_MS", (timeout * 1000).to_string());
                let file_disp = file.display().to_string();
                let decl_disp = decl.clone();
                std::thread::spawn(move || {
                    std::thread::sleep(std::time::Duration::from_secs(timeout));
                    match decl_disp {
                        Some(d) => eprintln!(
                            "[turbo-lean] ERROR: check timed out after {}s for `{}` in {}",
                            timeout, d, file_disp
                        ),
                        None => eprintln!(
                            "[turbo-lean] ERROR: check timed out after {}s for {}",
                            timeout, file_disp
                        ),
                    }
                    std::process::exit(124);
                });
            }
            let done_flag = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
            if !cli.json && std::env::var("TURBO_LEAN_NO_PROGRESS").is_err() {
                let done_watch = done_flag.clone();
                let file_disp = file.display().to_string();
                let decl_disp = decl.clone();
                std::thread::spawn(move || {
                    let t_start = std::time::Instant::now();
                    loop {
                        std::thread::sleep(std::time::Duration::from_secs(5));
                        if done_watch.load(std::sync::atomic::Ordering::Relaxed) {
                            break;
                        }
                        let elapsed_s = t_start.elapsed().as_secs();
                        match decl_disp {
                            Some(ref d) => eprintln!(
                                "[turbo-lean] still checking `{}` in {} ({}s elapsed)...",
                                d, file_disp, elapsed_s
                            ),
                            None => eprintln!(
                                "[turbo-lean] still checking {} ({}s elapsed)...",
                                file_disp, elapsed_s
                            ),
                        }
                    }
                });
            }
            let res = check::run_check_command(
                &mut store,
                db_warm_on_open,
                cli.json,
                file,
                decl,
                project_dir,
                jobs,
                parallel_shards,
                remote_http,
            );
            done_flag.store(true, std::sync::atomic::Ordering::Relaxed);
            res
        }

        Commands::FastCheck {
            file,
            backend,
            gpu,
            tpu,
            transpile_lean,
            remote_http,
            remote_ssh,
            via_jump,
        } => {
            let effective_tpu = tpu || backend.eq_ignore_ascii_case("tpu");
            let effective_gpu = gpu || backend.eq_ignore_ascii_case("gpu");
            std::env::set_var("TURBO_LEAN_FASTCHECK_BACKEND", &backend);
            if effective_tpu {
                gpu_fastcheck::run_tpu_fast_check(cli.json, &file, transpile_lean.as_deref())
            } else {
                gpu_fastcheck::run_fast_check_command(
                    &store,
                    cli.json,
                    file,
                    effective_gpu,
                    transpile_lean,
                    remote_http,
                    remote_ssh,
                    via_jump,
                )
            }
        }
        Commands::ClusterStatus { bench_cabi } => {
            cluster::run_cluster_status_command(bench_cabi, cli.json)
        }

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
            project_dir: _,
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
                    "[turbo-lean] GC complete: pruned {} worktrees, evicted {} actions ({} blobs), cleaned {} staging files, pruned {} fastcheck bins, reaped {} zygotes, freed {} bytes ({} bytes remaining reclaimable)",
                    report.pruned_worktrees,
                    report.evicted_actions,
                    report.unlinked_blobs,
                    report.cleaned_staging_files,
                    report.pruned_fastcheck_bins,
                    report.reaped_zygote_workers,
                    report.freed_reclaimable_bytes,
                    report.remaining_reclaimable_bytes
                );
            }
            Ok(())
        }

        Commands::Export {
            output,
            portable_only,
            signing_key,
        } => pack::run_export_command(&store, cli.json, output, portable_only, signing_key),

        Commands::Import {
            input,
            trust_domain,
            trusted_pubkey,
            allow_unattested_trusted,
            expected_sha256,
        } => pack::run_import_command(
            &mut store,
            cli.json,
            input,
            trust_domain,
            trusted_pubkey,
            allow_unattested_trusted,
            expected_sha256,
            prefetched_import,
        ),

        Commands::Sync {
            remote,
            push,
            bidirectional,
            trust_domain,
            trusted_pubkey,
            allow_unattested_trusted,
            expected_sha256,
        } => pack::run_sync_command(
            &mut store,
            cli.json,
            remote,
            push,
            bidirectional,
            trust_domain,
            trusted_pubkey,
            allow_unattested_trusted,
            expected_sha256,
            prefetched_export,
            prefetched_manifest,
        ),

        Commands::Serve {
            listen,
            gpu_enable,
            api_token,
            allow_unauthenticated_local,
        } => pack::run_server_with_auth(
            cli.cache_dir.as_deref(),
            &listen,
            gpu_enable,
            api_token.as_deref(),
            allow_unauthenticated_local,
        ),

        Commands::CiVerify {
            mode,
            project_dir,
            receipt,
            signing_key,
            seed_shards,
            scope,
        } => pr_verify::run_ci_verify_command(
            &mut store,
            cli.json,
            mode,
            project_dir,
            receipt,
            signing_key,
            seed_shards,
            scope,
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
            verify_pubkey,
            require_signature,
        } => pr_verify::run_verify_receipt_command(
            cli.json,
            receipt,
            receipt_flag,
            expected_interface_hash,
            baseline_receipt,
            verify_pubkey,
            require_signature,
        ),

        Commands::PrVerify {
            project_dir,
            base,
            mode,
            disallow_statement_changes,
            receipt,
            signing_key,
            remote_http,
            scope,
            cone_stats,
            max_cone_jobs,
            nanoda_bin,
        } => pr_verify::run_pr_verify_command(
            &mut store,
            cli.json,
            project_dir,
            base,
            mode,
            disallow_statement_changes,
            receipt,
            signing_key,
            remote_http,
            scope,
            cone_stats,
            max_cone_jobs,
            nanoda_bin,
        ),

        Commands::AgentStep {
            file,
            decl,
            project_dir,
            low_memory,
        } => gpu_fastcheck::run_agent_step_command(
            &mut store,
            &file,
            decl.as_deref(),
            project_dir.as_deref(),
            low_memory,
            cli.json,
        ),

        Commands::AuditSpec {
            files,
            decl,
            policy,
            config,
            forbid_namespaces,
            forbid_decl_kinds,
        } => gpu_fastcheck::run_audit_spec_command_with_options(
            &files,
            decl.as_deref(),
            cli.json,
            policy.as_deref(),
            config.as_deref(),
            &forbid_namespaces,
            &forbid_decl_kinds,
        ),

        Commands::Eval {
            file,
            project_dir,
            lean_path,
            timeout_ms,
            verify_determinism,
        } => {
            let source = fs::read_to_string(&file)?;
            let proj_dir = project_dir
                .map(|p| lake_build::find_project_root(&p))
                .unwrap_or_else(|| lake_build::find_project_root(&file));
            let toolchain = lake_build::detect_toolchain(&proj_dir);
            if !server::is_toolchain_installed(&toolchain) {
                eprintln!("error: toolchain '{}' is not installed", toolchain);
                std::process::exit(1);
            }
            let explicit_lp: Option<String> = lean_path.or_else(|| std::env::var("LEAN_PATH").ok());

            let (mut env_vars, lean_bin, req_lp) = if let Some(lp) = explicit_lp {
                let (mut ev, lb) = pack::resolve_server_lean_env_and_bin(&store, &toolchain, &lp);
                if lp.is_empty() {
                    ev.remove("LEAN_PATH");
                } else {
                    ev.insert("LEAN_PATH".to_string(), lp.clone());
                }
                (ev, lb, lp)
            } else if !proj_dir.join(".lake/packages").is_dir()
                && proj_dir.join(".lake/build/lib/lean").exists()
                && zygote::has_active_local_zygote_daemon(&store)
            {
                let canon_proj = proj_dir.canonicalize().unwrap_or_else(|_| proj_dir.clone());
                let lp = lake_build::resolve_remote_lean_path(&canon_proj, None);
                let mut ev = std::collections::HashMap::new();
                ev.insert("LEAN_PATH".to_string(), lp.clone());
                (ev, PathBuf::from("lean"), lp)
            } else if proj_dir.join("lakefile.lean").exists()
                || proj_dir.join("lakefile.toml").exists()
            {
                if let Ok((ev, _)) = lake_build::resolve_lake_env(&store, &proj_dir) {
                    let lp = ev.get("LEAN_PATH").cloned().unwrap_or_default();
                    let (_, lb) = pack::resolve_server_lean_env_and_bin(&store, &toolchain, &lp);
                    (ev, lb, lp)
                } else {
                    let (ev, lb) = pack::resolve_server_lean_env_and_bin(&store, &toolchain, "");
                    let lp = ev.get("LEAN_PATH").cloned().unwrap_or_default();
                    (ev, lb, lp)
                }
            } else {
                let (ev, lb) = pack::resolve_server_lean_env_and_bin(&store, &toolchain, "");
                (ev, lb, String::new())
            };

            for (k, v) in std::env::vars() {
                if k != "LEAN_PATH" {
                    env_vars.entry(k).or_insert(v);
                }
            }
            if let Ok(cwd) = std::env::current_dir() {
                env_vars.insert(
                    "TURBO_LEAN_CALLER_CWD".to_string(),
                    cwd.to_string_lossy().to_string(),
                );
            }

            let needs_direct_lean = source.contains("IO.Process.exit")
                || source.lines().take(20).any(|l| {
                    let t = l.split("--").next().unwrap_or(l).trim();
                    t == "module"
                        || t.starts_with("module ")
                        || t.starts_with("public import ")
                        || t.starts_with("meta import ")
                });

            let run_direct_lean = || -> Result<()> {
                use std::io::Write;
                let mut cmd = std::process::Command::new(&lean_bin);
                cmd.arg(&file).envs(&env_vars);
                if !req_lp.is_empty() {
                    cmd.env("LEAN_PATH", &req_lp);
                } else {
                    cmd.env_remove("LEAN_PATH");
                }
                let out = cmd.output()?;
                std::io::stdout().write_all(&out.stdout)?;
                std::io::stderr().write_all(&out.stderr)?;
                std::io::stdout().flush()?;
                std::io::stderr().flush()?;
                #[cfg(unix)]
                {
                    use std::os::unix::process::ExitStatusExt;
                    if let Some(code) = out.status.code() {
                        std::process::exit(code);
                    } else if let Some(sig) = out.status.signal() {
                        std::process::exit(128 + sig);
                    }
                }
                std::process::exit(out.status.code().unwrap_or(1));
            };

            if needs_direct_lean && !cli.json {
                run_direct_lean()?;
            }

            let file_display = file.to_string_lossy().to_string();
            let reply = if let Some(daemon_rep) = zygote::try_local_zygote_eval(
                &store,
                &env_vars,
                &lean_bin,
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
                    if timeout_ms > 0 {
                        Some(timeout_ms)
                    } else {
                        None
                    },
                )?
            };

            if reply.timed_out {
                if source.contains("#rsgb_") || std::env::var("TURBO_LEAN_RSGB_MODE").is_ok() {
                    println!("RSGB_TIMEOUT");
                } else {
                    eprintln!("[turbo-lean] evaluation timed out after {} ms", timeout_ms);
                }
                std::process::exit(124);
            }

            if (reply.crashed || !reply.import_ok) && !cli.json {
                run_direct_lean()?;
            }

            let mut rendered_stdout = String::new();
            if !reply.stdout.is_empty() {
                rendered_stdout.push_str(&reply.stdout);
                if !reply.stdout.ends_with('\n') {
                    rendered_stdout.push('\n');
                }
            }
            for msg in &reply.messages {
                rendered_stdout.push_str(msg);
                if !msg.ends_with('\n') {
                    rendered_stdout.push('\n');
                }
            }
            if !reply.ok && reply.messages.is_empty() {
                for err in &reply.errors {
                    rendered_stdout.push_str(err);
                    if !err.ends_with('\n') {
                        rendered_stdout.push('\n');
                    }
                }
            }

            let check_det = verify_determinism
                || std::env::var("TURBO_LEAN_VERIFY_DETERMINISM").as_deref() == Ok("1");
            if check_det {
                let mut cmd = std::process::Command::new(&lean_bin);
                cmd.arg(&file).envs(&env_vars);
                if !req_lp.is_empty() {
                    cmd.env("LEAN_PATH", &req_lp);
                } else {
                    cmd.env_remove("LEAN_PATH");
                }
                let lean_out = cmd.output()?;
                let lean_ok = lean_out.status.success();
                if reply.ok != lean_ok
                    || rendered_stdout.as_bytes() != lean_out.stdout.as_slice()
                    || !lean_out.stderr.is_empty()
                {
                    eprintln!(
                        "[turbo-lean eval --verify-determinism] Byte mismatch against `lean {}`!\n  turbo ok={} stdout_len={}\n  lean  ok={} stdout_len={} stderr_len={}",
                        file.display(),
                        reply.ok,
                        rendered_stdout.len(),
                        lean_ok,
                        lean_out.stdout.len(),
                        lean_out.stderr.len()
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

            print!("{}", rendered_stdout);
            if !reply.ok {
                std::process::exit(1);
            }
            Ok(())
        }

        Commands::WorktreeDedup { project_dir } => {
            accelerators::run_worktree_dedup_command(&store, &project_dir, cli.json)
        }

        Commands::Accelerators { project_dir } => {
            accelerators::run_accelerators_command(project_dir.as_deref(), cli.json)
        }

        Commands::Mcp { project_dir } => {
            mcp::run_mcp_stdio_server(project_dir.as_deref(), cli.cache_dir.as_deref())
        }

        Commands::Analytics { reset } => mcp::run_analytics_command(reset, cli.json),
    }
}
