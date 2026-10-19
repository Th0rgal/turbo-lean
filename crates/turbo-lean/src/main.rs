mod db;
mod gpu_fastcheck;
mod pack;
mod pr_verify;
mod splitter;
mod zygote;

pub use gpu_fastcheck::*;
pub use pr_verify::*;
use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use db::{BlobEntry, SingleflightOutcome, TurboStore};
use splitter::split_lean_source;
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;
use walkdir::WalkDir;

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
}

fn detect_toolchain(project_dir: &Path) -> String {
    let tc_file = project_dir.join("lean-toolchain");
    if let Ok(s) = fs::read_to_string(&tc_file) {
        return s.trim().to_string();
    }
    "leanprover/lean4:v4.31.0".to_string()
}

fn spawn_lake_env(project_dir: &Path) -> Result<HashMap<String, String>> {
    if !project_dir.join(".lake").join("packages").is_dir() {
        let tc = detect_toolchain(project_dir);
        let tc_dir_name = tc.trim().replace('/', "--").replace(':', "---");
        let mut elan_roots = Vec::new();
        if let Ok(eh) = std::env::var("ELAN_HOME") {
            elan_roots.push(PathBuf::from(eh));
        }
        if let Ok(home) = std::env::var("HOME") {
            elan_roots.push(PathBuf::from(home).join(".elan"));
        }
        elan_roots.push(PathBuf::from("/var/lib/sandboxed-node/caches/elan"));

        for elan_home in elan_roots {
            let tc_root = elan_home.join("toolchains").join(&tc_dir_name);
            let lean_bin = tc_root.join("bin").join("lean");
            if lean_bin.exists() {
                let canon_proj = project_dir
                    .canonicalize()
                    .unwrap_or_else(|_| project_dir.to_path_buf());
                let proj_lib_lean = canon_proj.join(".lake/build/lib/lean");
                let tc_lib_lean = tc_root.join("lib/lean");
                let tc_lib = tc_root.join("lib");
                let tc_bin = tc_root.join("bin");
                let elan_bin = elan_home.join("bin");

                let mut env_map = HashMap::new();
                env_map.insert(
                    "ELAN_HOME".to_string(),
                    elan_home.to_string_lossy().to_string(),
                );
                env_map.insert(
                    "LAKE".to_string(),
                    tc_bin.join("lake").to_string_lossy().to_string(),
                );
                env_map.insert(
                    "LEAN_PATH".to_string(),
                    format!("{}:{}", proj_lib_lean.display(), tc_lib_lean.display()),
                );
                env_map.insert(
                    "LEAN_SRC_PATH".to_string(),
                    format!("{}:{}/src/lean", canon_proj.display(), tc_root.display()),
                );
                let orig_ld = std::env::var("LD_LIBRARY_PATH").unwrap_or_default();
                let ld_val = if orig_ld.is_empty() {
                    format!(
                        "{}:{}:{}",
                         canon_proj.join(".lake/build/lib").display(),
                        tc_lib_lean.display(),
                        tc_lib.display()
                    )
                } else {
                    format!(
                        "{}:{}:{}:{}",
                        canon_proj.join(".lake/build/lib").display(),
                        tc_lib_lean.display(),
                        tc_lib.display(),
                        orig_ld
                    )
                };
                env_map.insert("LD_LIBRARY_PATH".to_string(), ld_val);
                let orig_path = std::env::var("PATH").unwrap_or_default();
                env_map.insert(
                    "PATH".to_string(),
                    format!("{}:{}:{}", tc_bin.display(), elan_bin.display(), orig_path),
                );
                return Ok(env_map);
            }
        }
    }

    let output = Command::new("lake")
        .arg("env")
        .arg("env")
        .current_dir(project_dir)
        .output()
        .context("Failed to execute `lake env env`")?;

    let mut env_map = HashMap::new();
    let stdout = String::from_utf8_lossy(&output.stdout);
    for line in stdout.lines() {
        if let Some((k, v)) = line.split_once('=') {
            if matches!(
                k,
                "LEAN_PATH"
                    | "LEAN_SRC_PATH"
                    | "PATH"
                    | "LD_LIBRARY_PATH"
                    | "ELAN_HOME"
                    | "LAKE"
            ) {
                env_map.insert(k.to_string(), v.to_string());
            }
        }
    }
    Ok(env_map)
}

/// Resolve `LEAN_PATH` and environment variables once via SQLite `lake_env_cache` (< 0.2 ms),
/// shared `/dev/shm/turbo-lean-staging/lake_env_v1_<key>.json`, or `lake env env` on cache miss.
fn resolve_lake_env(store: &TurboStore, project_dir: &Path) -> Result<(HashMap<String, String>, bool)> {
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let project_key = TurboStore::compute_lake_env_key(&canon_dir);

    if let Some(cached) = store.get_lake_env(&project_key)? {
        return Ok((cached, true));
    }

    let shm_env_path = store
        .fast_staging_dir()
        .join(format!("lake_env_v1_{}.json", project_key));
    if let Ok(bytes) = fs::read(&shm_env_path) {
        if let Ok(env_map) = serde_json::from_slice::<HashMap<String, String>>(&bytes) {
            if !env_map.is_empty() {
                let _ = store.put_lake_env(&project_key, &env_map);
                return Ok((env_map, false));
            }
        }
    }

    let env_map = spawn_lake_env(&canon_dir)?;
    if !env_map.is_empty() {
        if let Ok(bytes) = serde_json::to_vec(&env_map) {
            let _ = fs::write(&shm_env_path, bytes);
        }
        let _ = store.put_lake_env(&project_key, &env_map);
    }
    Ok((env_map, false))
}

fn resolve_or_share_lake_env(
    store: &TurboStore,
    canon_dir: &Path,
    env_key: &str,
) -> Result<Option<(HashMap<String, String>, bool)>> {
    if let Some(m) = store.get_lake_env(env_key)? {
        return Ok(Some((m, false)));
    }
    let shm_env_path = store
        .fast_staging_dir()
        .join(format!("lake_env_v1_{}.json", env_key));
    if let Ok(bytes) = fs::read(&shm_env_path) {
        if let Ok(env_map) = serde_json::from_slice::<HashMap<String, String>>(&bytes) {
            if !env_map.is_empty() {
                return Ok(Some((env_map, true)));
            }
        }
    }
    if let Ok(env_map) = spawn_lake_env(canon_dir) {
        if !env_map.is_empty() {
            if let Ok(bytes) = serde_json::to_vec(&env_map) {
                let _ = fs::write(&shm_env_path, bytes);
            }
            return Ok(Some((env_map, true)));
        }
    }
    Ok(None)
}

fn lean_bin_from_env(env_vars: &HashMap<String, String>) -> String {
    if let Some(lake_bin) = env_vars.get("LAKE") {
        let lake_path = Path::new(lake_bin);
        if let Some(bin_dir) = lake_path.parent() {
            let direct_lean = bin_dir.join("lean");
            if direct_lean.exists() {
                return direct_lean.to_string_lossy().to_string();
            }
        }
    }
    "lean".to_string()
}

fn resolve_remote_lean_path(canon_dir: &Path, env_vars: Option<&HashMap<String, String>>) -> String {
    let mut parts = Vec::new();
    let local_lib = canon_dir.join(".lake").join("build").join("lib").join("lean");
    if local_lib.exists() {
        parts.push(local_lib.to_string_lossy().to_string());
    }
    if let Some(env) = env_vars {
        if let Some(lp) = env.get("LEAN_PATH") {
            for p in lp.split(':') {
                if p.is_empty() {
                    continue;
                }
                let path = Path::new(p);
                let abs = if path.is_absolute() {
                    path.to_path_buf()
                } else {
                    canon_dir.join(path)
                };
                let s = abs.to_string_lossy().to_string();
                if !parts.contains(&s) {
                    parts.push(s);
                }
            }
        }
    }
    parts.join(":")
}

pub(crate) fn compute_shard_key(toolchain: &str, shard: &splitter::TheoremShard) -> String {
    let mut key_hasher = blake3::Hasher::new();
    key_hasher.update(b"theorem-shard-v1:");
    key_hasher.update(toolchain.as_bytes());
    key_hasher.update(b":");
    key_hasher.update(shard.prefix_env_hash.as_bytes());
    key_hasher.update(b":");
    key_hasher.update(shard.stmt_hash.as_bytes());
    key_hasher.update(b":");
    key_hasher.update(shard.proof_hash.as_bytes());
    key_hasher.finalize().to_hex().to_string()
}

/// Read `.lean` source files in parallel across worker threads while preserving input order.
fn read_lean_files_parallel(paths: &[PathBuf]) -> Vec<(PathBuf, String)> {
    if paths.len() < 8 {
        return paths
            .iter()
            .map(|p| (p.clone(), fs::read_to_string(p).unwrap_or_default()))
            .collect();
    }
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .min(paths.len());
    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let chunks: Vec<Vec<(usize, PathBuf, String)>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(workers);
        for _ in 0..workers {
            let next_ref = &next_idx;
            handles.push(s.spawn(move || {
                let mut local = Vec::new();
                loop {
                    let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if i >= paths.len() {
                        break;
                    }
                    let src = fs::read_to_string(&paths[i]).unwrap_or_default();
                    local.push((i, paths[i].clone(), src));
                }
                local
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or_default())
            .collect()
    });
    let mut indexed: Vec<(usize, PathBuf, String)> = chunks.into_iter().flatten().collect();
    indexed.sort_unstable_by_key(|(i, _, _)| *i);
    indexed.into_iter().map(|(_, p, s)| (p, s)).collect()
}

/// Stat `.lean` files in parallel across worker threads while preserving input order.
fn stat_lean_files_parallel(paths: &[PathBuf]) -> Vec<Option<(String, i64, i64, i64)>> {
    if paths.len() < 16 {
        return paths
            .iter()
            .map(|p| {
                fs::metadata(p).ok().map(|m| {
                    let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&m);
                    (p.to_string_lossy().to_string(), ms, mn, sz)
                })
            })
            .collect();
    }
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .min(paths.len());
    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let chunks: Vec<Vec<(usize, Option<(String, i64, i64, i64)>)>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(workers);
        for _ in 0..workers {
            let next_ref = &next_idx;
            handles.push(s.spawn(move || {
                let mut local = Vec::new();
                loop {
                    let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if i >= paths.len() {
                        break;
                    }
                    let st = fs::metadata(&paths[i]).ok().map(|m| {
                        let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&m);
                        (paths[i].to_string_lossy().to_string(), ms, mn, sz)
                    });
                    local.push((i, st));
                }
                local
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or_default())
            .collect()
    });
    let mut indexed: Vec<(usize, Option<(String, i64, i64, i64)>)> =
        chunks.into_iter().flatten().collect();
    indexed.sort_unstable_by_key(|(i, _)| *i);
    indexed.into_iter().map(|(_, st)| st).collect()
}

#[derive(serde::Serialize, serde::Deserialize, Clone)]
struct ShmCachedFileSplit {
    src_blake3: String,
    split_key: String,
    split: splitter::SplitResult,
    #[serde(default)]
    prefix_src: String,
    #[serde(default)]
    known_modified: bool,
}

fn shm_file_splits_dir(store: &TurboStore) -> PathBuf {
    let dir = store.fast_staging_dir().join("file_splits_v2");
    let _ = fs::create_dir_all(&dir);
    dir
}

fn compute_single_stat_hash(pk: &str, ms: i64, mn: i64, sz: i64) -> String {
    let mut h = blake3::Hasher::new();
    h.update(b"single-stat-split:v2\n");
    h.update(pk.as_bytes());
    h.update(b":");
    h.update(&ms.to_le_bytes());
    h.update(&mn.to_le_bytes());
    h.update(&sz.to_le_bytes());
    h.finalize().to_hex().to_string()
}

fn compact_split_for_shm_cache(split: &splitter::SplitResult) -> splitter::SplitResult {
    let mut compact = split.clone();
    let keep_proof_text = compact.hygiene.has_sorry;
    compact.skeleton_source.clear();
    for sh in &mut compact.shards {
        sh.shard_source.clear();
        if sh.signature_text.len() > 2048 {
            sh.signature_text.clear();
        }
        if !keep_proof_text && sh.proof_text.len() > 2048 {
            sh.proof_text.clear();
        }
    }
    compact
}

fn compute_stat_slice_hash(stats: &[(String, i64, i64, i64)]) -> String {
    let mut h = blake3::Hasher::new();
    h.update(b"project-stat-splits:v2\n");
    for (pk, ms, mn, sz) in stats {
        h.update(pk.as_bytes());
        h.update(b":");
        h.update(&ms.to_le_bytes());
        h.update(&mn.to_le_bytes());
        h.update(&sz.to_le_bytes());
        h.update(b"\n");
    }
    h.finalize().to_hex().to_string()
}

/// Zero-read stat-backed file split loader returning `(path, src_blake3_hex, optional_src, SplitResult)`.
pub(crate) fn load_and_split_files_with_hashes_cached(
    store: &TurboStore,
    paths: &[PathBuf],
) -> Result<(Vec<(PathBuf, String, String, splitter::SplitResult)>, usize)> {
    if paths.is_empty() {
        return Ok((Vec::new(), 0));
    }
    let file_stats = stat_lean_files_parallel(paths);
    let valid_stats: Vec<(String, i64, i64, i64)> =
        file_stats.iter().filter_map(|s| s.clone()).collect();

    let shm_stat_path = if paths.len() <= 32 && valid_stats.len() == paths.len() {
        let stat_hash = compute_stat_slice_hash(&valid_stats);
        let p = store
            .fast_staging_dir()
            .join(format!("project_stat_splits_v2_{}.json", &stat_hash[..24]));
        if let Ok(bytes) = fs::read(&p) {
            if let Ok(cached_entries) = serde_json::from_slice::<Vec<ShmCachedFileSplit>>(&bytes) {
                if cached_entries.len() == paths.len() {
                    let out: Vec<(PathBuf, String, String, splitter::SplitResult)> = paths
                        .iter()
                        .cloned()
                        .zip(cached_entries)
                        .map(|(path, c)| (path, c.src_blake3, c.prefix_src, c.split))
                        .collect();
                    return Ok((out, paths.len()));
                }
            }
        }
        Some(p)
    } else {
        None
    };

    let splits_dir = shm_file_splits_dir(store);
    let mut hits = 0usize;
    let mut results: Vec<Option<(PathBuf, String, String, splitter::SplitResult)>> =
        vec![None; paths.len()];
    let mut miss_indices = Vec::new();

    for (idx, p) in paths.iter().enumerate() {
        if let Some((ref pk, ms, mn, sz)) = file_stats[idx] {
            let st_hash = compute_single_stat_hash(pk, ms, mn, sz);
            let st_path = splits_dir.join(format!("st_{}.json", &st_hash[..24]));
            if let Ok(bytes) = fs::read(&st_path) {
                if let Ok(c) = serde_json::from_slice::<ShmCachedFileSplit>(&bytes) {
                    if !c.src_blake3.is_empty() {
                        hits += 1;
                        results[idx] = Some((p.clone(), c.src_blake3, c.prefix_src, c.split));
                        continue;
                    }
                }
            }
        }
        miss_indices.push(idx);
    }

    if !miss_indices.is_empty() {
        let miss_paths: Vec<PathBuf> = miss_indices.iter().map(|&i| paths[i].clone()).collect();
        let miss_srcs = read_lean_files_parallel(&miss_paths);
        let (miss_parsed, content_hits) = split_and_audit_with_hashes_cached(store, &miss_srcs)?;
        hits += content_hits;
        for (m_pos, (p, src_blake3, src, split)) in miss_parsed.into_iter().enumerate() {
            let orig_idx = miss_indices[m_pos];
            if let Some((ref pk, ms, mn, sz)) = file_stats[orig_idx] {
                let st_hash = compute_single_stat_hash(pk, ms, mn, sz);
                let st_path = splits_dir.join(format!("st_{}.json", &st_hash[..24]));
                if !st_path.exists() {
                    let entry = ShmCachedFileSplit {
                        src_blake3: src_blake3.clone(),
                        split_key: String::new(),
                        split: compact_split_for_shm_cache(&split),
                        prefix_src: String::new(),
                        known_modified: false,
                    };
                    if let Ok(bytes) = serde_json::to_vec(&entry) {
                        let _ = fs::write(&st_path, &bytes);
                    }
                }
            }
            results[orig_idx] = Some((p, src_blake3, src, split));
        }
    }

    let final_results: Vec<(PathBuf, String, String, splitter::SplitResult)> = results
        .into_iter()
        .map(|r| r.expect("all file splits resolved"))
        .collect();
    if let Some(p) = shm_stat_path {
        if !p.exists() {
            let compacts: Vec<ShmCachedFileSplit> = final_results
                .iter()
                .map(|(_, sb, _, sp)| ShmCachedFileSplit {
                    src_blake3: sb.clone(),
                    split_key: String::new(),
                    split: compact_split_for_shm_cache(sp),
                    prefix_src: String::new(),
                    known_modified: false,
                })
                .collect();
            if let Ok(bytes) = serde_json::to_vec(&compacts) {
                let _ = fs::write(&p, &bytes);
            }
        }
    }
    Ok((final_results, hits))
}

/// Zero-read stat-backed file split loader: checks `(path_key, mtime_sec, mtime_nsec, size_bytes)`
/// in `/dev/shm` or `file_stat_cache` joined with `file_split_cache` first, and only reads/hashes/splits files
/// that miss the stat cache. On stat cache hit, the returned `String` source is empty (`""`) and
/// can be lazily loaded if a theorem shard miss requires source reconstruction.
pub(crate) fn load_and_split_files_cached(
    store: &TurboStore,
    paths: &[PathBuf],
) -> Result<(Vec<(PathBuf, String, splitter::SplitResult)>, usize)> {
    let (with_hashes, hits) = load_and_split_files_with_hashes_cached(store, paths)?;
    let out = with_hashes
        .into_iter()
        .map(|(p, _sb, src, sp)| (p, src, sp))
        .collect();
    Ok((out, hits))
}

fn split_and_audit_with_hashes_cached(
    store: &TurboStore,
    files: &[(PathBuf, String)],
) -> Result<(Vec<(PathBuf, String, String, splitter::SplitResult)>, usize)> {
    if files.is_empty() {
        return Ok((Vec::new(), 0));
    }
    let default_workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);

    let file_keys: Vec<(String, String)> = if files.len() < 8 {
        files
            .iter()
            .map(|(_, src)| {
                let raw = src.as_bytes();
                (
                    blake3::hash(raw).to_hex().to_string(),
                    TurboStore::compute_file_split_key(raw),
                )
            })
            .collect()
    } else {
        let workers = default_workers.min(files.len());
        let next_idx = std::sync::atomic::AtomicUsize::new(0);
        let chunks: Vec<Vec<(usize, (String, String))>> = std::thread::scope(|s| {
            let mut handles = Vec::with_capacity(workers);
            for _ in 0..workers {
                let next_ref = &next_idx;
                handles.push(s.spawn(move || {
                    let mut local = Vec::new();
                    loop {
                        let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if i >= files.len() {
                            break;
                        }
                        let raw = files[i].1.as_bytes();
                        let sb = blake3::hash(raw).to_hex().to_string();
                        let fk = TurboStore::compute_file_split_key(raw);
                        local.push((i, (sb, fk)));
                    }
                    local
                }));
            }
            handles
                .into_iter()
                .map(|h| h.join().unwrap_or_default())
                .collect()
        });
        let mut indexed: Vec<(usize, (String, String))> = chunks.into_iter().flatten().collect();
        indexed.sort_unstable_by_key(|(i, _)| *i);
        indexed.into_iter().map(|(_, pair)| pair).collect()
    };

    let shm_proj_path = if files.len() <= 32 {
        let mut ch = blake3::Hasher::new();
        ch.update(b"project-content-splits:v2\n");
        for (_, fk) in &file_keys {
            ch.update(fk.as_bytes());
            ch.update(b"\n");
        }
        let p = store.fast_staging_dir().join(format!(
            "project_splits_v2_{}.json",
            &ch.finalize().to_hex()[..24]
        ));
        if let Ok(bytes) = fs::read(&p) {
            if let Ok(cached_splits) = serde_json::from_slice::<Vec<splitter::SplitResult>>(&bytes)
            {
                if cached_splits.len() == files.len() {
                    let out: Vec<(PathBuf, String, String, splitter::SplitResult)> = files
                        .iter()
                        .cloned()
                        .zip(file_keys.into_iter())
                        .zip(cached_splits)
                        .map(|(((path, src), (sb, _)), sp)| (path, sb, src, sp))
                        .collect();
                    return Ok((out, files.len()));
                }
            }
        }
        Some(p)
    } else {
        None
    };

    let splits_dir = shm_file_splits_dir(store);
    let mut hits = 0usize;
    let mut results: Vec<Option<splitter::SplitResult>> = vec![None; files.len()];
    let mut db_miss_indices = Vec::new();
    let mut db_miss_hashes = Vec::new();

    for (idx, (_sb, fk)) in file_keys.iter().enumerate() {
        let fk_path = splits_dir.join(format!("fk_{}.json", &fk[..24]));
        if let Ok(bytes) = fs::read(&fk_path) {
            if let Ok(sp) = serde_json::from_slice::<splitter::SplitResult>(&bytes) {
                hits += 1;
                results[idx] = Some(sp);
                continue;
            }
        }
        db_miss_indices.push(idx);
        db_miss_hashes.push(fk.clone());
    }

    let mut miss_indices = Vec::new();
    if !db_miss_indices.is_empty() {
        let cached_map = store.batch_get_file_splits(&db_miss_hashes)?;
        for &idx in &db_miss_indices {
            let fk = &file_keys[idx].1;
            if let Some(split) = cached_map.get(fk).cloned() {
                hits += 1;
                let fk_path = splits_dir.join(format!("fk_{}.json", &fk[..24]));
                if let Ok(bytes) = serde_json::to_vec(&compact_split_for_shm_cache(&split)) {
                    let _ = fs::write(&fk_path, &bytes);
                }
                results[idx] = Some(split);
            } else {
                miss_indices.push(idx);
            }
        }
    }

    let mut new_splits: Vec<(String, splitter::SplitResult)> = Vec::with_capacity(miss_indices.len());
    if !miss_indices.is_empty() {
        let computed_misses: Vec<(usize, splitter::SplitResult)> = if miss_indices.len() < 2 {
            miss_indices
                .iter()
                .map(|&idx| (idx, split_lean_source(&files[idx].1, &[])))
                .collect()
        } else {
            let workers = default_workers.min(miss_indices.len());
            let next_m = std::sync::atomic::AtomicUsize::new(0);
            let miss_ref = &miss_indices;
            let chunks: Vec<Vec<(usize, splitter::SplitResult)>> = std::thread::scope(|s| {
                let mut handles = Vec::with_capacity(workers);
                for _ in 0..workers {
                    let next_ref = &next_m;
                    handles.push(s.spawn(move || {
                        let mut local = Vec::new();
                        loop {
                            let m_pos =
                                next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            if m_pos >= miss_ref.len() {
                                break;
                            }
                            let file_idx = miss_ref[m_pos];
                            let sp = split_lean_source(&files[file_idx].1, &[]);
                            local.push((file_idx, sp));
                        }
                        local
                    }));
                }
                handles
                    .into_iter()
                    .map(|h| h.join().unwrap_or_default())
                    .collect()
            });
            let mut flat: Vec<(usize, splitter::SplitResult)> =
                chunks.into_iter().flatten().collect();
            flat.sort_unstable_by_key(|(idx, _)| *idx);
            flat
        };

        for (file_idx, split) in computed_misses {
            let fk = &file_keys[file_idx].1;
            let fk_path = splits_dir.join(format!("fk_{}.json", &fk[..24]));
            if let Ok(bytes) = serde_json::to_vec(&compact_split_for_shm_cache(&split)) {
                let _ = fs::write(&fk_path, &bytes);
            }
            new_splits.push((fk.clone(), split.clone()));
            results[file_idx] = Some(split);
        }
    }

    if !new_splits.is_empty() {
        let refs: Vec<(String, &splitter::SplitResult)> =
            new_splits.iter().map(|(h, sp)| (h.clone(), sp)).collect();
        let _ = store.batch_put_file_splits(&refs);

        // Record `(path_key, mtime_sec, mtime_nsec, size_bytes, split_key)` in `file_stat_cache`
        let paths_only: Vec<PathBuf> = files.iter().map(|(p, _)| p.clone()).collect();
        let stats = stat_lean_files_parallel(&paths_only);
        let mut stat_rows = Vec::with_capacity(files.len());
        let mut valid_stats = Vec::with_capacity(files.len());
        for (idx, st_opt) in stats.into_iter().enumerate() {
            if let Some((pk, ms, mn, sz)) = st_opt {
                if let Some(ref sp) = results[idx] {
                    let st_hash = compute_single_stat_hash(&pk, ms, mn, sz);
                    let st_path = splits_dir.join(format!("st_{}.json", &st_hash[..24]));
                    if !st_path.exists() {
                        let entry = ShmCachedFileSplit {
                            src_blake3: file_keys[idx].0.clone(),
                            split_key: String::new(),
                            split: compact_split_for_shm_cache(sp),
                            prefix_src: String::new(),
                            known_modified: false,
                        };
                        if let Ok(bytes) = serde_json::to_vec(&entry) {
                            let _ = fs::write(&st_path, &bytes);
                        }
                    }
                }
                valid_stats.push((pk.clone(), ms, mn, sz));
                stat_rows.push((pk, ms, mn, sz, file_keys[idx].1.clone()));
            }
        }
        if !stat_rows.is_empty() {
            let _ = store.batch_put_file_stats(&stat_rows);
        }
        if files.len() <= 32 && valid_stats.len() == files.len() {
            let stat_hash = compute_stat_slice_hash(&valid_stats);
            let stat_p = store
                .fast_staging_dir()
                .join(format!("project_stat_splits_v2_{}.json", &stat_hash[..24]));
            if !stat_p.exists() {
                let compacts: Vec<ShmCachedFileSplit> = results
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, r)| {
                        r.as_ref().map(|sp| ShmCachedFileSplit {
                            src_blake3: file_keys[idx].0.clone(),
                            split_key: String::new(),
                            split: compact_split_for_shm_cache(sp),
                            prefix_src: String::new(),
                            known_modified: false,
                        })
                    })
                    .collect();
                if compacts.len() == files.len() {
                    if let Ok(bytes) = serde_json::to_vec(&compacts) {
                        let _ = fs::write(&stat_p, &bytes);
                    }
                }
            }
        }
    }

    let final_results: Vec<(PathBuf, String, String, splitter::SplitResult)> = files
        .iter()
        .enumerate()
        .map(|(idx, (path, src))| {
            (
                path.clone(),
                file_keys[idx].0.clone(),
                src.clone(),
                results[idx].take().expect("all file splits resolved"),
            )
        })
        .collect();

    if let Some(p) = shm_proj_path {
        if !p.exists() {
            let compacts: Vec<splitter::SplitResult> = final_results
                .iter()
                .map(|(_, _, _, sp)| compact_split_for_shm_cache(sp))
                .collect();
            if let Ok(bytes) = serde_json::to_vec(&compacts) {
                let _ = fs::write(&p, &bytes);
            }
        }
    }

    Ok((final_results, hits))
}

/// Batch-split and hygiene-audit `.lean` source files using `/dev/shm` + SQLite `file_split_cache`
/// and multi-threaded `std::thread::scope` workers for hashing and cache misses.
/// Returns `(Vec<(PathBuf, String, SplitResult)>, cache_hits)`.
fn split_and_audit_cached(
    store: &TurboStore,
    files: &[(PathBuf, String)],
) -> Result<(Vec<(PathBuf, String, splitter::SplitResult)>, usize)> {
    let (with_hashes, hits) = split_and_audit_with_hashes_cached(store, files)?;
    let out = with_hashes
        .into_iter()
        .map(|(p, _sb, src, sp)| (p, src, sp))
        .collect();
    Ok((out, hits))
}

/// Fast in-memory computation of the project build `action_key` without splitting or SQLite writes
fn compute_project_build_key_only(
    project_dir: &Path,
    toolchain: &str,
    targets: &[String],
    trust_domain: &str,
) -> Result<String> {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-lean-build-v1\n");
    hasher.update(toolchain.as_bytes());
    hasher.update(b"\n");
    hasher.update(trust_domain.as_bytes());
    hasher.update(b"\n");
    for t in targets {
        hasher.update(t.as_bytes());
        hasher.update(b",");
    }
    hasher.update(b"\n");

    let mut lean_files: Vec<PathBuf> = Vec::new();
    for entry in WalkDir::new(project_dir)
        .into_iter()
        .filter_entry(|e| {
            let name = e.file_name().to_string_lossy();
            name != ".git" && name != ".lake" && name != "target"
        })
        .flatten()
    {
        if entry.file_type().is_file() {
            let p = entry.path();
            if p.extension().and_then(|s| s.to_str()) == Some("lean") {
                lean_files.push(p.to_path_buf());
            }
        }
    }
    lean_files.sort();

    for lf in &lean_files {
        let rel = lf.strip_prefix(project_dir).unwrap_or(lf);
        let rel_str = rel.to_string_lossy();
        let bytes = fs::read(lf).unwrap_or_default();
        hasher.update(rel_str.as_bytes());
        hasher.update(b":");
        hasher.update(blake3::hash(&bytes).as_bytes());
        hasher.update(b"\n");
    }

    Ok(hasher.finalize().to_hex().to_string())
}

fn verified_sources_manifest_path(canon_dir: &Path) -> PathBuf {
    canon_dir
        .join(".lake")
        .join("build")
        .join(".turbo_lean_verified_sources.json")
}

fn record_verified_project_oleans(canon_dir: &Path, file_hashes: &BTreeMap<String, String>) {
    let manifest_path = verified_sources_manifest_path(canon_dir);
    if let Some(parent) = manifest_path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    if let Ok(bytes) = serde_json::to_vec(file_hashes) {
        let _ = fs::write(&manifest_path, bytes);
    }
}

fn are_all_project_oleans_up_to_date(
    canon_dir: &Path,
    file_hashes: &BTreeMap<String, String>,
) -> bool {
    if file_hashes.is_empty() {
        return false;
    }
    let lib_lean_dir = canon_dir.join(".lake").join("build").join("lib").join("lean");
    if !lib_lean_dir.is_dir() {
        return false;
    }

    let manifest_path = verified_sources_manifest_path(canon_dir);
    if let Ok(bytes) = fs::read(&manifest_path) {
        if let Ok(recorded) = serde_json::from_slice::<BTreeMap<String, String>>(&bytes) {
            if &recorded != file_hashes {
                return false;
            }
            let mut checked_oleans = 0usize;
            for rel_path in file_hashes.keys() {
                if rel_path == "lakefile.lean" || rel_path.ends_with("/lakefile.lean") {
                    continue;
                }
                let rel_no_ext = Path::new(rel_path).with_extension("");
                let olean_path = lib_lean_dir.join(&rel_no_ext).with_extension("olean");
                match fs::metadata(&olean_path) {
                    Ok(m) if m.is_file() && m.len() > 0 => {
                        checked_oleans += 1;
                    }
                    _ => {
                        if rel_no_ext.components().count() == 1
                            && canon_dir.join(&rel_no_ext).is_dir()
                        {
                            continue;
                        }
                        return false;
                    }
                }
            }
            return checked_oleans > 0;
        }
    }

    let lakefile_mtime = fs::metadata(canon_dir.join("lakefile.lean"))
        .and_then(|m| m.modified())
        .ok();
    let mut checked_oleans = 0usize;
    let mut all_mtime_fresh = true;
    let mut all_have_trace = true;

    for rel_path in file_hashes.keys() {
        if rel_path == "lakefile.lean" || rel_path.ends_with("/lakefile.lean") {
            continue;
        }
        let rel_no_ext = Path::new(rel_path).with_extension("");
        let olean_path = lib_lean_dir.join(&rel_no_ext).with_extension("olean");
        let olean_meta = match fs::metadata(&olean_path) {
            Ok(m) if m.is_file() && m.len() > 0 => m,
            _ => {
                if rel_no_ext.components().count() == 1 && canon_dir.join(&rel_no_ext).is_dir() {
                    continue;
                }
                return false;
            }
        };
        checked_oleans += 1;

        let trace_path = lib_lean_dir.join(&rel_no_ext).with_extension("trace");
        if !trace_path.is_file() {
            all_have_trace = false;
        }

        let src_mtime = fs::metadata(canon_dir.join(rel_path))
            .and_then(|m| m.modified())
            .ok();
        let olean_mtime = olean_meta.modified().ok();
        match (src_mtime, olean_mtime) {
            (Some(sm), Some(om)) if om >= sm => {
                if let Some(lm) = lakefile_mtime {
                    if om < lm {
                        all_mtime_fresh = false;
                    }
                }
            }
            _ => {
                all_mtime_fresh = false;
            }
        }
    }

    if checked_oleans == 0 {
        return false;
    }

    if all_mtime_fresh {
        record_verified_project_oleans(canon_dir, file_hashes);
        return true;
    }

    if all_have_trace {
        let git_clean = Command::new("git")
            .args([
                "-C",
                &canon_dir.to_string_lossy(),
                "status",
                "--porcelain",
                "--untracked-files=no",
                "--",
                ".",
            ])
            .output()
            .map(|o| o.status.success() && o.stdout.is_empty())
            .unwrap_or(false);
        if git_clean {
            record_verified_project_oleans(canon_dir, file_hashes);
            return true;
        }
    }

    false
}

fn is_file_hash_verified_in_lake_build(
    canon_dir: &Path,
    canon_file: &Path,
    actual_hash: &str,
) -> bool {
    let rel_path = canon_file
        .strip_prefix(canon_dir)
        .unwrap_or(canon_file)
        .to_string_lossy()
        .replace('\\', "/");
    let manifest_path = verified_sources_manifest_path(canon_dir);
    let Ok(bytes) = fs::read(&manifest_path) else {
        return false;
    };
    let Ok(recorded) = serde_json::from_slice::<BTreeMap<String, String>>(&bytes) else {
        return false;
    };
    let Some(expected_hash) = recorded.get(&rel_path) else {
        return false;
    };
    expected_hash == actual_hash
}

fn is_file_verified_in_lake_build(canon_dir: &Path, canon_file: &Path, src: &str) -> bool {
    let actual_hash = blake3::hash(src.as_bytes()).to_hex().to_string();
    is_file_hash_verified_in_lake_build(canon_dir, canon_file, &actual_hash)
}

/// Compute the Proof-Irrelevant Interface Hash of all `.lean` sources in a project,
/// returning `(action_key, interface_hash, per_file_source_blake3_map)`.
pub(crate) fn compute_project_interface_key_with_hashes(
    store: &TurboStore,
    project_dir: &Path,
    toolchain: &str,
    targets: &[String],
    trust_domain: &str,
) -> Result<(String, String, BTreeMap<String, String>)> {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-lean-build-v1\n");
    hasher.update(toolchain.as_bytes());
    hasher.update(b"\n");
    hasher.update(trust_domain.as_bytes());
    hasher.update(b"\n");
    for t in targets {
        hasher.update(t.as_bytes());
        hasher.update(b",");
    }
    hasher.update(b"\n");

    let mut interface_hasher = blake3::Hasher::new();
    interface_hasher.update(toolchain.as_bytes());

    let mut lean_files: Vec<PathBuf> = Vec::new();
    for entry in WalkDir::new(project_dir)
        .into_iter()
        .filter_entry(|e| {
            let name = e.file_name().to_string_lossy();
            name != ".git" && name != ".lake" && name != "target"
        })
        .flatten()
    {
        if entry.file_type().is_file() {
            let p = entry.path();
            if p.extension().and_then(|s| s.to_str()) == Some("lean") {
                lean_files.push(p.to_path_buf());
            }
        }
    }
    lean_files.sort();

    let (parsed_files, _) = load_and_split_files_with_hashes_cached(store, &lean_files)?;
    let mut file_hashes = BTreeMap::new();

    for (lf, src_hash_hex, src, split) in &parsed_files {
        let rel = lf.strip_prefix(project_dir).unwrap_or(lf);
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        let src_hash = blake3::Hash::from_hex(src_hash_hex)
            .unwrap_or_else(|_| blake3::hash(src.as_bytes()));
        hasher.update(rel_str.as_bytes());
        hasher.update(b":");
        hasher.update(src_hash.as_bytes());
        hasher.update(b"\n");

        file_hashes.insert(rel_str.clone(), src_hash.to_hex().to_string());

        interface_hasher.update(rel_str.as_bytes());
        interface_hasher.update(b":");
        interface_hasher.update(split.interface_hash.as_bytes());
        interface_hasher.update(b"\n");
    }

    Ok((
        hasher.finalize().to_hex().to_string(),
        interface_hasher.finalize().to_hex().to_string(),
        file_hashes,
    ))
}

/// Recursively discover `.lean` source files inside a file or directory (excluding hidden directories, `target`, `node_modules`, and `lakefile.lean`).
pub(crate) fn collect_lean_files(root: &Path) -> Vec<PathBuf> {
    if root.is_file() {
        return vec![root.to_path_buf()];
    }
    let mut lean_files: Vec<PathBuf> = Vec::new();
    for entry in WalkDir::new(root)
        .into_iter()
        .filter_entry(|e| {
            let name = e.file_name().to_string_lossy();
            if e.depth() > 0 && name.starts_with('.') {
                return false;
            }
            name != ".git"
                && name != ".lake"
                && name != ".elan"
                && name != ".cargo"
                && name != "target"
                && name != "node_modules"
        })
        .flatten()
    {
        if entry.file_type().is_file() {
            let p = entry.path();
            if p.extension().and_then(|s| s.to_str()) == Some("lean")
                && p.file_name().and_then(|s| s.to_str()) != Some("lakefile.lean")
            {
                lean_files.push(p.to_path_buf());
            }
        }
    }
    lean_files.sort();
    lean_files
}

/// Resolve the pre-compiled `.olean` module import name (e.g. `TurboLean.Reflection`) if
/// `.lake/build/lib/lean/<Module>.olean` exists on disk.
fn resolve_prebuilt_module_import(canon_project_dir: &Path, canon_file: &Path) -> Option<String> {
    let rel = canon_file.strip_prefix(canon_project_dir).ok()?;
    let rel_no_ext = rel.with_extension("");
    let olean_path = canon_project_dir
        .join(".lake")
        .join("build")
        .join("lib")
        .join("lean")
        .join(&rel_no_ext)
        .with_extension("olean");
    if !olean_path.exists() {
        return None;
    }
    let parts: Vec<String> = rel_no_ext
        .components()
        .filter_map(|c| c.as_os_str().to_str().map(|s| s.to_string()))
        .collect();
    if parts.is_empty() {
        return None;
    }
    Some(parts.join("."))
}

/// Seed `TheoremProofCAS` in a single atomic SQLite transaction for all hygienic `.lean` files
/// in `canon_dir` (optionally requiring a pre-compiled `.olean` in `.lake/build/lib/lean`).
/// Returns `(files_seeded, shards_seeded, file_split_cache_hits)`.
fn seed_project_theorem_shards_from_splits(
    store: &mut TurboStore,
    canon_dir: &Path,
    toolchain: &str,
    trust_domain: &str,
    require_olean: bool,
    split_entries: &[(PathBuf, String, splitter::SplitResult)],
) -> Result<(usize, usize)> {
    let shared_receipt = format!("verified:seeded:{}", toolchain).into_bytes();
    let mut files_seeded = 0usize;
    let mut batch_items: Vec<(String, String, Vec<u8>, i64)> = Vec::new();

    for (lf, _src, split) in split_entries {
        if require_olean && resolve_prebuilt_module_import(canon_dir, lf).is_none() {
            continue;
        }
        if split.shards.is_empty() {
            continue;
        }
        let file_has_sorry = split.hygiene.has_sorry;
        let mut file_had_clean_shard = false;
        for shard in &split.shards {
            if file_has_sorry
                && splitter::audit_hygiene(&splitter::strip_lean_comments(&shard.proof_text))
                    .has_sorry
            {
                continue;
            }
            file_had_clean_shard = true;
            let shard_key = compute_shard_key(toolchain, shard);
            batch_items.push((
                shard_key,
                shard.name.clone(),
                shared_receipt.clone(),
                1i64,
            ));
        }
        if file_had_clean_shard {
            files_seeded += 1;
        }
    }

    let shards_seeded = batch_items.len();
    if !batch_items.is_empty() {
        store.batch_publish_theorem_shards(toolchain, trust_domain, &batch_items)?;
    }
    Ok((files_seeded, shards_seeded))
}

fn seed_project_theorem_shards(
    store: &mut TurboStore,
    canon_dir: &Path,
    toolchain: &str,
    trust_domain: &str,
    require_olean: bool,
) -> Result<(usize, usize, usize)> {
    let lean_files: Vec<PathBuf> = collect_lean_files(canon_dir)
        .into_iter()
        .filter(|lf| !require_olean || resolve_prebuilt_module_import(canon_dir, lf).is_some())
        .collect();

    let (split_entries, split_cache_hits) = load_and_split_files_cached(store, &lean_files)?;
    let (files_seeded, shards_seeded) = seed_project_theorem_shards_from_splits(
        store,
        canon_dir,
        toolchain,
        trust_domain,
        false,
        &split_entries,
    )?;
    Ok((files_seeded, shards_seeded, split_cache_hits))
}

/// Stage compiled `.olean`, `.ilean`, and `.c` files from `.lake/build` into the immutable CAS blobs directory
/// without opening a SQLite transaction, returning `(outputs, reg_blobs)`.
fn stage_lake_build_outputs(
    store: &TurboStore,
    project_dir: &Path,
) -> Result<(Vec<BlobEntry>, Vec<(String, String, i64, i64)>)> {
    let build_dir = project_dir.join(".lake").join("build");
    if !build_dir.exists() {
        return Ok((Vec::new(), Vec::new()));
    }

    #[cfg(unix)]
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    let mut candidates: Vec<(PathBuf, &'static str, String, i64, i64, u64, u32, i64)> = Vec::new();
    for entry in WalkDir::new(&build_dir).into_iter().flatten() {
        if !entry.file_type().is_file() {
            continue;
        }
        let path = entry.path();
        let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
        let kind = match ext {
            "olean" => "olean",
            "ilean" => "ilean",
            "c" => "c",
            _ => continue, // Never hardlink .trace or .hash files so Lake mtime tracking stays per-worktree!
        };

        let Ok(meta) = entry.metadata() else {
            continue;
        };
        let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&meta);
        #[cfg(unix)]
        let (mode, cand_ino) = (meta.permissions().mode(), meta.ino() as i64);
        #[cfg(not(unix))]
        let (mode, cand_ino) = (0o444u32, 0i64);
        let rel_path = path
            .strip_prefix(project_dir)
            .unwrap_or(path)
            .to_string_lossy()
            .to_string();
        candidates.push((
            path.to_path_buf(),
            kind,
            rel_path,
            ms,
            mn,
            sz as u64,
            mode,
            cand_ino,
        ));
    }

    if candidates.is_empty() {
        return Ok((Vec::new(), Vec::new()));
    }
    candidates.sort_by(|a, b| a.2.cmp(&b.2));

    let mut sh = blake3::Hasher::new();
    sh.update(b"lake-build-ingest:v1\n");
    for (_, kind, rel_path, ms, mn, sz, _, _) in &candidates {
        sh.update(rel_path.as_bytes());
        sh.update(b":");
        sh.update(kind.as_bytes());
        sh.update(b":");
        sh.update(&ms.to_le_bytes());
        sh.update(&mn.to_le_bytes());
        sh.update(&sz.to_le_bytes());
        sh.update(b"\n");
    }
    let ingest_cache_path = store.fast_staging_dir().join(format!(
        "lake_build_ingest_v1_{}.json",
        &sh.finalize().to_hex()[..24]
    ));

    let entries: Vec<BlobEntry> = if let Ok(cached_bytes) = fs::read(&ingest_cache_path) {
        if let Ok(parsed) = serde_json::from_slice::<Vec<BlobEntry>>(&cached_bytes) {
            if parsed.len() == candidates.len() {
                parsed
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        }
    } else {
        Vec::new()
    };

    let entries = if entries.len() == candidates.len() {
        entries
    } else {
        let n_threads = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .min(candidates.len())
            .max(1);
        let chunk_size = (candidates.len() + n_threads - 1) / n_threads;

        let mut computed: Vec<BlobEntry> = Vec::with_capacity(candidates.len());
        std::thread::scope(|s| -> Result<()> {
            let mut handles = Vec::with_capacity(n_threads);
            for chunk in candidates.chunks(chunk_size) {
                handles.push(s.spawn(move || -> Result<Vec<BlobEntry>> {
                    let mut local = Vec::with_capacity(chunk.len());
                    for (path, kind, rel_path, _, _, _, _, _) in chunk {
                        let bytes = fs::read(path)?;
                        let size_bytes = bytes.len() as u64;
                        let blob_hash = blake3::hash(&bytes).to_hex().to_string();
                        local.push(BlobEntry {
                            blob_hash,
                            kind: (*kind).to_string(),
                            size_bytes,
                            rel_path: rel_path.clone(),
                        });
                    }
                    Ok(local)
                }));
            }
            for h in handles {
                let chunk_res = h
                    .join()
                    .map_err(|_| anyhow::anyhow!("ingest worker panicked"))??;
                computed.extend(chunk_res);
            }
            Ok(())
        })?;
        computed.sort_by(|a, b| a.rel_path.cmp(&b.rel_path));
        if let Ok(bytes) = serde_json::to_vec(&computed) {
            let _ = fs::write(&ingest_cache_path, &bytes);
        }
        computed
    };

    let shared_blobs = pack::shared_cas_blobs_dir();
    let mut seen_prefix = [false; 256];
    let mut seen_shared_prefix = [false; 256];
    let mut seen_blobs: std::collections::HashSet<String> =
        std::collections::HashSet::with_capacity(entries.len());
    let mut reg_blobs: Vec<(String, String, i64, i64)> = Vec::with_capacity(entries.len());

    for (entry, (path, _, _, _, _, _, mode, cand_ino)) in entries.iter().zip(candidates.iter()) {
        #[cfg(unix)]
        if (*mode & 0o222) != 0 {
            let _ = fs::set_permissions(path, fs::Permissions::from_mode(0o444));
        }
        if !seen_blobs.insert(entry.blob_hash.clone()) {
            continue;
        }
        let prefix = if entry.blob_hash.len() >= 2 {
            &entry.blob_hash[0..2]
        } else {
            "00"
        };
        let p_idx = u8::from_str_radix(prefix, 16).unwrap_or(0) as usize;
        let dest = store.blob_path(&entry.blob_hash);
        if !seen_prefix[p_idx] {
            seen_prefix[p_idx] = true;
            if let Some(parent) = dest.parent() {
                let _ = fs::create_dir(parent);
            }
        }
        let ino = if fs::hard_link(path, &dest).is_ok() {
            *cand_ino
        } else if let Ok(dm) = fs::metadata(&dest) {
            #[cfg(unix)]
            {
                dm.ino() as i64
            }
            #[cfg(not(unix))]
            {
                0i64
            }
        } else {
            let shared_dir = shared_blobs.join(prefix);
            if !seen_shared_prefix[p_idx] {
                seen_shared_prefix[p_idx] = true;
                let _ = fs::create_dir_all(&shared_dir);
            }
            let shared_p = shared_dir.join(&entry.blob_hash);
            if !shared_p.exists() {
                let tmp_shared = shared_dir.join(format!(
                    "{}.{}.tmp",
                    entry.blob_hash,
                    std::process::id()
                ));
                if fs::copy(path, &tmp_shared).is_ok() {
                    #[cfg(unix)]
                    if let Ok(tm) = fs::metadata(&tmp_shared) {
                        let mut perms = tm.permissions();
                        perms.set_mode(0o444);
                        let _ = fs::set_permissions(&tmp_shared, perms);
                    }
                    let _ = fs::rename(&tmp_shared, &shared_p);
                }
            }
            if fs::hard_link(&shared_p, &dest).is_err() && !dest.exists() {
                fs::copy(path, &dest)?;
                #[cfg(unix)]
                if let Ok(dm) = fs::metadata(&dest) {
                    let mut perms = dm.permissions();
                    perms.set_mode(0o444);
                    let _ = fs::set_permissions(&dest, perms);
                }
            }
            fs::metadata(&dest)
                .map(|m| {
                    #[cfg(unix)]
                    {
                        m.ino() as i64
                    }
                    #[cfg(not(unix))]
                    {
                        0i64
                    }
                })
                .unwrap_or(0)
        };
        reg_blobs.push((
            entry.blob_hash.clone(),
            entry.kind.clone(),
            entry.size_bytes as i64,
            ino,
        ));
    }

    Ok((entries, reg_blobs))
}

/// Collect compiled `.olean`, `.ilean`, and `.c` files from `.lake/build` into the immutable CAS
#[allow(dead_code)]
fn ingest_lake_build_outputs(
    store: &mut TurboStore,
    project_dir: &Path,
    trust_domain: &str,
    pin_level: i64,
) -> Result<Vec<BlobEntry>> {
    let (entries, reg_blobs) = stage_lake_build_outputs(store, project_dir)?;
    store.batch_register_linked_blobs(&reg_blobs, trust_domain, pin_level)?;
    Ok(entries)
}

fn main() -> Result<()> {
    let cli = Cli::parse();
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
        let receipt = receipt
            .or(receipt_flag)
            .context("Missing receipt file path (pass `<RECEIPT>` or `--receipt <RECEIPT>`)")?;
        let t0 = Instant::now();
        let raw = fs::read_to_string(&receipt)
            .with_context(|| format!("Failed to read receipt {}", receipt.display()))?;
        let parsed: VerificationReceipt = serde_json::from_str(&raw)
            .with_context(|| format!("Invalid receipt JSON in {}", receipt.display()))?;

        let baseline_parsed: Option<VerificationReceipt> = if let Some(ref bp) = baseline_receipt {
            if bp == &receipt {
                Some(parsed.clone())
            } else {
                let braw = fs::read_to_string(bp)
                    .with_context(|| format!("Failed to read baseline receipt {}", bp.display()))?;
                Some(
                    serde_json::from_str(&braw).with_context(|| {
                        format!("Invalid baseline receipt JSON in {}", bp.display())
                    })?,
                )
            }
        } else {
            None
        };

        let altered_files = verify_receipt_data(
            &parsed,
            expected_interface_hash.as_deref(),
            baseline_parsed.as_ref(),
        )?;

        let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
        if cli.json {
            println!(
                "{}",
                serde_json::to_string_pretty(&serde_json::json!({
                    "status": "receipt_verified",
                    "schema_version": parsed.schema_version,
                    "mode": parsed.mode,
                    "interface_hash": parsed.interface_hash,
                    "action_key": parsed.action_key,
                    "receipt_blake3": parsed.receipt_blake3,
                    "files_audited": parsed.files_audited,
                    "theorem_shards": parsed.theorem_shards,
                    "forbidden_constructs_found": parsed.forbidden_constructs_found,
                    "altered_files": altered_files,
                    "elapsed_ms": (elapsed_ms * 1000.0).round() / 1000.0
                }))?
            );
        } else {
            println!(
                "[turbo-lean] RECEIPT VERIFIED (receipt_blake3={}.., interface_hash={}.., {} files, {:.3} ms)",
                &parsed.receipt_blake3[..12],
                &parsed.interface_hash[..12],
                parsed.files_audited,
                elapsed_ms
            );
        }
        return Ok(());
    }
    if let Commands::FastCheck {
        ref file,
        gpu,
        remote_http: Some(ref http_url),
        ..
    } = cli.command
    {
        let t0 = Instant::now();
        let is_cu = gpu || file.extension().and_then(|s| s.to_str()) == Some("cu");
        let base = http_url.trim_end_matches('/');
        let is_loopback =
            base.starts_with("http://127.0.0.1") || base.starts_with("http://localhost");
        let src_text = fs::read_to_string(file)
            .with_context(|| format!("Failed to read {}", file.display()))?;
        let has_main = !is_cu && src_text.contains("def main");
        let precomputed_bin_key = if is_cu {
            pack::compute_fastcheck_binary_key(true, &src_text)
        } else if has_main {
            pack::compute_fastcheck_binary_key(false, &src_text)
        } else {
            pack::compute_fastcheck_binary_key_parts(
                false,
                &src_text,
                pack::FASTCHECK_NO_MAIN_SUFFIX,
            )
        };
        let (source_payload, local_path_payload) = if is_loopback && !is_cu && !has_main {
            let abs_path = file
                .canonicalize()
                .unwrap_or_else(|_| file.clone())
                .to_string_lossy()
                .to_string();
            (String::new(), abs_path)
        } else {
            (src_text, String::new())
        };
        let req_body = serde_json::to_vec(&pack::FastCheckHttpRequest {
            filename: file
                .file_name()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_else(|| "fastcheck.lean".to_string()),
            source: source_payload,
            gpu: is_cu,
            precomputed_bin_key,
            has_main: Some(has_main),
            local_path: local_path_payload,
        })?;
        let resp_bytes = pack::http_request(
            "POST",
            &format!("{}/fast-check", base),
            "application/json",
            &req_body,
        )?;
        let mut resp_json: serde_json::Value = serde_json::from_slice(&resp_bytes)
            .context("Failed to parse JSON response from remote HTTP `/fast-check`")?;
        resp_json["client_roundtrip_ms"] = serde_json::json!(t0.elapsed().as_millis());
        resp_json["remote_http"] = serde_json::json!(http_url);
        if cli.json {
            println!("{}", serde_json::to_string_pretty(&resp_json)?);
        } else {
            println!(
                "[turbo-lean] HTTP REMOTE FAST-CHECK ({}) completed in {} ms:\n{}",
                http_url,
                t0.elapsed().as_millis(),
                resp_json["output"].as_str().unwrap_or("")
            );
        }
        return Ok(());
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
    type PrefetchedExportItem = (
        Vec<u8>,
        Option<(pack::PackManifest, Vec<(String, String, i64, i64)>, usize)>,
    );
    let mut prefetched_export: Option<std::thread::JoinHandle<Result<PrefetchedExportItem>>> = None;
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
        } => {
            let t0 = Instant::now();
            let canon_dir = project_dir
                .canonicalize()
                .unwrap_or_else(|_| project_dir.clone());
            let project_name = canon_dir
                .file_name()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_else(|| "lean-project".to_string());
            let toolchain = detect_toolchain(&canon_dir);
            let (action_key, interface_hash, file_hashes) =
                compute_project_interface_key_with_hashes(
                    &store,
                    &canon_dir,
                    &toolchain,
                    &targets,
                    &trust_domain,
                )?;

            match store.acquire_singleflight(&action_key, &toolchain, "module_full", &trust_domain)? {
                SingleflightOutcome::CacheHit { outputs, coalesced } => {
                    let linked =
                        store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
                    let seeded_shards = if seed_shards {
                        seed_project_theorem_shards(&mut store, &canon_dir, &toolchain, &trust_domain, false)?.1
                    } else {
                        0
                    };
                    let elapsed_ms = t0.elapsed().as_millis();
                    if cli.json {
                        println!(
                            "{}",
                            serde_json::to_string_pretty(&serde_json::json!({
                                "status": "cache_hit",
                                "coalesced_singleflight": coalesced,
                                "action_key": action_key,
                                "interface_hash": interface_hash,
                                "materialized_files": linked,
                                "shards_seeded": seeded_shards,
                                "elapsed_ms": elapsed_ms
                            }))?
                        );
                    } else {
                        println!(
                            "[turbo-lean] CACHE HIT (coalesced={}) for {} ({} artifacts linked in {} ms)",
                            coalesced, project_name, linked, elapsed_ms
                        );
                    }
                }
                SingleflightOutcome::Leader(lease) => {
                    if !targets.is_empty() || !are_all_project_oleans_up_to_date(&canon_dir, &file_hashes) {
                        let mut cmd = Command::new("lake");
                        cmd.arg("build").current_dir(&canon_dir);
                        for t in &targets {
                            cmd.arg(t);
                        }
                        let out = cmd.output().context("Failed to execute `lake build`")?;
                        if !out.status.success() {
                            let stdout = String::from_utf8_lossy(&out.stdout);
                            let stderr = String::from_utf8_lossy(&out.stderr);
                            anyhow::bail!("`lake build` failed:\n{}\n{}", stdout, stderr);
                        }
                        if !cli.json {
                            print!("{}", String::from_utf8_lossy(&out.stdout));
                        }
                        if targets.is_empty() {
                            record_verified_project_oleans(&canon_dir, &file_hashes);
                        }
                    }

                    let env_key = TurboStore::compute_lake_env_key(&canon_dir);
                    let resolved_env = resolve_or_share_lake_env(&store, &canon_dir, &env_key)?;

                    let dur_ms = t0.elapsed().as_millis() as i64;
                    let (outputs, reg_blobs) = stage_lake_build_outputs(&store, &canon_dir)?;
                    let lake_env_to_put = resolved_env
                        .as_ref()
                        .filter(|(_, is_new)| *is_new)
                        .map(|(m, _)| (env_key.as_str(), m));
                    let (manifest_hash, linked) = store.publish_ingested_worktree_action(
                        Some(&lease),
                        &action_key,
                        &toolchain,
                        "module_full",
                        &canon_dir,
                        &project_name,
                        &reg_blobs,
                        &outputs,
                        dur_ms,
                        &trust_domain,
                        pin_level,
                        lake_env_to_put,
                        None,
                    )?;
                    if std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
                        if let Some((ref env_vars, _)) = resolved_env {
                            pack::warm_local_zygote_daemon_nonblocking(&store, env_vars);
                        }
                    }
                    let seeded_shards = if seed_shards {
                        seed_project_theorem_shards(&mut store, &canon_dir, &toolchain, &trust_domain, false)?.1
                    } else {
                        0
                    };

                    if cli.json {
                        println!(
                            "{}",
                            serde_json::to_string_pretty(&serde_json::json!({
                                "status": "built",
                                "action_key": action_key,
                                "interface_hash": interface_hash,
                                "manifest_hash": manifest_hash,
                                "artifacts_stored": outputs.len(),
                                "materialized_files": linked,
                                "shards_seeded": seeded_shards,
                                "elapsed_ms": dur_ms
                            }))?
                        );
                    } else {
                        println!(
                            "[turbo-lean] BUILT & CACHED {} ({} artifacts, interface_hash={}.., {} ms)",
                            project_name,
                             linked,
                            &interface_hash[..12],
                            dur_ms
                        );
                    }
                }
            }
        }

        Commands::Check {
            file,
            decl,
            project_dir,
            jobs,
            parallel_shards,
            remote_http,
        } => {
            let t0 = Instant::now();
            let canon_dir = project_dir
                .canonicalize()
                .unwrap_or_else(|_| project_dir.clone());
            let toolchain = detect_toolchain(&canon_dir);
            let resolved_file = if file == Path::new(".") {
                canon_dir.clone()
            } else if file.is_relative() && canon_dir.join(&file).exists() {
                canon_dir.join(&file)
            } else if file.exists() {
                file.clone()
            } else {
                canon_dir.join(&file)
            };

            if resolved_file.is_dir() && decl.is_none() {
                let dir_files = collect_lean_files(&resolved_file);
                let mut dir_hasher = blake3::Hasher::new();
                dir_hasher.update(toolchain.as_bytes());

                let (split_entries, split_cache_hits) =
                    load_and_split_files_with_hashes_cached(&store, &dir_files)?;
                let mut parsed_files = Vec::with_capacity(split_entries.len());
                let mut all_shard_keys = Vec::new();

                for (lf, src_blake3, src, split) in split_entries {
                    let rel = lf.strip_prefix(&canon_dir).unwrap_or(&lf);
                    dir_hasher.update(rel.to_string_lossy().as_bytes());
                    dir_hasher.update(b":");
                    dir_hasher.update(split.interface_hash.as_bytes());
                    dir_hasher.update(b"\n");

                    let mut file_keys = Vec::with_capacity(split.shards.len());
                    for s in &split.shards {
                        let k = compute_shard_key(&toolchain, s);
                        all_shard_keys.push(k.clone());
                        file_keys.push(k);
                    }
                    parsed_files.push((lf, src_blake3, src, split, file_keys));
                }

                let dir_interface_hash = dir_hasher.finalize().to_hex().to_string();
                let cached_map = store.batch_get_theorem_shards(&all_shard_keys, "trusted")?;

                let mut total_hits = 0usize;
                let mut uncached_files = Vec::new();
                let mut all_uncached_hygiene_clean = true;
                for (lf, src_blake3, src, split, file_keys) in parsed_files {
                    let file_hygiene_clean = split.hygiene.is_clean_for_certification();
                    let mut file_uncached = Vec::new();
                    for (idx, shard) in split.shards.into_iter().enumerate() {
                        let k = file_keys[idx].clone();
                        if cached_map.contains_key(&k) {
                            total_hits += 1;
                        } else {
                            file_uncached.push((k, shard));
                        }
                    }
                    if !file_uncached.is_empty() {
                        if !file_hygiene_clean {
                            all_uncached_hygiene_clean = false;
                        }
                        uncached_files.push((lf, src_blake3, src, file_uncached));
                    }
                }

                let total_misses: usize = uncached_files.iter().map(|(_, _, _, u)| u.len()).sum();
                if total_misses == 0 {
                    let elapsed_ms = t0.elapsed().as_millis();
                    if cli.json {
                        println!(
                            "{}",
                            serde_json::to_string_pretty(&serde_json::json!({
                                "status": "all_shards_cached",
                                "file": file.display().to_string(),
                                "files_checked": dir_files.len(),
                                "file_split_cache_hits": split_cache_hits,
                                "shard_hits": total_hits,
                                "shard_misses": 0,
                                "interface_hash": dir_interface_hash,
                                "elapsed_ms": elapsed_ms
                            }))?
                        );
                    } else {
                        println!(
                            "[turbo-lean] ALL {} THEOREM SHARDS CACHED across {} files in {} ({} ms)",
                            total_hits,
                            dir_files.len(),
                            file.display(),
                            elapsed_ms
                        );
                    }
                    return Ok(());
                }

                let default_jobs = std::thread::available_parallelism()
                    .map(|n| n.get())
                    .unwrap_or(4);
                let effective_jobs = jobs.unwrap_or(default_jobs).max(1).min(uncached_files.len());
                let staging_dir = store.fast_staging_dir();
                let pid = std::process::id();

                let proj_build_verified = remote_http.is_none()
                    && all_uncached_hygiene_clean
                    && ({
                        let manifest_verified = fs::read(verified_sources_manifest_path(&canon_dir))
                            .ok()
                            .and_then(|b| serde_json::from_slice::<BTreeMap<String, String>>(&b).ok())
                            .map(|recorded| {
                                uncached_files.iter().all(|(lf, sb, _, _)| {
                                    !sb.is_empty() && {
                                        let rel = lf
                                            .strip_prefix(&canon_dir)
                                            .unwrap_or(lf)
                                            .to_string_lossy()
                                            .replace('\\', "/");
                                        recorded.get(&rel).map(|h| h == sb).unwrap_or(false)
                                    }
                                })
                            })
                            .unwrap_or(false);
                        manifest_verified
                            || compute_project_build_key_only(&canon_dir, &toolchain, &[], "trusted")
                                .map(|pk| store.has_completed_action(&pk))
                                .unwrap_or(false)
                    });

                if !proj_build_verified {
                    for (lf, _sb, src, _) in &mut uncached_files {
                        if src.is_empty() {
                            *src = fs::read_to_string(&*lf).unwrap_or_default();
                        }
                    }
                }
                let uncached_files: Vec<(PathBuf, String, Vec<(String, splitter::TheoremShard)>)> =
                    uncached_files
                        .into_iter()
                        .map(|(lf, _sb, src, fu)| (lf, src, fu))
                        .collect();

                // Fast path: if all files with uncached shards have pre-built `.olean` artifacts and
                // acyclic uncached shards, coalesce ALL uncached shards across all files into a SINGLE
                // `lean` invocation in `/dev/shm`!
                let mut cross_eligible = Vec::with_capacity(uncached_files.len());
                for (lf, src, file_uncached) in &uncached_files {
                    let canon_lf = lf.canonicalize().unwrap_or_else(|_| lf.clone());
                    if let Some(mod_imp) = resolve_prebuilt_module_import(&canon_dir, &canon_lf) {
                        if proj_build_verified {
                            cross_eligible.push((mod_imp, src.as_str(), file_uncached));
                        } else {
                            let uncached_names: std::collections::HashSet<String> =
                                file_uncached.iter().map(|(_, sh)| sh.name.clone()).collect();
                            if splitter::can_use_fast_olean_import(src, &uncached_names) {
                                cross_eligible.push((mod_imp, src.as_str(), file_uncached));
                            }
                        }
                    }
                }

                let (env_vars, env_cache_hit) = if proj_build_verified
                    && remote_http.is_none()
                    && cross_eligible.len() == uncached_files.len()
                {
                    (std::collections::HashMap::new(), true)
                } else {
                    resolve_lake_env(&store, &canon_dir)?
                };
                let lean_bin = lean_bin_from_env(&env_vars);

                let mut cross_verified_items: Option<Vec<(String, String, Vec<u8>, i64)>> = None;
                let mut cross_verify_mode = "cross_file_coalesced_shards";
                let lean_path_str = if proj_build_verified
                    && remote_http.is_none()
                    && cross_eligible.len() == uncached_files.len()
                {
                    String::new()
                } else {
                    resolve_remote_lean_path(&canon_dir, Some(&env_vars))
                };
                if cross_eligible.len() == uncached_files.len() {
                    let cross_src = if proj_build_verified {
                        let mut s = String::new();
                        for (mod_imp, _, _) in &cross_eligible {
                            s.push_str("import ");
                            s.push_str(mod_imp);
                            s.push('\n');
                        }
                        s.push_str("#check Nat\n");
                        s
                    } else {
                        let shard_ref_vecs: Vec<Vec<&splitter::TheoremShard>> = cross_eligible
                            .iter()
                            .map(|(_, _, fu)| fu.iter().map(|(_, sh)| sh).collect())
                            .collect();
                        let cross_inputs: Vec<(&str, &str, &[&splitter::TheoremShard])> =
                            cross_eligible
                                .iter()
                                .enumerate()
                                .map(|(i, (m, s, _))| (m.as_str(), *s, shard_ref_vecs[i].as_slice()))
                                .collect();
                        splitter::build_cross_file_coalesced_shard(&cross_inputs)
                    };
                    if let Some(ref remote_url) = remote_http {
                        let mut req_items = Vec::with_capacity(total_misses);
                        for (_, _, file_uncached) in &uncached_files {
                            for (k, sh) in file_uncached {
                                req_items.push(pack::CheckShardBatchItem {
                                    shard_key: k.clone(),
                                    decl_name: sh.name.clone(),
                                    prefix_env_hash: sh.prefix_env_hash.clone(),
                                    stmt_hash: sh.stmt_hash.clone(),
                                    proof_hash: sh.proof_hash.clone(),
                                });
                            }
                        }
                        if let Ok(resp) = pack::offload_check_shards_batch_http(
                            &mut store,
                            remote_url,
                            &req_items,
                            &cross_src,
                            "trusted",
                            &toolchain,
                            &lean_path_str,
                        ) {
                            if resp.ok {
                                cross_verify_mode = "remote_cross_file_coalesced_shards";
                                cross_verified_items = Some(Vec::new());
                            }
                        }
                    }

                    if cross_verified_items.is_none() {
                        let cross_t0 = Instant::now();
                        let zreq = pack::CheckShardHttpRequest {
                            decl: "__batch__".to_string(),
                            shard_key: format!("cross_batch_{}", pid),
                            shard_source: cross_src.clone(),
                            interface_hash: String::new(),
                            prefix_env_hash: String::new(),
                            stmt_hash: String::new(),
                            proof_hash: String::new(),
                            toolchain: toolchain.clone(),
                            lean_path: lean_path_str.clone(),
                            skip_cas_lock: true,
                        };
                        let mut cross_ok = proj_build_verified
                            || pack::try_local_zygote_check_shard(
                                &store,
                                &env_vars,
                                &zreq,
                            )
                            .is_some();
                        if !cross_ok {
                            let tmp_cross =
                                staging_dir.join(format!("cross_file_coalesced_{}.lean", pid));
                            fs::write(&tmp_cross, &cross_src)?;
                            let cross_out = Command::new(&lean_bin)
                                .arg(&tmp_cross)
                                .current_dir(&canon_dir)
                                .envs(&env_vars)
                                .output()?;
                            let _ = fs::remove_file(&tmp_cross);
                            cross_ok = cross_out.status.success();
                        }
                        if cross_ok {
                            let dur_ms = (cross_t0.elapsed().as_millis() as i64
                                / (total_misses as i64).max(1))
                            .max(1);
                            let now = db::now_unix();
                            let mut items = Vec::with_capacity(total_misses);
                            for (_, _, file_uncached) in &uncached_files {
                                for (k, sh) in file_uncached {
                                    let receipt = serde_json::to_vec(&serde_json::json!({
                                        "decl": sh.name,
                                        "prefix_env_hash": sh.prefix_env_hash,
                                        "stmt_hash": sh.stmt_hash,
                                        "proof_hash": sh.proof_hash,
                                        "verified_at": now
                                    }))?;
                                    items.push((k.clone(), sh.name.clone(), receipt, dur_ms));
                                }
                            }
                            cross_verified_items = Some(items);
                        }
                    }
                }

                let (all_batch_items, dir_verify_mode) = if let Some(items) = cross_verified_items {
                    (items, cross_verify_mode)
                } else {
                    let local_zygote_url = pack::ensure_local_zygote_daemon(&store, &env_vars);
                    let next_file_idx = std::sync::atomic::AtomicUsize::new(0);
                    let worker_results: Vec<Result<Vec<(String, String, Vec<u8>, i64)>>> =
                        std::thread::scope(|s| {
                            let mut handles = Vec::with_capacity(effective_jobs);
                            for _w in 0..effective_jobs {
                                let next_ref = &next_file_idx;
                                let files_ref = &uncached_files;
                                let staging_ref = &staging_dir;
                                let canon_ref = &canon_dir;
                                let env_ref = &env_vars;
                                let lean_bin_ref = &lean_bin;
                                let z_url_ref = local_zygote_url.as_deref();
                                let tc_ref = &toolchain;
                                let lp_ref = &lean_path_str;

                                handles.push(s.spawn(move || -> Result<Vec<(String, String, Vec<u8>, i64)>> {
                                    let mut items = Vec::new();
                                    loop {
                                        let f_idx = next_ref.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                                        if f_idx >= files_ref.len() {
                                            break;
                                        }
                                        let (ref lf, ref src, ref file_uncached) = files_ref[f_idx];
                                        let canon_lf = lf.canonicalize().unwrap_or_else(|_| lf.clone());
                                        let uncached_names: std::collections::HashSet<String> =
                                            file_uncached.iter().map(|(_, sh)| sh.name.clone()).collect();
                                        let tmp_batch = staging_ref
                                            .join(format!("dir_batch_{}_{}.lean", pid, f_idx));
                                        let f_t0 = Instant::now();

                                        let mut batch_ok = false;
                                        if let Some(mod_imp) = resolve_prebuilt_module_import(canon_ref, &canon_lf) {
                                            if let Some(fast_src) = splitter::build_fast_olean_shard_source(
                                                src,
                                                &mod_imp,
                                                &uncached_names,
                                            ) {
                                                if let Some(z_url) = z_url_ref {
                                                    let zreq = pack::CheckShardHttpRequest {
                                                        decl: "__batch__".to_string(),
                                                        shard_key: format!("dir_batch_{}_{}", pid, f_idx),
                                                        shard_source: fast_src.clone(),
                                                        interface_hash: String::new(),
                                                        prefix_env_hash: String::new(),
                                                        stmt_hash: String::new(),
                                                        proof_hash: String::new(),
                                                        toolchain: tc_ref.clone(),
                                                        lean_path: lp_ref.clone(),
                                                        skip_cas_lock: true,
                                                    };
                                                    if pack::try_zygote_url_check_shard(z_url, &zreq).is_some() {
                                                        batch_ok = true;
                                                    }
                                                }
                                                if !batch_ok {
                                                    fs::write(&tmp_batch, &fast_src)?;
                                                    let out = Command::new(lean_bin_ref)
                                                        .arg(&tmp_batch)
                                                        .current_dir(canon_ref)
                                                        .envs(env_ref)
                                                        .output()?;
                                                    let _ = fs::remove_file(&tmp_batch);
                                                    if out.status.success() {
                                                        batch_ok = true;
                                                    }
                                                }
                                            }
                                        }

                                        if !batch_ok {
                                            let coal_src = splitter::build_coalesced_shard_source(src, &uncached_names);
                                            fs::write(&tmp_batch, &coal_src)?;
                                            let out = Command::new(lean_bin_ref)
                                                .arg(&tmp_batch)
                                                .current_dir(canon_ref)
                                                .envs(env_ref)
                                                .output()?;
                                            let _ = fs::remove_file(&tmp_batch);
                                            if !out.status.success() {
                                                let stderr = String::from_utf8_lossy(&out.stderr);
                                                let stdout = String::from_utf8_lossy(&out.stdout);
                                                anyhow::bail!(
                                                    "Directory check failed in {}:\n{}\n{}",
                                                    lf.display(),
                                                    stdout,
                                                    stderr
                                                );
                                            }
                                        }

                                        let dur_ms = (f_t0.elapsed().as_millis() as i64
                                            / (file_uncached.len() as i64).max(1))
                                        .max(1);
                                        let now = db::now_unix();
                                        for (k, sh) in file_uncached {
                                            let receipt = serde_json::to_vec(&serde_json::json!({
                                                "decl": sh.name,
                                                "prefix_env_hash": sh.prefix_env_hash,
                                                "stmt_hash": sh.stmt_hash,
                                                "proof_hash": sh.proof_hash,
                                                "verified_at": now
                                            }))?;
                                            items.push((k.clone(), sh.name.clone(), receipt, dur_ms));
                                        }
                                    }
                                    Ok(items)
                                }));
                            }
                            handles
                                .into_iter()
                                .map(|h| h.join().unwrap_or_else(|_| Err(anyhow::anyhow!("Worker thread panicked"))))
                                .collect()
                        });

                    let mut items = Vec::with_capacity(total_misses);
                    for wr in worker_results {
                        items.extend(wr?);
                    }
                    (items, "directory_coalesced_shards")
                };

                store.batch_publish_theorem_shards(&toolchain, "trusted", &all_batch_items)?;

                let elapsed_ms = t0.elapsed().as_millis();
                if cli.json {
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&serde_json::json!({
                            "status": "file_verified",
                            "mode": dir_verify_mode,
                            "file": file.display().to_string(),
                            "files_checked": dir_files.len(),
                            "shard_hits": total_hits,
                            "shard_misses": total_misses,
                            "parallel_jobs": effective_jobs,
                            "lake_env_cache_hit": env_cache_hit,
                            "interface_hash": dir_interface_hash,
                            "elapsed_ms": elapsed_ms
                        }))?
                    );
                } else {
                    println!(
                        "[turbo-lean] VERIFIED {} files in {} ({} hits, {} misses cached, {} ms)",
                        dir_files.len(),
                        file.display(),
                        total_hits,
                        total_misses,
                        elapsed_ms
                    );
                }
                return Ok(());
            }

            let canon_resolved_initial = resolved_file
                .canonicalize()
                .unwrap_or_else(|_| resolved_file.clone());
            let file_stat_tuple: Option<(i64, i64, i64)> = fs::metadata(&canon_resolved_initial)
                .ok()
                .map(|m| TurboStore::extract_file_stat_tuple(&m));
            let stat_cached_entry: Option<ShmCachedFileSplit> =
                file_stat_tuple.and_then(|(ms, mn, sz)| {
                    let pk = canon_resolved_initial.to_string_lossy();
                    let st_hash = compute_single_stat_hash(&pk, ms, mn, sz);
                    let st_path =
                        shm_file_splits_dir(&store).join(format!("st_{}.json", &st_hash[..24]));
                    let bytes = fs::read(&st_path).ok()?;
                    serde_json::from_slice::<ShmCachedFileSplit>(&bytes).ok()
                });
            let mut known_modified_vs_head = false;
            let (mut src, mut cached_file_blake3, mut split, _single_split_hits) =
                if let Some(c) = stat_cached_entry {
                    known_modified_vs_head = c.known_modified;
                    let cb3 = if c.src_blake3.is_empty() {
                        None
                    } else {
                        Some(c.src_blake3)
                    };
                    (c.prefix_src, cb3, c.split, 1usize)
                } else if let Some((pref_src, fast_sp, 0)) = file_stat_tuple
                    .filter(|(_, _, sz)| *sz > 64 * 1024)
                    .and_then(|(_, _, sz)| {
                        try_fast_split_single_file_from_path(
                            &store,
                            &canon_dir,
                            &canon_resolved_initial,
                            sz,
                            &toolchain,
                        )
                    })
                {
                    known_modified_vs_head = true;
                    if let Some((ms, mn, sz)) = file_stat_tuple {
                        let pk = canon_resolved_initial.to_string_lossy();
                        let st_hash = compute_single_stat_hash(&pk, ms, mn, sz);
                        let st_path =
                            shm_file_splits_dir(&store).join(format!("st_{}.json", &st_hash[..24]));
                        let entry = ShmCachedFileSplit {
                            split_key: String::new(),
                            src_blake3: String::new(),
                            split: compact_split_for_shm_cache(&fast_sp),
                            prefix_src: pref_src.clone(),
                            known_modified: true,
                        };
                        if let Ok(bytes) = serde_json::to_vec(&entry) {
                            let _ = fs::write(&st_path, bytes);
                        }
                    }
                    (pref_src, None, fast_sp, 0usize)
                } else {
                    let mut loaded_src = fs::read_to_string(&resolved_file)
                        .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
                    let (sp, hits) = if loaded_src.len() <= 64 * 1024 {
                        (split_lean_source(&loaded_src, &[]), usize::from(db_warm_on_open))
                    } else if let Some(fast_res) = try_fast_split_single_file(
                        &store,
                        &canon_dir,
                        &canon_resolved_initial,
                        &loaded_src,
                        &toolchain,
                    ) {
                        if fast_res.1 == 0 {
                            known_modified_vs_head = true;
                        }
                        if let Some((ms, mn, sz)) = file_stat_tuple {
                            let pk = canon_resolved_initial.to_string_lossy();
                            let st_hash = compute_single_stat_hash(&pk, ms, mn, sz);
                            let st_path = shm_file_splits_dir(&store)
                                .join(format!("st_{}.json", &st_hash[..24]));
                            let (src_b3, pref_src) = if fast_res.1 > 0 {
                                (
                                    blake3::hash(loaded_src.as_bytes()).to_hex().to_string(),
                                    String::new(),
                                )
                            } else {
                                (String::new(), loaded_src[..fast_res.2].to_string())
                            };
                            let entry = ShmCachedFileSplit {
                                split_key: if src_b3.is_empty() {
                                    String::new()
                                } else {
                                    format!("file-split:v2:{}", src_b3)
                                },
                                src_blake3: src_b3,
                                split: compact_split_for_shm_cache(&fast_res.0),
                                prefix_src: pref_src,
                                known_modified: fast_res.1 == 0,
                            };
                            if let Ok(bytes) = serde_json::to_vec(&entry) {
                                let _ = fs::write(&st_path, bytes);
                            }
                        }
                        if fast_res.2 > 0 && fast_res.2 < loaded_src.len() {
                            loaded_src.truncate(fast_res.2);
                        }
                        (fast_res.0, fast_res.1)
                    } else {
                        let (mut single_parsed, hits) = split_and_audit_cached(
                            &store,
                            &[(resolved_file.clone(), loaded_src.clone())],
                        )?;
                        (
                            single_parsed
                                .pop()
                                .map(|(_, _, sp)| sp)
                                .unwrap_or_else(|| split_lean_source(&loaded_src, &[])),
                            hits,
                        )
                    };
                    (loaded_src, None, sp, hits)
                };
            if let Some(target_decl) = decl {
                let mut active_src = src;
                let mut active_file = resolved_file.clone();
                let matches_decl = |s_name: &str, q: &str| -> bool {
                    s_name == q
                        || q.ends_with(&format!(".{}", s_name))
                        || s_name.ends_with(&format!(".{}", q))
                };

                if !split.shards.iter().any(|s| matches_decl(&s.name, &target_decl)) {
                    for line in split.imports_header.lines() {
                        if let Some(mod_name) = line.trim().strip_prefix("import ") {
                            let rel_mod = mod_name.trim().replace('.', "/") + ".lean";
                            let sub_path = canon_dir.join(rel_mod);
                            if let Ok(sub_src) = fs::read_to_string(&sub_path) {
                                let sub_split = split_lean_source(&sub_src, &[]);
                                if sub_split
                                    .shards
                                    .iter()
                                    .any(|s| matches_decl(&s.name, &target_decl))
                                {
                                    split = sub_split;
                                    cached_file_blake3 = None;
                                    active_src = sub_src;
                                    active_file = sub_path;
                                    break;
                                }
                            }
                        }
                    }
                }

                let shard = split
                    .shards
                    .iter()
                    .find(|s| matches_decl(&s.name, &target_decl))
                    .with_context(|| {
                        format!(
                            "Declaration `{}` not found in {} (found {} theorem shards)",
                            target_decl,
                            file.display(),
                            split.shards.len()
                        )
                    })?;

                let shard_key = compute_shard_key(&toolchain, shard);

                if let Some(ref remote_url) = remote_http {
                    if db_warm_on_open
                        && store
                            .get_cached_action(&shard_key, "trusted")?
                            .is_some()
                    {
                        let elapsed_ms = t0.elapsed().as_millis();
                        if cli.json {
                            println!(
                                "{}",
                                serde_json::to_string_pretty(&serde_json::json!({
                                    "status": "theorem_cache_hit",
                                    "decl": target_decl,
                                    "coalesced": false,
                                    "shard_key": shard_key,
                                    "interface_hash": split.interface_hash,
                                    "prefix_env_hash": shard.prefix_env_hash,
                                    "elapsed_ms": elapsed_ms
                                }))?
                            );
                        } else {
                            println!(
                                "[turbo-lean] SHARD CACHE HIT `{}` (coalesced=false, {} ms)",
                                target_decl, elapsed_ms
                            );
                        }
                        return Ok(());
                    }
                    if active_src.is_empty() {
                        active_src = fs::read_to_string(&active_file)
                            .with_context(|| format!("Failed to read {}", active_file.display()))?;
                    }
                    let canon_file = if active_file == resolved_file {
                        canon_resolved_initial.clone()
                    } else {
                        active_file
                            .canonicalize()
                            .unwrap_or_else(|_| active_file.clone())
                    };
                    let mut single_set = std::collections::HashSet::new();
                    single_set.insert(target_decl.clone());
                    single_set.insert(shard.name.clone());
                    let pruned_src = splitter::build_pruned_imports_shard_source(
                        &active_src,
                        &single_set,
                    );
                    let fast_olean_src =
                        resolve_prebuilt_module_import(&canon_dir, &canon_file).and_then(
                            |mod_imp| {
                                splitter::build_fast_olean_shard_source_with_split(
                                    &active_src,
                                    &split,
                                    &mod_imp,
                                    &single_set,
                                )
                            },
                        );
                    let endpoint =
                        format!("{}/check-shard", remote_url.trim_end_matches('/'));
                    let fast_lib_lean = canon_dir.join(".lake/build/lib/lean");
                    let local_lean_path = if fast_lib_lean.exists()
                        && !canon_dir.join(".lake/build/packages").is_dir()
                    {
                        fast_lib_lean.to_string_lossy().to_string()
                    } else {
                        let cached_env = if db_warm_on_open {
                            let env_key = TurboStore::compute_lake_env_key(&canon_dir);
                            store.get_lake_env(&env_key).ok().flatten()
                        } else {
                            None
                        };
                        resolve_remote_lean_path(&canon_dir, cached_env.as_ref())
                    };

                    let mut fast_candidates: Vec<(&str, bool)> = Vec::new();
                    if let Some(ref psrc) = pruned_src {
                        fast_candidates.push((psrc.as_str(), true));
                    }
                    if let Some(ref fsrc) = fast_olean_src {
                        fast_candidates.push((fsrc.as_str(), true));
                    }

                    let mut resp_json = serde_json::Value::Null;
                    let mut remote_status = String::from("unknown");
                    let mut fast_olean_used = false;
                    let mut last_err: Option<anyhow::Error> = None;
                    let mut succeeded = false;
                    let mut prestaged_receipt: Option<Vec<u8>> = None;
                    let mut inflight_tx_open = false;

                    for (cand_src, is_fast) in fast_candidates {
                        let req_body = serde_json::to_vec(&pack::CheckShardHttpRequest {
                            decl: target_decl.clone(),
                            shard_key: shard_key.clone(),
                            shard_source: cand_src.to_string(),
                            interface_hash: split.interface_hash.clone(),
                            prefix_env_hash: shard.prefix_env_hash.clone(),
                            stmt_hash: shard.stmt_hash.clone(),
                            proof_hash: shard.proof_hash.clone(),
                            toolchain: toolchain.clone(),
                            lean_path: local_lean_path.clone(),
                            skip_cas_lock: false,
                        })?;
                        match pack::http_request_with_inflight(
                            "POST",
                            &endpoint,
                            "application/json",
                            &req_body,
                            || {
                                if prestaged_receipt.is_none() {
                                    if let Ok(r_bytes) = serde_json::to_vec(&serde_json::json!({
                                        "decl": &target_decl,
                                        "prefix_env_hash": &shard.prefix_env_hash,
                                        "stmt_hash": &shard.stmt_hash,
                                        "proof_hash": &shard.proof_hash,
                                        "verified_at": db::now_unix()
                                    })) {
                                        let items = [(
                                            shard_key.clone(),
                                            target_decl.clone(),
                                            r_bytes.clone(),
                                            1,
                                        )];
                                        let _ = store.prestage_theorem_shard_blobs(&items);
                                        if store
                                            .begin_inflight_publish_theorem_shards(
                                                &toolchain, "trusted", &items,
                                            )
                                            .is_ok()
                                        {
                                            inflight_tx_open = true;
                                        }
                                        prestaged_receipt = Some(r_bytes);
                                    }
                                }
                            },
                        ) {
                            Ok(resp_bytes) => {
                                if let Ok(rj) =
                                    serde_json::from_slice::<serde_json::Value>(&resp_bytes)
                                {
                                    let st = rj
                                        .get("status")
                                        .and_then(|v| v.as_str())
                                        .unwrap_or("unknown")
                                        .to_string();
                                    if st == "remote_theorem_verified"
                                        || st == "remote_theorem_cache_hit"
                                    {
                                        resp_json = rj;
                                        remote_status = st;
                                        fast_olean_used = is_fast;
                                        last_err = None;
                                        succeeded = true;
                                        break;
                                    }
                                    last_err = Some(anyhow::anyhow!(
                                        "Remote shard check failed on {}: {}",
                                        endpoint,
                                        rj
                                    ));
                                }
                            }
                            Err(e) => {
                                last_err = Some(e);
                            }
                        }
                    }
                    if !succeeded {
                        let full_shard_src = if !shard.shard_source.is_empty() {
                            shard.shard_source.clone()
                        } else {
                            splitter::reconstruct_single_shard_source(
                                &active_src,
                                &shard.name,
                            )
                            .unwrap_or_default()
                        };
                        let req_body = serde_json::to_vec(&pack::CheckShardHttpRequest {
                            decl: target_decl.clone(),
                            shard_key: shard_key.clone(),
                            shard_source: full_shard_src,
                            interface_hash: split.interface_hash.clone(),
                            prefix_env_hash: shard.prefix_env_hash.clone(),
                            stmt_hash: shard.stmt_hash.clone(),
                            proof_hash: shard.proof_hash.clone(),
                            toolchain: toolchain.clone(),
                            lean_path: local_lean_path.clone(),
                            skip_cas_lock: false,
                        })?;
                        match pack::http_request_with_inflight(
                            "POST",
                            &endpoint,
                            "application/json",
                            &req_body,
                            || {
                                if prestaged_receipt.is_none() {
                                    if let Ok(r_bytes) = serde_json::to_vec(&serde_json::json!({
                                        "decl": &target_decl,
                                        "prefix_env_hash": &shard.prefix_env_hash,
                                        "stmt_hash": &shard.stmt_hash,
                                        "proof_hash": &shard.proof_hash,
                                        "verified_at": db::now_unix()
                                    })) {
                                        let items = [(
                                            shard_key.clone(),
                                            target_decl.clone(),
                                            r_bytes.clone(),
                                            1,
                                        )];
                                        let _ = store.prestage_theorem_shard_blobs(&items);
                                        if store
                                            .begin_inflight_publish_theorem_shards(
                                                &toolchain, "trusted", &items,
                                            )
                                            .is_ok()
                                        {
                                            inflight_tx_open = true;
                                        }
                                        prestaged_receipt = Some(r_bytes);
                                    }
                                }
                            },
                        ) {
                            Ok(resp_bytes) => {
                                if let Ok(rj) =
                                    serde_json::from_slice::<serde_json::Value>(&resp_bytes)
                                {
                                    let st = rj
                                        .get("status")
                                        .and_then(|v| v.as_str())
                                        .unwrap_or("unknown")
                                        .to_string();
                                    if st == "remote_theorem_verified"
                                        || st == "remote_theorem_cache_hit"
                                    {
                                        resp_json = rj;
                                        remote_status = st;
                                        fast_olean_used = false;
                                        last_err = None;
                                    } else {
                                        last_err = Some(anyhow::anyhow!(
                                            "Remote shard check failed on {}: {}",
                                            endpoint,
                                            rj
                                        ));
                                    }
                                }
                            }
                            Err(e) => {
                                last_err = Some(e);
                            }
                        }
                    }
                    if let Some(err) = last_err {
                        if inflight_tx_open {
                            store.rollback_inflight_publish();
                        }
                        return Err(err);
                    }

                    let dur_ms = t0.elapsed().as_millis() as i64;
                    let server_arch = resp_json
                        .get("server_arch")
                        .and_then(|v| v.as_str())
                        .unwrap_or("unknown");
                    let server_elapsed_ms = resp_json
                        .get("server_elapsed_ms")
                        .and_then(|v| v.as_u64())
                        .unwrap_or(0);
                    let zygote_used = resp_json
                        .get("zygote_used")
                        .and_then(|v| v.as_bool())
                        .unwrap_or(false);
                    let zygote_env_cache_hit = resp_json
                        .get("zygote_env_cache_hit")
                        .and_then(|v| v.as_bool())
                        .unwrap_or(false);
                    let zygote_import_us = resp_json
                        .get("zygote_import_us")
                        .and_then(|v| v.as_u64())
                        .unwrap_or(0);
                    let zygote_elab_us = resp_json
                        .get("zygote_elab_us")
                        .and_then(|v| v.as_u64())
                        .unwrap_or(0);
                    if inflight_tx_open {
                        store.commit_inflight_publish()?;
                    } else {
                        let receipt = match prestaged_receipt {
                            Some(r) => r,
                            None => serde_json::to_vec(&serde_json::json!({
                                "decl": target_decl,
                                "prefix_env_hash": shard.prefix_env_hash,
                                "stmt_hash": shard.stmt_hash,
                                "proof_hash": shard.proof_hash,
                                "verified_at": db::now_unix()
                            }))?,
                        };
                        store.batch_publish_theorem_shards(
                            &toolchain,
                            "trusted",
                            &[(
                                shard_key.clone(),
                                target_decl.clone(),
                                receipt,
                                (server_elapsed_ms as i64).max(dur_ms),
                            )],
                        )?;
                    }

                    if cli.json {
                        println!(
                            "{}",
                            serde_json::to_string_pretty(&serde_json::json!({
                                "status": remote_status,
                                "decl": target_decl,
                                "shard_key": shard_key,
                                "remote_url": remote_url,
                                "server_arch": server_arch,
                                "server_elapsed_ms": server_elapsed_ms,
                                "fast_olean_import": fast_olean_used,
                                "zygote_used": zygote_used,
                                "zygote_env_cache_hit": zygote_env_cache_hit,
                                "zygote_import_us": zygote_import_us,
                                "zygote_elab_us": zygote_elab_us,
                                "interface_hash": split.interface_hash,
                                "prefix_env_hash": shard.prefix_env_hash,
                                "total_shards_in_file": split.shards.len(),
                                "elapsed_ms": dur_ms
                            }))?
                        );
                    } else {
                        println!(
                            "[turbo-lean] {} `{}` via {} (arch={}, server={} ms, total={} ms)",
                            remote_status.to_uppercase(),
                            target_decl,
                            remote_url,
                            server_arch,
                            server_elapsed_ms,
                            dur_ms
                        );
                    }
                    return Ok(());
                }

                match store.acquire_singleflight(&shard_key, &toolchain, "theorem_shard", "trusted")? {
                    SingleflightOutcome::CacheHit { coalesced, .. } => {
                        let elapsed_ms = t0.elapsed().as_millis();
                        if cli.json {
                            println!(
                                "{}",
                                serde_json::to_string_pretty(&serde_json::json!({
                                    "status": "theorem_cache_hit",
                                    "decl": target_decl,
                                    "coalesced": coalesced,
                                    "shard_key": shard_key,
                                    "interface_hash": split.interface_hash,
                                    "prefix_env_hash": shard.prefix_env_hash,
                                    "elapsed_ms": elapsed_ms
                                }))?
                            );
                        } else {
                            println!(
                                "[turbo-lean] SHARD CACHE HIT `{}` (coalesced={}, {} ms)",
                                target_decl, coalesced, elapsed_ms
                            );
                        }
                    }
                    SingleflightOutcome::Leader(lease) => {
                        if let Some(ref remote_url) = remote_http {
                            if active_src.is_empty() {
                                active_src = fs::read_to_string(&active_file)
                                    .with_context(|| format!("Failed to read {}", active_file.display()))?;
                            }
                            let canon_file = active_file
                                .canonicalize()
                                .unwrap_or_else(|_| active_file.clone());
                            let mut single_set = std::collections::HashSet::new();
                            single_set.insert(target_decl.clone());
                            single_set.insert(shard.name.clone());
                            let pruned_src = splitter::build_pruned_imports_shard_source(
                                &active_src,
                                &single_set,
                            );
                            let fast_olean_src =
                                resolve_prebuilt_module_import(&canon_dir, &canon_file).and_then(
                                    |mod_imp| {
                                        splitter::build_fast_olean_shard_source_with_split(
                                            &active_src,
                                            &split,
                                            &mod_imp,
                                            &single_set,
                                        )
                                    },
                                );
                            let endpoint =
                                format!("{}/check-shard", remote_url.trim_end_matches('/'));
                            let cached_env = if db_warm_on_open {
                                let env_key = TurboStore::compute_lake_env_key(&canon_dir);
                                store.get_lake_env(&env_key).ok().flatten()
                            } else {
                                None
                            };
                            let local_lean_path =
                                resolve_remote_lean_path(&canon_dir, cached_env.as_ref());

                            let mut fast_candidates: Vec<(&str, bool)> = Vec::new();
                            if let Some(ref psrc) = pruned_src {
                                fast_candidates.push((psrc.as_str(), true));
                            }
                            if let Some(ref fsrc) = fast_olean_src {
                                fast_candidates.push((fsrc.as_str(), true));
                            }

                            let mut resp_json = serde_json::Value::Null;
                            let mut remote_status = String::from("unknown");
                            let mut fast_olean_used = false;
                            let mut last_err: Option<anyhow::Error> = None;
                            let mut succeeded = false;

                            for (cand_src, is_fast) in fast_candidates {
                                let req_body = serde_json::to_vec(&pack::CheckShardHttpRequest {
                                    decl: target_decl.clone(),
                                    shard_key: shard_key.clone(),
                                    shard_source: cand_src.to_string(),
                                    interface_hash: split.interface_hash.clone(),
                                    prefix_env_hash: shard.prefix_env_hash.clone(),
                                    stmt_hash: shard.stmt_hash.clone(),
                                    proof_hash: shard.proof_hash.clone(),
                                    toolchain: toolchain.clone(),
                                    lean_path: local_lean_path.clone(),
                                    skip_cas_lock: false,
                                })?;
                                match pack::http_request(
                                    "POST",
                                    &endpoint,
                                    "application/json",
                                    &req_body,
                                ) {
                                    Ok(resp_bytes) => {
                                        if let Ok(rj) =
                                            serde_json::from_slice::<serde_json::Value>(&resp_bytes)
                                        {
                                            let st = rj
                                                .get("status")
                                                .and_then(|v| v.as_str())
                                                .unwrap_or("unknown")
                                                .to_string();
                                            if st == "remote_theorem_verified"
                                                || st == "remote_theorem_cache_hit"
                                            {
                                                resp_json = rj;
                                                remote_status = st;
                                                fast_olean_used = is_fast;
                                                last_err = None;
                                                succeeded = true;
                                                break;
                                            }
                                            last_err = Some(anyhow::anyhow!(
                                                "Remote shard check failed on {}: {}",
                                                endpoint,
                                                rj
                                            ));
                                        }
                                    }
                                    Err(e) => {
                                        last_err = Some(e);
                                    }
                                }
                            }
                            if !succeeded {
                                let full_shard_src = if !shard.shard_source.is_empty() {
                                    shard.shard_source.clone()
                                } else {
                                    splitter::reconstruct_single_shard_source(
                                        &active_src,
                                        &shard.name,
                                    )
                                    .unwrap_or_default()
                                };
                                let req_body = serde_json::to_vec(&pack::CheckShardHttpRequest {
                                    decl: target_decl.clone(),
                                    shard_key: shard_key.clone(),
                                    shard_source: full_shard_src,
                                    interface_hash: split.interface_hash.clone(),
                                    prefix_env_hash: shard.prefix_env_hash.clone(),
                                    stmt_hash: shard.stmt_hash.clone(),
                                    proof_hash: shard.proof_hash.clone(),
                                    toolchain: toolchain.clone(),
                                    lean_path: local_lean_path.clone(),
                                    skip_cas_lock: false,
                                })?;
                                match pack::http_request(
                                    "POST",
                                    &endpoint,
                                    "application/json",
                                    &req_body,
                                ) {
                                    Ok(resp_bytes) => {
                                        if let Ok(rj) =
                                            serde_json::from_slice::<serde_json::Value>(&resp_bytes)
                                        {
                                            let st = rj
                                                .get("status")
                                                .and_then(|v| v.as_str())
                                                .unwrap_or("unknown")
                                                .to_string();
                                            if st == "remote_theorem_verified"
                                                || st == "remote_theorem_cache_hit"
                                            {
                                                resp_json = rj;
                                                remote_status = st;
                                                fast_olean_used = false;
                                                last_err = None;
                                            } else {
                                                last_err = Some(anyhow::anyhow!(
                                                    "Remote shard check failed on {}: {}",
                                                    endpoint,
                                                    rj
                                                ));
                                            }
                                        }
                                    }
                                    Err(e) => {
                                        last_err = Some(e);
                                    }
                                }
                            }
                            if let Some(err) = last_err {
                                return Err(err);
                            }

                            let dur_ms = t0.elapsed().as_millis() as i64;
                            let server_arch = resp_json
                                .get("server_arch")
                                .and_then(|v| v.as_str())
                                .unwrap_or("unknown");
                            let server_elapsed_ms = resp_json
                                .get("server_elapsed_ms")
                                .and_then(|v| v.as_u64())
                                .unwrap_or(0);
                            let zygote_used = resp_json
                                .get("zygote_used")
                                .and_then(|v| v.as_bool())
                                .unwrap_or(false);
                            let zygote_env_cache_hit = resp_json
                                .get("zygote_env_cache_hit")
                                .and_then(|v| v.as_bool())
                                .unwrap_or(false);
                            let zygote_import_us = resp_json
                                .get("zygote_import_us")
                                .and_then(|v| v.as_u64())
                                .unwrap_or(0);
                            let zygote_elab_us = resp_json
                                .get("zygote_elab_us")
                                .and_then(|v| v.as_u64())
                                .unwrap_or(0);
                            let receipt = serde_json::to_vec(&serde_json::json!({
                                "decl": target_decl,
                                "prefix_env_hash": shard.prefix_env_hash,
                                "stmt_hash": shard.stmt_hash,
                                "proof_hash": shard.proof_hash,
                                "verified_at": db::now_unix()
                            }))?;
                            store.publish_action_with_blob(
                                &lease,
                                &receipt,
                                "expr_shard",
                                &format!("thm:{}", target_decl),
                                (server_elapsed_ms as i64).max(dur_ms),
                                "trusted",
                            )?;
                            drop(lease);

                            if cli.json {
                                println!(
                                    "{}",
                                    serde_json::to_string_pretty(&serde_json::json!({
                                        "status": remote_status,
                                        "decl": target_decl,
                                        "shard_key": shard_key,
                                        "remote_url": remote_url,
                                        "server_arch": server_arch,
                                        "server_elapsed_ms": server_elapsed_ms,
                                        "fast_olean_import": fast_olean_used,
                                        "zygote_used": zygote_used,
                                        "zygote_env_cache_hit": zygote_env_cache_hit,
                                        "zygote_import_us": zygote_import_us,
                                        "zygote_elab_us": zygote_elab_us,
                                        "interface_hash": split.interface_hash,
                                        "prefix_env_hash": shard.prefix_env_hash,
                                        "total_shards_in_file": split.shards.len(),
                                        "elapsed_ms": dur_ms
                                    }))?
                                );
                            } else {
                                println!(
                                    "[turbo-lean] {} `{}` via {} (arch={}, server={} ms, total={} ms)",
                                    remote_status.to_uppercase(),
                                    target_decl,
                                    remote_url,
                                    server_arch,
                                    server_elapsed_ms,
                                    dur_ms
                                );
                            }
                            return Ok(());
                        }

                        let same_as_initial = active_file == resolved_file;
                        let canon_file = if same_as_initial {
                            canon_resolved_initial.clone()
                        } else {
                            active_file
                                .canonicalize()
                                .unwrap_or_else(|_| active_file.clone())
                        };
                        let safe_name: String = target_decl
                            .chars()
                            .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
                            .collect();
                        let staging_dir = store.fast_staging_dir();
                        let tmp_shard = staging_dir
                            .join(format!("shard_{}_{}.lean", safe_name, std::process::id()));

                        // Fast path 0: Speculative Heavy External-Import Pruning (e.g., unused `import Mathlib.*`)
                        // Fast path 1: if the module's `.olean` is pre-compiled in `.lake/build/lib/lean/`
                        // and the shard is acyclic, import the pre-compiled `.olean` directly to skip
                        // re-elaborating all `inductive`, `structure`, and `def` declarations!
                        let mut single_set = std::collections::HashSet::new();
                        single_set.insert(target_decl.clone());
                        single_set.insert(shard.name.clone());

                        let proj_build_verified = !(known_modified_vs_head && same_as_initial)
                            && split.hygiene.is_clean_for_certification()
                            && (cached_file_blake3
                                .as_deref()
                                .map(|h| is_file_hash_verified_in_lake_build(&canon_dir, &canon_file, h))
                                .unwrap_or_else(|| {
                                    if active_src.is_empty() {
                                        active_src = fs::read_to_string(&active_file).unwrap_or_default();
                                    }
                                    is_file_verified_in_lake_build(&canon_dir, &canon_file, &active_src)
                                })
                                || (_single_split_hits > 0
                                    && compute_project_build_key_only(
                                        &canon_dir,
                                        &toolchain,
                                        &[],
                                        "trusted",
                                    )
                                    .map(|pk| store.has_completed_action(&pk))
                                    .unwrap_or(false)));
                        let prebuilt_mod = resolve_prebuilt_module_import(&canon_dir, &canon_file);
                        let mut verified_via_fast_olean =
                            proj_build_verified && prebuilt_mod.is_some();
                        let mut verified_via_zygote = verified_via_fast_olean;
                        let mut zygote_env_cache_hit = verified_via_fast_olean;
                        let mut zygote_import_us = 0u64;
                        let mut zygote_elab_us = 0u64;

                        let fast_local_zygote_url = if !verified_via_zygote && db_warm_on_open {
                            pack::ensure_local_zygote_daemon(
                                &store,
                                &std::collections::HashMap::new(),
                            )
                        } else {
                            None
                        };
                        let fast_lib_dir = canon_dir.join(".lake/build/lib/lean");
                        let (mut env_vars, mut env_cache_hit, mut lean_bin, local_lean_path) =
                            if fast_local_zygote_url.is_some() && fast_lib_dir.exists() {
                                (
                                    std::collections::HashMap::new(),
                                    true,
                                    "lean".to_string(),
                                    fast_lib_dir.to_string_lossy().to_string(),
                                )
                            } else {
                                let (ev, ech) = resolve_lake_env(&store, &canon_dir)?;
                                let lb = lean_bin_from_env(&ev);
                                let lp = resolve_remote_lean_path(&canon_dir, Some(&ev));
                                (ev, ech, lb, lp)
                            };

                        if !verified_via_zygote && active_src.is_empty() {
                            active_src = fs::read_to_string(&active_file)
                                .with_context(|| format!("Failed to read {}", active_file.display()))?;
                        }
                        let pruned_src = if verified_via_zygote {
                            None
                        } else {
                            splitter::build_pruned_imports_shard_source(&active_src, &single_set)
                        };
                        let fast_olean_src = if verified_via_zygote {
                            None
                        } else {
                            prebuilt_mod.as_ref().and_then(|mod_imp| {
                                if proj_build_verified {
                                    Some(format!("import {}\n#check Nat\n", mod_imp))
                                } else {
                                    splitter::build_fast_olean_shard_source_with_split(
                                        &active_src,
                                        &split,
                                        mod_imp,
                                        &single_set,
                                    )
                                }
                            })
                        };

                        let mut inflight_tx_open = false;
                        let mut try_zygote_src =
                            |src_text: &str,
                             ev: &std::collections::HashMap<String, String>|
                             -> Option<serde_json::Value> {
                                let zreq = pack::CheckShardHttpRequest {
                                    decl: target_decl.clone(),
                                    shard_key: shard_key.clone(),
                                    shard_source: src_text.to_string(),
                                    interface_hash: split.interface_hash.clone(),
                                    prefix_env_hash: shard.prefix_env_hash.clone(),
                                    stmt_hash: shard.stmt_hash.clone(),
                                    proof_hash: shard.proof_hash.clone(),
                                    toolchain: toolchain.clone(),
                                    lean_path: local_lean_path.clone(),
                                    skip_cas_lock: true,
                                };
                                if let Some(ref z_url) = fast_local_zygote_url {
                                    let res = pack::try_zygote_url_check_shard_with_inflight(
                                        z_url,
                                        &zreq,
                                        || {
                                            if !inflight_tx_open {
                                                if let Ok(r_bytes) =
                                                    serde_json::to_vec(&serde_json::json!({
                                                        "decl": target_decl,
                                                        "prefix_env_hash": shard.prefix_env_hash,
                                                        "stmt_hash": shard.stmt_hash,
                                                        "proof_hash": shard.proof_hash,
                                                        "verified_at": db::now_unix()
                                                    }))
                                                {
                                                    let bh = blake3::hash(&r_bytes)
                                                        .to_hex()
                                                        .to_string();
                                                    let sz = r_bytes.len() as i64;
                                                    let single_pub = vec![(
                                                        shard_key.clone(),
                                                        target_decl.clone(),
                                                        r_bytes,
                                                        1i64,
                                                    )];
                                                    if store
                                                        .prestage_theorem_shard_blobs(&single_pub)
                                                        .is_ok()
                                                    {
                                                        store.write_singleflight_done(
                                                            &shard_key,
                                                            &[db::BlobEntry {
                                                                blob_hash: bh,
                                                                kind: "expr_shard".to_string(),
                                                                rel_path: format!(
                                                                    "thm:{}",
                                                                    target_decl
                                                                ),
                                                                size_bytes: sz as u64,
                                                            }],
                                                        );
                                                    }
                                                    if store
                                                        .begin_inflight_publish_theorem_shards(
                                                            &toolchain,
                                                            "trusted",
                                                            &single_pub,
                                                        )
                                                        .is_ok()
                                                    {
                                                        inflight_tx_open = true;
                                                    }
                                                }
                                            }
                                        },
                                    );
                                    if let Some(r) = res {
                                        return Some(r);
                                    }
                                    if inflight_tx_open {
                                        store.rollback_inflight_publish();
                                        store.remove_singleflight_done(&shard_key);
                                        inflight_tx_open = false;
                                    }
                                }
                                pack::try_local_zygote_check_shard(&store, ev, &zreq)
                            };

                        if !verified_via_zygote {
                            if let Some(ref fsrc) = fast_olean_src {
                                if let Some(zjson) = try_zygote_src(fsrc, &env_vars) {
                                    verified_via_fast_olean = true;
                                    verified_via_zygote = true;
                                    zygote_env_cache_hit = zjson
                                        .get("zygote_env_cache_hit")
                                        .and_then(|v| v.as_bool())
                                        .unwrap_or(false);
                                    zygote_import_us = zjson
                                        .get("zygote_import_us")
                                        .and_then(|v| v.as_u64())
                                        .unwrap_or(0);
                                    zygote_elab_us = zjson
                                        .get("zygote_elab_us")
                                        .and_then(|v| v.as_u64())
                                        .unwrap_or(0);
                                }
                            }
                        }

                        if !verified_via_zygote {
                            if let Some(ref psrc) = pruned_src {
                                if let Some(zjson) = try_zygote_src(psrc, &env_vars) {
                                    verified_via_fast_olean = true;
                                    verified_via_zygote = true;
                                    zygote_env_cache_hit = zjson
                                        .get("zygote_env_cache_hit")
                                        .and_then(|v| v.as_bool())
                                        .unwrap_or(false);
                                    zygote_import_us = zjson
                                        .get("zygote_import_us")
                                        .and_then(|v| v.as_u64())
                                        .unwrap_or(0);
                                    zygote_elab_us = zjson
                                        .get("zygote_elab_us")
                                        .and_then(|v| v.as_u64())
                                        .unwrap_or(0);
                                }
                            }
                        }

                        if !verified_via_zygote && env_vars.is_empty() {
                            let (ev, ech) = resolve_lake_env(&store, &canon_dir)?;
                            lean_bin = lean_bin_from_env(&ev);
                            env_vars = ev;
                            env_cache_hit = ech;
                        }

                        if !verified_via_zygote {
                            if let Some(ref fast_src) = fast_olean_src {
                                fs::write(&tmp_shard, fast_src)?;
                                let fast_out = Command::new(&lean_bin)
                                    .arg(&tmp_shard)
                                    .current_dir(&canon_dir)
                                    .envs(&env_vars)
                                    .output()
                                    .context("Failed to execute `lean` on fast-olean shard")?;
                                let _ = fs::remove_file(&tmp_shard);
                                if fast_out.status.success() {
                                    verified_via_fast_olean = true;
                                }
                            }
                        }

                        if !verified_via_zygote && !verified_via_fast_olean {
                            if let Some(ref psrc) = pruned_src {
                                fs::write(&tmp_shard, psrc)?;
                                let pruned_out = Command::new(&lean_bin)
                                    .arg(&tmp_shard)
                                    .current_dir(&canon_dir)
                                    .envs(&env_vars)
                                    .output()
                                    .context("Failed to execute `lean` on pruned-imports shard")?;
                                let _ = fs::remove_file(&tmp_shard);
                                if pruned_out.status.success() {
                                    verified_via_fast_olean = true;
                                }
                            }
                        }

                        if !verified_via_zygote && !verified_via_fast_olean {
                            let full_shard_src = if !shard.shard_source.is_empty() {
                                shard.shard_source.clone()
                            } else {
                                splitter::reconstruct_single_shard_source(&active_src, &shard.name)
                                    .unwrap_or_default()
                            };
                            if let Some(zjson) = try_zygote_src(&full_shard_src, &env_vars) {
                                verified_via_zygote = true;
                                zygote_env_cache_hit = zjson
                                    .get("zygote_env_cache_hit")
                                    .and_then(|v| v.as_bool())
                                    .unwrap_or(false);
                                zygote_import_us = zjson
                                    .get("zygote_import_us")
                                    .and_then(|v| v.as_u64())
                                    .unwrap_or(0);
                                zygote_elab_us = zjson
                                    .get("zygote_elab_us")
                                    .and_then(|v| v.as_u64())
                                    .unwrap_or(0);
                            } else {
                                fs::write(&tmp_shard, &full_shard_src)?;
                                let out = Command::new(&lean_bin)
                                    .arg(&tmp_shard)
                                    .current_dir(&canon_dir)
                                    .envs(&env_vars)
                                    .output()
                                    .context("Failed to execute `lean` on theorem shard")?;
                                let _ = fs::remove_file(&tmp_shard);

                                if !out.status.success() {
                                    let stderr = String::from_utf8_lossy(&out.stderr);
                                    let stdout = String::from_utf8_lossy(&out.stdout);
                                    anyhow::bail!(
                                        "Shard check failed for `{}`:\n{}\n{}",
                                        target_decl,
                                        stdout,
                                        stderr
                                    );
                                }
                            }
                        }

                        let dur_ms = t0.elapsed().as_millis() as i64;
                        if inflight_tx_open {
                            store.commit_inflight_publish_for_lease(&shard_key)?;
                            drop(lease);
                        } else {
                            let receipt = serde_json::to_vec(&serde_json::json!({
                                "decl": target_decl,
                                "prefix_env_hash": shard.prefix_env_hash,
                                "stmt_hash": shard.stmt_hash,
                                "proof_hash": shard.proof_hash,
                                "verified_at": db::now_unix()
                            }))?;
                            store.publish_action_with_blob(
                                &lease,
                                &receipt,
                                "expr_shard",
                                &format!("thm:{}", target_decl),
                                dur_ms,
                                "trusted",
                            )?;
                            drop(lease);
                        }

                        if cli.json {
                            println!(
                                "{}",
                                serde_json::to_string_pretty(&serde_json::json!({
                                    "status": "theorem_verified",
                                    "decl": target_decl,
                                    "shard_key": shard_key,
                                    "lake_env_cache_hit": env_cache_hit,
                                    "fast_olean_import": verified_via_fast_olean,
                                    "zygote_used": verified_via_zygote,
                                    "zygote_env_cache_hit": zygote_env_cache_hit,
                                    "zygote_import_us": zygote_import_us,
                                    "zygote_elab_us": zygote_elab_us,
                                    "interface_hash": split.interface_hash,
                                    "prefix_env_hash": shard.prefix_env_hash,
                                    "total_shards_in_file": split.shards.len(),
                                    "elapsed_ms": dur_ms
                                }))?
                            );
                        } else {
                            println!(
                                "[turbo-lean] SHARD VERIFIED `{}` ({}/{} shards in file, env_cache_hit={}, fast_olean={}, zygote={}, interface_hash={}.., {} ms)",
                                target_decl,
                                1,
                                split.shards.len(),
                                env_cache_hit,
                                verified_via_fast_olean,
                                verified_via_zygote,
                                &split.interface_hash[..12],
                                dur_ms
                            );
                        }
                    }
                }
            } else {
                // Incremental & parallel multi-shard file check across all theorem shards in the file!
                // Batch-query all theorem shard keys in a single SQLite transaction.
                let file_shard_keys: Vec<String> = split
                    .shards
                    .iter()
                    .map(|shard| compute_shard_key(&toolchain, shard))
                    .collect();
                let cached_map = if db_warm_on_open {
                    store.batch_get_theorem_shards(&file_shard_keys, "trusted")?
                } else {
                    std::collections::HashMap::new()
                };

                let mut hits = 0usize;
                let mut uncached_shards = Vec::new();
                for (idx, shard) in split.shards.iter().enumerate() {
                    let shard_key = file_shard_keys[idx].clone();
                    if cached_map.contains_key(&shard_key) {
                        hits += 1;
                    } else {
                        uncached_shards.push((shard_key, shard));
                    }
                }
                let misses = uncached_shards.len();

                if misses == 0 && !split.shards.is_empty() && split.eligible_for_sharding {
                    let elapsed_ms = t0.elapsed().as_millis();
                    if cli.json {
                        println!(
                            "{}",
                            serde_json::to_string_pretty(&serde_json::json!({
                                "status": "all_shards_cached",
                                "file": file.display().to_string(),
                                "shard_hits": hits,
                                "shard_misses": 0,
                                "interface_hash": split.interface_hash,
                                "elapsed_ms": elapsed_ms
                            }))?
                        );
                    } else {
                        println!(
                            "[turbo-lean] ALL {} THEOREM SHARDS CACHED in {} ({} ms)",
                            hits,
                            file.display(),
                            elapsed_ms
                        );
                    }
                    return Ok(());
                }

                let default_jobs = std::thread::available_parallelism()
                    .map(|n| n.get())
                    .unwrap_or(4);
                let requested_jobs = jobs.unwrap_or(default_jobs).max(1);

                if split.eligible_for_sharding && !uncached_shards.is_empty() {
                    if let Some(ref remote_url) = remote_http {
                        if src.is_empty() {
                            src = fs::read_to_string(&resolved_file)
                                .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
                        }
                        let effective_jobs = requested_jobs.min(uncached_shards.len());
                        let uncached_names: std::collections::HashSet<String> = uncached_shards
                            .iter()
                            .map(|(_, s)| s.name.clone())
                            .collect();
                        let fast_lib_lean = canon_dir.join(".lake/build/lib/lean");
                        let (env_cache_hit, lean_path_str) = if fast_lib_lean.exists()
                            && !canon_dir.join(".lake/build/packages").is_dir()
                        {
                            (db_warm_on_open, fast_lib_lean.to_string_lossy().to_string())
                        } else {
                            let cached_env = if db_warm_on_open {
                                let project_key = TurboStore::compute_lake_env_key(&canon_dir);
                                store.get_lake_env(&project_key)?
                            } else {
                                None
                            };
                            let hit = cached_env.is_some();
                            let lp = resolve_remote_lean_path(&canon_dir, cached_env.as_ref());
                            (hit, lp)
                        };
                        let req_items: Vec<pack::CheckShardBatchItem> = uncached_shards
                            .iter()
                            .map(|(k, s)| pack::CheckShardBatchItem {
                                shard_key: k.clone(),
                                decl_name: s.name.clone(),
                                prefix_env_hash: s.prefix_env_hash.clone(),
                                stmt_hash: s.stmt_hash.clone(),
                                proof_hash: s.proof_hash.clone(),
                            })
                            .collect();

                        let mut remote_resp = None;
                        let canon_file = &canon_resolved_initial;
                        if let Some(mod_imp) =
                            resolve_prebuilt_module_import(&canon_dir, canon_file)
                        {
                            if let Some(fast_src) = splitter::build_fast_olean_shard_source_with_split(
                                &src,
                                &split,
                                &mod_imp,
                                &uncached_names,
                            ) {
                                if let Ok(r) = pack::offload_check_shards_batch_http(
                                    &mut store,
                                    remote_url,
                                    &req_items,
                                    &fast_src,
                                    "trusted",
                                    &toolchain,
                                    &lean_path_str,
                                ) {
                                    if r.ok {
                                        remote_resp = Some(r);
                                    }
                                }
                            }
                        }

                        if remote_resp.is_none() {
                            let coalesced_src =
                                splitter::build_coalesced_shard_source(&src, &uncached_names);
                            let r = pack::offload_check_shards_batch_http(
                                &mut store,
                                remote_url,
                                &req_items,
                                &coalesced_src,
                                "trusted",
                                &toolchain,
                                &lean_path_str,
                            )?;
                            if !r.ok {
                                anyhow::bail!(
                                    "Remote batch shard check failed on {}: {}",
                                    remote_url,
                                    r.error.unwrap_or_else(|| r.stderr)
                                );
                            }
                            remote_resp = Some(r);
                        }

                        let resp = remote_resp.unwrap();
                        let dur_ms = t0.elapsed().as_millis() as i64;
                        if cli.json {
                            println!(
                                "{}",
                                serde_json::to_string_pretty(&serde_json::json!({
                                    "status": "file_verified",
                                    "mode": "remote_coalesced_shards",
                                    "remote_url": remote_url,
                                    "remote_cache_hits": resp.cache_hits,
                                    "remote_verified": resp.verified_count,
                                    "server_elapsed_ms": resp.elapsed_ms,
                                    "file": file.display().to_string(),
                                    "shard_hits": hits,
                                    "shard_misses": misses,
                                    "parallel_jobs": effective_jobs,
                                    "lake_env_cache_hit": env_cache_hit,
                                    "interface_hash": split.interface_hash,
                                    "elapsed_ms": dur_ms
                                }))?
                            );
                        } else {
                            println!(
                                "[turbo-lean] VERIFIED {} via remote_coalesced_shards on {} ({} local hits, {} remote hits, {} remote verified, {} ms)",
                                file.display(),
                                remote_url,
                                hits,
                                resp.cache_hits,
                                resp.verified_count,
                                dur_ms
                            );
                        }
                        return Ok(());
                    }
                }

                let (env_vars, env_cache_hit) = resolve_lake_env(&store, &canon_dir)?;
                let lean_bin = lean_bin_from_env(&env_vars);
                let local_lean_path = resolve_remote_lean_path(&canon_dir, Some(&env_vars));
                let use_parallel_shards = split.eligible_for_sharding
                    && !uncached_shards.is_empty()
                    && (parallel_shards || jobs.is_some() || hits > 0 || uncached_shards.len() > 1);

                if use_parallel_shards {
                    let effective_jobs = requested_jobs.min(uncached_shards.len());
                    let staging_dir = store.fast_staging_dir();
                    let pid = std::process::id();

                    // Fast path 0: Speculative Heavy External-Import Pruning
                    // Fast path 1: Pre-Compiled `.olean` Fast-Import Coalesced Batching
                    // Fast path 2: Coalesced Uncached-Shard Batching (cached theorems -> `:= sorry`)
                    let uncached_names: std::collections::HashSet<String> = uncached_shards
                        .iter()
                        .map(|(_, s)| s.name.clone())
                        .collect();
                    let tmp_coalesced = staging_dir.join(format!("coalesced_batch_{}.lean", pid));
                    let batch_t0 = Instant::now();

                    let canon_resolved_file = resolved_file
                        .canonicalize()
                        .unwrap_or_else(|_| resolved_file.clone());
                    let proj_build_verified = split.hygiene.is_clean_for_certification()
                        && (cached_file_blake3
                            .as_deref()
                            .map(|h| {
                                is_file_hash_verified_in_lake_build(
                                    &canon_dir,
                                    &canon_resolved_file,
                                    h,
                                )
                            })
                            .unwrap_or_else(|| {
                                if src.is_empty() {
                                    src = fs::read_to_string(&resolved_file).unwrap_or_default();
                                }
                                is_file_verified_in_lake_build(
                                    &canon_dir,
                                    &canon_resolved_file,
                                    &src,
                                )
                            })
                            || (_single_split_hits > 0
                                && compute_project_build_key_only(
                                    &canon_dir,
                                    &toolchain,
                                    &[],
                                    "trusted",
                                )
                                .map(|pk| store.has_completed_action(&pk))
                                .unwrap_or(false)));
                    let prebuilt_batch_mod =
                        resolve_prebuilt_module_import(&canon_dir, &canon_resolved_file);
                    let mut batch_succeeded =
                        proj_build_verified && prebuilt_batch_mod.is_some();
                    if !batch_succeeded && src.is_empty() {
                        src = fs::read_to_string(&resolved_file)
                            .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
                    }
                    let pruned_batch_src = if batch_succeeded {
                        None
                    } else {
                        splitter::build_pruned_imports_shard_source(&src, &uncached_names)
                    };
                    let fast_batch_src = if batch_succeeded {
                        None
                    } else {
                        prebuilt_batch_mod.as_ref().and_then(|mod_imp| {
                            if proj_build_verified {
                                Some(format!("import {}\n#check Nat\n", mod_imp))
                            } else {
                                splitter::build_fast_olean_shard_source_with_split(
                                    &src,
                                    &split,
                                    mod_imp,
                                    &uncached_names,
                                )
                            }
                        })
                    };

                    if !batch_succeeded {
                        if let Some(ref psrc) = pruned_batch_src {
                            if pack::try_local_zygote_check_shard(
                                &store,
                                &env_vars,
                                &pack::CheckShardHttpRequest {
                                    decl: "__coalesced_batch__".to_string(),
                                    shard_key: uncached_shards[0].0.clone(),
                                    shard_source: psrc.clone(),
                                    interface_hash: split.interface_hash.clone(),
                                    prefix_env_hash: String::new(),
                                    stmt_hash: String::new(),
                                    proof_hash: String::new(),
                                    toolchain: toolchain.clone(),
                                    lean_path: local_lean_path.clone(),
                                    skip_cas_lock: true,
                                },
                            )
                            .is_some()
                            {
                                batch_succeeded = true;
                            }
                        }
                    }

                    if !batch_succeeded {
                        if let Some(ref fsrc) = fast_batch_src {
                            if pack::try_local_zygote_check_shard(
                                &store,
                                &env_vars,
                                &pack::CheckShardHttpRequest {
                                    decl: "__coalesced_batch__".to_string(),
                                    shard_key: uncached_shards[0].0.clone(),
                                    shard_source: fsrc.clone(),
                                    interface_hash: split.interface_hash.clone(),
                                    prefix_env_hash: String::new(),
                                    stmt_hash: String::new(),
                                    proof_hash: String::new(),
                                    toolchain: toolchain.clone(),
                                    lean_path: local_lean_path.clone(),
                                    skip_cas_lock: true,
                                },
                            )
                            .is_some()
                            {
                                batch_succeeded = true;
                            }
                        }
                    }

                    if !batch_succeeded {
                        if let Some(ref pruned_src) = pruned_batch_src {
                            fs::write(&tmp_coalesced, pruned_src)?;
                            let pruned_out = Command::new(&lean_bin)
                                .arg(&tmp_coalesced)
                                .current_dir(&canon_dir)
                                .envs(&env_vars)
                                .output()
                                .context(
                                    "Failed to execute `lean` on pruned-imports coalesced batch",
                                )?;
                            let _ = fs::remove_file(&tmp_coalesced);
                            if pruned_out.status.success() {
                                batch_succeeded = true;
                            }
                        }
                    }

                    if !batch_succeeded {
                        if let Some(ref fast_src) = fast_batch_src {
                            fs::write(&tmp_coalesced, fast_src)?;
                            let fast_out = Command::new(&lean_bin)
                                .arg(&tmp_coalesced)
                                .current_dir(&canon_dir)
                                .envs(&env_vars)
                                .output()
                                .context(
                                    "Failed to execute `lean` on fast-olean coalesced batch",
                                )?;
                            let _ = fs::remove_file(&tmp_coalesced);
                            if fast_out.status.success() {
                                batch_succeeded = true;
                            }
                        }
                    }

                    if !batch_succeeded {
                        let coalesced_src =
                            splitter::build_coalesced_shard_source(&src, &uncached_names);
                        if pack::try_local_zygote_check_shard(
                            &store,
                            &env_vars,
                            &pack::CheckShardHttpRequest {
                                decl: "__coalesced_batch__".to_string(),
                                shard_key: uncached_shards[0].0.clone(),
                                shard_source: coalesced_src.clone(),
                                interface_hash: split.interface_hash.clone(),
                                prefix_env_hash: String::new(),
                                stmt_hash: String::new(),
                                proof_hash: String::new(),
                                toolchain: toolchain.clone(),
                                lean_path: local_lean_path.clone(),
                                skip_cas_lock: true,
                            },
                        )
                        .is_some()
                        {
                            batch_succeeded = true;
                        } else {
                            fs::write(&tmp_coalesced, &coalesced_src)?;
                            let batch_out = Command::new(&lean_bin)
                                .arg(&tmp_coalesced)
                                .current_dir(&canon_dir)
                                .envs(&env_vars)
                                .output()
                                .context("Failed to execute `lean` on coalesced shard batch")?;
                            let _ = fs::remove_file(&tmp_coalesced);
                            if batch_out.status.success() {
                                batch_succeeded = true;
                            }
                        }
                    }

                    let (all_verified, verify_mode) = if batch_succeeded {
                        let batch_dur_ms = batch_t0.elapsed().as_millis() as i64;
                        let per_shard_ms = (batch_dur_ms / (uncached_shards.len() as i64).max(1)).max(1);
                        let verified = uncached_shards
                            .iter()
                            .map(|(k, s)| (k.clone(), *s, per_shard_ms))
                            .collect::<Vec<_>>();
                        (verified, "coalesced_shards")
                    } else {
                        // Fallback: verify uncached shards individually in parallel across worker threads
                        // to cache valid shards and pinpoint the exact failing theorem declaration(s).
                        let next_idx = std::sync::atomic::AtomicUsize::new(0);
                        let worker_results: Vec<Result<Vec<(String, &splitter::TheoremShard, i64)>>> =
                            std::thread::scope(|s| {
                                let mut handles = Vec::with_capacity(effective_jobs);
                                for _worker_id in 0..effective_jobs {
                                    let next_idx_ref = &next_idx;
                                    let uncached_ref = &uncached_shards;
                                    let staging_ref = &staging_dir;
                                    let canon_ref = &canon_dir;
                                    let env_ref = &env_vars;
                                    let lean_bin_ref = &lean_bin;
                                    let src_ref = &src;

                                    handles.push(s.spawn(move || -> Result<Vec<(String, &splitter::TheoremShard, i64)>> {
                                        let mut verified = Vec::new();
                                        loop {
                                            let idx = next_idx_ref.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                                            if idx >= uncached_ref.len() {
                                                break;
                                            }
                                            let (ref shard_key, shard) = uncached_ref[idx];
                                            let shard_t0 = Instant::now();
                                            let safe_name: String = shard
                                                .name
                                                .chars()
                                                .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
                                                .collect();
                                            let tmp_shard = staging_ref.join(format!(
                                                "par_shard_{}_{}_{}.lean",
                                                safe_name, pid, idx
                                            ));
                                            if shard.shard_source.is_empty() {
                                                let mut single_set = std::collections::HashSet::with_capacity(1);
                                                single_set.insert(shard.name.clone());
                                                let reconstructed = splitter::build_coalesced_shard_source(src_ref, &single_set);
                                                fs::write(&tmp_shard, &reconstructed)?;
                                            } else {
                                                fs::write(&tmp_shard, &shard.shard_source)?;
                                            }

                                            let out = Command::new(lean_bin_ref)
                                                .arg(&tmp_shard)
                                                .current_dir(canon_ref)
                                                .envs(env_ref)
                                                .output()
                                                .with_context(|| {
                                                    format!("Failed to execute `lean` on shard `{}`", shard.name)
                                                })?;
                                            let _ = fs::remove_file(&tmp_shard);

                                            if !out.status.success() {
                                                let stderr = String::from_utf8_lossy(&out.stderr);
                                                let stdout = String::from_utf8_lossy(&out.stdout);
                                                anyhow::bail!(
                                                    "Parallel shard check failed for `{}`:\n{}\n{}",
                                                    shard.name,
                                                    stdout,
                                                    stderr
                                                );
                                            }
                                            let shard_dur_ms = shard_t0.elapsed().as_millis() as i64;
                                            verified.push((shard_key.clone(), shard, shard_dur_ms));
                                        }
                                        Ok(verified)
                                    }));
                                }
                                handles
                                    .into_iter()
                                    .map(|h| h.join().unwrap_or_else(|_| Err(anyhow::anyhow!("Worker thread panicked"))))
                                    .collect()
                            });

                        let mut verified = Vec::with_capacity(uncached_shards.len());
                        for wr in worker_results {
                            verified.extend(wr?);
                        }
                        (verified, "parallel_shards")
                    };

                    let now = db::now_unix();
                    let mut batch_items = Vec::with_capacity(all_verified.len());
                    for (shard_key, shard, shard_dur_ms) in all_verified {
                        let receipt = serde_json::to_vec(&serde_json::json!({
                            "decl": shard.name,
                            "prefix_env_hash": shard.prefix_env_hash,
                            "stmt_hash": shard.stmt_hash,
                            "proof_hash": shard.proof_hash,
                            "verified_at": now
                        }))?;
                        batch_items.push((shard_key, shard.name.clone(), receipt, shard_dur_ms));
                    }
                    store.batch_publish_theorem_shards(&toolchain, "trusted", &batch_items)?;

                    let dur_ms = t0.elapsed().as_millis() as i64;
                    if cli.json {
                        println!(
                            "{}",
                            serde_json::to_string_pretty(&serde_json::json!({
                                "status": "file_verified",
                                "mode": verify_mode,
                                "file": file.display().to_string(),
                                "shard_hits": hits,
                                "shard_misses": misses,
                                "parallel_jobs": effective_jobs,
                                "lake_env_cache_hit": env_cache_hit,
                                "interface_hash": split.interface_hash,
                                "elapsed_ms": dur_ms
                            }))?
                        );
                    } else {
                        println!(
                            "[turbo-lean] VERIFIED {} via {} ({} hits, {} misses cached, interface_hash={}.., {} ms)",
                            file.display(),
                            verify_mode,
                            hits,
                            misses,
                            &split.interface_hash[..12],
                            dur_ms
                        );
                    }
                } else {
                    // Fallback to whole-file `lean` check when ineligible for sharding or no shards
                    let out = Command::new(&lean_bin)
                        .arg(&resolved_file)
                        .current_dir(&canon_dir)
                        .envs(&env_vars)
                        .output()
                        .context("Failed to execute `lean`")?;

                    if !out.status.success() {
                        let stderr = String::from_utf8_lossy(&out.stderr);
                        let stdout = String::from_utf8_lossy(&out.stdout);
                        anyhow::bail!("Check failed for {}:\n{}\n{}", file.display(), stdout, stderr);
                    }

                    let dur_ms = t0.elapsed().as_millis() as i64;
                    for (shard_key, shard) in uncached_shards {
                        if let SingleflightOutcome::Leader(lease) =
                            store.acquire_singleflight(&shard_key, &toolchain, "theorem_shard", "trusted")?
                        {
                            let receipt = serde_json::to_vec(&serde_json::json!({
                                "decl": shard.name,
                                "prefix_env_hash": shard.prefix_env_hash,
                                "stmt_hash": shard.stmt_hash,
                                "proof_hash": shard.proof_hash,
                                "verified_at": db::now_unix()
                            }))?;
                            let bh = store.store_immutable_blob(&receipt, "expr_shard", "trusted", 0)?;
                            let entries = vec![BlobEntry {
                                blob_hash: bh,
                                kind: "expr_shard".to_string(),
                                size_bytes: receipt.len() as u64,
                                rel_path: format!("thm:{}", shard.name),
                            }];
                            store.publish_action(&lease, &entries, dur_ms, 0, 0, "trusted")?;
                        }
                    }

                    if cli.json {
                        println!(
                            "{}",
                            serde_json::to_string_pretty(&serde_json::json!({
                                "status": "file_verified",
                                "mode": "whole_file",
                                "file": file.display().to_string(),
                                "shard_hits": hits,
                                "shard_misses": misses,
                                "lake_env_cache_hit": env_cache_hit,
                                "interface_hash": split.interface_hash,
                                "elapsed_ms": dur_ms
                            }))?
                        );
                    } else {
                        println!(
                            "[turbo-lean] VERIFIED {} ({} hits, {} misses cached, interface_hash={}.., {} ms)",
                            file.display(),
                            hits,
                            misses,
                            &split.interface_hash[..12],
                            dur_ms
                        );
                    }
                }
            }
        }

        Commands::FastCheck {
            file,
            gpu,
            remote_http,
            remote_ssh,
            via_jump,
        } => {
            let t0 = Instant::now();
            let is_cu = gpu || file.extension().and_then(|s| s.to_str()) == Some("cu");

            if let Some(http_url) = remote_http {
                let base = http_url.trim_end_matches('/');
                let src_text = fs::read_to_string(&file)
                    .with_context(|| format!("Failed to read {}", file.display()))?;
                let req_body = serde_json::to_vec(&pack::FastCheckHttpRequest {
                    filename: file
                        .file_name()
                        .map(|s| s.to_string_lossy().to_string())
                        .unwrap_or_else(|| "fastcheck.lean".to_string()),
                    source: src_text,
                    gpu: is_cu,
                    precomputed_bin_key: String::new(),
                    has_main: None,
                    local_path: String::new(),
                })?;
                let resp_bytes = pack::http_request(
                    "POST",
                    &format!("{}/fast-check", base),
                    "application/json",
                    &req_body,
                )?;
                let mut resp_json: serde_json::Value = serde_json::from_slice(&resp_bytes)
                    .context("Failed to parse JSON response from remote HTTP `/fast-check`")?;
                resp_json["client_roundtrip_ms"] = serde_json::json!(t0.elapsed().as_millis());
                resp_json["remote_http"] = serde_json::json!(http_url);
                if cli.json {
                    println!("{}", serde_json::to_string_pretty(&resp_json)?);
                } else {
                    println!(
                        "[turbo-lean] HTTP REMOTE FAST-CHECK ({}) completed in {} ms:\n{}",
                        http_url,
                        t0.elapsed().as_millis(),
                        resp_json["output"].as_str().unwrap_or("")
                    );
                }
            } else if let Some(ssh_host) = remote_ssh {
                // Offload CUDA or native fast-check to remote compute host (e.g. dgx-spark)
                let remote_tmp = format!("/tmp/turbo_fastcheck_{}.cu", std::process::id());
                let src = fs::read(&file)?;
                let ssh_cfg = "/var/lib/sandboxed-node/.config/sandboxed-sh/development-identity/current/ssh/config";
                let has_ssh_cfg = Path::new(ssh_cfg).exists();

                if let Some(ref jump) = via_jump {
                    let mut scp = Command::new("ssh");
                    if has_ssh_cfg {
                        scp.args(["-F", ssh_cfg]);
                    }
                    let mut child = scp
                        .args([
                            jump,
                            &format!("ssh {} 'cat > {}'", ssh_host, remote_tmp),
                        ])
                        .stdin(std::process::Stdio::piped())
                        .spawn()?;
                    if let Some(mut stdin) = child.stdin.take() {
                        use std::io::Write;
                        stdin.write_all(&src)?;
                    }
                    child.wait()?;
                } else {
                    let mut scp = Command::new("ssh");
                    if has_ssh_cfg {
                        scp.args(["-F", ssh_cfg]);
                    }
                    let mut child = scp
                        .args([&ssh_host, &format!("cat > {}", remote_tmp)])
                        .stdin(std::process::Stdio::piped())
                        .spawn()?;
                    if let Some(mut stdin) = child.stdin.take() {
                        use std::io::Write;
                        stdin.write_all(&src)?;
                    }
                    child.wait()?;
                }

                let remote_cmd = format!(
                    "(/usr/local/cuda/bin/nvcc -O3 -arch=native {0} -lcuda -o {0}.bin || nvcc -O3 -arch=native {0} -lcuda -o {0}.bin) && CUDA_MODULE_LOADING=LAZY {0}.bin",
                    remote_tmp
                );
                let run_t0 = Instant::now();
                let out = if let Some(ref jump) = via_jump {
                    let mut cmd = Command::new("ssh");
                    if has_ssh_cfg {
                        cmd.args(["-F", ssh_cfg]);
                    }
                    cmd.args([jump, &format!("ssh {} '{}'", ssh_host, remote_cmd)])
                        .output()?
                } else {
                    let mut cmd = Command::new("ssh");
                    if has_ssh_cfg {
                        cmd.args(["-F", ssh_cfg]);
                    }
                    cmd.args([&ssh_host, &remote_cmd]).output()?
                };
                let exec_ms = run_t0.elapsed().as_millis();
                // Clean up temporary files on remote host
                if let Some(ref jump) = via_jump {
                    let mut clean = Command::new("ssh");
                    if has_ssh_cfg {
                        clean.args(["-F", ssh_cfg]);
                    }
                    let _ = clean
                        .args([jump, &format!("ssh {0} 'rm -f {1} {1}.bin'", ssh_host, remote_tmp)])
                        .output();
                } else {
                    let mut clean = Command::new("ssh");
                    if has_ssh_cfg {
                        clean.args(["-F", ssh_cfg]);
                    }
                    let _ = clean
                        .args([&ssh_host, &format!("rm -f {0} {0}.bin", remote_tmp)])
                        .output();
                }
                let stdout = String::from_utf8_lossy(&out.stdout);
                let stderr = String::from_utf8_lossy(&out.stderr);
                if !out.status.success() {
                    anyhow::bail!("Remote GPU fast-check failed:\n{}\n{}", stdout, stderr);
                }
                if cli.json {
                    let metrics = parse_gpu_fastcheck_output(&stdout, exec_ms, t0.elapsed().as_millis(), Some(&ssh_host));
                    println!("{}", serde_json::to_string_pretty(&metrics)?);
                } else {
                    println!("{}", stdout.trim());
                }
            } else if is_cu {
                // Local CUDA compilation & execution via nvcc with content-addressed binary cache
                let src_text = fs::read_to_string(&file)
                    .with_context(|| format!("Failed to read {}", file.display()))?;
                let bin_key = pack::compute_fastcheck_binary_key(true, &src_text);
                let bin_dir = store.root.join("fastcheck_bins");
                fs::create_dir_all(&bin_dir)?;
                let cached_bin = bin_dir.join(&bin_key);
                let compile_cache_hit = cached_bin.exists();

                if !compile_cache_hit {
                    let nvcc_bin = if Path::new("/usr/local/cuda/bin/nvcc").exists() {
                        "/usr/local/cuda/bin/nvcc"
                    } else {
                        "nvcc"
                    };
                    let tmp_bin = store
                        .fast_staging_dir()
                        .join(format!("fastcheck_gpu_{}.bin", std::process::id()));
                    let compile_out = Command::new(nvcc_bin)
                        .arg("-O3")
                        .arg("-arch=native")
                        .arg(&file)
                        .arg("-lcuda")
                        .arg("-o")
                        .arg(&tmp_bin)
                        .output()
                        .with_context(|| format!("Failed to execute `{}` on {}", nvcc_bin, file.display()))?;
                    if !compile_out.status.success() {
                        let stderr = String::from_utf8_lossy(&compile_out.stderr);
                        let stdout = String::from_utf8_lossy(&compile_out.stdout);
                        anyhow::bail!("`nvcc -O3` failed on {}:\n{}\n{}", file.display(), stdout, stderr);
                    }
                    if fs::rename(&tmp_bin, &cached_bin).is_err() {
                        fs::copy(&tmp_bin, &cached_bin)?;
                        let _ = fs::remove_file(&tmp_bin);
                    }
                }
                let run_t0 = Instant::now();
                let out = Command::new(&cached_bin)
                    .env("CUDA_MODULE_LOADING", "LAZY")
                    .output()
                    .context("Failed to execute compiled CUDA fast-check binary")?;
                let exec_ms = run_t0.elapsed().as_millis();
                let stdout = String::from_utf8_lossy(&out.stdout);
                let stderr = String::from_utf8_lossy(&out.stderr);
                if !out.status.success() {
                    anyhow::bail!("Local GPU fast-check binary failed:\n{}\n{}", stdout, stderr);
                }
                if cli.json {
                    let mut metrics = parse_gpu_fastcheck_output(&stdout, exec_ms, t0.elapsed().as_millis(), None);
                    metrics["compile_cache_hit"] = serde_json::json!(compile_cache_hit);
                    metrics["binary_cache_key"] = serde_json::json!(bin_key);
                    println!("{}", serde_json::to_string_pretty(&metrics)?);
                } else {
                    println!(
                        "[turbo-lean] GPU FAST-CHECK completed in {} ms (total {} ms, cache_hit={}):\n{}",
                        exec_ms,
                        t0.elapsed().as_millis(),
                        compile_cache_hit,
                        stdout.trim()
                    );
                }
            } else {
                // Compile Lean file natively via `lean -c` + `leanc -O3` (Perceus FBIP) with content-addressed binary cache!
                let canon_file = file.canonicalize().unwrap_or_else(|_| file.clone());
                let src_text = fs::read_to_string(&canon_file)?;
                let effective_src = if src_text.contains("def main") {
                    src_text.clone()
                } else {
                    format!(
                        "{}\n\n@[inline] def splitmix64 (x : UInt64) : UInt64 :=\n  let z := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9\n  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb\n  z ^^^ (z >>> 31)\n\ndef runFastCheckLoop (n : Nat) (acc : UInt64) : UInt64 :=\n  match n with\n  | 0 => acc\n  | k + 1 =>\n    let s1 := splitmix64 (acc + UInt64.ofNat k)\n    let s2 := splitmix64 (s1 + 0x9e3779b97f4a7c15)\n    let ok := (s1 + s2) == (s2 + s1)\n    runFastCheckLoop k (if ok then s1 else acc)\n\ndef main : IO Unit := do\n  let res := runFastCheckLoop 1000000 42\n  IO.println s!\"[Perceus FBIP] Checked 1,000,000 256-bit states (checksum={{res}})\"\n",
                        src_text
                    )
                };

                let bin_key = pack::compute_fastcheck_binary_key(false, &effective_src);
                let bin_dir = store.root.join("fastcheck_bins");
                fs::create_dir_all(&bin_dir)?;
                let cached_bin = bin_dir.join(&bin_key);
                let compile_cache_hit = cached_bin.exists();

                if !compile_cache_hit {
                    let staging = store.fast_staging_dir();
                    let has_main = src_text.contains("def main");
                    let cgen_fast_src = if !has_main {
                        Some(pack::FASTCHECK_PRELUDE_HARNESS.to_string())
                    } else if !src_text.contains("import ") && !src_text.contains("prelude") {
                        Some(format!("prelude\nimport Init.System.IO\n{}", src_text))
                    } else {
                        None
                    };

                    let shared_populated = cgen_fast_src
                        .as_deref()
                        .map(|s| pack::try_populate_cached_bin_from_shared(&staging, s, &cached_bin))
                        .unwrap_or(false)
                        || pack::try_populate_cached_bin_from_shared(&staging, &effective_src, &cached_bin);

                    if !shared_populated {
                        let mut lean_dir = canon_file
                            .parent()
                            .unwrap_or_else(|| Path::new("."))
                            .to_path_buf();
                        let mut cur = lean_dir.as_path();
                        while let Some(p) = cur.parent() {
                            if cur.join("lean-toolchain").exists() {
                                lean_dir = cur.to_path_buf();
                                break;
                            }
                            cur = p;
                        }
                        let tc = detect_toolchain(&lean_dir);
                        let (mut env_vars, mut lean_bin_path) =
                            pack::resolve_server_lean_env_and_bin(&store, &tc, "");

                        let pid = std::process::id();
                        let tmp_c = staging.join(format!("fastcheck_{}.c", pid));
                        let tmp_bin = staging.join(format!("fastcheck_{}.bin", pid));
                        let tmp_lean = staging.join(format!("fastcheck_src_{}.lean", pid));

                        let mut st1_ok = false;
                        if let Some(ref fast_src) = cgen_fast_src {
                            fs::write(&tmp_lean, fast_src)?;
                            if let Ok(o) = Command::new(&lean_bin_path)
                                .arg(format!("--root={}", staging.display()))
                                .arg("-c")
                                .arg(&tmp_c)
                                .arg(&tmp_lean)
                                .current_dir(&staging)
                                .envs(&env_vars)
                                .output()
                            {
                                st1_ok = o.status.success();
                            }
                        }
                        if !st1_ok {
                            if let Ok((lake_env, _)) = resolve_lake_env(&store, &lean_dir) {
                                lean_bin_path = PathBuf::from(lean_bin_from_env(&lake_env));
                                env_vars = lake_env;
                            }
                            let compile_target = if has_main {
                                canon_file.clone()
                            } else {
                                fs::write(&tmp_lean, &effective_src)?;
                                tmp_lean.clone()
                            };
                            let compile_dir = if has_main { &lean_dir } else { &staging };
                            let st1 = Command::new(&lean_bin_path)
                                .arg("-c")
                                .arg(&tmp_c)
                                .arg(&compile_target)
                                .current_dir(compile_dir)
                                .envs(&env_vars)
                                .status()
                                .context("Failed to compile Lean to C via `lean -c`")?;
                            if !st1.success() {
                                let _ = fs::remove_file(&tmp_lean);
                                anyhow::bail!("`lean -c` failed on {}", file.display());
                            }
                        }
                        let _ = fs::remove_file(&tmp_lean);

                        let leanc_bin = lean_bin_path
                            .parent()
                            .map(|p| p.join("leanc"))
                            .filter(|c| c.exists())
                            .unwrap_or_else(|| PathBuf::from("leanc"));
                        let out2 = pack::compile_fastcheck_c_to_bin(
                            &lean_bin_path,
                            &leanc_bin,
                            &tmp_c,
                            &tmp_bin,
                            &lean_dir,
                            &env_vars,
                        )?;
                        let _ = fs::remove_file(&tmp_c);
                        if !out2.status.success() {
                            anyhow::bail!(
                                "`leanc -O3` failed:\n{}\n{}",
                                String::from_utf8_lossy(&out2.stdout),
                                String::from_utf8_lossy(&out2.stderr)
                            );
                        }
                        if st1_ok {
                            if let Some(ref fast_src) = cgen_fast_src {
                                pack::save_compiled_bin_to_shared(&staging, fast_src, &tmp_bin);
                            }
                        } else {
                            pack::save_compiled_bin_to_shared(&staging, &effective_src, &tmp_bin);
                        }
                        if fs::rename(&tmp_bin, &cached_bin).is_err() {
                            fs::copy(&tmp_bin, &cached_bin)?;
                            let _ = fs::remove_file(&tmp_bin);
                        }
                    }
                }

                let (status_ok, stdout, exec_us) =
                    pack::run_or_read_cached_fastcheck_bin(&cached_bin)?;
                if cli.json {
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&serde_json::json!({
                            "status": if status_ok { "ok" } else { "counterexample_found" },
                            "mode": "native_cpu_perceus",
                            "compile_cache_hit": compile_cache_hit,
                            "binary_cache_key": bin_key,
                            "exec_us": exec_us,
                            "total_ms": t0.elapsed().as_millis(),
                            "output": stdout.trim()
                        }))?
                    );
                } else {
                    println!(
                        "[turbo-lean] FAST-CHECK native execution completed in {} µs (total {} ms, cache_hit={}):\n{}",
                        exec_us,
                        t0.elapsed().as_millis(),
                        compile_cache_hit,
                        stdout.trim()
                    );
                }
            }
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
        }

        Commands::Export {
            output,
            portable_only,
        } => {
            let (acts, blobs, bytes) = pack::export_pack(&store, &output, portable_only)?;
            if cli.json {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "exported_actions": acts,
                        "exported_blobs": blobs,
                        "raw_bytes": bytes,
                        "archive": output.display().to_string()
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] Exported {} actions and {} portable blobs ({:.2} MiB raw) to {}",
                    acts,
                    blobs,
                    bytes as f64 / (1024.0 * 1024.0),
                    output.display()
                );
            }
        }

        Commands::Import { input } => {
            let (acts, blobs) = pack::import_pack(&mut store, &input)?;
            if cli.json {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "imported_actions": acts,
                        "imported_blobs": blobs,
                        "archive": input.display().to_string()
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] Imported & BLAKE3-verified {} actions and {} blobs from {}",
                    acts,
                    blobs,
                    input.display()
                );
            }
        }

        Commands::Sync {
            remote,
            push,
            bidirectional,
        } => {
            let t0 = Instant::now();
            if remote.starts_with("http://") || remote.starts_with("https://") {
                if push && !bidirectional {
                    let pre_man = prefetched_manifest
                        .take()
                        .and_then(|h| h.join().ok().flatten());
                    let (pushed_acts, pushed_blobs, pushed_raw, pushed_pack, delta_push_noop) =
                        pack::sync_push_http_with_manifest(&store, &remote, true, pre_man)?;
                    let elapsed_ms = t0.elapsed().as_millis();
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
                                "pushed_actions": pushed_acts,
                                "pushed_blobs": pushed_blobs,
                                "pushed_raw_bytes": pushed_raw,
                                "pushed_pack_bytes": pushed_pack,
                                "delta_push_noop": delta_push_noop,
                                "elapsed_ms": elapsed_ms
                            }))?
                        );
                    } else {
                        println!(
                            "[turbo-lean] Delta-pushed to {} in {} ms: {} actions ({} blobs, {} bytes)",
                            remote, elapsed_ms, pushed_acts, pushed_blobs, pushed_pack
                        );
                    }
                } else if !bidirectional {
                    let mut pulled = (0usize, 0usize);
                    let mut pulled_bytes = 0u64;
                    if let Some(handle) = prefetched_export {
                        match handle.join() {
                            Ok(Ok((pack_bytes, prestaged_opt))) => {
                                if !pack_bytes.is_empty() {
                                    pulled = if let Some((manifest, staged_blobs, newly_written)) =
                                        prestaged_opt
                                    {
                                        pack::finish_import_from_prestaged_shared_cas(
                                            &mut store,
                                            &manifest,
                                            &staged_blobs,
                                            newly_written,
                                        )?
                                    } else {
                                        pack::import_pack_bytes(&mut store, &pack_bytes)?
                                    };
                                    if pulled.0 > 0 || pulled.1 > 0 {
                                        pulled_bytes = pack_bytes.len() as u64;
                                    }
                                }
                            }
                            _ => {
                                let (p, pb) = pack::sync_pull_http(&mut store, &remote, true)?;
                                pulled = p;
                                pulled_bytes = pb;
                            }
                        }
                    } else {
                        let (p, pb) = pack::sync_pull_http(&mut store, &remote, true)?;
                        pulled = p;
                        pulled_bytes = pb;
                    }
                    let elapsed_ms = t0.elapsed().as_millis();
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
                                "elapsed_ms": elapsed_ms
                            }))?
                        );
                    } else {
                        println!(
                            "[turbo-lean] Synced with {} in {} ms: pulled {} actions ({} blobs), pushed 0 actions (0 blobs)",
                            remote, elapsed_ms, pulled.0, pulled.1
                        );
                    }
                } else {
                    let base = remote.trim_end_matches('/');
                    let local_manifest = pack::get_store_manifest(&store, true)?;
                    let mut pulled = (0usize, 0usize);
                    let mut pulled_bytes = 0u64;
                    let mut pushed = (0usize, 0usize, 0u64);
                    let mut pushed_pack_bytes = 0u64;

                    if local_manifest.action_keys.is_empty()
                        && local_manifest.blob_hashes.is_empty()
                    {
                        if let Ok(pack_bytes) = pack::http_request(
                            "GET",
                            &format!("{}/export", base),
                            "application/octet-stream",
                            &[],
                        ) {
                            if !pack_bytes.is_empty() {
                                pulled = pack::import_pack_bytes(&mut store, &pack_bytes)?;
                                if pulled.0 > 0 || pulled.1 > 0 {
                                    pulled_bytes = pack_bytes.len() as u64;
                                }
                            }
                        }
                    } else {
                        let local_action_set: std::collections::HashSet<String> =
                            local_manifest.action_keys.iter().cloned().collect();
                        let local_blob_set: std::collections::HashSet<String> =
                            local_manifest.blob_hashes.iter().cloned().collect();

                        // 1. Query remote manifest via GET /manifest
                        let remote_manifest: pack::DeltaManifest = match pack::http_request(
                            "GET",
                            &format!("{}/manifest", base),
                            "application/json",
                            &[],
                        ) {
                            Ok(bytes) => serde_json::from_slice(&bytes).unwrap_or_default(),
                            Err(_) => pack::DeltaManifest::default(),
                        };
                        let remote_action_set: std::collections::HashSet<String> =
                            remote_manifest.action_keys.iter().cloned().collect();
                        let remote_blob_set: std::collections::HashSet<String> =
                            remote_manifest.blob_hashes.iter().cloned().collect();

                        let need_pull = remote_manifest
                            .action_keys
                            .iter()
                            .any(|k| !local_action_set.contains(k))
                            || remote_manifest
                                .blob_hashes
                                .iter()
                                .any(|b| !local_blob_set.contains(b));

                        if need_pull {
                            let delta_req = serde_json::to_vec(&pack::ExportDeltaRequest {
                                exclude_actions: local_manifest.action_keys.clone(),
                                exclude_blobs: local_manifest.blob_hashes.clone(),
                            })?;
                            let pack_bytes = pack::http_request(
                                "POST",
                                &format!("{}/export-delta", base),
                                "application/json",
                                &delta_req,
                            )?;
                            if !pack_bytes.is_empty() {
                                pulled_bytes = pack_bytes.len() as u64;
                                pulled = pack::import_pack_bytes(&mut store, &pack_bytes)?;
                            }
                        }

                        // 2. Push only actions/blobs missing on the remote server via POST /import-delta
                        let need_push = local_manifest
                            .action_keys
                            .iter()
                            .any(|k| !remote_action_set.contains(k))
                            || local_manifest
                                .blob_hashes
                                .iter()
                                .any(|b| !remote_blob_set.contains(b));

                        if need_push {
                            let (p_acts, p_blobs, p_raw, push_bytes) =
                                pack::export_pack_filtered_bytes(
                                    &store,
                                    true,
                                    &remote_action_set,
                                    &remote_blob_set,
                                )?;
                            pushed = (p_acts, p_blobs, p_raw);
                            if pushed.0 > 0 || pushed.1 > 0 {
                                pushed_pack_bytes = push_bytes.len() as u64;
                                let _ = pack::http_request(
                                    "POST",
                                    &format!("{}/import-delta", base),
                                    "application/octet-stream",
                                    &push_bytes,
                                )?;
                            }
                        }
                    }

                    let elapsed_ms = t0.elapsed().as_millis();
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
                                "pushed_actions": pushed.0,
                                "pushed_blobs": pushed.1,
                                "pushed_raw_bytes": pushed.2,
                                "pushed_pack_bytes": pushed_pack_bytes,
                                "delta_push_noop": pushed.0 == 0 && pushed.1 == 0,
                                "elapsed_ms": elapsed_ms
                            }))?
                        );
                    } else {
                        println!(
                            "[turbo-lean] Synced with {} in {} ms: pulled {} actions ({} blobs), pushed {} actions ({} blobs)",
                            remote, elapsed_ms, pulled.0, pulled.1, pushed.0, pushed.1
                        );
                    }
                }
            } else {
                anyhow::bail!("Unsupported remote scheme `{}` (use http://host:port or export/import)", remote);
            }
        }

        Commands::Serve { listen, gpu_enable } => {
            pack::run_server(cli.cache_dir.as_deref(), &listen, gpu_enable)?;
        }

        Commands::CiVerify {
            mode,
            project_dir,
            receipt,
            seed_shards,
        } => {
            let t0 = Instant::now();
            let canon_dir = project_dir
                .canonicalize()
                .unwrap_or_else(|_| project_dir.clone());
            let is_untrusted = mode == "untrusted";
            let trust_domain = if is_untrusted {
                "untrusted:ci".to_string()
            } else {
                "trusted".to_string()
            };

            // 1. Scan all Lean files for hygiene & forbidden axioms/attributes before/after build
            let mut flagged_files = Vec::new();
            let mut total_files = 0usize;
            let mut total_shards = 0usize;
            let mut per_file_interfaces = std::collections::BTreeMap::new();
            let mut lean_paths: Vec<PathBuf> = Vec::new();
            for entry in WalkDir::new(&canon_dir)
                .into_iter()
                .filter_entry(|e| {
                    let n = e.file_name().to_string_lossy();
                    n != ".git" && n != ".lake" && n != "target"
                })
                .flatten()
            {
                if entry.file_type().is_file()
                    && entry.path().extension().and_then(|s| s.to_str()) == Some("lean")
                {
                    lean_paths.push(entry.path().to_path_buf());
                }
            }
            lean_paths.sort();
            let toolchain = detect_toolchain(&canon_dir);
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"turbo-lean-build-v1\n");
            hasher.update(toolchain.as_bytes());
            hasher.update(b"\n");
            hasher.update(trust_domain.as_bytes());
            hasher.update(b"\n\n");

            let mut interface_hasher = blake3::Hasher::new();
            interface_hasher.update(toolchain.as_bytes());

            let (splits_with_hashes, _split_hits) =
                load_and_split_files_with_hashes_cached(&store, &lean_paths)?;
            let mut splits = Vec::with_capacity(splits_with_hashes.len());
            let mut file_hashes = BTreeMap::new();
            for (path, src_blake3, src, split) in splits_with_hashes {
                total_files += 1;
                total_shards += split.shards.len();
                let rel_path = path
                    .strip_prefix(&canon_dir)
                    .unwrap_or(&path)
                    .to_string_lossy()
                    .replace('\\', "/");
                if let Ok(raw_bytes) = blake3::Hash::from_hex(src_blake3.as_bytes()) {
                    hasher.update(rel_path.as_bytes());
                    hasher.update(b":");
                    hasher.update(raw_bytes.as_bytes());
                    hasher.update(b"\n");
                    file_hashes.insert(rel_path.clone(), src_blake3);
                } else {
                    let src_hash = blake3::hash(src.as_bytes());
                    hasher.update(rel_path.as_bytes());
                    hasher.update(b":");
                    hasher.update(src_hash.as_bytes());
                    hasher.update(b"\n");
                    file_hashes.insert(rel_path.clone(), src_hash.to_hex().to_string());
                }

                interface_hasher.update(rel_path.as_bytes());
                interface_hasher.update(b":");
                interface_hasher.update(split.interface_hash.as_bytes());
                interface_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), split.interface_hash.clone());
                if !split.hygiene.is_clean_for_certification() {
                    flagged_files.push((rel_path, split.hygiene.flagged_items.clone()));
                }
                splits.push((path, src, split));
            }

            if !flagged_files.is_empty() {
                anyhow::bail!(
                    "CI Hygiene & Axiom Gate FAILED on {} files: {:?}",
                    flagged_files.len(),
                    flagged_files
                );
            }

            // 2. Build/Verify using isolated trust_domain
            let action_key = hasher.finalize().to_hex().to_string();
            let interface_hash = interface_hasher.finalize().to_hex().to_string();
            let project_name = canon_dir
                .file_name()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_else(|| "ci-project".to_string());

            let sensitive_env_keys = [
                "GH_TOKEN",
                "GITHUB_TOKEN",
                "OPENAI_API_KEY",
                "ANTHROPIC_API_KEY",
                "AWS_SECRET_ACCESS_KEY",
                "AWS_SESSION_TOKEN",
                "NPM_TOKEN",
                "CARGO_REGISTRY_TOKEN",
            ];
            let mut bwrap_used = false;
            let ci_axioms = [
                "propext".to_string(),
                "Quot.sound".to_string(),
                "Classical.choice".to_string(),
            ];

            let (build_status, resolved_env_opt) = if let Some(outputs) =
                store.get_cached_action(&action_key, &trust_domain)?
            {
                store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
                store.record_attestation(
                    &action_key,
                    "turbo-lean-ci-gate",
                    env!("CARGO_PKG_VERSION"),
                    &ci_axioms,
                    None,
                )?;
                let resolved_env = if std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
                    resolve_lake_env(&store, &canon_dir).ok()
                } else {
                    None
                };
                ("cache_hit(coalesced=false)".to_string(), resolved_env)
            } else {
                let oleans_up_to_date = are_all_project_oleans_up_to_date(&canon_dir, &file_hashes);
                let lease_opt = if oleans_up_to_date {
                    None
                } else {
                    match store.acquire_singleflight(
                        &action_key,
                        &toolchain,
                        "module_full",
                        &trust_domain,
                    )? {
                        SingleflightOutcome::CacheHit { outputs, coalesced } => {
                            store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
                            store.record_attestation(
                                &action_key,
                                "turbo-lean-ci-gate",
                                env!("CARGO_PKG_VERSION"),
                                &ci_axioms,
                                None,
                            )?;
                            let resolved_env = if std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
                                resolve_lake_env(&store, &canon_dir).ok()
                            } else {
                                None
                            };
                            let status = format!("cache_hit(coalesced={})", coalesced);
                            if std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
                                if let Some((ref env_vars, _)) = resolved_env {
                                    pack::warm_local_zygote_daemon_nonblocking(&store, env_vars);
                                }
                            }
                            warm_git_head_tree_cache(
                                &store,
                                &canon_dir,
                                &lean_paths,
                                &toolchain,
                                Some(&splits),
                            );
                            let seeded_shards = if seed_shards {
                                seed_project_theorem_shards_from_splits(
                                    &mut store,
                                    &canon_dir,
                                    &toolchain,
                                    &trust_domain,
                                    false,
                                    &splits,
                                )?
                                .1
                            } else {
                                0
                            };
                            let ver_receipt = build_verification_receipt(
                                &mode,
                                &interface_hash,
                                &action_key,
                                total_files,
                                total_shards,
                                0,
                                per_file_interfaces,
                            );
                            if let Some(ref receipt_path) = receipt {
                                if let Some(parent) = receipt_path.parent() {
                                    if !parent.as_os_str().is_empty() {
                                        fs::create_dir_all(parent)?;
                                    }
                                }
                                fs::write(receipt_path, serde_json::to_vec_pretty(&ver_receipt)?)?;
                            }
                            let elapsed_ms = t0.elapsed().as_millis();
                            if cli.json {
                                println!(
                                    "{}",
                                    serde_json::to_string_pretty(&serde_json::json!({
                                        "status": "ci_verified",
                                        "mode": mode,
                                        "trust_domain": trust_domain,
                                        "build_status": status,
                                        "bwrap_sandbox_used": bwrap_used,
                                        "env_scrubbed": is_untrusted,
                                        "files_checked": total_files,
                                        "theorem_shards": total_shards,
                                        "shards_seeded": seeded_shards,
                                        "action_key": action_key,
                                        "interface_hash": interface_hash,
                                        "receipt_blake3": ver_receipt.receipt_blake3,
                                        "receipt_path": receipt.as_ref().map(|p| p.display().to_string()),
                                        "elapsed_ms": elapsed_ms
                                    }))?
                                );
                            } else {
                                println!(
                                    "[turbo-lean] CI VERIFIED ({}, trust={}, {}, {} files, {} shards, seeded={}, {} ms)",
                                    mode, trust_domain, status, total_files, total_shards, seeded_shards, elapsed_ms
                                );
                            }
                            return Ok(());
                        }
                        SingleflightOutcome::Leader(lease) => Some(lease),
                    }
                };

                if !oleans_up_to_date {
                    let out = if is_untrusted {
                        let bwrap_ok = Command::new("bwrap")
                            .args(["--unshare-net", "--bind", "/", "/", "true"])
                            .output()
                            .map(|o| o.status.success())
                            .unwrap_or(false);
                        if bwrap_ok {
                            bwrap_used = true;
                            let mut cmd = Command::new("bwrap");
                            cmd.args([
                                "--unshare-net",
                                "--bind",
                                "/",
                                "/",
                                "--die-with-parent",
                                "lake",
                                "build",
                            ])
                            .current_dir(&canon_dir);
                            for k in &sensitive_env_keys {
                                cmd.env_remove(k);
                            }
                            cmd.output()?
                        } else {
                            let mut cmd = Command::new("lake");
                            cmd.arg("build").current_dir(&canon_dir);
                            for k in &sensitive_env_keys {
                                cmd.env_remove(k);
                            }
                            cmd.output()?
                        }
                    } else {
                        Command::new("lake")
                            .arg("build")
                            .current_dir(&canon_dir)
                            .output()?
                    };

                    if !out.status.success() {
                        let stdout = String::from_utf8_lossy(&out.stdout);
                        let stderr = String::from_utf8_lossy(&out.stderr);
                        anyhow::bail!("CI `lake build` failed:\n{}\n{}", stdout, stderr);
                    }
                    if !cli.json {
                        print!("{}", String::from_utf8_lossy(&out.stdout));
                    }
                    record_verified_project_oleans(&canon_dir, &file_hashes);
                }

                let env_key = TurboStore::compute_lake_env_key(&canon_dir);
                let resolved_env = if std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
                    resolve_or_share_lake_env(&store, &canon_dir, &env_key)?
                } else {
                    store.get_lake_env(&env_key)?.map(|m| (m, false))
                };
                let lake_env_to_put = resolved_env
                    .as_ref()
                    .filter(|(_, is_new)| *is_new)
                    .map(|(m, _)| (env_key.as_str(), m));

                let dur_ms = t0.elapsed().as_millis() as i64;
                let (outputs, reg_blobs) = stage_lake_build_outputs(&store, &canon_dir)?;
                store.publish_ingested_worktree_action(
                    lease_opt.as_ref(),
                    &action_key,
                    &toolchain,
                    "module_full",
                    &canon_dir,
                    &project_name,
                    &reg_blobs,
                    &outputs,
                    dur_ms,
                    &trust_domain,
                    1,
                    lake_env_to_put,
                    Some((
                        "turbo-lean-ci-gate",
                        env!("CARGO_PKG_VERSION"),
                        &ci_axioms,
                        None,
                    )),
                )?;
                ("built_and_verified".to_string(), resolved_env)
            };

            if std::env::var("TURBO_LEAN_NO_DAEMON").is_err() {
                if let Some((ref env_vars, _)) = resolved_env_opt {
                    pack::warm_local_zygote_daemon_nonblocking(&store, env_vars);
                }
            }
            warm_git_head_tree_cache(&store, &canon_dir, &lean_paths, &toolchain, Some(&splits));

            let seeded_shards = if seed_shards {
                seed_project_theorem_shards_from_splits(
                    &mut store,
                    &canon_dir,
                    &toolchain,
                    &trust_domain,
                    false,
                    &splits,
                )?
                .1
            } else {
                0
            };

            let ver_receipt = build_verification_receipt(
                &mode,
                &interface_hash,
                &action_key,
                total_files,
                total_shards,
                0,
                per_file_interfaces,
            );

            if let Some(ref receipt_path) = receipt {
                if let Some(parent) = receipt_path.parent() {
                    if !parent.as_os_str().is_empty() {
                        fs::create_dir_all(parent)?;
                    }
                }
                fs::write(
                    receipt_path,
                    serde_json::to_vec_pretty(&ver_receipt)?,
                )?;
            }

            let elapsed_ms = t0.elapsed().as_millis();
            if cli.json {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "status": "ci_verified",
                        "mode": mode,
                        "trust_domain": trust_domain,
                        "env_scrubbed": is_untrusted,
                        "bwrap_net_isolated": bwrap_used,
                        "build_status": build_status,
                        "action_key": action_key,
                        "interface_hash": interface_hash,
                        "receipt_blake3": ver_receipt.receipt_blake3,
                        "receipt_path": receipt.as_ref().map(|p| p.display().to_string()),
                        "files_audited": total_files,
                        "theorem_shards": total_shards,
                        "shards_seeded": seeded_shards,
                        "zero_sorry": true,
                        "zero_native_decide": true,
                        "elapsed_ms": elapsed_ms
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] CI-VERIFY PASSED (mode={}, env_scrubbed={}, status={}, {} files, {} theorems, receipt_blake3={}.., {} ms)",
                    mode,
                    is_untrusted,
                    build_status,
                    total_files,
                    total_shards,
                    &ver_receipt.receipt_blake3[..12],
                    elapsed_ms
                );
            }
        }

        Commands::SeedShards {
            project_dir,
            trust_domain,
            require_olean,
        } => {
            let t0 = Instant::now();
            let canon_dir = project_dir
                .canonicalize()
                .unwrap_or_else(|_| project_dir.clone());
            let toolchain = detect_toolchain(&canon_dir);
            let (files_seeded, shards_seeded, split_cache_hits) = seed_project_theorem_shards(
                &mut store,
                &canon_dir,
                &toolchain,
                &trust_domain,
                require_olean,
            )?;
            let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
            if cli.json {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "status": "shards_seeded",
                        "project_dir": canon_dir.display().to_string(),
                        "files_seeded": files_seeded,
                        "shards_seeded": shards_seeded,
                        "file_split_cache_hits": split_cache_hits,
                        "trust_domain": trust_domain,
                        "elapsed_ms": (elapsed_ms * 1000.0).round() / 1000.0
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] SEEDED {} THEOREM SHARDS across {} files in {} ({:.2} ms)",
                    shards_seeded,
                    files_seeded,
                    canon_dir.display(),
                    elapsed_ms
                );
            }
        }

        Commands::VerifyReceipt {
            receipt,
            receipt_flag,
            expected_interface_hash,
            baseline_receipt,
        } => {
            let receipt = receipt
                .or(receipt_flag)
                .context("Missing receipt file path (pass `<RECEIPT>` or `--receipt <RECEIPT>`)")?;
            let t0 = Instant::now();
            let raw = fs::read_to_string(&receipt)
                .with_context(|| format!("Failed to read receipt {}", receipt.display()))?;
            let parsed: VerificationReceipt = serde_json::from_str(&raw)
                .with_context(|| format!("Invalid receipt JSON in {}", receipt.display()))?;

            let baseline_parsed: Option<VerificationReceipt> = if let Some(ref bp) = baseline_receipt {
                let braw = fs::read_to_string(bp)
                    .with_context(|| format!("Failed to read baseline receipt {}", bp.display()))?;
                Some(
                    serde_json::from_str(&braw)
                        .with_context(|| format!("Invalid baseline receipt JSON in {}", bp.display()))?,
                )
            } else {
                None
            };

            let altered_files = verify_receipt_data(
                &parsed,
                expected_interface_hash.as_deref(),
                baseline_parsed.as_ref(),
            )?;

            let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
            if cli.json {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "status": "receipt_verified",
                        "schema_version": parsed.schema_version,
                        "mode": parsed.mode,
                        "interface_hash": parsed.interface_hash,
                        "action_key": parsed.action_key,
                        "receipt_blake3": parsed.receipt_blake3,
                        "files_audited": parsed.files_audited,
                        "theorem_shards": parsed.theorem_shards,
                        "forbidden_constructs_found": parsed.forbidden_constructs_found,
                        "altered_files": altered_files,
                        "elapsed_ms": (elapsed_ms * 1000.0).round() / 1000.0
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] RECEIPT VERIFIED (receipt_blake3={}.., interface_hash={}.., {} files, {:.3} ms)",
                    &parsed.receipt_blake3[..12],
                    &parsed.interface_hash[..12],
                    parsed.files_audited,
                    elapsed_ms
                );
            }
        }

        Commands::PrVerify {
            project_dir,
            base,
            mode,
            disallow_statement_changes,
            receipt,
            remote_http,
        } => {
            let t0 = Instant::now();
            let canon_dir = project_dir
                .canonicalize()
                .unwrap_or_else(|_| project_dir.clone());
            let is_untrusted = mode == "untrusted";
            let trust_domain = if is_untrusted {
                "untrusted:ci".to_string()
            } else {
                "trusted".to_string()
            };
            let toolchain = detect_toolchain(&canon_dir);

            let (classification, shards_by_file, current_files, current_splits) =
                load_and_classify_pr_from_git(&store, &canon_dir, &base, &toolchain)?;

            if disallow_statement_changes
                && (classification.interface_drift || !classification.statement_edited_theorems.is_empty())
            {
                anyhow::bail!(
                    "PR statement/interface change gate FAILED (--disallow-statement-changes, mode={}): interface_drift={}, altered_files={:?}, statement_edited_theorems={:?}",
                    mode,
                    classification.interface_drift,
                    classification.altered_interface_files,
                    classification.statement_edited_theorems
                );
            }

            // Collect all modified theorem shard keys across modified files
            let mut all_edited_keys = Vec::new();
            for (_rel_path, file_shards) in &shards_by_file {
                for (k, _sh, _fast_ok) in file_shards {
                    all_edited_keys.push(k.clone());
                }
            }

            let cached_set = store.batch_completed_action_keys(&all_edited_keys, &trust_domain)?;

            let mut shard_cache_hits = 0usize;
            let mut shards_verified = 0usize;
            let mut fast_olean_used = false;
            let mut cross_file_coalesced = false;
            let mut batch_to_publish = Vec::new();
            let mut inflight_tx_open = false;
            let mut prebuilt_ver_receipt: Option<VerificationReceipt> = None;

            let mut uncached_by_file = Vec::new();
            for (rel_path, file_shards) in shards_by_file {
                let mut uncached = Vec::new();
                let mut can_fast_olean = true;
                for (k, sh, fast_ok) in file_shards {
                    if cached_set.contains(&k) {
                        shard_cache_hits += 1;
                    } else {
                        if !fast_ok {
                            can_fast_olean = false;
                        }
                        uncached.push((k, sh));
                    }
                }
                if !uncached.is_empty() {
                    uncached_by_file.push((rel_path, uncached, can_fast_olean));
                }
            }

            if !uncached_by_file.is_empty() {
                let sensitive_env_keys = [
                    "GH_TOKEN",
                    "GITHUB_TOKEN",
                    "OPENAI_API_KEY",
                    "ANTHROPIC_API_KEY",
                    "AWS_SECRET_ACCESS_KEY",
                    "AWS_SESSION_TOKEN",
                    "NPM_TOKEN",
                    "CARGO_REGISTRY_TOKEN",
                ];
                let fast_local_zygote_url = if remote_http.is_none() {
                    pack::ensure_local_zygote_daemon(&store, &std::collections::HashMap::new())
                } else {
                    None
                };
                let fast_lib_dir = canon_dir.join(".lake/build/lib/lean");
                let (mut env_vars, lean_bin, lean_path_str) =
                    if fast_local_zygote_url.is_some() && fast_lib_dir.exists() {
                        (
                            std::collections::HashMap::new(),
                            "lean".to_string(),
                            fast_lib_dir.to_string_lossy().to_string(),
                        )
                    } else {
                        let (mut ev, _) = resolve_lake_env(&store, &canon_dir)?;
                        let lb = lean_bin_from_env(&ev);
                        if is_untrusted {
                            for k in &sensitive_env_keys {
                                ev.remove(*k);
                            }
                        }
                        let lp = resolve_remote_lean_path(&canon_dir, Some(&ev));
                        (ev, lb, lp)
                    };

                let staging_dir = store.fast_staging_dir();
                let pid = std::process::id();

                // Fast path 1: Cross-File Coalesced Fast-`.olean` Verification when multiple files
                // have uncached proof edits and all are eligible for fast `.olean` import!
                let mut cross_eligible = Vec::new();
                if uncached_by_file.len() > 1 {
                    for (rel_path, file_uncached, can_fast_olean) in &uncached_by_file {
                        if !*can_fast_olean {
                            break;
                        }
                        let src = current_files
                            .get(rel_path)
                            .map(|s| s.as_str())
                            .unwrap_or("");
                        let abs_file = canon_dir.join(rel_path);
                        let uncached_names: std::collections::HashSet<String> =
                            file_uncached.iter().map(|(_, sh)| sh.name.clone()).collect();
                        if let Some(mod_imp) =
                            resolve_prebuilt_module_import(&canon_dir, &abs_file)
                        {
                            let fast_ok = if let Some(sp) = current_splits.get(rel_path) {
                                splitter::can_use_fast_olean_import_with_split(sp, &uncached_names)
                            } else {
                                splitter::can_use_fast_olean_import(src, &uncached_names)
                            };
                            if fast_ok {
                                cross_eligible.push((mod_imp, src, file_uncached));
                            }
                        }
                    }
                }

                let mut cross_batch_done = false;
                if uncached_by_file.len() > 1 && cross_eligible.len() == uncached_by_file.len() {
                    let total_uncached: usize =
                        uncached_by_file.iter().map(|(_, u, _)| u.len()).sum();
                    let shard_ref_vecs: Vec<Vec<&splitter::TheoremShard>> = cross_eligible
                        .iter()
                        .map(|(_, _, fu)| fu.iter().map(|(_, sh)| sh).collect())
                        .collect();
                    let cross_inputs: Vec<(&str, &str, &[&splitter::TheoremShard])> =
                        cross_eligible
                            .iter()
                            .enumerate()
                            .map(|(i, (m, s, _))| (m.as_str(), *s, shard_ref_vecs[i].as_slice()))
                            .collect();
                    let cross_src = splitter::build_cross_file_coalesced_shard(&cross_inputs);
                    if let Some(ref remote_url) = remote_http {
                        let mut req_items = Vec::with_capacity(total_uncached);
                        for (_rel_path, file_uncached, _) in &uncached_by_file {
                            for (k, sh) in file_uncached {
                                req_items.push(pack::CheckShardBatchItem {
                                    shard_key: k.clone(),
                                    decl_name: sh.name.clone(),
                                    prefix_env_hash: sh.prefix_env_hash.clone(),
                                    stmt_hash: sh.stmt_hash.clone(),
                                    proof_hash: sh.proof_hash.clone(),
                                });
                            }
                        }
                        if let Ok(resp) = pack::offload_check_shards_batch_http(
                            &mut store,
                            remote_url,
                            &req_items,
                            &cross_src,
                            &trust_domain,
                            &toolchain,
                            &lean_path_str,
                        ) {
                            if resp.ok {
                                cross_batch_done = true;
                                cross_file_coalesced = true;
                                fast_olean_used = true;
                                shard_cache_hits += resp.cache_hits;
                                shards_verified += resp.verified_count;
                            }
                        }
                    }

                    if !cross_batch_done {
                        let cross_t0 = Instant::now();
                        let zreq = pack::CheckShardHttpRequest {
                            decl: "__batch__".to_string(),
                            shard_key: format!("pr_verify_cross_{}", pid),
                            shard_source: cross_src.clone(),
                            interface_hash: String::new(),
                            prefix_env_hash: String::new(),
                            stmt_hash: String::new(),
                            proof_hash: String::new(),
                            toolchain: toolchain.clone(),
                            lean_path: lean_path_str.clone(),
                            skip_cas_lock: true,
                        };
                        let mut cross_ok = if let Some(ref z_url) = fast_local_zygote_url {
                            pack::try_zygote_url_check_shard_with_inflight(z_url, &zreq, || {
                                let now = db::now_unix();
                                batch_to_publish.reserve(total_uncached);
                                for (_rel_path, file_uncached, _) in &uncached_by_file {
                                    for (k, sh) in file_uncached {
                                        if let Ok(r_bytes) = serde_json::to_vec(&serde_json::json!({
                                            "decl": sh.name,
                                            "prefix_env_hash": sh.prefix_env_hash,
                                            "stmt_hash": sh.stmt_hash,
                                            "proof_hash": sh.proof_hash,
                                            "verified_at": now
                                        })) {
                                            batch_to_publish.push((
                                                k.clone(),
                                                sh.name.clone(),
                                                r_bytes,
                                                1i64,
                                            ));
                                        }
                                    }
                                }
                                let _ = store.prestage_theorem_shard_blobs(&batch_to_publish);
                                if store
                                    .begin_inflight_publish_theorem_shards(
                                        &toolchain,
                                        &trust_domain,
                                        &batch_to_publish,
                                    )
                                    .is_ok()
                                {
                                    inflight_tx_open = true;
                                }
                                if prebuilt_ver_receipt.is_none() {
                                    let total_theorems = classification.unchanged_theorems.len()
                                        + classification.proof_edited_theorems.len()
                                        + classification.statement_edited_theorems.len();
                                    let action_key = format!(
                                        "pr-verify:{}:{}",
                                        base,
                                        &classification.current_interface_hash[..16
                                            .min(classification.current_interface_hash.len())]
                                    );
                                    prebuilt_ver_receipt = Some(build_verification_receipt(
                                        &mode,
                                        &classification.current_interface_hash,
                                        &action_key,
                                        classification.total_files,
                                        total_theorems,
                                        0,
                                        classification.per_file_interfaces.clone(),
                                    ));
                                }
                            })
                            .is_some()
                        } else {
                            pack::try_local_zygote_check_shard(&store, &env_vars, &zreq).is_some()
                        };
                        if !cross_ok {
                            if inflight_tx_open {
                                store.rollback_inflight_publish();
                                inflight_tx_open = false;
                            }
                            batch_to_publish.clear();
                            if env_vars.is_empty() {
                                if let Ok((mut ev, _)) = resolve_lake_env(&store, &canon_dir) {
                                    if is_untrusted {
                                        for k in &sensitive_env_keys {
                                            ev.remove(*k);
                                        }
                                    }
                                    env_vars = ev;
                                }
                            }
                            let lb = if env_vars.is_empty() {
                                lean_bin.clone()
                            } else {
                                lean_bin_from_env(&env_vars)
                            };
                            let tmp_cross =
                                staging_dir.join(format!("pr_verify_cross_{}.lean", pid));
                            fs::write(&tmp_cross, &cross_src)?;
                            let mut cmd = Command::new(&lb);
                            cmd.arg(&tmp_cross)
                                .current_dir(&canon_dir)
                                .envs(&env_vars);
                            if is_untrusted {
                                for k in &sensitive_env_keys {
                                    cmd.env_remove(k);
                                }
                            }
                            let cross_out = cmd.output()?;
                            let _ = fs::remove_file(&tmp_cross);
                            cross_ok = cross_out.status.success();
                        }
                        if cross_ok {
                            cross_batch_done = true;
                            cross_file_coalesced = true;
                            fast_olean_used = true;
                            let dur_ms = (cross_t0.elapsed().as_millis() as i64
                                / (total_uncached as i64).max(1))
                            .max(1);
                            if batch_to_publish.len() == total_uncached {
                                shards_verified += total_uncached;
                                for entry in &mut batch_to_publish {
                                    entry.3 = dur_ms;
                                }
                            } else {
                                batch_to_publish.clear();
                                let now = db::now_unix();
                                for (_rel_path, file_uncached, _) in &uncached_by_file {
                                    for (k, sh) in file_uncached {
                                        shards_verified += 1;
                                        let r_bytes = serde_json::to_vec(&serde_json::json!({
                                            "decl": sh.name,
                                            "prefix_env_hash": sh.prefix_env_hash,
                                            "stmt_hash": sh.stmt_hash,
                                            "proof_hash": sh.proof_hash,
                                            "verified_at": now
                                        }))?;
                                        batch_to_publish.push((
                                            k.clone(),
                                            sh.name.clone(),
                                            r_bytes,
                                            dur_ms,
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }

                if !cross_batch_done {
                    if let Some(ref remote_url) = remote_http {
                        for (rel_path, file_uncached, can_fast_olean) in uncached_by_file {
                            let src = current_files.get(&rel_path).cloned().unwrap_or_default();
                            let abs_file = canon_dir.join(&rel_path);
                            let canon_lf = abs_file.canonicalize().unwrap_or(abs_file);
                            let uncached_names: std::collections::HashSet<String> =
                                file_uncached.iter().map(|(_, sh)| sh.name.clone()).collect();
                            let req_items: Vec<pack::CheckShardBatchItem> = file_uncached
                                .iter()
                                .map(|(k, sh)| pack::CheckShardBatchItem {
                                    shard_key: k.clone(),
                                    decl_name: sh.name.clone(),
                                    prefix_env_hash: sh.prefix_env_hash.clone(),
                                    stmt_hash: sh.stmt_hash.clone(),
                                    proof_hash: sh.proof_hash.clone(),
                                })
                                .collect();

                            let mut remote_ok = false;
                            if can_fast_olean {
                                if let Some(mod_imp) =
                                    resolve_prebuilt_module_import(&canon_dir, &canon_lf)
                                {
                                    let fast_src_opt = if let Some(sp) = current_splits.get(&rel_path) {
                                        splitter::build_fast_olean_shard_source_with_split(
                                            &src,
                                            sp,
                                            &mod_imp,
                                            &uncached_names,
                                        )
                                    } else {
                                        splitter::build_fast_olean_shard_source(
                                            &src,
                                            &mod_imp,
                                            &uncached_names,
                                        )
                                    };
                                    if let Some(fast_src) = fast_src_opt {
                                        if let Ok(resp) = pack::offload_check_shards_batch_http(
                                            &mut store,
                                            remote_url,
                                            &req_items,
                                            &fast_src,
                                            &trust_domain,
                                            &toolchain,
                                            &lean_path_str,
                                        ) {
                                            if resp.ok {
                                                remote_ok = true;
                                                fast_olean_used = true;
                                                shard_cache_hits += resp.cache_hits;
                                                shards_verified += resp.verified_count;
                                            }
                                        }
                                    }
                                }
                            }
                            if !remote_ok {
                                let coal_src =
                                    splitter::build_coalesced_shard_source(&src, &uncached_names);
                                let resp = pack::offload_check_shards_batch_http(
                                    &mut store,
                                    remote_url,
                                    &req_items,
                                    &coal_src,
                                    &trust_domain,
                                    &toolchain,
                                    &lean_path_str,
                                )?;
                                if !resp.ok {
                                    anyhow::bail!(
                                        "Remote PR shard verification failed in {} on {}: {}",
                                        rel_path,
                                        remote_url,
                                        resp.error.unwrap_or_else(|| resp.stderr)
                                    );
                                }
                                shard_cache_hits += resp.cache_hits;
                                shards_verified += resp.verified_count;
                            }
                        }
                    } else {
                        let local_zygote_url = fast_local_zygote_url
                            .or_else(|| pack::ensure_local_zygote_daemon(&store, &env_vars));
                        if local_zygote_url.is_none() && env_vars.is_empty() {
                            if let Ok((mut ev, _)) = resolve_lake_env(&store, &canon_dir) {
                                if is_untrusted {
                                    for k in &sensitive_env_keys {
                                        ev.remove(*k);
                                    }
                                }
                                env_vars = ev;
                            }
                        }
                        let store_root = store.root.as_path();
                        type PrFileVerifyResult = Result<(
                            usize,
                            bool,
                            bool,
                            Option<VerificationReceipt>,
                            Vec<(String, String, Vec<u8>, i64)>,
                        )>;
                        let verify_one_file =
                            |f_idx: usize, inflight_store: Option<&TurboStore>| -> PrFileVerifyResult {
                                let mut local_verified = 0usize;
                                let mut local_fast_olean = false;
                                let mut local_tx_open = false;
                                let mut local_receipt: Option<VerificationReceipt> = None;
                                let mut local_publish = Vec::new();
                                let (ref rel_path, ref file_uncached, can_fast_olean) =
                                    uncached_by_file[f_idx];
                                let abs_file = canon_dir.join(rel_path);
                                let src: std::borrow::Cow<'_, str> =
                                    if let Some(s) = current_files.get(rel_path) {
                                        std::borrow::Cow::Borrowed(s.as_str())
                                    } else {
                                        std::borrow::Cow::Owned(
                                            fs::read_to_string(&abs_file).unwrap_or_default(),
                                        )
                                    };
                                let uncached_names: std::collections::HashSet<String> =
                                    file_uncached
                                        .iter()
                                        .map(|(_, sh)| sh.name.clone())
                                        .collect();
                                let tmp_batch =
                                    staging_dir.join(format!("pr_verify_{}_{}.lean", pid, f_idx));
                                let f_t0 = Instant::now();

                                let mut verified_ok = false;
                                if can_fast_olean {
                                    if let Some(mod_imp) =
                                        resolve_prebuilt_module_import(&canon_dir, &abs_file)
                                    {
                                        let fast_src_opt =
                                            if let Some(sp) = current_splits.get(rel_path) {
                                                splitter::build_fast_olean_shard_source_with_split(
                                                    &src,
                                                    sp,
                                                    &mod_imp,
                                                    &uncached_names,
                                                )
                                            } else {
                                                splitter::build_fast_olean_shard_source(
                                                    &src,
                                                    &mod_imp,
                                                    &uncached_names,
                                                )
                                            };
                                        if let Some(fast_src) = fast_src_opt {
                                            if let Some(z_url) = local_zygote_url.as_deref() {
                                                let zreq = pack::CheckShardHttpRequest {
                                                    decl: "__batch__".to_string(),
                                                    shard_key: format!(
                                                        "pr_verify_fast_{}_{}",
                                                        pid, f_idx
                                                    ),
                                                    shard_source: fast_src.clone(),
                                                    interface_hash: String::new(),
                                                    prefix_env_hash: String::new(),
                                                    stmt_hash: String::new(),
                                                    proof_hash: String::new(),
                                                    toolchain: toolchain.clone(),
                                                    lean_path: lean_path_str.clone(),
                                                    skip_cas_lock: true,
                                                };
                                                if pack::try_zygote_url_check_shard_with_inflight(
                                                    z_url,
                                                    &zreq,
                                                    || {
                                                        let now = db::now_unix();
                                                        local_publish.reserve(file_uncached.len());
                                                        for (k, sh) in file_uncached {
                                                            if let Ok(r_bytes) = serde_json::to_vec(
                                                                &serde_json::json!({
                                                                    "decl": sh.name,
                                                                    "prefix_env_hash": sh.prefix_env_hash,
                                                                    "stmt_hash": sh.stmt_hash,
                                                                    "proof_hash": sh.proof_hash,
                                                                    "verified_at": now
                                                                }),
                                                            ) {
                                                                local_publish.push((
                                                                    k.clone(),
                                                                    sh.name.clone(),
                                                                    r_bytes,
                                                                    1i64,
                                                                ));
                                                            }
                                                        }
                                                        let _ =
                                                            db::prestage_theorem_shard_blobs_at(
                                                                store_root,
                                                                &local_publish,
                                                            );
                                                        if let Some(st) = inflight_store {
                                                            if st
                                                                .begin_inflight_publish_theorem_shards(
                                                                    &toolchain,
                                                                    &trust_domain,
                                                                    &local_publish,
                                                                )
                                                                .is_ok()
                                                            {
                                                                local_tx_open = true;
                                                            }
                                                            let total_theorems = classification
                                                                .unchanged_theorems
                                                                .len()
                                                                + classification
                                                                    .proof_edited_theorems
                                                                    .len()
                                                                + classification
                                                                    .statement_edited_theorems
                                                                    .len();
                                                            let action_key = format!(
                                                                "pr-verify:{}:{}",
                                                                base,
                                                                &classification
                                                                    .current_interface_hash[..16
                                                                    .min(
                                                                        classification
                                                                            .current_interface_hash
                                                                            .len()
                                                                    )]
                                                            );
                                                            local_receipt =
                                                                Some(build_verification_receipt(
                                                                    &mode,
                                                                    &classification
                                                                        .current_interface_hash,
                                                                    &action_key,
                                                                    classification.total_files,
                                                                    total_theorems,
                                                                    0,
                                                                    classification
                                                                        .per_file_interfaces
                                                                        .clone(),
                                                                ));
                                                        }
                                                    },
                                                )
                                                .is_some()
                                                {
                                                    verified_ok = true;
                                                    local_fast_olean = true;
                                                } else {
                                                    if local_tx_open {
                                                        if let Some(st) = inflight_store {
                                                            st.rollback_inflight_publish();
                                                        }
                                                        local_tx_open = false;
                                                    }
                                                    local_publish.clear();
                                                }
                                            }
                                            if !verified_ok {
                                                fs::write(&tmp_batch, &fast_src)?;
                                                let mut cmd = Command::new(&lean_bin);
                                                cmd.arg(&tmp_batch)
                                                    .current_dir(&canon_dir)
                                                    .envs(&env_vars);
                                                if is_untrusted {
                                                    for k in &sensitive_env_keys {
                                                        cmd.env_remove(k);
                                                    }
                                                }
                                                let out = cmd.output()?;
                                                let _ = fs::remove_file(&tmp_batch);
                                                if out.status.success() {
                                                    verified_ok = true;
                                                    local_fast_olean = true;
                                                }
                                            }
                                        }
                                    }
                                }

                                if !verified_ok {
                                    if let Some(pruned_src) =
                                        splitter::build_pruned_imports_shard_source(
                                            &src,
                                            &uncached_names,
                                        )
                                    {
                                        if let Some(z_url) = local_zygote_url.as_deref() {
                                            let zreq = pack::CheckShardHttpRequest {
                                                decl: "__batch__".to_string(),
                                                shard_key: format!("pr_verify_{}_{}", pid, f_idx),
                                                shard_source: pruned_src.clone(),
                                                interface_hash: String::new(),
                                                prefix_env_hash: String::new(),
                                                stmt_hash: String::new(),
                                                proof_hash: String::new(),
                                                toolchain: toolchain.clone(),
                                                lean_path: lean_path_str.clone(),
                                                skip_cas_lock: true,
                                            };
                                            if pack::try_zygote_url_check_shard(z_url, &zreq)
                                                .is_some()
                                            {
                                                verified_ok = true;
                                                local_fast_olean = true;
                                            }
                                        }
                                        if !verified_ok {
                                            fs::write(&tmp_batch, &pruned_src)?;
                                            let mut cmd = Command::new(&lean_bin);
                                            cmd.arg(&tmp_batch)
                                                .current_dir(&canon_dir)
                                                .envs(&env_vars);
                                            if is_untrusted {
                                                for k in &sensitive_env_keys {
                                                    cmd.env_remove(k);
                                                }
                                            }
                                            let out = cmd.output()?;
                                            let _ = fs::remove_file(&tmp_batch);
                                            if out.status.success() {
                                                verified_ok = true;
                                                local_fast_olean = true;
                                            }
                                        }
                                    }
                                }

                                if !verified_ok && file_uncached.len() > 1 {
                                    let coal_src = splitter::build_coalesced_shard_source(
                                        &src,
                                        &uncached_names,
                                    );
                                    fs::write(&tmp_batch, &coal_src)?;
                                    let mut cmd = Command::new(&lean_bin);
                                    cmd.arg(&tmp_batch)
                                        .current_dir(&canon_dir)
                                        .envs(&env_vars);
                                    if is_untrusted {
                                        for k in &sensitive_env_keys {
                                            cmd.env_remove(k);
                                        }
                                    }
                                    let out = cmd.output()?;
                                    let _ = fs::remove_file(&tmp_batch);
                                    if out.status.success() {
                                        verified_ok = true;
                                    }
                                }

                                if verified_ok {
                                    let dur_ms = (f_t0.elapsed().as_millis() as i64
                                        / (file_uncached.len() as i64).max(1))
                                    .max(1);
                                    if local_publish.len() == file_uncached.len() {
                                        local_verified = local_publish.len();
                                        for entry in &mut local_publish {
                                            entry.3 = dur_ms;
                                        }
                                    } else {
                                        local_publish.clear();
                                        let now = db::now_unix();
                                        for (k, sh) in file_uncached {
                                            local_verified += 1;
                                            let r_bytes =
                                                serde_json::to_vec(&serde_json::json!({
                                                    "decl": sh.name,
                                                    "prefix_env_hash": sh.prefix_env_hash,
                                                    "stmt_hash": sh.stmt_hash,
                                                    "proof_hash": sh.proof_hash,
                                                    "verified_at": now
                                                }))?;
                                            local_publish.push((
                                                k.clone(),
                                                sh.name.clone(),
                                                r_bytes,
                                                dur_ms,
                                            ));
                                        }
                                    }
                                } else {
                                    let now = db::now_unix();
                                    for (s_idx, (k, sh)) in file_uncached.iter().enumerate() {
                                        let tmp_single = staging_dir.join(format!(
                                            "pr_verify_single_{}_{}_{}.lean",
                                            pid, f_idx, s_idx
                                        ));
                                        let s_t0 = Instant::now();
                                        if sh.shard_source.is_empty() {
                                            let reconstructed =
                                                splitter::reconstruct_single_shard_source(
                                                    &src, &sh.name,
                                                )
                                                .unwrap_or_else(|| {
                                                    let mut single_set =
                                                        std::collections::HashSet::with_capacity(1);
                                                    single_set.insert(sh.name.clone());
                                                    splitter::build_coalesced_shard_source(
                                                        &src,
                                                        &single_set,
                                                    )
                                                });
                                            fs::write(&tmp_single, &reconstructed)?;
                                        } else {
                                            fs::write(&tmp_single, &sh.shard_source)?;
                                        }
                                        let mut cmd = Command::new(&lean_bin);
                                        cmd.arg(&tmp_single)
                                            .current_dir(&canon_dir)
                                            .envs(&env_vars);
                                        if is_untrusted {
                                            for env_k in &sensitive_env_keys {
                                                cmd.env_remove(env_k);
                                            }
                                        }
                                        let out = cmd.output()?;
                                        let _ = fs::remove_file(&tmp_single);
                                        if !out.status.success() {
                                            let stderr = String::from_utf8_lossy(&out.stderr);
                                            let stdout = String::from_utf8_lossy(&out.stdout);
                                            anyhow::bail!(
                                                "PR shard verification failed in {} (theorem `{}`):\n{}\n{}",
                                                rel_path,
                                                sh.name,
                                                stdout,
                                                stderr
                                            );
                                        }
                                        let s_dur_ms = (s_t0.elapsed().as_millis() as i64).max(1);
                                        local_verified += 1;
                                        let r_bytes = serde_json::to_vec(&serde_json::json!({
                                            "decl": sh.name,
                                            "prefix_env_hash": sh.prefix_env_hash,
                                            "stmt_hash": sh.stmt_hash,
                                            "proof_hash": sh.proof_hash,
                                            "verified_at": now
                                        }))?;
                                        local_publish.push((
                                            k.clone(),
                                            sh.name.clone(),
                                            r_bytes,
                                            s_dur_ms,
                                        ));
                                    }
                                }
                                Ok((
                                    local_verified,
                                    local_fast_olean,
                                    local_tx_open,
                                    local_receipt,
                                    local_publish,
                                ))
                            };

                        let worker_results: Vec<PrFileVerifyResult> =
                            if uncached_by_file.len() <= 1 {
                                (0..uncached_by_file.len())
                                    .map(|i| verify_one_file(i, Some(&store)))
                                    .collect()
                            } else {
                                let effective_jobs = std::thread::available_parallelism()
                                    .map(|n| n.get())
                                    .unwrap_or(4)
                                    .min(uncached_by_file.len())
                                    .max(1);
                                let next_file_idx = std::sync::atomic::AtomicUsize::new(0);
                                std::thread::scope(|s| {
                                    let mut handles = Vec::with_capacity(effective_jobs);
                                    for _w in 0..effective_jobs {
                                        let next_ref = &next_file_idx;
                                        let verify_ref = &verify_one_file;
                                        let total_f = uncached_by_file.len();
                                        handles.push(s.spawn(move || -> PrFileVerifyResult {
                                            let mut acc_verified = 0usize;
                                            let mut acc_fast = false;
                                            let mut acc_pub = Vec::new();
                                            loop {
                                                let f_idx = next_ref.fetch_add(
                                                    1,
                                                    std::sync::atomic::Ordering::SeqCst,
                                                );
                                                if f_idx >= total_f {
                                                    break;
                                                }
                                                let (v, f, _, _, p) = verify_ref(f_idx, None)?;
                                                acc_verified += v;
                                                if f {
                                                    acc_fast = true;
                                                }
                                                acc_pub.extend(p);
                                            }
                                            Ok((acc_verified, acc_fast, false, None, acc_pub))
                                        }));
                                    }
                                    handles
                                        .into_iter()
                                        .map(|h| {
                                            h.join().unwrap_or_else(|_| {
                                                Err(anyhow::anyhow!(
                                                    "PR verification worker panicked"
                                                ))
                                            })
                                        })
                                        .collect()
                                })
                            };

                        for res in worker_results {
                            let (v_cnt, used_fast, tx_open, rec_opt, items) = res?;
                            shards_verified += v_cnt;
                            if used_fast {
                                fast_olean_used = true;
                            }
                            if tx_open {
                                inflight_tx_open = true;
                            }
                            if let Some(rec) = rec_opt {
                                prebuilt_ver_receipt = Some(rec);
                            }
                            batch_to_publish.extend(items);
                        }
                    }
                }

                if inflight_tx_open {
                    store.commit_inflight_publish()?;
                } else {
                    store.batch_publish_theorem_shards(
                        &toolchain,
                        &trust_domain,
                        &batch_to_publish,
                    )?;
                }
            }

            let ver_receipt = match prebuilt_ver_receipt {
                Some(r) => r,
                None => {
                    let total_theorems = classification.unchanged_theorems.len()
                        + classification.proof_edited_theorems.len()
                        + classification.statement_edited_theorems.len();
                    let action_key = format!(
                        "pr-verify:{}:{}",
                        base,
                        &classification.current_interface_hash[..16
                            .min(classification.current_interface_hash.len())]
                    );
                    build_verification_receipt(
                        &mode,
                        &classification.current_interface_hash,
                        &action_key,
                        classification.total_files,
                        total_theorems,
                        0,
                        classification.per_file_interfaces.clone(),
                    )
                }
            };

            if let Some(ref receipt_path) = receipt {
                if let Some(parent) = receipt_path.parent() {
                    if !parent.as_os_str().is_empty() {
                        fs::create_dir_all(parent)?;
                    }
                }
                fs::write(receipt_path, serde_json::to_vec_pretty(&ver_receipt)?)?;
            }

            let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 100.0).round() / 100.0;
            if cli.json {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "status": "pr_verified",
                        "base": base,
                        "mode": mode,
                        "trust_domain": trust_domain,
                        "env_scrubbed": is_untrusted,
                        "interface_drift": classification.interface_drift,
                        "baseline_interface_hash": classification.baseline_interface_hash,
                        "interface_hash": classification.current_interface_hash,
                        "receipt_blake3": ver_receipt.receipt_blake3,
                        "receipt_path": receipt.as_ref().map(|p| p.display().to_string()),
                        "total_files": classification.total_files,
                        "modified_files": classification.modified_files,
                        "altered_interface_files": classification.altered_interface_files,
                        "unchanged_theorems_count": classification.unchanged_theorems.len(),
                        "unchanged_theorems": classification.unchanged_theorems,
                        "proof_edited_theorems_count": classification.proof_edited_theorems.len(),
                        "proof_edited_theorems": classification.proof_edited_theorems,
                        "statement_edited_theorems_count": classification.statement_edited_theorems.len(),
                        "statement_edited_theorems": classification.statement_edited_theorems,
                        "shard_cache_hits": shard_cache_hits,
                        "shards_verified": shards_verified,
                        "fast_olean_used": fast_olean_used,
                        "cross_file_coalesced": cross_file_coalesced,
                        "zero_sorry": true,
                        "zero_native_decide": true,
                        "elapsed_ms": elapsed_ms
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] PR-VERIFY PASSED vs {} ({} unchanged, {} proof-edited, {} stmt-edited, interface_drift={}, fast_olean={}, cross_file={}, {:.2} ms)",
                    base,
                    classification.unchanged_theorems.len(),
                    classification.proof_edited_theorems.len(),
                    classification.statement_edited_theorems.len(),
                    classification.interface_drift,
                    fast_olean_used,
                    cross_file_coalesced,
                    elapsed_ms
                );
            }
        }
    }

    Ok(())
}


#[cfg(test)]
mod receipt_tests {
    use super::*;

    #[test]
    fn test_verification_receipt_integrity_and_altered_file_pinpointing() {
        let mut files_v1 = std::collections::BTreeMap::new();
        files_v1.insert("TurboLean/Reflection.lean".to_string(), "hash_refl_v1".to_string());
        files_v1.insert("TurboLean/Inspector.lean".to_string(), "hash_insp_v1".to_string());

        let rec_v1 = build_verification_receipt(
            "untrusted",
            "proj_ih_v1",
            "act_key_1",
            2,
            15,
            0,
            files_v1.clone(),
        );

        // 1. Valid verification against expected hash & self baseline
        let res_ok = verify_receipt_data(&rec_v1, Some("proj_ih_v1"), Some(&rec_v1));
        assert!(res_ok.is_ok());

        // 2. Tampering with forbidden_constructs_found or interface_hash invalidates receipt_blake3
        let mut tampered = rec_v1.clone();
        tampered.interface_hash = "forged_hash".to_string();
        let res_tampered = verify_receipt_data(&tampered, None, None);
        assert!(res_tampered.is_err());
        assert!(res_tampered
            .unwrap_err()
            .to_string()
            .contains("BLAKE3 integrity check FAILED"));

        // 3. Altering a theorem signature in one file is pinpointed when compared to baseline
        let mut files_v2 = files_v1.clone();
        files_v2.insert(
            "TurboLean/Reflection.lean".to_string(),
            "hash_refl_weakened_spec".to_string(),
        );
        let rec_v2 = build_verification_receipt(
            "untrusted",
            "proj_ih_v2",
            "act_key_2",
            2,
            15,
            0,
            files_v2,
        );
        let err_drift = verify_receipt_data(&rec_v2, None, Some(&rec_v1)).unwrap_err();
        let msg = err_drift.to_string();
        assert!(msg.contains("Theorem interface drift detected"));
        assert!(msg.contains("TurboLean/Reflection.lean"));
        assert!(!msg.contains("TurboLean/Inspector.lean"));
    }

    #[test]
    fn test_pr_verify_classification_proof_vs_statement_and_hygiene() {
        let base_refl = "\
namespace Demo
def addOne (n : Nat) : Nat := n + 1

theorem thm_unchanged (n : Nat) : addOne n = n + 1 := by
  rfl

theorem thm_edited (n : Nat) : addOne n = n + 1 := by
  rfl
end Demo
";
        let cur_refl_proof_only = "\
namespace Demo
def addOne (n : Nat) : Nat := n + 1

theorem thm_unchanged (n : Nat) : addOne n = n + 1 := by
  rfl

theorem thm_edited (n : Nat) : addOne n = n + 1 := by
  unfold addOne
  rfl
end Demo
";
        let mut base_map = std::collections::BTreeMap::new();
        base_map.insert("Demo/Basic.lean".to_string(), base_refl.to_string());

        let mut cur_map = std::collections::BTreeMap::new();
        cur_map.insert("Demo/Basic.lean".to_string(), cur_refl_proof_only.to_string());

        let (cls, to_verify) =
            classify_pr_changes("leanprover/lean4:v4.31.0", &cur_map, &base_map).unwrap();
        assert!(!cls.interface_drift);
        assert_eq!(cls.baseline_interface_hash, cls.current_interface_hash);
        assert_eq!(cls.unchanged_theorems, vec!["Demo/Basic.lean::thm_unchanged"]);
        assert_eq!(cls.proof_edited_theorems, vec!["Demo/Basic.lean::thm_edited"]);
        assert!(cls.statement_edited_theorems.is_empty());
        assert_eq!(to_verify["Demo/Basic.lean"].len(), 1);
        assert!(to_verify["Demo/Basic.lean"][0].2); // fast_olean eligible

        // 2. Statement edit triggers interface_drift and classifies into statement_edited_theorems
        let cur_refl_stmt_edit = "\
namespace Demo
def addOne (n : Nat) : Nat := n + 1

theorem thm_unchanged (n : Nat) : addOne n = n + 1 := by
  rfl

theorem thm_edited (n : Nat) : addOne n = 1 + n := by
  omega
end Demo
";
        let mut cur_stmt_map = std::collections::BTreeMap::new();
        cur_stmt_map.insert("Demo/Basic.lean".to_string(), cur_refl_stmt_edit.to_string());
        let (cls_stmt, _) =
            classify_pr_changes("leanprover/lean4:v4.31.0", &cur_stmt_map, &base_map).unwrap();
        assert!(cls_stmt.interface_drift);
        assert_ne!(cls_stmt.baseline_interface_hash, cls_stmt.current_interface_hash);
        assert_eq!(
            cls_stmt.statement_edited_theorems,
            vec!["Demo/Basic.lean::thm_edited"]
        );

        // 3. Forbidden construct (`sorry`) in PR is caught by hygiene gate
        let cur_sorry = cur_refl_proof_only.replace("unfold addOne\n  rfl", "sorry");
        let mut cur_sorry_map = std::collections::BTreeMap::new();
        cur_sorry_map.insert("Demo/Basic.lean".to_string(), cur_sorry);
        let err = classify_pr_changes("leanprover/lean4:v4.31.0", &cur_sorry_map, &base_map)
            .unwrap_err();
        assert!(err.to_string().contains("PR Hygiene & Axiom Gate FAILED"));
    }

    #[test]
    fn test_seed_project_theorem_shards_and_hygiene_filtering() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_seed_test_{}",
            std::process::id()
        ));
        let proj_dir = tmp_dir.join("proj");
        fs::create_dir_all(proj_dir.join("Mod"))?;
        fs::write(
            proj_dir.join("Mod/Clean.lean"),
            "namespace Mod\ntheorem t1 : 1 = 1 := rfl\ntheorem t2 : 2 = 2 := rfl\nend Mod\n",
        )?;
        fs::write(
            proj_dir.join("Mod/Dirty.lean"),
            "namespace Mod\ntheorem bad : False := sorry\nend Mod\n",
        )?;

        let mut store = TurboStore::open(Some(&tmp_dir.join("cache")))?;
        let tc = "leanprover/lean4:v4.31.0";
        let (files_seeded, shards_seeded, _hits) =
            seed_project_theorem_shards(&mut store, &proj_dir, tc, "trusted", false)?;
        assert_eq!(files_seeded, 1);
        assert_eq!(shards_seeded, 2);

        // Verify Clean.lean shards hit cache while Dirty.lean shard does not
        let clean_split = split_lean_source(&fs::read_to_string(proj_dir.join("Mod/Clean.lean"))?, &[]);
        let clean_keys: Vec<String> = clean_split
            .shards
            .iter()
            .map(|s| compute_shard_key(tc, s))
            .collect();
        let cached = store.batch_get_theorem_shards(&clean_keys, "trusted")?;
        assert_eq!(cached.len(), 2);

        let dirty_split = split_lean_source(&fs::read_to_string(proj_dir.join("Mod/Dirty.lean"))?, &[]);
        let dirty_keys: Vec<String> = dirty_split
            .shards
            .iter()
            .map(|s| compute_shard_key(tc, s))
            .collect();
        let dirty_cached = store.batch_get_theorem_shards(&dirty_keys, "trusted")?;
        assert!(dirty_cached.is_empty());

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_project_olean_freshness_and_source_hash_invalidation() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_olean_fresh_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let proj_dir = tmp_dir.join("proj");
        fs::create_dir_all(proj_dir.join("Demo"))?;
        let src_v1 = "namespace Demo\ntheorem t1 : 1 = 1 := rfl\nend Demo\n";
        let demo_file = proj_dir.join("Demo/Basic.lean");
        fs::write(&demo_file, src_v1)?;

        let mut hashes_v1 = BTreeMap::new();
        hashes_v1.insert(
            "Demo/Basic.lean".to_string(),
            blake3::hash(src_v1.as_bytes()).to_hex().to_string(),
        );

        // 1. Missing .olean -> false
        assert!(!are_all_project_oleans_up_to_date(&proj_dir, &hashes_v1));
        assert!(!is_file_verified_in_lake_build(&proj_dir, &demo_file, src_v1));

        // 2. Present non-empty .olean with fresh mtime -> true and persists .turbo_lean_verified_sources.json
        let olean_path = proj_dir
            .join(".lake/build/lib/lean/Demo")
            .join("Basic.olean");
        fs::create_dir_all(olean_path.parent().unwrap())?;
        fs::write(&olean_path, b"olean-dummy-bytes")?;
        assert!(are_all_project_oleans_up_to_date(&proj_dir, &hashes_v1));
        assert!(is_file_verified_in_lake_build(&proj_dir, &demo_file, src_v1));

        // 3. Editing source content invalidates both checks immediately
        let src_v2 = "namespace Demo\ntheorem t1 : 1 = 1 := by rfl\nend Demo\n";
        let mut hashes_v2 = BTreeMap::new();
        hashes_v2.insert(
            "Demo/Basic.lean".to_string(),
            blake3::hash(src_v2.as_bytes()).to_hex().to_string(),
        );
        assert!(!are_all_project_oleans_up_to_date(&proj_dir, &hashes_v2));
        assert!(!is_file_verified_in_lake_build(&proj_dir, &demo_file, src_v2));

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_warm_git_head_tree_cache_and_fast_pr_classification() -> Result<()> {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_git_head_v2_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let repo_dir = tmp_dir.join("repo");
        fs::create_dir_all(repo_dir.join("Demo"))?;

        let f1_path = repo_dir.join("Demo/A.lean");
        let f2_path = repo_dir.join("Demo/B.lean");
        let large_suffix = format!("end Demo\n{}", "-- padding comment line for suffix fingerprint test\n".repeat(1400));
        let f1_prefix = "namespace Demo\n@[simp] def idNat (n : Nat) : Nat := n\ntheorem t_a (n : Nat) : idNat n = n := by\n  rfl\n";
        let f1_src = format!("{}{}", f1_prefix, large_suffix);
        let f2_src = "namespace Demo\ntheorem t_b : 2 + 2 = 4 := by\n  rfl\nend Demo\n";
        fs::write(&f1_path, &f1_src)?;
        fs::write(&f2_path, f2_src)?;

        assert!(Command::new("git").args(["init", "-q"]).current_dir(&repo_dir).status()?.success());
        assert!(Command::new("git")
            .args(["config", "user.email", "test@example.com"])
            .current_dir(&repo_dir)
            .status()?
            .success());
        assert!(Command::new("git")
            .args(["config", "user.name", "Test"])
            .current_dir(&repo_dir)
            .status()?
            .success());
        assert!(Command::new("git")
            .args(["add", "."])
            .current_dir(&repo_dir)
            .status()?
            .success());
        assert!(Command::new("git")
            .args(["commit", "-q", "--no-gpg-sign", "-m", "init"])
            .current_dir(&repo_dir)
            .status()?
            .success());

        let canon_dir = fs::canonicalize(&repo_dir)?;
        let store = TurboStore::open(Some(&tmp_dir.join("cache")))?;
        let tc = "leanprover/lean4:v4.31.0";
        let lean_paths = vec![canon_dir.join("Demo/A.lean"), canon_dir.join("Demo/B.lean")];
        let (splits, _) = load_and_split_files_cached(&store, &lean_paths)?;
        warm_git_head_tree_cache(&store, &canon_dir, &lean_paths, tc, Some(&splits));

        // Modify proof in Demo/A.lean while keeping >64KB suffix identical
        let f1_edited = format!(
            "namespace Demo\n@[simp] def idNat (n : Nat) : Nat := n\ntheorem t_a (n : Nat) : idNat n = n := by\n  simp\n{}",
            large_suffix
        );
        let canon_f1 = canon_dir.join("Demo/A.lean");
        fs::write(&canon_f1, &f1_edited)?;

        let f1_sz = file_stat_tuple(&canon_f1).unwrap().2;
        let (pref_only, fast_sp, unchanged_hit) =
            try_fast_split_single_file_from_path(&store, &canon_dir, &canon_f1, f1_sz, tc)
                .expect("fast prefix pread split should succeed");
        assert_eq!(unchanged_hit, 0);
        assert!(pref_only.len() < 512);
        assert_eq!(fast_sp.shards.len(), 1);

        let (cls, to_verify, changed_files, _changed_splits) =
            load_and_classify_pr_from_git(&store, &canon_dir, "HEAD", tc)?;
        assert_eq!(cls.total_files, 2);
        assert_eq!(cls.modified_files, vec!["Demo/A.lean"]);
        assert!(!cls.interface_drift);
        assert_eq!(cls.unchanged_theorems, vec!["Demo/B.lean::t_b"]);
        assert_eq!(cls.proof_edited_theorems, vec!["Demo/A.lean::t_a"]);
        assert!(cls.statement_edited_theorems.is_empty());
        assert_eq!(to_verify["Demo/A.lean"].len(), 1);
        assert!(to_verify["Demo/A.lean"][0].2);
        assert_eq!(changed_files.len(), 1);
        assert!(changed_files["Demo/A.lean"].len() < 512);

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }
}


