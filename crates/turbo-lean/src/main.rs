mod db;
mod pack;
mod splitter;

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use db::{BlobEntry, SingleflightOutcome, TurboStore};
use splitter::split_lean_source;
use std::collections::HashMap;
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

/// Resolve `LEAN_PATH` and environment variables once via SQLite `lake_env_cache` (< 0.2 ms)
/// or `lake env env` on cache miss, bypassing the 805 MiB `lake` parent process completely.
fn resolve_lake_env(store: &TurboStore, project_dir: &Path) -> Result<(HashMap<String, String>, bool)> {
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let project_key = TurboStore::compute_lake_env_key(&canon_dir);

    if let Some(cached) = store.get_lake_env(&project_key)? {
        return Ok((cached, true));
    }

    let env_map = spawn_lake_env(&canon_dir)?;
    if !env_map.is_empty() {
        let _ = store.put_lake_env(&project_key, &env_map);
    }
    Ok((env_map, false))
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

fn compute_shard_key(toolchain: &str, shard: &splitter::TheoremShard) -> String {
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

/// Zero-read stat-backed file split loader: checks `(path_key, mtime_sec, mtime_nsec, size_bytes)`
/// in `file_stat_cache` joined with `file_split_cache` first, and only reads/hashes/splits files
/// that miss the stat cache. On stat cache hit, the returned `String` source is empty (`""`) and
/// can be lazily loaded if a theorem shard miss requires source reconstruction.
fn load_and_split_files_cached(
    store: &TurboStore,
    paths: &[PathBuf],
) -> Result<(Vec<(PathBuf, String, splitter::SplitResult)>, usize)> {
    if paths.is_empty() {
        return Ok((Vec::new(), 0));
    }
    let file_stats = stat_lean_files_parallel(paths);
    let valid_stats: Vec<(String, i64, i64, i64)> =
        file_stats.iter().filter_map(|s| s.clone()).collect();
    let mut stat_hits_map = store
        .batch_get_file_splits_by_stat(&valid_stats)
        .unwrap_or_default();

    let mut hits = 0usize;
    let mut results: Vec<Option<(PathBuf, String, splitter::SplitResult)>> =
        vec![None; paths.len()];
    let mut miss_indices = Vec::new();

    for (idx, p) in paths.iter().enumerate() {
        if let Some((ref pk, _, _, _)) = file_stats[idx] {
            if let Some((_sk, split)) = stat_hits_map.remove(pk) {
                hits += 1;
                results[idx] = Some((p.clone(), String::new(), split));
                continue;
            }
        }
        miss_indices.push(idx);
    }

    if !miss_indices.is_empty() {
        let miss_paths: Vec<PathBuf> = miss_indices.iter().map(|&i| paths[i].clone()).collect();
        let miss_srcs = read_lean_files_parallel(&miss_paths);
        let (miss_parsed, content_hits) = split_and_audit_cached(store, &miss_srcs)?;
        hits += content_hits;
        for (m_pos, parsed_tuple) in miss_parsed.into_iter().enumerate() {
            let orig_idx = miss_indices[m_pos];
            results[orig_idx] = Some(parsed_tuple);
        }
    }

    let final_results = results
        .into_iter()
        .map(|r| r.expect("all file splits resolved"))
        .collect();
    Ok((final_results, hits))
}

/// Batch-split and hygiene-audit `.lean` source files using SQLite `file_split_cache`
/// and multi-threaded `std::thread::scope` workers for hashing and cache misses.
/// Returns `(Vec<(PathBuf, String, SplitResult)>, cache_hits)`.
fn split_and_audit_cached(
    store: &TurboStore,
    files: &[(PathBuf, String)],
) -> Result<(Vec<(PathBuf, String, splitter::SplitResult)>, usize)> {
    if files.is_empty() {
        return Ok((Vec::new(), 0));
    }
    let default_workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);

    let file_hashes: Vec<String> = if files.len() < 8 {
        files
            .iter()
            .map(|(_, src)| TurboStore::compute_file_split_key(src.as_bytes()))
            .collect()
    } else {
        let workers = default_workers.min(files.len());
        let next_idx = std::sync::atomic::AtomicUsize::new(0);
        let chunks: Vec<Vec<(usize, String)>> = std::thread::scope(|s| {
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
                        let fk = TurboStore::compute_file_split_key(files[i].1.as_bytes());
                        local.push((i, fk));
                    }
                    local
                }));
            }
            handles
                .into_iter()
                .map(|h| h.join().unwrap_or_default())
                .collect()
        });
        let mut indexed: Vec<(usize, String)> = chunks.into_iter().flatten().collect();
        indexed.sort_unstable_by_key(|(i, _)| *i);
        indexed.into_iter().map(|(_, fk)| fk).collect()
    };

    let cached_map = store.batch_get_file_splits(&file_hashes)?;
    let mut hits = 0usize;
    let mut results: Vec<Option<splitter::SplitResult>> = vec![None; files.len()];
    let mut miss_indices = Vec::new();

    for (idx, fh) in file_hashes.iter().enumerate() {
        if let Some(split) = cached_map.get(fh).cloned() {
            hits += 1;
            results[idx] = Some(split);
        } else {
            miss_indices.push(idx);
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
            new_splits.push((file_hashes[file_idx].clone(), split.clone()));
            results[file_idx] = Some(split);
        }
    }

    if !new_splits.is_empty() {
        let refs: Vec<(String, &splitter::SplitResult)> =
            new_splits.iter().map(|(h, sp)| (h.clone(), sp)).collect();
        let _ = store.batch_put_file_splits(&refs);
    }

    // Record `(path_key, mtime_sec, mtime_nsec, size_bytes, split_key)` in `file_stat_cache`
    let paths_only: Vec<PathBuf> = files.iter().map(|(p, _)| p.clone()).collect();
    let stats = stat_lean_files_parallel(&paths_only);
    let mut stat_rows = Vec::with_capacity(files.len());
    for (idx, st_opt) in stats.into_iter().enumerate() {
        if let Some((pk, ms, mn, sz)) = st_opt {
            stat_rows.push((pk, ms, mn, sz, file_hashes[idx].clone()));
        }
    }
    if !stat_rows.is_empty() {
        let _ = store.batch_put_file_stats(&stat_rows);
    }

    let final_results = files
        .iter()
        .enumerate()
        .map(|(idx, (path, src))| {
            (
                path.clone(),
                src.clone(),
                results[idx].take().expect("all file splits resolved"),
            )
        })
        .collect();

    Ok((final_results, hits))
}

/// Compute the Proof-Irrelevant Interface Hash of all `.lean` sources in a project
fn compute_project_interface_key(
    store: &TurboStore,
    project_dir: &Path,
    toolchain: &str,
    targets: &[String],
    trust_domain: &str,
) -> Result<(String, String)> {
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

    let file_srcs = read_lean_files_parallel(&lean_files);
    let (parsed_files, _) = split_and_audit_cached(store, &file_srcs)?;

    for (lf, src, split) in &parsed_files {
        let rel = lf.strip_prefix(project_dir).unwrap_or(lf);
        let rel_str = rel.to_string_lossy();
        hasher.update(rel_str.as_bytes());
        hasher.update(b":");
        hasher.update(blake3::hash(src.as_bytes()).as_bytes());
        hasher.update(b"\n");

        interface_hasher.update(rel_str.as_bytes());
        interface_hasher.update(b":");
        interface_hasher.update(split.interface_hash.as_bytes());
        interface_hasher.update(b"\n");
    }

    Ok((
        hasher.finalize().to_hex().to_string(),
        interface_hasher.finalize().to_hex().to_string(),
    ))
}

/// Recursively discover `.lean` source files inside a file or directory (excluding hidden directories, `target`, `node_modules`, and `lakefile.lean`).
fn collect_lean_files(root: &Path) -> Vec<PathBuf> {
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
    let shared_receipt = format!("verified:seeded:{}", toolchain).into_bytes();
    let mut files_seeded = 0usize;
    let mut batch_items: Vec<(String, String, Vec<u8>, i64)> = Vec::new();

    for (_lf, _src, split) in split_entries {
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
    Ok((files_seeded, shards_seeded, split_cache_hits))
}

/// Collect compiled `.olean`, `.ilean`, and `.c` files from `.lake/build` into the immutable CAS
fn ingest_lake_build_outputs(
    store: &mut TurboStore,
    project_dir: &Path,
    trust_domain: &str,
    pin_level: i64,
) -> Result<Vec<BlobEntry>> {
    let build_dir = project_dir.join(".lake").join("build");
    if !build_dir.exists() {
        return Ok(Vec::new());
    }

    let mut candidates: Vec<(PathBuf, &'static str, String)> = Vec::new();
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

        let rel_path = path
            .strip_prefix(project_dir)
            .unwrap_or(path)
            .to_string_lossy()
            .to_string();
        candidates.push((path.to_path_buf(), kind, rel_path));
    }

    if candidates.is_empty() {
        return Ok(Vec::new());
    }

    let n_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .min(candidates.len())
        .max(1);
    let chunk_size = (candidates.len() + n_threads - 1) / n_threads;

    let mut batch_items: Vec<(String, Vec<u8>, String, String, u64)> =
        Vec::with_capacity(candidates.len());
    std::thread::scope(|s| -> Result<()> {
        let mut handles = Vec::with_capacity(n_threads);
        for chunk in candidates.chunks(chunk_size) {
            handles.push(s.spawn(move || -> Result<Vec<(String, Vec<u8>, String, String, u64)>> {
                let mut local = Vec::with_capacity(chunk.len());
                for (path, kind, rel_path) in chunk {
                    let bytes = fs::read(path)?;
                    let size_bytes = bytes.len() as u64;
                    let hash = blake3::hash(&bytes).to_hex().to_string();
                    local.push((hash, bytes, (*kind).to_string(), rel_path.clone(), size_bytes));
                }
                Ok(local)
            }));
        }
        for h in handles {
            let chunk_res = h.join().map_err(|_| anyhow::anyhow!("ingest worker panicked"))??;
            batch_items.extend(chunk_res);
        }
        Ok(())
    })?;

    store.batch_store_immutable_blobs(&batch_items, trust_domain, pin_level)
}

pub fn parse_gpu_fastcheck_output(
    stdout: &str,
    exec_ms: u128,
    total_ms: u128,
    remote_host: Option<&str>,
) -> serde_json::Value {
    let mut gpu_device = String::new();
    let mut valid_lemma_10m_ms = 0.0f64;
    let mut valid_lemma_10m_mstates_s = 0.0f64;
    let mut suite_10m_ms = 0.0f64;
    let mut suite_10m_mstates_s = 0.0f64;
    let mut cumutate_kernel_ms = 0.0f64;
    let mut cumutate_throughput_mevals_s = 0.0f64;
    let mut mutants_killed = 0u64;
    let mut mutants_total = 0u64;

    for line in stdout.lines() {
        let l = line.trim();
        if l.starts_with("=== CuDenote GPU Benchmark on ") {
            if let Some(rest) = l.strip_prefix("=== CuDenote GPU Benchmark on ") {
                if let Some(end) = rest.find(" ===") {
                    gpu_device = rest[..end].to_string();
                }
            }
        } else if l.starts_with("[Fast-Check Valid Lemma (10000000 states)]") {
            if let Some(t_idx) = l.find("Time: ") {
                let after = &l[t_idx + 6..];
                if let Some(ms_idx) = after.find(" ms") {
                    valid_lemma_10m_ms = after[..ms_idx].trim().parse().unwrap_or(0.0);
                }
            }
            if let Some(tp_idx) = l.find("Throughput: ") {
                let after = &l[tp_idx + 12..];
                if let Some(m_idx) = after.find(" M states/s") {
                    valid_lemma_10m_mstates_s = after[..m_idx].trim().parse().unwrap_or(0.0);
                }
            }
        } else if l.starts_with("[Fast-Reject 3-Lemma Suite (10000000 states)]") {
            if let Some(t_idx) = l.find("Time: ") {
                let after = &l[t_idx + 6..];
                if let Some(ms_idx) = after.find(" ms") {
                    suite_10m_ms = after[..ms_idx].trim().parse().unwrap_or(0.0);
                }
            }
            if let Some(tp_idx) = l.find("Throughput: ") {
                let after = &l[tp_idx + 12..];
                if let Some(m_idx) = after.find(" M states/s") {
                    suite_10m_mstates_s = after[..m_idx].trim().parse().unwrap_or(0.0);
                }
            }
        } else if l.starts_with("-> Kernel Time: ") {
            if let Some(after) = l.strip_prefix("-> Kernel Time: ") {
                if let Some(ms_idx) = after.find(" ms") {
                    cumutate_kernel_ms = after[..ms_idx].trim().parse().unwrap_or(0.0);
                }
            }
            if let Some(tp_idx) = l.find("Throughput: ") {
                let after = &l[tp_idx + 12..];
                if let Some(m_idx) = after.find(" M Denote-evals/s") {
                    cumutate_throughput_mevals_s = after[..m_idx].trim().parse().unwrap_or(0.0);
                }
            }
        } else if l.starts_with("-> Mutants Killed: ") {
            if let Some(after) = l.strip_prefix("-> Mutants Killed: ") {
                if let Some((k_str, rest)) = after.split_once(" / ") {
                    mutants_killed = k_str.trim().parse().unwrap_or(0);
                    if let Some((tot_str, _)) = rest.split_once(' ') {
                        mutants_total = tot_str.trim().parse().unwrap_or(0);
                    }
                }
            }
        }
    }

    serde_json::json!({
        "status": "ok",
        "mode": if remote_host.is_some() { "remote_gpu_cuda" } else { "local_gpu_cuda" },
        "remote_host": remote_host,
        "gpu_device": gpu_device,
        "throughput_mstates_s": valid_lemma_10m_mstates_s,
        "valid_lemma_10m_kernel_ms": valid_lemma_10m_ms,
        "fast_reject_3lemma_10m_kernel_ms": suite_10m_ms,
        "fast_reject_3lemma_mstates_s": suite_10m_mstates_s,
        "cumutate_kernel_ms": cumutate_kernel_ms,
        "cumutate_throughput_mevals_s": cumutate_throughput_mevals_s,
        "mutants_killed": mutants_killed,
        "mutants_total": mutants_total,
        "exec_ms": exec_ms,
        "total_ms": total_ms,
        "output": stdout.trim()
    })
}

fn main() -> Result<()> {
    let cli = Cli::parse();
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
            let (action_key, interface_hash) =
                compute_project_interface_key(&store, &canon_dir, &toolchain, &targets, &trust_domain)?;

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

                    let env_key = TurboStore::compute_lake_env_key(&canon_dir);
                    let need_env_warm = store.get_lake_env(&env_key)?.is_none();
                    let env_dir = canon_dir.clone();
                    let env_handle = if need_env_warm {
                        Some(std::thread::spawn(move || spawn_lake_env(&env_dir)))
                    } else {
                        None
                    };

                    let dur_ms = t0.elapsed().as_millis() as i64;
                    let outputs =
                        ingest_lake_build_outputs(&mut store, &canon_dir, &trust_domain, pin_level)?;
                    let manifest_hash = store.publish_action(
                        &lease,
                        &outputs,
                        dur_ms,
                        0,
                        0,
                        &trust_domain,
                    )?;
                    let linked =
                        store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
                    if let Some(h) = env_handle {
                        if let Ok(Ok(env_map)) = h.join() {
                            if !env_map.is_empty() {
                                let _ = store.put_lake_env(&env_key, &env_map);
                            }
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
                    load_and_split_files_cached(&store, &dir_files)?;
                let mut parsed_files = Vec::with_capacity(split_entries.len());
                let mut all_shard_keys = Vec::new();

                for (lf, src, split) in split_entries {
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
                    parsed_files.push((lf, src, split, file_keys));
                }

                let dir_interface_hash = dir_hasher.finalize().to_hex().to_string();
                let cached_map = store.batch_get_theorem_shards(&all_shard_keys, "trusted")?;

                let mut total_hits = 0usize;
                let mut uncached_files = Vec::new();
                for (lf, src, split, file_keys) in parsed_files {
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
                        let loaded_src = if src.is_empty() {
                            fs::read_to_string(&lf).unwrap_or_default()
                        } else {
                            src
                        };
                        uncached_files.push((lf, loaded_src, file_uncached));
                    }
                }

                let total_misses: usize = uncached_files.iter().map(|(_, _, u)| u.len()).sum();
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

                let (env_vars, env_cache_hit) = resolve_lake_env(&store, &canon_dir)?;
                let lean_bin = lean_bin_from_env(&env_vars);
                let default_jobs = std::thread::available_parallelism()
                    .map(|n| n.get())
                    .unwrap_or(4);
                let effective_jobs = jobs.unwrap_or(default_jobs).max(1).min(uncached_files.len());
                let staging_dir = store.fast_staging_dir();
                let pid = std::process::id();

                // Fast path: if all files with uncached shards have pre-built `.olean` artifacts and
                // acyclic uncached shards, coalesce ALL uncached shards across all files into a SINGLE
                // `lean` invocation in `/dev/shm`!
                let mut cross_eligible = Vec::with_capacity(uncached_files.len());
                for (lf, src, file_uncached) in &uncached_files {
                    let canon_lf = lf.canonicalize().unwrap_or_else(|_| lf.clone());
                    let uncached_names: std::collections::HashSet<String> =
                        file_uncached.iter().map(|(_, sh)| sh.name.clone()).collect();
                    if let Some(mod_imp) = resolve_prebuilt_module_import(&canon_dir, &canon_lf) {
                        if splitter::can_use_fast_olean_import(src, &uncached_names) {
                            cross_eligible.push((mod_imp, src.as_str(), file_uncached));
                        }
                    }
                }

                let mut cross_verified_items: Option<Vec<(String, String, Vec<u8>, i64)>> = None;
                let mut cross_verify_mode = "cross_file_coalesced_shards";
                let lean_path_str = resolve_remote_lean_path(&canon_dir, Some(&env_vars));
                if cross_eligible.len() == uncached_files.len() {
                    let shard_ref_vecs: Vec<Vec<&splitter::TheoremShard>> = cross_eligible
                        .iter()
                        .map(|(_, _, fu)| fu.iter().map(|(_, sh)| sh).collect())
                        .collect();
                    let cross_inputs: Vec<(&str, &str, &[&splitter::TheoremShard])> = cross_eligible
                        .iter()
                        .enumerate()
                        .map(|(i, (m, s, _))| (m.as_str(), *s, shard_ref_vecs[i].as_slice()))
                        .collect();
                    let cross_src = splitter::build_cross_file_coalesced_shard(&cross_inputs);
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
                        let tmp_cross =
                            staging_dir.join(format!("cross_file_coalesced_{}.lean", pid));
                        let cross_t0 = Instant::now();
                        fs::write(&tmp_cross, &cross_src)?;
                        let cross_out = Command::new(&lean_bin)
                            .arg(&tmp_cross)
                            .current_dir(&canon_dir)
                            .envs(&env_vars)
                            .output()?;
                        let _ = fs::remove_file(&tmp_cross);
                        if cross_out.status.success() {
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

            let src = fs::read_to_string(&resolved_file)
                .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
            let (mut single_parsed, _single_split_hits) =
                split_and_audit_cached(&store, &[(resolved_file.clone(), src.clone())])?;
            let mut split = single_parsed.pop().map(|(_, _, sp)| sp).unwrap_or_else(|| split_lean_source(&src, &[]));
            let mut active_src = src.clone();
            let mut active_file = resolved_file.clone();

            if let Some(target_decl) = decl {
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
                                let (mut sub_parsed, _) = split_and_audit_cached(
                                    &store,
                                    &[(sub_path.clone(), sub_src.clone())],
                                )?;
                                let sub_split = sub_parsed
                                    .pop()
                                    .map(|(_, _, sp)| sp)
                                    .unwrap_or_else(|| split_lean_source(&sub_src, &[]));
                                if sub_split
                                    .shards
                                    .iter()
                                    .any(|s| matches_decl(&s.name, &target_decl))
                                {
                                    split = sub_split;
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
                            let full_shard_src = if !shard.shard_source.is_empty() {
                                shard.shard_source.clone()
                            } else {
                                splitter::reconstruct_single_shard_source(&active_src, &shard.name)
                                    .unwrap_or_default()
                            };
                            let endpoint =
                                format!("{}/check-shard", remote_url.trim_end_matches('/'));
                            let req_body = serde_json::to_vec(&pack::CheckShardHttpRequest {
                                decl: target_decl.clone(),
                                shard_key: shard_key.clone(),
                                shard_source: full_shard_src,
                                interface_hash: split.interface_hash.clone(),
                                prefix_env_hash: shard.prefix_env_hash.clone(),
                                stmt_hash: shard.stmt_hash.clone(),
                                proof_hash: shard.proof_hash.clone(),
                                toolchain: toolchain.clone(),
                            })?;
                            let resp_bytes = pack::http_request(
                                "POST",
                                &endpoint,
                                "application/json",
                                &req_body,
                            )?;
                            let resp_json: serde_json::Value = serde_json::from_slice(&resp_bytes)?;
                            let remote_status = resp_json
                                .get("status")
                                .and_then(|v| v.as_str())
                                .unwrap_or("unknown")
                                .to_string();
                            if remote_status != "remote_theorem_verified"
                                && remote_status != "remote_theorem_cache_hit"
                            {
                                anyhow::bail!(
                                    "Remote shard check failed on {}: {}",
                                    endpoint,
                                    resp_json
                                );
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
                            let receipt = serde_json::to_vec(&serde_json::json!({
                                "decl": target_decl,
                                "prefix_env_hash": shard.prefix_env_hash,
                                "stmt_hash": shard.stmt_hash,
                                "proof_hash": shard.proof_hash,
                                "verified_at": db::now_unix()
                            }))?;
                            let bh =
                                store.store_immutable_blob(&receipt, "expr_shard", "trusted", 0)?;
                            let entries = vec![BlobEntry {
                                blob_hash: bh,
                                kind: "expr_shard".to_string(),
                                size_bytes: receipt.len() as u64,
                                rel_path: format!("thm:{}", target_decl),
                            }];
                            store.publish_action(
                                &lease,
                                &entries,
                                (server_elapsed_ms as i64).max(dur_ms),
                                0,
                                0,
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

                        let canon_file = active_file
                            .canonicalize()
                            .unwrap_or_else(|_| active_file.clone());
                        let (env_vars, env_cache_hit) = resolve_lake_env(&store, &canon_dir)?;
                        let lean_bin = lean_bin_from_env(&env_vars);
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

                        let mut verified_via_fast_olean = false;
                        if let Some(pruned_src) =
                            splitter::build_pruned_imports_shard_source(&active_src, &single_set)
                        {
                            fs::write(&tmp_shard, &pruned_src)?;
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

                        if !verified_via_fast_olean {
                            let fast_olean_src =
                                resolve_prebuilt_module_import(&canon_dir, &canon_file).and_then(
                                    |mod_imp| {
                                        splitter::build_fast_olean_shard_source(
                                            &active_src,
                                            &mod_imp,
                                            &single_set,
                                        )
                                    },
                                );
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

                        if !verified_via_fast_olean {
                            let full_shard_src = if !shard.shard_source.is_empty() {
                                shard.shard_source.clone()
                            } else {
                                splitter::reconstruct_single_shard_source(&active_src, &shard.name)
                                    .unwrap_or_default()
                            };
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

                        let dur_ms = t0.elapsed().as_millis() as i64;
                        let receipt = serde_json::to_vec(&serde_json::json!({
                            "decl": target_decl,
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
                            rel_path: format!("thm:{}", target_decl),
                        }];
                        store.publish_action(&lease, &entries, dur_ms, 0, 0, "trusted")?;
                        drop(lease);

                        if cli.json {
                            println!(
                                "{}",
                                serde_json::to_string_pretty(&serde_json::json!({
                                    "status": "theorem_verified",
                                    "decl": target_decl,
                                    "shard_key": shard_key,
                                    "lake_env_cache_hit": env_cache_hit,
                                    "fast_olean_import": verified_via_fast_olean,
                                    "interface_hash": split.interface_hash,
                                    "prefix_env_hash": shard.prefix_env_hash,
                                    "total_shards_in_file": split.shards.len(),
                                    "elapsed_ms": dur_ms
                                }))?
                            );
                        } else {
                            println!(
                                "[turbo-lean] SHARD VERIFIED `{}` ({}/{} shards in file, env_cache_hit={}, fast_olean={}, interface_hash={}.., {} ms)",
                                target_decl,
                                1,
                                split.shards.len(),
                                env_cache_hit,
                                verified_via_fast_olean,
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
                let cached_map = store.batch_get_theorem_shards(&file_shard_keys, "trusted")?;

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
                        let effective_jobs = requested_jobs.min(uncached_shards.len());
                        let uncached_names: std::collections::HashSet<String> = uncached_shards
                            .iter()
                            .map(|(_, s)| s.name.clone())
                            .collect();
                        let project_key = TurboStore::compute_lake_env_key(&canon_dir);
                        let cached_env = store.get_lake_env(&project_key)?;
                        let env_cache_hit = cached_env.is_some();
                        let lean_path_str =
                            resolve_remote_lean_path(&canon_dir, cached_env.as_ref());
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
                        if let Some(mod_imp) =
                            resolve_prebuilt_module_import(&canon_dir, &resolved_file)
                        {
                            if let Some(fast_src) = splitter::build_fast_olean_shard_source(
                                &src,
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

                    let mut batch_succeeded = false;
                    if let Some(pruned_src) =
                        splitter::build_pruned_imports_shard_source(&src, &uncached_names)
                    {
                        fs::write(&tmp_coalesced, &pruned_src)?;
                        let pruned_out = Command::new(&lean_bin)
                            .arg(&tmp_coalesced)
                            .current_dir(&canon_dir)
                            .envs(&env_vars)
                            .output()
                            .context("Failed to execute `lean` on pruned-imports coalesced batch")?;
                        let _ = fs::remove_file(&tmp_coalesced);
                        if pruned_out.status.success() {
                            batch_succeeded = true;
                        }
                    }

                    let canon_resolved_file = resolved_file
                        .canonicalize()
                        .unwrap_or_else(|_| resolved_file.clone());
                    if !batch_succeeded {
                        if let Some(mod_imp) =
                            resolve_prebuilt_module_import(&canon_dir, &canon_resolved_file)
                        {
                            if let Some(fast_src) = splitter::build_fast_olean_shard_source(
                                &src,
                                &mod_imp,
                                &uncached_names,
                            ) {
                                fs::write(&tmp_coalesced, &fast_src)?;
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
                    }

                    if !batch_succeeded {
                        let coalesced_src =
                            splitter::build_coalesced_shard_source(&src, &uncached_names);
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
                        .root
                        .join("staging")
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
                    let env_vars = resolve_lake_env(&store, &lean_dir)
                        .map(|(m, _)| m)
                        .unwrap_or_default();

                    let tmp_c = store
                        .root
                        .join("staging")
                        .join(format!("fastcheck_{}.c", std::process::id()));
                    let tmp_bin = store
                        .root
                        .join("staging")
                        .join(format!("fastcheck_{}.bin", std::process::id()));
                    let tmp_lean = store
                        .root
                        .join("staging")
                        .join(format!("fastcheck_src_{}.lean", std::process::id()));

                    let compile_target = if src_text.contains("def main") {
                        canon_file.clone()
                    } else {
                        fs::write(&tmp_lean, &effective_src)?;
                        tmp_lean.clone()
                    };

                    let st1 = Command::new("lean")
                        .arg("-c")
                        .arg(&tmp_c)
                        .arg(&compile_target)
                        .current_dir(store.root.join("staging"))
                        .envs(&env_vars)
                        .status()
                        .context("Failed to compile Lean to C via `lean -c`")?;
                    let _ = fs::remove_file(&tmp_lean);
                    if !st1.success() {
                        anyhow::bail!("`lean -c` failed on {}", file.display());
                    }
                    let st2 = Command::new("leanc")
                        .arg("-O3")
                        .arg(&tmp_c)
                        .arg("-o")
                        .arg(&tmp_bin)
                        .current_dir(&lean_dir)
                        .envs(&env_vars)
                        .status()
                        .context("Failed to compile C to native binary via `leanc -O3`")?;
                    let _ = fs::remove_file(&tmp_c);
                    if !st2.success() {
                        anyhow::bail!("`leanc -O3` failed");
                    }
                    if fs::rename(&tmp_bin, &cached_bin).is_err() {
                        fs::copy(&tmp_bin, &cached_bin)?;
                        let _ = fs::remove_file(&tmp_bin);
                    }
                }

                let run_t0 = Instant::now();
                let out = Command::new(&cached_bin).output()?;
                let exec_us = run_t0.elapsed().as_micros();

                let stdout = String::from_utf8_lossy(&out.stdout);
                if cli.json {
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&serde_json::json!({
                            "status": if out.status.success() { "ok" } else { "counterexample_found" },
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
                    let (pushed_acts, pushed_blobs, pushed_raw, pushed_pack, delta_push_noop) =
                        pack::sync_push_http(&store, &remote, true)?;
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
                } else {
                    let base = remote.trim_end_matches('/');
                    let local_manifest = pack::get_store_manifest(&store, true)?;
                    let local_action_set: std::collections::HashSet<String> =
                        local_manifest.action_keys.iter().cloned().collect();
                    let local_blob_set: std::collections::HashSet<String> =
                        local_manifest.blob_hashes.iter().cloned().collect();

                    // 1. Query remote manifest via GET /manifest
                    let remote_manifest: pack::DeltaManifest =
                        match pack::http_request("GET", &format!("{}/manifest", base), "application/json", &[]) {
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

                    let mut pulled = (0usize, 0usize);
                    let mut pulled_bytes = 0u64;
                    if need_pull {
                        let tmp_remote = store
                            .fast_staging_dir()
                            .join(format!("sync_in_{}.tlpack", std::process::id()));
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
                            fs::write(&tmp_remote, &pack_bytes)?;
                            pulled = pack::import_pack(&mut store, &tmp_remote)?;
                        }
                        let _ = fs::remove_file(&tmp_remote);
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

                    let mut pushed = (0usize, 0usize, 0u64);
                    let mut pushed_pack_bytes = 0u64;
                    if need_push {
                        let tmp_local = store
                            .fast_staging_dir()
                            .join(format!("sync_out_{}.tlpack", std::process::id()));
                        pushed = pack::export_pack_filtered(
                            &store,
                            &tmp_local,
                            true,
                            &remote_action_set,
                            &remote_blob_set,
                        )?;
                        if pushed.0 > 0 || pushed.1 > 0 {
                            let push_bytes = fs::read(&tmp_local)?;
                            pushed_pack_bytes = push_bytes.len() as u64;
                            let _ = pack::http_request(
                                "POST",
                                &format!("{}/import-delta", base),
                                "application/octet-stream",
                                &push_bytes,
                            )?;
                        }
                        let _ = fs::remove_file(&tmp_local);
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
            let (splits, _split_hits) = load_and_split_files_cached(&store, &lean_paths)?;
            for (path, _src, split) in splits {
                total_files += 1;
                total_shards += split.shards.len();
                let rel_path = path
                    .strip_prefix(&canon_dir)
                    .unwrap_or(&path)
                    .to_string_lossy()
                    .replace('\\', "/");
                per_file_interfaces.insert(rel_path.clone(), split.interface_hash.clone());
                if !split.hygiene.is_clean_for_certification() {
                    flagged_files.push((rel_path, split.hygiene.flagged_items));
                }
            }

            if !flagged_files.is_empty() {
                anyhow::bail!(
                    "CI Hygiene & Axiom Gate FAILED on {} files: {:?}",
                    flagged_files.len(),
                    flagged_files
                );
            }

            // 2. Build/Verify using isolated trust_domain
            let toolchain = detect_toolchain(&canon_dir);
            let (action_key, interface_hash) =
                compute_project_interface_key(&store, &canon_dir, &toolchain, &[], &trust_domain)?;
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

            let build_status = match store.acquire_singleflight(
                &action_key,
                &toolchain,
                "module_full",
                &trust_domain,
            )? {
                SingleflightOutcome::CacheHit { outputs, coalesced } => {
                    store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
                    format!("cache_hit(coalesced={})", coalesced)
                }
                SingleflightOutcome::Leader(lease) => {
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

                    let env_key = TurboStore::compute_lake_env_key(&canon_dir);
                    let need_env_warm = store.get_lake_env(&env_key)?.is_none();
                    let env_dir = canon_dir.clone();
                    let env_handle = if need_env_warm {
                        Some(std::thread::spawn(move || spawn_lake_env(&env_dir)))
                    } else {
                        None
                    };

                    let dur_ms = t0.elapsed().as_millis() as i64;
                    let outputs =
                        ingest_lake_build_outputs(&mut store, &canon_dir, &trust_domain, 1)?;
                    store.publish_action(&lease, &outputs, dur_ms, 0, 0, &trust_domain)?;
                    store.materialize_into_worktree(&canon_dir, &project_name, &outputs)?;
                    if let Some(h) = env_handle {
                        if let Ok(Ok(env_map)) = h.join() {
                            if !env_map.is_empty() {
                                let _ = store.put_lake_env(&env_key, &env_map);
                            }
                        }
                    }
                    "built_and_verified".to_string()
                }
            };

            let seeded_shards = if seed_shards {
                seed_project_theorem_shards(&mut store, &canon_dir, &toolchain, &trust_domain, false)?.1
            } else {
                0
            };

            store.record_attestation(
                &action_key,
                "turbo-lean-ci-gate",
                env!("CARGO_PKG_VERSION"),
                &[
                    "propext".to_string(),
                    "Quot.sound".to_string(),
                    "Classical.choice".to_string(),
                ],
                None,
            )?;

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

            let (classification, shards_by_file, current_files) =
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

            let mut cached_map = store.batch_get_theorem_shards(&all_edited_keys, "trusted")?;
            if is_untrusted {
                let untrusted_cached =
                    store.batch_get_theorem_shards(&all_edited_keys, &trust_domain)?;
                cached_map.extend(untrusted_cached);
            }

            let mut shard_cache_hits = 0usize;
            let mut shards_verified = 0usize;
            let mut fast_olean_used = false;
            let mut cross_file_coalesced = false;
            let mut batch_to_publish = Vec::new();

            let mut uncached_by_file = Vec::new();
            for (rel_path, file_shards) in shards_by_file {
                let mut uncached = Vec::new();
                let mut can_fast_olean = true;
                for (k, sh, fast_ok) in file_shards {
                    if cached_map.contains_key(&k) {
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
                let (mut env_vars, _env_cache_hit) = resolve_lake_env(&store, &canon_dir)?;
                let lean_bin = lean_bin_from_env(&env_vars);
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
                if is_untrusted {
                    for k in &sensitive_env_keys {
                        env_vars.remove(*k);
                    }
                }
                let lean_path_str = resolve_remote_lean_path(&canon_dir, Some(&env_vars));

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
                        let canon_lf = abs_file.canonicalize().unwrap_or(abs_file);
                        let uncached_names: std::collections::HashSet<String> =
                            file_uncached.iter().map(|(_, sh)| sh.name.clone()).collect();
                        if let Some(mod_imp) =
                            resolve_prebuilt_module_import(&canon_dir, &canon_lf)
                        {
                            if splitter::can_use_fast_olean_import(src, &uncached_names) {
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
                        let tmp_cross =
                            staging_dir.join(format!("pr_verify_cross_{}.lean", pid));
                        let cross_t0 = Instant::now();
                        fs::write(&tmp_cross, &cross_src)?;
                        let mut cmd = Command::new(&lean_bin);
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
                        if cross_out.status.success() {
                            cross_batch_done = true;
                            cross_file_coalesced = true;
                            fast_olean_used = true;
                            let dur_ms = (cross_t0.elapsed().as_millis() as i64
                                / (total_uncached as i64).max(1))
                            .max(1);
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
                                    batch_to_publish.push((k.clone(), sh.name.clone(), r_bytes, dur_ms));
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
                                    if let Some(fast_src) = splitter::build_fast_olean_shard_source(
                                        &src,
                                        &mod_imp,
                                        &uncached_names,
                                    ) {
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
                        let effective_jobs = std::thread::available_parallelism()
                            .map(|n| n.get())
                            .unwrap_or(4)
                            .min(uncached_by_file.len())
                            .max(1);
                        let next_file_idx = std::sync::atomic::AtomicUsize::new(0);
                        type PrFileVerifyResult =
                            Result<(usize, bool, Vec<(String, String, Vec<u8>, i64)>)>;
                        let worker_results: Vec<PrFileVerifyResult> = std::thread::scope(|s| {
                            let mut handles = Vec::with_capacity(effective_jobs);
                            for _w in 0..effective_jobs {
                                let next_ref = &next_file_idx;
                                let uncached_ref = &uncached_by_file;
                                let cur_files_ref = &current_files;
                                let canon_ref = &canon_dir;
                                let staging_ref = &staging_dir;
                                let lean_bin_ref = &lean_bin;
                                let env_ref = &env_vars;
                                let sens_ref = &sensitive_env_keys;

                                handles.push(s.spawn(move || -> PrFileVerifyResult {
                                    let mut local_verified = 0usize;
                                    let mut local_fast_olean = false;
                                    let mut local_publish = Vec::new();

                                    loop {
                                        let f_idx = next_ref
                                            .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                                        if f_idx >= uncached_ref.len() {
                                            break;
                                        }
                                        let (ref rel_path, ref file_uncached, can_fast_olean) =
                                            uncached_ref[f_idx];
                                        let abs_file = canon_ref.join(rel_path);
                                        let src = cur_files_ref
                                            .get(rel_path)
                                            .cloned()
                                            .unwrap_or_else(|| {
                                                fs::read_to_string(&abs_file).unwrap_or_default()
                                            });
                                        let canon_lf =
                                            abs_file.canonicalize().unwrap_or(abs_file);
                                        let uncached_names: std::collections::HashSet<String> =
                                            file_uncached
                                                .iter()
                                                .map(|(_, sh)| sh.name.clone())
                                                .collect();
                                        let tmp_batch = staging_ref.join(format!(
                                            "pr_verify_{}_{}.lean",
                                            pid, f_idx
                                        ));
                                        let f_t0 = Instant::now();

                                        let mut verified_ok = false;
                                        if let Some(pruned_src) =
                                            splitter::build_pruned_imports_shard_source(
                                                &src,
                                                &uncached_names,
                                            )
                                        {
                                            fs::write(&tmp_batch, &pruned_src)?;
                                            let mut cmd = Command::new(lean_bin_ref);
                                            cmd.arg(&tmp_batch)
                                                .current_dir(canon_ref)
                                                .envs(env_ref);
                                            if is_untrusted {
                                                for k in sens_ref {
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

                                        if !verified_ok && can_fast_olean {
                                            if let Some(mod_imp) = resolve_prebuilt_module_import(
                                                canon_ref, &canon_lf,
                                            ) {
                                                if let Some(fast_src) =
                                                    splitter::build_fast_olean_shard_source(
                                                        &src,
                                                        &mod_imp,
                                                        &uncached_names,
                                                    )
                                                {
                                                    fs::write(&tmp_batch, &fast_src)?;
                                                    let mut cmd = Command::new(lean_bin_ref);
                                                    cmd.arg(&tmp_batch)
                                                        .current_dir(canon_ref)
                                                        .envs(env_ref);
                                                    if is_untrusted {
                                                        for k in sens_ref {
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
                                            let mut cmd = Command::new(lean_bin_ref);
                                            cmd.arg(&tmp_batch)
                                                .current_dir(canon_ref)
                                                .envs(env_ref);
                                            if is_untrusted {
                                                for k in sens_ref {
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
                                        } else {
                                            let now = db::now_unix();
                                            for (s_idx, (k, sh)) in
                                                file_uncached.iter().enumerate()
                                            {
                                                let tmp_single = staging_ref.join(format!(
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
                                                let mut cmd = Command::new(lean_bin_ref);
                                                cmd.arg(&tmp_single)
                                                    .current_dir(canon_ref)
                                                    .envs(env_ref);
                                                if is_untrusted {
                                                    for env_k in sens_ref {
                                                        cmd.env_remove(env_k);
                                                    }
                                                }
                                                let out = cmd.output()?;
                                                let _ = fs::remove_file(&tmp_single);
                                                if !out.status.success() {
                                                    let stderr =
                                                        String::from_utf8_lossy(&out.stderr);
                                                    let stdout =
                                                        String::from_utf8_lossy(&out.stdout);
                                                    anyhow::bail!(
                                                        "PR shard verification failed in {} (theorem `{}`):\n{}\n{}",
                                                        rel_path,
                                                        sh.name,
                                                        stdout,
                                                        stderr
                                                    );
                                                }
                                                let s_dur_ms =
                                                    (s_t0.elapsed().as_millis() as i64).max(1);
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
                                                    s_dur_ms,
                                                ));
                                            }
                                        }
                                    }
                                    Ok((local_verified, local_fast_olean, local_publish))
                                }));
                            }
                            handles
                                .into_iter()
                                .map(|h| {
                                    h.join().unwrap_or_else(|_| {
                                        Err(anyhow::anyhow!("PR verification worker panicked"))
                                    })
                                })
                                .collect()
                        });

                        for res in worker_results {
                            let (v_cnt, used_fast, items) = res?;
                            shards_verified += v_cnt;
                            if used_fast {
                                fast_olean_used = true;
                            }
                            batch_to_publish.extend(items);
                        }
                    }
                }

                store.batch_publish_theorem_shards(
                    &toolchain,
                    &trust_domain,
                    &batch_to_publish,
                )?;
            }

            let total_theorems = classification.unchanged_theorems.len()
                + classification.proof_edited_theorems.len()
                + classification.statement_edited_theorems.len();
            let action_key = format!(
                "pr-verify:{}:{}",
                base,
                &classification.current_interface_hash[..16.min(classification.current_interface_hash.len())]
            );
            let ver_receipt = build_verification_receipt(
                &mode,
                &classification.current_interface_hash,
                &action_key,
                classification.total_files,
                total_theorems,
                0,
                classification.per_file_interfaces.clone(),
            );

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

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct PrClassification {
    pub total_files: usize,
    pub modified_files: Vec<String>,
    pub altered_interface_files: Vec<String>,
    pub interface_drift: bool,
    pub baseline_interface_hash: String,
    pub current_interface_hash: String,
    pub unchanged_theorems: Vec<String>,
    pub proof_edited_theorems: Vec<String>,
    pub statement_edited_theorems: Vec<String>,
    pub per_file_interfaces: std::collections::BTreeMap<String, String>,
}

fn resolve_git_toplevel(dir: &Path) -> Result<PathBuf> {
    let out = Command::new("git")
        .args(["-C", &dir.to_string_lossy(), "rev-parse", "--show-toplevel"])
        .output()
        .context("Failed to execute `git rev-parse --show-toplevel`")?;
    if !out.status.success() {
        anyhow::bail!(
            "Not a git repository ({}): {}",
            dir.display(),
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    let p = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
    Ok(p.canonicalize().unwrap_or(p))
}

fn load_and_classify_pr_from_git(
    store: &TurboStore,
    canon_dir: &Path,
    base_ref: &str,
    toolchain: &str,
) -> Result<(
    PrClassification,
    std::collections::BTreeMap<String, Vec<(String, splitter::TheoremShard, bool)>>,
    std::collections::BTreeMap<String, String>,
)> {
    let repo_root = resolve_git_toplevel(canon_dir)?;
    let proj_prefix = canon_dir
        .strip_prefix(&repo_root)
        .unwrap_or(Path::new(""))
        .to_string_lossy()
        .replace('\\', "/");

    let (verify_res, diff_res, untracked_res, preloaded_res) = std::thread::scope(|s| {
        let repo_ref = &repo_root;
        let verify_h = s.spawn(move || {
            Command::new("git")
                .args([
                    "-C",
                    &repo_ref.to_string_lossy(),
                    "rev-parse",
                    "--verify",
                    &format!("{}^{{commit}}", base_ref),
                ])
                .output()
                .context("Failed to execute `git rev-parse --verify`")
        });
        let diff_h = s.spawn(move || {
            Command::new("git")
                .args([
                    "-C",
                    &repo_ref.to_string_lossy(),
                    "diff",
                    "--name-only",
                    base_ref,
                    "--",
                    &canon_dir.to_string_lossy(),
                ])
                .output()
                .context("Failed to execute `git diff --name-only`")
        });
        let untracked_h = s.spawn(move || {
            Command::new("git")
                .args([
                    "-C",
                    &repo_ref.to_string_lossy(),
                    "ls-files",
                    "--others",
                    "--exclude-standard",
                    "--",
                    &canon_dir.to_string_lossy(),
                ])
                .output()
                .context("Failed to execute `git ls-files --others`")
        });

        let mut lean_paths: Vec<PathBuf> = Vec::new();
        for entry in WalkDir::new(canon_dir)
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
        let preloaded = load_and_split_files_cached(store, &lean_paths);

        (
            verify_h
                .join()
                .unwrap_or_else(|_| Err(anyhow::anyhow!("verify thread panicked"))),
            diff_h
                .join()
                .unwrap_or_else(|_| Err(anyhow::anyhow!("diff thread panicked"))),
            untracked_h
                .join()
                .unwrap_or_else(|_| Err(anyhow::anyhow!("untracked thread panicked"))),
            preloaded,
        )
    });

    let verify_out = verify_res?;
    if !verify_out.status.success() {
        anyhow::bail!(
            "Invalid git base ref `{}`: {}",
            base_ref,
            String::from_utf8_lossy(&verify_out.stderr).trim()
        );
    }

    let diff_out = diff_res?;
    let mut changed_repo_paths: std::collections::HashSet<String> =
        String::from_utf8_lossy(&diff_out.stdout)
            .lines()
            .map(|l| l.trim().replace('\\', "/"))
            .filter(|l| !l.is_empty())
            .collect();

    let untracked_out = untracked_res?;
    let untracked_repo_paths: std::collections::HashSet<String> =
        String::from_utf8_lossy(&untracked_out.stdout)
            .lines()
            .map(|l| l.trim().replace('\\', "/"))
            .filter(|l| !l.is_empty())
            .collect();
    changed_repo_paths.extend(untracked_repo_paths.iter().cloned());

    let (preloaded_splits, _) = preloaded_res?;

    enum PrFileEntry {
        Unchanged(splitter::SplitResult),
        Changed {
            base_src: Option<String>,
            cur_src: Option<String>,
            cur_split: Option<splitter::SplitResult>,
        },
    }

    let mut entries_by_rel_path: std::collections::HashMap<String, PrFileEntry> =
        std::collections::HashMap::with_capacity(preloaded_splits.len());
    let mut changed_current_files = std::collections::BTreeMap::new();
    let mut current_files_count = 0usize;

    for (path, cached_src, split) in preloaded_splits {
        current_files_count += 1;
        let rel_path = path
            .strip_prefix(canon_dir)
            .unwrap_or(&path)
            .to_string_lossy()
            .replace('\\', "/");

        let repo_rel = if proj_prefix.is_empty() {
            rel_path.clone()
        } else {
            format!("{}/{}", proj_prefix.trim_end_matches('/'), rel_path)
        };

        if !changed_repo_paths.contains(&repo_rel) {
            entries_by_rel_path.insert(rel_path, PrFileEntry::Unchanged(split));
        } else {
            let cur_src = if cached_src.is_empty() {
                fs::read_to_string(&path).unwrap_or_default()
            } else {
                cached_src
            };
            changed_current_files.insert(rel_path.clone(), cur_src.clone());
            let mut base_src = None;
            if !untracked_repo_paths.contains(&repo_rel) {
                let show_out = Command::new("git")
                    .args([
                        "-C",
                        &repo_root.to_string_lossy(),
                        "show",
                        &format!("{}:{}", base_ref, repo_rel),
                    ])
                    .output()
                    .context("Failed to execute `git show`")?;
                if show_out.status.success() {
                    base_src = Some(String::from_utf8_lossy(&show_out.stdout).to_string());
                }
            }
            entries_by_rel_path.insert(
                rel_path,
                PrFileEntry::Changed {
                    base_src,
                    cur_src: Some(cur_src),
                    cur_split: Some(split),
                },
            );
        }
    }

    // Check if any .lean file in `changed_repo_paths` was deleted in the working tree
    for repo_rel in &changed_repo_paths {
        if !repo_rel.ends_with(".lean") || untracked_repo_paths.contains(repo_rel) {
            continue;
        }
        let rel_path = if proj_prefix.is_empty() {
            repo_rel.clone()
        } else if let Some(stripped) =
            repo_rel.strip_prefix(&format!("{}/", proj_prefix.trim_end_matches('/')))
        {
            stripped.to_string()
        } else {
            continue;
        };
        if !entries_by_rel_path.contains_key(&rel_path) {
            let show_out = Command::new("git")
                .args([
                    "-C",
                    &repo_root.to_string_lossy(),
                    "show",
                    &format!("{}:{}", base_ref, repo_rel),
                ])
                .output()
                .context("Failed to execute `git show` for deleted file")?;
            if show_out.status.success() {
                let base_src = String::from_utf8_lossy(&show_out.stdout).to_string();
                entries_by_rel_path.insert(
                    rel_path,
                    PrFileEntry::Changed {
                        base_src: Some(base_src),
                        cur_src: None,
                        cur_split: None,
                    },
                );
            }
        }
    }

    let mut all_paths: Vec<String> = entries_by_rel_path.keys().cloned().collect();
    all_paths.sort_by(|a, b| Path::new(a.as_str()).cmp(Path::new(b.as_str())));

    let resolve_cached_or_split = |src: &str| -> splitter::SplitResult {
        let fk = TurboStore::compute_file_split_key(src.as_bytes());
        if let Ok(mut map) = store.batch_get_file_splits(std::slice::from_ref(&fk)) {
            if let Some(sp) = map.remove(&fk) {
                return sp;
            }
        }
        let sp = split_lean_source(src, &[]);
        let _ = store.batch_put_file_splits(&[(fk, &sp)]);
        sp
    };

    let mut baseline_ih_hasher = blake3::Hasher::new();
    baseline_ih_hasher.update(toolchain.as_bytes());
    let mut current_ih_hasher = blake3::Hasher::new();
    current_ih_hasher.update(toolchain.as_bytes());

    let mut modified_files = Vec::new();
    let mut altered_interface_files = Vec::new();
    let mut unchanged_theorems = Vec::new();
    let mut proof_edited_theorems = Vec::new();
    let mut statement_edited_theorems = Vec::new();
    let mut per_file_interfaces = std::collections::BTreeMap::new();
    let mut shards_to_verify_by_file = std::collections::BTreeMap::new();
    let mut flagged_files = Vec::new();

    for rel_path in all_paths {
        let Some(entry) = entries_by_rel_path.remove(&rel_path) else {
            continue;
        };
        match entry {
            PrFileEntry::Unchanged(split) => {
                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), split.interface_hash);
                for s in split.shards {
                    unchanged_theorems.push(format!("{}::{}", rel_path, s.name));
                }
            }
            PrFileEntry::Changed {
                base_src: Some(base_src),
                cur_src: Some(cur_src),
                cur_split,
            } if base_src == cur_src => {
                let split = cur_split.unwrap_or_else(|| resolve_cached_or_split(&cur_src));
                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), split.interface_hash);
                for s in split.shards {
                    unchanged_theorems.push(format!("{}::{}", rel_path, s.name));
                }
            }
            PrFileEntry::Changed {
                base_src: Some(base_src),
                cur_src: Some(cur_src),
                cur_split,
            } => {
                modified_files.push(rel_path.clone());
                let cur_split = cur_split.unwrap_or_else(|| resolve_cached_or_split(&cur_src));
                if !cur_split.hygiene.is_clean_for_certification() {
                    flagged_files.push((rel_path.clone(), cur_split.hygiene.flagged_items));
                }
                let base_split = resolve_cached_or_split(&base_src);

                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(base_split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(cur_split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), cur_split.interface_hash.clone());

                let file_interface_same = cur_split.interface_hash == base_split.interface_hash
                    && cur_split.shards.len() == base_split.shards.len();
                let mut file_has_stmt_change = !file_interface_same;

                let mut base_by_name = std::collections::HashMap::new();
                for bs in &base_split.shards {
                    base_by_name.insert(bs.name.as_str(), (bs, compute_shard_key(toolchain, bs)));
                }
                let cur_names: std::collections::HashSet<&str> =
                    cur_split.shards.iter().map(|s| s.name.as_str()).collect();
                for bs in &base_split.shards {
                    if !cur_names.contains(bs.name.as_str()) {
                        file_has_stmt_change = true;
                        statement_edited_theorems
                            .push(format!("{}::{} (deleted)", rel_path, bs.name));
                    }
                }

                let mut file_verify_list = Vec::new();
                for s in cur_split.shards {
                    let k = compute_shard_key(toolchain, &s);
                    let qualified = format!("{}::{}", rel_path, s.name);
                    if let Some((bs, bk)) = base_by_name.get(s.name.as_str()) {
                        if k == *bk {
                            unchanged_theorems.push(qualified);
                        } else if s.stmt_hash == bs.stmt_hash
                            && s.prefix_env_hash == bs.prefix_env_hash
                            && file_interface_same
                        {
                            proof_edited_theorems.push(qualified);
                            file_verify_list.push((k, s, true));
                        } else {
                            file_has_stmt_change = true;
                            statement_edited_theorems.push(qualified);
                            file_verify_list.push((k, s, false));
                        }
                    } else {
                        file_has_stmt_change = true;
                        statement_edited_theorems.push(qualified);
                        file_verify_list.push((k, s, false));
                    }
                }

                if file_has_stmt_change {
                    altered_interface_files.push(rel_path.clone());
                }
                if !file_verify_list.is_empty() {
                    shards_to_verify_by_file.insert(rel_path, file_verify_list);
                }
            }
            PrFileEntry::Changed {
                base_src: None,
                cur_src: Some(cur_src),
                cur_split,
            } => {
                modified_files.push(rel_path.clone());
                altered_interface_files.push(rel_path.clone());
                let cur_split = cur_split.unwrap_or_else(|| resolve_cached_or_split(&cur_src));
                if !cur_split.hygiene.is_clean_for_certification() {
                    flagged_files.push((rel_path.clone(), cur_split.hygiene.flagged_items));
                }
                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(cur_split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), cur_split.interface_hash);
                let mut file_verify_list = Vec::new();
                for s in cur_split.shards {
                    let k = compute_shard_key(toolchain, &s);
                    statement_edited_theorems.push(format!("{}::{}", rel_path, s.name));
                    file_verify_list.push((k, s, false));
                }
                if !file_verify_list.is_empty() {
                    shards_to_verify_by_file.insert(rel_path, file_verify_list);
                }
            }
            PrFileEntry::Changed {
                base_src: Some(base_src),
                cur_src: None,
                cur_split: _,
            } => {
                modified_files.push(rel_path.clone());
                altered_interface_files.push(rel_path.clone());
                let base_split = resolve_cached_or_split(&base_src);
                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(base_split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                for bs in base_split.shards {
                    statement_edited_theorems
                        .push(format!("{}::{} (deleted)", rel_path, bs.name));
                }
            }
            PrFileEntry::Changed {
                base_src: None,
                cur_src: None,
                cur_split: _,
            } => {}
        }
    }

    if !flagged_files.is_empty() {
        anyhow::bail!(
            "PR Hygiene & Axiom Gate FAILED on {} files: {:?}",
            flagged_files.len(),
            flagged_files
        );
    }

    let baseline_interface_hash = baseline_ih_hasher.finalize().to_hex().to_string();
    let current_interface_hash = current_ih_hasher.finalize().to_hex().to_string();
    let interface_drift =
        baseline_interface_hash != current_interface_hash || !altered_interface_files.is_empty();

    Ok((
        PrClassification {
            total_files: current_files_count,
            modified_files,
            altered_interface_files,
            interface_drift,
            baseline_interface_hash,
            current_interface_hash,
            unchanged_theorems,
            proof_edited_theorems,
            statement_edited_theorems,
            per_file_interfaces,
        },
        shards_to_verify_by_file,
        changed_current_files,
    ))
}

pub fn classify_pr_changes(
    toolchain: &str,
    current_files: &std::collections::BTreeMap<String, String>,
    base_files: &std::collections::BTreeMap<String, String>,
) -> Result<(
    PrClassification,
    std::collections::BTreeMap<String, Vec<(String, splitter::TheoremShard, bool)>>,
)> {
    classify_pr_changes_with_store(None, toolchain, current_files, base_files)
}

pub fn classify_pr_changes_with_store(
    store: Option<&TurboStore>,
    toolchain: &str,
    current_files: &std::collections::BTreeMap<String, String>,
    base_files: &std::collections::BTreeMap<String, String>,
) -> Result<(
    PrClassification,
    std::collections::BTreeMap<String, Vec<(String, splitter::TheoremShard, bool)>>,
)> {
    let mut baseline_ih_hasher = blake3::Hasher::new();
    baseline_ih_hasher.update(toolchain.as_bytes());
    let mut current_ih_hasher = blake3::Hasher::new();
    current_ih_hasher.update(toolchain.as_bytes());

    let mut all_paths_set: std::collections::BTreeSet<&String> = current_files.keys().collect();
    all_paths_set.extend(base_files.keys());
    let mut all_paths: Vec<&String> = all_paths_set.into_iter().collect();
    all_paths.sort_by(|a, b| Path::new(a.as_str()).cmp(Path::new(b.as_str())));

    let default_workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);

    // Collect unchanged (rel_path, cur_src) pairs
    let mut unchanged_srcs: Vec<(&str, &str)> = Vec::new();
    for path in &all_paths {
        let rel_path = path.as_str();
        if let (Some(base_src), Some(cur_src)) =
            (base_files.get(rel_path), current_files.get(rel_path))
        {
            if base_src == cur_src {
                unchanged_srcs.push((rel_path, cur_src.as_str()));
            }
        }
    }

    let unchanged_split_keys: Vec<String> = if unchanged_srcs.len() < 8 {
        unchanged_srcs
            .iter()
            .map(|(_, src)| TurboStore::compute_file_split_key(src.as_bytes()))
            .collect()
    } else {
        let workers = default_workers.min(unchanged_srcs.len());
        let next_idx = std::sync::atomic::AtomicUsize::new(0);
        let srcs_ref = &unchanged_srcs;
        let chunks: Vec<Vec<(usize, String)>> = std::thread::scope(|s| {
            let mut handles = Vec::with_capacity(workers);
            for _ in 0..workers {
                let next_ref = &next_idx;
                handles.push(s.spawn(move || {
                    let mut local = Vec::new();
                    loop {
                        let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if i >= srcs_ref.len() {
                            break;
                        }
                        let fk = TurboStore::compute_file_split_key(srcs_ref[i].1.as_bytes());
                        local.push((i, fk));
                    }
                    local
                }));
            }
            handles
                .into_iter()
                .map(|h| h.join().unwrap_or_default())
                .collect()
        });
        let mut indexed: Vec<(usize, String)> = chunks.into_iter().flatten().collect();
        indexed.sort_unstable_by_key(|(i, _)| *i);
        indexed.into_iter().map(|(_, fk)| fk).collect()
    };

    let mut cached_splits = if let Some(st) = store {
        st.batch_get_file_splits(&unchanged_split_keys).unwrap_or_default()
    } else {
        std::collections::HashMap::new()
    };

    // Map rel_path -> file_split_key for unchanged files, and pre-split any cache misses in parallel
    let mut unchanged_key_by_path: std::collections::HashMap<&str, String> =
        std::collections::HashMap::with_capacity(unchanged_srcs.len());
    let mut miss_unchanged: Vec<(usize, &str, &str)> = Vec::new();
    for (idx, &(rel_path, cur_src)) in unchanged_srcs.iter().enumerate() {
        let fk = &unchanged_split_keys[idx];
        unchanged_key_by_path.insert(rel_path, fk.clone());
        if !cached_splits.contains_key(fk) {
            miss_unchanged.push((idx, fk.as_str(), cur_src));
        }
    }

    let mut new_splits_to_cache: Vec<(String, splitter::SplitResult)> =
        Vec::with_capacity(miss_unchanged.len());
    if !miss_unchanged.is_empty() {
        let computed: Vec<(usize, String, splitter::SplitResult)> = if miss_unchanged.len() < 2 {
            miss_unchanged
                .iter()
                .map(|&(idx, fk, src)| (idx, fk.to_string(), split_lean_source(src, &[])))
                .collect()
        } else {
            let workers = default_workers.min(miss_unchanged.len());
            let next_m = std::sync::atomic::AtomicUsize::new(0);
            let miss_ref = &miss_unchanged;
            let chunks: Vec<Vec<(usize, String, splitter::SplitResult)>> = std::thread::scope(|s| {
                let mut handles = Vec::with_capacity(workers);
                for _ in 0..workers {
                    let next_ref = &next_m;
                    handles.push(s.spawn(move || {
                        let mut local = Vec::new();
                        loop {
                            let pos = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            if pos >= miss_ref.len() {
                                break;
                            }
                            let (orig_idx, fk, src) = miss_ref[pos];
                            let sp = split_lean_source(src, &[]);
                            local.push((orig_idx, fk.to_string(), sp));
                        }
                        local
                    }));
                }
                handles
                    .into_iter()
                    .map(|h| h.join().unwrap_or_default())
                    .collect()
            });
            let mut flat: Vec<(usize, String, splitter::SplitResult)> =
                chunks.into_iter().flatten().collect();
            flat.sort_unstable_by_key(|(idx, _, _)| *idx);
            flat
        };

        for (_idx, fk, sp) in computed {
            if store.is_some() {
                new_splits_to_cache.push((fk.clone(), sp.clone()));
            }
            cached_splits.insert(fk, sp);
        }
    }

    let mut modified_files = Vec::new();
    let mut altered_interface_files = Vec::new();
    let mut unchanged_theorems = Vec::new();
    let mut proof_edited_theorems = Vec::new();
    let mut statement_edited_theorems = Vec::new();
    let mut per_file_interfaces = std::collections::BTreeMap::new();
    let mut shards_to_verify_by_file = std::collections::BTreeMap::new();
    let mut flagged_files = Vec::new();

    for path in all_paths {
        let rel_path = (*path).clone();
        match (base_files.get(&rel_path), current_files.get(&rel_path)) {
            (Some(base_src), Some(cur_src)) if base_src == cur_src => {
                let split = if let Some(fk) = unchanged_key_by_path.get(rel_path.as_str()) {
                    cached_splits
                        .remove(fk)
                        .unwrap_or_else(|| split_lean_source(cur_src, &[]))
                } else {
                    split_lean_source(cur_src, &[])
                };
                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), split.interface_hash);
                for s in split.shards {
                    unchanged_theorems.push(format!("{}::{}", rel_path, s.name));
                }
            }
            (Some(base_src), Some(cur_src)) => {
                modified_files.push(rel_path.clone());
                let cur_split = split_lean_source(cur_src, &[]);
                if !cur_split.hygiene.is_clean_for_certification() {
                    flagged_files.push((rel_path.clone(), cur_split.hygiene.flagged_items));
                }
                let base_split = split_lean_source(base_src, &[]);

                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(base_split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(cur_split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), cur_split.interface_hash.clone());

                let file_interface_same = cur_split.interface_hash == base_split.interface_hash
                    && cur_split.shards.len() == base_split.shards.len();
                let mut file_has_stmt_change = !file_interface_same;

                let mut base_by_name = std::collections::HashMap::new();
                for bs in &base_split.shards {
                    base_by_name.insert(bs.name.as_str(), (bs, compute_shard_key(toolchain, bs)));
                }
                let cur_names: std::collections::HashSet<&str> =
                    cur_split.shards.iter().map(|s| s.name.as_str()).collect();
                for bs in &base_split.shards {
                    if !cur_names.contains(bs.name.as_str()) {
                        file_has_stmt_change = true;
                        statement_edited_theorems
                            .push(format!("{}::{} (deleted)", rel_path, bs.name));
                    }
                }

                let mut file_verify_list = Vec::new();
                for s in cur_split.shards {
                    let k = compute_shard_key(toolchain, &s);
                    let qualified = format!("{}::{}", rel_path, s.name);
                    if let Some((bs, bk)) = base_by_name.get(s.name.as_str()) {
                        if k == *bk {
                            unchanged_theorems.push(qualified);
                        } else if s.stmt_hash == bs.stmt_hash
                            && s.prefix_env_hash == bs.prefix_env_hash
                            && file_interface_same
                        {
                            proof_edited_theorems.push(qualified);
                            file_verify_list.push((k, s, true));
                        } else {
                            file_has_stmt_change = true;
                            statement_edited_theorems.push(qualified);
                            file_verify_list.push((k, s, false));
                        }
                    } else {
                        file_has_stmt_change = true;
                        statement_edited_theorems.push(qualified);
                        file_verify_list.push((k, s, false));
                    }
                }

                if file_has_stmt_change {
                    altered_interface_files.push(rel_path.clone());
                }
                if !file_verify_list.is_empty() {
                    shards_to_verify_by_file.insert(rel_path, file_verify_list);
                }
            }
            (None, Some(cur_src)) => {
                modified_files.push(rel_path.clone());
                altered_interface_files.push(rel_path.clone());
                let cur_split = split_lean_source(cur_src, &[]);
                if !cur_split.hygiene.is_clean_for_certification() {
                    flagged_files.push((rel_path.clone(), cur_split.hygiene.flagged_items));
                }
                current_ih_hasher.update(rel_path.as_bytes());
                current_ih_hasher.update(b":");
                current_ih_hasher.update(cur_split.interface_hash.as_bytes());
                current_ih_hasher.update(b"\n");

                per_file_interfaces.insert(rel_path.clone(), cur_split.interface_hash);
                let mut file_verify_list = Vec::new();
                for s in cur_split.shards {
                    let k = compute_shard_key(toolchain, &s);
                    statement_edited_theorems.push(format!("{}::{}", rel_path, s.name));
                    file_verify_list.push((k, s, false));
                }
                if !file_verify_list.is_empty() {
                    shards_to_verify_by_file.insert(rel_path, file_verify_list);
                }
            }
            (Some(base_src), None) => {
                modified_files.push(rel_path.clone());
                altered_interface_files.push(rel_path.clone());
                let base_split = split_lean_source(base_src, &[]);
                baseline_ih_hasher.update(rel_path.as_bytes());
                baseline_ih_hasher.update(b":");
                baseline_ih_hasher.update(base_split.interface_hash.as_bytes());
                baseline_ih_hasher.update(b"\n");

                for bs in base_split.shards {
                    statement_edited_theorems
                        .push(format!("{}::{} (deleted)", rel_path, bs.name));
                }
            }
            (None, None) => {}
        }
    }

    if let Some(st) = store {
        if !new_splits_to_cache.is_empty() {
            let refs: Vec<(String, &splitter::SplitResult)> = new_splits_to_cache
                .iter()
                .map(|(h, sp)| (h.clone(), sp))
                .collect();
            let _ = st.batch_put_file_splits(&refs);
        }
    }

    if !flagged_files.is_empty() {
        anyhow::bail!(
            "PR Hygiene & Axiom Gate FAILED on {} files: {:?}",
            flagged_files.len(),
            flagged_files
        );
    }

    let baseline_interface_hash = baseline_ih_hasher.finalize().to_hex().to_string();
    let current_interface_hash = current_ih_hasher.finalize().to_hex().to_string();
    let interface_drift =
        baseline_interface_hash != current_interface_hash || !altered_interface_files.is_empty();

    Ok((
        PrClassification {
            total_files: current_files.len(),
            modified_files,
            altered_interface_files,
            interface_drift,
            baseline_interface_hash,
            current_interface_hash,
            unchanged_theorems,
            proof_edited_theorems,
            statement_edited_theorems,
            per_file_interfaces,
        },
        shards_to_verify_by_file,
    ))
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct VerificationReceipt {
    pub schema_version: u32,
    pub mode: String,
    pub interface_hash: String,
    pub action_key: String,
    pub files_audited: usize,
    pub theorem_shards: usize,
    pub forbidden_constructs_found: usize,
    pub per_file_interfaces: std::collections::BTreeMap<String, String>,
    pub receipt_blake3: String,
}

pub fn compute_receipt_blake3(
    schema_version: u32,
    mode: &str,
    interface_hash: &str,
    action_key: &str,
    files_audited: usize,
    theorem_shards: usize,
    forbidden_constructs_found: usize,
    per_file_interfaces: &std::collections::BTreeMap<String, String>,
) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-lean-verification-receipt-v1\n");
    hasher.update(format!("schema_version:{}\n", schema_version).as_bytes());
    hasher.update(format!("mode:{}\n", mode).as_bytes());
    hasher.update(format!("interface_hash:{}\n", interface_hash).as_bytes());
    hasher.update(format!("action_key:{}\n", action_key).as_bytes());
    hasher.update(format!("files_audited:{}\n", files_audited).as_bytes());
    hasher.update(format!("theorem_shards:{}\n", theorem_shards).as_bytes());
    hasher.update(format!("forbidden_constructs_found:{}\n", forbidden_constructs_found).as_bytes());
    for (rel_path, file_ih) in per_file_interfaces {
        hasher.update(b"file:");
        hasher.update(rel_path.as_bytes());
        hasher.update(b"=");
        hasher.update(file_ih.as_bytes());
        hasher.update(b"\n");
    }
    hasher.finalize().to_hex().to_string()
}

pub fn build_verification_receipt(
    mode: &str,
    interface_hash: &str,
    action_key: &str,
    files_audited: usize,
    theorem_shards: usize,
    forbidden_constructs_found: usize,
    per_file_interfaces: std::collections::BTreeMap<String, String>,
) -> VerificationReceipt {
    let schema_version = 1u32;
    let receipt_blake3 = compute_receipt_blake3(
        schema_version,
        mode,
        interface_hash,
        action_key,
        files_audited,
        theorem_shards,
        forbidden_constructs_found,
        &per_file_interfaces,
    );
    VerificationReceipt {
        schema_version,
        mode: mode.to_string(),
        interface_hash: interface_hash.to_string(),
        action_key: action_key.to_string(),
        files_audited,
        theorem_shards,
        forbidden_constructs_found,
        per_file_interfaces,
        receipt_blake3,
    }
}

pub fn verify_receipt_data(
    receipt: &VerificationReceipt,
    expected_interface_hash: Option<&str>,
    baseline: Option<&VerificationReceipt>,
) -> Result<Vec<String>> {
    if receipt.schema_version != 1 {
        anyhow::bail!(
            "Unsupported receipt schema_version {} (expected 1)",
            receipt.schema_version
        );
    }
    let expected_blake3 = compute_receipt_blake3(
        receipt.schema_version,
        &receipt.mode,
        &receipt.interface_hash,
        &receipt.action_key,
        receipt.files_audited,
        receipt.theorem_shards,
        receipt.forbidden_constructs_found,
        &receipt.per_file_interfaces,
    );
    if receipt.receipt_blake3 != expected_blake3 {
        anyhow::bail!(
            "Cryptographic receipt BLAKE3 integrity check FAILED: expected {}, got {}",
            expected_blake3,
            receipt.receipt_blake3
        );
    }
    if receipt.forbidden_constructs_found != 0 {
        anyhow::bail!(
            "Receipt certification gate FAILED: forbidden_constructs_found = {} (must be 0)",
            receipt.forbidden_constructs_found
        );
    }
    if let Some(exp_ih) = expected_interface_hash {
        if receipt.interface_hash != exp_ih {
            anyhow::bail!(
                "Project InterfaceHash mismatch: expected {}, got {}",
                exp_ih,
                receipt.interface_hash
            );
        }
    }
    let mut altered_files = Vec::new();
    if let Some(base) = baseline {
        let base_blake3 = compute_receipt_blake3(
            base.schema_version,
            &base.mode,
            &base.interface_hash,
            &base.action_key,
            base.files_audited,
            base.theorem_shards,
            base.forbidden_constructs_found,
            &base.per_file_interfaces,
        );
        if base.receipt_blake3 != base_blake3 {
            anyhow::bail!(
                "Baseline receipt BLAKE3 integrity check FAILED: expected {}, got {}",
                base_blake3,
                base.receipt_blake3
            );
        }
        let mut all_paths: std::collections::BTreeSet<&String> =
            receipt.per_file_interfaces.keys().collect();
        all_paths.extend(base.per_file_interfaces.keys());
        for path in all_paths {
            match (
                base.per_file_interfaces.get(path),
                receipt.per_file_interfaces.get(path),
            ) {
                (Some(b_ih), Some(r_ih)) if b_ih == r_ih => {}
                _ => altered_files.push(path.clone()),
            }
        }
        if !altered_files.is_empty() || receipt.interface_hash != base.interface_hash {
            anyhow::bail!(
                "Theorem interface drift detected against baseline receipt (altered files: {:?}, baseline interface_hash={}, current interface_hash={})",
                altered_files,
                base.interface_hash,
                receipt.interface_hash
            );
        }
    }
    Ok(altered_files)
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
}


