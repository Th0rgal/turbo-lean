//! Incremental theorem-level (`--decl`), file-level, and directory-wide (`check <dir>`)
//! verification with `/dev/shm` stat-split singleflight, local Zygote CoW prefix reuse,
//! and cross-file coalesced shard batching.

mod diagnostics;
mod directory;
mod identity;
mod remote;
mod single_decl;
mod single_file;
#[cfg(test)]
mod tests;

use anyhow::{Context, Result};
#[cfg(test)]
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
#[cfg(test)]
use std::process::Command;
use std::time::Instant;

static PROCESS_START: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();

/// Set once at CLI entry, before argument parsing, locks, or opening the store.
pub fn init_process_start_instant(t0: Instant) {
    let _ = PROCESS_START.set(t0);
}

pub fn process_wall_ms(fallback_t0: Instant) -> i64 {
    PROCESS_START
        .get()
        .copied()
        .unwrap_or(fallback_t0)
        .elapsed()
        .as_millis() as i64
}

#[derive(Clone, Copy, Default, serde::Serialize)]
pub(super) struct CheckPhaseTimings {
    hygiene_ms: i64,
    import_refresh_ms: i64,
    identity_ms: i64,
    cache_ms: i64,
    elab_ms: i64,
    kernel_ms: i64,
}

thread_local! {
    static CHECK_START: std::cell::Cell<Option<Instant>> = const { std::cell::Cell::new(None) };
    static PHASES: std::cell::RefCell<std::sync::Arc<std::sync::Mutex<CheckPhaseTimings>>> =
        std::cell::RefCell::new(std::sync::Arc::new(std::sync::Mutex::new(CheckPhaseTimings::default())));
}

pub(super) fn reset_phases() {
    PHASES.with(|p| *p.borrow_mut() = std::sync::Arc::default());
}

/// Share only the current check's counters with its scoped workers.
pub(super) fn phase_context() -> std::sync::Arc<std::sync::Mutex<CheckPhaseTimings>> {
    PHASES.with(|p| p.borrow().clone())
}

pub(super) fn set_phase_context(context: std::sync::Arc<std::sync::Mutex<CheckPhaseTimings>>) {
    PHASES.with(|p| *p.borrow_mut() = context);
}

/// Add measured work, keeping unrelated startup/locking overhead outside phases.
pub(super) fn record_phase(name: &str, start: Instant) {
    PHASES.with(|cell| {
        let context = cell.borrow();
        let mut p = context.lock().unwrap_or_else(|e| e.into_inner());
        let ms = start.elapsed().as_millis() as i64;
        match name {
            "hygiene" => p.hygiene_ms += ms,
            "import_refresh" => p.import_refresh_ms += ms,
            "identity" => p.identity_ms += ms,
            "cache" => p.cache_ms += ms,
            "elab" => p.elab_ms += ms,
            "kernel" => p.kernel_ms += ms,
            _ => unreachable!("unknown check phase"),
        }
    });
}

/// Measures an actual operation, including failed attempts. Nested spans of the
/// same phase are counted only once. Zero means no separately measured work.
pub(crate) struct PhaseTimer {
    phase: &'static str,
    start: Instant,
    outer: bool,
}

thread_local! {
    static ACTIVE_PHASES: std::cell::RefCell<Vec<&'static str>> = const { std::cell::RefCell::new(Vec::new()) };
}

impl PhaseTimer {
    pub(crate) fn start(phase: &'static str) -> Self {
        let outer = ACTIVE_PHASES.with(|active| {
            let mut active = active.borrow_mut();
            let outer = !active.contains(&phase);
            active.push(phase);
            outer
        });
        Self {
            phase,
            start: Instant::now(),
            outer,
        }
    }
}

impl Drop for PhaseTimer {
    fn drop(&mut self) {
        ACTIVE_PHASES.with(|active| {
            let mut active = active.borrow_mut();
            let index = active
                .iter()
                .rposition(|phase| *phase == self.phase)
                .expect("active phase");
            active.remove(index);
        });
        if self.outer {
            record_phase(self.phase, self.start);
        }
    }
}

pub(super) fn insert_check_timings(out: &mut serde_json::Value, t0: Instant) {
    let elapsed = out["elapsed_ms"].as_i64().unwrap_or(0);
    let start = CHECK_START.with(|start| start.get()).unwrap_or(t0);
    let wall = process_wall_ms(start).max(elapsed);
    let phases = PHASES.with(|p| *p.borrow().lock().unwrap_or_else(|e| e.into_inner()));
    out["wall_ms"] = wall.into();
    out["phases"] = serde_json::to_value(phases).expect("phase serialization");
    let summary = out["compact_summary"].as_str().unwrap_or("OK");
    let summary = summary.split(" wall_ms=").next().unwrap_or(summary);
    out["compact_summary"] = format!("{summary} wall_ms={wall}").into();
}

#[cfg(test)]
#[allow(clippy::items_after_test_module)]
mod wallclock_tests {
    use super::*;

    #[test]
    fn phase_context_aggregates_workers_and_deduplicates_nested_spans() {
        reset_phases();
        let context = phase_context();
        std::thread::scope(|scope| {
            scope.spawn(move || {
                set_phase_context(context);
                let outer = PhaseTimer::start("kernel");
                let inner = PhaseTimer::start("kernel");
                assert!(outer.outer);
                assert!(!inner.outer);
                std::thread::sleep(std::time::Duration::from_millis(20));
                drop(inner);
                // Inner destruction must add exactly nothing, independent of
                // scheduling jitter or timer resolution.
                assert_eq!(phase_context().lock().unwrap().kernel_ms, 0);
                drop(outer);
            });
        });
        let phases = phase_context();
        let phases = *phases.lock().unwrap();
        assert!(phases.kernel_ms >= 20);
        assert_eq!(phases.elab_ms, 0);
        reset_phases();
        assert_eq!(phase_context().lock().unwrap().kernel_ms, 0);
    }

    #[test]
    fn check_wallclock_json_and_direct_call() -> Result<()> {
        let dir = std::env::temp_dir().join(format!("wallclock-{}", crate::pack::next_tmp_id()));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        let file = dir.join("Wall.lean");
        fs::write(&file, "theorem wall_test : True := by trivial\n")?;
        let mut store = TurboStore::open(Some(&dir.join("cache")))?;
        let result = run_check_command_value(
            &mut store,
            false,
            file.clone(),
            Some("wall_test".into()),
            dir.clone(),
            None,
            false,
            None,
        )?;
        assert!(result["wall_ms"].as_i64().unwrap() >= result["elapsed_ms"].as_i64().unwrap());
        for field in [
            "hygiene_ms",
            "import_refresh_ms",
            "identity_ms",
            "cache_ms",
            "elab_ms",
            "kernel_ms",
        ] {
            assert!(result["phases"][field].as_i64().unwrap() >= 0, "{field}");
        }
        assert!(result["compact_summary"]
            .as_str()
            .unwrap()
            .contains("wall_ms="));
        let binary = std::env::current_exe()?
            .parent()
            .and_then(Path::parent)
            .unwrap()
            .join("turbo-lean");
        let output = Command::new(&binary)
            .args(["check", "--json", "--decl", "wall_test", "--project-dir"])
            .arg(&dir)
            .arg(&file)
            .arg("--cache-dir")
            .arg(dir.join("cli-cache"))
            .output()?;
        anyhow::ensure!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let cli: serde_json::Value = serde_json::from_slice(&output.stdout)?;
        assert!(cli["wall_ms"].as_i64().unwrap() >= cli["elapsed_ms"].as_i64().unwrap());
        assert!(cli["phases"].is_object());
        assert_eq!(
            cli["compact_summary"]
                .as_str()
                .unwrap()
                .matches("wall_ms=")
                .count(),
            1
        );
        let human = Command::new(&binary)
            .args(["check", "--decl", "wall_test", "--project-dir"])
            .arg(&dir)
            .arg(&file)
            .arg("--cache-dir")
            .arg(dir.join("cli-cache"))
            .output()?;
        anyhow::ensure!(
            human.status.success(),
            "{}",
            String::from_utf8_lossy(&human.stderr)
        );
        let human = String::from_utf8(human.stdout)?;
        assert!(human.contains("wall_ms="), "{human}");
        assert!(human.contains("phases="), "{human}");
        for target in [&file, &dir] {
            let output = Command::new(&binary)
                .args(["check", "--json", "--project-dir"])
                .arg(&dir)
                .arg(target)
                .arg("--cache-dir")
                .arg(dir.join("cli-cache"))
                .output()?;
            anyhow::ensure!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let result: serde_json::Value = serde_json::from_slice(&output.stdout)?;
            assert!(result["wall_ms"].as_i64().unwrap() >= result["elapsed_ms"].as_i64().unwrap());
            assert!(result["phases"].is_object());
            assert_eq!(
                result["compact_summary"]
                    .as_str()
                    .unwrap()
                    .matches("wall_ms=")
                    .count(),
                1
            );
        }
        run_check_command_with_options(
            &mut store,
            true,
            true,
            file,
            Some("wall_test".into()),
            dir.clone(),
            None,
            false,
            None,
            false,
            false,
        )?;
        fs::remove_dir_all(dir)?;
        Ok(())
    }
}

#[cfg(test)]
use crate::db;
use crate::db::TurboStore;
use crate::lake_build::{
    collect_lean_files, compact_split_for_shm_cache, compute_imported_olean_interface_hashes,
    compute_single_stat_hash, detect_toolchain, shm_file_splits_dir, split_and_audit_cached,
    ShmCachedFileSplit,
};
use crate::pr_verify::{try_fast_split_single_file, try_fast_split_single_file_from_path};
use crate::splitter::{self, split_lean_source};

pub use diagnostics::extract_mismatch_diagnostics;
pub(crate) use identity::{
    confirm_decl_identity, confirm_decl_identity_with_budget,
    confirm_file_decl_identities_with_budget, confirm_file_decl_identities_with_extra_dirs,
    create_readonly_private_file, freeze_private_dir, stage_isolated_module_artifacts,
    thaw_private_dir_tree, verified_private_temp_scratch_base, PrivateScratchDir,
};
#[cfg(test)]
pub(crate) use identity::{
    confirm_decl_identity_with_trust, create_private_file, read_single_isolated_olean,
};
pub use remote::try_stateless_remote_check;
#[cfg(test)]
use single_decl::store_has_provenanced_subshard;
#[cfg(test)]
pub(crate) use single_decl::{compute_fission_store_key, compute_fission_store_key_with_args};

use directory::check_directory;
use remote::resolve_check_project_and_target;
use single_decl::check_single_decl;
use single_file::check_single_file;

pub(crate) fn make_shard_receipt_bytes(
    decl: &str,
    prefix_env_hash: &str,
    stmt_hash: &str,
    proof_hash: &str,
    verified_at: i64,
) -> Result<Vec<u8>> {
    make_attested_shard_receipt_bytes(
        decl,
        prefix_env_hash,
        stmt_hash,
        proof_hash,
        verified_at,
        None,
    )
}

pub(crate) fn make_attested_shard_receipt_bytes(
    decl: &str,
    prefix_env_hash: &str,
    stmt_hash: &str,
    proof_hash: &str,
    verified_at: i64,
    kernel_type_hash: Option<&str>,
) -> Result<Vec<u8>> {
    let mut obj = serde_json::json!({
        "decl": decl,
        "prefix_env_hash": prefix_env_hash,
        "stmt_hash": stmt_hash,
        "proof_hash": proof_hash,
        "verified_at": verified_at,
        "scanner_version": crate::zygote::ZYGOTE_SCANNER_VERSION,
        "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION
    });
    if let Some(kth) = kernel_type_hash {
        obj["kernel_type_hash"] = serde_json::Value::String(kth.to_string());
    }
    Ok(serde_json::to_vec(&obj)?)
}

pub(super) fn write_shm_cached_split(
    st_path: &Path,
    split_key: String,
    src_blake3: String,
    split: &splitter::SplitResult,
    prefix_src: String,
    known_modified: bool,
    dep_hashes: Vec<String>,
) {
    let entry = ShmCachedFileSplit {
        split_key,
        src_blake3,
        split: compact_split_for_shm_cache(split),
        prefix_src,
        known_modified,
        dep_hashes,
    };
    if let Ok(bytes) = serde_json::to_vec(&entry) {
        let _ = crate::shm_cache::atomic_write_shm(st_path, &bytes);
    }
}

pub(super) fn cache_shm_stat_split_with_prefix(
    store: &TurboStore,
    canon_file: &Path,
    src_b3: &str,
    split: &splitter::SplitResult,
    prefix_src: String,
    dep_hashes: Vec<String>,
) {
    if let Ok(meta) = fs::metadata(canon_file) {
        let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(&meta);
        let pk = canon_file.to_string_lossy();
        let st_hash = compute_single_stat_hash(&pk, ms, mn, sz);
        let st_path = shm_file_splits_dir(store).join(format!("st_{}.json", &st_hash[..24]));
        write_shm_cached_split(
            &st_path,
            TurboStore::compute_file_split_key_from_src_hash(src_b3),
            src_b3.to_string(),
            split,
            prefix_src,
            false,
            dep_hashes,
        );
    }
}

fn cache_shm_stat_split(
    store: &TurboStore,
    canon_file: &Path,
    active_src: &str,
    split: &splitter::SplitResult,
    dep_hashes: Vec<String>,
) {
    let src_b3 = blake3::hash(active_src.as_bytes()).to_hex().to_string();
    cache_shm_stat_split_with_prefix(store, canon_file, &src_b3, split, String::new(), dep_hashes);
}

fn default_parallel_jobs(jobs: Option<usize>) -> usize {
    match jobs {
        Some(j) => j.max(1),
        None => {
            let governor = crate::shm_cache::MemoryBudgetGovernor::detect();
            if governor.is_low_memory_mode() {
                governor.recommended_parallel_workers(512)
            } else {
                std::thread::available_parallelism()
                    .map(|n| n.get())
                    .unwrap_or(4)
            }
            .max(1)
        }
    }
}

/// Execute `turbo-lean check` in-process and return the structured JSON value without printing to stdout.
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub fn run_check_command_value(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    file: PathBuf,
    decl: Option<String>,
    project_dir: PathBuf,
    jobs: Option<usize>,
    parallel_shards: bool,
    remote_http: Option<String>,
) -> Result<serde_json::Value> {
    crate::module_builder::reset_lake_inputs_tag_memo();
    run_check_command_inner(
        store,
        db_warm_on_open,
        false,
        false,
        false,
        file,
        decl,
        project_dir,
        jobs,
        parallel_shards,
        remote_http,
        false,
    )
}

/// Evaluate `turbo-lean check` in-process (`emit_stdout: false`) and return its JSON payload.
pub fn evaluate_check_command_value(
    store: &mut TurboStore,
    file: PathBuf,
    decl: Option<String>,
    project_dir: PathBuf,
) -> Result<serde_json::Value> {
    crate::module_builder::reset_lake_inputs_tag_memo();
    run_check_command_inner(
        store,
        true,
        false,
        false,
        false,
        file,
        decl,
        project_dir,
        None,
        true,
        None,
        false,
    )
}

/// Execute `turbo-lean check` on a directory, a single file, or a specific `--decl` theorem.
#[allow(clippy::too_many_arguments)]
pub fn run_check_command(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    json_output: bool,
    file: PathBuf,
    decl: Option<String>,
    project_dir: PathBuf,
    jobs: Option<usize>,
    parallel_shards: bool,
    remote_http: Option<String>,
) -> Result<()> {
    run_check_command_with_options(
        store,
        db_warm_on_open,
        json_output,
        file,
        decl,
        project_dir,
        jobs,
        parallel_shards,
        remote_http,
        false,
        false,
    )
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub fn run_check_command_with_opts(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    json_output: bool,
    file: PathBuf,
    decl: Option<String>,
    project_dir: PathBuf,
    jobs: Option<usize>,
    parallel_shards: bool,
    remote_http: Option<String>,
    emit_olean: bool,
) -> Result<()> {
    run_check_command_with_options(
        store,
        db_warm_on_open,
        json_output,
        file,
        decl,
        project_dir,
        jobs,
        parallel_shards,
        remote_http,
        emit_olean,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn run_check_command_with_options(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    json_output: bool,
    file: PathBuf,
    decl: Option<String>,
    project_dir: PathBuf,
    jobs: Option<usize>,
    parallel_shards: bool,
    remote_http: Option<String>,
    emit_olean: bool,
    allow_sorry: bool,
) -> Result<()> {
    // One top-level command, one Lake-input memo window.
    crate::module_builder::reset_lake_inputs_tag_memo();
    run_check_command_inner(
        store,
        db_warm_on_open,
        json_output,
        true,
        emit_olean,
        file,
        decl,
        project_dir,
        jobs,
        parallel_shards,
        remote_http,
        allow_sorry,
    )
    .map(|_| ())
}

fn resolve_workspace_imported_decl_submodule(
    canon_dir: &Path,
    initial_file: &Path,
    target_decl: &str,
) -> Result<Option<PathBuf>> {
    let Ok(initial_src) = fs::read_to_string(initial_file) else {
        return Ok(None);
    };
    let initial_split = split_lean_source(&initial_src, &[]);
    if splitter::find_decl_shard_index(&initial_split.shards, target_decl)?.is_some() {
        return Ok(None);
    }
    let root_pkg_opt = crate::module_builder::optional_package_config(canon_dir)
        .ok()
        .flatten();
    let resolve_mod_src = |mod_name: &str| -> Option<PathBuf> {
        if mod_name == "Init" {
            return None;
        }
        if let Some(ref pkg) = root_pkg_opt {
            if let Some(spec) =
                crate::module_builder::resolve_module_in_package(pkg, true, mod_name)
            {
                if spec.src_path.is_file() {
                    return Some(spec.src_path);
                }
            }
        }
        let rel_slash = crate::module_builder::module_name_to_rel_slash(mod_name);
        crate::lake_build::resolve_project_lean_source(canon_dir, &rel_slash).or_else(|| {
            let direct = canon_dir.join(format!("{rel_slash}.lean"));
            direct.is_file().then_some(direct)
        })
    };

    let mut queue = std::collections::VecDeque::new();
    let mut visited = std::collections::HashSet::new();
    let initial_canon = initial_file
        .canonicalize()
        .unwrap_or_else(|_| initial_file.to_path_buf());
    visited.insert(initial_canon);
    for imp in crate::module_builder::parse_header_imports(&initial_split.imports_header) {
        if let Some(p) = resolve_mod_src(&imp) {
            let cp = p.canonicalize().unwrap_or_else(|_| p.clone());
            if visited.insert(cp) {
                queue.push_back(p);
            }
        }
    }

    let mut found = None;
    while let Some(cand_path) = queue.pop_front() {
        let Ok(cand_src) = fs::read_to_string(&cand_path) else {
            continue;
        };
        let cand_split = split_lean_source(&cand_src, &[]);
        if splitter::find_decl_shard_index(&cand_split.shards, target_decl)?.is_some() {
            anyhow::ensure!(
                found.is_none(),
                "Ambiguous declaration `{target_decl}` in imported modules: {} and {}",
                found
                    .as_ref()
                    .map_or_else(String::new, |p: &PathBuf| p.display().to_string()),
                cand_path.display()
            );
            found = Some(cand_path.clone());
        }
        for imp in crate::module_builder::parse_header_imports(&cand_split.imports_header) {
            if let Some(p) = resolve_mod_src(&imp) {
                let cp = p.canonicalize().unwrap_or_else(|_| p.clone());
                if visited.insert(cp) {
                    queue.push_back(p);
                }
            }
        }
    }
    Ok(found)
}

fn file_suffix_after_prefix_is_comment_only(canon_file: &Path, prefix_len: usize) -> bool {
    let Ok(bytes) = fs::read(canon_file) else {
        return false;
    };
    if prefix_len >= bytes.len() {
        return true;
    }
    let Ok(suffix_str) = std::str::from_utf8(&bytes[prefix_len..]) else {
        return false;
    };
    splitter::strip_lean_comments(suffix_str).trim().is_empty()
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_check_command_inner(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    json_output: bool,
    emit_stdout: bool,
    emit_olean: bool,
    file: PathBuf,
    decl: Option<String>,
    project_dir: PathBuf,
    jobs: Option<usize>,
    parallel_shards: bool,
    remote_http: Option<String>,
    allow_sorry: bool,
) -> Result<serde_json::Value> {
    let started = Instant::now();
    let mut result = run_check_command_impl(
        store,
        db_warm_on_open,
        json_output,
        emit_stdout && !json_output,
        emit_olean,
        file,
        decl,
        project_dir,
        jobs,
        parallel_shards,
        remote_http,
        allow_sorry,
    )?;
    // Finalize at the command boundary, including every early-return path and
    // optional artifact emission, before serializing the one JSON response.
    insert_check_timings(&mut result, started);
    if emit_stdout {
        if json_output {
            println!("{}", serde_json::to_string_pretty(&result)?);
        } else {
            println!(
                "[turbo-lean] wall_ms={} phases={}",
                result["wall_ms"], result["phases"]
            );
        }
    }
    Ok(result)
}

#[allow(clippy::too_many_arguments)]
fn run_check_command_impl(
    store: &mut TurboStore,
    db_warm_on_open: bool,
    json_output: bool,
    emit_stdout: bool,
    emit_olean: bool,
    mut file: PathBuf,
    decl: Option<String>,
    project_dir: PathBuf,
    jobs: Option<usize>,
    parallel_shards: bool,
    remote_http: Option<String>,
    allow_sorry: bool,
) -> Result<serde_json::Value> {
    if emit_olean && decl.is_some() {
        anyhow::bail!(
            "`--emit-olean` cannot be combined with `--decl` (must check a full module file)"
        );
    }
    let t0 = Instant::now();
    CHECK_START.with(|start| start.set(Some(t0)));
    reset_phases();
    let _lifecycle = crate::zygote::lifecycle_lock(false)?;
    let (canon_dir, mut resolved_file) = resolve_check_project_and_target(&file, &project_dir);
    crate::module_builder::try_project_lake_inputs_tag(&canon_dir)?;
    let toolchain = detect_toolchain(&canon_dir);
    let kernel_prov = crate::kernel::resolve_kernel_engine(
        crate::kernel::resolve_kernel_selection_from_env(None)?,
        &toolchain,
    )?;

    if resolved_file.is_dir() && decl.is_none() {
        if emit_olean {
            anyhow::bail!(
                "`--emit-olean` requires a single `.lean` module file, not directory `{}`",
                resolved_file.display()
            );
        }
        return {
            let dir_res = check_directory(
                store,
                json_output,
                emit_stdout,
                &kernel_prov,
                &t0,
                &file,
                &resolved_file,
                &canon_dir,
                &toolchain,
                jobs,
                remote_http.as_deref(),
                allow_sorry,
            );
            if dir_res.is_err() && allow_sorry {
                let dir_files = collect_lean_files(&resolved_file);
                crate::lake_build::purge_sorry_artifacts_after_allow_sorry_failure(
                    &canon_dir, &dir_files,
                );
            }
            dir_res
        };
    }

    if let Some(target_decl) = decl.as_deref() {
        if resolved_file.is_file() {
            if let Some(sub_path) =
                resolve_workspace_imported_decl_submodule(&canon_dir, &resolved_file, target_decl)?
            {
                file = sub_path
                    .strip_prefix(&canon_dir)
                    .map(PathBuf::from)
                    .unwrap_or_else(|_| sub_path.clone());
                resolved_file = sub_path;
            }
        }
    }

    let canon_resolved_initial = resolved_file
        .canonicalize()
        .unwrap_or_else(|_| resolved_file.clone());
    if canon_resolved_initial.is_file() {
        if !allow_sorry {
            let source = fs::read_to_string(&canon_resolved_initial)?;
            let hygiene = splitter::audit_hygiene(&splitter::strip_lean_comments(&source));
            if !hygiene.is_clean_or_deferred_to_kernel_gate() {
                let violations = if let Some(target) = decl.as_deref() {
                    let split = split_lean_source(&source, &[]);
                    if let Some(idx) = splitter::find_decl_shard_index(&split.shards, target)? {
                        let cone = single_decl::audited_cone_source(&source, &split.shards[idx])?;
                        splitter::audit_hygiene(&splitter::strip_lean_comments(&cone))
                            .disallowed_items()
                    } else {
                        Vec::new()
                    }
                } else {
                    hygiene.disallowed_items()
                };
                let violations: Vec<_> = violations
                    .into_iter()
                    .filter(|v| {
                        !splitter::HygieneReport {
                            flagged_items: vec![v.clone()],
                            ..Default::default()
                        }
                        .is_clean_or_deferred_to_kernel_gate()
                    })
                    .collect();
                anyhow::ensure!(
                    violations.is_empty(),
                    "Soundness hygiene violation in {}: {}",
                    file.display(),
                    violations.join(", ")
                );
            }
        }
        let refresh_start = Instant::now();
        let fresh_res = crate::lake_build::ensure_project_imports_fresh_for_check_with_options(
            &canon_dir,
            std::slice::from_ref(&canon_resolved_initial),
            allow_sorry,
        );
        if fresh_res.is_err() && allow_sorry {
            crate::lake_build::purge_sorry_artifacts_after_allow_sorry_failure(
                &canon_dir,
                std::slice::from_ref(&canon_resolved_initial),
            );
        }
        fresh_res?;
        record_phase("import_refresh", refresh_start);
        let kernel_timer = PhaseTimer::start("kernel");
        let import_res = crate::module_builder::ensure_imported_oleans_replayed_with_options(
            store,
            &canon_dir,
            std::slice::from_ref(&canon_resolved_initial),
            allow_sorry,
        );
        if import_res.is_err() && allow_sorry {
            crate::lake_build::purge_sorry_artifacts_after_allow_sorry_failure(
                &canon_dir,
                std::slice::from_ref(&canon_resolved_initial),
            );
        }
        import_res?;
        drop(kernel_timer);
    }
    let file_stat_tuple: Option<(i64, i64, i64)> = fs::metadata(&canon_resolved_initial)
        .ok()
        .map(|m| TurboStore::extract_file_stat_tuple(&m));

    let hygiene_start = Instant::now();
    let splits_dir = shm_file_splits_dir(store);
    let st_paths_opt = file_stat_tuple.map(|(ms, mn, sz)| {
        let pk = canon_resolved_initial.to_string_lossy();
        let st_hash = compute_single_stat_hash(&pk, ms, mn, sz);
        let st_path = splits_dir.join(format!("st_{}.json", &st_hash[..24]));
        let lock_path = splits_dir.join(format!("st_{}.lock", &st_hash[..24]));
        (st_path, lock_path)
    });

    let disk_spill_dir = store.root.join("disk_spill");
    let read_valid_stat_split = |st_path: &Path| -> Option<ShmCachedFileSplit> {
        crate::shm_cache::read_shm_or_disk_spill(st_path, Some(&disk_spill_dir))
            .and_then(|bytes| serde_json::from_slice::<ShmCachedFileSplit>(&bytes).ok())
            .filter(|c| {
                compute_imported_olean_interface_hashes(&c.split.imports_header, &canon_dir, None)
                    == c.dep_hashes
                    && (!c.src_blake3.is_empty()
                        || (!c.prefix_src.is_empty()
                            && file_suffix_after_prefix_is_comment_only(
                                &canon_resolved_initial,
                                c.prefix_src.len(),
                            )))
            })
    };
    let mut stat_cached_entry = st_paths_opt
        .as_ref()
        .and_then(|(st_path, _)| read_valid_stat_split(st_path));

    let mut held_split_lock: Option<crate::shm_cache::FlockGuard> = None;
    if stat_cached_entry.is_none() {
        if let Some((ref st_path, ref lock_path)) = st_paths_opt {
            if let Ok(Some(g)) = crate::shm_cache::acquire_flock(lock_path, true, true) {
                held_split_lock = Some(g);
            } else if let Ok(_sh) = crate::shm_cache::acquire_flock(lock_path, false, false) {
                stat_cached_entry = read_valid_stat_split(st_path);
            }
        }
    }

    let mut known_modified_vs_head = false;
    let (mut src, mut cached_file_blake3, mut split, single_split_hits) = if let Some(c) =
        stat_cached_entry
    {
        known_modified_vs_head = c.known_modified;
        let cb3 = (!c.src_blake3.is_empty()).then_some(c.src_blake3);
        (c.prefix_src, cb3, c.split, 1usize)
    } else if let Some((pref_src, fast_sp, 0, fast_deps)) = file_stat_tuple
        .filter(|(_, _, sz)| *sz > 64 * 1024)
        .and_then(|(_, _, sz)| {
            try_fast_split_single_file_from_path(
                store,
                &canon_dir,
                &canon_resolved_initial,
                sz,
                &toolchain,
            )
        })
        .filter(|(pref_src, _, _, _)| {
            file_suffix_after_prefix_is_comment_only(&canon_resolved_initial, pref_src.len())
        })
    {
        known_modified_vs_head = true;
        if let Some((ref st_path, _)) = st_paths_opt {
            let entry = ShmCachedFileSplit {
                split_key: String::new(),
                src_blake3: String::new(),
                split: compact_split_for_shm_cache(&fast_sp),
                prefix_src: pref_src.clone(),
                known_modified: true,
                dep_hashes: fast_deps,
            };
            if let Ok(bytes) = serde_json::to_vec(&entry) {
                let _ = crate::shm_cache::atomic_write_shm(st_path, &bytes);
            }
        }
        (pref_src, None, fast_sp, 0usize)
    } else {
        let mut loaded_src = fs::read_to_string(&resolved_file)
            .with_context(|| format!("Failed to read {}", resolved_file.display()))?;
        let dep_hashes = compute_imported_olean_interface_hashes(&loaded_src, &canon_dir, None);
        let mut opt_src_b3: Option<String> = None;
        let (sp, hits) = if loaded_src.len() <= 64 * 1024 {
            let sp = split_lean_source(&loaded_src, &dep_hashes);
            let src_b3 = blake3::hash(loaded_src.as_bytes()).to_hex().to_string();
            if let Some((ref st_path, _)) = st_paths_opt {
                write_shm_cached_split(
                    st_path,
                    TurboStore::compute_file_split_key_from_src_hash(&src_b3),
                    src_b3.clone(),
                    &sp,
                    String::new(),
                    false,
                    dep_hashes.clone(),
                );
            }
            opt_src_b3 = Some(src_b3);
            (sp, usize::from(db_warm_on_open))
        } else if let Some(fast_res) = try_fast_split_single_file(
            store,
            &canon_dir,
            &canon_resolved_initial,
            &loaded_src,
            &toolchain,
            &dep_hashes,
        )
        .filter(|(_, _, cur_prefix_len)| {
            *cur_prefix_len >= loaded_src.len()
                || splitter::strip_lean_comments(&loaded_src[*cur_prefix_len..])
                    .trim()
                    .is_empty()
        }) {
            if fast_res.1 == 0 {
                known_modified_vs_head = true;
            }
            if let Some((ref st_path, _)) = st_paths_opt {
                let (src_b3, pref_src) = if fast_res.1 > 0 {
                    (
                        blake3::hash(loaded_src.as_bytes()).to_hex().to_string(),
                        String::new(),
                    )
                } else {
                    (String::new(), loaded_src[..fast_res.2].to_string())
                };
                if !src_b3.is_empty() {
                    opt_src_b3 = Some(src_b3.clone());
                }
                let split_key = if src_b3.is_empty() {
                    String::new()
                } else {
                    TurboStore::compute_file_split_key_from_src_hash(&src_b3)
                };
                write_shm_cached_split(
                    st_path,
                    split_key,
                    src_b3,
                    &fast_res.0,
                    pref_src,
                    fast_res.1 == 0,
                    dep_hashes.clone(),
                );
            }
            if fast_res.2 > 0 && fast_res.2 < loaded_src.len() {
                loaded_src.truncate(fast_res.2);
            }
            (fast_res.0, fast_res.1)
        } else {
            let src_b3 = blake3::hash(loaded_src.as_bytes()).to_hex().to_string();
            let split_key =
                crate::lake_build::compute_file_split_key_with_deps(&src_b3, &dep_hashes);
            let fk_path = crate::lake_build::shm_file_splits_dir(store)
                .join(format!("fk_{}.json", &split_key[..24]));
            let (sp, hits) = if let Ok(sp) = fs::read(&fk_path).and_then(|b| {
                serde_json::from_slice::<splitter::SplitResult>(&b).map_err(std::io::Error::other)
            }) {
                (sp, 1usize)
            } else {
                let (mut single_parsed, hits) =
                    split_and_audit_cached(store, &[(resolved_file.clone(), loaded_src.clone())])?;
                (
                    single_parsed
                        .pop()
                        .map(|(_, _, sp)| sp)
                        .unwrap_or_else(|| split_lean_source(&loaded_src, &dep_hashes)),
                    hits,
                )
            };
            if let Some((ref st_path, _)) = st_paths_opt {
                write_shm_cached_split(
                    st_path,
                    split_key,
                    src_b3.clone(),
                    &sp,
                    String::new(),
                    false,
                    dep_hashes.clone(),
                );
            }
            opt_src_b3 = Some(src_b3);
            (sp, hits)
        };
        (loaded_src, opt_src_b3, sp, hits)
    };

    drop(held_split_lock);
    record_phase("hygiene", hygiene_start);

    let decl_mode = decl.is_some();
    let res_or_err: Result<serde_json::Value> = (|| {
        if let Some(target_decl) = decl {
            check_single_decl(
                store,
                db_warm_on_open,
                json_output,
                emit_stdout,
                &kernel_prov,
                &t0,
                &file,
                &resolved_file,
                &canon_resolved_initial,
                &canon_dir,
                &toolchain,
                &target_decl,
                src,
                &mut cached_file_blake3,
                &mut split,
                known_modified_vs_head,
                single_split_hits,
                remote_http.as_deref(),
                allow_sorry,
            )
        } else {
            if emit_olean {
                anyhow::ensure!(
                    !allow_sorry,
                    "`--emit-olean` cannot be combined with `--allow-sorry`"
                );
            }
            let mut out_json = check_single_file(
                store,
                db_warm_on_open,
                json_output,
                emit_stdout && !emit_olean,
                &kernel_prov,
                &t0,
                &file,
                &resolved_file,
                &canon_resolved_initial,
                &canon_dir,
                &toolchain,
                &mut src,
                cached_file_blake3.as_deref(),
                &split,
                single_split_hits,
                jobs,
                parallel_shards,
                remote_http.as_deref(),
                allow_sorry,
            )?;
            if emit_olean {
                anyhow::ensure!(
                    !crate::lake_build::worktree_auto_link_disabled(&canon_dir),
                    "Worktree opt-out prevents `--emit-olean` from writing `.lake/build` artifacts in {}",
                    canon_dir.display()
                );
                anyhow::ensure!(
                    split.hygiene.is_clean_for_certification(),
                    "Refusing `--emit-olean` for `{}`: source is not clean for certification (contains sorry/axiom/weakening directives)",
                    file.display()
                );
                let cfg = crate::module_builder::resolve_project_config(&canon_dir).with_context(
                    || {
                        format!(
                            "`--emit-olean` requires a valid Lake workspace in {}",
                            canon_dir.display()
                        )
                    },
                )?;
                let (target_spec, mod_spec) =
                    crate::module_builder::resolve_lean_file_to_workspace_target(
                        &cfg,
                        &canon_resolved_initial,
                    )
                    .ok_or_else(|| {
                        anyhow::anyhow!(
                            "`--emit-olean` could not resolve `{}` to a Lake library/executable module in `{}`",
                            file.display(),
                            canon_dir.display()
                        )
                    })?;
                let olean_path = mod_spec.build_lib_lean_dir.join(format!(
                    "{}.olean",
                    crate::module_builder::module_name_to_rel_slash(&mod_spec.module_name)
                ));
                crate::lake_build::recheck_dependents_if_nonlocal(
                    store,
                    &canon_dir,
                    &resolved_file,
                )?;
                // Re-run `build_project_modules_native` after any Lake dependent refresh so the target's
                // `.turbo_verified_sources.json` entry (`kernel_audited = true` + exact `.olean` digest)
                // stays synchronized with the final on-disk artifact set.
                let build_rep = crate::module_builder::build_project_modules_native(
                    store,
                    &canon_dir,
                    std::slice::from_ref(&target_spec),
                    "trusted",
                    1,
                    false,
                    true,
                    None,
                )?;
                let built_count = build_rep.modules_compiled
                    + build_rep.modules_cached
                    + build_rep.modules_up_to_date_reused;
                if build_rep.modules_total == 0 || built_count != build_rep.modules_total {
                    anyhow::bail!(
                        "`--emit-olean` target `{}` resolved an incomplete module build ({}/{} modules materialized)",
                        target_spec,
                        built_count,
                        build_rep.modules_total
                    );
                }
                let (_, emitted_gh) =
                    crate::module_builder::read_olean_header_version_and_githash_confined(
                        &mod_spec.pkg_root,
                        &olean_path,
                    )
                    .ok_or_else(|| {
                        anyhow::anyhow!(
                            "`--emit-olean` failed to materialize confined regular `.olean` artifact at `{}`",
                            olean_path.display()
                        )
                    })?;
                let exp_gh = cfg.lean_githash.trim();
                if !exp_gh.is_empty()
                    && exp_gh != "lean-not-installed"
                    && !emitted_gh.eq_ignore_ascii_case(exp_gh)
                {
                    anyhow::bail!(
                        "`--emit-olean` emitted `.olean` githash `{}` != active compiler `{}` at `{}`",
                        emitted_gh,
                        exp_gh,
                        olean_path.display()
                    );
                }
                let total_ms = t0.elapsed().as_millis() as i64;
                if let Some(obj) = out_json.as_object_mut() {
                    obj.insert("olean_emitted".to_string(), serde_json::json!(true));
                    obj.insert(
                        "olean_path".to_string(),
                        serde_json::json!(olean_path.display().to_string()),
                    );
                    obj.insert(
                        "module_name".to_string(),
                        serde_json::json!(mod_spec.module_name),
                    );
                    obj.insert(
                        "olean_cached".to_string(),
                        serde_json::json!(
                            build_rep.modules_cached > 0 && build_rep.modules_compiled == 0
                        ),
                    );
                    obj.insert("elapsed_ms".to_string(), serde_json::json!(total_ms));
                }
                if emit_stdout {
                    if json_output {
                        println!("{}", serde_json::to_string_pretty(&out_json)?);
                    } else {
                        println!(
                            "[turbo-lean] VERIFIED & EMITTED OLEAN {} -> {} ({} ms)",
                            file.display(),
                            olean_path.display(),
                            total_ms
                        );
                    }
                }
            }
            Ok(out_json)
        }
    })();
    let decl_with_sorry_siblings = decl_mode && split.hygiene.has_sorry;
    if res_or_err.is_err() && (allow_sorry || decl_with_sorry_siblings) {
        crate::lake_build::purge_sorry_artifacts_after_allow_sorry_failure(
            &canon_dir,
            std::slice::from_ref(&canon_resolved_initial),
        );
    }
    let res = res_or_err?;
    if !emit_olean {
        let recheck_res = crate::lake_build::recheck_dependents_if_nonlocal_for_check(
            store,
            &canon_dir,
            &resolved_file,
            allow_sorry,
            decl_mode,
            decl_with_sorry_siblings,
        );
        if recheck_res.is_err() && (allow_sorry || decl_with_sorry_siblings) {
            crate::lake_build::purge_sorry_artifacts_after_allow_sorry_failure(
                &canon_dir,
                std::slice::from_ref(&canon_resolved_initial),
            );
        }
        recheck_res?;
    }
    Ok(res)
}

impl TurboStore {
    #[cfg(test)]
    pub fn has_theorem_shard(&self, shard_key: &str) -> bool {
        self.has_cached_action_readonly(shard_key, "trusted")
            .unwrap_or(false)
    }
    #[cfg(test)]
    pub fn put_theorem_shard(
        &mut self,
        toolchain: &str,
        shard_key: &str,
        decl_name: &str,
        receipt_bytes: &[u8],
        duration_ms: i64,
    ) -> Result<()> {
        let items = [(
            shard_key.to_string(),
            decl_name.to_string(),
            receipt_bytes.to_vec(),
            duration_ms.max(1),
        )];
        self.batch_publish_theorem_shards(toolchain, "trusted", &items)
    }
    pub fn batch_put_theorem_shards(
        &mut self,
        toolchain: &str,
        items: &[(String, String, Vec<u8>, i64)],
    ) -> Result<()> {
        self.batch_publish_theorem_shards(toolchain, "trusted", items)
    }
}

#[cfg(test)]
pub fn verify_subshards_out_of_core(
    store: &mut TurboStore,
    toolchain: &str,
    lean_path: &str,
    env_vars: &HashMap<String, String>,
    lean_bin: &Path,
    prefix_source: &str,
    subshards: &[(String, String, String)],
) -> Result<(usize, usize)> {
    let governor = crate::shm_cache::MemoryBudgetGovernor::detect();
    if governor.is_low_memory_mode() {
        let shm_dir = store.fast_staging_dir();
        let disk_spill_dir = store.root.join("disk_spill");
        let _ = crate::shm_cache::spill_shm_to_disk_dir(
            &shm_dir,
            &disk_spill_dir,
            governor.recommended_shm_quota_bytes(),
        );
    }
    let prefix_env_hash = blake3::hash(prefix_source.as_bytes()).to_hex().to_string();
    let (mut disk_cached_hits, mut newly_verified) = (0usize, 0usize);
    for (step_label, sub_shard_key, sub_decl_source) in subshards {
        if store_has_provenanced_subshard(store, sub_shard_key) {
            let _ = store.batch_increment_action_hits(std::slice::from_ref(sub_shard_key));
            disk_cached_hits += 1;
            continue;
        }
        let step_t0 = Instant::now();
        let reply = crate::zygote::eval_shard_via_zygote(
            store,
            toolchain,
            lean_path,
            env_vars,
            lean_bin,
            prefix_source,
            sub_decl_source,
            &[],
        )?;
        if !reply.import_ok || !reply.ok {
            anyhow::bail!(
                "Out-of-core sub-shard `{}` ({}) verification failed: {}",
                step_label,
                sub_shard_key,
                reply.errors.join("; ")
            );
        }
        let dur_ms = (step_t0.elapsed().as_millis() as i64).max(1);
        let sub_hash = blake3::hash(sub_decl_source.as_bytes())
            .to_hex()
            .to_string();
        let receipt = serde_json::to_vec(&serde_json::json!({
            "decl": step_label, "sub_shard_key": sub_shard_key, "prefix_env_hash": prefix_env_hash,
            "stmt_hash": sub_hash, "proof_hash": sub_hash, "verified_at": db::now_unix(),
            "scanner_version": crate::zygote::ZYGOTE_SCANNER_VERSION,
            "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION,
        }))?;
        store.put_theorem_shard(toolchain, sub_shard_key, step_label, &receipt, dur_ms)?;
        newly_verified += 1;
    }
    Ok((disk_cached_hits, newly_verified))
}
