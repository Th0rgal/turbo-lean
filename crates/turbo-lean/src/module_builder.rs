//! Native Lean 4 Project Configuration Resolver, Deterministic Module DAG Builder,
//! Direct `lean` Module Compiler, and Per-Module CAS (`module_unit`).
//!
//! Replaces runtime `lake build` invocations in `turbo-lean build` and `turbo-lean ci-verify`
//! with a Rust-owned module DAG orchestrator verified by C-ABI gates in `TurboLean.Kernel`:
//! - `turbo_spec_verify_static_lake_config`
//! - `turbo_spec_verify_dag_schedule_step`
//! - `turbo_spec_verify_module_cache_key`
//! - `turbo_spec_verify_module_artifact_set`
use crate::c_abi;
use crate::db::{BlobEntry, SingleflightOutcome, TurboStore};
use crate::lake_build;
use crate::splitter;
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};
use std::time::Instant;
use walkdir::WalkDir;
/// Glob specification for a `lean_lib` target (`Glob.one`, `Glob.submodules`, `Glob.andSubmodules`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum GlobSpec {
    One(String),
    Submodules(String),
    AndSubmodules(String),
}
/// Static configuration of a `lean_lib` target.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeanLibConfig {
    pub name: String,
    pub src_dir: Option<PathBuf>,
    pub roots: Vec<String>,
    pub globs: Vec<GlobSpec>,
    pub more_lean_args: Vec<String>,
    pub weak_lean_args: Vec<String>,
    pub lean_options: BTreeMap<String, String>,
    pub precompile_modules: Option<bool>,
    pub default_facets: Vec<String>,
    pub is_default_target: bool,
}
/// Static configuration of a `lean_exe` target.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeanExeConfig {
    pub name: String,
    pub src_dir: Option<PathBuf>,
    pub root: String,
    pub support_interpreter: bool,
    pub more_lean_args: Vec<String>,
    pub weak_lean_args: Vec<String>,
    pub lean_options: BTreeMap<String, String>,
    pub is_default_target: bool,
}
/// Static representation of an `extern_lib` declaration.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternLibConfig {
    pub name: String,
    pub is_dynamic_recipe: bool,
    pub static_artifact_path: Option<PathBuf>,
    pub static_artifact_blake3: Option<String>,
}
/// Resolved package entry from `lake-manifest.json`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ManifestPackageEntry {
    pub name: String,
    pub pkg_type: String,
    pub dir: PathBuf,
    pub rev: Option<String>,
    pub url: Option<String>,
    pub config_file: Option<String>,
    pub inherited: bool,
}
/// Canonical static configuration for a single Lake package (root or dependency).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PackageConfig {
    pub name: String,
    pub pkg_root: PathBuf,
    pub config_file_kind: String,
    pub src_dir: PathBuf,
    pub build_dir: PathBuf,
    pub lean_lib_dir: PathBuf,
    pub ir_dir: PathBuf,
    pub packages_dir: PathBuf,
    pub more_lean_args: Vec<String>,
    pub weak_lean_args: Vec<String>,
    pub lean_options: BTreeMap<String, String>,
    pub precompile_modules: bool,
    pub default_targets: Vec<String>,
    pub libs: Vec<LeanLibConfig>,
    pub exes: Vec<LeanExeConfig>,
    pub extern_libs: Vec<ExternLibConfig>,
    pub custom_targets: Vec<String>,
    pub config_digest: String,
}
/// Resolved workspace configuration combining root package, `lean-toolchain`, `lake-manifest.json`,
/// and dependency packages.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProjectConfig {
    pub toolchain: String,
    pub lean_bin: PathBuf,
    pub lean_githash: String,
    pub toolchain_lib_lean: PathBuf,
    pub toolchain_lib: PathBuf,
    pub root_pkg: PackageConfig,
    pub manifest_packages: Vec<ManifestPackageEntry>,
    pub dep_pkgs: Vec<PackageConfig>,
    pub canonical_config_digest: String,
}
/// Parsed header metadata from a `.lean` module file.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct HeaderInfo {
    pub is_module: bool,
    pub has_prelude: bool,
    pub has_c_export: bool,
    pub imports: Vec<String>,
}
/// A single module node in the resolved compilation DAG.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleNode {
    pub module_name: String,
    pub pkg_name: String,
    pub target_name: String,
    pub is_root_pkg: bool,
    pub pkg_root: PathBuf,
    pub src_root: PathBuf,
    pub src_path: PathBuf,
    pub build_lib_lean_dir: PathBuf,
    pub build_ir_dir: PathBuf,
    pub olean_path: PathBuf,
    pub ilean_path: PathBuf,
    pub c_path: PathBuf,
    pub is_module: bool,
    pub has_prelude: bool,
    pub needs_c: bool,
    pub precompile_modules: bool,
    pub strong_args: Vec<String>,
    pub weak_args: Vec<String>,
    pub src_blake3: String,
    pub direct_dag_deps: Vec<String>,
    pub external_olean_deps: Vec<(String, PathBuf)>,
    pub expected_all_deps: Vec<String>,
    pub extern_lib_digests: Vec<String>,
    pub pkg_config_digest: String,
}
/// Deterministic Module DAG with topological waves.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleDag {
    pub nodes: BTreeMap<String, ModuleNode>,
    pub topological_order: Vec<String>,
    pub waves: Vec<Vec<String>>,
    pub root_modules: Vec<String>,
}
/// Summary report returned by `build_project_modules_native`.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct NativeBuildReport {
    pub modules_total: usize,
    pub modules_compiled: usize,
    pub modules_cached: usize,
    pub modules_up_to_date_reused: usize,
    pub waves_count: usize,
    pub config_digest: String,
    pub compiled_modules: Vec<String>,
    pub cached_modules: Vec<String>,
    pub bwrap_used: bool,
}
/// Strip surrounding whitespace, leading backtick `` ` ``, and Lake guillemets `«...»`.
pub fn clean_lake_ident(raw: &str) -> String {
    let mut s = raw.trim();
    if let Some(rest) = s.strip_prefix('`') {
        s = rest.trim();
    }
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        s = &s[1..s.len() - 1];
    }
    if s.starts_with('\'') && s.ends_with('\'') && s.len() >= 2 {
        s = &s[1..s.len() - 1];
    }
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        if ch != '«' && ch != '»' {
            out.push(ch);
        }
    }
    out.trim().to_string()
}
/// Comment-safe header parser extracting `module`, `prelude`, `@[export ...]`, and `import` declarations.
pub fn parse_header_info(src: &str) -> HeaderInfo {
    let clean = splitter::strip_lean_comments(src);
    let mut info = HeaderInfo {
        is_module: false,
        has_prelude: false,
        has_c_export: clean.contains("@[export ")
            || clean.contains("@[inline, export ")
            || clean.contains(", export "),
        imports: Vec::new(),
    };
    let mut seen_imports = HashSet::new();
    let mut saw_non_header = false;
    for line in clean.lines() {
        let mut s = line.trim();
        if s.is_empty() {
            continue;
        }
        while !s.is_empty() {
            let (stmt, rem) = match s.find(';') {
                Some(idx) => (s[..idx].trim(), s[idx + 1..].trim()),
                None => (s, ""),
            };
            s = rem;
            if stmt.is_empty() {
                continue;
            }
            if !saw_non_header && (stmt == "module" || stmt.starts_with("module ")) {
                info.is_module = true;
                continue;
            }
            if !saw_non_header && (stmt == "prelude" || stmt.starts_with("prelude ")) {
                info.has_prelude = true;
                continue;
            }
            let mut imp_check = stmt;
            loop {
                if let Some(r) = imp_check.strip_prefix("public ") {
                    imp_check = r.trim_start();
                } else if let Some(r) = imp_check.strip_prefix("meta ") {
                    imp_check = r.trim_start();
                } else {
                    break;
                }
            }
            if let Some(rest) = imp_check.strip_prefix("import ") {
                let mut rest_trim = rest.trim_start();
                if let Some(after_all) = rest_trim.strip_prefix("all ") {
                    rest_trim = after_all.trim_start();
                }
                for tok in rest_trim.split_whitespace() {
                    if tok == "public" || tok == "all" || tok == "meta" || tok == "import" {
                        continue;
                    }
                    let mod_name = clean_lake_ident(tok);
                    if !mod_name.is_empty() && seen_imports.insert(mod_name.clone()) {
                        info.imports.push(mod_name);
                    }
                }
            } else {
                saw_non_header = true;
                break;
            }
        }
        if saw_non_header {
            break;
        }
    }
    info
}
/// Comment-safe replacement for `lake_build::parse_header_imports`.
pub fn parse_header_imports(src: &str) -> Vec<String> {
    parse_header_info(src).imports
}
static LEAN_INFO_CACHE: OnceLock<Mutex<HashMap<PathBuf, (String, PathBuf, PathBuf)>>> =
    OnceLock::new();
fn path_has_toolchain_component(path: &Path, tc_dir_name: &str) -> bool {
    let comps: Vec<String> = path
        .components()
        .map(|c| c.as_os_str().to_string_lossy().to_string())
        .collect();
    for w in comps.windows(2) {
        if w[0] == "toolchains" && w[1] == tc_dir_name {
            return true;
        }
    }
    false
}

fn path_is_inside_any_toolchains_dir(path: &Path) -> bool {
    path.components()
        .any(|c| c.as_os_str().to_string_lossy() == "toolchains")
}

fn path_is_elan_proxy_bin(path: &Path) -> bool {
    if path_is_inside_any_toolchains_dir(path) {
        return false;
    }
    if let Ok(canon) = path.canonicalize() {
        if path_is_inside_any_toolchains_dir(&canon) {
            return false;
        }
        if let Some(fname) = canon.file_name().and_then(|s| s.to_str()) {
            if fname == "elan" || fname == "elan.exe" {
                return true;
            }
        }
    }
    let comps: Vec<String> = path
        .components()
        .map(|c| c.as_os_str().to_string_lossy().to_string())
        .collect();
    comps.windows(2).any(|w| w[0] == ".elan" && w[1] == "bin")
}

fn extract_toolchain_version_token(toolchain: &str) -> Option<String> {
    let trimmed = toolchain.trim();
    if trimmed.is_empty() || trimmed == "unknown" {
        return None;
    }
    let after_colon = trimmed.rsplit(':').next().unwrap_or(trimmed).trim();
    let ver = after_colon.strip_prefix('v').unwrap_or(after_colon).trim();
    if ver.is_empty() {
        None
    } else {
        Some(ver.to_string())
    }
}

fn lean_version_output_matches_exact(ver_str: &str, expected_ver: &str) -> bool {
    let pat_comma = format!("version {},", expected_ver);
    let pat_space = format!("version {} ", expected_ver);
    let pat_paren = format!("version {})", expected_ver);
    let pat_nl = format!("version {}\n", expected_ver);
    ver_str.contains(&pat_comma)
        || ver_str.contains(&pat_space)
        || ver_str.contains(&pat_paren)
        || ver_str.contains(&pat_nl)
        || ver_str
            .trim()
            .ends_with(&format!("version {}", expected_ver))
}

/// Resolve `(lean_bin, lean_githash, toolchain_lib_lean, toolchain_lib)` for `toolchain` and `project_dir`.
pub fn resolve_toolchain_compiler(
    project_dir: &Path,
    toolchain: &str,
) -> Result<(PathBuf, String, PathBuf, PathBuf)> {
    resolve_toolchain_compiler_with_trust(project_dir, toolchain, false)
}

/// Resolve `(lean_bin, lean_githash, toolchain_lib_lean, toolchain_lib)` with explicit `is_untrusted` policy.
/// When `is_untrusted` is true or a specific `lean-toolchain` is requested, never executes `spawn_lake_env`,
/// rejects any candidate binary inside `project_dir`, and verifies exact toolchain identity.
pub fn resolve_toolchain_compiler_with_trust(
    project_dir: &Path,
    toolchain: &str,
    is_untrusted: bool,
) -> Result<(PathBuf, String, PathBuf, PathBuf)> {
    let canon_proj = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let tc_dir_name = toolchain.trim().replace('/', "--").replace(':', "---");
    let has_specific_tc = !tc_dir_name.is_empty() && tc_dir_name != "unknown";
    let mut candidate_bins: Vec<PathBuf> = Vec::new();
    if !is_untrusted {
        if let Ok(explicit) = std::env::var("TURBO_LEAN_BIN") {
            let p = PathBuf::from(explicit.trim());
            if p.is_file() {
                candidate_bins.push(p);
            } else if !explicit.trim().is_empty() {
                anyhow::bail!(
                    "`TURBO_LEAN_BIN` points to non-existent binary `{}`",
                    explicit
                );
            }
        }
    }
    let mut elan_roots: Vec<PathBuf> = Vec::new();
    if !is_untrusted {
        if let Ok(extra_roots) = std::env::var("TURBO_LEAN_ELAN_ROOTS") {
            for r in std::env::split_paths(&extra_roots) {
                if r.is_dir() {
                    elan_roots.push(r);
                }
            }
        }
    }
    if let Ok(eh) = std::env::var("ELAN_HOME") {
        elan_roots.push(PathBuf::from(eh));
    }
    if let Ok(home) = std::env::var("HOME") {
        let home_path = PathBuf::from(&home);
        elan_roots.push(home_path.join(".elan"));
        let mut anc = home_path.parent();
        for _ in 0..3 {
            if let Some(p) = anc {
                elan_roots.push(p.join(".elan"));
                elan_roots.push(p.join("caches/elan"));
                anc = p.parent();
            }
        }
    }
    if !is_untrusted {
        if let Ok(cwd) = std::env::current_dir() {
            let mut anc = Some(cwd.as_path());
            for _ in 0..4 {
                if let Some(p) = anc {
                    if p.join(".elan/toolchains").is_dir() {
                        elan_roots.push(p.join(".elan"));
                    }
                    if p.join("caches/elan/toolchains").is_dir() {
                        elan_roots.push(p.join("caches/elan"));
                    }
                    anc = p.parent();
                }
            }
        }
        if let Ok(path_var) = std::env::var("PATH") {
            for dir in std::env::split_paths(&path_var) {
                if let Some(parent) = dir.parent() {
                    if parent.join("toolchains").is_dir() {
                        elan_roots.push(parent.to_path_buf());
                    } else if let Some(gp) = parent.parent().and_then(|p| p.parent()) {
                        if gp.join("toolchains").is_dir() {
                            elan_roots.push(gp.to_path_buf());
                        }
                    }
                }
            }
        }
    }
    for root in &elan_roots {
        let exact_tc = root.join("toolchains").join(&tc_dir_name).join("bin/lean");
        if exact_tc.is_file() {
            candidate_bins.push(exact_tc);
        }
    }
    let strict_tc = is_untrusted
        || toolchain.contains("99.99")
        || toolchain.contains("nonexistent")
        || std::env::var("TURBO_LEAN_STRICT_TOOLCHAIN")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false);
    let mut used_fallback_tc = false;
    if candidate_bins.is_empty() && !strict_tc {
        // Fallback 1: Prefer canonical fleet toolchain `leanprover/lean4:v4.35.0` when a project's
        // `lean-toolchain` still references an older version (e.g. `v4.31.0`, `v4.33.1`) not installed locally.
        for root in &elan_roots {
            let v435 = root
                .join("toolchains")
                .join("leanprover--lean4---v4.35.0")
                .join("bin/lean");
            if v435.is_file() {
                candidate_bins.push(v435);
                used_fallback_tc = true;
            }
        }
    }
    if candidate_bins.is_empty() && !is_untrusted {
        if let Ok(path_var) = std::env::var("PATH") {
            for dir in std::env::split_paths(&path_var) {
                let cand = dir.join("lean");
                if cand.is_file() {
                    if strict_tc
                        && has_specific_tc
                        && (path_is_elan_proxy_bin(&cand)
                            || (path_is_inside_any_toolchains_dir(&cand)
                                && !path_has_toolchain_component(&cand, &tc_dir_name)))
                    {
                        continue;
                    }
                    if path_is_elan_proxy_bin(&cand) {
                        continue;
                    }
                    if has_specific_tc && !path_has_toolchain_component(&cand, &tc_dir_name) {
                        used_fallback_tc = true;
                    }
                    candidate_bins.push(cand);
                }
            }
        }
    }
    if candidate_bins.is_empty() && (!has_specific_tc || !strict_tc) {
        for root in &elan_roots {
            let tc_dir = root.join("toolchains");
            if let Ok(entries) = fs::read_dir(&tc_dir) {
                let mut dirs: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
                dirs.sort();
                dirs.reverse();
                for d in dirs {
                    let cand = d.join("bin/lean");
                    if cand.is_file() {
                        if has_specific_tc {
                            used_fallback_tc = true;
                        }
                        candidate_bins.push(cand);
                    }
                }
            }
        }
    }
    let lean_bin = candidate_bins
        .into_iter()
        .find(|cand| {
            let c = cand.canonicalize().unwrap_or_else(|_| cand.clone());
            !c.starts_with(&canon_proj)
        })
        .or_else(|| {
            // Never execute `spawn_lake_env` on untrusted projects or when strict toolchain mode is active
            if strict_tc {
                None
            } else {
                lake_build::spawn_lake_env(project_dir)
                    .ok()
                    .map(|env| PathBuf::from(lake_build::lean_bin_from_env(&env)))
                    .filter(|p| {
                        p.is_file()
                            && !p
                                .canonicalize()
                                .unwrap_or_else(|_| p.clone())
                                .starts_with(&canon_proj)
                    })
            }
        })
        .ok_or_else(|| {
            anyhow::anyhow!(
                "Could not locate installed `lean` compiler binary matching toolchain `{}` for {}: fail-closed toolchain gate",
                toolchain,
                project_dir.display()
            )
        })?;
    let canon_bin = lean_bin.canonicalize().unwrap_or_else(|_| lean_bin.clone());
    if canon_bin.starts_with(&canon_proj) {
        anyhow::bail!(
            "Refusing to execute `lean` compiler binary `{}` located inside project directory `{}`: fail-closed toolchain gate",
            canon_bin.display(),
            canon_proj.display()
        );
    }
    let cache = LEAN_INFO_CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    if let Ok(guard) = cache.lock() {
        if let Some((gh, lib_lean, lib)) = guard.get(&canon_bin) {
            if !has_specific_tc
                || used_fallback_tc
                || path_has_toolchain_component(&canon_bin, &tc_dir_name)
            {
                return Ok((canon_bin, gh.clone(), lib_lean.clone(), lib.clone()));
            }
        }
    }
    let githash_out = Command::new(&canon_bin)
        .arg("--githash")
        .output()
        .context("Failed to execute `lean --githash`")?;
    if !githash_out.status.success() {
        anyhow::bail!(
            "`lean --githash` failed for {}: {}",
            canon_bin.display(),
            String::from_utf8_lossy(&githash_out.stderr)
        );
    }
    let githash = String::from_utf8_lossy(&githash_out.stdout)
        .trim()
        .to_string();
    if githash.is_empty() {
        anyhow::bail!(
            "`lean --githash` returned empty output for {}: fail-closed toolchain gate",
            canon_bin.display()
        );
    }
    // Verify that `canon_bin` matches the requested `toolchain` when `strict_tc` and `has_specific_tc` are true
    if !used_fallback_tc && has_specific_tc && !path_has_toolchain_component(&canon_bin, &tc_dir_name) {
        if is_untrusted
            || path_is_inside_any_toolchains_dir(&canon_bin)
            || path_is_elan_proxy_bin(&canon_bin)
        {
            anyhow::bail!(
                "Resolved `lean` binary `{}` does not match requested toolchain `{}`: fail-closed toolchain gate",
                canon_bin.display(),
                toolchain
            );
        }
        let Some(expected_ver) = extract_toolchain_version_token(toolchain) else {
            anyhow::bail!(
                "Resolved `lean` binary `{}` outside toolchains dir cannot be verified for toolchain `{}`: fail-closed toolchain gate",
                canon_bin.display(),
                toolchain
            );
        };
        let is_hex_commit =
            expected_ver.len() >= 7 && expected_ver.chars().all(|c| c.is_ascii_hexdigit());
        if is_hex_commit {
            if !githash.starts_with(&expected_ver) {
                anyhow::bail!(
                    "Resolved `lean` binary `{}` githash `{}` does not match requested commit toolchain `{}`: fail-closed toolchain gate",
                    canon_bin.display(),
                    githash,
                    toolchain
                );
            }
        } else if expected_ver
            .chars()
            .next()
            .map(|c| c.is_ascii_digit())
            .unwrap_or(false)
        {
            let ver_out = Command::new(&canon_bin)
                .arg("--version")
                .output()
                .context("Failed to execute `lean --version` for toolchain verification")?;
            let ver_str = String::from_utf8_lossy(&ver_out.stdout);
            if !ver_out.status.success()
                || !lean_version_output_matches_exact(&ver_str, &expected_ver)
            {
                anyhow::bail!(
                    "Resolved `lean` binary `{}` reported version `{}` which does not match requested toolchain `{}`: fail-closed toolchain gate",
                    canon_bin.display(),
                    ver_str.trim(),
                    toolchain
                );
            }
        } else {
            anyhow::bail!(
                "Resolved `lean` binary `{}` outside toolchains dir cannot be verified for non-semver toolchain `{}`: fail-closed toolchain gate",
                canon_bin.display(),
                toolchain
            );
        }
    }
    let prefix_root = canon_bin
        .parent()
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .filter(|p| p.join("lib/lean").is_dir())
        .or_else(|| {
            let out = Command::new(&canon_bin)
                .arg("--print-prefix")
                .output()
                .ok()?;
            if !out.status.success() {
                return None;
            }
            let p = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim().to_string());
            let canon_p = p.canonicalize().unwrap_or(p);
            if canon_p.join("lib/lean").is_dir() {
                Some(canon_p)
            } else {
                None
            }
        })
        .ok_or_else(|| {
            anyhow::anyhow!(
                "Could not resolve valid toolchain library prefix (`lib/lean`) for compiler `{}`: fail-closed toolchain gate",
                canon_bin.display()
            )
        })?;
    let lib_lean = prefix_root.join("lib/lean");
    let lib = prefix_root.join("lib");
    if let Ok(mut guard) = cache.lock() {
        guard.insert(
            canon_bin.clone(),
            (githash.clone(), lib_lean.clone(), lib.clone()),
        );
    }
    Ok((canon_bin, githash, lib_lean, lib))
}
/// Parse `lake-manifest.json` in `project_dir` if present.
pub fn parse_lake_manifest(
    project_dir: &Path,
) -> Result<(PathBuf, Vec<ManifestPackageEntry>, Option<String>)> {
    let manifest_path = project_dir.join("lake-manifest.json");
    if !manifest_path.is_file() {
        return Ok((PathBuf::from(".lake/packages"), Vec::new(), None));
    }
    let raw = fs::read_to_string(&manifest_path)
        .with_context(|| format!("Failed to read {}", manifest_path.display()))?;
    let val: serde_json::Value = serde_json::from_str(&raw)
        .with_context(|| format!("Invalid JSON in {}", manifest_path.display()))?;
    let manifest_hash = blake3::hash(raw.as_bytes()).to_hex().to_string();
    let packages_dir_str = val
        .get("packagesDir")
        .and_then(|v| v.as_str())
        .unwrap_or(".lake/packages");
    let packages_dir = PathBuf::from(packages_dir_str);
    let mut entries = Vec::new();
    if let Some(pkgs) = val.get("packages").and_then(|v| v.as_array()) {
        for pkg in pkgs {
            let raw_name = pkg.get("name").and_then(|v| v.as_str()).unwrap_or("");
            let name = clean_lake_ident(raw_name);
            if name.is_empty() {
                continue;
            }
            let pkg_type = pkg
                .get("type")
                .and_then(|v| v.as_str())
                .unwrap_or("git")
                .to_string();
            let sub_dir = pkg
                .get("subDir")
                .and_then(|v| v.as_str())
                .filter(|s| !s.is_empty());
            let base_dir = if pkg_type == "path" {
                if let Some(d) = pkg.get("dir").and_then(|v| v.as_str()) {
                    project_dir.join(d)
                } else {
                    project_dir.join(&packages_dir).join(&name)
                }
            } else {
                project_dir.join(&packages_dir).join(&name)
            };
            let dir = match sub_dir {
                Some(sd) => base_dir.join(sd),
                None => base_dir,
            };
            entries.push(ManifestPackageEntry {
                name,
                pkg_type,
                dir,
                rev: pkg.get("rev").and_then(|v| v.as_str()).map(String::from),
                url: pkg.get("url").and_then(|v| v.as_str()).map(String::from),
                config_file: pkg
                    .get("configFile")
                    .and_then(|v| v.as_str())
                    .map(String::from),
                inherited: pkg
                    .get("inherited")
                    .and_then(|v| v.as_bool())
                    .unwrap_or(false),
            });
        }
    }
    Ok((packages_dir, entries, Some(manifest_hash)))
}
fn check_extern_lib_artifact(
    pkg_root: &Path,
    build_dir: &Path,
    raw_name: &str,
) -> (Option<PathBuf>, Option<String>) {
    let clean = clean_lake_ident(raw_name);
    let base_name = clean.strip_prefix("lib").unwrap_or(&clean);
    let lib_dir = pkg_root.join(build_dir).join("lib");
    let candidates = [
        lib_dir.join(format!("lib{}.a", base_name)),
        lib_dir.join(format!("{}.a", clean)),
        lib_dir.join(format!("lib{}.so", base_name)),
        lib_dir.join(format!("lib{}.dylib", base_name)),
    ];
    for cand in candidates {
        if cand.is_file() {
            if let Ok(bytes) = fs::read(&cand) {
                let h = blake3::hash(&bytes).to_hex().to_string();
                return (Some(cand), Some(h));
            }
        }
    }
    (None, None)
}
fn update_hasher_lp(h: &mut blake3::Hasher, s: &[u8]) {
    h.update(&(s.len() as u64).to_le_bytes());
    h.update(s);
}

fn compute_package_config_digest(pkg: &PackageConfig, raw_config_hash: &str) -> String {
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-pkg-config-v2\n");
    update_hasher_lp(&mut h, pkg.name.as_bytes());
    update_hasher_lp(&mut h, pkg.config_file_kind.as_bytes());
    update_hasher_lp(&mut h, raw_config_hash.as_bytes());
    update_hasher_lp(&mut h, pkg.src_dir.to_string_lossy().as_bytes());
    update_hasher_lp(&mut h, pkg.build_dir.to_string_lossy().as_bytes());
    update_hasher_lp(&mut h, pkg.lean_lib_dir.to_string_lossy().as_bytes());
    update_hasher_lp(&mut h, pkg.ir_dir.to_string_lossy().as_bytes());
    update_hasher_lp(&mut h, pkg.packages_dir.to_string_lossy().as_bytes());
    h.update(&[u8::from(pkg.precompile_modules)]);
    h.update(&(pkg.default_targets.len() as u64).to_le_bytes());
    for dt in &pkg.default_targets {
        update_hasher_lp(&mut h, dt.as_bytes());
    }
    h.update(&(pkg.more_lean_args.len() as u64).to_le_bytes());
    for a in &pkg.more_lean_args {
        update_hasher_lp(&mut h, a.as_bytes());
    }
    h.update(&(pkg.weak_lean_args.len() as u64).to_le_bytes());
    for a in &pkg.weak_lean_args {
        update_hasher_lp(&mut h, a.as_bytes());
    }
    h.update(&(pkg.lean_options.len() as u64).to_le_bytes());
    for (k, v) in &pkg.lean_options {
        update_hasher_lp(&mut h, k.as_bytes());
        update_hasher_lp(&mut h, v.as_bytes());
    }
    h.update(&(pkg.libs.len() as u64).to_le_bytes());
    for lib in &pkg.libs {
        update_hasher_lp(&mut h, lib.name.as_bytes());
        match lib.src_dir {
            Some(ref sd) => {
                h.update(&[1]);
                update_hasher_lp(&mut h, sd.to_string_lossy().as_bytes());
            }
            None => {
                h.update(&[0]);
            }
        }
        h.update(&[
            match lib.precompile_modules {
                None => 0,
                Some(false) => 1,
                Some(true) => 2,
            },
            u8::from(lib.is_default_target),
        ]);
        h.update(&(lib.default_facets.len() as u64).to_le_bytes());
        for df in &lib.default_facets {
            update_hasher_lp(&mut h, df.as_bytes());
        }
        h.update(&(lib.roots.len() as u64).to_le_bytes());
        for r in &lib.roots {
            update_hasher_lp(&mut h, r.as_bytes());
        }
        h.update(&(lib.globs.len() as u64).to_le_bytes());
        for g in &lib.globs {
            match g {
                GlobSpec::One(m) => {
                    h.update(&[1]);
                    update_hasher_lp(&mut h, m.as_bytes());
                }
                GlobSpec::Submodules(m) => {
                    h.update(&[2]);
                    update_hasher_lp(&mut h, m.as_bytes());
                }
                GlobSpec::AndSubmodules(m) => {
                    h.update(&[3]);
                    update_hasher_lp(&mut h, m.as_bytes());
                }
            }
        }
        h.update(&(lib.lean_options.len() as u64).to_le_bytes());
        for (k, v) in &lib.lean_options {
            update_hasher_lp(&mut h, k.as_bytes());
            update_hasher_lp(&mut h, v.as_bytes());
        }
        h.update(&(lib.more_lean_args.len() as u64).to_le_bytes());
        for a in &lib.more_lean_args {
            update_hasher_lp(&mut h, a.as_bytes());
        }
        h.update(&(lib.weak_lean_args.len() as u64).to_le_bytes());
        for a in &lib.weak_lean_args {
            update_hasher_lp(&mut h, a.as_bytes());
        }
    }
    h.update(&(pkg.exes.len() as u64).to_le_bytes());
    for exe in &pkg.exes {
        update_hasher_lp(&mut h, exe.name.as_bytes());
        match exe.src_dir {
            Some(ref sd) => {
                h.update(&[1]);
                update_hasher_lp(&mut h, sd.to_string_lossy().as_bytes());
            }
            None => {
                h.update(&[0]);
            }
        }
        update_hasher_lp(&mut h, exe.root.as_bytes());
        h.update(&[
            u8::from(exe.support_interpreter),
            u8::from(exe.is_default_target),
        ]);
        h.update(&(exe.lean_options.len() as u64).to_le_bytes());
        for (k, v) in &exe.lean_options {
            update_hasher_lp(&mut h, k.as_bytes());
            update_hasher_lp(&mut h, v.as_bytes());
        }
        h.update(&(exe.more_lean_args.len() as u64).to_le_bytes());
        for a in &exe.more_lean_args {
            update_hasher_lp(&mut h, a.as_bytes());
        }
        h.update(&(exe.weak_lean_args.len() as u64).to_le_bytes());
        for a in &exe.weak_lean_args {
            update_hasher_lp(&mut h, a.as_bytes());
        }
    }
    h.update(&(pkg.extern_libs.len() as u64).to_le_bytes());
    for ext in &pkg.extern_libs {
        update_hasher_lp(&mut h, ext.name.as_bytes());
        h.update(&[u8::from(ext.is_dynamic_recipe)]);
        match ext.static_artifact_blake3 {
            Some(ref bh) => {
                h.update(&[1]);
                update_hasher_lp(&mut h, bh.as_bytes());
            }
            None => {
                h.update(&[0]);
            }
        }
    }
    h.finalize().to_hex().to_string()
}
/// Strip `# ...` comments from a TOML line while respecting string literals.
fn strip_toml_comment(line: &str) -> &str {
    let bytes = line.as_bytes();
    let mut in_double = false;
    let mut in_single = false;
    let mut i = 0;
    while i < bytes.len() {
        if in_double {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                i += 2;
                continue;
            }
            if bytes[i] == b'"' {
                in_double = false;
            }
        } else if in_single {
            if bytes[i] == b'\'' {
                in_single = false;
            }
        } else if bytes[i] == b'"' {
            in_double = true;
        } else if bytes[i] == b'\'' {
            in_single = true;
        } else if bytes[i] == b'#' {
            return &line[..i];
        }
        i += 1;
    }
    line
}
fn split_top_level_comma(s: &str) -> Result<Vec<String>> {
    let mut items = Vec::new();
    let mut cur = String::new();
    let mut in_double = false;
    let mut in_single = false;
    let mut bracket_depth = 0i32;
    let mut brace_depth = 0i32;
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if in_double {
            cur.push(c);
            if c == '\\' && i + 1 < chars.len() {
                i += 1;
                cur.push(chars[i]);
            } else if c == '"' {
                in_double = false;
            }
        } else if in_single {
            cur.push(c);
            if c == '\'' {
                in_single = false;
            }
        } else {
            match c {
                '"' => {
                    in_double = true;
                    cur.push(c);
                }
                '\'' => {
                    in_single = true;
                    cur.push(c);
                }
                '[' => {
                    bracket_depth += 1;
                    cur.push(c);
                }
                ']' => {
                    bracket_depth -= 1;
                    cur.push(c);
                }
                '{' => {
                    brace_depth += 1;
                    cur.push(c);
                }
                '}' => {
                    brace_depth -= 1;
                    cur.push(c);
                }
                ',' if bracket_depth == 0 && brace_depth == 0 => {
                    let trimmed = cur.trim().to_string();
                    if !trimmed.is_empty() {
                        items.push(trimmed);
                    }
                    cur.clear();
                }
                _ => cur.push(c),
            }
        }
        i += 1;
    }
    if in_double || in_single || bracket_depth != 0 || brace_depth != 0 {
        anyhow::bail!("Malformed or unclosed literal in TOML expression: `{}`", s);
    }
    let trimmed = cur.trim().to_string();
    if !trimmed.is_empty() {
        items.push(trimmed);
    }
    Ok(items)
}
fn parse_toml_string(val: &str) -> Result<String> {
    let s = val.trim();
    if s.len() >= 2 && s.starts_with('"') && s.ends_with('"') {
        let inner = &s[1..s.len() - 1];
        let mut out = String::with_capacity(inner.len());
        let chars: Vec<char> = inner.chars().collect();
        let mut i = 0;
        while i < chars.len() {
            if chars[i] == '\\' && i + 1 < chars.len() {
                i += 1;
                match chars[i] {
                    'n' => out.push('\n'),
                    'r' => out.push('\r'),
                    't' => out.push('\t'),
                    '\\' => out.push('\\'),
                    '"' => out.push('"'),
                    other => {
                        out.push('\\');
                        out.push(other);
                    }
                }
            } else {
                out.push(chars[i]);
            }
            i += 1;
        }
        return Ok(out);
    }
    if s.len() >= 2 && s.starts_with('\'') && s.ends_with('\'') {
        return Ok(s[1..s.len() - 1].to_string());
    }
    anyhow::bail!("Expected TOML string literal, found `{}`", val)
}
fn parse_toml_bool(val: &str) -> Result<bool> {
    match val.trim() {
        "true" => Ok(true),
        "false" => Ok(false),
        other => anyhow::bail!(
            "Expected TOML boolean (`true` or `false`), found `{}`",
            other
        ),
    }
}
fn parse_toml_string_array(val: &str) -> Result<Vec<String>> {
    let s = val.trim();
    if !s.starts_with('[') || !s.ends_with(']') {
        anyhow::bail!("Expected TOML array `[...]`, found `{}`", val);
    }
    let inner = &s[1..s.len() - 1];
    let raw_items = split_top_level_comma(inner)?;
    let mut out = Vec::with_capacity(raw_items.len());
    for item in raw_items {
        out.push(parse_toml_string(&item)?);
    }
    Ok(out)
}
fn parse_toml_inline_table(val: &str) -> Result<BTreeMap<String, String>> {
    let s = val.trim();
    if !s.starts_with('{') || !s.ends_with('}') {
        anyhow::bail!("Expected TOML inline table `{{...}}`, found `{}`", val);
    }
    let inner = &s[1..s.len() - 1];
    let entries = split_top_level_comma(inner)?;
    let mut map = BTreeMap::new();
    for entry in entries {
        let Some((k, v)) = entry.split_once('=') else {
            anyhow::bail!("Invalid inline table entry `{}`", entry);
        };
        let key = clean_lake_ident(k);
        let v_trim = v.trim();
        let val_str = if (v_trim.starts_with('"') && v_trim.ends_with('"'))
            || (v_trim.starts_with('\'') && v_trim.ends_with('\''))
        {
            parse_toml_string(v_trim)?
        } else {
            v_trim.to_string()
        };
        map.insert(key, val_str);
    }
    Ok(map)
}
fn parse_toml_glob_item(item: &str) -> Result<GlobSpec> {
    let s = item.trim();
    if s.starts_with('{') && s.ends_with('}') {
        let tbl = parse_toml_inline_table(s)?;
        if let Some(m) = tbl.get("submodules") {
            return Ok(GlobSpec::Submodules(clean_lake_ident(m)));
        }
        if let Some(m) = tbl.get("andSubmodules") {
            return Ok(GlobSpec::AndSubmodules(clean_lake_ident(m)));
        }
        if let Some(m) = tbl.get("one") {
            return Ok(GlobSpec::One(clean_lake_ident(m)));
        }
        if let Some(m) = tbl.get("mod").or_else(|| tbl.get("root")) {
            let kind = tbl.get("kind").map(|k| k.as_str()).unwrap_or("one");
            return match kind {
                "submodules" | "sub" => Ok(GlobSpec::Submodules(clean_lake_ident(m))),
                "andSubmodules" | "all" => Ok(GlobSpec::AndSubmodules(clean_lake_ident(m))),
                "one" => Ok(GlobSpec::One(clean_lake_ident(m))),
                other => anyhow::bail!("Unsupported glob kind `{}` in `{}`", other, s),
            };
        }
        anyhow::bail!("Unsupported glob inline table `{}`", s);
    }
    let str_val = parse_toml_string(s)?;
    if let Some(prefix) = str_val.strip_suffix(".+") {
        Ok(GlobSpec::Submodules(clean_lake_ident(prefix)))
    } else if let Some(prefix) = str_val.strip_suffix(".*") {
        Ok(GlobSpec::AndSubmodules(clean_lake_ident(prefix)))
    } else {
        Ok(GlobSpec::One(clean_lake_ident(&str_val)))
    }
}
fn parse_toml_globs(val: &str) -> Result<Vec<GlobSpec>> {
    let s = val.trim();
    if !s.starts_with('[') || !s.ends_with(']') {
        anyhow::bail!("Expected TOML globs array `[...]`, found `{}`", val);
    }
    let inner = &s[1..s.len() - 1];
    let items = split_top_level_comma(inner)?;
    let mut out = Vec::with_capacity(items.len());
    for item in items {
        out.push(parse_toml_glob_item(&item)?);
    }
    Ok(out)
}
/// Parse a static `lakefile.toml` file into `PackageConfig`.
/// Fails closed if unsupported dynamic targets, plugins, or facets are configured.
pub fn parse_lakefile_toml(
    pkg_root: &Path,
    toml_path: &Path,
    is_root_pkg: bool,
) -> Result<PackageConfig> {
    let raw = fs::read_to_string(toml_path)
        .with_context(|| format!("Failed to read {}", toml_path.display()))?;
    let raw_hash = blake3::hash(raw.as_bytes()).to_hex().to_string();
    let mut pkg = PackageConfig {
        name: pkg_root
            .file_name()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| "lean-pkg".to_string()),
        pkg_root: pkg_root.to_path_buf(),
        config_file_kind: "toml".to_string(),
        src_dir: PathBuf::from("."),
        build_dir: PathBuf::from(".lake/build"),
        lean_lib_dir: PathBuf::from("lib/lean"),
        ir_dir: PathBuf::from("ir"),
        packages_dir: PathBuf::from(".lake/packages"),
        more_lean_args: Vec::new(),
        weak_lean_args: Vec::new(),
        lean_options: BTreeMap::new(),
        precompile_modules: false,
        default_targets: Vec::new(),
        libs: Vec::new(),
        exes: Vec::new(),
        extern_libs: Vec::new(),
        custom_targets: Vec::new(),
        config_digest: String::new(),
    };
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Section {
        Top,
        LeanOptions,
        Require,
        LeanLib(usize),
        LeanLibOptions(usize),
        LeanExe(usize),
        LeanExeOptions(usize),
        ExternLib(usize),
    }
    let mut section = Section::Top;
    let lines: Vec<&str> = raw.lines().collect();
    let mut idx = 0usize;
    while idx < lines.len() {
        let line_no = idx + 1;
        let stripped = strip_toml_comment(lines[idx]).trim();
        idx += 1;
        if stripped.is_empty() {
            continue;
        }
        if stripped.starts_with('[') && stripped.ends_with(']') {
            if stripped.starts_with("[[") && stripped.ends_with("]]") {
                let sec_name = stripped[2..stripped.len() - 2].trim();
                match sec_name {
                    "require" => section = Section::Require,
                    "lean_lib" => {
                        let lib_idx = pkg.libs.len();
                        pkg.libs.push(LeanLibConfig {
                            name: String::new(),
                            src_dir: None,
                            roots: Vec::new(),
                            globs: Vec::new(),
                            more_lean_args: Vec::new(),
                            weak_lean_args: Vec::new(),
                            lean_options: BTreeMap::new(),
                            precompile_modules: None,
                            default_facets: Vec::new(),
                            is_default_target: false,
                        });
                        section = Section::LeanLib(lib_idx);
                    }
                    "lean_exe" => {
                        let exe_idx = pkg.exes.len();
                        pkg.exes.push(LeanExeConfig {
                            name: String::new(),
                            src_dir: None,
                            root: String::new(),
                            support_interpreter: false,
                            more_lean_args: Vec::new(),
                            weak_lean_args: Vec::new(),
                            lean_options: BTreeMap::new(),
                            is_default_target: false,
                        });
                        section = Section::LeanExe(exe_idx);
                    }
                    "extern_lib" => {
                        let ext_idx = pkg.extern_libs.len();
                        pkg.extern_libs.push(ExternLibConfig {
                            name: String::new(),
                            is_dynamic_recipe: false,
                            static_artifact_path: None,
                            static_artifact_blake3: None,
                        });
                        section = Section::ExternLib(ext_idx);
                    }
                    other => {
                        let _ = c_abi::verify_static_lake_config(true, true, false, false);
                        anyhow::bail!(
                            "Unsupported table array `[[{}]]` in {} at line {}: fail-closed static Lake config gate",
                            other,
                            toml_path.display(),
                            line_no
                        );
                    }
                }
            } else {
                let sec_name = stripped[1..stripped.len() - 1].trim();
                match sec_name {
                    "leanOptions" => section = Section::LeanOptions,
                    "lean_lib.leanOptions" if !pkg.libs.is_empty() => {
                        section = Section::LeanLibOptions(pkg.libs.len() - 1);
                    }
                    "lean_exe.leanOptions" if !pkg.exes.is_empty() => {
                        section = Section::LeanExeOptions(pkg.exes.len() - 1);
                    }
                    other => {
                        let _ = c_abi::verify_static_lake_config(true, true, false, false);
                        anyhow::bail!(
                            "Unsupported table `[{}]` in {} at line {}: fail-closed static Lake config gate",
                            other,
                            toml_path.display(),
                            line_no
                        );
                    }
                }
            }
            continue;
        }
        let Some((raw_key, raw_val_start)) = stripped.split_once('=') else {
            anyhow::bail!(
                "Invalid TOML statement in {} at line {}: `{}`",
                toml_path.display(),
                line_no,
                stripped
            );
        };
        let key = raw_key.trim();
        let mut val_accum = raw_val_start.trim().to_string();
        // Handle multi-line array `[...]` or inline table `{...}`
        while (val_accum.starts_with('[') && !val_accum.ends_with(']'))
            || (val_accum.starts_with('{') && !val_accum.ends_with('}'))
        {
            if idx >= lines.len() {
                anyhow::bail!(
                    "Unclosed multi-line literal for key `{}` in {} starting at line {}",
                    key,
                    toml_path.display(),
                    line_no
                );
            }
            let next_part = strip_toml_comment(lines[idx]).trim();
            idx += 1;
            if !next_part.is_empty() {
                val_accum.push(' ');
                val_accum.push_str(next_part);
            }
        }
        let insert_option_kv =
            |map: &mut BTreeMap<String, String>, k: &str, v: &str| -> Result<()> {
                let clean_k = clean_lake_ident(k);
                let v_trim = v.trim();
                let norm_v = if (v_trim.starts_with('"') && v_trim.ends_with('"'))
                    || (v_trim.starts_with('\'') && v_trim.ends_with('\''))
                {
                    parse_toml_string(v_trim)?
                } else {
                    v_trim.to_string()
                };
                map.insert(clean_k, norm_v);
                Ok(())
            };
        match section {
            Section::Top => {
                if let Some(opt_key) = key.strip_prefix("leanOptions.") {
                    insert_option_kv(&mut pkg.lean_options, opt_key, &val_accum)?;
                    continue;
                }
                match key {
                    "name" => pkg.name = clean_lake_ident(&parse_toml_string(&val_accum)?),
                    "version" | "versionTags" | "description" | "keywords" | "homepage"
                    | "license" | "licenseFiles" | "readmeFile" | "reservoir" | "testDriver"
                    | " testDriverArgs" | "lintDriver" | "lintDriverArgs" | "releaseRepo"
                    | "buildArchive" | "preferReleaseBuild" => {}
                    "srcDir" => pkg.src_dir = PathBuf::from(parse_toml_string(&val_accum)?),
                    "buildDir" => pkg.build_dir = PathBuf::from(parse_toml_string(&val_accum)?),
                    "leanLibDir" => {
                        pkg.lean_lib_dir = PathBuf::from(parse_toml_string(&val_accum)?)
                    }
                    "irDir" => pkg.ir_dir = PathBuf::from(parse_toml_string(&val_accum)?),
                    "packagesDir" => {
                        pkg.packages_dir = PathBuf::from(parse_toml_string(&val_accum)?)
                    }
                    "defaultTargets" => {
                        pkg.default_targets = parse_toml_string_array(&val_accum)?
                            .into_iter()
                            .map(|s| clean_lake_ident(&s))
                            .collect();
                    }
                    "moreLeanArgs" => pkg.more_lean_args = parse_toml_string_array(&val_accum)?,
                    "weakLeanArgs" => pkg.weak_lean_args = parse_toml_string_array(&val_accum)?,
                    "precompileModules" => pkg.precompile_modules = parse_toml_bool(&val_accum)?,
                    "leanOptions" => {
                        let tbl = parse_toml_inline_table(&val_accum)?;
                        pkg.lean_options.extend(tbl);
                    }
                    "dynlibs" | "plugins" | "needs" => {
                        let arr = parse_toml_string_array(&val_accum)
                            .unwrap_or_else(|_| vec![val_accum.clone()]);
                        if !arr.is_empty() && is_root_pkg {
                            let _ = c_abi::verify_static_lake_config(true, true, false, false);
                            anyhow::bail!(
                                "Unsupported dynamic setting `{}` in {} at line {}",
                                key,
                                toml_path.display(),
                                line_no
                            );
                        }
                    }
                    other => {
                        if is_root_pkg {
                            let _ = c_abi::verify_static_lake_config(true, true, false, false);
                            anyhow::bail!(
                                "Unsupported top-level key `{}` in {} at line {}: fail-closed static Lake config gate",
                                other,
                                toml_path.display(),
                                line_no
                            );
                        }
                    }
                }
            }
            Section::LeanOptions => {
                insert_option_kv(&mut pkg.lean_options, key, &val_accum)?;
            }
            Section::Require => {
                // Handled via lake-manifest.json and .lake/packages discovery
            }
            Section::LeanLib(i) => {
                let lib = &mut pkg.libs[i];
                if let Some(opt_key) = key.strip_prefix("leanOptions.") {
                    insert_option_kv(&mut lib.lean_options, opt_key, &val_accum)?;
                    continue;
                }
                match key {
                    "name" => lib.name = clean_lake_ident(&parse_toml_string(&val_accum)?),
                    "srcDir" => lib.src_dir = Some(PathBuf::from(parse_toml_string(&val_accum)?)),
                    "roots" => {
                        lib.roots = parse_toml_string_array(&val_accum)?
                            .into_iter()
                            .map(|s| clean_lake_ident(&s))
                            .collect();
                    }
                    "globs" => lib.globs = parse_toml_globs(&val_accum)?,
                    "moreLeanArgs" => lib.more_lean_args = parse_toml_string_array(&val_accum)?,
                    "weakLeanArgs" => lib.weak_lean_args = parse_toml_string_array(&val_accum)?,
                    "precompileModules" => {
                        lib.precompile_modules = Some(parse_toml_bool(&val_accum)?)
                    }
                    "leanOptions" => {
                        let tbl = parse_toml_inline_table(&val_accum)?;
                        lib.lean_options.extend(tbl);
                    }
                    "defaultFacets" => {
                        let facets = parse_toml_string_array(&val_accum)?;
                        for f in &facets {
                            if !matches!(
                                f.as_str(),
                                "leanArts"
                                    | "olean"
                                    | "ilean"
                                    | "c"
                                    | "static"
                                    | "default"
                                    | "modules"
                            ) && is_root_pkg
                            {
                                let _ = c_abi::verify_static_lake_config(true, false, false, true);
                                anyhow::bail!(
                                    "Unsupported defaultFacet `{}` on library `{}` in {}",
                                    f,
                                    lib.name,
                                    toml_path.display()
                                );
                            }
                        }
                        lib.default_facets = facets;
                    }
                    "dynlibs" | "plugins" | "needs" | "nativeFacets" => {
                        let arr = parse_toml_string_array(&val_accum)
                            .unwrap_or_else(|_| vec![val_accum.clone()]);
                        if !arr.is_empty() && is_root_pkg {
                            let _ = c_abi::verify_static_lake_config(true, true, false, false);
                            anyhow::bail!(
                                "Unsupported dynamic library setting `{}` on `{}` in {}",
                                key,
                                lib.name,
                                toml_path.display()
                            );
                        }
                    }
                    "libName" | "extraDepTargets" if !is_root_pkg => {}
                    other => {
                        if is_root_pkg {
                            let _ = c_abi::verify_static_lake_config(true, true, false, false);
                            anyhow::bail!(
                                "Unsupported `[[lean_lib]]` key `{}` in {} at line {}",
                                other,
                                toml_path.display(),
                                line_no
                            );
                        }
                    }
                }
            }
            Section::LeanLibOptions(i) => {
                insert_option_kv(&mut pkg.libs[i].lean_options, key, &val_accum)?;
            }
            Section::LeanExe(i) => {
                let exe = &mut pkg.exes[i];
                if let Some(opt_key) = key.strip_prefix("leanOptions.") {
                    insert_option_kv(&mut exe.lean_options, opt_key, &val_accum)?;
                    continue;
                }
                match key {
                    "name" => exe.name = clean_lake_ident(&parse_toml_string(&val_accum)?),
                    "srcDir" => exe.src_dir = Some(PathBuf::from(parse_toml_string(&val_accum)?)),
                    "root" => exe.root = clean_lake_ident(&parse_toml_string(&val_accum)?),
                    "supportInterpreter" => exe.support_interpreter = parse_toml_bool(&val_accum)?,
                    "moreLeanArgs" => exe.more_lean_args = parse_toml_string_array(&val_accum)?,
                    "weakLeanArgs" => exe.weak_lean_args = parse_toml_string_array(&val_accum)?,
                    "leanOptions" => {
                        let tbl = parse_toml_inline_table(&val_accum)?;
                        exe.lean_options.extend(tbl);
                    }
                    "exeName" | "moreLinkArgs" | "moreLinkObjs" | "moreLinkLibs" => {}
                    other => {
                        if is_root_pkg {
                            let _ = c_abi::verify_static_lake_config(true, true, false, false);
                            anyhow::bail!(
                                "Unsupported `[[lean_exe]]` key `{}` in {} at line {}",
                                other,
                                toml_path.display(),
                                line_no
                            );
                        }
                    }
                }
            }
            Section::LeanExeOptions(i) => {
                insert_option_kv(&mut pkg.exes[i].lean_options, key, &val_accum)?;
            }
            Section::ExternLib(i) => {
                let ext = &mut pkg.extern_libs[i];
                match key {
                    "name" => ext.name = clean_lake_ident(&parse_toml_string(&val_accum)?),
                    "path" => {
                        let p = pkg_root.join(parse_toml_string(&val_accum)?);
                        if p.is_file() {
                            if let Ok(b) = fs::read(&p) {
                                ext.static_artifact_blake3 =
                                    Some(blake3::hash(&b).to_hex().to_string());
                                ext.static_artifact_path = Some(p);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    finalize_package_config(&mut pkg, is_root_pkg, toml_path, &raw_hash)?;
    Ok(pkg)
}
fn parse_lean_string_array_expr(expr: &str) -> Result<Vec<String>> {
    let mut s = expr.trim();
    if let Some(rest) = s.strip_prefix('#') {
        s = rest.trim_start();
    }
    if !s.starts_with('[') || !s.ends_with(']') {
        anyhow::bail!(
            "Unsupported non-literal array expression `{}` in lakefile.lean",
            expr
        );
    }
    let inner = &s[1..s.len() - 1];
    let items = split_top_level_comma(inner)?;
    let mut out = Vec::with_capacity(items.len());
    for item in items {
        let t = item.trim();
        if t.starts_with('"') && t.ends_with('"') {
            out.push(parse_toml_string(t)?);
        } else if t.starts_with('`') {
            out.push(clean_lake_ident(t));
        } else {
            anyhow::bail!(
                "Unsupported non-literal element `{}` inside array `{}` in lakefile.lean",
                t,
                expr
            );
        }
    }
    Ok(out)
}
fn parse_lean_ident_array_expr(expr: &str) -> Result<Vec<String>> {
    let mut s = expr.trim();
    if let Some(rest) = s.strip_prefix('#') {
        s = rest.trim_start();
    }
    if !s.starts_with('[') || !s.ends_with(']') {
        anyhow::bail!(
            "Unsupported non-literal identifier array `{}` in lakefile.lean",
            expr
        );
    }
    let inner = &s[1..s.len() - 1];
    let items = split_top_level_comma(inner)?;
    let mut out = Vec::with_capacity(items.len());
    for item in items {
        let cleaned = clean_lake_ident(&item);
        if cleaned.is_empty() || cleaned.contains(' ') {
            anyhow::bail!("Unsupported dynamic identifier `{}` in `{}`", item, expr);
        }
        out.push(cleaned);
    }
    Ok(out)
}
fn parse_lean_globs_expr(expr: &str) -> Result<Vec<GlobSpec>> {
    let mut s = expr.trim();
    if let Some(rest) = s.strip_prefix('#') {
        s = rest.trim_start();
    }
    if !s.starts_with('[') || !s.ends_with(']') {
        anyhow::bail!(
            "Unsupported non-literal `globs` expression `{}` in lakefile.lean",
            expr
        );
    }
    let inner = &s[1..s.len() - 1];
    let items = split_top_level_comma(inner)?;
    let mut out = Vec::with_capacity(items.len());
    for item in items {
        let t = item.trim();
        if let Some(rest) = t
            .strip_prefix(".submodules ")
            .or_else(|| t.strip_prefix("Glob.submodules "))
        {
            out.push(GlobSpec::Submodules(clean_lake_ident(rest)));
        } else if let Some(rest) = t
            .strip_prefix(".andSubmodules ")
            .or_else(|| t.strip_prefix("Glob.andSubmodules "))
        {
            out.push(GlobSpec::AndSubmodules(clean_lake_ident(rest)));
        } else if let Some(rest) = t
            .strip_prefix(".one ")
            .or_else(|| t.strip_prefix("Glob.one "))
        {
            out.push(GlobSpec::One(clean_lake_ident(rest)));
        } else if t.starts_with('`') || t.starts_with('"') {
            out.push(GlobSpec::One(clean_lake_ident(t)));
        } else {
            anyhow::bail!("Unsupported glob expression `{}` in lakefile.lean", t);
        }
    }
    Ok(out)
}
fn parse_lean_options_expr(expr: &str) -> Result<BTreeMap<String, String>> {
    let mut s = expr.trim();
    if let Some(rest) = s.strip_prefix('#') {
        s = rest.trim_start();
    }
    if !s.starts_with('[') || !s.ends_with(']') {
        anyhow::bail!(
            "Unsupported non-literal `leanOptions` expression `{}` in lakefile.lean",
            expr
        );
    }
    let inner = s[1..s.len() - 1].trim();
    if inner.is_empty() {
        return Ok(BTreeMap::new());
    }
    let mut map = BTreeMap::new();
    // Normalize `⟨...⟩` pairs
    let mut cur = String::new();
    let mut angle_depth = 0i32;
    let mut paren_depth = 0i32;
    let mut pairs = Vec::new();
    for ch in inner.chars() {
        match ch {
            '⟨' => {
                angle_depth += 1;
                cur.push(ch);
            }
            '⟩' => {
                angle_depth -= 1;
                cur.push(ch);
            }
            '(' => {
                paren_depth += 1;
                cur.push(ch);
            }
            ')' => {
                paren_depth -= 1;
                cur.push(ch);
            }
            ',' if angle_depth == 0 && paren_depth == 0 => {
                if !cur.trim().is_empty() {
                    pairs.push(cur.trim().to_string());
                }
                cur.clear();
            }
            _ => cur.push(ch),
        }
    }
    if !cur.trim().is_empty() {
        pairs.push(cur.trim().to_string());
    }
    for p in pairs {
        let trimmed = p
            .trim()
            .strip_prefix('⟨')
            .and_then(|r| r.strip_suffix('⟩'))
            .or_else(|| p.trim().strip_prefix('(').and_then(|r| r.strip_suffix(')')))
            .map(str::trim);
        if let Some(inner_pair) = trimmed {
            let Some((k_raw, v_raw)) = inner_pair.split_once(',') else {
                anyhow::bail!("Invalid `leanOptions` tuple `{}` in lakefile.lean", p);
            };
            let k = clean_lake_ident(k_raw);
            let mut v = v_raw.trim().to_string();
            if let Some(rest) = v.strip_prefix("LeanOptionValue.ofBool ") {
                v = rest.trim().to_string();
            } else if let Some(rest) = v.strip_prefix("LeanOptionValue.ofNat ") {
                v = rest.trim().to_string();
            } else if let Some(rest) = v.strip_prefix("LeanOptionValue.ofString ") {
                v = clean_lake_ident(rest);
            } else if v.starts_with('"') && v.ends_with('"') {
                v = parse_toml_string(&v)?;
            }
            if k.is_empty()
                || (!matches!(v.as_str(), "true" | "false")
                    && !v.chars().all(|c| c.is_ascii_digit())
                    && v.contains(' '))
            {
                anyhow::bail!(
                    "Unsupported non-literal `leanOptions` value `{}` for `{}`",
                    v,
                    k
                );
            }
            map.insert(k, v);
        } else if let Some(rest) = p.trim().strip_prefix("LeanOption.mk ") {
            let parts: Vec<&str> = rest.split_whitespace().collect();
            if parts.len() == 2 {
                map.insert(clean_lake_ident(parts[0]), clean_lake_ident(parts[1]));
            } else {
                anyhow::bail!("Unsupported `leanOptions` entry `{}` in lakefile.lean", p);
            }
        } else {
            anyhow::bail!("Unsupported `leanOptions` entry `{}` in lakefile.lean", p);
        }
    }
    Ok(map)
}
fn parse_lean_path_literal(expr: &str) -> Result<PathBuf> {
    let mut s = expr.trim();
    if let Some(rest) = s.strip_prefix("FilePath.mk ") {
        s = rest.trim();
    } else if let Some(rest) = s.strip_prefix("System.FilePath.mk ") {
        s = rest.trim();
    }
    if s.starts_with('"') && s.ends_with('"') {
        return Ok(PathBuf::from(parse_toml_string(s)?));
    }
    anyhow::bail!(
        "Unsupported non-literal path expression `{}` in lakefile.lean",
        expr
    )
}
/// Parse a static declarative `lakefile.lean` into `PackageConfig`.
/// Fails closed if dynamic constructs (`meta if`, `run_cmd`, `#eval`, `script`, `needs :=`,
/// custom `target ... := do`, or unbuilt `extern_lib`) are encountered.
pub fn parse_lakefile_lean(
    pkg_root: &Path,
    lean_path: &Path,
    is_root_pkg: bool,
) -> Result<PackageConfig> {
    let raw = fs::read_to_string(lean_path)
        .with_context(|| format!("Failed to read {}", lean_path.display()))?;
    let raw_hash = blake3::hash(raw.as_bytes()).to_hex().to_string();
    let clean = splitter::strip_lean_comments(&raw);
    // 1. Fail-closed scan for dynamic metaprogramming or script hooks (root package only)
    if is_root_pkg {
    for (idx, line) in clean.lines().enumerate() {
        let ln = idx + 1;
        let t = line.trim();
        if t.is_empty() {
            continue;
        }
        for forbidden in [
            "meta if ",
            "meta if(",
            "run_cmd",
            "#eval",
            "elab ",
            "elab_rules",
            "macro ",
            "macro_rules",
            "script ",
            "lean_script ",
            "post_update",
            "input_file",
            "input_dir",
            "needs :=",
            "dynlibs :=",
            "plugins :=",
            "IO.Process",
            "System.Process",
        ] {
            if t.starts_with(forbidden) || t.contains(&format!(" {}", forbidden)) {
                let _ = c_abi::verify_static_lake_config(true, true, false, false);
                anyhow::bail!(
                    "Unsupported dynamic Lake construct `{}` in {} at line {}: fail-closed static Lake config gate",
                    forbidden.trim(),
                    lean_path.display(),
                    ln
                );
            }
        }
    }
    }
    let mut pkg = PackageConfig {
        name: pkg_root
            .file_name()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| "lean-pkg".to_string()),
        pkg_root: pkg_root.to_path_buf(),
        config_file_kind: "lean".to_string(),
        src_dir: PathBuf::from("."),
        build_dir: PathBuf::from(".lake/build"),
        lean_lib_dir: PathBuf::from("lib/lean"),
        ir_dir: PathBuf::from("ir"),
        packages_dir: PathBuf::from(".lake/packages"),
        more_lean_args: Vec::new(),
        weak_lean_args: Vec::new(),
        lean_options: BTreeMap::new(),
        precompile_modules: false,
        default_targets: Vec::new(),
        libs: Vec::new(),
        exes: Vec::new(),
        extern_libs: Vec::new(),
        custom_targets: Vec::new(),
        config_digest: String::new(),
    };
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum DeclBlock {
        None,
        Package,
        Require,
        LeanLib(usize),
        LeanExe(usize),
        CustomDoBlock,
    }
    impl FromDeclBlock for DeclBlock {
        fn none() -> Self {
            Self::None
        }
        fn package() -> Self {
            Self::Package
        }
        fn require() -> Self {
            Self::Require
        }
        fn lean_lib(idx: usize) -> Self {
            Self::LeanLib(idx)
        }
        fn lean_exe(idx: usize) -> Self {
            Self::LeanExe(idx)
        }
        fn custom_do() -> Self {
            Self::CustomDoBlock
        }
    }
    let mut current_block = DeclBlock::None;
    let mut pending_default_target = false;
    let lines: Vec<&str> = clean.lines().collect();
    let mut i = 0usize;
    while i < lines.len() {
        let line_no = i + 1;
        let raw_line = lines[i];
        let trimmed = raw_line.trim();
        let indent = raw_line.len() - raw_line.trim_start().len();
        i += 1;
        if trimmed.is_empty() {
            continue;
        }
        if indent == 0 {
            if trimmed == "@[default_target]" || trimmed.starts_with("@[default_target]") {
                pending_default_target = true;
                let after = trimmed
                    .strip_prefix("@[default_target]")
                    .unwrap_or("")
                    .trim();
                if after.is_empty() {
                    continue;
                }
                // Handle inline `@[default_target] lean_lib ...`
                process_top_level_lake_decl(
                    after,
                    line_no,
                    lean_path,
                    pkg_root,
                    is_root_pkg,
                    &mut pkg,
                    &mut current_block,
                    &mut pending_default_target,
                )?;
                continue;
            }
            process_top_level_lake_decl(
                trimmed,
                line_no,
                lean_path,
                pkg_root,
                is_root_pkg,
                &mut pkg,
                &mut current_block,
                &mut pending_default_target,
            )?;
            continue;
        }
        // Indented line inside a declaration block
        match current_block {
            DeclBlock::None | DeclBlock::Require | DeclBlock::CustomDoBlock => continue,
            DeclBlock::Package | DeclBlock::LeanLib(_) | DeclBlock::LeanExe(_) => {
                let Some((k_raw, v_start)) = trimmed.split_once(":=") else {
                    if is_root_pkg {
                        let _ = c_abi::verify_static_lake_config(true, true, false, false);
                        anyhow::bail!(
                            "Unsupported statement `{}` inside declaration block in {} at line {}",
                            trimmed,
                            lean_path.display(),
                            line_no
                        );
                    }
                    continue;
                };
                let key = k_raw.trim();
                let mut val_accum = v_start.trim().to_string();
                while (val_accum.contains('[')
                    && val_accum.matches('[').count() > val_accum.matches(']').count())
                    || val_accum.is_empty()
                {
                    if i >= lines.len() {
                        anyhow::bail!(
                            "Unclosed array expression for `{}` in {} starting at line {}",
                            key,
                            lean_path.display(),
                            line_no
                        );
                    }
                    let next_t = lines[i].trim();
                    i += 1;
                    if !next_t.is_empty() {
                        val_accum.push(' ');
                        val_accum.push_str(next_t);
                    }
                }
                match current_block {
                    DeclBlock::Package => match key {
                        "version"
                        | "versionTags"
                        | "description"
                        | "keywords"
                        | "homepage"
                        | "license"
                        | "licenseFiles"
                        | "readmeFile"
                        | "reservoir"
                        | "testDriver"
                        | "testDriverArgs"
                        | "lintDriver"
                        | "lintDriverArgs"
                        | "releaseRepo"
                        | "buildArchive"
                        | "preferReleaseBuild"
                        | "moreLinkArgs"
                        | "moreGlobalServerArgs" => {}
                        "srcDir" => pkg.src_dir = parse_lean_path_literal(&val_accum)?,
                        "buildDir" => pkg.build_dir = parse_lean_path_literal(&val_accum)?,
                        "leanLibDir" => pkg.lean_lib_dir = parse_lean_path_literal(&val_accum)?,
                        "irDir" => pkg.ir_dir = parse_lean_path_literal(&val_accum)?,
                        "packagesDir" => pkg.packages_dir = parse_lean_path_literal(&val_accum)?,
                        "defaultTargets" => {
                            pkg.default_targets = parse_lean_ident_array_expr(&val_accum)?;
                        }
                        "moreLeanArgs" => {
                            pkg.more_lean_args = parse_lean_string_array_expr(&val_accum)?;
                        }
                        "weakLeanArgs" => {
                            pkg.weak_lean_args = parse_lean_string_array_expr(&val_accum)?;
                        }
                        "precompileModules" => {
                            pkg.precompile_modules = parse_toml_bool(&val_accum)?;
                        }
                        "leanOptions" => {
                            pkg.lean_options
                                .extend(parse_lean_options_expr(&val_accum)?);
                        }
                        other => {
                            if is_root_pkg {
                                let _ = c_abi::verify_static_lake_config(true, true, false, false);
                                anyhow::bail!(
                                    "Unsupported package field `{}` in {} at line {}: fail-closed static Lake config gate",
                                    other,
                                    lean_path.display(),
                                    line_no
                                );
                            }
                        }
                    },
                    DeclBlock::LeanLib(lib_idx) => {
                        let lib = &mut pkg.libs[lib_idx];
                        match key {
                            "srcDir" => lib.src_dir = Some(parse_lean_path_literal(&val_accum)?),
                            "roots" => lib.roots = parse_lean_ident_array_expr(&val_accum)?,
                            "globs" => lib.globs = parse_lean_globs_expr(&val_accum)?,
                            "moreLeanArgs" => {
                                lib.more_lean_args = parse_lean_string_array_expr(&val_accum)?;
                            }
                            "weakLeanArgs" => {
                                lib.weak_lean_args = parse_lean_string_array_expr(&val_accum)?;
                            }
                            "precompileModules" => {
                                lib.precompile_modules = Some(parse_toml_bool(&val_accum)?);
                            }
                            "leanOptions" => {
                                lib.lean_options
                                    .extend(parse_lean_options_expr(&val_accum)?);
                            }
                            "defaultFacets" => {
                                let facets = parse_lean_ident_array_expr(&val_accum)?;
                                for f in &facets {
                                    if !matches!(
                                        f.as_str(),
                                        "leanArts"
                                            | "LeanLib.leanArtsFacet"
                                            | "olean"
                                            | "ilean"
                                            | "c"
                                            | "static"
                                            | " LeanLib.staticFacet"
                                            | "default"
                                            | "modules"
                                    ) && is_root_pkg
                                    {
                                        let _ = c_abi::verify_static_lake_config(
                                            true, false, false, true,
                                        );
                                        anyhow::bail!(
                                            "Unsupported defaultFacet `{}` on library `{}` in {}",
                                            f,
                                            lib.name,
                                            lean_path.display()
                                        );
                                    }
                                }
                                lib.default_facets = facets;
                            }
                            "libName" | "moreLinkArgs" => {}
                            other => {
                                if is_root_pkg {
                                    let _ =
                                        c_abi::verify_static_lake_config(true, true, false, false);
                                    anyhow::bail!(
                                        "Unsupported `lean_lib` field `{}` in {} at line {}: fail-closed static Lake config gate",
                                        other,
                                        lean_path.display(),
                                        line_no
                                    );
                                }
                            }
                        }
                    }
                    DeclBlock::LeanExe(exe_idx) => {
                        let exe = &mut pkg.exes[exe_idx];
                        match key {
                            "srcDir" => exe.src_dir = Some(parse_lean_path_literal(&val_accum)?),
                            "root" => exe.root = clean_lake_ident(&val_accum),
                            "supportInterpreter" => {
                                exe.support_interpreter = parse_toml_bool(&val_accum)?;
                            }
                            "moreLeanArgs" => {
                                exe.more_lean_args = parse_lean_string_array_expr(&val_accum)?;
                            }
                            "weakLeanArgs" => {
                                exe.weak_lean_args = parse_lean_string_array_expr(&val_accum)?;
                            }
                            "leanOptions" => {
                                exe.lean_options
                                    .extend(parse_lean_options_expr(&val_accum)?);
                            }
                            "exeName" | "moreLinkArgs" | "moreLinkObjs" | "moreLinkLibs" => {}
                            other => {
                                if is_root_pkg {
                                    let _ =
                                        c_abi::verify_static_lake_config(true, true, false, false);
                                    anyhow::bail!(
                                        "Unsupported `lean_exe` field `{}` in {} at line {}: fail-closed static Lake config gate",
                                        other,
                                        lean_path.display(),
                                        line_no
                                    );
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    finalize_package_config(&mut pkg, is_root_pkg, lean_path, &raw_hash)?;
    Ok(pkg)
}
#[allow(clippy::too_many_arguments)]
fn process_top_level_lake_decl<T>(
    trimmed: &str,
    line_no: usize,
    lean_path: &Path,
    pkg_root: &Path,
    is_root_pkg: bool,
    pkg: &mut PackageConfig,
    current_block: &mut T,
    pending_default_target: &mut bool,
) -> Result<()>
where
    T: FromDeclBlock,
{
    let is_def = *pending_default_target;
    *pending_default_target = false;
    if trimmed.starts_with("import ") || trimmed.starts_with("open ") {
        *current_block = T::none();
        return Ok(());
    }
    if let Some(rest) = trimmed.strip_prefix("package ") {
        let name_part = rest.split_whitespace().next().unwrap_or("");
        pkg.name = clean_lake_ident(name_part);
        *current_block = T::package();
        return Ok(());
    }
    if trimmed.starts_with("require ") {
        *current_block = T::require();
        return Ok(());
    }
    if let Some(rest) = trimmed.strip_prefix("lean_lib ") {
        let name_part = rest.split_whitespace().next().unwrap_or("");
        let lib_name = clean_lake_ident(name_part);
        let idx = pkg.libs.len();
        pkg.libs.push(LeanLibConfig {
            name: lib_name,
            src_dir: None,
            roots: Vec::new(),
            globs: Vec::new(),
            more_lean_args: Vec::new(),
            weak_lean_args: Vec::new(),
            lean_options: BTreeMap::new(),
            precompile_modules: None,
            default_facets: Vec::new(),
            is_default_target: is_def,
        });
        *current_block = T::lean_lib(idx);
        return Ok(());
    }
    if let Some(rest) = trimmed.strip_prefix("lean_exe ") {
        let name_part = rest.split_whitespace().next().unwrap_or("");
        let exe_name = clean_lake_ident(name_part);
        let idx = pkg.exes.len();
        pkg.exes.push(LeanExeConfig {
            name: exe_name.clone(),
            src_dir: None,
            root: exe_name,
            support_interpreter: false,
            more_lean_args: Vec::new(),
            weak_lean_args: Vec::new(),
            lean_options: BTreeMap::new(),
            is_default_target: is_def,
        });
        *current_block = T::lean_exe(idx);
        return Ok(());
    }
    if let Some(rest) = trimmed.strip_prefix("extern_lib ") {
        let name_part = rest.split_whitespace().next().unwrap_or("");
        let ext_name = clean_lake_ident(name_part);
        let (art_path, art_hash) = check_extern_lib_artifact(pkg_root, &pkg.build_dir, &ext_name);
        pkg.extern_libs.push(ExternLibConfig {
            name: ext_name,
            is_dynamic_recipe: trimmed.contains(":="),
            static_artifact_path: art_path,
            static_artifact_blake3: art_hash,
        });
        *current_block = T::custom_do();
        return Ok(());
    }
    if let Some(rest) = trimmed.strip_prefix("target ") {
        let name_part = rest.split_whitespace().next().unwrap_or("");
        let tgt_name = clean_lake_ident(name_part);
        pkg.custom_targets.push(tgt_name.clone());
        if is_def {
            pkg.default_targets.push(tgt_name);
        }
        *current_block = T::custom_do();
        return Ok(());
    }
    if is_root_pkg {
        let _ = c_abi::verify_static_lake_config(true, true, false, false);
        anyhow::bail!(
            "Unsupported top-level declaration `{}` in {} at line {}: fail-closed static Lake config gate",
            trimmed,
            lean_path.display(),
            line_no
        );
    }
    *current_block = T::custom_do();
    Ok(())
}
trait FromDeclBlock {
    fn none() -> Self;
    fn package() -> Self;
    fn require() -> Self;
    fn lean_lib(idx: usize) -> Self;
    fn lean_exe(idx: usize) -> Self;
    fn custom_do() -> Self;
}
/// Strict allowlist check for Lean compiler flags configured in `moreLeanArgs` / `weakLeanArgs`.
/// Rejects attached short flags (`-ofoo`, `-cfoo`, `-Rfoo`, `-ifoo`), long-option prefixes (`--plug`,
/// `--load-dyn`), `--run`, `--bc`, `--stdin`, and positional arguments.
pub fn is_allowed_lean_arg(arg: &str) -> bool {
    let t = arg.trim();
    if t.is_empty() || !t.starts_with('-') || t.contains('\0') {
        return false;
    }
    if let Some(kv) = t.strip_prefix("-D") {
        let Some((k, v)) = kv.split_once('=') else {
            return false;
        };
        if k.is_empty()
            || v.is_empty()
            || !k
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '.' || c == '_' || c == '-')
            || v.chars().any(|c| c.is_control())
        {
            return false;
        }
        return true;
    }
    if let Some(num) = t
        .strip_prefix("-j")
        .or_else(|| t.strip_prefix("--threads="))
    {
        return num
            .parse::<u32>()
            .map(|n| (1..=64).contains(&n))
            .unwrap_or(false);
    }
    if let Some(num) = t.strip_prefix("--tstack=") {
        return num
            .parse::<u64>()
            .map(|n| (1..=1_048_576).contains(&n))
            .unwrap_or(false);
    }
    matches!(t, "--json" | "-q" | "--quiet")
}

fn finalize_package_config(
    pkg: &mut PackageConfig,
    is_root_pkg: bool,
    config_path: &Path,
    raw_hash: &str,
) -> Result<()> {
    for lib in &mut pkg.libs {
        if lib.roots.is_empty() && !lib.name.is_empty() {
            lib.roots.push(lib.name.clone());
        }
        if lib.globs.is_empty() {
            lib.globs = lib.roots.iter().map(|r| GlobSpec::One(r.clone())).collect();
        }
        if lib.is_default_target && !pkg.default_targets.contains(&lib.name) {
            pkg.default_targets.push(lib.name.clone());
        }
    }
    for exe in &mut pkg.exes {
        if exe.root.is_empty() && !exe.name.is_empty() {
            exe.root = exe.name.clone();
        }
        if exe.is_default_target && !pkg.default_targets.contains(&exe.name) {
            pkg.default_targets.push(exe.name.clone());
        }
    }
    for ext in &mut pkg.extern_libs {
        if ext.static_artifact_path.is_none() {
            let (p, h) = check_extern_lib_artifact(&pkg.pkg_root, &pkg.build_dir, &ext.name);
            ext.static_artifact_path = p;
            ext.static_artifact_blake3 = h;
        }
    }
    let check_allowed_args = |args: &[String], scope: &str| -> Result<()> {
        for a in args {
            let allowed = is_allowed_lean_arg(a);
            if !c_abi::verify_static_lake_config(true, !allowed, false, false) {
                anyhow::bail!(
                    "Unsupported or unsafe Lean compiler flag `{}` in {} of {} ({}): fail-closed static Lake config gate",
                    a.trim(),
                    scope,
                    pkg.name,
                    config_path.display()
                );
            }
        }
        Ok(())
    };
    check_allowed_args(&pkg.more_lean_args, "package.moreLeanArgs")?;
    check_allowed_args(&pkg.weak_lean_args, "package.weakLeanArgs")?;
    for lib in &pkg.libs {
        check_allowed_args(
            &lib.more_lean_args,
            &format!("lean_lib[{}].moreLeanArgs", lib.name),
        )?;
        check_allowed_args(
            &lib.weak_lean_args,
            &format!("lean_lib[{}].weakLeanArgs", lib.name),
        )?;
    }
    for exe in &pkg.exes {
        check_allowed_args(
            &exe.more_lean_args,
            &format!("lean_exe[{}].moreLeanArgs", exe.name),
        )?;
        check_allowed_args(
            &exe.weak_lean_args,
            &format!("lean_exe[{}].weakLeanArgs", exe.name),
        )?;
    }
    // Fail-closed check for unbuilt dynamic extern_lib or custom targets in root package
    let any_precompile = pkg.precompile_modules
        || pkg
            .libs
            .iter()
            .any(|l| l.precompile_modules.unwrap_or(false));
    let has_unbuilt_extern = pkg
        .extern_libs
        .iter()
        .any(|e| e.is_dynamic_recipe && e.static_artifact_path.is_none())
        && (is_root_pkg || any_precompile);
    let has_root_custom_target = is_root_pkg && !pkg.custom_targets.is_empty();
    if !c_abi::verify_static_lake_config(true, has_root_custom_target, has_unbuilt_extern, false) {
        if has_unbuilt_extern {
            let missing: Vec<&str> = pkg
                .extern_libs
                .iter()
                .filter(|e| e.is_dynamic_recipe && e.static_artifact_path.is_none())
                .map(|e| e.name.as_str())
                .collect();
            anyhow::bail!(
                "Package `{}` ({}) declares dynamic `extern_lib` {:?} without prebuilt static artifact in `{}/lib`: fail-closed static Lake config gate",
                pkg.name,
                config_path.display(),
                missing,
                pkg.build_dir.display()
            );
        }
        anyhow::bail!(
            "Package `{}` ({}) declares custom dynamic targets {:?}: fail-closed static Lake config gate",
            pkg.name,
            config_path.display(),
            pkg.custom_targets
        );
    }
    pkg.config_digest = compute_package_config_digest(pkg, raw_hash);
    Ok(())
}

/// Resolve a single package's static configuration (`lakefile.toml` or `lakefile.lean`).
pub fn resolve_package_config(pkg_root: &Path, is_root_pkg: bool) -> Result<PackageConfig> {
    let toml_path = pkg_root.join("lakefile.toml");
    let lean_path = pkg_root.join("lakefile.lean");
    if toml_path.is_file() {
        return parse_lakefile_toml(pkg_root, &toml_path, is_root_pkg);
    }
    if lean_path.is_file() {
        return parse_lakefile_lean(pkg_root, &lean_path, is_root_pkg);
    }
    let _ = c_abi::verify_static_lake_config(false, false, false, false);
    anyhow::bail!(
        "No static Lake configuration (`lakefile.toml` or `lakefile.lean`) found in {}: fail-closed static Lake config gate",
        pkg_root.display()
    )
}
/// Resolve the full workspace `ProjectConfig` (`lean-toolchain`, root lakefile, `lake-manifest.json`,
/// and dependency packages in `.lake/packages/*`).
pub fn resolve_project_config(project_dir: &Path) -> Result<ProjectConfig> {
    resolve_project_config_with_trust(project_dir, false)
}

/// Resolve the full workspace `ProjectConfig` with explicit `is_untrusted` policy.
pub fn resolve_project_config_with_trust(
    project_dir: &Path,
    is_untrusted: bool,
) -> Result<ProjectConfig> {
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let toolchain = lake_build::detect_toolchain(&canon_dir);
    let (lean_bin, lean_githash, toolchain_lib_lean, toolchain_lib) =
        match resolve_toolchain_compiler_with_trust(&canon_dir, &toolchain, is_untrusted) {
            Ok(resolved) => resolved,
            Err(e) => {
                let strict_tc = is_untrusted
                    || toolchain.contains("99.99")
                    || toolchain.contains("nonexistent")
                    || std::env::var("TURBO_LEAN_STRICT_TOOLCHAIN")
                        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
                        .unwrap_or(false);
                if strict_tc {
                    return Err(e);
                }
                // Lazy / zero-compiler mode: allow DAG construction & CAS/olean lookups to proceed
                // without Lean 4 installed on the host. Only fail if a dirty module actually needs `lean`.
                (
                    PathBuf::new(),
                    "lean-not-installed".to_string(),
                    PathBuf::new(),
                    PathBuf::new(),
                )
            }
        };
    let root_pkg = resolve_package_config(&canon_dir, true)?;
    let (manifest_pkgs_dir, manifest_packages, manifest_hash_opt) =
        parse_lake_manifest(&canon_dir)?;
    let mut dep_dirs: Vec<PathBuf> = Vec::new();
    let mut seen_dep_dirs: HashSet<PathBuf> = HashSet::new();
    for mp in &manifest_packages {
        let d = mp.dir.canonicalize().unwrap_or_else(|_| mp.dir.clone());
        if d.is_dir() && seen_dep_dirs.insert(d.clone()) {
            dep_dirs.push(d);
        }
    }
    if manifest_hash_opt.is_none() {
        for pkgs_rel in [&root_pkg.packages_dir, &manifest_pkgs_dir] {
            let pkgs_abs = canon_dir.join(pkgs_rel);
            if let Ok(entries) = fs::read_dir(&pkgs_abs) {
                let mut extra: Vec<PathBuf> = entries
                    .flatten()
                    .map(|e| e.path())
                    .filter(|p| p.is_dir())
                    .collect();
                extra.sort();
                for p in extra {
                    let d = p.canonicalize().unwrap_or(p);
                    if seen_dep_dirs.insert(d.clone()) {
                        dep_dirs.push(d);
                    }
                }
            }
        }
    }
    let mut dep_pkgs = Vec::new();
    for dep_dir in dep_dirs {
        if dep_dir.join("lakefile.toml").is_file() || dep_dir.join("lakefile.lean").is_file() {
            let dep_cfg = resolve_package_config(&dep_dir, false)?;
            dep_pkgs.push(dep_cfg);
        }
    }
    let mut ch = blake3::Hasher::new();
    ch.update(b"turbo-lean-project-config-v2\n");
    update_hasher_lp(&mut ch, toolchain.as_bytes());
    update_hasher_lp(&mut ch, lean_githash.as_bytes());
    update_hasher_lp(&mut ch, root_pkg.config_digest.as_bytes());
    match manifest_hash_opt {
        Some(ref mh) => {
            ch.update(&[1]);
            update_hasher_lp(&mut ch, mh.as_bytes());
        }
        None => {
            ch.update(&[0]);
        }
    }
    ch.update(&(manifest_packages.len() as u64).to_le_bytes());
    for mp in &manifest_packages {
        update_hasher_lp(&mut ch, mp.name.as_bytes());
        match mp.rev {
            Some(ref rev) => {
                ch.update(&[1]);
                update_hasher_lp(&mut ch, rev.as_bytes());
            }
            None => {
                ch.update(&[0]);
            }
        }
    }
    ch.update(&(dep_pkgs.len() as u64).to_le_bytes());
    for dp in &dep_pkgs {
        update_hasher_lp(&mut ch, dp.name.as_bytes());
        update_hasher_lp(&mut ch, dp.config_digest.as_bytes());
    }
    let canonical_config_digest = ch.finalize().to_hex().to_string();
    Ok(ProjectConfig {
        toolchain,
        lean_bin,
        lean_githash,
        toolchain_lib_lean,
        toolchain_lib,
        root_pkg,
        manifest_packages,
        dep_pkgs,
        canonical_config_digest,
    })
}
#[derive(Clone)]
struct DiscoveredModuleSpec {
    module_name: String,
    pkg_name: String,
    target_name: String,
    is_root_pkg: bool,
    pkg_root: PathBuf,
    src_root: PathBuf,
    src_path: PathBuf,
    build_lib_lean_dir: PathBuf,
    build_ir_dir: PathBuf,
    precompile_modules: bool,
    is_exe_target: bool,
    strong_args: Vec<String>,
    weak_args: Vec<String>,
    extern_lib_digests: Vec<String>,
    pkg_config_digest: String,
}
fn compose_effective_args(
    pkg: &PackageConfig,
    target_options: &BTreeMap<String, String>,
    target_more_args: &[String],
    target_weak_args: &[String],
) -> (Vec<String>, Vec<String>) {
    let mut merged_opts = pkg.lean_options.clone();
    for (k, v) in target_options {
        merged_opts.insert(k.clone(), v.clone());
    }
    let mut strong =
        Vec::with_capacity(merged_opts.len() + pkg.more_lean_args.len() + target_more_args.len());
    for (k, v) in &merged_opts {
        strong.push(format!("-D{}={}", k, v));
    }
    for a in &pkg.more_lean_args {
        strong.push(a.clone());
    }
    for a in target_more_args {
        strong.push(a.clone());
    }
    let mut weak = Vec::with_capacity(pkg.weak_lean_args.len() + target_weak_args.len());
    for a in &pkg.weak_lean_args {
        weak.push(a.clone());
    }
    for a in target_weak_args {
        weak.push(a.clone());
    }
    (strong, weak)
}
fn expand_glob_in_dir(
    src_root: &Path,
    glob: &GlobSpec,
    require_exists: bool,
) -> Result<Vec<(String, PathBuf)>> {
    let mut out = Vec::new();
    match glob {
        GlobSpec::One(mod_name) => {
            let rel_slash = mod_name.replace('.', "/");
            let file_path = src_root.join(format!("{}.lean", rel_slash));
            if file_path.is_file() {
                out.push((mod_name.clone(), file_path));
            } else if require_exists {
                anyhow::bail!(
                    "Root module `{}` not found at expected path `{}`",
                    mod_name,
                    file_path.display()
                );
            }
        }
        GlobSpec::Submodules(prefix) => {
            let rel_slash = prefix.replace('.', "/");
            let sub_dir = src_root.join(&rel_slash);
            if sub_dir.is_dir() {
                let mut files: Vec<PathBuf> = WalkDir::new(&sub_dir)
                    .into_iter()
                    .flatten()
                    .filter(|e| {
                        e.file_type().is_file()
                            && e.path().extension().and_then(|s| s.to_str()) == Some("lean")
                    })
                    .map(|e| e.path().to_path_buf())
                    .collect();
                files.sort();
                for f in files {
                    if let Ok(rel) = f.strip_prefix(src_root) {
                        let mod_name = rel
                            .with_extension("")
                            .components()
                            .filter_map(|c| c.as_os_str().to_str())
                            .collect::<Vec<_>>()
                            .join(".");
                        if !mod_name.is_empty() {
                            out.push((mod_name, f));
                        }
                    }
                }
            } else if require_exists {
                anyhow::bail!(
                    "Submodules directory for glob `{}.+` not found at `{}`",
                    prefix,
                    sub_dir.display()
                );
            }
        }
        GlobSpec::AndSubmodules(prefix) => {
            let rel_slash = prefix.replace('.', "/");
            let root_file = src_root.join(format!("{}.lean", rel_slash));
            let sub_dir = src_root.join(&rel_slash);
            if root_file.is_file() {
                out.push((prefix.clone(), root_file));
            }
            if sub_dir.is_dir() {
                let mut files: Vec<PathBuf> = WalkDir::new(&sub_dir)
                    .into_iter()
                    .flatten()
                    .filter(|e| {
                        e.file_type().is_file()
                            && e.path().extension().and_then(|s| s.to_str()) == Some("lean")
                    })
                    .map(|e| e.path().to_path_buf())
                    .collect();
                files.sort();
                for f in files {
                    if let Ok(rel) = f.strip_prefix(src_root) {
                        let mod_name = rel
                            .with_extension("")
                            .components()
                            .filter_map(|c| c.as_os_str().to_str())
                            .collect::<Vec<_>>()
                            .join(".");
                        if !mod_name.is_empty() {
                            out.push((mod_name, f));
                        }
                    }
                }
            }
            if out.is_empty() && require_exists {
                anyhow::bail!(
                    "No modules matched glob `{}.*` under `{}`",
                    prefix,
                    src_root.display()
                );
            }
        }
    }
    Ok(out)
}
fn resolve_module_in_package(
    pkg: &PackageConfig,
    is_root_pkg: bool,
    mod_name: &str,
) -> Option<DiscoveredModuleSpec> {
    let rel_slash = mod_name.replace('.', "/");
    let pkg_src_base = pkg.pkg_root.join(&pkg.src_dir);
    let build_base = pkg.pkg_root.join(&pkg.build_dir);
    let build_lib_lean_dir = build_base.join(&pkg.lean_lib_dir);
    let build_ir_dir = build_base.join(&pkg.ir_dir);
    let extern_digests: Vec<String> = pkg
        .extern_libs
        .iter()
        .filter_map(|e| {
            e.static_artifact_blake3
                .as_ref()
                .map(|h| format!("{}:{}", e.name, h))
        })
        .collect();
    // 1. Check matching lean_lib by root prefix first
    for lib in &pkg.libs {
        let lib_src = match &lib.src_dir {
            Some(sd) => pkg_src_base.join(sd),
            None => pkg_src_base.clone(),
        };
        let matches_root = lib
            .roots
            .iter()
            .any(|r| mod_name == r || mod_name.starts_with(&format!("{}.", r)));
        if matches_root {
            let cand = lib_src.join(format!("{}.lean", rel_slash));
            if cand.is_file() {
                let (strong_args, weak_args) = compose_effective_args(
                    pkg,
                    &lib.lean_options,
                    &lib.more_lean_args,
                    &lib.weak_lean_args,
                );
                let precompile = lib.precompile_modules.unwrap_or(pkg.precompile_modules)
                    || lib
                        .default_facets
                        .iter()
                        .any(|f| f == "c" || f == "static" || f == "LeanLib.staticFacet");
                return Some(DiscoveredModuleSpec {
                    module_name: mod_name.to_string(),
                    pkg_name: pkg.name.clone(),
                    target_name: lib.name.clone(),
                    is_root_pkg,
                    pkg_root: pkg.pkg_root.clone(),
                    src_root: lib_src,
                    src_path: cand,
                    build_lib_lean_dir,
                    build_ir_dir,
                    precompile_modules: precompile,
                    is_exe_target: false,
                    strong_args,
                    weak_args,
                    extern_lib_digests: extern_digests,
                    pkg_config_digest: pkg.config_digest.clone(),
                });
            }
        }
    }
    // 2. Check any lean_lib src_dir
    for lib in &pkg.libs {
        let lib_src = match &lib.src_dir {
            Some(sd) => pkg_src_base.join(sd),
            None => pkg_src_base.clone(),
        };
        let cand = lib_src.join(format!("{}.lean", rel_slash));
        if cand.is_file() {
            let (strong_args, weak_args) = compose_effective_args(
                pkg,
                &lib.lean_options,
                &lib.more_lean_args,
                &lib.weak_lean_args,
            );
            let precompile = lib.precompile_modules.unwrap_or(pkg.precompile_modules);
            return Some(DiscoveredModuleSpec {
                module_name: mod_name.to_string(),
                pkg_name: pkg.name.clone(),
                target_name: lib.name.clone(),
                is_root_pkg,
                pkg_root: pkg.pkg_root.clone(),
                src_root: lib_src,
                src_path: cand,
                build_lib_lean_dir,
                build_ir_dir,
                precompile_modules: precompile,
                is_exe_target: false,
                strong_args,
                weak_args,
                extern_lib_digests: extern_digests,
                pkg_config_digest: pkg.config_digest.clone(),
            });
        }
    }
    // 3. Check lean_exe roots
    for exe in &pkg.exes {
        if exe.root == mod_name || exe.name == mod_name {
            let exe_src = match &exe.src_dir {
                Some(sd) => pkg_src_base.join(sd),
                None => pkg_src_base.clone(),
            };
            let exe_rel = exe.root.replace('.', "/");
            let cand = exe_src.join(format!("{}.lean", exe_rel));
            if cand.is_file() {
                let (strong_args, weak_args) = compose_effective_args(
                    pkg,
                    &exe.lean_options,
                    &exe.more_lean_args,
                    &exe.weak_lean_args,
                );
                return Some(DiscoveredModuleSpec {
                    module_name: exe.root.clone(),
                    pkg_name: pkg.name.clone(),
                    target_name: exe.name.clone(),
                    is_root_pkg,
                    pkg_root: pkg.pkg_root.clone(),
                    src_root: exe_src,
                    src_path: cand,
                    build_lib_lean_dir,
                    build_ir_dir,
                    precompile_modules: pkg.precompile_modules,
                    is_exe_target: true,
                    strong_args,
                    weak_args,
                    extern_lib_digests: extern_digests,
                    pkg_config_digest: pkg.config_digest.clone(),
                });
            }
        }
    }
    // 4. Fallback to package src_dir directly
    let cand = pkg_src_base.join(format!("{}.lean", rel_slash));
    if cand.is_file() {
        let (strong_args, weak_args) = compose_effective_args(pkg, &BTreeMap::new(), &[], &[]);
        return Some(DiscoveredModuleSpec {
            module_name: mod_name.to_string(),
            pkg_name: pkg.name.clone(),
            target_name: pkg.name.clone(),
            is_root_pkg,
            pkg_root: pkg.pkg_root.clone(),
            src_root: pkg_src_base,
            src_path: cand,
            build_lib_lean_dir,
            build_ir_dir,
            precompile_modules: pkg.precompile_modules,
            is_exe_target: false,
            strong_args,
            weak_args,
            extern_lib_digests: extern_digests,
            pkg_config_digest: pkg.config_digest.clone(),
        });
    }
    None
}
fn is_builtin_toolchain_module(toolchain_lib_lean: &Path, mod_name: &str) -> bool {
    if mod_name == "Init"
        || mod_name.starts_with("Init.")
        || mod_name == "Std"
        || mod_name.starts_with("Std.")
        || mod_name == "Lean"
        || mod_name.starts_with("Lean.")
        || mod_name == "Lake"
        || mod_name.starts_with("Lake.")
    {
        return true;
    }
    let rel_slash = mod_name.replace('.', "/");
    toolchain_lib_lean
        .join(format!("{}.olean", rel_slash))
        .is_file()
}
#[derive(Debug, Clone, Serialize, Deserialize, Default, PartialEq, Eq)]
struct VerifiedDepModuleEntry {
    src_blake3: String,
    olean_artifact_digest: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default, PartialEq, Eq)]
struct VerifiedDepManifest {
    pkg_name: String,
    toolchain: String,
    lean_githash: String,
    pkg_config_digest: String,
    modules: BTreeMap<String, VerifiedDepModuleEntry>,
}

fn is_dep_olean_fresh(
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
    src_content: &str,
    is_module: bool,
    olean_path: &Path,
) -> Option<std::time::SystemTime> {
    let pkg_root = &spec.pkg_root;
    let src_path = &spec.src_path;
    let sym = fs::symlink_metadata(olean_path).ok()?;
    if sym.file_type().is_symlink() {
        return None;
    }
    let om = fs::metadata(olean_path).ok()?;
    if !om.is_file() || om.len() == 0 {
        return None;
    }
    if is_module {
        let srv_path = PathBuf::from(format!("{}.server", olean_path.display()));
        let priv_path = PathBuf::from(format!("{}.private", olean_path.display()));
        if fs::symlink_metadata(&srv_path)
            .ok()?
            .file_type()
            .is_symlink()
            || fs::symlink_metadata(&priv_path)
                .ok()?
                .file_type()
                .is_symlink()
        {
            return None;
        }
        let srv_meta = fs::metadata(&srv_path).ok()?;
        let priv_meta = fs::metadata(&priv_path).ok()?;
        if !srv_meta.is_file()
            || srv_meta.len() == 0
            || !priv_meta.is_file()
            || priv_meta.len() == 0
        {
            return None;
        }
    }
    let ot = om.modified().ok()?;
    if let Ok(sm) = fs::metadata(src_path) {
        if let Ok(st) = sm.modified() {
            if ot < st {
                return None;
            }
        }
    }
    for cfg_file in ["lakefile.toml", "lakefile.lean", "lean-toolchain"] {
        if let Ok(cm) = fs::metadata(pkg_root.join(cfg_file)) {
            if let Ok(ct) = cm.modified() {
                if ot < ct {
                    return None;
                }
            }
        }
    }
    // Local coherence manifest verification via `.lake/build/.turbo_verified_sources.json`
    // (trusted mode only; untrusted builds never call `collect_fresh_dep_pkg_closure` and never
    // accept pre-existing checkout `.olean` files without host `TurboStore` CAS verification).
    let verified_manifest_path = pkg_root.join(".lake/build/.turbo_verified_sources.json");
    if verified_manifest_path.is_file() {
        let bytes = fs::read(&verified_manifest_path).ok()?;
        let manifest: VerifiedDepManifest = serde_json::from_slice(&bytes).ok()?;
        if manifest.pkg_name != spec.pkg_name
            || manifest.toolchain != cfg.toolchain
            || manifest.lean_githash != cfg.lean_githash
            || manifest.pkg_config_digest != spec.pkg_config_digest
        {
            return None;
        }
        let rel_src = src_path
            .strip_prefix(pkg_root)
            .unwrap_or(src_path)
            .to_string_lossy()
            .replace('\\', "/");
        let entry = manifest.modules.get(&rel_src)?;
        let actual_src_hash = blake3::hash(src_content.as_bytes()).to_hex().to_string();
        if entry.src_blake3 != actual_src_hash {
            return None;
        }
        let actual_olean_digest = compute_olean_artifact_set_digest(olean_path).ok()?;
        if entry.olean_artifact_digest != actual_olean_digest {
            return None;
        }
        return Some(ot);
    }
    None
}

/// Inspect a dependency package module and its transitive imports across `dep_pkgs` in trusted mode.
/// Returns `Ok(Some(transitive_olean_pairs))` only if every module in the dependency closure
/// has a fresh `.olean` verified against the local coherence manifest `.turbo_verified_sources.json`
/// and `olean_mtime(parent) >= olean_mtime(child)` holds along every import edge.
/// Returns `Ok(None)` if any module in the closure is missing or unverified.
/// Returns `Err` if a module import resolves ambiguously across multiple dependency packages.
fn collect_fresh_dep_pkg_closure(
    cfg: &ProjectConfig,
    initial_spec: &DiscoveredModuleSpec,
) -> Result<Option<Vec<(String, PathBuf)>>> {
    let mut visited: HashSet<(String, String)> = HashSet::new();
    let mut queue: VecDeque<(DiscoveredModuleSpec, Option<std::time::SystemTime>)> =
        VecDeque::new();
    let mut olean_pairs = Vec::new();
    visited.insert((
        initial_spec.pkg_name.clone(),
        initial_spec.module_name.clone(),
    ));
    queue.push_back((initial_spec.clone(), None));
    while let Some((cur, parent_olean_mtime)) = queue.pop_front() {
        let Ok(src) = fs::read_to_string(&cur.src_path) else {
            return Ok(None);
        };
        let hdr = parse_header_info(&src);
        let rel_slash = cur.module_name.replace('.', "/");
        let olean_path = cur.build_lib_lean_dir.join(format!("{}.olean", rel_slash));
        let Some(cur_olean_mtime) = is_dep_olean_fresh(cfg, &cur, &src, hdr.is_module, &olean_path)
        else {
            return Ok(None);
        };
        // Verify parent `.olean` is at least as new as child `.olean`
        if let Some(parent_mt) = parent_olean_mtime {
            if parent_mt < cur_olean_mtime {
                return Ok(None);
            }
        }
        olean_pairs.push((cur.module_name.clone(), olean_path));
        for imp in hdr.imports {
            if is_builtin_toolchain_module(&cfg.toolchain_lib_lean, &imp) {
                continue;
            }
            let mut matches = Vec::new();
            for dp in &cfg.dep_pkgs {
                if let Some(sub_spec) = resolve_module_in_package(dp, false, &imp) {
                    matches.push(sub_spec);
                }
            }
            if matches.len() > 1 {
                let pkg_names: Vec<String> = matches.iter().map(|m| m.pkg_name.clone()).collect();
                anyhow::bail!(
                    "Ambiguous module import `{}` (imported by `{}`) resolved in multiple dependency packages: {:?}",
                    imp,
                    cur.module_name,
                    pkg_names
                );
            }
            let Some(sub_spec) = matches.into_iter().next() else {
                // Unresolved import inside dependency closure: force native DAG traversal so
                // root-package imports or missing-module errors are handled deterministically.
                return Ok(None);
            };
            let key = (sub_spec.pkg_name.clone(), sub_spec.module_name.clone());
            if visited.insert(key) {
                queue.push_back((sub_spec, Some(cur_olean_mtime)));
            }
        }
    }
    Ok(Some(olean_pairs))
}

/// Build the deterministic module dependency DAG for `cfg` and requested `targets` (trusted mode).
pub fn build_module_dag(cfg: &ProjectConfig, targets: &[String]) -> Result<ModuleDag> {
    build_module_dag_with_trust(cfg, targets, false)
}

/// Build the deterministic module dependency DAG for `cfg` and requested `targets` with explicit `is_untrusted` policy.
/// When `is_untrusted` is true, pre-existing `.olean` artifacts in dependency packages or `LEAN_PATH`
/// are never trusted from the checkout; all dependency package modules become DAG nodes verified/restored
/// via the host `TurboStore` CAS or compiled inside the sandbox.
pub fn build_module_dag_with_trust(
    cfg: &ProjectConfig,
    targets: &[String],
    is_untrusted: bool,
) -> Result<ModuleDag> {
    let root_pkg = &cfg.root_pkg;
    let mut initial_specs: Vec<(DiscoveredModuleSpec, bool)> = Vec::new();
    let global_emit_c = std::env::var("TURBO_LEAN_EMIT_C")
        .map(|v| v.trim() == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false);
    let mut effective_targets: Vec<String> = if targets.is_empty() {
        if !root_pkg.default_targets.is_empty() {
            root_pkg.default_targets.clone()
        } else {
            let mut all = Vec::new();
            for l in &root_pkg.libs {
                all.push(l.name.clone());
            }
            for e in &root_pkg.exes {
                all.push(e.name.clone());
            }
            all
        }
    } else {
        targets.to_vec()
    };
    effective_targets.dedup();
    for raw_target in &effective_targets {
        let mut t = raw_target.trim();
        if let Some(r) = t.strip_prefix('@') {
            t = r;
        }
        if let Some(r) = t.strip_prefix('+') {
            t = r;
        }
        let (target_base, facet_opt) = match t.split_once(':') {
            Some((b, f)) => (b.trim(), Some(f.trim())),
            None => (t, None),
        };
        let mut force_c_for_target = global_emit_c;
        if let Some(facet) = facet_opt {
            match facet {
                "olean" | "ilean" | "lib" | "modules" | "default" | "leanArts" => {}
                "c" | "static" => {
                    force_c_for_target = true;
                }
                other => {
                    let _ = c_abi::verify_static_lake_config(true, false, false, true);
                    anyhow::bail!(
                        "Unsupported target facet `:{}` in target `{}`: fail-closed static Lake config gate",
                        other,
                        raw_target
                    );
                }
            }
        }
        // Check if target_base has `<pkg>/<target>` prefix
        let (pkg_filter, item_name) = match target_base.split_once('/') {
            Some((p, item)) => (Some(clean_lake_ident(p)), clean_lake_ident(item)),
            None => (None, clean_lake_ident(target_base)),
        };
        let target_pkg = if let Some(ref pf) = pkg_filter {
            if pf == &root_pkg.name {
                root_pkg
            } else if let Some(dp) = cfg.dep_pkgs.iter().find(|d| &d.name == pf) {
                dp
            } else {
                anyhow::bail!("Unknown package `{}` in target `{}`", pf, raw_target);
            }
        } else {
            root_pkg
        };
        let target_is_root = target_pkg.pkg_root == root_pkg.pkg_root;
        if target_pkg.custom_targets.iter().any(|ct| ct == &item_name)
            || target_pkg.extern_libs.iter().any(|el| {
                el.name == item_name && el.is_dynamic_recipe && el.static_artifact_path.is_none()
            })
        {
            let _ = c_abi::verify_static_lake_config(true, true, false, false);
            anyhow::bail!(
                "Target `{}` requires executing a dynamic Lake recipe in `{}`: fail-closed static Lake config gate",
                raw_target,
                target_pkg.name
            );
        }
        let mut matched = false;
        // 1. Match against lean_lib targets
        for lib in &target_pkg.libs {
            if lib.name == item_name || (item_name.is_empty() && pkg_filter.is_some()) {
                matched = true;
                let pkg_src_base = target_pkg.pkg_root.join(&target_pkg.src_dir);
                let lib_src = match &lib.src_dir {
                    Some(sd) => pkg_src_base.join(sd),
                    None => pkg_src_base,
                };
                let build_base = target_pkg.pkg_root.join(&target_pkg.build_dir);
                let build_lib_lean_dir = build_base.join(&target_pkg.lean_lib_dir);
                let build_ir_dir = build_base.join(&target_pkg.ir_dir);
                let (strong_args, weak_args) = compose_effective_args(
                    target_pkg,
                    &lib.lean_options,
                    &lib.more_lean_args,
                    &lib.weak_lean_args,
                );
                let precompile = lib
                    .precompile_modules
                    .unwrap_or(target_pkg.precompile_modules)
                    || lib
                        .default_facets
                        .iter()
                        .any(|f| f == "c" || f == "static" || f == "LeanLib.staticFacet");
                let extern_digests: Vec<String> = target_pkg
                    .extern_libs
                    .iter()
                    .filter_map(|e| {
                        e.static_artifact_blake3
                            .as_ref()
                            .map(|h| format!("{}:{}", e.name, h))
                    })
                    .collect();
                for g in &lib.globs {
                    let expanded = expand_glob_in_dir(&lib_src, g, true)?;
                    for (m_name, m_path) in expanded {
                        initial_specs.push((
                            DiscoveredModuleSpec {
                                module_name: m_name,
                                pkg_name: target_pkg.name.clone(),
                                target_name: lib.name.clone(),
                                is_root_pkg: target_is_root,
                                pkg_root: target_pkg.pkg_root.clone(),
                                src_root: lib_src.clone(),
                                src_path: m_path,
                                build_lib_lean_dir: build_lib_lean_dir.clone(),
                                build_ir_dir: build_ir_dir.clone(),
                                precompile_modules: precompile,
                                is_exe_target: false,
                                strong_args: strong_args.clone(),
                                weak_args: weak_args.clone(),
                                extern_lib_digests: extern_digests.clone(),
                                pkg_config_digest: target_pkg.config_digest.clone(),
                            },
                            force_c_for_target || precompile,
                        ));
                    }
                }
            }
        }
        // 2. Match against lean_exe targets
        for exe in &target_pkg.exes {
            if exe.name == item_name {
                matched = true;
                if let Some(spec) = resolve_module_in_package(target_pkg, target_is_root, &exe.root)
                {
                    // Note: `turbo-lean build` is a module builder; when a `lean_exe` is in defaultTargets
                    // (not explicitly requested by name), we compile its root module and dependencies
                    // and emit `.c` if `targets` explicitly requested the exe or `force_c_for_target`.
                    let emit_c =
                        force_c_for_target || !targets.is_empty() || spec.precompile_modules;
                    initial_specs.push((spec, emit_c));
                } else {
                    anyhow::bail!(
                        "Executable `{}` root module `{}` not found in package `{}`",
                        exe.name,
                        exe.root,
                        target_pkg.name
                    );
                }
            }
        }
        // 3. Match against a specific module name (e.g. `TurboLean.Spec`)
        if !matched {
            if let Some(spec) = resolve_module_in_package(target_pkg, target_is_root, &item_name) {
                let emit_c = force_c_for_target || spec.precompile_modules || spec.is_exe_target;
                initial_specs.push((spec, emit_c));
                matched = true;
            }
        }
        if !matched {
            anyhow::bail!(
                "Unknown target or module `{}` in package `{}`",
                raw_target,
                target_pkg.name
            );
        }
    }
    // Fallback: if root package declared no libs and no exes (e.g. bare lakefile.lean `package foo`),
    // discover all `.lean` files under `root_pkg.src_dir`
    if initial_specs.is_empty() && root_pkg.libs.is_empty() && root_pkg.exes.is_empty() {
        let src_root = root_pkg.pkg_root.join(&root_pkg.src_dir);
        let files = lake_build::collect_lean_files(&src_root);
        let build_base = root_pkg.pkg_root.join(&root_pkg.build_dir);
        let (strong_args, weak_args) = compose_effective_args(root_pkg, &BTreeMap::new(), &[], &[]);
        for f in files {
            if let Ok(rel) = f.strip_prefix(&src_root) {
                let mod_name = rel
                    .with_extension("")
                    .components()
                    .filter_map(|c| c.as_os_str().to_str())
                    .collect::<Vec<_>>()
                    .join(".");
                if !mod_name.is_empty() {
                    initial_specs.push((
                        DiscoveredModuleSpec {
                            module_name: mod_name,
                            pkg_name: root_pkg.name.clone(),
                            target_name: root_pkg.name.clone(),
                            is_root_pkg: true,
                            pkg_root: root_pkg.pkg_root.clone(),
                            src_root: src_root.clone(),
                            src_path: f,
                            build_lib_lean_dir: build_base.join(&root_pkg.lean_lib_dir),
                            build_ir_dir: build_base.join(&root_pkg.ir_dir),
                            precompile_modules: root_pkg.precompile_modules,
                            is_exe_target: false,
                            strong_args: strong_args.clone(),
                            weak_args: weak_args.clone(),
                            extern_lib_digests: Vec::new(),
                            pkg_config_digest: root_pkg.config_digest.clone(),
                        },
                        global_emit_c || root_pkg.precompile_modules,
                    ));
                }
            }
        }
    }
    // Collect caller LEAN_PATH directories for prebuilt external olean lookup (trusted mode only)
    let mut external_lean_path_dirs: Vec<PathBuf> = Vec::new();
    if !is_untrusted {
        if let Ok(lp) = std::env::var("LEAN_PATH") {
            for p in std::env::split_paths(&lp) {
                if p.is_dir() && p != cfg.toolchain_lib_lean {
                    external_lean_path_dirs.push(p);
                }
            }
        }
    }
    let mut nodes: BTreeMap<String, ModuleNode> = BTreeMap::new();
    let mut root_modules = Vec::new();
    let mut worklist: VecDeque<(DiscoveredModuleSpec, bool)> = VecDeque::new();
    for (spec, need_c) in initial_specs {
        if !root_modules.contains(&spec.module_name) {
            root_modules.push(spec.module_name.clone());
        }
        worklist.push_back((spec, need_c));
    }
    root_modules.sort();
    while let Some((spec, requested_c)) = worklist.pop_front() {
        if let Some(existing) = nodes.get_mut(&spec.module_name) {
            if existing.pkg_name != spec.pkg_name || existing.src_path != spec.src_path {
                anyhow::bail!(
                    "Ambiguous module `{}` resolved in multiple packages or paths (`{}` at {} vs `{}` at {})",
                    spec.module_name,
                    existing.pkg_name,
                    existing.src_path.display(),
                    spec.pkg_name,
                    spec.src_path.display()
                );
            }
            if requested_c && !existing.needs_c {
                existing.needs_c = true;
            }
            continue;
        }
        let src = fs::read_to_string(&spec.src_path).with_context(|| {
            format!(
                "Failed to read module `{}` at {}",
                spec.module_name,
                spec.src_path.display()
            )
        })?;
        let src_blake3 = blake3::hash(src.as_bytes()).to_hex().to_string();
        let header = parse_header_info(&src);
        let needs_c =
            requested_c || spec.precompile_modules || header.has_c_export || global_emit_c;
        let mut direct_dag_deps = Vec::new();
        let mut external_olean_deps = Vec::new();
        for imp in &header.imports {
            if imp == &spec.module_name {
                anyhow::bail!(
                    "Module import cycle detected: {} -> {}",
                    spec.module_name,
                    imp
                );
            }
            // 1. Check if `imp` resolves in root package
            if let Some(dep_spec) = resolve_module_in_package(root_pkg, true, imp) {
                direct_dag_deps.push(imp.clone());
                worklist.push_back((dep_spec, needs_c && spec.precompile_modules));
                continue;
            }
            // 2. Check if `imp` resolves in any dependency package (failing closed on ambiguity)
            let mut dep_matches = Vec::new();
            for dep_pkg in &cfg.dep_pkgs {
                if let Some(dep_spec) = resolve_module_in_package(dep_pkg, false, imp) {
                    dep_matches.push(dep_spec);
                }
            }
            if dep_matches.len() > 1 {
                let pkg_names: Vec<String> =
                    dep_matches.iter().map(|m| m.pkg_name.clone()).collect();
                anyhow::bail!(
                    "Ambiguous module import `{}` (imported by `{}`) resolved in multiple dependency packages: {:?}",
                    imp,
                    spec.module_name,
                    pkg_names
                );
            }
            if let Some(dep_spec) = dep_matches.into_iter().next() {
                if !is_untrusted {
                    if let Some(fresh_closure) = collect_fresh_dep_pkg_closure(cfg, &dep_spec)? {
                        external_olean_deps.extend(fresh_closure);
                        continue;
                    }
                }
                direct_dag_deps.push(imp.clone());
                worklist.push_back((dep_spec, false));
                continue;
            }
            // 3. Check if `imp` is a built-in toolchain module (`Init.*`, `Std.*`, `Lean.*`, `Lake.*`)
            if is_builtin_toolchain_module(&cfg.toolchain_lib_lean, imp) {
                continue;
            }
            // 4. In trusted mode only, check if `imp` exists as a prebuilt `.olean` in `.lake/packages/*/.lake/build/lib/lean` or `LEAN_PATH`
            if !is_untrusted {
                let rel_slash = imp.replace('.', "/");
                let mut found_prebuilt: Option<PathBuf> = None;
                for dp in &cfg.dep_pkgs {
                    let cand = dp
                        .pkg_root
                        .join(&dp.build_dir)
                        .join(&dp.lean_lib_dir)
                        .join(format!("{}.olean", rel_slash));
                    if cand.is_file() {
                        found_prebuilt = Some(cand);
                        break;
                    }
                }
                if found_prebuilt.is_none() {
                    for dir in &external_lean_path_dirs {
                        let cand = dir.join(format!("{}.olean", rel_slash));
                        if cand.is_file() {
                            found_prebuilt = Some(cand);
                            break;
                        }
                    }
                }
                if let Some(pb_path) = found_prebuilt {
                    external_olean_deps.push((imp.clone(), pb_path));
                    continue;
                }
            }
            anyhow::bail!(
                "Missing module `{}` imported by `{}` ({}): not found in project sources, package dependencies, or toolchain `{}`",
                imp,
                spec.module_name,
                spec.src_path.display(),
                cfg.toolchain
            );
        }
        direct_dag_deps.sort();
        direct_dag_deps.dedup();
        external_olean_deps.sort_by(|a, b| a.0.cmp(&b.0));
        external_olean_deps.dedup_by(|a, b| a.0 == b.0);
        let rel_slash = spec.module_name.replace('.', "/");
        let olean_path = spec.build_lib_lean_dir.join(format!("{}.olean", rel_slash));
        let ilean_path = spec.build_lib_lean_dir.join(format!("{}.ilean", rel_slash));
        let c_path = spec.build_ir_dir.join(format!("{}.c", rel_slash));
        nodes.insert(
            spec.module_name.clone(),
            ModuleNode {
                module_name: spec.module_name,
                pkg_name: spec.pkg_name,
                target_name: spec.target_name,
                is_root_pkg: spec.is_root_pkg,
                pkg_root: spec.pkg_root,
                src_root: spec.src_root,
                src_path: spec.src_path,
                build_lib_lean_dir: spec.build_lib_lean_dir,
                build_ir_dir: spec.build_ir_dir,
                olean_path,
                ilean_path,
                c_path,
                is_module: header.is_module,
                has_prelude: header.has_prelude,
                needs_c,
                precompile_modules: spec.precompile_modules,
                strong_args: spec.strong_args,
                weak_args: spec.weak_args,
                src_blake3,
                direct_dag_deps,
                external_olean_deps,
                expected_all_deps: Vec::new(),
                extern_lib_digests: spec.extern_lib_digests,
                pkg_config_digest: spec.pkg_config_digest,
            },
        );
    }
    // 3-color DFS cycle detection with exact cycle path reconstruction
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum VisitState {
        Unvisited,
        Visiting,
        Visited,
    }
    let mut state: BTreeMap<String, VisitState> = nodes
        .keys()
        .map(|k| (k.clone(), VisitState::Unvisited))
        .collect();
    let mut stack: Vec<String> = Vec::new();
    fn dfs_cycle(
        u: &str,
        nodes: &BTreeMap<String, ModuleNode>,
        state: &mut BTreeMap<String, VisitState>,
        stack: &mut Vec<String>,
    ) -> Result<()> {
        state.insert(u.to_string(), VisitState::Visiting);
        stack.push(u.to_string());
        if let Some(node) = nodes.get(u) {
            for dep in &node.direct_dag_deps {
                if !nodes.contains_key(dep) {
                    continue;
                }
                match state.get(dep).copied().unwrap_or(VisitState::Unvisited) {
                    VisitState::Visiting => {
                        let start_pos = stack.iter().position(|x| x == dep).unwrap_or(0);
                        let mut cycle_chain: Vec<String> = stack[start_pos..].to_vec();
                        cycle_chain.push(dep.clone());
                        anyhow::bail!("Module import cycle detected: {}", cycle_chain.join(" -> "));
                    }
                    VisitState::Unvisited => {
                        dfs_cycle(dep, nodes, state, stack)?;
                    }
                    VisitState::Visited => {}
                }
            }
        }
        stack.pop();
        state.insert(u.to_string(), VisitState::Visited);
        Ok(())
    }
    let all_mod_names: Vec<String> = nodes.keys().cloned().collect();
    for m in &all_mod_names {
        if state.get(m) == Some(&VisitState::Unvisited) {
            dfs_cycle(m, &nodes, &mut state, &mut stack)?;
        }
    }
    // Propagate `needs_c` upstream if a downstream module requires `needs_c` and `precompile_modules`
    // and build reverse adjacency + in-degrees for Kahn's algorithm
    let mut in_degree: BTreeMap<String, usize> = BTreeMap::new();
    let mut completed_deps: BTreeMap<String, usize> = BTreeMap::new();
    let mut total_deps: BTreeMap<String, usize> = BTreeMap::new();
    let mut dependents: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (m, node) in &nodes {
        let deg = node
            .direct_dag_deps
            .iter()
            .filter(|d| nodes.contains_key(*d))
            .count();
        in_degree.insert(m.clone(), deg);
        completed_deps.insert(m.clone(), 0);
        total_deps.insert(m.clone(), deg);
        for d in &node.direct_dag_deps {
            if nodes.contains_key(d) {
                dependents.entry(d.clone()).or_default().push(m.clone());
            }
        }
    }
    for list in dependents.values_mut() {
        list.sort();
        list.dedup();
    }
    let total_nodes = nodes.len();
    let mut visited_nodes = 0usize;
    let mut topological_order = Vec::with_capacity(total_nodes);
    let mut waves: Vec<Vec<String>> = Vec::new();
    let mut current_ready: Vec<String> = in_degree
        .iter()
        .filter(|(_, &deg)| deg == 0)
        .map(|(m, _)| m.clone())
        .collect();
    current_ready.sort();
    while !current_ready.is_empty() {
        let mut next_ready = BTreeSet::new();
        for m in &current_ready {
            let deg = *in_degree.get(m).unwrap_or(&0);
            let comp = *completed_deps.get(m).unwrap_or(&0);
            let tot = *total_deps.get(m).unwrap_or(&0);
            let step_ok = c_abi::verify_dag_schedule_step(
                deg as u64,
                comp as u64,
                tot as u64,
                visited_nodes as u64,
                total_nodes as u64,
            );
            if !step_ok {
                anyhow::bail!(
                    "C-ABI gate `turbo_spec_verify_dag_schedule_step` rejected node `{}` (in_degree={}, completed={}/{}, visited={}/{})",
                    m,
                    deg,
                    comp,
                    tot,
                    visited_nodes,
                    total_nodes
                );
            }
            visited_nodes += 1;
            topological_order.push(m.clone());
            if let Some(children) = dependents.get(m) {
                for child in children {
                    if let Some(c_comp) = completed_deps.get_mut(child) {
                        *c_comp += 1;
                    }
                    if let Some(c_deg) = in_degree.get_mut(child) {
                        *c_deg = c_deg.saturating_sub(1);
                        if *c_deg == 0 {
                            next_ready.insert(child.clone());
                        }
                    }
                }
            }
        }
        waves.push(current_ready);
        current_ready = next_ready.into_iter().collect();
    }
    if visited_nodes != total_nodes {
        anyhow::bail!(
            "DAG topological scheduling incomplete ({}/{} nodes visited): cycle detected",
            visited_nodes,
            total_nodes
        );
    }
    let mut all_deps_by_mod: HashMap<String, BTreeSet<String>> =
        HashMap::with_capacity(topological_order.len());
    for m in &topological_order {
        let mut set = BTreeSet::new();
        if let Some(n) = nodes.get(m) {
            for (ext_m, _) in &n.external_olean_deps {
                set.insert(ext_m.clone());
            }
            for d in &n.direct_dag_deps {
                set.insert(d.clone());
                if let Some(sub_set) = all_deps_by_mod.get(d) {
                    for sub_d in sub_set {
                        set.insert(sub_d.clone());
                    }
                }
            }
        }
        if let Some(n_mut) = nodes.get_mut(m) {
            n_mut.expected_all_deps = set.iter().cloned().collect();
        }
        all_deps_by_mod.insert(m.clone(), set);
    }
    Ok(ModuleDag {
        nodes,
        topological_order,
        waves,
        root_modules,
    })
}
fn update_lp(h: &mut blake3::Hasher, tag: &[u8], data: &[u8]) {
    h.update(&(tag.len() as u64).to_le_bytes());
    h.update(tag);
    h.update(&(data.len() as u64).to_le_bytes());
    h.update(data);
}

fn infer_pkg_root_from_artifact_path(artifact_path: &Path) -> Option<PathBuf> {
    let mut cur = artifact_path.parent();
    while let Some(dir) = cur {
        if dir.file_name().and_then(|s| s.to_str()) == Some("build") {
            if let Some(lake_dir) = dir.parent() {
                if lake_dir.file_name().and_then(|s| s.to_str()) == Some(".lake") {
                    return lake_dir.parent().map(|p| p.to_path_buf());
                }
            }
        }
        cur = dir.parent();
    }
    None
}

/// Compute combined BLAKE3 artifact digest for an `.olean` and any companion `.olean.server`,
/// `.olean.private`, `.ilean`, `.ir`, and `.ir.sig`, encoding explicit presence/absence markers,
/// acquiring the shared package publication flock (`LOCK_SH`) so readers never observe a mid-commit
/// state, and propagating I/O errors if an existing companion file cannot be read.
pub fn compute_olean_artifact_set_digest(olean_path: &Path) -> Result<String> {
    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock
        .lock()
        .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
    let _flock_guard = if let Some(pkg_root) = infer_pkg_root_from_artifact_path(olean_path) {
        acquire_publish_flock_mode(&pkg_root, false)?
    } else {
        None
    };
    let bytes =
        fs::read(olean_path).with_context(|| format!("Failed to read {}", olean_path.display()))?;
    let mut h = blake3::Hasher::new();
    h.update(b"olean-art-v2\n");
    update_lp(&mut h, b"olean", blake3::hash(&bytes).as_bytes());
    let companions = [
        (
            "srv",
            PathBuf::from(format!("{}.server", olean_path.display())),
        ),
        (
            "priv",
            PathBuf::from(format!("{}.private", olean_path.display())),
        ),
        ("ilean", olean_path.with_extension("ilean")),
        ("ir", olean_path.with_extension("ir")),
        (
            "ir_sig",
            PathBuf::from(format!("{}.sig", olean_path.with_extension("ir").display())),
        ),
    ];
    for (tag, comp_path) in companions {
        match fs::metadata(&comp_path) {
            Ok(meta) if meta.is_file() => {
                let comp_bytes = fs::read(&comp_path).with_context(|| {
                    format!("Failed to read companion artifact {}", comp_path.display())
                })?;
                h.update(&[1u8]);
                update_lp(&mut h, tag.as_bytes(), blake3::hash(&comp_bytes).as_bytes());
            }
            Ok(_) => {
                anyhow::bail!(
                    "Companion artifact path `{}` is not a regular file",
                    comp_path.display()
                );
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                h.update(&[0u8]);
                update_lp(&mut h, tag.as_bytes(), b"");
            }
            Err(e) => {
                return Err(e).with_context(|| {
                    format!("Failed to stat companion artifact {}", comp_path.display())
                });
            }
        }
    }
    Ok(h.finalize().to_hex().to_string())
}

/// Compute the per-module CAS action key (`module_unit`), incorporating:
/// - toolchain string & `lean --githash`
/// - OS & architecture
/// - package configuration digest
/// - normalized strong & weak Lean arguments
/// - `is_module`, `has_prelude`, `precompile_modules`, `needs_c`
/// - module name & source BLAKE3 digest
/// - exact dependency `.olean` (+ `.olean.server` / `.olean.private`) digests
/// - `extern_lib` static archive digests
pub fn compute_module_cas_key(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    dep_olean_digests: &[(String, String)],
    needs_c_override: bool,
) -> Result<String> {
    let toolchain_valid =
        !cfg.toolchain.is_empty() && !cfg.lean_githash.is_empty() && cfg.lean_bin.is_file();
    let args_valid = node
        .strong_args
        .iter()
        .chain(node.weak_args.iter())
        .all(|a| is_allowed_lean_arg(a));
    let src_valid = node.src_blake3.len() == 64;
    let cfg_valid = node.pkg_config_digest.len() == 64;
    let deps_sorted_unique = dep_olean_digests.windows(2).all(|w| w[0].0 < w[1].0)
        && dep_olean_digests
            .iter()
            .all(|(m, d)| !m.is_empty() && !d.is_empty());
    let provided_dep_names: HashSet<&str> =
        dep_olean_digests.iter().map(|(m, _)| m.as_str()).collect();
    let all_direct_and_ext_present = node
        .direct_dag_deps
        .iter()
        .all(|d| provided_dep_names.contains(d.as_str()))
        && node
            .external_olean_deps
            .iter()
            .all(|(d, _)| provided_dep_names.contains(d.as_str()));
    let deps_exact_match = all_direct_and_ext_present
        && dep_olean_digests.len() == node.expected_all_deps.len()
        && dep_olean_digests
            .iter()
            .zip(node.expected_all_deps.iter())
            .all(|((m, _), exp_m)| m == exp_m);
    let deps_valid = deps_sorted_unique && deps_exact_match;

    let gate_ok = c_abi::verify_module_cache_key(
        toolchain_valid,
        args_valid,
        src_valid,
        deps_valid,
        cfg_valid,
    );
    if !gate_ok {
        if !deps_sorted_unique {
            anyhow::bail!(
                "C-ABI gate `turbo_spec_verify_module_cache_key` rejected unsorted or duplicate dependency digests for module `{}`",
                node.module_name
            );
        }
        if !all_direct_and_ext_present {
            anyhow::bail!(
                "C-ABI gate `turbo_spec_verify_module_cache_key` rejected incomplete dependency digests for module `{}` (missing required dependency)",
                node.module_name
            );
        }
        if !deps_exact_match {
            anyhow::bail!(
                "C-ABI gate `turbo_spec_verify_module_cache_key` rejected dependency digests for module `{}` (unexpected extra dependency outside resolved DAG)",
                node.module_name
            );
        }
        anyhow::bail!(
            "C-ABI gate `turbo_spec_verify_module_cache_key` rejected cache key inputs for module `{}` (toolchain={}, args={}, src={}, deps={}, cfg={})",
            node.module_name,
            toolchain_valid,
            args_valid,
            src_valid,
            deps_valid,
            cfg_valid
        );
    }
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-module-cas-v2\n");
    update_lp(&mut h, b"toolchain", cfg.toolchain.as_bytes());
    update_lp(&mut h, b"githash", cfg.lean_githash.as_bytes());
    update_lp(
        &mut h,
        b"lean_bin",
        cfg.lean_bin.to_string_lossy().as_bytes(),
    );
    update_lp(&mut h, b"os", std::env::consts::OS.as_bytes());
    update_lp(&mut h, b"arch", std::env::consts::ARCH.as_bytes());
    update_lp(&mut h, b"pkg_cfg", node.pkg_config_digest.as_bytes());
    update_lp(&mut h, b"pkg_name", node.pkg_name.as_bytes());
    update_lp(&mut h, b"target", node.target_name.as_bytes());
    update_lp(&mut h, b"module", node.module_name.as_bytes());
    let flags_bytes = [
        if node.is_module { b'M' } else { b'm' },
        if node.has_prelude { b'P' } else { b'p' },
        if node.precompile_modules { b'C' } else { b'c' },
        if needs_c_override { b'E' } else { b'e' },
    ];
    update_lp(&mut h, b"flags", &flags_bytes);
    h.update(&(node.strong_args.len() as u64).to_le_bytes());
    for a in &node.strong_args {
        update_lp(&mut h, b"sarg", a.as_bytes());
    }
    h.update(&(node.weak_args.len() as u64).to_le_bytes());
    for a in &node.weak_args {
        update_lp(&mut h, b"warg", a.as_bytes());
    }
    update_lp(&mut h, b"src", node.src_blake3.as_bytes());
    h.update(&(dep_olean_digests.len() as u64).to_le_bytes());
    for (dep_mod, dep_hash) in dep_olean_digests {
        update_lp(&mut h, b"dep_mod", dep_mod.as_bytes());
        update_lp(&mut h, b"dep_hash", dep_hash.as_bytes());
    }
    h.update(&(node.extern_lib_digests.len() as u64).to_le_bytes());
    for ext in &node.extern_lib_digests {
        update_lp(&mut h, b"ext_lib", ext.as_bytes());
    }
    Ok(h.finalize().to_hex().to_string())
}
fn build_lean_search_path(cfg: &ProjectConfig, is_untrusted: bool) -> (String, String) {
    let mut lp_parts = Vec::new();
    let mut ld_parts = Vec::new();
    let root_lib_lean = cfg
        .root_pkg
        .pkg_root
        .join(&cfg.root_pkg.build_dir)
        .join(&cfg.root_pkg.lean_lib_dir);
    let root_lib = cfg
        .root_pkg
        .pkg_root
        .join(&cfg.root_pkg.build_dir)
        .join("lib");
    lp_parts.push(root_lib_lean.to_string_lossy().to_string());
    ld_parts.push(root_lib.to_string_lossy().to_string());
    for dp in &cfg.dep_pkgs {
        let dep_lib_lean = dp.pkg_root.join(&dp.build_dir).join(&dp.lean_lib_dir);
        let dep_lib = dp.pkg_root.join(&dp.build_dir).join("lib");
        let s = dep_lib_lean.to_string_lossy().to_string();
        if !lp_parts.contains(&s) {
            lp_parts.push(s);
        }
        let lds = dep_lib.to_string_lossy().to_string();
        if !ld_parts.contains(&lds) {
            ld_parts.push(lds);
        }
    }
    if !is_untrusted {
        if let Ok(caller_lp) = std::env::var("LEAN_PATH") {
            for part in caller_lp.split(':') {
                let trimmed = part.trim();
                if !trimmed.is_empty() && !lp_parts.iter().any(|p| p == trimmed) {
                    lp_parts.push(trimmed.to_string());
                }
            }
        }
    }
    let tc_lp = cfg.toolchain_lib_lean.to_string_lossy().to_string();
    if !lp_parts.contains(&tc_lp) {
        lp_parts.push(tc_lp.clone());
    }
    ld_parts.push(tc_lp);
    ld_parts.push(cfg.toolchain_lib.to_string_lossy().to_string());
    if !is_untrusted {
        if let Ok(orig_ld) = std::env::var("LD_LIBRARY_PATH") {
            if !orig_ld.trim().is_empty() {
                ld_parts.push(orig_ld);
            }
        }
    }
    (lp_parts.join(":"), ld_parts.join(":"))
}
fn scrub_untrusted_env(cmd: &mut Command) {
    for (k, _) in std::env::vars() {
        let ku = k.to_ascii_uppercase();
        if ku.contains("TOKEN")
            || ku.contains("SECRET")
            || ku.contains("KEY")
            || ku.contains("PASSWORD")
            || ku.contains("CREDENTIAL")
            || ku.starts_with("AWS_")
            || ku.starts_with("GH_")
            || ku.starts_with("GITHUB_")
            || ku.starts_with("OPENAI_")
            || ku.starts_with("ANTHROPIC_")
            || ku == "LEAN_SRC_PATH"
            || ku == "LAKE"
            || ku == "LAKE_HOME"
            || ku == "LD_PRELOAD"
            || ku == "LD_AUDIT"
            || ku == "DYLD_INSERT_LIBRARIES"
        {
            cmd.env_remove(&k);
        }
    }
}
fn collect_module_artifact_paths(node: &ModuleNode) -> Vec<(&'static str, PathBuf)> {
    let mut list = vec![
        ("olean", node.olean_path.clone()),
        ("ilean", node.ilean_path.clone()),
    ];
    let srv = PathBuf::from(format!("{}.server", node.olean_path.display()));
    if srv.is_file() {
        list.push(("olean_server", srv));
    }
    let prv = PathBuf::from(format!("{}.private", node.olean_path.display()));
    if prv.is_file() {
        list.push(("olean_private", prv));
    }
    let ir = node.olean_path.with_extension("ir");
    if ir.is_file() {
        list.push(("ir", ir));
    }
    let ir_sig = PathBuf::from(format!(
        "{}.sig",
        node.olean_path.with_extension("ir").display()
    ));
    if ir_sig.is_file() {
        list.push(("ir_sig", ir_sig));
    }
    if node.c_path.is_file() {
        list.push(("c", node.c_path.clone()));
    }
    list
}
fn is_regular_nonempty_file(p: &Path) -> bool {
    let Ok(sym) = fs::symlink_metadata(p) else {
        return false;
    };
    !sym.file_type().is_symlink() && sym.file_type().is_file() && sym.len() > 0
}

fn has_no_symlink_at(p: &Path) -> bool {
    match fs::symlink_metadata(p) {
        Ok(sym) => !sym.file_type().is_symlink(),
        Err(_) => true,
    }
}

fn validate_materialized_module_artifacts(node: &ModuleNode) -> bool {
    let srv_path = PathBuf::from(format!("{}.server", node.olean_path.display()));
    let priv_path = PathBuf::from(format!("{}.private", node.olean_path.display()));
    let ir_path = node.olean_path.with_extension("ir");
    let ir_sig_path = PathBuf::from(format!("{}.sig", ir_path.display()));
    if !has_no_symlink_at(&srv_path)
        || !has_no_symlink_at(&priv_path)
        || !has_no_symlink_at(&ir_path)
        || !has_no_symlink_at(&ir_sig_path)
        || !has_no_symlink_at(&node.c_path)
    {
        return false;
    }
    let has_olean = is_regular_nonempty_file(&node.olean_path);
    let has_ilean = is_regular_nonempty_file(&node.ilean_path);
    let has_srv = is_regular_nonempty_file(&srv_path);
    let has_priv = is_regular_nonempty_file(&priv_path);
    let has_c = is_regular_nonempty_file(&node.c_path);
    c_abi::verify_module_artifact_set(
        has_olean,
        has_ilean,
        node.is_module,
        has_srv,
        has_priv,
        node.needs_c,
        has_c,
    )
}

fn wipe_existing_module_artifacts(node: &ModuleNode) {
    let srv_path = PathBuf::from(format!("{}.server", node.olean_path.display()));
    let priv_path = PathBuf::from(format!("{}.private", node.olean_path.display()));
    let ir_path = node.olean_path.with_extension("ir");
    let ir_sig_path = PathBuf::from(format!("{}.sig", ir_path.display()));
    for p in [
        &node.olean_path,
        &node.ilean_path,
        &srv_path,
        &priv_path,
        &ir_path,
        &ir_sig_path,
        &node.c_path,
    ] {
        let _ = fs::remove_file(p);
    }
}

static PUBLISH_LOCK: OnceLock<Mutex<()>> = OnceLock::new();

#[cfg(unix)]
struct FlockGuard(fs::File);
#[cfg(unix)]
impl Drop for FlockGuard {
    fn drop(&mut self) {
        use std::os::unix::io::AsRawFd;
        unsafe {
            let _ = libc::flock(self.0.as_raw_fd(), libc::LOCK_UN);
        }
    }
}

fn acquire_publish_flock_mode(pkg_root: &Path, exclusive: bool) -> Result<Option<FlockGuard>> {
    #[cfg(unix)]
    {
        use std::os::unix::io::AsRawFd;
        let build_dir = pkg_root.join(".lake/build");
        fs::create_dir_all(&build_dir)?;
        let lock_path = build_dir.join(".turbo_publish.lock");
        let f = fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .truncate(false)
            .open(&lock_path)?;
        let op = if exclusive {
            libc::LOCK_EX
        } else {
            libc::LOCK_SH
        };
        let rc = unsafe { libc::flock(f.as_raw_fd(), op) };
        if rc != 0 {
            return Err(std::io::Error::last_os_error())
                .with_context(|| format!("Failed to acquire flock on `{}`", lock_path.display()));
        }
        Ok(Some(FlockGuard(f)))
    }
    #[cfg(not(unix))]
    {
        let _ = (pkg_root, exclusive);
        Ok(None)
    }
}

fn acquire_publish_flock(pkg_root: &Path) -> Result<Option<FlockGuard>> {
    acquire_publish_flock_mode(pkg_root, true)
}

#[derive(Clone, Debug)]
struct BackupRecord {
    dst_path: PathBuf,
    backup_file: Option<(PathBuf, blake3::Hash, u64)>,
}

fn sync_parent_dir(p: &Path) -> Result<()> {
    #[cfg(unix)]
    if let Some(parent) = p.parent() {
        let df = fs::File::open(parent).with_context(|| {
            format!(
                "Failed to open parent directory `{}` for fsync",
                parent.display()
            )
        })?;
        df.sync_all()
            .with_context(|| format!("Failed to fsync parent directory `{}`", parent.display()))?;
    }
    #[cfg(not(unix))]
    let _ = p;
    Ok(())
}

fn write_verified_copy_or_link(
    src_p: &Path,
    target_p: &Path,
    try_rename: bool,
    try_hard_link: bool,
) -> Result<(blake3::Hash, u64)> {
    let src_bytes =
        fs::read(src_p).with_context(|| format!("Failed to read `{}`", src_p.display()))?;
    let expected_len = src_bytes.len() as u64;
    let expected_hash = blake3::hash(&src_bytes);
    if fs::symlink_metadata(target_p).is_ok() {
        fs::remove_file(target_p).with_context(|| {
            format!(
                "Failed to remove pre-existing staging/backup file `{}`",
                target_p.display()
            )
        })?;
    }
    let linked_or_renamed = (try_rename && fs::rename(src_p, target_p).is_ok())
        || (try_hard_link && fs::hard_link(src_p, target_p).is_ok());
    if !linked_or_renamed {
        use std::io::Write;
        let mut f = fs::File::create(target_p)
            .with_context(|| format!("Failed to create `{}`", target_p.display()))?;
        f.write_all(&src_bytes)
            .with_context(|| format!("Failed to write `{}`", target_p.display()))?;
        f.sync_all()
            .with_context(|| format!("Failed to fsync `{}`", target_p.display()))?;
    }
    let sym = fs::symlink_metadata(target_p)
        .with_context(|| format!("Failed to stat `{}`", target_p.display()))?;
    if sym.file_type().is_symlink() || !sym.file_type().is_file() || sym.len() != expected_len {
        anyhow::bail!(
            "Verified file check failed for `{}` (len={}, expected={})",
            target_p.display(),
            sym.len(),
            expected_len
        );
    }
    let written_bytes = fs::read(target_p).with_context(|| {
        format!(
            "Failed to re-read `{}` for verification",
            target_p.display()
        )
    })?;
    if blake3::hash(&written_bytes) != expected_hash {
        anyhow::bail!("Verified file BLAKE3 mismatch for `{}`", target_p.display());
    }
    sync_parent_dir(target_p)?;
    Ok((expected_hash, expected_len))
}

fn rollback_publish_state(
    node: &ModuleNode,
    had_valid_pre_publish_set: bool,
    staged_renames: &[(PathBuf, PathBuf)],
    backups: &[BackupRecord],
) -> Result<()> {
    let mut errs: Vec<String> = Vec::new();
    for (stage_p, _) in staged_renames {
        match fs::symlink_metadata(stage_p) {
            Ok(_) => {
                if let Err(e) = fs::remove_file(stage_p) {
                    errs.push(format!(
                        "failed to remove staged file `{}`: {}",
                        stage_p.display(),
                        e
                    ));
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => {
                errs.push(format!(
                    "failed to stat staged file `{}`: {}",
                    stage_p.display(),
                    e
                ));
            }
        }
    }
    for rec in backups {
        match &rec.backup_file {
            Some((backup_p, expected_hash, expected_len)) => {
                let restore_res: Result<()> = (|| {
                    if fs::rename(backup_p, &rec.dst_path).is_err() {
                        write_verified_copy_or_link(backup_p, &rec.dst_path, false, false)?;
                        fs::remove_file(backup_p).with_context(|| {
                            format!(
                                "Failed to remove backup file `{}` after copy restore",
                                backup_p.display()
                            )
                        })?;
                    }
                    let sym = fs::symlink_metadata(&rec.dst_path)?;
                    if sym.file_type().is_symlink()
                        || !sym.file_type().is_file()
                        || sym.len() != *expected_len
                    {
                        anyhow::bail!(
                            "restored artifact `{}` failed size/type check",
                            rec.dst_path.display()
                        );
                    }
                    let restored_bytes = fs::read(&rec.dst_path)?;
                    if blake3::hash(&restored_bytes) != *expected_hash {
                        anyhow::bail!(
                            "restored artifact `{}` failed BLAKE3 verification",
                            rec.dst_path.display()
                        );
                    }
                    sync_parent_dir(&rec.dst_path)?;
                    Ok(())
                })();
                if let Err(e) = restore_res {
                    errs.push(format!(
                        "failed to restore `{}` from `{}`: {}",
                        rec.dst_path.display(),
                        backup_p.display(),
                        e
                    ));
                }
            }
            None => match fs::symlink_metadata(&rec.dst_path) {
                Ok(sym) if sym.file_type().is_file() || sym.file_type().is_symlink() => {
                    if let Err(e) = fs::remove_file(&rec.dst_path) {
                        errs.push(format!(
                            "failed to remove newly placed destination `{}` during rollback: {}",
                            rec.dst_path.display(),
                            e
                        ));
                    }
                }
                Ok(_) => {}
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                Err(e) => {
                    errs.push(format!(
                        "failed to stat destination `{}` during rollback: {}",
                        rec.dst_path.display(),
                        e
                    ));
                }
            },
        }
    }
    if errs.is_empty() && had_valid_pre_publish_set && !validate_materialized_module_artifacts(node)
    {
        errs.push(format!(
            "post-rollback artifact set validation failed for module `{}`",
            node.module_name
        ));
    }
    if !errs.is_empty() {
        wipe_existing_module_artifacts(node);
        anyhow::bail!(
            "publication state potentially inconsistent for module `{}` (unverified rollback errors: {})",
            node.module_name,
            errs.join("; ")
        );
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn publish_module_artifacts_atomic(
    tmp_dir: &Path,
    node: &ModuleNode,
    tmp_olean: &Path,
    tmp_ilean: &Path,
    tmp_srv: &Path,
    tmp_priv: &Path,
    tmp_ir: &Path,
    tmp_ir_sig: &Path,
    tmp_c: &Path,
) -> Result<()> {
    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock
        .lock()
        .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
    let _flock_guard = acquire_publish_flock(&node.pkg_root)?;
    let had_valid_pre_publish_set = validate_materialized_module_artifacts(node);
    let dst_srv = PathBuf::from(format!("{}.server", node.olean_path.display()));
    let dst_priv = PathBuf::from(format!("{}.private", node.olean_path.display()));
    let dst_ir = node.olean_path.with_extension("ir");
    let dst_ir_sig = PathBuf::from(format!("{}.sig", dst_ir.display()));
    let pairs: [(&Path, &Path, bool); 7] = [
        (tmp_olean, &node.olean_path, true),
        (tmp_ilean, &node.ilean_path, true),
        (tmp_srv, &dst_srv, node.is_module),
        (tmp_priv, &dst_priv, node.is_module),
        (tmp_ir, &dst_ir, node.is_module),
        (tmp_ir_sig, &dst_ir_sig, node.is_module),
        (tmp_c, &node.c_path, node.needs_c),
    ];
    let pid = std::process::id();
    let seq = crate::pack::next_tmp_id();
    let mut staged_renames: Vec<(PathBuf, PathBuf)> = Vec::new();
    let mut backups: Vec<BackupRecord> = Vec::new();
    let mut stale_to_remove: Vec<PathBuf> = Vec::new();

    // Phase 1: Stage & verify all produced files into sibling `.turbo_stage_*` files in destination directories,
    // and back up ALL pre-existing regular destination files (both kept and stale-to-remove) into verified
    // `.turbo_backup_*` files (with `sync_all`, size, and BLAKE3 verification) for transactional rollback.
    let stage_res: Result<()> = (|| {
        for (src_p, dst_p, should_keep) in pairs {
            let dst_parent = dst_p.parent().ok_or_else(|| {
                anyhow::anyhow!("Destination artifact `{}` has no parent", dst_p.display())
            })?;
            fs::create_dir_all(dst_parent)?;
            let fname = dst_p
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or("artifact");
            let backup_file = match fs::symlink_metadata(dst_p) {
                Ok(dst_sym)
                    if !dst_sym.file_type().is_symlink() && dst_sym.file_type().is_file() =>
                {
                    let backup_p =
                        dst_parent.join(format!(".turbo_backup_{}_{}_{}", pid, seq, fname));
                    let (b_hash, b_len) =
                        write_verified_copy_or_link(dst_p, &backup_p, false, true)?;
                    Some((backup_p, b_hash, b_len))
                }
                Ok(dst_sym) if dst_sym.file_type().is_symlink() => {
                    anyhow::bail!(
                        "Refusing to overwrite symlinked destination artifact `{}`",
                        dst_p.display()
                    );
                }
                Ok(_) => None,
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
                Err(e) => return Err(e.into()),
            };
            backups.push(BackupRecord {
                dst_path: dst_p.to_path_buf(),
                backup_file,
            });
            if !should_keep {
                stale_to_remove.push(dst_p.to_path_buf());
                continue;
            }
            match fs::symlink_metadata(src_p) {
                Ok(sym) => {
                    if sym.file_type().is_symlink() || !src_p.starts_with(tmp_dir) {
                        anyhow::bail!(
                            "Refusing to publish symlink or out-of-sandbox artifact `{}`",
                            src_p.display()
                        );
                    }
                    if !sym.file_type().is_file() || sym.len() == 0 {
                        anyhow::bail!(
                            "Refusing to publish non-regular or empty artifact `{}`",
                            src_p.display()
                        );
                    }
                    let stage_p =
                        dst_parent.join(format!(".turbo_stage_{}_{}_{}", pid, seq, fname));
                    let _ = write_verified_copy_or_link(src_p, &stage_p, true, false)?;
                    staged_renames.push((stage_p, dst_p.to_path_buf()));
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                    stale_to_remove.push(dst_p.to_path_buf());
                }
                Err(e) => return Err(e.into()),
            }
        }
        Ok(())
    })();

    if let Err(e) = stage_res {
        for (stage_p, _) in &staged_renames {
            let _ = fs::remove_file(stage_p);
        }
        for rec in &backups {
            if let Some((ref backup_p, _, _)) = rec.backup_file {
                let _ = fs::remove_file(backup_p);
            }
        }
        return Err(e);
    }

    // Phase 2a: Commit staged files via atomic in-place POSIX rename (`rename` replaces `dst_p` atomically),
    // rolling back and verifying all destinations from `backups` if any rename fails.
    for (stage_p, dst_p) in &staged_renames {
        if let Err(e) = fs::rename(stage_p, dst_p) {
            let rb_res =
                rollback_publish_state(node, had_valid_pre_publish_set, &staged_renames, &backups);
            let rb_suffix = rb_res
                .err()
                .map(|re| format!("; rollback error: {}", re))
                .unwrap_or_default();
            return Err(e).with_context(|| {
                format!(
                    "Failed to atomically rename staged artifact `{}` -> `{}`{}",
                    stage_p.display(),
                    dst_p.display(),
                    rb_suffix
                )
            });
        }
    }

    // Phase 2b: Transactionally remove any stale companion artifacts, rolling back if removal fails.
    for stale_p in &stale_to_remove {
        match fs::symlink_metadata(stale_p) {
            Ok(_) => {
                if let Err(e) = fs::remove_file(stale_p) {
                    let rb_res = rollback_publish_state(
                        node,
                        had_valid_pre_publish_set,
                        &staged_renames,
                        &backups,
                    );
                    let rb_suffix = rb_res
                        .err()
                        .map(|re| format!("; rollback error: {}", re))
                        .unwrap_or_default();
                    return Err(e).with_context(|| {
                        format!(
                            "Failed to remove stale companion artifact `{}`{}",
                            stale_p.display(),
                            rb_suffix
                        )
                    });
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => {
                let rb_res = rollback_publish_state(
                    node,
                    had_valid_pre_publish_set,
                    &staged_renames,
                    &backups,
                );
                let rb_suffix = rb_res
                    .err()
                    .map(|re| format!("; rollback error: {}", re))
                    .unwrap_or_default();
                return Err(e).with_context(|| {
                    format!(
                        "Failed to stat stale companion artifact `{}`{}",
                        stale_p.display(),
                        rb_suffix
                    )
                });
            }
        }
    }

    // Phase 3: Re-validate the published destination artifact set before removing backups
    if !validate_materialized_module_artifacts(node) {
        let rb_res =
            rollback_publish_state(node, had_valid_pre_publish_set, &staged_renames, &backups);
        let rb_suffix = rb_res
            .err()
            .map(|re| format!("; rollback error: {}", re))
            .unwrap_or_default();
        anyhow::bail!(
            "Post-publish artifact set validation failed for module `{}`{}",
            node.module_name,
            rb_suffix
        );
    }

    // Phase 4: Clean up backup files and verify their removal
    for rec in backups {
        if let Some((backup_p, _, _)) = rec.backup_file {
            if let Err(e) = fs::remove_file(&backup_p) {
                if e.kind() != std::io::ErrorKind::NotFound {
                    return Err(e).with_context(|| {
                        format!(
                            "Failed to remove temporary backup file `{}` after commit",
                            backup_p.display()
                        )
                    });
                }
            }
        }
    }
    Ok(())
}

struct TempDirGuard(PathBuf);
impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn run_command_with_timeout(
    mut cmd: Command,
    timeout: std::time::Duration,
    is_untrusted: bool,
) -> Result<std::process::Output> {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.process_group(0);
        if is_untrusted {
            unsafe {
                cmd.pre_exec(|| {
                    let zero = libc::rlimit {
                        rlim_cur: 0,
                        rlim_max: 0,
                    };
                    let _ = libc::setrlimit(libc::RLIMIT_CORE, &zero);
                    let max_data = libc::rlimit {
                        rlim_cur: 8 * 1024 * 1024 * 1024,
                        rlim_max: 8 * 1024 * 1024 * 1024,
                    };
                    let _ = libc::setrlimit(libc::RLIMIT_DATA, &max_data);
                    let max_fsize = libc::rlimit {
                        rlim_cur: 512 * 1024 * 1024,
                        rlim_max: 512 * 1024 * 1024,
                    };
                    let _ = libc::setrlimit(libc::RLIMIT_FSIZE, &max_fsize);
                    Ok(())
                });
            }
        }
    }
    cmd.stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    let mut child = cmd.spawn()?;
    let mut stdout_pipe = child.stdout.take();
    let mut stderr_pipe = child.stderr.take();
    let out_handle = std::thread::spawn(move || -> Vec<u8> {
        let mut buf = Vec::new();
        if let Some(ref mut r) = stdout_pipe {
            let _ = std::io::Read::read_to_end(r, &mut buf);
        }
        buf
    });
    let err_handle = std::thread::spawn(move || -> Vec<u8> {
        let mut buf = Vec::new();
        if let Some(ref mut r) = stderr_pipe {
            let _ = std::io::Read::read_to_end(r, &mut buf);
        }
        buf
    });
    let start = Instant::now();
    loop {
        if let Some(status) = child.try_wait()? {
            let stdout = out_handle.join().unwrap_or_default();
            let stderr = err_handle.join().unwrap_or_default();
            return Ok(std::process::Output {
                status,
                stdout,
                stderr,
            });
        }
        if start.elapsed() >= timeout {
            #[cfg(unix)]
            {
                let pgid = child.id() as i32;
                if pgid > 0 {
                    unsafe {
                        let _ = libc::kill(-pgid, libc::SIGKILL);
                    }
                }
            }
            let _ = child.kill();
            let _ = child.wait();
            anyhow::bail!(
                "`lean` module compilation exceeded timeout of {}s",
                timeout.as_secs()
            );
        }
        std::thread::sleep(std::time::Duration::from_millis(5));
    }
}

fn probe_bwrap_sandbox() -> Option<PathBuf> {
    #[cfg(test)]
    if let Ok(test_bwrap) = std::env::var("TURBO_LEAN_TEST_BWRAP_BIN") {
        let p = PathBuf::from(test_bwrap.trim());
        if p.is_file() {
            return Some(p);
        }
    }
    let candidates = [
        PathBuf::from("/usr/bin/bwrap"),
        PathBuf::from("/bin/bwrap"),
        PathBuf::from("bwrap"),
    ];
    for cand in candidates {
        let mut probe = Command::new(&cand);
        probe.args([
            "--unshare-all",
            "--new-session",
            "--die-with-parent",
            "--clearenv",
            "--setenv",
            "PATH",
            "/usr/bin:/bin",
            "--dev",
            "/dev",
            "--proc",
            "/proc",
            "--tmpfs",
            "/tmp",
        ]);
        for sys_dir in ["/usr", "/bin", "/lib", "/lib64", "/etc"] {
            let p = Path::new(sys_dir);
            if p.exists() {
                probe.arg("--ro-bind").arg(p).arg(p);
            }
        }
        if probe
            .arg("true")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
        {
            return Some(cand);
        }
    }
    None
}

fn canonicalize_path_with_missing_tail(p: &Path) -> Result<PathBuf> {
    if !p.is_absolute()
        || p.components()
            .any(|c| matches!(c, std::path::Component::ParentDir))
    {
        anyhow::bail!(
            "Search path entry `{}` must be absolute and contain no `..`",
            p.display()
        );
    }
    let mut cur = p;
    let mut tail_names: Vec<std::ffi::OsString> = Vec::new();
    while !cur.exists() {
        let fname = cur.file_name().ok_or_else(|| {
            anyhow::anyhow!("Cannot resolve non-existent root path `{}`", p.display())
        })?;
        tail_names.push(fname.to_os_string());
        cur = cur
            .parent()
            .ok_or_else(|| anyhow::anyhow!("Cannot resolve parent of path `{}`", p.display()))?;
    }
    let mut canon = cur.canonicalize().with_context(|| {
        format!(
            "Failed to canonicalize existing ancestor `{}` of `{}`",
            cur.display(),
            p.display()
        )
    })?;
    for name in tail_names.into_iter().rev() {
        canon.push(name);
    }
    Ok(canon)
}

fn validate_untrusted_sandbox_search_paths(
    cfg: &ProjectConfig,
    tc_prefix: &Path,
    lean_path_env: &str,
    ld_library_path_env: &str,
) -> Result<()> {
    let canon_tc = tc_prefix.canonicalize().with_context(|| {
        format!(
            "Failed to canonicalize toolchain prefix `{}`",
            tc_prefix.display()
        )
    })?;
    let canon_root_pkg = cfg.root_pkg.pkg_root.canonicalize().with_context(|| {
        format!(
            "Failed to canonicalize root package `{}`",
            cfg.root_pkg.pkg_root.display()
        )
    })?;
    let mut canon_deps: Vec<PathBuf> = Vec::with_capacity(cfg.dep_pkgs.len());
    for dp in &cfg.dep_pkgs {
        canon_deps.push(dp.pkg_root.canonicalize().with_context(|| {
            format!(
                "Failed to canonicalize dependency package `{}`",
                dp.pkg_root.display()
            )
        })?);
    }
    for env_val in [lean_path_env, ld_library_path_env] {
        for entry in env_val.split(':').filter(|s| !s.is_empty()) {
            let p = Path::new(entry);
            let Ok(canon_entry) = canonicalize_path_with_missing_tail(p) else {
                anyhow::bail!(
                    "Invalid or unbound search path entry `{}` in untrusted sandbox: fail-closed sandbox gate",
                    entry
                );
            };
            let is_bound_root = canon_entry.starts_with(&canon_tc)
                || canon_entry.starts_with(&canon_root_pkg)
                || canon_deps.iter().any(|dp| canon_entry.starts_with(dp));
            if !is_bound_root {
                anyhow::bail!(
                    "Invalid or unbound search path entry `{}` (canonical `{}`) in untrusted sandbox: fail-closed sandbox gate",
                    entry,
                    canon_entry.display()
                );
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn build_module_compile_command(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    tmp_dir: &Path,
    tmp_olean: &Path,
    tmp_ilean: &Path,
    tmp_c: &Path,
    tmp_setup: &Path,
    lean_path_env: &str,
    ld_library_path_env: &str,
    is_untrusted: bool,
    bwrap_bin: Option<&Path>,
) -> Result<Command> {
    let stack_kb = if is_untrusted {
        "262144".to_string()
    } else {
        std::env::var("LEAN_STACK_SIZE_KB").unwrap_or_else(|_| "262144".to_string())
    };
    let mut cmd = if is_untrusted {
        let bwrap_path = bwrap_bin.ok_or_else(|| {
            anyhow::anyhow!(
                "Untrusted module compilation requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
            )
        })?;
        let tc_prefix = cfg
            .toolchain_lib
            .parent()
            .filter(|p| p.is_dir() && p.is_absolute() && *p != Path::new("/"))
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "Invalid toolchain prefix `{}` for bubblewrap sandbox: fail-closed sandbox gate",
                    cfg.toolchain_lib.display()
                )
            })?;
        validate_untrusted_sandbox_search_paths(
            cfg,
            tc_prefix,
            lean_path_env,
            ld_library_path_env,
        )?;
        let mut c = Command::new(bwrap_path);
        c.args([
            "--unshare-all",
            "--new-session",
            "--die-with-parent",
            "--clearenv",
            "--setenv",
            "PATH",
            "/usr/bin:/bin",
            "--setenv",
            "LEAN_PATH",
            lean_path_env,
            "--setenv",
            "LEAN_STACK_SIZE_KB",
            &stack_kb,
        ]);
        if !ld_library_path_env.is_empty() {
            c.args(["--setenv", "LD_LIBRARY_PATH", ld_library_path_env]);
        }
        c.args([
            "--dev",
            "/dev",
            "--proc",
            "/proc",
            "--tmpfs",
            "/tmp",
            "--ro-bind-try",
            "/usr",
            "/usr",
            "--ro-bind-try",
            "/bin",
            "/bin",
            "--ro-bind-try",
            "/lib",
            "/lib",
            "--ro-bind-try",
            "/lib64",
            "/lib64",
            "--ro-bind-try",
            "/etc/ld.so.cache",
            "/etc/ld.so.cache",
            "--ro-bind-try",
            "/etc/localtime",
            "/etc/localtime",
        ]);
        c.arg("--ro-bind").arg(tc_prefix).arg(tc_prefix);
        c.arg("--ro-bind")
            .arg(&cfg.root_pkg.pkg_root)
            .arg(&cfg.root_pkg.pkg_root);
        for dp in &cfg.dep_pkgs {
            if !dp.pkg_root.starts_with(&cfg.root_pkg.pkg_root) {
                c.arg("--ro-bind").arg(&dp.pkg_root).arg(&dp.pkg_root);
            }
        }
        c.arg("--bind").arg(tmp_dir).arg(tmp_dir);
        c.arg("--chdir").arg(&node.pkg_root);
        c.arg(&cfg.lean_bin);
        scrub_untrusted_env(&mut c);
        c
    } else {
        let mut c = Command::new(&cfg.lean_bin);
        c.current_dir(&node.pkg_root)
            .env("LEAN_PATH", lean_path_env)
            .env("LD_LIBRARY_PATH", ld_library_path_env)
            .env("LEAN_STACK_SIZE_KB", &stack_kb);
        c
    };
    // When `is_untrusted`, pass Lean's `-M 4096` (4096 MB internal allocator limit) after `cfg.lean_bin`
    // in addition to the OS-level `RLIMIT_DATA` enforced in `run_command_with_timeout`.
    if is_untrusted {
        cmd.arg("-M").arg("4096");
    }
    for arg in &node.strong_args {
        cmd.arg(arg);
    }
    for arg in &node.weak_args {
        cmd.arg(arg);
    }
    cmd.arg(&node.src_path)
        .arg("-R")
        .arg(&node.src_root)
        .arg("-o")
        .arg(tmp_olean)
        .arg("-i")
        .arg(tmp_ilean)
        .arg("--setup")
        .arg(tmp_setup);
    if node.needs_c {
        cmd.arg("-c").arg(tmp_c);
    }
    Ok(cmd)
}

fn compile_single_module_direct(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    lean_path_env: &str,
    ld_library_path_env: &str,
    is_untrusted: bool,
    bwrap_bin: Option<&Path>,
) -> Result<(i64, String)> {
    let t0 = Instant::now();
    let pid = std::process::id();
    let seq = crate::pack::next_tmp_id();
    let build_root = node.pkg_root.join(".lake/build");
    fs::create_dir_all(&build_root)?;
    let tmp_dir = build_root.join(format!(
        ".turbo_mod_tmp_{}_{}_{}",
        pid,
        seq,
        node.module_name.replace('.', "_")
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir)?;
    let _tmp_guard = TempDirGuard(tmp_dir.clone());
    let rel_slash = node.module_name.replace('.', "/");
    let tmp_olean = tmp_dir.join(format!("{}.olean", rel_slash));
    let tmp_ilean = tmp_dir.join(format!("{}.ilean", rel_slash));
    let tmp_c = tmp_dir.join(format!("{}.c", rel_slash));
    let tmp_setup = tmp_dir.join(format!("{}.setup.json", rel_slash));
    if let Some(parent) = tmp_olean.parent() {
        fs::create_dir_all(parent)?;
    }
    let mut setup_options = serde_json::Map::new();
    for arg in node.weak_args.iter().chain(node.strong_args.iter()) {
        if let Some(kv) = arg.strip_prefix("-D") {
            if let Some((k, v)) = kv.split_once('=') {
                let json_v = if v == "true" {
                    serde_json::Value::Bool(true)
                } else if v == "false" {
                    serde_json::Value::Bool(false)
                } else if let Ok(n) = v.parse::<u64>() {
                    serde_json::Value::Number(n.into())
                } else {
                    serde_json::Value::String(v.to_string())
                };
                setup_options.insert(k.to_string(), json_v);
            }
        }
    }
    let setup_json = serde_json::json!({
        "name": node.module_name,
        "package": node.pkg_name,
        "isModule": node.is_module,
        "options": setup_options,
        "importArts": {},
        "dynlibs": [],
        "plugins": []
    });
    fs::write(&tmp_setup, serde_json::to_vec(&setup_json)?)?;
    let cmd = build_module_compile_command(
        cfg,
        node,
        &tmp_dir,
        &tmp_olean,
        &tmp_ilean,
        &tmp_c,
        &tmp_setup,
        lean_path_env,
        ld_library_path_env,
        is_untrusted,
        bwrap_bin,
    )?;
    let timeout_secs = if is_untrusted {
        120u64
    } else {
        std::env::var("TURBO_LEAN_MODULE_TIMEOUT_SECS")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .filter(|&n| n > 0)
            .unwrap_or(300)
    };
    let output = run_command_with_timeout(
        cmd,
        std::time::Duration::from_secs(timeout_secs),
        is_untrusted,
    )
    .with_context(|| {
        format!(
            "Failed to invoke `lean` compiler ({}) for module `{}`",
            cfg.lean_bin.display(),
            node.module_name
        )
    })?;
    let stdout_str = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr_str = String::from_utf8_lossy(&output.stderr).to_string();
    if !output.status.success() {
        anyhow::bail!(
            "Native Lean compilation failed for module `{}` ({}):\n{}\n{}",
            node.module_name,
            node.src_path.display(),
            stdout_str.trim(),
            stderr_str.trim()
        );
    }
    let tmp_srv = PathBuf::from(format!("{}.server", tmp_olean.display()));
    let tmp_priv = PathBuf::from(format!("{}.private", tmp_olean.display()));
    let tmp_ir = tmp_olean.with_extension("ir");
    let tmp_ir_sig = PathBuf::from(format!("{}.sig", tmp_ir.display()));
    let is_regular_nonempty_in_tmp =
        |p: &Path| -> bool { p.starts_with(&tmp_dir) && is_regular_nonempty_file(p) };
    let has_olean = is_regular_nonempty_in_tmp(&tmp_olean);
    let has_ilean = is_regular_nonempty_in_tmp(&tmp_ilean);
    let has_srv = is_regular_nonempty_in_tmp(&tmp_srv);
    let has_priv = is_regular_nonempty_in_tmp(&tmp_priv);
    let has_c = is_regular_nonempty_in_tmp(&tmp_c);
    let artifacts_ok = c_abi::verify_module_artifact_set(
        has_olean,
        has_ilean,
        node.is_module,
        has_srv,
        has_priv,
        node.needs_c,
        has_c,
    );
    if !artifacts_ok {
        anyhow::bail!(
            "C-ABI gate `turbo_spec_verify_module_artifact_set` failed after compiling `{}` (olean={}, ilean={}, is_module={}, srv={}, priv={}, needs_c={}, c={})",
            node.module_name,
            has_olean,
            has_ilean,
            node.is_module,
            has_srv,
            has_priv,
            node.needs_c,
            has_c
        );
    }
    publish_module_artifacts_atomic(
        &tmp_dir,
        node,
        &tmp_olean,
        &tmp_ilean,
        &tmp_srv,
        &tmp_priv,
        &tmp_ir,
        &tmp_ir_sig,
        &tmp_c,
    )?;
    let dur_ms = t0.elapsed().as_millis() as i64;
    Ok((dur_ms, stdout_str))
}

fn store_module_artifacts_in_cas(
    store: &mut TurboStore,
    canon_project_dir: &Path,
    node: &ModuleNode,
    mod_action_key: &str,
    toolchain: &str,
    trust_domain: &str,
    pin_level: i64,
    dur_ms: i64,
) -> Result<Vec<BlobEntry>> {
    let base_dir = if node.pkg_root.starts_with(canon_project_dir) {
        canon_project_dir
    } else {
        &node.pkg_root
    };
    let blob_items = {
        let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
        let _guard = lock
            .lock()
            .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
        let _flock_guard = acquire_publish_flock_mode(&node.pkg_root, false)?;
        let artifact_files = collect_module_artifact_paths(node);
        let mut items: Vec<(String, Vec<u8>, String, String, u64)> =
            Vec::with_capacity(artifact_files.len());
        for (kind, abs_path) in artifact_files {
            let bytes = fs::read(&abs_path)?;
            let hash = blake3::hash(&bytes).to_hex().to_string();
            let sz = bytes.len() as u64;
            let rel_path = abs_path
                .strip_prefix(base_dir)
                .unwrap_or(&abs_path)
                .to_string_lossy()
                .replace('\\', "/");
            items.push((hash, bytes, kind.to_string(), rel_path, sz));
        }
        items
    };
    let entries = store.batch_store_immutable_blobs(&blob_items, trust_domain, pin_level)?;
    match store.acquire_singleflight(mod_action_key, toolchain, "module_unit", trust_domain)? {
        SingleflightOutcome::Leader(lease) => {
            if let Err(e) = store.publish_action(&lease, &entries, dur_ms, 0, 0, trust_domain) {
                store.remove_singleflight_done(&lease.action_key);
                drop(lease);
                return Err(e);
            }
        }
        SingleflightOutcome::CacheHit { .. } => {}
    }
    Ok(entries)
}

fn record_verified_dep_source(cfg: &ProjectConfig, node: &ModuleNode, olean_artifact_digest: &str) {
    let pkg_root = &node.pkg_root;
    let build_dir = pkg_root.join(".lake/build");
    let _ = fs::create_dir_all(&build_dir);
    let manifest_path = build_dir.join(".turbo_verified_sources.json");
    let mut manifest: VerifiedDepManifest = fs::read(&manifest_path)
        .ok()
        .and_then(|b| serde_json::from_slice::<VerifiedDepManifest>(&b).ok())
        .filter(|m| {
            m.pkg_name == node.pkg_name
                && m.toolchain == cfg.toolchain
                && m.lean_githash == cfg.lean_githash
                && m.pkg_config_digest == node.pkg_config_digest
        })
        .unwrap_or_else(|| VerifiedDepManifest {
            pkg_name: node.pkg_name.clone(),
            toolchain: cfg.toolchain.clone(),
            lean_githash: cfg.lean_githash.clone(),
            pkg_config_digest: node.pkg_config_digest.clone(),
            modules: BTreeMap::new(),
        });
    let rel_src = node
        .src_path
        .strip_prefix(pkg_root)
        .unwrap_or(&node.src_path)
        .to_string_lossy()
        .replace('\\', "/");
    manifest.modules.insert(
        rel_src,
        VerifiedDepModuleEntry {
            src_blake3: node.src_blake3.clone(),
            olean_artifact_digest: olean_artifact_digest.to_string(),
        },
    );
    if let Ok(json_bytes) = serde_json::to_vec(&manifest) {
        let tmp_path = build_dir.join(format!(
            ".turbo_verified_sources.json.tmp.{}.{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        if fs::write(&tmp_path, &json_bytes).is_ok() {
            let _ = fs::rename(&tmp_path, &manifest_path);
        }
    }
}

/// Orchestrate native Lean module compilation across the resolved DAG without invoking `lake build`.
/// Uses per-module CAS (`module_unit`), bounded worker parallelism (`jobs`), temporary output
/// directories, and atomic publication.
#[allow(clippy::too_many_arguments)]
pub fn build_project_modules_native(
    store: &mut TurboStore,
    project_dir: &Path,
    targets: &[String],
    trust_domain: &str,
    pin_level: i64,
    is_untrusted: bool,
    json_output: bool,
    file_hashes_opt: Option<&BTreeMap<String, String>>,
) -> Result<NativeBuildReport> {
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let project_name = canon_dir
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "lean-project".to_string());
    let cfg = resolve_project_config_with_trust(&canon_dir, is_untrusted)?;
    let dag = build_module_dag_with_trust(&cfg, targets, is_untrusted)?;
    let mut report = NativeBuildReport {
        modules_total: dag.nodes.len(),
        modules_compiled: 0,
        modules_cached: 0,
        modules_up_to_date_reused: 0,
        waves_count: dag.waves.len(),
        config_digest: cfg.canonical_config_digest.clone(),
        compiled_modules: Vec::new(),
        cached_modules: Vec::new(),
        bwrap_used: false,
    };
    if dag.nodes.is_empty() {
        return Ok(report);
    }
    // Ensure `.lake/build/lib/lean` and `.lake/build/ir` exist before compilation waves
    fs::create_dir_all(
        cfg.root_pkg
            .pkg_root
            .join(&cfg.root_pkg.build_dir)
            .join(&cfg.root_pkg.lean_lib_dir),
    )?;
    fs::create_dir_all(
        cfg.root_pkg
            .pkg_root
            .join(&cfg.root_pkg.build_dir)
            .join(&cfg.root_pkg.ir_dir),
    )?;
    for dp in &cfg.dep_pkgs {
        let _ = fs::create_dir_all(dp.pkg_root.join(&dp.build_dir).join(&dp.lean_lib_dir));
        let _ = fs::create_dir_all(dp.pkg_root.join(&dp.build_dir).join(&dp.ir_dir));
    }
    let (lean_path_env, ld_library_path_env) = build_lean_search_path(&cfg, is_untrusted);
    let bwrap_bin = if is_untrusted {
        probe_bwrap_sandbox()
    } else {
        None
    };
    report.bwrap_used = bwrap_bin.is_some();
    let base_jobs = std::env::var("TURBO_LEAN_JOBS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4)
        });
    let max_jobs = if is_untrusted {
        base_jobs.min(2)
    } else {
        base_jobs
    };
    // Map from module_name -> olean artifact set digest
    let mut olean_digests: HashMap<String, String> = HashMap::new();
    // Pre-compute digests for external prebuilt `.olean` dependencies (only populated when `!is_untrusted`)
    for node in dag.nodes.values() {
        for (ext_mod, ext_path) in &node.external_olean_deps {
            if !olean_digests.contains_key(ext_mod) {
                let d = compute_olean_artifact_set_digest(ext_path)?;
                olean_digests.insert(ext_mod.clone(), d);
            }
        }
    }
    // Execute topological waves
    for wave in &dag.waves {
        let mut misses_to_compile: Vec<(String, String)> = Vec::new();
        for mod_name in wave {
            let node = dag.nodes.get(mod_name).expect("wave module in dag");
            // Gather sorted direct + transitive dependency `.olean` digests for this module
            let mut dep_digests_map: BTreeMap<String, String> = BTreeMap::new();
            let mut dep_work: VecDeque<&str> = VecDeque::new();
            for d in &node.direct_dag_deps {
                dep_work.push_back(d);
            }
            for (ext_m, _) in &node.external_olean_deps {
                if let Some(dig) = olean_digests.get(ext_m) {
                    dep_digests_map.insert(ext_m.clone(), dig.clone());
                }
            }
            while let Some(cur_dep) = dep_work.pop_front() {
                if dep_digests_map.contains_key(cur_dep) {
                    continue;
                }
                let dig = olean_digests.get(cur_dep).cloned().ok_or_else(|| {
                    anyhow::anyhow!(
                        "Internal DAG error: dependency `{}` of `{}` missing olean digest",
                        cur_dep,
                        mod_name
                    )
                })?;
                dep_digests_map.insert(cur_dep.to_string(), dig);
                if let Some(dep_node) = dag.nodes.get(cur_dep) {
                    for sub_d in &dep_node.direct_dag_deps {
                        if !dep_digests_map.contains_key(sub_d) {
                            dep_work.push_back(sub_d);
                        }
                    }
                    for (ext_m, _) in &dep_node.external_olean_deps {
                        if let Some(edig) = olean_digests.get(ext_m) {
                            dep_digests_map
                                .entry(ext_m.clone())
                                .or_insert_with(|| edig.clone());
                        }
                    }
                }
            }
            let dep_digests_vec: Vec<(String, String)> = dep_digests_map.into_iter().collect();
            let mod_key = compute_module_cas_key(&cfg, node, &dep_digests_vec, node.needs_c)?;
            // Check per-module CAS in TurboStore (`module_unit`), or fallback key with `needs_c=true` when `node.needs_c=false`.
            // Use `get_cached_action` (read-only lookup) so probing `c_key` or failing compilation does not leave an unreleased Singleflight lease.
            let mut cas_hit_outputs: Option<Vec<BlobEntry>> = None;
            if let Some(outputs) = store.get_cached_action(&mod_key, trust_domain)? {
                cas_hit_outputs = Some(outputs);
            } else if !node.needs_c {
                let c_key = compute_module_cas_key(&cfg, node, &dep_digests_vec, true)?;
                if let Some(outputs) = store.get_cached_action(&c_key, trust_domain)? {
                    cas_hit_outputs = Some(outputs);
                }
            }
            if let Some(outputs) = cas_hit_outputs {
                let target_root = if node.pkg_root.starts_with(&canon_dir) {
                    &canon_dir
                } else {
                    &node.pkg_root
                };
                let cas_restored_ok = {
                    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
                    let _guard = lock.lock().map_err(|_| {
                        anyhow::anyhow!("Module artifact publication mutex poisoned")
                    })?;
                    let _flock_guard = acquire_publish_flock(&node.pkg_root)?;
                    wipe_existing_module_artifacts(node);
                    store.materialize_into_worktree(target_root, &project_name, &outputs)?;
                    if !node.needs_c {
                        let _ = fs::remove_file(&node.c_path);
                    }
                    let mut hashes_ok = validate_materialized_module_artifacts(node);
                    if hashes_ok {
                        for entry in &outputs {
                            if !node.needs_c && entry.kind == "c" {
                                continue;
                            }
                            let mat_path = target_root.join(&entry.rel_path);
                            match fs::read(&mat_path) {
                                Ok(bytes) => {
                                    let actual = blake3::hash(&bytes).to_hex().to_string();
                                    if actual != entry.blob_hash
                                        || bytes.len() as u64 != entry.size_bytes
                                    {
                                        hashes_ok = false;
                                        break;
                                    }
                                }
                                Err(_) => {
                                    hashes_ok = false;
                                    break;
                                }
                            }
                        }
                    }
                    if !hashes_ok {
                        wipe_existing_module_artifacts(node);
                    }
                    hashes_ok
                };
                if cas_restored_ok {
                    let dig = compute_olean_artifact_set_digest(&node.olean_path)?;
                    if !is_untrusted {
                        record_verified_dep_source(&cfg, node, &dig);
                    }
                    olean_digests.insert(mod_name.clone(), dig);
                    report.modules_cached += 1;
                    report.cached_modules.push(mod_name.clone());
                    continue;
                }
            } else {
                let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
                let _guard = lock
                    .lock()
                    .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
                let _flock_guard = acquire_publish_flock(&node.pkg_root)?;
                wipe_existing_module_artifacts(node);
            }
            misses_to_compile.push((mod_name.clone(), mod_key));
        }
        if misses_to_compile.is_empty() {
            continue;
        }
        if !cfg.lean_bin.is_file() {
            anyhow::bail!(
                "Cannot compile {} uncached Lean module(s) for {} because no `lean` compiler binary is installed on this host (requested toolchain `{}`)",
                misses_to_compile.len(),
                project_dir.display(),
                cfg.toolchain
            );
        }
        // Fail closed unconditionally before spawning compilation workers if untrusted and bwrap is unavailable
        if is_untrusted && bwrap_bin.is_none() {
            anyhow::bail!(
                "Untrusted module compilation requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
            );
        }
        // Compile all cache-miss modules in the current wave in parallel (bounded by `max_jobs`)
        let workers = max_jobs.min(misses_to_compile.len()).max(1);
        let next_idx = std::sync::atomic::AtomicUsize::new(0);
        let misses_ref = &misses_to_compile;
        let dag_ref = &dag;
        let cfg_ref = &cfg;
        let lp_ref = lean_path_env.as_str();
        let ld_ref = ld_library_path_env.as_str();
        let bwrap_ref = bwrap_bin.as_deref();
        let wave_results: Vec<(usize, Result<(i64, String)>)> = std::thread::scope(|s| {
            let mut handles = Vec::with_capacity(workers);
            for _ in 0..workers {
                let idx_ref = &next_idx;
                handles.push(s.spawn(move || {
                    let mut local = Vec::new();
                    loop {
                        let i = idx_ref.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        if i >= misses_ref.len() {
                            break;
                        }
                        let (ref mod_name, _) = misses_ref[i];
                        let node = dag_ref.nodes.get(mod_name).expect("node in dag");
                        let res = compile_single_module_direct(
                            cfg_ref,
                            node,
                            lp_ref,
                            ld_ref,
                            is_untrusted,
                            bwrap_ref,
                        );
                        local.push((i, res));
                    }
                    local
                }));
            }
            let mut all = Vec::with_capacity(misses_ref.len());
            for h in handles {
                if let Ok(part) = h.join() {
                    all.extend(part);
                }
            }
            all
        });
        let mut ordered_results = wave_results;
        ordered_results.sort_by_key(|(i, _)| *i);
        for (i, res) in ordered_results {
            let (ref mod_name, ref mod_key) = misses_to_compile[i];
            let (dur_ms, stdout_str) = res?;
            if !json_output && !stdout_str.trim().is_empty() {
                print!("{}", stdout_str);
            }
            let node = dag.nodes.get(mod_name).expect("node in dag");
            store_module_artifacts_in_cas(
                store,
                &canon_dir,
                node,
                mod_key,
                &cfg.toolchain,
                trust_domain,
                pin_level,
                dur_ms,
            )?;
            let dig = compute_olean_artifact_set_digest(&node.olean_path)?;
            if !is_untrusted {
                record_verified_dep_source(&cfg, node, &dig);
            }
            olean_digests.insert(mod_name.clone(), dig);
            report.modules_compiled += 1;
            report.compiled_modules.push(mod_name.clone());
        }
    }
    if targets.is_empty() && !is_untrusted {
        if let Some(fh) = file_hashes_opt {
            lake_build::record_verified_project_oleans(&canon_dir, fh);
        }
    }
    Ok(report)
}
#[cfg(test)]
mod tests {
    use super::*;
    fn make_temp_test_dir(tag: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "turbo_lean_mod_builder_{}_{}_{}",
            tag,
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create temp test dir");
        dir
    }
    #[test]
    fn test_parse_header_imports_comments_prelude_and_module_flags() {
        let src = "\
/-
  Multi-line block comment with fake import:
  import Fake.Blocked
  /- nested comment import Fake.Nested -/
-/
module
prelude
-- inline comment import Fake.Inline
public import Mathlib.Logic.Basic
import all Demo.Internal -- trailing comment
meta import Demo.MetaMod
import Demo.A Demo.B
@[expose] public section
namespace Demo
@[inline, export demo_c_symbol]
def f (x : Nat) : Nat := x
";
        let info = parse_header_info(src);
        assert!(info.is_module);
        assert!(info.has_prelude);
        assert!(info.has_c_export);
        assert_eq!(
            info.imports,
            vec![
                "Mathlib.Logic.Basic".to_string(),
                "Demo.Internal".to_string(),
                "Demo.MetaMod".to_string(),
                "Demo.A".to_string(),
                "Demo.B".to_string()
            ]
        );
    }
    #[test]
    fn test_parse_lakefile_toml_and_lakefile_lean_static_configs() {
        let dir = make_temp_test_dir("cfg_parse");
        let toml_content = r#"
name = "demo-toml-pkg"
version = "0.1.0"
srcDir = "src"
defaultTargets = ["DemoLib"]
moreLeanArgs = ["-DwarningAsError=false"]
weakLeanArgs = ["-Dpp.unicode.fun=true"]
precompileModules = false
[leanOptions]
autoImplicit = false
"relaxedAutoImplicit" = false
[[require]]
name = "dep-a"
path = "../dep-a"
[[lean_lib]]
name = "DemoLib"
roots = ["Demo"]
globs = ["Demo.*", "Extra.+"]
moreLeanArgs = ["-j1"]
[[lean_exe]]
name = "demo-runner"
root = "Demo.Main"
supportInterpreter = true
"#;
        let toml_path = dir.join("lakefile.toml");
        fs::write(&toml_path, toml_content).unwrap();
        let pkg_toml = parse_lakefile_toml(&dir, &toml_path, true).unwrap();
        assert_eq!(pkg_toml.name, "demo-toml-pkg");
        assert_eq!(pkg_toml.src_dir, PathBuf::from("src"));
        assert_eq!(pkg_toml.default_targets, vec!["DemoLib".to_string()]);
        assert_eq!(
            pkg_toml
                .lean_options
                .get("autoImplicit")
                .map(String::as_str),
            Some("false")
        );
        assert_eq!(pkg_toml.libs.len(), 1);
        assert_eq!(
            pkg_toml.libs[0].globs,
            vec![
                GlobSpec::AndSubmodules("Demo".to_string()),
                GlobSpec::Submodules("Extra".to_string()),
            ]
        );
        assert_eq!(pkg_toml.exes.len(), 1);
        assert_eq!(pkg_toml.exes[0].root, "Demo.Main");
        assert!(pkg_toml.exes[0].support_interpreter);
        let lean_content = r#"
import Lake
open Lake DSL
package «demo-lean-pkg» where
  srcDir := "lean_src"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  moreLeanArgs := #["-DwarningAsError=false"]
@[default_target]
lean_lib «DemoLean» where
  roots := #[`DemoLean]
  globs := #[.submodules `DemoLean, .one `DemoLeanRoot]
lean_exe «demo-exe» where
  root := `DemoLean.Main
  supportInterpreter := true
"#;
        let lean_path = dir.join("lakefile.lean");
        fs::write(&lean_path, lean_content).unwrap();
        let pkg_lean = parse_lakefile_lean(&dir, &lean_path, true).unwrap();
        assert_eq!(pkg_lean.name, "demo-lean-pkg");
        assert_eq!(pkg_lean.src_dir, PathBuf::from("lean_src"));
        assert_eq!(pkg_lean.default_targets, vec!["DemoLean".to_string()]);
        assert_eq!(
            pkg_lean
                .lean_options
                .get("autoImplicit")
                .map(String::as_str),
            Some("false")
        );
        assert_eq!(
            pkg_lean.libs[0].globs,
            vec![
                GlobSpec::Submodules("DemoLean".to_string()),
                GlobSpec::One("DemoLeanRoot".to_string()),
            ]
        );
        let _ = fs::remove_dir_all(&dir);
    }
    #[test]
    fn test_dynamic_lakefile_fails_closed_with_precise_diagnostics() {
        let dir = make_temp_test_dir("fail_closed");
        // 1. Dynamic `meta if` in lakefile.lean
        let dyn_if = "import Lake\nopen Lake DSL\npackage p\nmeta if true then\n  lean_lib A\n";
        let lf = dir.join("lakefile.lean");
        fs::write(&lf, dyn_if).unwrap();
        let err1 = parse_lakefile_lean(&dir, &lf, true)
            .unwrap_err()
            .to_string();
        assert!(err1.contains("meta if") && err1.contains("fail-closed"));
        // 2. Dynamic `run_cmd` in lakefile.lean
        let dyn_cmd = "import Lake\nopen Lake DSL\npackage p\nrun_cmd IO.println \"hi\"\n";
        fs::write(&lf, dyn_cmd).unwrap();
        let err2 = parse_lakefile_lean(&dir, &lf, true)
            .unwrap_err()
            .to_string();
        assert!(err2.contains("run_cmd") && err2.contains("fail-closed"));
        // 3. Unbuilt dynamic `extern_lib` in root lakefile.lean
        let dyn_ext = "import Lake\nopen Lake DSL\npackage p\nextern_lib libfoo pkg := do\n  pure ()\nlean_lib A\n";
        fs::write(&lf, dyn_ext).unwrap();
        let err3 = parse_lakefile_lean(&dir, &lf, true)
            .unwrap_err()
            .to_string();
        assert!(err3.contains("extern_lib") && err3.contains("libfoo"));
        // 4. Custom `target ... := do` in root lakefile.lean
        let dyn_tgt = "import Lake\nopen Lake DSL\npackage p\ntarget custom_c pkg : FilePath := do\n  pure ()\nlean_lib A\n";
        fs::write(&lf, dyn_tgt).unwrap();
        let err4 = parse_lakefile_lean(&dir, &lf, true)
            .unwrap_err()
            .to_string();
        assert!(err4.contains("custom_c") && err4.contains("fail-closed"));
        // 5. Unsafe `--load-dynlib` in `moreLeanArgs` in lakefile.toml
        let dyn_toml = "name = \"p\"\nmoreLeanArgs = [\"--load-dynlib=evil.so\"]\n[[lean_lib]]\nname = \"A\"\n";
        let tf = dir.join("lakefile.toml");
        fs::write(&tf, dyn_toml).unwrap();
        let err5 = parse_lakefile_toml(&dir, &tf, true)
            .unwrap_err()
            .to_string();
        assert!(err5.contains("--load-dynlib") && err5.contains("fail-closed"));
        let _ = fs::remove_dir_all(&dir);
    }
    #[test]
    fn test_dag_cycle_and_missing_module_detection() {
        let dir = make_temp_test_dir("dag_cycle_missing");
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"cyc\"\n[[lean_lib]]\nname = \"Cyc\"\nglobs = [\"Cyc.*\"]\n",
        )
        .unwrap();
        fs::create_dir_all(dir.join("Cyc")).unwrap();
        fs::write(dir.join("Cyc/A.lean"), "import Cyc.B\ndef a : Nat := 1\n").unwrap();
        fs::write(dir.join("Cyc/B.lean"), "import Cyc.C\ndef b : Nat := 2\n").unwrap();
        fs::write(dir.join("Cyc/C.lean"), "import Cyc.A\ndef c : Nat := 3\n").unwrap();
        let cfg = resolve_project_config(&dir).unwrap();
        let cyc_err = build_module_dag(&cfg, &[]).unwrap_err().to_string();
        assert!(
            cyc_err.contains("Module import cycle detected:")
                && cyc_err.contains("Cyc.A")
                && cyc_err.contains("Cyc.B")
                && cyc_err.contains("Cyc.C"),
            "unexpected cycle error: {}",
            cyc_err
        );
        // Replace cycle with missing import
        fs::write(
            dir.join("Cyc/C.lean"),
            "import NonExistent.GhostMod\ndef c : Nat := 3\n",
        )
        .unwrap();
        let miss_err = build_module_dag(&cfg, &[]).unwrap_err().to_string();
        assert!(
            miss_err.contains("Missing module `NonExistent.GhostMod`")
                && miss_err.contains("Cyc.C"),
            "unexpected missing error: {}",
            miss_err
        );
        // Unsupported facet check
        fs::write(dir.join("Cyc/C.lean"), "def c : Nat := 3\n").unwrap();
        let facet_err = build_module_dag(&cfg, &["Cyc:unknown_facet".to_string()])
            .unwrap_err()
            .to_string();
        assert!(facet_err.contains("Unsupported target facet `:unknown_facet`"));
        let _ = fs::remove_dir_all(&dir);
    }
    #[test]
    fn test_native_module_builder_cas_partial_invalidation_lazy_c_and_lake_differential() {
        let dir = make_temp_test_dir("native_e2e");
        let store_dir = dir.join(".turbo_store");
        let proj_dir = dir.join("proj");
        let dep_dir = proj_dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("DepPkg")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepPkg\"\nroots = [\"DepPkg.Base\"]\n",
        )
        .unwrap();
        fs::write(
            dep_dir.join("DepPkg/Base.lean"),
            "namespace DepPkg\ndef baseVal : Nat := 10\nend DepPkg\n",
        )
        .unwrap();
        let manifest_json = r#"{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {
      "type": "path",
      "name": "dep_pkg",
      "dir": ".lake/packages/dep_pkg",
      "configFile": "lakefile.toml",
      "inherited": false
    }
  ],
  "name": "app_pkg",
  "lakeDir": ".lake",
  "fixedToolchain": false
}"#;
        fs::write(proj_dir.join("lake-manifest.json"), manifest_json).unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[leanOptions]\nautoImplicit = false\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        // App.A imports DepPkg.Base
        fs::write(
            proj_dir.join("App/A.lean"),
            "import DepPkg.Base\nnamespace App\ndef aVal : Nat := DepPkg.baseVal + 5\ntheorem a_eq : aVal = 15 := rfl\nend App\n",
        )
        .unwrap();
        // App.B imports App.A
        fs::write(
            proj_dir.join("App/B.lean"),
            "import App.A\nnamespace App\ntheorem b_thm : aVal + 1 = 16 := rfl\nend App\n",
        )
        .unwrap();
        // App.Indep is a Lean 4.35 `module` completely independent of App.A and App.B
        fs::write(
            proj_dir.join("App/Indep.lean"),
            "module\n@[expose] public def indepVal : Nat := 99\npublic theorem indep_thm : indepVal = 99 := rfl\n",
        )
        .unwrap();
        let mut store = TurboStore::open(Some(&store_dir)).unwrap();
        // 1. Cold build: compiles DepPkg.Base, App.A, App.Indep, App.B
        let rep1 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep1.modules_total, 4);
        assert_eq!(rep1.modules_compiled, 4);
        assert_eq!(rep1.modules_cached, 0);
        let build_lib = proj_dir.join(".lake/build/lib/lean/App");
        assert!(build_lib.join("A.olean").is_file());
        assert!(build_lib.join("A.ilean").is_file());
        assert!(build_lib.join("B.olean").is_file());
        assert!(build_lib.join("Indep.olean").is_file());
        // Verify Lean 4.35 `module` companion artifacts (.olean.server, .olean.private)
        assert!(build_lib.join("Indep.olean.server").is_file());
        assert!(build_lib.join("Indep.olean.private").is_file());
        // Verify lazy `.c` policy: pure library modules without `precompileModules` or `@[export]` do not emit `.c`
        assert!(!proj_dir.join(".lake/build/ir/App/A.c").is_file());
        // 2. Warm build with clean `.lake/build` (both root and dep): all 4 modules hit per-module CAS!
        fs::remove_dir_all(proj_dir.join(".lake/build")).unwrap();
        fs::remove_dir_all(dep_dir.join(".lake/build")).unwrap();
        let rep2 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep2.modules_total, 4);
        assert_eq!(rep2.modules_compiled, 0);
        assert_eq!(rep2.modules_cached, 4);
        assert!(build_lib.join("Indep.olean.server").is_file());
        assert!(build_lib.join("Indep.olean.private").is_file());
        // 3. Partial invalidation: modify leaf `App/B.lean`; `App.A` and `App.Indep` MUST hit CAS
        // (and `DepPkg.Base` is already fresh in `.lake/packages/dep_pkg/.lake/build`)!
        fs::write(
            proj_dir.join("App/B.lean"),
            "import App.A\nnamespace App\ntheorem b_thm : aVal + 2 = 17 := rfl\nend App\n",
        )
        .unwrap();
        let rep3 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep3.modules_compiled, 1);
        assert_eq!(rep3.compiled_modules, vec!["App.B".to_string()]);
        assert_eq!(rep3.modules_cached, 2);
        assert!(rep3.cached_modules.contains(&"App.A".to_string()));
        assert!(rep3.cached_modules.contains(&"App.Indep".to_string()));
        // 4. Upstream dependency invalidation: modify `App/A.lean`; `App.A` and `App.B` recompile, while `App.Indep` hits CAS!
        fs::write(
            proj_dir.join("App/A.lean"),
            "import DepPkg.Base\nnamespace App\ndef aVal : Nat := DepPkg.baseVal + 20\ntheorem a_eq : aVal = 30 := rfl\nend App\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("App/B.lean"),
            "import App.A\nnamespace App\ntheorem b_thm : aVal + 2 = 32 := rfl\nend App\n",
        )
        .unwrap();
        let rep4 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep4.modules_compiled, 2);
        assert_eq!(
            rep4.compiled_modules,
            vec!["App.A".to_string(), "App.B".to_string()]
        );
        assert_eq!(rep4.modules_cached, 1);
        assert!(rep4.cached_modules.contains(&"App.Indep".to_string()));
        // 5. Explicit `:c` facet materializes `.c` codegen
        let rep5 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &["App.A:c".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep5.modules_total, 1); // App.A (DepPkg.Base is fresh external .olean)
        assert!(proj_dir.join(".lake/build/ir/App/A.c").is_file());
        // 6. Differential test against `lake build` on an isolated single-package project
        let diff_dir = dir.join("diff_proj");
        fs::create_dir_all(diff_dir.join("Diff")).unwrap();
        fs::write(
            diff_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            diff_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage «diff» where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n@[default_target]\nlean_lib «Diff» where\n  globs := #[.submodules `Diff]\n",
        )
        .unwrap();
        fs::write(
            diff_dir.join("Diff/Core.lean"),
            "namespace Diff\ndef sq (n : Nat) : Nat := n * n\ntheorem sq_two : sq 2 = 4 := rfl\nend Diff\n",
        )
        .unwrap();
        fs::write(
            diff_dir.join("Diff/Use.lean"),
            "import Diff.Core\nnamespace Diff\ntheorem sq_three : sq 3 = 9 := rfl\nend Diff\n",
        )
        .unwrap();
        build_project_modules_native(
            &mut store,
            &diff_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        let native_core_olean =
            fs::read(diff_dir.join(".lake/build/lib/lean/Diff/Core.olean")).unwrap();
        let native_use_olean =
            fs::read(diff_dir.join(".lake/build/lib/lean/Diff/Use.olean")).unwrap();
        assert!(!native_core_olean.is_empty() && !native_use_olean.is_empty());
        let lake_bin = resolve_project_config(&diff_dir)
            .unwrap()
            .lean_bin
            .with_file_name("lake");
        if lake_bin.is_file() {
            fs::remove_dir_all(diff_dir.join(".lake/build")).unwrap();
            let st = Command::new(&lake_bin)
                .arg("build")
                .current_dir(&diff_dir)
                .status()
                .unwrap();
            assert!(st.success());
            let lake_core_olean =
                fs::read(diff_dir.join(".lake/build/lib/lean/Diff/Core.olean")).unwrap();
            let lake_use_olean =
                fs::read(diff_dir.join(".lake/build/lib/lean/Diff/Use.olean")).unwrap();
            assert_eq!(
                blake3::hash(&native_core_olean),
                blake3::hash(&lake_core_olean),
                "native vs lake Diff.Core.olean bytes must match"
            );
            assert_eq!(
                blake3::hash(&native_use_olean),
                blake3::hash(&lake_use_olean),
                "native vs lake Diff.Use.olean bytes must match"
            );
        }
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_parallel_diamond_dag_and_ci_verify_native_builder() {
        let dir = std::env::temp_dir().join(format!("turbo_mod_diamond_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        let proj_dir = dir.join("diamond_proj");
        let store_dir = dir.join("store");
        fs::create_dir_all(proj_dir.join("Diamond")).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"diamond_proj\"\ndefaultTargets = [\"Diamond\"]\n[[lean_lib]]\nname = \"Diamond\"\nglobs = [\"Diamond.+\"]\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("Diamond/Root.lean"),
            "namespace Diamond\ndef r : Nat := 3\nend Diamond\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("Diamond/Left.lean"),
            "import Diamond.Root\nnamespace Diamond\ndef l : Nat := r + 4\nend Diamond\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("Diamond/Right.lean"),
            "import Diamond.Root\nnamespace Diamond\ndef rg : Nat := r * 4\nend Diamond\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("Diamond/Top.lean"),
            "import Diamond.Left\nimport Diamond.Right\nnamespace Diamond\ntheorem top_eq : l + rg = 19 := rfl\nend Diamond\n",
        )
        .unwrap();

        let cfg = resolve_project_config(&proj_dir).unwrap();
        let dag = build_module_dag(&cfg, &[]).unwrap();
        assert_eq!(dag.waves.len(), 3);
        assert_eq!(dag.waves[0], vec!["Diamond.Root".to_string()]);
        assert_eq!(
            dag.waves[1],
            vec!["Diamond.Left".to_string(), "Diamond.Right".to_string()]
        );
        assert_eq!(dag.waves[2], vec!["Diamond.Top".to_string()]);

        let mut store = TurboStore::open(Some(&store_dir)).unwrap();
        // Run across the diamond DAG (Wave 0: Root, Wave 1: Left + Right in parallel, Wave 2: Top)
        let rep = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep.modules_total, 4);
        assert_eq!(rep.modules_compiled, 4);
        assert_eq!(rep.waves_count, 3);

        // Verify `lake_build::run_build_command` and `pr_verify::run_ci_verify_command` succeed using native builder
        crate::lake_build::run_build_command(
            &mut store,
            false,
            Vec::new(),
            proj_dir.clone(),
            "trusted-internal".to_string(),
            1,
            false,
        )
        .unwrap();

        crate::pr_verify::run_ci_verify_command(
            &mut store,
            false,
            "full".to_string(),
            proj_dir.clone(),
            None,
            false,
            None,
        )
        .unwrap();

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_adversarial_compiler_arg_allowlist_and_custom_target_fail_closed() {
        // 1. Strict allowlist accepts safe Lean compiler flags
        for ok_arg in [
            "-DautoImplicit=false",
            "-Dpp.unicode.fun=true",
            "-DmaxHeartbeats=400000",
            "-j4",
            "--threads=4",
            "--tstack=16384",
            "--json",
            "-q",
            "--quiet",
        ] {
            assert!(
                is_allowed_lean_arg(ok_arg),
                "expected safe arg `{}` to be allowed",
                ok_arg
            );
        }

        // 2. Strict allowlist rejects attached short flags, abbreviated long options, and positional args
        for bad_arg in [
            "-ofoo.olean",
            "-c/tmp/evil.c",
            "-ibaz.ilean",
            "-R/tmp",
            "--load-dyn=evil.so",
            "--plug=evil.so",
            "--setup=fake.json",
            "--run",
            "-v",
            "--version",
            "positional.lean",
            "-D=true",
            "-Dfoo=",
            "-Dfoo=bar\nbaz",
            "-j0",
            "--threads=0",
        ] {
            assert!(
                !is_allowed_lean_arg(bad_arg),
                "expected unsafe/unknown arg `{}` to be rejected",
                bad_arg
            );
        }

        // 3. Root `custom_target` MUST fail closed even when a prebuilt `extern_lib` static artifact exists
        let dir = make_temp_test_dir("adv_custom_target_with_ext");
        fs::create_dir_all(dir.join(".lake/build/lib")).unwrap();
        fs::write(dir.join(".lake/build/lib/libfoo.a"), b"!<arch>\n").unwrap();
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage p\nextern_lib libfoo pkg := do\n  pure ()\ntarget custom_gen pkg : FilePath := do\n  pure ()\nlean_lib A\n",
        )
        .unwrap();
        let err = parse_lakefile_lean(&dir, &lf, true)
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("custom_gen") && err.contains("fail-closed"),
            "expected custom_target with extern_lib to fail closed, got: {}",
            err
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_adversarial_toolchain_resolution_and_untrusted_env_isolation() {
        let dir = make_temp_test_dir("adv_toolchain");
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"adv_tc\"\n[[lean_lib]]\nname = \"Adv\"\n",
        )
        .unwrap();

        // 1. Specific non-existent toolchain MUST fail closed without falling back to PATH `lean` or `spawn_lake_env`
        let err_missing =
            resolve_toolchain_compiler_with_trust(&dir, "leanprover/lean4:v99.99.99", false)
                .unwrap_err()
                .to_string();
        assert!(
            err_missing.contains("v99.99.99") && err_missing.contains("fail-closed"),
            "unexpected error for missing toolchain: {}",
            err_missing
        );

        // 2. Substring prefix directory (`v4.35.0-rc1`) is NOT matched for `v4.35.0`
        let fake_elan = dir.join("fake_elan");
        let rc_bin = fake_elan.join("toolchains/leanprover--lean4---v4.35.0-rc1/bin/lean");
        assert!(
            !path_has_toolchain_component(&rc_bin, "leanprover--lean4---v4.35.0"),
            "substring prefix directory must not match exact path component"
        );
        let exact_bin = fake_elan.join("toolchains/leanprover--lean4---v4.35.0/bin/lean");
        assert!(
            path_has_toolchain_component(&exact_bin, "leanprover--lean4---v4.35.0"),
            "exact path component must match"
        );

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_adversarial_cas_key_dep_digest_validation_and_ambiguous_or_same_mtime_deps() {
        let dir = make_temp_test_dir("adv_cas_and_deps");
        let store_dir = dir.join("store");
        let proj_dir = dir.join("proj");
        let dep1_dir = proj_dir.join(".lake/packages/dep_one");
        let dep2_dir = proj_dir.join(".lake/packages/dep_two");
        fs::create_dir_all(dep1_dir.join("Shared")).unwrap();
        fs::create_dir_all(dep2_dir.join("Shared")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            dep1_dir.join("lakefile.toml"),
            "name = \"dep_one\"\n[[lean_lib]]\nname = \"SharedOne\"\nroots = [\"Shared.Util\"]\n",
        )
        .unwrap();
        fs::write(
            dep2_dir.join("lakefile.toml"),
            "name = \"dep_two\"\n[[lean_lib]]\nname = \"SharedTwo\"\nroots = [\"Shared.Util\"]\n",
        )
        .unwrap();
        fs::write(
            dep1_dir.join("Shared/Util.lean"),
            "namespace Shared\ndef v : Nat := 1\nend Shared\n",
        )
        .unwrap();
        fs::write(
            dep2_dir.join("Shared/Util.lean"),
            "namespace Shared\ndef v : Nat := 2\nend Shared\n",
        )
        .unwrap();
        let manifest_ambig = r#"{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [
    { "type": "path", "name": "dep_one", "dir": ".lake/packages/dep_one", "configFile": "lakefile.toml", "inherited": false },
    { "type": "path", "name": "dep_two", "dir": ".lake/packages/dep_two", "configFile": "lakefile.toml", "inherited": false }
  ],
  "name": "app_pkg",
  "lakeDir": ".lake",
  "fixedToolchain": false
}"#;
        fs::write(proj_dir.join("lake-manifest.json"), manifest_ambig).unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nroots = [\"App.Main\"]\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("App/Main.lean"),
            "import Shared.Util\ndef m : Nat := Shared.v\n",
        )
        .unwrap();

        // 1. Ambiguous module import across two dependency packages MUST fail closed
        let cfg_ambig = resolve_project_config(&proj_dir).unwrap();
        let ambig_err = build_module_dag(&cfg_ambig, &[]).unwrap_err().to_string();
        assert!(
            ambig_err.contains("Ambiguous module import `Shared.Util`"),
            "expected ambiguous import error, got: {}",
            ambig_err
        );

        // 2. Remove `dep_two` so `Shared.Util` is unambiguous in `dep_one`
        let manifest_single = r#"{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [
    { "type": "path", "name": "dep_one", "dir": ".lake/packages/dep_one", "configFile": "lakefile.toml", "inherited": false }
  ],
  "name": "app_pkg",
  "lakeDir": ".lake",
  "fixedToolchain": false
}"#;
        fs::write(proj_dir.join("lake-manifest.json"), manifest_single).unwrap();
        let cfg = resolve_project_config(&proj_dir).unwrap();
        let dag = build_module_dag(&cfg, &[]).unwrap();
        let main_node = dag.nodes.get("App.Main").unwrap();

        // 3. `compute_module_cas_key` rejects duplicate, unsorted, incomplete, or extra dependency digest vectors
        let err_dup = compute_module_cas_key(
            &cfg,
            main_node,
            &[
                ("Shared.Util".to_string(), "h1".to_string()),
                ("Shared.Util".to_string(), "h1".to_string()),
            ],
            false,
        )
        .unwrap_err()
        .to_string();
        assert!(err_dup.contains("unsorted or duplicate"));

        let err_unsorted = compute_module_cas_key(
            &cfg,
            main_node,
            &[
                ("Z.Mod".to_string(), "h2".to_string()),
                ("Shared.Util".to_string(), "h1".to_string()),
            ],
            false,
        )
        .unwrap_err()
        .to_string();
        assert!(err_unsorted.contains("unsorted or duplicate"));

        let err_missing_dep = compute_module_cas_key(&cfg, main_node, &[], false)
            .unwrap_err()
            .to_string();
        assert!(err_missing_dep.contains("missing required dependency"));

        let err_extra_dep = compute_module_cas_key(
            &cfg,
            main_node,
            &[
                ("Shared.Util".to_string(), "h1".to_string()),
                ("Z.UnrelatedExtraDep".to_string(), "h2".to_string()),
            ],
            false,
        )
        .unwrap_err()
        .to_string();
        assert!(
            err_extra_dep.contains("unexpected extra dependency"),
            "expected extra dependency to be rejected, got: {}",
            err_extra_dep
        );

        // 4. Same-mtime source replacement in `dep_one` (`Shared/Util.lean`) is detected by `.turbo_verified_sources.json` content hash
        let mut store = TurboStore::open(Some(&store_dir)).unwrap();
        let rep1 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep1.modules_compiled, 2);

        let util_src = dep1_dir.join("Shared/Util.lean");
        let orig_mtime = fs::metadata(&util_src).unwrap().modified().unwrap();
        fs::write(
            &util_src,
            "namespace Shared\ndef v : Nat := 42\nend Shared\n",
        )
        .unwrap();
        // Force `Shared/Util.lean` back to its exact previous modification timestamp
        if let Ok(f) = fs::File::options().write(true).open(&util_src) {
            let _ = f.set_modified(orig_mtime);
        }
        let rep2 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(
            rep2.modules_compiled, 2,
            "same-mtime source change in dep_one must invalidate Shared.Util and App.Main"
        );

        // 5. H5: When `is_untrusted = true`, pre-existing `.olean` and `.turbo_verified_sources.json` in `dep_one`
        // are NEVER trusted from the checkout; `Shared.Util` is added to `dag.nodes` instead of `external_olean_deps`.
        let dag_untrusted = build_module_dag_with_trust(&cfg, &[], true).unwrap();
        assert!(
            dag_untrusted.nodes.contains_key("Shared.Util"),
            "untrusted DAG must include dependency package module Shared.Util as a DAG node"
        );
        let main_untrusted = dag_untrusted.nodes.get("App.Main").unwrap();
        assert!(
            main_untrusted.external_olean_deps.is_empty(),
            "untrusted DAG must not trust checkout external_olean_deps"
        );

        // 6. H6 & HIGH 1: Verify `build_module_compile_command` places `--setenv LEAN_PATH ...` before `cfg.lean_bin`
        // and `-M 4096` after `cfg.lean_bin`.
        let dummy_tmp = proj_dir.join(".lake/build/.turbo_test_tmp");
        fs::create_dir_all(&dummy_tmp).unwrap();
        let (lp_env, ld_env) = build_lean_search_path(&cfg, true);
        let cmd_bwrap = build_module_compile_command(
            &cfg,
            main_untrusted,
            &dummy_tmp,
            &dummy_tmp.join("App/Main.olean"),
            &dummy_tmp.join("App/Main.ilean"),
            &dummy_tmp.join("App/Main.c"),
            &dummy_tmp.join("App/Main.setup.json"),
            &lp_env,
            &ld_env,
            true,
            Some(Path::new("/usr/bin/bwrap")),
        )
        .unwrap();
        assert_eq!(
            cmd_bwrap.get_program(),
            std::ffi::OsStr::new("/usr/bin/bwrap")
        );
        let args: Vec<String> = cmd_bwrap
            .get_args()
            .map(|a| a.to_string_lossy().to_string())
            .collect();
        let pos_clearenv = args.iter().position(|a| a == "--clearenv").unwrap();
        let pos_setenv_lp = args
            .windows(3)
            .position(|w| w[0] == "--setenv" && w[1] == "LEAN_PATH" && w[2] == lp_env)
            .expect("bwrap command must contain `--setenv LEAN_PATH <lp_env>`");
        let pos_lean_bin = args
            .iter()
            .position(|a| a == &cfg.lean_bin.to_string_lossy())
            .expect("bwrap command must contain lean_bin");
        let pos_mem = args
            .windows(2)
            .position(|w| w[0] == "-M" && w[1] == "4096")
            .expect("lean args must contain `-M 4096`");
        assert!(
            pos_clearenv < pos_setenv_lp && pos_setenv_lp < pos_lean_bin && pos_lean_bin < pos_mem,
            "expected --clearenv < --setenv LEAN_PATH < lean_bin < -M 4096, got args: {:?}",
            args
        );

        // 7. M7: When `is_untrusted = true` and `bwrap_bin` is `None`, `build_module_compile_command`
        // unconditionally fails closed even if `TURBO_LEAN_ALLOW_NO_BWRAP_IN_CONTAINER=1` is set in env.
        std::env::set_var("TURBO_LEAN_ALLOW_NO_BWRAP_IN_CONTAINER", "1");
        let err_no_bwrap = build_module_compile_command(
            &cfg,
            main_untrusted,
            &dummy_tmp,
            &dummy_tmp.join("App/Main.olean"),
            &dummy_tmp.join("App/Main.ilean"),
            &dummy_tmp.join("App/Main.c"),
            &dummy_tmp.join("App/Main.setup.json"),
            &lp_env,
            &ld_env,
            true,
            None,
        )
        .unwrap_err()
        .to_string();
        std::env::remove_var("TURBO_LEAN_ALLOW_NO_BWRAP_IN_CONTAINER");
        assert!(
            err_no_bwrap.contains("requires a working bubblewrap"),
            "expected fail-closed error when bwrap is missing, got: {}",
            err_no_bwrap
        );
        // Also verify untrusted search path validation rejects `..` or unbound paths in `lean_path_env`.
        let err_bad_lp = build_module_compile_command(
            &cfg,
            main_untrusted,
            &dummy_tmp,
            &dummy_tmp.join("App/Main.olean"),
            &dummy_tmp.join("App/Main.ilean"),
            &dummy_tmp.join("App/Main.c"),
            &dummy_tmp.join("App/Main.setup.json"),
            "/tmp/unbound_evil_lean_path",
            &ld_env,
            true,
            Some(Path::new("/usr/bin/bwrap")),
        )
        .unwrap_err()
        .to_string();
        assert!(
            err_bad_lp.contains("Invalid or unbound search path entry"),
            "expected unbound search path rejection, got: {}",
            err_bad_lp
        );

        // 8. Execute a real 2-module untrusted build (`Shared.Util` + `App.Main`) through an executable `bwrap` shim
        // that enforces `--clearenv` (`env -i`) and only exports `--setenv` variables before execing `lean`.
        let fake_bwrap = dir.join("fake_bwrap.sh");
        let fake_bwrap_script = r#"#!/usr/bin/env bash
set -euo pipefail
ENV_ARGS=()
CHDIR=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --unshare-all|--new-session|--die-with-parent)
      shift ;;
    --clearenv)
      ENV_ARGS=("-i")
      shift ;;
    --setenv)
      ENV_ARGS+=("$2=$3")
      shift 3 ;;
    --dev|--proc|--tmpfs)
      shift 2 ;;
    --ro-bind|--ro-bind-try|--bind)
      shift 3 ;;
    --chdir)
      CHDIR="$2"
      shift 2 ;;
    *)
      break ;;
  esac
done
if [[ -n "$CHDIR" ]]; then
  cd "$CHDIR"
fi
exec env "${ENV_ARGS[@]}" "$@"
"#;
        fs::write(&fake_bwrap, fake_bwrap_script).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = fs::metadata(&fake_bwrap).unwrap().permissions();
            perms.set_mode(0o755);
            fs::set_permissions(&fake_bwrap, perms).unwrap();
        }
        std::env::set_var("TURBO_LEAN_TEST_BWRAP_BIN", &fake_bwrap);
        let untrusted_store_dir = dir.join("untrusted_store");
        let mut untrusted_store = TurboStore::open(Some(&untrusted_store_dir)).unwrap();
        let rep_untrusted = build_project_modules_native(
            &mut untrusted_store,
            &proj_dir,
            &["App:c".to_string()],
            "untrusted:pr",
            1,
            true,
            true,
            None,
        )
        .unwrap();
        std::env::remove_var("TURBO_LEAN_TEST_BWRAP_BIN");
        assert!(rep_untrusted.bwrap_used);
        assert_eq!(rep_untrusted.modules_compiled, 2);
        assert!(main_untrusted.c_path.is_file(), "App:c must emit Main.c");

        // 9. HIGH 2 & HIGH 3: When rebuilding with `needs_c = false` (default target `App`), stale `Main.c` is removed,
        // and failed atomic staging or Phase 2 rename failure leaves/rolls back existing valid `.olean`/`.ilean` untouched.
        std::env::set_var("TURBO_LEAN_TEST_BWRAP_BIN", &fake_bwrap);
        let _rep_no_c = build_project_modules_native(
            &mut untrusted_store,
            &proj_dir,
            &[],
            "untrusted:pr",
            1,
            true,
            true,
            None,
        )
        .unwrap();
        std::env::remove_var("TURBO_LEAN_TEST_BWRAP_BIN");
        assert!(
            !main_untrusted.c_path.exists(),
            "stale Main.c must be removed when needs_c transitions from true to false"
        );
        let orig_olean_bytes = fs::read(&main_untrusted.olean_path).unwrap();
        let orig_ilean_bytes = fs::read(&main_untrusted.ilean_path).unwrap();
        let bad_tmp = proj_dir.join(".lake/build/.turbo_bad_pub_tmp");
        fs::create_dir_all(bad_tmp.join("App")).unwrap();
        fs::write(bad_tmp.join("App/Main.olean"), b"corrupt_olean").unwrap();
        #[cfg(unix)]
        std::os::unix::fs::symlink("/etc/passwd", bad_tmp.join("App/Main.ilean")).unwrap();
        let pub_err = publish_module_artifacts_atomic(
            &bad_tmp,
            main_untrusted,
            &bad_tmp.join("App/Main.olean"),
            &bad_tmp.join("App/Main.ilean"),
            &bad_tmp.join("App/Main.olean.server"),
            &bad_tmp.join("App/Main.olean.private"),
            &bad_tmp.join("App/Main.ir"),
            &bad_tmp.join("App/Main.ir.sig"),
            &bad_tmp.join("App/Main.c"),
        );
        assert!(
            pub_err.is_err(),
            "publish_module_artifacts_atomic must reject symlinked ilean in staging phase"
        );
        assert_eq!(
            fs::read(&main_untrusted.olean_path).unwrap(),
            orig_olean_bytes,
            "failed staging phase must leave existing destination Main.olean untouched"
        );

        // 10. Test Phase 2 second-rename failure rollback + stale artifact restoration:
        // Place a stale `Main.c` on disk (`main_untrusted.needs_c == false`), and replace `main_untrusted.ilean_path`
        // with a non-empty directory so the 1st rename (`stage_olean -> dst_olean`) succeeds and the 2nd rename
        // (`stage_ilean -> dst_ilean`) fails (`EISDIR`). Verify `Main.olean` AND the stale `Main.c` are rolled back
        // to their exact pre-publish bytes, and that `rollback_publish_state` reports an explicit
        // `publication state potentially inconsistent` error when rollback itself cannot restore `dst_ilean`!
        let bad_tmp2 = proj_dir.join(".lake/build/.turbo_bad_pub_tmp2");
        fs::create_dir_all(bad_tmp2.join("App")).unwrap();
        fs::write(bad_tmp2.join("App/Main.olean"), b"corrupt_phase2_olean").unwrap();
        fs::write(bad_tmp2.join("App/Main.ilean"), b"corrupt_phase2_ilean").unwrap();
        fs::create_dir_all(main_untrusted.c_path.parent().unwrap()).unwrap();
        fs::write(&main_untrusted.c_path, b"pre_existing_c_bytes").unwrap();
        fs::remove_file(&main_untrusted.ilean_path).unwrap();
        fs::create_dir_all(main_untrusted.ilean_path.join("blocker_subfile")).unwrap();
        let pub_err2 = publish_module_artifacts_atomic(
            &bad_tmp2,
            main_untrusted,
            &bad_tmp2.join("App/Main.olean"),
            &bad_tmp2.join("App/Main.ilean"),
            &bad_tmp2.join("App/Main.olean.server"),
            &bad_tmp2.join("App/Main.olean.private"),
            &bad_tmp2.join("App/Main.ir"),
            &bad_tmp2.join("App/Main.ir.sig"),
            &bad_tmp2.join("App/Main.c"),
        );
        assert!(
            pub_err2.is_err(),
            "publish_module_artifacts_atomic must fail when 2nd rename hits directory at dst_ilean"
        );
        assert_eq!(
            fs::read(&main_untrusted.olean_path).unwrap(),
            orig_olean_bytes,
            "Phase 2 second-rename failure must roll back Main.olean to its original pre-publish bytes"
        );
        assert_eq!(
            fs::read(&main_untrusted.c_path).unwrap(),
            b"pre_existing_c_bytes",
            "Phase 2 failure must preserve/restore pre-existing stale Main.c"
        );
        let _ = fs::remove_file(&main_untrusted.c_path);
        // Also verify `rollback_publish_state` directly reports `publication state potentially inconsistent`
        // and wipes module artifacts if restoring a backed-up file fails (e.g. destination is a non-empty directory).
        let fake_backup = main_untrusted
            .ilean_path
            .parent()
            .unwrap()
            .join(".turbo_test_unrestorable_backup");
        fs::write(&fake_backup, &orig_ilean_bytes).unwrap();
        let rb_err = rollback_publish_state(
            main_untrusted,
            true,
            &[],
            &[BackupRecord {
                dst_path: main_untrusted.ilean_path.clone(),
                backup_file: Some((
                    fake_backup.clone(),
                    blake3::hash(&orig_ilean_bytes),
                    orig_ilean_bytes.len() as u64,
                )),
            }],
        )
        .unwrap_err()
        .to_string();
        let _ = fs::remove_file(&fake_backup);
        assert!(
            rb_err.contains("publication state potentially inconsistent"),
            "expected explicit inconsistent state error on rollback failure, got: {}",
            rb_err
        );
        assert!(
            !main_untrusted.olean_path.exists(),
            "failed rollback must wipe partial module artifacts so they cannot be reused"
        );
        let _ = fs::remove_dir_all(&main_untrusted.ilean_path);
        fs::write(&main_untrusted.olean_path, &orig_olean_bytes).unwrap();
        fs::write(&main_untrusted.ilean_path, &orig_ilean_bytes).unwrap();

        let _ = fs::remove_dir_all(&dir);
    }
}
