use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::ffi::OsStr;
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};
use std::str::FromStr;

pub const KERNEL_ENGINE_ENV: &str = "TURBO_LEAN_KERNEL_ENGINE";
pub const KERNEL_ENGINE_FROM_CONFIG_ENV: &str = "TURBO_LEAN_KERNEL_ENGINE_FROM_CONFIG";
pub const CON_LECHE_BIN_ENV: &str = "TURBO_CON_LECHE_BIN";
pub const PINNED_CON_LECHE_REV: &str = "501589f5680d9599dee1bcef30a420bc8924c490";
pub const PINNED_CON_LECHE_TOOLCHAIN: &str = "leanprover/lean4:v4.35.0";
pub const BRIDGE_CON_LECHE_BIN_REL: &str =
    "verification/con-leche-bridge/.lake/packages/con-leche/.lake/build/bin/con-leche";
pub const DEFAULT_MAX_CON_LECHE_JOBS: usize = 8;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KernelEngineSelection {
    Auto,
    Standard,
    ConLeche,
    Both,
}

impl KernelEngineSelection {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::Standard => "standard",
            Self::ConLeche => "con-leche",
            Self::Both => "both",
        }
    }

    #[inline(always)]
    pub const fn to_c_abi_tag(self) -> u8 {
        match self {
            Self::Auto => 0,
            Self::Standard => 1,
            Self::ConLeche => 2,
            Self::Both => 3,
        }
    }

    pub fn parse_selection(raw: &str) -> Result<Self> {
        let trimmed = raw.trim();
        if trimmed.eq_ignore_ascii_case("auto") {
            Ok(Self::Auto)
        } else if trimmed.eq_ignore_ascii_case("standard") {
            Ok(Self::Standard)
        } else if trimmed.eq_ignore_ascii_case("con-leche")
            || trimmed.eq_ignore_ascii_case("con_leche")
        {
            Ok(Self::ConLeche)
        } else if trimmed.eq_ignore_ascii_case("both") {
            Ok(Self::Both)
        } else {
            anyhow::bail!(
                "Invalid kernel engine `{}`: expected one of `auto`, `standard`, `con-leche`, or `both`",
                trimmed
            );
        }
    }
}

impl fmt::Display for KernelEngineSelection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for KernelEngineSelection {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self> {
        Self::parse_selection(s)
    }
}

impl Serialize for KernelEngineSelection {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

impl<'de> Deserialize<'de> for KernelEngineSelection {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Self::parse_selection(&s).map_err(serde::de::Error::custom)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResolvedKernelEngine {
    Standard,
    ConLeche,
    Both,
}

impl ResolvedKernelEngine {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Standard => "standard",
            Self::ConLeche => "con-leche",
            Self::Both => "both",
        }
    }

    #[inline(always)]
    pub const fn from_c_abi_tag(tag: u8) -> Option<Self> {
        match tag {
            1 => Some(Self::Standard),
            2 => Some(Self::ConLeche),
            3 => Some(Self::Both),
            _ => None,
        }
    }

    pub fn parse_resolved(raw: &str) -> Result<Self> {
        let trimmed = raw.trim();
        match trimmed {
            "standard" => Ok(Self::Standard),
            "con-leche" => Ok(Self::ConLeche),
            "both" => Ok(Self::Both),
            _ => anyhow::bail!(
                "Invalid resolved kernel_engine `{}`: expected one of `standard`, `con-leche`, or `both`",
                trimmed
            ),
        }
    }
}

impl fmt::Display for ResolvedKernelEngine {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl Serialize for ResolvedKernelEngine {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

impl<'de> Deserialize<'de> for ResolvedKernelEngine {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Self::parse_resolved(&s).map_err(serde::de::Error::custom)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct KernelProvenance {
    pub requested_engine: KernelEngineSelection,
    pub kernel_engine: ResolvedKernelEngine,
    pub lean_toolchain: String,
    pub con_leche_rev: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub fallback_reason: Option<String>,
}

impl KernelProvenance {
    pub fn insert_json_fields(&self, val: &mut serde_json::Value) {
        if let Some(obj) = val.as_object_mut() {
            obj.insert(
                "kernel_engine".to_string(),
                serde_json::json!(self.kernel_engine.as_str()),
            );
            obj.insert(
                "kernel_requested".to_string(),
                serde_json::json!(self.requested_engine.as_str()),
            );
            obj.insert(
                "lean_toolchain".to_string(),
                serde_json::json!(self.lean_toolchain),
            );
            obj.insert(
                "con_leche_rev".to_string(),
                serde_json::json!(self.con_leche_rev),
            );
        }
    }
}

pub fn normalize_lean_toolchain(raw_toolchain: &str) -> String {
    let trimmed = raw_toolchain.trim();
    if trimmed.is_empty() {
        "unknown".to_string()
    } else {
        trimmed.to_string()
    }
}

pub fn probe_con_leche_support(_lean_toolchain: &str) -> Option<String> {
    None
}

pub fn probe_con_leche_support_for_selection(
    requested: KernelEngineSelection,
    lean_toolchain: &str,
    workspace_root: Option<&Path>,
) -> Option<String> {
    if !matches!(
        requested,
        KernelEngineSelection::ConLeche | KernelEngineSelection::Both
    ) {
        return probe_con_leche_support(lean_toolchain);
    }
    if normalize_lean_toolchain(lean_toolchain) != PINNED_CON_LECHE_TOOLCHAIN {
        return None;
    }
    let bin = discover_con_leche_binary(workspace_root).ok()?;
    if let Some(proj) = workspace_root {
        let canon_proj = proj.canonicalize().ok()?;
        let checkout = canon_proj
            .ancestors()
            .find(|p| p.join(".git").exists())
            .unwrap_or(&canon_proj);
        if bin.starts_with(checkout) || bin.ancestors().any(|p| p.join(".git").exists()) {
            let expected_bridge_bin = checkout.join(BRIDGE_CON_LECHE_BIN_REL).canonicalize().ok();
            if expected_bridge_bin.as_ref() != Some(&bin) {
                return None;
            }
        }
    }
    Some(PINNED_CON_LECHE_REV.to_string())
}

pub fn resolve_kernel_selection(
    cli_kernel: Option<&str>,
    caller_env_kernel: Option<&str>,
    config_kernel: Option<&str>,
) -> Result<KernelEngineSelection> {
    if let Some(cli) = cli_kernel {
        return KernelEngineSelection::parse_selection(cli);
    }
    if let Some(env_val) = caller_env_kernel.map(str::trim).filter(|s| !s.is_empty()) {
        return KernelEngineSelection::parse_selection(env_val);
    }
    if let Some(cfg_val) = config_kernel {
        return KernelEngineSelection::parse_selection(cfg_val);
    }
    Ok(KernelEngineSelection::Auto)
}

pub fn resolve_kernel_selection_from_env(
    cli_kernel: Option<&str>,
) -> Result<KernelEngineSelection> {
    if let Some(cli) = cli_kernel {
        return KernelEngineSelection::parse_selection(cli);
    }
    if let Ok(raw) = std::env::var(KERNEL_ENGINE_ENV) {
        let trimmed = raw.trim();
        if !trimmed.is_empty() {
            return KernelEngineSelection::parse_selection(trimmed);
        }
    }
    Ok(KernelEngineSelection::Auto)
}

pub fn resolve_kernel_engine(
    requested: KernelEngineSelection,
    lean_toolchain: &str,
) -> Result<KernelProvenance> {
    resolve_kernel_engine_in_workspace(requested, lean_toolchain, None)
}

pub fn resolve_kernel_engine_in_workspace(
    requested: KernelEngineSelection,
    lean_toolchain: &str,
    workspace_root: Option<&Path>,
) -> Result<KernelProvenance> {
    let lean_toolchain = normalize_lean_toolchain(lean_toolchain);
    let probed_con_leche_rev = workspace_root
        .and_then(|root| {
            probe_con_leche_support_for_selection(requested, &lean_toolchain, Some(root))
        })
        .or_else(|| probe_con_leche_support(&lean_toolchain));
    let routed_tag =
        crate::c_abi::route_kernel_engine(requested.to_c_abi_tag(), probed_con_leche_rev.is_some());
    let Some(kernel_engine) = ResolvedKernelEngine::from_c_abi_tag(routed_tag) else {
        anyhow::bail!(
            "Requested kernel engine `{}` cannot verify target toolchain `{}`: verified `con-leche` export/replay backend is not provisioned (fail-closed kernel gate)",
            requested.as_str(),
            lean_toolchain
        );
    };
    let (con_leche_rev, fallback_reason) = match kernel_engine {
        ResolvedKernelEngine::Standard => {
            let fallback = (requested == KernelEngineSelection::Auto).then(|| {
                format!(
                    "con-leche backend is not provisioned or supported for toolchain `{}`; using standard Lean kernel",
                    lean_toolchain
                )
            });
            (None, fallback)
        }
        ResolvedKernelEngine::ConLeche | ResolvedKernelEngine::Both => {
            let rev = probed_con_leche_rev.ok_or_else(|| {
                anyhow::anyhow!(
                    "Kernel routing invariant violated: `{}` resolved without `con_leche_rev`",
                    kernel_engine.as_str()
                )
            })?;
            (Some(rev), None)
        }
    };
    Ok(KernelProvenance {
        requested_engine: requested,
        kernel_engine,
        lean_toolchain,
        con_leche_rev,
        fallback_reason,
    })
}

pub fn resolve_project_kernel_provenance(
    project_dir: &Path,
    cli_kernel: Option<&str>,
) -> Result<KernelProvenance> {
    let requested = resolve_kernel_selection_from_env(cli_kernel)?;
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let tc = crate::lake_build::detect_toolchain(&canon_dir);
    resolve_kernel_engine(requested, &tc)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ConLecheVerdict {
    Accepted,
    Rejected,
    Declined,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConLecheRunReport {
    pub verdict: ConLecheVerdict,
    pub exit_code: i32,
    pub binary_path: PathBuf,
    pub con_leche_rev: String,
    pub jobs: usize,
    pub accepted_declarations: Option<u64>,
    pub stdout: String,
    pub stderr: String,
}

pub fn bounded_con_leche_jobs(requested: Option<usize>) -> usize {
    match requested {
        Some(n) => n.clamp(1, DEFAULT_MAX_CON_LECHE_JOBS),
        None => std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(2)
            .clamp(1, DEFAULT_MAX_CON_LECHE_JOBS),
    }
}

fn is_executable_file(path: &Path) -> bool {
    if !path.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        path.metadata()
            .map(|m| m.permissions().mode() & 0o111 != 0)
            .unwrap_or(false)
    }
    #[cfg(not(unix))]
    {
        true
    }
}

pub fn discover_con_leche_binary(workspace_root: Option<&Path>) -> Result<PathBuf> {
    if let Ok(raw) = std::env::var(CON_LECHE_BIN_ENV) {
        let trimmed = raw.trim();
        if !trimmed.is_empty() {
            let p = PathBuf::from(trimmed);
            if is_executable_file(&p) {
                return Ok(p.canonicalize().unwrap_or(p));
            }
            anyhow::bail!(
                "`{CON_LECHE_BIN_ENV}` points to missing or non-executable `con-leche` binary: `{}`",
                p.display()
            );
        }
    }

    let mut roots: Vec<PathBuf> = Vec::new();
    if let Some(root) = workspace_root {
        roots.push(root.to_path_buf());
    }
    if let Ok(cwd) = std::env::current_dir() {
        let mut cur: Option<&Path> = Some(cwd.as_path());
        while let Some(dir) = cur {
            roots.push(dir.to_path_buf());
            cur = dir.parent();
        }
    }
    if let Ok(exe) = std::env::current_exe() {
        let mut cur = exe.parent();
        while let Some(dir) = cur {
            roots.push(dir.to_path_buf());
            cur = dir.parent();
        }
    }

    for root in roots {
        let candidate = root.join(BRIDGE_CON_LECHE_BIN_REL);
        if is_executable_file(&candidate) {
            return Ok(candidate.canonicalize().unwrap_or(candidate));
        }
    }

    anyhow::bail!(
        "Verified `con-leche` binary not found (expected `{CON_LECHE_BIN_ENV}` or `{BRIDGE_CON_LECHE_BIN_REL}` built at rev `{PINNED_CON_LECHE_REV}`)"
    )
}

fn parse_accepted_declarations(stdout: &str) -> Option<u64> {
    for line in stdout.lines().rev() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("con-leche: accepted ") {
            let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
            if let Ok(n) = digits.parse::<u64>() {
                return Some(n);
            }
        }
    }
    None
}

fn resolve_scratch_tmpdir_with_env(
    explicit: Option<&Path>,
    env_tmpdir: Option<&OsStr>,
) -> Option<PathBuf> {
    if let Some(p) = explicit {
        return Some(p.to_path_buf());
    }
    let os_val = env_tmpdir?;
    if let Some(s) = os_val.to_str() {
        let trimmed = s.trim();
        if !trimmed.is_empty() {
            return Some(PathBuf::from(trimmed));
        }
        return None;
    }
    if !os_val.is_empty() {
        return Some(PathBuf::from(os_val));
    }
    None
}

fn resolve_scratch_tmpdir(explicit_tmpdir: Option<&Path>) -> Option<PathBuf> {
    resolve_scratch_tmpdir_with_env(explicit_tmpdir, std::env::var_os("TMPDIR").as_deref())
}

fn classify_con_leche_status(
    status: ExitStatus,
    binary_path: PathBuf,
    jobs: usize,
    stdout: String,
    stderr: String,
) -> Result<ConLecheRunReport> {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(sig) = status.signal() {
            anyhow::bail!(
                "`con-leche` terminated by signal {sig} (fail-closed kernel abort; stderr: {})",
                stderr.trim()
            );
        }
    }
    let Some(code) = status.code() else {
        anyhow::bail!(
            "`con-leche` terminated without exit code (fail-closed kernel abort; stderr: {})",
            stderr.trim()
        );
    };
    let verdict = match code {
        0 => ConLecheVerdict::Accepted,
        1 => ConLecheVerdict::Rejected,
        2 => ConLecheVerdict::Declined,
        3 => anyhow::bail!(
            "`con-leche` failed with usage/malformed/internal error (exit 3): {}",
            stderr.trim()
        ),
        other => anyhow::bail!(
            "`con-leche` exited with unexpected status {other} (fail-closed): {}",
            stderr.trim()
        ),
    };
    let accepted_declarations = if verdict == ConLecheVerdict::Accepted {
        parse_accepted_declarations(&stdout)
    } else {
        None
    };
    Ok(ConLecheRunReport {
        verdict,
        exit_code: code,
        binary_path,
        con_leche_rev: PINNED_CON_LECHE_REV.to_string(),
        jobs,
        accepted_declarations,
        stdout,
        stderr,
    })
}

pub fn verify_olean_modules_with_con_leche(
    binary_path: &Path,
    search_paths: &[PathBuf],
    root_modules: &[String],
    constants: &[String],
    requested_jobs: Option<usize>,
    scratch_tmpdir: Option<&Path>,
) -> Result<ConLecheRunReport> {
    if !is_executable_file(binary_path) {
        anyhow::bail!(
            "`con-leche` binary is missing or not executable: `{}`",
            binary_path.display()
        );
    }
    if search_paths.is_empty() {
        anyhow::bail!("`con-leche --olean` requires at least one `--search-path` directory");
    }
    if root_modules.is_empty() {
        anyhow::bail!("`con-leche --olean` requires at least one root module name");
    }
    for m in root_modules {
        let trimmed = m.trim();
        if trimmed.is_empty() || trimmed.starts_with('-') {
            anyhow::bail!("Invalid `con-leche` root module name `{m}`");
        }
    }
    let jobs = bounded_con_leche_jobs(requested_jobs);
    let joined_sp = std::env::join_paths(search_paths)
        .context("Failed to join `--search-path` entries for `con-leche`")?
        .into_string()
        .map_err(|_| anyhow::anyhow!("Non-UTF-8 `--search-path` entry passed to `con-leche`"))?;
    let tmpdir = resolve_scratch_tmpdir(scratch_tmpdir);

    let mut cmd = Command::new(binary_path);
    if let Some(ref td) = tmpdir {
        cmd.env("TMPDIR", td);
    }
    cmd.arg("--verified")
        .arg(format!("--jobs={jobs}"))
        .arg("--olean")
        .arg(format!("--search-path={joined_sp}"));
    for c in constants {
        let trimmed = c.trim();
        if trimmed.is_empty() {
            anyhow::bail!("Empty `--constant` name passed to `con-leche`");
        }
        cmd.arg(format!("--constant={trimmed}"));
    }
    cmd.arg("--");
    for m in root_modules {
        cmd.arg(m.trim());
    }

    let out = cmd.output().with_context(|| {
        format!(
            "Failed to spawn `con-leche` binary `{}`",
            binary_path.display()
        )
    })?;
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    classify_con_leche_status(out.status, binary_path.to_path_buf(), jobs, stdout, stderr)
}

pub fn verify_ndjson_with_con_leche(
    binary_path: &Path,
    ndjson_file: &Path,
    requested_jobs: Option<usize>,
    scratch_tmpdir: Option<&Path>,
) -> Result<ConLecheRunReport> {
    if !is_executable_file(binary_path) {
        anyhow::bail!(
            "`con-leche` binary is missing or not executable: `{}`",
            binary_path.display()
        );
    }
    if !ndjson_file.is_file() {
        anyhow::bail!(
            "`con-leche` NDJSON stream file does not exist: `{}`",
            ndjson_file.display()
        );
    }
    let jobs = bounded_con_leche_jobs(requested_jobs);
    let tmpdir = resolve_scratch_tmpdir(scratch_tmpdir);

    let mut cmd = Command::new(binary_path);
    if let Some(ref td) = tmpdir {
        cmd.env("TMPDIR", td);
    }
    let out = cmd
        .arg("--verified")
        .arg(format!("--jobs={jobs}"))
        .arg("--")
        .arg(ndjson_file)
        .output()
        .with_context(|| {
            format!(
                "Failed to spawn `con-leche` binary `{}`",
                binary_path.display()
            )
        })?;
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    classify_con_leche_status(out.status, binary_path.to_path_buf(), jobs, stdout, stderr)
}


/// A single compiled-import compiler-simplification (`@[csimp]` / `local csimp`) observation,
/// read from a module's public signature extension entries.
///
/// `scope` is `None` for a global `@[csimp]` entry and `Some(namespace)` for a `local csimp`
/// replacement scoped to a namespace, so a scoped replacement that leaks into the compiled cone is
/// never confused with its global twin.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct CompiledCsimpObservation {
    pub theorem: String,
    pub from: String,
    pub to: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub scope: Option<String>,
}

/// The `csimp` posture of one compiled module: the modules it imports (as observed in its public
/// signature) plus the replacement entries its own module data exports.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledModuleCsimpObservation {
    #[serde(default)]
    pub imports: Vec<String>,
    #[serde(default)]
    pub entries: Vec<CompiledCsimpObservation>,
}

/// Deterministic transitive compiled-import `csimp` posture for one root module.
///
/// `modules` is the root plus every module reachable through the transitively exported import
/// closure, keyed by canonical module name, in `BTreeMap` order. `digest` is the canonical BLAKE3
/// posture digest produced by [`compute_transitive_csimp_posture_digest`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransitiveCsimpPosture {
    pub root: String,
    pub modules: BTreeMap<String, Vec<CompiledCsimpObservation>>,
    pub digest: String,
}

impl TransitiveCsimpPosture {
    /// Number of `@[csimp]` / `local csimp` replacement entries anywhere in the reachable closure.
    pub fn entry_count(&self) -> usize {
        self.modules.values().map(|e| e.len()).sum()
    }

    /// Every observation in the closure, as `(module, observation)`, in canonical order.
    pub fn flattened(&self) -> Vec<(String, CompiledCsimpObservation)> {
        self.modules
            .iter()
            .flat_map(|(m, entries)| entries.iter().map(move |e| (m.clone(), e.clone())))
            .collect()
    }
}

/// Walk the transitively exported compiled-import closure of `root_module` and collect each
/// module's `@[csimp]` / `local csimp` entries.
///
/// `read` resolves one module name to its public-signature observation, returning `Ok(None)` when
/// the module cannot be resolved. Resolution never trusts the caller's iteration order: modules are
/// visited in sorted order and the result is independent of the order `read` answers them in, so two
/// scanners over the same graph always produce the same posture and digest. Any unresolvable module
/// in the closure, including the root, fails closed.
pub fn scan_transitive_csimp_posture<F>(
    root_module: &str,
    mut read: F,
) -> Result<TransitiveCsimpPosture>
where
    F: FnMut(&str) -> Result<Option<CompiledModuleCsimpObservation>>,
{
    let root = root_module.trim();
    let _ = &mut read;
    anyhow::ensure!(
        !root.is_empty(),
        "Cannot scan the transitive compiled-import csimp posture of an empty root module name"
    );
    anyhow::bail!(
        "transitive compiled-import csimp scanning is not implemented yet (root `{root}`)"
    )
}

/// Canonical BLAKE3 digest of a root module's transitive `csimp` posture.
///
/// The digest is length-prefixed and content-bound: it covers the root module name and, for every
/// reachable module in sorted order, the module name and its sorted, de-duplicated
/// `(theorem, from, to, scope)` observations. Insertion order and duplicate observations therefore
/// never move the digest, while any change of name, scope, or replacement pair does.
pub fn compute_transitive_csimp_posture_digest(
    root_module: &str,
    modules: &BTreeMap<String, Vec<CompiledCsimpObservation>>,
) -> String {
    let _ = (root_module, modules);
    String::new()
}

/// Parse one `csimp_entries` string from a compiled module's public signature, e.g.
/// `global:slowGlob->fastGlob:slowGlob_eq` or `scoped:Ns:slowF->fastF:slowF_eq`.
///
/// Malformed entries fail closed instead of being silently dropped, so a truncated or spoofed
/// signature can never look like a clean posture.
pub fn parse_public_signature_csimp_entry(raw: &str) -> Result<CompiledCsimpObservation> {
    let _ = raw;
    anyhow::bail!("public-signature csimp entry parsing is not implemented yet")
}


#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn test_kernel_selection_parsing_and_canonical_aliases() {
        assert_eq!(
            KernelEngineSelection::parse_selection("auto").unwrap(),
            KernelEngineSelection::Auto
        );
        assert_eq!(
            KernelEngineSelection::parse_selection(" STANDARD ").unwrap(),
            KernelEngineSelection::Standard
        );
        assert_eq!(
            KernelEngineSelection::parse_selection("con-leche").unwrap(),
            KernelEngineSelection::ConLeche
        );
        assert_eq!(
            KernelEngineSelection::parse_selection("con_leche").unwrap(),
            KernelEngineSelection::ConLeche
        );
        assert_eq!(KernelEngineSelection::ConLeche.as_str(), "con-leche");
        assert_eq!(
            KernelEngineSelection::parse_selection("both").unwrap(),
            KernelEngineSelection::Both
        );
        let err = KernelEngineSelection::parse_selection("nanoda").unwrap_err();
        assert!(err
            .to_string()
            .contains("expected one of `auto`, `standard`, `con-leche`, or `both`"));
    }

    #[test]
    fn test_kernel_selection_precedence() {
        assert_eq!(
            resolve_kernel_selection(Some("standard"), Some("both"), Some("con-leche")).unwrap(),
            KernelEngineSelection::Standard
        );
        assert_eq!(
            resolve_kernel_selection(None, Some("con_leche"), Some("standard")).unwrap(),
            KernelEngineSelection::ConLeche
        );
        assert_eq!(
            resolve_kernel_selection(None, Some("   "), Some("standard")).unwrap(),
            KernelEngineSelection::Standard
        );
        assert_eq!(
            resolve_kernel_selection(None, None, None).unwrap(),
            KernelEngineSelection::Auto
        );
        assert!(resolve_kernel_selection(None, None, Some("bogus")).is_err());
    }

    #[test]
    fn test_resolve_kernel_engine_fail_closed_and_auto_fallback() {
        let std_prov = resolve_kernel_engine(
            KernelEngineSelection::Standard,
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        assert_eq!(std_prov.requested_engine, KernelEngineSelection::Standard);
        assert_eq!(std_prov.kernel_engine, ResolvedKernelEngine::Standard);
        assert_eq!(std_prov.lean_toolchain, "leanprover/lean4:v4.35.0");
        assert_eq!(std_prov.con_leche_rev, None);
        assert_eq!(std_prov.fallback_reason, None);

        let auto_prov = resolve_kernel_engine(KernelEngineSelection::Auto, "  ").unwrap();
        assert_eq!(auto_prov.requested_engine, KernelEngineSelection::Auto);
        assert_eq!(auto_prov.kernel_engine, ResolvedKernelEngine::Standard);
        assert_eq!(auto_prov.lean_toolchain, "unknown");
        assert_eq!(auto_prov.con_leche_rev, None);
        assert!(auto_prov.fallback_reason.is_some());

        for req in [KernelEngineSelection::ConLeche, KernelEngineSelection::Both] {
            let err = resolve_kernel_engine(req, "leanprover/lean4:v4.35.0").unwrap_err();
            let msg = err.to_string();
            assert!(msg.contains(req.as_str()), "unexpected error: {msg}");
            assert!(
                msg.contains("leanprover/lean4:v4.35.0"),
                "unexpected error: {msg}"
            );
        }
    }

    #[test]
    fn test_resolve_scratch_tmpdir_explicit_and_inherited_default() {
        let explicit = Path::new("/tmp/turbo-con-leche-explicit");
        assert_eq!(
            resolve_scratch_tmpdir(Some(explicit)),
            Some(explicit.to_path_buf())
        );
        assert_eq!(
            resolve_scratch_tmpdir_with_env(Some(explicit), Some(OsStr::new("/tmp/ignored"))),
            Some(explicit.to_path_buf())
        );
        assert_eq!(resolve_scratch_tmpdir_with_env(None, None), None);
        assert_eq!(
            resolve_scratch_tmpdir_with_env(None, Some(OsStr::new("   "))),
            None
        );
        assert_eq!(
            resolve_scratch_tmpdir_with_env(None, Some(OsStr::new(" /tmp/turbo-con-leche-env "))),
            Some(PathBuf::from("/tmp/turbo-con-leche-env"))
        );
    }
    fn module_obs(
        imports: &[&str],
        entries: &[(&str, &str, &str, Option<&str>)],
    ) -> CompiledModuleCsimpObservation {
        CompiledModuleCsimpObservation {
            imports: imports.iter().map(|m| (*m).to_string()).collect(),
            entries: entries
                .iter()
                .map(|(theorem, from, to, scope)| CompiledCsimpObservation {
                    theorem: (*theorem).to_string(),
                    from: (*from).to_string(),
                    to: (*to).to_string(),
                    scope: scope.map(|s| s.to_string()),
                })
                .collect(),
        }
    }

    /// `Root` reaches `DepGlobal` and `DepScoped` only transitively, through `MidA`/`MidB`;
    /// `MidA` also closes a cycle back to `Root`, and `Unreachable` carries a csimp entry that
    /// must never enter the posture.
    fn transitive_csimp_fixture() -> BTreeMap<String, CompiledModuleCsimpObservation> {
        let mut m = BTreeMap::new();
        m.insert("Root".to_string(), module_obs(&["MidA", "MidB"], &[]));
        m.insert(
            "MidA".to_string(),
            module_obs(&["DepGlobal", "Root"], &[]),
        );
        m.insert("MidB".to_string(), module_obs(&["DepScoped"], &[]));
        m.insert(
            "DepGlobal".to_string(),
            module_obs(
                &["ToolchainBase"],
                &[("slowGlob_eq", "slowGlob", "fastGlob", None)],
            ),
        );
        m.insert(
            "DepScoped".to_string(),
            module_obs(&[], &[("slowF_eq", "slowF", "fastF", Some("Ns"))]),
        );
        m.insert("ToolchainBase".to_string(), module_obs(&[], &[]));
        m.insert(
            "Unreachable".to_string(),
            module_obs(&[], &[("ghost_eq", "ghostSlow", "ghostFast", None)]),
        );
        m
    }

    #[test]
    fn test_transitive_csimp_scan_walks_import_closure_deterministically() {
        let fixture = transitive_csimp_fixture();
        let posture = scan_transitive_csimp_posture("Root", |m| Ok(fixture.get(m).cloned()))
            .expect("fixture closure resolves");
        assert_eq!(posture.root, "Root");
        assert_eq!(
            posture.modules.keys().cloned().collect::<Vec<_>>(),
            vec![
                "DepGlobal".to_string(),
                "DepScoped".to_string(),
                "MidA".to_string(),
                "MidB".to_string(),
                "Root".to_string(),
                "ToolchainBase".to_string(),
            ],
            "posture must cover the root plus every transitively reachable module, sorted"
        );
        assert!(
            !posture.modules.contains_key("Unreachable"),
            "an unreachable module is not part of the imported posture"
        );
        assert_eq!(
            posture.modules["DepGlobal"],
            vec![CompiledCsimpObservation {
                theorem: "slowGlob_eq".into(),
                from: "slowGlob".into(),
                to: "fastGlob".into(),
                scope: None,
            }],
            "depth-3 global `@[csimp]` entry must be attributed to its owning module"
        );
        assert_eq!(
            posture.modules["DepScoped"],
            vec![CompiledCsimpObservation {
                theorem: "slowF_eq".into(),
                from: "slowF".into(),
                to: "fastF".into(),
                scope: Some("Ns".into()),
            }],
            "`local csimp` must retain its scoped namespace"
        );
        assert_eq!(posture.digest.len(), 64, "digest is a hex BLAKE3");
        assert_eq!(
            posture.digest,
            compute_transitive_csimp_posture_digest("Root", &posture.modules),
            "posture digest is recomputable from the canonical module map"
        );

        // A reader that yields the same graph in reverse insertion order must produce the exact
        // same posture and digest.
        let reversed: Vec<(String, CompiledModuleCsimpObservation)> =
            fixture.iter().rev().map(|(k, v)| (k.clone(), v.clone())).collect();
        let posture_rev = scan_transitive_csimp_posture("Root", |m| {
            Ok(reversed
                .iter()
                .find(|(k, _)| k == m)
                .map(|(_, v)| v.clone()))
        })
        .expect("reversed reader resolves the same closure");
        assert_eq!(posture, posture_rev);
    }

    #[test]
    fn test_transitive_csimp_posture_digest_is_canonical_and_content_bound() {
        let fixture = transitive_csimp_fixture();
        let posture = scan_transitive_csimp_posture("Root", |m| Ok(fixture.get(m).cloned())).unwrap();
        let base = posture.digest.clone();

        // Duplicating an observation, or re-inserting modules in another order, is digest-neutral.
        let mut duplicated = posture.modules.clone();
        let dep = duplicated.get_mut("DepGlobal").unwrap();
        dep.push(dep[0].clone());
        assert_eq!(compute_transitive_csimp_posture_digest("Root", &duplicated), base);
        let reordered: BTreeMap<String, Vec<CompiledCsimpObservation>> = posture
            .modules
            .iter()
            .rev()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        assert_eq!(compute_transitive_csimp_posture_digest("Root", &reordered), base);

        // Every canonical field is content-bound.
        let mutations: Vec<Box<dyn Fn(&mut BTreeMap<String, Vec<CompiledCsimpObservation>>)>> = vec![
            Box::new(|m| {
                let e = &mut m.get_mut("DepGlobal").unwrap()[0];
                e.theorem.push('x');
            }),
            Box::new(|m| {
                let e = &mut m.get_mut("DepGlobal").unwrap()[0];
                e.from.push('x');
            }),
            Box::new(|m| {
                let e = &mut m.get_mut("DepGlobal").unwrap()[0];
                e.to.push('x');
            }),
            Box::new(|m| {
                let e = &mut m.get_mut("DepScoped").unwrap()[0];
                e.scope = None;
            }),
            Box::new(|m| {
                let entries = m.remove("DepGlobal").unwrap();
                m.insert("DepGlobalRenamed".to_string(), entries);
            }),
        ];
        for (idx, mutate) in mutations.into_iter().enumerate() {
            let mut changed = posture.modules.clone();
            mutate(&mut changed);
            assert_ne!(
                compute_transitive_csimp_posture_digest("Root", &changed),
                base,
                "mutation #{idx} must change the posture digest"
            );
        }

        // The root identity is bound too, and field concatenation is unambiguous.
        assert_ne!(
            compute_transitive_csimp_posture_digest("Root2", &posture.modules),
            base
        );
        let mut a = BTreeMap::new();
        a.insert(
            "M".to_string(),
            vec![CompiledCsimpObservation {
                theorem: "ab".into(),
                from: "c".into(),
                to: "d".into(),
                scope: None,
            }],
        );
        let mut b = a.clone();
        b.get_mut("M").unwrap()[0] = CompiledCsimpObservation {
            theorem: "a".into(),
            from: "bc".into(),
            to: "d".into(),
            scope: None,
        };
        assert_ne!(
            compute_transitive_csimp_posture_digest("Root", &a),
            compute_transitive_csimp_posture_digest("Root", &b)
        );
    }

    #[test]
    fn test_transitive_csimp_scan_fails_closed_on_unresolvable_imports() {
        let fixture = transitive_csimp_fixture();
        let err = scan_transitive_csimp_posture("Root", |m| {
            if m == "DepGlobal" {
                Ok(None)
            } else {
                Ok(fixture.get(m).cloned())
            }
        })
        .unwrap_err();
        assert!(
            err.to_string().contains("DepGlobal"),
            "unresolvable transitive import must be named in the error: {err}"
        );
        let root_err = scan_transitive_csimp_posture("Root", |_| Ok(None)).unwrap_err();
        assert!(
            root_err.to_string().contains("Root"),
            "an unreadable root must fail closed: {root_err}"
        );
        let empty = scan_transitive_csimp_posture("  ", |_| Ok(None)).unwrap_err();
        assert!(
            empty.to_string().contains("empty"),
            "an empty root module must be rejected: {empty}"
        );
    }

    #[test]
    fn test_public_signature_csimp_entries_parse_losslessly_or_fail_closed() {
        assert_eq!(
            parse_public_signature_csimp_entry("global:slowGlob->fastGlob:slowGlob_eq").unwrap(),
            CompiledCsimpObservation {
                theorem: "slowGlob_eq".into(),
                from: "slowGlob".into(),
                to: "fastGlob".into(),
                scope: None,
            }
        );
        assert_eq!(
            parse_public_signature_csimp_entry("scoped:Ns:slowF->fastF:slowF_eq").unwrap(),
            CompiledCsimpObservation {
                theorem: "slowF_eq".into(),
                from: "slowF".into(),
                to: "fastF".into(),
                scope: Some("Ns".into()),
            }
        );
        for malformed in [
            "",
            "global",
            "global:slowGlob->fastGlob",
            "global:no-arrow:slowGlob_eq",
            "global:a->b->c:thm",
            "scoped:Ns:slowF->fastF",
            "scoped::slowF->fastF:thm",
            "kind:slowF->fastF:thm",
        ] {
            assert!(
                parse_public_signature_csimp_entry(malformed).is_err(),
                "malformed public-signature csimp entry must fail closed: {malformed:?}"
            );
        }
    }

}
