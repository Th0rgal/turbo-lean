use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
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
    /// The binary selection resolved for a con-leche engine, with its provenance and its
    /// selection-time blake3, carried so the executing sites run EXACTLY the probe-accepted
    /// BYTES (DA 388e906a F2; review b08785bc F3: the runners re-verify the digest before each
    /// spawn). Never serialized: receipts carry `con_leche_rev`, and a deserialized provenance
    /// carries no resolved binary.
    #[serde(skip)]
    pub con_leche_binary: Option<ResolvedConLecheBinary>,
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
    no_git: BridgeNoGitPolicy,
) -> Option<String> {
    if !matches!(
        requested,
        KernelEngineSelection::Auto
            | KernelEngineSelection::ConLeche
            | KernelEngineSelection::Both
    ) {
        return probe_con_leche_support(lean_toolchain);
    }
    discover_con_leche_binary_for_workspace_selection(
        requested,
        lean_toolchain,
        workspace_root,
        no_git,
    )
    .ok()
    .flatten()
    .map(|resolved| resolved.provenance.recorded_rev())
}

/// The selection-time binary resolution behind [`probe_con_leche_support_for_selection`] and
/// [`resolve_kernel_engine_in_workspace`]: the pinned-toolchain gate, then the ONE shared
/// discovery, returning the accepted binary with its provenance. G1c r2 (review 22ae951a F1) +
/// DA 388e906a F2: the resolved binary this returns (path, provenance and selection-time
/// digest) is stored in [`KernelProvenance`] so the executing sites run exactly this binary,
/// with no second discovery after the build.
fn discover_con_leche_binary_for_workspace_selection(
    requested: KernelEngineSelection,
    lean_toolchain: &str,
    workspace_root: Option<&Path>,
    no_git: BridgeNoGitPolicy,
) -> Result<Option<ResolvedConLecheBinary>> {
    if !matches!(
        requested,
        KernelEngineSelection::Auto
            | KernelEngineSelection::ConLeche
            | KernelEngineSelection::Both
    ) {
        return Ok(None);
    }
    if normalize_lean_toolchain(lean_toolchain) != PINNED_CON_LECHE_TOOLCHAIN {
        return Ok(None);
    }
    // DA b08785bc F6: the discovery error is NOT swallowed here; the resolver folds its cause
    // into the explicit-selection bail and the auto `fallback_reason`.
    discover_con_leche_binary_for_selection_with_provenance(
        requested,
        lean_toolchain,
        workspace_root,
        no_git,
    )
    .map(Some)
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
    // No workspace root: discovery never consults a checkout, so the bridge-binary
    // tracked-check (and with it the no-`.git` policy) is unreachable here.
    resolve_kernel_engine_in_workspace(
        requested,
        lean_toolchain,
        None,
        BridgeNoGitPolicy::PlainDirIsUntracked,
    )
}

pub fn resolve_kernel_engine_in_workspace(
    requested: KernelEngineSelection,
    lean_toolchain: &str,
    workspace_root: Option<&Path>,
    no_git: BridgeNoGitPolicy,
) -> Result<KernelProvenance> {
    let lean_toolchain = normalize_lean_toolchain(lean_toolchain);
    // DA 388e906a F2: resolve the binary ONCE, here at selection; the result is stored in the
    // provenance so the executing sites run exactly these bytes with no second discovery.
    // DA b08785bc F6: a discovery failure's cause is kept, for the explicit-selection bail and
    // the auto fallback_reason, never swallowed.
    let (discovered_binary, discovery_failure): (
        Option<ResolvedConLecheBinary>,
        Option<anyhow::Error>,
    ) = match workspace_root {
        None => (None, None),
        Some(root) => match discover_con_leche_binary_for_workspace_selection(
            requested,
            &lean_toolchain,
            Some(root),
            no_git,
        ) {
            Ok(found) => (found, None),
            Err(e) => (None, Some(e)),
        },
    };
    let probed_con_leche_rev = discovered_binary
        .as_ref()
        .map(|resolved| resolved.provenance.recorded_rev())
        .or_else(|| probe_con_leche_support(&lean_toolchain));
    let routed_tag =
        crate::c_abi::route_kernel_engine(requested.to_c_abi_tag(), probed_con_leche_rev.is_some());
    let Some(kernel_engine) = ResolvedKernelEngine::from_c_abi_tag(routed_tag) else {
        // DA b08785bc F6: the specific discovery failure (non-UTF-8 env value, tracked bridge
        // binary, failed tracked-check) reaches the user here, not a generic line.
        let cause = discovery_failure
            .as_ref()
            .map(|e| format!("; discovery: {e:#}"))
            .unwrap_or_default();
        anyhow::bail!(
            "Requested kernel engine `{}` cannot verify target toolchain `{}`: verified `con-leche` export/replay backend is not provisioned (fail-closed kernel gate){cause}",
            requested.as_str(),
            lean_toolchain
        );
    };
    let (con_leche_rev, fallback_reason) = match kernel_engine {
        ResolvedKernelEngine::Standard => {
            let fallback = (requested == KernelEngineSelection::Auto).then(|| {
                // DA b08785bc F6: the discovery failure's cause reaches the fallback_reason.
                match discovery_failure.as_ref() {
                    Some(e) => format!(
                        "con-leche backend is not provisioned or supported for toolchain `{}`; using standard Lean kernel (discovery: {e:#})",
                        lean_toolchain
                    ),
                    None => format!(
                        "con-leche backend is not provisioned or supported for toolchain `{}`; using standard Lean kernel",
                        lean_toolchain
                    ),
                }
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
        con_leche_binary: matches!(
            kernel_engine,
            ResolvedKernelEngine::ConLeche | ResolvedKernelEngine::Both
        )
        .then_some(discovered_binary)
        .flatten(),
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
    if let Some(raw) = std::env::var_os(CON_LECHE_BIN_ENV) {
        // DA 388e906a F5: a set but non-UTF-8 value is a reported misconfiguration, never a
        // silent skip (which would let `auto` switch to another binary).
        let Some(raw) = raw.to_str() else {
            anyhow::bail!(
                "`{CON_LECHE_BIN_ENV}` is set to a non-UTF-8 value: fail-closed misconfiguration"
            );
        };
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

/// The elan home the bundled-binary probe consults: `ELAN_HOME`, else `$HOME/.elan`. An empty or
/// relative value yields a path the bundled probe rejects (it requires an absolute elan home).
fn elan_home_dir() -> Option<PathBuf> {
    std::env::var_os("ELAN_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".elan")))
}

/// The toolchain-bundled `con-leche` binary (`<elan_home>/toolchains/<toolchain>/bin/con-leche`,
/// with elan's directory mangling of `/` to `--` and `:` to `---`), for the `auto` selection's
/// support probe (G1c). Returns the path only for the pinned toolchain and an ABSOLUTE elan home
/// (review 22ae951a F4: a relative or empty `ELAN_HOME` would resolve against the current
/// directory and could accept a file inside the PR checkout). Callers check executability,
/// canonicalize, and reject a path under the checkout. Explicit `con-leche`/`both` selections
/// never consult it.
fn bundled_toolchain_con_leche_binary(
    lean_toolchain: &str,
    elan_home: Option<&Path>,
) -> Option<PathBuf> {
    let toolchain = normalize_lean_toolchain(lean_toolchain);
    if toolchain != PINNED_CON_LECHE_TOOLCHAIN {
        return None;
    }
    let elan_home = elan_home?;
    if !elan_home.is_absolute() {
        return None;
    }
    let dir_name = toolchain.replace('/', "--").replace(':', "---");
    Some(
        elan_home
            .join("toolchains")
            .join(dir_name)
            .join("bin")
            .join("con-leche"),
    )
}

/// The provenance the recorded `con_leche_rev` string rests on (G1c r2): never record `PINNED_CON_LECHE_REV` for a binary whose rev was
/// not verified.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConLecheBinaryProvenance {
    /// A provisioned binary (`TURBO_CON_LECHE_BIN`, or the checkout's bridge binary behind the
    /// identity gate): built at the pinned rev by the provisioning contract.
    ProvisionedPinnedRev,
    /// The toolchain-bundled binary: accepted only after the `--help` capability probe, and its
    /// rev is NOT verified, so runs record [`BUNDLED_CON_LECHE_PROVENANCE_MARKER`], never the
    /// pinned rev.
    ToolchainBundledProbed,
    /// A provisioned binary (`TURBO_CON_LECHE_BIN`) whose canonical path IS the toolchain-bundled
    /// candidate: its rev is unverified AND the capability probe never ran on this path, so the
    /// recorded marker says provisioned, never probed (review b08785bc F2).
    ToolchainBundledProvisioned,
}

impl ConLecheBinaryProvenance {
    /// The `con_leche_rev` string recorded for a binary of this provenance. DA 388e906a F1: the
    /// recorded rev is decided HERE, from the provenance the one discovery classified, never
    /// re-derived from paths after the fact.
    pub fn recorded_rev(self) -> String {
        match self {
            Self::ProvisionedPinnedRev => PINNED_CON_LECHE_REV.to_string(),
            Self::ToolchainBundledProbed => BUNDLED_CON_LECHE_PROVENANCE_MARKER.to_string(),
            Self::ToolchainBundledProvisioned => {
                BUNDLED_CON_LECHE_PROVISIONED_MARKER.to_string()
            }
        }
    }
}

/// The `con_leche_rev` value recorded for a toolchain-bundled binary: a probed-capability
/// marker, because the capability probe establishes the CLI surface, not the rev.
pub const BUNDLED_CON_LECHE_PROVENANCE_MARKER: &str =
    "toolchain-bundled:rev-unverified:olean-help-probed";

/// The `con_leche_rev` recorded for a PROVISIONED binary that resolves to the toolchain-bundled
/// path: the rev is unverified and the capability probe never ran on this path
/// (review b08785bc F2).
pub const BUNDLED_CON_LECHE_PROVISIONED_MARKER: &str =
    "toolchain-bundled:rev-unverified:provisioned";

/// The binary a selection resolved, pinned by PATH, PROVENANCE and selection-time BLAKE3
/// (review b08785bc F3: a path pin alone lets a rebuild swap the bytes between selection and
/// execution; the runners re-verify the digest immediately before each spawn).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedConLecheBinary {
    pub path: PathBuf,
    pub provenance: ConLecheBinaryProvenance,
    /// BLAKE3 of the binary's bytes, read at selection time.
    pub blake3_hex: String,
}

impl ResolvedConLecheBinary {
    /// Pin `path` with `provenance` by reading its bytes now. The path is canonicalized first
    /// (every discovery route already hands over a canonical path), so the pinned final
    /// component is never a symlink and the digest can be taken from an `O_NOFOLLOW` fd.
    pub fn resolve(path: &Path, provenance: ConLecheBinaryProvenance) -> Result<Self> {
        let canon = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
        let (_file, blake3_hex) = open_nofollow_and_hash(&canon)?;
        Ok(Self {
            path: canon,
            provenance,
            blake3_hex,
        })
    }

    /// Open the pinned path (`O_NOFOLLOW`), hash the OPENED bytes, and fail closed when they no
    /// longer match the selection-time digest. The returned handle is what the runner executes
    /// (review 4f80161c U3): a path re-hash alone leaves a window in which a rebuild or rename
    /// can swap the binary between the hash and the spawn.
    fn open_execution_verified(&self) -> Result<VerifiedConLecheBinary> {
        let (file, now) = open_nofollow_and_hash(&self.path)?;
        anyhow::ensure!(
            now == self.blake3_hex,
            "`con-leche` binary `{}` changed between selection and execution: selected blake3 `{}`, opened blake3 `{}` (fail-closed; review b08785bc F3)",
            self.path.display(),
            self.blake3_hex,
            now
        );
        Ok(VerifiedConLecheBinary {
            file,
            path: self.path.clone(),
        })
    }
}

/// An open, digest-verified `con-leche` binary. On Linux the spawn goes through
/// `/proc/self/fd/<N>` of this handle, so the EXECUTED bytes are the HASHED bytes whatever
/// happens to the path meanwhile; elsewhere the canonical path is spawned after the fd hash,
/// the pre-U3 behavior (review 4f80161c U3).
#[derive(Debug)]
struct VerifiedConLecheBinary {
    file: std::fs::File,
    /// Spawned directly on non-Linux targets; on Linux the spawn goes through the fd and the
    /// path is carried for the `Debug` rendering of refusals alone.
    #[cfg_attr(target_os = "linux", allow(dead_code))]
    path: PathBuf,
}

impl VerifiedConLecheBinary {
    fn command(&self) -> Command {
        #[cfg(target_os = "linux")]
        {
            use std::os::fd::AsRawFd;
            use std::os::unix::process::CommandExt;
            let fd = self.file.as_raw_fd();
            let mut cmd = Command::new(format!("/proc/self/fd/{fd}"));
            // An ELF target is loaded by `execve` before close-on-exec processing, but a
            // shebang target's INTERPRETER re-opens the `/proc/self/fd/N` argument after it
            // (measured: `bash: /proc/self/fd/N: No such file or directory`, exit 127), so the
            // fd must survive the exec. Clear `FD_CLOEXEC` in the child alone: the parent's
            // handle keeps close-on-exec for every other spawn.
            unsafe {
                cmd.pre_exec(move || {
                    let flags = libc::fcntl(fd, libc::F_GETFD);
                    if flags < 0 {
                        return Err(std::io::Error::last_os_error());
                    }
                    if libc::fcntl(fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0 {
                        return Err(std::io::Error::last_os_error());
                    }
                    Ok(())
                });
            }
            cmd
        }
        #[cfg(not(target_os = "linux"))]
        {
            Command::new(&self.path)
        }
    }
}

/// Open `path` without following a symlink final component and hash the opened fd by
/// streaming, so the digest is of the bytes behind the returned handle, never of whatever a
/// racing rename or symlink swap puts at the path afterwards (review 4f80161c U3).
fn open_nofollow_and_hash(path: &Path) -> Result<(std::fs::File, String)> {
    let mut opts = std::fs::OpenOptions::new();
    opts.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.custom_flags(libc::O_NOFOLLOW);
    }
    let mut file = opts.open(path).with_context(|| {
        format!(
            "Failed to open `con-leche` binary `{}` for the selection digest (symlink final components are refused)",
            path.display()
        )
    })?;
    let mut hasher = blake3::Hasher::new();
    hasher.update_reader(&mut file).with_context(|| {
        format!(
            "Failed to read `con-leche` binary `{}` for the selection digest",
            path.display()
        )
    })?;
    use std::io::Seek;
    file.rewind().with_context(|| {
        format!(
            "Failed to rewind `con-leche` binary `{}` after hashing",
            path.display()
        )
    })?;
    Ok((file, hasher.finalize().to_hex().to_string()))
}

/// The capability probe for the bundled candidate (G1c r2):
/// selection accepts a toolchain-bundled binary only when `--help` EXITS 0 and advertises the
/// `--olean` mode the executing sites require (`verify_olean_modules_with_con_leche`), matched
/// as a whole token so `--olean-dir` does not pass (DA 388e906a F4). The spawn is bounded by a
/// 10 s kill. There is deliberately NO memo: a (path, mtime)-keyed cache is the memo shape this
/// repo rejects (same-length writes with a restored mtime poison it; see
/// `module_builder/dag.rs:6836-6841`), and one spawn per resolution is cheap next to a build
/// (review b08785bc F9). Measured live on 2026-11-26:
/// the v4.35.0 toolchain ships a con-leche whose usage has no `--olean` ("unknown option
/// --olean", exit 3), so on such a host `auto` falls back to standard, the pre-G1c behavior.
fn con_leche_help_advertises_olean(binary_path: &Path) -> bool {
    let canon = binary_path
        .canonicalize()
        .unwrap_or_else(|_| binary_path.to_path_buf());
    con_leche_help_probe_once(&canon)
}

/// One bounded `--help` spawn: exit 0 required; `--olean` as a whole token over stdout+stderr.
/// The output is read after exit, so a (hypothetical) help text larger than the pipe buffer
/// would stall the child into the timeout kill and read as incapable: fail-closed.
fn con_leche_help_probe_once(binary_path: &Path) -> bool {
    use std::io::Read;
    let Ok(mut child) = Command::new(binary_path)
        .arg("--help")
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
    else {
        return false;
    };
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {
                if std::time::Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    return false;
                }
                std::thread::sleep(std::time::Duration::from_millis(20));
            }
            Err(_) => {
                let _ = child.kill();
                let _ = child.wait();
                return false;
            }
        }
    };
    if !status.success() {
        return false;
    }
    let mut text = String::new();
    if let Some(mut out) = child.stdout.take() {
        let _ = out.read_to_string(&mut text);
    }
    if let Some(mut err) = child.stderr.take() {
        let mut err_text = String::new();
        let _ = err.read_to_string(&mut err_text);
        text.push_str(&err_text);
    }
    text.split(|c: char| !(c.is_ascii_alphanumeric() || c == '-' || c == '_'))
        .any(|token| token == "--olean")
}

/// How the bridge-binary tracked-check treats a checkout with NO `.git` entry. The policy is
/// the CALLER's, not the check's (review 4f80161c U2): what a missing `.git` means depends on
/// what the command is measuring.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BridgeNoGitPolicy {
    /// `check --emit-olean` in a plain directory: a tree without `.git` cannot have DELIVERED
    /// the file through a git tree, so the binary counts as untracked (DA b08785bc F4; failing
    /// closed here regressed plain-directory checks, where git exits 128).
    PlainDirIsUntracked,
    /// The `pr-verify` / `ci-verify` discovery path: those commands measure a git CHECKOUT, so
    /// a missing `.git` is an anomaly and the tracked-check fails closed.
    PlainDirFailsClosed,
}

/// Whether the checkout's bridge-binary path is TRACKED in git (DA 388e906a F3, scoped):
/// `pr-verify` materializes the head TREE, so a malicious PR can only plant a bridge binary by
/// COMMITTING it, while a legitimate bridge binary is a build output and stays untracked.
/// Exit 0 = tracked, exit 1 = untracked; anything else is an error the caller fails closed on.
fn bridge_binary_is_tracked(checkout: &Path, no_git: BridgeNoGitPolicy) -> Result<bool> {
    // A checkout without a `.git` entry is decided by the caller's policy (review 4f80161c U2).
    if !checkout.join(".git").exists() {
        return match no_git {
            BridgeNoGitPolicy::PlainDirIsUntracked => Ok(false),
            BridgeNoGitPolicy::PlainDirFailsClosed => Err(anyhow::anyhow!(
                "checkout `{}` has no `.git` entry, so the bridge-binary tracked-check cannot run; this verification path measures a git checkout and fails closed",
                checkout.display()
            )),
        };
    }
    // DA b08785bc F4: git is resolved through the trusted-tools resolver (`TURBO_LEAN_GIT`, the
    // vetted system paths, the MIN_GIT floor), never a bare PATH lookup.
    let mut git_cmd = crate::trusted_tools::git(checkout)
        .context("failed to resolve a trusted git for the bridge-binary tracked check")?;
    let out = git_cmd
        .current_dir(checkout)
        .args(["ls-files", "--error-unmatch", "--", BRIDGE_CON_LECHE_BIN_REL])
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .output()
        .context("failed to run `git ls-files` for the bridge-binary tracked check")?;
    match out.status.code() {
        Some(0) => Ok(true),
        Some(1) => Ok(false),
        other => anyhow::bail!(
            "`git ls-files --error-unmatch` for the bridge `con-leche` binary returned unexpected status {other:?}"
        ),
    }
}

/// G1c r2: the ONE discovery, run once at selection (review 22ae951a F1; DA 388e906a F2). The
/// accepted binary, its provenance and its selection-time blake3 are stored in
/// [`KernelProvenance`], and the executing sites run that stored result; no site re-discovers
/// at execution (review b08785bc F8: the old per-site wrapper is deleted with its callers).
pub fn discover_con_leche_binary_for_selection_with_provenance(
    requested: KernelEngineSelection,
    lean_toolchain: &str,
    workspace_root: Option<&Path>,
    no_git: BridgeNoGitPolicy,
) -> Result<ResolvedConLecheBinary> {
    // DA 388e906a F5: `var_os`, so a set but non-UTF-8 value still counts as provisioned (it is
    // a reported misconfiguration downstream, never a silent switch to the bundled binary).
    let env_provisioned = match std::env::var_os(CON_LECHE_BIN_ENV) {
        None => false,
        Some(raw) => raw.to_str().map(|s| !s.trim().is_empty()).unwrap_or(true),
    };
    discover_con_leche_binary_for_selection_impl(
        requested,
        lean_toolchain,
        workspace_root,
        discover_con_leche_binary(workspace_root),
        env_provisioned,
        elan_home_dir().as_deref(),
        &con_leche_help_advertises_olean,
        &|co: &Path| bridge_binary_is_tracked(co, no_git),
    )
}

/// The env-free core of [`discover_con_leche_binary_for_selection_with_provenance`], with the provisioned
/// discovery outcome, the elan home and the `--olean` capability probe injected for unit
/// testing (review 22ae951a F6).
fn discover_con_leche_binary_for_selection_impl(
    requested: KernelEngineSelection,
    lean_toolchain: &str,
    workspace_root: Option<&Path>,
    provisioned: Result<PathBuf>,
    env_provisioned: bool,
    elan_home: Option<&Path>,
    bundled_olean_capable: &dyn Fn(&Path) -> bool,
    bridge_tracked_in_checkout: &dyn Fn(&Path) -> Result<bool>,
) -> Result<ResolvedConLecheBinary> {
    // The checkout the identity and containment gates measure against. A workspace root that
    // cannot be canonicalized fails the gates closed for every selection.
    let checkout: Option<PathBuf> = match workspace_root {
        None => None,
        Some(proj) => match proj.canonicalize() {
            Ok(canon) => {
                let co = canon
                    .ancestors()
                    .find(|p| p.join(".git").exists())
                    .unwrap_or(canon.as_path())
                    .to_path_buf();
                Some(co)
            }
            Err(e) => anyhow::bail!(
                "Workspace root `{}` cannot be canonicalized for the `con-leche` identity gate (fail-closed): {e}",
                proj.display()
            ),
        },
    };
    let bundled_fallback = |err: anyhow::Error| -> Result<ResolvedConLecheBinary> {
        // Only `auto` consults the bundled binary, and never while `TURBO_CON_LECHE_BIN` is set:
        // a set-but-invalid provisioning env is a reported misconfiguration, not a silent switch
        // to another binary (review 22ae951a F4).
        if requested != KernelEngineSelection::Auto || env_provisioned {
            return Err(err);
        }
        let Some(candidate) = bundled_toolchain_con_leche_binary(lean_toolchain, elan_home)
            .filter(|b| is_executable_file(b))
        else {
            return Err(err);
        };
        let Ok(canon) = candidate.canonicalize() else {
            return Err(err);
        };
        // A bundled path inside the checkout is never accepted: a file in the PR tree must not
        // be recorded as the pinned rev (review 22ae951a F4).
        if let Some(co) = checkout.as_deref() {
            if canon.starts_with(co) {
                return Err(err);
            }
        }
        // Capability gate (G1c r2): the bundled binary is
        // accepted only when it advertises the `--olean` mode the executing sites require;
        // otherwise `auto` falls back to standard, the pre-G1c behavior.
        if !bundled_olean_capable(&canon) {
            return Err(err.context(format!(
                "toolchain-bundled `con-leche` at `{}` rejected: its `--help` does not advertise `--olean` (capability probe; `auto` falls back to standard)",
                canon.display()
            )));
        }
        ResolvedConLecheBinary::resolve(&canon, ConLecheBinaryProvenance::ToolchainBundledProbed)
    };
    let bin = match provisioned {
        Ok(bin) => bin,
        Err(e) => return bundled_fallback(e),
    };
    if let Some(co) = checkout.as_deref() {
        if bin.starts_with(co) || bin.ancestors().any(|p| p.join(".git").exists()) {
            let expected_bridge_bin = co.join(BRIDGE_CON_LECHE_BIN_REL).canonicalize().ok();
            if expected_bridge_bin.as_ref() != Some(&bin) {
                // A discovered binary inside a checkout that is not that checkout's bridge
                // binary is refused; `auto` then tries the bundled binary explicitly instead of
                // returning nothing (review 22ae951a F4).
                return bundled_fallback(anyhow::anyhow!(
                    "Discovered `con-leche` binary `{}` is inside a checkout and is not the expected bridge binary: fail-closed identity gate",
                    bin.display()
                ));
            }
            // DA 388e906a F3 (scoped): a bridge binary DELIVERED BY THE TREE is never accepted.
            // `pr-verify` materializes the head TREE, so a planted binary at the bridge path is
            // necessarily tracked there, while a legitimately built bridge binary is a `.lake`
            // build output and stays untracked. A check that cannot run fails closed.
            match bridge_tracked_in_checkout(co) {
                Ok(false) => {}
                Ok(true) => {
                    return bundled_fallback(anyhow::anyhow!(
                        "Bridge `con-leche` binary `{}` is TRACKED in checkout `{}`: a tree-delivered binary is refused (fail-closed identity gate)",
                        bin.display(),
                        co.display()
                    ));
                }
                Err(e) => {
                    return bundled_fallback(anyhow::anyhow!(
                        "Could not determine whether bridge `con-leche` binary `{}` is tracked in checkout `{}` (fail-closed): {e:#}",
                        bin.display(),
                        co.display()
                    ));
                }
            }
        }
    }
    // DA 388e906a F1: classify by canonical path in ONE place. A provisioned binary that IS the
    // toolchain-bundled candidate (e.g. `TURBO_CON_LECHE_BIN` pointing at it) carries the
    // bundled provenance: its rev is exactly as unverified found that way, and the recorded rev
    // must say so everywhere (selection, receipts, run reports).
    let is_bundled_candidate = bundled_toolchain_con_leche_binary(lean_toolchain, elan_home)
        .and_then(|p| p.canonicalize().ok())
        .is_some_and(|cand| {
            cand == bin || Some(cand.as_path()) == bin.canonicalize().ok().as_deref()
        });
    if is_bundled_candidate {
        // DA b08785bc F2: this branch never ran the capability probe, so the marker must say
        // provisioned, never probed.
        return ResolvedConLecheBinary::resolve(
            &bin,
            ConLecheBinaryProvenance::ToolchainBundledProvisioned,
        );
    }
    ResolvedConLecheBinary::resolve(&bin, ConLecheBinaryProvenance::ProvisionedPinnedRev)
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
    binary_provenance: ConLecheBinaryProvenance,
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
    // DA 388e906a F1: the run report's rev claim comes from the provenance the ONE discovery
    // classified at selection, never re-derived from paths after the fact.
    Ok(ConLecheRunReport {
        verdict,
        exit_code: code,
        binary_path,
        con_leche_rev: binary_provenance.recorded_rev(),
        jobs,
        accepted_declarations,
        stdout,
        stderr,
    })
}

pub fn verify_olean_modules_with_con_leche(
    resolved_binary: &ResolvedConLecheBinary,
    search_paths: &[PathBuf],
    root_modules: &[String],
    constants: &[String],
    requested_jobs: Option<usize>,
    scratch_tmpdir: Option<&Path>,
) -> Result<ConLecheRunReport> {
    let binary_path = resolved_binary.path.as_path();
    if !is_executable_file(binary_path) {
        anyhow::bail!(
            "`con-leche` binary is missing or not executable: `{}`",
            binary_path.display()
        );
    }
    // DA b08785bc F3 + review 4f80161c U3: the executed bytes must be the selected bytes; the
    // binary is opened (`O_NOFOLLOW`), hashed from that fd, and spawned from the same handle.
    let verified = resolved_binary.open_execution_verified()?;
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

    let mut cmd = verified.command();
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
    classify_con_leche_status(
        out.status,
        binary_path.to_path_buf(),
        resolved_binary.provenance,
        jobs,
        stdout,
        stderr,
    )
}

pub fn verify_ndjson_with_con_leche(
    resolved_binary: &ResolvedConLecheBinary,
    ndjson_file: &Path,
    requested_jobs: Option<usize>,
    scratch_tmpdir: Option<&Path>,
) -> Result<ConLecheRunReport> {
    let binary_path = resolved_binary.path.as_path();
    if !is_executable_file(binary_path) {
        anyhow::bail!(
            "`con-leche` binary is missing or not executable: `{}`",
            binary_path.display()
        );
    }
    // DA b08785bc F3 + review 4f80161c U3: the executed bytes must be the selected bytes; the
    // binary is opened (`O_NOFOLLOW`), hashed from that fd, and spawned from the same handle.
    let verified = resolved_binary.open_execution_verified()?;
    if !ndjson_file.is_file() {
        anyhow::bail!(
            "`con-leche` NDJSON stream file does not exist: `{}`",
            ndjson_file.display()
        );
    }
    let jobs = bounded_con_leche_jobs(requested_jobs);
    let tmpdir = resolve_scratch_tmpdir(scratch_tmpdir);

    let mut cmd = verified.command();
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
    classify_con_leche_status(
        out.status,
        binary_path.to_path_buf(),
        resolved_binary.provenance,
        jobs,
        stdout,
        stderr,
    )
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
/// visited in sorted order and the result is independent of the order `read` answers them in, so
/// two scanners over the same graph always produce the same posture and digest. Any unresolvable
/// module in the closure, including the root, fails closed.
pub fn scan_transitive_csimp_posture<F>(
    root_module: &str,
    mut read: F,
) -> Result<TransitiveCsimpPosture>
where
    F: FnMut(&str) -> Result<Option<CompiledModuleCsimpObservation>>,
{
    let root = root_module.trim();
    anyhow::ensure!(
        !root.is_empty(),
        "Cannot scan the transitive compiled-import csimp posture of an empty root module name"
    );
    let mut modules: BTreeMap<String, Vec<CompiledCsimpObservation>> = BTreeMap::new();
    let mut frontier: BTreeSet<String> = BTreeSet::new();
    frontier.insert(root.to_string());
    while let Some(module) = frontier.pop_first() {
        if modules.contains_key(&module) {
            continue;
        }
        let observation = read(&module).with_context(|| {
            format!("Failed to read the compiled csimp posture of module `{module}`")
        })?;
        let Some(observation) = observation else {
            anyhow::bail!(
                "[TurboLean.KernelGate] transitive compiled-import csimp scan of `{root}` \
                 could not resolve module `{module}`: fail-closed"
            );
        };
        let mut entries = observation.entries;
        entries.sort();
        entries.dedup();
        for import in &observation.imports {
            let import = import.trim();
            if !import.is_empty() && !modules.contains_key(import) {
                frontier.insert(import.to_string());
            }
        }
        modules.insert(module, entries);
    }
    let digest = compute_transitive_csimp_posture_digest(root, &modules);
    Ok(TransitiveCsimpPosture {
        root: root.to_string(),
        modules,
        digest,
    })
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
    fn field(h: &mut blake3::Hasher, s: &str) {
        h.update(&(s.len() as u64).to_le_bytes());
        h.update(s.as_bytes());
    }
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-transitive-csimp-posture-v1\n");
    field(&mut h, "root");
    field(&mut h, root_module.trim());
    for (module, entries) in modules {
        field(&mut h, "module");
        field(&mut h, module);
        let unique: BTreeSet<&CompiledCsimpObservation> = entries.iter().collect();
        h.update(&(unique.len() as u64).to_le_bytes());
        for entry in unique {
            field(&mut h, "entry");
            field(&mut h, &entry.theorem);
            field(&mut h, &entry.from);
            field(&mut h, &entry.to);
            match entry.scope.as_deref() {
                None => field(&mut h, "global"),
                Some(scope) => {
                    field(&mut h, "scoped");
                    field(&mut h, scope);
                }
            }
        }
    }
    h.finalize().to_hex().to_string()
}

/// Parse one `csimp_entries` string from a compiled module's public signature, e.g.
/// `global:slowGlob->fastGlob:slowGlob_eq` or `scoped:Ns:slowF->fastF:slowF_eq`.
///
/// Malformed entries fail closed instead of being silently dropped, so a truncated or spoofed
/// signature can never look like a clean posture.
pub fn parse_public_signature_csimp_entry(raw: &str) -> Result<CompiledCsimpObservation> {
    let parts = split_lean_csimp_fields(raw);
    let reject = |why: &str| {
        anyhow::anyhow!(
            "[TurboLean.KernelGate] malformed public-signature csimp entry `{raw}`: {why}"
        )
    };
    let (scope, pair, theorem) = match parts.as_slice() {
        [kind, pair, theorem] if *kind == "global" => (None, *pair, *theorem),
        [kind, scope, pair, theorem] if *kind == "scoped" => (Some(*scope), *pair, *theorem),
        _ => {
            return Err(reject(
                "expected `global:<from>-><to>:<theorem>` or `scoped:<ns>:<from>-><to>:<theorem>`",
            ))
        }
    };
    if let Some(scope) = scope {
        if scope.is_empty() {
            return Err(reject("empty scoped namespace"));
        }
    }
    if theorem.is_empty() {
        return Err(reject("empty replacement theorem name"));
    }
    let arrow_split = split_lean_csimp_arrow(pair);
    let (from, to) = match arrow_split.as_slice() {
        [from, to] if !from.is_empty() && !to.is_empty() => (*from, *to),
        _ => return Err(reject("expected exactly one non-empty `<from>-><to>` replacement pair")),
    };
    Ok(CompiledCsimpObservation {
        theorem: theorem.to_string(),
        from: from.to_string(),
        to: to.to_string(),
        scope: scope.map(str::to_string),
    })
}

/// Split a public-signature `csimp_entries` field on top-level `:` separators, ignoring separators
/// inside a guillemet-quoted identifier (`«...»`).
fn split_lean_csimp_fields(raw: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut start = 0usize;
    let mut in_guillemet = false;
    for (idx, ch) in raw.char_indices() {
        match ch {
            '«' => in_guillemet = true,
            '»' => in_guillemet = false,
            ':' if !in_guillemet => {
                out.push(&raw[start..idx]);
                start = idx + ch.len_utf8();
            }
            _ => {}
        }
    }
    out.push(&raw[start..]);
    out
}

/// Split a `csimp` replacement pair on its single top-level `->`, ignoring any `->` inside a
/// guillemet-quoted identifier.
fn split_lean_csimp_arrow(pair: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut start = 0usize;
    let mut in_guillemet = false;
    let mut i = 0usize;
    let bytes = pair.as_bytes();
    while i < bytes.len() {
        match bytes[i] {
            b'\xC2' if bytes.get(i + 1) == Some(&0xAB) => {
                in_guillemet = true;
                i += 2;
                continue;
            }
            b'\xC2' if bytes.get(i + 1) == Some(&0xBB) => {
                in_guillemet = false;
                i += 2;
                continue;
            }
            b'-' if !in_guillemet && bytes.get(i + 1) == Some(&b'>') => {
                out.push(&pair[start..i]);
                start = i + 2;
                i += 2;
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    out.push(&pair[start..]);
    out
}

// -------------------------------------------------------------------------------------------
// P9: imported-posture policy decision table (issues #411 / #412).
//
// The zygote worker's `--import-posture` command reports, for the modules an imported-`.olean`
// audit is about to cover, every policy-relevant posture fact with the structural exemptions the
// full audit applies already folded in (wrapper parents, Init-exec whitelists, pinned FFI,
// compiler-generated `unsafe_rec` twins, the kernel-cone reachability filter). The table below
// applies the project allowlists (`turbo-lean.toml` `[csimp]` / `[unsafe]` / `[implemented_by]` /
// `[axioms] allow`, resolved by the CLI into the `TURBO_LEAN_ALLOWED_*` environment) and decides
// each posture BEFORE the expensive audit machinery (closure snapshot, whole-closure kernel
// replay, per-declaration axiom-closure walks, per-entry verified-csimp replay) runs:
//
// | posture                                   | decided by                           | outcome   |
// |-------------------------------------------|--------------------------------------|-----------|
// | csimp entry, strict proven theorem        | `[csimp] allow` glob (raw or user)   | allow/forbid |
// | csimp entry, non-theorem or non-strict    | never allowlistable                  | forbid    |
// | csimp entry a target neither owns nor touches | never considered (mirrors the non-import audit) | skipped |
// | unsafe declaration (post structural exemptions) | `[unsafe] allow` on decl or wrapper | allow/forbid |
// | unsafe `_unsafe_rec` twin                 | never allowlistable by name          | forbid (wrapper `[unsafe]` allow only) |
// | unsafe inductive                          | never allowlistable                  | forbid    |
// | `@[extern]` bypass                        | never `[implemented_by]`-listable    | forbid (wrapper `[unsafe]` allow only) |
// | `@[implemented_by]` bypass                | `[implemented_by] allow`, or wrapper `[unsafe]` allow | allow/forbid |
// | custom axiom declaration                  | standard axioms + `[axioms] allow` (never `sorryAx` / `Lean.trustCompiler`) | allow/forbid |
//
// A forbidden outcome fails closed with a message naming the exact `turbo-lean.toml` knob; an
// allowed outcome proceeds into the unchanged, authoritative in-kernel audit. The pass decides
// exactly the entries that audit considers — for csimp, those a target module owns or touches
// (`checkCSimpEntry` with `isImportAudit = false`); for the rest, the per-target candidates the
// worker already passed through the audit's structural exemptions — so it refuses nothing the
// audit would skip and admits nothing it would refuse.
// -------------------------------------------------------------------------------------------

pub const EARLY_IMPORT_POLICY_ENV: &str = "TURBO_LEAN_EARLY_IMPORT_POLICY";

/// Whether the early imported-posture policy decision runs before the in-kernel audit.
/// `TURBO_LEAN_EARLY_IMPORT_POLICY=off|0|false` restores the legacy decide-inside-the-audit path
/// (including the expensive per-entry verified-csimp closure replay for unlisted entries).
pub fn early_import_policy_enabled() -> bool {
    match std::env::var(EARLY_IMPORT_POLICY_ENV) {
        Ok(v) => !matches!(v.trim().to_ascii_lowercase().as_str(), "off" | "0" | "false"),
        Err(_) => true,
    }
}

/// One `@[csimp]` / `local csimp` posture entry as the worker reports it: the parsed
/// public-signature observation plus the decision-relevant facts the worker computed in-kernel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PostureCsimpEntry {
    pub observation: CompiledCsimpObservation,
    /// `Lean.privateToUserName` of the replacement theorem (what the allowlist naturally names).
    pub thm_user_name: String,
    /// The entry is a real theorem whose statement proves exactly this `(from, to)` replacement.
    pub strict: bool,
    /// Any of the entry's names is owned by an audited target module.
    pub touches_target: bool,
}

/// One compiled module's csimp posture plus its direct imports (the `#455` scan's input).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ImportPostureModule {
    pub module: String,
    pub imports: Vec<String>,
    pub csimp: Vec<PostureCsimpEntry>,
}

/// An unsafe declaration that failed every structural exemption of the full audit; only the
/// allowlist half of the decision is left.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PostureUnsafeCandidate {
    pub raw: String,
    pub user: String,
    /// `false` for compiler-generated `_unsafe_rec` twins, which no name pattern may admit.
    pub pattern_allowable: bool,
    /// The audit would offer the `[unsafe] allow` knob for this declaration.
    pub can_allow: bool,
    /// Safe-wrapper parents whose `[unsafe] allow` listing admits this declaration.
    pub wrapper_names: Vec<String>,
}

/// An `@[extern]` / `@[implemented_by]` bypass that failed every structural exemption.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PostureBridgeCandidate {
    pub raw: String,
    pub user: String,
    pub is_extern: bool,
    pub is_implemented_by: bool,
    /// From the module's `extraConstNames` (the audit's "auxiliary" wording).
    pub auxiliary: bool,
    /// Safe-wrapper parents whose `[unsafe] allow` listing admits this bypass.
    pub wrapper_names: Vec<String>,
}

/// Per-target-module posture candidates (the modules the audit was asked to cover).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ImportPostureTarget {
    pub module: String,
    pub axioms: Vec<String>,
    pub unsafe_inductives: Vec<String>,
    pub unsafe_decls: Vec<PostureUnsafeCandidate>,
    pub bridge_decls: Vec<PostureBridgeCandidate>,
}

/// The four allowlists of the import policy. `axioms` is the full effective list including the
/// standard axioms (the caller builds it, e.g. from `splitter::allowed_axioms()`); the other three
/// are the raw `turbo-lean.toml` `allow` globs.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ImportPolicyAllowlists {
    pub axioms: Vec<String>,
    pub csimp: Vec<String>,
    pub unsafe_decls: Vec<String>,
    pub implemented_by: Vec<String>,
}

/// The decided import-policy outcome: empty `violations` means every posture is allowlisted (or
/// structurally exempt) and the expensive audit may proceed.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ImportPolicyDecision {
    pub violations: Vec<String>,
}

/// `*`-glob match, byte-for-byte the worker's `globMatch` semantics (kept local so the
/// `#[path]`-included copy of this file in `tests/pluggable_kernel_cli.rs` needs no extra stubs).
fn import_policy_glob_match(pat: &str, s: &str) -> bool {
    match pat.split_once('*') {
        None => pat == s,
        Some((head, rest)) => {
            s.starts_with(head)
                && (0..=s.len() - head.len())
                    .filter(|i| s.is_char_boundary(head.len() + i))
                    .any(|i| import_policy_glob_match(rest, &s[head.len() + i..]))
        }
    }
}

fn name_matches_import_policy(patterns: &[String], raw: &str, user: &str) -> bool {
    patterns
        .iter()
        .map(|p| p.trim())
        .filter(|p| !p.is_empty())
        .any(|p| import_policy_glob_match(p, raw) || import_policy_glob_match(p, user))
}

fn import_policy_axiom_allowed(ax: &str, axioms: &[String]) -> bool {
    ax != "sorryAx"
        && ax != "Lean.trustCompiler"
        && axioms
            .iter()
            .map(|p| p.trim())
            .filter(|p| !p.is_empty())
            .any(|p| import_policy_glob_match(p, ax))
}

fn import_policy_knob_hint(policy: &str, name: &str) -> String {
    format!("; configure [{policy}] allow = [\"{name}\"] in turbo-lean.toml")
}

/// Apply the import-policy decision table (module docs above) to a scanned posture.
pub fn decide_import_posture_policy(
    targets: &[ImportPostureTarget],
    modules: &BTreeMap<String, ImportPostureModule>,
    target_modules: &BTreeSet<String>,
    lists: &ImportPolicyAllowlists,
) -> ImportPolicyDecision {
    let mut violations = Vec::new();
    for t in targets {
        for ax in &t.axioms {
            if !import_policy_axiom_allowed(ax, &lists.axioms) {
                violations.push(format!(
                    "[TurboLean.KernelGate] custom axiom `{ax}` in `{}` is forbidden{}",
                    t.module,
                    import_policy_knob_hint("axioms", ax)
                ));
            }
        }
        for ind in &t.unsafe_inductives {
            violations.push(format!(
                "[TurboLean.KernelGate] unsafe inductive `{ind}` in `{}` is forbidden",
                t.module
            ));
        }
        for c in &t.unsafe_decls {
            let allowed = (c.pattern_allowable
                && name_matches_import_policy(&lists.unsafe_decls, &c.raw, &c.user))
                || c.wrapper_names
                    .iter()
                    .any(|w| name_matches_import_policy(&lists.unsafe_decls, w, w));
            if !allowed {
                let hint = if c.can_allow {
                    import_policy_knob_hint("unsafe", &c.user)
                } else {
                    String::new()
                };
                violations.push(format!(
                    "[TurboLean.KernelGate] unsafe declaration `{}` in `{}` is forbidden{hint}",
                    c.raw, t.module
                ));
            }
        }
        for b in &t.bridge_decls {
            let allowed = (!b.is_extern
                && name_matches_import_policy(&lists.implemented_by, &b.raw, &b.user))
                || b.wrapper_names
                    .iter()
                    .any(|w| name_matches_import_policy(&lists.unsafe_decls, w, w));
            if !allowed {
                let aux = if b.auxiliary { " auxiliary" } else { "" };
                let hint = if !b.is_extern && b.is_implemented_by {
                    import_policy_knob_hint("implemented_by", &b.user)
                } else {
                    String::new()
                };
                violations.push(format!(
                    "[TurboLean.KernelGate] extern/implemented_by bypass on{aux} `{}` in `{}` is forbidden{hint}",
                    b.raw, t.module
                ));
            }
        }
    }
    for (owner, m) in modules {
        for e in &m.csimp {
            // Mirror of the authoritative audit that runs next (`checkCSimpEntry` with
            // `isImportAudit = false` in `ZygoteWorker.lean`): a csimp entry that a target
            // module neither owns nor touches is never considered by that audit, so it is
            // never refused early either.
            if !(target_modules.contains(owner) || e.touches_target) {
                continue;
            }
            let allowed = e.strict
                && name_matches_import_policy(
                    &lists.csimp,
                    &e.observation.theorem,
                    &e.thm_user_name,
                );
            if !allowed {
                violations.push(format!(
                    "[TurboLean.KernelGate] csimp replacement `{}` ({} -> {}) touching `{owner}` is forbidden{}",
                    e.observation.theorem,
                    e.observation.from,
                    e.observation.to,
                    import_policy_knob_hint("csimp", &e.thm_user_name)
                ));
            }
        }
    }
    ImportPolicyDecision { violations }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn posture_lists(
        csimp: &[&str],
        unsafe_decls: &[&str],
        implemented_by: &[&str],
        axioms: &[&str],
    ) -> ImportPolicyAllowlists {
        let v = |xs: &[&str]| xs.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        ImportPolicyAllowlists {
            axioms: v(axioms),
            csimp: v(csimp),
            unsafe_decls: v(unsafe_decls),
            implemented_by: v(implemented_by),
        }
    }

    fn csimp_posture_module(
        module: &str,
        entries: &[(&str, &str, &str, &str, bool, bool)],
    ) -> ImportPostureModule {
        ImportPostureModule {
            module: module.to_string(),
            imports: Vec::new(),
            csimp: entries
                .iter()
                .map(
                    |(theorem, from, to, user, strict, touches)| PostureCsimpEntry {
                        observation: CompiledCsimpObservation {
                            theorem: (*theorem).to_string(),
                            from: (*from).to_string(),
                            to: (*to).to_string(),
                            scope: None,
                        },
                        thm_user_name: (*user).to_string(),
                        strict: *strict,
                        touches_target: *touches,
                    },
                )
                .collect(),
        }
    }

    fn decide_csimp_only(
        modules: &BTreeMap<String, ImportPostureModule>,
        targets: &BTreeSet<String>,
        lists: &ImportPolicyAllowlists,
    ) -> Vec<String> {
        decide_import_posture_policy(&[], modules, targets, lists).violations
    }

    #[test]
    fn test_import_policy_dependency_csimp_entries_follow_the_audited_set() {
        // Mirror of the non-import audit that runs next (`checkCSimpEntry` with
        // `isImportAudit = false`, `ZygoteWorker.lean`): a csimp entry that a target module
        // neither owns nor touches is never considered by that audit, so the early pass must
        // not refuse it either. Dependency shape: the target `Proj.Foo` imports the trusted
        // dependency `Batteries.Data.List.Basic`, which exports
        // `@[csimp] List.replaceF_eq_replaceFTR`, under an empty `[csimp] allow`.
        let mut modules = BTreeMap::new();
        modules.insert(
            "Batteries.Data.List.Basic".to_string(),
            csimp_posture_module(
                "Batteries.Data.List.Basic",
                &[(
                    "List.replaceF_eq_replaceFTR",
                    "List.replaceF",
                    "List.replaceFTR",
                    "List.replaceF_eq_replaceFTR",
                    true,
                    false,
                )],
            ),
        );
        let dependency_targets: BTreeSet<String> = ["Proj.Foo".to_string()].into();
        assert_eq!(
            decide_csimp_only(
                &modules,
                &dependency_targets,
                &posture_lists(&[], &[], &[], &[])
            ),
            Vec::<String>::new(),
            "a dependency csimp entry outside the audited set must not be refused early"
        );
        // The same entry with its owner audited as a target stays refused when unlisted.
        let owner_targets: BTreeSet<String> = ["Batteries.Data.List.Basic".to_string()].into();
        assert_eq!(
            decide_csimp_only(&modules, &owner_targets, &posture_lists(&[], &[], &[], &[])).len(),
            1,
            "a target-owned unlisted csimp entry stays refused"
        );
    }

    #[test]
    fn test_import_policy_decision_table_csimp() {
        let mut modules = BTreeMap::new();
        modules.insert(
            "Batteries.Data.List.Basic".to_string(),
            csimp_posture_module(
                "Batteries.Data.List.Basic",
                &[(
                    "List.replaceF_eq_replaceFTR",
                    "List.replaceF",
                    "List.replaceFTR",
                    "List.replaceF_eq_replaceFTR",
                    true,
                    false,
                )],
            ),
        );
        // The owner is audited as a target, so its entries are inside the audited set the
        // early pass mirrors; the dependency-shape test above pins the not-considered side.
        let targets: BTreeSet<String> = ["Batteries.Data.List.Basic".to_string()].into();

        // Strict proven theorem, exact user-name allowlist entry: allowed.
        let allowed = decide_csimp_only(
            &modules,
            &targets,
            &posture_lists(&["List.replaceF_eq_replaceFTR"], &[], &[], &[]),
        );
        assert_eq!(allowed, Vec::<String>::new());

        // Strict proven theorem, `*` allowlist: allowed.
        assert_eq!(
            decide_csimp_only(&modules, &targets, &posture_lists(&["*"], &[], &[], &[])),
            Vec::<String>::new()
        );

        // Strict proven theorem, no allowlist: forbidden, early, naming the knob.
        let refused = decide_csimp_only(&modules, &targets, &posture_lists(&[], &[], &[], &[]));
        assert_eq!(refused.len(), 1, "unlisted csimp entry must be refused: {refused:?}");
        assert!(
            refused[0].contains(
                "csimp replacement `List.replaceF_eq_replaceFTR` (List.replaceF -> List.replaceFTR) \
                 touching `Batteries.Data.List.Basic` is forbidden"
            ),
            "violation must name the entry, both declarations and the owner module (the audit \
             labels by the target it reports against; the early message names the owner, which \
             is what the `[csimp] allow` author needs): {}",
            refused[0]
        );
        assert!(
            refused[0].contains("[csimp] allow = [\"List.replaceF_eq_replaceFTR\"]"),
            "violation must name the turbo-lean.toml knob: {}",
            refused[0]
        );

        // A non-strict entry is never allowlistable, even under `*`.
        let mut non_strict = modules.clone();
        non_strict
            .get_mut("Batteries.Data.List.Basic")
            .unwrap()
            .csimp[0]
            .strict = false;
        let refused_non_strict =
            decide_csimp_only(&non_strict, &targets, &posture_lists(&["*"], &[], &[], &[]));
        assert_eq!(
            refused_non_strict.len(),
            1,
            "a non-strict csimp entry must stay forbidden under `*`: {refused_non_strict:?}"
        );

        // A toolchain module's entry outside the audited set (not owned by a target, touching
        // none) is never considered, like any other dependency entry...
        let mut init_mod = BTreeMap::new();
        init_mod.insert(
            "Init.Data.Array".to_string(),
            csimp_posture_module(
                "Init.Data.Array",
                &[("Init.thm", "Init.slow", "Init.fast", "Init.thm", true, false)],
            ),
        );
        assert_eq!(
            decide_csimp_only(&init_mod, &targets, &posture_lists(&[], &[], &[], &[])),
            Vec::<String>::new()
        );
        // ...but one touching an audited target is considered and refused when unlisted.
        init_mod.get_mut("Init.Data.Array").unwrap().csimp[0].touches_target = true;
        assert_eq!(
            decide_csimp_only(&init_mod, &targets, &posture_lists(&[], &[], &[], &[])).len(),
            1,
            "an entry touching an audited target is considered and stays refused when unlisted"
        );
    }

    #[test]
    fn test_import_policy_decision_table_unsafe_and_bridge() {
        let lists_none = posture_lists(&[], &[], &[], &[]);
        let target = |unsafe_decls: Vec<PostureUnsafeCandidate>,
                      bridge_decls: Vec<PostureBridgeCandidate>,
                      unsafe_inductives: Vec<String>| ImportPostureTarget {
            module: "Batteries.Tactic.Lint.Basic".to_string(),
            axioms: Vec::new(),
            unsafe_inductives,
            unsafe_decls,
            bridge_decls,
        };
        let modules = BTreeMap::new();
        let target_set = BTreeSet::new();
        let decide = |t: ImportPostureTarget, lists: &ImportPolicyAllowlists| {
            decide_import_posture_policy(&[t], &modules, &target_set, lists).violations
        };

        let unsafe_cand = PostureUnsafeCandidate {
            raw: "_private.Batteries.Tactic.Lint.Basic.0.Batteries.Tactic.Lint.getLinter.unsafe_1"
                .to_string(),
            user: "Batteries.Tactic.Lint.getLinter.unsafe_1".to_string(),
            pattern_allowable: true,
            can_allow: true,
            wrapper_names: Vec::new(),
        };

        // Unlisted unsafe declaration: forbidden with the [unsafe] knob named.
        let refused = decide(target(vec![unsafe_cand.clone()], vec![], vec![]), &lists_none);
        assert_eq!(refused.len(), 1);
        assert!(
            refused[0].contains("unsafe declaration")
                && refused[0].contains("is forbidden")
                && refused[0].contains("[unsafe] allow = [\"Batteries.Tactic.Lint.getLinter.unsafe_1\"]"),
            "unsafe violation must name the knob: {}",
            refused[0]
        );

        // `[unsafe] allow = ["*"]` admits it (the #412 workaround as config).
        assert_eq!(
            decide(
                target(vec![unsafe_cand.clone(), ], vec![], vec![]),
                &posture_lists(&[], &["*"], &[], &[])
            ),
            Vec::<String>::new()
        );

        // A compiler-generated `_unsafe_rec` twin is never admitted by name, even under `*`...
        let mut rec_twin = unsafe_cand.clone();
        rec_twin.pattern_allowable = false;
        rec_twin.can_allow = false;
        let refused_twin = decide(
            target(vec![rec_twin.clone()], vec![], vec![]),
            &posture_lists(&[], &["*"], &[], &[]),
        );
        assert_eq!(refused_twin.len(), 1);
        assert!(
            !refused_twin[0].contains("[unsafe] allow ="),
            "no knob hint when the audit would not offer one: {}",
            refused_twin[0]
        );
        // ...but an allowlisted safe-wrapper parent admits it.
        rec_twin.wrapper_names = vec!["Batteries.SafeWrapper".to_string()];
        assert_eq!(
            decide(
                target(vec![rec_twin], vec![], vec![]),
                &posture_lists(&[], &["Batteries.SafeWrapper"], &[], &[])
            ),
            Vec::<String>::new()
        );

        // implemented_by bypass: [implemented_by] allow admits; unlisted is forbidden with knob.
        let impl_by = PostureBridgeCandidate {
            raw: "_private.Batteries.Tactic.Lint.Basic.0.Batteries.Tactic.Lint.getLinter.unsafe_impl_2"
                .to_string(),
            user: "Batteries.Tactic.Lint.getLinter.unsafe_impl_2".to_string(),
            is_extern: false,
            is_implemented_by: true,
            auxiliary: false,
            wrapper_names: Vec::new(),
        };
        let refused_impl = decide(target(vec![], vec![impl_by.clone()], vec![]), &lists_none);
        assert_eq!(refused_impl.len(), 1);
        assert!(
            refused_impl[0].contains("extern/implemented_by bypass on `")
                && refused_impl[0].contains("[implemented_by] allow = [\"Batteries.Tactic.Lint.getLinter.unsafe_impl_2\"]"),
            "implemented_by violation must name the knob: {}",
            refused_impl[0]
        );
        assert_eq!(
            decide(
                target(vec![], vec![impl_by.clone()], vec![]),
                &posture_lists(&[], &[], &["*"], &[])
            ),
            Vec::<String>::new()
        );

        // An `@[extern]` bypass is never [implemented_by]-listable; a wrapper under [unsafe] is
        // the only admission, and the auxiliary wording is kept.
        let extern_cand = PostureBridgeCandidate {
            raw: "Solidity.externBridge".to_string(),
            user: "Solidity.externBridge".to_string(),
            is_extern: true,
            is_implemented_by: false,
            auxiliary: true,
            wrapper_names: vec!["Solidity.SafeBridge".to_string()],
        };
        let refused_extern = decide(
            target(vec![], vec![extern_cand.clone()], vec![]),
            &posture_lists(&[], &[], &["*"], &[]),
        );
        assert_eq!(refused_extern.len(), 1);
        assert!(
            refused_extern[0].contains("bypass on auxiliary `Solidity.externBridge`")
                && !refused_extern[0].contains("[implemented_by] allow ="),
            "extern bypass must keep the auxiliary wording and offer no implemented_by knob: {}",
            refused_extern[0]
        );
        assert_eq!(
            decide(
                target(vec![], vec![extern_cand], vec![]),
                &posture_lists(&[], &["Solidity.SafeBridge"], &[], &[])
            ),
            Vec::<String>::new()
        );

        // An unsafe inductive is always forbidden.
        let refused_ind = decide(
            target(vec![], vec![], vec!["Evil.UnsafeInd".to_string()]),
            &posture_lists(&["*"], &["*"], &["*"], &["*"]),
        );
        assert_eq!(refused_ind.len(), 1);
        assert!(refused_ind[0].contains("unsafe inductive `Evil.UnsafeInd`"));
    }

    #[test]
    fn test_import_policy_decision_table_axioms() {
        let modules = BTreeMap::new();
        let target_set = BTreeSet::new();
        let t = |axioms: &[&str]| ImportPostureTarget {
            module: "Proj.Axioms".to_string(),
            axioms: axioms.iter().map(|s| s.to_string()).collect(),
            unsafe_inductives: Vec::new(),
            unsafe_decls: Vec::new(),
            bridge_decls: Vec::new(),
        };
        let std_lists = posture_lists(
            &[],
            &[],
            &[],
            &["propext", "Quot.sound", "Classical.choice"],
        );

        // Standard axioms pass under the standard list; a custom one is refused naming the knob.
        assert_eq!(
            decide_import_posture_policy(&[t(&["propext"])], &modules, &target_set, &std_lists)
                .violations,
            Vec::<String>::new()
        );
        let refused = decide_import_posture_policy(
            &[t(&["Proj.customAx"])],
            &modules,
            &target_set,
            &std_lists,
        )
        .violations;
        assert_eq!(refused.len(), 1);
        assert!(
            refused[0].contains("custom axiom `Proj.customAx` in `Proj.Axioms` is forbidden")
                && refused[0].contains("[axioms] allow = [\"Proj.customAx\"]"),
            "axiom violation must name the knob: {}",
            refused[0]
        );

        // `sorryAx` and `Lean.trustCompiler` are hard-refused even under `*`.
        let star = posture_lists(&[], &[], &[], &["*"]);
        assert_eq!(
            decide_import_posture_policy(
                &[t(&["sorryAx", "Lean.trustCompiler"])],
                &modules,
                &target_set,
                &star
            )
            .violations
            .len(),
            2
        );
        // ...while `*` admits an ordinary custom axiom.
        assert_eq!(
            decide_import_posture_policy(&[t(&["Proj.customAx"])], &modules, &target_set, &star)
                .violations,
            Vec::<String>::new()
        );
    }

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

    /// RAII env guard: restores the previous value on drop, a failed assertion included
    /// (review 22ae951a F6).
    struct ScopedEnvVar {
        key: &'static str,
        prev: Option<std::ffi::OsString>,
    }

    impl ScopedEnvVar {
        fn set(key: &'static str, value: &std::ffi::OsStr) -> Self {
            let prev = std::env::var_os(key);
            std::env::set_var(key, value);
            Self { key, prev }
        }

        fn remove(key: &'static str) -> Self {
            let prev = std::env::var_os(key);
            std::env::remove_var(key);
            Self { key, prev }
        }
    }

    impl Drop for ScopedEnvVar {
        fn drop(&mut self) {
            match self.prev.take() {
                Some(v) => std::env::set_var(self.key, v),
                None => std::env::remove_var(self.key),
            }
        }
    }

    #[test]
    fn test_selection_discovery_matrix_bundled_and_provisioned() {
        // G1c r2: the env-free injected-lookup matrix over the shared selection discovery
        // (review 22ae951a F1/F4/F6; --olean capability probe, G1c r2). No environment variable is read or written, and no binary
        // or git process is executed: the capability probe and the bridge tracked-check are
        // injected. Caveat (DA 388e906a F8): cases that expect acceptance rely on
        // `std::env::temp_dir()` lying outside every git checkout; a TMPDIR inside a repo would
        // trip the in-checkout and `.git`-ancestor gates on the fixtures.
        let tmp = std::env::temp_dir().join(format!(
            "turbo_lean_g1c_selmx_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let ws = tmp.join("ws");
        let elan = tmp.join("elan");
        let bin_dir = elan.join("toolchains/leanprover--lean4---v4.35.0/bin");
        std::fs::create_dir_all(&ws).unwrap();
        std::fs::create_dir_all(&bin_dir).unwrap();
        let not_found = || anyhow::anyhow!("no provisioned con-leche");
        let olean_capable: &dyn Fn(&Path) -> bool = &|_| true;
        let olean_incapable: &dyn Fn(&Path) -> bool = &|_| false;
        let bridge_untracked: &dyn Fn(&Path) -> anyhow::Result<bool> = &|_| Ok(false);
        let write_exec = |p: &Path| {
            std::fs::write(p, b"#!/bin/sh\nexit 0\n").unwrap();
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                std::fs::set_permissions(p, std::fs::Permissions::from_mode(0o755)).unwrap();
            }
        };

        // 1. auto with no provisioned and no bundled file: the provisioned error stands.
        assert!(discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::Auto,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws),
            Err(not_found()),
            false,
            Some(&elan),
            olean_capable,
            bridge_untracked,
        )
        .is_err());

        // 2. auto with a bundled executable that passes the capability probe: selected,
        //    canonicalized, recorded as probed bundled provenance (never the pinned rev).
        let bundled = bin_dir.join("con-leche");
        write_exec(&bundled);
        let resolved = discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::Auto,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws),
            Err(not_found()),
            false,
            Some(&elan),
            olean_capable,
            bridge_untracked,
        )
        .unwrap();
        assert_eq!(resolved.path, bundled.canonicalize().unwrap());
        assert_eq!(
            resolved.provenance,
            ConLecheBinaryProvenance::ToolchainBundledProbed
        );
        // The selection-time byte pin (review b08785bc F3): a 64-hex blake3 of the bytes.
        assert_eq!(resolved.blake3_hex.len(), 64);
        assert!(resolved.blake3_hex.chars().all(|c| c.is_ascii_hexdigit()));

        // 2b. auto with a bundled executable that FAILS the --olean capability probe: rejected,
        //     with both the probe rejection and the original provisioned error reported
        //     (auto falls back to standard, the pre-G1c behavior).
        let err = discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::Auto,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws),
            Err(not_found()),
            false,
            Some(&elan),
            olean_incapable,
            bridge_untracked,
        )
        .unwrap_err();
        let chain = format!("{err:#}");
        assert!(chain.contains("does not advertise `--olean`"), "{chain}");
        assert!(chain.contains("no provisioned con-leche"), "{chain}");

        // 3. explicit selections never take the bundled binary, however capable.
        for req in [KernelEngineSelection::ConLeche, KernelEngineSelection::Both] {
            assert!(
                discover_con_leche_binary_for_selection_impl(
                    req,
                    PINNED_CON_LECHE_TOOLCHAIN,
                    Some(&ws),
                    Err(not_found()),
                    false,
                    Some(&elan),
                    olean_capable,
                    bridge_untracked,
                )
                .is_err(),
                "explicit {req} must not take the bundled binary"
            );
        }

        // 4. a set-but-invalid TURBO_CON_LECHE_BIN is a reported misconfiguration for auto too:
        //    no silent switch to the bundled binary, and the original error is preserved.
        let err = discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::Auto,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws),
            Err(anyhow::anyhow!("`TURBO_CON_LECHE_BIN` points to missing or non-executable")),
            true,
            Some(&elan),
            olean_capable,
            bridge_untracked,
        )
        .unwrap_err();
        assert!(err.to_string().contains("points to missing"));

        // 5. off the pinned toolchain the bundled binary is never consulted.
        assert!(discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::Auto,
            "leanprover/lean4:v4.36.0",
            Some(&ws),
            Err(not_found()),
            false,
            Some(&elan),
            olean_capable,
            bridge_untracked,
        )
        .is_err());

        // 6. a relative elan home never yields a bundled path (review 22ae951a F4).
        assert!(discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::Auto,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws),
            Err(not_found()),
            false,
            Some(Path::new("relative/elan")),
            olean_capable,
            bridge_untracked,
        )
        .is_err());

        // 7. a bundled binary under the checkout is rejected (review 22ae951a F4), before the
        //    capability probe is ever consulted: the injected probe panics if it runs
        //    (DA 388e906a F8).
        let ws2 = tmp.join("co");
        std::fs::create_dir_all(ws2.join(".git")).unwrap();
        let elan2 = ws2.join("elan");
        let bundled2 = elan2.join("toolchains/leanprover--lean4---v4.35.0/bin/con-leche");
        std::fs::create_dir_all(bundled2.parent().unwrap()).unwrap();
        write_exec(&bundled2);
        assert!(discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::Auto,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws2),
            Err(not_found()),
            false,
            Some(&elan2),
            &|_: &Path| -> bool {
                panic!("the in-checkout rejection must run before the capability probe")
            },
            bridge_untracked,
        )
        .is_err());

        // 8. a provisioned binary outside any checkout is accepted as-is, with pinned-rev
        //    provenance and no capability probe (the probe is for the bundled candidate only).
        let prov = tmp.join("prov").join("con-leche");
        std::fs::create_dir_all(prov.parent().unwrap()).unwrap();
        write_exec(&prov);
        let prov = prov.canonicalize().unwrap();
        let resolved = discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::ConLeche,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws),
            Ok(prov.clone()),
            true,
            None,
            olean_incapable,
            bridge_untracked,
        )
        .unwrap();
        assert_eq!(resolved.path, prov);
        assert_eq!(
            resolved.provenance,
            ConLecheBinaryProvenance::ProvisionedPinnedRev
        );

        // 9. a provisioned binary inside the checkout that is not that checkout's bridge binary
        //    is refused for explicit selections, and auto then tries the bundled binary
        //    explicitly (review 22ae951a F4: the bridge-rejected-then-None case).
        let inside = ws2.join("some").join("bin").join("con-leche");
        std::fs::create_dir_all(inside.parent().unwrap()).unwrap();
        write_exec(&inside);
        let inside = inside.canonicalize().unwrap();
        assert!(discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::Both,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws2),
            Ok(inside.clone()),
            false,
            Some(&elan),
            olean_capable,
            bridge_untracked,
        )
        .is_err());
        let resolved = discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::Auto,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws2),
            Ok(inside),
            false,
            Some(&elan),
            olean_capable,
            bridge_untracked,
        )
        .unwrap();
        assert_eq!(
            resolved.path,
            bundled.canonicalize().unwrap(),
            "auto must try the bundled binary when the identity gate rejects a discovered one"
        );
        assert_eq!(
            resolved.provenance,
            ConLecheBinaryProvenance::ToolchainBundledProbed
        );

        // 10. a bridge-path binary that is TRACKED in the checkout is refused (DA 388e906a F3):
        //     pr-verify materializes the head TREE, so committing the file is how a PR plants
        //     one; a legitimately built bridge binary is untracked build output.
        let bridge = ws2.join(BRIDGE_CON_LECHE_BIN_REL);
        std::fs::create_dir_all(bridge.parent().unwrap()).unwrap();
        write_exec(&bridge);
        let bridge = bridge.canonicalize().unwrap();
        let err = discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::ConLeche,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws2),
            Ok(bridge.clone()),
            false,
            None,
            olean_capable,
            &|_| Ok(true),
        )
        .unwrap_err();
        assert!(format!("{err:#}").contains("TRACKED"), "{err:#}");

        // 11. a tracked-check that cannot run fails closed.
        assert!(discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::ConLeche,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws2),
            Ok(bridge.clone()),
            false,
            None,
            olean_capable,
            &|_| Err(anyhow::anyhow!("git unavailable")),
        )
        .is_err());

        // 12. an untracked bridge binary stays accepted, with pinned-rev provenance.
        let resolved = discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::ConLeche,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws2),
            Ok(bridge.clone()),
            false,
            None,
            olean_capable,
            bridge_untracked,
        )
        .unwrap();
        assert_eq!(resolved.path, bridge);
        assert_eq!(
            resolved.provenance,
            ConLecheBinaryProvenance::ProvisionedPinnedRev
        );

        // 13. a provisioned binary that IS the toolchain-bundled candidate carries the bundled
        //     PROVISIONED provenance (DA 388e906a F1: classified by canonical path in ONE place;
        //     review b08785bc F2: the probe never ran on this path, so the marker must not claim
        //     it did).
        let resolved = discover_con_leche_binary_for_selection_impl(
            KernelEngineSelection::ConLeche,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws),
            Ok(bundled.canonicalize().unwrap()),
            true,
            Some(&elan),
            olean_incapable,
            bridge_untracked,
        )
        .unwrap();
        assert_eq!(resolved.path, bundled.canonicalize().unwrap());
        assert_eq!(
            resolved.provenance,
            ConLecheBinaryProvenance::ToolchainBundledProvisioned
        );
        assert_eq!(
            resolved.provenance.recorded_rev(),
            BUNDLED_CON_LECHE_PROVISIONED_MARKER
        );

        let _ = std::fs::remove_dir_all(&tmp);
    }

    #[test]
    fn test_kernel_auto_selects_bundled_con_leche_on_pinned_toolchain() {
        // G1c: `--kernel auto` performs the real support probe through the env-reading wrapper.
        // On the pinned toolchain with a bundled, --olean-capable binary under ELAN_HOME it
        // resolves con-leche with the probed bundled-provenance marker (never the unverified
        // pinned rev) whether or not the host carries a provisioned bridge binary (an
        // identity-rejected discovery falls back to the bundled binary); off the pin it resolves
        // standard; explicit selections keep failing closed on provisioned binaries only. Env
        // mutation is RAII-guarded and serialized under the crate's SHARED env lock
        // (DA 388e906a F6: a function-local lock serialized nothing against the other
        // env-mutating tests in this binary).
        let _env = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bin_guard = ScopedEnvVar::remove(CON_LECHE_BIN_ENV);

        let tmp = std::env::temp_dir().join(format!(
            "turbo_lean_g1c_elan_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let ws = tmp.join("ws");
        let elan = tmp.join("elan");
        let bin_dir = elan.join("toolchains/leanprover--lean4---v4.35.0/bin");
        std::fs::create_dir_all(&ws).unwrap();
        std::fs::create_dir_all(&bin_dir).unwrap();
        let _elan_guard = ScopedEnvVar::set("ELAN_HOME", elan.as_os_str());

        // No bundled binary yet: auto on the pinned toolchain stays standard, with a reason.
        let std_prov = resolve_kernel_engine_in_workspace(
            KernelEngineSelection::Auto,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws),
            BridgeNoGitPolicy::PlainDirIsUntracked,
        )
        .unwrap();
        assert_eq!(std_prov.kernel_engine, ResolvedKernelEngine::Standard);
        assert!(std_prov.fallback_reason.is_some());

        // A bundled executable whose --help does NOT advertise --olean (the live v4.35.0
        // toolchain's measured shape) fails the capability probe: auto stays standard with a
        // reason (G1c r2 capability gate).
        let bundled = bin_dir.join("con-leche");
        let make_bundled = |usage: &str| {
            std::fs::write(
                &bundled,
                format!("#!/bin/sh\nif [ \"$1\" = \"--help\" ]; then echo \"{usage}\"; fi\nexit 0\n"),
            )
            .unwrap();
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                std::fs::set_permissions(&bundled, std::fs::Permissions::from_mode(0o755))
                    .unwrap();
            }
        };
        make_bundled("usage: con-leche [--verified|--trusted] FILE.ndjson");
        let incapable_prov = resolve_kernel_engine_in_workspace(
            KernelEngineSelection::Auto,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws),
            BridgeNoGitPolicy::PlainDirIsUntracked,
        )
        .unwrap();
        assert_eq!(incapable_prov.kernel_engine, ResolvedKernelEngine::Standard);
        assert!(incapable_prov.fallback_reason.is_some());

        // Bundled executable advertising --olean: auto selects con-leche, recording the probed
        // bundled-provenance marker, no fallback.
        make_bundled("usage: con-leche [--verified|--trusted] [--olean] FILE.ndjson");
        let auto_prov = resolve_kernel_engine_in_workspace(
            KernelEngineSelection::Auto,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&ws),
            BridgeNoGitPolicy::PlainDirIsUntracked,
        )
        .unwrap();
        assert_eq!(
            auto_prov.kernel_engine,
            ResolvedKernelEngine::ConLeche,
            "auto on the pinned toolchain must select the bundled con-leche"
        );
        assert_eq!(
            auto_prov.con_leche_rev.as_deref(),
            Some(BUNDLED_CON_LECHE_PROVENANCE_MARKER)
        );
        assert_eq!(auto_prov.fallback_reason, None);
        // DA 388e906a F2: the resolved provenance carries the binary the executing sites run,
        // byte-pinned at selection (review b08785bc F3).
        let resolved = auto_prov
            .con_leche_binary
            .clone()
            .expect("a resolved con-leche engine carries its binary");
        assert_eq!(resolved.path, bundled.canonicalize().unwrap());
        assert_eq!(
            resolved.provenance,
            ConLecheBinaryProvenance::ToolchainBundledProbed
        );
        assert_eq!(resolved.blake3_hex.len(), 64);

        // Off the pinned toolchain the bundled binary is never consulted.
        let off_pin = resolve_kernel_engine_in_workspace(
            KernelEngineSelection::Auto,
            "leanprover/lean4:v4.36.0",
            Some(&ws),
            BridgeNoGitPolicy::PlainDirIsUntracked,
        )
        .unwrap();
        assert_eq!(off_pin.kernel_engine, ResolvedKernelEngine::Standard);

        // Explicit selections keep failing closed: the bundled binary does not provision them.
        for req in [KernelEngineSelection::ConLeche, KernelEngineSelection::Both] {
            let err = resolve_kernel_engine_in_workspace(
                req,
                PINNED_CON_LECHE_TOOLCHAIN,
                Some(&ws),
                BridgeNoGitPolicy::PlainDirIsUntracked,
            )
            .unwrap_err();
            assert!(
                err.to_string().contains("fail-closed kernel gate"),
                "explicit {req} must stay fail-closed with only the bundled binary present: {err:#}"
            );
        }

        let _ = std::fs::remove_dir_all(&tmp);
    }

    // Review 4f80161c U2: the no-`.git` outcome is the CALLER's policy, exercised on the real
    // tracked-check function, not an injected closure.
    #[test]
    fn bridge_tracked_check_policy_decides_plain_dirs() {
        let tmp = std::env::temp_dir().join(format!(
            "turbo-lean-nogit-policy-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&tmp).unwrap();
        // `check --emit-olean` shape: a tree without `.git` cannot have delivered the file.
        assert!(matches!(
            bridge_binary_is_tracked(&tmp, BridgeNoGitPolicy::PlainDirIsUntracked),
            Ok(false)
        ));
        // pr-verify / ci-verify shape: a checkout without `.git` fails the check closed.
        let err =
            bridge_binary_is_tracked(&tmp, BridgeNoGitPolicy::PlainDirFailsClosed).unwrap_err();
        assert!(
            err.to_string().contains("fails closed"),
            "the plain-dir refusal must name the fail-closed policy: {err:#}"
        );
        let _ = std::fs::remove_dir_all(&tmp);
    }

    // Review 4f80161c U3: the digest is taken from the opened handle and the runner executes
    // those bytes, so a swap between selection and execution, or a symlink planted at the
    // pinned path, is refused.
    #[test]
    fn execution_open_refuses_swapped_bytes_and_symlinks() {
        let tmp = std::env::temp_dir().join(format!("turbo-lean-swap-{}", std::process::id()));
        std::fs::create_dir_all(&tmp).unwrap();
        let bin = tmp.join("con-leche");
        std::fs::write(&bin, b"#!/bin/sh\nexit 0\n").unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&bin, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        let resolved =
            ResolvedConLecheBinary::resolve(&bin, ConLecheBinaryProvenance::ProvisionedPinnedRev)
                .unwrap();
        // Unchanged bytes verify and open.
        assert!(resolved.open_execution_verified().is_ok());
        // Bytes swapped after selection are refused at execution.
        std::fs::write(&bin, b"#!/bin/sh\nexit 1\n").unwrap();
        let err = resolved.open_execution_verified().unwrap_err();
        assert!(
            err.to_string()
                .contains("changed between selection and execution"),
            "a swapped binary must be refused: {err:#}"
        );
        // A symlink final component at the pinned path is refused by `O_NOFOLLOW`.
        #[cfg(unix)]
        {
            let target = tmp.join("elsewhere");
            std::fs::write(&target, b"#!/bin/sh\nexit 0\n").unwrap();
            std::fs::remove_file(&bin).unwrap();
            std::os::unix::fs::symlink(&target, &bin).unwrap();
            assert!(resolved.open_execution_verified().is_err());
        }
        let _ = std::fs::remove_dir_all(&tmp);
    }

    // Review 4f80161c U5: the REAL tracked gate (a real git index, the real `git ls-files`
    // check wired by `discover_con_leche_binary_for_selection_with_provenance`) refuses a
    // tree-delivered bridge binary, and that discovery cause reaches the explicit-selection
    // bail (DA b08785bc F6).
    #[test]
    fn real_tracked_gate_refuses_tree_delivered_bridge_binary() {
        let tmp = std::env::temp_dir().join(format!("turbo-lean-tracked-{}", std::process::id()));
        let co = tmp.join("checkout");
        let bridge = co.join(BRIDGE_CON_LECHE_BIN_REL);
        std::fs::create_dir_all(bridge.parent().unwrap()).unwrap();
        std::fs::write(&bridge, b"#!/bin/sh\nexit 0\n").unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&bridge, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        // An isolated ELAN_HOME, as in the bundled-binary test above, so no toolchain-bundled
        // binary can satisfy the selection in this environment.
        let elan = tmp.join("elan");
        std::fs::create_dir_all(&elan).unwrap();
        let _elan_guard = ScopedEnvVar::set("ELAN_HOME", elan.as_os_str());
        let git = |args: &[&str]| {
            let st = std::process::Command::new("git")
                .args(args)
                .current_dir(&co)
                .env("GIT_CONFIG_GLOBAL", "/dev/null")
                .env("GIT_CONFIG_SYSTEM", "/dev/null")
                .stdin(std::process::Stdio::null())
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .unwrap();
            assert!(st.success(), "git {args:?} failed");
        };
        git(&["init", "-q"]);
        // `git ls-files --error-unmatch` reads the index, so staging suffices to make the
        // bridge path tree-delivered.
        git(&["add", "--", BRIDGE_CON_LECHE_BIN_REL]);
        let err = discover_con_leche_binary_for_selection_with_provenance(
            KernelEngineSelection::ConLeche,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&co),
            BridgeNoGitPolicy::PlainDirFailsClosed,
        )
        .unwrap_err();
        assert!(
            format!("{err:#}").contains("TRACKED in checkout"),
            "the real tracked gate must refuse a tree-delivered bridge binary: {err:#}"
        );
        let gate_err = resolve_kernel_engine_in_workspace(
            KernelEngineSelection::ConLeche,
            PINNED_CON_LECHE_TOOLCHAIN,
            Some(&co),
            BridgeNoGitPolicy::PlainDirFailsClosed,
        )
        .unwrap_err();
        let msg = format!("{gate_err:#}");
        assert!(
            msg.contains("fail-closed kernel gate") && msg.contains("TRACKED in checkout"),
            "the discovery cause must reach the explicit-selection bail: {msg}"
        );
        let _ = std::fs::remove_dir_all(&tmp);
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
        type PostureMap = BTreeMap<String, Vec<CompiledCsimpObservation>>;
        let fixture = transitive_csimp_fixture();
        let posture =
            scan_transitive_csimp_posture("Root", |m| Ok(fixture.get(m).cloned())).unwrap();
        let base = posture.digest.clone();

        // Duplicating an observation, or re-inserting modules in another order, is digest-neutral.
        let mut duplicated = posture.modules.clone();
        let dep = duplicated.get_mut("DepGlobal").unwrap();
        dep.push(dep[0].clone());
        assert_eq!(compute_transitive_csimp_posture_digest("Root", &duplicated), base);
        let reordered: PostureMap = posture
            .modules
            .iter()
            .rev()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        assert_eq!(compute_transitive_csimp_posture_digest("Root", &reordered), base);

        // Every canonical field is content-bound.
        let mutations: Vec<Box<dyn Fn(&mut PostureMap)>> = vec![
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
