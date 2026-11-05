use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::path::Path;
use std::str::FromStr;

pub const KERNEL_ENGINE_ENV: &str = "TURBO_LEAN_KERNEL_ENGINE";
pub const KERNEL_ENGINE_FROM_CONFIG_ENV: &str = "TURBO_LEAN_KERNEL_ENGINE_FROM_CONFIG";

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
    let lean_toolchain = normalize_lean_toolchain(lean_toolchain);
    let probed_con_leche_rev = probe_con_leche_support(&lean_toolchain);
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

#[cfg(test)]
mod tests {
    use super::*;

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
}
