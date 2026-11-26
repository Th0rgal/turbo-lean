use super::*;

/// Glob specification for a `lean_lib` target (`Glob.one`, `Glob.submodules`, `Glob.andSubmodules`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum GlobSpec {
    One(String),
    Submodules(String),
    AndSubmodules(String),
}
/// One component of a Lean `Name` (`Name.str` or `Name.num`), preserving structural distinction.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LeanNamePart {
    Str(String),
    Num(u64),
}
/// Structural Lean `Name` ordered by `Lean.Name.quickCmp` (`hash` first, then `quickCmpAux`).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct LeanName(pub Vec<LeanNamePart>);
/// Typed `Lean.LeanOptionValue` (`ofBool` | `ofNat` | `ofString`).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "k", content = "v")]
pub enum LeanOptionValue {
    Bool(bool),
    Nat(u64),
    Str(String),
}
pub type LeanOptionsMap = BTreeMap<LeanName, LeanOptionValue>;
impl Serialize for LeanName {
    fn serialize<S: serde::Serializer>(
        &self,
        serializer: S,
    ) -> std::result::Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}
impl<'de> Deserialize<'de> for LeanName {
    fn deserialize<D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> std::result::Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Repr {
            Parts(Vec<LeanNamePart>),
            Legacy(String),
        }
        match Repr::deserialize(deserializer)? {
            Repr::Parts(parts) => Ok(LeanName(parts)),
            Repr::Legacy(s) => LeanName::from_str_to_name(&s).map_err(serde::de::Error::custom),
        }
    }
}
impl LeanOptionValue {
    /// `LeanOptionValue.asCliFlagValue`: strings wrap in `"..."` with NO backslash escaping.
    pub fn as_cli_flag_value(&self) -> String {
        match self {
            LeanOptionValue::Bool(b) => b.to_string(),
            LeanOptionValue::Nat(n) => n.to_string(),
            LeanOptionValue::Str(s) => format!("\"{s}\""),
        }
    }
    /// Raw CLI value for flat `-D` invocation without `setup.json`.
    pub fn raw_cli_value(&self) -> String {
        match self {
            LeanOptionValue::Bool(b) => b.to_string(),
            LeanOptionValue::Nat(n) => n.to_string(),
            LeanOptionValue::Str(s) => s.clone(),
        }
    }
    pub fn to_json_value(&self) -> serde_json::Value {
        match self {
            LeanOptionValue::Bool(b) => serde_json::Value::Bool(*b),
            LeanOptionValue::Nat(n) => serde_json::Value::Number((*n).into()),
            LeanOptionValue::Str(s) => serde_json::Value::String(s.clone()),
        }
    }
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
    pub lean_options: LeanOptionsMap,
    pub precompile_modules: Option<bool>,
    /// `platformIndependent` (`None` = unset, `Some(false)` traces the platform, `Some(true)` drops
    /// platform-dependent inputs).
    #[serde(default)]
    pub platform_independent: Option<bool>,
    pub default_facets: Vec<String>,
    pub is_default_target: bool,
    /// `needs := #[...]`: names of the package's `input_file` / `input_dir` targets.
    #[serde(default)]
    pub needs: Vec<String>,
    /// Names of package `target ...` custom targets declared in `needs := #[...]` (dependency packages).
    #[serde(default)]
    pub custom_target_needs: Vec<String>,
    /// Why turbo-lean cannot build this dependency target like Lake (see `PackageConfig`).
    #[serde(default)]
    pub unsupported: Option<String>,
    /// Native C-compilation setting (`buildType`, `moreLeancArgs`, `weakLeancArgs`) turbo-lean does not mirror.
    #[serde(default)]
    pub native_unsupported: Option<String>,
    /// Shared/dynlib linker setting (`moreLinkObjs`, `moreLinkLibs`, `moreLinkArgs`, `weakLinkArgs`, `libName`, `libPrefixOnWindows`).
    #[serde(default)]
    pub link_unsupported: Option<String>,
}
/// Static `input_file` / `input_dir` target (Lake's declarative file inputs).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InputTargetConfig {
    pub name: String,
    pub path: PathBuf,
    pub is_dir: bool,
    /// `filter := .extension "<ext>"` of an `input_dir`; `None` selects every file.
    pub extension: Option<String>,
    /// `filter := .extension <| .mem #[...]` of an `input_dir`; when `Some`, matches any listed extension.
    #[serde(default)]
    pub extensions: Option<Vec<String>>,
    pub text: bool,
    /// BLAKE3 of the selected files (relative paths and contents), folded into the module cache
    /// key of every module a `needs`-ing library can build.
    pub blake3: String,
    /// Lake's own 16-hex file hash of the same files (an `input_dir` folds them left-to-right),
    /// so the `.trace` files written here keep matching Lake's `extraDep` trace.
    pub lake_hash: String,
    /// Why turbo-lean cannot read this dependency's input the way Lake does: an unknown field, or
    /// a `filter` that is not `.extension "<ext>"`. The root package fails closed at parse time
    /// instead (see `unsupported_lake_field`); for a dependency this is promoted onto
    /// `PackageConfig::unsupported` by `finalize_package_config` and fails closed (`Err`) in
    /// `module_lake_input_digest`, `workspace_lake_inputs_digest`, and `try_project_lake_inputs_tag`.
    #[serde(default)]
    pub unsupported: Option<String>,
}

impl InputTargetConfig {
    pub fn matches_extension(&self, ext: Option<&std::ffi::OsStr>) -> bool {
        if let Some(ref exts) = self.extensions {
            return ext
                .and_then(|s| s.to_str())
                .is_some_and(|s| exts.iter().any(|w| w == s));
        }
        match &self.extension {
            Some(want) => ext == Some(std::ffi::OsStr::new(want)),
            None => true,
        }
    }
}
/// Static configuration of a `lean_exe` target.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeanExeConfig {
    pub name: String,
    #[serde(default)]
    pub exe_name: Option<String>,
    pub src_dir: Option<PathBuf>,
    pub root: String,
    pub support_interpreter: bool,
    pub more_lean_args: Vec<String>,
    pub weak_lean_args: Vec<String>,
    pub lean_options: LeanOptionsMap,
    /// `platformIndependent` (`None` = unset, `Some(false)` traces the platform, `Some(true)` drops
    /// platform-dependent inputs).
    #[serde(default)]
    pub platform_independent: Option<bool>,
    pub is_default_target: bool,
    /// Names of package `input_file` / `input_dir` targets declared in `needs := #[...]`.
    #[serde(default)]
    pub needs: Vec<String>,
    #[serde(default)]
    pub custom_target_needs: Vec<String>,
    #[serde(default)]
    pub unsupported: Option<String>,
    #[serde(default)]
    pub native_unsupported: Option<String>,
    #[serde(default)]
    pub link_unsupported: Option<String>,
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
pub(super) fn default_bin_dir() -> PathBuf {
    PathBuf::from("bin")
}

/// Canonical static configuration for a single Lake package (root or dependency).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PackageConfig {
    /// Lake `origName`: the name the lakefile declares (directory name when it declares none).
    pub name: String,
    /// Lake `baseName`: the manifest's package name when the manifest loaded the package, else
    /// `name`. Target specs and trace captions address a package by this name.
    #[serde(default)]
    pub base_name: String,
    pub pkg_root: PathBuf,
    pub config_file_kind: String,
    pub src_dir: PathBuf,
    pub build_dir: PathBuf,
    #[serde(default = "default_bin_dir")]
    pub bin_dir: PathBuf,
    pub lean_lib_dir: PathBuf,
    pub native_lib_dir: PathBuf,
    pub ir_dir: PathBuf,
    pub packages_dir: PathBuf,
    pub more_lean_args: Vec<String>,
    pub weak_lean_args: Vec<String>,
    pub lean_options: LeanOptionsMap,
    pub precompile_modules: bool,
    /// `platformIndependent` (`None` = unset, `Some(false)` traces the platform, `Some(true)` drops
    /// platform-dependent inputs).
    #[serde(default)]
    pub platform_independent: Option<bool>,
    pub default_targets: Vec<String>,
    pub libs: Vec<LeanLibConfig>,
    pub exes: Vec<LeanExeConfig>,
    pub extern_libs: Vec<ExternLibConfig>,
    pub custom_targets: Vec<String>,
    #[serde(default)]
    pub inputs: Vec<InputTargetConfig>,
    pub config_digest: String,
    #[serde(default)]
    pub(crate) pre_recipe_config_digest: String,
    /// Why turbo-lean cannot build this dependency's modules like Lake (a compile-affecting
    /// setting it does not mirror). A root package fails to parse instead; a dependency can
    /// still be used through Lake's own fresh build outputs.
    #[serde(default)]
    pub unsupported: Option<String>,
    #[serde(default)]
    pub native_unsupported: Option<String>,
    #[serde(default)]
    pub link_unsupported: Option<String>,
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
    pub is_untrusted: bool,
}
/// A single parsed import directive with Lake v4.35 module-system visibility flags.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParsedImport {
    pub module: String,
    pub is_exported: bool,
    pub is_meta: bool,
    pub import_all: bool,
}
/// Parsed header metadata from a `.lean` module file, aligned with Lean v4.35 `Lean.ParseImports`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct HeaderInfo {
    pub is_module: bool,
    pub has_prelude: bool,
    pub has_c_export: bool,
    pub body_byte_offset: usize,
    pub header_error: Option<String>,
    pub imports: Vec<String>,
    pub import_specs: Vec<ParsedImport>,
}
/// A single module node in the resolved compilation DAG.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleNode {
    pub module_name: String,
    /// Lake `Package.id?` / `origName`.
    pub pkg_name: String,
    /// Lake `Package.baseName`: the manifest's name for the package, else `pkg_name`.
    #[serde(default)]
    pub pkg_base_name: String,
    pub target_name: String,
    pub is_root_pkg: bool,
    pub pkg_root: PathBuf,
    pub src_root: PathBuf,
    pub src_path: PathBuf,
    pub build_lib_lean_dir: PathBuf,
    pub build_native_lib_dir: PathBuf,
    pub build_ir_dir: PathBuf,
    pub olean_path: PathBuf,
    pub ilean_path: PathBuf,
    pub c_path: PathBuf,
    pub is_module: bool,
    pub has_prelude: bool,
    pub needs_c: bool,
    pub needs_co_export: bool,
    pub needs_dynlib: bool,
    pub precompile_modules: bool,
    #[serde(default)]
    pub is_exe_target: bool,
    /// Effective `platformIndependent`: the target's value, else the package's.
    #[serde(default)]
    pub platform_independent: Option<bool>,
    #[serde(default)]
    pub import_specs: Vec<ParsedImport>,
    #[serde(default)]
    pub lean_options: LeanOptionsMap,
    pub strong_args: Vec<String>,
    pub weak_args: Vec<String>,
    pub src_blake3: String,
    pub direct_dag_deps: Vec<String>,
    pub external_olean_deps: Vec<(String, PathBuf)>,
    /// Source-less prebuilt `.olean`s among `external_olean_deps` (no replay provenance).
    #[serde(default)]
    pub prebuilt_olean_deps: Vec<String>,
    pub expected_all_deps: Vec<String>,
    pub extern_lib_digests: Vec<String>,
    pub pkg_config_digest: String,
    #[serde(default)]
    pub native_unsupported: Option<String>,
    #[serde(default)]
    pub link_unsupported: Option<String>,
}
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SharedLibSpec {
    pub pkg_name: String,
    #[serde(default)]
    pub pkg_base_name: String,
    #[serde(default)]
    pub pkg_root: PathBuf,
    pub lib_name: String,
    pub stem: String,
    pub path: PathBuf,
    pub is_plugin: bool,
    pub local_modules: Vec<String>,
}
/// Deterministic Module DAG with topological waves.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModuleDag {
    pub nodes: BTreeMap<String, ModuleNode>,
    pub topological_order: Vec<String>,
    pub waves: Vec<Vec<String>>,
    pub root_modules: Vec<String>,
    #[serde(default)]
    pub shared_libs: Vec<SharedLibSpec>,
}
/// Summary report returned by `build_project_modules_native`.
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
#[inline]
pub(super) fn is_lean_letter_like(c: char) -> bool {
    let v = c as u32;
    ((0x3b1..=0x3c9).contains(&v) && v != 0x3bb)
        || ((0x391..=0x3a9).contains(&v) && v != 0x3a0 && v != 0x3a3)
        || (0x3ca..=0x3fb).contains(&v)
        || (0x1f00..=0x1ffe).contains(&v)
        || (0x2100..=0x214f).contains(&v)
        || (0x1d49c..=0x1d59f).contains(&v)
        || ((0x00c0..=0x00ff).contains(&v) && v != 0x00d7 && v != 0x00f7)
        || (0x0100..=0x017f).contains(&v)
}

#[inline]
pub(super) fn is_lean_subscript_alnum(c: char) -> bool {
    let v = c as u32;
    (0x2080..=0x2089).contains(&v)
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
        || v == 0x2c7c
}

#[inline]
pub(super) fn is_lean_id_first(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || is_lean_letter_like(c)
}

#[inline]
pub(super) fn is_lean_id_rest(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || c == '_'
        || c == '\''
        || c == '!'
        || c == '?'
        || is_lean_letter_like(c)
        || is_lean_subscript_alnum(c)
}

impl LeanName {
    pub fn from_strs<I, S>(parts: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        LeanName(
            parts
                .into_iter()
                .map(|s| LeanNamePart::Str(s.into()))
                .collect(),
        )
    }

    /// `Lean.Name.hash` (`Init/Prelude.lean:4887`).
    pub fn lean_hash(&self) -> u64 {
        let mut h = 1723u64;
        for p in &self.0 {
            let k = match p {
                LeanNamePart::Str(s) => lake_murmur64a(s.as_bytes(), 11),
                LeanNamePart::Num(v) => *v,
            };
            h = lake_mix_hash(h, k);
        }
        h
    }

    pub fn has_macro_scopes(&self) -> bool {
        let mut idx = self.0.len();
        while idx > 0 {
            match &self.0[idx - 1] {
                LeanNamePart::Str(s) => return s == "_hyg",
                LeanNamePart::Num(_) => idx -= 1,
            }
        }
        false
    }

    pub fn is_inaccessible_user_name(&self) -> bool {
        self.0.iter().any(|p| match p {
            LeanNamePart::Str(s) => s.contains('✝') || s == "_inaccessible",
            LeanNamePart::Num(_) => false,
        })
    }

    pub fn maybe_pseudo_syntax(&self) -> bool {
        if self.0.len() == 1 && matches!(&self.0[0], LeanNamePart::Str(s) if s == "_") {
            return true;
        }
        matches!(self.0.first(), Some(LeanNamePart::Str(s)) if s.starts_with('#') || s.starts_with('?'))
    }

    pub(super) fn escape_part(s: &str, force: bool) -> String {
        let mut chars = s.chars();
        if let Some(first) = chars.next() {
            if !force && is_lean_id_first(first) && chars.all(is_lean_id_rest) {
                return s.to_string();
            }
            if s.contains('»') {
                return s.to_string();
            }
        }
        format!("«{s}»")
    }

    /// `Lean.Name.toString` (`escape = true`, `isToken = fun _ => false`).
    pub fn to_lean_string(&self) -> String {
        if self.0.is_empty() {
            return "[anonymous]".to_string();
        }
        let escape = !self.is_inaccessible_user_name()
            && !self.has_macro_scopes()
            && !self.maybe_pseudo_syntax();
        let mut out = String::new();
        for (i, p) in self.0.iter().enumerate() {
            if i > 0 {
                out.push('.');
            }
            match p {
                LeanNamePart::Str(s) => {
                    if escape {
                        out.push_str(&Self::escape_part(s, false));
                    } else {
                        out.push_str(s);
                    }
                }
                LeanNamePart::Num(v) => out.push_str(&v.to_string()),
            }
        }
        out
    }

    /// Parse `String.toName` (`Init/Meta/Defs.lean:1187-1239`).
    pub fn from_str_to_name(s: &str) -> Result<Self> {
        if s.is_empty() {
            anyhow::bail!("Empty Lean option name");
        }
        let mut parts = Vec::new();
        let mut rem = s;
        loop {
            let Some(curr) = rem.chars().next() else {
                anyhow::bail!("Trailing `.` in Lean name `{s}`");
            };
            if curr == '«' {
                let after_open = &rem['«'.len_utf8()..];
                let Some(end_idx) = after_open.find('»') else {
                    anyhow::bail!("Unterminated `«` in Lean name `{s}`");
                };
                let inner = &after_open[..end_idx];
                parts.push(LeanNamePart::Str(inner.to_string()));
                rem = &after_open[end_idx + '»'.len_utf8()..];
            } else if is_lean_id_first(curr) {
                let len: usize = rem
                    .chars()
                    .take_while(|&c| is_lean_id_rest(c))
                    .map(char::len_utf8)
                    .sum();
                parts.push(LeanNamePart::Str(rem[..len].to_string()));
                rem = &rem[len..];
            } else if curr.is_ascii_digit() {
                let len: usize = rem
                    .chars()
                    .take_while(|c| c.is_ascii_digit())
                    .map(char::len_utf8)
                    .sum();
                let digits = &rem[..len];
                let val: u64 = digits.parse().map_err(|_| {
                    anyhow::anyhow!("Numeric Lean name part `{digits}` overflows u64")
                })?;
                parts.push(LeanNamePart::Num(val));
                rem = &rem[len..];
            } else {
                anyhow::bail!("Invalid Lean name `{s}`");
            }
            if rem.is_empty() {
                break;
            }
            if let Some(after_dot) = rem.strip_prefix('.') {
                rem = after_dot;
            } else {
                anyhow::bail!("Invalid Lean name `{s}`");
            }
        }
        Ok(LeanName(parts))
    }

    /// Parse a backtick literal `` `... `` per `Lean.Parser.identFnAux` (`Lean/Parser/Basic.lean:975-1025`).
    pub fn from_backtick_literal(raw: &str) -> Result<Self> {
        let raw = raw.trim();
        let Some(mut rem) = raw.strip_prefix('`') else {
            anyhow::bail!("Unsupported non-literal `leanOptions` name `{raw}` in lakefile.lean");
        };
        if rem.is_empty() || rem.starts_with('`') {
            anyhow::bail!("Unsupported non-literal `leanOptions` name `{raw}` in lakefile.lean");
        }
        let mut parts = Vec::new();
        loop {
            let Some(curr) = rem.chars().next() else {
                anyhow::bail!(
                    "Unsupported non-literal `leanOptions` name `{raw}` in lakefile.lean"
                );
            };
            if curr == '«' {
                let after_open = &rem['«'.len_utf8()..];
                let Some(end_idx) = after_open.find('»') else {
                    anyhow::bail!("Unterminated `«` in `{raw}` in lakefile.lean");
                };
                parts.push(LeanNamePart::Str(after_open[..end_idx].to_string()));
                rem = &after_open[end_idx + '»'.len_utf8()..];
            } else if is_lean_id_first(curr) {
                let len: usize = rem
                    .chars()
                    .take_while(|&c| is_lean_id_rest(c))
                    .map(char::len_utf8)
                    .sum();
                parts.push(LeanNamePart::Str(rem[..len].to_string()));
                rem = &rem[len..];
            } else {
                anyhow::bail!(
                    "Unsupported non-literal `leanOptions` name `{raw}` in lakefile.lean"
                );
            }
            if rem.is_empty() {
                break;
            }
            if let Some(after_dot) = rem.strip_prefix('.') {
                rem = after_dot;
            } else {
                anyhow::bail!(
                    "Unsupported non-literal `leanOptions` name `{raw}` in lakefile.lean"
                );
            }
        }
        Ok(LeanName(parts))
    }

    pub fn with_weak_prefix(&self) -> Self {
        let mut out = Vec::with_capacity(self.0.len() + 1);
        out.push(LeanNamePart::Str("weak".to_string()));
        out.extend(self.0.iter().cloned());
        LeanName(out)
    }

    pub(super) fn quick_cmp_aux(a: &[LeanNamePart], b: &[LeanNamePart]) -> std::cmp::Ordering {
        use std::cmp::Ordering;
        match (a.split_last(), b.split_last()) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some((LeanNamePart::Num(_), _)), Some((LeanNamePart::Str(_), _))) => Ordering::Less,
            (Some((LeanNamePart::Str(_), _)), Some((LeanNamePart::Num(_), _))) => Ordering::Greater,
            (Some((LeanNamePart::Num(v1), p1)), Some((LeanNamePart::Num(v2), p2))) => {
                v1.cmp(v2).then_with(|| Self::quick_cmp_aux(p1, p2))
            }
            (Some((LeanNamePart::Str(s1), p1)), Some((LeanNamePart::Str(s2), p2))) => s1
                .as_bytes()
                .cmp(s2.as_bytes())
                .then_with(|| Self::quick_cmp_aux(p1, p2)),
        }
    }
}

impl Ord for LeanName {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.lean_hash()
            .cmp(&other.lean_hash())
            .then_with(|| Self::quick_cmp_aux(&self.0, &other.0))
    }
}

impl PartialOrd for LeanName {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[inline]
pub(super) fn is_lean_header_ws(c: char) -> bool {
    c == ' ' || c == '\r' || c == '\n'
}

pub(super) fn skip_parse_imports_whitespace(src: &str, mut pos: usize) -> std::result::Result<usize, String> {
    let bytes = src.as_bytes();
    while pos < bytes.len() {
        let ch = src[pos..].chars().next().unwrap();
        if ch == '\t' {
            return Err(
                "tabs are not allowed; please configure your editor to expand them".to_string(),
            );
        }
        if is_lean_header_ws(ch) {
            pos += ch.len_utf8();
            continue;
        }
        if ch == '-' && pos + 1 < bytes.len() && bytes[pos + 1] == b'-' {
            pos += 2;
            while pos < bytes.len() && bytes[pos] != b'\n' {
                pos += 1;
            }
            continue;
        }
        if ch == '/' && pos + 1 < bytes.len() && bytes[pos + 1] == b'-' {
            let after_open = pos + 2;
            let next_ch = src[after_open..].chars().next();
            if matches!(next_ch, Some('-') | Some('!')) {
                break;
            }
            pos = after_open;
            let mut nesting = 1usize;
            while nesting > 0 {
                if pos >= bytes.len() {
                    return Err("unterminated comment".to_string());
                }
                let c = src[pos..].chars().next().unwrap();
                pos += c.len_utf8();
                if c == '-' && pos < bytes.len() && bytes[pos] == b'/' {
                    pos += 1;
                    nesting -= 1;
                } else if c == '/' && pos < bytes.len() && bytes[pos] == b'-' {
                    pos += 1;
                    nesting += 1;
                }
            }
            continue;
        }
        break;
    }
    Ok(pos)
}

pub(super) fn match_parse_imports_keyword(
    src: &str,
    pos: usize,
    kw: &str,
) -> std::result::Result<Option<usize>, String> {
    if !src[pos..].starts_with(kw) {
        return Ok(None);
    }
    skip_parse_imports_whitespace(src, pos + kw.len()).map(Some)
}

#[inline]
pub(super) fn lean_name_part_needs_no_escape(part: &str) -> bool {
    let mut chars = part.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    is_lean_id_first(first) && chars.all(is_lean_id_rest)
}

#[inline]
pub(super) fn format_lean_name_part(raw_part: &str) -> String {
    if lean_name_part_needs_no_escape(raw_part) || raw_part.contains('»') {
        raw_part.to_string()
    } else {
        format!("«{}»", raw_part)
    }
}

/// Convert a dot-separated Lean `Name.toString` module identifier (possibly containing
/// `«...»`-escaped segments) into its unescaped filesystem slash path (`Lean.modToFilePath`).
pub fn module_name_to_rel_slash(mod_name: &str) -> String {
    let mut segs: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut in_escape = false;
    for ch in mod_name.chars() {
        if ch == '«' && !in_escape {
            in_escape = true;
        } else if ch == '»' && in_escape {
            in_escape = false;
        } else if ch == '.' && !in_escape {
            if !cur.is_empty() {
                segs.push(std::mem::take(&mut cur));
            }
        } else {
            cur.push(ch);
        }
    }
    if !cur.is_empty() {
        segs.push(cur);
    }
    segs.join("/")
}

/// Resolve `mod_name` along `search_dirs` matching Lean's `findOLean` (`findWithExt`):
/// the first directory containing the module's root package (`<pkg>/` or `<pkg>.olean`) wins,
/// and `<rel>.olean` is looked up only inside that winning directory.
pub(crate) fn resolve_olean_along_search_dirs<P: AsRef<Path>>(
    search_dirs: &[P],
    mod_name: &str,
) -> Option<PathBuf> {
    let rel = module_name_to_rel_slash(mod_name);
    let pkg = rel.split('/').next().unwrap_or_default();
    if pkg.is_empty() {
        return None;
    }
    let pkg_olean = format!("{pkg}.olean");
    let root = search_dirs
        .iter()
        .map(AsRef::as_ref)
        .find(|d| d.join(pkg).is_dir() || d.join(&pkg_olean).exists())?;
    Some(root.join(format!("{rel}.olean"))).filter(|p| p.is_file())
}

/// Format raw filesystem path components into a round-trippable `Lean.Name.toString` module name.
pub fn format_lean_module_name_from_parts<'a, I: IntoIterator<Item = &'a str>>(parts: I) -> String {
    parts
        .into_iter()
        .filter(|p| !p.is_empty())
        .map(format_lean_name_part)
        .collect::<Vec<_>>()
        .join(".")
}

pub(super) fn parse_module_ident_at(
    src: &str,
    mut pos: usize,
) -> std::result::Result<(String, usize), String> {
    let mut parts: Vec<String> = Vec::new();
    loop {
        if pos >= src.len() {
            return Err("unexpected end of input".to_string());
        }
        let curr = src[pos..].chars().next().unwrap();
        if curr == '«' {
            let start_part = pos + curr.len_utf8();
            let Some(rel_end) = src[start_part..].find('»') else {
                return Err("unterminated identifier escape".to_string());
            };
            let stop_part = start_part + rel_end;
            parts.push(format_lean_name_part(&src[start_part..stop_part]));
            pos = stop_part + '»'.len_utf8();
        } else if is_lean_id_first(curr) {
            let start_part = pos;
            pos += curr.len_utf8();
            while let Some(c) = src[pos..].chars().next() {
                if is_lean_id_rest(c) {
                    pos += c.len_utf8();
                } else {
                    break;
                }
            }
            parts.push(src[start_part..pos].to_string());
        } else {
            return Err("expected identifier".to_string());
        }

        if src[pos..].starts_with('.') {
            let after_dot = pos + 1;
            if let Some(nc) = src[after_dot..].chars().next() {
                if is_lean_id_first(nc) || nc == '«' {
                    pos = after_dot;
                    continue;
                }
            }
        }
        break;
    }
    let next_pos = skip_parse_imports_whitespace(src, pos)?;
    Ok((parts.join("."), next_pos))
}

/// Exact Lean v4.35 `Lean.ParseImports` (`ParseImportsFast.lean` + `Lean.Parser.Module`) header parser:
/// handles `module`, `prelude` (and implicit `Init` + `meta Init` when `prelude` is omitted),
/// per-import visibility modifiers (`public`, `meta`, `all`), duplicate imports with distinct flags,
/// strict termination at the first non-header token (including `;`, doc comments `/--`/`/-!`, attributes, etc.),
/// and rejects illegal modifiers (`public`/`meta`/`all` without `module`, or `public import all`).
pub fn parse_header_info(src: &str) -> HeaderInfo {
    let clean = splitter::strip_lean_comments(src);
    let has_c_export = clean.contains("@[export ")
        || clean.contains("@[inline, export ")
        || clean.contains(", export ");
    let mut info = HeaderInfo {
        is_module: false,
        has_prelude: false,
        has_c_export,
        body_byte_offset: 0,
        header_error: None,
        imports: Vec::new(),
        import_specs: Vec::new(),
    };

    let mut pos = match skip_parse_imports_whitespace(src, 0) {
        Ok(p) => p,
        Err(e) => {
            info.header_error = Some(e);
            return info;
        }
    };

    match match_parse_imports_keyword(src, pos, "module") {
        Ok(Some(next_pos)) => {
            info.is_module = true;
            pos = next_pos;
        }
        Ok(None) => {}
        Err(e) => {
            info.header_error = Some(e);
            return info;
        }
    }

    match match_parse_imports_keyword(src, pos, "prelude") {
        Ok(Some(next_pos)) => {
            info.has_prelude = true;
            pos = next_pos;
        }
        Ok(None) => {
            info.has_prelude = false;
            info.imports.push("Init".to_string());
            info.import_specs.push(ParsedImport {
                module: "Init".to_string(),
                is_exported: true,
                is_meta: false,
                import_all: false,
            });
            info.import_specs.push(ParsedImport {
                module: "Init".to_string(),
                is_exported: true,
                is_meta: true,
                import_all: false,
            });
        }
        Err(e) => {
            info.header_error = Some(e);
            return info;
        }
    }

    let mut seen_imports: HashSet<String> = info.imports.iter().cloned().collect();

    loop {
        let mut p = pos;
        let mut has_public = false;
        let mut has_meta = false;

        match match_parse_imports_keyword(src, p, "public") {
            Ok(Some(np)) => {
                has_public = true;
                p = np;
            }
            Ok(None) => {}
            Err(e) => {
                if !has_public {
                    break;
                }
                info.header_error = Some(e);
                return info;
            }
        }
        match match_parse_imports_keyword(src, p, "meta") {
            Ok(Some(np)) => {
                has_meta = true;
                p = np;
            }
            Ok(None) => {}
            Err(_) => {
                break;
            }
        }
        let after_import = match match_parse_imports_keyword(src, p, "import") {
            Ok(Some(np)) => np,
            Ok(None) | Err(_) => break,
        };

        let mut has_all = false;
        let after_all = match match_parse_imports_keyword(src, after_import, "all") {
            Ok(Some(np)) => {
                has_all = true;
                np
            }
            Ok(None) => after_import,
            Err(e) => {
                info.header_error = Some(e);
                return info;
            }
        };

        let (mod_name, next_pos) = match parse_module_ident_at(src, after_all) {
            Ok(pair) => pair,
            Err(e) => {
                info.header_error = Some(e);
                return info;
            }
        };

        if !info.is_module && (has_public || has_meta || has_all) {
            info.header_error =
                Some("cannot use 'public', 'meta', or 'all' without 'module'".to_string());
            return info;
        }
        if info.is_module && has_public && has_all {
            info.header_error = Some("cannot use `all` with `public import`".to_string());
            return info;
        }

        if seen_imports.insert(mod_name.clone()) {
            info.imports.push(mod_name.clone());
        }
        info.import_specs.push(ParsedImport {
            module: mod_name,
            is_exported: !info.is_module || has_public,
            is_meta: has_meta,
            import_all: has_all,
        });
        pos = next_pos;
    }

    info.body_byte_offset = pos;
    info
}
/// Comment-safe replacement for `lake_build::parse_header_imports`.
pub fn parse_header_imports(src: &str) -> Vec<String> {
    parse_header_info(src).imports
}

pub(super) fn read_le_u64_at(bytes: &[u8], off: usize) -> Option<u64> {
    let slice = bytes.get(off..off.checked_add(8)?)?;
    Some(u64::from_le_bytes(slice.try_into().ok()?))
}

pub(super) fn read_olean_name_at(bytes: &[u8], base_addr: u64, mut ptr: u64) -> Option<String> {
    let mut rev_parts: Vec<String> = Vec::new();
    let mut depth = 0usize;
    while ptr != 1 {
        depth += 1;
        if depth > 256 || (ptr & 1) != 0 || ptr < base_addr {
            return None;
        }
        let off = usize::try_from(ptr - base_addr).ok()?;
        let tag = *bytes.get(off.checked_add(7)?)?;
        match tag {
            1 => {
                let pre_ptr = read_le_u64_at(bytes, off.checked_add(8)?)?;
                let str_ptr = read_le_u64_at(bytes, off.checked_add(16)?)?;
                if (str_ptr & 1) != 0 || str_ptr < base_addr {
                    return None;
                }
                let str_off = usize::try_from(str_ptr - base_addr).ok()?;
                if *bytes.get(str_off.checked_add(7)?)? != 249 {
                    return None;
                }
                let m_size =
                    usize::try_from(read_le_u64_at(bytes, str_off.checked_add(8)?)?).ok()?;
                if m_size == 0 {
                    return None;
                }
                let data_start = str_off.checked_add(32)?;
                let data_end = data_start.checked_add(m_size - 1)?;
                let raw_part = std::str::from_utf8(bytes.get(data_start..data_end)?).ok()?;
                rev_parts.push(format_lean_name_part(raw_part));
                ptr = pre_ptr;
            }
            2 => {
                let pre_ptr = read_le_u64_at(bytes, off.checked_add(8)?)?;
                let num_ptr = read_le_u64_at(bytes, off.checked_add(16)?)?;
                if (num_ptr & 1) == 1 {
                    rev_parts.push((num_ptr >> 1).to_string());
                } else {
                    return None;
                }
                ptr = pre_ptr;
            }
            _ => return None,
        }
    }
    if rev_parts.is_empty() {
        return None;
    }
    rev_parts.reverse();
    Some(rev_parts.join("."))
}

/// Parse `(imports, is_module)` directly from a Lean v4 `.olean` binary header/heap
/// (`ModuleData` root object), enabling transitive dependency discovery even when `.lean`
/// sources or `.trace` sidecars are absent.
pub fn parse_olean_binary_imports(bytes: &[u8]) -> Option<(Vec<ParsedImport>, bool)> {
    if bytes.len() < 96 || &bytes[0..5] != b"olean" || bytes[5] != 2 {
        return None;
    }
    let base_addr = read_le_u64_at(bytes, 80)?;
    let root_ptr = read_le_u64_at(bytes, 88)?;
    if (root_ptr & 1) != 0 || root_ptr < base_addr {
        return None;
    }
    let root_off = usize::try_from(root_ptr - base_addr).ok()?;
    let root_num_objs = *bytes.get(root_off.checked_add(6)?)?;
    let root_tag = *bytes.get(root_off.checked_add(7)?)?;
    if root_tag != 0 || root_num_objs < 5 {
        return None;
    }
    let imports_ptr = read_le_u64_at(bytes, root_off.checked_add(8)?)?;
    let is_mod_off = root_off.checked_add(8 + (root_num_objs as usize) * 8)?;
    let is_module = *bytes.get(is_mod_off)? != 0;
    if (imports_ptr & 1) != 0 || imports_ptr < base_addr {
        return None;
    }
    let arr_off = usize::try_from(imports_ptr - base_addr).ok()?;
    if *bytes.get(arr_off.checked_add(7)?)? != 246 {
        return None;
    }
    let arr_sz = usize::try_from(read_le_u64_at(bytes, arr_off.checked_add(8)?)?).ok()?;
    if arr_sz > 65_536 {
        return None;
    }
    let elems_base = arr_off.checked_add(24)?;
    let mut out = Vec::with_capacity(arr_sz);
    for idx in 0..arr_sz {
        let elem_ptr = read_le_u64_at(bytes, elems_base.checked_add(idx * 8)?)?;
        if (elem_ptr & 1) != 0 || elem_ptr < base_addr {
            return None;
        }
        let imp_off = usize::try_from(elem_ptr - base_addr).ok()?;
        let imp_num_objs = *bytes.get(imp_off.checked_add(6)?)?;
        let imp_tag = *bytes.get(imp_off.checked_add(7)?)?;
        if imp_tag != 0 || imp_num_objs < 1 {
            return None;
        }
        let name_ptr = read_le_u64_at(bytes, imp_off.checked_add(8)?)?;
        let module = read_olean_name_at(bytes, base_addr, name_ptr)?;
        let flags_off = imp_off.checked_add(8 + (imp_num_objs as usize) * 8)?;
        let import_all = *bytes.get(flags_off)? != 0;
        let is_exported = *bytes.get(flags_off.checked_add(1)?)? != 0;
        let is_meta = *bytes.get(flags_off.checked_add(2)?)? != 0;
        out.push(ParsedImport {
            module,
            is_exported,
            is_meta,
            import_all,
        });
    }
    Some((out, is_module))
}
#[allow(clippy::type_complexity)]
pub(super) static LEAN_INFO_CACHE: OnceLock<Mutex<HashMap<PathBuf, (String, PathBuf, PathBuf)>>> =
    OnceLock::new();
pub(super) fn path_has_toolchain_component(path: &Path, tc_dir_name: &str) -> bool {
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

pub(super) fn path_is_inside_any_toolchains_dir(path: &Path) -> bool {
    path.components()
        .any(|c| c.as_os_str().to_string_lossy() == "toolchains")
}

pub(super) fn path_has_elan_bin_component(p: &Path) -> bool {
    let comps: Vec<String> = p
        .components()
        .map(|c| c.as_os_str().to_string_lossy().to_string())
        .collect();
    if comps
        .windows(2)
        .any(|w| (w[0] == ".elan" || w[0] == "elan") && w[1] == "bin")
    {
        return true;
    }
    if let Some(bin_dir) = p.parent() {
        if (bin_dir.join("elan").is_file() || bin_dir.join("elan.exe").is_file())
            && bin_dir
                .parent()
                .map(|gp| gp.join("toolchains").is_dir())
                .unwrap_or(false)
        {
            return true;
        }
    }
    false
}

pub(super) fn path_is_elan_proxy_bin(path: &Path) -> bool {
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
        if path_has_elan_bin_component(&canon) {
            return true;
        }
    }
    path_has_elan_bin_component(path)
}

pub(super) fn allow_toolchain_fallback_opt_in() -> bool {
    std::env::var("TURBO_LEAN_ALLOW_TOOLCHAIN_FALLBACK")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false)
}

pub(super) fn is_toolchain_eligible_for_fleet_fallback(toolchain: &str) -> bool {
    let trimmed = toolchain.trim();
    if trimmed.is_empty() || trimmed == "unknown" {
        return true;
    }
    if allow_toolchain_fallback_opt_in() {
        if let Some(ver) = extract_toolchain_version_token(trimmed) {
            let mut parts = ver.split('.');
            if let (Some(major_str), Some(minor_raw)) = (parts.next(), parts.next()) {
                let minor_str = minor_raw.split('-').next().unwrap_or(minor_raw);
                if let (Ok(4), Ok(minor)) = (major_str.parse::<u32>(), minor_str.parse::<u32>()) {
                    return minor <= 35;
                }
            }
        }
    }
    false
}

pub(super) fn extract_toolchain_version_token(toolchain: &str) -> Option<String> {
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

pub(crate) const FLEET_SYSTEM_ELAN_ROOTS: [&str; 7] = [
    "/root/.elan",
    "/var/lib/sandboxed-node/.elan",
    "/var/lib/sandboxed-node/caches/elan",
    "/var/lib/orb-node/.elan",
    "/var/lib/orb-node/caches/elan",
    "/var/lib/orb-node/work/caches/elan",
    "/opt/orb/elan",
];

pub(crate) fn parse_olean_header_version_and_githash(bytes: &[u8]) -> Option<(String, String)> {
    if bytes.len() < 80 || &bytes[0..5] != b"olean" || bytes[5] != 2 {
        return None;
    }
    let gh_bytes = &bytes[40..80];
    if !gh_bytes.iter().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    let ver_end = bytes[7..40]
        .iter()
        .position(|&b| b == 0)
        .map(|i| 7 + i)
        .unwrap_or(40);
    let version = String::from_utf8_lossy(&bytes[7..ver_end])
        .trim()
        .to_string();
    let githash = String::from_utf8_lossy(gh_bytes).to_string();
    Some((version, githash))
}

pub(crate) fn read_olean_header_version_and_githash_confined(
    base_root: &Path,
    path: &Path,
) -> Option<(String, String)> {
    let canon_base = base_root.canonicalize().ok()?;
    let rel = path.strip_prefix(&canon_base).ok()?;
    if rel.as_os_str().is_empty() {
        return None;
    }
    let mut cur = canon_base;
    let comps: Vec<_> = rel.components().collect();
    for (idx, comp) in comps.iter().enumerate() {
        let std::path::Component::Normal(seg) = comp else {
            return None;
        };
        cur.push(seg);
        let meta = fs::symlink_metadata(&cur).ok()?;
        if meta.file_type().is_symlink() {
            return None;
        }
        if idx + 1 == comps.len() {
            if !meta.is_file() {
                return None;
            }
        } else if !meta.is_dir() {
            return None;
        }
    }
    read_olean_header_version_and_githash(&cur)
}

pub(crate) fn read_olean_header_version_and_githash(path: &Path) -> Option<(String, String)> {
    use std::io::Read;
    let mut opts = fs::OpenOptions::new();
    opts.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.custom_flags(libc::O_NOFOLLOW);
    }
    let mut f = opts.open(path).ok()?;
    if !f.metadata().ok()?.is_file() {
        return None;
    }
    let mut hdr = [0u8; 80];
    f.read_exact(&mut hdr).ok()?;
    parse_olean_header_version_and_githash(&hdr)
}

pub(super) fn find_project_olean_header_with<F>(
    project_dir: &Path,
    mut pred: F,
) -> Option<(PathBuf, String, String)>
where
    F: FnMut(&str) -> bool,
{
    let is_real_rel_dir = |base: &Path, rel: &[&str]| -> Option<PathBuf> {
        let mut cur = base.to_path_buf();
        for seg in rel {
            cur.push(seg);
            if !fs::symlink_metadata(&cur).is_ok_and(|m| m.is_dir()) {
                return None;
            }
        }
        Some(cur)
    };
    let mut lib_dirs: Vec<PathBuf> = Vec::new();
    if let Some(root_lib) = is_real_rel_dir(project_dir, &[".lake", "build", "lib", "lean"]) {
        lib_dirs.push(root_lib);
    }
    if let Some(pkgs_dir) = is_real_rel_dir(project_dir, &[".lake", "packages"]) {
        if let Ok(entries) = fs::read_dir(&pkgs_dir) {
            let mut pkg_paths: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
            pkg_paths.sort();
            for p in pkg_paths {
                if fs::symlink_metadata(&p).is_ok_and(|m| m.is_dir()) {
                    if let Some(dep_lib) = is_real_rel_dir(&p, &[".lake", "build", "lib", "lean"]) {
                        lib_dirs.push(dep_lib);
                    }
                }
            }
        }
    }
    for dir in lib_dirs {
        for entry in walkdir::WalkDir::new(&dir)
            .follow_links(false)
            .sort_by_file_name()
            .into_iter()
            .flatten()
        {
            let p = entry.path();
            if p.extension().and_then(|s| s.to_str()) != Some("olean")
                || !entry.file_type().is_file()
            {
                continue;
            }
            if let Some((ver, gh)) = read_olean_header_version_and_githash(p) {
                if pred(&gh) {
                    return Some((p.to_path_buf(), ver, gh));
                }
            }
        }
    }
    None
}

pub(super) fn detect_project_olean_header_sample(project_dir: &Path) -> Option<(PathBuf, String, String)> {
    find_project_olean_header_with(project_dir, |_| true)
}

pub(crate) fn enforce_project_olean_githash_gate(
    project_dir: &Path,
    toolchain: &str,
    resolved_bin: &Path,
    resolved_githash: &str,
    elan_roots: &[PathBuf],
) -> Result<()> {
    let expected = resolved_githash.trim();
    let Some((olean_path, olean_ver, olean_gh)) =
        find_project_olean_header_with(project_dir, |gh| !gh.eq_ignore_ascii_case(expected))
    else {
        return Ok(());
    };
    let roots_str = elan_roots
        .iter()
        .map(|r| r.display().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    anyhow::bail!(
        "Prebuilt `.olean` toolchain/githash skew detected for {} (requested toolchain `{}`): `{}` has header version `{}` (githash `{}`), whereas resolved compiler `{}` has githash `{}` (scanned elan roots: [{}]): fail-closed toolchain gate",
        project_dir.display(),
        toolchain,
        olean_path.display(),
        olean_ver,
        olean_gh,
        resolved_bin.display(),
        expected,
        roots_str
    );
}

pub(crate) fn parse_toolchain_major_minor(toolchain: &str) -> Option<(u32, u32)> {
    let ver = extract_toolchain_version_token(toolchain)?;
    let mut parts = ver.split('.');
    let major_str = parts.next()?;
    let minor_raw = parts.next()?;
    let minor_str = minor_raw.split('-').next().unwrap_or(minor_raw);
    Some((major_str.parse().ok()?, minor_str.parse().ok()?))
}

/// Lean/Lake `< 4.33` nests `deps` + `libs` inside `[format!("{}:deps", mod_name), [...]]`
/// in `.trace` `"inputs"`, whereas `>= 4.33` emits `deps` and `libs` as separate top-level entries.
pub(crate) fn lake_trace_uses_nested_mod_deps(toolchain: &str) -> bool {
    matches!(parse_toolchain_major_minor(toolchain), Some((4, minor)) if minor < 33)
}

pub(super) fn trace_recorded_src_hash(tv: &serde_json::Value) -> Option<&str> {
    let inputs = tv.get("inputs")?.as_array()?;
    let first_tag = inputs.first()?.as_array()?.first()?.as_str()?;
    if first_tag.ends_with(":deps") {
        tv.pointer("/inputs/2/1")?.as_str()
    } else if first_tag == "deps" || inputs.len() >= 4 {
        tv.pointer("/inputs/3/1")?.as_str()
    } else {
        None
    }
}

pub(super) fn trace_recorded_imports_array(tv: &serde_json::Value) -> Option<&serde_json::Value> {
    let inputs = tv.get("inputs")?.as_array()?;
    let first_tag = inputs.first()?.as_array()?.first()?.as_str()?;
    let imports_pair = if first_tag == "deps" {
        tv.pointer("/inputs/0/1/1")?
    } else if first_tag.ends_with(":deps") {
        let deps_pair = tv.pointer("/inputs/0/1/0")?;
        if deps_pair.get(0).and_then(|v| v.as_str()) != Some("deps") {
            return None;
        }
        deps_pair.pointer("/1/1")?
    } else {
        return None;
    };
    if imports_pair.get(0).and_then(|v| v.as_str()) != Some("imports") {
        return None;
    }
    imports_pair.get(1)
}

pub(super) fn is_valid_16hex_hash(s: &str) -> bool {
    s.len() == 16 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

pub(super) fn lean_version_output_matches_exact(ver_str: &str, expected_ver: &str) -> bool {
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
    resolve_toolchain_compiler_with_roots(project_dir, toolchain, is_untrusted, None)
}

pub(super) fn resolve_toolchain_compiler_with_roots(
    project_dir: &Path,
    toolchain: &str,
    is_untrusted: bool,
    explicit_elan_roots: Option<&[PathBuf]>,
) -> Result<(PathBuf, String, PathBuf, PathBuf)> {
    if let Some(version) = extract_toolchain_version_token(toolchain) {
        let mut parts = version.split('.');
        if let (Some(major), Some(minor)) = (
            parts.next().and_then(|s| s.parse::<u32>().ok()),
            parts.next().and_then(|s| s.parse::<u32>().ok()),
        ) {
            anyhow::ensure!(
                (major, minor) >= (4, 31),
                "Unsupported Lean toolchain `{toolchain}`: turbo-lean requires Lean >= 4.31.0; update lean-toolchain and rebuild the project with Lake"
            );
        }
    }
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
    if let Some(roots) = explicit_elan_roots {
        elan_roots.extend_from_slice(roots);
    } else {
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
        for sys_elan in FLEET_SYSTEM_ELAN_ROOTS {
            let p = PathBuf::from(sys_elan);
            if p.is_dir() && !elan_roots.contains(&p) {
                elan_roots.push(p);
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
    }
    for root in &elan_roots {
        let exact_tc = root.join("toolchains").join(&tc_dir_name).join("bin/lean");
        if exact_tc.is_file() {
            candidate_bins.push(exact_tc);
        }
    }
    if candidate_bins.is_empty() {
        if let Some(nix_lean) = option_env!("TURBO_LEAN_NIX_DEFAULT_LEAN").filter(|s| !s.is_empty())
        {
            let p = PathBuf::from(nix_lean);
            if p.is_file() {
                candidate_bins.push(p);
            }
        }
    }
    let strict_tc = is_untrusted
        || !is_toolchain_eligible_for_fleet_fallback(toolchain)
        || std::env::var("TURBO_LEAN_STRICT_TOOLCHAIN")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false);
    let allow_explicit_fallback = allow_toolchain_fallback_opt_in() && !strict_tc;
    let mut used_fallback_tc = false;
    if candidate_bins.is_empty() && allow_explicit_fallback {
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
    if candidate_bins.is_empty() && !is_untrusted && (!has_specific_tc || allow_explicit_fallback) {
        if let Ok(path_var) = std::env::var("PATH") {
            for dir in std::env::split_paths(&path_var) {
                let cand = dir.join("lean");
                if cand.is_file() {
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
    if candidate_bins.is_empty() && (!has_specific_tc || allow_explicit_fallback) {
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
        .ok_or_else(|| {
            let roots_str = elan_roots
                .iter()
                .map(|r| r.display().to_string())
                .collect::<Vec<_>>()
                .join(", ");
            let olean_note = match detect_project_olean_header_sample(&canon_proj) {
                Some((op, ver, gh)) => format!(
                    "; detected prebuilt `.olean` `{}` with version `{}` (githash `{}`)",
                    op.display(),
                    ver,
                    gh
                ),
                None => String::new(),
            };
            anyhow::anyhow!(
                "Could not locate installed `lean` compiler binary matching toolchain `{}` for {} (scanned elan roots: [{}]{}): fail-closed toolchain gate",
                toolchain,
                project_dir.display(),
                roots_str,
                olean_note
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
                let (gh, lib_lean, lib) = (gh.clone(), lib_lean.clone(), lib.clone());
                drop(guard);
                if used_fallback_tc || crate::lake_build::worktree_auto_link_disabled(&canon_proj) {
                    enforce_project_olean_githash_gate(
                        &canon_proj,
                        toolchain,
                        &canon_bin,
                        &gh,
                        &elan_roots,
                    )?;
                }
                return Ok((canon_bin, gh, lib_lean, lib));
            }
        }
    }
    let githash_out = Command::new(&canon_bin)
        .env("PATH", crate::trusted_tools::trusted_sys_path())
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
    if !used_fallback_tc
        && has_specific_tc
        && !path_has_toolchain_component(&canon_bin, &tc_dir_name)
    {
        let is_nix_default = option_env!("TURBO_LEAN_NIX_DEFAULT_LEAN")
            .filter(|s| !s.is_empty())
            .and_then(|p| Path::new(p).canonicalize().ok())
            .as_deref()
            == Some(canon_bin.as_path());
        if (is_untrusted && !is_nix_default)
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
                .env("PATH", crate::trusted_tools::trusted_sys_path())
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
        .env("PATH", "/usr/bin:/bin")
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
    if used_fallback_tc || crate::lake_build::worktree_auto_link_disabled(&canon_proj) {
        enforce_project_olean_githash_gate(
            &canon_proj,
            toolchain,
            &canon_bin,
            &githash,
            &elan_roots,
        )?;
    }
    Ok((canon_bin, githash, lib_lean, lib))
}
/// Absolute verifier tools from one installed toolchain. Never derive these from Lake's
/// environment: Lake prepends project executable directories to PATH.
#[derive(Clone, Debug)]
pub(crate) struct ToolchainExecutables {
    pub lean: PathBuf,
    pub lake: PathBuf,
    pub leanc: PathBuf,
}

impl ToolchainExecutables {
    pub fn resolve(project: &Path, toolchain: &str) -> Result<Self> {
        let project = lake_build::find_project_root(project);
        let (lean, _, _, _) = resolve_toolchain_compiler_with_trust(&project, toolchain, true)?;
        let tools = Self::from_lean(&lean)?;
        let project = project.canonicalize()?;
        for tool in [&tools.lean, &tools.lake, &tools.leanc] {
            anyhow::ensure!(
                !tool.starts_with(&project),
                "Verifier executable `{}` is inside project: fail-closed toolchain gate",
                tool.display()
            );
        }
        Ok(tools)
    }

    pub fn from_lean(lean: &Path) -> Result<Self> {
        anyhow::ensure!(
            lean.is_absolute(),
            "Verifier compiler `{}` must be absolute: fail-closed toolchain gate",
            lean.display()
        );
        let lean = lean.canonicalize().with_context(|| {
            format!(
                "Missing verifier compiler `{}`: fail-closed toolchain gate",
                lean.display()
            )
        })?;
        let bin = lean
            .parent()
            .context("Missing verifier toolchain bin directory")?;
        let sibling = |name: &str| -> Result<PathBuf> {
            let path = bin.join(name);
            let canonical = path.canonicalize().with_context(|| {
                format!(
                    "Missing required toolchain sibling `{}`: fail-closed toolchain gate",
                    path.display()
                )
            })?;
            anyhow::ensure!(
                canonical.is_file() && canonical.parent() == Some(bin),
                "Invalid toolchain sibling `{}`: fail-closed toolchain gate",
                path.display()
            );
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                anyhow::ensure!(
                    canonical.metadata()?.permissions().mode() & 0o111 != 0,
                    "Toolchain sibling `{}` is not executable: fail-closed toolchain gate",
                    path.display()
                );
            }
            Ok(canonical)
        };
        Ok(Self {
            lake: sibling("lake")?,
            leanc: sibling("leanc")?,
            lean,
        })
    }

    pub fn path(&self) -> String {
        verifier_path(&self.lean)
    }

    pub fn lake_build_path(&self, canon_dir: &Path) -> String {
        trusted_lake_build_path(&self.lean, canon_dir)
    }

    pub fn apply_env(&self, env: &mut HashMap<String, String>) {
        env.insert("PATH".into(), self.path());
        for (name, path) in [
            ("LEAN", &self.lean),
            ("LAKE", &self.lake),
            ("LEANC", &self.leanc),
        ] {
            env.insert(name.into(), path.to_string_lossy().into_owned());
        }
    }
}

impl PackageConfig {
    /// Expected linked executable path for `exe` (`<pkg_root>/<build_dir>/<bin_dir>/<exe_name>`).
    pub fn exe_binary_path(&self, exe: &LeanExeConfig) -> PathBuf {
        let stem = exe
            .exe_name
            .as_deref()
            .filter(|s| !s.is_empty())
            .unwrap_or(&exe.name);
        let mut rel = PathBuf::from(stem);
        let suffix = std::env::consts::EXE_SUFFIX;
        if !suffix.is_empty() && !stem.ends_with(suffix) {
            let mut os = rel.into_os_string();
            os.push(suffix);
            rel = PathBuf::from(os);
        }
        self.pkg_root
            .join(&self.build_dir)
            .join(&self.bin_dir)
            .join(rel)
    }
}

/// Only the resolved toolchain and fixed system utilities, never caller/project bins.
pub(crate) fn verifier_path(lean: &Path) -> String {
    let sys = crate::trusted_tools::trusted_sys_path();
    match lean.parent().filter(|p| p.is_absolute()) {
        Some(bin) => format!("{}:{sys}", bin.display()),
        None => sys,
    }
}

///Trusted `lake build` PATH: toolchain bin first, then caller's existing absolute PATH entries
/// outside the checkout's `.lake/` tree (so `LEAN_CC` wrappers can resolve `ccache`/`clang`/`lld`),
/// plus standard system utility directories.
pub(crate) fn trusted_lake_build_path(lean: &Path, canon_dir: &Path) -> String {
    let mut dirs: Vec<PathBuf> = Vec::new();
    let lake_sub = canon_dir.join(".lake");
    let has_lake_component = |p: &Path| p.components().any(|c| c.as_os_str() == ".lake");
    let mut push_dir = |p: PathBuf| {
        if p.is_absolute()
            && !p.starts_with(&lake_sub)
            && !has_lake_component(&p)
            && !dirs.contains(&p)
        {
            dirs.push(p);
        }
    };
    if let Some(bin) = lean.parent() {
        push_dir(bin.to_path_buf());
    }
    if let Some(raw) = std::env::var_os("PATH") {
        for entry in std::env::split_paths(&raw) {
            if entry.is_absolute() && entry.is_dir() && !has_lake_component(&entry) {
                let canon_ok = entry
                    .canonicalize()
                    .map(|c| !c.starts_with(&lake_sub) && !has_lake_component(&c))
                    .unwrap_or(false);
                if canon_ok {
                    push_dir(entry);
                }
            }
        }
    }
    for sys in ["/usr/local/bin", "/usr/bin", "/bin"] {
        push_dir(PathBuf::from(sys));
    }
    std::env::join_paths(&dirs)
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|_| verifier_path(lean))
}

/// Revalidate toolchain siblings and replace executable overrides after supplied envs.
pub(crate) fn verifier_command(lean: &Path, env: &HashMap<String, String>) -> Result<Command> {
    let tools = ToolchainExecutables::from_lean(lean)?;
    let mut env = env.clone();
    tools.apply_env(&mut env);
    let mut command = Command::new(&tools.lean);
    command.envs(env);
    Ok(command)
}

/// Parse `lake-manifest.json` in `project_dir` if present. `packagesDir`, package names and
/// `subDir` must stay inside the workspace; so must a `path` dependency's `dir` when
/// `is_untrusted` (a trusted workspace may point one at a sibling checkout, as Lake allows).
pub fn parse_lake_manifest(
    project_dir: &Path,
    is_untrusted: bool,
) -> Result<(PathBuf, Vec<ManifestPackageEntry>, Option<String>)> {
    let manifest_path = project_dir.join("lake-manifest.json");
    if !manifest_path.is_file() {
        return Ok((PathBuf::from(".lake/packages"), Vec::new(), None));
    }
    let raw = fs::read_to_string(&manifest_path)
        .with_context(|| format!("Failed to read {}", manifest_path.display()))?;
    parse_lake_manifest_str(project_dir, &manifest_path, &raw, is_untrusted)
}

pub(crate) fn parse_lake_manifest_str(
    project_dir: &Path,
    manifest_path: &Path,
    raw: &str,
    is_untrusted: bool,
) -> Result<(PathBuf, Vec<ManifestPackageEntry>, Option<String>)> {
    let val: serde_json::Value = serde_json::from_str(raw)
        .with_context(|| format!("Invalid JSON in {}", manifest_path.display()))?;
    let manifest_hash = blake3::hash(raw.as_bytes()).to_hex().to_string();
    let packages_dir_str = val
        .get("packagesDir")
        .and_then(|v| v.as_str())
        .unwrap_or(".lake/packages");
    let packages_dir = lake_rel_path("packagesDir", packages_dir_str)?;
    let mut entries = Vec::new();
    if let Some(pkgs) = val.get("packages").and_then(|v| v.as_array()) {
        for pkg in pkgs {
            let raw_name = pkg.get("name").and_then(|v| v.as_str()).unwrap_or("");
            let name = clean_lake_ident(raw_name);
            if name.is_empty() {
                continue;
            }
            // The name is a directory under `packagesDir`.
            if name.contains('/') || name == "." || name == ".." {
                anyhow::bail!(
                    "Unsupported package name `{}` in {}: fail-closed static Lake config gate",
                    name,
                    manifest_path.display()
                );
            }
            let pkg_type = pkg
                .get("type")
                .and_then(|v| v.as_str())
                .unwrap_or("git")
                .to_string();
            let sub_dir = pkg
                .get("subDir")
                .and_then(|v| v.as_str())
                .filter(|s| !s.is_empty())
                .map(|sd| lake_rel_path("subDir", sd))
                .transpose()?;
            let base_dir = if pkg_type == "path" {
                if let Some(d) = pkg.get("dir").and_then(|v| v.as_str()) {
                    if is_untrusted {
                        lake_rel_path("dir", d)?;
                    }
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
pub(super) fn check_extern_lib_artifact(
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
pub(super) fn update_hasher_lp(h: &mut blake3::Hasher, s: &[u8]) {
    h.update(&(s.len() as u64).to_le_bytes());
    h.update(s);
}

pub(super) fn update_hasher_lean_options(h: &mut blake3::Hasher, opts: &LeanOptionsMap) {
    h.update(&(opts.len() as u64).to_le_bytes());
    for (k, v) in opts {
        h.update(&(k.0.len() as u64).to_le_bytes());
        for p in &k.0 {
            match p {
                LeanNamePart::Str(s) => {
                    h.update(&[1]);
                    update_hasher_lp(h, s.as_bytes());
                }
                LeanNamePart::Num(n) => {
                    h.update(&[2]);
                    h.update(&n.to_le_bytes());
                }
            }
        }
        match v {
            LeanOptionValue::Bool(b) => {
                h.update(&[1, u8::from(*b)]);
            }
            LeanOptionValue::Nat(n) => {
                h.update(&[2]);
                h.update(&n.to_le_bytes());
            }
            LeanOptionValue::Str(s) => {
                h.update(&[3]);
                update_hasher_lp(h, s.as_bytes());
            }
        }
    }
}

pub(super) fn compute_package_config_digest(pkg: &PackageConfig, raw_config_hash: &str) -> String {
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-pkg-config-v5\n");
    update_hasher_lp(&mut h, crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    update_hasher_lp(&mut h, pkg.name.as_bytes());
    update_hasher_lp(&mut h, pkg.base_name.as_bytes());
    update_hasher_lp(&mut h, pkg.config_file_kind.as_bytes());
    update_hasher_lp(&mut h, raw_config_hash.as_bytes());
    update_hasher_lp(&mut h, pkg.src_dir.to_string_lossy().as_bytes());
    update_hasher_lp(&mut h, pkg.build_dir.to_string_lossy().as_bytes());
    if pkg.bin_dir != Path::new("bin") {
        h.update(b"bin_dir:");
        update_hasher_lp(&mut h, pkg.bin_dir.to_string_lossy().as_bytes());
    }
    update_hasher_lp(&mut h, pkg.lean_lib_dir.to_string_lossy().as_bytes());
    update_hasher_lp(&mut h, pkg.native_lib_dir.to_string_lossy().as_bytes());
    update_hasher_lp(&mut h, pkg.ir_dir.to_string_lossy().as_bytes());
    update_hasher_lp(&mut h, pkg.packages_dir.to_string_lossy().as_bytes());
    h.update(&[
        u8::from(pkg.precompile_modules),
        match pkg.platform_independent {
            None => 0,
            Some(false) => 1,
            Some(true) => 2,
        },
    ]);
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
    update_hasher_lean_options(&mut h, &pkg.lean_options);
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
            match lib.platform_independent {
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
        update_hasher_lean_options(&mut h, &lib.lean_options);
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
        if let Some(ref en) = exe.exe_name {
            h.update(b"exe_name:");
            update_hasher_lp(&mut h, en.as_bytes());
        }
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
            match exe.platform_independent {
                None => 0,
                Some(false) => 1,
                Some(true) => 2,
            },
            u8::from(exe.is_default_target),
        ]);
        update_hasher_lean_options(&mut h, &exe.lean_options);
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
    // The `input_*` / `needs` *declarations* are already pinned by `raw_config_hash`. The input
    // file *contents* are deliberately not folded in here: they only affect the libraries that
    // `needs` them, so `module_lake_input_digest` folds them per module instead of invalidating
    // every module of the package.
    h.finalize().to_hex().to_string()
}
use crate::shm_cache::strip_toml_comment;
pub(super) fn split_top_level_comma(s: &str) -> Result<Vec<String>> {
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
pub(super) fn parse_toml_string(val: &str) -> Result<String> {
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
                    'b' => out.push('\u{8}'),
                    'f' => out.push('\u{c}'),
                    '\\' => out.push('\\'),
                    '"' => out.push('"'),
                    // TOML's `\uXXXX` / `\UXXXXXXXX` (e.g. `"src/\u03b1"`).
                    u @ ('u' | 'U') => {
                        let len = if u == 'u' { 4 } else { 8 };
                        let hex: String = chars
                            .get(i + 1..i + 1 + len)
                            .unwrap_or(&[])
                            .iter()
                            .collect();
                        let decoded = (hex.len() == len)
                            .then(|| u32::from_str_radix(&hex, 16).ok())
                            .flatten()
                            .and_then(char::from_u32);
                        let Some(c) = decoded else {
                            anyhow::bail!("Invalid `\\{}` escape in string `{}`", u, val);
                        };
                        out.push(c);
                        i += len;
                    }
                    other => {
                        anyhow::bail!("Unsupported escape `\\{}` in string `{}`", other, val);
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
pub(super) fn parse_toml_bool(val: &str) -> Result<bool> {
    match val.trim() {
        "true" => Ok(true),
        "false" => Ok(false),
        other => anyhow::bail!(
            "Expected TOML boolean (`true` or `false`), found `{}`",
            other
        ),
    }
}
pub(super) fn parse_toml_string_array(val: &str) -> Result<Vec<String>> {
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
/// Validate a TOML value recursively for inline-table duplicate/conflicting keys,
/// mirroring `Lake.Toml.elabInlineTable` (`Lake/Toml/Elab/Value.lean:211-234`).
pub(super) fn validate_toml_value_keys(val: &str) -> Result<()> {
    let s = val.trim();
    if s.starts_with('{') && s.ends_with('}') {
        let mut dict: BTreeMap<Vec<String>, bool> = BTreeMap::new(); // true = static value, false = partial table
        for entry in split_top_level_comma(&s[1..s.len() - 1])? {
            let Some((k, v)) = entry.split_once('=') else {
                anyhow::bail!("Invalid inline table entry `{}`", entry);
            };
            let ks = split_toml_dotted_key(k)?;
            let mut cur = Vec::with_capacity(ks.len());
            for seg in &ks[..ks.len() - 1] {
                cur.push(seg.clone());
                if let Some(&is_static) = dict.get(&cur) {
                    if is_static {
                        anyhow::bail!(
                            "cannot redefine key `{}` in TOML inline table",
                            cur.join(".")
                        );
                    }
                } else {
                    dict.insert(cur.clone(), false);
                }
            }
            cur.push(ks[ks.len() - 1].clone());
            if dict.contains_key(&cur) {
                anyhow::bail!(
                    "cannot redefine key `{}` in TOML inline table",
                    cur.join(".")
                );
            }
            validate_toml_value_keys(v)?;
            dict.insert(cur, true);
        }
    } else if s.starts_with('[') && s.ends_with(']') {
        for item in split_top_level_comma(&s[1..s.len() - 1])? {
            validate_toml_value_keys(&item)?;
        }
    }
    Ok(())
}
pub(super) fn parse_toml_inline_table(val: &str) -> Result<BTreeMap<String, String>> {
    validate_toml_value_keys(val)?;
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
        let ks = split_toml_dotted_key(k)?;
        let key = ks.join(".");
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
/// Split a TOML dotted key (`Lake/Toml/Grammar.lean:345-535`) into `simpleKey` string segments.
/// Each segment is either an `unquotedKey` (`[A-Za-z0-9_-]+`), a `basicString` (`"..."`), or a
/// `literalString` (`'...'`, no backslash escaping). Every TOML table key segment becomes `Name.str`.
pub(super) fn split_toml_dotted_key(raw: &str) -> Result<Vec<String>> {
    let mut rem = raw.trim();
    if rem.is_empty() {
        anyhow::bail!("Empty TOML key in lakefile.toml");
    }
    let mut parts = Vec::new();
    loop {
        rem = rem.trim_start();
        let Some(first) = rem.chars().next() else {
            anyhow::bail!("Trailing `.` in TOML key `{raw}` in lakefile.toml");
        };
        let (seg, rest) = if first == '"' {
            let mut idx = 1usize;
            let bytes = rem.as_bytes();
            let mut end_q = None;
            while idx < bytes.len() {
                if bytes[idx] == b'\\' {
                    idx += 2;
                    continue;
                }
                if bytes[idx] == b'"' {
                    end_q = Some(idx);
                    break;
                }
                idx += 1;
            }
            let Some(q) = end_q else {
                anyhow::bail!("Unterminated quoted TOML key `{raw}` in lakefile.toml");
            };
            (parse_toml_string(&rem[..=q])?, &rem[q + 1..])
        } else if first == '\'' {
            let Some(q) = rem[1..].find('\'') else {
                anyhow::bail!("Unterminated literal TOML key `{raw}` in lakefile.toml");
            };
            (rem[1..1 + q].to_string(), &rem[2 + q..])
        } else {
            let len: usize = rem
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-'))
                .map(char::len_utf8)
                .sum();
            if len == 0 {
                anyhow::bail!("Unsupported TOML key `{raw}` in lakefile.toml");
            }
            (rem[..len].to_string(), &rem[len..])
        };
        if seg.is_empty() || seg.contains('»') || seg.chars().any(char::is_control) {
            anyhow::bail!("Unsupported TOML `leanOptions` key `{raw}` in lakefile.toml");
        }
        parts.push(seg);
        let rest = rest.trim_start();
        if rest.is_empty() {
            break;
        }
        if let Some(after_dot) = rest.strip_prefix('.') {
            rem = after_dot;
        } else {
            anyhow::bail!("Unsupported TOML key `{raw}` in lakefile.toml");
        }
    }
    Ok(parts)
}

/// Parse a TOML `Nat` literal (`Lake/Toml/Grammar.lean:445-485`, `Decode.lean:105-120`):
/// decimal (`0` or `[+]?[1-9](_?[0-9])*`), hex (`0x`), octal (`0o`), or binary (`0b`), with single `_` between digits.
pub(super) fn parse_toml_nat(raw: &str) -> Option<u64> {
    let s = raw.trim();
    if s.is_empty() {
        return None;
    }
    let sep_digits = |body: &str, radix: u32| -> Option<u64> {
        if body.is_empty() || body.starts_with('_') || body.ends_with('_') || body.contains("__") {
            return None;
        }
        if !body.chars().all(|c| c == '_' || c.is_digit(radix)) {
            return None;
        }
        let clean: String = body.chars().filter(|&c| c != '_').collect();
        u64::from_str_radix(&clean, radix).ok()
    };
    if let Some(hex) = s.strip_prefix("0x") {
        return sep_digits(hex, 16);
    }
    if let Some(oct) = s.strip_prefix("0o") {
        return sep_digits(oct, 8);
    }
    if let Some(bin) = s.strip_prefix("0b") {
        return sep_digits(bin, 2);
    }
    let dec = s.strip_prefix('+').unwrap_or(s);
    if dec == "0" {
        return Some(0);
    }
    if dec.starts_with('0') {
        return None;
    }
    sep_digits(dec, 10)
}

pub(super) fn parse_toml_lean_option_value(raw: &str, key_ctx: &str) -> Result<LeanOptionValue> {
    let v = raw.trim();
    if v.starts_with('"') || v.starts_with('\'') {
        let s = parse_toml_string(v)?;
        if matches!(s.as_str(), "true" | "false")
            || s.parse::<u64>().is_ok()
            || s.is_empty()
            || s.chars().any(char::is_control)
        {
            anyhow::bail!(
                "Unsupported `leanOptions` string value `{}` for `{}` in lakefile.toml",
                v,
                key_ctx
            );
        }
        Ok(LeanOptionValue::Str(s))
    } else if v == "true" {
        Ok(LeanOptionValue::Bool(true))
    } else if v == "false" {
        Ok(LeanOptionValue::Bool(false))
    } else if let Some(n) = parse_toml_nat(v) {
        Ok(LeanOptionValue::Nat(n))
    } else {
        anyhow::bail!(
            "Unsupported `leanOptions` value `{}` for `{}` in lakefile.toml",
            v,
            key_ctx
        )
    }
}

/// Insert one or more TOML `leanOptions` entries under `prefix` (handling nested inline tables `{...}`).
/// Duplicate keys are rejected, matching Lake `KeyTy` / `elabInlineTable` elaboration.
pub(super) fn insert_toml_lean_option_entry(
    map: &mut LeanOptionsMap,
    prefix: &[String],
    raw_key: &str,
    raw_val: &str,
) -> Result<()> {
    let key_segs = split_toml_dotted_key(raw_key)?;
    let mut full_segs = Vec::with_capacity(prefix.len() + key_segs.len());
    full_segs.extend(prefix.iter().cloned());
    full_segs.extend(key_segs);
    let v = raw_val.trim();
    if v.starts_with('{') && v.ends_with('}') {
        validate_toml_value_keys(v)?;
        for entry in split_top_level_comma(&v[1..v.len() - 1])? {
            let Some((k, sub_v)) = entry.split_once('=') else {
                anyhow::bail!("Invalid inline table entry `{}`", entry);
            };
            insert_toml_lean_option_entry(map, &full_segs, k, sub_v)?;
        }
        return Ok(());
    }
    let name = LeanName(full_segs.into_iter().map(LeanNamePart::Str).collect());
    if map.contains_key(&name) {
        anyhow::bail!(
            "cannot redefine `leanOptions` key `{}` in lakefile.toml",
            name.to_lean_string()
        );
    }
    let val = parse_toml_lean_option_value(v, &name.to_lean_string())?;
    map.insert(name, val);
    Ok(())
}

/// Parse `leanOptions = { ... }` or `leanOptions = [ ... ]` (`Lake/Load/Toml.lean:116-140`).
pub(super) fn parse_toml_lean_options_value(val: &str, prefix: &[String]) -> Result<LeanOptionsMap> {
    validate_toml_value_keys(val)?;
    let s = val.trim();
    if s.starts_with('{') && s.ends_with('}') {
        let mut map = LeanOptionsMap::new();
        for entry in split_top_level_comma(&s[1..s.len() - 1])? {
            let Some((k, v)) = entry.split_once('=') else {
                anyhow::bail!("Invalid inline table entry `{}`", entry);
            };
            insert_toml_lean_option_entry(&mut map, prefix, k, v)?;
        }
        return Ok(map);
    }
    if s.starts_with('[') && s.ends_with(']') {
        anyhow::ensure!(
            prefix.is_empty(),
            "TOML `leanOptions` array syntax is only valid on `leanOptions = [...]`, found `{}`",
            val
        );
        let mut map = LeanOptionsMap::new();
        for item in split_top_level_comma(&s[1..s.len() - 1])? {
            let t = item.trim();
            if t.starts_with('[') && t.ends_with(']') {
                let elems = split_top_level_comma(&t[1..t.len() - 1])?;
                if elems.len() != 2 {
                    anyhow::bail!(
                        "Expected 2-element `[name, value]` in TOML `leanOptions`, found `{}`",
                        t
                    );
                }
                let name_str = parse_toml_string(&elems[0])?;
                let name = LeanName::from_str_to_name(&name_str)?;
                let opt_v = parse_toml_lean_option_value(&elems[1], &name_str)?;
                map.insert(name, opt_v);
            } else if t.starts_with('{') && t.ends_with('}') {
                let mut name_opt: Option<LeanName> = None;
                let mut val_raw_opt: Option<String> = None;
                for kv in split_top_level_comma(&t[1..t.len() - 1])? {
                    let Some((fk, fv)) = kv.split_once('=') else {
                        anyhow::bail!("Invalid TOML `leanOptions` record `{}`", t);
                    };
                    let fk_segs = split_toml_dotted_key(fk)?;
                    if fk_segs.len() != 1 {
                        anyhow::bail!(
                            "Invalid field `{}` in TOML `leanOptions` record `{}`",
                            fk,
                            t
                        );
                    }
                    match fk_segs[0].as_str() {
                        "name" => {
                            if name_opt.is_some() {
                                anyhow::bail!(
                                    "Duplicate field `name` in TOML `leanOptions` record `{}`",
                                    t
                                );
                            }
                            let ns = parse_toml_string(fv)?;
                            name_opt = Some(LeanName::from_str_to_name(&ns)?);
                        }
                        "value" => {
                            if val_raw_opt.is_some() {
                                anyhow::bail!(
                                    "Duplicate field `value` in TOML `leanOptions` record `{}`",
                                    t
                                );
                            }
                            val_raw_opt = Some(fv.trim().to_string());
                        }
                        other => {
                            anyhow::bail!(
                                "Unknown field `{}` in TOML `leanOptions` record `{}`",
                                other,
                                t
                            );
                        }
                    }
                }
                let (Some(name), Some(val_raw)) = (name_opt, val_raw_opt) else {
                    anyhow::bail!(
                        "TOML `leanOptions` record `{}` requires both `name` and `value`",
                        t
                    );
                };
                let opt_v = parse_toml_lean_option_value(&val_raw, &name.to_lean_string())?;
                map.insert(name, opt_v);
            } else {
                anyhow::bail!("Unsupported TOML `leanOptions` array item `{}`", t);
            }
        }
        return Ok(map);
    }
    anyhow::bail!(
        "Expected TOML inline table `{{...}}` or array `[...]` for `leanOptions`, found `{}`",
        val
    )
}

pub(super) fn toml_expr_is_unclosed(s: &str) -> bool {
    let mut bracket_depth = 0i32;
    let mut brace_depth = 0i32;
    let mut in_double = false;
    let mut in_single = false;
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0usize;
    while i < chars.len() {
        let c = chars[i];
        if in_double {
            if c == '\\' && i + 1 < chars.len() {
                i += 1;
            } else if c == '"' {
                in_double = false;
            }
        } else if in_single {
            if c == '\'' {
                in_single = false;
            }
        } else {
            match c {
                '"' => in_double = true,
                '\'' => in_single = true,
                '[' => bracket_depth += 1,
                ']' => bracket_depth -= 1,
                '{' => brace_depth += 1,
                '}' => brace_depth -= 1,
                _ => {}
            }
        }
        i += 1;
    }
    in_double || in_single || bracket_depth > 0 || brace_depth > 0
}

pub(super) fn parse_toml_glob_item(item: &str) -> Result<GlobSpec> {
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
pub(super) fn parse_toml_globs(val: &str) -> Result<Vec<GlobSpec>> {
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
/// A lakefile or manifest directory field, which must stay relative to its package: an absolute
/// path or `..` would point builds (and their writes) outside it.
pub(super) fn lake_rel_path(field: &str, raw: &str) -> Result<PathBuf> {
    let p = PathBuf::from(raw);
    if p.components().any(|c| {
        !matches!(
            c,
            std::path::Component::Normal(_) | std::path::Component::CurDir
        )
    }) {
        let _ = c_abi::verify_static_lake_config(true, true, false, false);
        anyhow::bail!(
            "Unsupported path `{}` for `{}`: must be relative and free of `..`: fail-closed static Lake config gate",
            raw,
            field
        );
    }
    Ok(p)
}
/// The lakefile scope a field belongs to.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum LakeScope {
    Package,
    Lib,
    Exe,
}
/// How a Lake 4.35 field that turbo-lean does not read itself affects the build.
pub(super) enum LakeField {
    /// Metadata, server, linker and native-library settings: no effect on a module's
    /// `.olean`/`.ilean`/`.c` or on the trace turbo-lean writes for it.
    Passive,
    /// A compile-affecting value turbo-lean does not mirror.
    Unsupported,
    Unknown,
}
/// Classify a field by `scope`, `key` and its raw value (`lakefile.toml` or `lakefile.lean`
/// syntax). Compile-affecting fields pass only at the value turbo-lean builds with.
pub(super) fn classify_lake_field(scope: LakeScope, key: &str, val: &str) -> LakeField {
    use LakeScope::*;
    let v = val.trim();
    let only_if = |ok: bool| {
        if ok {
            LakeField::Passive
        } else {
            LakeField::Unsupported
        }
    };
    // An enum value passes only as a TOML string (decoded like Lake's `ofString?`) or as a Lean
    // `.ctor` naming a real constructor: a qualified name (`Backend.default`) or a non-constructor
    // (`.C`) can name a lakefile's own helper, and any other expression is evaluated by Lake.
    let toml_str = v
        .starts_with(['"', '\''])
        .then(|| parse_toml_string(v).ok())
        .flatten();
    let dot_ctor = v.strip_prefix('.');
    let enum_is = |toml_ok: &dyn Fn(&str) -> bool, ctors: &[&str]| match (&toml_str, dot_ctor) {
        (Some(t), _) => toml_ok(t),
        (None, Some(c)) => ctors.contains(&c),
        _ => false,
    };
    const BUILD_TYPES: [&str; 3] = ["release", "relWithDebInfo", "minSizeRel"];
    // `[ ]` and multi-line empty arrays too (comments are already stripped).
    let compact: String = v.chars().filter(|c| !c.is_whitespace()).collect();
    let empty_array = matches!(compact.as_str(), "[]" | "#[]");
    match (scope, key) {
        (
            _,
            "moreLeancArgs"
            | "weakLeancArgs"
            | "moreLinkObjs"
            | "moreLinkLibs"
            | "moreLinkArgs"
            | "weakLinkArgs"
            | "moreServerOptions"
            | "requiresModuleSystem"
            | "allowNonModules",
        ) => LakeField::Passive,
        // Only `debug` adds an option (`debugAssertions`) to `lean`; the rest are `leanc` flags.
        (_, "buildType") => only_if(enum_is(
            &|t| {
                // Lake's TOML decoder decapitalizes the string.
                let mut cs = t.chars();
                let lower: String = cs
                    .next()
                    .map(|c| c.to_ascii_lowercase())
                    .into_iter()
                    .chain(cs)
                    .collect();
                BUILD_TYPES.contains(&lower.as_str())
            },
            &BUILD_TYPES,
        )),
        (_, "backend") => only_if(enum_is(
            &|t| matches!(t, "c" | "default"),
            &["c", "default"],
        )),
        (_, "precompileImports") => only_if(v == "false"),
        (_, "dynlibs" | "plugins") => only_if(empty_array),
        (_, "extraDepTargets") => only_if(empty_array),
        (Lib | Exe, "needs") => only_if(empty_array),
        (
            Package,
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
            | "testRunner"
            | "testDriverArgs"
            | "lintDriver"
            | "lintDriverArgs"
            | "releaseRepo"
            | "releaseRepo?"
            | "buildArchive"
            | "buildArchive?"
            | "preferReleaseBuild"
            | "moreServerArgs"
            | "moreGlobalServerArgs"
            | "fixedToolchain"
            | "restoreAllArtifacts"
            | "restoreAllArtifacts?"
            | "enableArtifactCache"
            | "enableArtifactCache?"
            | "libPrefixOnWindows"
            | "allowImportAll"
            | "builtinLint"
            | "builtinLint?"
            | "checks",
        ) => LakeField::Passive,
        (Package, "bootstrap") => only_if(v == "false"),
        (Lib, "libName" | "libPrefixOnWindows" | "allowImportAll") => LakeField::Passive,
        (Exe, "exeName") => LakeField::Passive,
        _ => LakeField::Unknown,
    }
}
/// A field turbo-lean cannot build like Lake: the root package fails closed now; a dependency
/// records `why` in `slot`, so only building one of its modules fails closed.
pub(super) fn unsupported_lake_field(slot: &mut Option<String>, is_root_pkg: bool, why: String) -> Result<()> {
    if is_root_pkg && !c_abi::verify_static_lake_config(true, true, false, false) {
        anyhow::bail!("{}: fail-closed static Lake config gate", why);
    }
    slot.get_or_insert(why);
    Ok(())
}
/// A `needs := [...]` in a `lakefile.toml` that actually names a target.
///
/// Such a `needs` fails closed for *every* package, so its call sites pass `is_root_pkg = true`
/// to [`unsupported_lake_field`]. Recording it in `unsupported` would only fail once one of the
/// package's own modules is built, but this parser reads no `input_file` / `input_dir`
/// declarations out of TOML (`[[input_dir]]` / `[[input_file]]` fail closed), so the named input
/// is one that nothing hashes: the digest and staleness callers that merely resolve the config
/// would see a clean config and vouch for a stale `.olean`.
pub(super) fn toml_needs_names_a_target(val: &str) -> bool {
    !parse_toml_string_array(val)
        .unwrap_or_else(|_| vec![val.to_string()])
        .is_empty()
}
/// Handle a field the parser does not read: pass it, or fail closed via
/// `unsupported_lake_field`.
pub(super) fn check_lake_field(
    slot: &mut Option<String>,
    is_root_pkg: bool,
    scope: LakeScope,
    key: &str,
    val: &str,
    location: impl FnOnce() -> String,
) -> Result<()> {
    let (what, passive) = match classify_lake_field(scope, key, val) {
        LakeField::Passive => ("", true),
        LakeField::Unsupported => ("Unsupported value for", false),
        LakeField::Unknown => ("Unsupported", false),
    };
    if c_abi::verify_static_lake_config(true, !passive, false, false) {
        return Ok(());
    }
    let scope_name = match scope {
        LakeScope::Package => "package",
        LakeScope::Lib => "lean_lib",
        LakeScope::Exe => "lean_exe",
    };
    unsupported_lake_field(
        slot,
        is_root_pkg,
        format!("{} {} field `{}` in {}", what, scope_name, key, location()),
    )
}
/// Check whether a passive field becomes unsupported for C object compilation vs shared/dynlib linking.
pub(super) fn classify_native_unsupported_field(
    scope: LakeScope,
    key: &str,
    val: &str,
    location: &dyn Fn() -> String,
) -> (Option<String>, Option<String>) {
    let v = val.trim();
    let compact: String = v.chars().filter(|c| !c.is_whitespace()).collect();
    let empty_array = matches!(compact.as_str(), "[]" | "#[]");
    let toml_str = v
        .starts_with(['"', '\''])
        .then(|| parse_toml_string(v).ok())
        .flatten();
    let dot_ctor = v.strip_prefix('.');
    match (scope, key) {
        (_, "moreLeancArgs" | "weakLeancArgs") if !empty_array => (
            Some(format!(
                "Non-empty native compiler field `{}` in {}",
                key,
                location()
            )),
            None,
        ),
        (_, "moreLinkObjs" | "moreLinkLibs" | "moreLinkArgs" | "weakLinkArgs") if !empty_array => (
            None,
            Some(format!(
                "Non-empty native linker field `{}` in {}",
                key,
                location()
            )),
        ),
        (_, "buildType") => {
            let is_release = match (&toml_str, dot_ctor) {
                (Some(t), _) => t.eq_ignore_ascii_case("release"),
                (None, Some(c)) => c == "release",
                _ => false,
            };
            if is_release {
                (None, None)
            } else {
                (
                    Some(format!(
                        "Non-release `buildType` (`{}`) for native precompilation in {}",
                        v,
                        location()
                    )),
                    None,
                )
            }
        }
        (LakeScope::Lib, "libName") => (
            None,
            Some(format!(
                "Custom `libName` (`{}`) for native precompilation in {}",
                v,
                location()
            )),
        ),
        (_, "libPrefixOnWindows") if v != "false" => (
            None,
            Some(format!(
                "Non-default `libPrefixOnWindows` (`{}`) for native precompilation in {}",
                v,
                location()
            )),
        ),
        _ => (None, None),
    }
}
/// `precompileLibrary` fails closed everywhere; `precompileModules` parses as a boolean and is
/// built natively in trusted mode (and rejected in untrusted mode).
pub(super) fn lake_precompile(key: &str, val: &str, location: &dyn Fn() -> String) -> Result<bool> {
    let on = parse_toml_bool(val)?;
    if key == "precompileLibrary" && !c_abi::verify_static_lake_config(true, on, false, false) {
        anyhow::bail!(
            "Unsupported `{} = true` in {}: Lake loads precompiled shared libraries turbo-lean does not build: fail-closed static Lake config gate",
            key,
            location()
        );
    }
    Ok(on)
}
/// Parse Lean DSL `platformIndependent : Option Bool` (`true`, `false`, `some true`, `some false`,
/// `none`, with optional outer parentheses). Anything else fails closed.
pub(super) fn parse_lean_option_bool(val: &str, location: &dyn Fn() -> String) -> Result<Option<bool>> {
    let mut s = val.trim();
    while let Some(inner) = s.strip_prefix('(').and_then(|r| r.strip_suffix(')')) {
        let t = inner.trim();
        if matches!(lean_scan(t, ""), Ok((_, 0))) {
            s = t;
        } else {
            break;
        }
    }
    match s {
        "none" | "Option.none" => Ok(None),
        "true" => Ok(Some(true)),
        "false" => Ok(Some(false)),
        _ => {
            if let Some(rest) = s
                .strip_prefix("some")
                .or_else(|| s.strip_prefix("Option.some"))
            {
                if rest.starts_with(char::is_whitespace) || rest.starts_with('(') {
                    let mut inner = rest.trim();
                    while let Some(p) = inner.strip_prefix('(').and_then(|r| r.strip_suffix(')')) {
                        let t = p.trim();
                        if matches!(lean_scan(t, ""), Ok((_, 0))) {
                            inner = t;
                        } else {
                            break;
                        }
                    }
                    match inner {
                        "true" => return Ok(Some(true)),
                        "false" => return Ok(Some(false)),
                        _ => {}
                    }
                }
            }
            let _ = c_abi::verify_static_lake_config(true, true, false, false);
            anyhow::bail!(
                "Unsupported `platformIndependent` expression `{}` in {}: fail-closed static Lake config gate",
                val.trim(),
                location()
            )
        }
    }
}
/// A token that starts a Lean or Lake command (`#eval`, `def`, `package`, ...).
pub(super) fn is_lean_command_token(t: &str) -> bool {
    (t.starts_with('#') && t.len() > 1)
        || matches!(
            t,
            "package"
                | "lean_lib"
                | "lean_exe"
                | "target"
                | "extern_lib"
                | "require"
                | "input_file"
                | "input_dir"
                | "post_update"
                | "script"
                | "lean_script"
                | "import"
                | "open"
                | "def"
                | "abbrev"
                | "theorem"
                | "instance"
                | "structure"
                | "inductive"
                | "class"
                | "axiom"
                | "opaque"
                | "example"
                | "mutual"
                | "deriving"
                | "attribute"
                | "set_option"
                | "namespace"
                | "section"
                | "end"
                | "universe"
                | "variable"
                | "include"
                | "omit"
                | "export"
                | "notation"
                | "infix"
                | "infixl"
                | "infixr"
                | "prefix"
                | "postfix"
                | "syntax"
                | "macro"
                | "macro_rules"
                | "elab"
                | "elab_rules"
                | "initialize"
                | "builtin_initialize"
                | "meta"
                | "run_cmd"
                | "run_elab"
                | "run_meta"
        )
}
/// Parse a static `lakefile.toml` file into `PackageConfig`.
/// Fails closed if unsupported dynamic targets, plugins, or facets are configured.
pub fn parse_lakefile_toml(
    pkg_root: &Path,
    toml_path: &Path,
    is_root_pkg: bool,
) -> Result<PackageConfig> {
    parse_lakefile_toml_inner(pkg_root, toml_path, is_root_pkg, true)
}

pub(crate) fn parse_lakefile_toml_without_disk_inputs(
    pkg_root: &Path,
    toml_path: &Path,
    is_root_pkg: bool,
) -> Result<PackageConfig> {
    parse_lakefile_toml_inner(pkg_root, toml_path, is_root_pkg, false)
}

pub(super) fn parse_lakefile_toml_inner(
    pkg_root: &Path,
    toml_path: &Path,
    is_root_pkg: bool,
    hash_inputs_from_disk: bool,
) -> Result<PackageConfig> {
    let raw = fs::read_to_string(toml_path)
        .with_context(|| format!("Failed to read {}", toml_path.display()))?;
    // The line-based reader below does not model multi-line TOML strings.
    if raw.contains("\"\"\"") || raw.contains("'''") {
        anyhow::bail!(
            "Unsupported multi-line string in {}: fail-closed static Lake config gate",
            toml_path.display()
        );
    }
    let raw_hash = blake3::hash(raw.as_bytes()).to_hex().to_string();
    let mut empty_roots: BTreeSet<usize> = BTreeSet::new();
    let default_pkg_name = pkg_root
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "lean-pkg".to_string());
    let mut pkg = PackageConfig {
        base_name: default_pkg_name.clone(),
        name: default_pkg_name,
        pkg_root: pkg_root.to_path_buf(),
        config_file_kind: "toml".to_string(),
        src_dir: PathBuf::from("."),
        build_dir: PathBuf::from(".lake/build"),
        bin_dir: PathBuf::from("bin"),
        lean_lib_dir: PathBuf::from("lib/lean"),
        native_lib_dir: PathBuf::from("lib"),
        ir_dir: PathBuf::from("ir"),
        packages_dir: PathBuf::from(".lake/packages"),
        more_lean_args: Vec::new(),
        weak_lean_args: Vec::new(),
        lean_options: BTreeMap::new(),
        precompile_modules: false,
        platform_independent: None,
        default_targets: Vec::new(),
        libs: Vec::new(),
        exes: Vec::new(),
        extern_libs: Vec::new(),
        custom_targets: Vec::new(),
        inputs: Vec::new(),
        config_digest: String::new(),
        pre_recipe_config_digest: String::new(),
        unsupported: None,
        native_unsupported: None,
        link_unsupported: None,
    };
    #[derive(Clone, PartialEq, Eq)]
    enum Section {
        Top,
        LeanOptions(Vec<String>),
        Require,
        LeanLib(usize),
        LeanLibOptions(usize, Vec<String>),
        LeanExe(usize),
        LeanExeOptions(usize, Vec<String>),
        ExternLib(usize),
    }
    let mut section = Section::Top;
    // Lake TOML `KeyTy` state (`Lake/Toml/Elab/Expression.lean`): redefining a key, or using a
    // key as both a value and a table/array/dotted prefix, is an elaboration error.
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum KeyTy {
        Value,
        StdTable,
        Array,
        DottedPrefix,
        HeaderPrefix,
    }
    impl KeyTy {
        fn label(self) -> &'static str {
            match self {
                KeyTy::Value => "value",
                KeyTy::StdTable => "table",
                KeyTy::Array => "array",
                KeyTy::DottedPrefix => "dotted",
                KeyTy::HeaderPrefix => "header",
            }
        }
    }
    #[derive(Clone)]
    struct TomlElabState {
        key_tys: BTreeMap<Vec<String>, KeyTy>,
        arr_key_tys: BTreeMap<Vec<String>, BTreeMap<Vec<String>, KeyTy>>,
        arr_parents: BTreeMap<Vec<String>, Vec<String>>,
        curr_arr_key: Vec<String>,
        curr_key: Vec<String>,
    }
    impl TomlElabState {
        fn new() -> Self {
            Self {
                key_tys: BTreeMap::new(),
                arr_key_tys: BTreeMap::new(),
                arr_parents: BTreeMap::new(),
                curr_arr_key: Vec::new(),
                curr_key: Vec::new(),
            }
        }
        fn elab_header_keys(
            &mut self,
            prefix_segs: &[String],
        ) -> std::result::Result<Vec<String>, String> {
            self.arr_key_tys
                .insert(self.curr_arr_key.clone(), self.key_tys.clone());
            self.curr_arr_key.clear();
            self.key_tys = self
                .arr_key_tys
                .get(&Vec::<String>::new())
                .cloned()
                .unwrap_or_default();
            let mut k = Vec::new();
            for seg in prefix_segs {
                k.push(seg.clone());
                if let Some(&ty) = self.key_tys.get(&k) {
                    match ty {
                        KeyTy::Array => {
                            let arr_map = self
                                .arr_key_tys
                                .get(&k)
                                .cloned()
                                .ok_or_else(|| format!("bad array key `{}`", k.join(".")))?;
                            self.key_tys = arr_map;
                            self.curr_arr_key = k.clone();
                        }
                        KeyTy::StdTable | KeyTy::HeaderPrefix | KeyTy::DottedPrefix => {}
                        _ => {
                            return Err(format!(
                                "cannot redefine {} key `{}`",
                                ty.label(),
                                k.join(".")
                            ));
                        }
                    }
                } else {
                    self.key_tys.insert(k.clone(), KeyTy::HeaderPrefix);
                }
            }
            Ok(k)
        }
        fn elab_std_table(&mut self, segs: &[String]) -> std::result::Result<(), String> {
            if segs.is_empty() {
                return Err("empty table header".to_string());
            }
            let mut k = self.elab_header_keys(&segs[..segs.len() - 1])?;
            k.push(segs[segs.len() - 1].clone());
            if let Some(&ty) = self.key_tys.get(&k) {
                if ty != KeyTy::HeaderPrefix {
                    return Err(format!(
                        "cannot redefine {} key `{}`",
                        ty.label(),
                        k.join(".")
                    ));
                }
            }
            self.curr_key = k.clone();
            self.key_tys.insert(k, KeyTy::StdTable);
            Ok(())
        }
        fn elab_array_table(&mut self, segs: &[String]) -> std::result::Result<(), String> {
            if segs.is_empty() {
                return Err("empty array table header".to_string());
            }
            let mut k = self.elab_header_keys(&segs[..segs.len() - 1])?;
            k.push(segs[segs.len() - 1].clone());
            if let Some(&ty) = self.key_tys.get(&k) {
                if ty == KeyTy::Array {
                    let parent = self
                        .arr_parents
                        .get(&k)
                        .and_then(|p| self.arr_key_tys.get(p))
                        .cloned()
                        .ok_or_else(|| format!("bad array key `{}`", k.join(".")))?;
                    self.key_tys = parent;
                    self.curr_key = k.clone();
                    self.curr_arr_key = k;
                } else {
                    return Err(format!(
                        "cannot redefine {} key `{}`",
                        ty.label(),
                        k.join(".")
                    ));
                }
            } else {
                self.key_tys.insert(k.clone(), KeyTy::Array);
                self.arr_key_tys
                    .insert(self.curr_arr_key.clone(), self.key_tys.clone());
                self.arr_parents
                    .insert(k.clone(), self.curr_arr_key.clone());
                self.curr_key = k.clone();
                self.curr_arr_key = k;
            }
            Ok(())
        }
        fn elab_keyval(&mut self, segs: &[String]) -> std::result::Result<(), String> {
            if segs.is_empty() {
                return Err("empty key".to_string());
            }
            let mut k = self.curr_key.clone();
            for seg in &segs[..segs.len() - 1] {
                k.push(seg.clone());
                if let Some(&ty) = self.key_tys.get(&k) {
                    if ty != KeyTy::DottedPrefix {
                        return Err(format!(
                            "cannot redefine {} key `{}`",
                            ty.label(),
                            k.join(".")
                        ));
                    }
                } else {
                    self.key_tys.insert(k.clone(), KeyTy::DottedPrefix);
                }
            }
            k.push(segs[segs.len() - 1].clone());
            if let Some(&ty) = self.key_tys.get(&k) {
                return Err(format!(
                    "cannot redefine {} key `{}`",
                    ty.label(),
                    k.join(".")
                ));
            }
            self.key_tys.insert(k, KeyTy::Value);
            Ok(())
        }
    }
    let mut toml_elab = TomlElabState::new();
    let key_err = |line_no: usize, msg: String| -> anyhow::Error {
        let _ = c_abi::verify_static_lake_config(true, true, false, false);
        anyhow::anyhow!(
            "{} in {} at line {}: fail-closed static Lake config gate",
            msg,
            toml_path.display(),
            line_no
        )
    };
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
                let sec_segs =
                    split_toml_dotted_key(sec_name).map_err(|e| key_err(line_no, e.to_string()))?;
                toml_elab
                    .elab_array_table(&sec_segs)
                    .map_err(|e| key_err(line_no, e))?;
                match sec_segs.as_slice() {
                    [head] if head == "require" => section = Section::Require,
                    [head] if head == "lean_lib" => {
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
                            platform_independent: None,
                            default_facets: Vec::new(),
                            is_default_target: false,
                            needs: Vec::new(),
                            custom_target_needs: Vec::new(),
                            unsupported: None,
                            native_unsupported: None,
                            link_unsupported: None,
                        });
                        section = Section::LeanLib(lib_idx);
                    }
                    [head] if head == "lean_exe" => {
                        let exe_idx = pkg.exes.len();
                        pkg.exes.push(LeanExeConfig {
                            name: String::new(),
                            exe_name: None,
                            src_dir: None,
                            root: String::new(),
                            support_interpreter: false,
                            more_lean_args: Vec::new(),
                            weak_lean_args: Vec::new(),
                            lean_options: BTreeMap::new(),
                            platform_independent: None,
                            is_default_target: false,
                            needs: Vec::new(),
                            custom_target_needs: Vec::new(),
                            unsupported: None,
                            native_unsupported: None,
                            link_unsupported: None,
                        });
                        section = Section::LeanExe(exe_idx);
                    }
                    [head] if head == "extern_lib" => {
                        let ext_idx = pkg.extern_libs.len();
                        pkg.extern_libs.push(ExternLibConfig {
                            name: String::new(),
                            is_dynamic_recipe: false,
                            static_artifact_path: None,
                            static_artifact_blake3: None,
                        });
                        section = Section::ExternLib(ext_idx);
                    }
                    _ => {
                        let _ = c_abi::verify_static_lake_config(true, true, false, false);
                        anyhow::bail!(
                            "Unsupported table array `[[{}]]` in {} at line {}: fail-closed static Lake config gate",
                            sec_name,
                            toml_path.display(),
                            line_no
                        );
                    }
                }
            } else {
                let sec_name = stripped[1..stripped.len() - 1].trim();
                let sec_segs =
                    split_toml_dotted_key(sec_name).map_err(|e| key_err(line_no, e.to_string()))?;
                toml_elab
                    .elab_std_table(&sec_segs)
                    .map_err(|e| key_err(line_no, e))?;
                match sec_segs.as_slice() {
                    [head, rest @ ..] if head == "leanOptions" => {
                        section = Section::LeanOptions(rest.to_vec());
                    }
                    [t, head, rest @ ..]
                        if t == "lean_lib" && head == "leanOptions" && !pkg.libs.is_empty() =>
                    {
                        section = Section::LeanLibOptions(pkg.libs.len() - 1, rest.to_vec());
                    }
                    [t, head, rest @ ..]
                        if t == "lean_exe" && head == "leanOptions" && !pkg.exes.is_empty() =>
                    {
                        section = Section::LeanExeOptions(pkg.exes.len() - 1, rest.to_vec());
                    }
                    _ => {
                        let _ = c_abi::verify_static_lake_config(true, true, false, false);
                        anyhow::bail!(
                            "Unsupported table `[{}]` in {} at line {}: fail-closed static Lake config gate",
                            sec_name,
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
        let key_segs =
            split_toml_dotted_key(raw_key).map_err(|e| key_err(line_no, e.to_string()))?;
        let key_owned = if key_segs.len() == 1 {
            key_segs[0].clone()
        } else {
            key_segs.join(".")
        };
        let key = key_owned.as_str();
        let mut val_accum = raw_val_start.trim().to_string();
        // Handle multi-line array `[...]` or inline table `{...}`
        while (val_accum.starts_with('[') || val_accum.starts_with('{'))
            && toml_expr_is_unclosed(&val_accum)
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
        toml_elab
            .elab_keyval(&key_segs)
            .map_err(|e| key_err(line_no, e))?;
        validate_toml_value_keys(&val_accum).map_err(|e| key_err(line_no, e.to_string()))?;
        let try_insert_dotted_lean_options =
            |map: &mut LeanOptionsMap, segs: &[String], raw_v: &str| -> Result<bool> {
                if segs.len() >= 2 && segs[0] == "leanOptions" {
                    let v_trim = raw_v.trim();
                    if v_trim.starts_with('{') && v_trim.ends_with('}') {
                        let tbl = parse_toml_lean_options_value(v_trim, &segs[1..])?;
                        for (k, v) in tbl {
                            if map.contains_key(&k) {
                                anyhow::bail!(
                                    "cannot redefine `leanOptions` key `{}` in lakefile.toml",
                                    k.to_lean_string()
                                );
                            }
                            map.insert(k, v);
                        }
                    } else {
                        let name =
                            LeanName(segs[1..].iter().cloned().map(LeanNamePart::Str).collect());
                        if map.contains_key(&name) {
                            anyhow::bail!(
                                "cannot redefine `leanOptions` key `{}` in lakefile.toml",
                                name.to_lean_string()
                            );
                        }
                        let val = parse_toml_lean_option_value(v_trim, &name.to_lean_string())?;
                        map.insert(name, val);
                    }
                    return Ok(true);
                }
                Ok(false)
            };
        let toml_path_field =
            || -> Result<PathBuf> { lake_rel_path(key, &parse_toml_string(&val_accum)?) };
        let location = || format!("{} at line {}", toml_path.display(), line_no);
        match &section {
            Section::Top => {
                if try_insert_dotted_lean_options(&mut pkg.lean_options, &key_segs, &val_accum)? {
                    continue;
                }
                match key {
                    "name" => {
                        let n = clean_lake_ident(&parse_toml_string(&val_accum)?);
                        pkg.base_name = n.clone();
                        pkg.name = n;
                    }
                    "srcDir" => pkg.src_dir = toml_path_field()?,
                    "buildDir" => pkg.build_dir = toml_path_field()?,
                    "leanLibDir" => pkg.lean_lib_dir = toml_path_field()?,
                    "nativeLibDir" => pkg.native_lib_dir = toml_path_field()?,
                    "irDir" => pkg.ir_dir = toml_path_field()?,
                    "packagesDir" => pkg.packages_dir = toml_path_field()?,
                    "binDir" => pkg.bin_dir = toml_path_field()?,
                    "defaultTargets" => {
                        pkg.default_targets = parse_toml_string_array(&val_accum)?
                            .into_iter()
                            .map(|s| clean_lake_ident(&s))
                            .collect();
                    }
                    "moreLeanArgs" => pkg.more_lean_args = parse_toml_string_array(&val_accum)?,
                    "weakLeanArgs" => pkg.weak_lean_args = parse_toml_string_array(&val_accum)?,
                    "precompileModules" => {
                        pkg.precompile_modules = lake_precompile(key, &val_accum, &location)?
                    }
                    "platformIndependent" => {
                        pkg.platform_independent = Some(parse_toml_bool(&val_accum)?)
                    }
                    "leanOptions" => {
                        let tbl = parse_toml_lean_options_value(&val_accum, &[])?;
                        pkg.lean_options.extend(tbl);
                    }
                    "needs" if toml_needs_names_a_target(&val_accum) => unsupported_lake_field(
                        &mut pkg.unsupported,
                        true,
                        format!("Unsupported `needs` in {}", location()),
                    )?,
                    other => {
                        let (c_why, l_why) = classify_native_unsupported_field(
                            LakeScope::Package,
                            other,
                            &val_accum,
                            &location,
                        );
                        if let Some(nwhy) = c_why {
                            pkg.native_unsupported.get_or_insert(nwhy);
                        }
                        if let Some(lwhy) = l_why {
                            pkg.link_unsupported.get_or_insert(lwhy);
                        }
                        check_lake_field(
                            &mut pkg.unsupported,
                            is_root_pkg,
                            LakeScope::Package,
                            other,
                            &val_accum,
                            location,
                        )?;
                    }
                }
            }
            Section::LeanOptions(prefix) => {
                insert_toml_lean_option_entry(&mut pkg.lean_options, prefix, raw_key, &val_accum)?;
            }
            Section::Require => {
                // Handled via lake-manifest.json and .lake/packages discovery
            }
            Section::LeanLib(i) => {
                let i = *i;
                let lib = &mut pkg.libs[i];
                if try_insert_dotted_lean_options(&mut lib.lean_options, &key_segs, &val_accum)? {
                    continue;
                }
                match key {
                    "name" => lib.name = clean_lake_ident(&parse_toml_string(&val_accum)?),
                    "srcDir" => lib.src_dir = Some(toml_path_field()?),
                    "roots" => {
                        lib.roots = parse_toml_string_array(&val_accum)?
                            .into_iter()
                            .map(|s| clean_lake_ident(&s))
                            .collect();
                        if lib.roots.is_empty() {
                            empty_roots.insert(i);
                        }
                    }
                    "globs" => lib.globs = nonempty(parse_toml_globs(&val_accum)?, "globs")?,
                    "moreLeanArgs" => lib.more_lean_args = parse_toml_string_array(&val_accum)?,
                    "weakLeanArgs" => lib.weak_lean_args = parse_toml_string_array(&val_accum)?,
                    "precompileModules" => {
                        lib.precompile_modules = Some(lake_precompile(key, &val_accum, &location)?)
                    }
                    "platformIndependent" => {
                        lib.platform_independent = Some(parse_toml_bool(&val_accum)?)
                    }
                    "precompileLibrary" => {
                        lake_precompile(key, &val_accum, &location)?;
                    }
                    "leanOptions" => {
                        let tbl = parse_toml_lean_options_value(&val_accum, &[])?;
                        lib.lean_options.extend(tbl);
                    }
                    // Lake's TOML decoder excludes `nativeFacets` (`Load/Toml.lean`), so it has
                    // no effect in a lakefile.toml.
                    "nativeFacets" => {}
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
                                    | "shared"
                                    | "default"
                                    | "modules"
                            ) {
                                let _ = c_abi::verify_static_lake_config(true, false, false, true);
                                unsupported_lake_field(
                                    &mut lib.unsupported,
                                    is_root_pkg,
                                    format!(
                                        "Unsupported defaultFacet `{}` on library `{}` in {}",
                                        f,
                                        lib.name,
                                        toml_path.display()
                                    ),
                                )?;
                            }
                        }
                        lib.default_facets = facets;
                    }
                    "needs" if toml_needs_names_a_target(&val_accum) => unsupported_lake_field(
                        &mut lib.unsupported,
                        true,
                        format!(
                            "Unsupported `needs` on library `{}` in {}",
                            lib.name,
                            location()
                        ),
                    )?,
                    other => {
                        let (c_why, l_why) = classify_native_unsupported_field(
                            LakeScope::Lib,
                            other,
                            &val_accum,
                            &location,
                        );
                        if let Some(nwhy) = c_why {
                            lib.native_unsupported.get_or_insert(nwhy);
                        }
                        if let Some(lwhy) = l_why {
                            lib.link_unsupported.get_or_insert(lwhy);
                        }
                        check_lake_field(
                            &mut lib.unsupported,
                            is_root_pkg,
                            LakeScope::Lib,
                            other,
                            &val_accum,
                            location,
                        )?;
                    }
                }
            }
            Section::LeanLibOptions(i, prefix) => {
                insert_toml_lean_option_entry(
                    &mut pkg.libs[*i].lean_options,
                    prefix,
                    raw_key,
                    &val_accum,
                )?;
            }
            Section::LeanExe(i) => {
                let exe = &mut pkg.exes[*i];
                if try_insert_dotted_lean_options(&mut exe.lean_options, &key_segs, &val_accum)? {
                    continue;
                }
                match key {
                    "name" => exe.name = clean_lake_ident(&parse_toml_string(&val_accum)?),
                    "exeName" => {
                        let p = toml_path_field()?;
                        exe.exe_name = Some(p.to_string_lossy().replace('\\', "/"));
                    }
                    "srcDir" => exe.src_dir = Some(toml_path_field()?),
                    "root" => exe.root = clean_lake_ident(&parse_toml_string(&val_accum)?),
                    "supportInterpreter" => exe.support_interpreter = parse_toml_bool(&val_accum)?,
                    "platformIndependent" => {
                        exe.platform_independent = Some(parse_toml_bool(&val_accum)?)
                    }
                    // Excluded by Lake's TOML decoder, as for `[[lean_lib]]`.
                    "nativeFacets" => {}
                    "moreLeanArgs" => exe.more_lean_args = parse_toml_string_array(&val_accum)?,
                    "weakLeanArgs" => exe.weak_lean_args = parse_toml_string_array(&val_accum)?,
                    "leanOptions" => {
                        let tbl = parse_toml_lean_options_value(&val_accum, &[])?;
                        exe.lean_options.extend(tbl);
                    }
                    "needs" if toml_needs_names_a_target(&val_accum) => unsupported_lake_field(
                        &mut exe.unsupported,
                        true,
                        format!(
                            "Unsupported `needs` on executable `{}` in {}",
                            exe.name,
                            location()
                        ),
                    )?,
                    other => {
                        let (c_why, l_why) = classify_native_unsupported_field(
                            LakeScope::Exe,
                            other,
                            &val_accum,
                            &location,
                        );
                        if let Some(nwhy) = c_why {
                            exe.native_unsupported.get_or_insert(nwhy);
                        }
                        if let Some(lwhy) = l_why {
                            exe.link_unsupported.get_or_insert(lwhy);
                        }
                        check_lake_field(
                            &mut exe.unsupported,
                            is_root_pkg,
                            LakeScope::Exe,
                            other,
                            &val_accum,
                            location,
                        )?;
                    }
                }
            }
            Section::LeanExeOptions(i, prefix) => {
                insert_toml_lean_option_entry(
                    &mut pkg.exes[*i].lean_options,
                    prefix,
                    raw_key,
                    &val_accum,
                )?;
            }
            Section::ExternLib(i) => {
                let ext = &mut pkg.extern_libs[*i];
                match key {
                    "name" => ext.name = clean_lake_ident(&parse_toml_string(&val_accum)?),
                    "path" => {
                        let p = pkg_root.join(toml_path_field()?);
                        if p.is_file() {
                            if let Ok(b) = fs::read(&p) {
                                ext.static_artifact_blake3 =
                                    Some(blake3::hash(&b).to_hex().to_string());
                                ext.static_artifact_path = Some(p);
                            }
                        }
                    }
                    other => unsupported_lake_field(
                        &mut pkg.unsupported,
                        is_root_pkg,
                        format!("Unsupported extern_lib field `{}` in {}", other, location()),
                    )?,
                }
            }
        }
    }
    check_empty_roots(&pkg, &empty_roots)?;
    finalize_package_config(
        &mut pkg,
        is_root_pkg,
        toml_path,
        &raw_hash,
        &empty_roots,
        hash_inputs_from_disk,
    )?;
    Ok(pkg)
}
pub(super) fn parse_lean_string_array_expr(expr: &str) -> Result<Vec<String>> {
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
    // The inner text must be balanced on its own, so `#["a"] ++ #["b"]` is not one literal.
    if !matches!(lean_scan(&s[1..s.len() - 1], ""), Ok((_, 0))) {
        anyhow::bail!(
            "Unsupported array expression `{}` in lakefile.lean (one `#[...]` literal only)",
            expr
        );
    }
    let inner = &s[1..s.len() - 1];
    let items = split_top_level_comma(inner)?;
    let mut out = Vec::with_capacity(items.len());
    for item in items {
        let t = item.trim();
        if t.starts_with('"') {
            out.push(plain_string_literal(t)?);
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
pub(super) fn parse_lean_ident_array_expr(expr: &str) -> Result<Vec<String>> {
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
    if !matches!(lean_scan(inner, ""), Ok((_, 0))) {
        anyhow::bail!(
            "Unsupported identifier array `{}` in lakefile.lean (one `#[...]` literal only)",
            expr
        );
    }
    let items = split_top_level_comma(inner)?;
    let mut out = Vec::with_capacity(items.len());
    for item in items {
        // A bare identifier may be a binding (`abbrev entry : Name := `Actual`), so only
        // name literals are read.
        out.push(lake_name_literal(&item, expr)?);
    }
    Ok(out)
}

/// `defaultFacets := #[...]` / `needs := #[...]`: names written bare (`LeanLib.staticFacet`) or
/// as name literals; callers check them (facet allowlist, `needs` against the package inputs).
pub(super) fn parse_lean_bare_name_array_expr(expr: &str, field: &str) -> Result<Vec<String>> {
    let s = expr.trim();
    let s = s.strip_prefix('#').map_or(s, str::trim_start);
    if !s.starts_with('[')
        || !s.ends_with(']')
        || !matches!(lean_scan(&s[1..s.len() - 1], ""), Ok((_, 0)))
    {
        anyhow::bail!(
            "Unsupported `{}` expression `{}` in lakefile.lean: fail-closed static Lake config gate",
            field,
            expr
        );
    }
    let mut out = Vec::new();
    for item in split_top_level_comma(&s[1..s.len() - 1])? {
        let cleaned = clean_lake_ident(&item);
        if cleaned.is_empty()
            || !cleaned
                .chars()
                .all(|c| c.is_alphanumeric() || matches!(c, '_' | '.'))
        {
            anyhow::bail!(
                "Unsupported `{}` entry `{}` in `{}`: fail-closed static Lake config gate",
                field,
                item,
                expr
            );
        }
        out.push(cleaned);
    }
    Ok(out)
}

/// A backtick name literal of plain dotted identifiers (or a `«...»` component of the
/// target-name alphabet), as its name string.
pub(super) fn lake_name_literal(item: &str, context: &str) -> Result<String> {
    let t = item.trim();
    let ok = t.strip_prefix('`').is_some_and(|name| {
        !name.starts_with('`')
            && name.split('.').all(|c| {
                let c = c
                    .strip_prefix('«')
                    .and_then(|c| c.strip_suffix('»'))
                    .unwrap_or(c);
                c.chars()
                    .next()
                    .is_some_and(|f| f.is_alphanumeric() || f == '_')
                    && c.chars().all(|ch| {
                        ch.is_alphanumeric() || matches!(ch, '_' | '\'' | '!' | '?' | '-')
                    })
            })
    });
    if !ok {
        anyhow::bail!(
            "Unsupported non-literal name `{}` in `{}` in lakefile.lean",
            t,
            context
        );
    }
    Ok(clean_lake_ident(t))
}
pub(super) fn parse_lean_globs_expr(expr: &str) -> Result<Vec<GlobSpec>> {
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
    if !matches!(lean_scan(inner, ""), Ok((_, 0))) {
        anyhow::bail!(
            "Unsupported `globs` expression `{}` in lakefile.lean (one `#[...]` literal only)",
            expr
        );
    }
    let items = split_top_level_comma(inner)?;
    let mut out = Vec::with_capacity(items.len());
    for item in items {
        let t = item.trim();
        if let Some(rest) = t
            .strip_prefix(".submodules ")
            .or_else(|| t.strip_prefix("Glob.submodules "))
        {
            out.push(GlobSpec::Submodules(lake_name_literal(rest, expr)?));
        } else if let Some(rest) = t
            .strip_prefix(".andSubmodules ")
            .or_else(|| t.strip_prefix("Glob.andSubmodules "))
        {
            out.push(GlobSpec::AndSubmodules(lake_name_literal(rest, expr)?));
        } else if let Some(rest) = t
            .strip_prefix(".one ")
            .or_else(|| t.strip_prefix("Glob.one "))
        {
            out.push(GlobSpec::One(lake_name_literal(rest, expr)?));
        } else if let Some(base) = t.strip_suffix(".+").filter(|_| t.starts_with('`')) {
            // Lake's name-literal glob syntax: `X.+ is X's submodules, `X.* adds X itself.
            out.push(GlobSpec::Submodules(lake_name_literal(base, expr)?));
        } else if let Some(base) = t.strip_suffix(".*").filter(|_| t.starts_with('`')) {
            out.push(GlobSpec::AndSubmodules(lake_name_literal(base, expr)?));
        } else if t.starts_with('`') {
            out.push(GlobSpec::One(lake_name_literal(t, expr)?));
        } else {
            anyhow::bail!("Unsupported glob expression `{}` in lakefile.lean", t);
        }
    }
    Ok(out)
}

/// Whether a `globs := #[...]` expression refers to `Glob` constructors by name (the spellings
/// `parse_lean_globs_expr` reads literally and a non-plain lakefile's declarations could
/// shadow), as opposed to backtick name-literal items, which cannot be shadowed even when a
/// name segment spells "Glob".
pub(super) fn glob_expr_names_constructors(expr: &str) -> bool {
    let mut s = expr.trim();
    if let Some(rest) = s.strip_prefix('#') {
        s = rest.trim_start();
    }
    let Some(inner) = s.strip_prefix('[').and_then(|r| r.strip_suffix(']')) else {
        // Not the one-literal shape `parse_lean_globs_expr` accepts; it fails closed there.
        return false;
    };
    let Ok(items) = split_top_level_comma(inner) else {
        return false;
    };
    items.iter().any(|item| {
        let t = item.trim();
        [
            "Glob.submodules ",
            "Glob.andSubmodules ",
            "Glob.one ",
            ".submodules ",
            ".andSubmodules ",
            ".one ",
        ]
        .iter()
        .any(|p| t.starts_with(p))
    })
}
/// An option name must be a backtick name literal (`Lean.Parser.identFnAux`). Bare identifiers
/// (`Name` values Lake would evaluate) and operators are rejected.
pub(super) fn lean_option_name_literal(raw: &str) -> Result<LeanName> {
    LeanName::from_backtick_literal(raw)
}

/// `v` is exactly one `"..."` token: its first unescaped closing quote is its last character
/// (so `"a" ++ "b"` is rejected).
pub(super) fn is_single_string_literal(v: &str) -> bool {
    let Some(body) = v.strip_prefix('"') else {
        return false;
    };
    let mut chars = body.char_indices();
    while let Some((i, c)) = chars.next() {
        match c {
            '\\' => {
                chars.next();
            }
            '"' => return i + 1 == body.len(),
            _ => {}
        }
    }
    false
}

/// A decimal literal exactly as Lean prints a `Nat` (no sign, no leading zero), so `-D` and
/// `setup.json` carry the value Lake would.
pub(super) fn is_canonical_nat(v: &str) -> bool {
    !v.is_empty()
        && v.bytes().all(|c| c.is_ascii_digit())
        && (v == "0" || !v.starts_with('0'))
        && v.parse::<u64>().is_ok()
}

/// The value of `t` if it is exactly one `"..."` token using only escapes that Lean and the
/// TOML decoder read identically.
pub(super) fn plain_string_literal(t: &str) -> Result<String> {
    let mut chars = t.chars();
    let mut plain = is_single_string_literal(t);
    while let Some(c) = chars.next() {
        if c == '\\' && !matches!(chars.next(), Some('\\' | '"' | 'n' | 't' | 'r')) {
            plain = false;
        }
    }
    if !plain {
        anyhow::bail!("Unsupported string expression `{}` in lakefile.lean", t);
    }
    parse_toml_string(t)
}

/// Normalise a `LeanOptionValue` literal: a bool, a natural number or a quoted string, optionally
/// wrapped in `LeanOptionValue.of*` / `.of*`. Anything else (e.g. a bare identifier, which would
/// otherwise reach Lean verbatim as `-Dkey=ident`) fails closed.
pub(super) fn lean_option_literal(raw: &str, key: &str) -> Result<LeanOptionValue> {
    let raw = raw.trim();
    let lit = |long: &str, short: &str, ok: fn(&str) -> bool| {
        Some(
            raw.strip_prefix(long)
                .or_else(|| raw.strip_prefix(short))
                .map_or(raw, str::trim),
        )
        .filter(|v| ok(v))
    };
    if let Some(b) = lit("LeanOptionValue.ofBool ", ".ofBool ", |v| {
        matches!(v, "true" | "false")
    }) {
        return Ok(LeanOptionValue::Bool(b == "true"));
    }
    if let Some(n) = lit("LeanOptionValue.ofNat ", ".ofNat ", is_canonical_nat) {
        return Ok(LeanOptionValue::Nat(n.parse::<u64>()?));
    }
    if let Some(q) = lit(
        "LeanOptionValue.ofString ",
        ".ofString ",
        is_single_string_literal,
    ) {
        // Only escapes that Lean and the TOML decoder read identically (no `\x`, `\u`, `\'`),
        // and no value that `-D`/`setup.json` would re-read as a bool or a number.
        let mut chars = q.chars();
        let mut plain_escapes = true;
        while let Some(c) = chars.next() {
            if c == '\\' && !matches!(chars.next(), Some('\\' | '"' | 'n' | 't' | 'r')) {
                plain_escapes = false;
            }
        }
        let v = parse_toml_string(q)?;
        if plain_escapes
            && !matches!(v.as_str(), "true" | "false")
            && v.parse::<u64>().is_err()
            && !v.chars().all(|c| c.is_ascii_digit())
            && !v.is_empty()
            && !v.chars().any(char::is_control)
        {
            return Ok(LeanOptionValue::Str(v));
        }
    }
    anyhow::bail!(
        "Unsupported non-literal `leanOptions` value `{}` for `{}`",
        raw,
        key
    )
}
/// Marker head for `leanOptions` entry forms Lake 4.35 rejects (`LeanOption.mk` applications,
/// `(k, v)` tuples): the lakefile reader downgrades this class to a dependency's `unsupported`
/// slot instead of refusing the whole workspace configuration.
pub(super) const LAKE_REJECTED_LEAN_OPTIONS_ENTRY: &str =
    "Unsupported `leanOptions` entry form Lake rejects";

pub(super) fn parse_lean_options_expr(expr: &str) -> Result<LeanOptionsMap> {
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
        return Ok(LeanOptionsMap::new());
    }
    let mut map = LeanOptionsMap::new();
    let (pairs, open) = lean_scan(inner, ",")?;
    if open != 0 {
        anyhow::bail!("Unclosed bracket in `leanOptions` expression `{}`", expr);
    }
    let pairs: Vec<String> = pairs.into_iter().filter(|p| !p.is_empty()).collect();
    for p in pairs {
        // #299: Lake 4.35 rejects plain `(k, v)` `Prod` tuples and explicit `LeanOption.mk`
        // applications in `leanOptions` arrays (unknown constants under the module system);
        // only the anonymous-constructor form `⟨k, v⟩` elaborates there.
        let trimmed = p
            .trim()
            .strip_prefix('⟨')
            .and_then(|r| r.strip_suffix('⟩'))
            .map(str::trim);
        if let Some(inner_pair) = trimmed {
            let Some((k_raw, v_raw)) = inner_pair.split_once(',') else {
                anyhow::bail!("Invalid `leanOptions` tuple `{}` in lakefile.lean", p);
            };
            let k = lean_option_name_literal(k_raw)?;
            let v = lean_option_literal(v_raw, &k.to_lean_string())?;
            map.insert(k, v);
        } else if {
            let t = p.trim();
            // Qualified spellings are the same rejected constant; a parenthesized ascription
            // `(⟨k, v⟩ : LeanOption)` is NOT a `(k, v)` tuple and takes the generic error.
            let unqualified = t
                .strip_prefix("Lake.")
                .or_else(|| t.strip_prefix("Lean."))
                .unwrap_or(t);
            unqualified
                .strip_prefix("LeanOption.mk")
                .is_some_and(|r| r.starts_with(char::is_whitespace))
                || t.strip_prefix('(')
                    .and_then(|r| r.strip_suffix(')'))
                    .is_some_and(|inner| {
                        !inner.trim_start().starts_with('⟨')
                            && lean_scan(inner, ",")
                                .is_ok_and(|(parts, depth)| depth == 0 && parts.len() >= 2)
                    })
        } {
            anyhow::bail!(
                "{LAKE_REJECTED_LEAN_OPTIONS_ENTRY}: `{}` in lakefile.lean (only the anonymous-constructor form `⟨k, v⟩` elaborates under Lake 4.35's module system)",
                p
            );
        } else {
            anyhow::bail!("Unsupported `leanOptions` entry `{}` in lakefile.lean", p);
        }
    }
    Ok(map)
}

/// Maximum identifier indirection depth when resolving `leanOptions` expressions.
pub(super) const LEAN_OPTIONS_MAX_DEPTH: usize = 16;

/// Lean-aware lexical scan of `s`: `"..."` strings (with `\` escapes) and char literals are
/// opaque, a `'` after an identifier character is a prime, and `()[]{}⟨⟩` must nest correctly.
/// Splits on `sep` at depth 0 (`sep` empty: no splitting) and returns the trimmed pieces plus
/// the final open-bracket depth.
pub(super) fn lean_scan(s: &str, sep: &str) -> Result<(Vec<String>, usize)> {
    let mut parts = Vec::new();
    let mut cur = String::new();
    let mut stack = Vec::new();
    let mut in_str = false;
    let mut prev_ident = false;
    let mut chars = s.char_indices().peekable();
    while let Some((i, c)) = chars.next() {
        let after_ident = std::mem::replace(
            &mut prev_ident,
            c.is_alphanumeric() || matches!(c, '_' | '\'' | '»' | '.'),
        );
        if !in_str && c == '\'' && !after_ident {
            // A char literal such as '[' or '"' is opaque; a prime after a name is not one.
            if let Some(end) = splitter::scan_lean_char_lit_end(s, i) {
                cur.push_str(&s[i..end]);
                while chars.peek().is_some_and(|(j, _)| *j < end) {
                    chars.next();
                }
                prev_ident = false;
                continue;
            }
        }
        if in_str {
            cur.push(c);
            if c == '\\' {
                if let Some((_, e)) = chars.next() {
                    cur.push(e);
                }
            } else if c == '"' {
                in_str = false;
            }
            continue;
        }
        match c {
            '"' => in_str = true,
            '(' | '[' | '{' | '⟨' => stack.push(c),
            ')' | ']' | '}' | '⟩' => {
                let open = match c {
                    ')' => '(',
                    ']' => '[',
                    '}' => '{',
                    _ => '⟨',
                };
                if stack.pop() != Some(open) {
                    anyhow::bail!("Mismatched `{}` in lakefile.lean expression `{}`", c, s);
                }
            }
            _ if stack.is_empty() && !sep.is_empty() && s[i..].starts_with(sep) => {
                for _ in 1..sep.chars().count() {
                    chars.next();
                }
                parts.push(std::mem::take(&mut cur).trim().to_string());
                continue;
            }
            _ => {}
        }
        cur.push(c);
    }
    if in_str {
        anyhow::bail!("Unclosed string in lakefile.lean expression `{}`", s);
    }
    parts.push(cur.trim().to_string());
    Ok((parts, stack.len()))
}

/// Column-0 parameterless `abbrev`/`def` bindings of a comment-stripped `lakefile.lean`, and the
/// names that must not be resolved statically (indented, declared more than once, with binders,
/// attributes or modifiers). A non-plain lakefile disables resolution entirely.
#[derive(Default)]
pub(super) struct LakefileBindings {
    /// name -> (body, first line, last line) of the declaration (1-based, comment-stripped).
    pub(super) defs: BTreeMap<String, (String, usize, usize)>,
    pub(super) rejected: std::collections::BTreeSet<String>,
    /// Names bound by any `abbrev` / `def` (including parameterised, modified or duplicate ones),
    /// so `input_file` / `input_dir` collisions with value declarations fail closed.
    pub(super) value_decls: std::collections::BTreeSet<String>,
    /// The lakefile is not plain (`lakefile_is_plain`): scopes, `where`, `open` or notation could
    /// change what an option expression denotes (even a literal one), so none is resolved.
    pub(super) scoped: bool,
}

/// Column-0 commands a "plain" Lake configuration may contain for its identifiers to be
/// resolved statically (Lake's own DSL plus option bindings; `post_update` hooks are blocks).
pub(super) const PLAIN_LAKEFILE_COMMANDS: [&str; 13] = [
    "import ",
    "require ",
    "package ",
    "lean_lib ",
    "lean_exe ",
    "input_file ",
    "input_dir ",
    "abbrev ",
    "def ",
    "nonrec def ",
    "target ",
    "extern_lib ",
    "post_update ",
];

/// Keywords that can introduce, scope or shadow bindings (declarations, scopes, `where`,
/// notation, `open`, modifiers, ...); see `lakefile_is_plain` for where they may appear.
pub(super) const BINDING_COMMANDS: [&str; 61] = [
    "where",
    "namespace",
    "section",
    "mutual",
    "end",
    "macro",
    "macro_rules",
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "syntax",
    "elab",
    "elab_rules",
    "open",
    "abbrev",
    "def",
    "theorem",
    "lemma",
    "axiom",
    "opaque",
    "constant",
    "instance",
    "structure",
    "inductive",
    "class",
    "attribute",
    "set_option",
    "export",
    "universe",
    "variable",
    "initialize",
    "builtin_initialize",
    "run_cmd",
    "run_elab",
    "run_meta",
    "with_weak_namespace",
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
    "nonrec",
    "public",
    "meta",
    "scoped",
    "local",
    "package",
    "lean_lib",
    "lean_exe",
    "require",
    "post_update",
    "target",
    "extern_lib",
    "script",
    "input_file",
    "input_dir",
    "in",
    ";",
];

/// Keep every lakefile.lean inside a lexical subset of Lean on which the line-based scanners
/// (`strip_lean_comments`, `lean_tokens_by_line`, `lean_scan`) agree with Lean. This is for
/// fidelity: soundness does not rest on it, because `is_allowed_lean_arg` admits only harmless
/// option keys and every compile forces `warn.sorry=true` and `debug.skipKernelTC=false`.
/// Rejects raw strings, char literals, `«»` anywhere but a target or `require` name, string braces
/// (interpolation) holding anything but one dotted name, `;`, `--` glued to an operator (Lean
/// lexes `<--` as `<-` `-`), non-ASCII letters in code (Lean's identifier boundaries differ from
/// Rust's), `#command`s, attributes other than Lake's target attributes, and every word in
/// `FORBIDDEN_IDENTS` (metaprogramming, elaboration-time IO, `buildType`). Returns `src` with
/// comments blanked byte for byte, as `strip_lean_comments` does, so the caller can check that
/// both lexers agree (`/--/` opens a doc comment in Lean and fails that check).
pub(super) fn lakefile_lexical_guard(
    src: &str,
    is_root_pkg: bool,
) -> std::result::Result<(String, String, BTreeSet<usize>), String> {
    const FORBIDDEN_IDENTS: [&str; 26] = [
        "run_io",
        "run_cmd",
        "run_elab",
        "run_meta",
        "run_tac",
        "buildType",
        "elab",
        "elab_rules",
        "macro",
        "macro_rules",
        "notation",
        "syntax",
        "declare_syntax_cat",
        "infix",
        "infixl",
        "infixr",
        "prefix",
        "postfix",
        "initialize",
        "builtin_initialize",
        "set_option",
        "local",
        "scoped",
        "attribute",
        "instance",
        "unsafe",
    ];
    let forbidden_word = |word: &str| -> std::result::Result<(), String> {
        match word.split('.').find(|s| FORBIDDEN_IDENTS.contains(s)) {
            Some(bad) => Err(format!("`{bad}`")),
            None => Ok(()),
        }
    };
    let mut out = String::with_capacity(src.len());
    let blank = |out: &mut String, c: char| {
        if c == '\n' {
            out.push('\n');
        } else {
            out.extend(std::iter::repeat_n(' ', c.len_utf8()));
        }
    };
    let mut chars = src.char_indices().peekable();
    let mut line_start = 0usize;
    let mut prev: Option<char> = None;
    // Byte spans of string interiors that cross a line break.
    let mut multiline_strings: Vec<(usize, usize)> = Vec::new();
    // 0-based lines a multi-line string starts, ends or runs through.
    let mut multiline_lines: BTreeSet<usize> = BTreeSet::new();
    while let Some((i, c)) = chars.next() {
        let next = chars.peek().map(|&(_, d)| d);
        if c == '-' && next == Some('-') {
            if prev.is_some_and(|p| {
                !(p.is_whitespace()
                    || p.is_ascii_alphanumeric()
                    || matches!(p, '_' | ')' | ']' | '}' | ','))
            }) {
                return Err(format!("`--` right after `{}`", prev.unwrap_or(' ')));
            }
            blank(&mut out, c);
            while let Some(&(_, d)) = chars.peek() {
                if d == '\n' {
                    break;
                }
                blank(&mut out, d);
                chars.next();
            }
            prev = None;
            continue;
        }
        if c == '/' && next == Some('-') {
            // Lean lexes `\/-` as `\/` `-` and `//-` as `//` `-` (operator tokens).
            if matches!(prev, Some('\\' | '/')) {
                return Err(format!("`/-` right after `{}`", prev.unwrap_or(' ')));
            }
            chars.next();
            out.push_str("  ");
            // Like Lean, `/--` and `/-!` open the comment as one token, so `/--/` stays open.
            if let Some(&(_, '-' | '!')) = chars.peek() {
                chars.next();
                out.push(' ');
            }
            let mut depth = 1usize;
            while depth > 0 {
                let Some((_, d)) = chars.next() else {
                    return Err("unterminated block comment".into());
                };
                let e = chars.peek().map(|&(_, e)| e);
                if (d == '/' && e == Some('-')) || (d == '-' && e == Some('/')) {
                    chars.next();
                    out.push_str("  ");
                    depth = if d == '/' { depth + 1 } else { depth - 1 };
                } else {
                    if d == '\n' {
                        line_start = out.len() + 1;
                    }
                    blank(&mut out, d);
                }
            }
            prev = None;
            continue;
        }
        if c == '"' {
            out.push('"');
            let body_start = out.len();
            loop {
                let Some((_, d)) = chars.next() else {
                    return Err("unterminated string literal".into());
                };
                out.push(d);
                match d {
                    '"' => break,
                    '\\' => {
                        let Some((_, e)) = chars.next() else {
                            return Err("unterminated string literal".into());
                        };
                        out.push(e);
                        if e == '\n' {
                            line_start = out.len();
                        }
                    }
                    '\n' => line_start = out.len(),
                    '{' => {
                        let mut name = String::new();
                        loop {
                            let Some((_, e)) = chars.next() else {
                                return Err("unterminated string literal".into());
                            };
                            out.push(e);
                            if e == '}' {
                                break;
                            }
                            name.push(e);
                        }
                        let dotted = name.split('.').all(|s| {
                            s.chars()
                                .next()
                                .is_some_and(|f| f.is_ascii_alphabetic() || f == '_')
                                && s.chars().all(|f| f.is_ascii_alphanumeric() || f == '_')
                        });
                        if !dotted {
                            return Err(format!(
                                "string braces `{{{name}}}` hold more than one dotted name"
                            ));
                        }
                        forbidden_word(&name)?;
                    }
                    '}' => return Err("unmatched `}` in a string literal".into()),
                    _ => {}
                }
            }
            let body_end = out.len() - 1;
            if out[body_start..body_end].contains('\n') {
                multiline_strings.push((body_start, body_end));
                let first = out[..body_start].matches('\n').count();
                let last = out[..body_end].matches('\n').count();
                multiline_lines.extend(first..=last);
            }
            prev = Some('"');
            continue;
        }
        // Words are consumed whole below, so a `'` or `r"`/`r#` seen here is never inside one.
        if c == '\'' {
            return Err("char literal".into());
        }
        if c == ';' && is_root_pkg {
            return Err("`;`".into());
        }
        if c == 'r' && matches!(next, Some('"' | '#')) {
            return Err("raw string literal".into());
        }
        if c == '#' && next.is_some_and(|d| d.is_alphabetic() || d == '_') {
            return Err("`#` command".into());
        }
        if c == '@'
            && next == Some('[')
            && !["@[default_target]", "@[test_driver]", "@[lint_driver]"]
                .iter()
                .any(|a| src[i..].starts_with(a))
        {
            return Err("attribute other than a Lake target attribute".into());
        }
        if c == '«' {
            let pre = &src[line_start..i];
            let mut head = pre.trim_end();
            for attr in ["@[default_target]", "@[test_driver]", "@[lint_driver]"] {
                if let Some(rest) = head.strip_prefix(attr) {
                    head = rest.trim_start();
                    break;
                }
            }
            let in_name_literal = matches!(prev, Some('`' | '.'));
            if !in_name_literal
                && (!matches!(
                    head,
                    "package" | "lean_lib" | "lean_exe" | "input_file" | "input_dir" | "require"
                ) || !pre.ends_with(char::is_whitespace))
            {
                return Err("`«»` outside a target name".into());
            }
            out.push(c);
            let mut name = String::new();
            loop {
                let Some((_, d)) = chars.next() else {
                    return Err("unterminated `«`".into());
                };
                out.push(d);
                if d == '»' {
                    break;
                }
                if !(d.is_ascii_alphanumeric()
                    || matches!(d, '_' | '-')
                    || (in_name_literal && d == '.'))
                {
                    return Err(format!("unsupported `{d}` inside `«»`"));
                }
                name.push(d);
            }
            if name.is_empty() || name.contains("--") {
                return Err("unsupported `«»` name".into());
            }
            prev = Some('»');
            continue;
        }
        if c == '»' {
            return Err("unmatched `»`".into());
        }
        if !c.is_ascii() && c.is_alphabetic() {
            return Err(format!(
                "non-ASCII letter `{c}` outside strings and comments"
            ));
        }
        if is_lean_id_first(c) {
            let mut end = i + c.len_utf8();
            while let Some(&(j, d)) = chars.peek() {
                // Like Lean, a `.` continues the name only when an identifier starts after it.
                let dot_continues =
                    d == '.' && src[j + 1..].chars().next().is_some_and(is_lean_id_first);
                if !(is_lean_id_rest(d) || dot_continues) {
                    break;
                }
                if !d.is_ascii() && d.is_alphabetic() {
                    return Err(format!(
                        "non-ASCII letter `{d}` outside strings and comments"
                    ));
                }
                end = j + d.len_utf8();
                chars.next();
            }
            let word = &src[i..end];
            forbidden_word(word)?;
            out.push_str(word);
            prev = word.chars().last();
            continue;
        }
        out.push(c);
        if c == '\n' {
            line_start = out.len();
        }
        prev = Some(c);
    }
    // Line-based declaration scanning must not read the lines inside a multi-line string
    // (a `lean_lib` there would become a phantom target).
    let mut flat = out.clone().into_bytes();
    for (a, b) in multiline_strings {
        for byte in &mut flat[a..b] {
            if *byte != b'\n' {
                *byte = b' ';
            }
        }
    }
    let flat = String::from_utf8(flat).expect("only ASCII spaces were written over whole chars");
    Ok((out, flat, multiline_lines))
}

/// Identifier-like tokens (plus `#command`s and `;`) of each line of `src`, skipping string
/// literals, char literals and backtick name literals. The scan runs over the whole file, so a
/// string spanning lines (Lean string gaps) stays a string on its continuation lines.
pub(super) fn lean_tokens_by_line(src: &str) -> Vec<Vec<&str>> {
    let mut lines = vec![Vec::new()];
    let mut chars = src.char_indices().peekable();
    let mut prev_ident = false;
    let mut in_str = false;
    let ident_char = |c: char| c.is_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?' | '.');
    while let Some((i, c)) = chars.next() {
        if c == '\n' {
            lines.push(Vec::new());
            prev_ident = false;
            continue;
        }
        if in_str {
            match c {
                '\\' => {
                    if chars.peek().is_some_and(|(_, d)| *d == '\n') {
                        continue;
                    }
                    chars.next();
                }
                '"' => in_str = false,
                _ => {}
            }
            continue;
        }
        let line = lines.last_mut().expect("at least one line");
        if c == '"' {
            in_str = true;
        } else if c == '\'' && !prev_ident {
            if let Some(end) = splitter::scan_lean_char_lit_end(src, i) {
                while chars.peek().is_some_and(|(j, _)| *j < end) {
                    chars.next();
                }
            }
        } else if c == '`' {
            while chars
                .peek()
                .is_some_and(|(_, d)| ident_char(*d) || matches!(d, '«' | '»'))
            {
                chars.next();
            }
        } else if c == ';' {
            line.push(";");
        } else if c.is_alphabetic()
            || c == '_'
            || (c == '#' && chars.peek().is_some_and(|(_, d)| d.is_alphabetic()))
        {
            let mut end = i + c.len_utf8();
            while let Some(&(j, d)) = chars.peek() {
                if !ident_char(d) {
                    break;
                }
                end = j + d.len_utf8();
                chars.next();
            }
            line.push(&src[i..end]);
            prev_ident = true;
            continue;
        }
        prev_ident = false;
    }
    lines
}

/// Whether identifier resolution may be trusted for this comment-stripped lakefile: every
/// column-0 line is a plain Lake command, an exact `open Lake DSL` form, a Lake target attribute
/// or a continuation; no indented line starts a binding command; and no binding keyword occurs
/// anywhere else on a line (commands can share a line), except a declaration's leading
/// `abbrev`/`def`, the allowed `open` lines and the trailing `where` of a target header.
/// Checked over every line, independently of body collection.
pub(super) fn lakefile_is_plain_with_policy(clean: &str, is_root_pkg: bool) -> bool {
    let tokens_by_line = lean_tokens_by_line(clean);
    let mut in_dep_recipe_body = false;
    clean.lines().zip(tokens_by_line).all(|(line, tokens)| {
        let t = line.trim();
        if t.is_empty() {
            return tokens.is_empty();
        }
        let indented = line.starts_with(char::is_whitespace);
        let inline_attr = ["@[default_target]", "@[test_driver]", "@[lint_driver]"]
            .iter()
            .any(|a| {
                t.strip_prefix(a).is_some_and(|rest| {
                    let rest = rest.trim();
                    // #299: Lake accepts an inline target attribute on any package's `where`,
                    // bare and `{` target headers alike (`lake init` emits the root inline
                    // `@[default_target] lean_exe ... where` form).
                    rest.starts_with("lean_lib ") || rest.starts_with("lean_exe ")
                })
            });
        let tokens = if inline_attr {
            &tokens[1..]
        } else {
            &tokens[..]
        };
        if !indented {
            in_dep_recipe_body = !is_root_pkg
                && [
                    "def ",
                    "nonrec def ",
                    "target ",
                    "extern_lib ",
                    "script ",
                    "lean_script ",
                    "post_update ",
                ]
                .iter()
                .any(|kw| t.starts_with(kw))
                && !t.starts_with([']', ')', '}', '⟩'])
                && !t.starts_with("++")
                && !t.starts_with("|>");
        }
        let header = matches!(
            tokens.first(),
            Some(&("package" | "lean_lib" | "lean_exe" | "input_file" | "input_dir"))
        );
        let open_line = matches!(
            t,
            "open Lake DSL"
                | "open System Lake DSL"
                | "open Lake DSL System"
                | "open Lake System DSL"
                | "open Lake"
        );
        let keywords_ok = tokens.iter().enumerate().all(|(i, tok)| {
            !(BINDING_COMMANDS.contains(tok) || tok.starts_with('#'))
                || (i == 0
                    && !indented
                    && matches!(
                        *tok,
                        "abbrev"
                            | "def"
                            | "nonrec"
                            | "package"
                            | "lean_lib"
                            | "lean_exe"
                            | "input_file"
                            | "input_dir"
                            | "target"
                            | "extern_lib"
                            | "require"
                            | "post_update"
                    ))
                || (i == 1 && !indented && tokens.first() == Some(&"nonrec") && *tok == "def")
                || (i == 0 && *tok == "open" && open_line)
                || (*tok == "where" && header && i + 1 == tokens.len())
                || (*tok == ";" && indented && in_dep_recipe_body)
        });
        if !keywords_ok {
            return false;
        }
        if indented {
            return splitter::strip_decl_prefixes(t).len() == t.len()
                && !splitter::is_section_header_line(t);
        }
        PLAIN_LAKEFILE_COMMANDS.iter().any(|c| t.starts_with(c))
            || open_line
            || ["@[default_target]", "@[test_driver]", "@[lint_driver]"]
                .iter()
                .any(|a| t.starts_with(a))
            || (!is_root_pkg && t == "}")
            || t.starts_with([']', ')'])
            || (t.starts_with(['}', '⟩']) && t.len() > 1)
            || (is_root_pkg && t.starts_with(['}', '⟩']))
            || t.starts_with("++")
            || t.starts_with("|>")
    })
}

#[cfg(test)]
pub(super) fn lakefile_is_plain(clean: &str) -> bool {
    lakefile_is_plain_with_policy(clean, true)
}

/// A body runs from `:=` until the next column-0 line once all brackets are closed; column-0
/// lines that close a bracket or continue with `++` still belong to it.
#[cfg(test)]
pub(super) fn collect_lakefile_abbrevs(clean: &str) -> LakefileBindings {
    collect_lakefile_abbrevs_with_policy(clean, true)
}

pub(super) fn collect_lakefile_abbrevs_with_policy(clean: &str, is_root_pkg: bool) -> LakefileBindings {
    let mut out = LakefileBindings {
        scoped: !lakefile_is_plain_with_policy(clean, is_root_pkg),
        ..Default::default()
    };
    let lines: Vec<&str> = clean.lines().collect();
    let mut attr_pending = false;
    let mut i = 0usize;
    while i < lines.len() {
        let line = lines[i];
        i += 1;
        let first_line = i;
        let indented = line.starts_with(char::is_whitespace);
        let t = line.trim();
        if t.is_empty() {
            continue;
        }
        // Attributes, `set_option ... in` and modifiers (same or previous line) make a
        // declaration unbindable; they are recognised by the splitter's command grammar.
        let decl = splitter::strip_decl_prefixes(t);
        let modified = std::mem::take(&mut attr_pending) || decl.len() != t.len();
        if decl.is_empty() {
            attr_pending = modified;
            continue;
        }
        // Lake target commands (`lean_lib`, `lean_exe`, `input_file`, `input_dir`, `extern_lib`,
        // `target`, `script`, `lean_script`) bind Lean identifiers in the lakefile namespace.
        // Reject any `abbrev`/`def` sharing a name with such a target so option resolution fails
        // closed on collisions in either declaration order.
        if let Some(target_rest) = [
            "lean_lib ",
            "lean_exe ",
            "input_file ",
            "input_dir ",
            "extern_lib ",
            "target ",
            "script ",
            "lean_script ",
        ]
        .iter()
        .find_map(|kw| decl.strip_prefix(kw))
        {
            let target_raw = target_rest.split_whitespace().next().unwrap_or("");
            let target_name = clean_lake_ident(target_raw.trim_end_matches('.'));
            if !target_name.is_empty() {
                out.defs.remove(&target_name);
                if target_name.contains('.') {
                    if let Some(last) = target_name.rsplit('.').next() {
                        out.defs.remove(last);
                        out.rejected.insert(last.to_string());
                    }
                }
                out.rejected.insert(target_name);
            }
            continue;
        }
        let Some(rest) = decl
            .strip_prefix("abbrev ")
            .or_else(|| decl.strip_prefix("def "))
            .or_else(|| t.strip_prefix("nonrec def "))
        else {
            continue;
        };
        let raw_name: String = rest
            .chars()
            .take_while(|c| !c.is_whitespace() && !matches!(c, ':' | '(' | '{' | '['))
            .collect();
        let name = clean_lake_ident(raw_name.trim_end_matches('.'));
        if name.is_empty() {
            continue;
        }
        out.value_decls.insert(name.clone());
        let header = rest[raw_name.len()..].trim_start();
        let body_start = match header.split_once(":=") {
            Some((ty, body)) if ty.trim().is_empty() || ty.starts_with(':') => Some(body),
            _ => None,
        };
        let mut body = body_start.unwrap_or_default().to_string();
        let mut lexed = lean_scan(&body, "");
        while i < lines.len() {
            let next = lines[i];
            let col0 = next.chars().next().is_some_and(|c| !c.is_whitespace());
            let nt = next.trim_start();
            let continues = nt.starts_with([']', ')', '}', '⟩'])
                || nt.starts_with("++")
                || nt.starts_with("|>");
            let open = lexed.as_ref().is_ok_and(|(_, d)| *d > 0);
            if col0 && !continues && !open {
                break;
            }
            body.push('\n');
            body.push_str(next);
            lexed = lean_scan(&body, "");
            i += 1;
        }
        let dotted = name.contains('.');
        let is_lake_pkg_ext = !is_root_pkg && name.starts_with("Lake.Package.");
        // `def LeanOption.mk ...` or `def LeanOptionValue.ofBool ...` would change what the
        // spellings the resolver reads mean, so such a lakefile is not plain.
        const RESERVED: [&str; 15] = [
            "LeanOption",
            "LeanOptionValue",
            "mk",
            "ofBool",
            "ofNat",
            "ofString",
            "true",
            "false",
            "weak",
            "Array",
            "Name",
            "Lake",
            "Lean",
            "Bool",
            "String",
        ];
        if (dotted && !is_lake_pkg_ext)
            || name
                .rsplit('.')
                .next()
                .is_some_and(|n| RESERVED.contains(&n))
        {
            out.scoped = true;
        }
        if modified
            || indented
            || dotted
            || body_start.is_none()
            || lexed.is_err()
            || out.defs.contains_key(&name)
        {
            out.defs.remove(&name);
            if let Some(last) = name
                .rsplit('.')
                .next()
                .filter(|_| dotted && !is_lake_pkg_ext)
            {
                out.defs.remove(last);
                out.rejected.insert(last.to_string());
            }
            out.rejected.insert(name);
        } else if !out.rejected.contains(&name) {
            out.defs
                .insert(name, (body.trim().to_string(), first_line, i));
        }
    }
    out
}

pub(super) fn is_lake_ident(s: &str) -> bool {
    s.chars()
        .next()
        .is_some_and(|c| c.is_alphabetic() || c == '_')
        && s.chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '.' || c == '\'')
}

/// Recognise `IDENT.map fun s ↦ { s with name := `weak ++ s.name }` (also `=>`), Mathlib's
/// idiom for passing options as `weak.`-prefixed, and return `IDENT`.
pub(super) fn parse_weak_prefix_map(expr: &str) -> Option<String> {
    let norm: String = expr.split_whitespace().collect::<Vec<_>>().join(" ");
    let (ident, rest) = norm.split_once(".map fun ")?;
    let (var, rest) = rest.split_once(' ')?;
    let rest = rest
        .strip_prefix("↦ ")
        .or_else(|| rest.strip_prefix("=> "))?;
    let expected = format!("{{ {var} with name := `weak ++ {var}.name }}");
    (rest == expected && is_lake_ident(ident) && is_lake_ident(var)).then(|| ident.to_string())
}

/// Statically resolve a `leanOptions` expression: literal arrays, top-level `++`,
/// parameterless top-level `abbrev`/`def` bindings of the same lakefile, parenthesised
/// subexpressions and the `weak.`-prefix `map`. Anything else fails closed; nothing is evaluated.
/// `line` is the (1-based) line of the expression: Lean elaborates declarations in order, so
/// only bindings that end before it are in scope.
pub(super) fn resolve_lean_options_expr(
    expr: &str,
    bindings: &LakefileBindings,
    line: usize,
) -> Result<LeanOptionsMap> {
    if bindings.scoped {
        anyhow::bail!(
            "Unsupported `leanOptions` expression `{}`: lakefile.lean is not plain (scopes, where, open, notation or metaprogramming)",
            expr.trim()
        );
    }
    resolve_lean_options_in(expr, bindings, line, 0, &mut BindingCache::default())
}

/// Each binding is resolved once (memoised), and a binding reached again while it is being
/// resolved is a cycle, so resolution is linear in the lakefile size.
#[derive(Default)]
pub(super) struct BindingCache {
    pub(super) done: BTreeMap<String, LeanOptionsMap>,
    pub(super) visiting: std::collections::BTreeSet<String>,
}

pub(super) fn resolve_lean_options_in(
    expr: &str,
    bindings: &LakefileBindings,
    line: usize,
    depth: usize,
    cache: &mut BindingCache,
) -> Result<LeanOptionsMap> {
    if depth > LEAN_OPTIONS_MAX_DEPTH {
        anyhow::bail!(
            "`leanOptions` expression `{}` nests deeper than {} in lakefile.lean",
            expr,
            LEAN_OPTIONS_MAX_DEPTH
        );
    }
    let (parts, _) = lean_scan(expr, "++")?;
    if parts.len() > 1 {
        let mut map = LeanOptionsMap::new();
        for part in &parts {
            // Pieces are strictly smaller, so `++` does not count towards the depth bound.
            map.extend(resolve_lean_options_in(part, bindings, line, depth, cache)?);
        }
        return Ok(map);
    }
    let s = expr.trim();
    let (pipes, _) = lean_scan(s, "|>")?;
    let (pushes, _) = lean_scan(s, ".push")?;
    let push = if pipes.len() > 1 {
        pipes
            .last()
            .and_then(|p| p.strip_prefix(".push"))
            .map(|elem| (pipes[..pipes.len() - 1].join(" |> "), elem.to_string()))
    } else if let Some(rest) = s
        .strip_prefix("Array.push")
        .filter(|r| r.starts_with(char::is_whitespace))
        .map(str::trim_start)
    {
        rest.char_indices().find_map(|(i, c)| {
            (c.is_whitespace() && lean_scan(&rest[..i], "").is_ok_and(|(_, d)| d == 0))
                .then(|| (rest[..i].to_string(), rest[i..].to_string()))
        })
    } else if pushes.len() > 1 {
        Some((
            pushes[..pushes.len() - 1].join(".push"),
            pushes.last().unwrap().clone(),
        ))
    } else {
        None
    };
    if let Some((base, elem)) = push {
        let mut elem = elem.trim();
        let mut nesting = depth + 1;
        while let Some(inner) = elem.strip_prefix('(').and_then(|r| r.strip_suffix(')')) {
            if !lean_scan(inner, "").is_ok_and(|(_, d)| d == 0) {
                break;
            }
            nesting += 1;
            anyhow::ensure!(
                nesting <= LEAN_OPTIONS_MAX_DEPTH,
                "`leanOptions` push nests too deeply"
            );
            elem = inner.trim();
        }
        anyhow::ensure!(
            !elem.is_empty() && lean_scan(elem, ",")?.0.len() == 1,
            "Expected one `leanOptions` push element"
        );
        let mut map = resolve_lean_options_in(&base, bindings, line, depth + 1, cache)?;
        map.extend(parse_lean_options_expr(&format!("#[{elem}]"))?);
        return Ok(map);
    }
    if s.starts_with('[') || s.starts_with("#[") {
        return parse_lean_options_expr(s);
    }
    if let Some(inner) = s.strip_prefix('(').and_then(|r| r.strip_suffix(')')) {
        if lean_scan(inner, "").is_ok_and(|(_, d)| d == 0) {
            return resolve_lean_options_in(inner, bindings, line, depth + 1, cache);
        }
    }
    let ident = if is_lake_ident(s) {
        Some((s.to_string(), false))
    } else {
        parse_weak_prefix_map(s).map(|i| (i, true))
    };
    if let Some((ident, weak)) = ident {
        if bindings.rejected.contains(&ident) {
            anyhow::bail!(
                "Unsupported `leanOptions` binding `{}` (scoped, duplicated, parameterised or in a non-plain lakefile) in lakefile.lean",
                ident
            );
        }
        if let Some((body, first, last)) = bindings.defs.get(&ident) {
            if *last >= line {
                anyhow::bail!(
                    "`leanOptions` binding `{}` is used before its declaration ends (line {}) in lakefile.lean",
                    ident,
                    last
                );
            }
            let map = match cache.done.get(&ident) {
                Some(map) => map.clone(),
                None => {
                    if !cache.visiting.insert(ident.clone()) {
                        anyhow::bail!("Cyclic `leanOptions` binding `{}` in lakefile.lean", ident);
                    }
                    let map = resolve_lean_options_in(body, bindings, *first, depth + 1, cache)?;
                    cache.visiting.remove(&ident);
                    cache.done.insert(ident.clone(), map.clone());
                    map
                }
            };
            return Ok(if weak {
                map.into_iter()
                    .map(|(k, v)| (k.with_weak_prefix(), v))
                    .collect()
            } else {
                map
            });
        }
    }
    parse_lean_options_expr(s)
}
/// `filter := .extension "<ext>"` or `.extension <| .mem #[...]` / `.extension (.mem #[...])`.
pub(super) fn lean_extension_filter(expr: &str) -> Option<(Option<String>, Option<Vec<String>>)> {
    let rest = expr.trim().strip_prefix(".extension")?.trim();
    if let Ok(single) = plain_string_literal(rest) {
        return Some((Some(single), None));
    }
    let mem_arg = if let Some(after_pipe) = rest.strip_prefix("<|") {
        after_pipe.trim().strip_prefix(".mem")?.trim()
    } else {
        let inner = rest.strip_prefix('(').and_then(|s| s.strip_suffix(')'))?;
        if !lean_scan(inner, "").is_ok_and(|(_, d)| d == 0) {
            return None;
        }
        inner.trim().strip_prefix(".mem")?.trim()
    };
    let arr = mem_arg.strip_prefix("#[")?.strip_suffix(']')?;
    if !lean_scan(arr, "").is_ok_and(|(_, d)| d == 0) {
        return None;
    }
    let items = split_top_level_comma(arr).ok()?;
    let mut exts = Vec::with_capacity(items.len());
    for item in items {
        let t = item.trim();
        if !t.starts_with('"') {
            return None;
        }
        exts.push(plain_string_literal(t).ok()?);
    }
    Some((None, Some(exts)))
}

pub(super) fn parse_lean_path_literal_with_bindings(
    field: &str,
    expr: &str,
    bindings: Option<(&LakefileBindings, usize)>,
) -> Result<PathBuf> {
    let s = expr.trim();
    if s.starts_with('"') {
        return lake_rel_path(field, &plain_string_literal(s)?);
    }
    if let Some((b, line)) = bindings {
        let resolve_seg = |seg: &str| -> Result<String> {
            let seg = seg.trim();
            if seg.starts_with('"') {
                return plain_string_literal(seg);
            }
            if is_lake_ident(seg) && !b.rejected.contains(seg) {
                if let Some((body, _, last)) = b.defs.get(seg) {
                    if *last < line {
                        let bt = body.trim();
                        if bt.starts_with('"') {
                            return plain_string_literal(bt);
                        }
                    }
                }
            }
            anyhow::bail!(
                "Unsupported non-literal path segment `{}` in `{}` in lakefile.lean",
                seg,
                expr
            )
        };
        if let Ok((parts, 0)) = lean_scan(s, "/") {
            if !parts.is_empty() && (parts.len() > 1 || is_lake_ident(s)) {
                let mut rel = String::new();
                for (idx, p) in parts.iter().enumerate() {
                    let seg = resolve_seg(p)?;
                    if idx > 0 && !rel.ends_with('/') && !seg.is_empty() {
                        rel.push('/');
                    }
                    rel.push_str(&seg);
                }
                return lake_rel_path(field, &rel);
            }
        }
    }
    anyhow::bail!(
        "Unsupported non-literal path expression `{}` in lakefile.lean",
        expr
    )
}

pub(super) fn parse_lean_path_literal(field: &str, expr: &str) -> Result<PathBuf> {
    parse_lean_path_literal_with_bindings(field, expr, None)
}
/// Extend `target` with a resolved `leanOptions` expression. The entry forms Lake 4.35 rejects
/// (`LeanOption.mk` applications, `(k, v)` tuples; `LAKE_REJECTED_LEAN_OPTIONS_ENTRY`) fail the
/// root package closed at parse time but only record `unsupported` on a dependency, so one
/// dependency's lakefile cannot refuse the whole workspace configuration; every other
/// resolution error keeps failing closed for every package.
pub(super) fn extend_lean_options_or_record(
    target: &mut LeanOptionsMap,
    slot: &mut Option<String>,
    val_accum: &str,
    bindings: &LakefileBindings,
    line_no: usize,
    is_root_pkg: bool,
    lean_path: &Path,
) -> Result<()> {
    match resolve_lean_options_expr(val_accum, bindings, line_no) {
        Ok(opts) => {
            target.extend(opts);
            Ok(())
        }
        Err(e) if !is_root_pkg && format!("{e:#}").contains(LAKE_REJECTED_LEAN_OPTIONS_ENTRY) => {
            unsupported_lake_field(
                slot,
                is_root_pkg,
                format!("{:#} in {} at line {}", e, lean_path.display(), line_no),
            )
        }
        Err(e) => Err(e),
    }
}

/// Parse a static declarative `lakefile.lean` into `PackageConfig`.
pub fn parse_lakefile_lean(
    pkg_root: &Path,
    lean_path: &Path,
    is_root_pkg: bool,
) -> Result<PackageConfig> {
    parse_lakefile_lean_inner(pkg_root, lean_path, is_root_pkg, true)
}

pub(crate) fn parse_lakefile_lean_without_disk_inputs(
    pkg_root: &Path,
    lean_path: &Path,
    is_root_pkg: bool,
) -> Result<PackageConfig> {
    parse_lakefile_lean_inner(pkg_root, lean_path, is_root_pkg, false)
}

pub(super) fn parse_lakefile_lean_inner(
    pkg_root: &Path,
    lean_path: &Path,
    is_root_pkg: bool,
    hash_inputs_from_disk: bool,
) -> Result<PackageConfig> {
    let raw = fs::read_to_string(lean_path)
        .with_context(|| format!("Failed to read {}", lean_path.display()))?;
    let raw_hash = blake3::hash(raw.as_bytes()).to_hex().to_string();
    let (guarded, flat, multiline_lines) =
        lakefile_lexical_guard(&raw, is_root_pkg).map_err(|e| {
            anyhow::anyhow!(
                "Unsupported Lean syntax in {}: {}: fail-closed static Lake config gate",
                lean_path.display(),
                e
            )
        })?;
    let clean = splitter::strip_lean_comments(&raw);
    if guarded != clean {
        anyhow::bail!(
            "Unsupported Lean syntax in {}: comment/string scanners disagree: fail-closed static Lake config gate",
            lean_path.display()
        );
    }
    let clean = flat;
    let lean_option_bindings = collect_lakefile_abbrevs_with_policy(&clean, is_root_pkg);
    // In a non-plain lakefile a `leanOptions` field or `needs` target reference can hide behind
    // `;`, `where`, `namespace` or notation, so its mere presence fails closed (rather than
    // parsing to fewer options or a shadowed input target). In a dependency lakefile whose only
    // non-plain trigger is a dotted helper (`def Lake.Package.foo ...`), `needs` may still name a
    // custom `target` (which marks that target's library `unsupported` below).
    let tokens_per_line = lean_tokens_by_line(&clean);
    if lean_option_bindings.scoped {
        let has_opt_tok = tokens_per_line.iter().any(|l| {
            l.iter()
                .any(|t| matches!(*t, "leanOptions" | "moreLeanArgs" | "weakLeanArgs"))
        });
        let has_needs_tok = tokens_per_line.iter().any(|l| l.contains(&"needs"));
        if has_opt_tok
            || (has_needs_tok
                && (is_root_pkg || !lakefile_is_plain_with_policy(&clean, is_root_pkg)))
        {
            anyhow::bail!(
                "Unsupported `leanOptions` / `needs` in {}: lakefile.lean is not plain (scopes, where, open, `;`, notation or metaprogramming)",
                lean_path.display()
            );
        }
    }
    // 1. Fail-closed scan for dynamic metaprogramming or script hooks. A dependency's
    //    `post_update`/`script` hooks and `def`/`target`/`extern_lib` recipe bodies never run when
    //    reusing or checking declarative Lean modules, so processes their bodies spawn only matter
    //    for the root (`extern_lib` static archives and `needs` on custom `target`s are gated
    //    separately); anything else marks the dependency unbuildable.
    let mut pkg_unsupported: Option<String> = None;
    let mut in_hook_body = false;
    for (idx, line) in clean.lines().enumerate() {
        let ln = idx + 1;
        let t = line.trim();
        if t.is_empty() {
            continue;
        }
        let is_hook = |w: &str| matches!(w, "script " | "lean_script " | "post_update");
        if !line.starts_with(char::is_whitespace) {
            in_hook_body = [
                "script ",
                "lean_script ",
                "post_update",
                "extern_lib ",
                "target ",
                "def ",
                "nonrec def ",
            ]
            .iter()
            .any(|h| t.starts_with(h));
        }
        for forbidden in [
            "meta if ",
            "meta if(",
            "run_cmd",
            "run_elab",
            "run_meta",
            "#eval",
            "elab ",
            "elab_rules",
            "macro ",
            "macro_rules",
            "script ",
            "lean_script ",
            "post_update",
            "IO.Process",
            "System.Process",
        ] {
            // `input_file` / `input_dir` / `needs :=` are declarative file inputs this parser
            // reads (into `pkg.inputs` / `lib.needs`) and folds into every cache key, so they are
            // no longer refused here; a `needs` naming no such target still fails closed below.
            let in_hook_ok = is_hook(forbidden)
                || (in_hook_body && matches!(forbidden, "IO.Process" | "System.Process"));
            if !is_root_pkg && in_hook_ok {
                continue;
            }
            if t.starts_with(forbidden) || t.contains(&format!(" {}", forbidden)) {
                unsupported_lake_field(
                    &mut pkg_unsupported,
                    is_root_pkg,
                    format!(
                        "Unsupported dynamic Lake construct `{}` in {} at line {}",
                        forbidden.trim(),
                        lean_path.display(),
                        ln
                    ),
                )?;
            }
        }
    }
    // 2. Lean commands may share a line or start at any column, so a command hidden after a
    //    declaration's keyword or inside a body the reader skips (helpers, hooks, `require`,
    //    field values) would configure Lake behind the parser's back.
    for (idx, (line, toks)) in clean.lines().zip(lean_tokens_by_line(&clean)).enumerate() {
        let mut cmds = toks.iter().filter(|t| is_lean_command_token(t));
        let hidden = if line.starts_with(char::is_whitespace) {
            cmds.next()
        } else {
            // A column-0 line may start one command (after an attribute and modifiers); a
            // command anywhere else on it (e.g. after a helper term's closing `]`) is hidden.
            let lead = line.trim_start();
            let lead = match lead.strip_prefix("@[") {
                Some(rest) => rest.find(']').map_or("", |e| rest[e + 1..].trim_start()),
                None => lead,
            };
            let lead_word = lead
                .split_whitespace()
                .find(|w| {
                    !matches!(
                        *w,
                        "private" | "protected" | "noncomputable" | "partial" | "unsafe" | "nonrec"
                    )
                })
                .unwrap_or("");
            let first = cmds.next();
            cmds.next().or(first.filter(|c| **c != lead_word))
        };
        if let Some(cmd) = hidden {
            unsupported_lake_field(
                &mut pkg_unsupported,
                is_root_pkg,
                format!(
                    "Unsupported embedded command `{}` in {} at line {}",
                    cmd,
                    lean_path.display(),
                    idx + 1
                ),
            )?;
        }
    }
    let default_pkg_name = pkg_root
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "lean-pkg".to_string());
    let mut pkg = PackageConfig {
        base_name: default_pkg_name.clone(),
        name: default_pkg_name,
        pkg_root: pkg_root.to_path_buf(),
        config_file_kind: "lean".to_string(),
        src_dir: PathBuf::from("."),
        build_dir: PathBuf::from(".lake/build"),
        bin_dir: PathBuf::from("bin"),
        lean_lib_dir: PathBuf::from("lib/lean"),
        native_lib_dir: PathBuf::from("lib"),
        ir_dir: PathBuf::from("ir"),
        packages_dir: PathBuf::from(".lake/packages"),
        more_lean_args: Vec::new(),
        weak_lean_args: Vec::new(),
        lean_options: BTreeMap::new(),
        precompile_modules: false,
        platform_independent: None,
        default_targets: Vec::new(),
        libs: Vec::new(),
        exes: Vec::new(),
        extern_libs: Vec::new(),
        custom_targets: Vec::new(),
        inputs: Vec::new(),
        config_digest: String::new(),
        pre_recipe_config_digest: String::new(),
        unsupported: pkg_unsupported,
        native_unsupported: None,
        link_unsupported: None,
    };
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum DeclBlock {
        None,
        Package { braced: bool },
        Require,
        LeanLib { idx: usize, braced: bool },
        LeanExe { idx: usize, braced: bool },
        Input(usize),
        CustomDoBlock,
    }
    impl FromDeclBlock for DeclBlock {
        fn none() -> Self {
            Self::None
        }
        fn package(braced: bool) -> Self {
            Self::Package { braced }
        }
        fn require() -> Self {
            Self::Require
        }
        fn lean_lib(idx: usize, braced: bool) -> Self {
            Self::LeanLib { idx, braced }
        }
        fn lean_exe(idx: usize, braced: bool) -> Self {
            Self::LeanExe { idx, braced }
        }
        fn input(idx: usize) -> Self {
            Self::Input(idx)
        }
        fn custom_do() -> Self {
            Self::CustomDoBlock
        }
    }
    let mut current_block = DeclBlock::None;
    let mut pending_default_target = false;
    let mut empty_roots: BTreeSet<usize> = BTreeSet::new();
    // Lake keeps only the last assignment of a repeated field; fail closed instead.
    let mut block_keys: BTreeSet<String> = BTreeSet::new();
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
        let braced = matches!(
            current_block,
            DeclBlock::Package { braced: true }
                | DeclBlock::LeanLib { braced: true, .. }
                | DeclBlock::LeanExe { braced: true, .. }
        );
        if braced && trimmed == "}" {
            current_block = DeclBlock::None;
            block_keys.clear();
            continue;
        }
        // A target declared on an indented line would be skipped below; Lake reads it.
        if indent > 0
            && trimmed.split_whitespace().next().is_some_and(|w| {
                matches!(
                    w,
                    "package"
                        | "lean_lib"
                        | "lean_exe"
                        | "input_file"
                        | "input_dir"
                        | "target"
                        | "extern_lib"
                        | "require"
                )
            })
        {
            anyhow::bail!(
                "Unsupported indented declaration `{}` in {} at line {}: fail-closed static Lake config gate",
                trimmed,
                lean_path.display(),
                line_no
            );
        }
        if indent == 0 && braced {
            anyhow::bail!(
                "Unclosed braced Lake declaration before `{}` in {} at line {}: fail-closed static Lake config gate",
                trimmed,
                lean_path.display(),
                line_no
            );
        }
        // Lake continues a field's expression on a column-0 `++` or closing-bracket line; the
        // field reader above stops at column 0, so such a line fails closed.
        if indent == 0
            && matches!(
                current_block,
                DeclBlock::Package { .. }
                    | DeclBlock::LeanLib { .. }
                    | DeclBlock::LeanExe { .. }
                    | DeclBlock::Input(_)
            )
            && (trimmed.starts_with("++")
                || trimmed.starts_with("|>")
                || trimmed.starts_with([']', ')', '}', '⟩']))
        {
            anyhow::bail!(
                "Unsupported column-0 continuation `{}` in {} at line {}: fail-closed static Lake config gate",
                trimmed,
                lean_path.display(),
                line_no
            );
        }
        if indent == 0 {
            block_keys.clear();
            // A helper's term (e.g. Mathlib's `abbrev ... := #[` ... `]`) continues on a
            // column-0 closing-bracket or `++` line; no command starts that way.
            if current_block == DeclBlock::CustomDoBlock
                && (trimmed.starts_with("++")
                    || trimmed.starts_with("|>")
                    || trimmed.starts_with([']', ')', '}', '⟩']))
            {
                continue;
            }
            // `@[test_driver]` / `@[lint_driver]` mark a target like `@[default_target]` does,
            // without making it a default target.
            let mut after = trimmed;
            while let Some(attr) = ["@[default_target]", "@[test_driver]", "@[lint_driver]"]
                .into_iter()
                .find(|a| after.starts_with(a))
            {
                pending_default_target |= attr == "@[default_target]";
                after = after[attr.len()..].trim();
            }
            if after != trimmed {
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
            DeclBlock::Package { .. }
            | DeclBlock::LeanLib { .. }
            | DeclBlock::LeanExe { .. }
            | DeclBlock::Input(_) => {
                if tokens_per_line
                    .get(line_no - 1)
                    .is_some_and(|l| l.contains(&";"))
                {
                    anyhow::bail!(
                        "Unsupported Lean syntax in {}: `;` inside declaration block at line {}: fail-closed static Lake config gate",
                        lean_path.display(),
                        line_no
                    );
                }
                let Some((k_raw, v_start)) = trimmed.split_once(":=") else {
                    let slot = match current_block {
                        DeclBlock::LeanLib { idx, .. } => &mut pkg.libs[idx].unsupported,
                        DeclBlock::LeanExe { idx, .. } => &mut pkg.exes[idx].unsupported,
                        _ => &mut pkg.unsupported,
                    };
                    unsupported_lake_field(
                        slot,
                        is_root_pkg,
                        format!(
                            "Unsupported statement `{}` inside declaration block in {} at line {}",
                            trimmed,
                            lean_path.display(),
                            line_no
                        ),
                    )?;
                    continue;
                };
                let key = k_raw.trim();
                // `toLeanConfig := { ... }` / `toLeanConfig.leanOptions := ...` set the same
                // options through the parent structure; never skip them silently.
                if key.starts_with("to") && key[2..].starts_with(|c: char| c.is_ascii_uppercase())
                    || key.contains('.')
                {
                    anyhow::bail!(
                        "Unsupported field `{}` in {} at line {}: fail-closed static Lake config gate",
                        key,
                        lean_path.display(),
                        line_no
                    );
                }
                if !block_keys.insert(key.to_string()) {
                    anyhow::bail!(
                        "Duplicate field `{}` in {} at line {}: fail-closed static Lake config gate",
                        key,
                        lean_path.display(),
                        line_no
                    );
                }
                let mut val_accum = v_start.trim().to_string();
                // A field's expression continues while it is empty or has open brackets, on
                // deeper-indented lines (fields of a `where` block share one column), and on
                // same-column lines that start with `++` or a closing bracket.
                let open_depth = |v: &str| lean_scan(v, "").map_or(1, |(_, d)| d);
                loop {
                    let needs_more = val_accum.is_empty() || open_depth(&val_accum) > 0;
                    let next = lines[i..].iter().position(|l| !l.trim().is_empty());
                    let Some(off) = next else {
                        if needs_more {
                            anyhow::bail!(
                                "Unclosed array expression for `{}` in {} starting at line {}",
                                key,
                                lean_path.display(),
                                line_no
                            );
                        }
                        break;
                    };
                    let next = lines[i + off];
                    let next_indent = next.len() - next.trim_start().len();
                    let next_t = next.trim();
                    if braced && next_t == "}" && !needs_more {
                        break;
                    }
                    let continues = next_indent > indent
                        || (next_indent == indent
                            && (next_t.starts_with("++")
                                || next_t.starts_with("|>")
                                || next_t.starts_with([']', ')', '}', '⟩'])));
                    if !needs_more && !continues {
                        break;
                    }
                    val_accum.push(' ');
                    val_accum.push_str(next_t);
                    i += off + 1;
                }
                // The declaration scanner reads multi-line string interiors as blanks, so a
                // field whose value uses one (e.g. a string gap) cannot be read faithfully.
                if (line_no - 1..i).any(|l| multiline_lines.contains(&l)) {
                    anyhow::bail!(
                        "Unsupported multi-line string in field `{}` in {} at line {}: fail-closed static Lake config gate",
                        key,
                        lean_path.display(),
                        line_no
                    );
                }
                let location = || format!("{} at line {}", lean_path.display(), line_no);
                match current_block {
                    DeclBlock::Package { .. } => match key {
                        "binDir" => pkg.bin_dir = parse_lean_path_literal(key, &val_accum)?,
                        "nativeLibDir" => {
                            pkg.native_lib_dir = parse_lean_path_literal(key, &val_accum)?
                        }
                        "srcDir" => pkg.src_dir = parse_lean_path_literal(key, &val_accum)?,
                        "buildDir" => pkg.build_dir = parse_lean_path_literal(key, &val_accum)?,
                        "leanLibDir" => {
                            pkg.lean_lib_dir = parse_lean_path_literal(key, &val_accum)?
                        }
                        "irDir" => pkg.ir_dir = parse_lean_path_literal(key, &val_accum)?,
                        "packagesDir" => {
                            pkg.packages_dir = parse_lean_path_literal(key, &val_accum)?
                        }
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
                            pkg.precompile_modules = lake_precompile(key, &val_accum, &location)?;
                        }
                        "platformIndependent" => {
                            pkg.platform_independent =
                                parse_lean_option_bool(&val_accum, &location)?;
                        }
                        "leanOptions" => {
                            extend_lean_options_or_record(
                                &mut pkg.lean_options,
                                &mut pkg.unsupported,
                                &val_accum,
                                &lean_option_bindings,
                                line_no,
                                is_root_pkg,
                                lean_path,
                            )?;
                        }
                        other => {
                            let (c_why, l_why) = classify_native_unsupported_field(
                                LakeScope::Package,
                                other,
                                &val_accum,
                                &location,
                            );
                            if let Some(nwhy) = c_why {
                                pkg.native_unsupported.get_or_insert(nwhy);
                            }
                            if let Some(lwhy) = l_why {
                                pkg.link_unsupported.get_or_insert(lwhy);
                            }
                            check_lake_field(
                                &mut pkg.unsupported,
                                is_root_pkg,
                                LakeScope::Package,
                                other,
                                &val_accum,
                                location,
                            )?;
                        }
                    },
                    DeclBlock::LeanLib { idx: lib_idx, .. } => {
                        let lib = &mut pkg.libs[lib_idx];
                        match key {
                            "srcDir" => {
                                lib.src_dir = Some(parse_lean_path_literal(key, &val_accum)?)
                            }
                            "roots" => {
                                lib.roots = parse_lean_ident_array_expr(&val_accum)?;
                                if lib.roots.is_empty() {
                                    empty_roots.insert(lib_idx);
                                }
                            }
                            "globs" => {
                                // #299: a non-plain lakefile can shadow the `Glob` constructor
                                // spellings this parser reads literally (e.g.
                                // `def Glob.submodules ... := .one`), so constructor-named glob
                                // items fail closed there like `leanOptions` bindings do;
                                // backtick name-literal globs cannot be shadowed and still parse.
                                if lean_option_bindings.scoped
                                    && glob_expr_names_constructors(&val_accum)
                                {
                                    unsupported_lake_field(
                                        &mut lib.unsupported,
                                        is_root_pkg,
                                        format!(
                                            "Unsupported `globs` constructor expression `{}` in non-plain {} at line {} (a declaration could shadow `Glob` constructors)",
                                            val_accum,
                                            lean_path.display(),
                                            line_no
                                        ),
                                    )?;
                                }
                                lib.globs = nonempty(parse_lean_globs_expr(&val_accum)?, "globs")?
                            }
                            "moreLeanArgs" => {
                                lib.more_lean_args = parse_lean_string_array_expr(&val_accum)?;
                            }
                            "weakLeanArgs" => {
                                lib.weak_lean_args = parse_lean_string_array_expr(&val_accum)?;
                            }
                            "precompileModules" => {
                                lib.precompile_modules =
                                    Some(lake_precompile(key, &val_accum, &location)?);
                            }
                            "platformIndependent" => {
                                lib.platform_independent =
                                    parse_lean_option_bool(&val_accum, &location)?;
                            }
                            "precompileLibrary" => {
                                lake_precompile(key, &val_accum, &location)?;
                            }
                            "leanOptions" => {
                                extend_lean_options_or_record(
                                    &mut lib.lean_options,
                                    &mut lib.unsupported,
                                    &val_accum,
                                    &lean_option_bindings,
                                    line_no,
                                    is_root_pkg,
                                    lean_path,
                                )?;
                            }
                            "needs" => {
                                let needs = parse_lean_bare_name_array_expr(&val_accum, key)?;
                                let mut input_needs = Vec::with_capacity(needs.len());
                                let mut custom_needs = Vec::new();
                                for n in needs {
                                    if pkg.inputs.iter().any(|i| i.name == n) {
                                        input_needs.push(n);
                                    } else if !is_root_pkg && pkg.custom_targets.contains(&n) {
                                        custom_needs.push(n.clone());
                                        unsupported_lake_field(
                                            &mut lib.unsupported,
                                            is_root_pkg,
                                            format!(
                                                "Unsupported `needs` custom target `{}` on library `{}` in {} at line {}",
                                                n,
                                                lib.name,
                                                lean_path.display(),
                                                line_no
                                            ),
                                        )?;
                                    } else {
                                        if is_root_pkg {
                                            let _ = c_abi::verify_static_lake_config(
                                                true, true, false, false,
                                            );
                                        }
                                        anyhow::bail!(
                                            "Unsupported `needs` entry `{}` on library `{}` in {} at line {} (not a previously declared `input_file` / `input_dir` of the package): fail-closed static Lake config gate",
                                            n,
                                            lib.name,
                                            lean_path.display(),
                                            line_no
                                        );
                                    }
                                }
                                lib.needs = input_needs;
                                lib.custom_target_needs = custom_needs;
                            }
                            "defaultFacets" => {
                                let facets = parse_lean_bare_name_array_expr(&val_accum, key)?;
                                for f in &facets {
                                    if !matches!(
                                        f.as_str(),
                                        "leanArts"
                                            | "LeanLib.leanArtsFacet"
                                            | "olean"
                                            | "ilean"
                                            | "c"
                                            | "static"
                                            | "LeanLib.staticFacet"
                                            | "shared"
                                            | "LeanLib.sharedFacet"
                                            | "default"
                                            | "modules"
                                    ) {
                                        let _ = c_abi::verify_static_lake_config(
                                            true, false, false, true,
                                        );
                                        unsupported_lake_field(
                                            &mut lib.unsupported,
                                            is_root_pkg,
                                            format!(
                                                "Unsupported defaultFacet `{}` on library `{}` in {}",
                                                f,
                                                lib.name,
                                                lean_path.display()
                                            ),
                                        )?;
                                    }
                                }
                                lib.default_facets = facets;
                            }
                            other => {
                                let (c_why, l_why) = classify_native_unsupported_field(
                                    LakeScope::Lib,
                                    other,
                                    &val_accum,
                                    &location,
                                );
                                if let Some(nwhy) = c_why {
                                    lib.native_unsupported.get_or_insert(nwhy);
                                }
                                if let Some(lwhy) = l_why {
                                    lib.link_unsupported.get_or_insert(lwhy);
                                }
                                check_lake_field(
                                    &mut lib.unsupported,
                                    is_root_pkg,
                                    LakeScope::Lib,
                                    other,
                                    &val_accum,
                                    location,
                                )?;
                            }
                        }
                    }
                    DeclBlock::LeanExe { idx: exe_idx, .. } => {
                        let exe = &mut pkg.exes[exe_idx];
                        match key {
                            "exeName" => {
                                let p = parse_lean_path_literal(key, &val_accum)?;
                                exe.exe_name = Some(p.to_string_lossy().replace('\\', "/"));
                            }
                            "srcDir" => {
                                exe.src_dir = Some(parse_lean_path_literal(key, &val_accum)?)
                            }
                            "root" => exe.root = lake_name_literal(&val_accum, "root")?,
                            "supportInterpreter" => {
                                exe.support_interpreter = parse_toml_bool(&val_accum)?;
                            }
                            "platformIndependent" => {
                                exe.platform_independent =
                                    parse_lean_option_bool(&val_accum, &location)?;
                            }
                            "moreLeanArgs" => {
                                exe.more_lean_args = parse_lean_string_array_expr(&val_accum)?;
                            }
                            "weakLeanArgs" => {
                                exe.weak_lean_args = parse_lean_string_array_expr(&val_accum)?;
                            }
                            "leanOptions" => {
                                extend_lean_options_or_record(
                                    &mut exe.lean_options,
                                    &mut exe.unsupported,
                                    &val_accum,
                                    &lean_option_bindings,
                                    line_no,
                                    is_root_pkg,
                                    lean_path,
                                )?;
                            }
                            "needs" => {
                                let needs = parse_lean_bare_name_array_expr(&val_accum, key)?;
                                let mut input_needs = Vec::with_capacity(needs.len());
                                let mut custom_needs = Vec::new();
                                for n in needs {
                                    if pkg.inputs.iter().any(|i| i.name == n) {
                                        input_needs.push(n);
                                    } else if !is_root_pkg && pkg.custom_targets.contains(&n) {
                                        custom_needs.push(n.clone());
                                        unsupported_lake_field(
                                            &mut exe.unsupported,
                                            is_root_pkg,
                                            format!(
                                                "Unsupported `needs` custom target `{}` on executable `{}` in {} at line {}",
                                                n,
                                                exe.name,
                                                lean_path.display(),
                                                line_no
                                            ),
                                        )?;
                                    } else {
                                        if is_root_pkg {
                                            let _ = c_abi::verify_static_lake_config(
                                                true, true, false, false,
                                            );
                                        }
                                        anyhow::bail!(
                                            "Unsupported `needs` entry `{}` on executable `{}` in {} at line {} (not a previously declared `input_file` / `input_dir` of the package): fail-closed static Lake config gate",
                                            n,
                                            exe.name,
                                            lean_path.display(),
                                            line_no
                                        );
                                    }
                                }
                                exe.needs = input_needs;
                                exe.custom_target_needs = custom_needs;
                            }
                            other => {
                                let (c_why, l_why) = classify_native_unsupported_field(
                                    LakeScope::Exe,
                                    other,
                                    &val_accum,
                                    &location,
                                );
                                if let Some(nwhy) = c_why {
                                    exe.native_unsupported.get_or_insert(nwhy);
                                }
                                if let Some(lwhy) = l_why {
                                    exe.link_unsupported.get_or_insert(lwhy);
                                }
                                check_lake_field(
                                    &mut exe.unsupported,
                                    is_root_pkg,
                                    LakeScope::Exe,
                                    other,
                                    &val_accum,
                                    location,
                                )?;
                            }
                        }
                    }
                    DeclBlock::Input(input_idx) => {
                        let input = &mut pkg.inputs[input_idx];
                        // A `filter` that is not `.extension "<ext>"` keeps every file of the
                        // directory, so the digest an unrecognised filter produces is always a
                        // superset -- but a superset is not the same set Lake hashes, and the
                        // field could equally be one that makes Lake read files this parser never
                        // selects. So an unknown field and an unrecognised filter take the same
                        // route as every other dependency field: the root package fails closed
                        // here, a dependency records `why` and fails closed once its inputs are
                        // what a key depends on (see `InputTargetConfig::unsupported`).
                        let ext = (key == "filter" && input.is_dir)
                            .then(|| lean_extension_filter(&val_accum))
                            .flatten();
                        match key {
                            "path" => {
                                let bindings_opt = (!is_root_pkg
                                    && !lean_option_bindings.scoped
                                    && lakefile_is_plain_with_policy(&clean, false))
                                .then_some((&lean_option_bindings, line_no));
                                input.path =
                                    checked_input_path(&parse_lean_path_literal_with_bindings(
                                        key,
                                        &val_accum,
                                        bindings_opt,
                                    )?)?
                            }
                            "text" => input.text = parse_toml_bool(&val_accum)?,
                            "filter" if ext.is_some() => {
                                let (single, multi) = ext.unwrap();
                                input.extension = single;
                                input.extensions = multi;
                            }
                            other => {
                                let why = format!(
                                    "Unsupported `{}` field `{} := {}` in {} at line {} (only `path`, `text` and `filter := .extension \"<ext>\"`)",
                                    if input.is_dir { "input_dir" } else { "input_file" },
                                    other,
                                    val_accum,
                                    lean_path.display(),
                                    line_no
                                );
                                unsupported_lake_field(&mut input.unsupported, is_root_pkg, why)?;
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    if matches!(
        current_block,
        DeclBlock::Package { braced: true }
            | DeclBlock::LeanLib { braced: true, .. }
            | DeclBlock::LeanExe { braced: true, .. }
    ) {
        anyhow::bail!(
            "Unclosed braced Lake declaration in {}: fail-closed static Lake config gate",
            lean_path.display()
        );
    }
    check_empty_roots(&pkg, &empty_roots)?;
    if let Some(inp) = pkg
        .inputs
        .iter()
        .find(|i| lean_option_bindings.value_decls.contains(&i.name))
    {
        if is_root_pkg {
            let _ = c_abi::verify_static_lake_config(true, true, false, false);
        }
        anyhow::bail!(
            "Conflicting `abbrev`/`def` and Lake input target `{}` in {}: fail-closed static Lake config gate",
            inp.name,
            lean_path.display()
        );
    }
    finalize_package_config(
        &mut pkg,
        is_root_pkg,
        lean_path,
        &raw_hash,
        &empty_roots,
        hash_inputs_from_disk,
    )?;
    Ok(pkg)
}
#[allow(clippy::too_many_arguments)]
pub(super) fn process_top_level_lake_decl<T>(
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
    if let Some(mods) = trimmed.strip_prefix("import ") {
        // Another import could bring syntax or elaborators that change what the declarations
        // read here mean to Lake.
        if mods.split_whitespace().any(|m| m != "Lake") {
            unsupported_lake_field(
                &mut pkg.unsupported,
                is_root_pkg,
                format!(
                    "Unsupported lakefile import `{}` in {} at line {}",
                    trimmed,
                    lean_path.display(),
                    line_no
                ),
            )?;
        }
        *current_block = T::none();
        return Ok(());
    }
    if trimmed.starts_with("open ") {
        *current_block = T::none();
        return Ok(());
    }
    // Lake also accepts `{ field := ... }` and `:=` after a target name; only `where` blocks are
    // parsed here, so anything else after the name fails closed.
    for kw in ["package", "lean_lib", "lean_exe", "input_file", "input_dir"] {
        let Some(rest) = trimmed.strip_prefix(kw) else {
            continue;
        };
        if rest.starts_with(|c: char| is_lean_id_rest(c) || c == '.') {
            continue; // a longer word such as `packageFoo`
        }
        {
            let mut words = rest.split_whitespace();
            let name_ok = rest.starts_with(char::is_whitespace)
                && words.next().is_some_and(|n| {
                    // `«name»` or Lake's `"name"` (`lake init` emits `package "demo" where`).
                    let quoted = n.len() >= 2 && n.starts_with('"') && n.ends_with('"');
                    let n = n
                        .strip_prefix('"')
                        .and_then(|n| n.strip_suffix('"'))
                        .unwrap_or(n);
                    // #299: a dot inside a quoted TARGET header is one atomic `Name.mkSimple`
                    // segment to Lake (`lean_lib "Foo.Bar"` builds `Foo.Bar.lean`), while this
                    // parser would split it into `Foo/Bar.lean`: fail closed. That covers
                    // quoted dotted INPUT names too, whose atomic name a dotted `needs` entry
                    // (two components, which Lake would never resolve to the input) would
                    // otherwise match here by string equality. Only a quoted package name keeps
                    // parsing: it never becomes a source path, and `lake init foo.bar` emits one.
                    if quoted && n.contains('.') && kw != "package" {
                        return false;
                    }
                    n.split('.').all(|seg| {
                        let seg = seg
                            .strip_prefix('«')
                            .and_then(|s| s.strip_suffix('»'))
                            .unwrap_or(seg);
                        !seg.is_empty()
                            && seg
                                .chars()
                                .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '\''))
                    })
                });
            let tail = (words.next(), words.next());
            let tail_ok = matches!(tail, (None | Some("where"), None))
                || (!is_root_pkg
                    && matches!(kw, "package" | "lean_lib" | "lean_exe")
                    && tail == (Some("{"), None));
            if !name_ok || !tail_ok {
                anyhow::bail!(
                    "Unsupported `{}` header `{}` in {} at line {}: fail-closed static Lake config gate",
                    kw.trim(),
                    trimmed,
                    lean_path.display(),
                    line_no
                );
            }
        }
    }
    if let Some(rest) = trimmed.strip_prefix("package ") {
        let name_part = rest.split_whitespace().next().unwrap_or("");
        let n = clean_lake_ident(name_part);
        pkg.base_name = n.clone();
        pkg.name = n;
        *current_block = T::package(trimmed.ends_with('{'));
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
            platform_independent: None,
            default_facets: Vec::new(),
            is_default_target: is_def,
            needs: Vec::new(),
            custom_target_needs: Vec::new(),
            unsupported: None,
            native_unsupported: None,
            link_unsupported: None,
        });
        *current_block = T::lean_lib(idx, trimmed.ends_with('{'));
        return Ok(());
    }
    if let Some(rest) = trimmed.strip_prefix("lean_exe ") {
        let name_part = rest.split_whitespace().next().unwrap_or("");
        let exe_name = clean_lake_ident(name_part);
        let idx = pkg.exes.len();
        pkg.exes.push(LeanExeConfig {
            name: exe_name.clone(),
            exe_name: None,
            src_dir: None,
            root: exe_name,
            support_interpreter: false,
            more_lean_args: Vec::new(),
            weak_lean_args: Vec::new(),
            lean_options: BTreeMap::new(),
            platform_independent: None,
            is_default_target: is_def,
            needs: Vec::new(),
            custom_target_needs: Vec::new(),
            unsupported: None,
            native_unsupported: None,
            link_unsupported: None,
        });
        *current_block = T::lean_exe(idx, trimmed.ends_with('{'));
        return Ok(());
    }
    for (kw, is_dir) in [("input_file ", false), ("input_dir ", true)] {
        if let Some(rest) = trimmed.strip_prefix(kw) {
            let name = clean_lake_ident(rest.split_whitespace().next().unwrap_or(""));
            pkg.inputs.push(InputTargetConfig {
                // Lake's default `path` is the target name.
                path: PathBuf::from(&name),
                name,
                is_dir,
                extension: None,
                extensions: None,
                text: false,
                blake3: String::new(),
                lake_hash: String::new(),
                unsupported: None,
            });
            *current_block = T::input(pkg.inputs.len() - 1);
            return Ok(());
        }
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
    // A dependency may define helpers (only literal field values are read, so a helper cannot
    // reach the config) and update/script hooks; any other command could change what Lake builds.
    let inert_dep_decl = ["abbrev ", "def ", "nonrec def ", "post_update ", "script "]
        .iter()
        .any(|kw| trimmed.starts_with(kw));
    if !inert_dep_decl {
        unsupported_lake_field(
            &mut pkg.unsupported,
            is_root_pkg,
            format!(
                "Unsupported top-level declaration `{}` in {} at line {}",
                trimmed,
                lean_path.display(),
                line_no
            ),
        )?;
    } else if is_root_pkg {
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
pub(super) trait FromDeclBlock {
    fn none() -> Self;
    fn package(braced: bool) -> Self;
    fn require() -> Self;
    fn lean_lib(idx: usize, braced: bool) -> Self;
    fn lean_exe(idx: usize, braced: bool) -> Self;
    fn input(idx: usize) -> Self;
    fn custom_do() -> Self;
}
/// Option keys a package may set (with or without the `weak.` prefix), via `leanOptions` or
/// `-D` flags. An allowlist, so no lakefile, however it is parsed, can reach options that weaken
/// checking (`debug.skipKernelTC`, `debug.*AsSorry`), run programs (`sat.solver`) or write
/// files (`trace.profiler.output`). `warn.sorry` may only be `true` and `debug.skipKernelTC`
/// only `false`; both are forced on every compile anyway.
pub(super) fn is_allowed_lean_option(key: &LeanName, value: &LeanOptionValue) -> bool {
    if key.0.is_empty()
        || key.is_inaccessible_user_name()
        || key.has_macro_scopes()
        || key.maybe_pseudo_syntax()
        || key.0.iter().any(|p| match p {
            LeanNamePart::Str(s) => {
                s.is_empty() || s.contains('»') || s.chars().any(char::is_control)
            }
            LeanNamePart::Num(_) => false,
        })
    {
        return false;
    }
    if let LeanOptionValue::Str(s) = value {
        if s.is_empty() || s.chars().any(char::is_control) {
            return false;
        }
    }
    let rem = match key.0.as_slice() {
        [LeanNamePart::Str(w), rest @ ..] if w == "weak" && !rest.is_empty() => rest,
        other => other,
    };
    let str_parts: Option<Vec<&str>> = rem
        .iter()
        .map(|p| match p {
            LeanNamePart::Str(s) => Some(s.as_str()),
            LeanNamePart::Num(_) => None,
        })
        .collect();
    if let Some(sp) = str_parts.as_deref() {
        match sp {
            ["warn", "sorry"] => return matches!(value, LeanOptionValue::Bool(true)),
            ["debug", "skipKernelTC"] => return matches!(value, LeanOptionValue::Bool(false)),
            // Not `pp.*` in general: `pp.all`, `pp.raw`, `pp.maxSteps`, ... change how the
            // `declaration uses 'sorry'` warning prints.
            ["pp", "unicode", "fun"]
            | ["pp", "mvars", "anonymous"]
            | ["autoImplicit"]
            | ["relaxedAutoImplicit"]
            | ["maxHeartbeats"]
            | ["maxRecDepth"]
            | ["maxSynthPendingDepth"]
            | ["synthInstance", "maxHeartbeats"]
            | ["synthInstance", "maxSize"]
            | ["warningAsError"]
            | ["exponentiation", "threshold"] => return true,
            _ => {}
        }
    }
    matches!(
        rem,
        [LeanNamePart::Str(ns), _, ..]
            if matches!(ns.as_str(), "linter" | "backward" | "experimental")
    )
}

/// Strict allowlist check for Lean compiler flags configured in `moreLeanArgs` / `weakLeanArgs`.
/// Rejects attached short flags (`-ofoo`, `-cfoo`, `-Rfoo`, `-ifoo`), long-option prefixes (`--plug`,
/// `--load-dyn`), `--run`, `--bc`, `--stdin`, and positional arguments.
pub fn is_allowed_lean_arg(arg: &str) -> bool {
    // Checked exactly as passed on: callers hand `arg` itself to Lean and setup.json.
    let t = arg;
    if t.is_empty() || t != t.trim() || !t.starts_with('-') || t.chars().any(char::is_control) {
        return false;
    }
    if let Some(kv) = t.strip_prefix("-D") {
        let Some((k, v)) = kv.split_once('=') else {
            return false;
        };
        if k.is_empty() || v.is_empty() || v.chars().any(char::is_control) {
            return false;
        }
        let Ok(name) = LeanName::from_str_to_name(k) else {
            return false;
        };
        if name.to_lean_string() != k {
            return false;
        }
        let val = if v == "true" {
            LeanOptionValue::Bool(true)
        } else if v == "false" {
            LeanOptionValue::Bool(false)
        } else if is_canonical_nat(v) {
            let Ok(n) = v.parse::<u64>() else {
                return false;
            };
            LeanOptionValue::Nat(n)
        } else if v.bytes().all(|b| b.is_ascii_digit()) {
            return false;
        } else {
            LeanOptionValue::Str(v.to_string())
        };
        return is_allowed_lean_option(&name, &val);
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

/// Fail closed at request/process boundaries using the static Lake argument policy.
/// Validate before filtering output-format flags or looking up cached verification results.
pub fn validate_lean_args(args: impl IntoIterator<Item = impl AsRef<str>>) -> Result<()> {
    let args: Vec<String> = args
        .into_iter()
        .map(|arg| arg.as_ref().to_string())
        .collect();
    validate_effective_lean_args(&args)
        .map(drop)
        .map_err(|error| anyhow::anyhow!("{error:#}: fail-closed static Lake config gate"))
}

/// Filter and normalize Lean compiler flags via `is_allowed_lean_arg`, dropping output-format
/// flags (`--json`, `-q`, `--quiet`): they never change elaboration, and callers that parse
/// plain-text `lean` output (`#print axioms`, determinism checks) must not receive them.
pub fn filter_allowed_lean_args<I, S>(args: I) -> Vec<String>
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    args.into_iter()
        .map(|s| s.as_ref().trim().to_string())
        .filter(|s| is_allowed_lean_arg(s) && !matches!(s.as_str(), "--json" | "-q" | "--quiet"))
        .collect()
}

/// Validate effective compiler options before any cache lookup or verification.
/// Output-format flags are not effective options: silently dropping them would alias an
/// invalid request with the legacy empty-option namespace.
pub fn validate_effective_lean_args(args: &[String]) -> Result<Vec<String>> {
    args.iter()
        .map(|arg| {
            let arg = arg.as_str();
            anyhow::ensure!(
                is_allowed_lean_arg(arg) && !matches!(arg, "--json" | "-q" | "--quiet"),
                "Unsupported effective Lean compiler flag `{arg}`"
            );
            Ok(arg.to_string())
        })
        .collect()
}

/// Validate and digest effective options; only truly empty input has the legacy identity.
pub fn compute_lean_args_digest(args: &[String]) -> Result<Option<String>> {
    Ok(effective_lean_args_digest(&validate_effective_lean_args(
        args,
    )?))
}

/// Hash an already validated effective option list without filtering. Infallible key
/// constructors use this after boundary validation; no nonempty list aliases empty options.
pub(crate) fn effective_lean_args_digest(args: &[String]) -> Option<String> {
    if args.is_empty() {
        return None;
    }
    let mut h = blake3::Hasher::new();
    h.update(b"lean-args-v1:");
    for (idx, a) in args.iter().enumerate() {
        if idx > 0 {
            h.update(b"\n");
        }
        h.update(a.as_bytes());
    }
    Some(h.finalize().to_hex()[..24].to_string())
}

/// Flatten weak-then-strong Lake args into filtered CLI argv order (matching Lean's setup/CLI
/// precedence where strong args come after weak args and override matching `-D` keys).
pub fn compose_flat_filtered_args(weak_args: &[String], strong_args: &[String]) -> Vec<String> {
    filter_allowed_lean_args(
        weak_args
            .iter()
            .chain(strong_args)
            .map(|a| verification_lake_arg(a)),
    )
}

// Preserve Lake's raw configuration for trace comparison; strengthen only compiler inputs.
pub(super) fn verification_lake_arg(arg: &str) -> &str {
    match arg {
        "-Dwarn.sorry=false" => "-Dwarn.sorry=true",
        "-Dweak.warn.sorry=false" => "-Dweak.warn.sorry=true",
        _ => arg,
    }
}

pub(super) fn verification_lake_option(key: &LeanName, value: &LeanOptionValue) -> LeanOptionValue {
    if matches!(
        key.to_lean_string().as_str(),
        "warn.sorry" | "weak.warn.sorry"
    ) && matches!(value, LeanOptionValue::Bool(false))
    {
        LeanOptionValue::Bool(true)
    } else {
        value.clone()
    }
}

pub(super) fn compose_flat_filtered_args_with_options(
    weak_args: &[String],
    strong_args: &[String],
    lean_options: &LeanOptionsMap,
) -> Vec<String> {
    let opt_flags: Vec<String> = lean_options
        .iter()
        .map(|(k, v)| {
            format!(
                "-D{}={}",
                k.to_lean_string(),
                verification_lake_option(k, v).raw_cli_value()
            )
        })
        .collect();
    filter_allowed_lean_args(
        weak_args
            .iter()
            .chain(strong_args)
            .chain(&opt_flags)
            .map(|a| verification_lake_arg(a)),
    )
}

/// Resolve filtered package-level Lean compiler flags from `pkg`.
pub fn package_default_lean_args(pkg: &PackageConfig) -> Vec<String> {
    let (opts, strong, weak) = compose_effective_args(pkg, &LeanOptionsMap::new(), &[], &[]);
    compose_flat_filtered_args_with_options(&weak, &strong, &opts)
}

/// Resolve filtered effective Lean compiler flags for a specific `.lean` file in `pkg`: the
/// target Lake would build it with (`resolve_module_in_package`, i.e. Lake's `findModule?`),
/// falling back to package-level flags for files no target owns.
pub fn resolve_file_lean_args_in_package(pkg: &PackageConfig, file_path: &Path) -> Vec<String> {
    let canon = |p: &Path| p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
    let canon_root = canon(&pkg.pkg_root);
    let canon_file = canon(&canon_root.join(file_path));
    let pkg_src_base = canon_root.join(&pkg.src_dir);
    let src_roots = pkg
        .libs
        .iter()
        .map(|l| l.src_dir.as_ref())
        .chain(pkg.exes.iter().map(|e| e.src_dir.as_ref()))
        .map(|sd| canon(&sd.map_or_else(|| pkg_src_base.clone(), |sd| pkg_src_base.join(sd))));
    for src_root in src_roots {
        let Ok(rel) = canon_file.strip_prefix(&src_root) else {
            continue;
        };
        let mod_name = format_lean_module_name_from_parts(
            rel.with_extension("")
                .components()
                .filter_map(|c| c.as_os_str().to_str()),
        );
        if let Some(spec) = resolve_module_in_package(pkg, true, &mod_name) {
            if canon(&spec.src_path) == canon_file {
                return compose_flat_filtered_args_with_options(
                    &spec.weak_args,
                    &spec.strong_args,
                    &spec.lean_options,
                );
            }
        }
    }
    package_default_lean_args(pkg)
}

/// Absence of a Lake config is allowed for standalone files; invalid configs are errors.
pub(crate) fn optional_package_config(project_dir: &Path) -> Result<Option<PackageConfig>> {
    if !project_dir.join("lakefile.toml").try_exists()?
        && !project_dir.join("lakefile.lean").try_exists()?
    {
        return Ok(None);
    }
    let pkg = resolve_package_config(project_dir, false).with_context(|| {
        format!(
            "Failed to resolve Lean options in {}",
            project_dir.display()
        )
    })?;
    // #299 round 2: this is the root-as-dependency parse (pr-verify's working-tree resolve,
    // `try_resolve_lean_args_for_path`). The dependency downgrade for Lake-rejected
    // `leanOptions` entry forms must not let a ROOT lakefile parse `Ok` here with entries
    // silently dropped from the args these callers hand out; only the workspace dependency
    // loader keeps the downgrade.
    if let Some(why) = std::iter::once(&pkg.unsupported)
        .chain(pkg.libs.iter().map(|l| &l.unsupported))
        .chain(pkg.exes.iter().map(|e| &e.unsupported))
        .find_map(|u| {
            u.as_deref()
                .filter(|w| w.contains(LAKE_REJECTED_LEAN_OPTIONS_ENTRY))
        })
    {
        anyhow::bail!("{why}");
    }
    Ok(Some(pkg))
}

/// Resolve effective Lake options, propagating configuration errors before cache lookup.
/// A directory without Lake configuration has genuinely empty options.
pub fn try_resolve_lean_args_for_path(
    project_dir: &Path,
    file_path: Option<&Path>,
) -> Result<Vec<String>> {
    let Some(pkg) = optional_package_config(project_dir)? else {
        return Ok(Vec::new());
    };
    Ok(match file_path {
        Some(fp) => resolve_file_lean_args_in_package(&pkg, fp),
        None => package_default_lean_args(&pkg),
    })
}

/// An explicit empty `globs` selects no modules in Lake, but an empty list here means "use the
/// default", so it fails closed.
pub(super) fn nonempty<T>(v: Vec<T>, field: &str) -> Result<Vec<T>> {
    if v.is_empty() {
        anyhow::bail!("Unsupported empty `{}` (selects no modules in Lake)", field);
    }
    Ok(v)
}

/// `roots = []` is fine next to explicit `globs` (Lake builds the globs); without them Lake
/// selects no modules while the defaults here would pick the library name, so it fails closed.
pub(super) fn check_empty_roots(pkg: &PackageConfig, empty_roots: &BTreeSet<usize>) -> Result<()> {
    for &i in empty_roots {
        if pkg.libs.get(i).is_some_and(|lib| lib.globs.is_empty()) {
            anyhow::bail!(
                "Unsupported empty `roots` without `globs` on `{}` (selects no modules in Lake)",
                pkg.libs[i].name
            );
        }
    }
    Ok(())
}

/// A Lake file input may only read inside its own package: an absolute path or a `..` component
/// would let a lakefile hash (and claim as a build input) files outside the checkout.
pub(super) fn checked_input_path(path: &Path) -> Result<PathBuf> {
    anyhow::ensure!(
        path.is_relative()
            && !path
                .components()
                .any(|c| c == std::path::Component::ParentDir),
        "Unsupported Lake input path `{}` (must be relative to the package root, without `..`): fail-closed static Lake config gate",
        path.display()
    );
    Ok(path.to_path_buf())
}

/// Fail closed on anything under an input path that is not a plain file inside the package.
///
/// Two host-side gates, both applied before any sandbox is entered, because both are ways for a
/// declared "input" to name bytes that no longer behave like a tracked file in the checkout:
///
/// - **Escaping symlinks.** `checked_input_path` rejects an escaping *declaration* (`..`, absolute),
///   but a symlink *inside* the tree can point anywhere. Lake would follow it; following it here
///   would hash bytes that no diff of the repository can report as changed, so the pr-verify
///   classifier could call a changed input "unchanged". Resolving to outside `pkg_root` is refused
///   rather than silently trusted. Every path is canonicalized, not just one whose leaf is a
///   symlink: a symlinked *directory* above the leaf escapes just as effectively, and `follow_links`
///   descent hides it, because the entry's own file type is then an ordinary file.
/// - **Non-regular files.** A FIFO, socket, or device node matching the filter cannot be hashed
///   reproducibly, and `fs::read` on a FIFO blocks forever. Lake quietly skips them, which would
///   let an input "contain" a file whose bytes are never in any digest. They are refused instead.
///
/// Both are deliberately stricter than Lake: they can only reject a configuration, never accept one
/// Lake would reject, and neither can trigger for an input made of ordinary files.
pub(super) fn check_input_file_is_contained_regular_file(canon_pkg_root: &Path, path: &Path) -> Result<()> {
    let target = fs::canonicalize(path).with_context(|| {
        format!(
            "Lake input `{}` does not resolve: fail-closed static Lake config gate",
            path.display()
        )
    })?;
    anyhow::ensure!(
        target.starts_with(canon_pkg_root),
        "Lake input `{}` resolves to `{}`, outside the package root `{}`: fail-closed static Lake config gate",
        path.display(),
        target.display(),
        canon_pkg_root.display()
    );
    let meta =
        fs::metadata(&target).with_context(|| format!("Failed to stat {}", target.display()))?;
    anyhow::ensure!(
        meta.file_type().is_file(),
        "Lake input `{}` is not a regular file: fail-closed static Lake config gate",
        path.display()
    );
    Ok(())
}

/// BLAKE3 and Lake file hash of the files an `input_file` / `input_dir` selects, read like Lake's
/// `inputFile` / `inputDir`: a recursive walk of regular files kept by the extension filter,
/// ordered by full path like Lake's `qsort (toString · < toString ·)` -- compared as raw bytes,
/// which agrees with Lake's `String` order on every valid UTF-8 path and, unlike
/// `to_string_lossy`, cannot map two distinct paths onto one sort key.
/// `text := true` normalizes `\r\n` as Lake's `computeTextFileHash` does. The Lake hash of an
/// `input_dir` folds its files left-to-right from `Hash.nil`, matching `Job.collectArray`.
///
/// Unlike Lake, a symlink that leaves the package root and any non-regular file fail closed; see
/// [`check_input_file_is_contained_regular_file`].
///
/// Deliberately **not** memoized by `(path, len, mtime)`. One command resolves the project config
/// several times, so a cache would save real work, but these digests gate `.olean` reuse and a
/// stats-keyed cache is only sound here if it can be bypassed for untrusted input -- which is what
/// `load_project_stat_summary_cached` does, and why `ci-verify` re-reads sources in untrusted mode.
/// Trust is not plumbed through `resolve_package_config`, so there is nothing to bypass on, and a
/// same-length write with a restored mtime -- the poisoning the untrusted `ci-verify` test
/// simulates with `utimensat` -- would be served the cached hash inside one long-lived `serve` or
/// zygote process.
///
/// The repeated-work problem is solved one level up instead, by [`project_lake_inputs_tag`]'s
/// per-command memo: it is keyed on the project directory alone, with no `(len, mtime)` for a
/// restored timestamp to fool, and it is cleared at every command and request boundary. Nothing
/// that gates an `.olean` on a *stat* was reintroduced; this function still re-reads every byte
/// every time it runs.
pub(super) fn hash_input_target(pkg_root: &Path, input: &InputTargetConfig) -> Result<(String, String)> {
    let root = pkg_root.join(checked_input_path(&input.path)?);
    let canon_pkg_root = fs::canonicalize(pkg_root).unwrap_or_else(|_| pkg_root.to_path_buf());
    let mut files = vec![root.clone()];
    if input.is_dir {
        anyhow::ensure!(root.is_dir(), "`{}` is not a directory", root.display());
        files.clear();
        for e in WalkDir::new(&root).follow_links(true) {
            let e = e?;
            let ext = e.path().extension();
            if !input.matches_extension(ext) {
                continue;
            }
            // A directory never carries bytes, so it is neither hashed nor refused; everything
            // else the filter selects must be a plain file inside the package.
            if e.file_type().is_dir() {
                continue;
            }
            check_input_file_is_contained_regular_file(&canon_pkg_root, e.path())?;
            files.push(e.into_path());
        }
        files.sort_by(|a, b| {
            a.as_os_str()
                .as_encoded_bytes()
                .cmp(b.as_os_str().as_encoded_bytes())
        });
    } else {
        check_input_file_is_contained_regular_file(&canon_pkg_root, &root)?;
    }
    let mut file_entries = Vec::with_capacity(files.len());
    for f in &files {
        let bytes = fs::read(f).with_context(|| format!("Failed to read {}", f.display()))?;
        let rel = f
            .strip_prefix(pkg_root)
            .unwrap_or(f)
            .as_os_str()
            .as_encoded_bytes();
        file_entries.push((rel, bytes));
    }
    hash_input_target_entries(
        input,
        file_entries
            .iter()
            .map(|(rel, bytes)| (*rel, bytes.as_slice())),
    )
}

pub(crate) fn hash_input_target_entries<'a, I>(
    input: &InputTargetConfig,
    entries: I,
) -> Result<(String, String)>
where
    I: IntoIterator<Item = (&'a [u8], &'a [u8])>,
{
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-lake-input-v1\n");
    let mut lake = LAKE_NIL_HASH;
    for (rel_path, bytes) in entries {
        let file_hash = if input.text {
            // Lake reads a text input with `IO.FS.readFile`, which rejects non-UTF-8 bytes.
            lake_hash_text(std::str::from_utf8(bytes).with_context(|| {
                format!(
                    "`{}` is not the UTF-8 text Lake expects",
                    String::from_utf8_lossy(rel_path)
                )
            })?)
        } else {
            lake_hash_bytes(bytes)
        };
        lake = if input.is_dir {
            lake_mix_hash(lake, file_hash)
        } else {
            file_hash
        };
        update_hasher_lp(&mut h, rel_path);
        update_hasher_lp(&mut h, bytes);
    }
    Ok((h.finalize().to_hex().to_string(), format!("{lake:016x}")))
}

pub(super) fn finalize_package_config(
    pkg: &mut PackageConfig,
    is_root_pkg: bool,
    config_path: &Path,
    raw_hash: &str,
    explicit_empty_roots: &BTreeSet<usize>,
    hash_inputs_from_disk: bool,
) -> Result<()> {
    // #299: Lake rejects a configuration declaring two targets under one name (a duplicate Lean
    // declaration in `lakefile.lean`), across target kinds too; accepting it would silently
    // build with whichever of the two configurations resolution happens to pick. Duplicate
    // `input_file` / `input_dir` pairs keep their own gate (and its message) below.
    let dup_target = {
        let mut names: Vec<(&str, &str)> = Vec::new();
        names.extend(pkg.libs.iter().map(|l| ("lean_lib", l.name.as_str())));
        names.extend(pkg.exes.iter().map(|e| ("lean_exe", e.name.as_str())));
        names.extend(pkg.custom_targets.iter().map(|c| ("target", c.as_str())));
        names.extend(
            pkg.extern_libs
                .iter()
                .map(|e| ("extern_lib", e.name.as_str())),
        );
        names.extend(pkg.inputs.iter().map(|i| ("input", i.name.as_str())));
        names.iter().enumerate().find_map(|(i, (kind, name))| {
            names[..i]
                .iter()
                .find(|(prev_kind, prev_name)| {
                    prev_name == name && !(*prev_kind == "input" && *kind == "input")
                })
                .map(|(prev_kind, _)| {
                    (
                        (*prev_kind).to_string(),
                        (*kind).to_string(),
                        (*name).to_string(),
                    )
                })
        })
    };
    if let Some((kind_a, kind_b, name)) = dup_target {
        unsupported_lake_field(
            &mut pkg.unsupported,
            is_root_pkg,
            format!(
                "Duplicate Lake target name `{}` (a `{}` and a `{}`) in {}",
                name,
                kind_a,
                kind_b,
                config_path.display()
            ),
        )?;
    }
    for (i, lib) in pkg.libs.iter_mut().enumerate() {
        // Lake's default `roots` is `#[name]`; an explicit `roots = []` stays empty.
        if lib.roots.is_empty() && !lib.name.is_empty() && !explicit_empty_roots.contains(&i) {
            lib.roots.push(lib.name.clone());
        }
        if lib.globs.is_empty() {
            lib.globs = lib.roots.iter().map(|r| GlobSpec::One(r.clone())).collect();
        }
        if lib.is_default_target && !pkg.default_targets.contains(&lib.name) {
            pkg.default_targets.push(lib.name.clone());
        }
    }
    // `needs` may only name the package's declarative file inputs; anything else (other
    // targets, modules, facets, other packages) would need Lake's build graph.
    //
    // The three input gates below hold for dependency packages too, not only the root. Their
    // declarations are hashed into cache keys for every package now, and `resolve_package_config`
    // is called with `is_root_pkg = false` on *root* directories as well (pr-verify's working-tree
    // resolve, `try_resolve_lean_args_for_path`). Gating them on the root would let that resolve
    // silently keep a `needs` that names nothing, or pick the first of two same-named inputs, and
    // hand the result to code that decides whether an input changed.
    let unknown_need = pkg
        .libs
        .iter()
        .find_map(|l| {
            let need = l.needs.iter().find(|n| {
                !pkg.inputs.iter().any(|i| &i.name == *n)
                    && (is_root_pkg || !pkg.custom_targets.contains(n))
            })?;
            Some(("library", l.name.clone(), need.clone()))
        })
        .or_else(|| {
            pkg.exes.iter().find_map(|e| {
                let need = e.needs.iter().find(|n| {
                    !pkg.inputs.iter().any(|i| &i.name == *n)
                        && (is_root_pkg || !pkg.custom_targets.contains(n))
                })?;
                Some(("executable", e.name.clone(), need.clone()))
            })
        });
    if let Some((kind, target_name, need)) = unknown_need {
        if is_root_pkg {
            let _ = c_abi::verify_static_lake_config(true, true, false, false);
        }
        anyhow::bail!(
            "Unsupported `needs` entry `{}` on {} `{}` in {} (not an `input_file` / `input_dir` of the package): fail-closed static Lake config gate",
            need,
            kind,
            target_name,
            config_path.display()
        );
    }
    // `needs` is resolved by name, so two inputs sharing one name would silently pick the first.
    let dup_input = pkg
        .inputs
        .iter()
        .enumerate()
        .find(|(i, inp)| pkg.inputs[..*i].iter().any(|p| p.name == inp.name));
    if let Some((_, dup)) = dup_input {
        if is_root_pkg {
            let _ = c_abi::verify_static_lake_config(true, true, false, false);
        }
        anyhow::bail!(
            "Duplicate Lake input target `{}` in {}: fail-closed static Lake config gate",
            dup.name,
            config_path.display()
        );
    }
    // An input this parser could not read like Lake makes every module of the package
    // unbuildable, not just the libraries that `needs` it: an input's `filter` or an unknown field
    // decides which bytes elaboration sees, and `workspace_lake_inputs_digest` folds the package's
    // inputs into keys that modules of *other* packages use too. The root package already failed
    // closed at parse time; this is the dependency half of the same gate, routed through the slot
    // `build_module_dag` already checks before it publishes a Lake trace for any module.
    if let Some(why) = pkg.inputs.iter().find_map(|i| i.unsupported.clone()) {
        pkg.unsupported.get_or_insert(why);
    }
    let pkg_root = pkg.pkg_root.clone();
    for input in &mut pkg.inputs {
        if !hash_inputs_from_disk {
            checked_input_path(&input.path).map_err(|e| {
                if is_root_pkg {
                    let _ = c_abi::verify_static_lake_config(true, true, false, false);
                }
                anyhow::anyhow!(
                    "Unreadable Lake input `{}` in {}: {:#}: fail-closed static Lake config gate",
                    input.name,
                    config_path.display(),
                    e
                )
            })?;
            continue;
        }
        // Dependency packages fail closed here too. A constant placeholder would make every
        // consumer of this digest -- `module_lake_input_digest`, the manifest guard, the
        // `build` / `ci-verify` action keys -- compare equal across two different sets of input
        // bytes, which is exactly the stale-`.olean` hit this gate exists to prevent. A package
        // whose declared input cannot be read is one Lake could not build either.
        let (blake3, lake_hash) = hash_input_target(&pkg_root, input).map_err(|e| {
            if is_root_pkg {
                let _ = c_abi::verify_static_lake_config(true, true, false, false);
            }
            anyhow::anyhow!(
                "Unreadable Lake input `{}` in {}: {:#}: fail-closed static Lake config gate",
                input.name,
                config_path.display(),
                e
            )
        })?;
        (input.blake3, input.lake_hash) = (blake3, lake_hash);
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
        validate_lean_args(args.iter().map(|a| verification_lake_arg(a))).map_err(|error| {
            anyhow::anyhow!(
                "{} of {} ({}): {error:#}",
                scope,
                pkg.name,
                config_path.display()
            )
        })
    };
    let check_allowed_opts = |opts: &LeanOptionsMap, scope: &str| -> Result<()> {
        for (k, v) in opts {
            let allowed = is_allowed_lean_option(k, &verification_lake_option(k, v));
            if !c_abi::verify_static_lake_config(true, !allowed, false, false) {
                anyhow::bail!(
                    "Unsupported or unsafe Lean option `{}={}` in {} of {} ({}): fail-closed static Lake config gate",
                    k.to_lean_string(),
                    v.raw_cli_value(),
                    scope,
                    pkg.name,
                    config_path.display()
                );
            }
        }
        Ok(())
    };
    let scopes = std::iter::once((
        "package".to_string(),
        &pkg.more_lean_args,
        &pkg.weak_lean_args,
        &pkg.lean_options,
    ))
    .chain(pkg.libs.iter().map(|l| {
        (
            format!("lean_lib[{}]", l.name),
            &l.more_lean_args,
            &l.weak_lean_args,
            &l.lean_options,
        )
    }))
    .chain(pkg.exes.iter().map(|e| {
        (
            format!("lean_exe[{}]", e.name),
            &e.more_lean_args,
            &e.weak_lean_args,
            &e.lean_options,
        )
    }));
    for (scope, more, weak, opts) in scopes {
        check_allowed_args(more, &format!("{scope}.moreLeanArgs"))?;
        check_allowed_args(weak, &format!("{scope}.weakLeanArgs"))?;
        check_allowed_opts(opts, &format!("{scope}.leanOptions"))?;
    }
    pkg.config_digest = compute_package_config_digest(pkg, raw_hash);
    pkg.pre_recipe_config_digest = pkg.config_digest.clone();
    Ok(())
}

/// Resolve a single package's static configuration (`lakefile.toml` or `lakefile.lean`).
pub fn resolve_package_config(pkg_root: &Path, is_root_pkg: bool) -> Result<PackageConfig> {
    resolve_package_config_file(pkg_root, is_root_pkg, None)
}
/// The configuration file Lake loads for a package: `config_file` (a manifest `configFile`,
/// default `lakefile`) as given if it has an extension, else its `.lean` before its `.toml`.
pub(crate) fn package_config_path(
    pkg_root: &Path,
    config_file: Option<&str>,
) -> Result<Option<PathBuf>> {
    let rel = lake_rel_path("configFile", config_file.unwrap_or("lakefile"))?;
    if rel.extension().is_some() {
        return Ok(Some(pkg_root.join(rel)).filter(|p| p.is_file()));
    }
    Ok(["lean", "toml"]
        .iter()
        .map(|ext| pkg_root.join(&rel).with_extension(ext))
        .find(|p| p.is_file()))
}
pub(crate) fn resolve_package_lean_lib_dir(pkg_root: &Path, config_file: Option<&str>) -> PathBuf {
    resolve_package_config_file(pkg_root, false, config_file)
        .map(|cfg| pkg_root.join(cfg.build_dir).join(cfg.lean_lib_dir))
        .unwrap_or_else(|_| pkg_root.join(".lake/build/lib/lean"))
}
pub(super) fn resolve_package_config_file(
    pkg_root: &Path,
    is_root_pkg: bool,
    config_file: Option<&str>,
) -> Result<PackageConfig> {
    let path = package_config_path(pkg_root, config_file)?;
    match path
        .as_ref()
        .and_then(|p| p.extension())
        .and_then(|e| e.to_str())
    {
        Some("lean") => return parse_lakefile_lean(pkg_root, path.as_ref().unwrap(), is_root_pkg),
        Some("toml") => return parse_lakefile_toml(pkg_root, path.as_ref().unwrap(), is_root_pkg),
        _ => {}
    }
    let _ = c_abi::verify_static_lake_config(false, false, false, false);
    anyhow::bail!(
        "No static Lake configuration (`{}.lean` or `.toml`) found in {}: fail-closed static Lake config gate",
        config_file.unwrap_or("lakefile"),
        pkg_root.display()
    )
}
/// Resolve the full workspace `ProjectConfig` (`lean-toolchain`, root lakefile, `lake-manifest.json`,
/// and dependency packages in `.lake/packages/*`).
pub fn resolve_project_config(project_dir: &Path) -> Result<ProjectConfig> {
    resolve_project_config_with_trust(project_dir, false)
}

pub(crate) fn compute_canonical_project_config_digest(
    toolchain: &str,
    lean_githash: &str,
    root_pkg: &PackageConfig,
    manifest_hash_opt: Option<&str>,
    manifest_packages: &[ManifestPackageEntry],
    dep_pkgs: &[PackageConfig],
) -> String {
    let mut ch = blake3::Hasher::new();
    ch.update(b"turbo-lean-project-config-v3\n");
    update_hasher_lp(&mut ch, crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    update_hasher_lp(&mut ch, toolchain.as_bytes());
    update_hasher_lp(&mut ch, lean_githash.as_bytes());
    update_hasher_lp(&mut ch, root_pkg.config_digest.as_bytes());
    match manifest_hash_opt {
        Some(mh) => {
            ch.update(&[1]);
            update_hasher_lp(&mut ch, mh.as_bytes());
        }
        None => {
            ch.update(&[0]);
        }
    }
    ch.update(&(manifest_packages.len() as u64).to_le_bytes());
    for mp in manifest_packages {
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
    for dp in dep_pkgs {
        update_hasher_lp(&mut ch, dp.name.as_bytes());
        update_hasher_lp(&mut ch, dp.base_name.as_bytes());
        update_hasher_lp(&mut ch, dp.config_digest.as_bytes());
    }
    ch.finalize().to_hex().to_string()
}

pub(crate) fn fold_materialized_recipe_config_digests<'a>(
    root_pkg_root: &Path,
    base_canonical_config_digest: &str,
    pkgs: impl Iterator<Item = &'a mut PackageConfig>,
    is_untrusted: bool,
) -> String {
    let mut pkgs: Vec<&mut PackageConfig> = pkgs.collect();
    if pkgs
        .iter()
        .all(|p| required_lake_recipe_names(root_pkg_root, p, is_untrusted).is_empty())
    {
        return base_canonical_config_digest.to_string();
    }
    let mut workspace = blake3::Hasher::new();
    workspace.update(b"turbo-lean-lake-recipes-v1\n");
    for pkg in pkgs.iter_mut() {
        let names = required_lake_recipe_names(root_pkg_root, pkg, is_untrusted);
        if names.is_empty() {
            continue;
        }
        let mut digest = blake3::Hasher::new();
        update_hasher_lp(&mut digest, pkg.pre_recipe_config_digest.as_bytes());
        for name in &names {
            if let Some(inp) = pkg.inputs.iter().find(|i| &i.name == name) {
                update_hasher_lp(&mut digest, name.as_bytes());
                update_hasher_lp(&mut digest, inp.path.as_os_str().as_encoded_bytes());
                update_hasher_lp(&mut digest, inp.blake3.as_bytes());
            }
        }
        pkg.config_digest = digest.finalize().to_hex().to_string();
        update_hasher_lp(&mut workspace, pkg.config_digest.as_bytes());
    }
    let native_digest = workspace.finalize();
    let mut canonical = blake3::Hasher::new();
    update_hasher_lp(&mut canonical, base_canonical_config_digest.as_bytes());
    update_hasher_lp(&mut canonical, native_digest.as_bytes());
    let out_canonical = canonical.finalize().to_hex().to_string();
    for pkg in pkgs.iter_mut() {
        let mut digest = blake3::Hasher::new();
        update_hasher_lp(&mut digest, pkg.config_digest.as_bytes());
        update_hasher_lp(&mut digest, native_digest.as_bytes());
        pkg.config_digest = digest.finalize().to_hex().to_string();
    }
    out_canonical
}

pub(crate) fn assign_manifest_dep_base_name(
    dep_cfg: &mut PackageConfig,
    manifest_name: &str,
    raw_cfg_bytes: &[u8],
) {
    let assigned = clean_lake_ident(manifest_name);
    if !assigned.is_empty() && assigned != dep_cfg.base_name {
        dep_cfg.base_name = assigned;
        let raw_hash = blake3::hash(raw_cfg_bytes).to_hex().to_string();
        dep_cfg.config_digest = compute_package_config_digest(dep_cfg, &raw_hash);
        dep_cfg.pre_recipe_config_digest = dep_cfg.config_digest.clone();
    }
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
    if lean_bin.is_absolute() {
        ToolchainExecutables::from_lean(&lean_bin)?;
    }
    let root_pkg = resolve_package_config(&canon_dir, true)?;
    let (manifest_pkgs_dir, manifest_packages, manifest_hash_opt) =
        parse_lake_manifest(&canon_dir, is_untrusted)?;
    let mut dep_dirs: Vec<(PathBuf, Option<&str>, Option<&str>)> = Vec::new();
    let mut seen_dep_dirs: HashSet<PathBuf> = HashSet::new();
    for mp in &manifest_packages {
        let d = mp.dir.canonicalize().unwrap_or_else(|_| mp.dir.clone());
        if d.is_dir() && seen_dep_dirs.insert(d.clone()) {
            let alias = clean_lake_ident(&mp.name);
            dep_dirs.push((
                d,
                mp.config_file.as_deref(),
                (!alias.is_empty()).then_some(mp.name.as_str()),
            ));
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
                        dep_dirs.push((d, None, None));
                    }
                }
            }
        }
    }
    let mut dep_pkgs = Vec::new();
    // An untrusted workspace must not adopt (and later publish into) a package elsewhere on
    // the host, whether through the manifest or a symlink.
    let package_roots = untrusted_package_roots(&canon_dir);
    for (dep_dir, config_file, manifest_name) in dep_dirs {
        if is_untrusted && !package_roots.iter().any(|r| dep_dir.starts_with(r)) {
            anyhow::bail!(
                "Dependency package `{}` resolves outside the workspace `{}`: fail-closed build path gate",
                dep_dir.display(),
                canon_dir.display()
            );
        }
        if let Some(cfg_path) = package_config_path(&dep_dir, config_file)? {
            let mut dep_cfg = resolve_package_config_file(&dep_dir, false, config_file)?;
            if let Some(mn) = manifest_name {
                let assigned = clean_lake_ident(mn);
                if !assigned.is_empty() && assigned != dep_cfg.base_name {
                    dep_cfg.base_name = assigned;
                    let raw_hash = fs::read(&cfg_path)
                        .map(|b| blake3::hash(&b).to_hex().to_string())
                        .unwrap_or_default();
                    dep_cfg.config_digest = compute_package_config_digest(&dep_cfg, &raw_hash);
                    dep_cfg.pre_recipe_config_digest = dep_cfg.config_digest.clone();
                }
            }
            dep_pkgs.push(dep_cfg);
        }
    }
    if is_untrusted {
        for pkg in std::iter::once(&root_pkg).chain(dep_pkgs.iter()) {
            let pkg_has_precompile = pkg.precompile_modules
                || pkg.libs.iter().any(|l| l.precompile_modules == Some(true));
            let has_unbuilt_recipe = (!pkg.custom_targets.is_empty()
                && (pkg.pkg_root == root_pkg.pkg_root || pkg_has_precompile))
                || pkg
                    .extern_libs
                    .iter()
                    .any(|e| e.static_artifact_blake3.is_none());
            anyhow::ensure!(
                !has_unbuilt_recipe,
                "Untrusted verification rejects dynamic Lake recipes in package `{}`",
                pkg.name
            );
            let pkg_has_precompile = pkg.precompile_modules
                || pkg.libs.iter().any(|l| l.precompile_modules == Some(true));
            if !c_abi::verify_static_lake_config(true, pkg_has_precompile, false, false) {
                anyhow::bail!(
                    "Untrusted verification rejects `precompileModules = true` in package `{}`: native code execution and dlopen plugins are forbidden in untrusted mode: fail-closed static Lake config gate",
                    pkg.name
                );
            }
            for lib in &pkg.libs {
                for f in &lib.default_facets {
                    if matches!(f.as_str(), "shared" | "LeanLib.sharedFacet") {
                        let _ = c_abi::verify_static_lake_config(true, false, false, true);
                        anyhow::bail!(
                            "Untrusted verification rejects native `defaultFacets` entry `{}` on library `{}` in `{}`: fail-closed static Lake config gate",
                            f,
                            lib.name,
                            pkg.name
                        );
                    }
                }
            }
        }
    }
    let canonical_config_digest = compute_canonical_project_config_digest(
        &toolchain,
        &lean_githash,
        &root_pkg,
        manifest_hash_opt.as_deref(),
        &manifest_packages,
        &dep_pkgs,
    );
    let cfg = ProjectConfig {
        toolchain,
        lean_bin,
        lean_githash,
        toolchain_lib_lean,
        toolchain_lib,
        root_pkg,
        manifest_packages,
        dep_pkgs,
        canonical_config_digest,
        is_untrusted,
    };
    materialize_lake_recipes(&cfg, is_untrusted)
}
#[derive(Clone)]
pub(crate) struct DiscoveredModuleSpec {
    pub(crate) module_name: String,
    pub(super) pkg_name: String,
    pub(super) pkg_base_name: String,
    /// The target Lake attributes the module to: the *last* `lean_lib` that can build it.
    pub(crate) target_name: String,
    pub(super) is_root_pkg: bool,
    pub(crate) pkg_root: PathBuf,
    pub(super) src_root: PathBuf,
    pub(crate) src_path: PathBuf,
    pub(crate) build_lib_lean_dir: PathBuf,
    pub(super) build_native_lib_dir: PathBuf,
    pub(crate) build_ir_dir: PathBuf,
    pub(crate) precompile_modules: bool,
    pub(crate) emit_c_default: bool,
    pub(crate) is_exe_target: bool,
    pub(super) platform_independent: Option<bool>,
    pub(super) lean_options: LeanOptionsMap,
    pub(super) strong_args: Vec<String>,
    pub(super) weak_args: Vec<String>,
    pub(super) extern_lib_digests: Vec<String>,
    pub(crate) custom_target_needs: Vec<String>,
    pub(crate) pkg_config_digest: String,
    /// Set when turbo-lean cannot build the module like Lake (`PackageConfig::unsupported`).
    pub(super) unsupported: Option<String>,
    pub(super) native_unsupported: Option<String>,
    pub(super) link_unsupported: Option<String>,
}
pub(super) fn compose_effective_args(
    pkg: &PackageConfig,
    target_options: &LeanOptionsMap,
    target_more_args: &[String],
    target_weak_args: &[String],
) -> (LeanOptionsMap, Vec<String>, Vec<String>) {
    let mut merged_opts = pkg.lean_options.clone();
    for (k, v) in target_options {
        merged_opts.insert(k.clone(), v.clone());
    }
    let mut strong = Vec::with_capacity(pkg.more_lean_args.len() + target_more_args.len());
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
    (merged_opts, strong, weak)
}
pub(super) fn for_each_module_in_dir(
    dir: &Path,
    src_root: &Path,
    out: &mut Vec<(String, PathBuf)>,
) -> Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            for_each_module_in_dir(&path, src_root, out)?;
        } else if path.extension().and_then(|s| s.to_str()) == Some("lean") {
            if let Ok(rel) = path.strip_prefix(src_root) {
                let mod_name = format_lean_module_name_from_parts(
                    rel.with_extension("")
                        .components()
                        .filter_map(|c| c.as_os_str().to_str()),
                );
                if !mod_name.is_empty() {
                    out.push((mod_name, path));
                }
            }
        }
    }
    Ok(())
}
pub(super) fn expand_glob_in_dir(
    src_root: &Path,
    glob: &GlobSpec,
    require_exists: bool,
) -> Result<Vec<(String, PathBuf)>> {
    let mut out = Vec::new();
    match glob {
        GlobSpec::One(mod_name) => {
            let rel_slash = module_name_to_rel_slash(mod_name);
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
            let rel_slash = module_name_to_rel_slash(prefix);
            let sub_dir = src_root.join(&rel_slash);
            if sub_dir.is_dir() {
                for_each_module_in_dir(&sub_dir, src_root, &mut out)?;
            } else if require_exists {
                anyhow::bail!(
                    "Submodules directory for glob `{}.+` not found at `{}`",
                    prefix,
                    sub_dir.display()
                );
            }
        }
        GlobSpec::AndSubmodules(prefix) => {
            let rel_slash = module_name_to_rel_slash(prefix);
            let root_file = src_root.join(format!("{}.lean", rel_slash));
            let sub_dir = src_root.join(&rel_slash);
            if root_file.is_file() {
                out.push((prefix.clone(), root_file));
            }
            if sub_dir.is_dir() {
                for_each_module_in_dir(&sub_dir, src_root, &mut out)?;
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
/// Root-package libraries that declare a non-empty `needs` and can build `mod_name`.
///
/// Used to pick what to hand `lake build`. Lake attributes a module to the **last** `lean_lib` that
/// can build it (`Package.findModule? = leanLibs.findSomeRev?`), and `lake build <Mod>` builds it
/// under that attribution's `extraDep` -- which, for a module that a *different* library `needs` an
/// input for, carries no input trace at all. The input edit then moves nothing Lake compares, and
/// Lake reports the module up to date. Naming the library instead makes Lake build that library's
/// module list with that library's `extraDep`, so the changed input is in the trace it checks.
///
/// Every such library is returned, not just the last one, for the same reason
/// [`module_lake_input_digest`] folds the union: either attribution has to be covered, and building
/// one library too many only costs time.
pub(crate) fn pkg_target_base_name(pkg: &PackageConfig) -> &str {
    if pkg.base_name.is_empty() {
        &pkg.name
    } else {
        &pkg.base_name
    }
}

pub(crate) fn input_bearing_libs_for_module(cfg: &ProjectConfig, mod_name: &str) -> Vec<String> {
    let mut out = Vec::new();
    if !cfg.root_pkg.inputs.is_empty() {
        for lib in &cfg.root_pkg.libs {
            if !lib.needs.is_empty() && lib_can_build_module(lib, mod_name) {
                out.push(lib.name.clone());
            }
        }
    }
    for dp in &cfg.dep_pkgs {
        if dp.inputs.is_empty() {
            continue;
        }
        let dp_base = pkg_target_base_name(dp);
        for lib in &dp.libs {
            if !lib.needs.is_empty() && lib_can_build_module(lib, mod_name) {
                out.push(format!("{}/{}", dp_base, lib.name));
            }
        }
    }
    out
}

/// Every `lean_exe` target (formatted as `@<pkg>/<exe>:exe`) whose root module is `mod_name`.
///
/// Passing `<Mod>` directly to `lake build` only refreshes `<Mod>.olean` and never relinks
/// `.lake/build/bin/<exe>` (`+<Mod>:olean` does not link either, and `@<pkg>/<exe>:olean` is not a
/// valid `lean_exe` facet). Returning `@<pkg>/<exe>:exe` ensures Lake both evaluates `<exe>`'s own
/// `extraDep` (`needs`) trace and relinks the executable binary.
pub(crate) fn exe_targets_for_module(cfg: &ProjectConfig, mod_name: &str) -> Vec<String> {
    let mut out = Vec::new();
    let root_base = pkg_target_base_name(&cfg.root_pkg);
    for exe in &cfg.root_pkg.exes {
        if exe.root == mod_name {
            out.push(format!("@{}/{}:exe", root_base, exe.name));
        }
    }
    for dp in &cfg.dep_pkgs {
        let dp_base = pkg_target_base_name(dp);
        for exe in &dp.exes {
            if exe.root == mod_name {
                out.push(format!("@{}/{}:exe", dp_base, exe.name));
            }
        }
    }
    out
}

/// Every input-bearing `lean_exe` target (`!exe.needs.is_empty()`, formatted as `@<pkg>/<exe>:exe`)
/// whose root module is `mod_name`.
pub(crate) fn input_bearing_exes_for_module(cfg: &ProjectConfig, mod_name: &str) -> Vec<String> {
    let mut out = Vec::new();
    let root_base = pkg_target_base_name(&cfg.root_pkg);
    if !cfg.root_pkg.inputs.is_empty() {
        for exe in &cfg.root_pkg.exes {
            if !exe.needs.is_empty() && exe.root == mod_name {
                out.push(format!("@{}/{}:exe", root_base, exe.name));
            }
        }
    }
    for dp in &cfg.dep_pkgs {
        if dp.inputs.is_empty() {
            continue;
        }
        let dp_base = pkg_target_base_name(dp);
        for exe in &dp.exes {
            if !exe.needs.is_empty() && exe.root == mod_name {
                out.push(format!("@{}/{}:exe", dp_base, exe.name));
            }
        }
    }
    out
}

/// Lake's `LeanLib.isBuildableModule`: one of the library's globs matches the module, or the
/// module lies under a root that one of the globs selects.
pub(crate) fn lib_can_build_module(lib: &LeanLibConfig, mod_name: &str) -> bool {
    let under = |m: &str, p: &str| m.starts_with(&format!("{}.", p));
    let matches = |m: &str| {
        lib.globs.iter().any(|g| match g {
            GlobSpec::One(x) => m == x,
            GlobSpec::Submodules(p) => under(m, p),
            GlobSpec::AndSubmodules(p) => m == p || under(m, p),
        })
    };
    matches(mod_name)
        || lib
            .roots
            .iter()
            .any(|r| (mod_name == r || under(mod_name, r)) && matches(r))
}
pub(crate) fn resolve_module_in_package(
    pkg: &PackageConfig,
    is_root_pkg: bool,
    mod_name: &str,
) -> Option<DiscoveredModuleSpec> {
    resolve_module_in_package_mode(pkg, is_root_pkg, mod_name, true)
}

pub(crate) fn resolve_importable_module_in_package(
    pkg: &PackageConfig,
    is_root_pkg: bool,
    mod_name: &str,
) -> Option<DiscoveredModuleSpec> {
    resolve_module_in_package_mode(pkg, is_root_pkg, mod_name, false)
}

pub(super) fn resolve_module_in_package_mode(
    pkg: &PackageConfig,
    is_root_pkg: bool,
    mod_name: &str,
    include_exe_roots: bool,
) -> Option<DiscoveredModuleSpec> {
    match resolve_module_in_package_ownership(pkg, is_root_pkg, mod_name, include_exe_roots) {
        ModuleOwnership::Found(spec) => Some(spec),
        ModuleOwnership::OwnedMissing { .. } | ModuleOwnership::NotOwned => None,
    }
}

/// Three-way module lookup: Lake's `findModule?` / `findTargetModule?` return the owning target
/// even when its source file is missing (and fail at build time), so a caller that would try
/// the next package on a plain `None` needs to see the difference (#299).
pub(super) enum ModuleOwnership {
    Found(DiscoveredModuleSpec),
    /// A target of this package owns the module name, but its source file is missing.
    OwnedMissing {
        target_name: String,
        src_path: PathBuf,
    },
    NotOwned,
}

pub(super) fn resolve_module_in_package_ownership(
    pkg: &PackageConfig,
    is_root_pkg: bool,
    mod_name: &str,
    include_exe_roots: bool,
) -> ModuleOwnership {
    let rel_slash = module_name_to_rel_slash(mod_name);
    let pkg_src_base = pkg.pkg_root.join(&pkg.src_dir);
    let build_base = pkg.pkg_root.join(&pkg.build_dir);
    let build_lib_lean_dir = build_base.join(&pkg.lean_lib_dir);
    let build_native_lib_dir = build_base.join(&pkg.native_lib_dir);
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
    // 1. An executable whose root is the module (`findTargetModule?`; skipped for `findModule?`).
    if include_exe_roots {
        for exe in pkg.exes.iter().rev() {
            if exe.root == mod_name {
                let exe_src = match &exe.src_dir {
                    Some(sd) => pkg_src_base.join(sd),
                    None => pkg_src_base.clone(),
                };
                let exe_rel = module_name_to_rel_slash(&exe.root);
                let cand = exe_src.join(format!("{}.lean", exe_rel));
                if cand.is_file() {
                    let (lean_options, strong_args, weak_args) = compose_effective_args(
                        pkg,
                        &exe.lean_options,
                        &exe.more_lean_args,
                        &exe.weak_lean_args,
                    );
                    return ModuleOwnership::Found(DiscoveredModuleSpec {
                        module_name: exe.root.clone(),
                        pkg_name: pkg.name.clone(),
                        pkg_base_name: pkg.base_name.clone(),
                        target_name: exe.name.clone(),
                        is_root_pkg,
                        pkg_root: pkg.pkg_root.clone(),
                        src_root: exe_src,
                        src_path: cand,
                        build_lib_lean_dir,
                        build_native_lib_dir,
                        build_ir_dir,
                        precompile_modules: pkg.precompile_modules,
                        emit_c_default: pkg.precompile_modules,
                        is_exe_target: true,
                        platform_independent: exe.platform_independent.or(pkg.platform_independent),
                        lean_options,
                        strong_args,
                        weak_args,
                        extern_lib_digests: extern_digests,
                        custom_target_needs: exe.custom_target_needs.clone(),
                        pkg_config_digest: pkg.config_digest.clone(),
                        unsupported: pkg.unsupported.clone().or_else(|| exe.unsupported.clone()),
                        native_unsupported: pkg
                            .native_unsupported
                            .clone()
                            .or_else(|| exe.native_unsupported.clone()),
                        link_unsupported: pkg
                            .link_unsupported
                            .clone()
                            .or_else(|| exe.link_unsupported.clone()),
                    });
                }
                // #299: Lake's `findTargetModule?` still returns this executable's module when
                // its source file is missing and fails at build time; trying an earlier
                // candidate instead would resolve a module Lake would never build.
                return ModuleOwnership::OwnedMissing {
                    target_name: exe.name.clone(),
                    src_path: cand,
                };
            }
        }
    }
    // 2. Like Lake's `findTargetModule?`: the last library that can build the module, i.e.
    //    one of its globs matches it or it lies under one of its roots.
    for lib in pkg.libs.iter().rev() {
        let lib_src = match &lib.src_dir {
            Some(sd) => pkg_src_base.join(sd),
            None => pkg_src_base.clone(),
        };
        // Lake's `isBuildableModule`: a glob matches the module, or the module lies under a
        // root that one of the globs selects.
        if lib_can_build_module(lib, mod_name) {
            let cand = lib_src.join(format!("{}.lean", rel_slash));
            if cand.is_file() {
                let (lean_options, strong_args, weak_args) = compose_effective_args(
                    pkg,
                    &lib.lean_options,
                    &lib.more_lean_args,
                    &lib.weak_lean_args,
                );
                let precompile = pkg.precompile_modules || lib.precompile_modules.unwrap_or(false);
                let emit_c_default = precompile
                    || lib.default_facets.iter().any(|f| {
                        matches!(
                            f.as_str(),
                            "c" | "static"
                                | "LeanLib.staticFacet"
                                | "shared"
                                | "LeanLib.sharedFacet"
                        )
                    });
                return ModuleOwnership::Found(DiscoveredModuleSpec {
                    module_name: mod_name.to_string(),
                    pkg_name: pkg.name.clone(),
                    pkg_base_name: pkg.base_name.clone(),
                    target_name: lib.name.clone(),
                    is_root_pkg,
                    pkg_root: pkg.pkg_root.clone(),
                    src_root: lib_src,
                    src_path: cand,
                    build_lib_lean_dir,
                    build_native_lib_dir,
                    build_ir_dir,
                    precompile_modules: precompile,
                    emit_c_default,
                    is_exe_target: false,
                    platform_independent: lib.platform_independent.or(pkg.platform_independent),
                    lean_options,
                    strong_args,
                    weak_args,
                    extern_lib_digests: extern_digests,
                    custom_target_needs: lib.custom_target_needs.clone(),
                    pkg_config_digest: pkg.config_digest.clone(),
                    unsupported: pkg.unsupported.clone().or_else(|| lib.unsupported.clone()),
                    native_unsupported: pkg
                        .native_unsupported
                        .clone()
                        .or_else(|| lib.native_unsupported.clone()),
                    link_unsupported: pkg
                        .link_unsupported
                        .clone()
                        .or_else(|| lib.link_unsupported.clone()),
                });
            }
            // #299: Lake's `findModule?` keeps this library as the module's owner even when the
            // source file is missing and fails at build time; trying an earlier library instead
            // would build a module Lake would never build.
            return ModuleOwnership::OwnedMissing {
                target_name: lib.name.clone(),
                src_path: cand,
            };
        }
    }
    // 3. A package without targets: its source directory (Lake has no target to ask).
    let cand = pkg_src_base.join(format!("{}.lean", rel_slash));
    if pkg.libs.is_empty() && pkg.exes.is_empty() && cand.is_file() {
        let (lean_options, strong_args, weak_args) =
            compose_effective_args(pkg, &LeanOptionsMap::new(), &[], &[]);
        return ModuleOwnership::Found(DiscoveredModuleSpec {
            module_name: mod_name.to_string(),
            pkg_name: pkg.name.clone(),
            pkg_base_name: pkg.base_name.clone(),
            target_name: pkg.name.clone(),
            is_root_pkg,
            pkg_root: pkg.pkg_root.clone(),
            src_root: pkg_src_base,
            src_path: cand,
            build_lib_lean_dir,
            build_native_lib_dir,
            build_ir_dir,
            precompile_modules: pkg.precompile_modules,
            emit_c_default: pkg.precompile_modules,
            is_exe_target: false,
            platform_independent: pkg.platform_independent,
            lean_options,
            strong_args,
            weak_args,
            extern_lib_digests: extern_digests,
            custom_target_needs: Vec::new(),
            pkg_config_digest: pkg.config_digest.clone(),
            unsupported: pkg.unsupported.clone(),
            native_unsupported: pkg.native_unsupported.clone(),
            link_unsupported: pkg.link_unsupported.clone(),
        });
    }
    ModuleOwnership::NotOwned
}
pub(crate) fn lean_githash_for_bin(lean_bin: &Path) -> Option<String> {
    let canon_bin = lean_bin.canonicalize().ok()?;
    let cache = LEAN_INFO_CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    if let Ok(guard) = cache.lock() {
        if let Some((gh, _, _)) = guard.get(&canon_bin) {
            return Some(gh.clone());
        }
    }
    let out = Command::new(&canon_bin)
        .env("PATH", "/usr/bin:/bin")
        .arg("--githash")
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let gh = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if gh.is_empty() {
        return None;
    }
    let prefix_root = canon_bin
        .parent()
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .filter(|p| p.join("lib/lean").is_dir());
    if let Some(root) = prefix_root {
        if let Ok(mut guard) = cache.lock() {
            guard.insert(
                canon_bin,
                (gh.clone(), root.join("lib/lean"), root.join("lib")),
            );
        }
    }
    Some(gh)
}

pub(crate) fn discover_host_installed_lean_githashes() -> HashSet<String> {
    let mut githashes = HashSet::new();
    let mut elan_roots: Vec<PathBuf> = Vec::new();
    if let Ok(extra_roots) = std::env::var("TURBO_LEAN_ELAN_ROOTS") {
        for r in std::env::split_paths(&extra_roots) {
            if r.is_dir() && !elan_roots.contains(&r) {
                elan_roots.push(r);
            }
        }
    }
    if let Ok(eh) = std::env::var("ELAN_HOME") {
        let p = PathBuf::from(eh);
        if p.is_dir() && !elan_roots.contains(&p) {
            elan_roots.push(p);
        }
    }
    if let Ok(home) = std::env::var("HOME") {
        let home_path = PathBuf::from(&home);
        let p = home_path.join(".elan");
        if p.is_dir() && !elan_roots.contains(&p) {
            elan_roots.push(p);
        }
        let mut anc = home_path.parent();
        for _ in 0..3 {
            if let Some(a) = anc {
                for cand in [a.join(".elan"), a.join("caches/elan")] {
                    if cand.is_dir() && !elan_roots.contains(&cand) {
                        elan_roots.push(cand);
                    }
                }
                anc = a.parent();
            }
        }
    }
    for sys_elan in FLEET_SYSTEM_ELAN_ROOTS {
        let p = PathBuf::from(sys_elan);
        if p.is_dir() && !elan_roots.contains(&p) {
            elan_roots.push(p);
        }
    }
    if let Ok(path_var) = std::env::var("PATH") {
        for dir in std::env::split_paths(&path_var) {
            for bin_name in ["lean", "lean.exe"] {
                let cand = dir.join(bin_name);
                if cand.is_file() {
                    if let Some(gh) = lean_githash_for_bin(&cand) {
                        githashes.insert(gh);
                    }
                }
            }
            if let Some(parent) = dir.parent() {
                if parent.join("toolchains").is_dir() && !elan_roots.contains(&parent.to_path_buf())
                {
                    elan_roots.push(parent.to_path_buf());
                } else if let Some(gp) = parent.parent().and_then(|p| p.parent()) {
                    if gp.join("toolchains").is_dir() && !elan_roots.contains(&gp.to_path_buf()) {
                        elan_roots.push(gp.to_path_buf());
                    }
                }
            }
        }
    }
    for root in elan_roots {
        let tc_dir = root.join("toolchains");
        let Ok(entries) = fs::read_dir(&tc_dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let p = entry.path();
            for bin_rel in ["bin/lean", "bin/lean.exe"] {
                let cand = p.join(bin_rel);
                if cand.is_file() {
                    if let Some(gh) = lean_githash_for_bin(&cand) {
                        githashes.insert(gh);
                    }
                }
            }
        }
    }
    githashes
}

pub(crate) fn lean_githash_for_sysroot_lib_lean(dir: &Path) -> Option<String> {
    let check_root = |p: &Path| -> Option<PathBuf> {
        if !p.ends_with("lib/lean") {
            return None;
        }
        let tc = p.parent()?.parent()?;
        [tc.join("bin/lean"), tc.join("bin/lean.exe")]
            .into_iter()
            .find(|cand| cand.is_file())
    };
    let lean_bin =
        check_root(dir).or_else(|| fs::canonicalize(dir).ok().and_then(|c| check_root(&c)))?;
    lean_githash_for_bin(&lean_bin)
}

pub(crate) fn is_verified_toolchain_olean_file(
    toolchain_lib_lean: &Path,
    lean_githash: Option<&str>,
    olean_path: &Path,
) -> bool {
    if toolchain_lib_lean.as_os_str().is_empty() {
        return false;
    }
    let Some(expected_gh) = lean_githash
        .map(str::trim)
        .filter(|s| !s.is_empty() && *s != "lean-not-installed")
    else {
        return false;
    };
    let Ok(canon_tc) = toolchain_lib_lean.canonicalize() else {
        return false;
    };
    let rel_from_tc = if let Ok(rel) = olean_path.strip_prefix(toolchain_lib_lean) {
        rel.to_path_buf()
    } else if let Ok(rel) = olean_path.strip_prefix(&canon_tc) {
        rel.to_path_buf()
    } else {
        return false;
    };
    if rel_from_tc.as_os_str().is_empty() {
        return false;
    }
    let mut cur = canon_tc.clone();
    let comps: Vec<_> = rel_from_tc.components().collect();
    for (idx, comp) in comps.iter().enumerate() {
        let std::path::Component::Normal(seg) = comp else {
            return false;
        };
        cur.push(seg);
        let Ok(meta) = fs::symlink_metadata(&cur) else {
            return false;
        };
        if meta.file_type().is_symlink() {
            return false;
        }
        if idx + 1 == comps.len() {
            if !meta.is_file() {
                return false;
            }
        } else if !meta.is_dir() {
            return false;
        }
    }
    let Some((_, hdr_gh)) = read_olean_header_version_and_githash(&cur) else {
        return false;
    };
    hdr_gh.eq_ignore_ascii_case(expected_gh)
}

pub(crate) fn is_builtin_toolchain_prefix_name(mod_name: &str) -> bool {
    mod_name == "Init"
        || mod_name.starts_with("Init.")
        || mod_name == "Std"
        || mod_name.starts_with("Std.")
        || mod_name == "Lean"
        || mod_name.starts_with("Lean.")
        || mod_name == "Lake"
        || mod_name.starts_with("Lake.")
}

pub(crate) fn is_builtin_toolchain_module(
    toolchain_lib_lean: &Path,
    lean_githash: Option<&str>,
    mod_name: &str,
) -> bool {
    if toolchain_lib_lean.as_os_str().is_empty() {
        let is_zero_compiler = lean_githash
            .map(str::trim)
            .is_none_or(|s| s.is_empty() || s == "lean-not-installed");
        return is_zero_compiler && is_builtin_toolchain_prefix_name(mod_name);
    }
    let rel_slash = module_name_to_rel_slash(mod_name);
    let cand = toolchain_lib_lean.join(format!("{}.olean", rel_slash));
    is_verified_toolchain_olean_file(toolchain_lib_lean, lean_githash, &cand)
}

pub(crate) fn is_unshadowed_toolchain_olean_import(
    cfg: &ProjectConfig,
    search_dirs: &[PathBuf],
    mod_name: &str,
    is_untrusted: bool,
) -> bool {
    if resolve_module_in_package(&cfg.root_pkg, true, mod_name).is_some()
        || cfg
            .dep_pkgs
            .iter()
            .any(|dp| resolve_module_in_package(dp, false, mod_name).is_some())
    {
        return false;
    }
    let mut all_dirs: Vec<PathBuf> = search_dirs.to_vec();
    if !cfg.toolchain_lib_lean.as_os_str().is_empty() && !all_dirs.contains(&cfg.toolchain_lib_lean)
    {
        all_dirs.push(cfg.toolchain_lib_lean.clone());
    }
    let Some(first_hit) = resolve_olean_along_search_dirs(&all_dirs, mod_name) else {
        return !is_untrusted
            && cfg.toolchain_lib_lean.as_os_str().is_empty()
            && is_builtin_toolchain_module(
                &cfg.toolchain_lib_lean,
                Some(&cfg.lean_githash),
                mod_name,
            );
    };
    is_verified_toolchain_olean_file(&cfg.toolchain_lib_lean, Some(&cfg.lean_githash), &first_hit)
}
pub fn lean_string_mangle(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 4);
    for ch in s.chars() {
        let code = ch as u32;
        if ch.is_ascii_alphanumeric() {
            out.push(ch);
        } else if ch == '_' {
            out.push_str("__");
        } else if code < 0x100 {
            out.push_str(&format!("_x{:02x}", code));
        } else if code < 0x10000 {
            out.push_str(&format!("_u{:04x}", code));
        } else {
            out.push_str(&format!("_U{:08x}", code));
        }
    }
    out
}

pub(super) fn check_lower_hex_prefix(s: &str, n: usize) -> bool {
    let bytes = s.as_bytes();
    bytes.len() >= n
        && bytes[..n]
            .iter()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b))
}

pub(super) fn lean_check_disambiguation(mangled: &str) -> bool {
    let rest = mangled.trim_start_matches('_');
    match rest.as_bytes().first().copied() {
        None => true,
        Some(b'x') => check_lower_hex_prefix(&rest[1..], 2),
        Some(b'u') => check_lower_hex_prefix(&rest[1..], 4),
        Some(b'U') => check_lower_hex_prefix(&rest[1..], 8),
        Some(b) => b.is_ascii_digit(),
    }
}

pub fn lean_name_mangle(name: &LeanName, pre: &str) -> String {
    let mut out = String::from(pre);
    let mut prev_part: Option<&LeanNamePart> = None;
    for part in &name.0 {
        match part {
            LeanNamePart::Str(s) => {
                let m = lean_string_mangle(s);
                match prev_part {
                    None => {
                        if lean_check_disambiguation(&m) {
                            out.push_str("00");
                        }
                        out.push_str(&m);
                    }
                    Some(prev) => {
                        let prev_ends_underscore =
                            matches!(prev, LeanNamePart::Str(ps) if ps.ends_with('_'));
                        if prev_ends_underscore || lean_check_disambiguation(&m) {
                            out.push_str("_00");
                        } else {
                            out.push('_');
                        }
                        out.push_str(&m);
                    }
                }
            }
            LeanNamePart::Num(n) => {
                if prev_part.is_some() {
                    out.push('_');
                }
                out.push_str(&n.to_string());
                out.push('_');
            }
        }
        prev_part = Some(part);
    }
    out
}

pub fn lean_mk_module_initialization_stem(mod_or_lib_name: &str, pkg_name: Option<&str>) -> String {
    let parsed = LeanName::from_str_to_name(mod_or_lib_name).unwrap_or_else(|_| {
        LeanName(
            mod_or_lib_name
                .split('.')
                .filter(|p| !p.is_empty())
                .map(|p| LeanNamePart::Str(clean_lake_ident(p)))
                .collect(),
        )
    });
    let pre = match pkg_name {
        Some(pkg) if !pkg.is_empty() => format!("{}_", lean_string_mangle(pkg)),
        _ => String::new(),
    };
    lean_name_mangle(&parsed, &pre)
}

pub(crate) fn expand_lib_configured_modules(
    pkg: &PackageConfig,
    lib: &LeanLibConfig,
) -> Result<Vec<(String, PathBuf)>> {
    let pkg_src_base = pkg.pkg_root.join(&pkg.src_dir);
    let lib_src = match &lib.src_dir {
        Some(sd) => pkg_src_base.join(sd),
        None => pkg_src_base,
    };
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    let globs_cow: Vec<GlobSpec> = if lib.globs.is_empty() {
        lib.roots.iter().cloned().map(GlobSpec::One).collect()
    } else {
        lib.globs.clone()
    };
    for g in &globs_cow {
        for (m_name, m_path) in expand_glob_in_dir(&lib_src, g, true)? {
            if seen.insert(m_name.clone()) {
                out.push((m_name, m_path));
            }
        }
    }
    Ok(out)
}

#[derive(Clone, Debug, Default)]
pub(crate) struct TrustedAssuranceSurface {
    pub mod_names: HashSet<String>,
    pub canon_paths: HashSet<PathBuf>,
    pub lib_names: HashSet<String>,
    pub exe_names: HashSet<String>,
}

pub(crate) fn discover_trusted_assurance_surface(
    project: &Path,
    pkg: &PackageConfig,
    allowed_axioms: &[String],
) -> TrustedAssuranceSurface {
    let canon = |p: &Path| p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
    let canon_proj = canon(project);
    let mut dep_roots: Vec<PathBuf> = parse_lake_manifest(project, false)
        .map(|(_, pkgs, _)| {
            pkgs.into_iter()
                .filter_map(|mp| {
                    let c = canon(&mp.dir);
                    (c != canon_proj && mp.dir != project).then_some(c)
                })
                .collect()
        })
        .unwrap_or_default();
    dep_roots.sort();
    dep_roots.dedup();
    let pkg_base = project.join(&pkg.src_dir);
    let mut roots = vec![canon(&pkg_base)];
    for dir in pkg
        .libs
        .iter()
        .filter_map(|l| l.src_dir.as_ref())
        .chain(pkg.exes.iter().filter_map(|e| e.src_dir.as_ref()))
    {
        roots.push(canon(&pkg_base.join(dir)));
    }
    if !roots.contains(&canon_proj) {
        roots.push(canon_proj.clone());
    }
    roots.sort_by_key(|r| std::cmp::Reverse(r.components().count()));
    roots.dedup();

    struct ModInfo {
        canon_path: PathBuf,
        imports: Vec<String>,
        is_dot_fixture: bool,
        is_zero_shard_meta_audit: bool,
    }
    let mut all_mods: HashMap<String, ModInfo> = HashMap::new();
    let mut lib_mods: Vec<(String, Vec<String>)> = Vec::new();
    let mut exe_mods: Vec<(String, String)> = Vec::new();

    let mut register_mod = |m_name: String, src: PathBuf| {
        if m_name.is_empty() || all_mods.contains_key(&m_name) {
            return;
        }
        let canon_src = canon(&src);
        if dep_roots.iter().any(|dr| canon_src.starts_with(dr)) {
            return;
        }
        let is_dot_fixture = canon_src.strip_prefix(&canon_proj).ok().is_some_and(|rel| {
            rel.components().any(|c| {
                c.as_os_str()
                    .to_str()
                    .is_some_and(|s| s.starts_with('.') && s != "." && s != "..")
            })
        });
        let Ok(raw) = fs::read_to_string(&src) else {
            return;
        };
        let hdr = parse_header_info(&raw);
        if hdr.header_error.is_some() {
            return;
        }
        let split = splitter::split_lean_source(&raw, &[]);
        let is_zero_shard_meta_audit = split.shards.is_empty()
            && split.hygiene.has_checking_weakening
            && !split.hygiene.has_checking_weakening_option
            && !split.hygiene.has_sorry
            && !split.hygiene.has_axiom
            && !split.hygiene.has_trust_compiler
            && !split.hygiene.native_violation_under(allowed_axioms);
        all_mods.insert(
            m_name,
            ModInfo {
                canon_path: canon_src,
                imports: hdr.imports,
                is_dot_fixture,
                is_zero_shard_meta_audit,
            },
        );
    };

    for lib in &pkg.libs {
        if let Ok(pairs) = expand_lib_configured_modules(pkg, lib) {
            let mut names = Vec::with_capacity(pairs.len());
            for (m_name, m_path) in pairs {
                names.push(m_name.clone());
                register_mod(m_name, m_path);
            }
            lib_mods.push((lib.name.clone(), names));
        }
    }
    for exe in &pkg.exes {
        if !exe.root.is_empty() {
            if let Some(spec) = resolve_module_in_package(pkg, true, &exe.root) {
                exe_mods.push((exe.name.clone(), exe.root.clone()));
                register_mod(exe.root.clone(), spec.src_path);
            }
        }
    }
    for source in crate::lake_build::collect_project_lean_files(project, false, None) {
        let canon_src = canon(&source);
        if dep_roots.iter().any(|dr| canon_src.starts_with(dr)) {
            continue;
        }
        let Some(root) = roots.iter().find(|r| canon_src.starts_with(r)) else {
            continue;
        };
        let Ok(rel) = canon_src.strip_prefix(root) else {
            continue;
        };
        let m_name = format_lean_module_name_from_parts(
            rel.with_extension("")
                .components()
                .filter_map(|c| c.as_os_str().to_str()),
        );
        register_mod(m_name, source);
    }

    let mut cand: HashSet<String> = all_mods
        .iter()
        .filter(|(_, info)| info.is_dot_fixture || info.is_zero_shard_meta_audit)
        .map(|(m, _)| m.clone())
        .collect();

    // Closed sink-cone pruning: remove any candidate imported by a module outside `cand`.
    let mut changed = !cand.is_empty();
    while changed {
        changed = false;
        let mut to_remove = Vec::new();
        for (importer, info) in &all_mods {
            if cand.contains(importer) {
                continue;
            }
            for imp in &info.imports {
                if cand.contains(imp) {
                    to_remove.push(imp.clone());
                }
            }
        }
        for bad in to_remove {
            if cand.remove(&bad) {
                changed = true;
            }
        }
    }
    if cand.is_empty() {
        return TrustedAssuranceSurface::default();
    }

    let canon_paths: HashSet<PathBuf> = cand
        .iter()
        .filter_map(|m| all_mods.get(m).map(|i| i.canon_path.clone()))
        .collect();
    let lib_names: HashSet<String> = lib_mods
        .into_iter()
        .filter(|(_, names)| !names.is_empty() && names.iter().any(|m| cand.contains(m)))
        .map(|(l, _)| l)
        .collect();
    let exe_names: HashSet<String> = exe_mods
        .into_iter()
        .filter(|(_, root)| cand.contains(root))
        .map(|(e, _)| e)
        .collect();
    TrustedAssuranceSurface {
        mod_names: cand,
        canon_paths,
        lib_names,
        exe_names,
    }
}

/// Build the deterministic module dependency DAG for `cfg` and requested `targets` (trusted mode).
pub fn build_module_dag(cfg: &ProjectConfig, targets: &[String]) -> Result<ModuleDag> {
    build_module_dag_with_trust(cfg, targets, false)
}

/// Build the deterministic module dependency DAG for `cfg` and requested `targets` with explicit `is_untrusted` policy.
/// When `is_untrusted` is true, pre-existing `.olean` artifacts in dependency packages or `LEAN_PATH`
/// are never trusted from the checkout; all dependency package modules become DAG nodes verified/restored
/// via the host `TurboStore` CAS or compiled inside the sandbox.
pub(crate) fn global_emit_c_enabled() -> bool {
    ["TURBO_LEAN_EMIT_C", "TURBO_LEAN_LAKE_COMPAT"]
        .into_iter()
        .any(|k| {
            std::env::var(k)
                .map(|v| v.trim() == "1" || v.eq_ignore_ascii_case("true"))
                .unwrap_or(false)
        })
}

pub(crate) fn resolve_lean_file_to_workspace_target(
    cfg: &ProjectConfig,
    file_path: &Path,
) -> Option<(String, DiscoveredModuleSpec)> {
    let mut candidate_files: Vec<PathBuf> = Vec::new();
    if file_path.is_absolute() {
        candidate_files.push(file_path.to_path_buf());
    } else {
        candidate_files.push(cfg.root_pkg.pkg_root.join(file_path));
        if let Ok(cwd) = std::env::current_dir() {
            let cwd_cand = cwd.join(file_path);
            if !candidate_files.contains(&cwd_cand) {
                candidate_files.push(cwd_cand);
            }
        }
    }
    let resolved_file = candidate_files
        .into_iter()
        .find(|p| p.is_file())
        .and_then(|p| p.canonicalize().ok())?;
    if resolved_file.extension().and_then(|s| s.to_str()) != Some("lean") {
        return None;
    }

    for (is_root, pkg) in
        std::iter::once((true, &cfg.root_pkg)).chain(cfg.dep_pkgs.iter().map(|dp| (false, dp)))
    {
        let pkg_src_base = pkg.pkg_root.join(&pkg.src_dir);
        let mut src_roots: Vec<PathBuf> = Vec::new();
        for lib in pkg.libs.iter().rev() {
            let lr = match &lib.src_dir {
                Some(sd) => pkg_src_base.join(sd),
                None => pkg_src_base.clone(),
            };
            if let Ok(c) = lr.canonicalize() {
                if !src_roots.contains(&c) {
                    src_roots.push(c);
                }
            }
        }
        for exe in pkg.exes.iter().rev() {
            let er = match &exe.src_dir {
                Some(sd) => pkg_src_base.join(sd),
                None => pkg_src_base.clone(),
            };
            if let Ok(c) = er.canonicalize() {
                if !src_roots.contains(&c) {
                    src_roots.push(c);
                }
            }
        }
        if let Ok(c) = pkg_src_base.canonicalize() {
            if !src_roots.contains(&c) {
                src_roots.push(c);
            }
        }
        for sr in src_roots {
            if let Ok(rel) = resolved_file.strip_prefix(&sr) {
                let mod_name = rel
                    .with_extension("")
                    .components()
                    .filter_map(|c| c.as_os_str().to_str())
                    .collect::<Vec<_>>()
                    .join(".");
                if mod_name.is_empty() {
                    continue;
                }
                if let Some(spec) = resolve_module_in_package(pkg, is_root, &mod_name) {
                    let spec_canon = spec
                        .src_path
                        .canonicalize()
                        .unwrap_or_else(|_| spec.src_path.clone());
                    if spec_canon == resolved_file {
                        let target_str = if is_root {
                            format!("+{mod_name}")
                        } else {
                            let pkg_base = if pkg.base_name.is_empty() {
                                &pkg.name
                            } else {
                                &pkg.base_name
                            };
                            format!("{pkg_base}/+{mod_name}")
                        };
                        return Some((target_str, spec));
                    }
                }
            }
        }
    }
    None
}

pub(crate) fn normalize_build_target_spec(cfg: &ProjectConfig, raw_target: &str) -> String {
    let trimmed = raw_target.trim();
    if trimmed.is_empty() || trimmed.starts_with('@') || trimmed.starts_with('+') {
        return trimmed.to_string();
    }
    let (base, facet_opt) = match trimmed.rsplit_once(':') {
        Some((b, f)) if b.ends_with(".lean") => (b.trim(), Some(f.trim())),
        _ => (trimmed, None),
    };
    if !base.ends_with(".lean") {
        return trimmed.to_string();
    }
    if let Some((mod_target, _)) = resolve_lean_file_to_workspace_target(cfg, Path::new(base)) {
        match facet_opt {
            Some(f) if !f.is_empty() => format!("{mod_target}:{f}"),
            _ => mod_target,
        }
    } else {
        trimmed.to_string()
    }
}

pub(crate) fn normalize_build_targets(cfg: &ProjectConfig, targets: &[String]) -> Vec<String> {
    targets
        .iter()
        .map(|t| normalize_build_target_spec(cfg, t))
        .collect()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedExeLinkTarget {
    pub pkg_root: PathBuf,
    pub lake_spec: String,
    pub binary_path: PathBuf,
}

/// Resolve all `lean_exe` binary targets selected by `targets` (or by root package `defaultTargets`
/// when `targets.is_empty()`), returning `(exe_targets, module_prep_targets)` where any `:exe` facet
/// on a matched `lean_exe` is normalized to `:default` for `build_project_modules_native`.
pub(crate) fn resolve_requested_exe_link_targets(
    cfg: &ProjectConfig,
    targets: &[String],
) -> (Vec<ResolvedExeLinkTarget>, Vec<String>) {
    let normalized = normalize_build_targets(cfg, targets);
    let root_pkg = &cfg.root_pkg;
    let ws_pkgs = || std::iter::once(root_pkg).chain(cfg.dep_pkgs.iter());
    let mut exe_targets: Vec<ResolvedExeLinkTarget> = Vec::new();
    let mut seen_specs: BTreeSet<String> = BTreeSet::new();
    let mut push_exe = |pkg: &PackageConfig, exe: &LeanExeConfig| {
        let lake_spec = format!("@{}/{}:exe", pkg.base_name, exe.name);
        if seen_specs.insert(lake_spec.clone()) {
            exe_targets.push(ResolvedExeLinkTarget {
                pkg_root: pkg.pkg_root.clone(),
                lake_spec,
                binary_path: pkg.exe_binary_path(exe),
            });
        }
    };
    let push_default_pkg_exes =
        |pkg: &PackageConfig, push: &mut dyn FnMut(&PackageConfig, &LeanExeConfig)| {
            if !pkg.default_targets.is_empty() {
                for dt in &pkg.default_targets {
                    let clean_dt = clean_lake_ident(dt);
                    if let Some(exe) = pkg.exes.iter().find(|e| e.name == clean_dt) {
                        push(pkg, exe);
                    }
                }
            } else {
                for exe in &pkg.exes {
                    push(pkg, exe);
                }
            }
        };
    if normalized.is_empty() {
        push_default_pkg_exes(root_pkg, &mut push_exe);
        return (exe_targets, Vec::new());
    }
    let mut module_prep_targets = Vec::with_capacity(normalized.len());
    for raw_target in &normalized {
        let raw_trimmed = raw_target.trim();
        let explicit_pkg = raw_trimmed.starts_with('@');
        let explicit_workspace_module = !explicit_pkg && raw_trimmed.starts_with('+');
        let t = raw_trimmed.strip_prefix('@').unwrap_or(raw_trimmed);
        if t.matches(':').count() > 1 {
            module_prep_targets.push(raw_target.clone());
            continue;
        }
        let (target_base, facet_opt) = match t.split_once(':') {
            Some((b, f)) => (b.trim(), Some(f.trim())),
            None => (t.trim(), None),
        };
        if facet_opt.is_some_and(|f| !matches!(f, "default" | "exe")) {
            module_prep_targets.push(raw_target.clone());
            continue;
        }
        let slash_parts: Vec<&str> = target_base.split('/').collect();
        let (pkg_filter, item_raw, explicit_pkg_item_mod) = match slash_parts.as_slice() {
            [only] => (None, *only, false),
            [pkg, item] => (
                Some((*pkg).trim()),
                (*item).trim(),
                (*item).trim().starts_with('+'),
            ),
            _ => {
                module_prep_targets.push(raw_target.clone());
                continue;
            }
        };
        if explicit_workspace_module || explicit_pkg_item_mod {
            module_prep_targets.push(raw_target.clone());
            continue;
        }
        let item_body = item_raw.strip_prefix('+').unwrap_or(item_raw);
        let item_name = clean_lake_ident(item_body);
        let mut matched_exe_with_exe_facet = false;
        if let Some(pf) = pkg_filter {
            let base = clean_lake_ident(pf.strip_prefix('@').unwrap_or(pf));
            let pkg_opt = if base.is_empty() {
                Some(root_pkg)
            } else {
                ws_pkgs().find(|p| p.base_name == base)
            };
            if let Some(pkg) = pkg_opt {
                if item_raw.is_empty() && facet_opt.is_none() {
                    push_default_pkg_exes(pkg, &mut push_exe);
                } else if !item_raw.is_empty() {
                    let lib_shadows = pkg.libs.iter().any(|l| l.name == item_name);
                    if !lib_shadows {
                        if let Some(exe) = pkg.exes.iter().find(|e| e.name == item_name) {
                            push_exe(pkg, exe);
                            if facet_opt == Some("exe") {
                                matched_exe_with_exe_facet = true;
                            }
                        }
                    }
                }
            }
        } else if explicit_pkg {
            if facet_opt.is_none() {
                let pkg_opt = if item_name.is_empty() {
                    Some(root_pkg)
                } else {
                    ws_pkgs().find(|p| p.base_name == item_name)
                };
                if let Some(pkg) = pkg_opt {
                    push_default_pkg_exes(pkg, &mut push_exe);
                }
            }
        } else if item_name.is_empty() {
            if facet_opt.is_none() {
                push_default_pkg_exes(root_pkg, &mut push_exe);
            }
        } else if let Some(pkg) = ws_pkgs().find(|p| {
            p.libs.iter().any(|l| l.name == item_name)
                || p.exes.iter().any(|e| e.name == item_name)
                || p.custom_targets.iter().any(|c| c == &item_name)
                || p.extern_libs.iter().any(|e| e.name == item_name)
        }) {
            let lib_shadows = pkg.libs.iter().any(|l| l.name == item_name);
            if !lib_shadows {
                if let Some(exe) = pkg.exes.iter().find(|e| e.name == item_name) {
                    push_exe(pkg, exe);
                    if facet_opt == Some("exe") {
                        matched_exe_with_exe_facet = true;
                    }
                }
            }
        } else if facet_opt.is_none() {
            if let Some(pkg) = ws_pkgs().find(|p| p.base_name == item_name) {
                push_default_pkg_exes(pkg, &mut push_exe);
            }
        }
        if matched_exe_with_exe_facet {
            let prefix = if explicit_pkg { "@" } else { "" };
            module_prep_targets.push(format!("{prefix}{target_base}:default"));
        } else {
            module_prep_targets.push(raw_target.clone());
        }
    }
    (exe_targets, module_prep_targets)
}

pub(super) fn collect_prebuilt_dep_pkg_closure_for_statement(
    cfg: &ProjectConfig,
    initial_spec: &DiscoveredModuleSpec,
    importer_needs_import_dynlibs: bool,
    importer_needs_c: bool,
    require_git_pinned_pkgs: bool,
    memo: &mut DepClosureMemo,
) -> Result<Option<Vec<(String, PathBuf)>>> {
    if initial_spec.precompile_modules || importer_needs_import_dynlibs {
        return Ok(None);
    }
    let memo_key = (
        initial_spec.pkg_root.clone(),
        initial_spec.module_name.clone(),
        importer_needs_c,
        require_git_pinned_pkgs,
    );
    if let Some(cached) = memo.prebuilt_closure.get(&memo_key) {
        return match cached {
            Ok(v) => Ok(v.clone()),
            Err(msg) => anyhow::bail!("{msg}"),
        };
    }
    let res: Result<Option<Vec<(String, PathBuf)>>> = (|| {
        let mut visited: HashSet<(PathBuf, String)> = HashSet::new();
        let mut queue: VecDeque<DiscoveredModuleSpec> = VecDeque::new();
        let mut olean_pairs = Vec::new();
        visited.insert((
            initial_spec.pkg_root.clone(),
            initial_spec.module_name.clone(),
        ));
        queue.push_back(initial_spec.clone());
        while let Some(cur) = queue.pop_front() {
            if cur.pkg_root != initial_spec.pkg_root || cur.module_name != initial_spec.module_name
            {
                let sub_key = (
                    cur.pkg_root.clone(),
                    cur.module_name.clone(),
                    importer_needs_c,
                    require_git_pinned_pkgs,
                );
                if let Some(sub_cached) = memo.prebuilt_closure.get(&sub_key) {
                    match sub_cached {
                        Ok(Some(sub_pairs)) => {
                            olean_pairs.extend(sub_pairs.iter().cloned());
                            continue;
                        }
                        Ok(None) => return Ok(None),
                        Err(msg) => anyhow::bail!("{msg}"),
                    }
                }
            }
            let unit_key = (
                cur.pkg_root.clone(),
                cur.module_name.clone(),
                importer_needs_c,
                require_git_pinned_pkgs,
            );
            let unit_res = if let Some(cached_unit) = memo.prebuilt_unit_memo.get(&unit_key) {
                cached_unit.clone()
            } else {
                let computed_unit: Result<Option<(PathBuf, Vec<String>)>, String> = (|| {
                    let is_git_pinned =
                        !cur.is_root_pkg && is_git_pinned_manifest_package(cfg, &cur);
                    if require_git_pinned_pkgs && !is_git_pinned {
                        return Ok(None);
                    }
                    let Ok(src) = fs::read_to_string(&cur.src_path) else {
                        return Ok(None);
                    };
                    if is_git_pinned {
                        splitter::reject_git_pinned_dep_checking_weakening(&src)
                            .with_context(|| {
                                format!("Module {} ({})", cur.module_name, cur.src_path.display())
                            })
                            .map_err(|e| format!("{e:#}"))?;
                    } else {
                        splitter::reject_checking_weakening(&src)
                            .with_context(|| {
                                format!("Module {} ({})", cur.module_name, cur.src_path.display())
                            })
                            .map_err(|e| format!("{e:#}"))?;
                    }
                    if spec_source_has_disallowed_elab_host_effects(cfg, &cur, &src) {
                        return Ok(None);
                    }
                    let hdr = parse_header_info(&src);
                    if hdr.header_error.is_some() {
                        return Ok(None);
                    }
                    let rel_slash = module_name_to_rel_slash(&cur.module_name);
                    let olean_path = cur.build_lib_lean_dir.join(format!("{}.olean", rel_slash));
                    if !is_regular_nonempty_file(&olean_path) {
                        return Ok(None);
                    }
                    let c_path = cur.build_ir_dir.join(format!("{}.c", rel_slash));
                    let Ok(tv) = verify_trace_outputs_against_artifacts_ext(
                        &olean_path,
                        hdr.is_module,
                        Some((c_path.as_path(), importer_needs_c)),
                        true,
                    ) else {
                        return Ok(None);
                    };
                    if tv.get("inputs").is_some() {
                        let expected_src_h = format!("{:016x}", lake_hash_text(&src));
                        let src_matched = trace_recorded_src_hash(&tv)
                            == Some(expected_src_h.as_str())
                            || tv
                                .pointer("/inputs/3/1")
                                .and_then(|v| v.as_str())
                                .is_some_and(|s| s == expected_src_h)
                            || tv
                                .pointer("/inputs/4/1")
                                .and_then(|v| v.as_str())
                                .is_some_and(|s| s == expected_src_h);
                        if !src_matched {
                            return Ok(None);
                        }
                    }
                    let mut lc_visiting = HashSet::new();
                    if lake_closure_export_info(
                        cfg,
                        &cur,
                        false,
                        &mut memo.lake_closure_cache,
                        &mut lc_visiting,
                    )
                    .is_none()
                    {
                        return Ok(None);
                    }
                    Ok(Some((olean_path, hdr.imports)))
                })(
                );
                memo.prebuilt_unit_memo
                    .insert(unit_key, computed_unit.clone());
                computed_unit
            };
            let (olean_path, unit_imports) = match unit_res {
                Ok(Some(pair)) => pair,
                Ok(None) => return Ok(None),
                Err(msg) => anyhow::bail!("{msg}"),
            };
            olean_pairs.push((cur.module_name.clone(), olean_path));
            for imp in unit_imports {
                let matches = memo.resolve_dep_pkg_matches(cfg, &imp);
                if matches.len() > 1 {
                    let pkg_names: Vec<String> =
                        matches.iter().map(|m| m.pkg_name.clone()).collect();
                    anyhow::bail!(
                        "Ambiguous module import `{}` (imported by `{}`) resolved in multiple dependency packages: {:?}",
                        imp,
                        cur.module_name,
                        pkg_names
                    );
                }
                if let Some(sub_spec) = matches.first().cloned() {
                    if sub_spec.precompile_modules {
                        return Ok(None);
                    }
                    let key = (sub_spec.pkg_root.clone(), sub_spec.module_name.clone());
                    if visited.insert(key) {
                        queue.push_back(sub_spec);
                    }
                    continue;
                }
                if memo.resolve_root_pkg_importable(cfg, &imp).is_some() {
                    return Ok(None);
                }
                match resolve_import_site(cfg, &imp) {
                    ImportSite::Toolchain if memo.is_unshadowed_toolchain(cfg, &imp) => {
                        continue;
                    }
                    ImportSite::Prebuilt(pb_path) => {
                        if let Some(pb_closure) =
                            memo.collect_prebuilt_olean_closure(cfg, &imp, &pb_path)
                        {
                            olean_pairs.extend(pb_closure);
                            continue;
                        }
                    }
                    _ => {}
                }
                return Ok(None);
            }
        }
        olean_pairs.sort_by(|a, b| a.0.cmp(&b.0));
        olean_pairs.dedup_by(|a, b| a.0 == b.0);
        Ok(Some(olean_pairs))
    })();
    memo.prebuilt_closure.insert(
        memo_key,
        match &res {
            Ok(v) => Ok(v.clone()),
            Err(e) => Err(format!("{e:#}")),
        },
    );
    res
}

pub(super) type LakeRecipeMemoKey = (PathBuf, String, PathBuf, String, Vec<String>, String);
pub(super) type LakeRecipeMemoVal = Vec<(String, PathBuf, String)>;
pub(super) static LAKE_RECIPE_MEMO: OnceLock<Mutex<HashMap<LakeRecipeMemoKey, LakeRecipeMemoVal>>> =
    OnceLock::new();

pub(super) fn pkg_non_lake_tree_digest(pkg: &PackageConfig) -> Option<String> {
    let root = pkg.pkg_root.canonicalize().ok()?;
    let build_abs = if pkg.build_dir.is_absolute() {
        pkg.build_dir.clone()
    } else {
        root.join(&pkg.build_dir)
    };
    let mut entries: Vec<(Vec<u8>, [u8; 32])> = Vec::new();
    let iter = walkdir::WalkDir::new(&root)
        .follow_links(false)
        .into_iter()
        .filter_entry(|e| {
            if e.depth() == 0 {
                return true;
            }
            let name = e.file_name();
            if name == ".lake" || name == ".git" {
                return false;
            }
            e.path() != build_abs
        });
    for entry in iter {
        let entry = entry.ok()?;
        if entry.path_is_symlink() {
            return None;
        }
        if entry.file_type().is_dir() {
            continue;
        }
        if !entry.file_type().is_file() || entries.len() >= 4096 {
            return None;
        }
        let rel = entry.path().strip_prefix(&root).ok()?;
        let bytes = fs::read(entry.path()).ok()?;
        entries.push((
            rel.as_os_str().as_encoded_bytes().to_vec(),
            *blake3::hash(&bytes).as_bytes(),
        ));
    }
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-pkg-recipe-tree-v1\n");
    for (rel, digest) in &entries {
        update_hasher_lp(&mut h, rel);
        h.update(digest);
    }
    Some(h.finalize().to_hex().to_string())
}

pub(crate) fn seed_materialized_lake_recipes_into_snapshot_pkg(
    cfg: &ProjectConfig,
    src_pkg: &PackageConfig,
    dst_pkg_root: &Path,
) -> Result<()> {
    let names = required_lake_recipe_names(&cfg.root_pkg.pkg_root, src_pkg, cfg.is_untrusted);
    if names.is_empty() {
        return Ok(());
    }
    let src_root = src_pkg.pkg_root.canonicalize()?;
    let mut raw_hashes: HashMap<String, String> = HashMap::with_capacity(names.len());
    for name in &names {
        let Some(inp) = src_pkg.inputs.iter().find(|i| &i.name == name) else {
            continue;
        };
        let src_art = src_root.join(&inp.path).canonicalize()?;
        anyhow::ensure!(
            src_art.starts_with(&src_root) && src_art.is_file(),
            "Materialized Lake artifact `{}/{name}` escaped package root",
            src_pkg.name
        );
        let (actual_input_hash, _) = hash_input_target(&src_pkg.pkg_root, inp)?;
        anyhow::ensure!(
            actual_input_hash == inp.blake3,
            "Materialized Lake artifact `{}/{name}` changed on disk",
            src_pkg.name
        );
        let bytes = fs::read(&src_art)?;
        let raw_hash = blake3::hash(&bytes).to_hex().to_string();
        if let Some(ext) = src_pkg.extern_libs.iter().find(|e| &e.name == name) {
            anyhow::ensure!(
                ext.static_artifact_blake3.as_ref() == Some(&raw_hash),
                "Materialized extern library `{}/{name}` changed on disk",
                src_pkg.name
            );
        }
        let dst_art = dst_pkg_root.join(&inp.path);
        if let Some(parent) = dst_art.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&dst_art, &bytes)?;
        raw_hashes.insert(name.clone(), raw_hash);
    }
    let dst_canon = dst_pkg_root.canonicalize()?;
    let mut dummy_pkg = src_pkg.clone();
    dummy_pkg.pkg_root = dst_canon.clone();
    if let (Some(td), Ok(raw_dst_cfg)) = (
        pkg_non_lake_tree_digest(&dummy_pkg),
        resolve_package_config(&dst_canon, false),
    ) {
        let mut items = Vec::with_capacity(names.len());
        for name in &names {
            if let (Some(inp), Some(raw_h)) = (
                src_pkg.inputs.iter().find(|i| &i.name == name),
                raw_hashes.get(name),
            ) {
                let dst_art = dst_canon.join(&inp.path).canonicalize()?;
                items.push((name.clone(), dst_art, raw_h.clone()));
            }
        }
        if items.len() == names.len() {
            let key = (
                cfg.lean_bin.clone(),
                cfg.lean_githash.clone(),
                dst_canon,
                raw_dst_cfg.config_digest,
                names,
                td,
            );
            let memo = LAKE_RECIPE_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
            if let Ok(mut g) = memo.lock() {
                if g.len() >= 256 {
                    g.clear();
                }
                g.insert(key, items);
            }
        }
    }
    Ok(())
}

pub(crate) fn required_lake_recipe_names(
    root_pkg_root: &Path,
    pkg: &PackageConfig,
    is_untrusted: bool,
) -> Vec<String> {
    if is_untrusted {
        return Vec::new();
    }
    let pkg_has_precompile =
        pkg.precompile_modules || pkg.libs.iter().any(|l| l.precompile_modules == Some(true));
    let materialize_custom_targets = pkg.pkg_root == root_pkg_root || pkg_has_precompile;
    pkg.custom_targets
        .iter()
        .filter(|_| materialize_custom_targets)
        .cloned()
        .chain(
            pkg.extern_libs
                .iter()
                .filter(|e| e.is_dynamic_recipe)
                .map(|e| e.name.clone()),
        )
        .collect()
}

pub(super) fn materialize_lake_recipes(cfg: &ProjectConfig, is_untrusted: bool) -> Result<ProjectConfig> {
    let root_pkg_root = cfg.root_pkg.pkg_root.clone();
    if std::iter::once(&cfg.root_pkg)
        .chain(&cfg.dep_pkgs)
        .all(|p| required_lake_recipe_names(&root_pkg_root, p, is_untrusted).is_empty())
    {
        return Ok(cfg.clone());
    }
    let mut resolved = cfg.clone();
    for pkg in std::iter::once(&mut resolved.root_pkg).chain(&mut resolved.dep_pkgs) {
        let names = required_lake_recipe_names(&root_pkg_root, pkg, is_untrusted);
        if names.is_empty() {
            continue;
        }
        anyhow::ensure!(
            !is_untrusted,
            "Untrusted verification rejects dynamic Lake recipes in package `{}`",
            pkg.name
        );
        anyhow::ensure!(
            !crate::lake_build::worktree_auto_link_disabled(&pkg.pkg_root),
            "Lake materialization requires a writable package `{}`",
            pkg.name
        );
        for name in &names {
            anyhow::ensure!(
                !pkg.inputs.iter().any(|i| &i.name == name),
                "Duplicate Lake materialization target `{name}`"
            );
        }
        let root = pkg.pkg_root.canonicalize()?;
        let tree_digest = pkg_non_lake_tree_digest(pkg);
        let memo_key = tree_digest.as_ref().map(|td| {
            (
                cfg.lean_bin.clone(),
                cfg.lean_githash.clone(),
                root.clone(),
                pkg.config_digest.clone(),
                names.clone(),
                td.clone(),
            )
        });
        let cached_artifacts: Option<Vec<(String, PathBuf, String)>> =
            memo_key.as_ref().and_then(|key| {
                let memo = LAKE_RECIPE_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
                let items = memo.lock().ok()?.get(key)?.clone();
                for (_, path, expected_hash) in &items {
                    let canon = path.canonicalize().ok()?;
                    if !canon.starts_with(&root) || !canon.is_file() {
                        return None;
                    }
                    let actual = blake3::hash(&fs::read(&canon).ok()?).to_hex().to_string();
                    if &actual != expected_hash {
                        return None;
                    }
                }
                Some(items)
            });
        let artifacts = if let Some(items) = cached_artifacts {
            items
        } else {
            let tools = ToolchainExecutables::from_lean(&cfg.lean_bin)?;
            let mut queried = Vec::with_capacity(names.len());
            for name in &names {
                let target = format!("@{}/{}", pkg.base_name, name);
                // #407: a `lake query` materializes (builds) its target, so it counts
                // toward the "zero Lake invocations on a warm hit" log.
                crate::module_builder::log_lake_build_invocation(
                    &cfg.root_pkg.pkg_root,
                    "query --json",
                    std::slice::from_ref(&target),
                    false,
                );
                let mut query_cmd = Command::new(&tools.lake);
                scrub_untrusted_env(&mut query_cmd);
                let output = query_cmd
                    .current_dir(&cfg.root_pkg.pkg_root)
                    .env("PATH", tools.lake_build_path(&cfg.root_pkg.pkg_root))
                    .env("LEAN", &tools.lean)
                    .env("LAKE", &tools.lake)
                    .env("LEANC", &tools.leanc)
                    .env("GIT_CONFIG_NOSYSTEM", "1")
                    .env("GIT_CONFIG_GLOBAL", "/dev/null")
                    .env("GIT_ATTR_NOSYSTEM", "1")
                    .env("GIT_TERMINAL_PROMPT", "0")
                    .env("GIT_NO_LAZY_FETCH", "1")
                    .env("GIT_ALLOW_PROTOCOL", "")
                    .env(
                        "GIT_CONFIG_PARAMETERS",
                        "'core.fsmonitor=' 'core.hooksPath=/dev/null' 'core.sshCommand=false' 'core.askPass=' 'credential.helper=' 'protocol.allow=never' 'diff.external=' 'core.attributesFile=/dev/null' 'submodule.recurse=false'",
                    )
                    .args(["query", "--json", &target])
                    .output()
                    .context("Failed to execute Lake materialization")?;
                anyhow::ensure!(
                    output.status.success(),
                    "Lake materialization of `{target}` failed: {}",
                    String::from_utf8_lossy(&output.stderr)
                );
                let path: String = serde_json::from_slice(&output.stdout).with_context(|| {
                    format!("Lake target `{target}` must return a single FilePath")
                })?;
                let path = PathBuf::from(path);
                let path = if path.is_absolute() {
                    path
                } else {
                    cfg.root_pkg.pkg_root.join(path)
                };
                let canonical = path
                    .canonicalize()
                    .with_context(|| format!("Missing Lake artifact for `{target}`"))?;
                anyhow::ensure!(
                    canonical.starts_with(&root) && canonical.is_file(),
                    "Lake target `{target}` must return a regular artifact inside its package"
                );
                let bytes = fs::read(&canonical)?;
                let hash = blake3::hash(&bytes).to_hex().to_string();
                queried.push((name.clone(), canonical, hash));
            }
            if let Some(key) = memo_key {
                let memo = LAKE_RECIPE_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
                if let Ok(mut g) = memo.lock() {
                    if g.len() >= 256 {
                        g.clear();
                    }
                    g.insert(key, queried.clone());
                }
            }
            queried
        };
        for (name, canonical, hash) in artifacts {
            let target = format!("@{}/{}", pkg.base_name, name);
            let mut input = InputTargetConfig {
                name: name.clone(),
                path: canonical.strip_prefix(&root)?.to_path_buf(),
                is_dir: false,
                extension: None,
                extensions: None,
                text: false,
                blake3: String::new(),
                lake_hash: String::new(),
                unsupported: None,
            };
            (input.blake3, input.lake_hash) = hash_input_target(&pkg.pkg_root, &input)?;
            pkg.inputs.push(input);
            if let Some(ext) = pkg.extern_libs.iter_mut().find(|e| e.name == name) {
                anyhow::ensure!(
                    canonical
                        .extension()
                        .and_then(|s| s.to_str())
                        .is_some_and(|s| matches!(s, "a" | "lib")),
                    "Extern library `{target}` did not return a static archive"
                );
                ext.static_artifact_path = Some(canonical);
                ext.static_artifact_blake3 = Some(hash);
            }
        }
    }
    resolved.canonical_config_digest = fold_materialized_recipe_config_digests(
        &root_pkg_root,
        &cfg.canonical_config_digest,
        std::iter::once(&mut resolved.root_pkg).chain(resolved.dep_pkgs.iter_mut()),
        is_untrusted,
    );
    Ok(resolved)
}

pub fn build_module_dag_with_trust(
    cfg: &ProjectConfig,
    targets: &[String],
    is_untrusted: bool,
) -> Result<ModuleDag> {
    build_module_dag_inner(cfg, targets, is_untrusted, false)
}

pub(crate) fn build_module_dag_for_trusted_statement(
    cfg: &ProjectConfig,
    targets: &[String],
) -> Result<ModuleDag> {
    build_module_dag_inner(cfg, targets, false, true)
}

pub(super) fn build_module_dag_inner(
    cfg: &ProjectConfig,
    targets: &[String],
    is_untrusted: bool,
    allow_prebuilt_dep_pkgs: bool,
) -> Result<ModuleDag> {
    if is_untrusted {
        anyhow::ensure!(
            std::iter::once(&cfg.root_pkg)
                .chain(&cfg.dep_pkgs)
                .all(|p| {
                    let pkg_has_precompile = p.precompile_modules
                        || p.libs.iter().any(|l| l.precompile_modules == Some(true));
                    (p.custom_targets.is_empty()
                        || (p.pkg_root != cfg.root_pkg.pkg_root && !pkg_has_precompile))
                        && p.extern_libs
                            .iter()
                            .all(|e| e.static_artifact_blake3.is_some())
                }),
            "Untrusted verification rejects dynamic Lake recipes"
        );
    }
    validate_materialized_artifacts(cfg)?;
    let root_pkg = &cfg.root_pkg;
    // For the `build <Lib>` scope gate below (#436): compare canonical paths, so a dependency
    // reached through a symlinked `.lake/packages` entry resolves to the checkout it really is.
    // An out-of-root packages dir counts as the project's own only with PROOF of ownership (a
    // `.turbo-lean-packages-owner` marker naming this project's canonical root): turbo-lean
    // cannot tell a private relocation onto another volume from a packages dir that several
    // projects or worktrees share through a symlink, and the shared case is the publish race
    // #436 closed.
    let root_canon = root_pkg
        .pkg_root
        .canonicalize()
        .unwrap_or_else(|_| root_pkg.pkg_root.clone());
    let packages_canon = root_pkg
        .pkg_root
        .join(&root_pkg.packages_dir)
        .canonicalize()
        .ok()
        .filter(|p| {
            p.starts_with(&root_canon)
                || fs::read_to_string(p.join(".turbo-lean-packages-owner"))
                    .is_ok_and(|s| Path::new(s.trim()) == root_canon.as_path())
        });
    let mut initial_specs: Vec<(DiscoveredModuleSpec, bool)> = Vec::new();
    // Shared-library identity is `(pkg_root, lib_name)`, never `origName`, so two dependencies
    // whose directories share a name cannot collide.
    let mut requested_shared_libs: BTreeSet<(PathBuf, String)> = BTreeSet::new();
    let mut explicit_co_export_mods: HashSet<String> = HashSet::new();
    let mut explicit_dynlib_mods: HashSet<String> = HashSet::new();
    let mut exe_cone_roots: HashSet<String> = HashSet::new();
    let global_emit_c = global_emit_c_enabled();
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
        normalize_build_targets(cfg, targets)
    };
    effective_targets.dedup();
    let push_lib_specs = |target_pkg: &PackageConfig,
                          lib: &LeanLibConfig,
                          target_is_root: bool,
                          force_c_for_target: bool,
                          force_co_export_for_target: bool,
                          force_dynlib_for_target: bool,
                          force_shared_for_target: bool,
                          is_default_lib_facet: bool,
                          req_shared: &mut BTreeSet<(PathBuf, String)>,
                          co_mods: &mut HashSet<String>,
                          dy_mods: &mut HashSet<String>,
                          specs_out: &mut Vec<(DiscoveredModuleSpec, bool)>|
     -> Result<()> {
        let pkg_src_base = target_pkg.pkg_root.join(&target_pkg.src_dir);
        let lib_src = match &lib.src_dir {
            Some(sd) => pkg_src_base.join(sd),
            None => pkg_src_base,
        };
        let build_base = target_pkg.pkg_root.join(&target_pkg.build_dir);
        let build_lib_lean_dir = build_base.join(&target_pkg.lean_lib_dir);
        let build_native_lib_dir = build_base.join(&target_pkg.native_lib_dir);
        let build_ir_dir = build_base.join(&target_pkg.ir_dir);
        let (lean_options, strong_args, weak_args) = compose_effective_args(
            target_pkg,
            &lib.lean_options,
            &lib.more_lean_args,
            &lib.weak_lean_args,
        );
        let precompile = target_pkg.precompile_modules || lib.precompile_modules.unwrap_or(false);
        let lib_shared_default = lib
            .default_facets
            .iter()
            .any(|f| matches!(f.as_str(), "shared" | "LeanLib.sharedFacet"));
        let emit_c_default = precompile
            || lib_shared_default
            || lib
                .default_facets
                .iter()
                .any(|f| matches!(f.as_str(), "c" | "static" | "LeanLib.staticFacet"));
        if force_shared_for_target || (is_default_lib_facet && (precompile || lib_shared_default)) {
            req_shared.insert((target_pkg.pkg_root.clone(), lib.name.clone()));
        }
        let extern_digests: Vec<String> = target_pkg
            .extern_libs
            .iter()
            .filter_map(|e| {
                e.static_artifact_blake3
                    .as_ref()
                    .map(|h| format!("{}:{}", e.name, h))
            })
            .collect();
        for (m_name, m_path) in expand_lib_configured_modules(target_pkg, lib)? {
            if force_co_export_for_target {
                co_mods.insert(m_name.clone());
            }
            if force_dynlib_for_target {
                dy_mods.insert(m_name.clone());
            }
            // #299: Lake attaches a module's build settings through `findModule?` (the LAST
            // library that can build it), even when an earlier library's glob expanded it here.
            // Route `leanOptions` / `moreLeanArgs` / `weakLeanArgs` through that resolution so
            // overlapping globs cannot hand a module the expanding library's options, and OR the
            // owner's fail-closed `unsupported` flags in below, so a clean expanding library
            // cannot launder a module of an owner turbo-lean cannot build like Lake. The
            // needs-trace attribution (`target_name`, facets, precompile) stays the expanding
            // library's, which `lake_needs_trace_entries` documents and pins. With a single
            // library the owner is the expander by construction, so the lookup is skipped.
            let owner = if target_pkg.libs.len() > 1 {
                resolve_importable_module_in_package(target_pkg, target_is_root, &m_name)
                    .filter(|o| o.src_path == m_path && o.target_name != lib.name)
            } else {
                None
            };
            let (m_opts, m_strong, m_weak) = match &owner {
                Some(o) => (
                    o.lean_options.clone(),
                    o.strong_args.clone(),
                    o.weak_args.clone(),
                ),
                None => (
                    lean_options.clone(),
                    strong_args.clone(),
                    weak_args.clone(),
                ),
            };
            specs_out.push((
                DiscoveredModuleSpec {
                    module_name: m_name,
                    pkg_name: target_pkg.name.clone(),
                    pkg_base_name: target_pkg.base_name.clone(),
                    target_name: lib.name.clone(),
                    platform_independent: lib
                        .platform_independent
                        .or(target_pkg.platform_independent),
                    is_root_pkg: target_is_root,
                    pkg_root: target_pkg.pkg_root.clone(),
                    src_root: lib_src.clone(),
                    src_path: m_path,
                    build_lib_lean_dir: build_lib_lean_dir.clone(),
                    build_native_lib_dir: build_native_lib_dir.clone(),
                    build_ir_dir: build_ir_dir.clone(),
                    precompile_modules: precompile,
                    emit_c_default,
                    is_exe_target: false,
                    lean_options: m_opts,
                    strong_args: m_strong,
                    weak_args: m_weak,
                    extern_lib_digests: extern_digests.clone(),
                    custom_target_needs: lib.custom_target_needs.clone(),
                    pkg_config_digest: target_pkg.config_digest.clone(),
                    unsupported: target_pkg
                        .unsupported
                        .clone()
                        .or_else(|| lib.unsupported.clone())
                        .or_else(|| owner.as_ref().and_then(|o| o.unsupported.clone())),
                    native_unsupported: target_pkg
                        .native_unsupported
                        .clone()
                        .or_else(|| lib.native_unsupported.clone())
                        .or_else(|| owner.as_ref().and_then(|o| o.native_unsupported.clone())),
                    link_unsupported: target_pkg
                        .link_unsupported
                        .clone()
                        .or_else(|| lib.link_unsupported.clone())
                        .or_else(|| owner.as_ref().and_then(|o| o.link_unsupported.clone())),
                },
                force_c_for_target || emit_c_default,
            ));
        }
        Ok(())
    };
    for raw_target in &effective_targets {
        let raw_trimmed = raw_target.trim();
        let explicit_pkg = raw_trimmed.starts_with('@');
        let explicit_workspace_module = !explicit_pkg && raw_trimmed.starts_with('+');
        let mut t = raw_trimmed;
        if let Some(r) = t.strip_prefix('@') {
            t = r;
        }
        if t.matches(':').count() > 1 {
            anyhow::bail!(
                "Invalid target spec `{}` (more than one `:`): fail-closed static Lake config gate",
                raw_target
            );
        }
        let (target_base, facet_opt) = match t.split_once(':') {
            Some((b, f)) => (b.trim(), Some(f.trim())),
            None => (t, None),
        };
        let mut force_c_for_target = global_emit_c;
        let mut force_co_export_for_target = false;
        let mut force_dynlib_for_target = false;
        let mut force_shared_for_target = false;
        if let Some(facet) = facet_opt {
            if facet.is_empty() {
                anyhow::bail!(
                    "Invalid target spec `{}` (more than one `:`): fail-closed static Lake config gate",
                    raw_target
                );
            }
            match facet {
                "olean"
                | "ilean"
                | "lib"
                | "modules"
                | "default"
                | "LeanLib.defaultFacet"
                | "leanArts"
                | "LeanLib.leanArtsFacet" => {}
                "c" | "static" | "LeanLib.staticFacet" => {
                    force_c_for_target = true;
                }
                "o.export" | "c.o.export" => {
                    if is_untrusted {
                        let _ = c_abi::verify_static_lake_config(true, false, false, true);
                        anyhow::bail!(
                            "Unsupported target facet `:{}` in untrusted target `{}`: fail-closed static Lake config gate",
                            facet,
                            raw_target
                        );
                    }
                    force_c_for_target = true;
                    force_co_export_for_target = true;
                }
                "dynlib" => {
                    if is_untrusted {
                        let _ = c_abi::verify_static_lake_config(true, false, false, true);
                        anyhow::bail!(
                            "Unsupported target facet `:{}` in untrusted target `{}`: fail-closed static Lake config gate",
                            facet,
                            raw_target
                        );
                    }
                    force_c_for_target = true;
                    force_co_export_for_target = true;
                    force_dynlib_for_target = true;
                }
                "shared" | "LeanLib.sharedFacet" => {
                    if is_untrusted {
                        let _ = c_abi::verify_static_lake_config(true, false, false, true);
                        anyhow::bail!(
                            "Unsupported target facet `:{}` in untrusted target `{}`: fail-closed static Lake config gate",
                            facet,
                            raw_target
                        );
                    }
                    force_c_for_target = true;
                    force_co_export_for_target = true;
                    force_shared_for_target = true;
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
        let slash_parts: Vec<&str> = target_base.split('/').collect();
        let (pkg_filter, item_raw, explicit_pkg_item_mod) = match slash_parts.as_slice() {
            [only] => (None, *only, false),
            [pkg, item] => (
                Some((*pkg).trim()),
                (*item).trim(),
                (*item).trim().starts_with('+'),
            ),
            _ => {
                anyhow::bail!(
                    "Invalid target spec `{}` (more than one `/`): fail-closed static Lake config gate",
                    raw_target
                );
            }
        };
        let item_body = item_raw.strip_prefix('+').unwrap_or(item_raw);
        let item_name = clean_lake_ident(item_body);
        let ws_pkgs = || std::iter::once(root_pkg).chain(cfg.dep_pkgs.iter());
        let find_pkg_by_base = |base: &str| -> Option<&PackageConfig> {
            if base.is_empty() {
                return Some(root_pkg);
            }
            ws_pkgs().find(|p| p.base_name == base)
        };
        let ws_target_decl_pkg = |name: &str| -> Option<&PackageConfig> {
            ws_pkgs().find(|p| {
                p.libs.iter().any(|l| l.name == name)
                    || p.exes.iter().any(|e| e.name == name)
                    || p.custom_targets.iter().any(|c| c == name)
                    || p.extern_libs.iter().any(|e| e.name == name)
            })
        };
        let ws_target_module_pkg = |name: &str| -> Option<&PackageConfig> {
            ws_pkgs().find(|p| {
                resolve_module_in_package(p, p.pkg_root == root_pkg.pkg_root, name).is_some()
            })
        };
        let mut target_pkg = if let Some(pf) = pkg_filter {
            let pf_clean = pf.strip_prefix('@').unwrap_or(pf);
            let base = clean_lake_ident(pf_clean);
            match find_pkg_by_base(&base) {
                Some(p) => p,
                None => anyhow::bail!("Unknown package `{}` in target `{}`", pf, raw_target),
            }
        } else if explicit_workspace_module {
            match ws_target_module_pkg(&item_name) {
                Some(p) => p,
                None => {
                    anyhow::bail!("Unknown target module `{}` in workspace", raw_target)
                }
            }
        } else if explicit_pkg {
            if item_raw.starts_with('+') {
                anyhow::bail!("Unknown package `{}` in target `{}`", item_raw, raw_target);
            }
            match find_pkg_by_base(&item_name) {
                Some(p) => p,
                None => anyhow::bail!("Unknown package `{}` in target `{}`", item_raw, raw_target),
            }
        } else {
            root_pkg
        };
        let mut bare_as_package = false;
        if pkg_filter.is_none()
            && !explicit_pkg
            && !explicit_workspace_module
            && !item_name.is_empty()
        {
            if let Some(p) = ws_target_decl_pkg(&item_name) {
                target_pkg = p;
            } else if let Some(p) = find_pkg_by_base(&item_name) {
                target_pkg = p;
                bare_as_package = true;
            } else if let Some(p) = ws_target_module_pkg(&item_name) {
                target_pkg = p;
            }
        }
        let target_is_root = target_pkg.pkg_root == root_pkg.pkg_root;
        let package_defaults =
            item_raw.is_empty() || bare_as_package || (explicit_pkg && pkg_filter.is_none());
        let explicit_module = explicit_workspace_module || explicit_pkg_item_mod;
        if package_defaults && facet_opt.is_some() {
            let _ = c_abi::verify_static_lake_config(true, false, false, true);
            anyhow::bail!(
                "Unsupported target facet `:{}` on package `{}`: fail-closed static Lake config gate",
                facet_opt.unwrap_or(""),
                raw_target
            );
        }
        if !package_defaults
            && !explicit_module
            && (target_pkg.custom_targets.iter().any(|ct| ct == &item_name)
                || target_pkg.extern_libs.iter().any(|el| el.name == item_name))
        {
            anyhow::ensure!(
                facet_opt.is_none(),
                "Unsupported facet on materialized Lake target `{raw_target}`"
            );
            continue;
        }
        let mut matched = false;
        let mut default_entries: Vec<String> = Vec::new();
        if package_defaults {
            matched = true;
            default_entries = target_pkg.default_targets.clone();
        }
        for entry in &default_entries {
            let entry_name = clean_lake_ident(entry);
            if target_pkg.custom_targets.iter().any(|ct| ct == &entry_name)
                || target_pkg
                    .extern_libs
                    .iter()
                    .any(|el| el.name == entry_name)
            {
                continue;
            }
            if let Some(lib) = target_pkg.libs.iter().find(|l| l.name == entry_name) {
                push_lib_specs(
                    target_pkg,
                    lib,
                    target_is_root,
                    force_c_for_target,
                    false,
                    false,
                    force_shared_for_target,
                    true,
                    &mut requested_shared_libs,
                    &mut explicit_co_export_mods,
                    &mut explicit_dynlib_mods,
                    &mut initial_specs,
                )?;
            } else if let Some(exe) = target_pkg.exes.iter().find(|e| e.name == entry_name) {
                if let Some(spec) = resolve_module_in_package(target_pkg, target_is_root, &exe.root)
                {
                    let emit_c = !is_untrusted || force_c_for_target || spec.emit_c_default;
                    if emit_c && !is_untrusted {
                        exe_cone_roots.insert(spec.module_name.clone());
                    }
                    initial_specs.push((spec, emit_c));
                } else {
                    anyhow::bail!(
                        "Executable `{}` root module `{}` not found in package `{}`",
                        exe.name,
                        exe.root,
                        target_pkg.name
                    );
                }
            } else if let Some(spec) =
                resolve_module_in_package(target_pkg, target_is_root, &entry_name)
            {
                let emit_c = force_c_for_target || spec.emit_c_default || spec.is_exe_target;
                if spec.is_exe_target && emit_c && !is_untrusted {
                    exe_cone_roots.insert(spec.module_name.clone());
                }
                initial_specs.push((spec, emit_c));
            } else {
                anyhow::bail!(
                    "Unknown target or module `{}` in package `{}`",
                    entry,
                    target_pkg.name
                );
            }
        }
        // 1. Match against lean_lib targets
        for lib in &target_pkg.libs {
            if !package_defaults && !explicit_module && lib.name == item_name {
                matched = true;
                if facet_opt.is_some_and(|f| matches!(f, "dynlib" | "o.export" | "c.o.export")) {
                    let _ = c_abi::verify_static_lake_config(true, false, false, true);
                    anyhow::bail!(
                        "Unsupported target facet `:{}` on lean_lib `{}`: fail-closed static Lake config gate",
                        facet_opt.unwrap_or(""),
                        raw_target
                    );
                }
                let is_default_lib_facet = match facet_opt {
                    None => true,
                    Some(f) => matches!(f, "default" | "LeanLib.defaultFacet"),
                };
                push_lib_specs(
                    target_pkg,
                    lib,
                    target_is_root,
                    force_c_for_target,
                    force_co_export_for_target,
                    force_dynlib_for_target,
                    force_shared_for_target,
                    is_default_lib_facet,
                    &mut requested_shared_libs,
                    &mut explicit_co_export_mods,
                    &mut explicit_dynlib_mods,
                    &mut initial_specs,
                )?;
            }
        }
        // 2. Match against lean_exe targets. Lake's LeanExe facets are only `default` and `exe`
        // (`LeanExe.initFacetConfigs`); `:exe` links a native binary turbo-lean does not produce,
        // and `default` only succeeds when it stays at module-level preparation (`facet_opt == Some("default")` or `None`).
        for exe in &target_pkg.exes {
            if !package_defaults && exe.name == item_name && !explicit_module {
                matched = true;
                if facet_opt.is_some_and(|f| f != "default") {
                    let _ = c_abi::verify_static_lake_config(true, false, false, true);
                    anyhow::bail!(
                        "Unsupported target facet `:{}` on lean_exe `{}`: fail-closed static Lake config gate",
                        facet_opt.unwrap_or(""),
                        raw_target
                    );
                }
                if let Some(spec) = resolve_module_in_package(target_pkg, target_is_root, &exe.root)
                {
                    let emit_c = !is_untrusted
                        || force_c_for_target
                        || !targets.is_empty()
                        || spec.emit_c_default;
                    if emit_c && !is_untrusted {
                        exe_cone_roots.insert(spec.module_name.clone());
                    }
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
                if facet_opt.is_some_and(|f| {
                    matches!(
                        f,
                        "lib"
                            | "modules"
                            | "LeanLib.defaultFacet"
                            | "LeanLib.leanArtsFacet"
                            | "static"
                            | "LeanLib.staticFacet"
                            | "shared"
                            | "LeanLib.sharedFacet"
                    )
                }) {
                    let _ = c_abi::verify_static_lake_config(true, false, false, true);
                    anyhow::bail!(
                        "Unsupported target facet `:{}` on module `{}`: fail-closed static Lake config gate",
                        facet_opt.unwrap_or(""),
                        raw_target
                    );
                }
                if force_co_export_for_target {
                    explicit_co_export_mods.insert(spec.module_name.clone());
                }
                if force_dynlib_for_target {
                    explicit_dynlib_mods.insert(spec.module_name.clone());
                }
                let emit_c = force_c_for_target || spec.emit_c_default || spec.is_exe_target;
                if spec.is_exe_target && emit_c && !is_untrusted {
                    exe_cone_roots.insert(spec.module_name.clone());
                }
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
    // Fallback: if no explicit targets were passed and root package declared no libs and no exes
    // (e.g. bare lakefile.lean `package foo`), discover all `.lean` files under `root_pkg.src_dir`
    if targets.is_empty()
        && initial_specs.is_empty()
        && root_pkg.libs.is_empty()
        && root_pkg.exes.is_empty()
    {
        let src_root = root_pkg.pkg_root.join(&root_pkg.src_dir);
        let files = lake_build::collect_lean_files(&src_root);
        let build_base = root_pkg.pkg_root.join(&root_pkg.build_dir);
        let (lean_options, strong_args, weak_args) =
            compose_effective_args(root_pkg, &LeanOptionsMap::new(), &[], &[]);
        let extern_lib_digests: Vec<String> = root_pkg
            .extern_libs
            .iter()
            .filter_map(|e| {
                e.static_artifact_blake3
                    .as_ref()
                    .map(|h| format!("{}:{}", e.name, h))
            })
            .collect();
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
                            pkg_base_name: root_pkg.base_name.clone(),
                            target_name: root_pkg.name.clone(),
                            platform_independent: root_pkg.platform_independent,
                            is_root_pkg: true,
                            pkg_root: root_pkg.pkg_root.clone(),
                            src_root: src_root.clone(),
                            src_path: f,
                            build_lib_lean_dir: build_base.join(&root_pkg.lean_lib_dir),
                            build_native_lib_dir: build_base.join(&root_pkg.native_lib_dir),
                            build_ir_dir: build_base.join(&root_pkg.ir_dir),
                            precompile_modules: root_pkg.precompile_modules,
                            emit_c_default: root_pkg.precompile_modules,
                            is_exe_target: false,
                            lean_options: lean_options.clone(),
                            strong_args: strong_args.clone(),
                            weak_args: weak_args.clone(),
                            extern_lib_digests: extern_lib_digests.clone(),
                            custom_target_needs: Vec::new(),
                            pkg_config_digest: root_pkg.config_digest.clone(),
                            unsupported: root_pkg.unsupported.clone(),
                            native_unsupported: root_pkg.native_unsupported.clone(),
                            link_unsupported: root_pkg.link_unsupported.clone(),
                        },
                        global_emit_c || root_pkg.precompile_modules,
                    ));
                }
            }
        }
    }
    // Collect caller LEAN_PATH directories for prebuilt external olean lookup (trusted mode only)
    let external_lean_path_dirs = if is_untrusted {
        Vec::new()
    } else {
        trusted_lean_path_dirs(cfg)
    };
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
    let mut expanded_shared_libs: HashSet<(PathBuf, String)> = HashSet::new();
    let enqueue_shared_lib_mods = |pkg_root: &Path,
                                   lib_name: &str,
                                   expanded: &mut HashSet<(PathBuf, String)>,
                                   req_shared: &mut BTreeSet<(PathBuf, String)>,
                                   wl: &mut VecDeque<(DiscoveredModuleSpec, bool)>|
     -> Result<()> {
        let key = (pkg_root.to_path_buf(), lib_name.to_string());
        req_shared.insert(key.clone());
        if !expanded.insert(key) {
            return Ok(());
        }
        let Some(pkg) = cfg
            .dep_pkgs
            .iter()
            .chain(std::iter::once(&cfg.root_pkg))
            .find(|p| p.pkg_root == pkg_root)
        else {
            return Ok(());
        };
        let Some(lib) = pkg.libs.iter().find(|l| l.name == lib_name) else {
            return Ok(());
        };
        let is_root = pkg.pkg_root == root_pkg.pkg_root;
        for (m_name, _) in expand_lib_configured_modules(pkg, lib)? {
            if let Some(lspec) = resolve_importable_module_in_package(pkg, is_root, &m_name) {
                wl.push_back((lspec, true));
            }
        }
        Ok(())
    };
    for (pkg_root, lib_name) in requested_shared_libs.clone() {
        enqueue_shared_lib_mods(
            &pkg_root,
            &lib_name,
            &mut expanded_shared_libs,
            &mut requested_shared_libs,
            &mut worklist,
        )?;
    }
    let mut dep_closure_memo = DepClosureMemo::new(cfg);
    // #299 round 2: per-import memo of dependencies that OWN the name with a MISSING source
    // file; they count toward the ambiguity check and stop resolution, while
    // `resolve_dep_pkg_matches` memoizes only Found results.
    let mut owned_missing_memo: std::collections::HashMap<String, Vec<(String, String, PathBuf)>> =
        std::collections::HashMap::new();
    loop {
        while let Some((spec, requested_c)) = worklist.pop_front() {
            if let Some(existing) = nodes.get_mut(&spec.module_name) {
                if existing.pkg_root != spec.pkg_root || existing.src_path != spec.src_path {
                    anyhow::bail!(
                    "Ambiguous module `{}` resolved in multiple packages or paths (`{}` at {} vs `{}` at {})",
                    spec.module_name,
                    existing.pkg_name,
                    existing.src_path.display(),
                    spec.pkg_name,
                    spec.src_path.display()
                );
                }
                let mut recheck_native = false;
                if requested_c && !existing.needs_c {
                    existing.needs_c = true;
                    recheck_native = true;
                    if !is_untrusted && !exe_cone_roots.is_empty() {
                        for dep in &existing.direct_dag_deps {
                            if let Some(dspec) = resolve_importable_module_in_package(
                                root_pkg, true, dep,
                            )
                            .or_else(|| {
                                cfg.dep_pkgs.iter().find_map(|dp| {
                                    resolve_importable_module_in_package(dp, false, dep)
                                })
                            }) {
                                worklist.push_back((dspec, true));
                            }
                        }
                        let mut dep_revisit = Vec::new();
                        for (ext_mod, _) in &existing.external_olean_deps {
                            if let Some(dspec) = cfg.dep_pkgs.iter().find_map(|dp| {
                                resolve_importable_module_in_package(dp, false, ext_mod)
                            }) {
                                let fresh_ok = collect_fresh_dep_pkg_closure(
                                    cfg,
                                    &dspec,
                                    false,
                                    true,
                                    &mut dep_closure_memo,
                                )?
                                .is_some();
                                let pb_ok = !fresh_ok
                                    && (allow_prebuilt_dep_pkgs
                                        || is_git_pinned_manifest_package(cfg, &dspec))
                                    && collect_prebuilt_dep_pkg_closure_for_statement(
                                        cfg,
                                        &dspec,
                                        false,
                                        true,
                                        !allow_prebuilt_dep_pkgs,
                                        &mut dep_closure_memo,
                                    )?
                                    .is_some();
                                if !fresh_ok && !pb_ok {
                                    dep_revisit.push(dspec);
                                }
                            }
                        }
                        for dspec in dep_revisit {
                            existing
                                .external_olean_deps
                                .retain(|(m, _)| m != &dspec.module_name);
                            existing.direct_dag_deps.push(dspec.module_name.clone());
                            worklist.push_back((dspec, true));
                        }
                    }
                }
                if spec.precompile_modules && !existing.precompile_modules {
                    existing.precompile_modules = true;
                    recheck_native = true;
                }
                if explicit_co_export_mods.contains(&spec.module_name)
                    || explicit_dynlib_mods.contains(&spec.module_name)
                {
                    recheck_native = true;
                }
                if recheck_native && !is_untrusted {
                    let c_obj_why = existing.native_unsupported.as_ref().filter(|_| {
                        existing.precompile_modules
                            || explicit_co_export_mods.contains(&spec.module_name)
                            || explicit_dynlib_mods.contains(&spec.module_name)
                    });
                    let link_why = existing.link_unsupported.as_ref().filter(|_| {
                        existing.precompile_modules
                            || explicit_dynlib_mods.contains(&spec.module_name)
                    });
                    if let Some(why) = c_obj_why.or(link_why) {
                        let _ = c_abi::verify_static_lake_config(true, true, false, false);
                        anyhow::bail!(
                        "Cannot build module `{}` of package `{}` like Lake ({}): fail-closed static Lake config gate",
                        spec.module_name,
                        spec.pkg_name,
                        why
                    );
                    }
                }
                continue;
            }
            // `turbo-lean build <Lib>` scope (#436): a git-pinned dependency checkout outside
            // both the project root and its OWNER-MARKED packages dir is another (possibly
            // shared) checkout, reached through a symlinked `.lake/packages` entry or an
            // unproven relocated packages dir. Compiling its modules natively would publish
            // `.olean`/`.trace` rewrites and `.turbo_publish.lock` files into that foreign
            // checkout, so a pinned out-of-tree dependency is adopted read-only (the fresh or
            // prebuilt closure during import resolution) or fails here, naming the Lake command
            // that refreshes it. Path dependencies and pinned clones under the project root or
            // its proven packages dir keep building, like Lake builds them. The gate covers
            // every trusted non-statement caller of `build_module_dag_with_trust` (`build`,
            // `ci-verify`, freshness probes); `check`'s statement path
            // (`allow_prebuilt_dep_pkgs`) and untrusted builds are unchanged.
            if !is_untrusted && !allow_prebuilt_dep_pkgs && !spec.is_root_pkg {
                let pkg_canon = spec
                    .pkg_root
                    .canonicalize()
                    .unwrap_or_else(|_| spec.pkg_root.clone());
                if !pkg_canon.starts_with(&root_canon)
                    && !packages_canon
                        .as_deref()
                        .is_some_and(|p| pkg_canon.starts_with(p))
                    && is_git_pinned_manifest_package(cfg, &spec)
                {
                    anyhow::bail!(
                        "Cannot build module `{}`: package `{}` is a git-pinned dependency checkout outside the project root ({} is neither under {} nor under an owner-marked packages dir); turbo-lean never compiles or publishes into it. Refresh its Lake artifacts first (run `lake build +{}` from the project root {}) and retry",
                        spec.module_name,
                        spec.pkg_name,
                        pkg_canon.display(),
                        root_canon.display(),
                        spec.module_name,
                        root_pkg.pkg_root.display()
                    );
                }
            }
            // Every DAG node is compiled or restored and published with a Lake trace, which must
            // not happen for a module Lake would build differently.
            if let Some(why) = &spec.unsupported {
                let _ = c_abi::verify_static_lake_config(true, true, false, false);
                anyhow::bail!(
                "Cannot build module `{}` of package `{}` like Lake ({}): fail-closed static Lake config gate",
                spec.module_name,
                spec.pkg_name,
                why
            );
            }
            let src = fs::read_to_string(&spec.src_path).with_context(|| {
                format!(
                    "Failed to read module `{}` at {}",
                    spec.module_name,
                    spec.src_path.display()
                )
            })?;
            if !spec.is_root_pkg && is_git_pinned_manifest_package(cfg, &spec) {
                splitter::reject_git_pinned_dep_checking_weakening(&src).with_context(|| {
                    format!("Module {} ({})", spec.module_name, spec.src_path.display())
                })?;
            } else {
                splitter::reject_checking_weakening(&src).with_context(|| {
                    format!("Module {} ({})", spec.module_name, spec.src_path.display())
                })?;
            }
            let src_blake3 = blake3::hash(src.as_bytes()).to_hex().to_string();
            let header = parse_header_info(&src);
            if let Some(ref herr) = header.header_error {
                anyhow::bail!(
                    "Invalid module header in `{}` ({}): {}",
                    spec.module_name,
                    spec.src_path.display(),
                    herr
                );
            }
            let needs_c =
                requested_c || spec.emit_c_default || header.has_c_export || global_emit_c;
            let native_why = if !is_untrusted {
                let c_obj_why = spec.native_unsupported.as_ref().filter(|_| {
                    spec.precompile_modules
                        || explicit_co_export_mods.contains(&spec.module_name)
                        || explicit_dynlib_mods.contains(&spec.module_name)
                });
                let link_why = spec.link_unsupported.as_ref().filter(|_| {
                    spec.precompile_modules || explicit_dynlib_mods.contains(&spec.module_name)
                });
                c_obj_why.or(link_why)
            } else {
                None
            };
            if let Some(why) = native_why {
                let _ = c_abi::verify_static_lake_config(true, true, false, false);
                anyhow::bail!(
                "Cannot build module `{}` of package `{}` like Lake ({}): fail-closed static Lake config gate",
                spec.module_name,
                spec.pkg_name,
                why
            );
            }
            let mut direct_dag_deps = Vec::new();
            let mut external_olean_deps = Vec::new();
            let mut prebuilt_olean_deps = Vec::new();
            for imp in &header.imports {
                if imp == &spec.module_name {
                    anyhow::bail!(
                        "Module import cycle detected: {} -> {}",
                        spec.module_name,
                        imp
                    );
                }
                // 1. Check if `imp` resolves in root package (`findModule?`, not exe roots)
                let propagate_c_to_deps = !is_untrusted
                    && (spec.precompile_modules
                        || exe_cone_roots.contains(&spec.module_name)
                        || (requested_c && !exe_cone_roots.is_empty()));
                if let Some(dep_spec) = dep_closure_memo.resolve_root_pkg_importable(cfg, imp) {
                    if !dep_spec.is_exe_target
                        && dep_spec.target_name != spec.target_name
                        && (spec.precompile_modules || dep_spec.precompile_modules)
                    {
                        enqueue_shared_lib_mods(
                            &dep_spec.pkg_root,
                            &dep_spec.target_name,
                            &mut expanded_shared_libs,
                            &mut requested_shared_libs,
                            &mut worklist,
                        )?;
                    }
                    direct_dag_deps.push(imp.clone());
                    worklist.push_back((dep_spec, spec.precompile_modules || propagate_c_to_deps));
                    continue;
                }
                // #299: the root package may OWN `imp` (a library's globs select it) while its
                // source file is missing. Lake fails there; falling through would resolve a
                // same-named module from a dependency package instead.
                if let ModuleOwnership::OwnedMissing {
                    target_name,
                    src_path,
                } = resolve_module_in_package_ownership(root_pkg, true, imp, false)
                {
                    anyhow::bail!(
                        "Missing source file for module `{}` (imported by `{}`): library `{}` of the root package owns it at {}, so Lake fails here instead of resolving it in another package",
                        imp,
                        spec.module_name,
                        target_name,
                        src_path.display()
                    );
                }
                // 2. Check if `imp` resolves in any dependency package, failing closed on
                //    ambiguity. A dependency that OWNS the name with a MISSING source file
                //    counts as a candidate too (#299): Lake's `findSomeRev?` may pick it and
                //    fail, so a Found sibling must not resolve silently past it.
                let dep_matches = dep_closure_memo.resolve_dep_pkg_matches(cfg, imp);
                let owned_missing = owned_missing_memo
                    .entry(imp.clone())
                    .or_insert_with(|| {
                        cfg.dep_pkgs
                            .iter()
                            .filter_map(|dp| {
                                match resolve_module_in_package_ownership(dp, false, imp, false) {
                                    ModuleOwnership::OwnedMissing {
                                        target_name,
                                        src_path,
                                    } => Some((dp.name.clone(), target_name, src_path)),
                                    _ => None,
                                }
                            })
                            .collect()
                    })
                    .clone();
                if dep_matches.len() + owned_missing.len() > 1 {
                    let mut pkg_names: Vec<String> =
                        dep_matches.iter().map(|m| m.pkg_name.clone()).collect();
                    pkg_names.extend(owned_missing.iter().map(|(pkg, _, path)| {
                        format!("{pkg} (source file missing at {})", path.display())
                    }));
                    anyhow::bail!(
                    "Ambiguous module import `{}` (imported by `{}`) resolved in multiple dependency packages: {:?}",
                    imp,
                    spec.module_name,
                    pkg_names
                );
                }
                if let Some(dep_spec) = dep_matches.first().cloned() {
                    let importer_in_shared = !spec.is_exe_target
                        && requested_shared_libs
                            .iter()
                            .any(|(_, ln)| ln == &spec.target_name);
                    let same_lib_name = !spec.is_exe_target
                        && !dep_spec.is_exe_target
                        && dep_spec.target_name == spec.target_name;
                    let importer_needs_dep_dynlib = spec.precompile_modules
                        || dep_spec.precompile_modules
                        || importer_in_shared
                        || explicit_dynlib_mods.contains(&spec.module_name);
                    let importer_needs_dep_c =
                        importer_needs_dep_dynlib || propagate_c_to_deps || global_emit_c;
                    if !is_untrusted {
                        if let Some(fresh_closure) = collect_fresh_dep_pkg_closure(
                            cfg,
                            &dep_spec,
                            importer_needs_dep_dynlib,
                            importer_needs_dep_c,
                            &mut dep_closure_memo,
                        )? {
                            external_olean_deps.extend(fresh_closure);
                            continue;
                        }
                        if allow_prebuilt_dep_pkgs || is_git_pinned_manifest_package(cfg, &dep_spec)
                        {
                            if let Some(pb_closure) =
                                collect_prebuilt_dep_pkg_closure_for_statement(
                                    cfg,
                                    &dep_spec,
                                    importer_needs_dep_dynlib,
                                    importer_needs_dep_c,
                                    !allow_prebuilt_dep_pkgs,
                                    &mut dep_closure_memo,
                                )?
                            {
                                external_olean_deps.extend(pb_closure);
                                continue;
                            }
                        }
                    }
                    if !dep_spec.is_exe_target && !same_lib_name && importer_needs_dep_dynlib {
                        enqueue_shared_lib_mods(
                            &dep_spec.pkg_root,
                            &dep_spec.target_name,
                            &mut expanded_shared_libs,
                            &mut requested_shared_libs,
                            &mut worklist,
                        )?;
                    }
                    direct_dag_deps.push(imp.clone());
                    worklist.push_back((dep_spec.clone(), importer_needs_dep_c));
                    continue;
                }
                // #299: the same stop one package out: a dependency that OWNS `imp` with a
                // missing source file is where Lake fails; never fall through to a prebuilt
                // `.olean` or the toolchain for it.
                if let Some((pkg_name, target_name, src_path)) = owned_missing.first() {
                    anyhow::bail!(
                        "Missing source file for module `{}` (imported by `{}`): library `{}` of package `{}` owns it at {}, so Lake fails here instead of resolving it elsewhere",
                        imp,
                        spec.module_name,
                        target_name,
                        pkg_name,
                        src_path.display()
                    );
                }
                // 3. In trusted mode only, check if `imp` exists as a prebuilt `.olean` in `.lake/packages/*/.lake/build/lib/lean` or `LEAN_PATH`
                // BEFORE checking the toolchain library, matching Lean's actual `LEAN_PATH` search order.
                if !is_untrusted {
                    let rel_slash = module_name_to_rel_slash(imp);
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
                            if cand.is_file()
                                && !is_verified_toolchain_olean_file(
                                    &cfg.toolchain_lib_lean,
                                    Some(&cfg.lean_githash),
                                    &cand,
                                )
                            {
                                found_prebuilt = Some(cand);
                                break;
                            }
                        }
                    }
                    if let Some(pb_path) = found_prebuilt {
                        let pb_closure = dep_closure_memo
                            .collect_prebuilt_olean_closure(cfg, imp, &pb_path)
                            .ok_or_else(|| {
                                anyhow::anyhow!(
                                    "Prebuilt import `{}` at {} lacks valid Lake `.trace` / `.hash` sidecars or has a stale transitive import closure",
                                    imp,
                                    pb_path.display()
                                )
                            })?;
                        for (pb_mod, _) in &pb_closure {
                            prebuilt_olean_deps.push(pb_mod.clone());
                        }
                        external_olean_deps.extend(pb_closure);
                        continue;
                    }
                }
                // 4. Check if `imp` resolves to a genuine built-in toolchain `.olean` inside `toolchain_lib_lean`
                if is_builtin_toolchain_module(
                    &cfg.toolchain_lib_lean,
                    Some(&cfg.lean_githash),
                    imp,
                ) {
                    continue;
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
            prebuilt_olean_deps.sort();
            prebuilt_olean_deps.dedup();
            let rel_slash = module_name_to_rel_slash(&spec.module_name);
            let olean_path = spec.build_lib_lean_dir.join(format!("{}.olean", rel_slash));
            let ilean_path = spec.build_lib_lean_dir.join(format!("{}.ilean", rel_slash));
            let c_path = spec.build_ir_dir.join(format!("{}.c", rel_slash));
            nodes.insert(
                spec.module_name.clone(),
                ModuleNode {
                    module_name: spec.module_name.clone(),
                    pkg_name: spec.pkg_name,
                    pkg_base_name: spec.pkg_base_name,
                    target_name: spec.target_name,
                    platform_independent: spec.platform_independent,
                    is_root_pkg: spec.is_root_pkg,
                    pkg_root: spec.pkg_root,
                    src_root: spec.src_root,
                    src_path: spec.src_path,
                    build_lib_lean_dir: spec.build_lib_lean_dir,
                    build_native_lib_dir: spec.build_native_lib_dir,
                    build_ir_dir: spec.build_ir_dir,
                    olean_path,
                    ilean_path,
                    c_path,
                    is_module: header.is_module,
                    has_prelude: header.has_prelude,
                    needs_c,
                    needs_co_export: false,
                    needs_dynlib: false,
                    precompile_modules: spec.precompile_modules,
                    is_exe_target: spec.is_exe_target,
                    lean_options: spec.lean_options,
                    strong_args: spec.strong_args,
                    weak_args: spec.weak_args,
                    src_blake3,
                    direct_dag_deps,
                    external_olean_deps,
                    prebuilt_olean_deps,
                    expected_all_deps: Vec::new(),
                    extern_lib_digests: spec.extern_lib_digests,
                    pkg_config_digest: spec.pkg_config_digest,
                    import_specs: header.import_specs,
                    native_unsupported: spec.native_unsupported,
                    link_unsupported: spec.link_unsupported,
                },
            );
        }
        let mut promoted_ext_deps = false;
        let mut native_stack: Vec<String> = explicit_dynlib_mods.iter().cloned().collect();
        while let Some(m) = native_stack.pop() {
            let Some(node) = nodes.get(&m) else {
                continue;
            };
            for dep in &node.direct_dag_deps {
                if let Some(dn) = nodes.get(dep) {
                    if !dn.is_exe_target
                        && !node.is_exe_target
                        && dn.target_name == node.target_name
                        && explicit_dynlib_mods.insert(dep.clone())
                    {
                        native_stack.push(dep.clone());
                    }
                }
            }
            if !node.external_olean_deps.is_empty() {
                let mut promoted_direct: Vec<String> = Vec::new();
                let mut kept_external: Vec<(String, PathBuf)> = Vec::new();
                for (ext_m, ext_p) in &node.external_olean_deps {
                    let mut dep_spec_opt = None;
                    for dp in &cfg.dep_pkgs {
                        if let Some(ds) = resolve_importable_module_in_package(dp, false, ext_m) {
                            dep_spec_opt = Some(ds);
                            break;
                        }
                    }
                    if let Some(ds) = dep_spec_opt {
                        let is_direct = node.import_specs.iter().any(|is| &is.module == ext_m);
                        if is_direct {
                            if !ds.is_exe_target
                                && (node.is_exe_target || ds.target_name != node.target_name)
                            {
                                enqueue_shared_lib_mods(
                                    &ds.pkg_root,
                                    &ds.target_name,
                                    &mut expanded_shared_libs,
                                    &mut requested_shared_libs,
                                    &mut worklist,
                                )?;
                            } else if !ds.is_exe_target {
                                explicit_dynlib_mods.insert(ext_m.clone());
                                native_stack.push(ext_m.clone());
                            }
                            promoted_direct.push(ext_m.clone());
                            worklist.push_back((ds, true));
                            promoted_ext_deps = true;
                        } else {
                            kept_external.push((ext_m.clone(), ext_p.clone()));
                        }
                    } else {
                        kept_external.push((ext_m.clone(), ext_p.clone()));
                    }
                }
                if let Some(n_mut) = nodes.get_mut(&m) {
                    for dm in promoted_direct {
                        if !n_mut.direct_dag_deps.contains(&dm) {
                            n_mut.direct_dag_deps.push(dm);
                        }
                    }
                    n_mut.external_olean_deps = kept_external;
                }
            }
        }
        let shared_promo_mods: Vec<String> = nodes
            .values()
            .filter(|n| {
                !n.external_olean_deps.is_empty()
                    && (n.precompile_modules
                        || (!n.is_exe_target
                            && requested_shared_libs
                                .iter()
                                .any(|(_, ln)| ln == &n.target_name)))
            })
            .map(|n| n.module_name.clone())
            .collect();
        for sm in shared_promo_mods {
            let Some(node) = nodes.get(&sm) else {
                continue;
            };
            let mut promoted_direct: Vec<String> = Vec::new();
            let mut kept_external: Vec<(String, PathBuf)> = Vec::new();
            for (ext_m, ext_p) in &node.external_olean_deps {
                let mut dep_spec_opt = None;
                for dp in &cfg.dep_pkgs {
                    if let Some(ds) = resolve_importable_module_in_package(dp, false, ext_m) {
                        dep_spec_opt = Some(ds);
                        break;
                    }
                }
                if let Some(ds) = dep_spec_opt {
                    if !ds.is_exe_target
                        && (node.is_exe_target || ds.target_name != node.target_name)
                    {
                        enqueue_shared_lib_mods(
                            &ds.pkg_root,
                            &ds.target_name,
                            &mut expanded_shared_libs,
                            &mut requested_shared_libs,
                            &mut worklist,
                        )?;
                    }
                    if node.import_specs.iter().any(|is| &is.module == ext_m) {
                        promoted_direct.push(ext_m.clone());
                    }
                    worklist.push_back((ds, true));
                    promoted_ext_deps = true;
                } else {
                    kept_external.push((ext_m.clone(), ext_p.clone()));
                }
            }
            if let Some(n_mut) = nodes.get_mut(&sm) {
                for dm in promoted_direct {
                    if !n_mut.direct_dag_deps.contains(&dm) {
                        n_mut.direct_dag_deps.push(dm);
                    }
                }
                n_mut.external_olean_deps = kept_external;
            }
        }
        let precomp_promo_mods: Vec<String> = nodes
            .values()
            .filter(|n| !n.external_olean_deps.is_empty())
            .map(|n| n.module_name.clone())
            .collect();
        for pm in precomp_promo_mods {
            let Some(node) = nodes.get(&pm) else {
                continue;
            };
            let mut has_precomp_ext = false;
            for (ext_m, _) in &node.external_olean_deps {
                for dp in &cfg.dep_pkgs {
                    if let Some(ds) = resolve_importable_module_in_package(dp, false, ext_m) {
                        if ds.precompile_modules {
                            has_precomp_ext = true;
                        }
                        break;
                    }
                }
            }
            if !has_precomp_ext {
                continue;
            }
            let mut promoted_direct: Vec<String> = Vec::new();
            let mut kept_external: Vec<(String, PathBuf)> = Vec::new();
            for (ext_m, ext_p) in &node.external_olean_deps {
                let mut dep_spec_opt = None;
                for dp in &cfg.dep_pkgs {
                    if let Some(ds) = resolve_importable_module_in_package(dp, false, ext_m) {
                        dep_spec_opt = Some(ds);
                        break;
                    }
                }
                if let Some(ds) = dep_spec_opt {
                    if ds.precompile_modules {
                        if !ds.is_exe_target
                            && (node.is_exe_target || ds.target_name != node.target_name)
                        {
                            enqueue_shared_lib_mods(
                                &ds.pkg_root,
                                &ds.target_name,
                                &mut expanded_shared_libs,
                                &mut requested_shared_libs,
                                &mut worklist,
                            )?;
                        }
                        if node.import_specs.iter().any(|is| &is.module == ext_m) {
                            promoted_direct.push(ext_m.clone());
                        }
                        worklist.push_back((ds, true));
                        promoted_ext_deps = true;
                    } else if node.import_specs.iter().any(|is| &is.module == ext_m)
                        || (!ds.is_exe_target
                            && requested_shared_libs
                                .iter()
                                .any(|(_, ln)| ln == &ds.target_name))
                    {
                        promoted_direct.push(ext_m.clone());
                        worklist.push_back((ds, false));
                        promoted_ext_deps = true;
                    } else {
                        kept_external.push((ext_m.clone(), ext_p.clone()));
                    }
                } else {
                    kept_external.push((ext_m.clone(), ext_p.clone()));
                }
            }
            if let Some(n_mut) = nodes.get_mut(&pm) {
                for dm in promoted_direct {
                    if !n_mut.direct_dag_deps.contains(&dm) {
                        n_mut.direct_dag_deps.push(dm);
                    }
                }
                n_mut.external_olean_deps = kept_external;
            }
        }
        let mut discovered_new_shared = promoted_ext_deps;
        let snapshot_nodes: Vec<(String, PathBuf, String, bool, Vec<String>)> = nodes
            .values()
            .map(|n| {
                (
                    n.module_name.clone(),
                    n.pkg_root.clone(),
                    n.target_name.clone(),
                    n.precompile_modules,
                    n.direct_dag_deps.clone(),
                )
            })
            .collect();
        // Any module transitively reachable from a `precompile_modules` node in `nodes`
        // whose library differs from that importer's library causes that library's shared `.so`
        // (and any cross-library imports of `requested_shared_libs` local modules) to be built by Lake.
        for (imp_mod, _imp_root, imp_target, _imp_precomp, imp_deps) in &snapshot_nodes {
            if explicit_dynlib_mods.contains(imp_mod) {
                let imp_is_exe = nodes.get(imp_mod).is_some_and(|n| n.is_exe_target);
                for dm in imp_deps {
                    if let Some(dn) = nodes.get(dm) {
                        if !dn.is_exe_target && (imp_is_exe || dn.target_name != *imp_target) {
                            let key = (dn.pkg_root.clone(), dn.target_name.clone());
                            if !expanded_shared_libs.contains(&key) {
                                enqueue_shared_lib_mods(
                                    &dn.pkg_root,
                                    &dn.target_name,
                                    &mut expanded_shared_libs,
                                    &mut requested_shared_libs,
                                    &mut worklist,
                                )?;
                                discovered_new_shared = true;
                            }
                        }
                    }
                }
            }
        }
        let any_node_precomp = snapshot_nodes.iter().any(|(_, _, _, p, _)| *p);
        if any_node_precomp || !requested_shared_libs.is_empty() || !explicit_dynlib_mods.is_empty()
        {
            for (imp_mod, _imp_root, imp_target, imp_precomp, imp_deps) in &snapshot_nodes {
                let imp_is_exe = nodes.get(imp_mod).is_some_and(|n| n.is_exe_target);
                let explicit_dynlib = explicit_dynlib_mods.contains(imp_mod);
                let importer_is_in_shared =
                    !imp_is_exe && requested_shared_libs.iter().any(|(_, ln)| ln == imp_target);
                if !(*imp_precomp || importer_is_in_shared || explicit_dynlib || any_node_precomp) {
                    continue;
                }
                let mut visited_t: HashSet<String> = HashSet::new();
                let mut stack_t: Vec<String> = imp_deps.clone();
                while let Some(dm) = stack_t.pop() {
                    if !visited_t.insert(dm.clone()) {
                        continue;
                    }
                    if let Some(dn) = nodes.get(&dm) {
                        if !dn.is_exe_target && (imp_is_exe || dn.target_name != *imp_target) {
                            if *imp_precomp
                                || importer_is_in_shared
                                || explicit_dynlib
                                || dn.precompile_modules
                            {
                                let key = (dn.pkg_root.clone(), dn.target_name.clone());
                                if !expanded_shared_libs.contains(&key) {
                                    enqueue_shared_lib_mods(
                                        &dn.pkg_root,
                                        &dn.target_name,
                                        &mut expanded_shared_libs,
                                        &mut requested_shared_libs,
                                        &mut worklist,
                                    )?;
                                    discovered_new_shared = true;
                                }
                            }
                        } else if !dn.is_exe_target && importer_is_in_shared {
                            if let Some(dn_mut) = nodes.get_mut(&dm) {
                                if !dn_mut.needs_c {
                                    dn_mut.needs_c = true;
                                    discovered_new_shared = true;
                                }
                            }
                        }
                        if let Some(dn_ref) = nodes.get(&dm) {
                            stack_t.extend(dn_ref.direct_dag_deps.iter().cloned());
                        }
                    }
                }
            }
        }
        if !discovered_new_shared && worklist.is_empty() {
            break;
        }
    }
    let dag_mod_names: HashSet<String> = nodes.keys().cloned().collect();
    for node in nodes.values_mut() {
        node.external_olean_deps
            .retain(|(ext_m, _)| !dag_mod_names.contains(ext_m));
        node.prebuilt_olean_deps
            .retain(|pb_m| !dag_mod_names.contains(pb_m));
        for imp in &node.import_specs {
            if imp.module != node.module_name
                && dag_mod_names.contains(&imp.module)
                && !node.direct_dag_deps.contains(&imp.module)
            {
                node.direct_dag_deps.push(imp.module.clone());
            }
        }
    }
    let mut shared_libs: Vec<SharedLibSpec> = Vec::new();
    let tc_native_opt = if !requested_shared_libs.is_empty()
        || !explicit_dynlib_mods.is_empty()
        || nodes.values().any(|n| n.precompile_modules)
    {
        Some(query_toolchain_native_spec(&cfg.lean_bin)?)
    } else {
        None
    };
    let (sh_ext, sh_lib_prefix) = match &tc_native_opt {
        Some(spec) => (
            spec.shared_lib_ext(),
            if spec.is_windows { "" } else { "lib" },
        ),
        None => (
            if cfg!(target_os = "macos") {
                "dylib"
            } else if cfg!(target_os = "windows") {
                "dll"
            } else {
                "so"
            },
            if cfg!(target_os = "windows") {
                ""
            } else {
                "lib"
            },
        ),
    };
    for (pkg_root, lib_name) in &requested_shared_libs {
        let Some(pkg) = cfg
            .dep_pkgs
            .iter()
            .chain(std::iter::once(&cfg.root_pkg))
            .find(|p| &p.pkg_root == pkg_root)
        else {
            continue;
        };
        let Some(lib) = pkg.libs.iter().find(|l| &l.name == lib_name) else {
            continue;
        };
        let mut local_modules = Vec::new();
        let mut visited_local = HashSet::new();
        fn rec_collect_local(
            m: &str,
            lib_name: &str,
            nodes: &BTreeMap<String, ModuleNode>,
            visited: &mut HashSet<String>,
            out: &mut Vec<String>,
        ) {
            if !visited.insert(m.to_string()) {
                return;
            }
            let Some(node) = nodes.get(m) else {
                return;
            };
            if node.is_exe_target || node.target_name != lib_name {
                return;
            }
            for imp in &node.import_specs {
                if let Some(dn) = nodes.get(&imp.module) {
                    if !dn.is_exe_target && dn.target_name == lib_name {
                        rec_collect_local(&imp.module, lib_name, nodes, visited, out);
                    }
                }
            }
            out.push(m.to_string());
        }
        if targets.is_empty()
            || expanded_shared_libs.contains(&(pkg_root.clone(), lib_name.clone()))
        {
            for (m, _) in expand_lib_configured_modules(pkg, lib)? {
                rec_collect_local(&m, lib_name, &nodes, &mut visited_local, &mut local_modules);
            }
        } else {
            for m in nodes
                .values()
                .filter(|n| {
                    !n.is_exe_target && &n.pkg_root == pkg_root && &n.target_name == lib_name
                })
                .map(|n| n.module_name.clone())
                .collect::<Vec<_>>()
            {
                rec_collect_local(&m, lib_name, &nodes, &mut visited_local, &mut local_modules);
            }
        }
        if local_modules.is_empty() {
            continue;
        }
        let stem = lean_mk_module_initialization_stem(lib_name, Some(&pkg.name));
        let so_path = pkg
            .pkg_root
            .join(&pkg.build_dir)
            .join(&pkg.native_lib_dir)
            .join(format!("{sh_lib_prefix}{stem}.{sh_ext}"));
        let is_plugin = lib.roots.len() == 1
            && stem == lean_mk_module_initialization_stem(&lib.roots[0], Some(&pkg.name));
        shared_libs.push(SharedLibSpec {
            pkg_name: pkg.name.clone(),
            pkg_base_name: pkg.base_name.clone(),
            pkg_root: pkg.pkg_root.clone(),
            lib_name: lib_name.clone(),
            stem,
            path: so_path,
            is_plugin,
            local_modules,
        });
    }
    let mut precompiled_by_lib: BTreeMap<String, HashSet<String>> = BTreeMap::new();
    for other in nodes.values() {
        if !other.is_exe_target && other.precompile_modules {
            let mut visited_trans: HashSet<String> = HashSet::new();
            let mut stack: Vec<String> = other
                .import_specs
                .iter()
                .filter(|imp| imp.module != other.module_name)
                .map(|imp| imp.module.clone())
                .collect();
            let entry = precompiled_by_lib
                .entry(other.target_name.clone())
                .or_default();
            while let Some(cur_m) = stack.pop() {
                if !visited_trans.insert(cur_m.clone()) {
                    continue;
                }
                if let Some(dn) = nodes.get(&cur_m) {
                    if !dn.is_exe_target && dn.target_name == other.target_name {
                        entry.insert(cur_m.clone());
                    }
                    for sub_imp in &dn.import_specs {
                        if sub_imp.module != cur_m {
                            stack.push(sub_imp.module.clone());
                        }
                    }
                }
            }
        }
    }
    for node in nodes.values_mut() {
        let explicit_co = explicit_co_export_mods.contains(&node.module_name);
        let explicit_dy = explicit_dynlib_mods.contains(&node.module_name);
        let in_shared_lib = shared_libs
            .iter()
            .any(|s| s.local_modules.iter().any(|m| m == &node.module_name));
        let imported_by_same_lib_precompiled = !node.is_exe_target
            && precompiled_by_lib
                .get(&node.target_name)
                .is_some_and(|s| s.contains(&node.module_name));
        node.needs_dynlib = explicit_dy || imported_by_same_lib_precompiled;
        node.needs_co_export = explicit_co || in_shared_lib || node.needs_dynlib;
        if node.needs_co_export {
            node.needs_c = true;
        }
    }
    let mut shared_local_map: HashMap<(PathBuf, String), Vec<String>> = HashMap::new();
    for s in &shared_libs {
        shared_local_map.insert(
            (s.pkg_root.clone(), s.lib_name.clone()),
            s.local_modules.clone(),
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
    for m in nodes.keys().cloned().collect::<Vec<_>>() {
        let Some(node) = nodes.get(&m).cloned() else {
            continue;
        };
        let node_in_shared = shared_libs
            .iter()
            .any(|s| s.local_modules.iter().any(|lm| lm == &m));
        let mut visited_t: HashSet<String> = HashSet::new();
        let mut stack_t: Vec<String> = node.direct_dag_deps.clone();
        while let Some(dep_mod) = stack_t.pop() {
            if !visited_t.insert(dep_mod.clone()) {
                continue;
            }
            let Some(dn) = nodes.get(&dep_mod) else {
                continue;
            };
            stack_t.extend(dn.direct_dag_deps.iter().cloned());
            if !node.is_exe_target && !dn.is_exe_target && dn.target_name == node.target_name {
                continue;
            }
            let is_direct_dep = node.direct_dag_deps.iter().any(|d| d == &dep_mod);
            if !(node.precompile_modules
                || dn.precompile_modules
                || node_in_shared
                || (node.needs_dynlib && is_direct_dep))
                || dn.is_exe_target
            {
                continue;
            }
            let Some(locals) = shared_local_map.get(&(dn.pkg_root.clone(), dn.target_name.clone()))
            else {
                continue;
            };
            for local in locals {
                if local == &m || !nodes.contains_key(local) {
                    continue;
                }
                let already = dependents
                    .get(local)
                    .is_some_and(|list| list.iter().any(|c| c == &m));
                if !already {
                    *in_degree.entry(m.clone()).or_insert(0) += 1;
                    *total_deps.entry(m.clone()).or_insert(0) += 1;
                    dependents.entry(local.clone()).or_default().push(m.clone());
                }
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
        let wave_in_deg_sum: u64 = current_ready
            .iter()
            .map(|m| *in_degree.get(m).unwrap_or(&0) as u64)
            .sum();
        let wave_len = current_ready.len() as u64;
        if !c_abi::verify_dag_wave_step(
            wave_in_deg_sum,
            wave_len,
            visited_nodes as u64,
            total_nodes as u64,
            1,
            wave_len.max(1),
        ) {
            anyhow::bail!(
                "C-ABI gate `leansys_verify_dag_wave_step` rejected DAG wave (in_degree_sum={}, wave_len={}, visited={}/{})",
                wave_in_deg_sum,
                wave_len,
                visited_nodes,
                total_nodes
            );
        }
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
    for m in topological_order.iter().rev() {
        let propagate = nodes.get(m).is_some_and(|n| {
            n.needs_c && (n.precompile_modules || (!is_untrusted && exe_cone_roots.contains(m)))
        });
        if propagate {
            let mut stack: Vec<String> = nodes
                .get(m)
                .map(|n| n.direct_dag_deps.clone())
                .unwrap_or_default();
            let mut visited: HashSet<String> = HashSet::new();
            while let Some(d) = stack.pop() {
                if !visited.insert(d.clone()) {
                    continue;
                }
                if let Some(dn) = nodes.get_mut(&d) {
                    dn.needs_c = true;
                    stack.extend(dn.direct_dag_deps.iter().cloned());
                }
            }
        }
    }
    if is_untrusted {
        if let Some(sl) = shared_libs.first() {
            let _ = c_abi::verify_static_lake_config(true, true, false, false);
            anyhow::bail!(
                "Refusing to precompile/load native shared library `{}` (`{}:{}`) in untrusted mode: fail-closed untrusted native code gate",
                sl.path.display(),
                sl.pkg_name,
                sl.lib_name
            );
        }
        for m in &topological_order {
            if let Some(node) = nodes.get(m) {
                if node.precompile_modules || node.needs_co_export || node.needs_dynlib {
                    let _ = c_abi::verify_static_lake_config(true, true, false, false);
                    anyhow::bail!(
                        "Refusing `precompileModules` / native dynlib build for module `{}` (`{}`) in untrusted mode: fail-closed untrusted native code gate",
                        node.module_name,
                        node.pkg_name
                    );
                }
            }
        }
    } else {
        for (pkg_root, lib_name) in &requested_shared_libs {
            if let Some(pkg) = std::iter::once(&cfg.root_pkg)
                .chain(&cfg.dep_pkgs)
                .find(|p| &p.pkg_root == pkg_root)
            {
                let lib_cfg = pkg.libs.iter().find(|l| &l.name == lib_name);
                let lib_c_why = lib_cfg.and_then(|l| l.native_unsupported.as_deref());
                let lib_link_why = lib_cfg.and_then(|l| l.link_unsupported.as_deref());
                if let Some(why) = pkg
                    .native_unsupported
                    .as_deref()
                    .or(lib_c_why)
                    .or(pkg.link_unsupported.as_deref())
                    .or(lib_link_why)
                {
                    let _ = c_abi::verify_static_lake_config(true, true, false, false);
                    anyhow::bail!(
                        "Cannot build shared library `{}` of package `{}` like Lake ({}): fail-closed static Lake config gate",
                        lib_name,
                        pkg.name,
                        why
                    );
                }
            }
        }
        for m in &topological_order {
            if let Some(node) = nodes.get(m) {
                if node.precompile_modules || node.needs_co_export || node.needs_dynlib {
                    if let Some(ref why) = node.native_unsupported {
                        let _ = c_abi::verify_static_lake_config(true, true, false, false);
                        anyhow::bail!(
                            "Cannot build module `{}` of package `{}` like Lake ({}): fail-closed static Lake config gate",
                            node.module_name,
                            node.pkg_name,
                            why
                        );
                    }
                }
                if node.precompile_modules || node.needs_dynlib {
                    if let Some(ref why) = node.link_unsupported {
                        let _ = c_abi::verify_static_lake_config(true, true, false, false);
                        anyhow::bail!(
                            "Cannot build module `{}` of package `{}` like Lake ({}): fail-closed static Lake config gate",
                            node.module_name,
                            node.pkg_name,
                            why
                        );
                    }
                }
            }
        }
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
        shared_libs,
    })
}
/// The workspace package a module belongs to (root package or a resolved dependency), matched by `pkg_root`.
pub(super) fn package_by_root<'a>(cfg: &'a ProjectConfig, pkg_root: &Path) -> Option<&'a PackageConfig> {
    let packages = || std::iter::once(&cfg.root_pkg).chain(cfg.dep_pkgs.iter());
    packages().find(|p| p.pkg_root == pkg_root).or_else(|| {
        let canonical_root = pkg_root.canonicalize().ok()?;
        packages().find(|p| p.pkg_root.canonicalize().ok().as_ref() == Some(&canonical_root))
    })
}

/// The content digest of the declarative Lake file inputs (`input_file` / `input_dir`) a module's
/// elaboration may read, i.e. those `needs`-ed by a library that can build it. Empty for every
/// module of a package without inputs, so cache keys there are byte-identical to before.
///
/// Lake v4.31 attributes a module to the **last** declared library that can build it
/// (`Package.findModule?` = `leanLibs.findSomeRev?`), which is what `resolve_module_in_package`
/// reproduces for `node.target_name`. But `lake build <lib>` builds the module list of *that*
/// library, so a module selected by two libraries is built under either attribution depending on
/// the target asked for. The digest therefore folds the union over **every** library that can
/// build the module: the conservative choice, which can only over-invalidate, never miss a change.
///
/// Note the converse, which mirrors Lake rather than guarding against it: a module that no library
/// with a `needs` can build gets the empty digest, so an input edit does not invalidate it. That is
/// correct for Lake, where `needs` feeds the `extraDep` job of the declaring library only and a
/// module outside every such library never has the input on its build path. It does mean a file
/// that reads an input at elaboration time while sitting outside the `needs`-ing library's globs is
/// not tracked -- the same blind spot a plain `lake build` has, not one introduced here.
pub(crate) fn module_lake_input_digest(cfg: &ProjectConfig, node: &ModuleNode) -> Result<String> {
    let Some(pkg) = package_by_root(cfg, &node.pkg_root).filter(|p| !p.inputs.is_empty()) else {
        return Ok(String::new());
    };
    for i in &pkg.inputs {
        if let Some(ref why) = i.unsupported {
            anyhow::bail!(
                "Unsupported Lake input `{}` in package `{}`: {}: fail-closed static Lake config gate",
                i.name,
                pkg.name,
                why
            );
        }
    }
    let needed: BTreeSet<&str> = pkg
        .libs
        .iter()
        .filter(|lib| lib_can_build_module(lib, &node.module_name))
        .flat_map(|lib| lib.needs.iter().map(String::as_str))
        .chain(
            pkg.exes
                .iter()
                .filter(|exe| exe.root == node.module_name)
                .flat_map(|exe| exe.needs.iter().map(String::as_str)),
        )
        .collect();
    Ok(pkg
        .inputs
        .iter()
        .filter(|i| needed.contains(i.name.as_str()))
        .map(|i| format!("{}:{}\n", i.name, i.blake3))
        .collect())
}

/// Content digest of every declarative Lake file input in the **workspace**: the root package and
/// every resolved dependency, each entry qualified by its package name.
///
/// [`module_lake_input_digest`] is the precise, per-module answer, but it can only be computed from
/// a resolved [`ModuleNode`]. The warm-build-directory fast paths accept an existing `.olean` out of
/// `.lake/build/.turbo_verified_sources.json` *without* ever computing a module key -- they only
/// have a source path -- so they guard the whole manifest with this workspace-wide digest and fail
/// closed on any difference. Over-invalidating there is cheap: discarding the manifest only gives
/// up the "the whole project is already up to date, skip the DAG" shortcut, after which
/// `build_project_modules_native` re-elaborates exactly the modules whose
/// [`compute_module_cas_key`] moved. Under-invalidating is not: it serves `.olean` files elaborated
/// against input bytes that no longer exist, under a fresh action key.
///
/// Dependency packages are in scope because a dependency's `input_dir` is read while *its* modules
/// elaborate, and those modules are split, sharded and cached by the same machinery as the root's.
///
/// Empty when no package in the workspace declares inputs, so a manifest written before this field
/// existed stays valid for every input-free project (its recorded digest defaults to the empty
/// string) and every such project's keys stay byte-identical.
///
/// An input whose declaration this parser could not read like Lake
/// ([`InputTargetConfig::unsupported`]) fails closed (`Err`) rather than emitting a constant
/// placeholder string: any deterministic string would compare equal across two runs with different
/// underlying input bytes, turning cache consumers and manifest guards into false-green hits.
pub(crate) fn workspace_lake_inputs_digest(cfg: &ProjectConfig) -> Result<String> {
    validate_materialized_artifacts(cfg)?;
    let mut out = String::new();
    if std::iter::once(&cfg.root_pkg)
        .chain(&cfg.dep_pkgs)
        .any(|p| !p.custom_targets.is_empty() || !p.extern_libs.is_empty())
    {
        out.push_str(&format!("native:{}\n", cfg.canonical_config_digest));
    }
    for p in std::iter::once(&cfg.root_pkg)
        .chain(cfg.dep_pkgs.iter())
        .filter(|p| !p.inputs.is_empty())
    {
        for i in &p.inputs {
            if let Some(ref why) = i.unsupported {
                anyhow::bail!(
                    "Unsupported Lake input `{}/{}`: {}: fail-closed static Lake config gate",
                    p.name,
                    i.name,
                    why
                );
            }
            out.push_str(&format!("{}/{}:{}\n", p.name, i.name, i.blake3));
        }
    }
    Ok(out)
}

pub(super) fn validate_materialized_artifacts(cfg: &ProjectConfig) -> Result<()> {
    for pkg in std::iter::once(&cfg.root_pkg).chain(&cfg.dep_pkgs) {
        for name in required_lake_recipe_names(&cfg.root_pkg.pkg_root, pkg, cfg.is_untrusted) {
            anyhow::ensure!(
                pkg.inputs.iter().any(|i| i.name == name),
                "Lake recipe `{}/{name}` has not been materialized",
                pkg.name
            );
        }
        for ext in &pkg.extern_libs {
            let path = ext
                .static_artifact_path
                .as_ref()
                .with_context(|| format!("Missing native archive `{}/{}`", pkg.name, ext.name))?;
            let digest = blake3::hash(&fs::read(path)?).to_hex().to_string();
            anyhow::ensure!(
                ext.static_artifact_blake3.as_ref() == Some(&digest),
                "Materialized Lake artifact `{}/{}` changed during build",
                pkg.name,
                ext.name
            );
        }
        for input in &pkg.inputs {
            if pkg.custom_targets.contains(&input.name)
                || pkg.extern_libs.iter().any(|e| e.name == input.name)
            {
                let (digest, _) = hash_input_target(&pkg.pkg_root, input)?;
                anyhow::ensure!(
                    digest == input.blake3,
                    "Materialized Lake artifact `{}/{}` changed during build",
                    pkg.name,
                    input.name
                );
            }
        }
    }
    Ok(())
}

/// Every Lake config file a workspace resolve would read: the root package's, plus one per
/// dependency package [`resolve_project_config_with_trust`] would adopt.
///
/// Derived from the same manifest and resolver logic rather than from `.lake/packages/*`, because
/// four manifest fields move a package's config somewhere else entirely -- `packagesDir`, a
/// package's `subDir`, a `type: path` dependency's `dir`, and a `configFile` that is not
/// `lakefile` -- and a dependency config this list misses is a dependency whose `input_dir`
/// reaches no cache key at all: invisible to [`project_lake_inputs_tag`] and to
/// `lake_build::update_with_lake_input_digests`, so an edit under it is served the old bytes.
///
/// Over-approximates where that is the cheaper side: it enumerates the `packagesDir` directories
/// even when a manifest pins the package list, and lists candidates the resolve may discard. A
/// candidate that declares no input costs one `read_to_string`; a candidate that declares one but
/// is not adopted costs a resolve whose digest simply will not mention it.
///
/// `Err` is the fail-closed answer, and every caller reads it as "may declare inputs": a manifest
/// or a `configFile` that will not parse leaves the dependency set unknown, and the alternative --
/// reporting the default `.lake/packages` layout for a workspace whose real layout nobody could
/// read -- is exactly the silent stale hit this guards. Every `Err` here is one
/// `resolve_project_config` raises too, so no workspace that resolves today starts failing.
pub(crate) fn workspace_lake_config_candidates(project_dir: &Path) -> Result<Vec<PathBuf>> {
    let mut out: Vec<PathBuf> = Vec::new();
    let root_config = package_config_path(project_dir, None)?;
    out.extend(root_config.clone());
    // `is_untrusted = false`: this enumerates candidates to byte-scan, it does not adopt a
    // package. The trust gate stays in `resolve_project_config_with_trust`, which rejects an
    // out-of-workspace dependency before reading anything out of it.
    let (manifest_pkgs_dir, manifest_packages, manifest_hash) =
        parse_lake_manifest(project_dir, false)?;
    for mp in &manifest_packages {
        out.extend(package_config_path(&mp.dir, mp.config_file.as_deref())?);
    }
    let mut pkgs_dirs: Vec<PathBuf> = vec![manifest_pkgs_dir];
    if manifest_hash.is_none() {
        // The resolver's no-manifest path enumerates the root package's `packagesDir` as well.
        // That field only exists inside the root config, so learning a custom value needs the
        // root parse -- paid for only when the config names the field at all, and `is_root_pkg
        // = false` so an unsupported field elsewhere in the config is recorded rather than
        // turning every such project into one that "may declare inputs".
        if root_config
            .as_ref()
            .is_some_and(|p| fs::read_to_string(p).is_ok_and(|s| s.contains("packagesDir")))
        {
            pkgs_dirs.push(resolve_package_config(project_dir, false)?.packages_dir);
        }
    }
    for pkgs_rel in pkgs_dirs {
        let Ok(entries) = fs::read_dir(project_dir.join(pkgs_rel)) else {
            continue;
        };
        let mut dirs: Vec<PathBuf> = entries
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.is_dir())
            .collect();
        dirs.sort();
        for d in dirs {
            out.extend(package_config_path(&d, None)?);
        }
    }
    out.sort();
    out.dedup();
    Ok(out)
}

/// Cheap "could this workspace declare Lake file inputs at all?" test: a byte scan of every Lake
/// config [`workspace_lake_config_candidates`] names for `input_file` / `input_dir`.
///
/// Every project that declares none -- which is every project but the one this feature exists for
/// -- answers `false` here and never pays for a config resolve, so the hot per-file key paths that
/// consult [`project_lake_inputs_tag`] stay cheap. It can only over-approximate (the words also
/// appear in comments and strings), never under-approximate: a package that really declares an
/// input necessarily contains the word that declares it, in a file this candidate list names.
pub(crate) fn workspace_may_declare_lake_inputs(project_dir: &Path) -> bool {
    match workspace_lake_config_candidates(project_dir) {
        Ok(candidates) => candidates.iter().any(|p| {
            fs::read_to_string(p).is_ok_and(|s| {
                ["input_file", "input_dir", "extern_lib", "target "]
                    .iter()
                    .any(|needle| s.contains(needle))
            })
        }),
        Err(_) => true,
    }
}
