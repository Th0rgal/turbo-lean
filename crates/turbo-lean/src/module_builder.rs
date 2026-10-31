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
#[inline]
fn is_lean_letter_like(c: char) -> bool {
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
fn is_lean_subscript_alnum(c: char) -> bool {
    let v = c as u32;
    (0x2080..=0x2089).contains(&v)
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
        || v == 0x2c7c
}

#[inline]
fn is_lean_id_first(c: char) -> bool {
    c.is_alphabetic() || c == '_' || is_lean_letter_like(c)
}

#[inline]
fn is_lean_id_rest(c: char) -> bool {
    c.is_alphanumeric()
        || (c != '.'
            && c != '\n'
            && c != ' '
            && (c == '_'
                || c == '\''
                || c == '!'
                || c == '?'
                || is_lean_letter_like(c)
                || is_lean_subscript_alnum(c)))
}

#[inline]
fn is_lean_header_ws(c: char) -> bool {
    c == ' ' || c == '\r' || c == '\n'
}

fn skip_parse_imports_whitespace(src: &str, mut pos: usize) -> std::result::Result<usize, String> {
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

fn match_parse_imports_keyword(
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
fn lean_name_part_needs_no_escape(part: &str) -> bool {
    let mut chars = part.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    is_lean_id_first(first) && chars.all(is_lean_id_rest)
}

#[inline]
fn format_lean_name_part(raw_part: &str) -> String {
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

/// Format raw filesystem path components into a round-trippable `Lean.Name.toString` module name.
pub fn format_lean_module_name_from_parts<'a, I: IntoIterator<Item = &'a str>>(parts: I) -> String {
    parts
        .into_iter()
        .filter(|p| !p.is_empty())
        .map(format_lean_name_part)
        .collect::<Vec<_>>()
        .join(".")
}

fn parse_module_ident_at(
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

fn read_le_u64_at(bytes: &[u8], off: usize) -> Option<u64> {
    let slice = bytes.get(off..off.checked_add(8)?)?;
    Some(u64::from_le_bytes(slice.try_into().ok()?))
}

fn read_olean_name_at(bytes: &[u8], base_addr: u64, mut ptr: u64) -> Option<String> {
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

fn path_has_elan_bin_component(p: &Path) -> bool {
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
        if path_has_elan_bin_component(&canon) {
            return true;
        }
    }
    path_has_elan_bin_component(path)
}

fn is_toolchain_eligible_for_fleet_fallback(toolchain: &str) -> bool {
    let trimmed = toolchain.trim();
    if trimmed.is_empty() || trimmed == "unknown" {
        return true;
    }
    if std::env::var("TURBO_LEAN_ALLOW_TOOLCHAIN_FALLBACK")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false)
    {
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
    for sys_elan in [
        "/root/.elan",
        "/var/lib/sandboxed-node/.elan",
        "/var/lib/sandboxed-node/caches/elan",
    ] {
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
    for root in &elan_roots {
        let exact_tc = root.join("toolchains").join(&tc_dir_name).join("bin/lean");
        if exact_tc.is_file() {
            candidate_bins.push(exact_tc);
        }
    }
    let strict_tc = is_untrusted
        || !is_toolchain_eligible_for_fleet_fallback(toolchain)
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
                    if !strict_tc
                        && has_specific_tc
                        && !path_has_toolchain_component(&cand, &tc_dir_name)
                    {
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
    if !used_fallback_tc
        && has_specific_tc
        && !path_has_toolchain_component(&canon_bin, &tc_dir_name)
    {
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
use crate::shm_cache::strip_toml_comment;
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
/// One `leanOptions` entry of a lakefile.toml. Keys must be bare dotted names (TOML reads a
/// quoted `"a.b"` as one component, Lake as `«a.b»`). A string value that `-D`/setup.json would
/// re-read as a bool or a number fails closed (Lake keeps it a string); bare values must be a
/// bool or a canonical natural number.
fn toml_lean_option(k: &str, v: &str) -> Result<(String, String)> {
    let k = k.trim();
    // A quoted key without a dot is the same name as the bare key.
    let k = k
        .strip_prefix('"')
        .and_then(|k| k.strip_suffix('"'))
        .filter(|k| !k.contains('.'))
        .unwrap_or(k);
    if k.is_empty()
        || !k
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.'))
    {
        anyhow::bail!("Unsupported `leanOptions` key `{}` in lakefile.toml", k);
    }
    let v = v.trim();
    let value = if v.starts_with('"') || v.starts_with('\'') {
        let s = parse_toml_string(v)?;
        if matches!(s.as_str(), "true" | "false") || s.parse::<u64>().is_ok() || s.is_empty() {
            anyhow::bail!(
                "Unsupported `leanOptions` string value `{}` for `{}` in lakefile.toml",
                v,
                k
            );
        }
        s
    } else if matches!(v, "true" | "false") || is_canonical_nat(v) {
        v.to_string()
    } else {
        anyhow::bail!(
            "Unsupported `leanOptions` value `{}` for `{}` in lakefile.toml",
            v,
            k
        );
    };
    Ok((k.to_string(), value))
}

/// A `leanOptions = { ... }` inline table of a lakefile.toml.
fn parse_toml_lean_options_table(val: &str) -> Result<BTreeMap<String, String>> {
    let s = val.trim();
    if !s.starts_with('{') || !s.ends_with('}') {
        anyhow::bail!("Expected TOML inline table `{{...}}`, found `{}`", val);
    }
    let mut map = BTreeMap::new();
    for entry in split_top_level_comma(&s[1..s.len() - 1])? {
        let Some((k, v)) = entry.split_once('=') else {
            anyhow::bail!("Invalid inline table entry `{}`", entry);
        };
        let (k, v) = toml_lean_option(k, v)?;
        map.insert(k, v);
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
    // The line-based reader below does not model multi-line TOML strings.
    if raw.contains("\"\"\"") || raw.contains("'''") {
        anyhow::bail!(
            "Unsupported multi-line string in {}: fail-closed static Lake config gate",
            toml_path.display()
        );
    }
    let raw_hash = blake3::hash(raw.as_bytes()).to_hex().to_string();
    let mut empty_roots: BTreeSet<usize> = BTreeSet::new();
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
                let (k, v) = toml_lean_option(k, v)?;
                map.insert(k, v);
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
                    | "testDriverArgs" | "lintDriver" | "lintDriverArgs" | "releaseRepo"
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
                        let tbl = parse_toml_lean_options_table(&val_accum)?;
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
                        if lib.roots.is_empty() {
                            empty_roots.insert(i);
                        }
                    }
                    "globs" => lib.globs = nonempty(parse_toml_globs(&val_accum)?, "globs")?,
                    "moreLeanArgs" => lib.more_lean_args = parse_toml_string_array(&val_accum)?,
                    "weakLeanArgs" => lib.weak_lean_args = parse_toml_string_array(&val_accum)?,
                    "precompileModules" => {
                        lib.precompile_modules = Some(parse_toml_bool(&val_accum)?)
                    }
                    "leanOptions" => {
                        let tbl = parse_toml_lean_options_table(&val_accum)?;
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
                        let tbl = parse_toml_lean_options_table(&val_accum)?;
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
    check_empty_roots(&pkg, &empty_roots)?;
    finalize_package_config(&mut pkg, is_root_pkg, toml_path, &raw_hash, &empty_roots)?;
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

/// `defaultFacets := #[...]`: facet names are written bare (`LeanLib.staticFacet`) or as name
/// literals; root packages check them against an allowlist.
fn parse_lean_facet_array_expr(expr: &str) -> Result<Vec<String>> {
    let s = expr.trim();
    let s = s.strip_prefix('#').map_or(s, str::trim_start);
    if !s.starts_with('[')
        || !s.ends_with(']')
        || !matches!(lean_scan(&s[1..s.len() - 1], ""), Ok((_, 0)))
    {
        anyhow::bail!(
            "Unsupported `defaultFacets` expression `{}` in lakefile.lean",
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
            anyhow::bail!("Unsupported facet `{}` in `{}`", item, expr);
        }
        out.push(cleaned);
    }
    Ok(out)
}

/// A backtick name literal of plain dotted identifiers (or a `«...»` component of the
/// target-name alphabet), as its name string.
fn lake_name_literal(item: &str, context: &str) -> Result<String> {
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
/// An option name must be a name literal: one leading backtick, then `.`-separated plain
/// identifiers. Bare identifiers (`Name` values Lake would evaluate), guillemet-escaped
/// components (whose structure differs from the dotted reading) and operators are rejected.
fn lean_option_name_literal(raw: &str) -> Result<String> {
    let raw = raw.trim();
    let ident = |c: &str| {
        c.chars()
            .next()
            .is_some_and(|f| f.is_alphabetic() || f == '_')
            && c.chars()
                .all(|ch| ch.is_alphanumeric() || matches!(ch, '_' | '\'' | '!' | '?'))
    };
    match raw.strip_prefix('`') {
        Some(name) if name.split('.').all(ident) => Ok(name.to_string()),
        _ => anyhow::bail!(
            "Unsupported non-literal `leanOptions` name `{}` in lakefile.lean",
            raw
        ),
    }
}

/// `v` is exactly one `"..."` token: its first unescaped closing quote is its last character
/// (so `"a" ++ "b"` is rejected).
fn is_single_string_literal(v: &str) -> bool {
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
fn is_canonical_nat(v: &str) -> bool {
    !v.is_empty()
        && v.bytes().all(|c| c.is_ascii_digit())
        && (v == "0" || !v.starts_with('0'))
        && v.parse::<u64>().is_ok()
}

/// The value of `t` if it is exactly one `"..."` token using only escapes that Lean and the
/// TOML decoder read identically.
fn plain_string_literal(t: &str) -> Result<String> {
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
fn lean_option_literal(raw: &str, key: &str) -> Result<String> {
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
        return Ok(b.to_string());
    }
    if let Some(n) = lit("LeanOptionValue.ofNat ", ".ofNat ", |v| is_canonical_nat(v)) {
        return Ok(n.to_string());
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
        {
            return Ok(v);
        }
    }
    anyhow::bail!(
        "Unsupported non-literal `leanOptions` value `{}` for `{}`",
        raw,
        key
    )
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
    let (pairs, open) = lean_scan(inner, ",")?;
    if open != 0 {
        anyhow::bail!("Unclosed bracket in `leanOptions` expression `{}`", expr);
    }
    let pairs: Vec<String> = pairs.into_iter().filter(|p| !p.is_empty()).collect();
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
            let k = lean_option_name_literal(k_raw)?;
            let v = lean_option_literal(v_raw, &k)?;
            map.insert(k, v);
        } else if let Some(rest) = p.trim().strip_prefix("LeanOption.mk ") {
            let Some((k_raw, v_raw)) = rest.trim().split_once(char::is_whitespace) else {
                anyhow::bail!("Unsupported `leanOptions` entry `{}` in lakefile.lean", p);
            };
            let v_raw = v_raw.trim();
            let v_raw = v_raw
                .strip_prefix('(')
                .and_then(|r| r.strip_suffix(')'))
                .filter(|inner| lean_scan(inner, "").is_ok_and(|(_, d)| d == 0))
                .unwrap_or(v_raw);
            let k = lean_option_name_literal(k_raw)?;
            let v = lean_option_literal(v_raw, &k)?;
            map.insert(k, v);
        } else {
            anyhow::bail!("Unsupported `leanOptions` entry `{}` in lakefile.lean", p);
        }
    }
    Ok(map)
}

/// Maximum identifier indirection depth when resolving `leanOptions` expressions.
const LEAN_OPTIONS_MAX_DEPTH: usize = 16;

/// Lean-aware lexical scan of `s`: `"..."` strings (with `\` escapes) and char literals are
/// opaque, a `'` after an identifier character is a prime, and `()[]{}⟨⟩` must nest correctly.
/// Splits on `sep` at depth 0 (`sep` empty: no splitting) and returns the trimmed pieces plus
/// the final open-bracket depth.
fn lean_scan(s: &str, sep: &str) -> Result<(Vec<String>, usize)> {
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
struct LakefileBindings {
    /// name -> (body, first line, last line) of the declaration (1-based, comment-stripped).
    defs: BTreeMap<String, (String, usize, usize)>,
    rejected: std::collections::BTreeSet<String>,
    /// The lakefile is not plain (`lakefile_is_plain`): scopes, `where`, `open` or notation could
    /// change what an option expression denotes (even a literal one), so none is resolved.
    scoped: bool,
}

/// Column-0 commands a "plain" Lake configuration may contain for its identifiers to be
/// resolved statically (Lake's own DSL plus option bindings; `post_update` hooks are blocks).
const PLAIN_LAKEFILE_COMMANDS: [&str; 8] = [
    "import ",
    "require ",
    "package ",
    "lean_lib ",
    "lean_exe ",
    "abbrev ",
    "def ",
    "post_update ",
];

/// Keywords that can introduce, scope or shadow bindings (declarations, scopes, `where`,
/// notation, `open`, modifiers, ...); see `lakefile_is_plain` for where they may appear.
const BINDING_COMMANDS: [&str; 61] = [
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
fn lakefile_lexical_guard(
    src: &str,
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
        if c == ';' {
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
            let head = pre.trim_end();
            let head = head
                .strip_prefix("@[default_target]")
                .map_or(head, str::trim_start);
            let in_name_literal = matches!(prev, Some('`' | '.'));
            if !in_name_literal
                && (!matches!(head, "package" | "lean_lib" | "lean_exe" | "require")
                    || !pre.ends_with(char::is_whitespace))
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
                if !(d.is_ascii_alphanumeric() || matches!(d, '_' | '-')) {
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
fn lean_tokens_by_line(src: &str) -> Vec<Vec<&str>> {
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
fn lakefile_is_plain(clean: &str) -> bool {
    let tokens_by_line = lean_tokens_by_line(clean);
    clean.lines().zip(tokens_by_line).all(|(line, tokens)| {
        let t = line.trim();
        if t.is_empty() {
            return tokens.is_empty();
        }
        let indented = line.starts_with(char::is_whitespace);
        let header = matches!(tokens.first(), Some(&("package" | "lean_lib" | "lean_exe")));
        let open_line = matches!(t, "open Lake DSL" | "open System Lake DSL" | "open Lake");
        let keywords_ok = tokens.iter().enumerate().all(|(i, tok)| {
            !(BINDING_COMMANDS.contains(tok) || tok.starts_with('#'))
                || (i == 0
                    && !indented
                    && matches!(
                        *tok,
                        "abbrev"
                            | "def"
                            | "package"
                            | "lean_lib"
                            | "lean_exe"
                            | "require"
                            | "post_update"
                    ))
                || (i == 0 && *tok == "open" && open_line)
                || (*tok == "where" && header && i + 1 == tokens.len())
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
            || t.starts_with([']', ')', '}', '⟩'])
            || t.starts_with("++")
    })
}

/// A body runs from `:=` until the next column-0 line once all brackets are closed; column-0
/// lines that close a bracket or continue with `++` still belong to it.
fn collect_lakefile_abbrevs(clean: &str) -> LakefileBindings {
    let mut out = LakefileBindings {
        scoped: !lakefile_is_plain(clean),
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
        let Some(rest) = decl
            .strip_prefix("abbrev ")
            .or_else(|| decl.strip_prefix("def "))
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
            let continues = nt.starts_with([']', ')', '}', '⟩']) || nt.starts_with("++");
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
        if dotted
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
            if let Some(last) = name.rsplit('.').next().filter(|_| dotted) {
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

fn is_lake_ident(s: &str) -> bool {
    s.chars()
        .next()
        .is_some_and(|c| c.is_alphabetic() || c == '_')
        && s.chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '.' || c == '\'')
}

/// Recognise `IDENT.map fun s ↦ { s with name := `weak ++ s.name }` (also `=>`), Mathlib's
/// idiom for passing options as `weak.`-prefixed, and return `IDENT`.
fn parse_weak_prefix_map(expr: &str) -> Option<String> {
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
fn resolve_lean_options_expr(
    expr: &str,
    bindings: &LakefileBindings,
    line: usize,
) -> Result<BTreeMap<String, String>> {
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
struct BindingCache {
    done: BTreeMap<String, BTreeMap<String, String>>,
    visiting: std::collections::BTreeSet<String>,
}

fn resolve_lean_options_in(
    expr: &str,
    bindings: &LakefileBindings,
    line: usize,
    depth: usize,
    cache: &mut BindingCache,
) -> Result<BTreeMap<String, String>> {
    if depth > LEAN_OPTIONS_MAX_DEPTH {
        anyhow::bail!(
            "`leanOptions` expression `{}` nests deeper than {} in lakefile.lean",
            expr,
            LEAN_OPTIONS_MAX_DEPTH
        );
    }
    let (parts, _) = lean_scan(expr, "++")?;
    if parts.len() > 1 {
        let mut map = BTreeMap::new();
        for part in &parts {
            // Pieces are strictly smaller, so `++` does not count towards the depth bound.
            map.extend(resolve_lean_options_in(part, bindings, line, depth, cache)?);
        }
        return Ok(map);
    }
    let s = expr.trim();
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
                    .map(|(k, v)| (format!("weak.{k}"), v))
                    .collect()
            } else {
                map
            });
        }
    }
    parse_lean_options_expr(s)
}
fn parse_lean_path_literal(expr: &str) -> Result<PathBuf> {
    // Only a string literal: `FilePath.mk "..."` can be shadowed by the lakefile itself.
    let s = expr.trim();
    if s.starts_with('"') {
        return Ok(PathBuf::from(plain_string_literal(s)?));
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
    let (guarded, flat, multiline_lines) = lakefile_lexical_guard(&raw).map_err(|e| {
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
    let lean_option_bindings = collect_lakefile_abbrevs(&clean);
    // In a non-plain lakefile a `leanOptions` field can hide behind `;`, `where` or notation,
    // so its mere presence fails closed (rather than parsing to fewer options than Lake sets).
    if lean_option_bindings.scoped
        && lean_tokens_by_line(&clean).iter().any(|l| {
            l.iter()
                .any(|t| matches!(*t, "leanOptions" | "moreLeanArgs" | "weakLeanArgs"))
        })
    {
        anyhow::bail!(
            "Unsupported `leanOptions` in {}: lakefile.lean is not plain (scopes, where, open, `;`, notation or metaprogramming)",
            lean_path.display()
        );
    }
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
        // A target declared on an indented line would be skipped below; Lake reads it.
        if indent > 0
            && trimmed.split_whitespace().next().is_some_and(|w| {
                matches!(
                    w,
                    "package" | "lean_lib" | "lean_exe" | "target" | "extern_lib" | "require"
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
        // Lake continues a field's expression on a column-0 `++` or closing-bracket line; the
        // field reader above stops at column 0, so such a line fails closed.
        if indent == 0
            && matches!(
                current_block,
                DeclBlock::Package | DeclBlock::LeanLib(_) | DeclBlock::LeanExe(_)
            )
            && (trimmed.starts_with("++") || trimmed.starts_with([']', ')', '}', '⟩']))
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
            // `@[test_driver]` / `@[lint_driver]` mark a target like `@[default_target]` does,
            // without making it a default target.
            let (attr, is_default) = if trimmed.starts_with("@[default_target]") {
                ("@[default_target]", true)
            } else if trimmed.starts_with("@[test_driver]") {
                ("@[test_driver]", false)
            } else if trimmed.starts_with("@[lint_driver]") {
                ("@[lint_driver]", false)
            } else {
                ("", false)
            };
            if !attr.is_empty() {
                pending_default_target = is_default;
                let after = trimmed.strip_prefix(attr).unwrap_or("").trim();
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
                // `toLeanConfig := { ... }` / `toLeanConfig.leanOptions := ...` set the same
                // options through the parent structure; never skip them silently.
                if key.starts_with("to") && key[2..].starts_with(|c: char| c.is_ascii_uppercase())
                    || key.contains('.')
                    || matches!(key, "dynlibs" | "plugins")
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
                    let continues = next_indent > indent
                        || (next_indent == indent
                            && (next_t.starts_with("++")
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
                            pkg.lean_options.extend(resolve_lean_options_expr(
                                &val_accum,
                                &lean_option_bindings,
                                line_no,
                            )?);
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
                            "roots" => {
                                lib.roots = parse_lean_ident_array_expr(&val_accum)?;
                                if lib.roots.is_empty() {
                                    empty_roots.insert(lib_idx);
                                }
                            }
                            "globs" => {
                                lib.globs = nonempty(parse_lean_globs_expr(&val_accum)?, "globs")?
                            }
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
                                lib.lean_options.extend(resolve_lean_options_expr(
                                    &val_accum,
                                    &lean_option_bindings,
                                    line_no,
                                )?);
                            }
                            "defaultFacets" => {
                                let facets = parse_lean_facet_array_expr(&val_accum)?;
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
                            "root" => exe.root = lake_name_literal(&val_accum, "root")?,
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
                                exe.lean_options.extend(resolve_lean_options_expr(
                                    &val_accum,
                                    &lean_option_bindings,
                                    line_no,
                                )?);
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
    check_empty_roots(&pkg, &empty_roots)?;
    finalize_package_config(&mut pkg, is_root_pkg, lean_path, &raw_hash, &empty_roots)?;
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
    // Lake also accepts `{ field := ... }` and `:=` after a target name; only `where` blocks are
    // parsed here, so anything else after the name fails closed.
    for kw in ["package", "lean_lib", "lean_exe"] {
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
                    let n = n
                        .strip_prefix('«')
                        .and_then(|n| n.strip_suffix('»'))
                        .or_else(|| n.strip_prefix('"').and_then(|n| n.strip_suffix('"')))
                        .unwrap_or(n);
                    n.split('.').all(|seg| {
                        !seg.is_empty()
                            && seg
                                .chars()
                                .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '\''))
                    })
                });
            if !name_ok || !matches!((words.next(), words.next()), (None | Some("where"), None)) {
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
/// Option keys a package may set (with or without the `weak.` prefix), via `leanOptions` or
/// `-D` flags. An allowlist, so no lakefile, however it is parsed, can reach options that weaken
/// checking (`debug.skipKernelTC`, `debug.*AsSorry`), run programs (`sat.solver`) or write
/// files (`trace.profiler.output`). `warn.sorry` may only be `true` and `debug.skipKernelTC`
/// only `false`; both are forced on every compile anyway.
fn is_allowed_lean_option(key: &str, value: &str) -> bool {
    // Not `pp.*` in general: `pp.all`, `pp.raw`, `pp.maxSteps`, ... change how the
    // `declaration uses 'sorry'` warning prints.
    const PREFIXES: [&str; 3] = ["linter.", "backward.", "experimental."];
    const KEYS: [&str; 11] = [
        "pp.unicode.fun",
        "pp.mvars.anonymous",
        "autoImplicit",
        "relaxedAutoImplicit",
        "maxHeartbeats",
        "maxRecDepth",
        "maxSynthPendingDepth",
        "synthInstance.maxHeartbeats",
        "synthInstance.maxSize",
        "warningAsError",
        "exponentiation.threshold",
    ];
    match key {
        "warn.sorry" => value == "true",
        "debug.skipKernelTC" => value == "false",
        _ => KEYS.contains(&key) || PREFIXES.iter().any(|p| key.starts_with(p)),
    }
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
        if k.is_empty()
            || v.is_empty()
            || !is_allowed_lean_option(k.strip_prefix("weak.").unwrap_or(k), v)
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

/// Canonical digest of filtered effective Lean compiler flags. Returns `None` when empty
/// so cache/CAS keys remain byte-identical for projects with no configured options.
pub fn compute_lean_args_digest(args: &[String]) -> Option<String> {
    let filtered = filter_allowed_lean_args(args);
    if filtered.is_empty() {
        return None;
    }
    let mut h = blake3::Hasher::new();
    h.update(b"lean-args-v1:");
    for (idx, a) in filtered.iter().enumerate() {
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
    filter_allowed_lean_args(weak_args.iter().chain(strong_args))
}

/// Resolve filtered package-level Lean compiler flags from `pkg`.
pub fn package_default_lean_args(pkg: &PackageConfig) -> Vec<String> {
    let (strong, weak) = compose_effective_args(pkg, &BTreeMap::new(), &[], &[]);
    compose_flat_filtered_args(&weak, &strong)
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
                return compose_flat_filtered_args(&spec.weak_args, &spec.strong_args);
            }
        }
    }
    package_default_lean_args(pkg)
}

/// Best-effort static lookup of filtered Lake compiler flags for `project_dir` (and optional `file_path`).
/// Returns an empty `Vec` if `project_dir` has no Lake config or fails static parsing.
pub fn try_resolve_lean_args_for_path(project_dir: &Path, file_path: Option<&Path>) -> Vec<String> {
    if !project_dir.join("lakefile.toml").is_file() && !project_dir.join("lakefile.lean").is_file()
    {
        return Vec::new();
    }
    let Ok(pkg) = resolve_package_config(project_dir, false) else {
        return Vec::new();
    };
    match file_path {
        Some(fp) => resolve_file_lean_args_in_package(&pkg, fp),
        None => package_default_lean_args(&pkg),
    }
}

/// An explicit empty `globs` selects no modules in Lake, but an empty list here means "use the
/// default", so it fails closed.
fn nonempty<T>(v: Vec<T>, field: &str) -> Result<Vec<T>> {
    if v.is_empty() {
        anyhow::bail!("Unsupported empty `{}` (selects no modules in Lake)", field);
    }
    Ok(v)
}

/// `roots = []` is fine next to explicit `globs` (Lake builds the globs); without them Lake
/// selects no modules while the defaults here would pick the library name, so it fails closed.
fn check_empty_roots(pkg: &PackageConfig, empty_roots: &BTreeSet<usize>) -> Result<()> {
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

fn finalize_package_config(
    pkg: &mut PackageConfig,
    is_root_pkg: bool,
    config_path: &Path,
    raw_hash: &str,
    explicit_empty_roots: &BTreeSet<usize>,
) -> Result<()> {
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
    // `leanOptions` reach Lean as `-Dk=v`, so they pass the same gate as explicit flags
    // (e.g. `warn.sorry=false` and malformed keys are rejected).
    let as_flags = |opts: &BTreeMap<String, String>| -> Vec<String> {
        opts.iter().map(|(k, v)| format!("-D{k}={v}")).collect()
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
        check_allowed_args(&as_flags(opts), &format!("{scope}.leanOptions"))?;
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
pub(crate) struct DiscoveredModuleSpec {
    module_name: String,
    pkg_name: String,
    target_name: String,
    is_root_pkg: bool,
    pkg_root: PathBuf,
    src_root: PathBuf,
    pub(crate) src_path: PathBuf,
    build_lib_lean_dir: PathBuf,
    build_ir_dir: PathBuf,
    precompile_modules: bool,
    is_exe_target: bool,
    strong_args: Vec<String>,
    weak_args: Vec<String>,
    extern_lib_digests: Vec<String>,
    pub(crate) pkg_config_digest: String,
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
    for a in &pkg.more_lean_args {
        strong.push(a.clone());
    }
    for a in target_more_args {
        strong.push(a.clone());
    }
    // Lake passes `leanOptions` in setup.json, which overrides `-D` flags on the command line,
    // so they come last: the setup built from these args keeps Lake's precedence
    // (leanOptions > moreLeanArgs > weakLeanArgs).
    for (k, v) in &merged_opts {
        strong.push(format!("-D{}={}", k, v));
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
                        let mod_name = format_lean_module_name_from_parts(
                            rel.with_extension("")
                                .components()
                                .filter_map(|c| c.as_os_str().to_str()),
                        );
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
            let rel_slash = module_name_to_rel_slash(prefix);
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
                        let mod_name = format_lean_module_name_from_parts(
                            rel.with_extension("")
                                .components()
                                .filter_map(|c| c.as_os_str().to_str()),
                        );
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
pub(crate) fn resolve_module_in_package(
    pkg: &PackageConfig,
    is_root_pkg: bool,
    mod_name: &str,
) -> Option<DiscoveredModuleSpec> {
    let rel_slash = module_name_to_rel_slash(mod_name);
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
    // 1. An executable whose root is the module (Lake checks executables first, last one
    //    first like `findSomeRev?`).
    for exe in pkg.exes.iter().rev() {
        if exe.root == mod_name {
            let exe_src = match &exe.src_dir {
                Some(sd) => pkg_src_base.join(sd),
                None => pkg_src_base.clone(),
            };
            let exe_rel = module_name_to_rel_slash(&exe.root);
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
    // 2. Like Lake's `findTargetModule?`: the last library that can build the module, i.e.
    //    one of its globs matches it or it lies under one of its roots.
    for lib in pkg.libs.iter().rev() {
        let lib_src = match &lib.src_dir {
            Some(sd) => pkg_src_base.join(sd),
            None => pkg_src_base.clone(),
        };
        // Lake's `isBuildableModule`: a glob matches the module, or the module lies under a
        // root that one of the globs selects.
        let under = |m: &str, p: &str| m.starts_with(&format!("{}.", p));
        let matches = |m: &str| {
            lib.globs.iter().any(|g| match g {
                GlobSpec::One(x) => m == x,
                GlobSpec::Submodules(p) => under(m, p),
                GlobSpec::AndSubmodules(p) => m == p || under(m, p),
            })
        };
        let buildable = matches(mod_name)
            || lib
                .roots
                .iter()
                .any(|r| (mod_name == r || under(mod_name, r)) && matches(r));
        if buildable {
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
    // 3. A package without targets: its source directory (Lake has no target to ask).
    let cand = pkg_src_base.join(format!("{}.lean", rel_slash));
    if pkg.libs.is_empty() && pkg.exes.is_empty() && cand.is_file() {
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
pub(crate) fn is_builtin_toolchain_module(toolchain_lib_lean: &Path, mod_name: &str) -> bool {
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
    let rel_slash = module_name_to_rel_slash(mod_name);
    toolchain_lib_lean
        .join(format!("{}.olean", rel_slash))
        .is_file()
}
#[derive(Debug, Clone, Serialize, Deserialize, Default, PartialEq, Eq)]
pub(crate) struct VerifiedDepModuleEntry {
    pub src_blake3: String,
    pub olean_artifact_digest: String,
    #[serde(default)]
    pub kernel_audited: bool,
    /// Artifact-set digests of the direct imports this `.olean` was elaborated against.
    /// Deliberately not `#[serde(default)]`: legacy entries without it fail closed.
    pub import_olean_digests: BTreeMap<String, String>,
    /// `olean_artifact_stat_fingerprint` when recorded (empty: always re-hash on use).
    #[serde(default)]
    pub artifact_stat_fingerprint: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub(crate) struct VerifiedDepManifest {
    pub pkg_name: String,
    pub toolchain: String,
    pub lean_githash: String,
    pub pkg_config_digest: String,
    #[serde(default)]
    pub allowed_axioms: Vec<String>,
    pub modules: BTreeMap<String, VerifiedDepModuleEntry>,
    /// Workspace configuration the manifest was validated against on load (never serialized).
    #[serde(skip)]
    pub cfg: Option<ProjectConfig>,
    /// Dependency-closure nodes `(package, module, pin)` already found consistent (never
    /// serialized).
    #[serde(skip)]
    pub dep_import_memo: DepImportMemo,
}

#[derive(Debug, Default)]
pub(crate) struct DepImportMemo(Mutex<HashSet<(String, String, String)>>);

impl Clone for DepImportMemo {
    fn clone(&self) -> Self {
        Self::default()
    }
}

/// Load `pkg_root`'s verified-sources manifest if it was written for this package, toolchain,
/// configuration, and axiom policy.
fn read_pkg_verified_manifest(
    cfg: &ProjectConfig,
    pkg_root: &Path,
    pkg_name: &str,
    pkg_config_digest: &str,
) -> Option<VerifiedDepManifest> {
    let bytes = fs::read(pkg_root.join(".lake/build/.turbo_verified_sources.json")).ok()?;
    let manifest: VerifiedDepManifest = serde_json::from_slice(&bytes).ok()?;
    (manifest.pkg_name == pkg_name
        && manifest.toolchain == cfg.toolchain
        && manifest.lean_githash == cfg.lean_githash
        && manifest.pkg_config_digest == pkg_config_digest
        && manifest.allowed_axioms == crate::splitter::allowed_axioms())
    .then_some(manifest)
}

/// Where a non-root-package import resolves, in `build_module_dag_with_trust` (trusted) order.
pub(crate) enum ImportSite {
    Module(Box<DiscoveredModuleSpec>),
    Toolchain,
    Prebuilt(PathBuf),
    Unresolved,
}

/// Caller `LEAN_PATH` directories searched for prebuilt external `.olean`s (trusted mode).
fn trusted_lean_path_dirs(cfg: &ProjectConfig) -> Vec<PathBuf> {
    std::env::var_os("LEAN_PATH")
        .map(|lp| {
            std::env::split_paths(&lp)
                .filter(|p| p.is_dir() && *p != cfg.toolchain_lib_lean)
                .collect()
        })
        .unwrap_or_default()
}

pub(crate) fn resolve_import_site(cfg: &ProjectConfig, imp: &str) -> ImportSite {
    let mut deps = cfg
        .dep_pkgs
        .iter()
        .filter_map(|dp| resolve_module_in_package(dp, false, imp));
    match (deps.next(), deps.next()) {
        (Some(spec), None) => return ImportSite::Module(Box::new(spec)),
        (Some(_), Some(_)) => return ImportSite::Unresolved,
        _ => {}
    }
    if is_builtin_toolchain_module(&cfg.toolchain_lib_lean, imp) {
        return ImportSite::Toolchain;
    }
    let rel = format!("{}.olean", module_name_to_rel_slash(imp));
    cfg.dep_pkgs
        .iter()
        .map(|dp| dp.pkg_root.join(&dp.build_dir).join(&dp.lean_lib_dir))
        .chain(trusted_lean_path_dirs(cfg))
        .map(|d| d.join(&rel))
        .find(|p| p.is_file())
        .map_or(ImportSite::Unresolved, ImportSite::Prebuilt)
}

fn spec_olean_path(spec: &DiscoveredModuleSpec) -> PathBuf {
    spec.build_lib_lean_dir.join(format!(
        "{}.olean",
        module_name_to_rel_slash(&spec.module_name)
    ))
}

fn spec_rel_src(spec: &DiscoveredModuleSpec) -> String {
    spec.src_path
        .strip_prefix(&spec.pkg_root)
        .unwrap_or(&spec.src_path)
        .to_string_lossy()
        .replace('\\', "/")
}

/// P0-4: whether `entry`'s `.olean` was elaborated against the current artifacts of its direct
/// imports. `pin_current(import, pin)` judges each import; only toolchain imports may be
/// unpinned, and every pin must name a current import.
pub(crate) fn verified_entry_imports_current(
    entry: &VerifiedDepModuleEntry,
    imports: &[String],
    mut pin_current: impl FnMut(&str, Option<&str>) -> bool,
) -> bool {
    entry
        .import_olean_digests
        .keys()
        .all(|k| imports.contains(k))
        && imports
            .iter()
            .all(|imp| pin_current(imp, entry.import_olean_digests.get(imp).map(String::as_str)))
}

/// Check-time judgement of a non-root-package import pinned at `pin` from the root package:
/// prebuilt `.olean`s are re-digested; dependency-package imports must have a consistent
/// closure (`dep_pkg_import_pins_consistent`), memoized per manifest load.
pub(crate) fn external_import_pin_current(
    cfg: &ProjectConfig,
    memo: &DepImportMemo,
    imp: &str,
    pin: Option<&str>,
) -> bool {
    match (resolve_import_site(cfg, imp), pin) {
        (ImportSite::Toolchain, None) => true,
        (ImportSite::Prebuilt(olean), Some(pin)) => olean_digest_is(cfg, &olean, pin),
        (ImportSite::Module(spec), Some(pin)) => {
            dep_pkg_import_pins_consistent(cfg, memo, *spec, pin)
        }
        _ => false,
    }
}

/// Whether `olean`'s artifact set digests to `pin`, hashed under the root worktree policy.
fn olean_digest_is(cfg: &ProjectConfig, olean: &Path, pin: &str) -> bool {
    let preserve = crate::lake_build::worktree_auto_link_disabled(&cfg.root_pkg.pkg_root);
    compute_olean_artifact_set_digest_with_policy(olean, preserve).is_ok_and(|d| d == pin)
}

/// Inode/size/mtime/ctime fingerprint of an `.olean` artifact set. Any rewrite, replacement,
/// or timestamp reset changes `ctime`, so an unchanged fingerprint implies unchanged bytes.
fn olean_artifact_stat_fingerprint(olean: &Path) -> Option<String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let mut h = blake3::Hasher::new();
        for (tag, path) in olean_artifact_paths(olean) {
            h.update(tag.as_bytes());
            match fs::metadata(&path) {
                Ok(m) => {
                    for v in [m.ino() as i64, m.len() as i64, m.mtime(), m.mtime_nsec()] {
                        h.update(&v.to_le_bytes());
                    }
                    h.update(&m.ctime().to_le_bytes());
                    h.update(&m.ctime_nsec().to_le_bytes());
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                    h.update(b"-");
                }
                Err(_) => return None,
            }
        }
        Some(h.finalize().to_hex().to_string())
    }
    #[cfg(not(unix))]
    {
        let _ = olean;
        None
    }
}

/// Whether the `.olean` artifact set at `olean` still matches `entry`: by its recorded stat
/// fingerprint, else by re-hashing.
pub(crate) fn entry_artifacts_current(
    cfg: &ProjectConfig,
    olean: &Path,
    entry: &VerifiedDepModuleEntry,
) -> bool {
    (!entry.artifact_stat_fingerprint.is_empty()
        && olean_artifact_stat_fingerprint(olean).as_deref()
            == Some(entry.artifact_stat_fingerprint.as_str()))
        || olean_digest_is(cfg, olean, &entry.olean_artifact_digest)
}

/// Whether dependency-package module `imp` has a verified-sources entry whose closure is no
/// longer consistent. Without an entry there is no turbo-lean evidence (Lake-managed): `false`.
pub(crate) fn dep_pkg_module_stale(cfg: &ProjectConfig, memo: &DepImportMemo, imp: &str) -> bool {
    let ImportSite::Module(spec) = resolve_import_site(cfg, imp) else {
        return false;
    };
    let Some(digest) =
        read_pkg_verified_manifest(cfg, &spec.pkg_root, &spec.pkg_name, &spec.pkg_config_digest)
            .and_then(|m| {
                m.modules
                    .get(&spec_rel_src(&spec))
                    .map(|e| e.olean_artifact_digest.clone())
            })
    else {
        return false;
    };
    !dep_pkg_import_pins_consistent(cfg, memo, *spec, &digest)
}

/// Check-time counterpart of `collect_fresh_dep_pkg_closure` for a dependency-package module
/// pinned at `pin` (memoizing verified nodes in `memo`): every visited module's artifacts must
/// match its manifest entry (by stat fingerprint, else by re-hashing), its source must match the
/// entry, and every import of that source must be pinned to the current artifacts (root- and
/// dependency-package modules recursively, root ones kernel-audited; prebuilt imports
/// re-digested).
fn dep_pkg_import_pins_consistent(
    cfg: &ProjectConfig,
    memo: &DepImportMemo,
    spec: DiscoveredModuleSpec,
    pin: &str,
) -> bool {
    let mut manifests: HashMap<PathBuf, Option<VerifiedDepManifest>> = HashMap::new();
    let mut seen: HashMap<(String, String), String> = HashMap::new();
    let mut stack = vec![(spec, pin.to_string())];
    while let Some((cur, pin)) = stack.pop() {
        let key = (cur.pkg_name.clone(), cur.module_name.clone());
        let memo_key = (key.0.clone(), key.1.clone(), pin.clone());
        if memo.0.lock().is_ok_and(|m| m.contains(&memo_key)) {
            continue;
        }
        if let Some(prev) = seen.get(&key) {
            if *prev != pin {
                return false;
            }
            continue;
        }
        let manifest = manifests.entry(cur.pkg_root.clone()).or_insert_with(|| {
            read_pkg_verified_manifest(cfg, &cur.pkg_root, &cur.pkg_name, &cur.pkg_config_digest)
        });
        let Some(entry) = manifest
            .as_ref()
            .and_then(|m| m.modules.get(&spec_rel_src(&cur)))
        else {
            return false;
        };
        let artifacts_ok = (!cur.is_root_pkg || entry.kernel_audited)
            && entry_artifacts_current(cfg, &spec_olean_path(&cur), entry);
        let Ok(src) = fs::read_to_string(&cur.src_path) else {
            return false;
        };
        let src_ok = blake3::hash(src.as_bytes()).to_hex().as_str() == entry.src_blake3;
        let hdr = parse_header_info(&src);
        let pins_ok = hdr.header_error.is_none()
            && verified_entry_imports_current(entry, &hdr.imports, |imp, sub_pin| {
                let site = match resolve_module_in_package(&cfg.root_pkg, true, imp) {
                    Some(root_spec) => ImportSite::Module(Box::new(root_spec)),
                    None => resolve_import_site(cfg, imp),
                };
                match (site, sub_pin) {
                    (ImportSite::Toolchain, None) => true,
                    (ImportSite::Prebuilt(o), Some(p)) => olean_digest_is(cfg, &o, p),
                    (ImportSite::Module(sub), Some(p)) => {
                        stack.push((*sub, p.to_string()));
                        true
                    }
                    _ => false,
                }
            });
        if !c_abi::verify_module_cache_key(
            true,
            true,
            src_ok,
            artifacts_ok && pins_ok && entry.olean_artifact_digest == pin,
            true,
        ) {
            return false;
        }
        seen.insert(key, pin);
    }
    if let Ok(mut m) = memo.0.lock() {
        m.extend(
            seen.into_iter()
                .map(|((pkg, module), pin)| (pkg, module, pin)),
        );
    }
    true
}

pub(crate) fn verify_module_lake_sidecars(
    olean_path: &Path,
    ir_dir_opt: Option<&Path>,
    rel_slash: &str,
    src_raw: &str,
    is_module: bool,
    needs_c: bool,
) -> Result<()> {
    let olean_h = verify_and_hash_artifact_bytes(olean_path, true, true)?;
    let ilean_path = olean_path.with_extension("ilean");
    let ilean_h = verify_and_hash_artifact_bytes(&ilean_path, true, true)?;
    let srv_path = PathBuf::from(format!("{}.server", olean_path.display()));
    let priv_path = PathBuf::from(format!("{}.private", olean_path.display()));
    let ir_path = olean_path.with_extension("ir");
    let ir_sig_path = PathBuf::from(format!("{}.sig", ir_path.display()));
    let mod_comp_hashes = if is_module {
        let srv_h = verify_and_hash_artifact_bytes(&srv_path, true, true)?;
        let priv_h = verify_and_hash_artifact_bytes(&priv_path, true, true)?;
        let ir_sig_h = verify_and_hash_artifact_bytes(&ir_sig_path, true, true)?;
        let ir_h = verify_and_hash_artifact_bytes(&ir_path, true, true)?;
        Some((srv_h, priv_h, ir_sig_h, ir_h))
    } else {
        None
    };
    let c_path_opt = ir_dir_opt.map(|d| d.join(format!("{}.c", rel_slash)));
    let c_h_opt = match c_path_opt {
        Some(ref cp) if cp.exists() || needs_c => {
            Some(verify_and_hash_artifact_bytes(cp, true, true)?)
        }
        _ => None,
    };
    let trace_path = olean_path.with_extension("trace");
    if !trace_path.is_file() {
        anyhow::bail!(
            "Required Lake module trace `{}` is missing",
            trace_path.display()
        );
    }
    let tb = fs::read(&trace_path)?;
    let tv: serde_json::Value = serde_json::from_slice(&tb).map_err(|_| {
        anyhow::anyhow!(
            "Malformed JSON in Lake module trace `{}`",
            trace_path.display()
        )
    })?;
    let expected_o = format!("{:016x}.olean", olean_h);
    let expected_i = format!("{:016x}.ilean", ilean_h);
    let expected_dep_h = format!("{:016x}", lake_input_hash(&tv["inputs"])?);
    if tv.get("schemaVersion").and_then(|v| v.as_str()) != Some("2025-09-10")
        || tv.pointer("/outputs/m").and_then(|v| v.as_bool()) != Some(is_module)
        || tv.pointer("/outputs/o/0").and_then(|v| v.as_str()) != Some(expected_o.as_str())
        || tv.pointer("/outputs/i").and_then(|v| v.as_str()) != Some(expected_i.as_str())
        || tv.get("depHash").and_then(|v| v.as_str()) != Some(expected_dep_h.as_str())
    {
        anyhow::bail!(
            "Lake module trace `{}` failed integrity verification against artifacts",
            trace_path.display()
        );
    }
    if let Some((srv_h, priv_h, ir_sig_h, ir_h)) = mod_comp_hashes {
        if tv.pointer("/outputs/o/1").and_then(|v| v.as_str())
            != Some(format!("{:016x}.olean.server", srv_h).as_str())
            || tv.pointer("/outputs/o/2").and_then(|v| v.as_str())
                != Some(format!("{:016x}.olean.private", priv_h).as_str())
            || tv.pointer("/outputs/rs").and_then(|v| v.as_str())
                != Some(format!("{:016x}.ir.sig", ir_sig_h).as_str())
            || tv.pointer("/outputs/r").and_then(|v| v.as_str())
                != Some(format!("{:016x}.ir", ir_h).as_str())
        {
            anyhow::bail!(
                "Lake module trace `{}` module companion outputs do not match artifacts",
                trace_path.display()
            );
        }
    }
    if let Some(c_h) = c_h_opt {
        if tv.pointer("/outputs/c").and_then(|v| v.as_str())
            != Some(format!("{:016x}.c", c_h).as_str())
        {
            anyhow::bail!(
                "Lake module trace `{}` `.c` output hash does not match artifact",
                trace_path.display()
            );
        }
    }
    let expected_src_h = format!("{:016x}", lake_hash_text(src_raw));
    if tv.pointer("/inputs/3/1").and_then(|v| v.as_str()) != Some(expected_src_h.as_str()) {
        anyhow::bail!(
            "Lake module trace `{}` recorded source hash does not match source",
            trace_path.display()
        );
    }
    Ok(())
}

fn is_dep_olean_fresh(
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
    src_content: &str,
    is_module: bool,
    imports: &[String],
    olean_path: &Path,
) -> Option<std::time::SystemTime> {
    let pkg_root = &spec.pkg_root;
    let src_path = &spec.src_path;
    if !is_regular_nonempty_file(olean_path) {
        return None;
    }
    let om = fs::metadata(olean_path).ok()?;
    if is_module {
        let srv_path = PathBuf::from(format!("{}.server", olean_path.display()));
        let priv_path = PathBuf::from(format!("{}.private", olean_path.display()));
        if !is_regular_nonempty_file(&srv_path) || !is_regular_nonempty_file(&priv_path) {
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
    // Fail closed (`None`) when the manifest or audited module entry is absent or stale.
    let manifest =
        read_pkg_verified_manifest(cfg, pkg_root, &spec.pkg_name, &spec.pkg_config_digest)?;
    let rel_src = src_path
        .strip_prefix(pkg_root)
        .unwrap_or(src_path)
        .to_string_lossy()
        .replace('\\', "/");
    let entry = manifest.modules.get(&rel_src)?;
    if spec.is_root_pkg && !entry.kernel_audited {
        return None;
    }
    let actual_src_hash = blake3::hash(src_content.as_bytes()).to_hex().to_string();
    if entry.src_blake3 != actual_src_hash {
        return None;
    }
    let actual_olean_digest = compute_olean_artifact_set_digest_with_policy(
        olean_path,
        crate::lake_build::worktree_auto_link_disabled(&cfg.root_pkg.pkg_root),
    )
    .ok()?;
    if entry.olean_artifact_digest != actual_olean_digest {
        return None;
    }
    // Same-package pins compare against `manifest`; other packages' against their on-disk
    // artifacts. `collect_fresh_dep_pkg_closure` verifies every visited module the same way.
    let preserve = crate::lake_build::worktree_auto_link_disabled(&cfg.root_pkg.pkg_root);
    let pins_ok = verified_entry_imports_current(entry, imports, |imp, pin| {
        match (resolve_import_site(cfg, imp), pin) {
            (ImportSite::Toolchain, None) => true,
            (ImportSite::Module(d), Some(pin)) if d.pkg_name == spec.pkg_name => manifest
                .modules
                .get(&spec_rel_src(&d))
                .is_some_and(|e| e.olean_artifact_digest == pin),
            (ImportSite::Module(d), Some(pin)) => {
                compute_olean_artifact_set_digest_with_policy(&spec_olean_path(&d), preserve)
                    .is_ok_and(|dig| dig == pin)
            }
            _ => false,
        }
    });
    // Toolchain, configuration, and source were matched above.
    if !c_abi::verify_module_cache_key(true, true, true, pins_ok, true) {
        return None;
    }
    let rel_slash = module_name_to_rel_slash(&spec.module_name);
    if verify_module_lake_sidecars(
        olean_path,
        Some(&spec.build_ir_dir),
        &rel_slash,
        src_content,
        is_module,
        spec.precompile_modules || spec.is_exe_target,
    )
    .is_err()
    {
        return None;
    }
    Some(ot)
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
        if hdr.header_error.is_some() {
            return Ok(None);
        }
        let rel_slash = module_name_to_rel_slash(&cur.module_name);
        let olean_path = cur.build_lib_lean_dir.join(format!("{}.olean", rel_slash));
        let Some(cur_olean_mtime) =
            is_dep_olean_fresh(cfg, &cur, &src, hdr.is_module, &hdr.imports, &olean_path)
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
            if let Some(sub_spec) = matches.into_iter().next() {
                let key = (sub_spec.pkg_name.clone(), sub_spec.module_name.clone());
                if visited.insert(key) {
                    queue.push_back((sub_spec, Some(cur_olean_mtime)));
                }
                continue;
            }
            if resolve_module_in_package(&cfg.root_pkg, true, &imp).is_some() {
                return Ok(None);
            }
            if is_builtin_toolchain_module(&cfg.toolchain_lib_lean, &imp) {
                continue;
            }
            // Unresolved import inside dependency closure: force native DAG traversal so
            // root-package imports or missing-module errors are handled deterministically.
            return Ok(None);
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
    let global_emit_c = ["TURBO_LEAN_EMIT_C", "TURBO_LEAN_LAKE_COMPAT"]
        .into_iter()
        .any(|k| {
            std::env::var(k)
                .map(|v| v.trim() == "1" || v.eq_ignore_ascii_case("true"))
                .unwrap_or(false)
        });
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
        if let Some(ref herr) = header.header_error {
            anyhow::bail!(
                "Invalid module header in `{}` ({}): {}",
                spec.module_name,
                spec.src_path.display(),
                herr
            );
        }
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
        let rel_slash = module_name_to_rel_slash(&spec.module_name);
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
    compute_olean_artifact_set_digest_with_policy(olean_path, false)
}

fn compute_olean_artifact_set_digest_with_policy(
    olean_path: &Path,
    preserve_caller: bool,
) -> Result<String> {
    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock
        .lock()
        .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
    let _flock_guard = if let Some(pkg_root) = infer_pkg_root_from_artifact_path(olean_path) {
        Some(acquire_publish_flock_mode(
            &pkg_root,
            false,
            preserve_caller || crate::lake_build::worktree_auto_link_disabled(&pkg_root),
        )?)
    } else {
        None
    };
    compute_olean_artifact_set_digest_locked(olean_path, _flock_guard.as_ref())
}

fn olean_artifact_paths(olean_path: &Path) -> [(&'static str, PathBuf); 6] {
    [
        ("olean", olean_path.to_path_buf()),
        ("srv", olean_path.with_extension("olean.server")),
        ("priv", olean_path.with_extension("olean.private")),
        ("ilean", olean_path.with_extension("ilean")),
        ("ir", olean_path.with_extension("ir")),
        ("ir_sig", olean_path.with_extension("ir.sig")),
    ]
}

fn compute_olean_artifact_set_digest_locked(
    olean_path: &Path,
    guard: Option<&crate::shm_cache::PublishFlockGuard>,
) -> Result<String> {
    read_olean_artifact_set_digest(olean_path, guard, |p| Ok(fs::read(p)?))
}

fn read_olean_artifact_set_digest(
    olean_path: &Path,
    guard: Option<&crate::shm_cache::PublishFlockGuard>,
    mut read: impl FnMut(&Path) -> Result<Vec<u8>>,
) -> Result<String> {
    let artifacts = olean_artifact_paths(olean_path);
    let paths: Vec<_> = artifacts.iter().map(|(_, p)| p.clone()).collect();
    let mut digest = || {
        let mut h = blake3::Hasher::new();
        h.update(b"olean-art-v2\n");
        for (tag, path) in &artifacts {
            let present = match fs::metadata(path) {
                Ok(meta) => {
                    anyhow::ensure!(
                        meta.is_file(),
                        "Artifact path `{}` is not a regular file",
                        path.display()
                    );
                    true
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound && *tag != "olean" => false,
                Err(e) => {
                    return Err(e)
                        .with_context(|| format!("Failed to stat artifact {}", path.display()))
                }
            };
            if *tag != "olean" {
                h.update(&[u8::from(present)]);
            }
            if present {
                let bytes = read(path)
                    .with_context(|| format!("Failed to read artifact {}", path.display()))?;
                update_lp(&mut h, tag.as_bytes(), blake3::hash(&bytes).as_bytes());
            } else {
                update_lp(&mut h, tag.as_bytes(), b"");
            }
        }
        Ok(h.finalize().to_hex().to_string())
    };
    match guard {
        Some(guard) => guard.read_consistent(&paths, digest),
        None => digest(),
    }
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
    let allowed = crate::splitter::allowed_axioms();
    if allowed.len() > crate::splitter::STANDARD_AXIOMS.len() {
        update_lp(&mut h, b"axioms", allowed.join(",").as_bytes());
    }
    Ok(h.finalize().to_hex().to_string())
}
pub(crate) fn build_lean_search_path(cfg: &ProjectConfig, is_untrusted: bool) -> (String, String) {
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
pub(crate) fn scrub_untrusted_env(cmd: &mut Command) {
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
        let _ = fs::remove_file(format!("{}.hash", p.display()));
    }
    let _ = fs::remove_file(node.olean_path.with_extension("trace"));
}

pub fn lake_murmur64a(data: &[u8], seed: u64) -> u64 {
    const M: u64 = 0xc6a4a7935bd1e995;
    const R: u32 = 47;
    let mut h = seed ^ (data.len() as u64).wrapping_mul(M);
    let mut chunks = data.chunks_exact(8);
    for chunk in &mut chunks {
        let mut k = u64::from_le_bytes(chunk.try_into().unwrap());
        k = k.wrapping_mul(M);
        k ^= k >> R;
        k = k.wrapping_mul(M);
        h ^= k;
        h = h.wrapping_mul(M);
    }
    let rem = chunks.remainder();
    if !rem.is_empty() {
        let mut val = 0u64;
        for &b in rem.iter().rev() {
            val = (val << 8) | (b as u64);
        }
        h ^= val;
        h = h.wrapping_mul(M);
    }
    h ^= h >> R;
    h = h.wrapping_mul(M);
    h ^= h >> R;
    h
}

#[inline]
pub fn lake_mix_hash(h: u64, mut k: u64) -> u64 {
    const M: u64 = 0xc6a4a7935bd1e995;
    k = k.wrapping_mul(M);
    k ^= k >> 47;
    k ^= M;
    (h ^ k).wrapping_mul(M)
}

#[inline]
pub fn lake_hash_bytes(data: &[u8]) -> u64 {
    lake_mix_hash(1723, lake_murmur64a(data, 11))
}

#[inline]
pub fn lake_hash_text(s: &str) -> u64 {
    if s.as_bytes().contains(&b'\r') {
        lake_hash_bytes(s.replace("\r\n", "\n").as_bytes())
    } else {
        lake_hash_bytes(s.as_bytes())
    }
}

pub fn lake_hash_name(mod_name: &str) -> u64 {
    let mut h = 1723u64;
    for part in mod_name.split('.').filter(|p| !p.is_empty()) {
        h = lake_mix_hash(h, lake_murmur64a(part.as_bytes(), 11));
    }
    lake_mix_hash(1723, h)
}

pub fn lake_hash_pkg_id(pkg_name: &str) -> u64 {
    lake_mix_hash(
        1723,
        lake_mix_hash(lake_murmur64a(pkg_name.as_bytes(), 11), 13),
    )
}

fn lake_input_hash(val: &serde_json::Value) -> Result<u64> {
    if let Some(s) = val.as_str() {
        if s.len() != 16 || !s.bytes().all(|b| b.is_ascii_hexdigit()) {
            anyhow::bail!("Malformed 16-hex trace input hash `{}`", s);
        }
        return Ok(u64::from_str_radix(s, 16)?);
    }
    if let Some(arr) = val.as_array() {
        let mut h = 1723u64;
        for item in arr {
            let Some(pair) = item.as_array() else {
                anyhow::bail!("Malformed trace input entry (expected 2-element array)");
            };
            if pair.len() != 2 || !pair[0].is_string() {
                anyhow::bail!("Malformed trace input pair (expected [caption, hash_or_array])");
            }
            h = lake_mix_hash(h, lake_input_hash(&pair[1])?);
        }
        return Ok(h);
    }
    anyhow::bail!("Malformed trace input value (expected hex string or array)")
}

#[derive(Clone, Copy, Debug)]
struct LakeModuleExportInfo {
    arts_trace: u64,
    meta_arts_trace: u64,
    all_arts_trace: u64,
    trans_trace: u64,
    meta_trans_trace: u64,
    all_trans_trace: u64,
    legacy_trans_trace: u64,
}

fn verify_and_hash_artifact_bytes(
    artifact_path: &Path,
    check_existing_sidecar: bool,
    require_hash_file: bool,
) -> Result<u64> {
    if !has_no_symlink_at(artifact_path) || !is_regular_nonempty_file(artifact_path) {
        anyhow::bail!(
            "Artifact `{}` is missing, empty, or a symlink",
            artifact_path.display()
        );
    }
    let bytes = fs::read(artifact_path)?;
    if artifact_path.extension().and_then(|s| s.to_str()) == Some("olean")
        && (bytes.len() < 32 || !bytes.starts_with(b"olean"))
    {
        anyhow::bail!(
            "Artifact `{}` lacks valid Lean 4 .olean header magic",
            artifact_path.display()
        );
    }
    let actual_h = lake_hash_bytes(&bytes);
    if check_existing_sidecar {
        let hash_path = PathBuf::from(format!("{}.hash", artifact_path.display()));
        if hash_path.exists() {
            let raw = fs::read_to_string(&hash_path)?;
            let trimmed = raw.trim();
            if trimmed.len() != 16 || !trimmed.bytes().all(|b| b.is_ascii_hexdigit()) {
                anyhow::bail!("Malformed 16-hex hash in sidecar `{}`", hash_path.display());
            }
            let recorded_h = u64::from_str_radix(trimmed, 16)?;
            if recorded_h != actual_h {
                anyhow::bail!(
                    "Sidecar hash mismatch for `{}` (recorded {:016x} != actual {:016x})",
                    artifact_path.display(),
                    recorded_h,
                    actual_h
                );
            }
        } else if require_hash_file {
            anyhow::bail!(
                "Required dependency hash sidecar `{}` is missing",
                hash_path.display()
            );
        }
    }
    Ok(actual_h)
}

fn compute_lake_export_info(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    requester: &ModuleNode,
    mod_name: &str,
    memo: &mut HashMap<String, LakeModuleExportInfo>,
    visiting: &mut HashSet<String>,
) -> Result<LakeModuleExportInfo> {
    if let Some(info) = memo.get(mod_name) {
        return Ok(*info);
    }
    if !visiting.insert(mod_name.to_string()) {
        anyhow::bail!(
            "Import cycle detected while computing Lake export trace for `{}`",
            mod_name
        );
    }
    let resolved: Option<(Option<PathBuf>, PathBuf, bool)> =
        if let Some(n) = dag.nodes.get(mod_name) {
            Some((Some(n.src_path.clone()), n.olean_path.clone(), true))
        } else if let Some((_, ext_p)) = requester
            .external_olean_deps
            .iter()
            .find(|(m, _)| m == mod_name)
        {
            let src_opt = resolve_module_in_package(&cfg.root_pkg, true, mod_name)
                .or_else(|| {
                    cfg.dep_pkgs
                        .iter()
                        .find_map(|dp| resolve_module_in_package(dp, false, mod_name))
                })
                .map(|sp| sp.src_path);
            Some((src_opt, ext_p.clone(), false))
        } else {
            resolve_module_in_package(&cfg.root_pkg, true, mod_name)
                .or_else(|| {
                    cfg.dep_pkgs
                        .iter()
                        .find_map(|dp| resolve_module_in_package(dp, false, mod_name))
                })
                .map(|sp| {
                    let rel_slash = module_name_to_rel_slash(mod_name);
                    let olean_p = sp.build_lib_lean_dir.join(format!("{}.olean", rel_slash));
                    (Some(sp.src_path), olean_p, false)
                })
        };
    let Some((src_opt, olean_path, _is_in_dag)) = resolved else {
        visiting.remove(mod_name);
        anyhow::bail!("Unresolved workspace/package import `{}`", mod_name);
    };
    let olean_h = verify_and_hash_artifact_bytes(&olean_path, true, true)?;
    let ilean_h = verify_and_hash_artifact_bytes(&olean_path.with_extension("ilean"), true, true)?;
    let srv_path = PathBuf::from(format!("{}.server", olean_path.display()));
    let priv_path = PathBuf::from(format!("{}.private", olean_path.display()));
    let ir_path = olean_path.with_extension("ir");
    let ir_sig_path = PathBuf::from(format!("{}.sig", ir_path.display()));
    let dep_src_info = match src_opt {
        Some(ref sp) if sp.is_file() => {
            let raw = fs::read_to_string(sp)?;
            let hdr = parse_header_info(&raw);
            if let Some(ref herr) = hdr.header_error {
                anyhow::bail!(
                    "Invalid module header in dependency `{}` ({}): {}",
                    mod_name,
                    sp.display(),
                    herr
                );
            }
            Some((sp.clone(), raw, hdr))
        }
        _ => None,
    };
    let is_mod = dep_src_info
        .as_ref()
        .map(|(_, _, h)| h.is_module)
        .unwrap_or_else(|| srv_path.is_file());
    let arts_trace = lake_mix_hash(1723, olean_h);
    let (meta_arts_trace, all_arts_trace, mod_comp_hashes) = if is_mod {
        let srv_h = verify_and_hash_artifact_bytes(&srv_path, true, true)?;
        let priv_h = verify_and_hash_artifact_bytes(&priv_path, true, true)?;
        let ir_sig_h = verify_and_hash_artifact_bytes(&ir_sig_path, true, true)?;
        let ir_h = verify_and_hash_artifact_bytes(&ir_path, true, true)?;
        let meta_t = lake_mix_hash(lake_mix_hash(lake_mix_hash(1723, olean_h), ir_sig_h), ir_h);
        let all_t = lake_mix_hash(
            lake_mix_hash(
                lake_mix_hash(lake_mix_hash(lake_mix_hash(1723, olean_h), srv_h), priv_h),
                ir_sig_h,
            ),
            ir_h,
        );
        (meta_t, all_t, Some((srv_h, priv_h, ir_sig_h, ir_h)))
    } else {
        (arts_trace, arts_trace, None)
    };
    let trace_path = olean_path.with_extension("trace");
    let trace_val_opt: Option<serde_json::Value> = if trace_path.exists() {
        let tb = fs::read(&trace_path)?;
        let tv: serde_json::Value = serde_json::from_slice(&tb).map_err(|_| {
            anyhow::anyhow!(
                "Malformed JSON in dependency trace `{}`",
                trace_path.display()
            )
        })?;
        let expected_o = format!("{:016x}.olean", olean_h);
        let expected_i = format!("{:016x}.ilean", ilean_h);
        let expected_dep_h = format!("{:016x}", lake_input_hash(&tv["inputs"])?);
        if tv.get("schemaVersion").and_then(|v| v.as_str()) != Some("2025-09-10")
            || tv.pointer("/outputs/m").and_then(|v| v.as_bool()) != Some(is_mod)
            || tv.pointer("/outputs/o/0").and_then(|v| v.as_str()) != Some(expected_o.as_str())
            || tv.pointer("/outputs/i").and_then(|v| v.as_str()) != Some(expected_i.as_str())
            || tv.get("depHash").and_then(|v| v.as_str()) != Some(expected_dep_h.as_str())
        {
            anyhow::bail!(
                "Dependency trace `{}` failed integrity verification against artifacts",
                trace_path.display()
            );
        }
        if let Some((srv_h, priv_h, ir_sig_h, ir_h)) = mod_comp_hashes {
            if tv.pointer("/outputs/o/1").and_then(|v| v.as_str())
                != Some(format!("{:016x}.olean.server", srv_h).as_str())
                || tv.pointer("/outputs/o/2").and_then(|v| v.as_str())
                    != Some(format!("{:016x}.olean.private", priv_h).as_str())
                || tv.pointer("/outputs/rs").and_then(|v| v.as_str())
                    != Some(format!("{:016x}.ir.sig", ir_sig_h).as_str())
                || tv.pointer("/outputs/r").and_then(|v| v.as_str())
                    != Some(format!("{:016x}.ir", ir_h).as_str())
            {
                anyhow::bail!(
                    "Dependency trace `{}` module companion outputs do not match artifacts",
                    trace_path.display()
                );
            }
        }
        if let Some((_, ref src_raw, _)) = dep_src_info {
            let expected_src_h = format!("{:016x}", lake_hash_text(src_raw));
            if tv.pointer("/inputs/3/1").and_then(|v| v.as_str()) != Some(expected_src_h.as_str()) {
                anyhow::bail!(
                    "Dependency trace `{}` recorded source hash does not match `{}`",
                    trace_path.display(),
                    mod_name
                );
            }
        }
        Some(tv)
    } else {
        anyhow::bail!(
            "Required dependency trace `{}` is missing for module `{}`",
            trace_path.display(),
            mod_name
        );
    };
    let mut trans_trace = 1723u64;
    let mut meta_trans_trace = 1723u64;
    let mut all_trans_trace = 1723u64;
    let mut legacy_trans_trace = 1723u64;
    if let Some((_, _, ref dh)) = dep_src_info {
        for sub_imp in &dh.import_specs {
            let is_ws_or_pkg = dag.nodes.contains_key(&sub_imp.module)
                || requester
                    .external_olean_deps
                    .iter()
                    .any(|(m, _)| m == &sub_imp.module)
                || resolve_module_in_package(&cfg.root_pkg, true, &sub_imp.module).is_some()
                || cfg
                    .dep_pkgs
                    .iter()
                    .any(|dp| resolve_module_in_package(dp, false, &sub_imp.module).is_some());
            if !is_ws_or_pkg
                && is_builtin_toolchain_module(&cfg.toolchain_lib_lean, &sub_imp.module)
            {
                continue;
            }
            let sub_exp =
                compute_lake_export_info(cfg, dag, requester, &sub_imp.module, memo, visiting)?;
            legacy_trans_trace = lake_mix_hash(
                lake_mix_hash(legacy_trans_trace, sub_exp.legacy_trans_trace),
                sub_exp.all_arts_trace,
            );
            all_trans_trace = if sub_imp.import_all {
                lake_mix_hash(
                    lake_mix_hash(all_trans_trace, sub_exp.all_trans_trace),
                    sub_exp.all_arts_trace,
                )
            } else if sub_imp.is_meta {
                lake_mix_hash(
                    lake_mix_hash(all_trans_trace, sub_exp.meta_trans_trace),
                    sub_exp.meta_arts_trace,
                )
            } else {
                lake_mix_hash(
                    lake_mix_hash(all_trans_trace, sub_exp.trans_trace),
                    sub_exp.arts_trace,
                )
            };
            meta_trans_trace = lake_mix_hash(
                lake_mix_hash(meta_trans_trace, sub_exp.meta_trans_trace),
                sub_exp.meta_arts_trace,
            );
            if sub_imp.is_exported {
                trans_trace = if sub_imp.is_meta {
                    lake_mix_hash(
                        lake_mix_hash(trans_trace, sub_exp.meta_trans_trace),
                        sub_exp.meta_arts_trace,
                    )
                } else {
                    lake_mix_hash(
                        lake_mix_hash(trans_trace, sub_exp.trans_trace),
                        sub_exp.arts_trace,
                    )
                };
            }
        }
    } else {
        let tv = trace_val_opt.as_ref().ok_or_else(|| {
            anyhow::anyhow!("Missing trace for source-less dependency `{}`", mod_name)
        })?;
        let arr = tv.pointer("/inputs/0/1/1/1").ok_or_else(|| {
            anyhow::anyhow!(
                "Missing `/inputs/0/1/1/1` import array in trace for `{}`",
                mod_name
            )
        })?;
        let h = lake_input_hash(arr)?;
        legacy_trans_trace = h;
        all_trans_trace = h;
        meta_trans_trace = h;
        trans_trace = h;
    }
    visiting.remove(mod_name);
    let info = LakeModuleExportInfo {
        arts_trace,
        meta_arts_trace,
        all_arts_trace,
        trans_trace,
        meta_trans_trace,
        all_trans_trace,
        legacy_trans_trace,
    };
    memo.insert(mod_name.to_string(), info);
    Ok(info)
}

#[inline]
fn nonzero_u64_digest(raw: u64) -> u64 {
    if raw == 0 {
        1
    } else {
        raw
    }
}

fn nonzero_blake3_u64(s: &str) -> u64 {
    if s.is_empty() {
        return 0;
    }
    let bytes = blake3::hash(s.as_bytes());
    let mut arr = [0u8; 8];
    arr.copy_from_slice(&bytes.as_bytes()[..8]);
    nonzero_u64_digest(u64::from_le_bytes(arr))
}

pub fn write_lake_module_hashes_and_trace(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    node: &ModuleNode,
    expected_artifact_digest: &str,
    audited_artifact_digest: Option<&str>,
    kernel_audit_clean: bool,
) -> Result<()> {
    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock
        .lock()
        .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
    let _flock_guard = acquire_publish_flock(&node.pkg_root, false)?;
    let srv_path = PathBuf::from(format!("{}.server", node.olean_path.display()));
    let priv_path = PathBuf::from(format!("{}.private", node.olean_path.display()));
    let ir_path = node.olean_path.with_extension("ir");
    let ir_sig_path = PathBuf::from(format!("{}.sig", ir_path.display()));
    let (src_raw, src_read_ok) = match fs::read_to_string(&node.src_path) {
        Ok(s) => (s, true),
        Err(_) => (String::new(), false),
    };
    let src_blake3_matches =
        src_read_ok && blake3::hash(src_raw.as_bytes()).to_hex().as_str() == node.src_blake3;
    let hygiene = splitter::audit_hygiene(&splitter::strip_lean_comments(&src_raw));
    let no_forbidden_proof_tokens = !hygiene.has_sorry
        && !hygiene.has_axiom
        && !hygiene.native_violation()
        && !hygiene.has_trust_compiler;
    let skeleton_clean = src_blake3_matches && no_forbidden_proof_tokens;
    let is_stubbed_skeleton =
        hygiene.has_sorry || !no_forbidden_proof_tokens || !src_blake3_matches;
    let olean_h_res = verify_and_hash_artifact_bytes(&node.olean_path, false, false);
    let ilean_h_res = verify_and_hash_artifact_bytes(&node.ilean_path, false, false);
    let c_h_res = if is_regular_nonempty_file(&node.c_path) {
        Some(verify_and_hash_artifact_bytes(&node.c_path, false, false))
    } else if node.needs_c {
        Some(Err(anyhow::anyhow!("Required .c artifact missing")))
    } else {
        None
    };
    let mod_companions_res = if node.is_module {
        Some((
            verify_and_hash_artifact_bytes(&srv_path, false, false),
            verify_and_hash_artifact_bytes(&priv_path, false, false),
            verify_and_hash_artifact_bytes(&ir_sig_path, false, false),
            verify_and_hash_artifact_bytes(&ir_path, false, false),
        ))
    } else {
        None
    };
    let actual_art_digest_opt =
        compute_olean_artifact_set_digest_locked(&node.olean_path, Some(&_flock_guard)).ok();
    let digest_matches = !expected_artifact_digest.is_empty()
        && actual_art_digest_opt.as_deref() == Some(expected_artifact_digest);
    let all_shards_certified =
        validate_materialized_module_artifacts(node) && !hygiene.has_sorry && digest_matches;
    let artifact_hashes_match = digest_matches
        && olean_h_res.is_ok()
        && ilean_h_res.is_ok()
        && c_h_res.as_ref().is_none_or(|r| r.is_ok())
        && mod_companions_res
            .as_ref()
            .is_none_or(|(s, p, rs, r)| s.is_ok() && p.is_ok() && rs.is_ok() && r.is_ok());
    let header = parse_header_info(&src_raw);
    let mut import_entries = Vec::new();
    let mut dep_trace_fresh = header.header_error.is_none() && header.is_module == node.is_module;
    let mut exp_memo = HashMap::new();
    let mut visiting = HashSet::new();
    if dep_trace_fresh {
        for imp in &header.import_specs {
            let is_ws_or_pkg = dag.nodes.contains_key(&imp.module)
                || node
                    .external_olean_deps
                    .iter()
                    .any(|(m, _)| m == &imp.module)
                || resolve_module_in_package(&cfg.root_pkg, true, &imp.module).is_some()
                || cfg
                    .dep_pkgs
                    .iter()
                    .any(|dp| resolve_module_in_package(dp, false, &imp.module).is_some());
            if !is_ws_or_pkg {
                if is_builtin_toolchain_module(&cfg.toolchain_lib_lean, &imp.module) {
                    continue;
                }
                dep_trace_fresh = false;
                break;
            }
            match compute_lake_export_info(
                cfg,
                dag,
                node,
                &imp.module,
                &mut exp_memo,
                &mut visiting,
            ) {
                Ok(exp_info) => {
                    if !node.is_module {
                        import_entries.push(serde_json::json!([
                            format!("{} transitive imports (legacy)", imp.module),
                            format!("{:016x}", exp_info.legacy_trans_trace)
                        ]));
                        import_entries.push(serde_json::json!([
                            format!("{}:importAllArts", imp.module),
                            format!("{:016x}", exp_info.all_arts_trace)
                        ]));
                    } else if imp.import_all {
                        import_entries.push(serde_json::json!([
                            format!("{} transitive imports (all)", imp.module),
                            format!("{:016x}", exp_info.all_trans_trace)
                        ]));
                        import_entries.push(serde_json::json!([
                            format!("{}:importAllArts", imp.module),
                            format!("{:016x}", exp_info.all_arts_trace)
                        ]));
                    } else if imp.is_meta {
                        import_entries.push(serde_json::json!([
                            format!("{} transitive imports (meta)", imp.module),
                            format!("{:016x}", exp_info.meta_trans_trace)
                        ]));
                        import_entries.push(serde_json::json!([
                            format!("{}:importArts (meta)", imp.module),
                            format!("{:016x}", exp_info.meta_arts_trace)
                        ]));
                    } else {
                        import_entries.push(serde_json::json!([
                            format!("{} transitive imports (public)", imp.module),
                            format!("{:016x}", exp_info.trans_trace)
                        ]));
                        import_entries.push(serde_json::json!([
                            format!("{}:importArts", imp.module),
                            format!("{:016x}", exp_info.arts_trace)
                        ]));
                    }
                }
                Err(_) => {
                    dep_trace_fresh = false;
                    break;
                }
            }
        }
    }
    let src_h = lake_hash_text(&src_raw);
    let mut opt_entries = Vec::new();
    let mut lean_args = Vec::new();
    for a in &node.strong_args {
        if a.starts_with("-D") {
            opt_entries.push(serde_json::json!([
                a,
                format!("{:016x}", lake_hash_text(a))
            ]));
        } else {
            lean_args.push(a.as_str());
        }
    }
    let lean_args_h = lean_args.iter().fold(1723u64, |acc, a| {
        lake_mix_hash(acc, lake_hash_bytes(a.as_bytes()))
    });
    let pkg_ident = if node.pkg_name.contains('-') {
        format!("«{}»", node.pkg_name)
    } else {
        node.pkg_name.clone()
    };
    let ver_short = cfg
        .toolchain
        .rsplit(':')
        .next()
        .unwrap_or(&cfg.toolchain)
        .trim_start_matches('v');
    let lean_cap = format!("Lean {}, commit {}", ver_short, cfg.lean_githash);
    let lean_gh_h = lake_hash_bytes(cfg.lean_githash.as_bytes());
    let is_mod_h = lake_mix_hash(1723, if node.is_module { 11 } else { 13 });
    let lean_args_cap = if lean_args.is_empty() {
        "Module.leanArgs: #[]".to_string()
    } else {
        format!("Module.leanArgs: #[{}]", lean_args.join(", "))
    };
    let inputs = serde_json::json!([
        [
            "deps",
            [
                [
                    format!("{}/{}:extraDep", pkg_ident, node.target_name),
                    [[format!("@{}:extraDep", pkg_ident), "00000000000006bb"]]
                ],
                ["imports", import_entries]
            ]
        ],
        [
            "libs",
            [
                ["import dynlibs", "00000000000006bb"],
                ["package external libraries", "00000000000006bb"],
                ["module dynlibs", "00000000000006bb"],
                ["module plugins", "00000000000006bb"]
            ]
        ],
        [lean_cap, format!("{:016x}", lean_gh_h)],
        [node.src_path.to_string_lossy(), format!("{:016x}", src_h)],
        ["options", opt_entries],
        [
            format!("isModule: {}", node.is_module),
            format!("{:016x}", is_mod_h)
        ],
        [
            format!("Module.name: {}", node.module_name),
            format!("{:016x}", lake_hash_name(&node.module_name))
        ],
        [
            format!("Package.id?: (some {})", node.pkg_name),
            format!("{:016x}", lake_hash_pkg_id(&node.pkg_name))
        ],
        [lean_args_cap, format!("{:016x}", lean_args_h)]
    ]);
    let dep_hash_opt = lake_input_hash(&inputs).ok();
    let stubbed_placeholder_count = if is_stubbed_skeleton { 1u64 } else { 0u64 };
    let total_shard_count = 1u64;
    let certified_shard_count = if all_shards_certified && artifact_hashes_match {
        1u64
    } else {
        0u64
    };
    let distinct_covered_shard_count = certified_shard_count;
    let expected_interface_digest = nonzero_blake3_u64(&node.src_blake3);
    let actual_interface_digest = if src_blake3_matches {
        nonzero_blake3_u64(blake3::hash(src_raw.as_bytes()).to_hex().as_str())
    } else {
        0
    };
    let expected_olean_digest = nonzero_blake3_u64(expected_artifact_digest);
    let actual_olean_digest = if artifact_hashes_match {
        actual_art_digest_opt
            .as_deref()
            .map(nonzero_blake3_u64)
            .unwrap_or(0)
    } else {
        0
    };
    let actual_ilean_digest = ilean_h_res
        .as_ref()
        .ok()
        .copied()
        .map(nonzero_u64_digest)
        .unwrap_or(0);
    let expected_ilean_digest = if artifact_hashes_match {
        actual_ilean_digest
    } else {
        0
    };
    let actual_c_digest = match c_h_res {
        Some(Ok(ch)) => nonzero_u64_digest(ch),
        _ => 0,
    };
    let expected_c_digest = if node.needs_c && artifact_hashes_match {
        actual_c_digest
    } else {
        0
    };
    let dep_trace_digest = if dep_trace_fresh {
        dep_hash_opt.map(nonzero_u64_digest).unwrap_or(0)
    } else {
        0
    };
    let audited_digest_u64 = audited_artifact_digest.map(nonzero_blake3_u64).unwrap_or(0);
    if !c_abi::verify_audit_materialize_gate(
        skeleton_clean,
        stubbed_placeholder_count,
        certified_shard_count,
        distinct_covered_shard_count,
        total_shard_count,
        expected_interface_digest,
        actual_interface_digest,
        expected_olean_digest,
        actual_olean_digest,
        expected_ilean_digest,
        actual_ilean_digest,
        node.needs_c,
        expected_c_digest,
        actual_c_digest,
        dep_trace_digest,
        audited_digest_u64,
        kernel_audit_clean,
    ) {
        for p in [
            &node.olean_path,
            &node.ilean_path,
            &srv_path,
            &priv_path,
            &ir_path,
            &ir_sig_path,
            &node.c_path,
        ] {
            let _ = fs::remove_file(format!("{}.hash", p.display()));
        }
        let _ = fs::remove_file(node.olean_path.with_extension("trace"));
        anyhow::bail!(
            "Audit materialization gate `turbo_spec_verify_audit_materialize_gate` rejected sidecar emission for `{}` (skeleton_clean={}, all_shards_certified={}, is_stubbed={}, hashes_match={}, dep_trace_fresh={}, kernel_audit_clean={})",
            node.module_name,
            skeleton_clean,
            all_shards_certified,
            is_stubbed_skeleton,
            artifact_hashes_match,
            dep_trace_fresh,
            kernel_audit_clean
        );
    }
    let dep_hash = dep_hash_opt.ok_or_else(|| {
        anyhow::anyhow!(
            "Failed to compute Lake trace depHash for `{}`",
            node.module_name
        )
    })?;
    let olean_h = olean_h_res?;
    let ilean_h = ilean_h_res?;
    let mut sidecar_writes: Vec<(PathBuf, Vec<u8>)> = vec![
        (
            PathBuf::from(format!("{}.hash", node.olean_path.display())),
            format!("{:016x}", olean_h).into_bytes(),
        ),
        (
            PathBuf::from(format!("{}.hash", node.ilean_path.display())),
            format!("{:016x}", ilean_h).into_bytes(),
        ),
    ];
    let c_h = match c_h_res {
        Some(Ok(ch)) => {
            sidecar_writes.push((
                PathBuf::from(format!("{}.hash", node.c_path.display())),
                format!("{:016x}", ch).into_bytes(),
            ));
            ch
        }
        _ => {
            let _ = fs::remove_file(format!("{}.hash", node.c_path.display()));
            1723
        }
    };
    let outputs_json =
        if let Some((Ok(srv_h), Ok(priv_h), Ok(ir_sig_h), Ok(ir_h))) = mod_companions_res {
            for (p, h) in [
                (&srv_path, srv_h),
                (&priv_path, priv_h),
                (&ir_sig_path, ir_sig_h),
                (&ir_path, ir_h),
            ] {
                sidecar_writes.push((
                    PathBuf::from(format!("{}.hash", p.display())),
                    format!("{:016x}", h).into_bytes(),
                ));
            }
            serde_json::json!({
                "o": [
                    format!("{:016x}.olean", olean_h),
                    format!("{:016x}.olean.server", srv_h),
                    format!("{:016x}.olean.private", priv_h)
                ],
                "m": true,
                "i": format!("{:016x}.ilean", ilean_h),
                "rs": format!("{:016x}.ir.sig", ir_sig_h),
                "r": format!("{:016x}.ir", ir_h),
                "c": format!("{:016x}.c", c_h)
            })
        } else {
            for p in [&srv_path, &priv_path, &ir_sig_path, &ir_path] {
                if is_regular_nonempty_file(p) {
                    if let Ok(h) = verify_and_hash_artifact_bytes(p, false, false) {
                        sidecar_writes.push((
                            PathBuf::from(format!("{}.hash", p.display())),
                            format!("{:016x}", h).into_bytes(),
                        ));
                    }
                } else {
                    let _ = fs::remove_file(format!("{}.hash", p.display()));
                }
            }
            serde_json::json!({
                "o": [format!("{:016x}.olean", olean_h)],
                "m": false,
                "i": format!("{:016x}.ilean", ilean_h),
                "c": format!("{:016x}.c", c_h)
            })
        };
    let trace_json = serde_json::json!({
        "synthetic": false,
        "schemaVersion": "2025-09-10",
        "outputs": outputs_json,
        "log": [],
        "inputs": inputs,
        "depHash": format!("{:016x}", dep_hash)
    });
    let trace_path = node.olean_path.with_extension("trace");
    let trace_bytes = serde_json::to_vec(&trace_json)?;
    sidecar_writes.push((trace_path, trace_bytes));
    let pid = std::process::id();
    let seq = crate::pack::next_tmp_id();
    let mut staged_pairs: Vec<(PathBuf, PathBuf)> = Vec::with_capacity(sidecar_writes.len());
    for (dst_p, content) in sidecar_writes {
        let Some(parent) = dst_p.parent() else {
            anyhow::bail!("Sidecar destination `{}` has no parent", dst_p.display());
        };
        fs::create_dir_all(parent)?;
        let fname = dst_p
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("sidecar");
        let tmp_p = parent.join(format!(".turbo_stage_sidecar_{}_{}_{}", pid, seq, fname));
        let write_res: Result<()> = (|| {
            use std::io::Write;
            let mut f = fs::File::create(&tmp_p)?;
            f.write_all(&content)?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                f.set_permissions(fs::Permissions::from_mode(0o644))?;
            }
            f.sync_all()?;
            Ok(())
        })();
        if let Err(e) = write_res {
            let _ = fs::remove_file(&tmp_p);
            for (sp, _) in &staged_pairs {
                let _ = fs::remove_file(sp);
            }
            return Err(e);
        }
        staged_pairs.push((tmp_p, dst_p));
    }
    for (tmp_p, dst_p) in &staged_pairs {
        if let Err(e) = fs::rename(tmp_p, dst_p) {
            for (sp, dp) in &staged_pairs {
                let _ = fs::remove_file(sp);
                let _ = fs::remove_file(dp);
            }
            return Err(e).with_context(|| {
                format!(
                    "Failed to atomically commit sidecar `{}` -> `{}`",
                    tmp_p.display(),
                    dst_p.display()
                )
            });
        }
    }
    Ok(())
}

static PUBLISH_LOCK: OnceLock<Mutex<()>> = OnceLock::new();

fn acquire_publish_flock_mode(
    pkg_root: &Path,
    exclusive: bool,
    preserve_lake: bool,
) -> Result<crate::shm_cache::PublishFlockGuard> {
    crate::shm_cache::acquire_publish_flock(pkg_root, exclusive, preserve_lake).with_context(|| {
        format!(
            "Failed to acquire publication flock for `{}`",
            pkg_root.display()
        )
    })
}

fn acquire_publish_flock(
    pkg_root: &Path,
    preserve_lake: bool,
) -> Result<crate::shm_cache::PublishFlockGuard> {
    acquire_publish_flock_mode(pkg_root, true, preserve_lake)
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
    let _flock_guard = acquire_publish_flock(&node.pkg_root, false)?;
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

    let fmt_rb = |staged_renames: &[(PathBuf, PathBuf)], backups: &[BackupRecord]| -> String {
        rollback_publish_state(node, had_valid_pre_publish_set, staged_renames, backups)
            .err()
            .map(|re| format!("; rollback error: {}", re))
            .unwrap_or_default()
    };

    // Phase 2a: Commit staged files via atomic in-place POSIX rename (`rename` replaces `dst_p` atomically),
    // rolling back and verifying all destinations from `backups` if any rename fails.
    for (stage_p, dst_p) in &staged_renames {
        if let Err(e) = fs::rename(stage_p, dst_p) {
            let sfx = fmt_rb(&staged_renames, &backups);
            return Err(e).with_context(|| {
                format!(
                    "Failed to atomically rename staged artifact `{}` -> `{}`{}",
                    stage_p.display(),
                    dst_p.display(),
                    sfx
                )
            });
        }
    }

    // Phase 2b: Transactionally remove any stale companion artifacts, rolling back if removal fails.
    for stale_p in &stale_to_remove {
        match fs::symlink_metadata(stale_p) {
            Ok(_) => {
                if let Err(e) = fs::remove_file(stale_p) {
                    let sfx = fmt_rb(&staged_renames, &backups);
                    return Err(e).with_context(|| {
                        format!(
                            "Failed to remove stale companion artifact `{}`{}",
                            stale_p.display(),
                            sfx
                        )
                    });
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => {
                let sfx = fmt_rb(&staged_renames, &backups);
                return Err(e).with_context(|| {
                    format!(
                        "Failed to stat stale companion artifact `{}`{}",
                        stale_p.display(),
                        sfx
                    )
                });
            }
        }
    }

    // Phase 3: Re-validate the published destination artifact set before removing backups
    if !validate_materialized_module_artifacts(node) {
        let sfx = fmt_rb(&staged_renames, &backups);
        anyhow::bail!(
            "Post-publish artifact set validation failed for module `{}`{}",
            node.module_name,
            sfx
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

pub(crate) fn run_command_with_timeout(
    cmd: &mut Command,
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
                    for (res, lim) in [
                        (libc::RLIMIT_CORE, 0),
                        (libc::RLIMIT_DATA, 8 * 1024 * 1024 * 1024),
                        (libc::RLIMIT_FSIZE, 512 * 1024 * 1024),
                    ] {
                        let r = libc::rlimit {
                            rlim_cur: lim,
                            rlim_max: lim,
                        };
                        let _ = libc::setrlimit(res, &r);
                    }
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
    let mut poll_iter = 0u32;
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
            let _ = out_handle.join();
            let _ = err_handle.join();
            anyhow::bail!("`lean` command timed out after {}ms", timeout.as_millis());
        }
        let sleep_dur = if poll_iter < 25 {
            std::time::Duration::from_micros(200)
        } else if poll_iter < 50 {
            std::time::Duration::from_millis(1)
        } else {
            std::time::Duration::from_millis(5)
        };
        poll_iter = poll_iter.saturating_add(1);
        std::thread::sleep(sleep_dur);
    }
}

#[cfg(test)]
std::thread_local! {
    static TEST_BWRAP_BIN_OVERRIDE: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

#[cfg(test)]
pub(crate) struct ScopedTestBwrapOverride {
    prev: Option<String>,
}

#[cfg(test)]
impl ScopedTestBwrapOverride {
    pub(crate) fn set(val: impl Into<String>) -> Self {
        let prev = TEST_BWRAP_BIN_OVERRIDE.with(|cell| cell.replace(Some(val.into())));
        Self { prev }
    }

    pub(crate) fn write_fake_bwrap_script(dir: &Path) -> std::io::Result<PathBuf> {
        let path = dir.join("fake_bwrap.sh");
        fs::write(
            &path,
            concat!(
                "#!/usr/bin/env bash\nset -euo pipefail\nENV_ARGS=()\nCHDIR=\"\"\n",
                "while [[ $# -gt 0 ]]; do\n  case \"$1\" in\n",
                "    --unshare-all|--new-session|--die-with-parent) shift ;;\n",
                "    --clearenv) ENV_ARGS=(\"-i\"); shift ;;\n",
                "    --setenv) ENV_ARGS+=(\"$2=$3\"); shift 3 ;;\n",
                "    --dev|--proc|--tmpfs) shift 2 ;;\n",
                "    --ro-bind|--ro-bind-try|--bind) shift 3 ;;\n",
                "    --chdir) CHDIR=\"$2\"; shift 2 ;;\n",
                "    *) break ;;\n  esac\ndone\n",
                "[[ -n \"$CHDIR\" ]] && cd \"$CHDIR\"\nexec env \"${ENV_ARGS[@]}\" \"$@\"\n",
            ),
        )?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = fs::metadata(&path)?.permissions();
            perms.set_mode(0o755);
            fs::set_permissions(&path, perms)?;
        }
        Ok(path)
    }
}

#[cfg(test)]
impl Drop for ScopedTestBwrapOverride {
    fn drop(&mut self) {
        let prev = self.prev.take();
        TEST_BWRAP_BIN_OVERRIDE.with(|cell| {
            *cell.borrow_mut() = prev;
        });
    }
}

pub(crate) fn probe_bwrap_sandbox() -> Option<PathBuf> {
    #[cfg(test)]
    if let Some(test_bwrap) = TEST_BWRAP_BIN_OVERRIDE
        .with(|cell| cell.borrow().clone())
        .or_else(|| std::env::var("TURBO_LEAN_TEST_BWRAP_BIN").ok())
    {
        let trimmed = test_bwrap.trim();
        if trimmed == "__NONE__" || trimmed.is_empty() {
            return None;
        }
        let p = PathBuf::from(trimmed);
        if p.is_file() {
            return Some(p);
        }
        return None;
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

pub(crate) fn validate_untrusted_sandbox_search_paths(
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
        c.args(["--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp"]);
        for sys_p in [
            "/usr",
            "/bin",
            "/lib",
            "/lib64",
            "/etc/ld.so.cache",
            "/etc/localtime",
        ] {
            c.args(["--ro-bind-try", sys_p, sys_p]);
        }
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
    // Lake passes `weakLeanArgs` before `moreLeanArgs`.
    for arg in &node.weak_args {
        cmd.arg(arg);
    }
    for arg in &node.strong_args {
        cmd.arg(arg);
    }
    cmd.arg("-Dwarn.sorry=true")
        .arg("-Ddebug.skipKernelTC=false")
        .arg(&node.src_path)
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

type ModuleCompileOutput = (i64, String, String);

fn compile_single_module_direct(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    lean_path_env: &str,
    ld_library_path_env: &str,
    is_untrusted: bool,
    bwrap_bin: Option<&Path>,
) -> Result<ModuleCompileOutput> {
    let t0 = Instant::now();
    let pid = std::process::id();
    let seq = crate::pack::next_tmp_id();
    let build_root = node.pkg_root.join(".lake/build");
    fs::create_dir_all(&build_root)?;
    let rel_slash = module_name_to_rel_slash(&node.module_name);
    let tmp_dir = build_root.join(format!(
        ".turbo_mod_tmp_{}_{}_{}",
        pid,
        seq,
        rel_slash.replace('/', "_")
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir)?;
    let _tmp_guard = TempDirGuard(tmp_dir.clone());
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
                } else if let Some(n) = Some(v)
                    .filter(|v| is_canonical_nat(v))
                    .and_then(|v| v.parse::<u64>().ok())
                {
                    serde_json::Value::Number(n.into())
                } else {
                    serde_json::Value::String(v.to_string())
                };
                setup_options.insert(k.to_string(), json_v);
            }
        }
    }
    setup_options.insert("warn.sorry".to_string(), serde_json::Value::Bool(true));
    setup_options.insert(
        "debug.skipKernelTC".to_string(),
        serde_json::Value::Bool(false),
    );
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
    let mut cmd = build_module_compile_command(
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
        &mut cmd,
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
    // Match the prefix: `pp.*` options change how the `sorry` term itself prints.
    if stdout_str.contains("declaration uses ") || stderr_str.contains("declaration uses ") {
        anyhow::bail!(
            "Native Lean compilation rejected module `{}` ({}) due to `sorry` axiom usage",
            node.module_name,
            node.src_path.display()
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
    let expected_dig = compute_olean_artifact_set_digest(&node.olean_path)?;
    let dur_ms = t0.elapsed().as_millis() as i64;
    Ok((dur_ms, stdout_str, expected_dig))
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
        let preserve_lake = crate::lake_build::worktree_auto_link_disabled(canon_project_dir)
            || crate::lake_build::worktree_auto_link_disabled(&node.pkg_root);
        let _flock_guard = acquire_publish_flock_mode(&node.pkg_root, false, preserve_lake)?;
        let artifact_files = collect_module_artifact_paths(node);
        let paths: Vec<_> = artifact_files.iter().map(|(_, p)| p.clone()).collect();
        _flock_guard.read_consistent(&paths, || {
            let mut items = Vec::with_capacity(artifact_files.len());
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
            Ok(items)
        })?
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

pub(crate) fn record_verified_dep_source(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    olean_artifact_digest: &str,
    kernel_audited: bool,
    olean_digests: &HashMap<String, String>,
) {
    // Pin the direct imports the `.olean` was elaborated against; skip recording if the
    // source moved on mid-build or a dependency digest is unknown.
    let Some(header) = fs::read_to_string(&node.src_path)
        .ok()
        .filter(|src| blake3::hash(src.as_bytes()).to_hex().as_str() == node.src_blake3)
        .map(|src| parse_header_info(&src))
    else {
        return;
    };
    let direct_imports = node.direct_dag_deps.iter().chain(
        node.external_olean_deps
            .iter()
            .map(|(m, _)| m)
            .filter(|m| header.imports.contains(m)),
    );
    let Some(import_olean_digests) = direct_imports
        .map(|m| Some((m.clone(), olean_digests.get(m)?.clone())))
        .collect::<Option<BTreeMap<_, _>>>()
    else {
        return;
    };
    // Fingerprint only a stable artifact set that still digests to the recorded value.
    let fp = olean_artifact_stat_fingerprint(&node.olean_path);
    let artifact_stat_fingerprint = fp
        .filter(|fp| {
            compute_olean_artifact_set_digest_with_policy(
                &node.olean_path,
                crate::lake_build::worktree_auto_link_disabled(&cfg.root_pkg.pkg_root),
            )
            .is_ok_and(|d| d == olean_artifact_digest)
                && olean_artifact_stat_fingerprint(&node.olean_path).as_ref() == Some(fp)
        })
        .unwrap_or_default();
    let pkg_root = &node.pkg_root;
    let build_dir = pkg_root.join(".lake/build");
    let _ = fs::create_dir_all(&build_dir);
    let manifest_path = build_dir.join(".turbo_verified_sources.json");
    let allowed_axioms = crate::splitter::allowed_axioms();
    let mut manifest: VerifiedDepManifest = fs::read(&manifest_path)
        .ok()
        .and_then(|b| serde_json::from_slice::<VerifiedDepManifest>(&b).ok())
        .filter(|m| {
            m.pkg_name == node.pkg_name
                && m.toolchain == cfg.toolchain
                && m.lean_githash == cfg.lean_githash
                && m.pkg_config_digest == node.pkg_config_digest
                && m.allowed_axioms == allowed_axioms
        })
        .unwrap_or_else(|| VerifiedDepManifest {
            pkg_name: node.pkg_name.clone(),
            toolchain: cfg.toolchain.clone(),
            lean_githash: cfg.lean_githash.clone(),
            pkg_config_digest: node.pkg_config_digest.clone(),
            allowed_axioms,
            modules: BTreeMap::new(),
            cfg: None,
            dep_import_memo: DepImportMemo::default(),
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
            kernel_audited,
            import_olean_digests,
            artifact_stat_fingerprint,
        },
    );
    if let Ok(json_bytes) = serde_json::to_vec(&manifest) {
        let tmp_path = build_dir.join(format!(
            ".turbo_verified_sources.json.tmp.{}.{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let write_ok = (|| -> std::io::Result<()> {
            use std::io::Write;
            let mut f = fs::File::create(&tmp_path)?;
            f.write_all(&json_bytes)?;
            f.sync_all()?;
            Ok(())
        })()
        .is_ok();
        if write_ok {
            let _ = fs::rename(&tmp_path, &manifest_path);
        } else {
            let _ = fs::remove_file(&tmp_path);
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
    _file_hashes_opt: Option<&BTreeMap<String, String>>,
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
    let preserve_project = crate::lake_build::worktree_auto_link_disabled(&canon_dir);
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
    // Opted-out packages must not acquire new build directories either.
    for pkg in std::iter::once(&cfg.root_pkg).chain(&cfg.dep_pkgs) {
        if !preserve_project && !crate::lake_build::worktree_auto_link_disabled(&pkg.pkg_root) {
            fs::create_dir_all(pkg.pkg_root.join(&pkg.build_dir).join(&pkg.lean_lib_dir))?;
            fs::create_dir_all(pkg.pkg_root.join(&pkg.build_dir).join(&pkg.ir_dir))?;
        }
    }
    let (lean_path_env, ld_library_path_env) = build_lean_search_path(&cfg, is_untrusted);
    let bwrap_bin = if is_untrusted {
        probe_bwrap_sandbox()
    } else {
        None
    };
    if is_untrusted {
        if bwrap_bin.is_none() {
            anyhow::bail!(
                "Untrusted module verification requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
            );
        }
        report.bwrap_used = true;
    } else {
        report.bwrap_used = bwrap_bin.is_some();
    }
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
                let d = compute_olean_artifact_set_digest_with_policy(ext_path, preserve_project)?;
                olean_digests.insert(ext_mod.clone(), d);
            }
        }
    }
    // Execute topological waves
    for wave in &dag.waves {
        let mut misses_to_compile: Vec<(String, String)> = Vec::new();
        for mod_name in wave {
            let node = dag.nodes.get(mod_name).expect("wave module in dag");
            let preserve_lake =
                preserve_project || crate::lake_build::worktree_auto_link_disabled(&node.pkg_root);
            let invalidate = || -> Result<()> {
                if !preserve_lake {
                    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
                    let _guard = lock.lock().map_err(|_| {
                        anyhow::anyhow!("Module artifact publication mutex poisoned")
                    })?;
                    let _flock_guard = acquire_publish_flock(&node.pkg_root, false)?;
                    wipe_existing_module_artifacts(node);
                }
                Ok(())
            };
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
                // The invocation's project policy also covers external package roots.
                // Keep cache-hit validation/auditing, but do not erase artifacts or
                // regenerate Lake sidecars when automatic materialization is disabled.
                let cas_restored_dig_opt = {
                    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
                    let _guard = lock.lock().map_err(|_| {
                        anyhow::anyhow!("Module artifact publication mutex poisoned")
                    })?;
                    let _flock_guard =
                        acquire_publish_flock_mode(&node.pkg_root, !preserve_lake, preserve_lake)?;
                    if !preserve_lake {
                        wipe_existing_module_artifacts(node);
                        store.materialize_into_worktree(target_root, &project_name, &outputs)?;
                        if !node.needs_c {
                            let _ = fs::remove_file(&node.c_path);
                        }
                    }
                    let mut paths: Vec<_> = olean_artifact_paths(&node.olean_path)
                        .into_iter()
                        .map(|(_, p)| p)
                        .collect();
                    paths.extend(outputs.iter().map(|e| target_root.join(&e.rel_path)));
                    let restored = _flock_guard.read_consistent(&paths, || {
                        if preserve_lake {
                            crate::db::reuse_worktree_outputs(target_root, &outputs)?;
                        }
                        let hashes_ok = validate_materialized_module_artifacts(node)
                            && outputs
                                .iter()
                                .filter(|e| node.needs_c || e.kind != "c")
                                .all(|entry| {
                                    fs::read(target_root.join(&entry.rel_path)).is_ok_and(|bytes| {
                                        bytes.len() as u64 == entry.size_bytes
                                            && blake3::hash(&bytes).to_hex().as_str()
                                                == entry.blob_hash
                                    })
                                });
                        if hashes_ok {
                            compute_olean_artifact_set_digest_locked(
                                &node.olean_path,
                                Some(&_flock_guard),
                            )
                            .map(Some)
                        } else {
                            Ok(None)
                        }
                    })?;
                    if restored.is_none() && !preserve_lake {
                        wipe_existing_module_artifacts(node);
                    }
                    restored
                };
                if let Some(dig) = cas_restored_dig_opt {
                    if is_untrusted || node.is_root_pkg {
                        let audit_res = crate::zygote::audit_compiled_modules_with_zygote(
                            store,
                            &cfg,
                            std::slice::from_ref(mod_name),
                            &lean_path_env,
                            &[],
                            is_untrusted,
                        );
                        if let Err(audit_err) = audit_res {
                            invalidate()?;
                            return Err(audit_err.context(format!(
                                "In-kernel `.olean` audit rejected materialized CAS hit for module `{}`",
                                mod_name
                            )));
                        }
                    }
                    let post_audit_dig = compute_olean_artifact_set_digest_with_policy(
                        &node.olean_path,
                        preserve_project,
                    )?;
                    if post_audit_dig != dig {
                        invalidate()?;
                        anyhow::bail!(
                            "Artifact digest mutated during `.olean` kernel audit for `{}`",
                            mod_name
                        );
                    }
                    if !preserve_lake {
                        write_lake_module_hashes_and_trace(
                            &cfg,
                            &dag,
                            node,
                            &dig,
                            Some(&post_audit_dig),
                            true,
                        )?;
                        if !is_untrusted {
                            record_verified_dep_source(
                                &cfg,
                                node,
                                &dig,
                                node.is_root_pkg,
                                &olean_digests,
                            );
                        }
                    }
                    olean_digests.insert(mod_name.clone(), dig);
                    report.modules_cached += 1;
                    report.cached_modules.push(mod_name.clone());
                    continue;
                }
                anyhow::ensure!(!preserve_lake, "Worktree opt-out prevents rebuilding invalid CAS outputs for `{mod_name}`; build with Lake first");
            } else {
                anyhow::ensure!(!preserve_lake, "Worktree opt-out prevents compiling uncached module `{mod_name}`; build with Lake first");
                invalidate()?;
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
        // Compile all cache-miss modules in the current wave in parallel (bounded by `max_jobs`).
        // Fast path: when `workers == 1`, execute directly on the calling thread without thread-spawn overhead.
        let workers = max_jobs.min(misses_to_compile.len()).max(1);
        let dag_ref = &dag;
        let cfg_ref = &cfg;
        let lp_ref = lean_path_env.as_str();
        let ld_ref = ld_library_path_env.as_str();
        let bwrap_ref = bwrap_bin.as_deref();
        let mut ordered_results: Vec<(usize, Result<ModuleCompileOutput>)> = if workers == 1 {
            misses_to_compile
                .iter()
                .enumerate()
                .map(|(i, (mod_name, _))| {
                    let node = dag_ref.nodes.get(mod_name).expect("node in dag");
                    let res = compile_single_module_direct(
                        cfg_ref,
                        node,
                        lp_ref,
                        ld_ref,
                        is_untrusted,
                        bwrap_ref,
                    );
                    (i, res)
                })
                .collect()
        } else {
            let next_idx = std::sync::atomic::AtomicUsize::new(0);
            let misses_ref = &misses_to_compile;
            std::thread::scope(|s| {
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
            })
        };
        ordered_results.sort_by_key(|(i, _)| *i);
        let mut compiled_wave_ok: Vec<(usize, i64, String, String)> =
            Vec::with_capacity(ordered_results.len());
        let mut first_compile_err: Option<anyhow::Error> = None;
        for (i, res) in ordered_results {
            match res {
                Ok((dur_ms, stdout_str, dig)) => {
                    compiled_wave_ok.push((i, dur_ms, stdout_str, dig));
                }
                Err(e) => {
                    if first_compile_err.is_none() {
                        first_compile_err = Some(e);
                    }
                }
            }
        }
        if let Some(err) = first_compile_err {
            let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
            if let Ok(_guard) = lock.lock() {
                for (i, _, _, _) in &compiled_wave_ok {
                    let (ref mod_name, _) = misses_to_compile[*i];
                    if let Some(node) = dag.nodes.get(mod_name) {
                        if let Ok(_flock) = acquire_publish_flock(&node.pkg_root, false) {
                            wipe_existing_module_artifacts(node);
                        }
                    }
                }
            }
            return Err(err);
        }
        let wave_audit_mod_names: Vec<String> = compiled_wave_ok
            .iter()
            .filter_map(|(i, _, _, _)| {
                let mod_name = &misses_to_compile[*i].0;
                let node = dag.nodes.get(mod_name)?;
                if is_untrusted || node.is_root_pkg {
                    Some(mod_name.clone())
                } else {
                    None
                }
            })
            .collect();
        if let Err(audit_err) = crate::zygote::audit_compiled_modules_with_zygote(
            store,
            &cfg,
            &wave_audit_mod_names,
            &lean_path_env,
            &[],
            is_untrusted,
        ) {
            let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
            if let Ok(_guard) = lock.lock() {
                for (i, _, _, _) in &compiled_wave_ok {
                    let (ref mod_name, _) = misses_to_compile[*i];
                    if let Some(node) = dag.nodes.get(mod_name) {
                        if let Ok(_flock) = acquire_publish_flock(&node.pkg_root, false) {
                            wipe_existing_module_artifacts(node);
                        }
                    }
                }
            }
            return Err(audit_err);
        }
        for (i, dur_ms, stdout_str, dig) in compiled_wave_ok {
            let (ref mod_name, ref mod_key) = misses_to_compile[i];
            if !json_output && !stdout_str.trim().is_empty() {
                print!("{}", stdout_str);
            }
            let node = dag.nodes.get(mod_name).expect("node in dag");
            let post_audit_dig =
                compute_olean_artifact_set_digest_with_policy(&node.olean_path, preserve_project)?;
            if post_audit_dig != dig {
                let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
                if let Ok(_guard) = lock.lock() {
                    if let Ok(_flock) = acquire_publish_flock(&node.pkg_root, false) {
                        wipe_existing_module_artifacts(node);
                    }
                }
                anyhow::bail!(
                    "Artifact digest mutated during `.olean` kernel audit for `{}`",
                    mod_name
                );
            }
            write_lake_module_hashes_and_trace(
                &cfg,
                &dag,
                node,
                &dig,
                Some(&post_audit_dig),
                true,
            )?;
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
            if !is_untrusted {
                record_verified_dep_source(&cfg, node, &dig, node.is_root_pkg, &olean_digests);
            }
            olean_digests.insert(mod_name.clone(), dig);
            report.modules_compiled += 1;
            report.compiled_modules.push(mod_name.clone());
        }
    }
    Ok(report)
}
#[cfg(test)]
pub(crate) static BWRAP_TEST_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
#[cfg(test)]
mod tests {
    use super::*;
    /// Serialize native builds with tests that toggle `TURBO_LEAN_NO_WORKTREE_LINK`.
    fn native_build_env_guard() -> std::sync::MutexGuard<'static, ()> {
        crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner())
    }
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
    #[cfg(unix)]
    #[test]
    fn test_publication_process_child() -> Result<()> {
        let Some(root) = std::env::var_os("TURBO_TEST_PUBLISH_ROOT").map(PathBuf::from) else {
            return Ok(());
        };
        let mode = std::env::var("TURBO_TEST_PUBLISH_MODE")?;
        let node: ModuleNode = serde_json::from_slice(&fs::read(root.join("node.json"))?)?;
        fs::write(root.join("starting"), b"")?;
        if mode == "legacy" {
            let _legacy = crate::shm_cache::acquire_flock(
                &node.pkg_root.join(".lake/build/.turbo_publish.lock"),
                true,
                false,
            )?;
            fs::write(&node.olean_path, b"new olean")?;
            fs::write(&node.ilean_path, b"new ilean")?;
        } else if mode == "reader" {
            let digest = compute_olean_artifact_set_digest(&node.olean_path)?;
            assert_eq!(digest, fs::read_to_string(root.join("expected"))?);
        } else {
            let tmp = root.join("staged");
            publish_module_artifacts_atomic(
                &tmp,
                &node,
                &tmp.join("P.olean"),
                &tmp.join("P.ilean"),
                &tmp.join("P.olean.server"),
                &tmp.join("P.olean.private"),
                &tmp.join("P.ir"),
                &tmp.join("P.ir.sig"),
                &tmp.join("P.c"),
            )?;
        }
        fs::write(root.join("done"), b"")?;
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_reader_rejects_legacy_first_publication_mid_digest() -> Result<()> {
        use crate::worktree_test_support::{LakeTree, TestChild};
        let tree = LakeTree::new("legacy_race", &[("P/A.lean", "def value : Nat := 1\n")])?;
        let cfg = resolve_project_config(&tree.project)?;
        let dag = build_module_dag(&cfg, &[])?;
        let node = &dag.nodes["P.A"];
        tree.opt_out()?;
        let legacy = tree.project.join(".lake/build/.turbo_publish.lock");
        if legacy.exists() {
            fs::remove_file(&legacy)?;
        }
        fs::write(tree.root.join("node.json"), serde_json::to_vec(node)?)?;
        // Reader starts first and consumes the old .olean. An old binary then
        // creates only the legacy lock and replaces both outputs before .ilean.
        let guard = acquire_publish_flock_mode(&tree.project, false, true)?;
        let err = read_olean_artifact_set_digest(&node.olean_path, Some(&guard), |path| {
            let bytes = fs::read(path)?;
            if path == node.olean_path {
                let mut command =
                    TestChild::command("module_builder::tests::test_publication_process_child")?;
                command
                    .env("TURBO_TEST_PUBLISH_ROOT", &tree.root)
                    .env("TURBO_TEST_PUBLISH_MODE", "legacy");
                let mut child = TestChild::spawn(&mut command)?;
                child.finish(&tree.root.join("done"))?;
            }
            Ok(bytes)
        })
        .unwrap_err()
        .to_string();
        assert!(
            err.contains("changed during") || err.contains("appeared or changed"),
            "{err}"
        );
        assert_eq!(fs::read(&node.olean_path)?, b"new olean");
        drop(guard);
        // A fresh reader locks the now-existing legacy inode and succeeds.
        compute_olean_artifact_set_digest(&node.olean_path)?;
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_publication_process_contention_across_cache_homes_and_legacy() -> Result<()> {
        use crate::worktree_test_support::{LakeTree, TestChild};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::new(
            "publish_contention",
            &[("P/A.lean", "def value : Nat := 1\n")],
        )?;
        let cfg = resolve_project_config(&tree.project)?;
        let dag = build_module_dag(&cfg, &[])?;
        let node = &dag.nodes["P.A"];
        fs::write(tree.root.join("node.json"), serde_json::to_vec(node)?)?;
        fs::create_dir_all(tree.root.join("staged"))?;
        // The parent and child use different HOME and TURBO_LEAN_HOME values. Exercise
        // both lock directions, first publication without a legacy file, and old holders.
        for (mode, legacy_holder, optout, missing_legacy) in [
            ("publisher", false, true, true),
            ("publisher", false, false, false),
            ("reader", false, false, false),
            ("reader", false, true, false),
            ("publisher", true, false, false),
            ("reader", true, true, false),
        ] {
            for name in ["starting", "done"] {
                let _ = fs::remove_file(tree.root.join(name));
            }
            if missing_legacy {
                let _ = fs::remove_file(tree.project.join(".lake/build/.turbo_publish.lock"));
            }
            if optout {
                tree.opt_out()?;
            } else {
                let _ = fs::remove_file(tree.project.join("turbo-lean.toml"));
            }
            let legacy = if legacy_holder {
                crate::shm_cache::acquire_flock(
                    &tree.project.join(".lake/build/.turbo_publish.lock"),
                    true,
                    false,
                )?
            } else {
                None
            };
            let current = if legacy_holder {
                None
            } else {
                Some(acquire_publish_flock_mode(
                    &tree.project,
                    mode == "reader",
                    optout,
                )?)
            };
            let mut command =
                TestChild::command("module_builder::tests::test_publication_process_child")?;
            command
                .env("TURBO_TEST_PUBLISH_ROOT", &tree.root)
                .env("TURBO_TEST_PUBLISH_MODE", mode)
                .env("TURBO_LEAN_HOME", tree.root.join("other-cache"))
                .env("HOME", tree.root.join("other-home"))
                // Only the reader opts out; its competing publisher must still create the
                // legacy lock once the directory reader has released it.
                .env("TURBO_LEAN_NO_WORKTREE_LINK", "0");
            if mode == "publisher" && optout {
                fs::remove_file(tree.project.join("turbo-lean.toml"))?;
            }
            if mode == "publisher" {
                fs::write(tree.root.join("staged/P.olean"), b"new olean generation")?;
                fs::write(tree.root.join("staged/P.ilean"), b"new ilean generation")?;
            }
            let mut child = TestChild::spawn(&mut command)?;
            child.wait_for(&tree.root.join("starting"))?;
            child.assert_blocked(&tree.root.join("done"))?;
            if mode == "reader" {
                // Finish a multi-file transaction while the real digest reader is blocked.
                fs::write(&node.olean_path, b"committed olean")?;
                fs::write(&node.ilean_path, b"committed ilean")?;
                fs::write(
                    tree.root.join("expected"),
                    compute_olean_artifact_set_digest_locked(&node.olean_path, current.as_ref())?,
                )?;
            }
            drop((legacy, current));
            child.finish(&tree.root.join("done"))?;
            if mode == "publisher" {
                assert_eq!(fs::read(&node.olean_path)?, b"new olean generation");
                assert_eq!(fs::read(&node.ilean_path)?, b"new ilean generation");
            }
        }
        Ok(())
    }

    #[test]
    fn test_parse_lakefile_lean_namespaced_static_facet() {
        let dir = make_temp_test_dir("namespaced_static_facet");
        let path = dir.join("lakefile.lean");
        fs::write(
            &path,
            r#"import Lake
open Lake DSL
package demo
lean_lib spec_cabi where
  roots := #[`Demo]
  defaultFacets := #[LeanLib.staticFacet]
"#,
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &path, true).unwrap();
        assert_eq!(pkg.libs.len(), 1);
        assert_eq!(pkg.libs[0].default_facets, vec!["LeanLib.staticFacet"]);
        fs::remove_dir_all(dir).unwrap();
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
import all Demo.Internal -- space-separated
meta
import
Demo.MetaMod
public import Demo.Shared
import all Demo.Shared
import Demo.A
import «Demo».«B»
@[expose] public section
namespace Demo
@[inline, export demo_c_symbol]
public def f (x : Nat) : Nat := x
";
        let info = parse_header_info(src);
        assert!(info.header_error.is_none());
        assert!(info.is_module);
        assert!(info.has_prelude);
        assert!(info.has_c_export);
        assert_eq!(
            info.imports,
            vec![
                "Mathlib.Logic.Basic".to_string(),
                "Demo.Internal".to_string(),
                "Demo.MetaMod".to_string(),
                "Demo.Shared".to_string(),
                "Demo.A".to_string(),
                "Demo.B".to_string()
            ]
        );
        let shared_specs: Vec<&ParsedImport> = info
            .import_specs
            .iter()
            .filter(|s| s.module == "Demo.Shared")
            .collect();
        assert_eq!(shared_specs.len(), 2);
        assert!(shared_specs[0].is_exported && !shared_specs[0].import_all);
        assert!(!shared_specs[1].is_exported && shared_specs[1].import_all);
    }

    #[test]
    fn test_parse_header_info_differential_against_lean_deps_json() {
        let dir = make_temp_test_dir("diff_header_deps_json");
        let (lean_bin, _, _, _) = resolve_toolchain_compiler(&dir, "leanprover/lean4:v4.35.0")
            .expect("resolve Lean v4.35.0 binary");
        let cases: &[(&str, &str)] = &[
            ("plain_default", "import Std.Data.HashMap\ndef x : Nat := 1\n"),
            ("module_no_prelude", "module\npublic import Std\nmeta import Lean.Elab\nimport all Init.Data.Array\npublic section\n"),
            ("module_prelude_dup_flags", "module\nprelude\npublic import Foo.Bar\nimport all Foo.Bar\nmeta import Foo.Bar\n"),
            ("guillemets_and_multiline", "module\n  /- nested /- block -/ -/\n  prelude\n  public\n  meta\n  import «Foo».«Bar Baz».Qux'!\n"),
            ("stops_at_doc_comment", "/-- module doc stops header -/\nimport IgnoredAfterDoc\n"),
            ("stops_at_semicolon", "import Foo.A; import IgnoredAfterSemi\n"),
            ("concat_module_prefix", "moduleFoo\n"),
            ("char_quote_in_body", "import Foo.A\ndef quoteChar : Char := '\"' -- import Fake.InComment\n"),
            ("stops_at_tab_after_import_kw", "import\tFoo.A\n"),
            ("err_tab_after_all", "module\nprelude\nimport all\tFoo.A\n"),
            ("err_modifier_without_module", "public import Foo.A\n"),
            ("err_unterminated_comment", "/- unterminated\nimport Foo.A\n"),
            ("err_missing_ident", "import -- nothing\n"),
            ("err_public_import_all", "module\nprelude\npublic import all Foo.A\n"),
        ];

        for (name, content) in cases {
            let file_path = dir.join(format!("{}.lean", name));
            fs::write(&file_path, content).unwrap();
            let info = parse_header_info(content);
            let out = Command::new(&lean_bin)
                .arg("--deps-json")
                .arg(&file_path)
                .output()
                .unwrap();
            assert!(out.status.success(), "lean --deps-json failed for {}", name);
            let parsed_json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
            let entry = &parsed_json["imports"][0];
            let lean_errs = entry["errors"].as_array().cloned().unwrap_or_default();
            if *name == "err_public_import_all" {
                // `ParseImportsFast` defers `public import all` rejection to `Lean.Parser.Module.parseHeader`
                assert!(
                    info.header_error.is_some(),
                    "expected header_error for {}",
                    name
                );
                continue;
            }
            if !lean_errs.is_empty() {
                assert!(
                    info.header_error.is_some(),
                    "expected header_error for {} matching lean --deps-json errors {:?}",
                    name,
                    lean_errs
                );
            } else {
                assert!(
                    info.header_error.is_none(),
                    "unexpected header_error {:?} for {}",
                    info.header_error,
                    name
                );
                let res = &entry["result"];
                assert_eq!(
                    info.is_module,
                    res["isModule"].as_bool().unwrap(),
                    "isModule mismatch for {}",
                    name
                );
                let expected_specs: Vec<ParsedImport> = res["imports"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|imp| ParsedImport {
                        module: imp["module"].as_str().unwrap().to_string(),
                        is_exported: imp["isExported"].as_bool().unwrap(),
                        is_meta: imp["isMeta"].as_bool().unwrap(),
                        import_all: imp["importAll"].as_bool().unwrap(),
                    })
                    .collect();
                assert_eq!(
                    info.import_specs, expected_specs,
                    "import_specs mismatch vs lean --deps-json for {}",
                    name
                );
            }
        }
        let _ = fs::remove_dir_all(dir);
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
    fn test_computed_lean_options_mathlib_lakefile() {
        // Mathlib @ 0df444a3 binds `leanOptions` through `abbrev`s built with `++` and a
        // `weak.`-prefix `map`, which the literal-only parser used to reject.
        let dir = make_temp_test_dir("mathlib_opts");
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            include_str!("../tests/fixtures/mathlib-0df444a3-lakefile.lean"),
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
        let lib = |name: &str| {
            pkg.libs
                .iter()
                .find(|l| l.name == name)
                .unwrap_or_else(|| panic!("missing lean_lib {name}"))
                .lean_options
                .clone()
        };
        let expected: BTreeMap<String, String> = [
            ("pp.unicode.fun", "true"),
            ("autoImplicit", "false"),
            ("maxSynthPendingDepth", "3"),
            ("weak.linter.mathlibStandardSet", "true"),
            ("weak.linter.style.header", "true"),
            ("weak.linter.checkInitImports", "true"),
            ("weak.linter.allScriptsDocumented", "true"),
            ("weak.linter.pythonStyle", "true"),
            ("weak.linter.style.longFile", "1500"),
        ]
        .into_iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect();
        assert_eq!(lib("Mathlib"), expected);
        assert_eq!(lib("Archive"), expected);
        assert_eq!(lib("Counterexamples"), expected);
        assert_eq!(
            lib("MathlibTest"),
            BTreeMap::from([("pp.mvars.anonymous".to_string(), "false".to_string())])
        );
        // turbo-lean's own proofs package (CI builds it) uses `«»` names, including on
        // `require`; it must keep parsing.
        let own = dir.join("own-lakefile.lean");
        fs::write(&own, include_str!("../../../lean/lakefile.lean")).unwrap();
        let own_pkg = parse_lakefile_lean(&dir, &own, true).unwrap();
        assert_eq!((own_pkg.libs.len(), own_pkg.exes.len()), (3, 4));
        // `Cache.+` / `MathlibTest.+` are submodule globs, not modules named `+`.
        let globs = |name: &str| {
            pkg.libs
                .iter()
                .find(|l| l.name == name)
                .unwrap()
                .globs
                .clone()
        };
        assert_eq!(
            globs("Cache"),
            vec![GlobSpec::Submodules("Cache".to_string())]
        );
        assert_eq!(
            globs("MathlibTest"),
            vec![GlobSpec::Submodules("MathlibTest".to_string())]
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_computed_lean_options_fail_closed() {
        let defs = collect_lakefile_abbrevs(
            "abbrev a := b\nabbrev b := a\nabbrev xs : Array LeanOption := #[⟨`x, true⟩]\n",
        );
        // Cyclic identifiers are detected instead of looping.
        let err = resolve_lean_options_expr("a", &defs, usize::MAX)
            .unwrap_err()
            .to_string();
        // Under sequential elaboration a cycle is a forward reference.
        assert!(
            err.contains("Cyclic") || err.contains("before its declaration"),
            "{err}"
        );
        // Self-referential appends and wide diamonds resolve in linear time (memoised).
        let selfref = collect_lakefile_abbrevs(
            "abbrev a := a ++ a ++ a ++ a
",
        );
        assert!(resolve_lean_options_expr("a", &selfref, usize::MAX).is_err());
        let wide = |n: usize| {
            (0..32)
                .map(|_| format!("a{n}"))
                .collect::<Vec<_>>()
                .join(" ++ ")
        };
        let mut src = "abbrev a0 : Array LeanOption := #[⟨`x, true⟩]
"
        .to_string();
        for n in 1..=8 {
            src.push_str(&format!(
                "abbrev a{n} : Array LeanOption := {}
",
                wide(n - 1)
            ));
        }
        let diamond = collect_lakefile_abbrevs(&src);
        let start = std::time::Instant::now();
        assert_eq!(
            resolve_lean_options_expr("a8", &diamond, usize::MAX).unwrap(),
            BTreeMap::from([("x".to_string(), "true".to_string())])
        );
        assert!(start.elapsed() < std::time::Duration::from_secs(2));
        // Unknown identifiers and other computations are still rejected.
        for expr in [
            "missing",
            "xs.filter fun s ↦ true",
            "xs.map fun s ↦ { s with name := `strong ++ s.name }",
            "xs.map fun s ↦ { s with value := true }",
            "if cond then xs else #[]",
            // Values must be literals, not identifiers passed through as `-Dk=ident`.
            "#[⟨`maxHeartbeats, someIdent⟩]",
            "#[⟨`x, .ofBool 3⟩]",
            "#[⟨`x, .ofString bare⟩]",
            "#[LeanOption.mk `x someIdent]",
        ] {
            let err = resolve_lean_options_expr(expr, &defs, usize::MAX)
                .unwrap_err()
                .to_string();
            assert!(err.contains("Unsupported"), "{expr}: {err}");
        }
        // Literal, append, parenthesised and weak-prefix forms resolve; later entries win.
        let got = resolve_lean_options_expr(
            "(xs) ++ #[⟨`x, false⟩, ⟨`n, .ofNat 7⟩, ⟨`s, .ofString \"hi\"⟩] ++ xs.map fun s => { s with name := `weak ++ s.name }",
            &defs,
            usize::MAX,
        )
        .unwrap();
        assert_eq!(
            got,
            BTreeMap::from([
                ("x".to_string(), "false".to_string()),
                ("n".to_string(), "7".to_string()),
                ("s".to_string(), "hi".to_string()),
                ("weak.x".to_string(), "true".to_string()),
            ])
        );
    }

    #[test]
    fn test_lakefile_toml_lean_options_fail_closed() {
        // Gemini r7: multi-line TOML strings, string values that setup.json would re-read as a
        // bool or a number, and quoted dotted keys.
        let dir = make_temp_test_dir("toml_opts");
        let tf = dir.join("lakefile.toml");
        let parse = |src: &str| {
            fs::write(&tf, src).unwrap();
            parse_lakefile_toml(&dir, &tf, false)
        };
        for bad in [
            "name = \"demo\"\nleanOptions = { autoImplicit = false }\ndescription = \"\"\"\nleanOptions = { autoImplicit = true }\n# \"\"\"\n[[lean_lib]]\nname = \"Demo\"\n",
            "name = \"demo\"\n[leanOptions]\nweak.linter.myStr = \"true\"\n",
            "name = \"demo\"\n[leanOptions]\nweak.linter.myStr = \"1500\"\n",
            "name = \"demo\"\n[leanOptions]\n\"weak.linter.myStr\" = \"x\"\n",
        ] {
            assert!(parse(bad).is_err(), "{bad}");
        }
        let ok = parse("name = \"demo\"\n[leanOptions]\nweak.linter.style.longFile = 1500\n\"autoImplicit\" = false\n").unwrap();
        // Astra r10: TOML escapes decode (`α`) or fail; explicit empty selections fail.
        let esc = parse("name = \"demo\"\nsrcDir = \"src/\\u03b1\"\n").unwrap();
        assert_eq!(esc.src_dir, PathBuf::from("src/α"));
        assert!(parse("name = \"demo\"\nsrcDir = \"src/\\q\"\n").is_err());
        assert!(parse("name = \"demo\"\n[[lean_lib]]\nname = \"Demo\"\nglobs = []\n").is_err());
        assert!(parse("name = \"demo\"\n[[lean_lib]]\nname = \"Demo\"\nroots = []\n").is_err());
        let tools = parse(
            "name = \"demo\"\n[[lean_lib]]\nname = \"Tools\"\nroots = []\nglobs = [\"Tools.+\"]\n",
        )
        .unwrap();
        assert_eq!(
            tools.libs[0].globs,
            vec![GlobSpec::Submodules("Tools".to_string())]
        );
        assert_eq!(
            ok.lean_options,
            BTreeMap::from([
                ("autoImplicit".to_string(), "false".to_string()),
                ("weak.linter.style.longFile".to_string(), "1500".to_string()),
            ])
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_lake_init_templates_and_module_resolution_follow_lake() {
        // Gemini r9: `lake init demo std.lean` output, `«»` in name literals.
        let dir = make_temp_test_dir("lake_init_resolution");
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\n\npackage \"demo\" where\n  version := v!\"0.1.0\"\n\nlean_lib «Demo» where\n  -- add library configuration options here\n\n@[default_target]\nlean_exe \"demo\" where\n  root := `Main\n",
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, true).unwrap();
        assert_eq!(pkg.name, "demo");
        assert_eq!(pkg.libs[0].name, "Demo");
        assert_eq!(pkg.exes[0].name, "demo");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage «p» where\n  defaultTargets := #[`«demo-exe»]\nlean_exe «demo-exe» where\n  root := `Main\n",
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, true).unwrap();
        assert_eq!(pkg.default_targets, vec!["demo-exe".to_string()]);
        let _ = fs::remove_dir_all(&dir);

        // Module-to-target resolution follows Lake's `findTargetModule?`.
        let dir = make_temp_test_dir("lake_resolution");
        let tf = dir.join("lakefile.toml");
        let touch = |rel: &str| {
            let f = dir.join(rel);
            fs::create_dir_all(f.parent().unwrap()).unwrap();
            fs::write(f, "").unwrap();
        };
        for f in [
            "Demo.lean",
            "Main.lean",
            "Guest.lean",
            "Tools.lean",
            "Tools/Helper.lean",
            "Parent.lean",
            "Parent/Child/Leaf.lean",
        ] {
            touch(f);
        }
        let target = |toml: &str, module: &str| {
            fs::write(&tf, toml).unwrap();
            let pkg = parse_lakefile_toml(&dir, &tf, true).unwrap();
            resolve_module_in_package(&pkg, true, module).map(|m| m.target_name)
        };
        // An executable's root belongs to the executable, not to a library sharing srcDir.
        let std_toml = "name = \"demo\"\ndefaultTargets = [\"demo\"]\n[[lean_lib]]\nname = \"Demo\"\n[[lean_exe]]\nname = \"demo\"\nroot = \"Main\"\n";
        assert_eq!(target(std_toml, "Main").as_deref(), Some("demo"));
        assert_eq!(target(std_toml, "Demo").as_deref(), Some("Demo"));
        // `roots = []` + `globs = ["Tools.+"]`: submodules belong to that library, and
        // `Tools` itself is no library's module.
        let tools = "name = \"Guest\"\n[[lean_lib]]\nname = \"Guest\"\n[[lean_lib]]\nname = \"HelperLib\"\nroots = []\nglobs = [\"Tools.+\"]\n";
        assert_eq!(target(tools, "Tools.Helper").as_deref(), Some("HelperLib"));
        assert_eq!(target(tools, "Tools"), None);
        // Later libraries win (`findSomeRev?`).
        let nested = "name = \"P\"\n[[lean_lib]]\nname = \"Parent\"\n[[lean_lib]]\nname = \"Parent.Child\"\n";
        assert_eq!(
            target(nested, "Parent.Child.Leaf").as_deref(),
            Some("Parent.Child")
        );
        assert_eq!(target(nested, "Parent").as_deref(), Some("Parent"));
        // Astra r12: a root claims its subtree only if a glob selects the root itself.
        touch("Parent/Other.lean");
        touch("Parent/Child.lean");
        let selective = "name = \"P\"\n[[lean_lib]]\nname = \"Parent\"\n[[lean_lib]]\nname = \"Selected\"\nroots = [\"Parent\"]\nglobs = [\"Parent.Child\"]\n";
        assert_eq!(target(selective, "Parent.Other").as_deref(), Some("Parent"));
        assert_eq!(
            target(selective, "Parent.Child").as_deref(),
            Some("Selected")
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_lakefile_lexical_guard_rejects_desync_syntax() {
        let dir = make_temp_test_dir("lakefile_lexical_guard");
        let lf = dir.join("lakefile.lean");
        let parse = |src: &str, root: bool| {
            fs::write(&lf, src).unwrap();
            parse_lakefile_lean(&dir, &lf, root)
        };
        let lib = "@[default_target]\nlean_lib Demo where\n  leanOptions := opts\n";
        let opts = "abbrev opts : Array LeanOption := #[⟨`autoImplicit, false⟩]\n";
        // Gemini r5, each verified against real Lake: guillemets that open a fake comment or
        // string, raw strings, interpolation braces holding comments, brace configs, `;`,
        // guillemet field names, `buildType`, duplicate fields, `run_io`.
        let cases = [
            "import Lake\nopen Lake DSL\n\npackage «demo/-»\n\n#eval IO.println \"PWNED\"\nmacro_rules | `(#[⟨`autoImplicit, false⟩]) => `(#[⟨`warn.sorry, false⟩])\n\n-- -/\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n".to_string(),
            format!("import Lake\nopen Lake DSL\n{opts}def n1 : Lean.Name := `«\"» #eval IO.println \"EXEC\" def n2 : Lean.Name := `«\"»\npackage demo\n{lib}"),
            format!("import Lake\nopen Lake DSL\n{opts}def s1 : String := r#\"\\\"# #eval IO.println r#\"RAW\"# def s2 : String := r#\"\"\"#\npackage demo\n{lib}"),
            format!("import Lake\nopen Lake DSL\n{opts}def s1 : String := s!\"{{ /- \"{{ -/ 0 }}\" #eval IO.println \"INTERP\" def s2 : String := s!\"{{ /- \" -/ 0 }}\"\npackage demo\n{lib}"),
            "import Lake\nopen Lake DSL\n\npackage demo { leanOptions := #[⟨`autoImplicit, false⟩] }\n\n@[default_target]\nlean_lib Demo { leanOptions := #[⟨`warn.sorry, false⟩] }\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  libName := \"a\"; moreLeanArgs := #[\"-Dwarn.sorry=false\"]\n".to_string(),
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  «leanOptions» := #[⟨`warn.sorry, false⟩]\n".to_string(),
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  buildType := .debug\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n  leanOptions := #[]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo where\n  description := run_io do\n    IO.println \"RUN_IO\"\n    return \"desc\"\n  leanOptions := #[⟨`autoImplicit, false⟩]\n\n@[default_target]\nlean_lib Demo\n".to_string(),
            format!("import Lake\nopen Lake DSL\n{opts}def c : Char := '\"' #eval IO.println \"CHAR\"\npackage demo\n{lib}"),
            format!("import Lake\nopen Lake DSL\n{opts}def inλ : Nat := 1\npackage demo\n{lib}"),
        ];
        for src in &cases {
            for root in [false, true] {
                assert!(parse(src, root).is_err(), "root={root}: {src}");
            }
        }
        // Gemini r6: `<--` and `/--/` comment desyncs, `!run_io` / `!r#"` after a non-word char,
        // `run_io` inside string braces, header braces without a space, `toLeanConfig`,
        // indented metaprogramming, `#[..] ++ #[..]` argument arrays.
        let r6 = [
            "import Lake\nopen Lake DSL\n\npackage demo where\n  description := (fun _ => \"ok\") (`(tactic| rw [<-- h]) : Lean.MacroM _) #eval IO.println \"x\" /-\n  ])) -/\n\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n".to_string(),
            "import Lake\nopen Lake DSL\n\n/--/\n-- -/ def hidden : Unit := () #eval IO.println \"x\"\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo where\n  preferReleaseBuild := !run_io do\n    IO.println \"x\"\n    return false\n\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n".to_string(),
            format!("import Lake\nopen Lake DSL\n{opts}def b1 : Bool := !r#\"\\\"#.isEmpty #eval IO.println \"x\" def b2 : Bool := !r#\"\"\"#.isEmpty\npackage demo\n{lib}"),
            format!("import Lake\nopen Lake DSL\n{opts}def payload : IO String := pure \"h\"\npackage demo where\n  description := s!\"{{run_io payload}}\"\n{lib}"),
            "import Lake\nopen Lake DSL\n\npackage demo{leanOptions:=#[⟨`warn.sorry,false⟩]}\n\n@[default_target]\nlean_lib Demo\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  toLeanConfig := { leanOptions := #[⟨`autoImplicit, false⟩] }\n".to_string(),
            "import Lake\nopen Lake DSL\n\n  local notation \"#[]\" => #[\"-DautoImplicit=true\"]\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  moreLeanArgs := #[]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  moreLeanArgs := #[\"-DautoImplicit=false\"] ++ #[\"-DautoImplicit=true\"]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  moreLeanArgs := #[\"-DautoImplicit=\\x66alse\"]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target] lean_lib«Demo» where\n  moreLeanArgs := #[]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib\n  Demo where\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`sat.solver, \"./evil.sh\"⟩]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`maxHeartbeats, 18446744073709551616⟩]\n".to_string(),
        ];
        for src in &r6 {
            for root in [false, true] {
                assert!(parse(src, root).is_err(), "root={root}: {src}");
            }
        }
        for bad in [
            "-Dsat.solver=./evil.sh",
            "-Dtrace.profiler.output=/tmp/x.json",
            "-Ddebug.byAsSorry=true",
            "-Dweak.debug.proofAsSorry=true",
        ] {
            assert!(!is_allowed_lean_arg(bad), "{bad}");
        }
        for ok in [
            "-Dweak.linter.style.longFile=1500",
            "-Dexperimental.module=true",
            "-DwarningAsError=false",
        ] {
            assert!(is_allowed_lean_arg(ok), "{ok}");
        }
        // Gemini r7 / Astra r9: `\/-` and `//-` openers, `lo...r#"` dotted words, indented and
        // inline-driver targets, whitespace-only multi-line values, shadowable `FilePath.mk`,
        // bare names and `++` in name arrays.
        let r9 = [
            "import Lake\nopen Lake DSL\n\npackage demo where\n  preferReleaseBuild := (fun _ => false) (True \\/- -1 < (0 : Int))\n  leanOptions := #[⟨`autoImplicit, false⟩]\n  buildArchive := (fun _ => \"x\") (True -- -/\n  )\n\n@[default_target]\nlean_lib Demo\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo where\n  preferReleaseBuild := (fun lo => (lo...r#\"\\\"#.length).lower == 99) 0\n  leanOptions := #[⟨`autoImplicit, false⟩]\n  buildArchive := (fun lo => (lo...r#\"\"\"#.length).lower.repr) 0\n\n@[default_target]\nlean_lib Demo\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo where\n  defaultTargets := #[`Demo]\nopen Lake\n\n@[default_target]\n  lean_lib Demo where\n    moreLeanArgs := #[\"-DautoImplicit=false\"]\n".to_string(),
            "import Lake\nopen Lake DSL\npackage demo where\n  srcDir := \"\n  \"\n@[default_target]\nlean_lib Demo\n".to_string(),
            "import Lake\nopen System Lake DSL\ndef FilePath.mk (_ : String) : System.FilePath := \"actual\"\npackage demo where\n  srcDir := FilePath.mk \"wrong\"\n@[default_target]\nlean_lib Demo\n".to_string(),
            "import Lake\nopen Lake DSL\nabbrev entry : Lean.Name := `Actual\npackage demo\n@[default_target]\nlean_lib Demo where\n  roots := #[entry]\n".to_string(),
            "import Lake\nopen Lake DSL\npackage demo\n@[default_target]\nlean_lib Demo where\n  roots := #[`A]++#[`B]\n".to_string(),
        ];
        for src in &r9 {
            for root in [false, true] {
                assert!(parse(src, root).is_err(), "root={root}: {src}");
            }
        }
        // `@[test_driver]` marks the next target without dropping its fields; on the header
        // line itself the plain gate refuses it (fails closed) rather than drop them.
        let driver = "import Lake\nopen Lake DSL\npackage demo\n@[test_driver]\nlean_lib Demo where\n  moreLeanArgs := #[\"-DautoImplicit=false\"]\n";
        assert!(parse(&driver.replace("]\nlean_lib", "] lean_lib"), false).is_err());
        let pkg = parse(driver, false).unwrap();
        assert_eq!(pkg.libs.len(), 1);
        assert_eq!(
            pkg.libs[0].more_lean_args,
            vec!["-DautoImplicit=false".to_string()]
        );
        assert!(!pkg.libs[0].is_default_target);
        // Args are checked exactly as passed on; `pp.*` beyond Mathlib's two keys is refused
        // (`pp.maxSteps`, `pp.all`, ... reprint the sorry warning).
        for bad in [
            " --quiet",
            "\n-DautoImplicit=false",
            "-Dweak.linter.s=foo\n",
            "-Dweak.warn.sorry=true ",
            "-Dpp.maxSteps=0",
            "-Dpp.all=true",
            "-Dweak.pp.raw=true",
            "-Dweak.weak.linter.x=true",
        ] {
            assert!(!is_allowed_lean_arg(bad), "{bad:?}");
        }
        // Fable r9: a column-0 `++` continuing a target field; Astra r10: explicit empty
        // module selections.
        for src in [
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n++ #[⟨`linter.x, true⟩]\n",
            "import Lake\nopen Lake DSL\npackage demo\n@[default_target]\nlean_lib Demo where\n  globs := #[]\n",
            "import Lake\nopen Lake DSL\npackage demo\n@[default_target]\nlean_lib Demo where\n  roots := #[]\n",
        ] {
            for root in [false, true] {
                assert!(parse(src, root).is_err(), "root={root}: {src}");
            }
        }
        // Signed or zero-padded digit strings and Nats would be re-read as other numbers.
        for v in ["\"+0\"", "\"+42\"", "007", ".ofNat 01"] {
            let src = format!(
                "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`maxHeartbeats, {v}⟩]\n"
            );
            assert!(parse(&src, false).is_err(), "{v}");
        }
        assert!(!is_allowed_lean_arg("-Ddebug.skipKernelTC=true"));
        assert!(!is_allowed_lean_arg("-Dweak.debug.skipKernelTC=true"));
        // What Mathlib needs still passes: `«»` target names, `s!` with a dotted name in
        // braces, structure-instance braces in code.
        let ok = "import Lake\nopen Lake DSL\nabbrev xs : Array LeanOption := #[⟨`a, true⟩].map fun s ↦ { s with name := `weak ++ s.name }\npackage demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\nlean_exe «cache-test» where\n  root := `Main\npost_update pkg do\n  IO.println s!\"x ({pkg.baseName}) \\\n    y\"\n";
        assert_eq!(
            lakefile_lexical_guard(ok).unwrap().0,
            splitter::strip_lean_comments(ok)
        );
        assert!(parse(ok, false).is_ok());
        // Astra r7: a target written inside a multi-line string is not a target.
        let phantom = "import Lake\nopen Lake DSL\ndef msg : String := \"\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, true⟩]\n  \"\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n";
        let pkg = parse(phantom, false).unwrap();
        assert_eq!(pkg.libs.len(), 1);
        assert_eq!(
            pkg.libs[0].lean_options,
            BTreeMap::from([("autoImplicit".to_string(), "false".to_string())])
        );
        // Astra r8: shadowing a constructor spelling the resolver reads, and a field value
        // written with a string gap, both fail closed.
        let shadow = "import Lake\nopen Lake DSL\ndef LeanOption.mk (_ : Lean.Name) (_ : LeanOptionValue) : Lake.LeanOption := ⟨`autoImplicit, false⟩\npackage demo\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[LeanOption.mk `autoImplicit true]\n";
        assert!(parse(shadow, false).is_err());
        let gap = "import Lake\nopen Lake DSL\npackage demo where\n  srcDir := \"s\\\n    rc\"\n@[default_target]\nlean_lib Demo\n";
        assert!(parse(gap, false)
            .unwrap_err()
            .to_string()
            .contains("multi-line string"));
        // Astra r7: `leanOptions` reach Lean through setup.json, which beats `-D` flags, so
        // they come after `moreLeanArgs` and win in the setup built from these args.
        let precedence = "import Lake\nopen Lake DSL\npackage demo\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n  moreLeanArgs := #[\"-DautoImplicit=true\"]\n";
        let pkg = parse(precedence, false).unwrap();
        let lib = &pkg.libs[0];
        let (strong, _) = compose_effective_args(
            &pkg,
            &lib.lean_options,
            &lib.more_lean_args,
            &lib.weak_lean_args,
        );
        let last_auto = strong
            .iter()
            .filter(|a| a.starts_with("-DautoImplicit="))
            .next_back();
        assert_eq!(last_auto.map(String::as_str), Some("-DautoImplicit=false"));
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_computed_lean_options_scopes_continuations_and_lexing() {
        let dir = make_temp_test_dir("lean_opts_regress");
        let lf = dir.join("lakefile.lean");
        let parse = |src: &str| {
            fs::write(&lf, src).unwrap();
            parse_lakefile_lean(&dir, &lf, false)
        };
        let opts = |pkg: &PackageConfig| pkg.libs[0].lean_options.clone();
        // A same-named binding inside a namespace makes the reference ambiguous: fail closed
        // rather than pick a body (Lake would resolve the global one).
        let scoped = "import Lake\nopen Lake DSL\nabbrev opts : Array LeanOption := #[⟨`autoImplicit, false⟩]\nnamespace Other\nabbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\nend Other\npackage demo\nlean_lib Demo where\n  leanOptions := opts\n";
        assert!(parse(scoped).unwrap_err().to_string().contains("not plain"));
        // Indented declarations and declarations inside an indented namespace also block
        // resolution (Lean would pick `N.opts` here).
        let indented = "import Lake\nopen Lake DSL\nabbrev opts : Array LeanOption := #[⟨`autoImplicit, false⟩]\nnamespace N\n  abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\nlean_lib Demo where\n  leanOptions := opts\nend N\npackage demo\n";
        assert!(parse(indented).is_err());
        // A value must be one string token, not an expression that starts and ends with quotes.
        for v in [
            "\"a\" ++ \"b\"",
            ".ofString \"a\" ++ \"b\"",
            "\"a\" \"b\"",
            "\"a\\\"",
        ] {
            let src = format!(
                "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`linter.s, {v}⟩]\n"
            );
            assert!(parse(&src).is_err(), "{v}");
        }
        // Parameterised declarations are not bindings.
        let param = "import Lake\nopen Lake DSL\nabbrev opts (b : Bool) : Array LeanOption := #[⟨`autoImplicit, b⟩]\npackage demo\nlean_lib Demo where\n  leanOptions := opts\n";
        assert!(parse(param)
            .unwrap_err()
            .to_string()
            .contains("parameterised"));
        // A field's expression continues on deeper-indented lines; later entries win.
        let cont = "import Lake\nopen Lake DSL\nabbrev xs : Array LeanOption := #[⟨`linter.a, true⟩]\nabbrev ys : Array LeanOption := #[⟨`linter.a, false⟩]\npackage demo\nlean_lib Demo where\n  leanOptions := xs\n\n    ++ ys\n  srcDir := \"src\"\n";
        assert_eq!(
            opts(&parse(cont).unwrap()),
            BTreeMap::from([("linter.a".to_string(), "false".to_string())])
        );
        let bad_cont = cont.replace("++ ys", "++ ys.filter fun _ => true");
        assert!(parse(&bad_cont).is_err());
        // Delimiters inside strings do not change nesting, so the following column-0
        // declaration is not swallowed into the binding body.
        let strs = "import Lake\nopen Lake DSL\nabbrev xs : Array LeanOption := #[⟨`linter.s, \"[\"⟩, ⟨`linter.t, \"a,b\"⟩]\npackage demo\nlean_lib Demo where\n  leanOptions := xs\n";
        assert_eq!(
            opts(&parse(strs).unwrap()),
            BTreeMap::from([
                ("linter.s".to_string(), "[".to_string()),
                ("linter.t".to_string(), "a,b".to_string()),
            ])
        );
        // `'` is an identifier character in Lean names, not a string delimiter: lexing splits
        // correctly, and the resulting primed key is then refused by the `-D` key gate.
        let (parts, open) = lean_scan("⟨`custom.flag', true⟩, ⟨`linter.x, false⟩", ",").unwrap();
        assert_eq!((parts.len(), open), (2, 0));
        let prime = "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`custom.flag', true⟩, ⟨`linter.x, false⟩]\n";
        assert!(parse(prime)
            .unwrap_err()
            .to_string()
            .contains("leanOptions"));
        // `leanOptions` pass the same flag gate as `moreLeanArgs`.
        let sorry_off = "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`warn.sorry, false⟩]\n";
        let err = parse(sorry_off).unwrap_err().to_string();
        assert!(
            err.contains("warn.sorry") && err.contains("fail-closed"),
            "{err}"
        );
        // Modified or attributed declarations are not bindings (same line or previous line).
        for decl in [
            "private abbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]",
            "@[reducible] abbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]",
            "@[reducible]\nabbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]",
        ] {
            let src = format!(
                "import Lake\nopen Lake DSL\n{decl}\npackage demo\nlean_lib Demo where\n  leanOptions := opts\n"
            );
            assert!(parse(&src).is_err(), "{decl}");
        }
        // String values may contain spaces and escapes.
        let spaced = "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`linter.s, .ofString \"a b\\\"c\"⟩]\n";
        assert_eq!(
            opts(&parse(spaced).unwrap()),
            BTreeMap::from([("linter.s".to_string(), "a b\"c".to_string())])
        );
        // Mismatched delimiters fail.
        assert!(lean_scan("#[⟨`linter.a, true)]", ",").is_err());
        assert!(lean_scan("#[\"unclosed]", ",").is_err());
        let lib = |opts_expr: &str, prelude: &str| {
            format!("import Lake\nopen Lake DSL\n{prelude}package demo\nlean_lib Demo where\n  leanOptions := {opts_expr}\n")
        };
        // `weak.warn.sorry=false` disables the sorry warning too, directly or via the weak map.
        assert!(parse(&lib("#[⟨`weak.warn.sorry, false⟩]", "")).is_err());
        let ws = "abbrev ws : Array LeanOption := #[⟨`warn.sorry, false⟩]\n";
        assert!(parse(&lib(
            "ws.map fun s ↦ { s with name := `weak ++ s.name }",
            ws
        ))
        .is_err());
        // Option names must be name literals; LeanOption.mk validates key and value.
        for e in [
            "#[⟨optKey, false⟩]",
            "#[⟨``linter.x, false⟩]",
            "#[LeanOption.mk optKey false]",
            "#[LeanOption.mk ` true]",
        ] {
            assert!(parse(&lib(e, "")).is_err(), "{e}");
        }
        assert_eq!(
            opts(
                &parse(&lib(
                    "#[LeanOption.mk `linter.n (.ofNat 1500), LeanOption.mk `linter.s \"a b\"]",
                    ""
                ))
                .unwrap()
            ),
            BTreeMap::from([
                ("linter.n".to_string(), "1500".to_string()),
                ("linter.s".to_string(), "a b".to_string()),
            ])
        );
        // Every scope form disables resolution; binders, dotted and universe names are rejected.
        for prelude in [
            "abbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]\nnoncomputable section\nend\n",
            "abbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]\nmutual\nend\n",
            "abbrev opts(b : Bool) : Array LeanOption := #[⟨`linter.a, true⟩]\n",
            "abbrev opts.{u} : Array LeanOption := #[⟨`linter.a, true⟩]\n",
            "abbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]\nabbrev Foo.opts : Array LeanOption := #[⟨`linter.a, false⟩]\n",
            "set_option autoImplicit true in\nabbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]\n",
        ] {
            assert!(parse(&lib("opts", prelude)).is_err(), "{prelude}");
        }
        // Same-column `++` continues a field, and a column-0 `++` continues a binding body.
        let xs = "abbrev xs : Array LeanOption := #[⟨`linter.a, true⟩]\nabbrev ys : Array LeanOption := #[⟨`linter.a, false⟩]\n";
        assert_eq!(
            opts(&parse(&lib("xs\n  ++ ys", xs)).unwrap()),
            BTreeMap::from([("linter.a".to_string(), "false".to_string())])
        );
        let body =
            "abbrev zs : Array LeanOption := #[⟨`linter.a, true⟩]\n++ #[⟨`linter.a, false⟩]\n";
        assert_eq!(
            opts(&parse(&lib("zs", body)).unwrap()),
            BTreeMap::from([("linter.a".to_string(), "false".to_string())])
        );
        // Char literals such as '[' or '"' are outside the lexical subset: fail closed.
        let chars = "def openBr : Char := '['\ndef dq : Char := '\"'\nabbrev xs : Array LeanOption := #[⟨`linter.a, true⟩]\n";
        assert!(parse(&lib("xs", chars))
            .unwrap_err()
            .to_string()
            .contains("char literal"));
        // Root packages keep rejecting top-level declarations (stricter root gate).
        fs::write(&lf, lib("xs", xs)).unwrap();
        assert!(parse_lakefile_lean(&dir, &lf, true).is_err());
        // Non-plain lakefiles disable identifier resolution: scopes hidden inside an unrelated
        // binding's body, `where` clauses, notation/macros and `open ... in` can all shadow `opts`.
        let opts_g = "abbrev opts : Array LeanOption := #[⟨`autoImplicit, false⟩]\n";
        for extra in [
            "def unrelated : Nat := 0\n  namespace N\n  abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n",
            "abbrev other : Array LeanOption := opts\nwhere\n  opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n",
            "macro \"opts\" : term => `(#[⟨`autoImplicit, true⟩])\n",
            "def Other.opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\nopen Other in\n",
        ] {
            let prelude = format!("{opts_g}{extra}");
            assert!(parse(&lib("opts", &prelude)).is_err(), "{extra}");
        }
        // Commands may share a line: a namespace and a shadowing declaration after an unrelated
        // body on the same line are still detected.
        let same_line = format!(
            "{opts_g}def unrelated : Nat := 0 namespace N abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n"
        );
        assert!(parse(&lib("opts", &same_line)).is_err());
        assert!(!lakefile_is_plain(
            "abbrev opts : Array LeanOption := #[] end N\npackage demo\n"
        ));
        assert!(lakefile_is_plain(
            "import Lake\nopen Lake DSL\nlean_lib Demo where\n  leanOptions := #[⟨`linter.s, \"namespace end\"⟩]\n"
        ));
        // Metaprogramming anywhere (incl. inside a post_update do-block or as `#command`s), `;`
        // field separators and a second target command mid-line make the file non-plain; then
        // even literal arrays fail closed, since notation/macro_rules can rewrite literals.
        for extra in [
            "post_update _pkg do\n  pure ()\n  macro:max (priority := high) \"opts\" : term => `(#[])\n",
            "post_update _pkg do\n  pure ()\n  #eval pure ()\n",
            "run_cmd pure ()\n",
            "notation:max \"false\" => true\n",
            "macro_rules | `(false) => `(true)\n",
            "@[default_target] lean_lib Dummy namespace N\n",
        ] {
            let prelude = format!("{opts_g}{extra}");
            assert!(parse(&lib("opts", &prelude)).is_err(), "{extra}");
            assert!(parse(&lib("#[⟨`autoImplicit, false⟩]", &prelude)).is_err(), "{extra}");
        }
        // Fable r4: keywords after an allowed start, after a `++` continuation, or later on an
        // indented continuation line; and a command hidden after a multi-line string closes.
        for extra in [
            "abbrev junk : Nat := 7 namespace Other abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n",
            "abbrev junk : Array Nat := #[1]\n++ #[2] namespace Other abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n",
            "def junk : Nat :=\n  7 namespace Other abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n",
            "def junk : Nat := 7\n  macro_rules | `(opts) => `((#[] : Array LeanOption))\n",
            "def s : String := \"abc\\\n  foo\" namespace N abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n",
        ] {
            let prelude = format!("{opts_g}{extra}");
            assert!(parse(&lib("opts", &prelude)).is_err(), "{extra}");
        }
        // A multi-line string mentioning keywords is still just a string.
        assert!(lakefile_is_plain(
            "abbrev xs : Array LeanOption := #[]\ndef msg : String := \"open in \\\n  namespace end\"\npackage demo\n"
        ));
        let semi = format!(
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  moreLinkArgs := #[]; leanOptions := #[⟨`autoImplicit, true⟩]\n"
        );
        assert!(parse(&semi).is_err());
        // Lean elaborates in order: a binding declared after its use is not in scope.
        let forward = "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := opts\nabbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]\n";
        assert!(parse(forward)
            .unwrap_err()
            .to_string()
            .contains("before its declaration"));
        let fwd_binding =
            "abbrev a : Array LeanOption := b\nabbrev b : Array LeanOption := #[⟨`linter.x, true⟩]\n";
        assert!(parse(&lib("a", fwd_binding)).is_err());
        let where_field = format!(
            "import Lake\nopen Lake DSL\n{opts_g}package demo\nlean_lib Demo where\n  leanOptions := opts\n  where\n    opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n"
        );
        assert!(parse(&where_field).is_err());
        // Option names are plain dotted identifiers only.
        for e in [
            "#[⟨`«a.b», true⟩]",
            "#[⟨`\"warn.sorry\", true⟩]",
            "#[⟨`x++y, true⟩]",
            "#[⟨`a..b, true⟩]",
        ] {
            assert!(parse(&lib(e, "")).is_err(), "{e}");
        }
        // String values: only escapes Lean and the decoder agree on, no bool/number lookalikes.
        for e in [
            "#[⟨`linter.s, \"\\x41\"⟩]",
            "#[⟨`linter.s, \"\\u0041\"⟩]",
            "#[⟨`linter.s, \"\\'\"⟩]",
            "#[⟨`linter.s, .ofString \"true\"⟩]",
            "#[⟨`linter.s, \"42\"⟩]",
        ] {
            assert!(parse(&lib(e, "")).is_err(), "{e}");
        }
        assert_eq!(
            opts(&parse(&lib("#[⟨`linter.s, \"a\\\\b \\\"c\\\"\"⟩]", "")).unwrap()),
            BTreeMap::from([("linter.s".to_string(), "a\\b \"c\"".to_string())])
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
    #[cfg(unix)]
    #[test]
    fn test_optout_module_cache_hits_preserve_existing_lake_tree() -> Result<()> {
        use crate::worktree_test_support::{snapshot, LakeTree};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::new("module_cas", &[("P/Fixture.lean",
            "module\n@[expose] public def value : Nat := 7\npublic theorem value_eq : value = 7 := rfl\n")])?;
        let project = &tree.project;
        let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
        // Seed the module action from Lake's actual output bytes, without a turbo build.
        let cfg = resolve_project_config(project)?;
        let dag = build_module_dag_with_trust(&cfg, &[], false)?;
        let node = &dag.nodes["P.Fixture"];
        let key = compute_module_cas_key(&cfg, node, &[], node.needs_c)?;
        store_module_artifacts_in_cas(
            &mut store,
            project,
            node,
            &key,
            &cfg.toolchain,
            "trusted-internal",
            1,
            0,
        )?;
        tree.opt_out()?;
        tree.prepare_snapshot(".lake/build/lib/lean/P/Fixture.olean")?;
        let artifact = project.join(".lake/build/lib/lean/P/Fixture.olean");
        let build = |store: &mut TurboStore| {
            build_project_modules_native(
                store,
                project,
                &[],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
        };
        let before = snapshot(project)?;
        let report = build(&mut store)?;
        assert_eq!(report.modules_compiled, 0);
        assert_eq!(report.modules_cached, 1);
        assert_eq!(
            snapshot(project)?,
            before,
            "module CAS hit changed Lake artifacts/entries"
        );
        // A missing companion must fail without wiping the remaining output set.
        fs::remove_file(artifact.with_extension("olean.server"))?;
        let before = snapshot(project)?;
        let err = build(&mut store).unwrap_err().to_string();
        assert!(err.contains("Worktree opt-out prevents restoring"), "{err}");
        assert_eq!(snapshot(project)?, before);
        drop(store);
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_caller_optout_preserves_external_path_dependency() -> Result<()> {
        use crate::worktree_test_support::{snapshot, LakeTree};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for prebuilt in [false, true] {
            let tree = LakeTree::new("external_dep", &[("P/A.lean", "def depValue : Nat := 7\n")])?;
            let caller = tree.root.join("caller");
            fs::create_dir_all(&caller)?;
            fs::write(
                caller.join("lean-toolchain"),
                include_str!("../../../lean/lean-toolchain"),
            )?;
            fs::write(caller.join("lakefile.toml"),
                "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"fixture\"\npath = \"../project\"\n[[lean_lib]]\nname = \"App\"\n")?;
            fs::write(
                caller.join("App.lean"),
                "import P.A\ntheorem app : depValue = 7 := rfl\n",
            )?;
            let out = Command::new("lake")
                .args(["build", "App"])
                .current_dir(&caller)
                .output()?;
            anyhow::ensure!(
                out.status.success(),
                "{}",
                String::from_utf8_lossy(&out.stderr)
            );
            let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
            let targets = vec!["App".to_string()];
            // Seed both module actions before opting out. Keep the dependency's
            // manifest only in the case exercising external-prebuilt digest reads.
            let seed = build_project_modules_native(
                &mut store,
                &caller,
                &targets,
                "trusted-internal",
                1,
                false,
                true,
                None,
            )?;
            assert_eq!(seed.modules_compiled, 2);
            if !prebuilt {
                fs::remove_file(
                    tree.project
                        .join(".lake/build/.turbo_verified_sources.json"),
                )?;
            }
            fs::write(
                caller.join("turbo-lean.toml"),
                "[worktree]\nauto_link = false\n",
            )?;
            assert!(!tree.project.join("turbo-lean.toml").exists());
            tree.prepare_snapshot(".lake/build/lib/lean/P/A.olean")?;
            fs::remove_file(caller.join(".lake/build/.turbo_publish.lock"))?;
            let dep_before = snapshot(&tree.project)?;
            let caller_before = snapshot(&caller)?;
            let cfg = resolve_project_config(&caller)?;
            let dag = build_module_dag(&cfg, &targets)?;
            assert_eq!(dag.nodes.contains_key("P.A"), !prebuilt);
            let report = build_project_modules_native(
                &mut store,
                &caller,
                &targets,
                "trusted-internal",
                1,
                false,
                true,
                None,
            )?;
            assert_eq!(report.modules_compiled, 0);
            assert_eq!(report.modules_cached, if prebuilt { 1 } else { 2 });
            crate::lake_build::run_build_command(
                &mut store,
                true,
                targets,
                caller.clone(),
                "trusted-internal".to_string(),
                1,
                false,
            )?;
            assert_eq!(
                snapshot(&tree.project)?,
                dep_before,
                "external dependency changed (prebuilt={prebuilt})"
            );
            assert_eq!(
                snapshot(&caller)?,
                caller_before,
                "caller changed (prebuilt={prebuilt})"
            );
        }
        Ok(())
    }

    /// P0-4: rebuilding only an imported module (`build App.A`) must invalidate the manifest
    /// entry of its reverse dependent `App.B`, whose `.olean` was elaborated against the old `A`.
    #[test]
    fn test_dependent_manifest_entry_stale_after_import_only_rebuild() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("stale_dependent");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let a_src = |v: u32| format!("namespace App\ndef g : Nat := {v}\nend App\n");
        fs::write(proj_dir.join("App/A.lean"), a_src(3)).unwrap();
        let b_file = proj_dir.join("App/B.lean");
        let b_src = "import App.A\nnamespace App\ntheorem g_eq : g = 3 := rfl\nend App\n";
        fs::write(&b_file, b_src).unwrap();
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        let mut build = |targets: &[String]| {
            build_project_modules_native(
                &mut store,
                &proj_dir,
                targets,
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap()
        };
        assert_eq!(build(&[]).modules_compiled, 2);
        let canon = proj_dir.canonicalize().unwrap();
        let canon_b = b_file.canonicalize().unwrap();
        assert!(crate::lake_build::is_file_verified_in_lake_build(
            &canon, &canon_b, b_src
        ));
        assert!(crate::lake_build::resolve_prebuilt_module_import(&canon, &canon_b).is_some());
        // Edit `A` so `B`'s theorem no longer holds, then rebuild only `App.A`.
        fs::write(proj_dir.join("App/A.lean"), a_src(4)).unwrap();
        let rep = build(&["App.A".to_string()]);
        assert_eq!(rep.compiled_modules, vec!["App.A".to_string()]);
        assert!(
            !crate::lake_build::is_file_verified_in_lake_build(&canon, &canon_b, b_src),
            "`App.B` reported verified from an `.olean` built against the old `App.A`"
        );
        assert!(crate::lake_build::resolve_prebuilt_module_import(&canon, &canon_b).is_none());
        // Restoring the original `A` (CAS hit) makes `B`'s recorded inputs current again.
        fs::write(proj_dir.join("App/A.lean"), a_src(3)).unwrap();
        let rep = build(&["App.A".to_string()]);
        assert_eq!(rep.cached_modules, vec!["App.A".to_string()]);
        assert!(crate::lake_build::is_file_verified_in_lake_build(
            &canon, &canon_b, b_src
        ));
        // Legacy entries without pinned import digests fail closed.
        let manifest_path = crate::lake_build::verified_sources_manifest_path(&canon);
        let mut legacy: serde_json::Value =
            serde_json::from_slice(&fs::read(&manifest_path).unwrap()).unwrap();
        for entry in legacy["modules"].as_object_mut().unwrap().values_mut() {
            entry
                .as_object_mut()
                .unwrap()
                .remove("import_olean_digests");
        }
        fs::write(&manifest_path, serde_json::to_vec(&legacy).unwrap()).unwrap();
        assert!(!crate::lake_build::is_file_verified_in_lake_build(
            &canon, &canon_b, b_src
        ));
        // ...and gives no freshness evidence before elaboration: every built import is refreshed.
        let c_file = canon.join("App/C.lean");
        fs::write(&c_file, "import App.B\n").unwrap();
        let res = crate::lake_build::ensure_project_imports_fresh_for_check(&canon, &[c_file]);
        assert!(
            !matches!(res, Ok(0)),
            "legacy manifest fell back to timestamps"
        );
        assert!(!manifest_path.exists());
        let _ = fs::remove_dir_all(&dir);
    }

    /// P0-4 across packages: rebuilding only a transitive dependency-package import must
    /// invalidate the root module, and an entry missing an external pin fails closed.
    #[test]
    fn test_root_entry_stale_after_transitive_dep_pkg_rebuild() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("stale_dep_pkg");
        let proj_dir = dir.join("proj");
        let dep_dir = proj_dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("DepPkg")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        for d in [&proj_dir, &dep_dir] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepPkg\"\nglobs = [\"DepPkg.+\"]\n",
        )
        .unwrap();
        let a_src = |v: u32| format!("namespace DepPkg\ndef g : Nat := {v}\nend DepPkg\n");
        fs::write(dep_dir.join("DepPkg/A.lean"), a_src(3)).unwrap();
        fs::write(
            dep_dir.join("DepPkg/B.lean"),
            "import DepPkg.A\nnamespace DepPkg\ndef h : Nat := g\nend DepPkg\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lake-manifest.json"),
            r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep_pkg", "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml", "inherited": false}], "name": "app_pkg", "lakeDir": ".lake", "fixedToolchain": false}"#,
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let c_file = proj_dir.join("App/C.lean");
        let c_src = "import DepPkg.B\nnamespace App\ntheorem h_eq : DepPkg.h = 3 := rfl\nend App\n";
        fs::write(&c_file, c_src).unwrap();
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        let mut build = |root: &Path, targets: &[String]| {
            build_project_modules_native(
                &mut store,
                root,
                targets,
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap()
        };
        assert_eq!(build(&proj_dir, &[]).modules_compiled, 3);
        let canon = proj_dir.canonicalize().unwrap();
        let canon_c = c_file.canonicalize().unwrap();
        let verified =
            || crate::lake_build::is_file_verified_in_lake_build(&canon, &canon_c, c_src);
        assert!(verified());
        // An entry missing its external pin fails closed.
        let manifest_path = crate::lake_build::verified_sources_manifest_path(&canon);
        let good = fs::read(&manifest_path).unwrap();
        let mut partial: serde_json::Value = serde_json::from_slice(&good).unwrap();
        partial["modules"]["App/C.lean"]["import_olean_digests"] = serde_json::json!({});
        fs::write(&manifest_path, serde_json::to_vec(&partial).unwrap()).unwrap();
        assert!(!verified(), "unpinned dependency-package import accepted");
        fs::write(&manifest_path, &good).unwrap();
        assert!(verified());
        // ...and so does a dependency-package entry missing a pin.
        let dep_manifest_path = dep_dir.join(".lake/build/.turbo_verified_sources.json");
        let dep_good = fs::read(&dep_manifest_path).unwrap();
        let mut dep_partial: serde_json::Value = serde_json::from_slice(&dep_good).unwrap();
        assert!(
            dep_partial["modules"]["DepPkg/A.lean"]["artifact_stat_fingerprint"]
                .as_str()
                .is_some_and(|fp| !fp.is_empty())
        );
        dep_partial["modules"]["DepPkg/B.lean"]["import_olean_digests"] = serde_json::json!({});
        fs::write(
            &dep_manifest_path,
            serde_json::to_vec(&dep_partial).unwrap(),
        )
        .unwrap();
        assert!(!verified(), "unpinned transitive import accepted");
        fs::write(&dep_manifest_path, &dep_good).unwrap();
        assert!(verified());
        // A foreign rewrite of a transitive `.olean` with an old mtime is detected, and putting
        // the original bytes back (new ctime, same digest) is accepted again.
        let a_olean = dep_dir.join(".lake/build/lib/lean/DepPkg/A.olean");
        let a_bytes = fs::read(&a_olean).unwrap();
        let _ = fs::remove_file(&a_olean);
        fs::write(&a_olean, b"foreign olean").unwrap();
        assert!(Command::new("touch")
            .args(["-d", "@1000000000"])
            .arg(&a_olean)
            .status()
            .unwrap()
            .success());
        assert!(!verified(), "rewritten transitive `.olean` accepted");
        let _ = fs::remove_file(&a_olean);
        fs::write(&a_olean, &a_bytes).unwrap();
        assert!(verified());
        // Rebuild only the transitive import `DepPkg.A` (inside the dependency package).
        std::thread::sleep(std::time::Duration::from_millis(20));
        fs::write(dep_dir.join("DepPkg/A.lean"), a_src(4)).unwrap();
        let rep = build(&dep_dir, &["DepPkg.A".to_string()]);
        assert_eq!(rep.compiled_modules, vec!["DepPkg.A".to_string()]);
        assert!(
            !verified(),
            "`App.C` reported verified against a dependency closure rebuilt underneath it"
        );
        assert!(crate::lake_build::resolve_prebuilt_module_import(&canon, &canon_c).is_none());
        // `check` must not elaborate `App.C` against the stale `DepPkg.B` either.
        let res =
            crate::lake_build::ensure_project_imports_fresh_for_check(&canon, &[canon_c.clone()]);
        assert!(
            !matches!(res, Ok(0)),
            "stale `DepPkg.B` left in place for elaboration"
        );
        // Rebuilding the root must not reuse the stale `DepPkg.B` as a fresh external closure:
        // its pin for `DepPkg.A` no longer matches, so `B` is rebuilt and `App.C` (`h = 3`) fails.
        let rebuilt = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        );
        assert!(rebuilt.is_err(), "stale `DepPkg.B` reused: {rebuilt:?}");
        assert!(!verified());
        let _ = fs::remove_dir_all(&dir);
    }

    /// P0-4 on the elaboration path: a CAS restore of an import (old blob mtime) must still make
    /// `ensure_project_imports_fresh_for_check` treat dependents built against the newer import
    /// as stale, so `check` never elaborates against a stale intermediate `.olean`.
    #[test]
    fn test_check_refreshes_dependent_after_import_cas_restore() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("stale_dependent_restore");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let a_src = |v: u32| format!("namespace App\ndef g : Nat := {v}\nend App\n");
        let b_src = |v: u32| {
            format!("import App.A\nnamespace App\ntheorem g_eq : g = {v} := rfl\nend App\n")
        };
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        let mut build = |targets: &[String]| {
            build_project_modules_native(
                &mut store,
                &proj_dir,
                targets,
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap()
        };
        fs::write(proj_dir.join("App/A.lean"), a_src(3)).unwrap();
        fs::write(proj_dir.join("App/B.lean"), b_src(3)).unwrap();
        build(&[]);
        std::thread::sleep(std::time::Duration::from_millis(20));
        fs::write(proj_dir.join("App/A.lean"), a_src(4)).unwrap();
        fs::write(proj_dir.join("App/B.lean"), b_src(4)).unwrap();
        build(&[]);
        // Restore `A` v3 from CAS; `B` (built against `A` v4) is now stale.
        fs::write(proj_dir.join("App/A.lean"), a_src(3)).unwrap();
        let rep = build(&["App.A".to_string()]);
        assert_eq!(rep.cached_modules, vec!["App.A".to_string()]);
        let canon = proj_dir.canonicalize().unwrap();
        let c_file = canon.join("App/C.lean");
        fs::write(&c_file, "import App.B\n").unwrap();
        // Lake must be asked to refresh `App.B` (which then fails: `g = 4` no longer holds).
        let res = crate::lake_build::ensure_project_imports_fresh_for_check(&canon, &[c_file]);
        assert!(
            !matches!(res, Ok(0)),
            "stale `App.B` left in place for elaboration"
        );
        let _ = fs::remove_dir_all(&dir);
    }

    /// P0-4 on the elaboration path: an import whose artifacts were replaced behind turbo-lean's
    /// back (old mtimes, unchanged source and manifest) must be refreshed before elaboration.
    #[test]
    fn test_check_refreshes_after_foreign_import_artifact_restore() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("foreign_import_restore");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let a_src = |v: u32| format!("namespace App\ndef g : Nat := {v}\nend App\n");
        let b_src = |v: u32| {
            format!("import App.A\nnamespace App\ntheorem g_eq : g = {v} := rfl\nend App\n")
        };
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        let mut build = || {
            build_project_modules_native(
                &mut store,
                &proj_dir,
                &[],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap()
        };
        fs::write(proj_dir.join("App/A.lean"), a_src(3)).unwrap();
        fs::write(proj_dir.join("App/B.lean"), b_src(3)).unwrap();
        build();
        let a_olean = proj_dir.join(".lake/build/lib/lean/App/A.olean");
        let old_a = fs::read(&a_olean).unwrap();
        fs::write(proj_dir.join("App/A.lean"), a_src(4)).unwrap();
        fs::write(proj_dir.join("App/B.lean"), b_src(4)).unwrap();
        build();
        // Put the `A` v3 `.olean` back with ordered, old timestamps; source and manifest say v4.
        let _ = fs::remove_file(&a_olean);
        fs::write(&a_olean, &old_a).unwrap();
        for (path, stamp) in [
            (proj_dir.join("App/A.lean"), "@1000000000"),
            (a_olean.clone(), "@1000000001"),
        ] {
            assert!(Command::new("touch")
                .args(["-d", stamp])
                .arg(&path)
                .status()
                .unwrap()
                .success());
        }
        let canon = proj_dir.canonicalize().unwrap();
        let c_file = canon.join("App/C.lean");
        fs::write(&c_file, "import App.B\n").unwrap();
        let res = crate::lake_build::ensure_project_imports_fresh_for_check(&canon, &[c_file]);
        assert!(
            !matches!(res, Ok(0)),
            "foreign `App.A` artifact left in place under `App.B`"
        );
        let _ = fs::remove_dir_all(&dir);
    }

    /// P0-4 across a dependency-to-root edge: `App.C → DepPkg.B → App.A → App.X`; rebuilding only
    /// `App.X` must invalidate `App.C`.
    #[test]
    fn test_root_entry_stale_through_dep_to_root_import() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("stale_dep_to_root");
        let proj_dir = dir.join("proj");
        let dep_dir = proj_dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("DepPkg")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        for d in [&proj_dir, &dep_dir] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepPkg\"\nglobs = [\"DepPkg.+\"]\n",
        )
        .unwrap();
        fs::write(
            dep_dir.join("DepPkg/B.lean"),
            "import App.A\nnamespace DepPkg\ndef h : Nat := App.k\nend DepPkg\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lake-manifest.json"),
            r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep_pkg", "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml", "inherited": false}], "name": "app_pkg", "lakeDir": ".lake", "fixedToolchain": false}"#,
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let x_src = |v: u32| format!("namespace App\ndef x : Nat := {v}\nend App\n");
        fs::write(proj_dir.join("App/X.lean"), x_src(3)).unwrap();
        fs::write(
            proj_dir.join("App/A.lean"),
            "import App.X\nnamespace App\ndef k : Nat := x\nend App\n",
        )
        .unwrap();
        let c_file = proj_dir.join("App/C.lean");
        let c_src = "import DepPkg.B\nnamespace App\ntheorem h_eq : DepPkg.h = 3 := rfl\nend App\n";
        fs::write(&c_file, c_src).unwrap();
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        let mut build = |targets: &[String]| {
            build_project_modules_native(
                &mut store,
                &proj_dir,
                targets,
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap()
        };
        assert_eq!(build(&[]).modules_compiled, 4);
        let canon = proj_dir.canonicalize().unwrap();
        let canon_c = c_file.canonicalize().unwrap();
        let verified =
            || crate::lake_build::is_file_verified_in_lake_build(&canon, &canon_c, c_src);
        assert!(verified());
        fs::write(proj_dir.join("App/X.lean"), x_src(4)).unwrap();
        assert_eq!(
            build(&["App.X".to_string()]).compiled_modules,
            vec!["App.X".to_string()]
        );
        assert!(
            !verified(),
            "`App.C` accepted through a dependency-to-root edge onto a rebuilt `App.X`"
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_native_module_builder_cas_partial_invalidation_lazy_c_and_lake_differential() {
        let _env_guard = native_build_env_guard();
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
        fs::write(
            diff_dir.join("Diff/ModBase.lean"),
            "module\nnamespace Diff\npublic def mbase : Nat := 5\nend Diff\n",
        )
        .unwrap();
        fs::write(
            diff_dir.join("Diff/ModSys.lean"),
            "module\npublic import Diff.ModBase\nnamespace Diff\npublic def cube (n : Nat) : Nat := n * mbase\nend Diff\n",
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
            // Re-run with `:c` facet so `.c`, `.c.hash`, `.olean.hash`, `.ilean.hash`, companion `.hash`, and `.trace` are materialized,
            // then verify `lake build --no-build` succeeds with 0 rebuilds!
            build_project_modules_native(
                &mut store,
                &diff_dir,
                &["Diff:c".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            let native_use_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(diff_dir.join(".lake/build/lib/lean/Diff/Use.trace")).unwrap(),
            )
            .unwrap();
            let native_modsys_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(diff_dir.join(".lake/build/lib/lean/Diff/ModSys.trace")).unwrap(),
            )
            .unwrap();
            let no_build_st = Command::new(&lake_bin)
                .args(["build", "--no-build"])
                .current_dir(&diff_dir)
                .status()
                .unwrap();
            assert!(
                no_build_st.success(),
                "`lake build --no-build` must succeed directly on turbo-lean materialized artifacts"
            );
            fs::remove_dir_all(diff_dir.join(".lake/build")).unwrap();
            let st = Command::new(&lake_bin)
                .arg("build")
                .current_dir(&diff_dir)
                .status()
                .unwrap();
            assert!(st.success());
            let lake_use_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(diff_dir.join(".lake/build/lib/lean/Diff/Use.trace")).unwrap(),
            )
            .unwrap();
            let lake_modsys_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(diff_dir.join(".lake/build/lib/lean/Diff/ModSys.trace")).unwrap(),
            )
            .unwrap();
            assert_eq!(
                native_use_trace["depHash"], lake_use_trace["depHash"],
                "native vs lake Diff.Use.trace depHash must match bit-for-bit"
            );
            assert_eq!(
                native_use_trace["outputs"], lake_use_trace["outputs"],
                "native vs lake Diff.Use.trace outputs must match bit-for-bit"
            );
            assert_eq!(
                native_modsys_trace["depHash"], lake_modsys_trace["depHash"],
                "native vs lake module-system Diff.ModSys.trace depHash must match bit-for-bit"
            );
            assert_eq!(
                native_modsys_trace["outputs"], lake_modsys_trace["outputs"],
                "native vs lake module-system Diff.ModSys.trace outputs must match bit-for-bit"
            );
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

        // 3. Symlink to `.elan/bin/lean` (where `lean` is a hardlink or regular file, not a symlink to `elan`)
        // MUST be detected by `path_is_elan_proxy_bin` via canonicalized component check.
        let fake_dot_elan_bin = dir.join(".elan/bin");
        fs::create_dir_all(&fake_dot_elan_bin).unwrap();
        let fake_proxy = fake_dot_elan_bin.join("lean");
        fs::write(&fake_proxy, b"#!/bin/sh\n").unwrap();
        assert!(path_is_elan_proxy_bin(&fake_proxy));
        #[cfg(unix)]
        {
            let usr_local_bin = dir.join("usr_local_bin");
            fs::create_dir_all(&usr_local_bin).unwrap();
            let sym_lean = usr_local_bin.join("lean");
            std::os::unix::fs::symlink(&fake_proxy, &sym_lean).unwrap();
            assert!(
                path_is_elan_proxy_bin(&sym_lean),
                "symlink pointing into .elan/bin/lean must be detected as elan proxy"
            );
        }

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_adversarial_cas_key_dep_digest_validation_and_ambiguous_or_same_mtime_deps() {
        let _env_guard = native_build_env_guard();
        let _bwrap_guard = BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
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

        // 8. Execute a real 2-module untrusted build (`Shared.Util` + `App.Main`) through an executable `bwrap` shim.
        let fake_bwrap = ScopedTestBwrapOverride::write_fake_bwrap_script(&dir).unwrap();
        let mut untrusted_store = TurboStore::open(Some(&dir.join("untrusted_store"))).unwrap();
        let rep_untrusted = {
            let _bwrap_guard =
                ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy().into_owned());
            build_project_modules_native(
                &mut untrusted_store,
                &proj_dir,
                &["App:c".to_string()],
                "untrusted:pr",
                1,
                true,
                true,
                None,
            )
            .unwrap()
        };
        assert!(
            rep_untrusted.bwrap_used
                && rep_untrusted.modules_compiled == 2
                && main_untrusted.c_path.is_file()
        );

        // 9. When rebuilding with `needs_c = false`, stale `Main.c` is removed, and failed staging leaves destination untouched.
        {
            let _bwrap_guard =
                ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy().into_owned());
            build_project_modules_native(
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
        }
        assert!(!main_untrusted.c_path.exists());
        let orig_olean_bytes = fs::read(&main_untrusted.olean_path).unwrap();
        let orig_ilean_bytes = fs::read(&main_untrusted.ilean_path).unwrap();
        let bad_tmp = proj_dir.join(".lake/build/.turbo_bad_pub_tmp");
        fs::create_dir_all(bad_tmp.join("App")).unwrap();
        fs::write(bad_tmp.join("App/Main.olean"), b"corrupt_olean").unwrap();
        #[cfg(unix)]
        std::os::unix::fs::symlink("/etc/passwd", bad_tmp.join("App/Main.ilean")).unwrap();
        let pub_from_tmp = |tmp_root: &Path| {
            publish_module_artifacts_atomic(
                tmp_root,
                main_untrusted,
                &tmp_root.join("App/Main.olean"),
                &tmp_root.join("App/Main.ilean"),
                &tmp_root.join("App/Main.olean.server"),
                &tmp_root.join("App/Main.olean.private"),
                &tmp_root.join("App/Main.ir"),
                &tmp_root.join("App/Main.ir.sig"),
                &tmp_root.join("App/Main.c"),
            )
        };
        assert!(pub_from_tmp(&bad_tmp).is_err());
        assert_eq!(
            fs::read(&main_untrusted.olean_path).unwrap(),
            orig_olean_bytes
        );

        // 10. Phase 2 second-rename failure rollback + stale artifact restoration + inconsistent state reporting.
        let bad_tmp2 = proj_dir.join(".lake/build/.turbo_bad_pub_tmp2");
        fs::create_dir_all(bad_tmp2.join("App")).unwrap();
        fs::write(bad_tmp2.join("App/Main.olean"), b"corrupt_phase2_olean").unwrap();
        fs::write(bad_tmp2.join("App/Main.ilean"), b"corrupt_phase2_ilean").unwrap();
        fs::create_dir_all(main_untrusted.c_path.parent().unwrap()).unwrap();
        fs::write(&main_untrusted.c_path, b"pre_existing_c_bytes").unwrap();
        fs::remove_file(&main_untrusted.ilean_path).unwrap();
        fs::create_dir_all(main_untrusted.ilean_path.join("blocker_subfile")).unwrap();
        assert!(pub_from_tmp(&bad_tmp2).is_err());
        assert_eq!(
            fs::read(&main_untrusted.olean_path).unwrap(),
            orig_olean_bytes
        );
        assert_eq!(
            fs::read(&main_untrusted.c_path).unwrap(),
            b"pre_existing_c_bytes"
        );
        let _ = fs::remove_file(&main_untrusted.c_path);
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
            rb_err.contains("publication state potentially inconsistent")
                && !main_untrusted.olean_path.exists()
        );
        let _ = fs::remove_dir_all(&main_untrusted.ilean_path);
        fs::write(&main_untrusted.olean_path, &orig_olean_bytes).unwrap();
        fs::write(&main_untrusted.ilean_path, &orig_ilean_bytes).unwrap();

        // 11. Verify Lake `.hash` and `.trace` sidecars + bit-exact Lake MurmurHash64A parity
        assert_eq!(
            format!("{:016x}", lake_hash_text("-DautoImplicit=false")),
            "4a85acb881fd49d0"
        );
        assert_eq!(
            format!("{:016x}", lake_hash_name("TurboLean.Assembler")),
            "6f4e7ca5f8ee9bd1"
        );
        assert_eq!(
            format!("{:016x}", lake_hash_pkg_id("turbo-lean-proofs")),
            "537b25143adc2c3f"
        );
        assert_eq!(
            format!(
                "{:016x}",
                lake_hash_bytes(b"eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
            ),
            "407ce514b71d5a10"
        );
        let expected_main_dig =
            compute_olean_artifact_set_digest(&main_untrusted.olean_path).unwrap();
        let write_hashes = |art: &str, aud: Option<&str>, clean: bool| {
            write_lake_module_hashes_and_trace(
                &cfg,
                &dag_untrusted,
                main_untrusted,
                art,
                aud,
                clean,
            )
        };
        write_hashes(&expected_main_dig, Some(&expected_main_dig), true).unwrap();
        let olean_hash_p = PathBuf::from(format!("{}.hash", main_untrusted.olean_path.display()));
        let ilean_hash_p = PathBuf::from(format!("{}.hash", main_untrusted.ilean_path.display()));
        let trace_p = main_untrusted.olean_path.with_extension("trace");
        assert!(olean_hash_p.is_file() && fs::read_to_string(&olean_hash_p).unwrap().len() == 16);
        assert!(ilean_hash_p.is_file() && fs::read_to_string(&ilean_hash_p).unwrap().len() == 16);
        let trace_val: serde_json::Value =
            serde_json::from_slice(&fs::read(&trace_p).unwrap()).unwrap();
        assert!(
            trace_val["schemaVersion"] == "2025-09-10"
                && trace_val["depHash"].as_str().unwrap_or_default().len() == 16
        );
        assert!(write_hashes("mismatch_digest", Some(&expected_main_dig), true).is_err());
        assert!(!olean_hash_p.exists() && !ilean_hash_p.exists() && !trace_p.exists());
        assert!(write_hashes(&expected_main_dig, Some(&expected_main_dig), false).is_err());
        assert!(write_hashes(&expected_main_dig, Some("tampered_audit_digest"), true).is_err());
        assert!(write_hashes(&expected_main_dig, None, true).is_err());
        let shared_node = dag_untrusted.nodes.get("Shared.Util").unwrap();
        let shared_hash_p = PathBuf::from(format!("{}.hash", shared_node.olean_path.display()));
        let orig_shared_hash = fs::read_to_string(&shared_hash_p).unwrap();
        fs::write(&shared_hash_p, "0000000000000000").unwrap();
        assert!(write_hashes(&expected_main_dig, Some(&expected_main_dig), true).is_err());
        fs::write(&shared_hash_p, &orig_shared_hash).unwrap();
        let orig_main_src = fs::read_to_string(&main_untrusted.src_path).unwrap();
        fs::write(
            &main_untrusted.src_path,
            "import Shared.Util\ntheorem bad : False := sorry\n",
        )
        .unwrap();
        assert!(write_hashes(&expected_main_dig, Some(&expected_main_dig), true).is_err());
        fs::write(&main_untrusted.src_path, &orig_main_src).unwrap();
        fs::remove_file(&main_untrusted.olean_path).unwrap();
        assert!(write_hashes(&expected_main_dig, Some(&expected_main_dig), true).is_err());

        fs::write(proj_dir.join("App/Empty.lean"), b"").unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nroots = [\"App.Main\", \"App.Empty\"]\n",
        )
        .unwrap();
        let rep_empty = build_project_modules_native(
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
        assert!(rep_empty.modules_compiled >= 1);
        let cfg_empty = resolve_project_config(&proj_dir).unwrap();
        let dag_empty = build_module_dag(&cfg_empty, &[]).unwrap();
        let empty_node = dag_empty.nodes.get("App.Empty").unwrap();
        assert!(
            empty_node.olean_path.is_file()
                && empty_node.olean_path.with_extension("trace").is_file()
        );

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_lean_args_allowlist_and_per_target_resolution() {
        assert!(is_allowed_lean_arg("-DmaxHeartbeats=4000000"));
        assert!(!is_allowed_lean_arg(" -DautoImplicit=false "));
        assert!(is_allowed_lean_arg("-j8"));
        assert!(is_allowed_lean_arg("--threads=16"));
        assert!(is_allowed_lean_arg("--tstack=262144"));
        assert!(is_allowed_lean_arg("--json"));
        assert!(is_allowed_lean_arg("-q"));
        assert!(is_allowed_lean_arg("--quiet"));

        assert!(!is_allowed_lean_arg(""));
        assert!(!is_allowed_lean_arg("Foo.lean"));
        assert!(!is_allowed_lean_arg("-Dwarn.sorry=false"));
        assert!(!is_allowed_lean_arg("-D"));
        assert!(!is_allowed_lean_arg("-D=1"));
        assert!(!is_allowed_lean_arg("-Dfoo="));
        assert!(!is_allowed_lean_arg("-Dbad$key=1"));
        assert!(!is_allowed_lean_arg("-Dfoo=bar\nbaz"));
        assert!(!is_allowed_lean_arg("-ofoo.olean"));
        assert!(!is_allowed_lean_arg("--plugin=evil.so"));
        assert!(!is_allowed_lean_arg("--load-dynlib=evil.so"));
        assert!(!is_allowed_lean_arg("--run"));
        assert!(!is_allowed_lean_arg("-j0"));
        assert!(!is_allowed_lean_arg("-j65"));

        assert_eq!(
            filter_allowed_lean_args(["--json", " -q ", "--quiet", "-DautoImplicit=false"]),
            vec!["-DautoImplicit=false".to_string()]
        );
        assert_eq!(compute_lean_args_digest(&["--json".to_string()]), None);
        assert_eq!(compute_lean_args_digest(&[]), None);
        assert_eq!(
            compute_lean_args_digest(&["--plugin=evil.so".to_string(), "pos.lean".to_string()]),
            None
        );
        let d_hb_4m = compute_lean_args_digest(&["-DmaxHeartbeats=4000000".to_string()]).unwrap();
        let d_hb_200k = compute_lean_args_digest(&["-DmaxHeartbeats=200000".to_string()]).unwrap();
        assert_ne!(d_hb_4m, d_hb_200k);

        let dir = make_temp_test_dir("per_target_lean_args");
        fs::create_dir_all(dir.join("Fast")).unwrap();
        fs::create_dir_all(dir.join("Heavy")).unwrap();
        let fast_file = dir.join("Fast/Basic.lean");
        let heavy_file = dir.join("Heavy/Big.lean");
        fs::write(&fast_file, "def x : Nat := 1\n").unwrap();
        fs::write(&heavy_file, "def y : Nat := 2\n").unwrap();

        fs::write(
            dir.join("lakefile.toml"),
            r#"name = "unsafe_opts"
moreLeanArgs = ["--plugin=evil.so"]
[[lean_lib]]
name = "Fast"
roots = ["Fast"]
"#,
        )
        .unwrap();
        assert!(resolve_package_config(&dir, false).is_err());
        assert!(try_resolve_lean_args_for_path(&dir, Some(&fast_file)).is_empty());

        fs::write(
            dir.join("lakefile.toml"),
            r#"name = "demo_opts"
weakLeanArgs = ["-DmaxHeartbeats=300000"]
[leanOptions]
autoImplicit = false

[[lean_lib]]
name = "Heavy"
roots = ["Heavy"]
globs = ["Heavy.+", "Extra.+"]
moreLeanArgs = ["-DmaxHeartbeats=4000000"]

[[lean_lib]]
name = "Fast"
roots = ["Fast"]
"#,
        )
        .unwrap();

        let fast_args = try_resolve_lean_args_for_path(&dir, Some(&fast_file));
        assert_eq!(
            fast_args,
            vec![
                "-DmaxHeartbeats=300000".to_string(),
                "-DautoImplicit=false".to_string()
            ]
        );
        let heavy_args = try_resolve_lean_args_for_path(&dir, Some(&heavy_file));
        assert_eq!(
            heavy_args,
            vec![
                "-DmaxHeartbeats=300000".to_string(),
                "-DmaxHeartbeats=4000000".to_string(),
                "-DautoImplicit=false".to_string(),
            ]
        );
        // Lake ownership: globs select modules outside the roots, and a file no target owns
        // gets package-level flags rather than those of the first lib sharing its src dir.
        fs::create_dir_all(dir.join("Extra")).unwrap();
        let extra_file = dir.join("Extra/Glob.lean");
        let scratch_file = dir.join("Scratch.lean");
        fs::write(&extra_file, "def z : Nat := 3\n").unwrap();
        fs::write(&scratch_file, "def w : Nat := 4\n").unwrap();
        assert_eq!(
            try_resolve_lean_args_for_path(&dir, Some(&extra_file)),
            heavy_args
        );
        assert_eq!(
            try_resolve_lean_args_for_path(&dir, Some(&scratch_file)),
            try_resolve_lean_args_for_path(&dir, None)
        );
        assert_eq!(try_resolve_lean_args_for_path(&dir, None), fast_args);
        fs::remove_dir_all(dir).unwrap();
    }
}
