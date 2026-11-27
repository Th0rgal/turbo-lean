//! Zero-config `csimp` import policy for Lake projects (`#411`/`#412`, roadmap P9 + G1a).
//!
//! Lean and Lake trust proven `@[csimp]` theorems from imported dependency modules (they only
//! redirect compiled code, and the kernel audit still covers the compiled result), so a project
//! importing Batteries-style packages must not need a manual `[csimp] allow` flag to get a
//! verdict. This module resolves the import policy *before* expensive work:
//!
//! - dependency-package `@[csimp]` theorems are auto-allowed (zero-config), and
//! - project-owned `@[csimp]` theorems keep the manual gate: an entry the configured allowlist
//!   does not cover fails closed before any audit/replay/build work, naming the fix.
//!
//! Scraping is deliberately an over-approximation: the zygote worker only honors an allowlist
//! match for a replacement entry that really exists in the audited environment with a matching
//! `(from, to)` pair, so a scraped name that never reaches the compiled cone is inert.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use anyhow::Result;

/// Records `(effective_allowlist, configured_allowlist)` whenever `apply_env = true` extends
/// `TURBO_LEAN_ALLOWED_CSIMP` with dependency-scraped entries, so subsequent read-only preflights
/// (`freshness.rs`) still evaluate project-owned `@[csimp]` theorems against the pre-auto-allow
/// configured policy rather than treating auto-allowed dependency names as user-configured.
fn auto_allow_csimp_overlay() -> &'static Mutex<Option<(Vec<String>, Vec<String>)>> {
    static OVERLAY: OnceLock<Mutex<Option<(Vec<String>, Vec<String>)>>> = OnceLock::new();
    OVERLAY.get_or_init(|| Mutex::new(None))
}

fn configured_csimp_allowlist_from_env() -> (Vec<String>, Vec<String>) {
    let current = crate::splitter::normalized_policy_env_vec("TURBO_LEAN_ALLOWED_CSIMP");
    let guard = auto_allow_csimp_overlay()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    if let Some((ref recorded_effective, ref recorded_configured)) = *guard {
        if *recorded_effective == current {
            return (current, recorded_configured.clone());
        }
    }
    (current.clone(), current)
}

/// What the preflight should scrape.
pub(crate) enum CsimpPreflightScope {
    /// The precise target-file closure: project-owned and dependency-owned modules reachable
    /// from these files. Project-owned entries fail closed when not allowlisted.
    Targets(Vec<PathBuf>),
    /// Every dependency package's sources: auto-allow only, never fails. Used where the target
    /// files are not known yet but the effective worker policy must already be resolved.
    AllDependencyPackages,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LeanScope {
    Namespace(String),
    Section(Option<String>),
}

/// Scrape `@[csimp]`-attributed theorem names from Lean source text, fully qualified the way the
/// worker sees them.
///
/// Comments and string literals are stripped first, so a `@[csimp]` mention in documentation or
/// a string never scrapes. Names are qualified by the enclosing `namespace` scopes (`_root_.`
/// opts out), `private` theorems become `_private.<module>.0.<name>` (or `_private.*.0.<name>`
/// when no module name is provided), and both `@[csimp]` (alone, in nested attribute lists such
/// as `@[simp [bar], csimp]`, or stacked before another `@[...]`) and the `attribute [csimp] name`
/// command are recognized. Modifiers (`private`, `protected`, `public`, `meta`, `exposed`,
/// `unsafe`, `noncomputable`, `partial`, `scoped`, `local`) between the attribute and
/// `theorem`/`lemma` are skipped. The result is sorted and de-duplicated.
#[cfg(test)]
pub(crate) fn scrape_csimp_theorems(src: &str) -> Vec<String> {
    scrape_csimp_theorems_for_module(None, src)
}

pub(crate) fn scrape_csimp_theorems_for_module(module: Option<&str>, src: &str) -> Vec<String> {
    let comment_free = crate::splitter::strip_lean_comments(src);
    let clean = crate::splitter::strip_string_literals(&comment_free);
    let clean: &str = clean.as_ref();
    let mut out = BTreeSet::new();
    let mut scopes: Vec<LeanScope> = Vec::new();
    let mut private_decls: HashSet<String> = HashSet::new();
    let mut pos = 0usize;
    while let Some((tok, tok_start, tok_end)) = next_token(clean, pos) {
        pos = tok_end;
        if tok.starts_with("@[") || tok == "attribute" {
            let Some(open) = clean[tok_start..].find('[').map(|i| tok_start + i) else {
                continue;
            };
            let Some(close) = find_matching_bracket(clean, open) else {
                break;
            };
            pos = close + 1;
            if !attr_list_has_csimp(&clean[open + 1..close]) {
                continue;
            }
            if tok == "attribute" {
                let line_end = clean[pos..].find('\n').map_or(clean.len(), |i| pos + i);
                for name in clean[pos..line_end].split_whitespace() {
                    if let Some(full) = qualify_plain_name(&scopes, name) {
                        let is_priv = private_decls.contains(&full);
                        out.insert(format_csimp_name(module, &full, is_priv));
                    }
                }
                pos = line_end;
            } else if let Some((name, private)) = theorem_name_after_attribute(&clean[pos..]) {
                if let Some(full) = qualify_plain_name(&scopes, &name) {
                    if private {
                        private_decls.insert(full.clone());
                    }
                    out.insert(format_csimp_name(module, &full, private));
                }
            }
            continue;
        }
        match tok {
            "private" => {
                if let Some((next_tok, _, next_end)) = next_token(clean, pos) {
                    if matches!(next_tok, "theorem" | "lemma") {
                        if let Some((name, _, _)) = next_token(clean, next_end) {
                            if let Some(full) = qualify_plain_name(&scopes, name) {
                                private_decls.insert(full);
                            }
                        }
                    }
                }
            }
            "namespace" => {
                if let Some((ns, _, ns_end)) = next_token(clean, pos) {
                    pos = ns_end;
                    let ns = extract_decl_ident(ns);
                    let ns = ns.strip_prefix("_root_.").unwrap_or(ns);
                    for seg in ns.split('.').filter(|s| !s.is_empty()) {
                        scopes.push(LeanScope::Namespace(seg.to_string()));
                    }
                }
            }
            "section" => {
                if let Some((sec_name, _, sec_end)) = next_token_same_line(clean, pos) {
                    let sec_ident = extract_decl_ident(sec_name);
                    if !sec_ident.is_empty() && is_lean_ident_start(sec_ident) {
                        pos = sec_end;
                        scopes.push(LeanScope::Section(Some(sec_ident.to_string())));
                    } else {
                        scopes.push(LeanScope::Section(None));
                    }
                } else {
                    scopes.push(LeanScope::Section(None));
                }
            }
            "mutual" => scopes.push(LeanScope::Section(None)),
            "end" => {
                if let Some((end_tok, _, end_end)) = next_token_same_line(clean, pos) {
                    let end_ident = extract_decl_ident(end_tok);
                    let end_ident = end_ident.strip_prefix("_root_.").unwrap_or(end_ident);
                    if !end_ident.is_empty() && is_lean_ident_start(end_ident) {
                        pos = end_end;
                        pop_named_end(&mut scopes, end_ident);
                    } else {
                        scopes.pop();
                    }
                } else {
                    scopes.pop();
                }
            }
            _ => {}
        }
    }
    out.into_iter().collect()
}

/// Pop matching namespace/section frames for `end <ident>` (handling partial closes like
/// `namespace A.B ... end B ... end A` as well as `section S ... end S`).
fn pop_named_end(scopes: &mut Vec<LeanScope>, end_ident: &str) {
    if matches!(scopes.last(), Some(LeanScope::Section(Some(name))) if name == end_ident) {
        scopes.pop();
        return;
    }
    let segs: Vec<&str> = end_ident.split('.').filter(|s| !s.is_empty()).collect();
    if segs.is_empty() {
        scopes.pop();
        return;
    }
    let mut popped = 0usize;
    for seg in segs.iter().rev() {
        if matches!(scopes.last(), Some(LeanScope::Namespace(ns)) if ns == seg) {
            scopes.pop();
            popped += 1;
        } else {
            break;
        }
    }
    if popped == 0 {
        scopes.pop();
    }
}

/// The next whitespace-delimited token at or after `pos`, with its byte span.
fn next_token(s: &str, pos: usize) -> Option<(&str, usize, usize)> {
    let start = pos + s[pos..].find(|c: char| !c.is_whitespace())?;
    let end = s[start..]
        .find(char::is_whitespace)
        .map_or(s.len(), |i| start + i);
    Some((&s[start..end], start, end))
}

/// The next whitespace-delimited token on the current line (before `\n`), with its byte span.
fn next_token_same_line(s: &str, pos: usize) -> Option<(&str, usize, usize)> {
    let line_end = s[pos..].find('\n').map_or(s.len(), |i| pos + i);
    let slice = &s[pos..line_end];
    let rel_start = slice.find(|c: char| !c.is_whitespace())?;
    let start = pos + rel_start;
    let end = s[start..line_end]
        .find(char::is_whitespace)
        .map_or(line_end, |i| start + i);
    Some((&s[start..end], start, end))
}

/// Find the matching `]` for the `[` at byte index `open`, tracking nested `[...]` brackets.
fn find_matching_bracket(s: &str, open: usize) -> Option<usize> {
    let bytes = s.as_bytes();
    if bytes.get(open).copied() != Some(b'[') {
        return None;
    }
    let mut depth = 0usize;
    for (i, &b) in bytes[open..].iter().enumerate() {
        match b {
            b'[' => depth += 1,
            b']' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return Some(open + i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Whether an attribute list (`simp, csimp`, `simp [bar], csimp`, `local csimp`, ...) contains
/// the `csimp` attribute at top-level comma separation.
fn attr_list_has_csimp(list: &str) -> bool {
    let mut bracket_depth = 0usize;
    let mut paren_depth = 0usize;
    let mut start = 0usize;
    let bytes = list.as_bytes();
    let check_item = |item: &str| {
        let words: Vec<&str> = item.split_whitespace().collect();
        words == ["csimp"] || words == ["local", "csimp"] || words == ["scoped", "csimp"]
    };
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'[' => bracket_depth += 1,
            b']' => bracket_depth = bracket_depth.saturating_sub(1),
            b'(' => paren_depth += 1,
            b')' => paren_depth = paren_depth.saturating_sub(1),
            b',' if bracket_depth == 0 && paren_depth == 0 => {
                if check_item(&list[start..i]) {
                    return true;
                }
                start = i + 1;
            }
            _ => {}
        }
    }
    check_item(&list[start..])
}

fn is_lean_ident_start(s: &str) -> bool {
    s.chars()
        .next()
        .is_some_and(|c| c.is_alphabetic() || c == '_' || c == '«')
}

/// Extract the leading Lean identifier from a token, stripping trailing universe params (`.{u}`),
/// attached binders (`(`, `{`, `[`), or punctuation (`:`, `,`, `;`, `=`), while preserving
/// guillemet-quoted segments (`«...»`).
fn extract_decl_ident(raw: &str) -> &str {
    let mut in_guillemet = false;
    let mut chars = raw.char_indices().peekable();
    let mut end = raw.len();
    while let Some((idx, ch)) = chars.next() {
        if in_guillemet {
            if ch == '»' {
                in_guillemet = false;
            }
            continue;
        }
        match ch {
            '«' => in_guillemet = true,
            '(' | '{' | '[' | ':' | ',' | ';' | '=' => {
                end = idx;
                break;
            }
            '.' if matches!(chars.peek(), Some(&(_, '{'))) => {
                end = idx;
                break;
            }
            _ => {}
        }
    }
    &raw[..end]
}

/// Qualify a declared `@[csimp]` name by the open namespaces, as Lean elaborates it.
fn qualify_plain_name(scopes: &[LeanScope], name: &str) -> Option<String> {
    let name = extract_decl_ident(name);
    if name.is_empty() || !is_lean_ident_start(name) {
        return None;
    }
    let full = match name.strip_prefix("_root_.") {
        Some(rooted) => rooted.to_string(),
        None => scopes
            .iter()
            .filter_map(|s| match s {
                LeanScope::Namespace(ns) => Some(ns.as_str()),
                LeanScope::Section(_) => None,
            })
            .chain(std::iter::once(name))
            .collect::<Vec<_>>()
            .join("."),
    };
    Some(full)
}

/// Format a qualified declaration name, applying Lean's `_private.<module>.0.<name>` mangling
/// when `private` is set (scoping private dependency entries strictly to their declaring module).
fn format_csimp_name(module: Option<&str>, full: &str, private: bool) -> String {
    if !private {
        return full.to_string();
    }
    match module.map(str::trim).filter(|m| !m.is_empty()) {
        Some(m) => format!("_private.{m}.0.{full}"),
        None => format!("_private.*.0.{full}"),
    }
}

/// The declaration name introduced by the next `theorem`/`lemma` after an attribute, skipping
/// stacked `@[...]` attributes and modifiers, plus whether it is `private`. Returns `None` when
/// the next declaration is not a theorem.
fn theorem_name_after_attribute(rest: &str) -> Option<(String, bool)> {
    let mut pos = 0usize;
    let mut private = false;
    let kw = loop {
        let (tok, tok_start, tok_end) = next_token(rest, pos)?;
        if tok.starts_with("@[") {
            let open = rest[tok_start..].find('[').map(|i| tok_start + i)?;
            let close = find_matching_bracket(rest, open)?;
            pos = close + 1;
            continue;
        }
        pos = tok_end;
        match tok {
            "private" => private = true,
            "protected" | "public" | "meta" | "exposed" | "unsafe" | "noncomputable" | "partial"
            | "scoped" | "local" => {}
            kw => break kw,
        }
    };
    if kw != "theorem" && kw != "lemma" {
        return None;
    }
    let (name, _, _) = next_token(rest, pos)?;
    Some((name.to_string(), private))
}

/// One scraped module contribution: the owning module name plus its `@[csimp]` theorem names.
fn scrape_module_csimp_theorems(module: &str, src: &str) -> Vec<(String, String)> {
    scrape_csimp_theorems_for_module(Some(module), src)
        .into_iter()
        .map(|t| (module.to_string(), t))
        .collect()
}

/// Derive the dot-separated Lean module name for a project target file.
fn target_file_module_name(
    canon_dir: &Path,
    tf: &Path,
    root_cfg: Option<&crate::module_builder::ProjectConfig>,
) -> Option<String> {
    let canon_tf = tf.canonicalize().ok();
    let candidates: [&Path; 2] = [tf, canon_tf.as_deref().unwrap_or(tf)];
    if let Some(cfg) = root_cfg {
        let src_base = cfg.root_pkg.pkg_root.join(&cfg.root_pkg.src_dir);
        let canon_src_base = src_base.canonicalize().ok();
        for base in [Some(src_base.as_path()), canon_src_base.as_deref()]
            .into_iter()
            .flatten()
        {
            for cand in candidates {
                if let Ok(rel) = cand.strip_prefix(base) {
                    let mod_dots = rel
                        .with_extension("")
                        .to_string_lossy()
                        .replace('\\', "/")
                        .trim_matches('/')
                        .replace('/', ".");
                    if !mod_dots.is_empty() {
                        return Some(mod_dots);
                    }
                }
            }
        }
    }
    for cand in candidates {
        if let Ok(rel) = cand.strip_prefix(canon_dir) {
            let rel_no_ext = rel.with_extension("");
            let mut comps = rel_no_ext.components();
            if let Some(first) = comps.next().and_then(|c| c.as_os_str().to_str()) {
                let rest: PathBuf = comps.collect();
                let module = if matches!(first, "submission" | "src" | "lean")
                    && !rest.as_os_str().is_empty()
                {
                    rest.to_string_lossy().replace('\\', "/")
                } else {
                    rel_no_ext.to_string_lossy().replace('\\', "/")
                };
                let mod_dots = module.trim_matches('/').replace('/', ".");
                if !mod_dots.is_empty() {
                    return Some(mod_dots);
                }
            }
        }
    }
    None
}

/// Walk the transitive import closure of `target_files`, classifying every reachable module as
/// project-owned or dependency-owned, and scrape the `@[csimp]` theorems each module's source
/// declares. Returns the project-owned module names plus all `(owner module, theorem)` entries.
///
/// Modules that cannot be classified or whose source is unreadable are skipped (the freshness
/// gate and the worker's kernel gate stay the authority); this preflight only ever adds an
/// earlier, actionable decision on what it can prove.
fn collect_target_csimp_entries(
    canon_dir: &Path,
    target_files: &[PathBuf],
    root_cfg: Option<&crate::module_builder::ProjectConfig>,
) -> (BTreeSet<String>, Vec<(String, String)>) {
    let mut owned_modules: BTreeSet<String> = BTreeSet::new();
    let mut entries: Vec<(String, String)> = Vec::new();
    let mut visited: HashSet<String> = HashSet::new();
    let mut src_memo: HashMap<PathBuf, Option<String>> = HashMap::new();

    let mut worklist: Vec<String> = Vec::new();
    for tf in target_files {
        // The target file itself is a project-owned module: derive its dot-separated module name
        // so `owned_modules` and `visited` match `entries` even for nested paths (`Sub/Own.lean`).
        if let Some(module_dots) = target_file_module_name(canon_dir, tf, root_cfg) {
            owned_modules.insert(module_dots.clone());
            visited.insert(module_dots.clone());
            if let Some(src) = read_scrape_src(&mut src_memo, tf) {
                entries.extend(scrape_module_csimp_theorems(&module_dots, &src));
                if let Some(hdr) = parse_header(&src) {
                    worklist.extend(hdr.imports);
                }
            }
        } else if let Some(src) = read_scrape_src(&mut src_memo, tf) {
            if let Some(hdr) = parse_header(&src) {
                worklist.extend(hdr.imports);
            }
        }
    }

    while let Some(mod_name) = worklist.pop() {
        if !visited.insert(mod_name.clone()) {
            continue;
        }
        let Some((owner, src_path)) = classify_module(canon_dir, root_cfg, &mod_name) else {
            continue;
        };
        let Some(src) = read_scrape_src(&mut src_memo, &src_path) else {
            continue;
        };
        match owner {
            ModuleOwner::Project => {
                owned_modules.insert(mod_name.clone());
            }
            ModuleOwner::Dependency => {}
        }
        entries.extend(scrape_module_csimp_theorems(&mod_name, &src));
        if let Some(hdr) = parse_header(&src) {
            worklist.extend(hdr.imports);
        }
    }
    (owned_modules, entries)
}

enum ModuleOwner {
    Project,
    Dependency,
}

/// Resolve which package owns `mod_name` and where its source lives.
fn classify_module(
    canon_dir: &Path,
    root_cfg: Option<&crate::module_builder::ProjectConfig>,
    mod_name: &str,
) -> Option<(ModuleOwner, PathBuf)> {
    if let Some(cfg) = root_cfg {
        if let Some(spec) =
            crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, mod_name)
        {
            return Some((ModuleOwner::Project, spec.src_path));
        }
        return match crate::module_builder::resolve_import_site(cfg, mod_name) {
            crate::module_builder::ImportSite::Module(spec) => {
                Some((ModuleOwner::Dependency, spec.src_path))
            }
            _ => None,
        };
    }
    // Standalone directory: the legacy filesystem lookup, everything non-toolchain is project-owned.
    let rel_slash = crate::module_builder::module_name_to_rel_slash(mod_name);
    resolve_project_lean_source_local(canon_dir, &rel_slash).map(|p| (ModuleOwner::Project, p))
}

fn resolve_project_lean_source_local(canon_dir: &Path, rel_slash: &str) -> Option<PathBuf> {
    let rel_file = format!("{rel_slash}.lean");
    let direct = canon_dir.join(&rel_file);
    if direct.is_file() {
        return Some(direct);
    }
    for prefix in ["submission", "src", "lean"] {
        let cand = canon_dir.join(prefix).join(&rel_file);
        if cand.is_file() {
            return Some(cand);
        }
    }
    None
}

fn parse_header(src: &str) -> Option<crate::module_builder::HeaderInfo> {
    let hdr = crate::module_builder::parse_header_info(src);
    if hdr.header_error.is_some() {
        None
    } else {
        Some(hdr)
    }
}

fn read_scrape_src(memo: &mut HashMap<PathBuf, Option<String>>, path: &Path) -> Option<String> {
    if let Some(hit) = memo.get(path) {
        return hit.clone();
    }
    let read = fs::read_to_string(path).ok();
    memo.insert(path.to_path_buf(), read.clone());
    read
}

/// Resolve the zero-config `csimp` import policy for `scope` and, when `apply_env` is set,
/// export the effective allowlist through `TURBO_LEAN_ALLOWED_CSIMP` for the rest of the run.
///
/// Fails closed (before expensive work) when a project-owned `@[csimp]` theorem is not covered
/// by the configured allowlist. Dependency-package entries are always auto-allowed.
pub(crate) fn preflight_zero_config_csimp_import_policy(
    canon_dir: &Path,
    scope: CsimpPreflightScope,
    apply_env: bool,
) -> Result<()> {
    let (current_env, configured) = configured_csimp_allowlist_from_env();
    let (owned_modules, entries) = match scope {
        CsimpPreflightScope::Targets(target_files) => {
            let root_cfg = crate::module_builder::resolve_project_config(canon_dir).ok();
            collect_target_csimp_entries(canon_dir, &target_files, root_cfg.as_ref())
        }
        CsimpPreflightScope::AllDependencyPackages => {
            let cfg = match crate::module_builder::resolve_project_config(canon_dir) {
                Ok(cfg) => cfg,
                Err(_) => return Ok(()),
            };
            let mut entries = Vec::new();
            for dp in &cfg.dep_pkgs {
                for src in dep_package_sources(dp) {
                    if let Ok(src_text) = fs::read_to_string(&src) {
                        let module = module_label_for_dep_source(dp, &src);
                        entries.extend(scrape_module_csimp_theorems(&module, &src_text));
                    }
                }
            }
            (BTreeSet::new(), entries)
        }
    };
    if entries.is_empty() {
        return Ok(());
    }
    let effective =
        crate::kernel::effective_csimp_policy_allowlist(&owned_modules, &entries, &configured)?;
    if apply_env && effective != current_env {
        std::env::set_var("TURBO_LEAN_ALLOWED_CSIMP", effective.join(","));
        let mut guard = auto_allow_csimp_overlay()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        *guard = Some((effective, configured));
    }
    Ok(())
}

/// Every `.lean` source under a dependency package's source directory (stable order), skipping
/// `.lake`/`.git` metadata directories, root `lakefile.lean`, and symlink cycles.
///
/// `src_dir` is stored relative to the package root, so the walk joins it with `pkg_root`.
fn dep_package_sources(pkg: &crate::module_builder::PackageConfig) -> Vec<PathBuf> {
    let src_base = pkg.pkg_root.join(&pkg.src_dir);
    let canon_pkg_root = pkg.pkg_root.canonicalize().ok();
    let mut out = Vec::new();
    let mut stack = vec![src_base];
    let mut seen_dirs: HashSet<PathBuf> = HashSet::new();
    while let Some(dir) = stack.pop() {
        let dir_key = dir.canonicalize().unwrap_or_else(|_| dir.clone());
        if !seen_dirs.insert(dir_key) {
            continue;
        }
        let Ok(read) = fs::read_dir(&dir) else {
            continue;
        };
        let mut entries: Vec<_> = read.filter_map(|e| e.ok()).collect();
        entries.sort_by_key(|e| e.file_name());
        for entry in entries {
            let file_name = entry.file_name();
            let name_str = file_name.to_string_lossy();
            if name_str == ".lake" || name_str == ".git" {
                continue;
            }
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().and_then(|e| e.to_str()) == Some("lean") {
                if name_str == "lakefile.lean"
                    && path.parent().and_then(|p| p.canonicalize().ok()) == canon_pkg_root
                {
                    continue;
                }
                out.push(path);
            }
        }
    }
    out.sort();
    out.dedup();
    out
}

/// A stable attribution label for a scraped dependency source path. Dependency sources are
/// scraped only to auto-allow theorem names, so the label only has to be deterministic.
fn module_label_for_dep_source(pkg: &crate::module_builder::PackageConfig, src: &Path) -> String {
    let src_base = pkg.pkg_root.join(&pkg.src_dir);
    let rel = src
        .strip_prefix(&src_base)
        .unwrap_or(src)
        .with_extension("");
    let rel = rel.to_string_lossy().replace('\\', "/");
    if rel.is_empty() {
        pkg.name.clone()
    } else {
        rel.replace('/', ".")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scrape_csimp_theorems_basic_and_noise() {
        let src = "\
@[csimp] theorem fast_eq : @slow = @fast := rfl
private theorem not_csimp : True := trivial
/-- doc comment mentioning @[csimp] theorem doc_mention -/
def s : String := \"@[csimp] theorem str_mention\"
@[csimp]
private theorem modified_eq : @a = @b := rfl
@[csimp] def not_a_theorem := 0
@[implemented_by fast] def gated := 0
@[csimp] theorem dup_eq : @x = @x := rfl
@[csimp] theorem dup_eq : @x = @x := rfl
";
        let scraped = scrape_csimp_theorems(src);
        assert_eq!(
            scraped,
            vec![
                "_private.*.0.modified_eq".to_string(),
                "dup_eq".to_string(),
                "fast_eq".to_string(),
            ],
            "scrape must skip doc/string mentions, non-theorem decls, and dedup+sort"
        );
    }

    #[test]
    fn test_scrape_csimp_theorems_qualifies_namespaces() {
        let src = "\
namespace List
@[csimp] theorem scan_eq : @scan = @scanTR := rfl
section Inner
@[simp, csimp] lemma fold_eq : @fold = @foldTR := rfl
end Inner
namespace Nested.Deep
@[csimp] protected theorem deep_eq : @a = @b := rfl
@[csimp] theorem _root_.Top.rooted_eq : @c = @d := rfl
end Nested.Deep
theorem plain : True := trivial
attribute [csimp] plain
end List
@[csimp] theorem outside_eq : @e = @f := rfl
noncomputable section
@[local csimp] theorem in_anon_section : @g = @h := rfl
end
";
        assert_eq!(
            scrape_csimp_theorems(src),
            vec![
                "List.Nested.Deep.deep_eq".to_string(),
                "List.fold_eq".to_string(),
                "List.plain".to_string(),
                "List.scan_eq".to_string(),
                "Top.rooted_eq".to_string(),
                "in_anon_section".to_string(),
                "outside_eq".to_string(),
            ],
            "names must be qualified as Lean elaborates them"
        );
        // The qualified names are what a user writes under `[csimp] allow`, and what the worker
        // matches, so a namespaced project allowlist entry covers the scraped theorem.
        assert!(crate::kernel::csimp_pattern_allows(
            &["List.*".to_string()],
            "List.scan_eq"
        ));
    }

    #[test]
    fn test_scrape_csimp_theorems_empty_and_comment_only() {
        assert!(scrape_csimp_theorems("").is_empty());
        assert!(scrape_csimp_theorems("-- @[csimp] theorem commented\n").is_empty());
        assert!(scrape_csimp_theorems("/-! @[csimp] theorem block /\n").is_empty());
    }

    #[test]
    fn test_collect_target_csimp_entries_standalone_owns_targets() {
        let dir = std::env::temp_dir().join(format!(
            "tl_csimp_scrape_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(dir.join("Sub")).unwrap();
        let target = dir.join("Main.lean");
        fs::write(
            &target,
            "import Sub.Dep\n@[csimp] theorem own_eq : @slow = @fast := rfl\n",
        )
        .unwrap();
        fs::write(dir.join("Sub/Dep.lean"), "def slow := 1\ndef fast := 1\n").unwrap();

        let (owned, entries) = collect_target_csimp_entries(&dir, &[target], None);
        assert!(
            owned.contains("Main"),
            "target file must be classified project-owned: {owned:?}"
        );
        assert!(
            entries.contains(&("Main".to_string(), "own_eq".to_string())),
            "own csimp entry must be scraped: {entries:?}"
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_scrape_csimp_theorems_adversarial_syntax_and_module_scoped_private() {
        let src = "\
@[csimp] public theorem pub_eq : @a = @b := rfl
@[csimp]
@[simp [foo, bar]]
private lemma stacked_eq.{u}(x : Nat) : @c = @d := rfl
@[simp [baz, qux], csimp] theorem nested_attr_eq{α} : @e = @f := rfl
namespace A.B
@[csimp] theorem in_ab[BEq Nat] : @g = @h := rfl
end B
@[csimp] theorem in_a : @i = @j := rfl
end A
private theorem late_priv : @k = @l := rfl
attribute [csimp] late_priv
";
        let scraped = scrape_csimp_theorems_for_module(Some("Batteries.Fast"), src);
        assert_eq!(
            scraped,
            vec![
                "A.B.in_ab".to_string(),
                "A.in_a".to_string(),
                "_private.Batteries.Fast.0.late_priv".to_string(),
                "_private.Batteries.Fast.0.stacked_eq".to_string(),
                "nested_attr_eq".to_string(),
                "pub_eq".to_string(),
            ],
            "scraper must handle Lean 4.35 modifiers, stacked/nested attrs, binders/univs, partial end, and module-scoped private names"
        );
    }

    #[test]
    fn test_collect_target_csimp_entries_nested_target_is_project_owned() {
        let dir = std::env::temp_dir().join(format!(
            "tl_csimp_nested_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(dir.join("Sub")).unwrap();
        let target = dir.join("Sub/Own.lean");
        fs::write(
            &target,
            "@[csimp] public theorem nested_own_eq : @slow = @fast := rfl\n",
        )
        .unwrap();

        let (owned, entries) = collect_target_csimp_entries(&dir, &[target], None);
        assert!(
            owned.contains("Sub.Own"),
            "nested target module must be recorded dot-separated in owned_modules: {owned:?}"
        );
        assert!(
            entries.contains(&("Sub.Own".to_string(), "nested_own_eq".to_string())),
            "nested target csimp entry must be scraped under Sub.Own: {entries:?}"
        );
        let err = crate::kernel::effective_csimp_policy_allowlist(&owned, &entries, &[])
            .expect_err("nested target project-owned csimp must fail closed");
        assert!(
            format!("{err:#}").contains("nested_own_eq"),
            "error must name nested_own_eq: {err:#}"
        );
        let _ = fs::remove_dir_all(&dir);
    }
}
