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

use anyhow::Result;

/// What the preflight should scrape.
pub(crate) enum CsimpPreflightScope {
    /// The precise target-file closure: project-owned and dependency-owned modules reachable
    /// from these files. Project-owned entries fail closed when not allowlisted.
    Targets(Vec<PathBuf>),
    /// Every dependency package's sources: auto-allow only, never fails. Used where the target
    /// files are not known yet but the effective worker policy must already be resolved.
    AllDependencyPackages,
}

/// Scrape `@[csimp]`-attributed theorem names from Lean source text, fully qualified the way the
/// worker sees them.
///
/// Comments and string literals are stripped first, so a `@[csimp]` mention in documentation or
/// a string never scrapes. Names are qualified by the enclosing `namespace` scopes (`_root_.`
/// opts out), `private` theorems become the `_private.*.0.<name>` glob of Lean's private-name
/// mangling, and both `@[csimp]` (alone or in an attribute list such as `@[simp, csimp]`) and
/// the `attribute [csimp] name` command are recognized. Modifiers (`private`, `protected`,
/// `unsafe`, `noncomputable`, `partial`) between the attribute and `theorem`/`lemma` are skipped.
/// The result is sorted and de-duplicated.
pub(crate) fn scrape_csimp_theorems(src: &str) -> Vec<String> {
    let comment_free = crate::splitter::strip_lean_comments(src);
    let clean = crate::splitter::strip_string_literals(&comment_free);
    let clean: &str = clean.as_ref();
    let mut out = BTreeSet::new();
    // One entry per open scope: the namespace components it adds (`section`/`mutual` add none).
    let mut scopes: Vec<Vec<String>> = Vec::new();
    let mut pos = 0usize;
    while let Some((tok, tok_start, tok_end)) = next_token(clean, pos) {
        pos = tok_end;
        if tok.starts_with("@[") || tok == "attribute" {
            let Some(open) = clean[tok_start..].find('[').map(|i| tok_start + i) else {
                continue;
            };
            let Some(close) = clean[open..].find(']').map(|i| open + i) else {
                break;
            };
            pos = close + 1;
            if !attr_list_has_csimp(&clean[open + 1..close]) {
                continue;
            }
            if tok == "attribute" {
                let line_end = clean[pos..].find('\n').map_or(clean.len(), |i| pos + i);
                for name in clean[pos..line_end].split_whitespace() {
                    if let Some(full) = qualify_csimp_name(&scopes, name, false) {
                        out.insert(full);
                    }
                }
                pos = line_end;
            } else if let Some((name, private)) = theorem_name_after_attribute(&clean[pos..]) {
                if let Some(full) = qualify_csimp_name(&scopes, &name, private) {
                    out.insert(full);
                }
            }
            continue;
        }
        match tok {
            "namespace" => {
                if let Some((ns, _, ns_end)) = next_token(clean, pos) {
                    pos = ns_end;
                    let ns = ns.strip_prefix("_root_.").unwrap_or(ns);
                    scopes.push(ns.split('.').map(str::to_string).collect());
                }
            }
            "section" | "mutual" => scopes.push(Vec::new()),
            "end" => {
                scopes.pop();
            }
            _ => {}
        }
    }
    out.into_iter().collect()
}

/// The next whitespace-delimited token at or after `pos`, with its byte span.
fn next_token(s: &str, pos: usize) -> Option<(&str, usize, usize)> {
    let start = pos + s[pos..].find(|c: char| !c.is_whitespace())?;
    let end = s[start..]
        .find(char::is_whitespace)
        .map_or(s.len(), |i| start + i);
    Some((&s[start..end], start, end))
}

/// Whether an attribute list (`simp, csimp`, `local csimp`, ...) contains the `csimp` attribute.
fn attr_list_has_csimp(list: &str) -> bool {
    list.split(',').any(|attr| {
        let words: Vec<&str> = attr.split_whitespace().collect();
        words == ["csimp"] || words == ["local", "csimp"] || words == ["scoped", "csimp"]
    })
}

/// Qualify a declared `@[csimp]` name by the open namespaces, as Lean elaborates it.
fn qualify_csimp_name(scopes: &[Vec<String>], name: &str, private: bool) -> Option<String> {
    let name = name.trim_end_matches([':', ',']);
    if name.is_empty()
        || !name
            .chars()
            .next()
            .is_some_and(|c| c.is_alphabetic() || c == '_')
    {
        return None;
    }
    let full = match name.strip_prefix("_root_.") {
        Some(rooted) => rooted.to_string(),
        None => scopes
            .iter()
            .flatten()
            .map(String::as_str)
            .chain(std::iter::once(name))
            .collect::<Vec<_>>()
            .join("."),
    };
    Some(if private {
        format!("_private.*.0.{full}")
    } else {
        full
    })
}

/// The declaration name introduced by the next `theorem`/`lemma` after an attribute, skipping
/// modifiers, plus whether it is `private`. Returns `None` when the next declaration is not a
/// theorem.
fn theorem_name_after_attribute(rest: &str) -> Option<(String, bool)> {
    let mut tokens = rest.split_whitespace();
    let mut private = false;
    let kw = loop {
        match tokens.next()? {
            "private" => private = true,
            "protected" | "unsafe" | "noncomputable" | "partial" => {}
            kw => break kw,
        }
    };
    if kw != "theorem" && kw != "lemma" {
        return None;
    }
    Some((tokens.next()?.to_string(), private))
}

/// One scraped module contribution: the owning module name plus its `@[csimp]` theorem names.
fn scrape_module_csimp_theorems(module: &str, src: &str) -> Vec<(String, String)> {
    scrape_csimp_theorems(src)
        .into_iter()
        .map(|t| (module.to_string(), t))
        .collect()
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
        // The target file itself is a project-owned module: derive its module name from the
        // path relative to the project (same convention as the freshness gate).
        if let Ok(rel) = tf.strip_prefix(canon_dir) {
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
                if !module.is_empty() {
                    owned_modules.insert(module.clone());
                    visited.insert(module.clone());
                    let module_dots = module.replace('/', ".");
                    if let Some(src) = read_scrape_src(&mut src_memo, tf) {
                        entries.extend(scrape_module_csimp_theorems(&module_dots, &src));
                        if let Some(hdr) = parse_header(&src) {
                            worklist.extend(hdr.imports);
                        }
                    }
                }
            }
        }
    }
    worklist.extend(
        target_files
            .iter()
            .filter_map(|tf| read_header_imports(tf))
            .flatten(),
    );

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

fn read_header_imports(path: &Path) -> Option<Vec<String>> {
    let content = fs::read_to_string(path).ok()?;
    parse_header(&content).map(|hdr| hdr.imports)
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
    let configured = crate::splitter::normalized_policy_env_vec("TURBO_LEAN_ALLOWED_CSIMP");
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
    if apply_env && effective != configured {
        std::env::set_var("TURBO_LEAN_ALLOWED_CSIMP", effective.join(","));
    }
    Ok(())
}

/// Every `.lean` source under a dependency package's source directory (stable order).
///
/// `src_dir` is stored relative to the package root, so the walk joins it with `pkg_root`.
fn dep_package_sources(pkg: &crate::module_builder::PackageConfig) -> Vec<PathBuf> {
    let src_base = pkg.pkg_root.join(&pkg.src_dir);
    let mut out = Vec::new();
    let mut stack = vec![src_base.clone()];
    let mut seen_dirs: HashSet<PathBuf> = HashSet::new();
    while let Some(dir) = stack.pop() {
        if !seen_dirs.insert(dir.clone()) {
            continue;
        }
        let Ok(read) = fs::read_dir(&dir) else {
            continue;
        };
        let mut entries: Vec<_> = read.filter_map(|e| e.ok()).collect();
        entries.sort_by_key(|e| e.file_name());
        for entry in entries {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().and_then(|e| e.to_str()) == Some("lean") {
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
}
