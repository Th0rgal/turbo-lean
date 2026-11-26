use super::*;

pub(crate) fn purge_elab_host_effect_artifacts_in_closure(
    cfg: &ProjectConfig,
    seeds: &[String],
) -> Result<bool> {
    let mut visited = HashSet::new();
    let mut postorder: Vec<DiscoveredModuleSpec> = Vec::new();
    let mut stack: Vec<(DiscoveredModuleSpec, bool)> = seeds
        .iter()
        .filter_map(|imp| {
            let site = match resolve_module_in_package(&cfg.root_pkg, true, imp) {
                Some(rs) => ImportSite::Module(Box::new(rs)),
                None => resolve_import_site(cfg, imp),
            };
            match site {
                ImportSite::Module(spec) => Some((*spec, false)),
                _ => None,
            }
        })
        .collect();
    while let Some((spec, expanded)) = stack.pop() {
        let key = (spec.pkg_root.clone(), spec.module_name.clone());
        if expanded {
            postorder.push(spec);
            continue;
        }
        if !visited.insert(key) {
            continue;
        }
        let sub_imps = fs::read_to_string(&spec.src_path)
            .ok()
            .map(|s| parse_header_info(&s))
            .filter(|h| h.header_error.is_none())
            .map(|h| h.imports)
            .unwrap_or_default();
        stack.push((spec, true));
        for sub in sub_imps {
            let site = match resolve_module_in_package(&cfg.root_pkg, true, &sub) {
                Some(rs) => ImportSite::Module(Box::new(rs)),
                None => resolve_import_site(cfg, &sub),
            };
            if let ImportSite::Module(sub_spec) = site {
                if !visited.contains(&(sub_spec.pkg_root.clone(), sub_spec.module_name.clone())) {
                    stack.push((*sub_spec, false));
                }
            }
        }
    }
    // #438 / #433: only spreading taint (import-time host reads and invocable-definer
    // bodies, plus every fail-closed shape) walks up to importers; a self-only tainted
    // module (a `run_cmd` reading host state, an uncovered `include_str`) is purged
    // alone. Its importers stay pinned to its artifact digest through the
    // verified-source stamps and Lake traces, so a rebuilt artifact still invalidates
    // them without deleting whole import closures up front. Deletion honors the #434
    // ownership guard: a module the project does not own is never deleted here. A
    // refusal is keyed on that module's OWN artifact — a pinned `#eval` or `run_cmd`
    // is a static property of the source, and bailing on it would brick every later
    // refresh. When the unowned artifact is fresh (what the pin built, or nothing on
    // disk at all): a module with SPREADING taint is still marked spreading, so the
    // owned importers are purged and rebuilt against its digest; a `SelfOnly` module
    // is skipped outright, because its digest does not change and the digest pin
    // already covers its importers. Only a stale unowned artifact fails the walk
    // closed (below), because a later build could reuse it as fresh and only its own
    // workspace may rebuild it.
    let mut spreading: HashSet<(PathBuf, String)> = HashSet::new();
    let mut purged_any = false;
    for spec in postorder {
        let key = (spec.pkg_root.clone(), spec.module_name.clone());
        let purgeable = spec_artifacts_purgeable_from_project_root(cfg, &spec);
        // The stale-and-unowned case: these artifacts may embed host state, Lake's
        // traces do not cover host reads, and deleting is not ours to do (#434: the
        // package belongs to a shared or foreign checkout), so the walk fails closed,
        // deletes nothing, and names the action that clears the condition: an
        // own-workspace rebuild refreshes the stale artifact, after which the walk no
        // longer refuses. Staleness is the mtime gate of
        // `spec_own_artifact_stale_on_disk` (source, package config, resolved
        // `include_str` targets); a `run_cmd` host read whose external input changed
        // is beyond it and stays undetected here by design.
        let refuse_purge = |spec: &DiscoveredModuleSpec| -> Result<()> {
            anyhow::bail!(
                "Failed to purge stale build artifact(s) of {} ({}): the module's \
                 artifacts are stale and the package is not purgeable from this \
                 project root (a shared or foreign checkout). Rebuild it in its own \
                 workspace (`lake build {}` from {}) to refresh its artifacts, then \
                 rerun.",
                spec.module_name,
                spec.pkg_root.display(),
                spec.module_name,
                spec.pkg_root.display()
            )
        };
        let Ok(src_raw) = fs::read_to_string(&spec.src_path) else {
            spreading.insert(key);
            if purgeable {
                crate::lake_build::remove_spec_build_artifacts_checked(&spec)?;
                purged_any = true;
            } else if spec_own_artifact_stale_on_disk(&spec) {
                refuse_purge(&spec)?;
            }
            continue;
        };
        let hdr = parse_header_info(&src_raw);
        let imports_spreading = hdr.header_error.is_some()
            || hdr.imports.iter().any(|sub| {
                let site = match resolve_module_in_package(&cfg.root_pkg, true, sub) {
                    Some(rs) => ImportSite::Module(Box::new(rs)),
                    None => resolve_import_site(cfg, sub),
                };
                match site {
                    ImportSite::Module(sub_spec) => {
                        spreading.contains(&(sub_spec.pkg_root, sub_spec.module_name))
                    }
                    _ => false,
                }
            });
        let taint = spec_source_host_effect_taint(cfg, &spec, &src_raw);
        if imports_spreading || taint.spreads_to_importers() {
            spreading.insert(key);
            if purgeable {
                crate::lake_build::remove_spec_build_artifacts_checked(&spec)?;
                purged_any = true;
            } else if spec_own_artifact_stale_on_disk(&spec) {
                refuse_purge(&spec)?;
            }
        } else if taint.is_tainted() {
            if purgeable {
                crate::lake_build::remove_spec_build_artifacts_checked(&spec)?;
                purged_any = true;
            } else if spec_own_artifact_stale_on_disk(&spec) {
                refuse_purge(&spec)?;
            }
            // Unowned, fresh, `SelfOnly`: skipped outright. The artifact is what the
            // pin built, its digest does not change, and importers are pinned to that
            // digest by the verified-source stamps and Lake traces, so purging them
            // would rebuild identical artifacts while forcing the no-cache path on
            // every refresh (DA 71add786 finding 3).
        }
    }
    Ok(purged_any)
}

/// Whether `spec`'s own on-disk `.olean` is stale by the cheap mtime gates the
/// dependency freshness check also applies: present but older than the module source,
/// a package config file, or a resolved literal `include_str` target (a regenerated
/// gitignored target goes stale with no source mtime change, DA 71add786 finding 1).
/// A missing artifact is NOT stale here — nothing is on disk for a later build to
/// reuse, so a purge refusal would protect nothing. Beyond an mtime gate by design,
/// and so undetected here: a `run_cmd` host read whose external input changed, and a
/// non-literal or unresolvable `include_str` target.
fn spec_own_artifact_stale_on_disk(spec: &DiscoveredModuleSpec) -> bool {
    let olean = spec_olean_path(spec);
    let Ok(om) = fs::metadata(&olean) else {
        return false;
    };
    let Ok(ot) = om.modified() else {
        return true;
    };
    let newer_than_olean = |p: &Path| {
        fs::metadata(p)
            .and_then(|m| m.modified())
            .is_ok_and(|t| ot < t)
    };
    if newer_than_olean(&spec.src_path)
        || ["lakefile.toml", "lakefile.lean", "lean-toolchain"]
            .iter()
            .any(|f| newer_than_olean(&spec.pkg_root.join(f)))
    {
        return true;
    }
    // Resolved literal `include_str` targets are part of the artifact's input set.
    let Ok(src_raw) = fs::read_to_string(&spec.src_path) else {
        return true;
    };
    if !source_uses_include_str(&src_raw) {
        return false;
    }
    let Some(rels) = crate::splitter::extract_include_relative_paths(&src_raw) else {
        return false;
    };
    let Some(src_dir) = spec.src_path.parent() else {
        return false;
    };
    rels.iter().any(|rel| newer_than_olean(&src_dir.join(rel)))
}

/// #433: how a module's source can make its compiled artifacts depend on host state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HostEffectTaint {
    /// No host-state dependence that stamp / CAS / warm-adoption reuse has to respect.
    None,
    /// The module's own `.olean` may depend on host state, so its artifacts are never
    /// stamp- or cache-reused, but importing it executes nothing host-reading: the taint
    /// stays on the module and reaches importers only through its artifact digest, which
    /// the verified-source stamps and Lake traces already pin.
    SelfOnly,
    /// Code in this module re-runs inside importers — `initialize` /
    /// `builtin_initialize` / `@[init]` bodies at import time, and invocable
    /// definitions (elaborators, tactics, simprocs, linters) whenever an importer
    /// elaborates the syntax they handle — and an unreadable or unresolvable source
    /// fails closed, so the taint spreads to the whole importer cone.
    SpreadsToImporters,
}

impl HostEffectTaint {
    pub(crate) fn is_tainted(self) -> bool {
        !matches!(self, HostEffectTaint::None)
    }
    pub(crate) fn spreads_to_importers(self) -> bool {
        matches!(self, HostEffectTaint::SpreadsToImporters)
    }
}

const DECL_MODIFIER_WORDS: &[&str] = &[
    "private",
    "protected",
    "public",
    "scoped",
    "local",
    "noncomputable",
    "unsafe",
    "partial",
    "nonrec",
    "meta",
];

/// True for a line holding only attribute groups (`@[...]`) and declaration modifiers,
/// i.e. a line that cannot be a whole declaration by itself.
fn line_is_attr_or_modifier_only(uq_line: &str) -> bool {
    let mut rest = uq_line.trim();
    if rest.is_empty() {
        return false;
    }
    while !rest.is_empty() {
        if let Some(tail) = rest.strip_prefix("@[") {
            let mut depth = 1usize;
            let mut end = None;
            for (i, ch) in tail.char_indices() {
                match ch {
                    '[' => depth += 1,
                    ']' => {
                        depth -= 1;
                        if depth == 0 {
                            end = Some(i);
                            break;
                        }
                    }
                    _ => {}
                }
            }
            let Some(end) = end else {
                return false;
            };
            rest = tail[end + 1..].trim_start();
            continue;
        }
        let word_end = rest.find(char::is_whitespace).unwrap_or(rest.len());
        let (word, tail) = rest.split_at(word_end);
        if !DECL_MODIFIER_WORDS.contains(&word) {
            return false;
        }
        rest = tail.trim_start();
    }
    true
}

/// Walks the top-level declaration blocks of a source whose comment-stripped and
/// string-stripped views are given, calling `hit` with each block's two views prefixed
/// by the file's top-level `open` / `namespace` lines (so a bare `getEnv` under
/// `open IO` still counts inside its block). Blocks are split at Lean's column-0
/// declaration starts; continuation lines of a declaration are indented in valid Lean,
/// and a column-0 line holding only attribute groups and declaration modifiers
/// (`@[tactic foo]`, `private`, ...) continues into the next line's block, because Lean
/// and Mathlib write such attributes on their own line above the definition they apply
/// to, and splitting there separated the trigger from the body it governs.
/// Returns `None` when the two views disagree on line structure (callers fail closed).
fn scan_top_level_blocks(
    comment_free: &str,
    unquoted: &str,
    hit: impl Fn(&str, &str) -> bool,
) -> Option<bool> {
    let cf_lines: Vec<&str> = comment_free.lines().collect();
    let uq_lines: Vec<&str> = unquoted.lines().collect();
    if cf_lines.len() != uq_lines.len() {
        return None;
    }
    let mut open_prefix = String::new();
    for line in &uq_lines {
        let t = line.trim_start();
        if t.starts_with("open ") || t.starts_with("namespace ") {
            open_prefix.push_str(line);
            open_prefix.push('\n');
        }
    }
    let block_hit = |cf_block: &str, uq_block: &str| -> bool {
        hit(
            &format!("{open_prefix}{cf_block}"),
            &format!("{open_prefix}{uq_block}"),
        )
    };
    let mut cf_block = String::new();
    let mut uq_block = String::new();
    let mut block_attr_only = true;
    for (cf, uq) in cf_lines.iter().zip(uq_lines.iter()) {
        if uq.chars().next().is_some_and(|c| !c.is_whitespace())
            && !uq_block.is_empty()
            && !block_attr_only
        {
            if block_hit(&cf_block, &uq_block) {
                return Some(true);
            }
            cf_block.clear();
            uq_block.clear();
            block_attr_only = true;
        }
        cf_block.push_str(cf);
        cf_block.push('\n');
        uq_block.push_str(uq);
        uq_block.push('\n');
        if !uq.trim().is_empty() && !line_is_attr_or_modifier_only(uq) {
            block_attr_only = false;
        }
    }
    Some(block_hit(&cf_block, &uq_block))
}

/// True when an initializer trigger (an `initialize` / `builtin_initialize`
/// declaration, or the attribute spellings `@[init f]` / `@[builtin_init f]`) pairs
/// with a host-read token, i.e. the host read executes at *import time* in every
/// importer. The pairing is per top-level block, except that an initializer body may
/// reach host state through a same-file helper definition: when the trigger block
/// itself carries no read token, every same-file defining block whose name the trigger
/// block references *in run position* is checked for read tokens. A reference that is
/// only an argument to a registration call (`initialize addLinter fooLinter`,
/// `register*`) stores the definition for later invocations instead of running it, so
/// it does not count: that is #433's definition-only IO. The reference check is one
/// level deep: a helper that reaches host state only through a second helper is not
/// followed. A structural disagreement between the stripped views fails closed.
fn initialize_block_reads_host(comment_free: &str, unquoted: &str) -> bool {
    const INIT_WORDS: [&str; 2] = ["initialize", "builtin_initialize"];
    const INIT_ATTRS: [&str; 2] = ["init", "builtin_init"];
    let has_init_trigger = |uq: &str| {
        INIT_WORDS
            .iter()
            .any(|w| crate::splitter::contains_lean_word(uq, w))
            || crate::splitter::contains_lean_attribute_word(uq, &INIT_ATTRS)
    };
    if !has_init_trigger(unquoted) {
        return false;
    }
    let blocks: std::cell::RefCell<Vec<(String, String)>> = std::cell::RefCell::new(Vec::new());
    let walked = scan_top_level_blocks(comment_free, unquoted, |cf_block, uq_block| {
        blocks
            .borrow_mut()
            .push((cf_block.to_string(), uq_block.to_string()));
        false
    });
    if walked.is_none() {
        // The stripped views disagree on line structure: fail closed.
        return true;
    }
    let blocks = blocks.into_inner();
    let block_reads_host = |(cf, uq): &(String, String)| {
        crate::splitter::unquoted_has_host_read_tokens(cf, uq)
    };
    blocks.iter().enumerate().any(|(i, block)| {
        if !has_init_trigger(&block.1) {
            return false;
        }
        if block_reads_host(block) {
            return true;
        }
        // One level of same-file indirection: a helper definition the trigger block
        // runs, whose own block carries the read token.
        blocks.iter().enumerate().any(|(j, other)| {
            j != i
                && defined_def_names(&other.1)
                    .iter()
                    .any(|name| name_run_referenced(&block.1, name))
                && block_reads_host(other)
        })
    })
}

/// Strips leading attribute groups and declaration modifiers from a line, returning
/// the declaration head (`@[inline] private partial def foo ...` becomes `def foo ...`).
fn strip_attrs_and_modifiers(line: &str) -> &str {
    let mut rest = line.trim_start();
    loop {
        if let Some(tail) = rest.strip_prefix("@[") {
            let mut depth = 1usize;
            let mut end = None;
            for (i, ch) in tail.char_indices() {
                match ch {
                    '[' => depth += 1,
                    ']' => {
                        depth -= 1;
                        if depth == 0 {
                            end = Some(i);
                            break;
                        }
                    }
                    _ => {}
                }
            }
            let Some(end) = end else {
                return rest;
            };
            rest = tail[end + 1..].trim_start();
            continue;
        }
        let word_end = rest.find(char::is_whitespace).unwrap_or(rest.len());
        let (word, tail) = rest.split_at(word_end);
        if DECL_MODIFIER_WORDS.contains(&word) {
            rest = tail.trim_start();
            continue;
        }
        return rest;
    }
}

/// Calls that only STORE their argument for later invocation: a host read inside the
/// stored definition stays definition-only IO. Everything else counts as a run —
/// `registerEnvExtension` (Lean runs the initial-value thunk whenever an importer
/// creates its environment), `registerBuiltinAttribute` (the handler runs in every
/// importer that applies the attribute), and any user helper named `addX` or
/// `registerX` that executes its argument.
const STORE_ONLY_REGISTRATION_HEADS: &[&str] = &["addLinter"];

/// True when `uq_block` references `name` in a position its body would *run*, rather
/// than only passing it to a store-only registration call. `initialize addLinter
/// fooLinter` stores the definition for later invocations instead of executing it at
/// import time; `initialize cfg ← loadCfg` runs `loadCfg`. The discriminator is the
/// word right before the reference, and only the explicit allowlist
/// [`STORE_ONLY_REGISTRATION_HEADS`] makes that occurrence a registration argument: a
/// name-shape rule (`register...`, `add` + capital) also swallowed
/// `registerEnvExtension` and `registerBuiltinAttribute`, whose arguments do run
/// inside importers.
fn name_run_referenced(uq_block: &str, name: &str) -> bool {
    let is_ident = |c: char| crate::splitter::is_lean_id_rest(c) || c == '.';
    let mut from = 0usize;
    while let Some(rel) = uq_block[from..].find(name) {
        let idx = from + rel;
        let end = idx + name.len();
        from = end;
        let prev_ok = idx == 0 || !uq_block[..idx].chars().next_back().is_some_and(is_ident);
        let next_ok = !uq_block[end..].chars().next().is_some_and(is_ident);
        if !prev_ok || !next_ok {
            continue;
        }
        let before = uq_block[..idx].trim_end();
        let head = before
            .char_indices()
            .rev()
            .take_while(|&(_, c)| is_ident(c))
            .last()
            .map(|(p, _)| &before[p..])
            .unwrap_or("");
        let head_seg = head.rsplit('.').next().unwrap_or(head);
        if !STORE_ONLY_REGISTRATION_HEADS.contains(&head_seg) {
            return true;
        }
    }
    false
}

/// The identifiers a block's column-0 head lines define through `def` / `abbrev` /
/// `opaque`, with leading attribute groups and declaration modifiers stripped
/// (`private partial def readCfg`, `@[inline] def f`). A dotted name also yields its
/// last segment, since a reference inside `namespace Foo` writes `helper` for
/// `Foo.helper`. These are the defining-block spellings the one-level same-file
/// reference checks follow.
fn defined_def_names(uq_block: &str) -> Vec<String> {
    let mut names = Vec::new();
    for l in uq_block.lines() {
        if !l.chars().next().is_some_and(|c| !c.is_whitespace()) {
            continue;
        }
        let head = strip_attrs_and_modifiers(l);
        let Some(rest) = ["def ", "abbrev ", "opaque "]
            .iter()
            .find_map(|kw| head.strip_prefix(kw))
        else {
            continue;
        };
        let rest = rest.trim_start();
        let end = rest
            .char_indices()
            .find(|&(_, c)| !(crate::splitter::is_lean_id_rest(c) || c == '.'))
            .map_or(rest.len(), |(idx, _)| idx);
        if end == 0 {
            continue;
        }
        // `def helper.{u}`: the ident scan accepts `.`, so a universe-binder suffix
        // leaves a trailing dot that no reference would ever match. A Lean name never
        // ends in a dot; strip it.
        let name = rest[..end].trim_end_matches('.');
        if name.is_empty() {
            continue;
        }
        if let Some(seg) = name.rsplit('.').next() {
            if seg != name && !seg.is_empty() {
                names.push(seg.to_string());
            }
        }
        names.push(name.to_string());
    }
    names
}

/// Collects the top-level blocks (both stripped views, `open`-prefixed) for the
/// block-pairing checks below. `None` when the views disagree (callers fail closed).
fn collect_top_level_blocks(comment_free: &str, unquoted: &str) -> Option<Vec<(String, String)>> {
    let blocks: std::cell::RefCell<Vec<(String, String)>> = std::cell::RefCell::new(Vec::new());
    scan_top_level_blocks(comment_free, unquoted, |cf_block, uq_block| {
        blocks
            .borrow_mut()
            .push((cf_block.to_string(), uq_block.to_string()));
        false
    })?;
    Some(blocks.into_inner())
}

/// True when block `i` reads host state itself, or *runs* (one level of same-file
/// indirection, exactly as in [`initialize_block_reads_host`], registration references
/// excluded) a defining block that does.
fn block_reads_host_directly_or_via_helper(blocks: &[(String, String)], i: usize) -> bool {
    let reads =
        |(cf, uq): &(String, String)| crate::splitter::unquoted_has_host_read_tokens(cf, uq);
    if reads(&blocks[i]) {
        return true;
    }
    blocks.iter().enumerate().any(|(j, other)| {
        j != i
            && defined_def_names(&other.1)
                .iter()
                .any(|name| name_run_referenced(&blocks[i].1, name))
            && reads(other)
    })
}

/// True when a top-level block *defines* invocable host-reading code (an
/// `elab` / `elab_rules`, a simproc, a `@[tactic]` / `@[command_elab]` / linter
/// handler, an attribute or environment-extension registration) whose host reads are
/// direct or one same-file helper away. Importers execute those bodies when they
/// elaborate the invoking syntax, and the defining module's `.olean` can come out
/// byte-identical, so its artifact digest does not protect them: this taint spreads.
fn any_block_defines_invocable_host_reads(comment_free: &str, unquoted: &str) -> bool {
    let Some(blocks) = collect_top_level_blocks(comment_free, unquoted) else {
        return true;
    };
    (0..blocks.len()).any(|i| {
        crate::splitter::unquoted_has_invocable_definer_trigger(&blocks[i].1)
            && block_reads_host_directly_or_via_helper(&blocks, i)
    })
}

/// True when a top-level block executes host reads during *this* module's own build
/// only: a self-run command (`run_cmd`, `run_elab`, ...) whose reads are direct or one
/// same-file helper away, or a bare `#eval` (arbitrary code at build time). Definition-
/// only IO in plain `def` blocks does not count.
fn any_block_executes_self_run_host_reads(comment_free: &str, unquoted: &str) -> bool {
    let Some(blocks) = collect_top_level_blocks(comment_free, unquoted) else {
        return true;
    };
    (0..blocks.len()).any(|i| {
        (crate::splitter::unquoted_has_self_run_only_trigger(&blocks[i].1)
            && block_reads_host_directly_or_via_helper(&blocks, i))
            || ["#eval", "#eval!"]
                .iter()
                .any(|w| crate::splitter::contains_lean_word(&blocks[i].1, w))
    })
}

/// A module of a *clean, git-pinned* dependency package is host-effect tainted only by
/// code that executes when the module itself elaborates or is imported (#433, #438):
///
/// * import-time and invocable-definer host reads are classified by the caller (they
///   spread before this function is reached);
/// * a host read behind a self-run-only command (`run_cmd`, a `#eval`) taints the
///   module itself, exactly like an editable module;
/// * definition-only IO (a linter's `def` bodies) and literal in-tree `include_str`
///   content that git *tracks at the pinned rev* are covered by the pin: stock Lake's
///   traces already treat the pinned sources plus the toolchain as the module's whole
///   input set, and the kernel replay and soundness-hygiene gates are unaffected.
///   Out-of-tree, non-literal, or untracked (gitignored / generated) `include_str`
///   targets still taint the module itself, because the pinned rev does not fix their
///   content.
fn classify_clean_pinned_dep_source(
    pkg_root: &Path,
    src_path: &Path,
    src_raw: &str,
    exec_taint: HostEffectTaint,
) -> HostEffectTaint {
    let Ok(canon_pkg_root) = fs::canonicalize(pkg_root) else {
        return HostEffectTaint::SpreadsToImporters;
    };
    if source_uses_include_str(src_raw) {
        let Some(rel_paths) = crate::splitter::extract_include_relative_paths(src_raw) else {
            return HostEffectTaint::SelfOnly;
        };
        if rel_paths.is_empty() {
            return HostEffectTaint::SelfOnly;
        }
        let Some(src_dir) = src_path.parent() else {
            return HostEffectTaint::SelfOnly;
        };
        let mut rels_in_root: Vec<PathBuf> = Vec::new();
        for rel in &rel_paths {
            let Ok(canon_target) = fs::canonicalize(src_dir.join(rel)) else {
                return HostEffectTaint::SelfOnly;
            };
            let Ok(rel_in_root) = canon_target.strip_prefix(&canon_pkg_root) else {
                return HostEffectTaint::SelfOnly;
            };
            rels_in_root.push(rel_in_root.to_path_buf());
        }
        if !include_targets_tracked_at_pin(&canon_pkg_root, &rels_in_root) {
            return HostEffectTaint::SelfOnly;
        }
    }
    exec_taint
}

/// Memoized `git ls-files --error-unmatch` answers for `include_str` targets, per
/// (package root, relative path). The checkout is pinned only between requests: a
/// daemon outlives `lake update`, after which the same `.lake/packages/<pkg>` path can
/// hold a new rev where a target's tracked-ness changed, so
/// [`reset_lake_inputs_tag_memo`] clears this memo at every memo-window boundary (once
/// per CLI command and per serve / MCP request).
/// Entries are `(window, tracked)` and a read accepts only the current window, so a
/// git read that started before a reset cannot serve the new window a stale answer by
/// inserting after it — the same shape as `CLEAN_GIT_PIN_MEMO` and
/// `publish_lake_inputs_tag` (DA 71add786 finding 2). The reset also clears the map,
/// bounding growth.
pub(super) static TRACKED_INCLUDE_MEMO: std::sync::OnceLock<
    std::sync::Mutex<HashMap<(PathBuf, PathBuf), (u64, bool)>>,
> = std::sync::OnceLock::new();

/// Inside-the-root is not pinned-by-the-rev. The checkout is clean, so a *tracked*
/// path's content equals the pinned rev's; a gitignored or generated file changes
/// without moving the pin. Pathspec magic is disabled, so a literal `gen*.txt` target
/// is never read as a glob that an unrelated tracked file satisfies. An unanswerable
/// git (missing, refusing) fails closed. Answers are memoized per (package root,
/// path) in [`TRACKED_INCLUDE_MEMO`]: classification runs many times per module per
/// check, and the checkout is pinned for the memo window's lifetime.
fn include_targets_tracked_at_pin(canon_pkg_root: &Path, rels: &[PathBuf]) -> bool {
    // Captured before any git runs: an insert stamped with this window is ignored by
    // every reader whose window is newer (DA 71add786 finding 2).
    let window = current_memo_window();
    let memo = TRACKED_INCLUDE_MEMO.get_or_init(|| std::sync::Mutex::new(HashMap::new()));
    let mut pending: Vec<&PathBuf> = Vec::new();
    {
        let memo = memo.lock().unwrap_or_else(|e| e.into_inner());
        for rel in rels {
            match memo.get(&(canon_pkg_root.to_path_buf(), rel.clone())) {
                Some(&(w, tracked)) if w == window => {
                    if !tracked {
                        return false;
                    }
                }
                _ => pending.push(rel),
            }
        }
    }
    let mut all_tracked = true;
    for rel in pending {
        let tracked = crate::trusted_tools::git(canon_pkg_root).is_ok_and(|mut cmd| {
            cmd.arg("--literal-pathspecs")
                .arg("-C")
                .arg(canon_pkg_root)
                .args(["ls-files", "--error-unmatch", "--"])
                .arg(rel);
            cmd.output().is_ok_and(|o| o.status.success())
        });
        memo.lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert((canon_pkg_root.to_path_buf(), rel.clone()), (window, tracked));
        all_tracked &= tracked;
    }
    all_tracked
}

/// #433 / #438: classify how `src_raw` can taint `module_name`'s compiled artifacts.
///
/// The predicate this replaces was a whole-file co-occurrence test (any elaboration
/// trigger word plus any host-read token anywhere in the file) whose verdict both
/// disabled every kind of reuse for the module *and* spread to every importer. On real
/// dependency trees that tainted most of Mathlib through a handful of linter modules
/// (#433) and made every `check` delete and rebuild whole import closures (#438, #407).
/// The split:
///
/// * import-time execution spreads: `initialize` / `builtin_initialize` / `@[init]`
///   declarations whose host reads are direct or in same-file definitions their bodies
///   run, plus every fail-closed shape, because importers re-run those bodies;
/// * a block *defining* invocable host-reading code (an `elab`, a simproc, a
///   `@[tactic]` / `@[command_elab]` handler, a linter) spreads too:
///   importers run that body when they elaborate the invoking syntax, and the defining
///   module's `.olean` can come out byte-identical, so the artifact digest does not
///   protect them;
/// * host reads behind commands that run only during this module's own build (`#eval`,
///   `run_cmd` / `run_elab` / `run_meta`, an uncovered `include_str`) taint the module
///   alone (`SelfOnly`); importers are protected by the recorded `.olean` digests,
///   which go stale the moment the tainted module's artifact changes;
/// * a module of a clean git-pinned dependency package follows
///   [`classify_clean_pinned_dep_source`].
pub(crate) fn classify_source_host_effect_taint(
    cfg: &ProjectConfig,
    pkg_root: &Path,
    is_root_pkg: bool,
    is_git_pinned: bool,
    module_name: &str,
    src_path: &Path,
    src_raw: &str,
) -> HostEffectTaint {
    let comment_free = crate::splitter::strip_lean_comments(src_raw);
    let clean = crate::splitter::strip_string_literals(&comment_free);
    let unquoted = clean.replace(['«', '»'], "");
    if initialize_block_reads_host(&comment_free, &unquoted) {
        return HostEffectTaint::SpreadsToImporters;
    }
    // A block that *defines* invocable host-reading code spreads too: importers run it.
    if any_block_defines_invocable_host_reads(&comment_free, &unquoted) {
        return HostEffectTaint::SpreadsToImporters;
    }
    if is_git_pinned && !is_root_pkg {
        let exec_taint = if any_block_executes_self_run_host_reads(&comment_free, &unquoted) {
            HostEffectTaint::SelfOnly
        } else {
            HostEffectTaint::None
        };
        return classify_clean_pinned_dep_source(pkg_root, src_path, src_raw, exec_taint);
    }
    // Editable sources (the root package and path dependencies) keep the conservative
    // whole-file co-occurrence test; what changed is only that the verdict no longer
    // spreads to importers by itself.
    let Ok(canon_pkg_root) = fs::canonicalize(pkg_root) else {
        return HostEffectTaint::SpreadsToImporters;
    };
    let Some(pkg) = std::iter::once(&cfg.root_pkg)
        .chain(cfg.dep_pkgs.iter())
        .find(|pkg| fs::canonicalize(&pkg.pkg_root).is_ok_and(|root| root == canon_pkg_root))
    else {
        return HostEffectTaint::SpreadsToImporters;
    };
    if crate::splitter::source_may_read_host_state(src_raw)
        || !module_includes_all_covered_by_lake_inputs(pkg, module_name, src_path, src_raw)
    {
        return HostEffectTaint::SelfOnly;
    }
    if is_root_pkg {
        if crate::splitter::source_has_disallowed_root_runtime_replacement_attribute(src_raw) {
            HostEffectTaint::SelfOnly
        } else {
            HostEffectTaint::None
        }
    } else if crate::splitter::source_may_execute_elab_host_effects(src_raw, false) {
        HostEffectTaint::SelfOnly
    } else {
        HostEffectTaint::None
    }
}

/// [`classify_source_host_effect_taint`] with the package identity (root / clean
/// git-pinned) derived from `pkg_root`; an unresolvable package fails closed.
pub(crate) fn source_host_effect_taint(
    cfg: &ProjectConfig,
    pkg_root: &Path,
    module_name: &str,
    src_path: &Path,
    src_raw: &str,
) -> HostEffectTaint {
    let identity = fs::canonicalize(pkg_root).ok().and_then(|canon| {
        let pkg = std::iter::once(&cfg.root_pkg)
            .chain(cfg.dep_pkgs.iter())
            .find(|pkg| fs::canonicalize(&pkg.pkg_root).is_ok_and(|root| root == canon))?;
        let is_root = fs::canonicalize(&cfg.root_pkg.pkg_root).is_ok_and(|root| root == canon);
        let is_pinned = !is_root
            && is_clean_git_pinned_pkg(
                cfg,
                false,
                &pkg.name,
                pkg_target_base_name(pkg),
                &pkg.pkg_root,
            );
        Some((is_root, is_pinned))
    });
    let Some((is_root_pkg, is_git_pinned)) = identity else {
        return HostEffectTaint::SpreadsToImporters;
    };
    classify_source_host_effect_taint(
        cfg,
        pkg_root,
        is_root_pkg,
        is_git_pinned,
        module_name,
        src_path,
        src_raw,
    )
}

/// Stamp eligibility keeps its pre-narrowing (pre-#433) meaning: the module's own `.olean`
/// may depend on host state (a host read reachable from an elaboration-exec trigger, or
/// an include not covered by the package's Lake inputs). For a clean git-pinned
/// dependency the pin already fixes in-tree includes and definition-only IO, so the
/// narrower #433 taint classification decides instead. Pure `elab` / `simproc` /
/// `macro` / `@[extern]` shapes without host reads stay stamp-eligible; the callers'
/// separate gated `is_tainted` clause polices those.
pub(crate) fn source_ineligible_for_stamp_reuse(
    cfg: &ProjectConfig,
    pkg_root: &Path,
    module_name: &str,
    src_path: &Path,
    src_raw: &str,
) -> bool {
    let taint = source_host_effect_taint(cfg, pkg_root, module_name, src_path, src_raw);
    source_stamp_ineligible_given_taint(cfg, pkg_root, module_name, src_path, src_raw, taint)
}

/// [`source_ineligible_for_stamp_reuse`] with the taint already computed, so a caller
/// that needs both answers classifies the module once.
pub(crate) fn source_stamp_ineligible_given_taint(
    cfg: &ProjectConfig,
    pkg_root: &Path,
    module_name: &str,
    src_path: &Path,
    src_raw: &str,
    taint: HostEffectTaint,
) -> bool {
    if taint.spreads_to_importers() {
        // Import-time host reads and every fail-closed shape.
        return true;
    }
    let Ok(canon_pkg_root) = fs::canonicalize(pkg_root) else {
        return true;
    };
    let Some(pkg) = std::iter::once(&cfg.root_pkg)
        .chain(cfg.dep_pkgs.iter())
        .find(|pkg| fs::canonicalize(&pkg.pkg_root).is_ok_and(|root| root == canon_pkg_root))
    else {
        return true;
    };
    let is_root = fs::canonicalize(&cfg.root_pkg.pkg_root).is_ok_and(|root| root == canon_pkg_root);
    if !is_root
        && is_clean_git_pinned_pkg(cfg, false, &pkg.name, pkg_target_base_name(pkg), &pkg.pkg_root)
    {
        return taint.is_tainted();
    }
    crate::splitter::source_may_read_host_state(src_raw)
        || !module_includes_all_covered_by_lake_inputs(pkg, module_name, src_path, src_raw)
}

pub(crate) fn spec_source_stamp_ineligible_given_taint(
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
    src_raw: &str,
    taint: HostEffectTaint,
) -> bool {
    source_stamp_ineligible_given_taint(
        cfg,
        &spec.pkg_root,
        &spec.module_name,
        &spec.src_path,
        src_raw,
        taint,
    )
}

pub(crate) fn spec_source_host_effect_taint(
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
    src_raw: &str,
) -> HostEffectTaint {
    classify_source_host_effect_taint(
        cfg,
        &spec.pkg_root,
        spec.is_root_pkg,
        !spec.is_root_pkg && is_git_pinned_manifest_package(cfg, spec),
        &spec.module_name,
        &spec.src_path,
        src_raw,
    )
}

pub(crate) fn spec_source_has_disallowed_elab_host_effects(
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
    src_raw: &str,
) -> bool {
    spec_source_host_effect_taint(cfg, spec, src_raw).is_tainted()
}

/// #434: the Lake-inputs fallback sweep may delete build artifacts only for modules
/// the project owns (see [`pkg_root_owned_by_project`]); deleting a dependency
/// checkout's artifacts from here damaged shared Mathlib checkouts.
pub(crate) fn spec_artifacts_purgeable_from_project_root(
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
) -> bool {
    if spec.is_root_pkg {
        return true;
    }
    pkg_root_owned_by_project(cfg, &spec.pkg_name, &spec.pkg_base_name, &spec.pkg_root)
}

/// #434: dependency-package `lake build` targets are driven from the dependency's own
/// workspace unless the project owns the package (see [`pkg_root_owned_by_project`]);
/// the fallback after a successful check used to run uncapped `lake build` on every
/// input-bearing dependency target, Mathlib included.
pub(crate) fn dep_pkg_lake_targets_owned_by_project(
    cfg: &ProjectConfig,
    dp: &PackageConfig,
) -> bool {
    pkg_root_owned_by_project(cfg, &dp.name, pkg_target_base_name(dp), &dp.pkg_root)
}

/// Project ownership of a dependency package root:
///
/// * a clean git-pinned package (a manifest `git` entry, clean at its rev) is never
///   project-owned: its own workspace refreshes it from the pin (#434);
/// * a root inside another package's `.lake/packages` is a nested checkout, never ours;
/// * a `path` manifest entry is editable project state when it resolves inside the
///   project root, or when its directory is not itself a git checkout (an editable
///   scratch sibling, review finding 6: un-owning one turns its edited `include_str`
///   targets into silent skips that nothing refreshes); an out-of-tree GIT clone
///   behind a `path` entry (`require mathlib from "/abs/mathlib4"`, one clone shared
///   across projects) is refreshed by its own workspace, exactly the #434 class
///   (DA 71add786 finding 4);
/// * everything else (no matching manifest entry — a hand-built or synthesized
///   package — or a git entry whose checkout is not clean at its pin) falls back to
///   location: a canonical root inside the project root is ours, and a symlinked
///   `.lake/packages` directory that points at a checkout elsewhere (#434's damaged
///   shared Mathlib) resolves outside the root and stays refused.
fn pkg_root_owned_by_project(
    cfg: &ProjectConfig,
    pkg_name: &str,
    pkg_base_name: &str,
    pkg_root: &Path,
) -> bool {
    if is_clean_git_pinned_pkg(cfg, false, pkg_name, pkg_base_name, pkg_root) {
        return false;
    }
    if pkg_root_inside_foreign_lake_packages(cfg, pkg_root) {
        return false;
    }
    let inside_root = match (
        fs::canonicalize(pkg_root),
        fs::canonicalize(&cfg.root_pkg.pkg_root),
    ) {
        (Ok(pkg), Ok(root)) => pkg.starts_with(&root),
        _ => false,
    };
    if manifest_entry_is_path_dep(cfg, pkg_name, pkg_base_name, pkg_root) {
        // Inside the root it is project state; outside, only a directory that is not
        // itself a git checkout counts as editable scratch (finding 6). An
        // out-of-tree git clone shared across projects is #434's shape whatever the
        // manifest entry type says (DA 71add786 finding 4).
        return inside_root || !pkg_root.join(".git").exists();
    }
    inside_root
}

fn manifest_entry_is_path_dep(
    cfg: &ProjectConfig,
    pkg_name: &str,
    pkg_base_name: &str,
    pkg_root: &Path,
) -> bool {
    let pkg_canon = pkg_root.canonicalize().ok();
    cfg.manifest_packages.iter().any(|mp| {
        mp.pkg_type == "path"
            && (mp.name == pkg_name
                || (!pkg_base_name.is_empty() && mp.name == pkg_base_name)
                || mp.dir == pkg_root
                || mp
                    .dir
                    .canonicalize()
                    .ok()
                    .zip(pkg_canon.as_ref())
                    .is_some_and(|(a, b)| a == *b))
    })
}

/// A package root inside a *different* package's `.lake/packages` is a nested checkout
/// (a dependency's own dependency), never project state; the project's own
/// `packagesDir` is where its dependencies normally live and does not count.
fn pkg_root_inside_foreign_lake_packages(cfg: &ProjectConfig, pkg_root: &Path) -> bool {
    let Ok(canon) = fs::canonicalize(pkg_root) else {
        return true;
    };
    let own_packages_dir =
        fs::canonicalize(cfg.root_pkg.pkg_root.join(&cfg.root_pkg.packages_dir)).ok();
    std::iter::once(&cfg.root_pkg)
        .chain(cfg.dep_pkgs.iter())
        .any(|p| {
            let Ok(proot) = fs::canonicalize(&p.pkg_root) else {
                return false;
            };
            if proot == canon {
                return false;
            }
            let Ok(pdir) = fs::canonicalize(proot.join(&p.packages_dir)) else {
                return false;
            };
            own_packages_dir.as_ref() != Some(&pdir) && canon.starts_with(&pdir)
        })
}

#[cfg(test)]
thread_local! {
    /// Tests route the Lake-invocation log here instead of the process-wide
    /// environment variable, so a concurrently running test cannot write into another
    /// test's log.
    pub(crate) static TEST_LAKE_CMD_LOG: std::cell::RefCell<Option<PathBuf>> =
        const { std::cell::RefCell::new(None) };
}

/// #407: every Lake invocation the tool runs that can rebuild artifacts (the module
/// build in `lake_build_modules_opts`, and the `lake query` materialization in the
/// recipe path) is appended, with its real subcommand, to the file
/// `TURBO_LEAN_LAKE_CMD_LOG` names, so benchmarks can assert that a warm hit runs zero
/// Lake invocations and zero `lake --no-cache` rebuilds. This sink is the
/// machine-readable record; it prints nothing itself.
pub(crate) fn log_lake_build_invocation(
    canon_dir: &Path,
    verb: &str,
    modules: &[String],
    bypass_artifact_cache: bool,
) {
    let flag = if bypass_artifact_cache {
        " --no-cache"
    } else {
        ""
    };
    let line = format!(
        "[turbo-lean] running `lake{flag} {verb} {}` in {}",
        modules.join(" "),
        canon_dir.display()
    );
    let append = |log_path: &std::ffi::OsStr| {
        if let Ok(mut f) = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(log_path)
        {
            use std::io::Write as _;
            let _ = writeln!(f, "{line}");
        }
    };
    #[cfg(test)]
    if let Some(path) = TEST_LAKE_CMD_LOG.with(|p| p.borrow().clone()) {
        append(path.as_os_str());
        return;
    }
    if let Some(log_path) = std::env::var_os("TURBO_LEAN_LAKE_CMD_LOG") {
        append(&log_path);
    }
}

pub(crate) fn build_lean_search_path(cfg: &ProjectConfig, is_untrusted: bool) -> (String, String) {
    let mut lp_parts = Vec::new();
    let mut ld_parts = Vec::new();
    let push_unique = |vec: &mut Vec<String>, s: String| {
        if !s.is_empty() && !vec.contains(&s) {
            vec.push(s);
        }
    };
    let root_build = cfg.root_pkg.pkg_root.join(&cfg.root_pkg.build_dir);
    let root_lib_lean = root_build.join(&cfg.root_pkg.lean_lib_dir);
    let root_native_lib = root_build.join(&cfg.root_pkg.native_lib_dir);
    let root_lib = root_build.join("lib");
    push_unique(&mut lp_parts, root_lib_lean.to_string_lossy().to_string());
    push_unique(&mut ld_parts, root_native_lib.to_string_lossy().to_string());
    push_unique(&mut ld_parts, root_lib.to_string_lossy().to_string());
    push_unique(&mut ld_parts, root_lib_lean.to_string_lossy().to_string());
    for dp in &cfg.dep_pkgs {
        let dep_build = dp.pkg_root.join(&dp.build_dir);
        let dep_lib_lean = dep_build.join(&dp.lean_lib_dir);
        let dep_native_lib = dep_build.join(&dp.native_lib_dir);
        let dep_lib = dep_build.join("lib");
        push_unique(&mut lp_parts, dep_lib_lean.to_string_lossy().to_string());
        push_unique(&mut ld_parts, dep_native_lib.to_string_lossy().to_string());
        push_unique(&mut ld_parts, dep_lib.to_string_lossy().to_string());
        push_unique(&mut ld_parts, dep_lib_lean.to_string_lossy().to_string());
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
            || ku.starts_with("GIT_")
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
pub(super) struct TempDirGuard(pub(super) PathBuf);
impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Typed timeout marker for `run_command_with_timeout*` so call sites can attribute a
/// timeout to the right knob by downcast instead of string matching (#437).
#[derive(Debug, Clone, Copy)]
pub(crate) struct CommandTimedOut {
    pub(crate) timeout: std::time::Duration,
}

impl std::fmt::Display for CommandTimedOut {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "`lean` command timed out after {}ms",
            self.timeout.as_millis()
        )
    }
}

impl std::error::Error for CommandTimedOut {}

pub(crate) fn run_command_with_timeout(
    cmd: &mut Command,
    timeout: std::time::Duration,
    is_untrusted: bool,
) -> Result<std::process::Output> {
    run_command_with_timeout_pinned_fd(cmd, timeout, is_untrusted, None)
}

pub(crate) fn run_command_with_timeout_pinned_fd(
    cmd: &mut Command,
    timeout: std::time::Duration,
    is_untrusted: bool,
    pinned_dir_raw_fd: Option<i32>,
) -> Result<std::process::Output> {
    #[cfg(target_os = "linux")]
    let _inherited_dir_fd: Option<std::os::unix::io::OwnedFd> = if !is_untrusted {
        if let Some(src_fd) = pinned_dir_raw_fd {
            use std::os::unix::io::FromRawFd;
            let dup_fd = unsafe { libc::fcntl(src_fd, libc::F_DUPFD_CLOEXEC, 32) };
            anyhow::ensure!(
                dup_fd >= 0,
                "Failed to duplicate pinned closure snapshot dir_fd {}: {}",
                src_fd,
                std::io::Error::last_os_error()
            );
            let owned = unsafe { std::os::unix::io::OwnedFd::from_raw_fd(dup_fd) };
            let cur_lp = cmd
                .get_envs()
                .find(|(k, _)| *k == std::ffi::OsStr::new("LEAN_PATH"))
                .and_then(|(_, v)| v.map(|s| s.to_string_lossy().to_string()))
                .unwrap_or_default();
            let new_lp = match cur_lp.split_once(':') {
                Some((_, rest)) if !rest.is_empty() => format!("/proc/self/fd/{dup_fd}:{rest}"),
                _ => format!("/proc/self/fd/{dup_fd}"),
            };
            cmd.env("LEAN_PATH", new_lp);
            Some(owned)
        } else {
            None
        }
    } else {
        None
    };
    #[cfg(not(target_os = "linux"))]
    let _ = pinned_dir_raw_fd;
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.process_group(0);
        #[cfg(target_os = "linux")]
        let child_keep_fd: Option<i32> = {
            use std::os::unix::io::AsRawFd;
            _inherited_dir_fd.as_ref().map(|f| f.as_raw_fd())
        };
        #[cfg(not(target_os = "linux"))]
        let child_keep_fd: Option<i32> = None;
        if is_untrusted || child_keep_fd.is_some() {
            unsafe {
                cmd.pre_exec(move || {
                    if let Some(fd) = child_keep_fd {
                        let flags = libc::fcntl(fd, libc::F_GETFD);
                        if flags < 0
                            || libc::fcntl(fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0
                        {
                            return Err(std::io::Error::last_os_error());
                        }
                    }
                    if is_untrusted {
                        for (res, lim) in [
                            (libc::RLIMIT_CORE, 0),
                            (libc::RLIMIT_DATA, 12 * 1024 * 1024 * 1024),
                            (libc::RLIMIT_FSIZE, 512 * 1024 * 1024),
                        ] {
                            let mut cur = std::mem::zeroed::<libc::rlimit>();
                            let capped = if libc::getrlimit(res, &mut cur) == 0
                                && cur.rlim_max != libc::RLIM_INFINITY
                                && cur.rlim_max < lim
                            {
                                cur.rlim_max
                            } else {
                                lim
                            };
                            let r = libc::rlimit {
                                rlim_cur: capped,
                                rlim_max: capped,
                            };
                            if libc::setrlimit(res, &r) != 0 {
                                return Err(std::io::Error::last_os_error());
                            }
                        }
                    }
                    Ok(())
                });
            }
        }
    }
    cmd.stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    let mut child = cmd.spawn()?;
    #[cfg(target_os = "linux")]
    drop(_inherited_dir_fd);
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
            #[cfg(unix)]
            {
                let pgid = child.id() as i32;
                if pgid > 0 {
                    unsafe {
                        let _ = libc::kill(-pgid, libc::SIGKILL);
                    }
                }
            }
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
            return Err(anyhow::Error::new(CommandTimedOut { timeout }));
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
pub(super) static TEST_BWRAP_BIN_OVERRIDE: std::sync::Mutex<Option<String>> = std::sync::Mutex::new(None);

#[cfg(test)]
pub(crate) struct ScopedTestBwrapOverride {
    pub(super) prev: Option<String>,
}

#[cfg(test)]
impl ScopedTestBwrapOverride {
    pub(crate) fn set(val: impl Into<String>) -> Self {
        let mut guard = TEST_BWRAP_BIN_OVERRIDE
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let prev = guard.replace(val.into());
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
        let mut guard = TEST_BWRAP_BIN_OVERRIDE
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        *guard = prev;
    }
}

pub(crate) fn probe_bwrap_sandbox(project: &Path) -> Option<PathBuf> {
    #[cfg(test)]
    if let Some(test_bwrap) = TEST_BWRAP_BIN_OVERRIDE
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .clone()
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
    let mut cands = Vec::new();
    if let Some(nix_bw) = option_env!("TURBO_LEAN_NIX_BWRAP").filter(|s| !s.is_empty()) {
        cands.push(nix_bw);
    }
    cands.extend([
        "/usr/bin/bwrap",
        "/bin/bwrap",
        "/run/current-system/sw/bin/bwrap",
    ]);
    probe_bwrap_candidates(project, &cands)
}

pub(super) fn probe_bwrap_candidates(project: &Path, candidates: &[&str]) -> Option<PathBuf> {
    let sys_path = crate::trusted_tools::trusted_sys_path();
    for candidate in candidates {
        let Ok(cand) = crate::trusted_tools::system_executable(Path::new(candidate), project)
        else {
            continue;
        };
        let mut probe = Command::new(&cand);
        probe.env_clear().env("PATH", &sys_path);
        probe.args([
            "--unshare-all",
            "--new-session",
            "--die-with-parent",
            "--clearenv",
            "--setenv",
            "PATH",
            &sys_path,
            "--dev",
            "/dev",
            "--proc",
            "/proc",
            "--tmpfs",
            "/tmp",
        ]);
        for sys_dir in [
            "/usr",
            "/bin",
            "/lib",
            "/lib64",
            "/etc",
            "/nix",
            "/run/current-system/sw",
        ] {
            let p = Path::new(sys_dir);
            if p.exists() {
                probe.arg("--ro-bind").arg(p).arg(p);
            }
        }
        let probe_bin = [
            "/usr/bin/true",
            "/bin/true",
            "/run/current-system/sw/bin/true",
        ]
        .into_iter()
        .find(|p| Path::new(p).exists())
        .unwrap_or("/bin/sh");
        if probe_bin == "/bin/sh" {
            probe.args(["/bin/sh", "-c", "true"]);
        } else {
            probe.arg(probe_bin);
        }
        if probe.output().map(|o| o.status.success()).unwrap_or(false) {
            return Some(cand);
        }
    }
    None
}

#[cfg(test)]
#[test]
pub(super) fn unusable_system_sandbox_never_falls_back_to_project_bwrap() -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let root = std::env::temp_dir().join(format!(
        "turbo-bwrap-shim-{}-{}",
        std::process::id(),
        crate::pack::next_tmp_id()
    ));
    fs::create_dir_all(&root)?;
    let shim = root.join("bwrap");
    let marker = root.join("executed");
    fs::write(
        &shim,
        format!("#!/bin/sh\ntouch '{}'\nexit 0\n", marker.display()),
    )?;
    fs::set_permissions(&shim, fs::Permissions::from_mode(0o755))?;
    assert!(Command::new(&shim).status()?.success());
    fs::remove_file(&marker)?;
    // An absolute, executable system candidate fails its probe; neither a bare
    // PATH fallback nor an absolute checkout shim may replace it.
    assert!(
        probe_bwrap_candidates(&root, &["/usr/bin/false", "bwrap", shim.to_str().unwrap()])
            .is_none()
    );
    assert!(!marker.exists());
    fs::remove_dir_all(root)?;
    Ok(())
}

pub(super) fn canonicalize_path_with_missing_tail(p: &Path) -> Result<PathBuf> {
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
    // A dangling symlink is not a missing tail: canonicalizing it below fails closed.
    while fs::symlink_metadata(cur).is_err() {
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

/// Roots an untrusted build may use as package roots: the checkout, plus directories the
/// operator lists in `TURBO_LEAN_TRUSTED_PACKAGES_DIR` (e.g. a shared `.lake/packages` cache).
pub(super) fn untrusted_package_roots(canon_dir: &Path) -> Vec<PathBuf> {
    let mut roots = vec![canon_dir.to_path_buf()];
    if let Some(v) = std::env::var_os("TURBO_LEAN_TRUSTED_PACKAGES_DIR") {
        roots.extend(
            std::env::split_paths(&v)
                .filter(|p| p.is_absolute())
                .filter_map(|p| p.canonicalize().ok()),
        );
    }
    roots
}

/// Fail closed unless every directory a native build writes to (package build directories and
/// each module's artifact directories) lies inside its package root. Untrusted builds also
/// resolve symlinks and require each package root inside the checkout or a trusted packages dir.
pub(super) fn validate_build_write_dirs(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    canon_dir: &Path,
    is_untrusted: bool,
) -> Result<()> {
    let roots = untrusted_package_roots(canon_dir);
    let check = |pkg_root: &Path, dir: &Path| -> Result<()> {
        let lexical_ok = dir.starts_with(pkg_root)
            && !dir
                .components()
                .any(|c| matches!(c, std::path::Component::ParentDir));
        let canonical_ok = !is_untrusted
            || (|| -> Result<bool> {
                let canon_root = pkg_root.canonicalize()?;
                Ok(roots.iter().any(|r| canon_root.starts_with(r))
                    && canonicalize_path_with_missing_tail(dir)?.starts_with(&canon_root))
            })()
            .unwrap_or(false);
        if !(lexical_ok && canonical_ok) {
            anyhow::bail!(
                "Refusing to write build outputs to `{}`: outside package `{}`: fail-closed build path gate",
                dir.display(),
                pkg_root.display()
            );
        }
        Ok(())
    };
    for pkg in std::iter::once(&cfg.root_pkg).chain(&cfg.dep_pkgs) {
        let build = pkg.pkg_root.join(&pkg.build_dir);
        for dir in [
            build.join(&pkg.bin_dir),
            build.join(&pkg.lean_lib_dir),
            build.join(&pkg.native_lib_dir),
            build.join(&pkg.ir_dir),
            pkg.pkg_root.join(".lake/build"),
        ] {
            check(&pkg.pkg_root, &dir)?;
        }
    }
    for sl in &dag.shared_libs {
        if let Some(pkg) = std::iter::once(&cfg.root_pkg)
            .chain(&cfg.dep_pkgs)
            .find(|p| p.pkg_root == sl.pkg_root)
        {
            check(&pkg.pkg_root, sl.path.parent().unwrap_or(&sl.path))?;
        }
    }
    for node in dag.nodes.values() {
        check(&node.pkg_root, &node.pkg_root.join(".lake/build"))?;
        for p in [&node.olean_path, &node.ilean_path, &node.c_path] {
            check(&node.pkg_root, p.parent().unwrap_or(p))?;
        }
        if let Some(so_p) = module_dynlib_so_path(node) {
            check(&node.pkg_root, so_p.parent().unwrap_or(&so_p))?;
        }
    }
    Ok(())
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

pub(crate) fn per_worker_lean_num_threads(
    raw_env: Option<&str>,
    host_cores: usize,
    compile_pool_size: usize,
) -> usize {
    let pool = compile_pool_size.max(1);
    let cores = host_cores.max(1);
    let configured = raw_env
        .and_then(|s| s.trim().parse::<usize>().ok())
        .filter(|&n| n > 0);
    if pool <= 1 {
        configured.unwrap_or(cores)
    } else {
        let fair_share = (cores / pool).max(1);
        configured.map_or(fair_share, |c| c.min(fair_share))
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn build_module_compile_command(
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
    compile_pool_size: usize,
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
            "LEAN_NUM_THREADS",
            "4",
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
            "/nix",
            "/run/current-system/sw",
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
        let host_cores = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4);
        let lean_threads = per_worker_lean_num_threads(
            std::env::var("LEAN_NUM_THREADS").ok().as_deref(),
            host_cores,
            compile_pool_size,
        );
        let mut c = Command::new(&cfg.lean_bin);
        c.current_dir(&node.pkg_root)
            .env("PATH", verifier_path(&cfg.lean_bin))
            .env("LEAN_PATH", lean_path_env)
            .env("LD_LIBRARY_PATH", ld_library_path_env)
            .env("LEAN_STACK_SIZE_KB", &stack_kb)
            .env("LEAN_NUM_THREADS", lean_threads.to_string());
        c
    };
    // When `is_untrusted`, pass Lean's `-M 4096 -j 4` (4096 MB internal allocator limit and 4
    // task threads so 256 MB per-thread stacks + imported `.olean` mappings fit inside the 12 GiB
    // `RLIMIT_DATA` cap on ≥8-core hosts)
    // after `cfg.lean_bin` in addition to the OS-level `RLIMIT_DATA` enforced in `run_command_with_timeout`.
    if is_untrusted {
        cmd.args(["-M", "4096", "-j", "4"]);
    }
    // Lake passes `weakLeanArgs` before `moreLeanArgs`.
    for arg in &node.weak_args {
        cmd.arg(verification_lake_arg(arg));
    }
    for arg in &node.strong_args {
        cmd.arg(verification_lake_arg(arg));
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

pub(super) type ModuleCompileOutput = (i64, String, String);
pub(super) type StagedModuleCompileOutput = (i64, String, TempDirGuard);

/// Per-module / per-shard compile timeout in seconds (`TURBO_LEAN_MODULE_TIMEOUT_SECS` or
/// `[build] module_timeout_secs` in turbo-lean.toml, which main.rs maps onto the same
/// environment key), clamped in untrusted mode to `[15, 600]` so heavy proof modules do not
/// spuriously fail on shared 4-vCPU CI runners while untrusted builds remain bounded.
///
/// With no explicit setting the trusted default is 1800 s — a flat 300 s killed legitimate
/// proof-heavy modules that take over 400 s. The `last_duration_ms` parameter implements
/// the adaptive `max(300 s, 3 × the last recorded compile duration)` policy (#437) for a
/// caller that knows one; no production call site passes a duration yet (they all route
/// through `module_compile_timeout_secs_from` with `None`) — the scheduler's cached action
/// durations (`get_cached_action_duration_ms`) are the intended source.
pub(crate) fn module_compile_timeout_secs_with_history(
    raw_env: Option<&str>,
    is_untrusted: bool,
    last_duration_ms: Option<u64>,
) -> u64 {
    let configured = raw_env
        .and_then(|s| s.trim().parse::<u64>().ok())
        .filter(|&n| n > 0);
    if is_untrusted {
        return configured.unwrap_or(300).clamp(15, 600);
    }
    configured.unwrap_or_else(|| match last_duration_ms {
        Some(ms) => ms.div_ceil(1000).saturating_mul(3).max(300),
        None => 1800,
    })
}

pub(crate) fn module_compile_timeout_secs_from(raw_env: Option<&str>, is_untrusted: bool) -> u64 {
    module_compile_timeout_secs_with_history(raw_env, is_untrusted, None)
}

pub(crate) fn module_compile_timeout_secs(is_untrusted: bool) -> u64 {
    module_compile_timeout_secs_from(
        std::env::var("TURBO_LEAN_MODULE_TIMEOUT_SECS")
            .ok()
            .as_deref(),
        is_untrusted,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn compile_single_module_staged(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    node: &ModuleNode,
    lean_path_env: &str,
    ld_library_path_env: &str,
    is_untrusted: bool,
    bwrap_bin: Option<&Path>,
    preserve_lake: bool,
    compile_pool_size: usize,
) -> Result<StagedModuleCompileOutput> {
    let t0 = Instant::now();
    record_scheduler_test_event(
        "compile_subprocess_start",
        std::slice::from_ref(&node.module_name),
    );
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
    let tmp_guard = TempDirGuard(tmp_dir.clone());
    let tmp_olean = tmp_dir.join(format!("{}.olean", rel_slash));
    let tmp_ilean = tmp_dir.join(format!("{}.ilean", rel_slash));
    let tmp_c = tmp_dir.join(format!("{}.c", rel_slash));
    let tmp_setup = tmp_dir.join(format!("{}.setup.json", rel_slash));
    if let Some(parent) = tmp_olean.parent() {
        fs::create_dir_all(parent)?;
    }
    let setup_json = build_setup_json(cfg, dag, node, None, None)?;
    let setup_bytes = serde_json::to_vec(&setup_json)?;
    fs::write(&tmp_setup, &setup_bytes)?;
    if !preserve_lake {
        write_file_atomic(&module_setup_json_path(node), &setup_bytes)?;
    }
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
        compile_pool_size,
    )?;
    let timeout_secs = module_compile_timeout_secs(is_untrusted);
    let output = run_command_with_timeout(
        &mut cmd,
        std::time::Duration::from_secs(timeout_secs),
        is_untrusted,
    )
    .map_err(|e| {
        // #437: a timeout names the knob instead of a bare "timed out after Nms".
        if e.downcast_ref::<CommandTimedOut>().is_some() {
            e.context(format!(
                "module `{}` exceeded its {}s compile timeout (raise `[build] module_timeout_secs` in turbo-lean.toml or `TURBO_LEAN_MODULE_TIMEOUT_SECS`)",
                node.module_name, timeout_secs
            ))
        } else {
            e.context(format!(
                "Failed to invoke `lean` compiler ({}) for module `{}`",
                cfg.lean_bin.display(),
                node.module_name
            ))
        }
    })?;
    record_scheduler_test_event(
        "compile_subprocess_end",
        std::slice::from_ref(&node.module_name),
    );
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
    if stdout_str.contains("declaration uses ") || stderr_str.contains("declaration uses ") {
        anyhow::bail!(
            "Native Lean compilation rejected module `{}` ({}) due to `sorry` axiom usage",
            node.module_name,
            node.src_path.display()
        );
    }
    let tmp_srv = PathBuf::from(format!("{}.server", tmp_olean.display()));
    let tmp_priv = PathBuf::from(format!("{}.private", tmp_olean.display()));
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
    let dur_ms = t0.elapsed().as_millis() as i64;
    Ok((dur_ms, stdout_str, tmp_guard))
}

/// `check` / trusted `pr-verify` gate: every non-toolchain `.olean` that `target_files`
/// transitively import (project-local or dependency, however it was built) must carry current
/// kernel-replay authority in `TurboStore` (`kernel_replayed_oleans` keyed by freshly hashed
/// on-disk `.olean`+`.ilean` bytes, `ZYGOTE_REPLAY_VERSION`, and `lean_githash`) or be
/// independently replayed now. Checkout manifests (`.turbo_verified_sources.json`) are freshness
/// metadata only and never grant replay authority. Fails closed.
/// Verify that an imported non-toolchain module belonging to the workspace root package or one
/// of its dependency packages resolves unambiguously to a `.lean` source file whose directives
/// satisfy checking-weakening and native-decide hygiene gates. Fails closed if a workspace or
/// dependency package `.olean` artifact lacks a resolvable `.lean` source or fails source hygiene.
pub(crate) fn verify_imported_package_module_source_hygiene(
    cfg: &ProjectConfig,
    mod_name: &str,
    olean_path: &Path,
    allowed_axioms: &[String],
) -> Result<bool> {
    let mut specs = Vec::new();
    if let Some(root_spec) = resolve_module_in_package(&cfg.root_pkg, true, mod_name) {
        specs.push(root_spec);
    }
    for dp in &cfg.dep_pkgs {
        if let Some(dep_spec) = resolve_module_in_package(dp, false, mod_name) {
            specs.push(dep_spec);
        }
    }
    if specs.len() > 1 {
        let pkg_names: Vec<&str> = specs.iter().map(|s| s.pkg_name.as_str()).collect();
        anyhow::bail!(
            "Ambiguous imported module `{mod_name}` resolved in multiple packages ({pkg_names:?}): fail-closed"
        );
    }
    let Some(spec) = specs.into_iter().next() else {
        let canon_olean = olean_path
            .canonicalize()
            .unwrap_or_else(|_| olean_path.to_path_buf());
        let belongs_to_pkg = std::iter::once(&cfg.root_pkg)
            .chain(cfg.dep_pkgs.iter())
            .any(|pkg| {
                let pkg_root_canon = pkg
                    .pkg_root
                    .canonicalize()
                    .unwrap_or_else(|_| pkg.pkg_root.clone());
                let pkg_lib_canon = pkg
                    .pkg_root
                    .join(&pkg.build_dir)
                    .join(&pkg.lean_lib_dir)
                    .canonicalize()
                    .unwrap_or_else(|_| pkg.pkg_root.join(&pkg.build_dir).join(&pkg.lean_lib_dir));
                canon_olean.starts_with(&pkg_lib_canon) || canon_olean.starts_with(&pkg_root_canon)
            });
        if belongs_to_pkg {
            // Standalone root-package `.lean` files outside Lake library/exe globs (e.g.
            // `TurboLean.lean` alongside `TurboLean.+`, or auxiliary scripts compiled by
            // `stock_statement_build`) still resolve unambiguously under a root-package source dir.
            let canon_root_lib = cfg
                .root_pkg
                .pkg_root
                .join(&cfg.root_pkg.build_dir)
                .join(&cfg.root_pkg.lean_lib_dir)
                .canonicalize()
                .unwrap_or_else(|_| {
                    cfg.root_pkg
                        .pkg_root
                        .join(&cfg.root_pkg.build_dir)
                        .join(&cfg.root_pkg.lean_lib_dir)
                });
            let canon_root_pkg = cfg
                .root_pkg
                .pkg_root
                .canonicalize()
                .unwrap_or_else(|_| cfg.root_pkg.pkg_root.clone());
            let canon_packages = cfg
                .root_pkg
                .pkg_root
                .join(&cfg.root_pkg.packages_dir)
                .canonicalize()
                .unwrap_or_else(|_| cfg.root_pkg.pkg_root.join(&cfg.root_pkg.packages_dir));
            if canon_olean.starts_with(&canon_root_lib)
                || (canon_olean.starts_with(&canon_root_pkg)
                    && !canon_olean.starts_with(&canon_packages))
            {
                let rel_slash = module_name_to_rel_slash(mod_name);
                let base = cfg.root_pkg.pkg_root.join(&cfg.root_pkg.src_dir);
                let mut roots = vec![base.clone()];
                roots.extend(
                    cfg.root_pkg
                        .libs
                        .iter()
                        .filter_map(|l| l.src_dir.as_ref())
                        .map(|d| base.join(d)),
                );
                roots.extend(
                    cfg.root_pkg
                        .exes
                        .iter()
                        .filter_map(|e| e.src_dir.as_ref())
                        .map(|d| base.join(d)),
                );
                roots.sort();
                roots.dedup();
                let cands: Vec<PathBuf> = roots
                    .into_iter()
                    .map(|r| r.join(format!("{rel_slash}.lean")))
                    .filter(|p| p.is_file())
                    .collect();
                if cands.len() == 1 {
                    let standalone_src = &cands[0];
                    let hygiene = load_source_hygiene_cached(standalone_src).with_context(|| {
                        format!(
                            "Failed to read `.lean` source `{}` for imported module `{mod_name}`: fail-closed",
                            standalone_src.display()
                        )
                    })?;
                    anyhow::ensure!(
                        !hygiene.has_checking_weakening,
                        "Soundness hygiene violation in imported module `{mod_name}` ({}): {:?}",
                        standalone_src.display(),
                        hygiene.disallowed_items_under(allowed_axioms)
                    );
                    anyhow::ensure!(
                        !hygiene.native_violation_under(allowed_axioms),
                        "[TurboLean.KernelGate] native_decide/bv_decide in imported module `{mod_name}` ({}) is not admitted by the project's axiom allowlist",
                        standalone_src.display()
                    );
                    anyhow::ensure!(
                        !hygiene.has_trust_compiler,
                        "Soundness hygiene violation (trustCompiler) in imported module `{mod_name}` ({})",
                        standalone_src.display()
                    );
                    return Ok(true);
                }
            }
            anyhow::bail!(
                "Workspace/dependency `.olean` `{}` for imported module `{mod_name}` has no resolvable `.lean` source in project or dependency packages: fail-closed",
                olean_path.display()
            );
        }
        return Ok(false);
    };
    let hygiene = load_source_hygiene_cached(&spec.src_path).with_context(|| {
        format!(
            "Failed to read `.lean` source `{}` for imported module `{mod_name}`: fail-closed",
            spec.src_path.display()
        )
    })?;
    let is_git_pinned_dep = !spec.is_root_pkg && is_git_pinned_manifest_package(cfg, &spec);
    anyhow::ensure!(
        if is_git_pinned_dep {
            !hygiene.has_checking_weakening_option
        } else {
            !hygiene.has_checking_weakening
        },
        "Soundness hygiene violation in imported module `{mod_name}` ({}): {:?}",
        spec.src_path.display(),
        hygiene.disallowed_items_under(allowed_axioms)
    );
    anyhow::ensure!(
        is_git_pinned_dep || !hygiene.native_violation_under(allowed_axioms),
        "[TurboLean.KernelGate] native_decide/bv_decide in imported module `{mod_name}` ({}) is not admitted by the project's axiom allowlist",
        spec.src_path.display()
    );
    anyhow::ensure!(
        !hygiene.has_trust_compiler,
        "Soundness hygiene violation (trustCompiler) in imported module `{mod_name}` ({})",
        spec.src_path.display()
    );
    Ok(spec.is_root_pkg)
}

pub(crate) fn ensure_imported_oleans_replayed(
    store: &TurboStore,
    canon_dir: &Path,
    target_files: &[PathBuf],
) -> Result<usize> {
    ensure_imported_oleans_replayed_with_options(store, canon_dir, target_files, false)
}

pub(crate) fn ensure_imported_oleans_replayed_with_options(
    store: &TurboStore,
    canon_dir: &Path,
    target_files: &[PathBuf],
    allow_sorry: bool,
) -> Result<usize> {
    let mut allowed = splitter::allowed_axioms();
    if allow_sorry && !allowed.iter().any(|a| a == "sorryAx") {
        allowed.push("sorryAx".to_string());
    }
    ensure_imported_oleans_replayed_with_roots_and_axioms(
        store,
        canon_dir,
        target_files,
        &[],
        &allowed,
    )
}

pub(crate) fn ensure_imported_oleans_replayed_with_roots(
    store: &TurboStore,
    canon_dir: &Path,
    target_files: &[PathBuf],
    root_modules: &[String],
) -> Result<usize> {
    ensure_imported_oleans_replayed_with_roots_and_axioms(
        store,
        canon_dir,
        target_files,
        root_modules,
        &splitter::allowed_axioms(),
    )
}

pub(crate) fn ensure_imported_oleans_replayed_with_roots_and_axioms(
    store: &TurboStore,
    canon_dir: &Path,
    target_files: &[PathBuf],
    root_modules: &[String],
    allowed_axioms: &[String],
) -> Result<usize> {
    let mut worklist: Vec<String> = target_files
        .iter()
        .filter_map(|f| fs::read_to_string(f).ok())
        .flat_map(|s| parse_header_info(&s).imports)
        .chain(root_modules.iter().cloned())
        .collect();
    if worklist.is_empty() {
        return Ok(0);
    }
    let cfg = resolve_project_config(canon_dir);
    let tc_lib = cfg.as_ref().map(|c| c.toolchain_lib_lean.clone()).ok();
    let tc_gh = cfg.as_ref().map(|c| c.lean_githash.clone()).ok();
    let lean_path = match &cfg {
        Ok(c) => build_lean_search_path(c, false).0,
        Err(_) => lake_build::resolve_remote_lean_path(canon_dir, None),
    };
    let mut dirs: Vec<PathBuf> = std::env::split_paths(&lean_path).collect();
    if let Some(ref t) = tc_lib {
        if !t.as_os_str().is_empty() && !dirs.contains(t) {
            dirs.push(t.clone());
        }
    }
    let mut seen = HashSet::new();
    let mut imported: Vec<(String, PathBuf)> = Vec::new();
    while let Some(m) = worklist.pop() {
        if !seen.insert(m.clone()) {
            continue;
        }
        let Some(path) = resolve_olean_along_search_dirs(&dirs, &m) else {
            continue;
        };
        if let Some(ref t) = tc_lib {
            if is_verified_toolchain_olean_file(t, tc_gh.as_deref(), &path) {
                continue;
            }
        }
        let (imps, _) = read_olean_binary_imports_cached(&path).with_context(|| {
            format!(
                "Failed to parse binary `.olean` header of imported `{m}` (`{}`): fail-closed",
                path.display()
            )
        })?;
        worklist.extend(imps.into_iter().map(|i| i.module));
        imported.push((m, path));
    }
    if imported.is_empty() {
        return Ok(0);
    }
    let cfg = cfg.context(
        "Cannot kernel-replay imported `.olean`s without a resolvable project configuration: fail-closed",
    )?;
    let mut pending_audit = Vec::new();
    let mut pending_replay = Vec::new();
    let (replay_lp, _) = build_lean_search_path(&cfg, false);
    let mut replay_batch = ReplayLookupBatchCache::new(store, &cfg, &replay_lp);
    for (m, path) in &imported {
        let needs_audit =
            verify_imported_package_module_source_hygiene(&cfg, m, path, allowed_axioms)?;
        if needs_audit {
            if !replay_batch.is_audited_in_store(store, &cfg, &replay_lp, m, path) {
                pending_audit.push(m.clone());
            }
        } else if !replay_batch.is_replayed_in_store(store, &cfg, &replay_lp, path) {
            pending_replay.push(m.clone());
        }
    }
    if !pending_audit.is_empty() {
        let allow_sorry_axiom = allowed_axioms.iter().any(|a| a == "sorryAx");
        crate::zygote::audit_compiled_modules_with_zygote_options(
            store,
            &cfg,
            &pending_audit,
            &replay_lp,
            &[],
            false,
            allow_sorry_axiom,
        )
        .context("Imported `.olean` failed in-kernel soundness & replay audit")?;
    }
    if !pending_replay.is_empty() {
        crate::zygote::kernel_replay_modules_with_zygote(store, &cfg, &pending_replay, &replay_lp)
            .context("Imported `.olean` failed independent kernel replay")?;
    }
    Ok(pending_audit.len() + pending_replay.len())
}

pub(crate) fn node_is_git_pinned_manifest_package(cfg: &ProjectConfig, node: &ModuleNode) -> bool {
    is_clean_git_pinned_pkg(
        cfg,
        node.is_root_pkg,
        &node.pkg_name,
        &node.pkg_base_name,
        &node.pkg_root,
    )
}

pub(super) fn node_source_host_effect_taint(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    src_raw: &str,
) -> HostEffectTaint {
    classify_source_host_effect_taint(
        cfg,
        &node.pkg_root,
        node.is_root_pkg,
        !node.is_root_pkg && node_is_git_pinned_manifest_package(cfg, node),
        &node.module_name,
        &node.src_path,
        src_raw,
    )
}

pub(super) fn node_source_has_disallowed_elab_host_effects(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    src_raw: &str,
) -> bool {
    node_source_host_effect_taint(cfg, node, src_raw).is_tainted()
}

/// The TRANSITIVE spread verdict per (project config digest, package root, module),
/// stamped with the memo window captured before its computation's reads (DA 71add786
/// finding 5; the stamping is finding 2's `CLEAN_GIT_PIN_MEMO` shape). Within one
/// window the closure is walked once; a new window (one per CLI command and per
/// serve / MCP request) recomputes, which is how an edit below an unchanged importer
/// still flips its verdict in a long-lived daemon. The verdict depends on the whole
/// workspace configuration (root-first import resolution, the package set), so the key
/// carries `ProjectConfig::canonical_config_digest`: two projects sharing one absolute
/// `path` dependency never read each other's verdicts. A verdict whose computation
/// read an in-progress cycle sentinel is never published here (DA 3ff1014b finding 2).
/// One entry per module, overwritten per window; [`reset_lake_inputs_tag_memo`]
/// clears it too.
#[allow(clippy::type_complexity)]
pub(super) static SPREAD_TRANSITIVE_VERDICTS: std::sync::OnceLock<
    std::sync::Mutex<HashMap<(String, PathBuf, String), (u64, bool)>>,
> = std::sync::OnceLock::new();

/// Whether `spec`'s module, or anything below it in its *own* import graph, carries
/// spreading host-effect taint. External `.olean` dependencies are not dag nodes, so
/// spreading has to be chased through their source headers; one hop was not enough
/// (`Dep.B` importing a host-reading `Dep.A` never marked the root). Lean import
/// graphs are acyclic; a resolver cycle is cut by the in-progress memo entry (`None`),
/// and a verdict whose computation read such a sentinel holds only under that call's
/// assumption, so it stays in the per-call memo and is never published to
/// [`SPREAD_TRANSITIVE_VERDICTS`] (DA 3ff1014b finding 2: publishing it served a
/// wrong "does not spread" for the rest of the window). An unreadable source or
/// broken header fails closed, as in the purge walk. Two cache layers: PER-FILE facts
/// (the own-source spread verdict and the parsed header) keyed by source content, and
/// the TRANSITIVE verdict in [`SPREAD_TRANSITIVE_VERDICTS`], keyed by project config
/// and memo window — within one window the closure is walked once, and the next
/// request's fresh window recomputes, so an edit below an unchanged importer still
/// flips the importer's verdict in a long-lived daemon (every request resets the
/// window at entry).
pub(super) fn spec_spreads_host_effects_transitively(
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
    memo: &mut HashMap<(PathBuf, String), Option<bool>>,
) -> bool {
    spec_spreads_host_effects_transitively_inner(cfg, spec, memo).0
}

/// Returns `(verdict, cycle_cut)`: `cycle_cut` is true when this computation, anywhere
/// below it, read an in-progress memo sentinel. Such a verdict is correct for the
/// queried root but conditioned on the cut for the members of the cycle, so no frame
/// on a cut path publishes to the cross-call cache.
fn spec_spreads_host_effects_transitively_inner(
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
    memo: &mut HashMap<(PathBuf, String), Option<bool>>,
) -> (bool, bool) {
    // Per-file facts only: whether the module's OWN source spreads, whether its header
    // failed to parse, and its imports. Never the transitive verdict, which depends on
    // every file below the module while this key covers only the one file.
    #[allow(clippy::type_complexity)]
    static SPREAD_FILE_FACTS: std::sync::OnceLock<
        std::sync::Mutex<HashMap<(PathBuf, String, [u8; 32]), (bool, bool, Vec<String>)>>,
    > = std::sync::OnceLock::new();
    let key = (spec.pkg_root.clone(), spec.module_name.clone());
    match memo.get(&key) {
        // Finalized within this call.
        Some(Some(v)) => return (*v, false),
        // An ancestor's in-progress entry: the resolver cycle is cut here, so the
        // caller's verdict is conditioned on this frame's assumed `false`.
        Some(None) => return (false, true),
        None => {}
    }
    // Captured before any reads: a verdict computed before a reset is stamped with
    // the old window and never served to the new one (the finding 2 shape).
    let window = current_memo_window();
    let cache_key = (
        cfg.canonical_config_digest.clone(),
        spec.pkg_root.clone(),
        spec.module_name.clone(),
    );
    let cached = SPREAD_TRANSITIVE_VERDICTS
        .get_or_init(|| std::sync::Mutex::new(HashMap::new()))
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .get(&cache_key)
        .copied();
    if let Some((w, v)) = cached {
        if w == window {
            memo.insert(key, Some(v));
            return (v, false);
        }
    }
    memo.insert(key.clone(), None);
    let mut cycle_cut = false;
    let v = match fs::read_to_string(&spec.src_path) {
        Err(_) => true,
        Ok(src) => {
            let cache = SPREAD_FILE_FACTS.get_or_init(|| std::sync::Mutex::new(HashMap::new()));
            let content_key = (
                spec.pkg_root.clone(),
                spec.module_name.clone(),
                *blake3::hash(src.as_bytes()).as_bytes(),
            );
            let cached = cache
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .get(&content_key)
                .cloned();
            let (own_spreads, header_broken, imports) = match cached {
                Some(facts) => facts,
                None => {
                    let own =
                        spec_source_host_effect_taint(cfg, spec, &src).spreads_to_importers();
                    let hdr = parse_header_info(&src);
                    let facts = (own, hdr.header_error.is_some(), hdr.imports);
                    cache
                        .lock()
                        .unwrap_or_else(|e| e.into_inner())
                        .insert(content_key, facts.clone());
                    facts
                }
            };
            let mut spreads = own_spreads || header_broken;
            if !spreads {
                for sub in &imports {
                    let site = match resolve_module_in_package(&cfg.root_pkg, true, sub) {
                        Some(rs) => ImportSite::Module(Box::new(rs)),
                        None => resolve_import_site(cfg, sub),
                    };
                    if let ImportSite::Module(sub_spec) = site {
                        let (sub_v, sub_cut) =
                            spec_spreads_host_effects_transitively_inner(cfg, &sub_spec, memo);
                        cycle_cut |= sub_cut;
                        if sub_v {
                            spreads = true;
                            break;
                        }
                    }
                }
            }
            spreads
        }
    };
    memo.insert(key, Some(v));
    if !cycle_cut {
        SPREAD_TRANSITIVE_VERDICTS
            .get_or_init(|| std::sync::Mutex::new(HashMap::new()))
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(cache_key, (window, v));
    }
    (v, cycle_cut)
}

/// #433: a module is tainted when its own source is (`SelfOnly` or worse), or when a
/// spreading module (an import-time initializer, or an invocable host-reading
/// definer) sits anywhere below it in the import graph, its external `.olean`
/// dependencies' own imports included. Taint that is `SelfOnly` no longer spreads:
/// importers are pinned to the tainted module's artifact digest by the verified-source
/// stamps and Lake traces, so a content change still invalidates them without disabling
/// their own reuse up front.
pub(super) fn compute_tainted_elab_host_effect_modules(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
) -> HashSet<String> {
    let mut ext_spread_memo: HashMap<(PathBuf, String), Option<bool>> = HashMap::new();
    let mut ext_olean_memo: HashMap<PathBuf, bool> = HashMap::new();
    let mut tainted: HashSet<String> = HashSet::new();
    let mut spreading: HashSet<String> = HashSet::new();
    for mod_name in &dag.topological_order {
        let Some(node) = dag.nodes.get(mod_name) else {
            continue;
        };
        let self_taint = fs::read_to_string(&node.src_path)
            .map(|s| node_source_host_effect_taint(cfg, node, &s))
            .unwrap_or(HostEffectTaint::SpreadsToImporters);
        let dag_dep_spreads = node.direct_dag_deps.iter().any(|d| spreading.contains(d));
        let ext_dep_spreads = node.external_olean_deps.iter().any(|(_, olean_path)| {
            *ext_olean_memo.entry(olean_path.clone()).or_insert_with(|| {
                resolve_source_spec_for_prebuilt_olean(cfg, olean_path)
                    .map(|spec| {
                        spec_spreads_host_effects_transitively(cfg, &spec, &mut ext_spread_memo)
                    })
                    // An external `.olean` with no resolvable source never counted as
                    // tainting its importer (toolchain and unrelated prebuilts).
                    .unwrap_or(false)
            })
        });
        if self_taint.spreads_to_importers() || dag_dep_spreads || ext_dep_spreads {
            spreading.insert(mod_name.clone());
            tainted.insert(mod_name.clone());
        } else if self_taint.is_tainted() {
            tainted.insert(mod_name.clone());
        }
    }
    tainted
}

#[derive(Deserialize)]
pub(super) struct WorkerZygoteAuditReply {
    pub(super) ok: bool,
    #[serde(default)]
    pub(super) audited: Option<Vec<String>>,
    #[serde(default)]
    pub(super) violations: Vec<String>,
}

pub(super) fn parse_worker_audit_reply(out: &std::process::Output, mod_names: &[String]) -> Result<()> {
    let stdout_str = String::from_utf8_lossy(&out.stdout);
    let stderr_str = String::from_utf8_lossy(&out.stderr);
    let json_line = stdout_str
        .lines()
        .rev()
        .map(str::trim)
        .find(|l| l.starts_with('{') && l.ends_with('}'))
        .unwrap_or("");
    let parsed: Option<WorkerZygoteAuditReply> = serde_json::from_str(json_line).ok();
    match parsed {
        Some(reply)
            if out.status.success()
                && reply.ok
                && reply.violations.is_empty()
                && reply.audited.as_deref() == Some(mod_names) =>
        {
            Ok(())
        }
        Some(reply) => {
            let details = if reply.violations.is_empty() {
                format!(
                    "exit={} stdout={} stderr={}",
                    out.status,
                    stdout_str.trim(),
                    stderr_str.trim()
                )
            } else {
                reply.violations.join("\n")
            };
            anyhow::bail!(
                "In-kernel `.olean` soundness audit rejected compiled artifact(s) ({:?}):\n{}",
                mod_names,
                details
            );
        }
        None => {
            anyhow::bail!(
                "In-kernel `.olean` soundness auditor failed closed (exit={}, modules={:?}):\nstdout: {}\nstderr: {}",
                out.status,
                mod_names,
                stdout_str.trim(),
                stderr_str.trim()
            );
        }
    }
}

pub(super) fn scheduler_audit_batch_size() -> usize {
    std::env::var("TURBO_LEAN_AUDIT_BATCH_SIZE")
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .filter(|&v| v > 0)
        .unwrap_or(8)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn run_audit_chunk_subprocess(
    store_root: &Path,
    cfg: &ProjectConfig,
    mod_names: &[String],
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
    is_untrusted: bool,
    skip_child_replay: bool,
    pinned_dir_raw_fd: Option<i32>,
) -> Result<()> {
    if mod_names.is_empty() || mod_names.iter().any(|m| m.trim().is_empty()) {
        anyhow::bail!("In-kernel `.olean` audit received an empty module name: fail-closed");
    }
    record_scheduler_test_event("audit_subprocess_start", mod_names);
    let (mut cmd, timeout) = crate::zygote::kernel_reader_command(
        store_root,
        cfg,
        lean_path_env,
        extra_ro_binds,
        is_untrusted,
    )?;
    cmd.arg("--audit-modules");
    if skip_child_replay {
        cmd.arg("--skip-child-replay");
    }
    for a in crate::zygote::pinned_ffi_allow_args(cfg, mod_names) {
        cmd.arg(a);
    }
    for m in mod_names {
        cmd.arg(m);
    }
    let out =
        run_command_with_timeout_pinned_fd(&mut cmd, timeout, is_untrusted, pinned_dir_raw_fd);
    record_scheduler_test_event("audit_subprocess_end", mod_names);
    match out.and_then(|o| parse_worker_audit_reply(&o, mod_names)) {
        Ok(()) => Ok(()),
        Err(_) if mod_names.len() > 1 => {
            let mid = mod_names.len() / 2;
            run_audit_chunk_subprocess(
                store_root,
                cfg,
                &mod_names[..mid],
                lean_path_env,
                extra_ro_binds,
                is_untrusted,
                skip_child_replay,
                pinned_dir_raw_fd,
            )?;
            run_audit_chunk_subprocess(
                store_root,
                cfg,
                &mod_names[mid..],
                lean_path_env,
                extra_ro_binds,
                is_untrusted,
                skip_child_replay,
                pinned_dir_raw_fd,
            )
        }
        Err(e) => Err(e),
    }
}

pub(super) type ModuleSnapshotAuthority = (std::sync::Arc<crate::zygote::ClosureSnapshot>, bool, bool);
pub(super) enum ModuleAuditAuthority {
    Snapshot(ModuleSnapshotAuthority),
    FastStore(VerifiedFastStoreAuthority),
}
pub(super) type PerModuleAuditOutcome = (Result<()>, Option<ModuleAuditAuthority>);
pub(super) type AuditBatchWorkerOutcome = HashMap<String, PerModuleAuditOutcome>;

pub(super) fn run_audit_or_replay_batch_worker_bound(
    store_root: &Path,
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    mod_names: &[String],
    snap: &std::sync::Arc<crate::zygote::ClosureSnapshot>,
    live_lean_path_env: &str,
    is_untrusted: bool,
) -> Result<AuditBatchWorkerOutcome> {
    let (snap_lp, snap_dir) =
        crate::zygote::ensure_bound_audit_closure(snap, "sched_audit_before_replay")?;
    let pinned_fd = crate::zygote::snapshot_pinned_dir_raw_fd(snap);
    let parent_snap_lp =
        crate::zygote::snapshot_parent_search_path(snap).unwrap_or_else(|| snap_lp.clone());
    let snap_binds: Vec<PathBuf> = if is_untrusted {
        vec![snap_dir]
    } else {
        Vec::new()
    };

    let (mut audit, replay): (Vec<String>, Vec<String>) = mod_names
        .iter()
        .cloned()
        .partition(|m| is_untrusted || dag.nodes.get(m).is_none_or(|n| n.is_root_pkg));
    audit.sort();
    audit.dedup();
    let mut replay_sorted = replay;
    replay_sorted.sort();
    replay_sorted.dedup();

    let mut per_mod: AuditBatchWorkerOutcome = HashMap::with_capacity(mod_names.len());
    let mut snap_replayed: HashSet<String> = HashSet::new();
    if !is_untrusted {
        if let Ok(worker_store) = TurboStore::open(Some(store_root)) {
            let live_batch = ReplayLookupBatchCache::new(&worker_store, cfg, live_lean_path_env);
            let mut snap_batch = ReplayLookupBatchCache::new(&worker_store, cfg, &parent_snap_lp);
            for m in audit.iter().chain(replay_sorted.iter()) {
                let Some(snap_olean) = snap_batch.resolve_module_olean(m) else {
                    continue;
                };
                let Some((ref orig_olean, _)) = snap.entries.get(m).and_then(|e| e.as_ref()) else {
                    continue;
                };
                let binds_policy = live_batch.is_root_module_olean(orig_olean);
                if snap_batch.is_replayed_in_store_with_binds_policy(
                    &worker_store,
                    cfg,
                    &snap_olean,
                    binds_policy,
                ) {
                    snap_replayed.insert(m.clone());
                }
            }
        }
    }

    let need_replay_audit: Vec<String> = audit
        .iter()
        .filter(|m| is_untrusted || !snap_replayed.contains(*m))
        .cloned()
        .collect();
    let need_replay_dep: Vec<String> = replay_sorted
        .iter()
        .filter(|m| !snap_replayed.contains(*m))
        .cloned()
        .collect();
    let mut pre_replayed = need_replay_audit.is_empty() && !is_untrusted;
    if is_untrusted && audit.len() > 1 {
        crate::zygote::kernel_replay_modules_exec_pinned(
            store_root,
            cfg,
            &audit,
            &snap_lp,
            &snap_binds,
            true,
            None,
        )?;
        let _ = crate::zygote::ensure_bound_audit_closure(snap, "sched_audit_after_replay")?;
        pre_replayed = true;
    } else if !is_untrusted && need_replay_audit.len() + need_replay_dep.len() > 1 {
        let mut union_replay = Vec::with_capacity(need_replay_audit.len() + need_replay_dep.len());
        union_replay.extend(need_replay_audit.iter().cloned());
        union_replay.extend(need_replay_dep.iter().cloned());
        union_replay.sort();
        union_replay.dedup();
        if crate::zygote::kernel_replay_modules_exec_pinned(
            store_root,
            cfg,
            &union_replay,
            &parent_snap_lp,
            &[],
            false,
            pinned_fd,
        )
        .is_ok()
        {
            let _ = crate::zygote::ensure_bound_audit_closure(snap, "sched_audit_after_replay")?;
            pre_replayed = true;
            for m in &replay_sorted {
                let record_rep = !snap_replayed.contains(m);
                per_mod.insert(
                    m.clone(),
                    (
                        Ok(()),
                        Some(ModuleAuditAuthority::Snapshot((
                            std::sync::Arc::clone(snap),
                            record_rep,
                            false,
                        ))),
                    ),
                );
            }
            replay_sorted.clear();
        }
    } else if !is_untrusted && need_replay_dep.is_empty() && !replay_sorted.is_empty() {
        for m in &replay_sorted {
            per_mod.insert(
                m.clone(),
                (
                    Ok(()),
                    Some(ModuleAuditAuthority::Snapshot((
                        std::sync::Arc::clone(snap),
                        false,
                        false,
                    ))),
                ),
            );
        }
        replay_sorted.clear();
    }

    let explicit_audit_batch = std::env::var("TURBO_LEAN_AUDIT_BATCH_SIZE")
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .filter(|&v| v > 0);
    let audit_chunk_sz = match explicit_audit_batch {
        Some(sz) => sz,
        None if !is_untrusted => 128,
        None => scheduler_audit_batch_size(),
    };

    for chunk in audit.chunks(audit_chunk_sz) {
        let _ = crate::zygote::ensure_bound_audit_closure(snap, "sched_audit_before_chunk")?;
        let chunk_skip_replay = (is_untrusted && pre_replayed)
            || (!is_untrusted && (pre_replayed || chunk.iter().all(|m| snap_replayed.contains(m))));
        match run_audit_chunk_subprocess(
            store_root,
            cfg,
            chunk,
            &snap_lp,
            &snap_binds,
            is_untrusted,
            chunk_skip_replay,
            pinned_fd,
        ) {
            Ok(()) => {
                let _ = crate::zygote::ensure_bound_audit_closure(snap, "sched_audit_after_chunk")?;
                for m in chunk {
                    let record_rep = !is_untrusted && !snap_replayed.contains(m);
                    let record_aud = !is_untrusted;
                    per_mod.insert(
                        m.clone(),
                        (
                            Ok(()),
                            Some(ModuleAuditAuthority::Snapshot((
                                std::sync::Arc::clone(snap),
                                record_rep,
                                record_aud,
                            ))),
                        ),
                    );
                }
            }
            Err(chunk_err) => {
                if chunk.len() == 1 {
                    per_mod.insert(chunk[0].clone(), (Err(chunk_err), None));
                } else {
                    for m in chunk {
                        let single_skip_replay = (is_untrusted && pre_replayed)
                            || (!is_untrusted && (pre_replayed || snap_replayed.contains(m)));
                        let single_res = crate::zygote::ensure_bound_audit_closure(
                            snap,
                            "sched_audit_before_chunk",
                        )
                        .and_then(|_| {
                            run_audit_chunk_subprocess(
                                store_root,
                                cfg,
                                std::slice::from_ref(m),
                                &snap_lp,
                                &snap_binds,
                                is_untrusted,
                                single_skip_replay,
                                pinned_fd,
                            )?;
                            let _ = crate::zygote::ensure_bound_audit_closure(
                                snap,
                                "sched_audit_after_chunk",
                            )?;
                            Ok(())
                        });
                        match single_res {
                            Ok(()) => {
                                let record_rep = !is_untrusted && !snap_replayed.contains(m);
                                let record_aud = !is_untrusted;
                                per_mod.insert(
                                    m.clone(),
                                    (
                                        Ok(()),
                                        Some(ModuleAuditAuthority::Snapshot((
                                            std::sync::Arc::clone(snap),
                                            record_rep,
                                            record_aud,
                                        ))),
                                    ),
                                );
                            }
                            Err(e) => {
                                per_mod.insert(m.clone(), (Err(e), None));
                            }
                        }
                    }
                }
            }
        }
    }

    for m in &replay_sorted {
        if m.trim().is_empty() {
            per_mod.insert(
                m.clone(),
                (
                    Err(anyhow::anyhow!(
                        "Kernel replay received an empty module name: fail-closed"
                    )),
                    None,
                ),
            );
            continue;
        }
        if !is_untrusted && snap_replayed.contains(m) {
            per_mod.insert(
                m.clone(),
                (
                    Ok(()),
                    Some(ModuleAuditAuthority::Snapshot((
                        std::sync::Arc::clone(snap),
                        false,
                        false,
                    ))),
                ),
            );
            continue;
        }
        record_scheduler_test_event("replay_subprocess_start", std::slice::from_ref(m));
        let res = (|| -> Result<()> {
            let _ = crate::zygote::ensure_bound_audit_closure(snap, "sched_replay_before_single")?;
            let (mut cmd, timeout) =
                crate::zygote::kernel_reader_command(store_root, cfg, &snap_lp, &[], false)?;
            cmd.args(["--kernel-replay-module", m.as_str()]);
            let out = run_command_with_timeout_pinned_fd(&mut cmd, timeout, false, pinned_fd)
                .context(
                    "Failed to execute independent kernel replay (`--kernel-replay-module`)",
                )?;
            anyhow::ensure!(
                out.status.success(),
                "[TurboLean.KernelReplay] independent kernel re-check of dependency `{}` failed (exit={}):\n{}",
                m,
                out.status,
                String::from_utf8_lossy(&out.stderr).trim()
            );
            let _ = crate::zygote::ensure_bound_audit_closure(snap, "sched_replay_after_single")?;
            Ok(())
        })();
        record_scheduler_test_event("replay_subprocess_end", std::slice::from_ref(m));
        match res {
            Ok(()) => {
                per_mod.insert(
                    m.clone(),
                    (
                        Ok(()),
                        Some(ModuleAuditAuthority::Snapshot((
                            std::sync::Arc::clone(snap),
                            true,
                            false,
                        ))),
                    ),
                );
            }
            Err(e) => {
                per_mod.insert(m.clone(), (Err(e), None));
            }
        }
    }

    Ok(per_mod)
}

pub(super) fn run_audit_or_replay_batch_worker(
    store_root: &Path,
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    mod_names: &[String],
    lean_path_env: &str,
    is_untrusted: bool,
) -> Result<AuditBatchWorkerOutcome> {
    if mod_names.is_empty() {
        return Ok(HashMap::new());
    }
    if is_untrusted {
        crate::zygote::validate_untrusted_audit_caller_paths(cfg, lean_path_env, &[])?;
    }
    match crate::zygote::materialize_bound_audit_closure(cfg, mod_names, lean_path_env) {
        Ok(snap) => {
            let snap = std::sync::Arc::new(snap);
            run_audit_or_replay_batch_worker_bound(
                store_root,
                cfg,
                dag,
                mod_names,
                &snap,
                lean_path_env,
                is_untrusted,
            )
        }
        Err(batch_err) if mod_names.len() == 1 => {
            let mut per_mod = HashMap::with_capacity(1);
            per_mod.insert(mod_names[0].clone(), (Err(batch_err), None));
            Ok(per_mod)
        }
        Err(_) => {
            let mut per_mod = HashMap::with_capacity(mod_names.len());
            for m in mod_names {
                let single_slice = std::slice::from_ref(m);
                match crate::zygote::materialize_bound_audit_closure(
                    cfg,
                    single_slice,
                    lean_path_env,
                ) {
                    Ok(snap) => {
                        let snap = std::sync::Arc::new(snap);
                        match run_audit_or_replay_batch_worker_bound(
                            store_root,
                            cfg,
                            dag,
                            single_slice,
                            &snap,
                            lean_path_env,
                            is_untrusted,
                        ) {
                            Ok(mut sub) => {
                                if let Some(v) = sub.remove(m) {
                                    per_mod.insert(m.clone(), v);
                                }
                            }
                            Err(e) => {
                                per_mod.insert(m.clone(), (Err(e), None));
                            }
                        }
                    }
                    Err(e) => {
                        per_mod.insert(m.clone(), (Err(e), None));
                    }
                }
            }
            Ok(per_mod)
        }
    }
}

#[cfg(test)]
pub(crate) static BWRAP_TEST_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[cfg(test)]
mod host_effect_taint_tests {
    use super::*;

    /// A Mathlib-linter-shaped module: a pure `initialize` body (registration only) plus a
    /// *definition* that reads host state when invoked. Nothing host-reading executes at
    /// elaboration or import time.
    const LINTER_SHAPE: &str =
        "initialize myExt : Nat ← pure 0\n\ndef readProbe : IO (Option String) := IO.getEnv \"TURBO_TAINT_PROBE\"\n";
    /// An import-time host read: `initialize` bodies re-run in every importer.
    const IMPORT_TIME_SHAPE: &str =
        "initialize envFlag : Option String ← IO.getEnv \"TURBO_TAINT_TEST\"\n";
    /// An elaborator whose own body reads host state: that executes when this module
    /// (or anything invoking the syntax) elaborates, so the module itself stays tainted
    /// even inside a clean git-pinned dependency.
    const ELAB_BLOCK_HOST_READ_SHAPE: &str = "import Lean\nelab \"dep_env_ty\" : term => do\n  let _rows ← IO.FS.lines \"flag.txt\"\n  return Lean.mkConst ``Nat\n";
    /// A host read behind a command that runs only in this module's own build.
    const RUN_CMD_HELPER_SHAPE: &str =
        "def loadCfg : IO String := IO.FS.readFile \"cfg\"\nrun_cmd do let _ ← loadCfg\n";
    /// A bare `#eval` runs arbitrary code during this module's own build only, so a
    /// pinned dependency module holding one classifies `SelfOnly`.
    const EVAL_SHAPE: &str = "def forty : Nat := 40\n#eval forty\n";
    /// An environment extension: Lean runs the registered initial-value thunk whenever
    /// an importer creates its environment, so a host read inside it spreads.
    const REG_ENV_EXT_SHAPE: &str = "import Lean\ndef loadInitial : IO (Array String) := do\n  let _ ← IO.getEnv \"TURBO_TAINT_TEST\"\n  pure #[]\ninitialize ext : Lean.EnvExtension (Array String) ← Lean.registerEnvExtension loadInitial\n";
    /// A builtin attribute registration: the handler runs in every importer that
    /// applies the attribute, so a host read inside it spreads.
    const REG_BUILTIN_ATTR_SHAPE: &str = "import Lean\ndef fooAttrImpl : IO Unit := do\n  let _ ← IO.FS.readFile \"style.txt\"\n  pure ()\ninitialize registerBuiltinAttribute fooAttrImpl\n";
    /// Lean and Mathlib write the attribute on its own line above the definition it
    /// applies to; the two lines are one declaration.
    const SPLIT_ATTR_TACTIC_SHAPE: &str = "import Lean\n@[tactic fooTac]\ndef evalFoo : IO Nat := do\n  let _rows ← IO.FS.lines \"x\"\n  return 3\n";
    /// A pure elaborator (no host read) is tainted but stamp-eligible.
    const PURE_ELAB_SHAPE: &str =
        "import Lean\nelab \"pure_ty\" : term => return Lean.mkConst ``Nat\n";
    /// The standard linter registration: `initialize addLinter fooLinter` only stores
    /// the definition for later invocations; nothing host-reading runs at import time,
    /// so this is the definition-only IO #433 keeps untainted.
    const REG_LINTER_SHAPE: &str = "def fooLinter : IO Unit := do\n  let _ ← IO.FS.readFile \"style.txt\"\n  pure ()\ninitialize addLinter fooLinter\n";
    /// A modifier-prefixed helper that the initializer body runs.
    const PRIVATE_DEF_INIT_HELPER_SHAPE: &str =
        "private def readCfg : IO String := IO.FS.readFile \"cfg\"\ninitialize cfg : String ← readCfg\n";
    /// `init` inside an attribute list, which a raw `@[init` substring scan misses.
    const INIT_LIST_ATTR_SHAPE: &str =
        "def loadCfg : IO String := IO.FS.readFile \"cfg\"\n@[export cexp, init loadCfg] opaque cfg : String\n";
    /// An import-time host read reached through a same-file helper: the `initialize`
    /// body's block holds no read token itself, the helper's block holds no trigger.
    const INIT_HELPER_INDIRECTION_SHAPE: &str =
        "def helper : IO (Option String) := IO.getEnv \"TURBO_TAINT_TEST\"\n\ninitialize x : String ← do\n  let v ← helper\n  pure (v.getD \"\")\n";
    /// The attribute spelling of an initializer: `@[init helper]` registers `helper` to
    /// run at import time in every importer, exactly like an `initialize` block.
    const INIT_ATTR_HELPER_SHAPE: &str =
        "def helper : IO String := do\n  let v ← IO.getEnv \"TURBO_TAINT_TEST\"\n  pure (v.getD \"\")\n\n@[init helper] opaque x : String\n";

    fn temp_dir(label: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "turbo_he_taint_{label}_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ))
    }

    fn git_init_commit(repo: &Path) -> Result<String> {
        anyhow::ensure!(crate::trusted_tools::git(repo)?
            .args(["init", "-q"])
            .arg(repo)
            .status()?
            .success());
        anyhow::ensure!(crate::trusted_tools::git(repo)?
            .arg("-C")
            .arg(repo)
            .args(["add", "."])
            .status()?
            .success());
        anyhow::ensure!(crate::trusted_tools::git(repo)?
            .arg("-C")
            .arg(repo)
            .args([
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@e",
                "-c",
                "commit.gpgsign=false",
                "commit",
                "-qm",
                "init",
            ])
            .status()?
            .success());
        Ok(String::from_utf8(
            crate::trusted_tools::git(repo)?
                .arg("-C")
                .arg(repo)
                .args(["rev-parse", "HEAD"])
                .output()?
                .stdout,
        )?
        .trim()
        .to_string())
    }

    /// Root project with one clean git-pinned dependency package `lintlib` whose single
    /// module `LintLib` holds `dep_source`. Returns the project config and the dependency
    /// module's spec.
    fn pinned_dep_fixture(
        label: &str,
        dep_source: &str,
    ) -> Result<(PathBuf, ProjectConfig, DiscoveredModuleSpec)> {
        dep_fixture(label, dep_source, true)
    }

    /// Like [`pinned_dep_fixture`], but `git_pinned: false` records `lintlib` as an
    /// in-project *path* dependency instead.
    fn dep_fixture(
        label: &str,
        dep_source: &str,
        git_pinned: bool,
    ) -> Result<(PathBuf, ProjectConfig, DiscoveredModuleSpec)> {
        dep_fixture_with(label, dep_source, git_pinned, &[])
    }

    /// [`dep_fixture`] with extra committed files inside the dependency package.
    fn dep_fixture_with(
        label: &str,
        dep_source: &str,
        git_pinned: bool,
        dep_extra_files: &[(&str, &str)],
    ) -> Result<(PathBuf, ProjectConfig, DiscoveredModuleSpec)> {
        let dir = temp_dir(label);
        let proj = dir.join("proj");
        let dep_in_pkgs = proj.join(".lake/packages/lintlib");
        fs::create_dir_all(&dep_in_pkgs)?;
        let tc = include_str!("../../../../lean/lean-toolchain");
        fs::write(dep_in_pkgs.join("lean-toolchain"), tc)?;
        fs::write(dep_in_pkgs.join(".gitignore"), "/.lake/\ngen.txt\n")?;
        fs::write(dep_in_pkgs.join("data.txt"), "pinned data\n")?;
        fs::write(
            dep_in_pkgs.join("lakefile.toml"),
            "name = \"lintlib\"\ndefaultTargets = [\"LintLib\"]\n[[lean_lib]]\nname = \"LintLib\"\n",
        )?;
        fs::write(dep_in_pkgs.join("LintLib.lean"), dep_source)?;
        for (rel, content) in dep_extra_files {
            let p = dep_in_pkgs.join(rel);
            if let Some(parent) = p.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::write(p, content)?;
        }
        let rev = git_init_commit(&dep_in_pkgs)?;
        fs::write(proj.join("lean-toolchain"), tc)?;
        fs::write(
            proj.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage proj where\nrequire lintlib from \".lake/packages/lintlib\"\n@[default_target]\nlean_lib Proj where\n",
        )?;
        fs::write(proj.join("Proj.lean"), "import LintLib\ndef p : Nat := 1\n")?;
        let pkg_entry = if git_pinned {
            serde_json::json!({
                "type": "git",
                "name": "lintlib",
                "rev": rev,
                "url": "https://example.invalid/lintlib",
                "inherited": false,
                "configFile": "lakefile.toml"
            })
        } else {
            serde_json::json!({
                "type": "path",
                "name": "lintlib",
                "dir": ".lake/packages/lintlib",
                "manifestFile": "lake-manifest.json",
                "inherited": false,
                "configFile": "lakefile.toml"
            })
        };
        fs::write(
            proj.join("lake-manifest.json"),
            serde_json::to_string_pretty(&serde_json::json!({
                "version": "1.1.0",
                "packagesDir": ".lake/packages",
                "packages": [pkg_entry]
            }))?,
        )?;
        let canon = fs::canonicalize(&proj)?;
        reset_lake_inputs_tag_memo();
        let cfg = resolve_project_config(&canon)?;
        let dep_pkg = cfg
            .dep_pkgs
            .iter()
            .find(|dp| dp.name == "lintlib")
            .expect("lintlib dependency resolves");
        let spec = resolve_module_in_package(dep_pkg, false, "LintLib")
            .expect("LintLib module resolves in lintlib");
        assert_eq!(
            is_git_pinned_manifest_package(&cfg, &spec),
            git_pinned,
            "fixture pin kind must match or the assertions prove nothing"
        );
        Ok((dir, cfg, spec))
    }

    /// #434: the Lake-inputs fallback sweep's deletion policy. Artifacts and lake
    /// targets of a clean git-pinned dependency are never project-driven; root modules
    /// and in-project path dependencies stay project-owned.
    #[test]
    fn host_effects_issue_434_dep_artifacts_not_purgeable_from_project_root() -> Result<()> {
        let (dir, cfg, spec) = pinned_dep_fixture("sweep_pinned", LINTER_SHAPE)?;
        assert!(
            !spec_artifacts_purgeable_from_project_root(&cfg, &spec),
            "a clean git-pinned dependency's artifacts must never be purged from the project (#434)"
        );
        let root_spec =
            resolve_module_in_package(&cfg.root_pkg, true, "Proj").expect("root module resolves");
        assert!(
            spec_artifacts_purgeable_from_project_root(&cfg, &root_spec),
            "root-package artifacts stay purgeable"
        );
        let dep_pkg = cfg
            .dep_pkgs
            .iter()
            .find(|dp| dp.name == "lintlib")
            .expect("dep pkg");
        assert!(
            !dep_pkg_lake_targets_owned_by_project(&cfg, dep_pkg),
            "a git-pinned dependency's lake targets are not driven from the project (#434)"
        );
        let _ = fs::remove_dir_all(&dir);

        let (dir2, cfg2, spec2) = dep_fixture("sweep_path", LINTER_SHAPE, false)?;
        assert!(
            spec_artifacts_purgeable_from_project_root(&cfg2, &spec2),
            "an in-project path dependency stays project-owned"
        );
        let dep_pkg2 = cfg2
            .dep_pkgs
            .iter()
            .find(|dp| dp.name == "lintlib")
            .expect("dep pkg");
        assert!(
            dep_pkg_lake_targets_owned_by_project(&cfg2, dep_pkg2),
            "an in-project path dependency's targets are project-driven"
        );
        let _ = fs::remove_dir_all(&dir2);
        Ok(())
    }

    /// An editable `path` dependency (`require foo from "../foo"`) is project state
    /// wherever its directory resolves: #434's damage came from shared GIT checkouts
    /// (a pinned Mathlib behind a symlinked `.lake/packages` entry), not from path
    /// entries, and un-owning siblings turned every edited `include_str` target there
    /// into a silent skip that nothing refreshes (review finding 6).
    #[test]
    fn host_effects_editable_sibling_path_dep_is_project_owned() -> Result<()> {
        let dir = temp_dir("sibling_path");
        let proj = dir.join("proj");
        let dep = dir.join("lintlib");
        fs::create_dir_all(&proj)?;
        fs::create_dir_all(&dep)?;
        let tc = include_str!("../../../../lean/lean-toolchain");
        fs::write(dep.join("lean-toolchain"), tc)?;
        fs::write(
            dep.join("lakefile.toml"),
            "name = \"lintlib\"\ndefaultTargets = [\"LintLib\"]\n[[lean_lib]]\nname = \"LintLib\"\n",
        )?;
        fs::write(dep.join("LintLib.lean"), LINTER_SHAPE)?;
        fs::write(proj.join("lean-toolchain"), tc)?;
        fs::write(
            proj.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage proj where\nrequire lintlib from \"../lintlib\"\n@[default_target]\nlean_lib Proj where\n",
        )?;
        fs::write(proj.join("Proj.lean"), "import LintLib\ndef p : Nat := 1\n")?;
        fs::write(
            proj.join("lake-manifest.json"),
            serde_json::to_string_pretty(&serde_json::json!({
                "version": "1.1.0",
                "packagesDir": ".lake/packages",
                "packages": [{
                    "type": "path",
                    "name": "lintlib",
                    "dir": "../lintlib",
                    "manifestFile": "lake-manifest.json",
                    "inherited": false,
                    "configFile": "lakefile.toml"
                }]
            }))?,
        )?;
        let canon = fs::canonicalize(&proj)?;
        reset_lake_inputs_tag_memo();
        let cfg = resolve_project_config(&canon)?;
        let dep_pkg = cfg
            .dep_pkgs
            .iter()
            .find(|dp| dp.name == "lintlib")
            .expect("sibling lintlib dependency resolves");
        let spec = resolve_module_in_package(dep_pkg, false, "LintLib")
            .expect("LintLib module resolves in sibling lintlib");
        assert!(
            spec_artifacts_purgeable_from_project_root(&cfg, &spec),
            "an editable sibling path dependency is project state; its edited \
             include_str targets are purged and rebuilt from here (finding 6)"
        );
        assert!(
            dep_pkg_lake_targets_owned_by_project(&cfg, dep_pkg),
            "an editable sibling path dependency's targets are project-driven \
             (finding 6)"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// A `path` entry pointing at an out-of-tree GIT clone is a shared checkout
    /// (`require mathlib from "/abs/mathlib4"` shares one clone across projects):
    /// deleting its artifacts or lake-building its targets from this project is the
    /// #434 class, whatever the manifest entry type says (DA 71add786 finding 4). The
    /// editable-sibling test above stays owned because that fixture is not itself a
    /// git checkout.
    #[test]
    fn host_effects_out_of_tree_path_dep_git_clone_is_not_project_owned() -> Result<()> {
        let dir = temp_dir("shared_clone_path");
        let proj = dir.join("proj");
        let dep = dir.join("lintlib");
        fs::create_dir_all(&proj)?;
        fs::create_dir_all(&dep)?;
        let tc = include_str!("../../../../lean/lean-toolchain");
        fs::write(dep.join("lean-toolchain"), tc)?;
        fs::write(
            dep.join("lakefile.toml"),
            "name = \"lintlib\"\ndefaultTargets = [\"LintLib\"]\n[[lean_lib]]\nname = \"LintLib\"\n",
        )?;
        fs::write(dep.join("LintLib.lean"), LINTER_SHAPE)?;
        git_init_commit(&dep)?;
        fs::write(proj.join("lean-toolchain"), tc)?;
        fs::write(
            proj.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage proj where\nrequire lintlib from \"../lintlib\"\n@[default_target]\nlean_lib Proj where\n",
        )?;
        fs::write(proj.join("Proj.lean"), "import LintLib\ndef p : Nat := 1\n")?;
        fs::write(
            proj.join("lake-manifest.json"),
            serde_json::to_string_pretty(&serde_json::json!({
                "version": "1.1.0",
                "packagesDir": ".lake/packages",
                "packages": [{
                    "type": "path",
                    "name": "lintlib",
                    "dir": "../lintlib",
                    "manifestFile": "lake-manifest.json",
                    "inherited": false,
                    "configFile": "lakefile.toml"
                }]
            }))?,
        )?;
        let canon = fs::canonicalize(&proj)?;
        reset_lake_inputs_tag_memo();
        let cfg = resolve_project_config(&canon)?;
        let dep_pkg = cfg
            .dep_pkgs
            .iter()
            .find(|dp| dp.name == "lintlib")
            .expect("shared-clone lintlib dependency resolves");
        let spec = resolve_module_in_package(dep_pkg, false, "LintLib")
            .expect("LintLib module resolves in the shared clone");
        assert!(
            !spec_artifacts_purgeable_from_project_root(&cfg, &spec),
            "an out-of-tree git clone behind a path entry is a shared checkout; its \
             artifacts are never purged from this project (#434, DA finding 4)"
        );
        assert!(
            !dep_pkg_lake_targets_owned_by_project(&cfg, dep_pkg),
            "an out-of-tree git clone behind a path entry is not lake-built from this \
             project (#434, DA finding 4)"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// A pinned module whose gitignored `include_str` target is regenerated goes
    /// stale with no change to its source or lakefile mtimes: the resolved targets
    /// are part of the artifact's input set, so the staleness gate reads them too
    /// (DA 71add786 finding 1). With the target untouched the walk completes and
    /// leaves everything in place.
    #[test]
    fn host_effects_regenerated_include_str_target_makes_pinned_artifact_stale() -> Result<()> {
        let include_src = "def g := include_str \"gen.txt\"\n";
        let (dir, cfg, spec) = pinned_dep_fixture("regen_include", include_src)?;
        // Present but gitignored: untracked at the pin, so the module is SelfOnly.
        fs::write(spec.pkg_root.join("gen.txt"), "generated v1\n")?;
        assert_eq!(
            spec_source_host_effect_taint(&cfg, &spec, include_src),
            HostEffectTaint::SelfOnly,
            "an untracked include target is not covered by the pin"
        );
        let dep_olean = spec.build_lib_lean_dir.join("LintLib.olean");
        fs::create_dir_all(dep_olean.parent().unwrap())?;
        fs::write(&dep_olean, b"fake dep olean")?;
        let root_spec = resolve_module_in_package(&cfg.root_pkg, true, "Proj")
            .expect("root module resolves");
        let root_olean = root_spec.build_lib_lean_dir.join("Proj.olean");
        fs::create_dir_all(root_olean.parent().unwrap())?;
        fs::write(&root_olean, b"fake root olean")?;
        let fresh = purge_elab_host_effect_artifacts_in_closure(&cfg, &["Proj".to_string()])?;
        assert!(!fresh, "a fresh unowned SelfOnly module purges nothing");
        assert!(
            dep_olean.is_file() && root_olean.is_file(),
            "the fresh leg leaves every artifact in place"
        );
        // Regenerate the target: strictly newer than the artifact, source untouched.
        fs::write(spec.pkg_root.join("gen.txt"), "generated v2\n")?;
        fs::File::options()
            .write(true)
            .open(spec.pkg_root.join("gen.txt"))?
            .set_modified(
                std::time::SystemTime::now() + std::time::Duration::from_secs(3600),
            )?;
        let err = purge_elab_host_effect_artifacts_in_closure(&cfg, &["Proj".to_string()])
            .expect_err("a regenerated include target makes the pinned artifact stale");
        assert!(
            format!("{err:#}").contains("Failed to purge stale build artifact"),
            "the refusal names the purge failure, got: {err:#}"
        );
        assert!(
            dep_olean.is_file() && root_olean.is_file(),
            "a refusal deletes nothing"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// #433: a clean git-pinned dependency module that only *defines* host-reading code
    /// (a linter: pure `initialize`, IO in a `def` body) must not be host-effect tainted;
    /// an import-time host read in the same position must stay tainted.
    #[test]
    fn host_effects_issue_433_linter_only_pinned_dep_module_is_not_tainted() -> Result<()> {
        let (dir, cfg, spec) = pinned_dep_fixture("pinned_linter", LINTER_SHAPE)?;
        assert!(
            !spec_source_has_disallowed_elab_host_effects(&cfg, &spec, LINTER_SHAPE),
            "linter-shaped pinned dependency module (pure initialize + IO only in def bodies) \
             must not be host-effect tainted (#433)"
        );
        assert!(
            spec_source_has_disallowed_elab_host_effects(&cfg, &spec, IMPORT_TIME_SHAPE),
            "an `initialize` body reading host state must stay tainted"
        );
        assert!(
            spec_source_has_disallowed_elab_host_effects(&cfg, &spec, ELAB_BLOCK_HOST_READ_SHAPE),
            "an elaborator body reading host state must stay tainted even in a pinned dependency"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// An invocable definer whose body (or one-helper-away body) reads host state
    /// spreads to importers (they run it when they elaborate its syntax); a column-0
    /// attribute line counts as its definition's trigger; self-run-only commands stay
    /// on the module; and a registration (`initialize addLinter fooLinter`,
    /// `register*`) is not a run, so the standard linter shape stays untainted (#433).
    #[test]
    fn host_effects_invocable_definer_host_reads_spread_to_importers() -> Result<()> {
        let (dir, cfg, spec) = pinned_dep_fixture("definer_classify", LINTER_SHAPE)?;
        let taint = |src: &str| spec_source_host_effect_taint(&cfg, &spec, src);
        assert_eq!(
            taint(ELAB_BLOCK_HOST_READ_SHAPE),
            HostEffectTaint::SpreadsToImporters,
            "an elab definer reading host state runs inside importers"
        );
        assert_eq!(
            taint(SPLIT_ATTR_TACTIC_SHAPE),
            HostEffectTaint::SpreadsToImporters,
            "@[tactic] on its own line governs the definition below it"
        );
        assert_eq!(
            taint(RUN_CMD_HELPER_SHAPE),
            HostEffectTaint::SelfOnly,
            "a run_cmd reaching host state through a same-file helper runs only here"
        );
        assert_eq!(
            taint(LINTER_SHAPE),
            HostEffectTaint::None,
            "the #433 linter shape stays clean"
        );
        assert_eq!(
            taint(REG_LINTER_SHAPE),
            HostEffectTaint::None,
            "`initialize addLinter fooLinter` registers, it does not run: #433's \
             definition-only IO must stay untainted"
        );
        assert_eq!(
            taint(REG_ENV_EXT_SHAPE),
            HostEffectTaint::SpreadsToImporters,
            "registerEnvExtension runs its initial-value thunk whenever an importer \
             creates its environment: not a store-only registration"
        );
        assert_eq!(
            taint(REG_BUILTIN_ATTR_SHAPE),
            HostEffectTaint::SpreadsToImporters,
            "a registerBuiltinAttribute handler runs in every importer that applies \
             the attribute: not a store-only registration"
        );
        assert_eq!(
            taint(PRIVATE_DEF_INIT_HELPER_SHAPE),
            HostEffectTaint::SpreadsToImporters,
            "a modifier-prefixed helper the initializer runs is import-time taint"
        );
        assert_eq!(
            taint(INIT_LIST_ATTR_SHAPE),
            HostEffectTaint::SpreadsToImporters,
            "`init` inside an attribute list is an initializer trigger"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// #407: a warm hit runs zero `lake --no-cache` invocations, and the tool logs every
    /// Lake build it runs so a benchmark can assert that. The first freshness pass over a
    /// linter-shaped pinned dependency may Lake-build the missing artifacts (logged,
    /// without `--no-cache`); the second pass is a warm hit and must add no Lake
    /// invocation at all.
    #[test]
    fn host_effects_issue_407_warm_hit_runs_zero_lake_no_cache() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let (dir, _cfg, _spec) = pinned_dep_fixture("warmhit", LINTER_SHAPE)?;
        let proj = fs::canonicalize(dir.join("proj"))?;
        let tc = include_str!("../../../../lean/lean-toolchain").trim().to_string();
        let lake_log = dir.join("lake-cmd.log");
        // The log path is thread-local in tests, so a concurrently running test that
        // builds with Lake cannot write into this test's log.
        TEST_LAKE_CMD_LOG.with(|p| *p.borrow_mut() = Some(lake_log.clone()));
        let run = || -> Result<()> {
            let target = [proj.join("Proj.lean")];
            reset_lake_inputs_tag_memo();
            let rebuilt =
                crate::lake_build::ensure_project_imports_fresh(&proj, &target, Some(&tc), true)?;
            assert!(rebuilt >= 1, "first call must Lake-build the missing dep import");
            let after_first = fs::read_to_string(&lake_log).unwrap_or_default();
            assert!(
                after_first.lines().count() >= 1,
                "every Lake build the tool runs must be logged (#407); got: {after_first:?}"
            );
            assert!(
                !after_first.contains("--no-cache"),
                "a linter-shaped pinned dependency must not force `lake --no-cache` (#407/#433); got: {after_first:?}"
            );
            reset_lake_inputs_tag_memo();
            let rebuilt2 =
                crate::lake_build::ensure_project_imports_fresh(&proj, &target, Some(&tc), true)?;
            assert_eq!(rebuilt2, 0, "warm hit must find nothing stale (#407)");
            let after_second = fs::read_to_string(&lake_log).unwrap_or_default();
            assert_eq!(
                after_second, after_first,
                "a warm hit must run zero Lake invocations (#407)"
            );
            Ok(())
        };
        let res = run();
        TEST_LAKE_CMD_LOG.with(|p| *p.borrow_mut() = None);
        let _ = fs::remove_dir_all(dir);
        res
    }

    /// An `include_str` target inside a pinned package root but not tracked at the
    /// pinned rev (generated or gitignored) is not covered by the pin.
    #[test]
    fn host_effects_untracked_pinned_include_str_taints() -> Result<()> {
        let tracked_src = "def d := include_str \"data.txt\"\n";
        let untracked_src = "def g := include_str \"gen.txt\"\n";
        let (dir, cfg, spec) = pinned_dep_fixture("untracked_include", tracked_src)?;
        assert_eq!(
            spec_source_host_effect_taint(&cfg, &spec, tracked_src),
            HostEffectTaint::None,
            "a tracked in-tree include target is covered by the pin"
        );
        // A gitignored (generated) file inside the package root: present, invisible to
        // the clean check, but not fixed by the pinned rev.
        fs::write(spec.pkg_root.join("gen.txt"), "generated\n")?;
        assert_eq!(
            spec_source_host_effect_taint(&cfg, &spec, untracked_src),
            HostEffectTaint::SelfOnly,
            "an untracked include target is not covered by the pin"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// Stamp eligibility keeps its host-read meaning. A path-dependency module with a
    /// pure elaborator (no host read) stays stamp-eligible; the taint stays on the
    /// separate gated check. Host-reading editable sources stay ineligible.
    #[test]
    fn host_effects_stamp_eligibility_is_host_read_only() -> Result<()> {
        let (dir, cfg, spec) = dep_fixture("stamp_pure_elab", PURE_ELAB_SHAPE, false)?;
        assert!(
            !source_ineligible_for_stamp_reuse(
                &cfg,
                &spec.pkg_root,
                &spec.module_name,
                &spec.src_path,
                PURE_ELAB_SHAPE,
            ),
            "a pure elaborator must stay stamp-eligible"
        );
        assert!(
            spec_source_has_disallowed_elab_host_effects(&cfg, &spec, PURE_ELAB_SHAPE),
            "the gated taint check still covers the pure elaborator"
        );
        assert!(
            source_ineligible_for_stamp_reuse(
                &cfg,
                &spec.pkg_root,
                &spec.module_name,
                &spec.src_path,
                LINTER_SHAPE,
            ),
            "an editable module whose source may read host state stays stamp-ineligible"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// #438 and #434 together: spreading follows execution, deletion follows
    /// ownership, and a refusal is keyed on the unowned module's own artifact. A
    /// definition-only linter module (registration included) purges nothing;
    /// project-owned path-dependency artifacts are purged in place along with the
    /// importer cone; a pinned (unowned) module with FRESH artifacts completes the
    /// refresh — spreading taint still purges the owned importers, while a `SelfOnly`
    /// one is skipped outright (its unchanged digest already pins the importers, DA
    /// 71add786 finding 3); only a pinned module whose own artifact is actually
    /// stale fails the walk closed, deleting nothing, because clearing that needs a
    /// rebuild in the dependency's own workspace.
    #[test]
    fn host_effects_purge_follows_ownership_and_fails_closed_on_refusal() -> Result<()> {
        #[allow(clippy::type_complexity)]
        let rows: [(&str, &str, bool, bool, Result<(bool, bool), ()>); 10] = [
            ("linter", LINTER_SHAPE, true, false, Ok((false, false))),
            ("reglinter", REG_LINTER_SHAPE, true, false, Ok((false, false))),
            ("path_elabread", ELAB_BLOCK_HOST_READ_SHAPE, false, false, Ok((true, true))),
            ("path_importtime", IMPORT_TIME_SHAPE, false, false, Ok((true, true))),
            ("pinned_elabread_fresh", ELAB_BLOCK_HOST_READ_SHAPE, true, false, Ok((false, true))),
            ("pinned_importtime_fresh", IMPORT_TIME_SHAPE, true, false, Ok((false, true))),
            ("pinned_selfonly_fresh", RUN_CMD_HELPER_SHAPE, true, false, Ok((false, false))),
            ("pinned_eval_fresh", EVAL_SHAPE, true, false, Ok((false, false))),
            ("pinned_importtime_stale", IMPORT_TIME_SHAPE, true, true, Err(())),
            ("pinned_selfonly_stale", RUN_CMD_HELPER_SHAPE, true, true, Err(())),
        ];
        for (label, dep_source, git_pinned, stale_dep, expect) in rows {
            let (dir, cfg, spec) =
                dep_fixture(&format!("purge_{label}"), dep_source, git_pinned)?;
            let dep_olean = spec.build_lib_lean_dir.join("LintLib.olean");
            fs::create_dir_all(dep_olean.parent().unwrap())?;
            fs::write(&dep_olean, b"fake dep olean")?;
            if stale_dep {
                // Dial the artifact's mtime below the source's: the artifact itself
                // is stale, independent of filesystem timestamp granularity.
                fs::File::options().write(true).open(&dep_olean)?.set_modified(
                    std::time::SystemTime::now() - std::time::Duration::from_secs(3600),
                )?;
            }
            let root_spec = resolve_module_in_package(&cfg.root_pkg, true, "Proj")
                .expect("root module resolves");
            let root_olean = root_spec.build_lib_lean_dir.join("Proj.olean");
            fs::create_dir_all(root_olean.parent().unwrap())?;
            fs::write(&root_olean, b"fake root olean")?;
            let res = purge_elab_host_effect_artifacts_in_closure(&cfg, &["Proj".to_string()]);
            match expect {
                Ok((expect_dep_purged, expect_importer_purged)) => {
                    let purged = res.unwrap_or_else(|e| panic!("{label}: {e:#}"));
                    assert_eq!(
                        purged,
                        expect_dep_purged || expect_importer_purged,
                        "{label}: purged_any"
                    );
                    assert_eq!(!dep_olean.is_file(), expect_dep_purged, "{label}: dep artifact");
                    assert_eq!(
                        !root_olean.is_file(),
                        expect_importer_purged,
                        "{label}: importer artifact"
                    );
                }
                Err(()) => {
                    let err = res.expect_err(
                        "an unowned module whose own artifact is stale must fail the \
                         walk closed, not be kept silently",
                    );
                    assert!(
                        format!("{err:#}").contains("Failed to purge stale build artifact"),
                        "{label}: refusal must name the purge failure, got: {err:#}"
                    );
                    assert!(
                        format!("{err:#}").contains("its own workspace"),
                        "{label}: refusal must name the action that clears the \
                         condition (an own-workspace rebuild), got: {err:#}"
                    );
                    assert!(
                        dep_olean.is_file() && root_olean.is_file(),
                        "{label}: a refusal must delete nothing"
                    );
                }
            }
            let _ = fs::remove_dir_all(dir);
        }
        Ok(())
    }

    /// #433: taint spreads to importers only from import-time host reads. A root module
    /// with a definition-only host read is tainted itself but must not taint its importer.
    #[test]
    fn host_effects_issue_433_taint_spreads_only_from_import_time_host_reads() -> Result<()> {
        for (label, linter_src, expect_importer_tainted) in [
            ("defonly", LINTER_SHAPE, false),
            ("importtime", IMPORT_TIME_SHAPE, true),
            // An elaborator that reads host state runs inside importers.
            ("elabdef", ELAB_BLOCK_HOST_READ_SHAPE, true),
        ] {
            let dir = temp_dir(label);
            let proj = dir.join("proj");
            fs::create_dir_all(proj.join("P"))?;
            fs::write(
                proj.join("lean-toolchain"),
                include_str!("../../../../lean/lean-toolchain"),
            )?;
            fs::write(
                proj.join("lakefile.toml"),
                "name = \"p\"\ndefaultTargets = [\"P\"]\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n",
            )?;
            fs::write(proj.join("P/Linter.lean"), linter_src)?;
            fs::write(
                proj.join("P/Top.lean"),
                "import P.Linter\ndef top : Nat := 2\n",
            )?;
            let canon = fs::canonicalize(&proj)?;
            reset_lake_inputs_tag_memo();
            let cfg = resolve_project_config(&canon)?;
            let dag = build_module_dag(&cfg, &["P.Top".to_string()])?;
            let tainted = compute_tainted_elab_host_effect_modules(&cfg, &dag);
            assert!(
                tainted.contains("P.Linter"),
                "{label}: the host-reading module itself must stay tainted"
            );
            assert_eq!(
                tainted.contains("P.Top"),
                expect_importer_tainted,
                "{label}: importer taint must follow import-time execution only (#433); got {tainted:?}"
            );
            let _ = fs::remove_dir_all(dir);
        }
        Ok(())
    }

    /// An `initialize` body that reaches host state only through a same-file helper
    /// `def` must classify like the direct shape (`SpreadsToImporters`), not narrower:
    /// the body still re-runs in every importer.
    #[test]
    fn host_effects_initialize_via_same_file_helper_spreads() -> Result<()> {
        let (dir, cfg, spec) = pinned_dep_fixture("init_helper", INIT_HELPER_INDIRECTION_SHAPE)?;
        assert_eq!(
            spec_source_host_effect_taint(&cfg, &spec, INIT_HELPER_INDIRECTION_SHAPE),
            spec_source_host_effect_taint(&cfg, &spec, IMPORT_TIME_SHAPE),
            "same-file helper indirection must take the whole-file verdict IMPORT_TIME_SHAPE gets"
        );
        assert_eq!(
            spec_source_host_effect_taint(&cfg, &spec, INIT_HELPER_INDIRECTION_SHAPE),
            HostEffectTaint::SpreadsToImporters,
            "an initialize body reading host state through a same-file helper spreads"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// The `@[init f]` / `@[builtin_init f]` attribute spellings are initializer
    /// triggers like the `initialize` keyword, so an `@[init helper]` whose helper
    /// reads host state classifies as import-time taint (`SpreadsToImporters`).
    #[test]
    fn host_effects_init_attribute_spelling_is_an_initializer_trigger() -> Result<()> {
        let (dir, cfg, spec) = pinned_dep_fixture("init_attr", INIT_ATTR_HELPER_SHAPE)?;
        assert_eq!(
            spec_source_host_effect_taint(&cfg, &spec, INIT_ATTR_HELPER_SHAPE),
            spec_source_host_effect_taint(&cfg, &spec, IMPORT_TIME_SHAPE),
            "`@[init helper]` must take the whole-file verdict IMPORT_TIME_SHAPE gets"
        );
        assert_eq!(
            spec_source_host_effect_taint(&cfg, &spec, INIT_ATTR_HELPER_SHAPE),
            HostEffectTaint::SpreadsToImporters,
            "`@[init helper]` with a host-reading same-file helper spreads"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// Spreading taint in an external dependency travels the dependency's own import
    /// graph, not just one hop.
    #[test]
    fn host_effects_external_dep_spreading_travels_its_import_graph() -> Result<()> {
        let (dir, cfg, spec) = dep_fixture_with(
            "ext_transitive",
            "import LintLib.A\ndef l : Nat := 0\n",
            true,
            &[("LintLib/A.lean", IMPORT_TIME_SHAPE)],
        )?;
        let own = fs::read_to_string(&spec.src_path)?;
        assert_eq!(
            spec_source_host_effect_taint(&cfg, &spec, &own),
            HostEffectTaint::None,
            "LintLib's own source carries no taint"
        );
        let mut memo = HashMap::new();
        assert!(
            spec_spreads_host_effects_transitively(&cfg, &spec, &mut memo),
            "a spreading initialize below LintLib must reach it through its own imports"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// The daemon outlives edits: when an imported module's source gains an
    /// `initialize` host read while the importer's own content is unchanged, the
    /// importer's recomputed transitive verdict must flip. A verdict cached under the
    /// importer's own content hash would come back stale without recursing.
    #[test]
    fn host_effects_transitive_spread_verdict_tracks_edited_imports() -> Result<()> {
        let (dir, cfg, spec) = dep_fixture_with(
            "spread_recompute",
            "import LintLib.A\ndef l : Nat := 0\n",
            false,
            &[("LintLib/A.lean", "def a : Nat := 1\n")],
        )?;
        let mut memo = HashMap::new();
        assert!(
            !spec_spreads_host_effects_transitively(&cfg, &spec, &mut memo),
            "a clean two-module dependency must not spread"
        );
        fs::write(spec.pkg_root.join("LintLib/A.lean"), IMPORT_TIME_SHAPE)?;
        // The daemon's next request resets the memo window at entry; model it.
        reset_lake_inputs_tag_memo();
        let mut memo2 = HashMap::new();
        assert!(
            spec_spreads_host_effects_transitively(&cfg, &spec, &mut memo2),
            "an initialize host read added below an unchanged importer must flip the \
             importer's transitive verdict"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// A universe-polymorphic head (`def helper.{u}`) defines `helper`: the trailing
    /// dot of the scanned name belongs to the `.{u}` suffix, not the name, and a name
    /// ending in a dot never matches any reference.
    #[test]
    fn defined_def_names_strip_universe_suffix_dots() {
        let names = defined_def_names("def helper.{u} : Sort u := default\n");
        assert!(
            names.iter().any(|n| n == "helper"),
            "def helper.{{u}} must define `helper`; got {names:?}"
        );
        let dotted = defined_def_names("def Foo.helper.{u} : Sort u := default\n");
        assert!(
            dotted.iter().any(|n| n == "helper") && dotted.iter().any(|n| n == "Foo.helper"),
            "def Foo.helper.{{u}} must define `Foo.helper` and its last segment; got {dotted:?}"
        );
    }

    /// The checkout is pinned only between requests: a daemon outlives `lake update`,
    /// after which the same package path can hold a rev where a target's tracked-ness
    /// changed. The tracked-include memo must reset with the Lake-inputs memo window.
    #[test]
    fn tracked_include_memo_resets_with_the_lake_inputs_memo_window() -> Result<()> {
        let dir = temp_dir("tracked_reset");
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("data.txt"), "x\n")?;
        git_init_commit(&dir)?;
        let canon = fs::canonicalize(&dir)?;
        let rels = [PathBuf::from("data.txt")];
        assert!(
            include_targets_tracked_at_pin(&canon, &rels),
            "a committed file is tracked at the pin"
        );
        // The pin moves while the process runs: data.txt is no longer tracked.
        let git = |args: &[&str]| -> Result<()> {
            anyhow::ensure!(crate::trusted_tools::git(&canon)?
                .arg("-C")
                .arg(&canon)
                .args(["-c", "user.name=t", "-c", "user.email=t@e", "-c", "commit.gpgsign=false"])
                .args(args)
                .status()?
                .success());
            Ok(())
        };
        git(&["rm", "--cached", "-q", "data.txt"])?;
        git(&["commit", "-qm", "untrack"])?;
        // No assert on the memoized stale answer here: the memo is process-global and
        // any concurrently running fixture test may reset the window between the
        // seeding call above and a re-read, so only the post-reset behavior below is a
        // stable promise. (Before the fix nothing cleared the memo at all, so the
        // final assert alone is the deterministic red.)
        reset_lake_inputs_tag_memo();
        assert!(
            !include_targets_tracked_at_pin(&canon, &rels),
            "a new memo window must re-read git: the pin can move while the daemon runs"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// The publication half of the tracked-include memo, exercised deterministically
    /// (the shape of `test_lake_inputs_tag_memo_rejects_cross_request_publication`):
    /// an entry stamped with a superseded window — what a git read started before a
    /// reset would insert afterwards — is ignored, never served to the new window.
    #[test]
    fn tracked_include_memo_ignores_entries_from_a_superseded_window() -> Result<()> {
        let dir = temp_dir("tracked_stale_window");
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("data.txt"), "x\n")?;
        git_init_commit(&dir)?;
        let canon = fs::canonicalize(&dir)?;
        let rel = PathBuf::from("data.txt");
        reset_lake_inputs_tag_memo();
        let superseded = current_memo_window().wrapping_sub(1);
        TRACKED_INCLUDE_MEMO
            .get_or_init(|| std::sync::Mutex::new(HashMap::new()))
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert((canon.clone(), rel.clone()), (superseded, false));
        assert!(
            include_targets_tracked_at_pin(&canon, &[rel]),
            "a planted wrong answer stamped with a superseded window must be ignored: \
             the tracked file re-reads as tracked"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// The window-scoped transitive spread cache never serves a superseded window: a
    /// planted wrong verdict stamped with an old window is ignored and the clean
    /// closure recomputes (DA 71add786 finding 5's cache, finding 2's stamping).
    #[test]
    fn transitive_spread_cache_ignores_entries_from_a_superseded_window() -> Result<()> {
        let (dir, cfg, spec) = dep_fixture_with(
            "spread_stale_window",
            "import LintLib.A\ndef l : Nat := 0\n",
            false,
            &[("LintLib/A.lean", "def a : Nat := 1\n")],
        )?;
        reset_lake_inputs_tag_memo();
        let superseded = current_memo_window().wrapping_sub(1);
        SPREAD_TRANSITIVE_VERDICTS
            .get_or_init(|| std::sync::Mutex::new(HashMap::new()))
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(
                (
                    cfg.canonical_config_digest.clone(),
                    spec.pkg_root.clone(),
                    spec.module_name.clone(),
                ),
                (superseded, true),
            );
        let mut memo = HashMap::new();
        assert!(
            !spec_spreads_host_effects_transitively(&cfg, &spec, &mut memo),
            "a planted wrong verdict stamped with a superseded window must be \
             ignored: the clean closure recomputes to non-spreading"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// DA 3ff1014b finding 2: an intermediate verdict computed through a cycle cut (it
    /// read an ancestor's in-progress entry) is only valid inside that call. Published
    /// to the cross-call cache it serves a wrong "does not spread" answer for the rest
    /// of the window: A imports B and a spreading C, B imports A back; querying A first
    /// computes B = false against A's in-progress entry, and a later fresh query for B
    /// in the same window must still answer true.
    #[test]
    fn transitive_spread_cycle_cut_verdicts_stay_per_call() -> Result<()> {
        // Serializes the process-global memo window against the module_builder tests
        // that bump it: a reset between the two queries below would clear the cache and
        // mask a poisoned entry.
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let (dir, cfg, spec) = dep_fixture_with(
            "spread_cycle",
            "import LintLib.B\nimport LintLib.C\ndef l : Nat := 0\n",
            false,
            &[
                ("LintLib/B.lean", "import LintLib\ndef b : Nat := 0\n"),
                ("LintLib/C.lean", IMPORT_TIME_SHAPE),
            ],
        )?;
        let dep_pkg = cfg
            .dep_pkgs
            .iter()
            .find(|dp| dp.name == "lintlib")
            .expect("dep pkg");
        let b_spec = resolve_module_in_package(dep_pkg, false, "LintLib.B")
            .expect("LintLib.B resolves in lintlib");
        reset_lake_inputs_tag_memo();
        let mut memo = HashMap::new();
        assert!(
            spec_spreads_host_effects_transitively(&cfg, &spec, &mut memo),
            "the queried root spreads through C whatever the cycle contributes"
        );
        let published_b = SPREAD_TRANSITIVE_VERDICTS
            .get_or_init(|| std::sync::Mutex::new(HashMap::new()))
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get(&(
                cfg.canonical_config_digest.clone(),
                b_spec.pkg_root.clone(),
                b_spec.module_name.clone(),
            ))
            .copied();
        assert!(
            published_b.is_none(),
            "a cycle-cut intermediate stays per-call, never published: {published_b:?}"
        );
        let mut memo2 = HashMap::new();
        assert!(
            spec_spreads_host_effects_transitively(&cfg, &b_spec, &mut memo2),
            "B spreads through A: the cycle-cut intermediate from A's call must not \
             be served from the cross-call cache"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }

    /// DA 3ff1014b finding 2 (key): the cross-call cache key carries the project
    /// configuration identity, so a verdict computed under another configuration for
    /// the same (package root, module) is never served.
    #[test]
    fn transitive_spread_cache_is_scoped_to_the_project_config() -> Result<()> {
        let (dir, cfg, spec) = dep_fixture_with(
            "spread_cfg_scope",
            "import LintLib.A\ndef l : Nat := 0\n",
            false,
            &[("LintLib/A.lean", "def a : Nat := 1\n")],
        )?;
        reset_lake_inputs_tag_memo();
        let window = current_memo_window();
        SPREAD_TRANSITIVE_VERDICTS
            .get_or_init(|| std::sync::Mutex::new(HashMap::new()))
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(
                (
                    "another-project-config-digest".to_string(),
                    spec.pkg_root.clone(),
                    spec.module_name.clone(),
                ),
                (window, true),
            );
        let mut memo = HashMap::new();
        assert!(
            !spec_spreads_host_effects_transitively(&cfg, &spec, &mut memo),
            "a verdict stamped with another project configuration must be ignored: \
             the clean closure recomputes to non-spreading"
        );
        let _ = fs::remove_dir_all(dir);
        Ok(())
    }
}
