use anyhow::{bail, Context, Result};
use serde_json::{json, Value};
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use super::audit_spec::{
    audit_spec_file_or_source_with_policy, extract_all_lean_theorems, extract_local_def_unfoldings,
    inline_stmt_let_bindings, AuditSpecPolicyConfig,
};
use super::{
    is_known_binder_value_type, split_top_level_colon, split_top_level_implications,
    strip_lean_comments, ExtractedDecl,
};
use crate::splitter::{
    audit_hygiene, canonicalize_lean_name, decl_name_matches_target, extract_public_signature,
    qualified_decl_name, skip_lean_lexeme, ScopeFrame, ScopeKind,
};

const UNCHECKED: &[&str] = &[
    "transitive imported axioms (statement text is not elaborated and imports are not walked)",
    "semantic domain intent, including whether hypotheses are logically independent",
    "unmodeled FFI, native, and environment boundaries",
    "proof-term completeness beyond source tokens (sorry, admit, axiom, native_decide, extern)",
    "instance binders and section variable/include context are syntactic only; nonstandard ones are not evaluated",
];

const TOTAL_INSTANCE_HEADS: &[&str] = &[
    "BEq",
    "DecidableEq",
    "DecidablePred",
    "DecidableRel",
    "Hashable",
    "LE",
    "LT",
    "Ord",
    "Repr",
    "ToString",
];

const PRIMITIVE_LAWFUL_TYPES: &[&str] = &[
    "Bool", "Char", "Int", "Nat", "String", "UInt8", "UInt16", "UInt32", "UInt64", "USize",
];

pub fn run_spec_card_command(
    files: &[PathBuf],
    decl_filter: Option<&str>,
    json_mode: bool,
    policy_override: Option<&str>,
    config_override: Option<&Path>,
    public_only: bool,
) -> Result<()> {
    anyhow::ensure!(!files.is_empty(), "No files provided to spec-card");
    for file in files {
        anyhow::ensure!(
            file.exists(),
            "Failed to read {}: path does not exist",
            file.display()
        );
    }
    if let Some(policy) = policy_override {
        anyhow::ensure!(
            matches!(
                policy.trim().to_ascii_lowercase().as_str(),
                "default" | "permissive" | "strict-proofs" | "strict_proofs" | "strict"
            ),
            "Unknown audit-spec policy: {policy}"
        );
    }
    if let Some(path) = config_override {
        let text = fs::read_to_string(path)
            .with_context(|| format!("Failed to read audit-spec config {}", path.display()))?;
        anyhow::ensure!(
            AuditSpecPolicyConfig::parse_config_str(&text).is_some(),
            "Invalid audit-spec config {}",
            path.display()
        );
    }
    let started = Instant::now();
    let mut sources = Vec::new();
    for file in files {
        sources.extend(load_sources(file)?);
    }
    sources.sort_by(|left, right| left.0.cmp(&right.0));
    sources.dedup_by(|left, right| left.0 == right.0);
    let mut cards = Vec::new();
    let mut matched = 0usize;
    let mut hidden_private = 0usize;
    let mut hygiene_dirty = false;
    let mut extraction_incomplete = false;
    let mut all_audits_ok = true;
    let mut any_audit_error = false;
    let mut resolved_policies = Vec::with_capacity(sources.len());
    for (path, src) in &sources {
        let policy = AuditSpecPolicyConfig::load_for_target(
            path,
            policy_override,
            config_override,
            &[],
            &[],
        );
        resolved_policies.push(policy.policy.clone());
        let audit = audit_spec_file_or_source_with_policy(path, None, decl_filter, &policy);
        if audit.get("status").and_then(Value::as_str) == Some("error") {
            any_audit_error = true;
        }
        if audit.get("ok").and_then(Value::as_bool) != Some(true) {
            all_audits_ok = false;
        }
        let clean = strip_lean_comments(src);
        let hygiene = audit_hygiene(&clean);
        if !hygiene_flags(&hygiene).is_empty() {
            hygiene_dirty = true;
        }
        let public_sig = extract_public_signature(src);
        let public_names: BTreeSet<String> = public_sig
            .declarations
            .iter()
            .filter(|decl| decl.kind == "theorem" || decl.kind == "lemma")
            .map(|decl| canonicalize_lean_name(&decl.const_name))
            .collect();
        let visibility_known = !public_sig
            .public_signature_digest
            .starts_with("pubsig-custom-cmd:")
            && !public_sig
                .public_signature_digest
                .starts_with("pubsig-invalid:");
        let local_defs = extract_local_def_unfoldings(&clean);
        let details = audit
            .get("specs")
            .and_then(Value::as_array)
            .cloned()
            .unwrap_or_default();
        let all_decls = extract_all_lean_theorems(src, None);
        let (extras, file_has_malformed_scope) = scan_decl_extras(src);
        if file_has_malformed_scope {
            extraction_incomplete = true;
        }
        let aligned_extras = all_decls.len() == extras.len();
        let mut filtered_idx = 0usize;
        for (decl_idx, decl) in all_decls.into_iter().enumerate() {
            let matches_filter = match decl_filter {
                Some(target) if !target.is_empty() && target != "auto" => {
                    decl_name_matches_target(&decl.name, target)
                }
                _ => true,
            };
            if !matches_filter {
                continue;
            }
            matched += 1;
            let detail = details.get(filtered_idx);
            filtered_idx += 1;
            let extra = aligned_extras.then(|| &extras[decl_idx]);
            let effective_name = extra.map_or(decl.name.as_str(), |row| row.name.as_str());
            let visibility = visibility_of(
                effective_name,
                &public_names,
                visibility_known,
                public_sig.is_module,
                extra,
            );
            if public_only && visibility != "public" {
                if visibility == "unresolved"
                    || extra.is_none()
                    || extra.is_some_and(|row| row.saw_unparsed_binder)
                {
                    extraction_incomplete = true;
                }
                hidden_private += 1;
                continue;
            }
            let ctx = FileCardCtx {
                path,
                local_defs: &local_defs,
                hygiene: &hygiene,
                audit: &audit,
            };
            cards.push(card_for(
                &ctx,
                &decl,
                effective_name,
                visibility,
                extra,
                detail,
            ));
        }
    }
    let policy_name = match resolved_policies.first() {
        Some(first) if resolved_policies.iter().all(|item| item == first) => first.clone(),
        Some(_) => "mixed".to_string(),
        None => policy_override.unwrap_or("default").to_string(),
    };
    let elapsed_ms = (started.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
    let filter_miss = decl_filter.is_some() && matched == 0;
    let public_miss = public_only && matched > 0 && cards.is_empty();
    let incomplete = extraction_incomplete
        || cards.iter().any(|card| {
            card.pointer("/contract/extraction_complete")
                .and_then(Value::as_bool)
                == Some(false)
        });
    let all_cards_tight = cards
        .iter()
        .all(|card| card.get("verdict").and_then(Value::as_str) == Some("TIGHT"));
    let ok = !any_audit_error
        && all_audits_ok
        && all_cards_tight
        && !hygiene_dirty
        && !filter_miss
        && !public_miss
        && !incomplete;
    let status = if any_audit_error {
        "error"
    } else if ok {
        "ok"
    } else {
        "failed"
    };
    let report = json!({
        "status": status,
        "ok": ok,
        "analysis_tier": "source_syntactic",
        "unchecked_boundaries": UNCHECKED,
        "summary": {
            "files": sources.len(),
            "cards": cards.len(),
            "matched_decls": matched,
            "hidden_by_public_only": hidden_private,
            "audit_ok": all_audits_ok,
            "hygiene_clean": !hygiene_dirty,
            "extraction_complete": !incomplete,
            "policy": policy_name,
            "elapsed_ms": elapsed_ms,
        },
        "cards": cards,
    });
    if json_mode {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        print!("{}", render_human(&report));
    }
    if !ok {
        std::process::exit(1);
    }
    Ok(())
}

fn load_sources(file: &Path) -> Result<Vec<(PathBuf, String)>> {
    if file.is_dir() {
        let paths = crate::lake_build::collect_lean_files(file);
        if paths.is_empty() {
            bail!("No readable Lean files found in {}", file.display());
        }
        let mut sources = Vec::with_capacity(paths.len());
        for path in paths {
            let src = fs::read_to_string(&path)
                .with_context(|| format!("Failed to read {}", path.display()))?;
            sources.push((path, src));
        }
        sources.sort_by(|left, right| left.0.cmp(&right.0));
        return Ok(sources);
    }
    let src =
        fs::read_to_string(file).with_context(|| format!("Failed to read {}", file.display()))?;
    let mut sources = vec![(file.to_path_buf(), src)];
    let sub_dir = file.with_extension("");
    if sub_dir.is_dir() {
        for path in crate::lake_build::collect_lean_files(&sub_dir) {
            let sub_src = fs::read_to_string(&path)
                .with_context(|| format!("Failed to read {}", path.display()))?;
            sources.push((path, sub_src));
        }
        sources.sort_by(|left, right| left.0.cmp(&right.0));
    }
    Ok(sources)
}

struct DeclExtra {
    name: String,
    is_private: bool,
    explicit_public: bool,
    instance_binders: Vec<String>,
    context_assumptions: Vec<String>,
    saw_unparsed_binder: bool,
}

fn scan_decl_extras(src: &str) -> (Vec<DeclExtra>, bool) {
    let masked = mask_comments(src);
    let chars: Vec<char> = masked.chars().collect();
    let byte_offsets: Vec<usize> = masked.char_indices().map(|(offset, _)| offset).collect();
    let n = chars.len();
    let mut i = 0usize;
    let mut scope: Vec<ScopeFrame> = Vec::new();
    let mut context: Vec<Vec<String>> = vec![Vec::new()];
    let mut at_cmd_head = true;
    let mut pending_private = false;
    let mut pending_public = false;
    let mut pending_assumptions: Vec<String> = Vec::new();
    let mut has_malformed_scope = false;
    let mut out = Vec::new();
    while i < n {
        if let Some(end) = skip_any(&masked, &byte_offsets, i) {
            i = end;
            continue;
        }
        if chars[i] == '\n' {
            if !at_cmd_head {
                pending_private = false;
                pending_public = false;
                pending_assumptions.clear();
            }
            at_cmd_head = true;
            i += 1;
            continue;
        }
        if chars[i] == ';' {
            at_cmd_head = true;
            pending_private = false;
            pending_public = false;
            pending_assumptions.clear();
            i += 1;
            continue;
        }
        if chars[i].is_whitespace() {
            i += 1;
            continue;
        }
        if at_cmd_head && chars[i] == '@' && i + 1 < n && chars[i + 1] == '[' {
            if let Some(end) = matching_close(&masked, &byte_offsets, &chars, i + 1, '[', ']') {
                i = end;
                continue;
            }
        }
        if at_cmd_head {
            if let Some((after_in, inline_assumption)) =
                consume_in_command_prefix(&masked, &byte_offsets, &chars, i)
            {
                if let Some(assumption) = inline_assumption {
                    pending_assumptions.push(assumption);
                }
                i = after_in;
                continue;
            }
        }
        if chars[i] == '«' {
            if let Some(end) = skip_any_lexeme(&masked, &byte_offsets, i) {
                at_cmd_head = false;
                pending_private = false;
                pending_public = false;
                pending_assumptions.clear();
                i = end;
                continue;
            }
        }
        if !is_ident_start(chars[i]) {
            at_cmd_head = false;
            pending_private = false;
            pending_public = false;
            pending_assumptions.clear();
            i += 1;
            continue;
        }
        let start = i;
        while i < n && is_ident_continue(chars[i]) {
            i += 1;
        }
        let word: String = chars[start..i].iter().collect();
        if !at_cmd_head && !matches!(word.as_str(), "theorem" | "lemma") {
            continue;
        }
        if at_cmd_head
            && matches!(
                word.as_str(),
                "public"
                    | "private"
                    | "protected"
                    | "noncomputable"
                    | "scoped"
                    | "local"
                    | "unsafe"
                    | "partial"
                    | "nonrec"
                    | "meta"
            )
        {
            if word == "private" || word == "local" {
                pending_private = true;
                pending_public = false;
            }
            if word == "public" {
                pending_public = true;
                pending_private = false;
            }
            if word == "scoped" && i < n && chars[i] == '[' {
                if let Some(end) = matching_close(&masked, &byte_offsets, &chars, i, '[', ']') {
                    i = end;
                }
            }
            continue;
        }
        let was_at_cmd_head = at_cmd_head;
        let decl_private = std::mem::replace(&mut pending_private, false);
        let decl_public = std::mem::replace(&mut pending_public, false);
        let decl_inline_assumptions = if matches!(word.as_str(), "theorem" | "lemma") {
            std::mem::take(&mut pending_assumptions)
        } else {
            Vec::new()
        };
        if !matches!(
            word.as_str(),
            "namespace" | "section" | "mutual" | "theorem" | "lemma"
        ) {
            pending_assumptions.clear();
        }
        at_cmd_head = false;
        match word.as_str() {
            "namespace" if i < n && chars[i].is_whitespace() => {
                if decl_public || decl_private {
                    has_malformed_scope = true;
                }
                let (name, next) = dotted_name(&masked, &byte_offsets, &chars, i, n);
                i = next;
                let segs: Vec<&str> = crate::splitter::split_lean_name_components(&name);
                let inline = std::mem::take(&mut pending_assumptions);
                let last_idx = segs.len().saturating_sub(1);
                for (seg_idx, seg) in segs.into_iter().enumerate() {
                    scope.push(ScopeFrame {
                        kind: ScopeKind::Namespace,
                        name: seg.to_string(),
                        open_span_idx: 0,
                    });
                    context.push(if seg_idx == last_idx {
                        inline.clone()
                    } else {
                        Vec::new()
                    });
                }
                at_cmd_head = true;
            }
            "section" => {
                if decl_private {
                    has_malformed_scope = true;
                }
                let (name, next) = if i < n && chars[i].is_whitespace() && chars[i] != '\n' {
                    dotted_name(&masked, &byte_offsets, &chars, i, n)
                } else {
                    (String::new(), i)
                };
                i = next;
                let segs: Vec<String> = if name.is_empty() {
                    vec![String::new()]
                } else {
                    crate::splitter::split_lean_name_components(&name)
                        .into_iter()
                        .map(str::to_string)
                        .collect()
                };
                let inline = std::mem::take(&mut pending_assumptions);
                let last_idx = segs.len().saturating_sub(1);
                for (seg_idx, seg) in segs.into_iter().enumerate() {
                    scope.push(ScopeFrame {
                        kind: ScopeKind::Section,
                        name: seg,
                        open_span_idx: 0,
                    });
                    context.push(if seg_idx == last_idx {
                        inline.clone()
                    } else {
                        Vec::new()
                    });
                }
                at_cmd_head = true;
            }
            "mutual" if i >= n || chars[i].is_whitespace() => {
                if decl_public || decl_private {
                    has_malformed_scope = true;
                }
                scope.push(ScopeFrame {
                    kind: ScopeKind::Mutual,
                    name: String::new(),
                    open_span_idx: 0,
                });
                context.push(std::mem::take(&mut pending_assumptions));
                at_cmd_head = true;
            }
            "end" if i >= n || chars[i].is_whitespace() => {
                if decl_public || decl_private {
                    has_malformed_scope = true;
                }
                let (name, next) = if i < n && chars[i].is_whitespace() && chars[i] != '\n' {
                    dotted_name(&masked, &byte_offsets, &chars, i, n)
                } else {
                    (String::new(), i)
                };
                i = next;
                if pop_scope(&mut scope, &mut context, &name) {
                    has_malformed_scope = true;
                }
                at_cmd_head = true;
            }
            "variable" | "variables" | "include" | "omit" => {
                let body_start = i;
                while i < n && chars[i] != '\n' && chars[i] != ';' {
                    if let Some(end) = skip_any(&masked, &byte_offsets, i) {
                        i = end;
                        continue;
                    }
                    i += 1;
                }
                let body: String = chars[body_start..i].iter().collect();
                let clean_body = normalize_ws(&body);
                if let Some(frame) = context.last_mut() {
                    if clean_body.is_empty() {
                        frame.push(word);
                    } else {
                        frame.push(format!("{word} {clean_body}"));
                    }
                }
            }
            "theorem" | "lemma" => {
                while i < n && chars[i].is_whitespace() {
                    i += 1;
                }
                let (raw_name, next) = dotted_name(&masked, &byte_offsets, &chars, i, n);
                if raw_name.is_empty() {
                    continue;
                }
                i = next;
                let mut binders = Vec::new();
                let mut saw_unparsed_binder = !was_at_cmd_head;
                let mut found_colon = false;
                while i < n {
                    while i < n && chars[i].is_whitespace() {
                        i += 1;
                    }
                    if i >= n {
                        break;
                    }
                    if let Some(end) = skip_any_lexeme(&masked, &byte_offsets, i) {
                        i = end;
                        continue;
                    }
                    if chars[i] == ':' && (i + 1 >= n || chars[i + 1] != '=') {
                        i += 1;
                        found_colon = true;
                        break;
                    }
                    if chars[i] == ':' && i + 1 < n && chars[i + 1] == '=' {
                        break;
                    }
                    if chars[i] == '[' {
                        let open_at = i;
                        if let Some(end) =
                            matching_close(&masked, &byte_offsets, &chars, i, '[', ']')
                        {
                            let inner: String = chars[open_at + 1..end - 1].iter().collect();
                            binders.push(normalize_ws(&inner));
                            i = end;
                        } else {
                            saw_unparsed_binder = true;
                            break;
                        }
                    } else if chars[i] == '(' || chars[i] == '{' {
                        let close = if chars[i] == '(' { ')' } else { '}' };
                        if let Some(end) =
                            matching_close(&masked, &byte_offsets, &chars, i, chars[i], close)
                        {
                            i = end;
                        } else {
                            saw_unparsed_binder = true;
                            break;
                        }
                    } else if chars[i] == '⦃' {
                        saw_unparsed_binder = true;
                        if let Some(end) =
                            matching_close(&masked, &byte_offsets, &chars, i, '⦃', '⦄')
                        {
                            i = end;
                        } else {
                            break;
                        }
                    } else {
                        i += 1;
                    }
                }
                if !found_colon {
                    continue;
                }
                let stmt_start = i;
                let mut paren_depth = 0usize;
                let mut angle_depth = 0usize;
                let mut pending_let_assign = false;
                let mut stmt_end = n;
                while i < n {
                    if let Some(end) = skip_any_lexeme(&masked, &byte_offsets, i) {
                        i = end;
                        continue;
                    }
                    let ch = chars[i];
                    if ch == '(' || ch == '{' || ch == '[' {
                        paren_depth += 1;
                    } else if ch == ')' || ch == '}' || ch == ']' {
                        paren_depth = paren_depth.saturating_sub(1);
                    } else if ch == '⟨' {
                        angle_depth += 1;
                    } else if ch == '⟩' {
                        angle_depth = angle_depth.saturating_sub(1);
                    } else if paren_depth == 0
                        && angle_depth == 0
                        && ch == 'l'
                        && i + 3 < n
                        && chars[i + 1] == 'e'
                        && chars[i + 2] == 't'
                        && chars[i + 3].is_whitespace()
                        && (i == stmt_start || !is_ident_continue(chars[i - 1]))
                    {
                        pending_let_assign = true;
                        i += 3;
                        continue;
                    } else if paren_depth == 0
                        && angle_depth == 0
                        && ch == ':'
                        && i + 1 < n
                        && chars[i + 1] == '='
                    {
                        if pending_let_assign {
                            pending_let_assign = false;
                            i += 2;
                            continue;
                        }
                        stmt_end = i;
                        break;
                    } else if paren_depth == 0
                        && angle_depth == 0
                        && ch == '|'
                        && i > stmt_start
                        && chars[stmt_start..i].contains(&'\n')
                    {
                        stmt_end = i;
                        break;
                    }
                    i += 1;
                }
                let prop_str: String = chars[stmt_start..stmt_end].iter().collect();
                if inline_stmt_let_bindings(prop_str.trim()).is_empty() {
                    continue;
                }
                let mut assumptions: Vec<String> = context
                    .iter()
                    .flat_map(|frame| frame.iter().cloned())
                    .collect();
                assumptions.extend(decl_inline_assumptions);
                out.push(DeclExtra {
                    name: qualified_decl_name(&raw_name, &scope),
                    is_private: decl_private,
                    explicit_public: decl_public,
                    instance_binders: binders,
                    context_assumptions: assumptions,
                    saw_unparsed_binder,
                });
            }
            _ => {}
        }
    }
    (out, has_malformed_scope)
}

fn pop_scope(scope: &mut Vec<ScopeFrame>, context: &mut Vec<Vec<String>>, name: &str) -> bool {
    if name.is_empty() {
        let Some(top) = scope.pop() else {
            return true;
        };
        if context.len() > 1 {
            context.pop();
        }
        return !top.name.is_empty();
    }
    let mut malformed = false;
    for seg in crate::splitter::split_lean_name_components(name)
        .into_iter()
        .rev()
    {
        let canon = crate::splitter::canonical_lean_name_component(seg);
        if let Some(pos) = scope
            .iter()
            .rposition(|frame| crate::splitter::canonical_lean_name_component(&frame.name) == canon)
        {
            if pos + 1 != scope.len() {
                malformed = true;
            }
            scope.truncate(pos);
            context.truncate(pos + 1);
        } else {
            malformed = true;
            if scope.pop().is_some() && context.len() > 1 {
                context.pop();
            }
        }
    }
    malformed
}

fn mask_comments(src: &str) -> String {
    let mut out = src.as_bytes().to_vec();
    let mut i = 0usize;
    while i < src.len() {
        if let Some(span) = skip_lean_lexeme(src, i) {
            if span.is_comment {
                for byte in &mut out[i..span.end] {
                    if *byte != b'\n' {
                        *byte = b' ';
                    }
                }
            }
            i = span.end;
        } else {
            i += src[i..].chars().next().map_or(1, char::len_utf8);
        }
    }
    String::from_utf8(out).unwrap_or_else(|_| src.to_string())
}

fn skip_any(src: &str, byte_offsets: &[usize], idx: usize) -> Option<usize> {
    let byte = *byte_offsets.get(idx)?;
    let span = skip_lean_lexeme(src, byte)?;
    if !(span.is_comment || span.is_literal) {
        return None;
    }
    Some(byte_offsets.partition_point(|offset| *offset < span.end))
}

fn skip_any_lexeme(src: &str, byte_offsets: &[usize], idx: usize) -> Option<usize> {
    let byte = *byte_offsets.get(idx)?;
    let span = skip_lean_lexeme(src, byte)?;
    Some(byte_offsets.partition_point(|offset| *offset < span.end))
}

fn consume_in_command_prefix(
    src: &str,
    byte_offsets: &[usize],
    chars: &[char],
    start: usize,
) -> Option<(usize, Option<String>)> {
    const PREFIXES: &[&str] = &[
        "set_option",
        "open",
        "universe",
        "universes",
        "variable",
        "variables",
        "include",
        "omit",
        "attribute",
        "export",
        "deriving",
        "#guard_msgs",
        "#guard_panic",
        "#info_trees",
    ];
    let byte_start = *byte_offsets.get(start)?;
    let tail = &src[byte_start..];
    if let Some(rest) = tail
        .strip_prefix("#time")
        .or_else(|| tail.strip_prefix("#with_exporting"))
    {
        if rest.starts_with(char::is_whitespace) {
            let consumed = tail.len() - rest.len();
            return Some((
                byte_offsets.partition_point(|offset| *offset < byte_start + consumed),
                None,
            ));
        }
    }
    let kw = *PREFIXES.iter().find(|&&kw| {
        tail.strip_prefix(kw)
            .is_some_and(|rest| rest.starts_with(char::is_whitespace) || rest.starts_with('('))
    })?;
    let mut i = start + kw.chars().count();
    let mut depth = 0usize;
    while i < chars.len() {
        if let Some(end) = skip_any(src, byte_offsets, i) {
            i = end;
            continue;
        }
        match chars[i] {
            '(' | '[' | '{' | '⦃' => depth += 1,
            ')' | ']' | '}' | '⦄' => depth = depth.saturating_sub(1),
            '\n' | ';' if depth == 0 => return None,
            'i' if depth == 0
                && i + 1 < chars.len()
                && chars[i + 1] == 'n'
                && i > 0
                && chars[i - 1].is_whitespace()
                && (i + 2 >= chars.len() || chars[i + 2].is_whitespace()) =>
            {
                let after = i + 2;
                let assumption =
                    matches!(kw, "variable" | "variables" | "include" | "omit").then(|| {
                        let raw: String = chars[start..after].iter().collect();
                        normalize_ws(&raw)
                    });
                return Some((after, assumption));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn dotted_name(
    src: &str,
    byte_offsets: &[usize],
    chars: &[char],
    mut pos: usize,
    n: usize,
) -> (String, usize) {
    while pos < n && chars[pos].is_whitespace() && chars[pos] != '\n' {
        pos += 1;
    }
    let start = pos;
    while pos < n {
        if chars[pos] == '«' {
            if let Some(end) = skip_any_lexeme(src, byte_offsets, pos) {
                pos = end;
                continue;
            }
            break;
        }
        if is_ident_continue(chars[pos]) || chars[pos] == '.' {
            pos += 1;
        } else {
            break;
        }
    }
    (
        chars[start..pos]
            .iter()
            .collect::<String>()
            .trim_end_matches('.')
            .to_string(),
        pos,
    )
}

fn matching_close(
    src: &str,
    byte_offsets: &[usize],
    chars: &[char],
    open_at: usize,
    open: char,
    close: char,
) -> Option<usize> {
    let mut depth = 0usize;
    let mut i = open_at;
    while i < chars.len() {
        if let Some(end) = skip_any(src, byte_offsets, i) {
            i = end;
            continue;
        }
        if chars[i] == open {
            depth += 1;
        } else if chars[i] == close {
            depth -= 1;
            if depth == 0 {
                return Some(i + 1);
            }
        }
        i += 1;
    }
    None
}

fn normalize_ws(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn instance_class_expr(text: &str) -> &str {
    split_top_level_colon(text).map_or_else(|| text.trim(), |(_, ty)| ty.trim())
}

fn instance_head_and_arg(text: &str) -> Option<(&str, &str)> {
    let class_expr = instance_class_expr(text);
    let mut parts = class_expr.split_whitespace();
    let head_raw = parts.next()?;
    let arg = parts.next()?;
    if parts.next().is_some() {
        return None;
    }
    let head = head_raw.rsplit('.').next()?;
    let valid_arg =
        arg.chars().next().is_some_and(is_ident_start) && arg.chars().all(is_ident_continue);
    valid_arg.then_some((head, arg))
}

fn has_matching_instance(all_binders: &[String], want_head: &str, want_arg: &str) -> bool {
    all_binders.iter().any(|other| {
        instance_head_and_arg(other).is_some_and(|(head, arg)| head == want_head && arg == want_arg)
    })
}

fn standard_instance(text: &str, all_binders: &[String], type_params: &BTreeSet<String>) -> bool {
    let class_expr = instance_class_expr(text);
    let head = class_expr
        .split_whitespace()
        .next()
        .unwrap_or("")
        .rsplit('.')
        .next()
        .unwrap_or("");
    if matches!(head, "DecidablePred" | "DecidableRel") {
        return class_expr.split_whitespace().nth(1).is_some();
    }
    let Some((head, arg)) = instance_head_and_arg(text) else {
        return false;
    };
    if TOTAL_INSTANCE_HEADS.contains(&head) {
        return true;
    }
    let allowed_lawful_target = PRIMITIVE_LAWFUL_TYPES.contains(&arg) || type_params.contains(arg);
    if !allowed_lawful_target {
        return false;
    }
    match head {
        "LawfulBEq" | "EquivBEq" => {
            PRIMITIVE_LAWFUL_TYPES.contains(&arg) || has_matching_instance(all_binders, "BEq", arg)
        }
        "LawfulHashable" => {
            PRIMITIVE_LAWFUL_TYPES.contains(&arg)
                || (has_matching_instance(all_binders, "BEq", arg)
                    && has_matching_instance(all_binders, "Hashable", arg))
        }
        _ => false,
    }
}

fn visibility_of(
    name: &str,
    public_names: &BTreeSet<String>,
    known: bool,
    is_module: bool,
    extra: Option<&DeclExtra>,
) -> &'static str {
    if !known {
        return "unresolved";
    }
    if extra.is_some_and(|row| row.is_private) {
        return "private";
    }
    if !is_module {
        return "public";
    }
    if extra.is_some_and(|row| row.explicit_public) {
        return "public";
    }
    if public_names.contains(&canonicalize_lean_name(name)) {
        "public"
    } else {
        "private"
    }
}

struct FileCardCtx<'a> {
    path: &'a Path,
    local_defs: &'a [(String, Vec<String>, String, String)],
    hygiene: &'a crate::splitter::HygieneReport,
    audit: &'a Value,
}

fn card_for(
    ctx: &FileCardCtx<'_>,
    decl: &ExtractedDecl,
    effective_name: &str,
    visibility: &str,
    extra: Option<&DeclExtra>,
    detail: Option<&Value>,
) -> Value {
    let mut param_binders = Vec::new();
    let mut hypothesis_text = Vec::new();
    let mut type_params = BTreeSet::new();
    for (vars, ty) in &decl.binders {
        let ty_trimmed = ty.trim();
        if ty_trimmed == "Type"
            || ty_trimmed.starts_with("Type ")
            || ty_trimmed.starts_with("Sort ")
        {
            for var in vars {
                type_params.insert(var.clone());
            }
        }
        if is_known_binder_value_type(ty) {
            param_binders.push(json!({"vars": vars, "type": ty}));
        } else {
            let names = vars.join(" ");
            hypothesis_text.push(format!("({names} : {ty})"));
        }
    }
    let parts = split_top_level_implications(&decl.prop_str);
    let conclusion = if parts.len() <= 1 {
        parts.first().cloned().unwrap_or_default()
    } else {
        hypothesis_text.extend_from_slice(&parts[..parts.len() - 1]);
        parts.last().cloned().unwrap_or_default()
    };
    let instance_binders = extra
        .map(|row| row.instance_binders.clone())
        .unwrap_or_default();
    let context_assumptions = extra
        .map(|row| row.context_assumptions.clone())
        .unwrap_or_default();
    let mut extraction_warnings = Vec::new();
    let nonstandard: Vec<&str> = instance_binders
        .iter()
        .filter(|binder| !standard_instance(binder, &instance_binders, &type_params))
        .map(String::as_str)
        .collect();
    if !nonstandard.is_empty() {
        extraction_warnings.push(format!(
            "nonstandard instance binders are not evaluated by the syntactic audit: {}",
            nonstandard.join(", ")
        ));
    }
    if !context_assumptions.is_empty() {
        extraction_warnings.push(
            "section variable/include/omit assumptions are not bound by the syntactic audit"
                .to_string(),
        );
    }
    if extra.is_none() || extra.is_some_and(|row| row.saw_unparsed_binder) {
        extraction_warnings.push(
            "declaration modifiers, attributes, or binders were not fully parsed".to_string(),
        );
    }
    let extraction_complete = extraction_warnings.is_empty();
    let hypothesis_count = hypothesis_text.len();
    let hypotheses: Vec<Value> = hypothesis_text
        .iter()
        .enumerate()
        .map(|(idx, text)| json!({"id": format!("H_{}", idx + 1), "text": text}))
        .collect();
    let mut full_stmt = String::new();
    for binder in &instance_binders {
        full_stmt.push('[');
        full_stmt.push_str(binder);
        full_stmt.push_str("] ");
    }
    for assumption in &context_assumptions {
        full_stmt.push_str(assumption);
        full_stmt.push(' ');
    }
    for (_, ty) in &decl.binders {
        full_stmt.push_str(ty);
        full_stmt.push(' ');
    }
    full_stmt.push_str(&decl.prop_str);
    let (local_refs, external_refs) = statement_refs(&full_stmt, ctx.local_defs);
    let raw_verdict = match detail {
        Some(row) if row.get("vacuous").and_then(Value::as_bool) == Some(true) => "VACUOUS",
        Some(row) if row.get("trivial").and_then(Value::as_bool) == Some(true) => "TRIVIAL",
        Some(row) if row.get("tight").and_then(Value::as_bool) == Some(true) => "TIGHT",
        _ => "UNCHECKED",
    };
    let verdict = if raw_verdict == "TIGHT" && !extraction_complete {
        "UNCHECKED_ASSUMPTIONS"
    } else {
        raw_verdict
    };
    json!({
        "file": ctx.path.display().to_string(),
        "decl": effective_name,
        "visibility": visibility,
        "contract": {
            "binders": param_binders,
            "instance_binders": instance_binders,
            "context_assumptions": context_assumptions,
            "extraction_complete": extraction_complete,
            "extraction_warnings": extraction_warnings,
            "hypotheses": hypotheses,
            "conclusion": {"id": "C", "text": conclusion},
            "statement_chars": full_stmt.trim().chars().count(),
            "hypothesis_count": hypothesis_count,
        },
        "referenced_definitions": {
            "label": "syntactic_statement_refs",
            "note": "unelaborated identifier mentions in the statement text; not a kernel dependency cone",
            "local_defs": local_refs,
            "external_qualified": external_refs,
        },
        "hygiene": {
            "source_flags": hygiene_flags(ctx.hygiene),
            "flagged_lines": ctx.hygiene.flagged_items.clone(),
            "shadowed_constants": ctx.audit.get("shadowed_constants").cloned().unwrap_or(json!([])),
            "forbidden_scope": ctx.audit.get("forbidden_scope_decls").cloned().unwrap_or(json!([])),
            "stub_defs": detail
                .and_then(|row| row.get("stub_defs"))
                .cloned()
                .or_else(|| ctx.audit.get("stub_defs").cloned())
                .unwrap_or(json!([])),
        },
        "verdict": verdict,
        "pos_witness": detail.and_then(|row| row.get("pos_witness")).cloned().unwrap_or(Value::Null),
        "neg_witness": detail.and_then(|row| row.get("neg_witness")).cloned().unwrap_or(Value::Null),
        "droppable_hypotheses": detail
            .and_then(|row| row.get("droppable_hypotheses"))
            .cloned()
            .unwrap_or(json!([])),
        "assessment": detail.and_then(|row| row.get("assessment")).cloned().unwrap_or(Value::Null),
    })
}

fn statement_refs(
    prop: &str,
    local_defs: &[(String, Vec<String>, String, String)],
) -> (Vec<Value>, Vec<String>) {
    let mut local = Vec::new();
    let mut seen = BTreeSet::new();
    for (name, params, body, type_deps) in local_defs {
        let short = name.rsplit('.').next().unwrap_or(name);
        if (ident_mentioned(prop, name) || ident_mentioned(prop, short))
            && seen.insert(name.clone())
        {
            local.push(json!({
                "name": name,
                "params": params,
                "body_preview": one_line(body, 96),
                "type_deps": type_deps,
            }));
        }
    }
    let local_names: BTreeSet<String> = local
        .iter()
        .filter_map(|row| row.get("name").and_then(Value::as_str).map(str::to_string))
        .collect();
    let mut external = BTreeSet::new();
    let chars: Vec<char> = prop.chars().collect();
    let mut idx = 0usize;
    while idx < chars.len() {
        if is_ident_start(chars[idx]) {
            let start = idx;
            idx += 1;
            while idx < chars.len() && (is_ident_continue(chars[idx]) || chars[idx] == '.') {
                idx += 1;
            }
            let raw: String = chars[start..idx].iter().collect();
            let raw = raw.trim_end_matches('.').to_string();
            let is_local = local_names
                .iter()
                .any(|name| name == &raw || name.ends_with(&format!(".{raw}")));
            if raw.contains('.') && !is_local {
                external.insert(raw);
            }
        } else {
            idx += 1;
        }
    }
    (local, external.into_iter().collect())
}

fn ident_mentioned(text: &str, ident: &str) -> bool {
    if ident.is_empty() {
        return false;
    }
    let chars: Vec<char> = text.chars().collect();
    let needle: Vec<char> = ident.chars().collect();
    let mut idx = 0usize;
    while idx + needle.len() <= chars.len() {
        if chars[idx..idx + needle.len()] == needle[..] {
            let before_ok = idx == 0 || !is_ident_continue(chars[idx - 1]);
            let after = idx + needle.len();
            let after_ok =
                after >= chars.len() || !(is_ident_continue(chars[after]) || chars[after] == '.');
            if before_ok && after_ok {
                return true;
            }
        }
        idx += 1;
    }
    false
}

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

fn is_lean_subscript_alnum(c: char) -> bool {
    let v = c as u32;
    (0x2080..=0x2089).contains(&v)
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
        || v == 0x2c7c
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || is_lean_letter_like(c)
}

fn is_ident_continue(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(c, '_' | '\'' | '!' | '?')
        || is_lean_letter_like(c)
        || is_lean_subscript_alnum(c)
}

fn one_line(body: &str, max_chars: usize) -> String {
    let flat = body.split_whitespace().collect::<Vec<_>>().join(" ");
    if flat.chars().count() <= max_chars {
        flat
    } else {
        let truncated: String = flat.chars().take(max_chars).collect();
        format!("{truncated}…")
    }
}

fn hygiene_flags(hygiene: &crate::splitter::HygieneReport) -> Vec<String> {
    let mut flags = Vec::new();
    if hygiene.has_sorry {
        flags.push("sorry".to_string());
    }
    if hygiene.has_axiom {
        flags.push("axiom".to_string());
    }
    if hygiene.has_native_decide {
        flags.push("native_decide_or_ofReduceBool".to_string());
    }
    if hygiene.has_trust_compiler {
        flags.push("trustCompiler".to_string());
    }
    if hygiene.has_unsafe {
        flags.push("unsafe".to_string());
    }
    if hygiene.has_extern_or_implemented_by {
        flags.push("extern_or_implemented_by".to_string());
    }
    if hygiene.has_impure_metaprograms {
        flags.push("impure_metaprogram".to_string());
    }
    if hygiene.has_checking_weakening {
        flags.push("checking_weakening".to_string());
    }
    flags
}

fn render_human(report: &Value) -> String {
    let mut out = String::new();
    let summary = &report["summary"];
    out.push_str(&format!(
        "spec-card  tier=source_syntactic  ok={}  cards={}  policy={}  {:.3} ms\n",
        report.get("ok").and_then(Value::as_bool).unwrap_or(false),
        summary.get("cards").and_then(Value::as_u64).unwrap_or(0),
        summary
            .get("policy")
            .and_then(Value::as_str)
            .unwrap_or("default"),
        summary
            .get("elapsed_ms")
            .and_then(Value::as_f64)
            .unwrap_or(0.0),
    ));
    out.push_str(
        "unchecked: transitive imported axioms; semantic domain intent; FFI/environment; proof-term completeness\n",
    );
    let Some(cards) = report.get("cards").and_then(Value::as_array) else {
        return out;
    };
    if cards.is_empty() {
        out.push_str("(no declarations)\n");
        return out;
    }
    for card in cards {
        out.push_str(&format!(
            "\n{}  {}  {}\n  file  {}\n",
            field(card, "verdict"),
            field(card, "visibility"),
            field(card, "decl"),
            field(card, "file")
        ));
        let contract = &card["contract"];
        if let Some(binders) = contract.get("binders").and_then(Value::as_array) {
            for binder in binders {
                let vars = binder
                    .get("vars")
                    .and_then(Value::as_array)
                    .map(|values| {
                        values
                            .iter()
                            .filter_map(Value::as_str)
                            .collect::<Vec<_>>()
                            .join(" ")
                    })
                    .unwrap_or_default();
                let ty = binder.get("type").and_then(Value::as_str).unwrap_or("");
                out.push_str(&format!("  binder  {vars} : {ty}\n"));
            }
        }
        if let Some(instances) = contract.get("instance_binders").and_then(Value::as_array) {
            for instance in instances {
                if let Some(text) = instance.as_str() {
                    out.push_str(&format!("  inst  [{text}]\n"));
                }
            }
        }
        if let Some(assumptions) = contract
            .get("context_assumptions")
            .and_then(Value::as_array)
        {
            for assumption in assumptions {
                if let Some(text) = assumption.as_str() {
                    out.push_str(&format!("  context  {text}\n"));
                }
            }
        }
        if let Some(warnings) = contract
            .get("extraction_warnings")
            .and_then(Value::as_array)
        {
            for warning in warnings {
                if let Some(text) = warning.as_str() {
                    out.push_str(&format!("  extraction  {text}\n"));
                }
            }
        }
        if let Some(hypotheses) = contract.get("hypotheses").and_then(Value::as_array) {
            for hypothesis in hypotheses {
                out.push_str(&format!(
                    "  {}  {}\n",
                    hypothesis.get("id").and_then(Value::as_str).unwrap_or("H"),
                    hypothesis.get("text").and_then(Value::as_str).unwrap_or("")
                ));
            }
        }
        let conclusion = contract
            .pointer("/conclusion/text")
            .and_then(Value::as_str)
            .unwrap_or("");
        out.push_str(&format!("  C  {conclusion}\n"));
        out.push_str(&format!(
            "  size  hypotheses={}  chars={}\n",
            contract
                .get("hypothesis_count")
                .and_then(Value::as_u64)
                .unwrap_or(0),
            contract
                .get("statement_chars")
                .and_then(Value::as_u64)
                .unwrap_or(0)
        ));
        out.push_str("  refs  syntactic_statement_refs (unelaborated)\n");
        if let Some(locals) = card
            .pointer("/referenced_definitions/local_defs")
            .and_then(Value::as_array)
        {
            for defn in locals {
                out.push_str(&format!(
                    "    local  {}  := {}\n",
                    defn.get("name").and_then(Value::as_str).unwrap_or(""),
                    defn.get("body_preview")
                        .and_then(Value::as_str)
                        .unwrap_or("")
                ));
            }
        }
        if let Some(external) = card
            .pointer("/referenced_definitions/external_qualified")
            .and_then(Value::as_array)
        {
            let names = external
                .iter()
                .filter_map(Value::as_str)
                .collect::<Vec<_>>();
            if !names.is_empty() {
                out.push_str(&format!("    external  {}\n", names.join(", ")));
            }
        }
        let source_flags = card
            .pointer("/hygiene/source_flags")
            .and_then(Value::as_array)
            .map(|flags| {
                flags
                    .iter()
                    .filter_map(Value::as_str)
                    .collect::<Vec<_>>()
                    .join(", ")
            })
            .unwrap_or_default();
        if !source_flags.is_empty() {
            out.push_str(&format!("  hygiene  {source_flags}\n"));
        }
        for key in ["shadowed_constants", "forbidden_scope", "stub_defs"] {
            if let Some(values) = card
                .pointer(&format!("/hygiene/{key}"))
                .and_then(Value::as_array)
            {
                if !values.is_empty() {
                    out.push_str(&format!(
                        "  {key}  {}\n",
                        clip(&Value::Array(values.clone()).to_string(), 160)
                    ));
                }
            }
        }
        out.push_str(&format!(
            "  witnesses  pos={}  neg={}\n",
            clip(&compact(card.get("pos_witness")), 120),
            clip(&compact(card.get("neg_witness")), 120)
        ));
        if let Some(drops) = card.get("droppable_hypotheses").and_then(Value::as_array) {
            if !drops.is_empty() {
                out.push_str(&format!(
                    "  droppable  {}\n",
                    clip(&Value::Array(drops.clone()).to_string(), 160)
                ));
            }
        }
    }
    out
}

fn field(value: &Value, key: &str) -> String {
    value
        .get(key)
        .and_then(Value::as_str)
        .unwrap_or("?")
        .to_string()
}

fn compact(value: Option<&Value>) -> String {
    match value {
        None | Some(Value::Null) => "-".to_string(),
        Some(other) => other.to_string(),
    }
}

fn clip(text: &str, max_chars: usize) -> String {
    if text.chars().count() <= max_chars {
        text.to_string()
    } else {
        let truncated: String = text.chars().take(max_chars.saturating_sub(3)).collect();
        format!("{truncated}...")
    }
}
