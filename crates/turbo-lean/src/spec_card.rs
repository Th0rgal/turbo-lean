use anyhow::{bail, Context, Result};
use serde_json::{json, Value};
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use super::audit_spec::{
    audit_spec_file_or_source_with_policy, extract_all_lean_theorems, extract_local_def_unfoldings,
    AuditSpecPolicyConfig,
};
use super::{
    is_known_binder_value_type, split_top_level_implications, strip_lean_comments, ExtractedDecl,
};
use crate::splitter::{
    audit_hygiene, canonicalize_lean_name, extract_public_signature, qualified_decl_name,
    skip_lean_lexeme, ScopeFrame, ScopeKind,
};

const UNCHECKED: &[&str] = &[
    "transitive imported axioms (statement text is not elaborated and imports are not walked)",
    "semantic domain intent, including whether hypotheses are logically independent",
    "unmodeled FFI, native, and environment boundaries",
    "proof-term completeness beyond source tokens (sorry, admit, axiom, native_decide, extern)",
    "instance binders and section variable/include context are syntactic only; nonstandard ones are not evaluated",
];

const STANDARD_INSTANCE_HEADS: &[&str] = &[
    "BEq",
    "Decidable",
    "DecidableEq",
    "DecidablePred",
    "DecidableRel",
    "EquivBEq",
    "Hashable",
    "Inhabited",
    "LE",
    "LT",
    "LawfulBEq",
    "LawfulHashable",
    "Nonempty",
    "Ord",
    "Repr",
    "ToString",
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
    let mut all_audits_ok = true;
    let mut any_audit_error = false;
    let mut policy_name = policy_override.unwrap_or("default").to_string();
    for (idx, (path, src)) in sources.iter().enumerate() {
        let policy = AuditSpecPolicyConfig::load_for_target(
            path,
            policy_override,
            config_override,
            &[],
            &[],
        );
        if idx == 0 {
            policy_name = policy.policy.clone();
        }
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
        let extras = scan_decl_extras(src);
        for decl in extract_all_lean_theorems(src, decl_filter) {
            matched += 1;
            let visibility = visibility_of(&decl.name, &public_names, visibility_known);
            if public_only && visibility != "public" {
                hidden_private += 1;
                continue;
            }
            let detail = details
                .iter()
                .find(|row| row.get("decl").and_then(Value::as_str) == Some(decl.name.as_str()));
            let extra = extras.iter().find(|row| {
                canonicalize_lean_name(&row.name) == canonicalize_lean_name(&decl.name)
            });
            let ctx = FileCardCtx {
                path,
                local_defs: &local_defs,
                hygiene: &hygiene,
                audit: &audit,
            };
            cards.push(card_for(&ctx, &decl, visibility, extra, detail));
        }
    }
    let elapsed_ms = (started.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
    let filter_miss = decl_filter.is_some() && matched == 0;
    let public_miss = public_only && matched > 0 && cards.is_empty();
    let incomplete = cards.iter().any(|card| {
        card.pointer("/contract/extraction_complete")
            .and_then(Value::as_bool)
            == Some(false)
    });
    let ok = !any_audit_error
        && all_audits_ok
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
        let mut sources: Vec<(PathBuf, String)> = crate::lake_build::collect_lean_files(file)
            .into_iter()
            .filter_map(|path| fs::read_to_string(&path).ok().map(|src| (path, src)))
            .collect();
        sources.sort_by(|left, right| left.0.cmp(&right.0));
        if sources.is_empty() {
            bail!("No readable Lean files found in {}", file.display());
        }
        return Ok(sources);
    }
    let src =
        fs::read_to_string(file).with_context(|| format!("Failed to read {}", file.display()))?;
    Ok(vec![(file.to_path_buf(), src)])
}

struct DeclExtra {
    name: String,
    instance_binders: Vec<String>,
    context_assumptions: Vec<String>,
}

fn scan_decl_extras(src: &str) -> Vec<DeclExtra> {
    let masked = mask_comments(src);
    let chars: Vec<char> = masked.chars().collect();
    let n = chars.len();
    let mut i = 0usize;
    let mut scope: Vec<ScopeFrame> = Vec::new();
    let mut context: Vec<Vec<String>> = vec![Vec::new()];
    let mut out = Vec::new();
    while i < n {
        if let Some(end) = skip_any(&masked, i) {
            i = end;
            continue;
        }
        if !is_ident_start(chars[i]) || !line_command_start(&chars, i) {
            i += 1;
            continue;
        }
        let start = i;
        while i < n && is_ident_continue(chars[i]) {
            i += 1;
        }
        let word: String = chars[start..i].iter().collect();
        match word.as_str() {
            "namespace" if i < n && chars[i].is_whitespace() => {
                let (name, next) = dotted_name(&chars, i, n);
                i = next;
                for seg in crate::splitter::split_lean_name_components(&name) {
                    scope.push(ScopeFrame {
                        kind: ScopeKind::Namespace,
                        name: seg.to_string(),
                        open_span_idx: 0,
                    });
                }
                context.push(Vec::new());
            }
            "section" => {
                let (name, next) = if i < n && chars[i].is_whitespace() {
                    dotted_name(&chars, i, n)
                } else {
                    (String::new(), i)
                };
                i = next;
                let segs = if name.is_empty() {
                    vec![String::new()]
                } else {
                    crate::splitter::split_lean_name_components(&name)
                        .into_iter()
                        .map(str::to_string)
                        .collect()
                };
                for seg in segs {
                    scope.push(ScopeFrame {
                        kind: ScopeKind::Section,
                        name: seg,
                        open_span_idx: 0,
                    });
                    context.push(Vec::new());
                }
            }
            "end" => {
                let (name, next) = if i < n && chars[i].is_whitespace() {
                    dotted_name(&chars, i, n)
                } else {
                    (String::new(), i)
                };
                i = next;
                let pops = if name.is_empty() {
                    1
                } else {
                    crate::splitter::split_lean_name_components(&name).len()
                };
                for _ in 0..pops {
                    scope.pop();
                    if context.len() > 1 {
                        context.pop();
                    }
                }
            }
            "variable" | "variables" | "include" | "omit" => {
                let body_start = i;
                while i < n && chars[i] != '\n' {
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
                let (raw_name, next) = dotted_name(&chars, i, n);
                if raw_name.is_empty() {
                    continue;
                }
                i = next;
                let mut binders = Vec::new();
                while i < n {
                    while i < n && chars[i].is_whitespace() {
                        i += 1;
                    }
                    if i >= n {
                        break;
                    }
                    if let Some(end) = skip_any(&masked, i) {
                        i = end;
                        continue;
                    }
                    if chars[i] == ':' && (i + 1 >= n || chars[i + 1] != '=') {
                        break;
                    }
                    if chars[i] == ':' && i + 1 < n && chars[i + 1] == '=' {
                        break;
                    }
                    if chars[i] == '[' {
                        let open_at = i;
                        if let Some(end) = matching_close(&chars, i, '[', ']') {
                            let inner: String = chars[open_at + 1..end - 1].iter().collect();
                            binders.push(normalize_ws(&inner));
                            i = end;
                        } else {
                            break;
                        }
                    } else if chars[i] == '(' || chars[i] == '{' {
                        let (open, close) = if chars[i] == '(' {
                            ('(', ')')
                        } else {
                            ('{', '}')
                        };
                        if let Some(end) = matching_close(&chars, i, open, close) {
                            i = end;
                        } else {
                            break;
                        }
                    } else {
                        i += 1;
                    }
                }
                let assumptions = context.iter().flatten().cloned().collect();
                out.push(DeclExtra {
                    name: qualified_decl_name(&raw_name, &scope),
                    instance_binders: binders,
                    context_assumptions: assumptions,
                });
            }
            _ => {}
        }
    }
    out
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

fn skip_any(src: &str, idx: usize) -> Option<usize> {
    let byte = byte_to_char_inverse(src, idx);
    let span = skip_lean_lexeme(src, byte)?;
    if !(span.is_comment || span.is_literal) {
        return None;
    }
    Some(byte_to_char(src, span.end))
}

fn byte_to_char_inverse(src: &str, char_idx: usize) -> usize {
    src.chars().take(char_idx).map(char::len_utf8).sum()
}

fn byte_to_char(src: &str, byte: usize) -> usize {
    src[..byte.min(src.len())].chars().count()
}

fn line_command_start(chars: &[char], word_idx: usize) -> bool {
    let mut pos = word_idx;
    while pos > 0 && (chars[pos - 1] == ' ' || chars[pos - 1] == '\t') {
        pos -= 1;
    }
    pos == 0 || chars[pos - 1] == '\n' || chars[pos - 1] == ';'
}

fn dotted_name(chars: &[char], mut pos: usize, n: usize) -> (String, usize) {
    while pos < n && chars[pos].is_whitespace() && chars[pos] != '\n' {
        pos += 1;
    }
    let start = pos;
    while pos < n && (is_ident_continue(chars[pos]) || chars[pos] == '.') {
        pos += 1;
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

fn matching_close(chars: &[char], open_at: usize, open: char, close: char) -> Option<usize> {
    let mut depth = 0usize;
    let mut i = open_at;
    while i < chars.len() {
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

fn standard_instance(text: &str) -> bool {
    let head = text
        .split_whitespace()
        .next()
        .unwrap_or("")
        .rsplit('.')
        .next()
        .unwrap_or("");
    STANDARD_INSTANCE_HEADS.contains(&head)
}

fn visibility_of(name: &str, public_names: &BTreeSet<String>, known: bool) -> &'static str {
    if !known {
        return "unresolved";
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
    visibility: &str,
    extra: Option<&DeclExtra>,
    detail: Option<&Value>,
) -> Value {
    let mut param_binders = Vec::new();
    let mut hypothesis_text = Vec::new();
    for (vars, ty) in &decl.binders {
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
        .filter(|binder| !standard_instance(binder))
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
        "decl": decl.name,
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
            "stub_defs": ctx.audit.get("stub_defs").cloned().unwrap_or(json!([])),
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

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_ident_continue(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\''
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
