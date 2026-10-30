//! Zero-Trust Specification Auditor (`audit-spec` v2.1) & Anti-Reward-Hacking Gate (`turbo-lean.toml`).
//!
//! Extracted from `gpu_fastcheck.rs` to isolate multi-hop vacuity/tightness checking,
//! definitional-lowering tautology detection, stub `def` rejection, and Blake3 per-file caching.

use super::*;

pub(super) fn split_at_first_top_level_assign(s: &str) -> Option<(&str, &str)> {
    // Case 2: multi-character ASCII Unicode-aware scan (needed when non-ASCII operators like `×`, `→`, `≈`, `≤` appear before `:=`)
    let chars: Vec<(usize, char)> = s.char_indices().collect();
    let mut depth = 0i32;
    let mut in_string = false;
    let mut i = 0usize;
    while i < chars.len() {
        let (byte_pos, c) = chars[i];
        if in_string {
            if c == '\\' {
                i += 2;
                continue;
            }
            if c == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        match c {
            '"' => in_string = true,
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth = (depth - 1).max(0),
            ':' if depth == 0 && i + 1 < chars.len() && chars[i + 1].1 == '=' => {
                let after_eq = chars[i + 1].0 + chars[i + 1].1.len_utf8();
                return Some((&s[..byte_pos], &s[after_eq..]));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum LeanScopeKind {
    Namespace,
    Section,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct LeanScopeFrame {
    pub kind: LeanScopeKind,
    pub closing_name: Option<String>,
    pub namespace_segment: Option<String>,
}

pub(super) fn push_lean_namespace(stack: &mut Vec<LeanScopeFrame>, ns: &str) {
    let segs: Vec<&str> = ns.split('.').map(str::trim).filter(|s| !s.is_empty()).collect();
    if !segs.is_empty() {
        let joined = segs.join(".");
        stack.push(LeanScopeFrame {
            kind: LeanScopeKind::Namespace,
            closing_name: Some(joined.clone()),
            namespace_segment: Some(joined),
        });
    }
}

pub(super) fn push_lean_section(stack: &mut Vec<LeanScopeFrame>, sec_name: Option<&str>) {
    let trimmed = sec_name.unwrap_or("").trim();
    if trimmed.is_empty() {
        stack.push(LeanScopeFrame {
            kind: LeanScopeKind::Section,
            closing_name: None,
            namespace_segment: None,
        });
    } else {
        let segs: Vec<&str> = trimmed.split('.').map(str::trim).filter(|s| !s.is_empty()).collect();
        if !segs.is_empty() {
            stack.push(LeanScopeFrame {
                kind: LeanScopeKind::Section,
                closing_name: Some(segs.join(".")),
                namespace_segment: None,
            });
        }
    }
}

pub(super) fn pop_lean_scope(stack: &mut Vec<LeanScopeFrame>, end_name: &str) {
    let trimmed = end_name.trim();
    if trimmed.is_empty() {
        let _ = stack.pop();
        return;
    }
    let clean_target = trimmed
        .split('.')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>()
        .join(".");
    if let Some(pos) = stack
        .iter()
        .rposition(|frame| frame.closing_name.as_deref() == Some(clean_target.as_str()))
    {
        stack.truncate(pos);
        return;
    }
    let segs: Vec<&str> = clean_target.split('.').filter(|s| !s.is_empty()).collect();
    for seg in segs.into_iter().rev() {
        if let Some(pos) = stack
            .iter()
            .rposition(|frame| frame.closing_name.as_deref() == Some(seg))
        {
            stack.truncate(pos);
        } else if let Some(pos) = stack.iter().rposition(|frame| {
            frame
                .closing_name
                .as_deref()
                .is_some_and(|cn| cn.ends_with(&format!(".{}", seg)))
        }) {
            stack.truncate(pos + 1);
            if let Some(top) = stack.last_mut() {
                if let Some(cn) = top.closing_name.clone() {
                    if let Some(prefix) = cn.strip_suffix(&format!(".{}", seg)) {
                        top.closing_name = Some(prefix.to_string());
                        if top.namespace_segment.is_some() {
                            top.namespace_segment = Some(prefix.to_string());
                        }
                    }
                }
            }
        } else {
            let _ = stack.pop();
        }
    }
}

pub(super) fn format_lean_scope_namespace(stack: &[LeanScopeFrame]) -> String {
    stack
        .iter()
        .filter_map(|f| f.namespace_segment.as_deref())
        .collect::<Vec<_>>()
        .join(".")
}

/// Extract 1-level local `def`/`abbrev` definitions (`name`, `params`, `body`) from clean Lean source
/// so `audit-spec` can delta-unfold predicate wrappers (e.g., `def Impossible (x : Nat) : Prop := x < 0`),
/// multi-line lowering definitions (`def evalLCNF ... :=\n  evalCode ...`), and tautological conclusion wrappers.
pub(super) fn extract_local_def_unfoldings(clean_src: &str) -> Vec<(String, Vec<String>, String)> {
    extract_local_def_unfoldings_with_vis(clean_src, true)
}

pub(super) fn extract_local_def_unfoldings_with_vis(
    clean_src: &str,
    include_private: bool,
) -> Vec<(String, Vec<String>, String)> {
    let mut defs = Vec::new();
    let lines: Vec<&str> = clean_src.lines().collect();
    let mut scope_stack: Vec<LeanScopeFrame> = Vec::new();
    let mut idx = 0usize;

    while idx < lines.len() {
        let mut line = lines[idx].trim();
        if line == "section" || line.starts_with("section ") {
            let sec_name = line
                .strip_prefix("section")
                .unwrap_or("")
                .split_whitespace()
                .next();
            push_lean_section(&mut scope_stack, sec_name);
            idx += 1;
            continue;
        }
        if let Some(ns) = line.strip_prefix("namespace ") {
            let ns_name = ns.split_whitespace().next().unwrap_or("").trim();
            if !ns_name.is_empty() {
                push_lean_namespace(&mut scope_stack, ns_name);
            }
            idx += 1;
            continue;
        }
        if line == "end" || line.starts_with("end ") {
            let end_ns = line.strip_prefix("end").unwrap_or("").trim();
            pop_lean_scope(&mut scope_stack, end_ns);
            idx += 1;
            continue;
        }
        let current_ns = format_lean_scope_namespace(&scope_stack);

        let mut is_private = false;
        loop {
            let mut stripped = false;
            if let Some(rest) = line.strip_prefix("private ") {
                is_private = true;
                line = rest.trim();
                stripped = true;
            }
            if line.starts_with("@[") {
                if let Some(rb) = line.find(']') {
                    line = line[rb + 1..].trim();
                    stripped = true;
                }
            }
            for pfx in ["protected ", "noncomputable ", "partial "] {
                if let Some(rest) = line.strip_prefix(pfx) {
                    line = rest.trim();
                    stripped = true;
                }
            }
            if !stripped {
                break;
            }
        }
        let rest_kw = if let Some(r) = line.strip_prefix("def ") {
            Some(r.trim())
        } else if let Some(r) = line.strip_prefix("abbrev ") {
            Some(r.trim())
        } else {
            None
        };
        let Some(first_rest) = rest_kw else {
            idx += 1;
            continue;
        };

        // Gather continuation lines belonging to this `def`/`abbrev` up to the next top-level command
        let first_line_trimmed_end = lines[idx].trim_end();
        let first_rest_col = first_line_trimmed_end
            .chars()
            .count()
            .saturating_sub(first_rest.chars().count());
        let mut combined = first_rest.to_string();
        idx += 1;
        while idx < lines.len() {
            let next_raw = lines[idx];
            let next_trim = next_raw.trim();
            if next_trim.is_empty() {
                idx += 1;
                break;
            }
            if next_trim == "end"
                || next_trim == "section"
                || [
                    "def ",
                    "abbrev ",
                    "theorem ",
                    "lemma ",
                    "structure ",
                    "inductive ",
                    "namespace ",
                    "end ",
                    "section ",
                    "open ",
                    "import ",
                    "infix ",
                    "infixl",
                    "infixr",
                    "prefix ",
                    "postfix ",
                    "notation ",
                    "private ",
                    "protected ",
                    "@[",
                    "noncomputable ",
                    "#",
                ]
                .iter()
                .any(|kw| next_trim.starts_with(kw))
            {
                break;
            }
            combined.push('\n');
            combined.push_str(next_raw);
            idx += 1;
        }
        if is_private && !include_private {
            continue;
        }

        let Some((sig, body_raw)) = split_at_first_top_level_assign(&combined) else {
            continue;
        };
        if replace_ident_boundary(sig, "where", "__WHERE__") != sig {
            continue;
        }
        let body_trimmed_check = body_raw.trim();
        if body_trimmed_check.is_empty()
            || body_trimmed_check.starts_with("by ")
            || body_trimmed_check.starts_with("do")
            || body_trimmed_check.starts_with("Id.run")
            || body_trimmed_check.ends_with(" do")
        {
            continue;
        }
        let assign_end_byte = combined.len().saturating_sub(body_raw.len());
        let body_col0 = if let Some(nl_pos) = combined[..assign_end_byte].rfind('\n') {
            combined[nl_pos + 1..assign_end_byte].chars().count()
        } else {
            first_rest_col + combined[..assign_end_byte].chars().count()
        };
        let padded_body = format!("{}{}", " ".repeat(body_col0), body_raw);
        let desugared_body = crate::gpu_fastcheck::desugar_lean_layout_blocks(&padded_body);
        let body = desugared_body.trim();
        if body.is_empty() {
            continue;
        }
        let mut name_end = 0;
        for (c_idx, c) in sig.char_indices() {
            if is_ident_continue(c) || c == '.' {
                name_end = c_idx + c.len_utf8();
            } else {
                break;
            }
        }
        if name_end == 0 {
            continue;
        }
        let raw_def_name = sig[..name_end].trim().to_string();
        let def_name = if !current_ns.is_empty() && !raw_def_name.contains('.') {
            format!("{}.{}", current_ns, raw_def_name)
        } else {
            raw_def_name
        };
        let after_name = sig[name_end..].trim();
        let mut explicit_only_params = Vec::new();
        let mut value_params = Vec::new();
        let mut all_params = Vec::new();
        let mut implicit_val_params = Vec::new();
        let chars: Vec<char> = after_name.chars().collect();
        let mut i = 0;
        while i < chars.len() {
            while i < chars.len() && chars[i].is_whitespace() {
                i += 1;
            }
            if i >= chars.len() || (chars[i] == ':' && (i + 1 >= chars.len() || chars[i + 1] != '=')) {
                break;
            }
            if chars[i] == '(' || chars[i] == '{' || chars[i] == '[' {
                let open = chars[i];
                let close = match open {
                    '(' => ')',
                    '{' => '}',
                    _ => ']',
                };
                i += 1;
                let b_start = i;
                let mut depth = 1usize;
                while i < chars.len() && depth > 0 {
                    if chars[i] == open {
                        depth += 1;
                    } else if chars[i] == close {
                        depth -= 1;
                    }
                    i += 1;
                }
                if open != '[' {
                    let inner: String = chars[b_start..i.saturating_sub(1)].iter().collect();
                    let (vars_part, ty_opt) = match split_top_level_colon(&inner) {
                        Some((v, t)) => (v, Some(t.trim())),
                        None => (inner.as_str(), None),
                    };
                    let is_type_sort = ty_opt.is_some_and(|t| {
                        t == "Type"
                            || t.starts_with("Type ")
                            || t == "Sort"
                            || t.starts_with("Sort ")
                    });
                    for v in vars_part.split_whitespace() {
                        if !v.is_empty() {
                            all_params.push(v.to_string());
                            // Only `{...}` (curly-brace) binders are implicit in Lean 4 and omitted at
                            // ordinary call sites. Explicit `(...)` parameters are never omitted.
                            if open == '(' {
                                let encoded_explicit = if let Some(ty_s) = ty_opt {
                                    let mentions_imp = implicit_val_params.iter().any(|imp: &String| {
                                        replace_ident_boundary(ty_s, imp, "__I__") != ty_s
                                    });
                                    if mentions_imp {
                                        format!("{}@{}", v, ty_s)
                                    } else {
                                        v.to_string()
                                    }
                                } else {
                                    v.to_string()
                                };
                                explicit_only_params.push(encoded_explicit);
                                value_params.push(v.to_string());
                            } else {
                                let later_signature: String = chars[i..].iter().collect();
                                let used_inferred_type = is_type_sort
                                    && (replace_ident_boundary(&later_signature, v, "__TYPE__")
                                        != later_signature
                                        || replace_ident_boundary(body, v, "__TYPE__") != body);
                                if !used_inferred_type {
                                    if !is_type_sort {
                                        implicit_val_params.push(v.to_string());
                                    }
                                    value_params.push(v.to_string());
                                }
                            }
                        }
                    }
                }
            } else if is_ident_start(chars[i]) {
                let s = i;
                while i < chars.len() && is_ident_continue(chars[i]) {
                    i += 1;
                }
                let p_name: String = chars[s..i].iter().collect();
                explicit_only_params.push(p_name.clone());
                value_params.push(p_name.clone());
                all_params.push(p_name);
            } else {
                i += 1;
            }
        }
        // Push `value_params` first so `audit_referenced_local_defs_for_stubs` inspects all value
        // parameters (including `{n : Nat}` implicit value parameters), followed by `explicit_only_params`
        // (for call sites that omit `{...}` implicit arguments) and `all_params` (for `@` / explicit calls).
        defs.push((def_name.clone(), value_params.clone(), body.to_string()));
        if !explicit_only_params.is_empty() && explicit_only_params != value_params {
            defs.push((def_name.clone(), explicit_only_params.clone(), body.to_string()));
        }
        if all_params != value_params && all_params != explicit_only_params {
            defs.push((def_name, all_params, body.to_string()));
        }
    }
    defs
}

pub(super) fn infer_implicit_subst_from_call_args(
    params: &[String],
    args: &[String],
    binder_types: &std::collections::HashMap<String, String>,
) -> Option<std::collections::HashMap<String, String>> {
    let mut subst = std::collections::HashMap::new();
    for (p_spec, arg_expr) in params.iter().zip(args.iter()) {
        if let Some((_, ty_pat)) = p_spec.split_once('@') {
            let arg_clean = strip_balanced_outer_parens(arg_expr.trim());
            let actual_ty = binder_types.get(arg_clean)?;
            let pat_tokens = split_lean_app_args(ty_pat.trim());
            let act_tokens = split_lean_app_args(actual_ty.trim());
            if pat_tokens.len() < 2
                || pat_tokens.len() != act_tokens.len()
                || pat_tokens[0] != act_tokens[0]
            {
                return None;
            }
            for (pt, at) in pat_tokens[1..].iter().zip(act_tokens[1..].iter()) {
                let pt_trim = pt.trim();
                let at_trim = at.trim();
                if pt_trim.chars().all(is_ident_continue) && !pt_trim.is_empty() {
                    if let Some(prev) = subst.get(pt_trim) {
                        if prev != at_trim {
                            return None;
                        }
                    } else {
                        subst.insert(pt_trim.to_string(), at_trim.to_string());
                    }
                } else if pt_trim != at_trim {
                    return None;
                }
            }
        }
    }
    Some(subst)
}

pub(super) fn extract_expr_identifiers(expr: &str) -> Vec<String> {
    let mut out = Vec::new();
    let chars: Vec<char> = expr.chars().collect();
    let mut i = 0usize;
    while i < chars.len() {
        if is_ident_start(chars[i]) {
            let s = i;
            i += 1;
            while i < chars.len() && is_ident_continue(chars[i]) {
                i += 1;
            }
            let ident: String = chars[s..i].iter().collect();
            if !matches!(
                ident.as_str(),
                "fun" | "forall" | "exists" | "let" | "in" | "if" | "then" | "else"
                    | "match" | "with" | "true" | "false" | "True" | "False" | "some" | "none"
            ) {
                out.push(ident);
            }
        } else {
            i += 1;
        }
    }
    out
}

fn match_binder_domain_op_at(chars: &[char], idx: usize) -> Option<(&'static str, usize)> {
    let ch = chars[idx];
    let prev = if idx > 0 { Some(chars[idx - 1]) } else { None };
    let next = if idx + 1 < chars.len() {
        Some(chars[idx + 1])
    } else {
        None
    };
    match ch {
        ':' if prev != Some(':') && next != Some('=') && next != Some(':') => Some((":", 1)),
        '∈' => Some(("∈", 1)),
        '∉' => Some(("∉", 1)),
        '⊆' => Some(("⊆", 1)),
        '⊂' => Some(("⊂", 1)),
        '≤' => Some(("≤", 1)),
        '≥' => Some(("≥", 1)),
        '<' if next == Some('=') => Some(("<=", 2)),
        '>' if next == Some('=') => Some((">=", 2)),
        '<' if prev != Some('<') && !matches!(next, Some('-' | '<' | '|')) => Some(("<", 1)),
        '>' if !matches!(prev, Some('-' | '=' | '>' | '|')) && !matches!(next, Some('>' | '=')) => {
            Some((">", 1))
        }
        _ => None,
    }
}

fn split_top_level_binder_domain(s: &str) -> Option<(&str, &'static str, &str)> {
    let chars: Vec<(usize, char)> = s.char_indices().collect();
    let only_chars: Vec<char> = chars.iter().map(|&(_, c)| c).collect();
    let mut depth = 0i32;
    let mut i = 0usize;
    while i < chars.len() {
        let (bp, c) = chars[i];
        if c == '"' {
            i += 1;
            while i < chars.len() {
                let (_, sc) = chars[i];
                i += 1;
                if sc == '\\' && i < chars.len() {
                    i += 1;
                } else if sc == '"' {
                    break;
                }
            }
            continue;
        }
        match c {
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth = (depth - 1).max(0),
            _ if depth == 0 => {
                if let Some((op, char_len)) = match_binder_domain_op_at(&only_chars, i) {
                    let end_byte = if i + char_len < chars.len() {
                        chars[i + char_len].0
                    } else {
                        s.len()
                    };
                    return Some((&s[..bp], op, &s[end_byte..]));
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn format_binder_domain_expr(op: &str, dom_raw: &str) -> String {
    let dt = dom_raw.trim();
    if dt.is_empty() {
        return "Prop".to_string();
    }
    let tag = match op {
        ":" => return dt.to_string(),
        "∈" => "__BoundMem",
        "∉" => "__BoundNotMem",
        "⊆" => "__BoundSubset",
        "⊂" => "__BoundSsubset",
        "≤" | "<=" => "__BoundLe",
        "≥" | ">=" => "__BoundGe",
        "<" => "__BoundLt",
        ">" => "__BoundGt",
        _ => return dt.to_string(),
    };
    format!("{} ({})", tag, dt)
}

fn parse_binder_header_groups(binder_header: &str) -> Vec<(String, String)> {
    let hdr = binder_header.trim();
    if hdr.is_empty() {
        return Vec::new();
    }
    if let Some((vars_part, op, dom_part)) = split_top_level_binder_domain(hdr) {
        let dom_expr = format_binder_domain_expr(op, dom_part);
        let mut out = Vec::new();
        for v in vars_part
            .split(|c: char| c.is_whitespace() || matches!(c, ',' | '(' | ')' | '⟨' | '⟩'))
        {
            if !v.is_empty() && (v == "_" || is_ident_start(v.chars().next().unwrap_or('0'))) {
                out.push((v.to_string(), dom_expr.clone()));
            }
        }
        if out.is_empty() {
            out.push(("_".to_string(), dom_expr));
        }
        return out;
    }
    let mut out = Vec::new();
    let chars: Vec<char> = hdr.chars().collect();
    let mut i = 0usize;
    while i < chars.len() {
        while i < chars.len() && chars[i].is_whitespace() {
            i += 1;
        }
        if i >= chars.len() {
            break;
        }
        if matches!(chars[i], '(' | '{' | '[' | '⟨') {
            let open = chars[i];
            let close = match open {
                '(' => ')',
                '{' => '}',
                '[' => ']',
                _ => '⟩',
            };
            i += 1;
            let start = i;
            let mut depth = 1usize;
            while i < chars.len() && depth > 0 {
                if chars[i] == open {
                    depth += 1;
                } else if chars[i] == close {
                    depth -= 1;
                }
                i += 1;
            }
            let inner: String = chars[start..i.saturating_sub(1)].iter().collect();
            if open == '[' {
                out.push(("_".to_string(), inner.trim().to_string()));
            } else if let Some((vars_part, op, dom_part)) = split_top_level_binder_domain(&inner) {
                let dom_expr = format_binder_domain_expr(op, dom_part);
                let mut pushed = false;
                for v in vars_part
                    .split(|c: char| c.is_whitespace() || matches!(c, ',' | '(' | ')' | '⟨' | '⟩'))
                {
                    if !v.is_empty()
                        && (v == "_" || is_ident_start(v.chars().next().unwrap_or('0')))
                    {
                        out.push((v.to_string(), dom_expr.clone()));
                        pushed = true;
                    }
                }
                if !pushed {
                    out.push(("_".to_string(), dom_expr));
                }
            } else {
                for v in inner
                    .split(|c: char| c.is_whitespace() || matches!(c, ',' | '(' | ')' | '⟨' | '⟩'))
                {
                    if !v.is_empty()
                        && (v == "_" || is_ident_start(v.chars().next().unwrap_or('0')))
                    {
                        out.push((v.to_string(), "Prop".to_string()));
                    }
                }
            }
        } else if is_ident_start(chars[i]) {
            let s = i;
            i += 1;
            while i < chars.len() && is_ident_continue(chars[i]) {
                i += 1;
            }
            let v: String = chars[s..i].iter().collect();
            out.push((v, "Prop".to_string()));
        } else {
            i += 1;
        }
    }
    out
}

fn extract_binder_names_from_header(binder_header: &str) -> Vec<String> {
    parse_binder_header_groups(binder_header)
        .into_iter()
        .filter_map(|(v, _)| (v != "_").then_some(v))
        .collect()
}

fn is_valid_top_level_delim_at(
    s: &str,
    chars: &[(usize, char)],
    idx: usize,
    delim: &str,
) -> bool {
    let byte_pos = chars[idx].0;
    if !s[byte_pos..].starts_with(delim) {
        return false;
    }
    if delim == " in " {
        return true;
    }
    if matches!(delim, "then" | "else" | "with") {
        let prev_ok = idx == 0 || (!is_ident_continue(chars[idx - 1].1) && chars[idx - 1].1 != '.');
        let end_byte = byte_pos + delim.len();
        let next_ok = s[end_byte..]
            .chars()
            .next()
            .map_or(true, |ch| !is_ident_continue(ch) && ch != '.');
        return prev_ok && next_ok;
    }
    let prev = if idx > 0 { Some(chars[idx - 1].1) } else { None };
    let dlen = delim.chars().count();
    let next = if idx + dlen < chars.len() {
        Some(chars[idx + dlen].1)
    } else {
        None
    };
    match delim {
        "&&" => prev != Some('&') && next != Some('&'),
        "&&&" => prev != Some('&') && next != Some('&'),
        "||" => prev != Some('|') && next != Some('|'),
        "|||" => prev != Some('|') && next != Some('|'),
        "^^^" => prev != Some('^') && next != Some('^'),
        "<<<" => prev != Some('<') && next != Some('<'),
        ">>>" => prev != Some('>') && next != Some('>'),
        "++" => prev != Some('+') && next != Some('+'),
        "=" => {
            !matches!(prev, Some('!' | '<' | '>' | ':' | '='))
                && !matches!(next, Some('=' | '>'))
        }
        ">" => {
            !matches!(prev, Some('=' | '-' | '>' | '|')) && !matches!(next, Some('=' | '>'))
        }
        "<" => prev != Some('<') && !matches!(next, Some('=' | '-' | '<' | '|')),
        "|>" => prev != Some('<') && next != Some('.'),
        "|>." => prev != Some('<'),
        "::" => prev != Some(':') && next != Some(':') && next != Some('='),
        "+" | "-" | "*" | "/" | "%" => {
            let dch = delim.chars().next().unwrap_or('+');
            let prev_ws = prev.is_some_and(|ch| ch.is_whitespace());
            let next_ws = next.is_some_and(|ch| ch.is_whitespace());
            prev_ws
                && next_ws
                && prev != Some(dch)
                && next != Some(dch)
                && !(dch == '-' && next == Some('>'))
                && !(dch == '/' && matches!(next, Some('\\' | '-')))
        }
        _ => true,
    }
}

fn find_top_level_delim(s: &str, delim: &str) -> Option<usize> {
    let chars: Vec<(usize, char)> = s.char_indices().collect();
    let mut depth = 0i32;
    let mut idx = 0usize;
    while idx < chars.len() {
        let (byte_pos, c) = chars[idx];
        if c == '"' {
            idx += 1;
            while idx < chars.len() {
                let (_, sc) = chars[idx];
                idx += 1;
                if sc == '\\' && idx < chars.len() {
                    idx += 1;
                } else if sc == '"' {
                    break;
                }
            }
            continue;
        }
        match c {
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth = (depth - 1).max(0),
            _ if depth == 0 && is_valid_top_level_delim_at(s, &chars, idx, delim) => {
                return Some(byte_pos);
            }
            _ => {}
        }
        idx += 1;
    }
    None
}

fn rfind_top_level_delim(s: &str, delim: &str) -> Option<usize> {
    let chars: Vec<(usize, char)> = s.char_indices().collect();
    let mut depth = 0i32;
    let mut idx = 0usize;
    let mut last_match = None;
    while idx < chars.len() {
        let (byte_pos, c) = chars[idx];
        if c == '"' {
            idx += 1;
            while idx < chars.len() {
                let (_, sc) = chars[idx];
                idx += 1;
                if sc == '\\' && idx < chars.len() {
                    idx += 1;
                } else if sc == '"' {
                    break;
                }
            }
            continue;
        }
        match c {
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth = (depth - 1).max(0),
            _ if depth == 0 && is_valid_top_level_delim_at(s, &chars, idx, delim) => {
                last_match = Some(byte_pos);
            }
            _ => {}
        }
        idx += 1;
    }
    last_match
}

fn allocate_fresh_alpha_ident(
    base: &str,
    avoid: &std::collections::HashSet<String>,
    used_idents: &mut std::collections::HashSet<String>,
) -> String {
    let mut k = 1usize;
    loop {
        let cand = format!("{}_alpha{}", base, k);
        if !avoid.contains(&cand) && !used_idents.contains(&cand) {
            used_idents.insert(cand.clone());
            return cand;
        }
        k += 1;
    }
}

fn extract_pattern_bound_vars(pat: &str) -> Vec<String> {
    let mut out = Vec::new();
    let chars: Vec<char> = pat.chars().collect();
    let mut i = 0usize;
    let mut is_first_ctor = false;
    while i < chars.len() {
        while i < chars.len() && chars[i].is_whitespace() {
            i += 1;
        }
        if i >= chars.len() {
            break;
        }
        if chars[i] == '.' {
            i += 1;
            while i < chars.len() && (is_ident_continue(chars[i]) || chars[i] == '.') {
                i += 1;
            }
            is_first_ctor = true;
            continue;
        }
        if is_ident_start(chars[i]) {
            let s = i;
            i += 1;
            while i < chars.len() && (is_ident_continue(chars[i]) || chars[i] == '.') {
                i += 1;
            }
            let tok: String = chars[s..i].iter().collect();
            if tok.contains('.')
                || matches!(
                    tok.as_str(),
                    "_" | "true" | "false" | "True" | "False" | "none" | "some" | "ok" | "error" | "nil" | "cons"
                )
            {
                is_first_ctor = true;
                continue;
            }
            if !is_first_ctor
                && tok
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_ascii_uppercase())
            {
                is_first_ctor = true;
                continue;
            }
            if !out.contains(&tok) {
                out.push(tok);
            }
        } else {
            is_first_ctor = false;
            i += 1;
        }
    }
    out
}

fn is_match_arm_bar_at(chars: &[(usize, char)], idx: usize) -> bool {
    if idx >= chars.len() || chars[idx].1 != '|' {
        return false;
    }
    let prev = if idx > 0 { Some(chars[idx - 1].1) } else { None };
    let next = if idx + 1 < chars.len() {
        Some(chars[idx + 1].1)
    } else {
        None
    };
    !matches!(prev, Some('|' | '<')) && !matches!(next, Some('|' | '>'))
}

fn find_let_newline_sep(after_assign: &str) -> Option<usize> {
    let chars: Vec<(usize, char)> = after_assign.char_indices().collect();
    let mut depth = 0i32;
    let mut idx = 0usize;
    while idx < chars.len() {
        let (bp, c) = chars[idx];
        if c == '"' {
            idx += 1;
            while idx < chars.len() {
                let (_, sc) = chars[idx];
                idx += 1;
                if sc == '\\' && idx < chars.len() {
                    idx += 1;
                } else if sc == '"' {
                    break;
                }
            }
            continue;
        }
        match c {
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth = (depth - 1).max(0),
            '\n' if depth == 0 => {
                let before = after_assign[..bp].trim();
                let after = after_assign[bp + 1..].trim();
                let cont = before.is_empty()
                    || before.ends_with(":=")
                    || before.ends_with("=>")
                    || before.ends_with("&&")
                    || before.ends_with("||")
                    || before.ends_with("++")
                    || before.ends_with("::")
                    || before.ends_with("|>")
                    || before.ends_with("|>.")
                    || before.ends_with("then")
                    || before.ends_with("else")
                    || before.ends_with("with")
                    || before.ends_with("in");
                if !cont && !after.is_empty() {
                    return Some(bp);
                }
            }
            _ => {}
        }
        idx += 1;
    }
    None
}

fn canonicalize_pattern_alpha(pat_raw: &str, pvars: &[String]) -> String {
    let mut cur = pat_raw.trim().to_string();
    for (idx, pv) in pvars.iter().enumerate() {
        cur = replace_ident_boundary(&cur, pv, &format!("__PAT_ALPHA_PH_{}__", idx));
    }
    for idx in 0..pvars.len() {
        cur = cur.replace(&format!("__PAT_ALPHA_PH_{}__", idx), &format!("$p{}", idx));
    }
    cur.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn subst_binder_header_and_extend_scope(
    header: &str,
    outer_subst: &std::collections::HashMap<String, String>,
    avoid_vars: &std::collections::HashSet<String>,
    used_idents: &mut std::collections::HashSet<String>,
) -> (String, std::collections::HashMap<String, String>) {
    let mut pre_clause_subst = outer_subst.clone();
    let mut local_subst = outer_subst.clone();
    let mut local_avoid = avoid_vars.clone();
    let chars: Vec<char> = header.chars().collect();
    let mut out_hdr = String::with_capacity(header.len());
    let mut i = 0usize;
    while i < chars.len() {
        if chars[i].is_whitespace() {
            out_hdr.push(chars[i]);
            i += 1;
            continue;
        }
        if let Some((op, op_len)) = match_binder_domain_op_at(&chars, i) {
            let rest_ty: String = chars[i + op_len..].iter().collect();
            let sub_ty = subst_lean_expr_scoped(&rest_ty, &pre_clause_subst, used_idents);
            if op == ":" {
                out_hdr.push_str(": ");
            } else {
                if !out_hdr.is_empty() && !out_hdr.ends_with(char::is_whitespace) {
                    out_hdr.push(' ');
                }
                out_hdr.push_str(op);
                out_hdr.push(' ');
            }
            out_hdr.push_str(sub_ty.trim());
            break;
        }
        if matches!(chars[i], '(' | '{' | '[') {
            let open = chars[i];
            let close = match open {
                '(' => ')',
                '{' => '}',
                _ => ']',
            };
            i += 1;
            let b_start = i;
            let mut depth = 1usize;
            while i < chars.len() && depth > 0 {
                if chars[i] == open {
                    depth += 1;
                } else if chars[i] == close {
                    depth -= 1;
                }
                i += 1;
            }
            let inner: String = chars[b_start..i.saturating_sub(1)].iter().collect();
            if open == '[' {
                let sub_in = subst_lean_expr_scoped(&inner, &pre_clause_subst, used_idents);
                out_hdr.push('[');
                out_hdr.push_str(&sub_in);
                out_hdr.push(']');
            } else if let Some((vars_part, op, ty_part)) = split_top_level_binder_domain(&inner) {
                let sub_ty = subst_lean_expr_scoped(ty_part.trim(), &pre_clause_subst, used_idents);
                let mut renamed_vars = Vec::new();
                for raw_v in vars_part.split_whitespace() {
                    let v = raw_v.trim();
                    if v.is_empty() {
                        continue;
                    }
                    if v == "_" {
                        renamed_vars.push("_".to_string());
                        continue;
                    }
                    local_subst.remove(v);
                    if local_avoid.contains(v) {
                        let fresh = allocate_fresh_alpha_ident(v, &local_avoid, used_idents);
                        local_subst.insert(v.to_string(), fresh.clone());
                        local_avoid.insert(fresh.clone());
                        renamed_vars.push(fresh);
                    } else {
                        local_avoid.insert(v.to_string());
                        renamed_vars.push(v.to_string());
                    }
                }
                out_hdr.push(open);
                out_hdr.push_str(&renamed_vars.join(" "));
                if op == ":" {
                    out_hdr.push_str(" : ");
                } else {
                    out_hdr.push(' ');
                    out_hdr.push_str(op);
                    out_hdr.push(' ');
                }
                out_hdr.push_str(&sub_ty);
                out_hdr.push(close);
            } else {
                let mut renamed_vars = Vec::new();
                for raw_v in
                    inner.split(|c: char| c.is_whitespace() || matches!(c, ',' | '(' | ')' | '⟨' | '⟩'))
                {
                    let v = raw_v.trim();
                    if v.is_empty() {
                        continue;
                    }
                    if v == "_" {
                        renamed_vars.push("_".to_string());
                        continue;
                    }
                    local_subst.remove(v);
                    if local_avoid.contains(v) {
                        let fresh = allocate_fresh_alpha_ident(v, &local_avoid, used_idents);
                        local_subst.insert(v.to_string(), fresh.clone());
                        local_avoid.insert(fresh.clone());
                        renamed_vars.push(fresh);
                    } else {
                        local_avoid.insert(v.to_string());
                        renamed_vars.push(v.to_string());
                    }
                }
                let sep = if inner.contains(',') { ", " } else { " " };
                out_hdr.push(open);
                out_hdr.push_str(&renamed_vars.join(sep));
                out_hdr.push(close);
            }
            pre_clause_subst = local_subst.clone();
        } else if is_ident_start(chars[i]) {
            let s = i;
            i += 1;
            while i < chars.len() && is_ident_continue(chars[i]) {
                i += 1;
            }
            let v: String = chars[s..i].iter().collect();
            if v == "_" {
                out_hdr.push('_');
            } else {
                local_subst.remove(&v);
                if local_avoid.contains(&v) {
                    let fresh = allocate_fresh_alpha_ident(&v, &local_avoid, used_idents);
                    local_subst.insert(v, fresh.clone());
                    local_avoid.insert(fresh.clone());
                    out_hdr.push_str(&fresh);
                } else {
                    local_avoid.insert(v.clone());
                    out_hdr.push_str(&v);
                }
            }
        } else {
            out_hdr.push(chars[i]);
            i += 1;
        }
    }
    (out_hdr, local_subst)
}

/// Substitute inside Lean 4 structure literal / record update `{ [base with] f1 := v1, f2 := v2 }`:
/// field names on the LHS of `:=` are record labels (never substituted), whereas `base` and RHS values are substituted.
fn subst_lean_brace_group_scoped(
    inner: &str,
    subst: &std::collections::HashMap<String, String>,
    used_idents: &mut std::collections::HashSet<String>,
) -> String {
    if find_top_level_delim(inner, ":=").is_none() {
        return subst_lean_expr_scoped(inner, subst, used_idents);
    }
    let (prefix_out, fields_slice) = if let Some(w_pos) = find_top_level_delim(inner, " with ") {
        let base_s = &inner[..w_pos];
        let sub_base = subst_lean_expr_scoped(base_s, subst, used_idents);
        (format!("{} with ", sub_base), &inner[w_pos + 6..])
    } else {
        (String::new(), inner)
    };
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut in_str = false;
    let mut last = 0usize;
    let fchars: Vec<(usize, char)> = fields_slice.char_indices().collect();
    let mut fi = 0usize;
    while fi < fchars.len() {
        let (bp, ch) = fchars[fi];
        if in_str {
            if ch == '\\' && fi + 1 < fchars.len() {
                fi += 2;
                continue;
            }
            if ch == '"' {
                in_str = false;
            }
            fi += 1;
            continue;
        }
        match ch {
            '"' => in_str = true,
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth = (depth - 1).max(0),
            ',' | ';' if depth == 0 => {
                parts.push((&fields_slice[last..bp], Some(ch)));
                last = bp + ch.len_utf8();
            }
            _ => {}
        }
        fi += 1;
    }
    parts.push((&fields_slice[last..], None));
    let mut out = prefix_out;
    for (seg, sep_ch) in parts {
        if let Some(assign_pos) = find_top_level_delim(seg, ":=") {
            let lhs_field = &seg[..assign_pos];
            let rhs_val = &seg[assign_pos + 2..];
            let sub_rhs = subst_lean_expr_scoped(rhs_val, subst, used_idents);
            out.push_str(lhs_field);
            out.push_str(":=");
            out.push_str(&sub_rhs);
        } else {
            out.push_str(&subst_lean_expr_scoped(seg, subst, used_idents));
        }
        if let Some(sc) = sep_ch {
            out.push(sc);
        }
    }
    out
}
/// Confines binder scopes (`fun`/`λ`/`∀`/`forall`/`∃`/`exists`, `let`/`have`, and `| pat => rhs` match arms)
/// to their enclosing bracketed groups or arm boundaries so free occurrences outside a binder's scope
/// (e.g. trailing `y` in `(fun y => x) y` or `(∀ y, P y) ∧ Q y`) are never corrupted.
pub(super) fn subst_lean_expr_scoped(
    expr: &str,
    subst: &std::collections::HashMap<String, String>,
    used_idents: &mut std::collections::HashSet<String>,
) -> String {
    if expr.is_empty() {
        return String::new();
    }
    let mut avoid_vars = std::collections::HashSet::new();
    for (k, v) in subst {
        avoid_vars.insert(k.clone());
        for id in extract_expr_identifiers(v) {
            avoid_vars.insert(id);
        }
    }

    let chars: Vec<(usize, char)> = expr.char_indices().collect();
    let mut out = String::with_capacity(expr.len());
    let mut idx = 0usize;

    while idx < chars.len() {
        let (byte_pos, c) = chars[idx];

        // 1. String literal: copy verbatim
        if c == '"' {
            out.push(c);
            idx += 1;
            while idx < chars.len() {
                let (_, sc) = chars[idx];
                out.push(sc);
                idx += 1;
                if sc == '\\' && idx < chars.len() {
                    out.push(chars[idx].1);
                    idx += 1;
                } else if sc == '"' {
                    break;
                }
            }
            continue;
        }

        // 2. Bracketed subexpression `(...)`, `{...}`, `[...]`, `⟨...⟩`: isolate lexical scope!
        if matches!(c, '(' | '{' | '[' | '⟨') {
            let open = c;
            let close = match open {
                '(' => ')',
                '{' => '}',
                '[' => ']',
                _ => '⟩',
            };
            let inner_start_byte = byte_pos + open.len_utf8();
            let mut depth = 1usize;
            idx += 1;
            let mut close_byte = expr.len();
            let mut found_close = false;
            while idx < chars.len() {
                let (bp, ch) = chars[idx];
                if ch == '"' {
                    idx += 1;
                    while idx < chars.len() {
                        let (_, sc) = chars[idx];
                        idx += 1;
                        if sc == '\\' && idx < chars.len() {
                            idx += 1;
                        } else if sc == '"' {
                            break;
                        }
                    }
                    continue;
                }
                if ch == open {
                    depth += 1;
                } else if ch == close {
                    depth -= 1;
                    if depth == 0 {
                        close_byte = bp;
                        found_close = true;
                        idx += 1;
                        break;
                    }
                }
                idx += 1;
            }
            if found_close {
                let inner = &expr[inner_start_byte..close_byte];
                let sub_inner = if open == '{' {
                    subst_lean_brace_group_scoped(inner, subst, used_idents)
                } else {
                    subst_lean_expr_scoped(inner, subst, used_idents)
                };
                out.push(open);
                out.push_str(&sub_inner);
                out.push(close);
            } else {
                let inner = &expr[inner_start_byte..];
                let sub_inner = subst_lean_expr_scoped(inner, subst, used_idents);
                out.push(open);
                out.push_str(&sub_inner);
            }
            continue;
        }

        // 3. Match arm `| pat => rhs`: scope pattern variables strictly to this arm (up to next top-level `|`)
        if is_match_arm_bar_at(&chars, idx) {
            let arm_start = byte_pos + 1;
            // Find the end of this arm (next top-level match-arm `|`, or end of `expr`)
            let mut arm_end_byte = expr.len();
            let mut next_idx = chars.len();
            let mut depth = 0i32;
            let mut scan = idx + 1;
            while scan < chars.len() {
                let (s_bp, s_ch) = chars[scan];
                if s_ch == '"' {
                    scan += 1;
                    while scan < chars.len() {
                        let (_, sc) = chars[scan];
                        scan += 1;
                        if sc == '\\' && scan < chars.len() {
                            scan += 1;
                        } else if sc == '"' {
                            break;
                        }
                    }
                    continue;
                }
                match s_ch {
                    '(' | '{' | '[' | '⟨' => depth += 1,
                    ')' | '}' | ']' | '⟩' => depth = (depth - 1).max(0),
                    '|' if depth == 0 && is_match_arm_bar_at(&chars, scan) => {
                        arm_end_byte = s_bp;
                        next_idx = scan;
                        break;
                    }
                    _ => {}
                }
                scan += 1;
            }
            let arm_slice = &expr[arm_start..arm_end_byte];
            if let Some(arrow_pos) = find_top_level_delim(arm_slice, "=>") {
                let pat_raw = &arm_slice[..arrow_pos];
                let rhs_raw = &arm_slice[arrow_pos + 2..];
                let pat_vars = extract_pattern_bound_vars(pat_raw);
                let mut arm_subst = subst.clone();
                let mut arm_avoid = avoid_vars.clone();
                let mut sub_pat = pat_raw.to_string();
                for pv in pat_vars {
                    arm_subst.remove(&pv);
                    if arm_avoid.contains(&pv) {
                        let fresh = allocate_fresh_alpha_ident(&pv, &arm_avoid, used_idents);
                        sub_pat = replace_ident_boundary(&sub_pat, &pv, &fresh);
                        arm_subst.insert(pv, fresh.clone());
                        arm_avoid.insert(fresh);
                    } else {
                        arm_avoid.insert(pv);
                    }
                }
                let sub_rhs = subst_lean_expr_scoped(rhs_raw, &arm_subst, used_idents);
                out.push('|');
                out.push_str(&sub_pat);
                out.push_str("=>");
                out.push_str(&sub_rhs);
                idx = next_idx;
                continue;
            }
        }

        // 4. Identifier or binder keyword (`fun`, `λ`, `∀`, `forall`, `∃`, `exists`, `let`, `have`)
        let prev_ok = idx == 0 || (!is_ident_continue(chars[idx - 1].1) && chars[idx - 1].1 != '.');
        if prev_ok {
            let rem = &expr[byte_pos..];
            let mut matched_binder: Option<(&str, &str)> = None;
            for (kw, delim) in [
                ("fun", "=>"),
                ("λ", "=>"),
                ("∀", ","),
                ("forall", ","),
                ("∃", ","),
                ("exists", ","),
            ] {
                if let Some(after_kw) = rem.strip_prefix(kw) {
                    if after_kw
                        .chars()
                        .next()
                        .is_some_and(|ch| ch.is_whitespace() || matches!(ch, '(' | '{' | '['))
                    {
                        matched_binder = Some((kw, delim));
                        break;
                    }
                }
            }
            if let Some((kw, delim)) = matched_binder {
                let hdr_start = byte_pos + kw.len();
                let after_kw = &expr[hdr_start..];
                if let Some(rel_delim) = find_top_level_delim(after_kw, delim) {
                    let header = &after_kw[..rel_delim];
                    let body = &after_kw[rel_delim + delim.len()..];
                    let (sub_hdr, local_subst) = subst_binder_header_and_extend_scope(
                        header,
                        subst,
                        &avoid_vars,
                        used_idents,
                    );
                    let sub_body = subst_lean_expr_scoped(body, &local_subst, used_idents);
                    out.push_str(kw);
                    out.push_str(&sub_hdr);
                    out.push_str(delim);
                    out.push_str(&sub_body);
                    break;
                }
            }

            // `let f (x : T) [: Ret] := val in body` or `let x [: T] := val; body`
            for let_kw in ["let", "have"] {
                if let Some(after_let) = rem.strip_prefix(let_kw) {
                    if after_let.chars().next().is_some_and(|ch| ch.is_whitespace()) {
                        if let Some(assign_rel) = find_top_level_delim(after_let, ":=") {
                            let lhs_hdr = &after_let[..assign_rel];
                            let after_assign = &after_let[assign_rel + 2..];
                            let sep_match = find_top_level_delim(after_assign, " in ")
                                .map(|p| (p, " in "))
                                .or_else(|| find_top_level_delim(after_assign, ";").map(|p| (p, ";")))
                                .or_else(|| find_let_newline_sep(after_assign).map(|p| (p, "\n")));
                            if let Some((sep_rel, sep_str)) = sep_match {
                                let val_part = &after_assign[..sep_rel];
                                let body_part = &after_assign[sep_rel + sep_str.len()..];
                                // Split `lhs_hdr` into the bound name/pattern (which scopes over `body_part`)
                                // and any function parameters `(x : T)` (which scope over `val_part`).
                                let lhs_trim = lhs_hdr.trim_start();
                                let lead_ws_len = lhs_hdr.len() - lhs_trim.len();
                                let mut name_end = 0usize;
                                for (bi, ch) in lhs_trim.char_indices() {
                                    if ch.is_whitespace() || matches!(ch, '(' | '{' | '[' | ':') {
                                        break;
                                    }
                                    name_end = bi + ch.len_utf8();
                                }
                                let let_name_slice = &lhs_hdr[..lead_ws_len + name_end];
                                let fn_params_slice = &lhs_hdr[lead_ws_len + name_end..];
                                let (sub_fn_params, val_subst) = subst_binder_header_and_extend_scope(
                                    fn_params_slice,
                                    subst,
                                    &avoid_vars,
                                    used_idents,
                                );
                                let sub_val =
                                    subst_lean_expr_scoped(val_part, &val_subst, used_idents);
                                let (sub_let_name, body_subst) = subst_binder_header_and_extend_scope(
                                    let_name_slice,
                                    subst,
                                    &avoid_vars,
                                    used_idents,
                                );
                                let sub_body =
                                    subst_lean_expr_scoped(body_part, &body_subst, used_idents);
                                out.push_str(let_kw);
                                out.push_str(&sub_let_name);
                                out.push_str(&sub_fn_params);
                                if !out.ends_with(char::is_whitespace) {
                                    out.push(' ');
                                }
                                out.push_str(":= ");
                                out.push_str(sub_val.trim_start());
                                out.push_str(sep_str);
                                out.push_str(&sub_body);
                                return out;
                            }
                        }
                    }
                }
            }

            if is_ident_start(c) {
                let start_idx = idx;
                idx += 1;
                while idx < chars.len() && is_ident_continue(chars[idx].1) {
                    idx += 1;
                }
                let end_byte = if idx < chars.len() {
                    chars[idx].0
                } else {
                    expr.len()
                };
                let ident = &expr[chars[start_idx].0..end_byte];
                if let Some(rep) = subst.get(ident) {
                    out.push_str(rep);
                } else {
                    out.push_str(ident);
                }
                continue;
            }
        }

        out.push(c);
        idx += 1;
    }

    out
}

#[allow(dead_code)]
pub(super) fn alpha_rename_conflicting_binders(
    body: &str,
    avoid: &std::collections::HashSet<String>,
    used_idents: &mut std::collections::HashSet<String>,
) -> String {
    let mut dummy_subst = std::collections::HashMap::with_capacity(avoid.len());
    for v in avoid {
        dummy_subst.insert(format!("__AVOID_ONLY_{}__", v), v.clone());
    }
    subst_lean_expr_scoped(body, &dummy_subst, used_idents)
}

pub(super) fn replace_ident_boundary(haystack: &str, ident: &str, replacement: &str) -> String {
    if ident.is_empty() || ident == "_" {
        return haystack.to_string();
    }
    let chars: Vec<char> = haystack.chars().collect();
    let id_chars: Vec<char> = ident.chars().collect();
    let mut out = String::with_capacity(haystack.len());
    let mut i = 0;
    while i < chars.len() {
        if i + id_chars.len() <= chars.len() && chars[i..i + id_chars.len()] == id_chars[..] {
            let prev_ok = i == 0 || (!is_ident_continue(chars[i - 1]) && chars[i - 1] != '.');
            let next_ok = i + id_chars.len() == chars.len() || !is_ident_continue(chars[i + id_chars.len()]);
            if prev_ok && next_ok {
                out.push_str(replacement);
                i += id_chars.len();
                continue;
            }
        }
        out.push(chars[i]);
        i += 1;
    }
    out
}

/// Scans `inner` for top-level tuple/list commas, returning `None` if brackets inside `inner`
/// become negative or end unbalanced, and ignoring commas belonging to quantifiers (`∀ x, ...`, `∃ x, ...`)
/// or `match a, b with | p1, p2 => ...` scrutinees and patterns.
fn find_top_level_tuple_comma_positions(inner: &str) -> Option<Vec<usize>> {
    let chars: Vec<(usize, char)> = inner.char_indices().collect();
    let mut depth = 0i32;
    let mut pending_quant_commas = 0usize;
    let mut in_match_scrut = false;
    let mut in_match_pat = false;
    let mut commas = Vec::new();
    let mut idx = 0usize;
    while idx < chars.len() {
        let (byte_pos, c) = chars[idx];
        if c == '"' {
            idx += 1;
            while idx < chars.len() {
                let (_, sc) = chars[idx];
                idx += 1;
                if sc == '\\' && idx < chars.len() {
                    idx += 1;
                } else if sc == '"' {
                    break;
                }
            }
            continue;
        }
        if c == '\'' && (idx == 0 || !is_ident_continue(chars[idx - 1].1)) {
            if idx + 2 < chars.len() && chars[idx + 1].1 != '\\' && chars[idx + 2].1 == '\'' {
                idx += 3;
                continue;
            }
            if idx + 3 < chars.len() && chars[idx + 1].1 == '\\' && chars[idx + 3].1 == '\'' {
                idx += 4;
                continue;
            }
        }
        match c {
            '(' | '{' | '[' | '⟨' => {
                depth += 1;
                idx += 1;
                continue;
            }
            ')' | '}' | ']' | '⟩' => {
                depth -= 1;
                if depth < 0 {
                    return None;
                }
                idx += 1;
                continue;
            }
            _ => {}
        }
        if depth == 0 {
            if c == '=' && idx + 1 < chars.len() && chars[idx + 1].1 == '>' {
                in_match_pat = false;
                idx += 2;
                continue;
            }
            if is_match_arm_bar_at(&chars, idx) {
                in_match_scrut = false;
                in_match_pat = true;
                pending_quant_commas = 0;
                idx += 1;
                continue;
            }
            if c == ',' {
                if !in_match_scrut && !in_match_pat {
                    if pending_quant_commas > 0 {
                        pending_quant_commas -= 1;
                    } else {
                        commas.push(byte_pos);
                    }
                }
                idx += 1;
                continue;
            }
            let prev_ok = idx == 0 || (!is_ident_continue(chars[idx - 1].1) && chars[idx - 1].1 != '.');
            if prev_ok {
                let rem = &inner[byte_pos..];
                let mut matched_quant_len: Option<usize> = None;
                for qkw in ["∀", "forall", "∃", "exists"] {
                    if let Some(after_q) = rem.strip_prefix(qkw) {
                        if after_q
                            .chars()
                            .next()
                            .is_some_and(|ch| ch.is_whitespace() || matches!(ch, '(' | '{' | '['))
                        {
                            matched_quant_len = Some(qkw.chars().count());
                            break;
                        }
                    }
                }
                if let Some(qchars) = matched_quant_len {
                    if !in_match_pat {
                        pending_quant_commas += 1;
                    }
                    idx += qchars;
                    continue;
                }
                if let Some(after_m) = rem.strip_prefix("match") {
                    if after_m.chars().next().is_some_and(char::is_whitespace) {
                        in_match_scrut = true;
                        in_match_pat = false;
                        idx += 5;
                        continue;
                    }
                }
                if let Some(after_w) = rem.strip_prefix("with") {
                    if after_w
                        .chars()
                        .next()
                        .map_or(true, |ch| !is_ident_continue(ch) && ch != '.')
                    {
                        in_match_scrut = false;
                        idx += 4;
                        continue;
                    }
                }
            }
        }
        idx += 1;
    }
    if depth == 0 {
        Some(commas)
    } else {
        None
    }
}

fn has_unbracketed_whitespace_or_op(s: &str) -> bool {
    let t = s.trim();
    if t.is_empty() {
        return false;
    }
    let chars: Vec<(usize, char)> = t.char_indices().collect();
    let mut depth = 0i32;
    let mut idx = 0usize;
    while idx < chars.len() {
        let (_, c) = chars[idx];
        if c == '"' {
            idx += 1;
            while idx < chars.len() {
                let (_, sc) = chars[idx];
                idx += 1;
                if sc == '\\' && idx < chars.len() {
                    idx += 1;
                } else if sc == '"' {
                    break;
                }
            }
            continue;
        }
        if c == '\'' && (idx == 0 || !is_ident_continue(chars[idx - 1].1)) {
            if idx + 2 < chars.len() && chars[idx + 1].1 != '\\' && chars[idx + 2].1 == '\'' {
                idx += 3;
                continue;
            }
            if idx + 3 < chars.len() && chars[idx + 1].1 == '\\' && chars[idx + 3].1 == '\'' {
                idx += 4;
                continue;
            }
        }
        match c {
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth = (depth - 1).max(0),
            _ if depth == 0 => {
                if c.is_whitespace() {
                    return true;
                }
                if idx == 0 && matches!(c, '!' | '¬' | '-') {
                    return true;
                }
                if matches!(
                    c,
                    '+' | '-'
                        | '*'
                        | '/'
                        | '%'
                        | '='
                        | '<'
                        | '>'
                        | '&'
                        | '|'
                        | '^'
                        | '~'
                        | ':'
                        | ';'
                        | ','
                        | '→'
                        | '↔'
                        | '∧'
                        | '∨'
                        | '≠'
                        | '≤'
                        | '≥'
                        | '∈'
                        | '∉'
                        | '⊆'
                        | '⊂'
                ) {
                    return true;
                }
            }
            _ => {}
        }
        idx += 1;
    }
    false
}

#[inline]
fn needs_parens_as_atom(s: &str) -> bool {
    has_unbracketed_whitespace_or_op(s)
}

#[inline]
fn needs_parens_as_proj_base(s: &str) -> bool {
    let t = s.trim();
    has_unbracketed_whitespace_or_op(t)
        || (t.contains('#') && !t.starts_with("#[") && !t.starts_with('('))
}

fn is_ambiguous_prelude_short_name(short: &str) -> bool {
    matches!(
        short,
        "max"
            | "min"
            | "zero"
            | "one"
            | "add"
            | "sub"
            | "mul"
            | "div"
            | "mod"
            | "and"
            | "or"
            | "xor"
            | "not"
            | "lt"
            | "le"
            | "beq"
            | "default"
            | "empty"
            | "size"
            | "length"
            | "get"
            | "set"
            | "map"
            | "foldl"
            | "foldr"
            | "filter"
            | "append"
            | "head"
            | "tail"
            | "fst"
            | "snd"
            | "val"
            | "mk"
            | "ok"
            | "error"
            | "some"
            | "none"
    )
}

pub(super) fn strip_balanced_outer_parens(s: &str) -> &str {
    let mut cur = s.trim();
    loop {
        if cur.starts_with('(') && cur.ends_with(')') && cur.len() >= 2 {
            let inner = &cur[1..cur.len() - 1];
            if !inner.trim().is_empty() {
                if let Some(commas) = find_top_level_tuple_comma_positions(inner) {
                    if commas.is_empty() {
                        cur = inner.trim();
                        continue;
                    }
                }
            }
        }
        break;
    }
    cur
}

fn split_top_level_tuple_elements(s: &str) -> Option<Vec<String>> {
    let trimmed = s.trim();
    let inner = if trimmed.starts_with('(') && trimmed.ends_with(')') && trimmed.len() >= 2 {
        &trimmed[1..trimmed.len() - 1]
    } else if trimmed.starts_with('⟨')
        && trimmed.ends_with('⟩')
        && trimmed.len() > '⟨'.len_utf8() + '⟩'.len_utf8()
    {
        &trimmed['⟨'.len_utf8()..trimmed.len() - '⟩'.len_utf8()]
    } else {
        return None;
    };
    let commas = find_top_level_tuple_comma_positions(inner)?;
    if commas.is_empty() {
        return None;
    }
    let mut parts = Vec::with_capacity(commas.len() + 1);
    let mut last = 0usize;
    for bp in commas {
        let seg = inner[last..bp].trim();
        if seg.is_empty() {
            return None;
        }
        parts.push(seg.to_string());
        last = bp + 1;
    }
    let tail = inner[last..].trim();
    if tail.is_empty() {
        return None;
    }
    parts.push(tail.to_string());
    Some(parts)
}

fn is_surface_open_binder_or_ctrl_at(s: &str, byte_pos: usize, prev_ch: Option<char>) -> bool {
    if prev_ch.is_some_and(is_ident_continue) {
        return false;
    }
    let rem = &s[byte_pos..];
    if rem.starts_with('∀') || rem.starts_with('∃') || rem.starts_with('λ') {
        return true;
    }
    for kw in ["forall", "exists", "fun", "let", "have", "match", "if"] {
        if let Some(after) = rem.strip_prefix(kw) {
            if after.chars().next().is_some_and(|ch| ch.is_whitespace() || matches!(ch, '(' | '{' | '[')) {
                return true;
            }
        }
    }
    false
}

pub(super) fn split_top_level_conjuncts(expr: &str) -> Vec<String> {
    let s = strip_balanced_outer_parens(expr);
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut last = 0usize;
    let chars: Vec<(usize, char)> = s.char_indices().collect();
    let mut idx = 0usize;
    while idx < chars.len() {
        let (byte_pos, c) = chars[idx];
        if c == '"' {
            idx += 1;
            while idx < chars.len() {
                let (_, sc) = chars[idx];
                idx += 1;
                if sc == '\\' && idx < chars.len() {
                    idx += 1;
                } else if sc == '"' {
                    break;
                }
            }
            continue;
        }
        let prev_ch = if idx > 0 { Some(chars[idx - 1].1) } else { None };
        if depth == 0 && is_surface_open_binder_or_ctrl_at(s, byte_pos, prev_ch) {
            break;
        }
        match c {
            '(' | '[' | '{' | '⟨' => depth += 1,
            ')' | ']' | '}' | '⟩' => depth = (depth - 1).max(0),
            '∧' if depth == 0 => {
                parts.push(s[last..byte_pos].trim().to_string());
                last = byte_pos + c.len_utf8();
            }
            '/' if depth == 0 && idx + 1 < chars.len() && chars[idx + 1].1 == '\\' => {
                parts.push(s[last..byte_pos].trim().to_string());
                last = chars[idx + 1].0 + chars[idx + 1].1.len_utf8();
                idx += 1;
            }
            _ => {}
        }
        idx += 1;
    }
    if last < s.len() {
        parts.push(s[last..].trim().to_string());
    }
    if parts.is_empty() {
        vec![s.to_string()]
    } else {
        parts
    }
}

pub(super) fn split_top_level_rel(expr: &str) -> Option<(String, String, &'static str)> {
    let chars: Vec<char> = expr.chars().collect();
    let n = chars.len();
    let (mut depth, mut i) = (0usize, 0usize);
    while i < n {
        if chars[i] == '"' {
            i += 1;
            while i < n {
                if chars[i] == '\\' && i + 1 < n {
                    i += 2;
                } else if chars[i] == '"' {
                    i += 1;
                    break;
                } else {
                    i += 1;
                }
            }
            continue;
        }
        if depth == 0 && crate::gpu_fastcheck::is_open_binder_or_ctrl_kw_at(&chars, i) {
            return None;
        }
        match chars[i] {
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth = depth.saturating_sub(1),
            '→' if depth == 0 => {
                let lhs: String = chars[..i].iter().collect();
                let rhs: String = chars[i + 1..].iter().collect();
                return Some((lhs.trim().to_string(), rhs.trim().to_string(), "→"));
            }
            '-' if depth == 0 && i + 1 < n && chars[i + 1] == '>' => {
                let lhs: String = chars[..i].iter().collect();
                let rhs: String = chars[i + 2..].iter().collect();
                return Some((lhs.trim().to_string(), rhs.trim().to_string(), "→"));
            }
            '≈' if depth == 0 => {
                let lhs: String = chars[..i].iter().collect();
                let rhs: String = chars[i + 1..].iter().collect();
                return Some((lhs.trim().to_string(), rhs.trim().to_string(), "≈"));
            }
            '↔' if depth == 0 => {
                let lhs: String = chars[..i].iter().collect();
                let rhs: String = chars[i + 1..].iter().collect();
                return Some((lhs.trim().to_string(), rhs.trim().to_string(), "↔"));
            }
            '<' if depth == 0 && i + 2 < n && chars[i + 1] == '-' && chars[i + 2] == '>' => {
                let lhs: String = chars[..i].iter().collect();
                let rhs: String = chars[i + 3..].iter().collect();
                return Some((lhs.trim().to_string(), rhs.trim().to_string(), "↔"));
            }
            '=' if depth == 0 => {
                let prev = if i > 0 { Some(chars[i - 1]) } else { None };
                let next = if i + 1 < n { Some(chars[i + 1]) } else { None };
                if matches!(prev, Some('!' | '<' | '>' | ':' | '=')) || matches!(next, Some('=' | '>')) {
                    i += 1;
                    continue;
                }
                let lhs: String = chars[..i].iter().collect();
                let rhs: String = chars[i + 1..].iter().collect();
                return Some((lhs.trim().to_string(), rhs.trim().to_string(), "="));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

pub(super) fn split_lean_app_args(rest: &str) -> Vec<String> {
    let mut args = Vec::new();
    let chars: Vec<char> = rest.trim().chars().collect();
    let n = chars.len();
    let mut i = 0usize;
    while i < n {
        while i < n && chars[i].is_whitespace() {
            i += 1;
        }
        if i >= n {
            break;
        }
        if matches!(chars[i], '(' | '{' | '[' | '⟨') {
            let open = chars[i];
            let close = match open {
                '(' => ')',
                '{' => '}',
                '[' => ']',
                _ => '⟩',
            };
            let start = i + 1;
            let mut depth = 1usize;
            i += 1;
            while i < n && depth > 0 {
                if chars[i] == '"' {
                    i += 1;
                    while i < n {
                        if chars[i] == '\\' && i + 1 < n {
                            i += 2;
                        } else if chars[i] == '"' {
                            i += 1;
                            break;
                        } else {
                            i += 1;
                        }
                    }
                    continue;
                }
                if chars[i] == open {
                    depth += 1;
                } else if chars[i] == close {
                    depth -= 1;
                }
                i += 1;
            }
            if i < n && chars[i] == '.' {
                while i < n {
                    if chars[i] == '"' {
                        i += 1;
                        while i < n {
                            if chars[i] == '\\' && i + 1 < n {
                                i += 2;
                            } else if chars[i] == '"' {
                                i += 1;
                                break;
                            } else {
                                i += 1;
                            }
                        }
                        continue;
                    }
                    if matches!(chars[i], '(' | '{' | '[' | '⟨') {
                        depth += 1;
                    } else if matches!(chars[i], ')' | '}' | ']' | '⟩') {
                        depth = depth.saturating_sub(1);
                    } else if depth == 0 && chars[i].is_whitespace() {
                        break;
                    }
                    i += 1;
                }
                let full_tok: String = chars[start.saturating_sub(1)..i].iter().collect();
                args.push(full_tok.trim().to_string());
            } else {
                let full_tok: String = chars[start.saturating_sub(1)..i].iter().collect();
                let trimmed_tok = full_tok.trim();
                if open == '('
                    && trimmed_tok != "()"
                    && split_top_level_tuple_elements(trimmed_tok).is_none()
                {
                    let unwrapped = strip_balanced_outer_parens(trimmed_tok);
                    args.push(unwrapped.to_string());
                } else {
                    args.push(trimmed_tok.to_string());
                }
            }
        } else {
            let start = i;
            let mut depth = 0usize;
            while i < n {
                if chars[i] == '"' {
                    i += 1;
                    while i < n {
                        if chars[i] == '\\' && i + 1 < n {
                            i += 2;
                        } else if chars[i] == '"' {
                            i += 1;
                            break;
                        } else {
                            i += 1;
                        }
                    }
                    continue;
                }
                if matches!(chars[i], '(' | '{' | '[' | '⟨') {
                    depth += 1;
                } else if matches!(chars[i], ')' | '}' | ']' | '⟩') {
                    depth = depth.saturating_sub(1);
                } else if depth == 0 && chars[i].is_whitespace() {
                    break;
                }
                i += 1;
            }
            let tok: String = chars[start..i].iter().collect();
            if !tok.is_empty() {
                args.push(tok);
            }
        }
    }
    args
}

fn unfold_binder_header_domains(hdr: &str, local_defs: &[(String, Vec<String>, String)]) -> String {
    let trimmed = hdr.trim();
    if trimmed.is_empty() {
        return String::new();
    }
    if let Some((vars_part, op, dom_part)) = split_top_level_binder_domain(trimmed) {
        let vp = vars_part.trim();
        let dp = dom_part.trim();
        if !vp.is_empty() && !dp.is_empty() {
            let u_dom = unfold_expr_single_step(dp, local_defs);
            if u_dom != dp {
                if op == ":" {
                    return format!("{} : {}", vp, u_dom);
                } else {
                    return format!("{} {} {}", vp, op, u_dom);
                }
            }
            return trimmed.to_string();
        }
    }
    let chars: Vec<char> = trimmed.chars().collect();
    let mut i = 0usize;
    let mut out = String::with_capacity(trimmed.len());
    let mut shadowed: Vec<String> = Vec::new();
    let mut changed = false;
    while i < chars.len() {
        if matches!(chars[i], '(' | '{' | '[') {
            let open = chars[i];
            let close = match open {
                '(' => ')',
                '{' => '}',
                _ => ']',
            };
            i += 1;
            let start = i;
            let mut depth = 1usize;
            while i < chars.len() && depth > 0 {
                if chars[i] == open {
                    depth += 1;
                } else if chars[i] == close {
                    depth -= 1;
                }
                i += 1;
            }
            let inner: String = chars[start..i.saturating_sub(1)].iter().collect();
            let cur_defs: Vec<(String, Vec<String>, String)> = local_defs
                .iter()
                .filter(|(dn, _, _)| {
                    let short = dn.rsplit('.').next().unwrap_or(dn.as_str());
                    !shadowed
                        .iter()
                        .any(|bv| bv == dn || bv == short || dn == &format!("__binder_ty:{}", bv))
                })
                .cloned()
                .collect();
            if open == '[' {
                let it = inner.trim();
                let u_in = unfold_expr_single_step(it, &cur_defs);
                if u_in != it {
                    changed = true;
                }
                out.push('[');
                out.push_str(&u_in);
                out.push(']');
            } else if let Some((vars_part, op, dom_part)) = split_top_level_binder_domain(&inner) {
                let vp = vars_part.trim();
                let dp = dom_part.trim();
                let u_dom = unfold_expr_single_step(dp, &cur_defs);
                if u_dom != dp {
                    changed = true;
                }
                for v in vp.split_whitespace() {
                    if !v.is_empty() && v != "_" {
                        shadowed.push(v.to_string());
                    }
                }
                out.push(open);
                out.push_str(vp);
                if op == ":" {
                    out.push_str(" : ");
                } else {
                    out.push(' ');
                    out.push_str(op);
                    out.push(' ');
                }
                out.push_str(&u_dom);
                out.push(close);
            } else {
                for v in inner.split_whitespace() {
                    if !v.is_empty() && v != "_" {
                        shadowed.push(v.to_string());
                    }
                }
                out.push(open);
                out.push_str(&inner);
                out.push(close);
            }
        } else {
            if is_ident_start(chars[i]) {
                let s = i;
                i += 1;
                while i < chars.len() && is_ident_continue(chars[i]) {
                    i += 1;
                }
                let id: String = chars[s..i].iter().collect();
                if id != "_" {
                    shadowed.push(id.clone());
                }
                out.push_str(&id);
            } else {
                out.push(chars[i]);
                i += 1;
            }
        }
    }
    if changed {
        out
    } else {
        trimmed.to_string()
    }
}

fn split_top_level_ite_branches(after_if: &str) -> Option<(&str, &str, &str)> {
    let chars: Vec<(usize, char)> = after_if.char_indices().collect();
    let match_kw_at = |slice: &str, cs: &[(usize, char)], idx: usize, kw: &str| -> bool {
        if idx > 0 {
            let prev = cs[idx - 1].1;
            if is_ident_continue(prev) || prev == '.' {
                return false;
            }
        }
        let bp = cs[idx].0;
        let Some(after) = slice[bp..].strip_prefix(kw) else {
            return false;
        };
        match after.chars().next() {
            None => true,
            Some(ch) => ch.is_whitespace() || matches!(ch, '(' | '{' | '[' | '⟨'),
        }
    };
    let mut depth = 0i32;
    let mut nested_if_then = 0usize;
    let mut then_bp = None;
    let mut i = 0usize;
    while i < chars.len() {
        let (bp, c) = chars[i];
        if c == '"' {
            i += 1;
            while i < chars.len() {
                let (_, sc) = chars[i];
                i += 1;
                if sc == '\\' && i < chars.len() {
                    i += 1;
                } else if sc == '"' {
                    break;
                }
            }
            continue;
        }
        match c {
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth = (depth - 1).max(0),
            _ if depth == 0 => {
                if match_kw_at(after_if, &chars, i, "if") {
                    nested_if_then += 1;
                    i += 2;
                    continue;
                } else if match_kw_at(after_if, &chars, i, "then") {
                    if nested_if_then == 0 {
                        then_bp = Some(bp);
                        break;
                    }
                    nested_if_then -= 1;
                    i += 4;
                    continue;
                }
            }
            _ => {}
        }
        i += 1;
    }
    let then_pos = then_bp?;
    let cond_str = after_if[..then_pos].trim();
    let after_then = after_if[then_pos + 4..].trim();
    let tchars: Vec<(usize, char)> = after_then.char_indices().collect();
    let mut tdepth = 0i32;
    let mut nested_if_else = 0usize;
    let mut else_bp = None;
    let mut ti = 0usize;
    while ti < tchars.len() {
        let (bp, c) = tchars[ti];
        if c == '"' {
            ti += 1;
            while ti < tchars.len() {
                let (_, sc) = tchars[ti];
                ti += 1;
                if sc == '\\' && ti < tchars.len() {
                    ti += 1;
                } else if sc == '"' {
                    break;
                }
            }
            continue;
        }
        match c {
            '(' | '{' | '[' | '⟨' => tdepth += 1,
            ')' | '}' | ']' | '⟩' => tdepth = (tdepth - 1).max(0),
            _ if tdepth == 0 => {
                if match_kw_at(after_then, &tchars, ti, "if") {
                    nested_if_else += 1;
                    ti += 2;
                    continue;
                } else if match_kw_at(after_then, &tchars, ti, "else") {
                    if nested_if_else == 0 {
                        else_bp = Some(bp);
                        break;
                    }
                    nested_if_else -= 1;
                    ti += 4;
                    continue;
                }
            }
            _ => {}
        }
        ti += 1;
    }
    let else_pos = else_bp?;
    let then_str = after_then[..else_pos].trim();
    let else_str = after_then[else_pos + 4..].trim();
    if cond_str.is_empty() || then_str.is_empty() || else_str.is_empty() {
        return None;
    }
    Some((cond_str, then_str, else_str))
}

pub(super) fn unfold_expr_single_step(expr: &str, local_defs: &[(String, Vec<String>, String)]) -> String {
    let mut inlined = inline_stmt_let_bindings(expr);
    for _ in 0..4 {
        let s = strip_balanced_outer_parens(&inlined);
        if s.starts_with("let ") || s.starts_with("have ") {
            let next = inline_stmt_let_bindings(s);
            if next != s {
                inlined = next;
                continue;
            }
        }
        break;
    }
    let trimmed = strip_balanced_outer_parens(&inlined);
    for (kw, delim) in [
        ("∀", ","),
        ("forall", ","),
        ("fun", "=>"),
        ("λ", "=>"),
        ("∃", ","),
        ("exists", ","),
    ] {
        if let Some(after_kw) = trimmed.strip_prefix(kw) {
            if after_kw
                .chars()
                .next()
                .is_some_and(|ch| ch.is_whitespace() || matches!(ch, '(' | '{' | '['))
            {
                if let Some(rel_delim) = find_top_level_delim(after_kw, delim) {
                    let hdr = after_kw[..rel_delim].trim();
                    let body = after_kw[rel_delim + delim.len()..].trim();
                    let u_hdr = unfold_binder_header_domains(hdr, local_defs);
                    let bvars = extract_binder_names_from_header(hdr);
                    let filtered_defs: Vec<(String, Vec<String>, String)> = local_defs
                        .iter()
                        .filter(|(dn, _, _)| {
                            let short = dn.rsplit('.').next().unwrap_or(dn.as_str());
                            !bvars
                                .iter()
                                .any(|bv| bv == dn || bv == short || dn == &format!("__binder_ty:{}", bv))
                        })
                        .cloned()
                        .collect();
                    let u_body = unfold_expr_single_step(body, &filtered_defs);
                    if u_hdr != hdr || u_body != body {
                        let sep = if delim == "," { ", " } else { " => " };
                        return format!("{} {}{}{}", kw, u_hdr, sep, u_body);
                    }
                    return trimmed.to_string();
                }
            }
        }
    }
    for let_kw in ["let ", "have "] {
        if let Some(after_let) = trimmed.strip_prefix(let_kw) {
            if let Some(assign_rel) = find_top_level_delim(after_let, ":=") {
                let lhs_hdr = after_let[..assign_rel].trim();
                let after_assign = &after_let[assign_rel + 2..];
                let sep_match = find_top_level_delim(after_assign, " in ")
                    .map(|p| (p, 4usize, " in "))
                    .or_else(|| find_top_level_delim(after_assign, ";").map(|p| (p, 1usize, "; ")))
                    .or_else(|| find_let_newline_sep(after_assign).map(|p| (p, 1usize, "; ")));
                if let Some((sep_rel, sep_len, out_sep)) = sep_match {
                    let val_part = after_assign[..sep_rel].trim();
                    let body_part = after_assign[sep_rel + sep_len..].trim();
                    if !val_part.is_empty() && !body_part.is_empty() {
                        let mut name_end = 0usize;
                        for (bi, ch) in lhs_hdr.char_indices() {
                            if ch.is_whitespace() || matches!(ch, '(' | '{' | '[' | ':') {
                                break;
                            }
                            name_end = bi + ch.len_utf8();
                        }
                        let let_name_slice = &lhs_hdr[..name_end];
                        let fn_params_slice = &lhs_hdr[name_end..];
                        let fn_bvars = extract_binder_names_from_header(fn_params_slice);
                        let val_defs: Vec<(String, Vec<String>, String)> = local_defs
                            .iter()
                            .filter(|(dn, _, _)| {
                                let short = dn.rsplit('.').next().unwrap_or(dn.as_str());
                                !fn_bvars
                                    .iter()
                                    .any(|bv| bv == dn || bv == short || dn == &format!("__binder_ty:{}", bv))
                            })
                            .cloned()
                            .collect();
                        let u_val = unfold_expr_single_step(val_part, &val_defs);
                        let pat_only = split_top_level_colon(lhs_hdr)
                            .map(|(l, _)| l.trim())
                            .unwrap_or(let_name_slice.trim());
                        let body_bvars = extract_pattern_bound_vars(pat_only);
                        let body_defs: Vec<(String, Vec<String>, String)> = local_defs
                            .iter()
                            .filter(|(dn, _, _)| {
                                let short = dn.rsplit('.').next().unwrap_or(dn.as_str());
                                !body_bvars
                                    .iter()
                                    .any(|bv| bv == dn || bv == short || dn == &format!("__binder_ty:{}", bv))
                            })
                            .cloned()
                            .collect();
                        let u_body = unfold_expr_single_step(body_part, &body_defs);
                        if u_val != val_part || u_body != body_part {
                            let fmt_val = if u_val.starts_with("let ")
                                || u_val.starts_with("have ")
                                || u_val.starts_with("match ")
                            {
                                format!("({})", u_val)
                            } else {
                                u_val
                            };
                            return format!("{}{} := {}{}{}", let_kw, lhs_hdr, fmt_val, out_sep, u_body);
                        }
                        return trimmed.to_string();
                    }
                }
            }
        }
    }
    if let Some(after_if) = trimmed.strip_prefix("if ") {
        if let Some((cond_str, then_str, else_str)) = split_top_level_ite_branches(after_if) {
            let u_c = unfold_expr_single_step(cond_str, local_defs);
            let u_t = unfold_expr_single_step(then_str, local_defs);
            let u_e = unfold_expr_single_step(else_str, local_defs);
            if u_c != cond_str || u_t != then_str || u_e != else_str {
                let wrap_if_branch = |s: String| -> String {
                    if is_surface_open_binder_or_ctrl_at(&s, 0, None) && !s.starts_with("if ") {
                        format!("({})", s)
                    } else {
                        s
                    }
                };
                let fmt_c = if is_surface_open_binder_or_ctrl_at(&u_c, 0, None) {
                    format!("({})", u_c)
                } else {
                    u_c
                };
                return format!(
                    "if {} then {} else {}",
                    fmt_c,
                    wrap_if_branch(u_t),
                    wrap_if_branch(u_e)
                );
            }
            return trimmed.to_string();
        }
    }
    if let Some(after_match) = trimmed.strip_prefix("match ") {
        if let Some(with_pos) = find_top_level_delim(after_match, "with") {
            let scrut_str = after_match[..with_pos].trim();
            let arms_str = after_match[with_pos + 4..].trim();
            if !scrut_str.is_empty() && !arms_str.is_empty() {
                let wrap_scrut = |s: String| -> String {
                    if is_surface_open_binder_or_ctrl_at(&s, 0, None) {
                        format!("({})", s)
                    } else {
                        s
                    }
                };
                let (u_scrut, mut any_changed) =
                    if let Some(commas) = find_top_level_tuple_comma_positions(scrut_str) {
                        if !commas.is_empty() {
                            let mut parts = Vec::with_capacity(commas.len() + 1);
                            let mut chg = false;
                            let mut last = 0usize;
                            for bp in commas {
                                let seg = scrut_str[last..bp].trim();
                                let u_seg = unfold_expr_single_step(seg, local_defs);
                                if u_seg != seg {
                                    chg = true;
                                }
                                parts.push(wrap_scrut(u_seg));
                                last = bp + 1;
                            }
                            let tail = scrut_str[last..].trim();
                            let u_tail = unfold_expr_single_step(tail, local_defs);
                            if u_tail != tail {
                                chg = true;
                            }
                            parts.push(wrap_scrut(u_tail));
                            (parts.join(", "), chg)
                        } else {
                            let us = unfold_expr_single_step(scrut_str, local_defs);
                            let chg = us != scrut_str;
                            (wrap_scrut(us), chg)
                        }
                    } else {
                        let us = unfold_expr_single_step(scrut_str, local_defs);
                        let chg = us != scrut_str;
                        (wrap_scrut(us), chg)
                    };
                let mut out_arms = Vec::new();
                let chars: Vec<(usize, char)> = arms_str.char_indices().collect();
                let mut idx = 0usize;
                while idx < chars.len() {
                    let (bp, _) = chars[idx];
                    if is_match_arm_bar_at(&chars, idx) {
                        let arm_start = bp + 1;
                        let mut arm_end = arms_str.len();
                        let mut next_idx = chars.len();
                        let mut depth = 0i32;
                        let mut scan = idx + 1;
                        while scan < chars.len() {
                            let (s_bp, s_ch) = chars[scan];
                            if s_ch == '"' {
                                scan += 1;
                                while scan < chars.len() {
                                    let (_, sc) = chars[scan];
                                    scan += 1;
                                    if sc == '\\' && scan < chars.len() {
                                        scan += 1;
                                    } else if sc == '"' {
                                        break;
                                    }
                                }
                                continue;
                            }
                            match s_ch {
                                '(' | '{' | '[' | '⟨' => depth += 1,
                                ')' | '}' | ']' | '⟩' => depth = (depth - 1).max(0),
                                '|' if depth == 0 && is_match_arm_bar_at(&chars, scan) => {
                                    arm_end = s_bp;
                                    next_idx = scan;
                                    break;
                                }
                                _ => {}
                            }
                            scan += 1;
                        }
                        let arm_slice = arms_str[arm_start..arm_end].trim();
                        if let Some(arrow_pos) = find_top_level_delim(arm_slice, "=>") {
                            let pat_raw = arm_slice[..arrow_pos].trim();
                            let rhs_raw = arm_slice[arrow_pos + 2..].trim();
                            let pvars = extract_pattern_bound_vars(pat_raw);
                            let filtered_defs: Vec<(String, Vec<String>, String)> = local_defs
                                .iter()
                                .filter(|(dn, _, _)| {
                                    let short = dn.rsplit('.').next().unwrap_or(dn.as_str());
                                    !pvars.iter().any(|pv| {
                                        pv == dn || pv == short || dn == &format!("__binder_ty:{}", pv)
                                    })
                                })
                                .cloned()
                                .collect();
                            let u_rhs = unfold_expr_single_step(rhs_raw, &filtered_defs);
                            if u_rhs != rhs_raw {
                                any_changed = true;
                            }
                            let fmt_rhs = if u_rhs.starts_with("match ") {
                                format!("({})", u_rhs)
                            } else {
                                u_rhs
                            };
                            out_arms.push(format!("| {} => {}", pat_raw, fmt_rhs));
                        } else {
                            out_arms.push(format!("| {}", arm_slice));
                        }
                        idx = next_idx;
                        continue;
                    }
                    idx += 1;
                }
                if any_changed && !out_arms.is_empty() {
                    return format!("match {} with {}", u_scrut, out_arms.join(" "));
                }
                return trimmed.to_string();
            }
        }
    }
    for iff_op in ["↔", "<->"] {
        if let Some(pos) = find_top_level_delim(trimmed, iff_op) {
            let lhs = trimmed[..pos].trim();
            let rhs = trimmed[pos + iff_op.len()..].trim();
            if !lhs.is_empty() && !rhs.is_empty() {
                let u_lhs = unfold_expr_single_step(lhs, local_defs);
                let u_rhs = unfold_expr_single_step(rhs, local_defs);
                if u_lhs != lhs || u_rhs != rhs {
                    let wrap_iff = |s: String| -> String {
                        if is_surface_open_binder_or_ctrl_at(&s, 0, None)
                            || split_top_level_conjuncts(&s).len() > 1
                            || split_top_level_implications(&s).len() > 1
                            || find_top_level_delim(&s, "∨").is_some()
                            || find_top_level_delim(&s, "↔").is_some()
                            || find_top_level_delim(&s, "<->").is_some()
                        {
                            format!("({})", s)
                        } else {
                            s
                        }
                    };
                    return format!("{} ↔ {}", wrap_iff(u_lhs), wrap_iff(u_rhs));
                }
                return trimmed.to_string();
            }
        }
    }
    let imp_segs = split_top_level_implications(trimmed);
    if imp_segs.len() > 1 {
        let last_idx = imp_segs.len() - 1;
        let mut any_changed = false;
        let mut fmt_segs = Vec::with_capacity(imp_segs.len());
        for (idx, seg) in imp_segs.into_iter().enumerate() {
            let u_seg = unfold_expr_single_step(&seg, local_defs);
            if u_seg != seg.trim() && u_seg != strip_balanced_outer_parens(&seg) {
                any_changed = true;
            }
            if (idx < last_idx
                && (split_top_level_implications(&u_seg).len() > 1
                    || is_surface_open_binder_or_ctrl_at(&u_seg, 0, None)))
                || find_top_level_delim(&u_seg, "↔").is_some()
                || find_top_level_delim(&u_seg, "<->").is_some()
            {
                fmt_segs.push(format!("({})", u_seg));
            } else {
                fmt_segs.push(u_seg);
            }
        }
        if any_changed {
            return fmt_segs.join(" → ");
        }
        return trimmed.to_string();
    }
    if let Some(pos) = find_top_level_delim(trimmed, "∨") {
        let lhs = trimmed[..pos].trim();
        let rhs = trimmed[pos + "∨".len()..].trim();
        if !lhs.is_empty() && !rhs.is_empty() {
            let u_lhs = unfold_expr_single_step(lhs, local_defs);
            let u_rhs = unfold_expr_single_step(rhs, local_defs);
            if u_lhs != lhs && u_lhs != strip_balanced_outer_parens(lhs)
                || u_rhs != rhs && u_rhs != strip_balanced_outer_parens(rhs)
            {
                let wrap_or = |s: String| -> String {
                    if is_surface_open_binder_or_ctrl_at(&s, 0, None)
                        || split_top_level_conjuncts(&s).len() > 1
                        || split_top_level_implications(&s).len() > 1
                        || find_top_level_delim(&s, "∨").is_some()
                        || find_top_level_delim(&s, "↔").is_some()
                        || find_top_level_delim(&s, "<->").is_some()
                    {
                        format!("({})", s)
                    } else {
                        s
                    }
                };
                return format!("{} ∨ {}", wrap_or(u_lhs), wrap_or(u_rhs));
            }
            return trimmed.to_string();
        }
    }
    let conjuncts = split_top_level_conjuncts(trimmed);
    if conjuncts.len() > 1 {
        let mut any_changed = false;
        let mut fmt_conjs = Vec::with_capacity(conjuncts.len());
        for c in conjuncts {
            let u_c = unfold_expr_single_step(&c, local_defs);
            if u_c != c.trim() && u_c != strip_balanced_outer_parens(&c) {
                any_changed = true;
            }
            if is_surface_open_binder_or_ctrl_at(&u_c, 0, None)
                || split_top_level_conjuncts(&u_c).len() > 1
                || split_top_level_implications(&u_c).len() > 1
                || find_top_level_delim(&u_c, "↔").is_some()
                || find_top_level_delim(&u_c, "<->").is_some()
                || find_top_level_delim(&u_c, "∨").is_some()
            {
                fmt_conjs.push(format!("({})", u_c));
            } else {
                fmt_conjs.push(u_c);
            }
        }
        if any_changed {
            return fmt_conjs.join(" ∧ ");
        }
        return trimmed.to_string();
    }
    if let Some((lhs, rhs, is_ne)) = split_top_level_eq(trimmed) {
        let u_lhs = unfold_expr_single_step(&lhs, local_defs);
        let u_rhs = unfold_expr_single_step(&rhs, local_defs);
        if (u_lhs != lhs.trim() && u_lhs != strip_balanced_outer_parens(&lhs))
            || (u_rhs != rhs.trim() && u_rhs != strip_balanced_outer_parens(&rhs))
        {
            let wrap_eq_side = |s: String| -> String {
                if is_surface_open_binder_or_ctrl_at(&s, 0, None)
                    || split_top_level_eq(&s).is_some()
                    || find_top_level_delim(&s, "||").is_some()
                    || find_top_level_delim(&s, "&&").is_some()
                    || split_top_level_conjuncts(&s).len() > 1
                    || split_top_level_implications(&s).len() > 1
                    || find_top_level_delim(&s, "∨").is_some()
                    || find_top_level_delim(&s, "↔").is_some()
                    || find_top_level_delim(&s, "<->").is_some()
                {
                    format!("({})", s)
                } else {
                    s
                }
            };
            let eq_op = if !is_ne {
                "="
            } else if find_top_level_delim(trimmed, "≠").is_some() {
                "≠"
            } else {
                "!="
            };
            return format!("{} {} {}", wrap_eq_side(u_lhs), eq_op, wrap_eq_side(u_rhs));
        }
        return trimmed.to_string();
    }
    if let Some((lhs, rhs, op)) = split_top_level_rel(trimmed) {
        let u_lhs = unfold_expr_single_step(&lhs, local_defs);
        let u_rhs = unfold_expr_single_step(&rhs, local_defs);
        if (u_lhs != lhs.trim() && u_lhs != strip_balanced_outer_parens(&lhs))
            || (u_rhs != rhs.trim() && u_rhs != strip_balanced_outer_parens(&rhs))
        {
            let wrap_rel_side = |s: String| -> String {
                if is_surface_open_binder_or_ctrl_at(&s, 0, None)
                    || split_top_level_eq(&s).is_some()
                    || split_top_level_conjuncts(&s).len() > 1
                    || split_top_level_implications(&s).len() > 1
                    || find_top_level_delim(&s, "∨").is_some()
                    || find_top_level_delim(&s, "↔").is_some()
                {
                    format!("({})", s)
                } else {
                    s
                }
            };
            return format!("{} {} {}", wrap_rel_side(u_lhs), op, wrap_rel_side(u_rhs));
        }
        return trimmed.to_string();
    }
    for bool_op in ["||", "&&"] {
        if let Some(pos) = find_top_level_delim(trimmed, bool_op) {
            let lhs = trimmed[..pos].trim();
            let rhs = trimmed[pos + bool_op.len()..].trim();
            if !lhs.is_empty() && !rhs.is_empty() {
                let u_lhs = unfold_expr_single_step(lhs, local_defs);
                let u_rhs = unfold_expr_single_step(rhs, local_defs);
                if (u_lhs != lhs && u_lhs != strip_balanced_outer_parens(lhs))
                    || (u_rhs != rhs && u_rhs != strip_balanced_outer_parens(rhs))
                {
                    let wrap_b = |s: String| -> String {
                        if is_surface_open_binder_or_ctrl_at(&s, 0, None)
                            || find_top_level_delim(&s, "||").is_some()
                            || find_top_level_delim(&s, "&&").is_some()
                            || split_top_level_eq(&s).is_some()
                            || split_top_level_conjuncts(&s).len() > 1
                            || split_top_level_implications(&s).len() > 1
                            || find_top_level_delim(&s, "∨").is_some()
                            || find_top_level_delim(&s, "↔").is_some()
                        {
                            format!("({})", s)
                        } else {
                            s
                        }
                    };
                    return format!("{} {} {}", wrap_b(u_lhs), bool_op, wrap_b(u_rhs));
                }
                return trimmed.to_string();
            }
        }
    }
    const CMP_OPS: [&str; 12] = ["==", "!=", "<=", "≤", ">=", "≥", "<", ">", "∈", "∉", "⊆", "⊂"];
    for cmp_op in CMP_OPS {
        if let Some(pos) = find_top_level_delim(trimmed, cmp_op) {
            let lhs = trimmed[..pos].trim();
            let rhs = trimmed[pos + cmp_op.len()..].trim();
            if !lhs.is_empty() && !rhs.is_empty() {
                let u_lhs = unfold_expr_single_step(lhs, local_defs);
                let u_rhs = unfold_expr_single_step(rhs, local_defs);
                if (u_lhs != lhs && u_lhs != strip_balanced_outer_parens(lhs))
                    || (u_rhs != rhs && u_rhs != strip_balanced_outer_parens(rhs))
                {
                    let wrap_cmp = |s: String| -> String {
                        let has_sub_cmp = CMP_OPS
                            .iter()
                            .any(|op| find_top_level_delim(&s, op).is_some());
                        if is_surface_open_binder_or_ctrl_at(&s, 0, None)
                            || has_sub_cmp
                            || find_top_level_delim(&s, "||").is_some()
                            || find_top_level_delim(&s, "&&").is_some()
                            || split_top_level_eq(&s).is_some()
                            || split_top_level_conjuncts(&s).len() > 1
                            || split_top_level_implications(&s).len() > 1
                            || find_top_level_delim(&s, "∨").is_some()
                            || find_top_level_delim(&s, "↔").is_some()
                        {
                            format!("({})", s)
                        } else {
                            s
                        }
                    };
                    return format!("{} {} {}", wrap_cmp(u_lhs), cmp_op, wrap_cmp(u_rhs));
                }
                return trimmed.to_string();
            }
        }
    }
    for neg_pfx in ["!", "¬"] {
        if let Some(neg_inner) = trimmed.strip_prefix(neg_pfx) {
            let inner_trim = neg_inner.trim();
            if !inner_trim.is_empty() && !inner_trim.starts_with('=') {
                let u_in = unfold_expr_single_step(inner_trim, local_defs);
                if u_in != inner_trim && u_in != strip_balanced_outer_parens(inner_trim) {
                    if needs_parens_as_atom(&u_in) {
                        return format!("{}({})", neg_pfx, u_in);
                    }
                    return format!("{}{}", neg_pfx, u_in);
                }
                return trimmed.to_string();
            }
        }
    }
    let last_pipe_dot = rfind_top_level_delim(trimmed, "|>.").map(|p| (p, "|>."));
    let last_pipe = rfind_top_level_delim(trimmed, "|>").map(|p| (p, "|>"));
    let chosen_pipe = match (last_pipe_dot, last_pipe) {
        (Some(a), Some(b)) => {
            if a.0 >= b.0 {
                Some(a)
            } else {
                Some(b)
            }
        }
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        (None, None) => None,
    };
    if let Some((pos, pipe_op)) = chosen_pipe {
        let lhs = trimmed[..pos].trim();
        let rhs = trimmed[pos + pipe_op.len()..].trim();
        if !lhs.is_empty() && !rhs.is_empty() {
            let u_lhs = unfold_expr_single_step(lhs, local_defs);
            let mut rhs_changed = false;
            let u_rhs = if pipe_op == "|>." {
                let m_toks = split_lean_app_args(rhs);
                if m_toks.len() > 1 {
                    let mut m_out = Vec::with_capacity(m_toks.len());
                    m_out.push(m_toks[0].trim().to_string());
                    for ma in &m_toks[1..] {
                        let uma = unfold_expr_single_step(ma, local_defs);
                        if &uma != ma && uma != strip_balanced_outer_parens(ma) {
                            rhs_changed = true;
                        }
                        if needs_parens_as_atom(&uma) {
                            m_out.push(format!("({})", uma));
                        } else {
                            m_out.push(uma);
                        }
                    }
                    m_out.join(" ")
                } else {
                    rhs.to_string()
                }
            } else {
                let ur = unfold_expr_single_step(rhs, local_defs);
                if ur != rhs && ur != strip_balanced_outer_parens(rhs) {
                    rhs_changed = true;
                }
                ur
            };
            if (u_lhs != lhs && u_lhs != strip_balanced_outer_parens(lhs)) || rhs_changed {
                let wrap_l = if needs_parens_as_atom(&u_lhs) {
                    format!("({})", u_lhs)
                } else {
                    u_lhs
                };
                let wrap_r = if pipe_op == "|>" && needs_parens_as_atom(&u_rhs) {
                    format!("({})", u_rhs)
                } else {
                    u_rhs
                };
                let sep = if pipe_op == "|>." { " |>." } else { " |> " };
                return format!("{}{}{}", wrap_l, sep, wrap_r);
            }
            return trimmed.to_string();
        }
    }
    const SEQ_OPS: [&str; 13] = [
        "<|>", "++", "::", "|||", "^^^", "&&&", "<<<", ">>>", "+", "-", "*", "/", "%",
    ];
    for seq_op in SEQ_OPS {
        if let Some(pos) = find_top_level_delim(trimmed, seq_op) {
            let lhs = trimmed[..pos].trim();
            let rhs = trimmed[pos + seq_op.len()..].trim();
            if !lhs.is_empty() && !rhs.is_empty() {
                let u_lhs = unfold_expr_single_step(lhs, local_defs);
                let u_rhs = unfold_expr_single_step(rhs, local_defs);
                if (u_lhs != lhs && u_lhs != strip_balanced_outer_parens(lhs))
                    || (u_rhs != rhs && u_rhs != strip_balanced_outer_parens(rhs))
                {
                    let wrap_s = |s: String| -> String {
                        let has_sub_op = SEQ_OPS
                            .iter()
                            .chain(["||", "&&", "==", "!=", "≠", "=", "→", "->", "|>", "|>."].iter())
                            .any(|op| find_top_level_delim(&s, op).is_some());
                        if is_surface_open_binder_or_ctrl_at(&s, 0, None) || has_sub_op {
                            format!("({})", s)
                        } else {
                            s
                        }
                    };
                    return format!("{} {} {}", wrap_s(u_lhs), seq_op, wrap_s(u_rhs));
                }
                return trimmed.to_string();
            }
        }
    }
    if (trimmed.starts_with('[') && trimmed.ends_with(']') && trimmed.len() >= 2)
        || (trimmed.starts_with("#[") && trimmed.ends_with(']') && trimmed.len() >= 3)
    {
        let is_arr = trimmed.starts_with("#[");
        let open_s = if is_arr { "#[" } else { "[" };
        let inner = if is_arr {
            trimmed[2..trimmed.len() - 1].trim()
        } else {
            trimmed[1..trimmed.len() - 1].trim()
        };
        if !inner.is_empty() {
            let tuple_probe = format!("({})", inner);
            if let Some(elems) = split_top_level_tuple_elements(&tuple_probe) {
                let mut any_changed = false;
                let mut u_elems = Vec::with_capacity(elems.len());
                for el in &elems {
                    let u_el = unfold_expr_single_step(el, local_defs);
                    if &u_el != el && u_el != strip_balanced_outer_parens(el) {
                        any_changed = true;
                    }
                    u_elems.push(u_el);
                }
                if any_changed {
                    return format!("{}{}]", open_s, u_elems.join(", "));
                }
            } else {
                let u_in = unfold_expr_single_step(inner, local_defs);
                if u_in != inner && u_in != strip_balanced_outer_parens(inner) {
                    return format!("{}{}]", open_s, u_in);
                }
            }
        }
        return trimmed.to_string();
    }
    if let Some(elems) = split_top_level_tuple_elements(trimmed) {
        let mut any_changed = false;
        let mut u_elems = Vec::with_capacity(elems.len());
        for el in &elems {
            let u_el = unfold_expr_single_step(el, local_defs);
            if &u_el != el && u_el != strip_balanced_outer_parens(el) {
                any_changed = true;
            }
            u_elems.push(u_el);
        }
        if any_changed {
            let (open_ch, close_ch) = if trimmed.starts_with('⟨') {
                ('⟨', '⟩')
            } else {
                ('(', ')')
            };
            return format!("{}{}{}", open_ch, u_elems.join(", "), close_ch);
        }
        return trimmed.to_string();
    }
    if let Some(comp_inner) = trimmed.strip_prefix("~~~") {
        let inner_trim = comp_inner.trim();
        if !inner_trim.is_empty() {
            let u_in = unfold_expr_single_step(inner_trim, local_defs);
            if u_in != inner_trim && u_in != strip_balanced_outer_parens(inner_trim) {
                if needs_parens_as_atom(&u_in) {
                    return format!("~~~({})", u_in);
                }
                return format!("~~~{}", u_in);
            }
            return trimmed.to_string();
        }
    }
    for ok_pfx in [
        ".ok ",
        ".ok(",
        "Except.ok ",
        "Except.ok(",
        "Option.some ",
        "Option.some(",
        "some ",
        "some(",
    ] {
        if let Some(inner) = trimmed.strip_prefix(ok_pfx) {
            let head_kw = ok_pfx.trim().trim_end_matches('(');
            let reconstructed = if ok_pfx.ends_with('(') {
                format!("({}", inner)
            } else {
                inner.trim().to_string()
            };
            let rest_args = split_lean_app_args(&reconstructed);
            if rest_args.len() == 1 {
                let clean_inner = strip_balanced_outer_parens(&reconstructed);
                let u_inner = unfold_expr_single_step(clean_inner, local_defs);
                if u_inner != clean_inner {
                    if needs_parens_as_atom(&u_inner) {
                        return format!("{} ({})", head_kw, u_inner);
                    }
                    return format!("{} {}", head_kw, u_inner);
                }
                return trimmed.to_string();
            }
        }
    }
    let mut binder_types = std::collections::HashMap::new();
    for (dn, _, b_ty) in local_defs {
        if let Some(b_name) = dn.strip_prefix("__binder_ty:") {
            binder_types.insert(b_name.to_string(), b_ty.clone());
        }
    }
    for (def_name, params, body) in local_defs {
        if def_name.starts_with("__binder_ty:") {
            continue;
        }
        let short = def_name.rsplit('.').next().unwrap_or(def_name.as_str());
        if body.len() > 4096
            || replace_ident_boundary(body, short, "__SELF__") != *body
            || replace_ident_boundary(body, def_name, "__SELF__") != *body
        {
            continue;
        }
        for cand in [def_name.as_str(), short] {
            if params.is_empty() && trimmed == cand {
                return body.clone();
            }
            if let Some(rest) = trimmed.strip_prefix(cand) {
                if rest.starts_with(char::is_whitespace) || rest.starts_with('(') {
                    let args = split_lean_app_args(rest);
                    if params.is_empty() && !args.is_empty() {
                        if cand == short
                            && def_name.contains('.')
                            && is_ambiguous_prelude_short_name(short)
                        {
                            continue;
                        }
                        let b_clean = strip_balanced_outer_parens(body);
                        let is_non_fn_val = b_clean.starts_with('{')
                            || b_clean.starts_with('⟨')
                            || b_clean.starts_with('[')
                            || b_clean.starts_with("#[")
                            || b_clean.starts_with('"')
                            || b_clean.chars().next().is_some_and(|c| c.is_ascii_digit())
                            || matches!(b_clean, "true" | "false" | "True" | "False" | "()")
                            || split_top_level_tuple_elements(body).is_some();
                        if is_non_fn_val {
                            continue;
                        }
                        let u_args: Vec<String> = args
                            .iter()
                            .map(|a| {
                                let ua = unfold_expr_single_step(a, local_defs);
                                if needs_parens_as_atom(&ua) {
                                    format!("({})", ua)
                                } else {
                                    ua
                                }
                            })
                            .collect();
                        let fmt_body = if needs_parens_as_atom(body) {
                            format!("({})", body)
                        } else {
                            body.clone()
                        };
                        return format!("{} {}", fmt_body, u_args.join(" "));
                    }
                    if args.len() >= params.len() && !params.is_empty() {
                        if args.len() > params.len()
                            && local_defs.iter().any(|(dn2, ps2, _)| {
                                ps2.len() == args.len()
                                    && (dn2 == def_name
                                        || dn2.rsplit('.').next().unwrap_or(dn2.as_str()) == short)
                                    && infer_implicit_subst_from_call_args(ps2, &args, &binder_types)
                                        .is_some()
                            })
                        {
                            continue;
                        }
                        let (call_args, extra_args) = args.split_at(params.len());
                        let Some(imp_subst) =
                            infer_implicit_subst_from_call_args(params, call_args, &binder_types)
                        else {
                            continue;
                        };
                        let u_args: Vec<String> = call_args
                            .iter()
                            .map(|a| unfold_expr_single_step(a, local_defs))
                            .collect();
                        let mut all_idents = std::collections::HashSet::new();
                        for id in extract_expr_identifiers(body) {
                            all_idents.insert(id);
                        }
                        let mut subst_map =
                            std::collections::HashMap::with_capacity(params.len() + imp_subst.len());
                        for (imp_k, imp_v) in imp_subst {
                            all_idents.insert(imp_k.clone());
                            for id in extract_expr_identifiers(&imp_v) {
                                all_idents.insert(id);
                            }
                            let rep = if needs_parens_as_atom(&imp_v) {
                                format!("({})", imp_v)
                            } else {
                                imp_v
                            };
                            subst_map.insert(imp_k, rep);
                        }
                        for (p, u_arg) in params.iter().zip(u_args.into_iter()) {
                            let pt = p
                                .split('@')
                                .next()
                                .unwrap_or(p.as_str())
                                .trim()
                                .to_string();
                            all_idents.insert(pt.clone());
                            for id in extract_expr_identifiers(&u_arg) {
                                all_idents.insert(id);
                            }
                            let rep = if needs_parens_as_atom(&u_arg) {
                                format!("({})", u_arg)
                            } else {
                                u_arg
                            };
                            subst_map.insert(pt, rep);
                        }
                        let base_res = subst_lean_expr_scoped(body, &subst_map, &mut all_idents);
                        if extra_args.is_empty() {
                            return base_res;
                        }
                        let fmt_extra: Vec<String> = extra_args
                            .iter()
                            .map(|a| {
                                let ua = unfold_expr_single_step(a, local_defs);
                                if needs_parens_as_atom(&ua) {
                                    format!("({})", ua)
                                } else {
                                    ua
                                }
                            })
                            .collect();
                        return format!("({}) {}", base_res, fmt_extra.join(" "));
                    }
                }
            }
        }
    }
    if !has_unbracketed_whitespace_or_op(trimmed) {
        if let Some((base, field)) = trimmed.rsplit_once('.') {
            let base_trim = base.trim();
            let is_compound = !has_unbracketed_whitespace_or_op(base_trim)
                && ((base_trim.starts_with('(') && base_trim.ends_with(')'))
                    || (base_trim.starts_with('[') && base_trim.ends_with(']'))
                    || (base_trim.starts_with("#[") && base_trim.ends_with(']'))
                    || (base_trim.starts_with('{') && base_trim.ends_with('}'))
                    || (base_trim.starts_with('⟨') && base_trim.ends_with('⟩'))
                    || base_trim.contains(')')
                    || base_trim.contains(']')
                    || base_trim.contains('}')
                    || base_trim.contains('⟩')
                    || base_trim.contains('#'));
            if !base_trim.is_empty()
                && !field.is_empty()
                && !field.contains(char::is_whitespace)
                && field
                    .chars()
                    .all(|c| is_ident_continue(c) || c == '?' || c == '!' || c.is_ascii_digit())
                && (is_compound
                    || local_defs.iter().any(|(dn, ps, _)| {
                        ps.is_empty()
                            && (dn == base_trim
                                || dn.rsplit('.').next().unwrap_or(dn.as_str()) == base_trim)
                    }))
            {
                let u_base = unfold_expr_single_step(base_trim, local_defs);
                if u_base != base_trim && u_base != strip_balanced_outer_parens(base_trim) {
                    let wrap_b = if needs_parens_as_proj_base(&u_base) {
                        format!("({})", u_base)
                    } else {
                        u_base
                    };
                    return format!("{}.{}", wrap_b, field);
                }
            }
        }
    }
    let app_tokens = split_lean_app_args(trimmed);
    if app_tokens.len() > 1 {
        let head = app_tokens[0].trim();
        let args = &app_tokens[1..];
        let is_compound_fn_head = head.starts_with('(')
            || head.starts_with('[')
            || head.starts_with("#[")
            || head.starts_with('{')
            || head.starts_with('⟨')
            || (head.contains('.') && !has_unbracketed_whitespace_or_op(head));
        let is_valid_fn_head = !head.is_empty()
            && ((head.chars().next().is_some_and(|c| is_ident_start(c) || c == '.')
                && head.chars().all(|c| is_ident_continue(c) || c == '.' || c == '?' || c == '!'))
                || is_compound_fn_head)
            && !matches!(
                head,
                "fun" | "λ" | "if" | "match" | "let" | "have" | "∀" | "forall" | "∃" | "exists" | "by" | "do"
            );
        if is_valid_fn_head && !args.is_empty() {
            let u_head = if is_compound_fn_head
                || local_defs.iter().any(|(dn, ps, _)| {
                    ps.is_empty()
                        && (dn == head
                            || (dn.rsplit('.').next().unwrap_or(dn.as_str()) == head
                                && !is_ambiguous_prelude_short_name(head)))
                })
            {
                unfold_expr_single_step(head, local_defs)
            } else {
                head.to_string()
            };
            let mut any_changed = u_head != head && u_head != strip_balanced_outer_parens(head);
            let mut u_args = Vec::with_capacity(args.len());
            for a in args {
                let ua = unfold_expr_single_step(a, local_defs);
                if &ua != a && ua != strip_balanced_outer_parens(a) {
                    any_changed = true;
                }
                if needs_parens_as_atom(&ua) {
                    u_args.push(format!("({})", ua));
                } else {
                    u_args.push(ua);
                }
            }
            if head.starts_with('(') || u_head.starts_with("fun ") || u_head.starts_with("λ ") {
                let stripped_head = strip_balanced_outer_parens(&u_head);
                if let Some(after_fun) = stripped_head
                    .strip_prefix("fun ")
                    .or_else(|| stripped_head.strip_prefix("λ "))
                {
                    if let Some(rel_arrow) = find_top_level_delim(after_fun, "=>") {
                        let hdr = after_fun[..rel_arrow].trim();
                        let lam_body = after_fun[rel_arrow + 2..].trim();
                        let bvars = extract_binder_names_from_header(hdr);
                        if !bvars.is_empty() && args.len() >= bvars.len() {
                            let mut all_idents = std::collections::HashSet::new();
                            for id in extract_expr_identifiers(lam_body) {
                                all_idents.insert(id);
                            }
                            let mut subst_map = std::collections::HashMap::with_capacity(bvars.len());
                            for (bv, a_raw) in bvars.iter().zip(args.iter()) {
                                let ua = unfold_expr_single_step(a_raw, local_defs);
                                all_idents.insert(bv.clone());
                                for id in extract_expr_identifiers(&ua) {
                                    all_idents.insert(id);
                                }
                                let rep = if needs_parens_as_atom(&ua) {
                                    format!("({})", ua)
                                } else {
                                    ua
                                };
                                subst_map.insert(bv.clone(), rep);
                            }
                            let applied = subst_lean_expr_scoped(lam_body, &subst_map, &mut all_idents);
                            if args.len() == bvars.len() {
                                return applied;
                            }
                            return format!("({}) {}", applied, u_args[bvars.len()..].join(" "));
                        }
                    }
                }
            }
            if any_changed {
                let fmt_head = if needs_parens_as_atom(&u_head) {
                    format!("({})", u_head)
                } else {
                    u_head
                };
                return format!("{} {}", fmt_head, u_args.join(" "));
            }
        }
    }
    trimmed.to_string()
}

/// Transitive fixed-point delta unfolder (up to 16 hops with cycle detection) so multi-hop
/// local `def`/`abbrev` wrappers cannot hide vacuous preconditions or trivial postconditions.
pub(super) fn unfold_expr_one_level(expr: &str, local_defs: &[(String, Vec<String>, String)]) -> String {
    let mut cur = expr.trim().to_string();
    let mut seen = std::collections::HashSet::new();
    seen.insert(cur.clone());
    for _hop in 0..16 {
        if cur.len() > 12288 {
            break;
        }
        let next = unfold_expr_single_step(&cur, local_defs);
        if next == cur || !seen.insert(next.clone()) {
            break;
        }
        cur = next;
    }
    cur
}

pub(super) fn is_trivial_existential_mask(concl: &str) -> bool {
    let c = strip_balanced_outer_parens(concl);
    let rest = if let Some(r) = c.strip_prefix('∃') {
        r.trim()
    } else if let Some(r) = c.strip_prefix("Exists ") {
        r.trim().trim_start_matches('(').trim_start_matches("fun ").trim()
    } else {
        return false;
    };
    let Some((binder_part, body_part)) = rest.split_once(',').or_else(|| rest.split_once("=>")) else {
        return false;
    };
    let b_clean = binder_part
        .trim()
        .trim_start_matches('(')
        .trim_end_matches(')');
    let binder_var = split_top_level_colon(b_clean)
        .map(|(v, _)| v.trim())
        .unwrap_or(b_clean)
        .split_whitespace()
        .next()
        .unwrap_or("");
    if binder_var.is_empty() || binder_var == "_" {
        return false;
    }
    let body = strip_balanced_outer_parens(body_part);
    if let Some((lhs, rhs, is_ne)) = split_top_level_eq(body) {
        if !is_ne {
            let l = strip_balanced_outer_parens(&lhs);
            let r = strip_balanced_outer_parens(&rhs);
            if l == binder_var && replace_ident_boundary(r, binder_var, "__CHK__") == r {
                return true;
            }
            if r == binder_var && replace_ident_boundary(l, binder_var, "__CHK__") == l {
                return true;
            }
        }
    }
    false
}

pub(super) fn is_provably_unsigned_expr(
    expr: &str,
    unsigned_vars: &std::collections::HashSet<String>,
) -> bool {
    let s = strip_balanced_outer_parens(expr.trim());
    if s.is_empty() || s.starts_with('-') {
        return false;
    }
    if let Some((_, ty_part)) = split_top_level_colon(s) {
        return is_explicitly_unsigned_binder_type(ty_part.trim());
    }
    if s.chars().all(|c| c.is_ascii_digit()) {
        return true;
    }
    if unsigned_vars.contains(s) {
        return true;
    }
    if let Some(base) = s.strip_suffix(".val") {
        let b = strip_balanced_outer_parens(base.trim());
        // `.val` is only guaranteed unsigned when its receiver `b` is itself a known unsigned/Fin variable.
        if unsigned_vars.contains(b) {
            return true;
        }
    }
    for sfx in [
        ".size",
        ".length",
        ".toNat",
        ".toUInt64",
        ".toUInt32",
        ".toUInt16",
        ".toUInt8",
    ] {
        if let Some(base) = s.strip_suffix(sfx) {
            let b = strip_balanced_outer_parens(base.trim());
            if !b.is_empty() && !b.starts_with('-') {
                return true;
            }
        }
    }
    if matches!(s, "Nat.zero" | "Word256.zero" | "Word256.one") {
        return true;
    }
    for pfx in [
        "Nat.add ",
        "Nat.mul ",
        "Nat.div ",
        "Nat.mod ",
        "Nat.pow ",
        "Nat.gcd ",
        "Nat.lcm ",
        "Nat.land ",
        "Nat.lor ",
        "Nat.xor ",
        "Nat.shiftLeft ",
        "Nat.shiftRight ",
        "Nat.succ ",
        "Nat.pred ",
        "Nat.min ",
        "Nat.max ",
        "UInt64.add ",
        "UInt64.mul ",
        "UInt64.div ",
        "UInt64.mod ",
        "UInt64.land ",
        "UInt64.lor ",
        "UInt64.xor ",
        "UInt64.shiftLeft ",
        "UInt64.shiftRight ",
        "UInt64.ofNat ",
        "Word256.add ",
        "Word256.mul ",
        "Word256.div ",
        "Word256.mod ",
        "Word256.bitAnd ",
        "Word256.bitOr ",
        "Word256.bitXor ",
        "Word256.shl ",
        "Word256.shr ",
        "List.length ",
        "Array.size ",
        "ByteArray.size ",
        "String.length ",
    ] {
        if s.starts_with(pfx) {
            return true;
        }
    }
    // Check top-level multi-char bitwise/shift operators over provably unsigned operands
    for op in ["&&&", "|||", "^^^", "<<<", ">>>"] {
        if let Some(pos) = find_top_level_delim(s, op) {
            if pos > 0 {
                let lhs = &s[..pos];
                let rhs = &s[pos + op.len()..];
                return is_provably_unsigned_expr(lhs, unsigned_vars)
                    && is_provably_unsigned_expr(rhs, unsigned_vars);
            }
        }
    }
    // Check top-level binary arithmetic over provably unsigned operands
    let chars: Vec<(usize, char)> = s.char_indices().collect();
    let mut depth = 0i32;
    for &(byte_pos, c) in &chars {
        match c {
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth = (depth - 1).max(0),
            '+' | '*' | '/' | '%' | '^' if depth == 0 && byte_pos > 0 => {
                let lhs = &s[..byte_pos];
                let rhs = &s[byte_pos + c.len_utf8()..];
                return is_provably_unsigned_expr(lhs, unsigned_vars)
                    && is_provably_unsigned_expr(rhs, unsigned_vars);
            }
            _ => {}
        }
    }
    false
}

#[allow(dead_code)]
pub(super) fn is_syntactically_contradictory_hyp(hyp: &str) -> bool {
    is_syntactically_contradictory_hyp_with_binders(hyp, &std::collections::HashSet::new())
}

pub(super) fn is_syntactically_contradictory_hyp_with_binders(
    hyp: &str,
    unsigned_vars: &std::collections::HashSet<String>,
) -> bool {
    let h = strip_balanced_outer_parens(strip_hypothesis_binder_name(hyp).trim());
    let conjuncts = split_top_level_conjuncts(h);
    if conjuncts.len() > 1 {
        if conjuncts
            .iter()
            .any(|c| is_syntactically_contradictory_hyp_with_binders(c, unsigned_vars))
        {
            return true;
        }
        for i in 0..conjuncts.len() {
            for j in (i + 1)..conjuncts.len() {
                let ci = strip_balanced_outer_parens(&conjuncts[i]);
                let cj = strip_balanced_outer_parens(&conjuncts[j]);
                if cj == format!("¬{}", ci)
                    || cj == format!("¬({})", ci)
                    || ci == format!("¬{}", cj)
                    || ci == format!("¬({})", cj)
                {
                    return true;
                }
                if let (Some((l1, r1, ne1)), Some((l2, r2, ne2))) =
                    (split_top_level_eq(ci), split_top_level_eq(cj))
                {
                    if ne1 != ne2 && ((l1 == l2 && r1 == r2) || (l1 == r2 && r1 == l2)) {
                        return true;
                    }
                }
            }
        }
    }
    if matches!(
        h,
        "False" | "false" | "false = true" | "true = false" | "0 = 1" | "1 = 0"
    ) {
        return true;
    }
    for (op, is_strict) in [("<", true), ("≤", false), ("<=", false)] {
        if let Some((l, r)) = h.split_once(op) {
            let lt = l.trim();
            let rt = r.trim();
            if is_strict && lt == rt {
                return true;
            }
            if is_strict && rt == "0" && is_provably_unsigned_expr(lt, unsigned_vars) {
                return true;
            }
            if !is_strict && lt == "1" && rt == "0" {
                return true;
            }
            if let (Ok(ln), Ok(rn)) = (lt.parse::<u128>(), rt.parse::<u128>()) {
                if (is_strict && ln >= rn) || (!is_strict && ln > rn) {
                    return true;
                }
            }
        }
    }
    if let Some((lhs, rhs, is_ne)) = split_top_level_eq(h) {
        let l = lhs.trim();
        let r = rhs.trim();
        if is_ne && l == r {
            return true;
        }
        if !is_ne {
            // Detect `a = Word256.add a Word256.one` or `a = a + 1`
            if r == format!("Word256.add {} Word256.one", l)
                || r == format!("{} + 1", l)
                || l == format!("Word256.add {} Word256.one", r)
                || l == format!("{} + 1", r)
            {
                return true;
            }
        }
    }
    false
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct AuditSpecPathRule {
    pub glob_pattern: String,
    #[serde(default)]
    pub forbid_decl_kinds: Vec<String>,
    #[serde(default)]
    pub allow_decl_names: Vec<String>,
    #[serde(default)]
    pub forbid_namespaces: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct AuditSpecPolicyConfig {
    pub policy: String,
    pub reject_conjunct_tautologies: bool,
    pub reject_definitional_lowering_tautology: bool,
    pub reject_identity_stubs: bool,
    pub reject_unused_param_defs: bool,
    pub reject_size_only_parsers: bool,
    #[serde(default)]
    pub forbid_decl_kinds: Vec<String>,
    #[serde(default)]
    pub forbid_namespaces: Vec<String>,
    #[serde(default)]
    pub path_rules: Vec<AuditSpecPathRule>,
}

impl Default for AuditSpecPolicyConfig {
    fn default() -> Self {
        Self::from_preset("default")
    }
}

impl AuditSpecPolicyConfig {
    pub fn from_preset(preset: &str) -> Self {
        match preset.trim().to_ascii_lowercase().as_str() {
            "permissive" => Self {
                policy: "permissive".to_string(),
                reject_conjunct_tautologies: false,
                reject_definitional_lowering_tautology: false,
                reject_identity_stubs: false,
                reject_unused_param_defs: false,
                reject_size_only_parsers: false,
                forbid_decl_kinds: Vec::new(),
                forbid_namespaces: Vec::new(),
                path_rules: Vec::new(),
            },
            "strict-proofs" | "strict_proofs" | "strict" => Self {
                policy: "strict-proofs".to_string(),
                reject_conjunct_tautologies: true,
                reject_definitional_lowering_tautology: true,
                reject_identity_stubs: true,
                reject_unused_param_defs: true,
                reject_size_only_parsers: true,
                forbid_decl_kinds: Vec::new(),
                forbid_namespaces: Vec::new(),
                path_rules: vec![AuditSpecPathRule {
                    glob_pattern: "lean/**/Proofs/**".to_string(),
                    forbid_decl_kinds: vec!["inductive".to_string()],
                    allow_decl_names: vec!["SymExpr".to_string()],
                    forbid_namespaces: vec![
                        "ConLeche".to_string(),
                        "TurboLean.Kernel.ConLeche".to_string(),
                        "TurboLean.ElabAudit".to_string(),
                        "LCNF".to_string(),
                        "LeanMLIR".to_string(),
                        "LNSym".to_string(),
                    ],
                }],
            },
            _ => Self {
                policy: "default".to_string(),
                reject_conjunct_tautologies: true,
                reject_definitional_lowering_tautology: true,
                reject_identity_stubs: true,
                reject_unused_param_defs: true,
                reject_size_only_parsers: true,
                forbid_decl_kinds: Vec::new(),
                forbid_namespaces: Vec::new(),
                path_rules: Vec::new(),
            },
        }
    }

    pub fn load_for_target(
        file: &Path,
        policy_override: Option<&str>,
        config_path_override: Option<&Path>,
        extra_forbid_namespaces: &[String],
        extra_forbid_decl_kinds: &[String],
    ) -> Self {
        let mut resolved = None;
        if let Some(cfg_path) = config_path_override {
            if let Ok(txt) = fs::read_to_string(cfg_path) {
                resolved = Self::parse_config_str(&txt);
            }
        }
        if resolved.is_none() {
            if let Ok(env_cfg) = std::env::var("TURBO_LEAN_AUDIT_SPEC_CONFIG") {
                let t = env_cfg.trim();
                if !t.is_empty() {
                    resolved = Self::parse_config_str(t)
                        .or_else(|| fs::read_to_string(t).ok().and_then(|s| Self::parse_config_str(&s)));
                }
            }
        }
        if resolved.is_none() {
            let start_dir = if file.is_dir() {
                file.to_path_buf()
            } else {
                file.parent().unwrap_or_else(|| Path::new(".")).to_path_buf()
            };
            let canon_start = start_dir.canonicalize().unwrap_or(start_dir);
            for anc in canon_start.ancestors() {
                for rel in ["turbo-lean.toml", ".turbo-lean.toml"] {
                    let cand = anc.join(rel);
                    if cand.is_file() {
                        if let Ok(txt) = fs::read_to_string(&cand) {
                            if let Some(cfg) = Self::parse_config_str(&txt) {
                                resolved = Some(cfg);
                                break;
                            }
                        }
                    }
                }
                if resolved.is_some() {
                    break;
                }
            }
        }

        let mut cfg = resolved.unwrap_or_default();
        if let Some(pol) = policy_override.filter(|s| !s.trim().is_empty()) {
            let preset = Self::from_preset(pol);
            cfg.policy = preset.policy;
            cfg.reject_conjunct_tautologies = preset.reject_conjunct_tautologies;
            cfg.reject_definitional_lowering_tautology = preset.reject_definitional_lowering_tautology;
            cfg.reject_identity_stubs = preset.reject_identity_stubs;
            cfg.reject_unused_param_defs = preset.reject_unused_param_defs;
            cfg.reject_size_only_parsers = preset.reject_size_only_parsers;
            for pr in preset.path_rules {
                if let Some(existing) = cfg
                    .path_rules
                    .iter_mut()
                    .find(|r| r.glob_pattern == pr.glob_pattern)
                {
                    for k in pr.forbid_decl_kinds {
                        if !existing.forbid_decl_kinds.contains(&k) {
                            existing.forbid_decl_kinds.push(k);
                        }
                    }
                    for a in pr.allow_decl_names {
                        if !existing.allow_decl_names.contains(&a) {
                            existing.allow_decl_names.push(a);
                        }
                    }
                    for ns in pr.forbid_namespaces {
                        if !existing.forbid_namespaces.contains(&ns) {
                            existing.forbid_namespaces.push(ns);
                        }
                    }
                } else {
                    cfg.path_rules.push(pr);
                }
            }
        }
        for ns in extra_forbid_namespaces {
            let t = ns.trim();
            if !t.is_empty() && !cfg.forbid_namespaces.iter().any(|x| x == t) {
                cfg.forbid_namespaces.push(t.to_string());
            }
        }
        for kd in extra_forbid_decl_kinds {
            let t = kd.trim();
            if !t.is_empty() && !cfg.forbid_decl_kinds.iter().any(|x| x == t) {
                cfg.forbid_decl_kinds.push(t.to_string());
            }
        }
        cfg
    }

    pub fn parse_config_str(text: &str) -> Option<Self> {
        let trimmed = text.trim();
        if trimmed.is_empty() {
            return None;
        }
        if trimmed.starts_with('{') {
            return serde_json::from_str::<Self>(trimmed).ok();
        }
        let mut cfg = Self::default();
        let mut in_audit_spec = false;
        let mut current_rule: Option<AuditSpecPathRule> = None;
        let mut parsed_any = false;

        let unquote = |s: &str| -> String {
            let t = s.trim();
            if (t.starts_with('"') && t.ends_with('"')) || (t.starts_with('\'') && t.ends_with('\'')) {
                t[1..t.len().saturating_sub(1)].to_string()
            } else {
                t.to_string()
            }
        };
        let parse_arr = |s: &str| -> Vec<String> {
            let t = s.trim();
            if let Ok(v) = serde_json::from_str::<Vec<String>>(t) {
                return v;
            }
            let inner = t.strip_prefix('[').and_then(|x| x.strip_suffix(']')).unwrap_or(t);
            inner
                .split(',')
                .map(&unquote)
                .filter(|x| !x.is_empty())
                .collect()
        };

        // Pre-join multiline `[...]` arrays across lines before line-by-line parsing
        let mut joined_lines: Vec<String> = Vec::new();
        let mut pending_arr: Option<String> = None;
        for raw_line in trimmed.lines() {
            let clean = raw_line.split('#').next().unwrap_or("").trim();
            if clean.is_empty() {
                continue;
            }
            if let Some(mut acc) = pending_arr.take() {
                acc.push(' ');
                acc.push_str(clean);
                if clean.ends_with(']') {
                    joined_lines.push(acc);
                } else {
                    pending_arr = Some(acc);
                }
            } else if clean.contains('=') && clean.contains('[') && !clean.ends_with(']') {
                pending_arr = Some(clean.to_string());
            } else {
                joined_lines.push(clean.to_string());
            }
        }
        if let Some(acc) = pending_arr {
            joined_lines.push(acc);
        }

        for line in joined_lines {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            if line.starts_with('[') && line.ends_with(']') {
                if let Some(r) = current_rule.take() {
                    if !r.glob_pattern.is_empty() {
                        cfg.path_rules.push(r);
                    }
                }
                let sec = &line[1..line.len() - 1].trim();
                if *sec == "audit_spec" || *sec == "audit-spec" {
                    in_audit_spec = true;
                    parsed_any = true;
                } else if let Some(rest) = sec
                    .strip_prefix("audit_spec.path_rules.")
                    .or_else(|| sec.strip_prefix("audit-spec.path_rules."))
                {
                    in_audit_spec = false;
                    parsed_any = true;
                    current_rule = Some(AuditSpecPathRule {
                        glob_pattern: unquote(rest),
                        forbid_decl_kinds: Vec::new(),
                        allow_decl_names: Vec::new(),
                        forbid_namespaces: Vec::new(),
                    });
                } else {
                    in_audit_spec = false;
                }
                continue;
            }
            let Some((k, v)) = line.split_once('=') else {
                continue;
            };
            let (key, val) = (k.trim(), v.trim());
            if let Some(ref mut rule) = current_rule {
                match key {
                    "forbid_decl_kinds" => rule.forbid_decl_kinds = parse_arr(val),
                    "allow_decl_names" => rule.allow_decl_names = parse_arr(val),
                    "forbid_namespaces" => rule.forbid_namespaces = parse_arr(val),
                    _ => {}
                }
            } else if in_audit_spec {
                match key {
                    "policy" => {
                        let p = unquote(val);
                        let preset = Self::from_preset(&p);
                        cfg.policy = preset.policy;
                        cfg.reject_conjunct_tautologies = preset.reject_conjunct_tautologies;
                        cfg.reject_definitional_lowering_tautology =
                            preset.reject_definitional_lowering_tautology;
                        cfg.reject_identity_stubs = preset.reject_identity_stubs;
                        cfg.reject_unused_param_defs = preset.reject_unused_param_defs;
                        cfg.reject_size_only_parsers = preset.reject_size_only_parsers;
                        for pr in preset.path_rules {
                            if !cfg.path_rules.iter().any(|r| r.glob_pattern == pr.glob_pattern) {
                                cfg.path_rules.push(pr);
                            }
                        }
                    }
                    "reject_conjunct_tautologies" => {
                        if let Ok(b) = val.parse() {
                            cfg.reject_conjunct_tautologies = b;
                        }
                    }
                    "reject_definitional_lowering_tautology" => {
                        if let Ok(b) = val.parse() {
                            cfg.reject_definitional_lowering_tautology = b;
                        }
                    }
                    "reject_identity_stubs" => {
                        if let Ok(b) = val.parse() {
                            cfg.reject_identity_stubs = b;
                        }
                    }
                    "reject_unused_param_defs" => {
                        if let Ok(b) = val.parse() {
                            cfg.reject_unused_param_defs = b;
                        }
                    }
                    "reject_size_only_parsers" => {
                        if let Ok(b) = val.parse() {
                            cfg.reject_size_only_parsers = b;
                        }
                    }
                    "forbid_decl_kinds" => cfg.forbid_decl_kinds = parse_arr(val),
                    "forbid_namespaces" => cfg.forbid_namespaces = parse_arr(val),
                    _ => {}
                }
            }
        }
        if let Some(r) = current_rule.take() {
            if !r.glob_pattern.is_empty() {
                cfg.path_rules.push(r);
            }
        }
        parsed_any.then_some(cfg)
    }

    pub fn effective_forbidden_for_path(&self, file: &Path) -> (Vec<String>, Vec<String>, Vec<String>) {
        let mut kinds = self.forbid_decl_kinds.clone();
        let mut allow_names = Vec::new();
        let mut namespaces = self.forbid_namespaces.clone();
        let path_norm = file.to_string_lossy().replace('\\', "/");
        for rule in &self.path_rules {
            if path_matches_audit_glob(&path_norm, &rule.glob_pattern) {
                for k in &rule.forbid_decl_kinds {
                    if !kinds.iter().any(|x| x == k) {
                        kinds.push(k.clone());
                    }
                }
                for a in &rule.allow_decl_names {
                    if !allow_names.iter().any(|x| x == a) {
                        allow_names.push(a.clone());
                    }
                }
                for ns in &rule.forbid_namespaces {
                    if !namespaces.iter().any(|x| x == ns) {
                        namespaces.push(ns.clone());
                    }
                }
            }
        }
        (kinds, allow_names, namespaces)
    }
}

pub(super) fn path_matches_audit_glob(path_str: &str, glob_pat: &str) -> bool {
    let pat = glob_pat.trim().replace('\\', "/");
    if pat.is_empty() || pat == "**" || pat == "*" {
        return true;
    }
    // Common proof-directory glob fast-paths (e.g. `lean/**/Proofs/**`)
    let anchor_parts: Vec<&str> = pat
        .split("**")
        .map(|s| s.trim_matches('/'))
        .filter(|s| !s.is_empty() && *s != "*")
        .collect();
    if anchor_parts.is_empty() {
        return true;
    }
    let mut search_from = 0usize;
    for part in anchor_parts {
        let Some(pos) = path_str[search_from..].find(part) else {
            return false;
        };
        search_from += pos + part.len();
    }
    true
}

pub(super) fn is_single_conjunct_trivial(c: &str) -> bool {
    let ct = strip_balanced_outer_parens(c);
    if matches!(ct, "True" | "true" | "true = true" | "false = false") {
        return true;
    }
    if let Some((l, r, op)) = split_top_level_rel(ct) {
        let lt = strip_balanced_outer_parens(&l);
        let rt = strip_balanced_outer_parens(&r);
        if lt == rt {
            return true;
        }
        if op == "=" {
            for ok_pfx in [".ok", "Except.ok", "Option.some", "some"] {
                if let (Some(li), Some(ri)) = (lt.strip_prefix(ok_pfx), rt.strip_prefix(ok_pfx)) {
                    if strip_balanced_outer_parens(li) == strip_balanced_outer_parens(ri) {
                        return true;
                    }
                }
            }
        }
    }
    let no_sp = ct.replace(' ', "");
    matches!(no_sp.as_str(), "0≤" | "0<=")
        || ct.starts_with("0 ≤ ")
        || ct.starts_with("0 <= ")
        || is_trivial_existential_mask(ct)
}

pub(super) fn substitute_equational_hypotheses(
    conclusion: &str,
    hyp_strings: &[String],
    local_defs: &[(String, Vec<String>, String)],
) -> String {
    let mut cur = conclusion.to_string();
    let mut subs: Vec<(String, String)> = Vec::new();
    for h in hyp_strings {
        for conj in split_top_level_conjuncts(h) {
            if let Some((lhs, rhs, is_ne)) = split_top_level_eq(&conj) {
                if is_ne {
                    continue;
                }
                let l = strip_balanced_outer_parens(&lhs);
                let r = strip_balanced_outer_parens(&rhs);
                // Case 1: `.ok expr = .ok var` or `.ok var = .ok expr`
                for pfx in [".ok", "Except.ok", "Option.some", "some"] {
                    if let (Some(l_in), Some(r_in)) = (l.strip_prefix(pfx), r.strip_prefix(pfx)) {
                        let li = strip_balanced_outer_parens(l_in.trim());
                        let ri = strip_balanced_outer_parens(r_in.trim());
                        if ri.chars().all(is_ident_continue) && !ri.is_empty() && li != ri {
                            subs.push((ri.to_string(), li.to_string()));
                        } else if li.chars().all(is_ident_continue) && !li.is_empty() && li != ri {
                            subs.push((li.to_string(), ri.to_string()));
                        }
                    }
                }
                // Case 2: direct variable equality `var = expr` or `expr = var`
                if l.chars().all(is_ident_continue)
                    && !l.is_empty()
                    && !matches!(l, "true" | "false" | "True" | "False")
                    && l != r
                {
                    subs.push((l.to_string(), r.to_string()));
                } else if r.chars().all(is_ident_continue)
                    && !r.is_empty()
                    && !matches!(r, "true" | "false" | "True" | "False")
                    && l != r
                {
                    subs.push((r.to_string(), l.to_string()));
                }
            }
        }
    }
    if subs.is_empty() {
        return cur;
    }
    let mut used_idents = std::collections::HashSet::new();
    for id in extract_expr_identifiers(&cur) {
        used_idents.insert(id);
    }
    let mut subst_map = std::collections::HashMap::with_capacity(subs.len());
    for (var, expr) in &subs {
        used_idents.insert(var.clone());
        for id in extract_expr_identifiers(expr) {
            used_idents.insert(id);
        }
        let wrapped = if expr.contains(char::is_whitespace) {
            format!("({})", expr)
        } else {
            expr.clone()
        };
        subst_map.insert(var.clone(), wrapped);
    }
    for _pass in 0..4 {
        let prev = cur.clone();
        cur = subst_lean_expr_scoped(&cur, &subst_map, &mut used_idents);
        cur = unfold_expr_one_level(&cur, local_defs);
        if cur == prev {
            break;
        }
    }
    cur
}

/// Recognize the conservative application/equality shape `f ... x ... = f ... y ...`.
/// Only universally bound, same-type, unconstrained variables may differ, and
/// every differing position must be absent from the resolved local definition.
pub(super) fn relational_ignored_parameters(
    decl: &ExtractedDecl,
    conjunct: &str,
    local_defs: &[(String, Vec<String>, String)],
) -> Option<(String, Vec<usize>)> {
    let (lhs, rhs, false) = split_top_level_eq(strip_balanced_outer_parens(conjunct))? else {
        return None;
    };
    let lhs = split_lean_app_args(strip_balanced_outer_parens(&lhs));
    let rhs = split_lean_app_args(strip_balanced_outer_parens(&rhs));
    let head = lhs.first()?;
    if lhs.len() != rhs.len()
        || rhs.first()? != head
        || lhs == rhs
        || decl.binders.iter().any(|(names, _)| names.contains(head))
    {
        return None;
    }
    let mut matching_names = std::collections::HashSet::new();
    let mut chosen: Option<&(String, Vec<String>, String)> = None;
    for entry in local_defs {
        let (name, params, _) = entry;
        if name.starts_with("__binder_ty:") {
            continue;
        }
        if name == head || name.rsplit('.').next() == Some(head.as_str()) {
            matching_names.insert(name.as_str());
            if chosen.is_none() && params.len() + 1 == lhs.len() {
                chosen = Some(entry);
            }
        }
    }
    if matching_names.len() != 1 {
        return None;
    }
    let (name, params, body) = chosen?;
    let binder_type = |arg: &str| {
        let clean_arg = strip_balanced_outer_parens(arg.trim());
        let mut matches = decl
            .binders
            .iter()
            .filter(|(names, _)| names.iter().any(|n| n == clean_arg));
        let (_, ty) = matches.next()?;
        (matches.next().is_none() && is_known_binder_value_type(ty)).then_some(ty)
    };
    let segments = split_top_level_implications(&decl.prop_str);
    let constraints: Vec<&str> = decl
        .binders
        .iter()
        .filter(|(_, ty)| !is_known_binder_value_type(ty))
        .map(|(_, ty)| ty.as_str())
        .chain(
            segments
                .iter()
                .take(segments.len().saturating_sub(1))
                .map(String::as_str),
        )
        .collect();
    let mut varied = Vec::new();
    for (i, ((a, b), param)) in lhs[1..].iter().zip(&rhs[1..]).zip(params).enumerate() {
        let ca = strip_balanced_outer_parens(a.trim());
        let cb = strip_balanced_outer_parens(b.trim());
        if ca == cb {
            continue;
        }
        let param_ident = param.split('@').next().unwrap_or(param).trim();
        if binder_type(ca)? != binder_type(cb)?
            || replace_ident_boundary(body, param_ident, "__USED__") != *body
            || constraints.iter().any(|h| {
                [ca, cb]
                    .iter()
                    .any(|v| replace_ident_boundary(h, v, "__BOUND__") != *h)
            })
        {
            return None;
        }
        varied.push(i);
    }
    (!varied.is_empty()).then(|| (name.clone(), varied))
}

pub(super) fn audit_referenced_local_defs_for_stubs(
    decl: &ExtractedDecl,
    unfolded_binder_types: &[(Vec<String>, String)],
    hyp_strings: &[String],
    unfolded_conclusion: &str,
    local_defs: &[(String, Vec<String>, String)],
    policy: &AuditSpecPolicyConfig,
) -> Vec<String> {
    if !policy.reject_identity_stubs
        && !policy.reject_unused_param_defs
        && !policy.reject_size_only_parsers
    {
        return Vec::new();
    }
    let mut full_stmt = decl.prop_str.clone();
    for (_, ty) in &decl.binders {
        full_stmt.push(' ');
        full_stmt.push_str(ty);
    }
    for (_, ty) in unfolded_binder_types {
        full_stmt.push(' ');
        full_stmt.push_str(ty);
    }
    for h in hyp_strings {
        full_stmt.push(' ');
        full_stmt.push_str(h);
    }
    full_stmt.push(' ');
    full_stmt.push_str(unfolded_conclusion);

    // Collect transitively referenced local defs (up to 4 hops)
    let mut visited = std::collections::HashSet::new();
    let mut frontier = vec![full_stmt];
    let mut referenced = Vec::new();
    for _hop in 0..4 {
        let mut next_frontier = Vec::new();
        for (def_name, params, body) in local_defs {
            if visited.contains(def_name.as_str()) {
                continue;
            }
            let short = def_name.rsplit('.').next().unwrap_or(def_name.as_str());
            let is_ref = frontier.iter().any(|txt| {
                replace_ident_boundary(txt, def_name, "__REF__") != *txt
                    || replace_ident_boundary(txt, short, "__REF__") != *txt
            });
            if is_ref {
                visited.insert(def_name.clone());
                referenced.push((def_name.as_str(), params.as_slice(), body.as_str()));
                next_frontier.push(body.clone());
            }
        }
        if next_frontier.is_empty() {
            break;
        }
        frontier = next_frontier;
    }

    let mut stub_findings = Vec::new();
    for (def_name, params, body) in referenced {
        let short = def_name.rsplit('.').next().unwrap_or(def_name);
        let b_trim = strip_balanced_outer_parens(body);

        // 1. Identity stub: `def f (x : T) : T := x`
        if policy.reject_identity_stubs && params.len() == 1 {
            let p0 = params[0].trim();
            if !p0.is_empty() && b_trim == p0 && short != "id" {
                stub_findings.push(format!(
                    "{}: local def `{}` is an identity stub (`{} := {}`)",
                    decl.name, def_name, p0, b_trim
                ));
            }
        }

        // 2. Unused parameter in a referenced function/predicate:
        //    - Reject any non-underscore parameter that never occurs in `body`.
        //    - Reject any function where zero parameters are referenced in `body`.
        //    - Reject underscore-prefixed parameters under `strict-proofs` or when `params.len() <= 3`,
        //      UNLESS the theorem is a 2-call relational hyperproperty (`f ... a ... = f ... b ...`).
        if policy.reject_unused_param_defs && !params.is_empty() {
            let conclusions = split_top_level_implications(&decl.prop_str);
            let relations: Vec<_> = if policy.policy == "strict-proofs" {
                Vec::new()
            } else {
                split_top_level_conjuncts(conclusions.last().map(String::as_str).unwrap_or(""))
                    .iter()
                    .filter_map(|c| relational_ignored_parameters(decl, c, local_defs))
                    .collect()
            };
            let mut used_count = 0usize;
            for (p_idx, p) in params.iter().enumerate() {
                let pt = p.split('@').next().unwrap_or(p).trim();
                if relations
                    .iter()
                    .any(|(name, positions)| name == def_name && positions.contains(&p_idx))
                {
                    used_count += 1;
                    continue;
                }
                if pt.starts_with('_') {
                    if params.len() <= 3 || policy.policy == "strict-proofs" {
                        stub_findings.push(format!(
                            "{}: local def `{}` ignores parameter `{}`",
                            decl.name, def_name, pt
                        ));
                    }
                } else if !pt.is_empty() {
                    if replace_ident_boundary(b_trim, pt, "__USED__") == b_trim {
                        stub_findings.push(format!(
                            "{}: local def `{}` never references parameter `{}` in its body",
                            decl.name, def_name, pt
                        ));
                    } else {
                        used_count += 1;
                    }
                }
            }
            if used_count == 0 {
                stub_findings.push(format!(
                    "{}: local def `{}` ignores all {} parameters in its body",
                    decl.name,
                    def_name,
                    params.len()
                ));
            }
        }

        // 3. Size-only parser / empty-payload stub: e.g. `parseOleanShard` checking only `.size` and returning `decls := []`
        if policy.reject_size_only_parsers && params.len() == 1 {
            let p0 = params[0].trim();
            let checks_size = b_trim.contains(&format!("{}.size", p0));
            let uses_elements = b_trim.contains(&format!("{}.get", p0))
                || b_trim.contains(&format!("{}.data", p0))
                || b_trim.contains(&format!("{}.extract", p0))
                || b_trim.contains(&format!("{}.foldl", p0))
                || b_trim.contains(&format!("{}[", p0));
            let has_empty_list_field = b_trim.contains(":= []") || b_trim.contains(":=[]");
            if checks_size && !uses_elements && has_empty_list_field {
                stub_findings.push(format!(
                    "{}: local def `{}` is a size-only stub returning an empty collection without reading `{}` contents",
                    decl.name, def_name, p0
                ));
            }
        }
    }
    stub_findings
}

pub(super) fn audit_forbidden_scope_declarations(
    clean_src: &str,
    forbid_kinds: &[String],
    allow_decl_names: &[String],
    forbid_namespaces: &[String],
) -> Vec<String> {
    if forbid_kinds.is_empty() && forbid_namespaces.is_empty() {
        return Vec::new();
    }
    let mut violations = Vec::new();
    let mut scope_stack: Vec<LeanScopeFrame> = Vec::new();
    for (idx, raw_line) in clean_src.lines().enumerate() {
        let ln = idx + 1;
        let mut line = raw_line.trim();
        if line.is_empty() {
            continue;
        }
        if line == "section" || line.starts_with("section ") {
            let sec_name = line
                .strip_prefix("section")
                .unwrap_or("")
                .split_whitespace()
                .next();
            push_lean_section(&mut scope_stack, sec_name);
            continue;
        }
        if let Some(ns_rest) = line.strip_prefix("namespace ") {
            let ns = ns_rest.split_whitespace().next().unwrap_or("").trim();
            if !ns.is_empty() {
                push_lean_namespace(&mut scope_stack, ns);
                let current_ns = format_lean_scope_namespace(&scope_stack);
                for fns in forbid_namespaces {
                    if current_ns == *fns
                        || ns == fns.as_str()
                        || current_ns.starts_with(&format!("{}.", fns))
                    {
                        violations.push(format!(
                            "L{}: forbidden namespace `{}` opened in restricted scope",
                            ln, current_ns
                        ));
                        break;
                    }
                }
            }
            continue;
        }
        if line == "end" || line.starts_with("end ") {
            let end_ns = line.strip_prefix("end").unwrap_or("").trim();
            pop_lean_scope(&mut scope_stack, end_ns);
            continue;
        }
        loop {
            let mut stripped = false;
            for pfx in [
                "private ",
                "protected ",
                "@[inline] ",
                "@[reducible] ",
                "@[simp] ",
                "noncomputable ",
                "scoped ",
                "local ",
            ] {
                if let Some(rest) = line.strip_prefix(pfx) {
                    line = rest.trim();
                    stripped = true;
                }
            }
            if !stripped {
                break;
            }
        }
        for fk in forbid_kinds {
            let kw_space = format!("{} ", fk.trim());
            if line.starts_with(&kw_space) {
                let decl_name = line[kw_space.len()..]
                    .split(|c: char| c.is_whitespace() || c == '(' || c == '{' || c == ':')
                    .next()
                    .unwrap_or("<anon>");
                if allow_decl_names.iter().any(|a| a == decl_name) {
                    continue;
                }
                violations.push(format!(
                    "L{}: forbidden `{}` declaration `{}` in restricted scope",
                    ln,
                    fk.trim(),
                    decl_name
                ));
            }
        }
    }
    violations
}

/// Audit a single extracted theorem declaration for vacuous preconditions and postcondition tightness.
pub(super) fn audit_single_decl_spec(decl: &ExtractedDecl) -> (bool, bool, String) {
    audit_single_decl_spec_with_defs(decl, &[]).0
}

pub(super) fn audit_single_decl_spec_with_defs(
    decl: &ExtractedDecl,
    local_defs: &[(String, Vec<String>, String)],
) -> ((bool, bool, String), String, String) {
    let (res, pos_w, neg_w, _, _) =
        audit_single_decl_spec_full_with_policy(decl, local_defs, &AuditSpecPolicyConfig::default());
    (res, pos_w, neg_w)
}

#[allow(dead_code)]
pub(super) fn audit_single_decl_spec_full(
    decl: &ExtractedDecl,
    local_defs: &[(String, Vec<String>, String)],
) -> ((bool, bool, String), String, String, Vec<String>) {
    let (res, pos_w, neg_w, drop_hyps, _) =
        audit_single_decl_spec_full_with_policy(decl, local_defs, &AuditSpecPolicyConfig::default());
    (res, pos_w, neg_w, drop_hyps)
}

fn is_explicitly_unsigned_binder_type(ty: &str) -> bool {
    let t = ty.trim();
    t == "Nat"
        || t == "USize"
        || t == "Word256"
        || t == "EVMWord"
        || t.starts_with("UInt")
        || t.starts_with("Fin ")
        || t.starts_with("BitVec ")
}

fn mk_con_leche_const(
    name: &str,
    global_consts: &mut std::collections::HashSet<String>,
) -> crate::c_abi::ConLecheExpr {
    global_consts.insert(name.to_string());
    crate::c_abi::ConLecheExpr::Const(name.to_string(), Vec::new())
}

fn mk_con_leche_op2(
    lhs: crate::c_abi::ConLecheExpr,
    rhs: crate::c_abi::ConLecheExpr,
    global_consts: &mut std::collections::HashSet<String>,
) -> crate::c_abi::ConLecheExpr {
    use crate::c_abi::ConLecheExpr;
    let app_fn = mk_con_leche_const("__App", global_consts);
    ConLecheExpr::App(
        Box::new(ConLecheExpr::App(Box::new(app_fn), Box::new(lhs))),
        Box::new(rhs),
    )
}

fn mk_con_leche_forall(
    dom: crate::c_abi::ConLecheExpr,
    body: crate::c_abi::ConLecheExpr,
    global_consts: &mut std::collections::HashSet<String>,
) -> crate::c_abi::ConLecheExpr {
    use crate::c_abi::{ConLecheExpr, ConLecheLevel};
    let prop_sort = ConLecheExpr::Sort(ConLecheLevel::Zero);
    let forall_fn = mk_con_leche_const("__Forall", global_consts);
    let pred = ConLecheExpr::Lam(Box::new(prop_sort), Box::new(body));
    ConLecheExpr::App(
        Box::new(ConLecheExpr::App(Box::new(forall_fn), Box::new(dom))),
        Box::new(pred),
    )
}

fn mk_con_leche_distinct_prop_val(idx: usize) -> crate::c_abi::ConLecheExpr {
    use crate::c_abi::{ConLecheExpr, ConLecheLevel};
    let prop_sort = ConLecheExpr::Sort(ConLecheLevel::Zero);
    let bit0 = ConLecheExpr::ForallE(
        Box::new(prop_sort.clone()),
        Box::new(ConLecheExpr::BVar(0)),
    );
    let bit1 = ConLecheExpr::ForallE(
        Box::new(prop_sort.clone()),
        Box::new(ConLecheExpr::ForallE(
            Box::new(prop_sort),
            Box::new(ConLecheExpr::BVar(0)),
        )),
    );
    let mut v = idx.saturating_add(1);
    let mut acc = bit0.clone();
    while v > 0 {
        let b_expr = if (v & 1) == 1 {
            bit1.clone()
        } else {
            bit0.clone()
        };
        acc = ConLecheExpr::ForallE(Box::new(b_expr), Box::new(acc));
        v >>= 1;
    }
    acc
}

fn mk_con_leche_domain_tree(
    doms: &[crate::c_abi::ConLecheExpr],
    global_consts: &mut std::collections::HashSet<String>,
) -> Option<crate::c_abi::ConLecheExpr> {
    if doms.is_empty() {
        return None;
    }
    let mut layer = doms.to_vec();
    while layer.len() > 1 {
        let mut next = Vec::with_capacity((layer.len() + 1) / 2);
        for pair in layer.chunks(2) {
            if pair.len() == 2 {
                next.push(mk_con_leche_op2(
                    pair[0].clone(),
                    pair[1].clone(),
                    global_consts,
                ));
            } else {
                next.push(pair[0].clone());
            }
        }
        layer = next;
    }
    layer.into_iter().next()
}

#[derive(Debug, Clone)]
struct CompiledDefSig {
    canon_name: String,
    kernel_params: Vec<String>,
    explicit_params_with_ty: Vec<String>,
}

fn mk_con_leche_leaf_with_bound_vars(
    s: &str,
    bound_stack: &[String],
    local_def_names: &std::collections::HashSet<String>,
    compiled_def_sigs: &std::collections::HashMap<String, CompiledDefSig>,
    global_consts: &mut std::collections::HashSet<String>,
) -> crate::c_abi::ConLecheExpr {
    if !local_def_names.contains(s) {
        if let Some(rev_pos) = bound_stack.iter().rev().position(|b| b == s) {
            return crate::c_abi::ConLecheExpr::BVar(rev_pos);
        }
    }
    let mut template = s.to_string();
    let mut matched_bvars = Vec::new();
    let mut seen_names = std::collections::HashSet::new();
    let mut subst_map = std::collections::HashMap::new();
    let mut slot_by_name = Vec::new();
    for (rev_pos, b_name) in bound_stack.iter().rev().enumerate() {
        if b_name.is_empty()
            || b_name == "_"
            || local_def_names.contains(b_name)
            || !seen_names.insert(b_name.as_str())
        {
            continue;
        }
        let ph = format!("__BVSLOT_{}__", slot_by_name.len());
        subst_map.insert(b_name.clone(), ph.clone());
        slot_by_name.push((ph, rev_pos));
    }
    if !subst_map.is_empty() {
        let mut used_idents = std::collections::HashSet::new();
        for id in extract_expr_identifiers(&template) {
            used_idents.insert(id);
        }
        let scoped = subst_lean_expr_scoped(&template, &subst_map, &mut used_idents);
        let mut cur_tpl = scoped;
        let mut hit_idx = 0usize;
        for (ph, rev_pos) in slot_by_name {
            if cur_tpl.contains(&ph) {
                cur_tpl = cur_tpl.replace(&ph, &format!("$arg{}", hit_idx));
                matched_bvars.push(rev_pos);
                hit_idx += 1;
            }
        }
        template = cur_tpl;
    }
    let violates_arity_or_shadow = compiled_def_sigs
        .values()
        .any(|sig| !sig.kernel_params.is_empty() && sig.canon_name == template)
        || compiled_def_sigs
            .get(&template)
            .is_some_and(|sig| !sig.kernel_params.is_empty())
        || bound_stack.iter().any(|b| b == &template);
    if violates_arity_or_shadow {
        template = format!("__Leaf({})", template);
    }
    let mut leaf_nodes = Vec::with_capacity(1 + matched_bvars.len());
    leaf_nodes.push(mk_con_leche_const(&template, global_consts));
    for rev_pos in matched_bvars {
        leaf_nodes.push(crate::c_abi::ConLecheExpr::BVar(rev_pos));
    }
    mk_con_leche_domain_tree(&leaf_nodes, global_consts)
        .unwrap_or_else(|| mk_con_leche_const(&template, global_consts))
}

fn elaborate_lean_surface_expr_to_con_leche(
    expr_str: &str,
    bound_stack: &[String],
    local_def_names: &std::collections::HashSet<String>,
    compiled_def_sigs: &std::collections::HashMap<String, CompiledDefSig>,
    binder_types: &std::collections::HashMap<String, String>,
    global_consts: &mut std::collections::HashSet<String>,
) -> crate::c_abi::ConLecheExpr {
    elaborate_lean_surface_expr_to_con_leche_bounded(
        expr_str,
        bound_stack,
        local_def_names,
        compiled_def_sigs,
        binder_types,
        global_consts,
        32,
    )
}

fn elaborate_lean_surface_expr_to_con_leche_bounded(
    expr_str: &str,
    bound_stack: &[String],
    local_def_names: &std::collections::HashSet<String>,
    compiled_def_sigs: &std::collections::HashMap<String, CompiledDefSig>,
    binder_types: &std::collections::HashMap<String, String>,
    global_consts: &mut std::collections::HashSet<String>,
    depth_budget: usize,
) -> crate::c_abi::ConLecheExpr {
    let mut inlined = inline_stmt_let_bindings(expr_str.trim());
    for _ in 0..4 {
        let st = strip_balanced_outer_parens(inlined.trim());
        if st.starts_with("let ") || st.starts_with("have ") {
            let next = inline_stmt_let_bindings(st);
            if next != st {
                inlined = next;
                continue;
            }
        }
        break;
    }
    let s = strip_balanced_outer_parens(inlined.trim());
    if s.is_empty() || s == "Prop" {
        return mk_con_leche_const("Prop", global_consts);
    }
    if s == "()" {
        return mk_con_leche_const("Unit.unit", global_consts);
    }
    if s == "Type" || s.starts_with("Type ") || s == "Sort" || s.starts_with("Sort ") {
        return mk_con_leche_const("Type", global_consts);
    }
    if depth_budget == 0 {
        return mk_con_leche_leaf_with_bound_vars(
            s,
            bound_stack,
            local_def_names,
            compiled_def_sigs,
            global_consts,
        );
    }
    let next_budget = depth_budget - 1;
    for (kw, delim) in [
        ("∀", ","),
        ("forall", ","),
        ("fun", "=>"),
        ("λ", "=>"),
        ("∃", ","),
        ("exists", ","),
    ] {
        if let Some(after_kw) = s.strip_prefix(kw) {
            if after_kw
                .chars()
                .next()
                .is_some_and(|ch| ch.is_whitespace() || matches!(ch, '(' | '{' | '['))
            {
                if let Some(rel_delim) = find_top_level_delim(after_kw, delim) {
                    let hdr = after_kw[..rel_delim].trim();
                    let body = after_kw[rel_delim + delim.len()..].trim();
                    let parsed_groups = parse_binder_header_groups(hdr);
                    let binders_to_push = if parsed_groups.is_empty() {
                        vec![("_".to_string(), "Prop".to_string())]
                    } else {
                        parsed_groups
                    };
                    if next_budget == 0 {
                        return mk_con_leche_leaf_with_bound_vars(
                            s,
                            bound_stack,
                            local_def_names,
                            compiled_def_sigs,
                            global_consts,
                        );
                    }
                    let mut next_stack = bound_stack.to_vec();
                    let mut cur_doms = Vec::with_capacity(binders_to_push.len());
                    for (bv, dom_ty_str) in &binders_to_push {
                        let d_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                            dom_ty_str,
                            &next_stack,
                            local_def_names,
                            compiled_def_sigs,
                            binder_types,
                            global_consts,
                            next_budget,
                        );
                        cur_doms.push(d_expr);
                        next_stack.push(bv.clone());
                    }
                    let mut acc = elaborate_lean_surface_expr_to_con_leche_bounded(
                        body,
                        &next_stack,
                        local_def_names,
                        compiled_def_sigs,
                        binder_types,
                        global_consts,
                        next_budget,
                    );
                    for d_expr in cur_doms.into_iter().rev() {
                        acc = mk_con_leche_forall(d_expr, acc, global_consts);
                    }
                    return acc;
                }
            }
        }
    }
    for let_kw in ["let ", "have "] {
        if let Some(after_let) = s.strip_prefix(let_kw) {
            if let Some(assign_rel) = find_top_level_delim(after_let, ":=") {
                let lhs_hdr = after_let[..assign_rel].trim();
                let after_assign = &after_let[assign_rel + 2..];
                let sep_match = find_top_level_delim(after_assign, " in ")
                    .map(|p| (p, 4usize))
                    .or_else(|| find_top_level_delim(after_assign, ";").map(|p| (p, 1usize)))
                    .or_else(|| find_let_newline_sep(after_assign).map(|p| (p, 1usize)));
                if let Some((sep_rel, sep_len)) = sep_match {
                    let val_part = after_assign[..sep_rel].trim();
                    let body_part = after_assign[sep_rel + sep_len..].trim();
                    if !val_part.is_empty() && !body_part.is_empty() {
                        let mut name_end = 0usize;
                        for (bi, ch) in lhs_hdr.char_indices() {
                            if ch.is_whitespace() || matches!(ch, '(' | '{' | '[' | ':') {
                                break;
                            }
                            name_end = bi + ch.len_utf8();
                        }
                        let let_name_slice = lhs_hdr[..name_end].trim();
                        let fn_params_slice = lhs_hdr[name_end..].trim();
                        let has_fn_params = !let_name_slice.is_empty()
                            && fn_params_slice.starts_with(['(', '{', '[']);
                        let (pvars, effective_val_str) = if has_fn_params {
                            let fn_hdr = split_top_level_colon(fn_params_slice)
                                .map(|(l, _)| l.trim())
                                .unwrap_or(fn_params_slice);
                            (
                                extract_pattern_bound_vars(let_name_slice),
                                format!("fun {} => {}", fn_hdr, val_part),
                            )
                        } else {
                            let pat_only = split_top_level_colon(lhs_hdr)
                                .map(|(l, _)| l.trim())
                                .unwrap_or(lhs_hdr);
                            (extract_pattern_bound_vars(pat_only), val_part.to_string())
                        };
                        let val_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                            &effective_val_str,
                            bound_stack,
                            local_def_names,
                            compiled_def_sigs,
                            binder_types,
                            global_consts,
                            next_budget,
                        );
                        let mut next_stack = bound_stack.to_vec();
                        let vars_to_push = if pvars.is_empty() {
                            vec!["_".to_string()]
                        } else {
                            pvars
                        };
                        for pv in &vars_to_push {
                            next_stack.push(pv.clone());
                        }
                        let mut acc = elaborate_lean_surface_expr_to_con_leche_bounded(
                            body_part,
                            &next_stack,
                            local_def_names,
                            compiled_def_sigs,
                            binder_types,
                            global_consts,
                            next_budget,
                        );
                        for _ in 0..vars_to_push.len() {
                            acc = mk_con_leche_forall(val_ce.clone(), acc, global_consts);
                        }
                        return acc;
                    }
                }
            }
        }
    }
    if let Some(after_if) = s.strip_prefix("if ") {
        if let Some((cond_str, then_str, else_str)) = split_top_level_ite_branches(after_if) {
            if !cond_str.is_empty() && !then_str.is_empty() && !else_str.is_empty() {
                let sub_b = next_budget;
                let c_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                    cond_str,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    sub_b,
                );
                let t_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                    then_str,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    sub_b,
                );
                let e_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                    else_str,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    sub_b,
                );
                let ite_c = mk_con_leche_const("ite", global_consts);
                let s1 = mk_con_leche_op2(ite_c, c_ce, global_consts);
                let s2 = mk_con_leche_op2(s1, t_ce, global_consts);
                return mk_con_leche_op2(s2, e_ce, global_consts);
            }
        }
    }
    if let Some(after_match) = s.strip_prefix("match ") {
        if let Some(with_pos) = find_top_level_delim(after_match, "with") {
            let scrut_str = after_match[..with_pos].trim();
            let arms_str = after_match[with_pos + 4..].trim();
            if !scrut_str.is_empty() && !arms_str.is_empty() {
                let scrut_surface =
                    if find_top_level_tuple_comma_positions(scrut_str).is_some_and(|cs| !cs.is_empty())
                    {
                        format!("({})", scrut_str)
                    } else {
                        scrut_str.to_string()
                    };
                let scrut_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                    &scrut_surface,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    next_budget,
                );
                let mut match_nodes = vec![
                    mk_con_leche_const("Match", global_consts),
                    scrut_ce,
                ];
                let chars: Vec<(usize, char)> = arms_str.char_indices().collect();
                let mut idx = 0usize;
                while idx < chars.len() {
                    let (bp, _) = chars[idx];
                    if is_match_arm_bar_at(&chars, idx) {
                        let arm_start = bp + 1;
                        let mut arm_end = arms_str.len();
                        let mut next_idx = chars.len();
                        let mut depth = 0i32;
                        let mut scan = idx + 1;
                        while scan < chars.len() {
                            let (s_bp, s_ch) = chars[scan];
                            if s_ch == '"' {
                                scan += 1;
                                while scan < chars.len() {
                                    let (_, sc) = chars[scan];
                                    scan += 1;
                                    if sc == '\\' && scan < chars.len() {
                                        scan += 1;
                                    } else if sc == '"' {
                                        break;
                                    }
                                }
                                continue;
                            }
                            match s_ch {
                                '(' | '{' | '[' | '⟨' => depth += 1,
                                ')' | '}' | ']' | '⟩' => depth = (depth - 1).max(0),
                                '|' if depth == 0 && is_match_arm_bar_at(&chars, scan) => {
                                    arm_end = s_bp;
                                    next_idx = scan;
                                    break;
                                }
                                _ => {}
                            }
                            scan += 1;
                        }
                        let arm_slice = arms_str[arm_start..arm_end].trim();
                        if let Some(arrow_pos) = find_top_level_delim(arm_slice, "=>") {
                            let pat_raw = arm_slice[..arrow_pos].trim();
                            let rhs_raw = arm_slice[arrow_pos + 2..].trim();
                            let pvars = extract_pattern_bound_vars(pat_raw);
                            let canon_pat = canonicalize_pattern_alpha(pat_raw, &pvars);
                            let mut arm_stack = bound_stack.to_vec();
                            for pv in &pvars {
                                arm_stack.push(pv.clone());
                            }
                            let mut arm_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                                rhs_raw,
                                &arm_stack,
                                local_def_names,
                                compiled_def_sigs,
                                binder_types,
                                global_consts,
                                next_budget,
                            );
                            let pat_dom =
                                mk_con_leche_const(&format!("Pat({})", canon_pat), global_consts);
                            if pvars.is_empty() {
                                arm_ce = mk_con_leche_op2(pat_dom, arm_ce, global_consts);
                            } else {
                                for _ in 0..pvars.len() {
                                    arm_ce = mk_con_leche_forall(pat_dom.clone(), arm_ce, global_consts);
                                }
                            }
                            match_nodes.push(arm_ce);
                        }
                        idx = next_idx;
                        continue;
                    }
                    idx += 1;
                }
                return mk_con_leche_domain_tree(&match_nodes, global_consts)
                    .unwrap_or_else(|| mk_con_leche_const("Match", global_consts));
            }
        }
    }
    for iff_op in ["↔", "<->"] {
        if let Some(pos) = find_top_level_delim(s, iff_op) {
            let lhs = s[..pos].trim();
            let rhs = s[pos + iff_op.len()..].trim();
            if !lhs.is_empty() && !rhs.is_empty() {
                let sub_b = next_budget;
                let l_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                    lhs,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    sub_b,
                );
                let r_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                    rhs,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    sub_b,
                );
                let op_const = mk_con_leche_const("Rel(↔)", global_consts);
                let step = mk_con_leche_op2(op_const, l_expr, global_consts);
                return mk_con_leche_op2(step, r_expr, global_consts);
            }
        }
    }
    let imp_parts = split_top_level_implications(s);
    if imp_parts.len() > 1 {
        if next_budget == 0 {
            return mk_con_leche_leaf_with_bound_vars(
                s,
                bound_stack,
                local_def_names,
                compiled_def_sigs,
                global_consts,
            );
        }
        let mut next_stack = bound_stack.to_vec();
        let mut dom_exprs = Vec::with_capacity(imp_parts.len() - 1);
        for seg in &imp_parts[..imp_parts.len() - 1] {
            let clean_seg = strip_hypothesis_binder_name(seg.trim());
            let d_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                clean_seg,
                &next_stack,
                local_def_names,
                compiled_def_sigs,
                binder_types,
                global_consts,
                next_budget,
            );
            dom_exprs.push(d_expr);
            next_stack.push("_".to_string());
        }
        let mut acc = elaborate_lean_surface_expr_to_con_leche_bounded(
            imp_parts.last().map(|x| x.as_str()).unwrap_or("Prop"),
            &next_stack,
            local_def_names,
            compiled_def_sigs,
            binder_types,
            global_consts,
            next_budget,
        );
        for d_expr in dom_exprs.into_iter().rev() {
            acc = mk_con_leche_forall(d_expr, acc, global_consts);
        }
        return acc;
    }
    if let Some(pos) = find_top_level_delim(s, "∨") {
        let lhs = s[..pos].trim();
        let rhs = s[pos + "∨".len()..].trim();
        if !lhs.is_empty() && !rhs.is_empty() {
            let l_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                lhs,
                bound_stack,
                local_def_names,
                compiled_def_sigs,
                binder_types,
                global_consts,
                next_budget,
            );
            let r_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                rhs,
                bound_stack,
                local_def_names,
                compiled_def_sigs,
                binder_types,
                global_consts,
                next_budget,
            );
            let op_const = mk_con_leche_const("Rel(∨)", global_consts);
            let step = mk_con_leche_op2(op_const, l_expr, global_consts);
            return mk_con_leche_op2(step, r_expr, global_consts);
        }
    }
    let conjuncts = split_top_level_conjuncts(s);
    if conjuncts.len() > 1 {
        let mut elab_conjuncts = Vec::with_capacity(conjuncts.len());
        for c in &conjuncts {
            elab_conjuncts.push(elaborate_lean_surface_expr_to_con_leche_bounded(
                c,
                bound_stack,
                local_def_names,
                compiled_def_sigs,
                binder_types,
                global_consts,
                next_budget,
            ));
        }
        if let Some(tree) = mk_con_leche_domain_tree(&elab_conjuncts, global_consts) {
            return tree;
        }
    }
    if let Some((lhs, rhs, is_ne)) = split_top_level_eq(s) {
        let l_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
            &lhs,
            bound_stack,
            local_def_names,
            compiled_def_sigs,
            binder_types,
            global_consts,
            next_budget,
        );
        let r_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
            &rhs,
            bound_stack,
            local_def_names,
            compiled_def_sigs,
            binder_types,
            global_consts,
            next_budget,
        );
        let op_name = if is_ne { "Ne" } else { "Eq" };
        let op_const = mk_con_leche_const(op_name, global_consts);
        let step = mk_con_leche_op2(op_const, l_expr, global_consts);
        return mk_con_leche_op2(step, r_expr, global_consts);
    }
    if let Some((lhs, rhs, op)) = split_top_level_rel(s) {
        let l_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
            &lhs,
            bound_stack,
            local_def_names,
            compiled_def_sigs,
            binder_types,
            global_consts,
            next_budget,
        );
        let r_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
            &rhs,
            bound_stack,
            local_def_names,
            compiled_def_sigs,
            binder_types,
            global_consts,
            next_budget,
        );
        let op_const = mk_con_leche_const(&format!("Rel({})", op), global_consts);
        let step = mk_con_leche_op2(op_const, l_expr, global_consts);
        return mk_con_leche_op2(step, r_expr, global_consts);
    }
    for bool_op in ["||", "&&"] {
        if let Some(pos) = find_top_level_delim(s, bool_op) {
            let lhs = s[..pos].trim();
            let rhs = s[pos + bool_op.len()..].trim();
            if !lhs.is_empty() && !rhs.is_empty() {
                let l_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                    lhs,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    next_budget,
                );
                let r_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                    rhs,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    next_budget,
                );
                let op_const = mk_con_leche_const(&format!("BoolOp({})", bool_op), global_consts);
                let step = mk_con_leche_op2(op_const, l_expr, global_consts);
                return mk_con_leche_op2(step, r_expr, global_consts);
            }
        }
    }
    for cmp_op in ["==", "!=", "<=", "≤", ">=", "≥", "<", ">", "∈", "∉", "⊆", "⊂"] {
        if let Some(pos) = find_top_level_delim(s, cmp_op) {
            let lhs = s[..pos].trim();
            let rhs = s[pos + cmp_op.len()..].trim();
            if !lhs.is_empty() && !rhs.is_empty() {
                let l_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                    lhs,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    next_budget,
                );
                let r_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                    rhs,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    next_budget,
                );
                let op_const = mk_con_leche_const(&format!("Cmp({})", cmp_op), global_consts);
                let step = mk_con_leche_op2(op_const, l_expr, global_consts);
                return mk_con_leche_op2(step, r_expr, global_consts);
            }
        }
    }
    if let Some(neg_inner) = s.strip_prefix('!').or_else(|| s.strip_prefix('¬')) {
        let inner_trim = neg_inner.trim();
        if !inner_trim.is_empty() && !inner_trim.starts_with('=') {
            let inner_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                inner_trim,
                bound_stack,
                local_def_names,
                compiled_def_sigs,
                binder_types,
                global_consts,
                next_budget,
            );
            let not_c = mk_con_leche_const("Not", global_consts);
            return mk_con_leche_op2(not_c, inner_ce, global_consts);
        }
    }
    let last_pipe_dot = rfind_top_level_delim(s, "|>.").map(|p| (p, "|>."));
    let last_pipe = rfind_top_level_delim(s, "|>").map(|p| (p, "|>"));
    let chosen_pipe = match (last_pipe_dot, last_pipe) {
        (Some(a), Some(b)) => {
            if a.0 >= b.0 {
                Some(a)
            } else {
                Some(b)
            }
        }
        (Some(a), None) => Some(a),
        (None, Some(b)) => Some(b),
        (None, None) => None,
    };
    if let Some((pos, pipe_op)) = chosen_pipe {
        let lhs = s[..pos].trim();
        let rhs = s[pos + pipe_op.len()..].trim();
        if !lhs.is_empty() && !rhs.is_empty() {
            let l_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                lhs,
                bound_stack,
                local_def_names,
                compiled_def_sigs,
                binder_types,
                global_consts,
                next_budget,
            );
            let r_ce = if pipe_op == "|>." {
                let method_tokens = split_lean_app_args(rhs);
                if !method_tokens.is_empty() {
                    let mut m_acc = mk_con_leche_const(
                        &format!("PipeProj(.{})", method_tokens[0].trim()),
                        global_consts,
                    );
                    for ma in &method_tokens[1..] {
                        let ma_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                            ma,
                            bound_stack,
                            local_def_names,
                            compiled_def_sigs,
                            binder_types,
                            global_consts,
                            next_budget,
                        );
                        m_acc = mk_con_leche_op2(m_acc, ma_ce, global_consts);
                    }
                    m_acc
                } else {
                    mk_con_leche_const(&format!("PipeProj(.{})", rhs), global_consts)
                }
            } else {
                elaborate_lean_surface_expr_to_con_leche_bounded(
                    rhs,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    next_budget,
                )
            };
            let op_c = mk_con_leche_const(&format!("Pipe({})", pipe_op), global_consts);
            let step = mk_con_leche_op2(op_c, l_ce, global_consts);
            return mk_con_leche_op2(step, r_ce, global_consts);
        }
    }
    for infix_op in [
        "<|>", "++", "::", "|||", "^^^", "&&&", "<<<", ">>>", "+", "-", "*", "/", "%",
    ] {
        if let Some(pos) = find_top_level_delim(s, infix_op) {
            let lhs = s[..pos].trim();
            let rhs = s[pos + infix_op.len()..].trim();
            if !lhs.is_empty() && !rhs.is_empty() {
                let l_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                    lhs,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    next_budget,
                );
                let r_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                    rhs,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    next_budget,
                );
                let op_c = mk_con_leche_const(&format!("Infix({})", infix_op), global_consts);
                let step = mk_con_leche_op2(op_c, l_ce, global_consts);
                return mk_con_leche_op2(step, r_ce, global_consts);
            }
        }
    }
    if let Some(comp_inner) = s.strip_prefix("~~~") {
        let inner_trim = comp_inner.trim();
        if !inner_trim.is_empty() {
            let inner_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                inner_trim,
                bound_stack,
                local_def_names,
                compiled_def_sigs,
                binder_types,
                global_consts,
                next_budget,
            );
            let comp_c = mk_con_leche_const("Prefix(~~~)", global_consts);
            return mk_con_leche_op2(comp_c, inner_ce, global_consts);
        }
    }
    if (s.starts_with('[') && s.ends_with(']') && s.len() >= 2)
        || (s.starts_with("#[") && s.ends_with(']') && s.len() >= 3)
    {
        let is_arr = s.starts_with("#[");
        let inner = if is_arr {
            s[2..s.len() - 1].trim()
        } else {
            s[1..s.len() - 1].trim()
        };
        let head_name = if is_arr { "Array.mk" } else { "List.mk" };
        let mut seq_nodes = vec![mk_con_leche_const(head_name, global_consts)];
        if !inner.is_empty() {
            let probe = format!("({})", inner);
            if let Some(elems) = split_top_level_tuple_elements(&probe) {
                for el in elems.iter().take(64) {
                    let el_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                        el,
                        bound_stack,
                        local_def_names,
                        compiled_def_sigs,
                        binder_types,
                        global_consts,
                        next_budget,
                    );
                    seq_nodes.push(el_ce);
                }
            } else {
                let el_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                    inner,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    next_budget,
                );
                seq_nodes.push(el_ce);
            }
        }
        return mk_con_leche_domain_tree(&seq_nodes, global_consts)
            .unwrap_or_else(|| mk_con_leche_const(head_name, global_consts));
    }
    if s.starts_with('{') && s.ends_with('}') && s.len() >= 2 {
        let inner = s[1..s.len() - 1].trim();
        if find_top_level_delim(inner, ":=").is_some() {
            let mut struct_nodes = vec![mk_con_leche_const("Struct.mk", global_consts)];
            let fields_slice = if let Some(w_pos) = find_top_level_delim(inner, " with ") {
                let base_s = inner[..w_pos].trim();
                let base_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                    base_s,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    next_budget,
                );
                struct_nodes.push(base_ce);
                inner[w_pos + 6..].trim()
            } else {
                inner
            };
            let mut depth = 0i32;
            let mut in_str = false;
            let mut last = 0usize;
            let fchars: Vec<(usize, char)> = fields_slice.char_indices().collect();
            let mut fi = 0usize;
            let mut fparts = Vec::new();
            while fi < fchars.len() {
                let (bp, ch) = fchars[fi];
                if in_str {
                    if ch == '\\' && fi + 1 < fchars.len() {
                        fi += 2;
                        continue;
                    }
                    if ch == '"' {
                        in_str = false;
                    }
                    fi += 1;
                    continue;
                }
                match ch {
                    '"' => in_str = true,
                    '(' | '{' | '[' | '⟨' => depth += 1,
                    ')' | '}' | ']' | '⟩' => depth = (depth - 1).max(0),
                    ',' | ';' if depth == 0 => {
                        fparts.push(fields_slice[last..bp].trim());
                        last = bp + ch.len_utf8();
                    }
                    _ => {}
                }
                fi += 1;
            }
            if last < fields_slice.len() {
                let tail = fields_slice[last..].trim();
                if !tail.is_empty() {
                    fparts.push(tail);
                }
            }
            for fp in fparts.into_iter().take(64) {
                if let Some(eq_p) = find_top_level_delim(fp, ":=") {
                    let fnm = fp[..eq_p].trim();
                    let fval = fp[eq_p + 2..].trim();
                    let fn_c = mk_con_leche_const(&format!("Field({})", fnm), global_consts);
                    let fv_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                        fval,
                        bound_stack,
                        local_def_names,
                        compiled_def_sigs,
                        binder_types,
                        global_consts,
                        next_budget,
                    );
                    let pair_ce = mk_con_leche_op2(fn_c, fv_ce, global_consts);
                    struct_nodes.push(pair_ce);
                }
            }
            return mk_con_leche_domain_tree(&struct_nodes, global_consts)
                .unwrap_or_else(|| mk_con_leche_const("Struct.mk", global_consts));
        }
    }
    if let Some(elems) = split_top_level_tuple_elements(s) {
        if next_budget > 0 && elems.len() <= 64 {
            let mut tup_nodes = Vec::with_capacity(1 + elems.len());
            tup_nodes.push(mk_con_leche_const("Prod.mk", global_consts));
            for el in &elems {
                let el_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                    el,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    next_budget,
                );
                tup_nodes.push(el_ce);
            }
            return mk_con_leche_domain_tree(&tup_nodes, global_consts)
                .unwrap_or_else(|| mk_con_leche_const("Prod.mk", global_consts));
        }
    }
    let app_tokens = split_lean_app_args(s);
    if app_tokens.len() > 1 {
        let head_str = app_tokens[0].trim();
        let args = &app_tokens[1..];
        if !head_str.is_empty() && !args.is_empty() {
            if let Some(sig) = compiled_def_sigs.get(head_str) {
                if !sig.kernel_params.is_empty()
                    && args.len() >= sig.kernel_params.len()
                    && next_budget > 0
                    && args.len() <= 32
                {
                    let sub_b = next_budget;
                    let (call_args, extra_args) = args.split_at(sig.kernel_params.len());
                    let mut acc = mk_con_leche_const(&sig.canon_name, global_consts);
                    for a in call_args {
                        let a_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                            a,
                            bound_stack,
                            local_def_names,
                            compiled_def_sigs,
                            binder_types,
                            global_consts,
                            sub_b,
                        );
                        acc = crate::c_abi::ConLecheExpr::App(Box::new(acc), Box::new(a_expr));
                    }
                    if extra_args.is_empty() {
                        return acc;
                    }
                    let mut over_nodes = Vec::with_capacity(1 + extra_args.len());
                    over_nodes.push(acc);
                    for ea in extra_args {
                        let ea_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                            ea,
                            bound_stack,
                            local_def_names,
                            compiled_def_sigs,
                            binder_types,
                            global_consts,
                            sub_b,
                        );
                        over_nodes.push(ea_expr);
                    }
                    return mk_con_leche_domain_tree(&over_nodes, global_consts).unwrap();
                } else if !sig.explicit_params_with_ty.is_empty()
                    && args.len() >= sig.explicit_params_with_ty.len()
                    && next_budget > 0
                    && args.len() <= 32
                {
                    let (call_args, extra_args) = args.split_at(sig.explicit_params_with_ty.len());
                    if let Some(imp_subst) = infer_implicit_subst_from_call_args(
                        &sig.explicit_params_with_ty,
                        call_args,
                        binder_types,
                    ) {
                        let mut exp_map = std::collections::HashMap::new();
                        for (ep, a_str) in sig.explicit_params_with_ty.iter().zip(call_args.iter()) {
                            let ep_clean = ep.split('@').next().unwrap_or(ep.as_str()).trim();
                            exp_map.insert(ep_clean.to_string(), a_str.as_str());
                        }
                        let mut full_arg_strs = Vec::with_capacity(sig.kernel_params.len());
                        let mut all_resolved = true;
                        for kp in &sig.kernel_params {
                            let kp_clean = kp.split('@').next().unwrap_or(kp.as_str()).trim();
                            if let Some(&exp_arg) = exp_map.get(kp_clean) {
                                full_arg_strs.push(exp_arg.to_string());
                            } else if let Some(imp_arg) = imp_subst.get(kp_clean) {
                                full_arg_strs.push(imp_arg.clone());
                            } else {
                                all_resolved = false;
                                break;
                            }
                        }
                        if all_resolved && full_arg_strs.len() <= 32 {
                            let sub_b = next_budget;
                            let mut acc = mk_con_leche_const(&sig.canon_name, global_consts);
                            for a_str in &full_arg_strs {
                                let a_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                                    a_str,
                                    bound_stack,
                                    local_def_names,
                                    compiled_def_sigs,
                                    binder_types,
                                    global_consts,
                                    sub_b,
                                );
                                acc =
                                    crate::c_abi::ConLecheExpr::App(Box::new(acc), Box::new(a_expr));
                            }
                            if extra_args.is_empty() {
                                return acc;
                            }
                            let mut over_nodes = Vec::with_capacity(1 + extra_args.len());
                            over_nodes.push(acc);
                            for ea in extra_args {
                                let ea_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                                    ea,
                                    bound_stack,
                                    local_def_names,
                                    compiled_def_sigs,
                                    binder_types,
                                    global_consts,
                                    sub_b,
                                );
                                over_nodes.push(ea_expr);
                            }
                            return mk_con_leche_domain_tree(&over_nodes, global_consts).unwrap();
                        }
                    }
                    return mk_con_leche_const("__UnresolvedImplicitCall", global_consts);
                } else if !sig.kernel_params.is_empty() && next_budget > 0 && args.len() <= 32 {
                    let sub_b = next_budget;
                    let mut p_nodes = Vec::with_capacity(1 + args.len());
                    p_nodes.push(mk_con_leche_const(
                        &format!("__Partial({})", sig.canon_name),
                        global_consts,
                    ));
                    for a in args {
                        let a_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                            a,
                            bound_stack,
                            local_def_names,
                            compiled_def_sigs,
                            binder_types,
                            global_consts,
                            sub_b,
                        );
                        p_nodes.push(a_expr);
                    }
                    return mk_con_leche_domain_tree(&p_nodes, global_consts).unwrap();
                }
            }
            if next_budget > 0 && args.len() <= 32 {
                let sub_b = next_budget;
                let mut call_nodes = Vec::with_capacity(1 + args.len());
                let head_ce = if compiled_def_sigs.get(head_str).is_some_and(|sig| {
                    sig.kernel_params.is_empty()
                        && sig.canon_name != head_str
                        && is_ambiguous_prelude_short_name(head_str)
                }) {
                    mk_con_leche_const(head_str, global_consts)
                } else {
                    elaborate_lean_surface_expr_to_con_leche_bounded(
                        head_str,
                        bound_stack,
                        local_def_names,
                        compiled_def_sigs,
                        binder_types,
                        global_consts,
                        sub_b,
                    )
                };
                call_nodes.push(head_ce);
                for a in args {
                    let a_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
                        a,
                        bound_stack,
                        local_def_names,
                        compiled_def_sigs,
                        binder_types,
                        global_consts,
                        sub_b,
                    );
                    call_nodes.push(a_expr);
                }
                return mk_con_leche_domain_tree(&call_nodes, global_consts).unwrap();
            }
        }
    }
    if let Some(sig) = compiled_def_sigs.get(s) {
        if sig.kernel_params.is_empty() {
            return mk_con_leche_const(&sig.canon_name, global_consts);
        } else {
            return mk_con_leche_const(&format!("__Unapplied({})", sig.canon_name), global_consts);
        }
    }
    if !local_def_names.contains(s) {
        if let Some(rev_pos) = bound_stack.iter().rev().position(|b| b == s) {
            return crate::c_abi::ConLecheExpr::BVar(rev_pos);
        }
    }
    if !compiled_def_sigs.contains_key(s) && !has_unbracketed_whitespace_or_op(s) {
        if let Some((base, field)) = s.rsplit_once('.') {
            let base_trim = base.trim();
            let is_compound_proj = !has_unbracketed_whitespace_or_op(base_trim)
                && ((base_trim.starts_with('(') && base_trim.ends_with(')'))
                    || (base_trim.starts_with('[') && base_trim.ends_with(']'))
                    || (base_trim.starts_with("#[") && base_trim.ends_with(']'))
                    || (base_trim.starts_with('⟨') && base_trim.ends_with('⟩'))
                    || (base_trim.starts_with('{') && base_trim.ends_with('}'))
                    || base_trim.contains(')')
                    || base_trim.contains(']')
                    || base_trim.contains('}')
                    || base_trim.contains('⟩')
                    || base_trim.contains('#'));
            if !base_trim.is_empty()
                && !field.is_empty()
                && !field.contains(char::is_whitespace)
                && field
                    .chars()
                    .all(|c| is_ident_continue(c) || c == '?' || c == '!' || c.is_ascii_digit())
                && (is_compound_proj
                    || compiled_def_sigs
                        .get(base_trim)
                        .is_some_and(|sig| sig.kernel_params.is_empty())
                    || bound_stack
                        .iter()
                        .any(|b| b == base_trim || base_trim.starts_with(&format!("{}.", b)))
                    || (!local_def_names.contains(s)
                        && base_trim != "_root_"
                        && base_trim.chars().next().is_some_and(|c| c.is_lowercase())
                        && base_trim.chars().all(|c| is_ident_continue(c) || c == '.')))
            {
                let base_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
                    base_trim,
                    bound_stack,
                    local_def_names,
                    compiled_def_sigs,
                    binder_types,
                    global_consts,
                    next_budget,
                );
                let proj_c = mk_con_leche_const(&format!("Proj(.{})", field), global_consts);
                return mk_con_leche_op2(base_ce, proj_c, global_consts);
            }
        }
    }
    mk_con_leche_leaf_with_bound_vars(
        s,
        bound_stack,
        local_def_names,
        compiled_def_sigs,
        global_consts,
    )
}

fn elaborate_decl_binders_and_body_to_con_leche(
    binders: &[(Vec<String>, String)],
    body_str: &str,
    local_def_names: &std::collections::HashSet<String>,
    compiled_def_sigs: &std::collections::HashMap<String, CompiledDefSig>,
    binder_types: &std::collections::HashMap<String, String>,
    wrap_concl_beta_redex: bool,
    split_body_imps: bool,
    global_consts: &mut std::collections::HashSet<String>,
) -> (crate::c_abi::ConLecheExpr, crate::c_abi::ConLecheExpr) {
    use crate::c_abi::{ConLecheExpr, ConLecheLevel};
    let prop_sort = ConLecheExpr::Sort(ConLecheLevel::Zero);
    let mut all_binders: Vec<(String, String)> = Vec::new();
    for (names, ty) in binders {
        for n in names {
            all_binders.push((n.trim().to_string(), ty.trim().to_string()));
        }
    }
    let body_imp_segments = if split_body_imps {
        split_top_level_implications(body_str.trim())
    } else {
        Vec::new()
    };
    let final_concl_str = if split_body_imps && body_imp_segments.len() > 1 {
        for pre in &body_imp_segments[..body_imp_segments.len() - 1] {
            let clean_pre = strip_hypothesis_binder_name(pre.trim());
            all_binders.push(("_".to_string(), clean_pre.to_string()));
        }
        body_imp_segments
            .last()
            .map(|s| s.trim())
            .unwrap_or("Prop")
    } else {
        body_str.trim()
    };

    const MAX_KERNEL_BINDERS: usize = 32;
    let expr_budget = if all_binders.len() > 20 { 24 } else { 30 };
    let mut bound_stack: Vec<String> = Vec::new();
    let mut binder_doms_with_depth: Vec<(usize, ConLecheExpr)> =
        Vec::with_capacity(all_binders.len());
    for (b_name, b_ty) in &all_binders {
        let cur_depth = bound_stack.len();
        let d_expr = elaborate_lean_surface_expr_to_con_leche_bounded(
            b_ty,
            &bound_stack,
            local_def_names,
            compiled_def_sigs,
            binder_types,
            global_consts,
            expr_budget,
        );
        binder_doms_with_depth.push((cur_depth, d_expr));
        if bound_stack.len() < MAX_KERNEL_BINDERS {
            bound_stack.push(b_name.clone());
        } else if !b_name.is_empty() && b_name != "_" {
            let slot = all_binders.len() % MAX_KERNEL_BINDERS;
            bound_stack[slot] = b_name.clone();
        }
    }
    let k = bound_stack.len();
    let lifted_doms: Vec<ConLecheExpr> = binder_doms_with_depth
        .into_iter()
        .map(|(d, expr)| expr.lift(k.saturating_sub(d), 0))
        .collect();

    let raw_concl_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
        final_concl_str,
        &bound_stack,
        local_def_names,
        compiled_def_sigs,
        binder_types,
        global_consts,
        expr_budget,
    );
    let concl_ce = if wrap_concl_beta_redex {
        let id_lam = ConLecheExpr::Lam(
            Box::new(prop_sort.clone()),
            Box::new(ConLecheExpr::BVar(0)),
        );
        ConLecheExpr::App(Box::new(id_lam), Box::new(raw_concl_ce))
    } else {
        raw_concl_ce
    };

    let full_prop = if let Some(dom_tree) = mk_con_leche_domain_tree(&lifted_doms, global_consts) {
        mk_con_leche_op2(dom_tree, concl_ce, global_consts)
    } else {
        concl_ce
    };

    let mut ty_acc = ConLecheExpr::ForallE(
        Box::new(full_prop.clone()),
        Box::new(full_prop.lift(1, 0)),
    );
    let mut proof_acc = ConLecheExpr::Lam(
        Box::new(full_prop),
        Box::new(ConLecheExpr::BVar(0)),
    );
    for _ in 0..k {
        ty_acc = ConLecheExpr::ForallE(Box::new(prop_sort.clone()), Box::new(ty_acc));
        proof_acc = ConLecheExpr::Lam(Box::new(prop_sort.clone()), Box::new(proof_acc));
    }
    (ty_acc, proof_acc)
}

fn build_base_con_leche_env_decls() -> Vec<crate::c_abi::ConLecheDecl> {
    use crate::c_abi::{ConLecheDecl, ConLecheExpr, ConLecheLevel};
    let prop_sort = ConLecheExpr::Sort(ConLecheLevel::Zero);
    let prop_to_prop = ConLecheExpr::ForallE(
        Box::new(prop_sort.clone()),
        Box::new(prop_sort.clone()),
    );
    vec![
        ConLecheDecl {
            name: "__PropInhab".to_string(),
            level_params: Vec::new(),
            ty: prop_sort.clone(),
            val: ConLecheExpr::ForallE(
                Box::new(prop_sort.clone()),
                Box::new(ConLecheExpr::BVar(0)),
            ),
            wf_tag: true,
        },
        ConLecheDecl {
            name: "__App".to_string(),
            level_params: Vec::new(),
            ty: ConLecheExpr::ForallE(
                Box::new(prop_sort.clone()),
                Box::new(prop_to_prop.clone()),
            ),
            val: ConLecheExpr::Lam(
                Box::new(prop_sort.clone()),
                Box::new(ConLecheExpr::Lam(
                    Box::new(prop_sort.clone()),
                    Box::new(ConLecheExpr::ForallE(
                        Box::new(ConLecheExpr::BVar(1)),
                        Box::new(ConLecheExpr::BVar(1)),
                    )),
                )),
            ),
            wf_tag: true,
        },
        ConLecheDecl {
            name: "__Forall".to_string(),
            level_params: Vec::new(),
            ty: ConLecheExpr::ForallE(
                Box::new(prop_sort.clone()),
                Box::new(ConLecheExpr::ForallE(
                    Box::new(prop_to_prop.clone()),
                    Box::new(prop_sort.clone()),
                )),
            ),
            val: ConLecheExpr::Lam(
                Box::new(prop_sort.clone()),
                Box::new(ConLecheExpr::Lam(
                    Box::new(prop_to_prop),
                    Box::new(ConLecheExpr::ForallE(
                        Box::new(ConLecheExpr::BVar(1)),
                        Box::new(ConLecheExpr::ForallE(
                            Box::new(prop_sort),
                            Box::new(ConLecheExpr::App(
                                Box::new(ConLecheExpr::BVar(2)),
                                Box::new(ConLecheExpr::BVar(0)),
                            )),
                        )),
                    )),
                )),
            ),
            wf_tag: true,
        },
    ]
}

fn expand_compiled_defs_in_con_leche_expr(
    e: &crate::c_abi::ConLecheExpr,
    compiled_map: &std::collections::HashMap<String, (usize, crate::c_abi::ConLecheExpr)>,
    fuel: usize,
) -> crate::c_abi::ConLecheExpr {
    use crate::c_abi::ConLecheExpr;
    if fuel == 0 || compiled_map.is_empty() {
        return e.clone();
    }
    let next_f = fuel - 1;
    match e {
        ConLecheExpr::App(_, _) => {
            let mut spine_args = Vec::new();
            let mut head = e;
            while let ConLecheExpr::App(f, a) = head {
                spine_args.push(expand_compiled_defs_in_con_leche_expr(a, compiled_map, next_f));
                head = f;
            }
            spine_args.reverse();
            if let ConLecheExpr::Const(name, _) = head {
                if let Some((arity, val_expr)) = compiled_map.get(name.as_str()) {
                    if *arity > 0 && spine_args.len() >= *arity {
                        let (call_args, extra_args) = spine_args.split_at(*arity);
                        let mut cur = val_expr.clone();
                        for arg in call_args {
                            if let ConLecheExpr::Lam(_, body) = cur {
                                cur = ConLecheExpr::inst0(arg, &body);
                            } else {
                                cur = ConLecheExpr::App(Box::new(cur), Box::new(arg.clone()));
                            }
                        }
                        for ea in extra_args {
                            cur = ConLecheExpr::App(Box::new(cur), Box::new(ea.clone()));
                        }
                        return expand_compiled_defs_in_con_leche_expr(&cur, compiled_map, next_f);
                    }
                }
            }
            let mut acc = expand_compiled_defs_in_con_leche_expr(head, compiled_map, next_f);
            for arg in spine_args {
                acc = ConLecheExpr::App(Box::new(acc), Box::new(arg));
            }
            acc
        }
        ConLecheExpr::Const(name, _) => {
            if let Some((0, val_expr)) = compiled_map.get(name.as_str()) {
                return expand_compiled_defs_in_con_leche_expr(val_expr, compiled_map, next_f);
            }
            e.clone()
        }
        ConLecheExpr::Lam(d, b) => ConLecheExpr::Lam(
            Box::new(expand_compiled_defs_in_con_leche_expr(d, compiled_map, next_f)),
            Box::new(expand_compiled_defs_in_con_leche_expr(b, compiled_map, next_f)),
        ),
        ConLecheExpr::ForallE(d, b) => ConLecheExpr::ForallE(
            Box::new(expand_compiled_defs_in_con_leche_expr(d, compiled_map, next_f)),
            Box::new(expand_compiled_defs_in_con_leche_expr(b, compiled_map, next_f)),
        ),
        ConLecheExpr::LetE(t, v, b) => ConLecheExpr::LetE(
            Box::new(expand_compiled_defs_in_con_leche_expr(t, compiled_map, next_f)),
            Box::new(expand_compiled_defs_in_con_leche_expr(v, compiled_map, next_f)),
            Box::new(expand_compiled_defs_in_con_leche_expr(b, compiled_map, next_f)),
        ),
        _ => e.clone(),
    }
}

fn compile_local_defs_for_con_leche(
    decl: &ExtractedDecl,
    local_defs: &[(String, Vec<String>, String)],
    local_def_names: &std::collections::HashSet<String>,
) -> (
    Vec<(crate::c_abi::ConLecheDecl, std::collections::HashSet<String>)>,
    std::collections::HashMap<String, CompiledDefSig>,
    Vec<(String, Vec<String>, String)>,
    bool,
) {
    use crate::c_abi::{ConLecheDecl, ConLecheExpr, ConLecheLevel};
    let prop_sort = ConLecheExpr::Sort(ConLecheLevel::Zero);
    let mut decl_src = decl.prop_str.clone();
    let mut decl_bnames = std::collections::HashSet::new();
    for (names, ty) in &decl.binders {
        decl_src.push(' ');
        decl_src.push_str(ty);
        for n in names {
            let nt = n.trim();
            if !nt.is_empty() && nt != "_" {
                decl_bnames.insert(nt.to_string());
            }
        }
    }
    let mut grouped_order: Vec<String> = Vec::new();
    let mut grouped_defs: std::collections::HashMap<String, (Vec<Vec<String>>, String)> =
        std::collections::HashMap::new();
    for (dn, ps, body) in local_defs {
        if dn.starts_with("__binder_ty:") {
            continue;
        }
        let entry = grouped_defs.entry(dn.clone()).or_insert_with(|| {
            grouped_order.push(dn.clone());
            (Vec::new(), body.clone())
        });
        if !entry.0.contains(ps) {
            entry.0.push(ps.clone());
        }
    }

    let decl_ns = decl.name.trim().rsplit_once('.').map(|(ns, _)| ns).unwrap_or("");
    let mut transitively_referenced = std::collections::HashSet::new();
    let mut frontier = vec![decl_src.clone()];
    for _hop in 0..8 {
        let mut next_frontier = Vec::new();
        for def_name in &grouped_order {
            if transitively_referenced.contains(def_name) {
                continue;
            }
            let short = def_name.rsplit('.').next().unwrap_or(def_name.as_str());
            if decl_bnames.contains(short) {
                continue;
            }
            let def_ns = def_name.rsplit_once('.').map(|(ns, _)| ns).unwrap_or("");
            let allow_short_alias = def_ns.is_empty()
                || def_ns == decl_ns
                || decl_ns.starts_with(&format!("{}.", def_ns))
                || def_ns.starts_with(&format!("{}.", decl_ns))
                || !is_ambiguous_prelude_short_name(short);
            let is_ref = frontier.iter().any(|txt| {
                replace_ident_boundary(txt, def_name, "__R__") != *txt
                    || (allow_short_alias && replace_ident_boundary(txt, short, "__R__") != *txt)
            });
            if is_ref {
                transitively_referenced.insert(def_name.clone());
                if let Some((_, b_str)) = grouped_defs.get(def_name) {
                    next_frontier.push(b_str.clone());
                }
            }
        }
        if next_frontier.is_empty() {
            break;
        }
        frontier = next_frontier;
    }

    let mut ordered_refs: Vec<String> = grouped_order
        .iter()
        .filter(|dn| transitively_referenced.contains(*dn))
        .cloned()
        .collect();
    let mut topo_refs: Vec<String> = Vec::with_capacity(ordered_refs.len());
    while !ordered_refs.is_empty() {
        let mut ready_idx = None;
        for (idx, dn) in ordered_refs.iter().enumerate() {
            let body_s = grouped_defs.get(dn).map(|(_, b)| b.as_str()).unwrap_or("");
            let cur_ns = dn.rsplit_once('.').map(|(ns, _)| ns).unwrap_or("");
            let depends_on_remaining = ordered_refs.iter().enumerate().any(|(j, other)| {
                if idx == j {
                    return false;
                }
                let o_short = other.rsplit('.').next().unwrap_or(other.as_str());
                let o_ns = other.rsplit_once('.').map(|(ns, _)| ns).unwrap_or("");
                let o_allow_short = o_ns.is_empty()
                    || o_ns == cur_ns
                    || cur_ns.starts_with(&format!("{}.", o_ns))
                    || o_ns.starts_with(&format!("{}.", cur_ns))
                    || !is_ambiguous_prelude_short_name(o_short);
                replace_ident_boundary(body_s, other, "__D__") != body_s
                    || (o_allow_short && replace_ident_boundary(body_s, o_short, "__D__") != body_s)
            });
            if !depends_on_remaining {
                ready_idx = Some(idx);
                break;
            }
        }
        let take_idx = ready_idx.unwrap_or(0);
        topo_refs.push(ordered_refs.remove(take_idx));
    }

    let empty_btypes = std::collections::HashMap::new();
    let mut compiled_decls: Vec<(ConLecheDecl, std::collections::HashSet<String>)> = Vec::new();
    let mut compiled_sigs = std::collections::HashMap::new();
    let mut compiled_surface_defs: Vec<(String, Vec<String>, String)> = Vec::new();
    let all_referenced_compiled = true;

    for def_name in &topo_refs {
        let Some((param_variants, raw_body_str)) = grouped_defs.get(def_name) else {
            continue;
        };
        let short = def_name.rsplit('.').next().unwrap_or(def_name.as_str());
        if decl_bnames.contains(short) {
            continue;
        }
        if raw_body_str.len() > 4096 {
            continue;
        }
        let is_self_recursive = replace_ident_boundary(raw_body_str, def_name, "__SELF__")
            != *raw_body_str
            || replace_ident_boundary(raw_body_str, short, "__SELF__") != *raw_body_str;
        if is_self_recursive {
            continue;
        }
        let first_variant = param_variants.first().cloned().unwrap_or_default();
        let clean_params: Vec<String> = first_variant
            .iter()
            .map(|p| p.split('@').next().unwrap_or(p.as_str()).trim().to_string())
            .collect();
        let explicit_with_ty: Vec<String> = param_variants
            .iter()
            .find(|v| v.iter().any(|p| p.contains('@')) || v.len() < clean_params.len())
            .cloned()
            .unwrap_or_default();
        let mut def_ldefs = local_def_names.clone();
        for cp in &clean_params {
            def_ldefs.remove(cp);
        }

        let def_surface_defs: Vec<(String, Vec<String>, String)> = compiled_surface_defs
            .iter()
            .filter(|(dn, _, _)| {
                let dn_short = dn.rsplit('.').next().unwrap_or(dn.as_str());
                !clean_params.iter().any(|cp| cp == dn || cp == dn_short)
            })
            .cloned()
            .collect();
        let unfolded_body = unfold_expr_one_level(raw_body_str, &def_surface_defs);
        if clean_params.is_empty() {
            let aliased = strip_balanced_outer_parens(unfolded_body.trim()).trim_start_matches('@').trim();
            if compiled_sigs
                .get(aliased)
                .is_some_and(|sig: &CompiledDefSig| !sig.kernel_params.is_empty())
            {
                continue;
            }
        }
        let mut def_consts = std::collections::HashSet::new();
        let raw_body_ce = elaborate_lean_surface_expr_to_con_leche_bounded(
            &unfolded_body,
            &clean_params,
            &def_ldefs,
            &compiled_sigs,
            &empty_btypes,
            &mut def_consts,
            28,
        );
        if def_consts.iter().any(|c| decl_bnames.contains(c)) {
            continue;
        }
        let body_ce = raw_body_ce;
        let param_leaked = def_consts.iter().any(|c_name| {
            clean_params
                .iter()
                .any(|p| !p.is_empty() && replace_ident_boundary(c_name, p, "__P__") != *c_name)
        });
        if param_leaked {
            continue;
        }
        let mut ty_ce = prop_sort.clone();
        let mut val_ce = body_ce;
        for _ in 0..clean_params.len() {
            ty_ce = ConLecheExpr::ForallE(Box::new(prop_sort.clone()), Box::new(ty_ce));
            val_ce = ConLecheExpr::Lam(Box::new(prop_sort.clone()), Box::new(val_ce));
        }
        let d_decl = ConLecheDecl {
            name: def_name.clone(),
            level_params: Vec::new(),
            ty: ty_ce,
            val: val_ce,
            wf_tag: true,
        };
        let mut candidate_env_decls = build_base_con_leche_env_decls();
        for (prev_d, prev_cs) in &compiled_decls {
            for pc in prev_cs {
                if !candidate_env_decls.iter().any(|ed| &ed.name == pc)
                    && !compiled_decls.iter().any(|(cd, _)| &cd.name == pc)
                {
                    let idx = candidate_env_decls.len();
                    candidate_env_decls.push(ConLecheDecl {
                        name: pc.clone(),
                        level_params: Vec::new(),
                        ty: prop_sort.clone(),
                        val: mk_con_leche_distinct_prop_val(idx),
                        wf_tag: true,
                    });
                }
            }
            if !candidate_env_decls.iter().any(|ed| ed.name == prev_d.name) {
                candidate_env_decls.push(prev_d.clone());
            }
        }
        for dc in &def_consts {
            if !candidate_env_decls.iter().any(|ed| &ed.name == dc) {
                let idx = candidate_env_decls.len();
                candidate_env_decls.push(ConLecheDecl {
                    name: dc.clone(),
                    level_params: Vec::new(),
                    ty: prop_sort.clone(),
                    val: mk_con_leche_distinct_prop_val(idx),
                    wf_tag: true,
                });
            }
        }
        let candidate_pfx = crate::c_abi::ConLecheEnv {
            decls: candidate_env_decls,
            rec_rules: Vec::new(),
            header_magic: 0x4F4C_454E,
        };
        if !crate::c_abi::con_leche_verify_decl(&candidate_pfx, &d_decl) {
            continue;
        }
        let sig = CompiledDefSig {
            canon_name: def_name.clone(),
            kernel_params: clean_params.clone(),
            explicit_params_with_ty: explicit_with_ty.clone(),
        };
        let def_ns = def_name.rsplit_once('.').map(|(ns, _)| ns).unwrap_or("");
        let allow_short_alias = def_ns.is_empty()
            || def_ns == decl_ns
            || decl_ns.starts_with(&format!("{}.", def_ns))
            || def_ns.starts_with(&format!("{}.", decl_ns))
            || !is_ambiguous_prelude_short_name(short);
        compiled_sigs.insert(def_name.clone(), sig.clone());
        if !decl_bnames.contains(short) && allow_short_alias {
            if def_ns == decl_ns {
                compiled_sigs.insert(short.to_string(), sig.clone());
            } else {
                compiled_sigs.entry(short.to_string()).or_insert_with(|| sig.clone());
            }
        }
        let mut dot_pos = 0usize;
        while let Some(rel) = def_name[dot_pos..].find('.') {
            let sfx = &def_name[dot_pos + rel + 1..];
            if !sfx.is_empty() && sfx != short && !decl_bnames.contains(sfx) {
                compiled_sigs.entry(sfx.to_string()).or_insert_with(|| sig.clone());
            }
            dot_pos += rel + 1;
        }
        compiled_decls.push((d_decl, def_consts));
        for pv in param_variants {
            compiled_surface_defs.push((def_name.clone(), pv.clone(), unfolded_body.clone()));
            let mut dp = 0usize;
            while let Some(rel) = def_name[dp..].find('.') {
                let sfx = &def_name[dp + rel + 1..];
                if !sfx.is_empty() && sfx != short {
                    compiled_surface_defs.push((sfx.to_string(), pv.clone(), unfolded_body.clone()));
                }
                dp += rel + 1;
            }
        }
    }
    (
        compiled_decls,
        compiled_sigs,
        compiled_surface_defs,
        all_referenced_compiled,
    )
}

fn construct_negative_witness_for_decl(
    unfolded_decl: &ExtractedDecl,
    conclusion_str: &str,
    inner_concl: &str,
    concl_conjuncts: &[String],
    has_conjunct_tautology: bool,
    has_stub_findings: bool,
    local_def_names: &std::collections::HashSet<String>,
    compiled_def_sigs: &std::collections::HashMap<String, CompiledDefSig>,
    binder_types: &std::collections::HashMap<String, String>,
    base_decls: &[crate::c_abi::ConLecheDecl],
) -> Option<String> {
    use crate::c_abi::{ConLecheDecl, ConLecheEnv, ConLecheExpr, ConLecheLevel};
    if has_conjunct_tautology
        || has_stub_findings
        || is_single_conjunct_trivial(inner_concl)
        || is_single_conjunct_trivial(conclusion_str)
    {
        return None;
    }
    let mut bound_names: Vec<String> = Vec::new();
    for (names, _) in &unfolded_decl.binders {
        for n in names {
            bound_names.push(n.trim().to_string());
        }
    }
    let prop_sort = ConLecheExpr::Sort(ConLecheLevel::Zero);
    let bound_ctx = vec![prop_sort.clone(); bound_names.len()];

    let mut g_consts = std::collections::HashSet::new();
    let mut conjunct_pairs: Vec<(ConLecheExpr, ConLecheExpr, Option<(ConLecheExpr, ConLecheExpr, bool)>)> =
        Vec::with_capacity(concl_conjuncts.len());

    for raw_c in concl_conjuncts {
        let c = strip_balanced_outer_parens(raw_c.trim());
        if c.is_empty() || is_single_conjunct_trivial(c) {
            return None;
        }
        let orig_ce = elaborate_lean_surface_expr_to_con_leche(
            c,
            &bound_names,
            local_def_names,
            compiled_def_sigs,
            binder_types,
            &mut g_consts,
        );
        if let Some((lhs, rhs, is_ne)) = split_top_level_eq(c) {
            let l = strip_balanced_outer_parens(lhs.trim());
            let r = strip_balanced_outer_parens(rhs.trim());
            if !is_ne && l == r {
                return None;
            }
            let l_ce = elaborate_lean_surface_expr_to_con_leche(
                l,
                &bound_names,
                local_def_names,
                compiled_def_sigs,
                binder_types,
                &mut g_consts,
            );
            let r_ce = elaborate_lean_surface_expr_to_con_leche(
                r,
                &bound_names,
                local_def_names,
                compiled_def_sigs,
                binder_types,
                &mut g_consts,
            );
            let mut_str = if !is_ne {
                format!("{} != {}", l, r)
            } else {
                format!("{} = {}", l, r)
            };
            let mut_ce = elaborate_lean_surface_expr_to_con_leche(
                &mut_str,
                &bound_names,
                local_def_names,
                compiled_def_sigs,
                binder_types,
                &mut g_consts,
            );
            conjunct_pairs.push((orig_ce, mut_ce, Some((l_ce, r_ce, is_ne))));
        } else if c.contains('<') || c.contains('>') || c.contains('≤') || c.contains('≥') {
            for cmp_op in ["<=", "≤", ">=", "≥", "<", ">"] {
                if let Some(pos) = find_top_level_delim(c, cmp_op) {
                    let l = strip_balanced_outer_parens(c[..pos].trim());
                    let r = strip_balanced_outer_parens(c[pos + cmp_op.len()..].trim());
                    if l == r {
                        return None;
                    }
                    break;
                }
            }
            let mut_str = format!("({}) = false", c);
            let mut_ce = elaborate_lean_surface_expr_to_con_leche(
                &mut_str,
                &bound_names,
                local_def_names,
                compiled_def_sigs,
                binder_types,
                &mut g_consts,
            );
            conjunct_pairs.push((orig_ce, mut_ce, None));
        } else if !extract_expr_identifiers(c).is_empty() {
            let mut_str = format!("({}) = false", c);
            let mut_ce = elaborate_lean_surface_expr_to_con_leche(
                &mut_str,
                &bound_names,
                local_def_names,
                compiled_def_sigs,
                binder_types,
                &mut g_consts,
            );
            conjunct_pairs.push((orig_ce, mut_ce, None));
        } else {
            return None;
        }
    }
    if conjunct_pairs.is_empty() {
        return None;
    }

    // Build the kernel environment with distinct WHNF constant inhabitants and compiled local defs
    let mut env_decls = base_decls.to_vec();
    let mut sorted_consts: Vec<String> = g_consts.into_iter().collect();
    sorted_consts.sort();
    for c_name in &sorted_consts {
        if !env_decls.iter().any(|d| &d.name == c_name) {
            let c_idx = env_decls.len();
            env_decls.push(ConLecheDecl {
                name: c_name.clone(),
                level_params: Vec::new(),
                ty: prop_sort.clone(),
                val: mk_con_leche_distinct_prop_val(c_idx),
                wf_tag: true,
            });
        }
    }
    let check_env = ConLecheEnv {
        decls: env_decls,
        rec_rules: Vec::new(),
        header_magic: 0x4F4C_454E,
    };

    for (orig_ce, mut_ce, eq_pair) in &conjunct_pairs {
        if let Some((l_ce, r_ce, is_ne)) = eq_pair {
            if !is_ne && crate::c_abi::con_leche_is_def_eq(256, &check_env, l_ce, r_ce) {
                return None;
            }
        }
        if crate::c_abi::con_leche_infer_type(256, &check_env, &bound_ctx, orig_ce).is_none()
            || crate::c_abi::con_leche_infer_type(256, &check_env, &bound_ctx, mut_ce).is_none()
            || crate::c_abi::con_leche_is_def_eq(256, &check_env, orig_ce, mut_ce)
        {
            return None;
        }
    }

    // Always attempt the concrete countermodel evaluator first (even for unconditional theorems)
    let mut neg_decl = unfolded_decl.clone();
    let mut segs = split_top_level_implications(&neg_decl.prop_str);
    if let Some(last) = segs.last_mut() {
        *last = if let Some((l, r, is_ne)) = split_top_level_eq(last) {
            if is_ne {
                format!("{} = {}", l.trim(), r.trim())
            } else {
                format!("{} != {}", l.trim(), r.trim())
            }
        } else {
            format!("({}) = false", last.trim())
        };
        neg_decl.prop_str = segs.join(" → ");
    }
    if let Some((neg_rep, _, _)) = eval_extracted_decl_in_memory(&neg_decl, 256) {
        if neg_rep.violations > 0 {
            return Some(format!(
                "sampled_fastcheck_verified(postcondition_discriminates: {}; counterexample_violations={}/{})",
                conclusion_str, neg_rep.violations, neg_rep.satisfied_preconditions
            ));
        }
        return None;
    }

    Some(format!(
        "structural_ast_verified(postcondition_discriminates: {}; kernel_mutation_ineq_verified)",
        conclusion_str
    ))
}

fn validate_decl_pin_and_olean_shard(
    decl: &ExtractedDecl,
    imp_segments: &[String],
    raw_conclusion_str: &str,
    _conclusion_str: &str,
    local_defs: &[(String, Vec<String>, String)],
    is_vacuous: bool,
    is_trivial_conclusion: bool,
) -> (bool, bool) {
    use crate::c_abi::{ConLecheDecl, ConLecheEnv, ConLecheExpr, ConLecheLevel};
    let decl_name = decl.name.trim();
    let has_name = !decl_name.is_empty();
    let mut seen_val_binders = std::collections::HashSet::new();
    let mut bound_names = Vec::new();
    let mut binder_types = std::collections::HashMap::new();
    let mut distinct_val_binders = true;
    for (names, ty) in &decl.binders {
        let is_val = is_known_binder_value_type(ty);
        for n in names {
            let nt = n.trim();
            if !nt.is_empty() && nt != "_" {
                bound_names.push(nt.to_string());
                binder_types.insert(nt.to_string(), ty.trim().to_string());
                if is_val && !seen_val_binders.insert(nt.to_string()) {
                    distinct_val_binders = false;
                }
            }
        }
    }

    let decl_ns = decl_name.rsplit_once('.').map(|(ns, _)| ns).unwrap_or("");
    let mut local_def_names = std::collections::HashSet::new();
    for c in [
        "MAX_UINT256",
        "WAD",
        "RAY",
        "SECP256K1_N",
        "ADDRESS_MODULUS",
        "Word256",
        "Uint256",
    ] {
        local_def_names.insert(c.to_string());
    }
    for (def_name, _, _) in local_defs {
        if def_name.starts_with("__binder_ty:") {
            continue;
        }
        local_def_names.insert(def_name.clone());
        let def_ns = def_name.rsplit_once('.').map(|(ns, _)| ns).unwrap_or("");
        if def_ns == decl_ns {
            let short = def_name.rsplit('.').next().unwrap_or(def_name.as_str());
            local_def_names.insert(short.to_string());
        }
    }

    let prop_trim = decl.prop_str.trim();
    let has_proof_leak = raw_conclusion_str.contains(":= by")
        || raw_conclusion_str.contains("sorryAx")
        || prop_trim.contains(":= by");

    let (compiled_def_decls, compiled_sigs, mut compiled_surface_defs, all_referenced_compiled) =
        compile_local_defs_for_con_leche(decl, local_defs, &local_def_names);
    for (b_name, b_ty) in &binder_types {
        compiled_surface_defs.push((
            format!("__binder_ty:{}", b_name),
            Vec::new(),
            b_ty.clone(),
        ));
    }

    // 1. Elaborate `pinned_ty` from the raw surface signature (`decl.binders` + `decl.prop_str`,
    //    keeping compiled local definitions un-unfolded as `App(Const(def_name, []), args)`),
    //    and elaborate `elaborated_ty` + `proof_expr` from the unfolded segmented signature
    //    (where compiled local definitions have been unfolded via `unfold_expr_one_level` and
    //    `expand_compiled_defs_in_con_leche_expr`).
    let mut all_consts = std::collections::HashSet::new();
    for (_, def_c) in &compiled_def_decls {
        for c in def_c {
            all_consts.insert(c.clone());
        }
    }
    let (pinned_ty, pinned_proof) = elaborate_decl_binders_and_body_to_con_leche(
        &decl.binders,
        prop_trim,
        &local_def_names,
        &compiled_sigs,
        &binder_types,
        false,
        true,
        &mut all_consts,
    );

    let mut segmented_binders: Vec<(Vec<String>, String)> = decl
        .binders
        .iter()
        .map(|(ns, ty)| (ns.clone(), unfold_expr_one_level(ty, &compiled_surface_defs)))
        .collect();
    for pre in &imp_segments[..imp_segments.len().saturating_sub(1)] {
        let clean_pre = strip_hypothesis_binder_name(pre.trim());
        segmented_binders.push((
            vec!["_".to_string()],
            unfold_expr_one_level(clean_pre, &compiled_surface_defs),
        ));
    }
    let unfolded_concl_for_pin = unfold_expr_one_level(raw_conclusion_str.trim(), &compiled_surface_defs);
    let mut elab_consts = std::collections::HashSet::new();
    let (raw_elaborated_ty, raw_proof_expr) = elaborate_decl_binders_and_body_to_con_leche(
        &segmented_binders,
        unfolded_concl_for_pin.trim(),
        &local_def_names,
        &compiled_sigs,
        &binder_types,
        true,
        false,
        &mut elab_consts,
    );
    let mut compiled_val_map = std::collections::HashMap::new();
    for (d_decl, _) in &compiled_def_decls {
        let arity = compiled_sigs
            .get(&d_decl.name)
            .map(|s| s.kernel_params.len())
            .unwrap_or(0);
        compiled_val_map.insert(d_decl.name.clone(), (arity, d_decl.val.clone()));
    }
    let expanded_pinned_ty =
        expand_compiled_defs_in_con_leche_expr(&pinned_ty, &compiled_val_map, 32);
    let elaborated_ty =
        expand_compiled_defs_in_con_leche_expr(&raw_elaborated_ty, &compiled_val_map, 32);
    let expanded_proof_expr =
        expand_compiled_defs_in_con_leche_expr(&raw_proof_expr, &compiled_val_map, 32);
    for c in &elab_consts {
        all_consts.insert(c.clone());
    }
    fn collect_expr_consts(e: &crate::c_abi::ConLecheExpr, out: &mut std::collections::HashSet<String>) {
        use crate::c_abi::ConLecheExpr;
        match e {
            ConLecheExpr::Const(nm, _) => {
                out.insert(nm.clone());
            }
            ConLecheExpr::App(f, a) => {
                collect_expr_consts(f, out);
                collect_expr_consts(a, out);
            }
            ConLecheExpr::Lam(d, b) | ConLecheExpr::ForallE(d, b) => {
                collect_expr_consts(d, out);
                collect_expr_consts(b, out);
            }
            ConLecheExpr::LetE(t, v, b) => {
                collect_expr_consts(t, out);
                collect_expr_consts(v, out);
                collect_expr_consts(b, out);
            }
            _ => {}
        }
    }
    collect_expr_consts(&pinned_ty, &mut all_consts);
    collect_expr_consts(&expanded_pinned_ty, &mut all_consts);
    collect_expr_consts(&pinned_proof, &mut all_consts);
    collect_expr_consts(&elaborated_ty, &mut all_consts);
    collect_expr_consts(&expanded_proof_expr, &mut all_consts);
    collect_expr_consts(&raw_proof_expr, &mut all_consts);
    let has_unresolved_implicit = all_consts.contains("__UnresolvedImplicitCall");
    let mut sorted_consts: Vec<String> = all_consts.into_iter().collect();
    sorted_consts.sort();
    let no_shadowing = distinct_val_binders
        && crate::c_abi::check_no_shadowed_consts(&sorted_consts, &bound_names, &pinned_ty)
        && crate::c_abi::check_no_shadowed_consts(&sorted_consts, &bound_names, &elaborated_ty);

    // 2. Build a well-typed `ConLecheEnv` in `Prop` (`Sort 0`) with distinct WHNF constant values
    //    and compiled local definitions, serialize the lambda proof term `proof_expr` as `LNE1`
    //    (`0x4C4E4531`), and replay it against `pinned_ty` through `ElabAudit.replayCasProofBlob`.
    let prop_sort = ConLecheExpr::Sort(ConLecheLevel::Zero);
    let mut env_decls = build_base_con_leche_env_decls();
    let compiled_names: std::collections::HashSet<&str> = compiled_def_decls
        .iter()
        .map(|(d, _)| d.name.as_str())
        .collect();
    for c_name in &sorted_consts {
        if !matches!(c_name.as_str(), "__PropInhab" | "__App" | "__Forall")
            && !compiled_names.contains(c_name.as_str())
        {
            let c_idx = env_decls.len();
            env_decls.push(ConLecheDecl {
                name: c_name.clone(),
                level_params: Vec::new(),
                ty: prop_sort.clone(),
                val: mk_con_leche_distinct_prop_val(c_idx),
                wf_tag: true,
            });
        }
    }
    for (d_decl, _) in compiled_def_decls {
        if !env_decls.iter().any(|existing| existing.name == d_decl.name) {
            env_decls.push(d_decl);
        }
    }
    let replay_env = ConLecheEnv {
        decls: env_decls.clone(),
        rec_rules: Vec::new(),
        header_magic: 0x4F4C_454E,
    };

    let ast_pin_matches = !raw_conclusion_str.trim().is_empty()
        && !prop_trim.is_empty()
        && !has_proof_leak
        && all_referenced_compiled
        && !has_unresolved_implicit
        && (crate::c_abi::con_leche_is_def_eq(256, &replay_env, &pinned_ty, &elaborated_ty)
            || crate::c_abi::con_leche_is_def_eq(256, &replay_env, &pinned_ty, &raw_elaborated_ty)
            || (crate::c_abi::con_leche_is_def_eq(256, &replay_env, &pinned_ty, &expanded_pinned_ty)
                && (crate::c_abi::con_leche_is_def_eq(256, &replay_env, &expanded_pinned_ty, &elaborated_ty)
                    || crate::c_abi::con_leche_is_def_eq(256, &replay_env, &expanded_pinned_ty, &raw_elaborated_ty))));

    let proof_expr = if crate::c_abi::con_leche_infer_type(64, &replay_env, &[], &expanded_proof_expr)
        .is_some_and(|inf_ty| crate::c_abi::con_leche_is_def_eq(64, &replay_env, &inf_ty, &pinned_ty))
    {
        expanded_proof_expr
    } else if crate::c_abi::con_leche_infer_type(64, &replay_env, &[], &raw_proof_expr)
        .is_some_and(|inf_ty| crate::c_abi::con_leche_is_def_eq(64, &replay_env, &inf_ty, &pinned_ty))
    {
        raw_proof_expr
    } else {
        pinned_proof
    };

    let lne1_blob = crate::c_abi::serialize_expr_v1(&proof_expr);
    let lne1_ty_blob = crate::c_abi::serialize_expr_v1(&pinned_ty);
    let parsed_ty = crate::c_abi::parse_expr_v1(&lne1_ty_blob);
    let cas_magic_valid = lne1_blob.len() >= 5
        && u32::from_be_bytes([lne1_blob[0], lne1_blob[1], lne1_blob[2], lne1_blob[3]])
            == 0x4C4E_4531
        && crate::c_abi::replay_cas_proof_blob(&replay_env, &lne1_blob, &pinned_ty).is_some();
    let consumed_exact_len = parsed_ty
        .as_ref()
        .is_some_and(|(e, off)| e == &pinned_ty && *off == lne1_ty_blob.len());

    let header_pin_ok = crate::c_abi::verify_elab_header_pin(
        has_name,
        no_shadowing,
        ast_pin_matches,
        cas_magic_valid,
        consumed_exact_len,
    );

    // 3. Encode a complete binary `OLEN` shard (`0x4F4C454E`) using `ConLeche.encodeOleanShard`
    //    and validate it via `ConLeche.parseOleanShard` (which decodes `encodeNat`, `levelParams`,
    //    `ConLecheExpr` tags `0..6`, and `RecRule`s, and runs `verifyDeclsPrefix` + `verifyRecRule`).
    let all_decls_typed = has_name && !is_vacuous && !is_trivial_conclusion && ast_pin_matches;
    let thm_decl_name = format!("__Thm_{}", decl_name);
    if !env_decls.iter().any(|d| d.name == thm_decl_name) {
        env_decls.push(ConLecheDecl {
            name: thm_decl_name,
            level_params: Vec::new(),
            ty: pinned_ty,
            val: proof_expr,
            wf_tag: all_decls_typed,
        });
    }
    let shard_env = ConLecheEnv {
        decls: env_decls,
        rec_rules: Vec::new(),
        header_magic: 0x4F4C_454E,
    };
    let shard_bytes = crate::c_abi::encode_olean_shard(&shard_env);
    let shard_gate_ok = crate::c_abi::validate_olean_shard_header_bytes(
        &shard_bytes,
        shard_bytes.len(),
        all_decls_typed,
    );
    (header_pin_ok, shard_gate_ok)
}

pub(super) fn audit_single_decl_spec_full_with_policy(
    decl: &ExtractedDecl,
    raw_local_defs: &[(String, Vec<String>, String)],
    policy: &AuditSpecPolicyConfig,
) -> ((bool, bool, String), String, String, Vec<String>, Vec<String>) {
    let mut decl_binder_names = std::collections::HashSet::new();
    let mut binder_types_map = std::collections::HashMap::new();
    for (names, ty) in &decl.binders {
        for n in names {
            let nt = n.trim();
            if !nt.is_empty() && nt != "_" {
                decl_binder_names.insert(nt.to_string());
                binder_types_map.insert(nt.to_string(), ty.trim().to_string());
            }
        }
    }
    let mut filtered_defs: Vec<(String, Vec<String>, String)> = raw_local_defs
        .iter()
        .filter(|(def_name, params, _)| {
            let short = def_name.rsplit('.').next().unwrap_or(def_name.as_str());
            !(params.is_empty() && decl_binder_names.contains(short))
        })
        .cloned()
        .collect();
    for (names, ty) in &decl.binders {
        for n in names {
            let nt = n.trim();
            if !nt.is_empty() && nt != "_" {
                filtered_defs.push((
                    format!("__binder_ty:{}", nt),
                    Vec::new(),
                    ty.trim().to_string(),
                ));
            }
        }
    }
    let local_defs = filtered_defs.as_slice();
    let mut hyp_strings = Vec::new();
    let mut unsigned_vars = std::collections::HashSet::new();
    for (names, ty) in &decl.binders {
        let unfolded_ty = unfold_expr_one_level(ty, local_defs);
        if is_explicitly_unsigned_binder_type(ty)
            || is_explicitly_unsigned_binder_type(&unfolded_ty)
        {
            for n in names {
                unsigned_vars.insert(n.trim().to_string());
            }
        }
        if !is_known_binder_value_type(ty) {
            hyp_strings.push(unfolded_ty);
        }
    }
    let imp_segments = split_top_level_implications(&decl.prop_str);
    let raw_conclusion_str = imp_segments
        .last()
        .map(|s| s.trim().to_string())
        .unwrap_or_default();
    let mut conclusion_str = unfold_expr_one_level(&raw_conclusion_str, local_defs);
    for pre in &imp_segments[..imp_segments.len().saturating_sub(1)] {
        let stripped = strip_hypothesis_binder_name(pre);
        hyp_strings.push(unfold_expr_one_level(stripped, local_defs));
    }

    if policy.reject_definitional_lowering_tautology && !hyp_strings.is_empty() {
        conclusion_str = substitute_equational_hypotheses(&conclusion_str, &hyp_strings, local_defs);
    }

    let mut is_vacuous = hyp_strings
        .iter()
        .any(|h| is_syntactically_contradictory_hyp_with_binders(h, &unsigned_vars));

    // Check pairwise contradictory hypotheses (e.g. `h1 : a = b` and `h2 : a != b`)
    if !is_vacuous && hyp_strings.len() >= 2 {
        for i in 0..hyp_strings.len() {
            for j in (i + 1)..hyp_strings.len() {
                let hi = hyp_strings[i].trim();
                let hj = hyp_strings[j].trim();
                if hj == format!("¬{}", hi)
                    || hj == format!("¬({})", hi)
                    || hi == format!("¬{}", hj)
                    || hi == format!("¬({})", hj)
                {
                    is_vacuous = true;
                }
                if let (Some((l1, r1, ne1)), Some((l2, r2, ne2))) =
                    (split_top_level_eq(hi), split_top_level_eq(hj))
                {
                    if ne1 != ne2 && ((l1 == l2 && r1 == r2) || (l1 == r2 && r1 == l2)) {
                        is_vacuous = true;
                    }
                    if !ne1 && !ne2 && l1 == l2 && r1 != r2 {
                        if r1.parse::<u128>().is_ok() && r2.parse::<u128>().is_ok() {
                            is_vacuous = true;
                        }
                    }
                }
                for (eq_h, other_h) in [(hi, hj), (hj, hi)] {
                    if let Some((el, er, false)) = split_top_level_eq(eq_h) {
                        let elt = strip_balanced_outer_parens(el.trim());
                        let ert = strip_balanced_outer_parens(er.trim());
                        if !elt.is_empty() && ert.parse::<u128>().is_ok() {
                            let subst_other = replace_ident_boundary(other_h, elt, ert);
                            if subst_other != other_h
                                && is_syntactically_contradictory_hyp_with_binders(
                                    &subst_other,
                                    &unsigned_vars,
                                )
                            {
                                is_vacuous = true;
                            }
                        }
                    }
                }
            }
        }
    }

    let mut unfolded_decl = decl.clone();
    if !local_defs.is_empty() {
        unfolded_decl.binders = decl
            .binders
            .iter()
            .map(|(ns, ty)| (ns.clone(), unfold_expr_one_level(ty, local_defs)))
            .collect();
        unfolded_decl.prop_str = imp_segments
            .iter()
            .map(|seg| unfold_expr_one_level(strip_hypothesis_binder_name(seg), local_defs))
            .collect::<Vec<_>>()
            .join(" → ");
    }

    let mut pos_witness = if hyp_strings.is_empty() {
        "structural_ast_verified(unconditional)".to_string()
    } else {
        "structural_ast_verified(non_contradictory_preconditions)".to_string()
    };
    let mut droppable_hyps = Vec::new();
    if !is_vacuous {
        if let Some((rep, _, _)) = eval_extracted_decl_in_memory(&unfolded_decl, 256) {
            if !hyp_strings.is_empty()
                && (rep.vacuous_precondition_warning || rep.satisfied_preconditions == 0)
            {
                is_vacuous = true;
            } else if rep.satisfied_preconditions > 0 {
                pos_witness = format!(
                    "sampled_fastcheck_verified(satisfied_states={}/{})",
                    rep.satisfied_preconditions, rep.n_states
                );
                if !hyp_strings.is_empty() {
                    // Hypothesis-drop mutation probe: drop each non-value binder hypothesis one by one
                    // and check whether the postcondition still holds across all 256 states and has no
                    // variable overlap with the conclusion (indicating a redundant hypothesis).
                    for (b_idx, (_, ty)) in unfolded_decl.binders.iter().enumerate() {
                        if !is_known_binder_value_type(ty) {
                            let mut mutated = unfolded_decl.clone();
                            mutated.binders.remove(b_idx);
                            if let Some((m_rep, _, _)) = eval_extracted_decl_in_memory(&mutated, 256)
                            {
                                if m_rep.verified && m_rep.violations == 0 {
                                    let mut hyp_vars = std::collections::HashSet::new();
                                    let mut concl_vars = std::collections::HashSet::new();
                                    let val_params: std::collections::HashSet<&str> = unfolded_decl
                                        .binders
                                        .iter()
                                        .filter(|(_, bt)| is_known_binder_value_type(bt))
                                        .flat_map(|(ns, _)| ns.iter().map(|s| s.as_str()))
                                        .collect();
                                    if let Ok(h_ast) = parse_lean_expr_str(ty) {
                                        let _ = collect_expr_bound_vars(
                                            &h_ast,
                                            &val_params,
                                            &mut hyp_vars,
                                        );
                                    }
                                    if let Ok(c_ast) = parse_lean_expr_str(&conclusion_str) {
                                        let _ = collect_expr_bound_vars(
                                            &c_ast,
                                            &val_params,
                                            &mut concl_vars,
                                        );
                                    }
                                    let disjoint = !hyp_vars.is_empty()
                                        && hyp_vars.is_disjoint(&concl_vars);
                                    if disjoint
                                        || m_rep.satisfied_preconditions
                                            > rep.satisfied_preconditions
                                    {
                                        droppable_hyps.push(format!("{}: {}", decl.name, ty.trim()));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn flatten_top_level_conjuncts(expr: &str) -> Vec<String> {
        let parts = split_top_level_conjuncts(expr);
        if parts.len() <= 1 {
            return parts;
        }
        let mut out = Vec::with_capacity(parts.len());
        for p in parts {
            out.extend(flatten_top_level_conjuncts(&p));
        }
        out
    }
    let concl_imp_segments = split_top_level_implications(&conclusion_str);
    let inner_concl = concl_imp_segments
        .last()
        .map(|s| s.trim())
        .unwrap_or(conclusion_str.as_str());
    let concl_conjuncts = flatten_top_level_conjuncts(inner_concl);
    let raw_concl_imp_segments = split_top_level_implications(&decl.prop_str);
    let raw_inner_concl = raw_concl_imp_segments
        .last()
        .map(|s| s.trim())
        .unwrap_or(decl.prop_str.as_str());
    let raw_concl_conjuncts = flatten_top_level_conjuncts(raw_inner_concl);
    let relational = |c: &str| {
        policy.policy != "strict-proofs"
            && relational_ignored_parameters(decl, c, local_defs).is_some()
    };
    let has_conjunct_tautology = policy.reject_conjunct_tautologies
        && concl_conjuncts.len() > 1
        && concl_conjuncts.iter().enumerate().any(|(idx, c)| {
            is_single_conjunct_trivial(c)
                && !raw_concl_conjuncts
                    .get(idx)
                    .is_some_and(|raw| relational(raw))
        });
    let is_whole_trivial = (is_single_conjunct_trivial(inner_concl)
        || is_single_conjunct_trivial(&conclusion_str))
        && !relational(raw_inner_concl);
    let stub_findings = audit_referenced_local_defs_for_stubs(
        decl,
        &unfolded_decl.binders,
        &hyp_strings,
        &conclusion_str,
        local_defs,
        policy,
    );
    let is_trivial_conclusion =
        is_whole_trivial || has_conjunct_tautology || !stub_findings.is_empty();

    let decl_ns = decl.name.trim().rsplit_once('.').map(|(ns, _)| ns).unwrap_or("");
    let mut neg_local_def_names = std::collections::HashSet::new();
    for (dn, _, _) in local_defs {
        if dn.starts_with("__binder_ty:") {
            continue;
        }
        neg_local_def_names.insert(dn.clone());
        let dns = dn.rsplit_once('.').map(|(ns, _)| ns).unwrap_or("");
        if dns == decl_ns {
            let short = dn.rsplit('.').next().unwrap_or(dn.as_str());
            neg_local_def_names.insert(short.to_string());
        }
    }
    let (neg_compiled_decls, neg_compiled_sigs, _, _) =
        compile_local_defs_for_con_leche(&unfolded_decl, local_defs, &neg_local_def_names);
    let mut neg_base_decls = build_base_con_leche_env_decls();
    let prop_sort = crate::c_abi::ConLecheExpr::Sort(crate::c_abi::ConLecheLevel::Zero);
    for (_, def_c) in &neg_compiled_decls {
        for c_name in def_c {
            if !neg_base_decls.iter().any(|d| &d.name == c_name) {
                let idx = neg_base_decls.len();
                neg_base_decls.push(crate::c_abi::ConLecheDecl {
                    name: c_name.clone(),
                    level_params: Vec::new(),
                    ty: prop_sort.clone(),
                    val: mk_con_leche_distinct_prop_val(idx),
                    wf_tag: true,
                });
            }
        }
    }
    for (d_decl, _) in neg_compiled_decls {
        if !neg_base_decls.iter().any(|d| d.name == d_decl.name) {
            neg_base_decls.push(d_decl);
        }
    }

    let has_pos_witness = !is_vacuous;
    let computed_neg_witness = construct_negative_witness_for_decl(
        &unfolded_decl,
        &conclusion_str,
        inner_concl,
        &concl_conjuncts,
        has_conjunct_tautology,
        !stub_findings.is_empty(),
        &neg_local_def_names,
        &neg_compiled_sigs,
        &binder_types_map,
        &neg_base_decls,
    )
    .or_else(|| {
        if !is_trivial_conclusion && relational(raw_inner_concl) {
            Some("relational_hyperproperty_verified(varied_unconstrained_binders)".to_string())
        } else {
            None
        }
    });
    let has_neg_witness = !is_trivial_conclusion && computed_neg_witness.is_some();
    let neg_witness = if let Some(nw) = computed_neg_witness {
        nw
    } else if is_whole_trivial {
        "none(tautological_postcondition)".to_string()
    } else if !stub_findings.is_empty() {
        format!("none(referenced_stub_def: {})", stub_findings.join("; "))
    } else if has_conjunct_tautology {
        format!("none(conjunct_tautology_in: {})", conclusion_str)
    } else {
        "none(tautological_postcondition)".to_string()
    };
    let (header_pin_ok, shard_gate_ok) = validate_decl_pin_and_olean_shard(
        decl,
        &imp_segments,
        &raw_conclusion_str,
        &conclusion_str,
        local_defs,
        is_vacuous,
        is_trivial_conclusion,
    );
    let witness_gate_ok = crate::c_abi::spec_audit_witness_gate(has_pos_witness, has_neg_witness);
    let gate_ok = witness_gate_ok && header_pin_ok && shard_gate_ok;
    let is_tight = gate_ok && !is_vacuous && !is_trivial_conclusion;
    let reason = if is_vacuous {
        "vacuous_precondition".to_string()
    } else if !stub_findings.is_empty() {
        "stubbed_definition_in_spec".to_string()
    } else if has_conjunct_tautology {
        "conjunct_tautological_postcondition".to_string()
    } else if is_trivial_conclusion || !witness_gate_ok {
        "trivial_tautological_postcondition".to_string()
    } else if !header_pin_ok {
        "header_pin_or_def_eq_failed".to_string()
    } else if !shard_gate_ok {
        "olean_shard_gate_failed".to_string()
    } else {
        "non_vacuous_and_tight".to_string()
    };
    (
        (is_vacuous, is_tight, reason),
        pos_witness,
        neg_witness,
        droppable_hyps,
        stub_findings,
    )
}

pub(super) fn extract_decls_fast(src: &str, decl_filter: Option<&str>) -> Vec<ExtractedDecl> {
    if let Some(t) = decl_filter {
        if !t.is_empty() && t != "auto" && src.len() > 8192 {
            let short = t.rsplit('.').next().unwrap_or(t);
            for cand in [t, short] {
                for kw in ["theorem ", "lemma "] {
                    let needle = format!("{}{}", kw, cand);
                    if let Some(pos) = src.find(&needle) {
                        let end = (pos + needle.len() + 4096).min(src.len());
                        let mut valid_end = end;
                        while valid_end < src.len() && !src.is_char_boundary(valid_end) {
                            valid_end += 1;
                        }
                        let sub_clean = strip_lean_comments(&src[pos..valid_end]);
                        let sub_decls = extract_all_lean_theorems(&sub_clean, decl_filter);
                        if !sub_decls.is_empty() {
                            return sub_decls;
                        }
                    }
                }
            }
        }
    }
    let clean = strip_lean_comments(src);
    extract_all_lean_theorems(&clean, decl_filter)
}

/// Schema version for the Blake3 content-addressed `audit-spec` per-file JSON cache.
pub const AUDIT_SPEC_CACHE_SCHEMA_VERSION: u32 = 27;

static AUDIT_SPEC_CACHE_TMP_SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

pub(super) fn resolve_audit_spec_cache_dir() -> Option<PathBuf> {
    if std::env::var("TURBO_LEAN_NO_AUDIT_CACHE")
        .ok()
        .is_some_and(|v| matches!(v.trim(), "1" | "true" | "yes"))
    {
        return None;
    }
    let dir = std::env::var("TURBO_LEAN_AUDIT_CACHE_DIR")
        .ok()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/tmp/turbo-lean-audit-spec-cache-v1"));
    Some(dir)
}

fn find_lean_project_root(file: &Path) -> Option<PathBuf> {
    let mut cur = file.parent();
    while let Some(dir) = cur {
        if dir.join("lakefile.lean").is_file() || dir.join("lakefile.toml").is_file() {
            return Some(dir.to_path_buf());
        }
        cur = dir.parent();
    }
    None
}

fn collect_imported_or_sibling_lean_files(file: &Path) -> Vec<PathBuf> {
    let Some(proj_root) = find_lean_project_root(file) else {
        let mut fallback = Vec::new();
        if let Some(parent) = file.parent() {
            fallback.extend(crate::lake_build::collect_lean_files(parent));
            if let Some(grandparent) = parent.parent() {
                if let Ok(entries) = fs::read_dir(grandparent) {
                    for p in entries
                        .flatten()
                        .map(|e| e.path())
                        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("lean"))
                    {
                        fallback.push(p);
                    }
                }
            }
        }
        fallback.sort();
        fallback.dedup();
        fallback.retain(|p| p != file);
        return fallback;
    };
    let mut visited = std::collections::HashSet::new();
    let mut queue = std::collections::VecDeque::new();
    let mut ordered = Vec::new();
    if let Ok(canon_self) = file.canonicalize() {
        visited.insert(canon_self);
    }
    visited.insert(file.to_path_buf());
    queue.push_back(file.to_path_buf());
    while let Some(cur_file) = queue.pop_front() {
        let Ok(raw_src) = fs::read_to_string(&cur_file) else {
            continue;
        };
        let clean = strip_lean_comments(&raw_src);
        for line in clean.lines() {
            let trimmed = line.trim();
            let rest = if let Some(r) = trimmed.strip_prefix("import ") {
                r.trim()
            } else if let Some(r) = trimmed.strip_prefix("public import ") {
                r.trim()
            } else {
                continue;
            };
            for mod_tok in rest.split_whitespace() {
                if mod_tok.is_empty() {
                    continue;
                }
                let rel_path = format!("{}.lean", mod_tok.replace('.', "/"));
                let cand = proj_root.join(&rel_path);
                if cand.is_file() {
                    let key = cand.canonicalize().unwrap_or_else(|_| cand.clone());
                    if visited.insert(key) {
                        ordered.push(cand.clone());
                        queue.push_back(cand);
                    }
                }
            }
        }
    }
    if ordered.is_empty() {
        if let Some(parent) = file.parent() {
            for p in crate::lake_build::collect_lean_files(parent) {
                if p != file {
                    ordered.push(p);
                }
            }
            if let Some(grandparent) = parent.parent() {
                if let Ok(entries) = fs::read_dir(grandparent) {
                    for p in entries
                        .flatten()
                        .map(|e| e.path())
                        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("lean"))
                    {
                        if p != file && !ordered.contains(&p) {
                            ordered.push(p);
                        }
                    }
                }
            }
            ordered.sort();
            ordered.dedup();
        }
    }
    ordered
}

pub(super) fn compute_neighbor_lean_digest(file: &Path) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-lean-neighbor-lean-defs-v4:");
    for p in collect_imported_or_sibling_lean_files(file) {
        if let Ok(sib_src) = fs::read_to_string(&p) {
            let defs = extract_local_def_unfoldings_with_vis(&strip_lean_comments(&sib_src), false);
            if !defs.is_empty() {
                let p_str = p.to_string_lossy();
                hasher.update(&(p_str.len() as u64).to_le_bytes());
                hasher.update(p_str.as_bytes());
                hasher.update(&(defs.len() as u64).to_le_bytes());
                for (name, params, body) in &defs {
                    hasher.update(&(name.len() as u64).to_le_bytes());
                    hasher.update(name.as_bytes());
                    hasher.update(&(params.len() as u64).to_le_bytes());
                    for param in params {
                        hasher.update(&(param.len() as u64).to_le_bytes());
                        hasher.update(param.as_bytes());
                    }
                    hasher.update(&(body.len() as u64).to_le_bytes());
                    hasher.update(body.as_bytes());
                }
            }
        }
    }
    *hasher.finalize().as_bytes()
}

pub(super) fn compute_audit_spec_cache_key_with_policy(
    file: &Path,
    decl_filter: Option<&str>,
    file_bytes: &[u8],
    policy: &AuditSpecPolicyConfig,
    forbid_kinds: &[String],
    allow_names: &[String],
    forbid_namespaces: &[String],
) -> String {
    static ENGINE_DIGEST: std::sync::OnceLock<[u8; 32]> = std::sync::OnceLock::new();
    let engine_digest = ENGINE_DIGEST.get_or_init(|| {
        let mut h = blake3::Hasher::new();
        h.update(include_bytes!("audit_spec.rs"));
        h.update(b":");
        h.update(include_bytes!("c_abi.rs"));
        *h.finalize().as_bytes()
    });
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-lean-audit-spec-cache:");
    hasher.update(&AUDIT_SPEC_CACHE_SCHEMA_VERSION.to_le_bytes());
    hasher.update(b":");
    hasher.update(engine_digest);
    hasher.update(b":");
    let canon_path = file
        .canonicalize()
        .unwrap_or_else(|_| file.to_path_buf());
    let path_str = canon_path.to_string_lossy();
    hasher.update(&(path_str.len() as u64).to_le_bytes());
    hasher.update(path_str.as_bytes());
    hasher.update(b":");
    let df = decl_filter.unwrap_or("");
    hasher.update(&(df.len() as u64).to_le_bytes());
    hasher.update(df.as_bytes());
    hasher.update(b":");
    if let Ok(pol_json) = serde_json::to_vec(&(policy, forbid_kinds, allow_names, forbid_namespaces)) {
        hasher.update(&(pol_json.len() as u64).to_le_bytes());
        hasher.update(&pol_json);
        hasher.update(b":");
    }
    let neighbor_digest = compute_neighbor_lean_digest(file);
    hasher.update(&neighbor_digest);
    hasher.update(b":");
    hasher.update(file_bytes);
    hasher.finalize().to_hex().to_string()
}

pub(super) fn write_audit_spec_cache_atomic(target: &Path, report: &serde_json::Value) {
    let Some(parent) = target.parent() else {
        return;
    };
    if fs::create_dir_all(parent).is_err() {
        return;
    }
    let Ok(bytes) = serde_json::to_vec(report) else {
        return;
    };
    let file_name = target
        .file_name()
        .map(|n| n.to_string_lossy())
        .unwrap_or_else(|| std::borrow::Cow::Borrowed("audit_spec_entry"));
    let tid_str: String = format!("{:?}", std::thread::current().id())
        .chars()
        .filter(|c| c.is_ascii_alphanumeric())
        .collect();
    let seq = AUDIT_SPEC_CACHE_TMP_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let tmp_path = parent.join(format!(
        ".{}.pid{}.{}.{}.tmp",
        file_name,
        std::process::id(),
        tid_str,
        seq
    ));
    if fs::write(&tmp_path, &bytes).is_ok() {
        if fs::rename(&tmp_path, target).is_err() {
            let _ = fs::remove_file(&tmp_path);
        }
    } else {
        let _ = fs::remove_file(&tmp_path);
    }
}

/// Unified specification & hygiene audit across `file` (or `inline_src`):
/// - **Tier 1 (Blocking, `"ok": false` if any > 0)**: `vacuous_specs`, `trivial_specs`, `shadowed_constants`, `forbidden_scope_decls`, `stub_defs`.
/// - **Tier 2 (Advisory, `"warnings"` only, non-blocking)**: `unused_private_decls`, `horizontal_packing_warnings`.
pub fn audit_spec_file_or_source(
    file: &Path,
    inline_src: Option<&str>,
    decl_filter: Option<&str>,
) -> serde_json::Value {
    let policy = AuditSpecPolicyConfig::load_for_target(file, None, None, &[], &[]);
    audit_spec_file_or_source_with_policy(file, inline_src, decl_filter, &policy)
}

pub fn audit_spec_file_or_source_with_policy(
    file: &Path,
    inline_src: Option<&str>,
    decl_filter: Option<&str>,
    policy: &AuditSpecPolicyConfig,
) -> serde_json::Value {
    audit_spec_file_or_source_inner(file, inline_src, decl_filter, policy, true)
}

fn audit_spec_file_or_source_inner(
    file: &Path,
    inline_src: Option<&str>,
    decl_filter: Option<&str>,
    policy: &AuditSpecPolicyConfig,
    expand_umbrella_subdir: bool,
) -> serde_json::Value {
    let t0 = Instant::now();
    let (eff_forbid_kinds, eff_allow_names, eff_forbid_namespaces) =
        policy.effective_forbidden_for_path(file);
    let mut cache_target_path: Option<PathBuf> = None;
    let mut cache_hex_key: Option<String> = None;
    let mut preloaded_file_src: Option<String> = None;
    if inline_src.is_none()
        && file.is_file()
        && (!expand_umbrella_subdir || !file.with_extension("").is_dir())
    {
        if let Ok(file_bytes) = fs::read(file) {
            if let Some(cache_dir) = resolve_audit_spec_cache_dir() {
                let hex_hash = compute_audit_spec_cache_key_with_policy(
                    file,
                    decl_filter,
                    &file_bytes,
                    policy,
                    &eff_forbid_kinds,
                    &eff_allow_names,
                    &eff_forbid_namespaces,
                );
                let cache_path = cache_dir.join(format!("{}.json", hex_hash));
                if let Ok(cached_bytes) = fs::read(&cache_path) {
                    if let Ok(mut cached_val) =
                        serde_json::from_slice::<serde_json::Value>(&cached_bytes)
                    {
                        let valid_schema = cached_val["schema_version"].as_u64()
                            == Some(u64::from(AUDIT_SPEC_CACHE_SCHEMA_VERSION))
                            && cached_val["cache_key"].as_str() == Some(hex_hash.as_str())
                            && cached_val["ok"].is_boolean();
                        if valid_schema {
                            let elapsed_ms =
                                (t0.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
                            if let Some(obj) = cached_val.as_object_mut() {
                                obj.insert(
                                    "file".to_string(),
                                    serde_json::json!(file.display().to_string()),
                                );
                                obj.insert("elapsed_ms".to_string(), serde_json::json!(elapsed_ms));
                                obj.insert("ms".to_string(), serde_json::json!(elapsed_ms));
                                obj.insert("cache_hit".to_string(), serde_json::json!(true));
                            }
                            return cached_val;
                        }
                    }
                }
                cache_target_path = Some(cache_path);
                cache_hex_key = Some(hex_hash);
            }
            if let Ok(s) = String::from_utf8(file_bytes) {
                preloaded_file_src = Some(s);
            }
        }
    }

    let mut read_errors: Vec<String> = Vec::new();
    let sources: Vec<(PathBuf, String)> = if let Some(s) = inline_src {
        vec![(file.to_path_buf(), s.to_string())]
    } else if file.is_dir() {
        let mut v = Vec::new();
        for p in crate::lake_build::collect_lean_files(file) {
            match fs::read_to_string(&p) {
                Ok(s) => v.push((p, s)),
                Err(e) => read_errors.push(format!("unreadable_source: {} ({})", p.display(), e)),
            }
        }
        if v.is_empty() && read_errors.is_empty() {
            let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
            return serde_json::json!({
                "status": "error",
                "ok": false,
                "verdict": "error",
                "error": format!("No readable Lean files found in {}", file.display()),
                "file": file.display().to_string(),
                "decl": decl_filter.unwrap_or("file"),
                "elapsed_ms": elapsed_ms,
                "ms": elapsed_ms,
            });
        }
        v
    } else {
        if !file.exists() {
            let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
            return serde_json::json!({
                "status": "error",
                "ok": false,
                "verdict": "error",
                "error": format!("Failed to read {}: path does not exist", file.display()),
                "file": file.display().to_string(),
                "decl": decl_filter.unwrap_or("file"),
                "elapsed_ms": elapsed_ms,
                "ms": elapsed_ms,
            });
        }
        let mut v: Vec<(PathBuf, String)> = match preloaded_file_src.or_else(|| fs::read_to_string(file).ok()) {
            Some(s) => vec![(file.to_path_buf(), s)],
            None => {
                let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
                return serde_json::json!({
                    "status": "error",
                    "ok": false,
                    "verdict": "error",
                    "error": format!("Failed to read {}", file.display()),
                    "file": file.display().to_string(),
                    "decl": decl_filter.unwrap_or("file"),
                    "elapsed_ms": elapsed_ms,
                    "ms": elapsed_ms,
                });
            }
        };
        if expand_umbrella_subdir {
            let sub_dir = file.with_extension("");
            if sub_dir.is_dir() {
                for p in crate::lake_build::collect_lean_files(&sub_dir) {
                    match fs::read_to_string(&p) {
                        Ok(s) => v.push((p, s)),
                        Err(e) => read_errors.push(format!("unreadable_source: {} ({})", p.display(), e)),
                    }
                }
            }
        }
        v
    };

    let mut total_specs_audited = 0usize;
    let mut vacuous_specs = 0usize;
    let mut trivial_specs = 0usize;
    let mut tight_specs = 0usize;
    let mut vacuous_spec_names = Vec::new();
    let mut trivial_spec_names = Vec::new();
    let mut shadowed_constants = Vec::new();
    let mut forbidden_scope_decls = read_errors.clone();
    let mut stub_defs = Vec::new();
    let mut unused_private_decls = Vec::new();
    let mut horizontal_packing_warnings = Vec::new();
    let mut droppable_hypotheses = Vec::new();
    let mut spec_details = Vec::new();

    for (src_path, src) in &sources {
        let (sh, un_priv, horiz) = crate::splitter::audit_source_declarations(src, decl_filter);
        shadowed_constants.extend(sh);
        unused_private_decls.extend(un_priv);
        horizontal_packing_warnings.extend(horiz);
        let clean_src = strip_lean_comments(src);
        let (path_forbid_kinds, path_allow_names, path_forbid_namespaces) =
            policy.effective_forbidden_for_path(src_path);
        for v in audit_forbidden_scope_declarations(
            &clean_src,
            &path_forbid_kinds,
            &path_allow_names,
            &path_forbid_namespaces,
        ) {
            if !forbidden_scope_decls.contains(&v) {
                forbidden_scope_decls.push(v);
            }
        }
        let mut local_defs = extract_local_def_unfoldings(&clean_src);
        if inline_src.is_none() && src_path.is_file() {
            for p in collect_imported_or_sibling_lean_files(src_path) {
                if let Ok(sib_src) = fs::read_to_string(&p) {
                    local_defs.extend(extract_local_def_unfoldings_with_vis(
                        &strip_lean_comments(&sib_src),
                        false,
                    ));
                }
            }
        }

        for d in extract_decls_fast(src, decl_filter) {
            total_specs_audited += 1;
            let ((is_vacuous, is_tight, reason), pos_witness, neg_witness, drop_hyps, decl_stubs) =
                audit_single_decl_spec_full_with_policy(&d, &local_defs, policy);
            droppable_hypotheses.extend(drop_hyps.iter().cloned());
            for st in &decl_stubs {
                if !stub_defs.contains(st) {
                    stub_defs.push(st.clone());
                }
            }
            let is_trivial = !is_vacuous && !is_tight;
            if is_vacuous {
                vacuous_specs += 1;
                vacuous_spec_names.push(d.name.clone());
            } else if is_trivial {
                trivial_specs += 1;
                trivial_spec_names.push(d.name.clone());
            } else {
                tight_specs += 1;
            }
            let verification_mode = if pos_witness.starts_with("sampled_fastcheck_verified") {
                "sampled_fastcheck_verified"
            } else {
                "structural_ast_verified"
            };
            spec_details.push(serde_json::json!({
                "decl": d.name,
                "vacuous": is_vacuous,
                "trivial": is_trivial,
                "tight": is_tight,
                "verification_mode": verification_mode,
                "assessment": reason,
                "pos_witness": pos_witness,
                "neg_witness": neg_witness,
                "droppable_hypotheses": drop_hyps,
                "stub_defs": decl_stubs,
            }));
        }
    }

    let unmatched_decl_filter = decl_filter
        .is_some_and(|df| !df.trim().is_empty() && df != "file" && df != "auto")
        && total_specs_audited == 0;
    let mut warnings: Vec<String> = unused_private_decls
        .iter()
        .map(|u| format!("unused_private_decl: {}", u))
        .collect();
    warnings.extend(
        horizontal_packing_warnings
            .iter()
            .map(|h| format!("horizontal_packing: {}", h)),
    );
    warnings.extend(
        droppable_hypotheses
            .iter()
            .map(|dh| format!("droppable_hypothesis: {}", dh)),
    );
    let tier1_clean = !sources.is_empty()
        && read_errors.is_empty()
        && !unmatched_decl_filter
        && vacuous_specs == 0
        && trivial_specs == 0
        && shadowed_constants.is_empty()
        && forbidden_scope_decls.is_empty()
        && stub_defs.is_empty();
    let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
    let report = serde_json::json!({
        "schema_version": AUDIT_SPEC_CACHE_SCHEMA_VERSION,
        "cache_key": cache_hex_key.as_deref().unwrap_or(""),
        "status": if tier1_clean { "ok" } else { "failed" },
        "ok": tier1_clean,
        "verdict": if unmatched_decl_filter { "decl_not_found" } else { "specs_audited" },
        "policy": policy.policy,
        "file": file.display().to_string(),
        "decl": decl_filter.unwrap_or("file"),
        "total_specs_audited": total_specs_audited,
        "vacuous_specs": vacuous_specs,
        "trivial_specs": trivial_specs,
        "tight_specs": tight_specs,
        "vacuous": vacuous_specs > 0,
        "vacuous_spec_names": vacuous_spec_names,
        "trivial_spec_names": trivial_spec_names,
        "shadowed_constants": shadowed_constants,
        "forbidden_scope_decls": forbidden_scope_decls,
        "stub_defs": stub_defs,
        "unused_private_decls": unused_private_decls,
        "horizontal_packing_warnings": horizontal_packing_warnings,
        "droppable_hypotheses": droppable_hypotheses,
        "warnings": warnings,
        "specs": spec_details,
        "cache_hit": false,
        "elapsed_ms": elapsed_ms,
        "ms": elapsed_ms,
    });
    if let Some(ref cache_path) = cache_target_path {
        write_audit_spec_cache_atomic(cache_path, &report);
    }
    report
}

/// Audit theorem specifications across multiple `files` concurrently and merge into a unified report.
pub fn audit_spec_files(files: &[PathBuf], decl_filter: Option<&str>) -> serde_json::Value {
    let policy = files
        .first()
        .map(|f| AuditSpecPolicyConfig::load_for_target(f, None, None, &[], &[]))
        .unwrap_or_default();
    audit_spec_files_with_policy(files, decl_filter, &policy)
}

pub fn audit_spec_files_with_policy(
    files: &[PathBuf],
    decl_filter: Option<&str>,
    policy: &AuditSpecPolicyConfig,
) -> serde_json::Value {
    let mut expanded_files: Vec<PathBuf> = Vec::new();
    let mut seen_files = std::collections::HashSet::new();
    let mut push_unique = |p: PathBuf| {
        let key = p.canonicalize().unwrap_or_else(|_| p.clone());
        if seen_files.insert(key) {
            expanded_files.push(p);
        }
    };
    for f in files {
        if f.is_dir() {
            for p in crate::lake_build::collect_lean_files(f) {
                push_unique(p);
            }
        } else {
            push_unique(f.clone());
            let sub_dir = f.with_extension("");
            if sub_dir.is_dir() {
                for p in crate::lake_build::collect_lean_files(&sub_dir) {
                    push_unique(p);
                }
            }
        }
    }
    if expanded_files.is_empty() {
        if let Some(first) = files.first() {
            return audit_spec_file_or_source_with_policy(first, None, decl_filter, policy);
        }
    }
    if expanded_files.len() == 1 && files.len() == 1 && !files[0].is_dir() {
        return audit_spec_file_or_source_inner(&expanded_files[0], None, decl_filter, policy, false);
    }
    let t0 = Instant::now();
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .min(expanded_files.len().max(1));
    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let mut worker_panicked = false;
    let expanded_ref = &expanded_files;
    let per_file_reports: Vec<serde_json::Value> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..workers)
            .map(|_| {
                let next_ref = &next_idx;
                s.spawn(move || {
                    let mut local = Vec::new();
                    loop {
                        let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if i >= expanded_ref.len() {
                            break;
                        }
                        local.push((
                            i,
                            audit_spec_file_or_source_inner(
                                &expanded_ref[i],
                                None,
                                decl_filter,
                                policy,
                                false,
                            ),
                        ));
                    }
                    local
                })
            })
            .collect();
        let mut indexed: Vec<(usize, serde_json::Value)> = Vec::new();
        for h in handles {
            match h.join() {
                Ok(batch) => indexed.extend(batch),
                Err(_) => worker_panicked = true,
            }
        }
        indexed.sort_by_key(|(i, _)| *i);
        indexed.into_iter().map(|(_, r)| r).collect()
    });

    let mut total_specs_audited = 0usize;
    let mut vacuous_specs = 0usize;
    let mut trivial_specs = 0usize;
    let mut tight_specs = 0usize;
    let mut vacuous_spec_names = Vec::new();
    let mut trivial_spec_names = Vec::new();
    let mut shadowed_constants = Vec::new();
    let mut forbidden_scope_decls = Vec::new();
    if worker_panicked {
        forbidden_scope_decls.push(serde_json::json!("worker_thread_panic"));
    }
    let mut stub_defs = Vec::new();
    let mut unused_private_decls = Vec::new();
    let mut horizontal_packing_warnings = Vec::new();
    let mut droppable_hypotheses = Vec::new();
    let mut warnings = Vec::new();
    let mut spec_details = Vec::new();
    let mut file_labels = Vec::new();
    let mut cache_hits = 0usize;
    let mut any_report_error = false;
    let mut error_messages = Vec::new();

    for rep in &per_file_reports {
        if rep["status"].as_str() == Some("error")
            || (rep["ok"].as_bool() == Some(false) && rep["verdict"].as_str() == Some("error"))
        {
            any_report_error = true;
            if let Some(em) = rep["error"].as_str() {
                error_messages.push(em.to_string());
            }
        }
        if let Some(f) = rep["file"].as_str() {
            file_labels.push(f.to_string());
        }
        if rep["cache_hit"].as_bool() == Some(true) {
            cache_hits += 1;
        }
        total_specs_audited += rep["total_specs_audited"].as_u64().unwrap_or(0) as usize;
        vacuous_specs += rep["vacuous_specs"].as_u64().unwrap_or(0) as usize;
        trivial_specs += rep["trivial_specs"].as_u64().unwrap_or(0) as usize;
        tight_specs += rep["tight_specs"].as_u64().unwrap_or(0) as usize;
        if let Some(arr) = rep["vacuous_spec_names"].as_array() {
            vacuous_spec_names.extend(arr.iter().cloned());
        }
        if let Some(arr) = rep["trivial_spec_names"].as_array() {
            trivial_spec_names.extend(arr.iter().cloned());
        }
        if let Some(arr) = rep["shadowed_constants"].as_array() {
            shadowed_constants.extend(arr.iter().cloned());
        }
        if let Some(arr) = rep["forbidden_scope_decls"].as_array() {
            forbidden_scope_decls.extend(arr.iter().cloned());
        }
        if let Some(arr) = rep["stub_defs"].as_array() {
            stub_defs.extend(arr.iter().cloned());
        }
        if let Some(arr) = rep["unused_private_decls"].as_array() {
            unused_private_decls.extend(arr.iter().cloned());
        }
        if let Some(arr) = rep["horizontal_packing_warnings"].as_array() {
            horizontal_packing_warnings.extend(arr.iter().cloned());
        }
        if let Some(arr) = rep["droppable_hypotheses"].as_array() {
            droppable_hypotheses.extend(arr.iter().cloned());
        }
        if let Some(arr) = rep["warnings"].as_array() {
            warnings.extend(arr.iter().cloned());
        }
        if let Some(arr) = rep["specs"].as_array() {
            spec_details.extend(arr.iter().cloned());
        }
    }

    let has_explicit_decl_filter = decl_filter
        .is_some_and(|df| !df.trim().is_empty() && df != "file" && df != "auto");
    let unmatched_decl_filter = has_explicit_decl_filter && total_specs_audited == 0;
    let all_files_ok = !expanded_files.is_empty()
        && per_file_reports.len() == expanded_files.len()
        && per_file_reports.iter().all(|r| {
            r["ok"].as_bool() == Some(true)
                || (has_explicit_decl_filter
                    && total_specs_audited > 0
                    && r["verdict"].as_str() == Some("decl_not_found"))
        });
    let tier1_clean = !any_report_error
        && !worker_panicked
        && !unmatched_decl_filter
        && all_files_ok
        && vacuous_specs == 0
        && trivial_specs == 0
        && shadowed_constants.is_empty()
        && forbidden_scope_decls.is_empty()
        && stub_defs.is_empty();
    let all_cache_hit = !per_file_reports.is_empty() && cache_hits == per_file_reports.len();
    let top_file_label = if files.len() == 1 {
        files[0].display().to_string()
    } else {
        file_labels.join(", ")
    };
    let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
    let mut out = serde_json::json!({
        "schema_version": AUDIT_SPEC_CACHE_SCHEMA_VERSION,
        "status": if any_report_error { "error" } else if tier1_clean { "ok" } else { "failed" },
        "ok": tier1_clean,
        "verdict": if any_report_error { "error" } else if unmatched_decl_filter { "decl_not_found" } else { "specs_audited" },
        "policy": policy.policy,
        "file": top_file_label,
        "files": file_labels,
        "file_reports": per_file_reports,
        "decl": decl_filter.unwrap_or("file"),
        "total_specs_audited": total_specs_audited,
        "vacuous_specs": vacuous_specs,
        "trivial_specs": trivial_specs,
        "tight_specs": tight_specs,
        "vacuous": vacuous_specs > 0,
        "vacuous_spec_names": vacuous_spec_names,
        "trivial_spec_names": trivial_spec_names,
        "shadowed_constants": shadowed_constants,
        "forbidden_scope_decls": forbidden_scope_decls,
        "stub_defs": stub_defs,
        "unused_private_decls": unused_private_decls,
        "horizontal_packing_warnings": horizontal_packing_warnings,
        "droppable_hypotheses": droppable_hypotheses,
        "warnings": warnings,
        "specs": spec_details,
        "cache_hit": all_cache_hit,
        "cache_hits": cache_hits,
        "elapsed_ms": elapsed_ms,
        "ms": elapsed_ms,
    });
    if !error_messages.is_empty() {
        out["error"] = serde_json::json!(error_messages.join("; "));
    }
    out
}

/// Audit theorem specifications in `files` for vacuous preconditions and postcondition tightness.
pub fn run_audit_spec_command(files: &[PathBuf], decl_filter: Option<&str>, json_mode: bool) -> Result<()> {
    run_audit_spec_command_with_options(files, decl_filter, json_mode, None, None, &[], &[])
}

pub fn run_audit_spec_command_with_options(
    files: &[PathBuf],
    decl_filter: Option<&str>,
    json_mode: bool,
    policy_override: Option<&str>,
    config_override: Option<&Path>,
    forbid_namespaces: &[String],
    forbid_decl_kinds: &[String],
) -> Result<()> {
    anyhow::ensure!(!files.is_empty(), "No files provided to audit-spec");
    for f in files {
        anyhow::ensure!(f.exists(), "Failed to read {}: path does not exist", f.display());
    }
    let first_file = &files[0];
    let policy = AuditSpecPolicyConfig::load_for_target(
        first_file,
        policy_override,
        config_override,
        forbid_namespaces,
        forbid_decl_kinds,
    );
    let report = audit_spec_files_with_policy(files, decl_filter, &policy);
    if crate::mcp::should_emit_cli_telemetry() {
        let ok_flag = report["ok"].as_bool().unwrap_or(false);
        let decl_label = decl_filter.map(String::from).unwrap_or_else(|| {
            if files.len() == 1 {
                first_file
                    .file_name()
                    .map(|s| s.to_string_lossy().to_string())
                    .unwrap_or_else(|| first_file.display().to_string())
            } else {
                format!("batch({})", files.len())
            }
        });
        let proj_dir = if first_file.is_dir() {
            first_file.as_path()
        } else {
            first_file.parent().unwrap_or_else(|| Path::new("."))
        };
        crate::mcp::emit_cli_telemetry_event(
            Some(proj_dir),
            true,
            serde_json::json!({
                "schema": "turbo-lean.telemetry.v1",
                "tool_name": "audit_spec",
                "command": "audit-spec",
                "policy": report["policy"],
                "decl_name": decl_label,
                "file_path": report["file"],
                "status": if ok_flag { "ok" } else { "failed" },
                "accepted": ok_flag,
                "total_specs_audited": report["total_specs_audited"],
                "tight_specs": report["tight_specs"],
                "vacuous_specs": report["vacuous_specs"],
                "trivial_specs": report["trivial_specs"],
                "shadowed_constants_count": report["shadowed_constants"].as_array().map_or(0, Vec::len),
                "forbidden_scope_decls_count": report["forbidden_scope_decls"].as_array().map_or(0, Vec::len),
                "stub_defs_count": report["stub_defs"].as_array().map_or(0, Vec::len),
                "elapsed_ms": report["elapsed_ms"],
            }),
            "turbo_lean_events.jsonl",
        );
    }
    if json_mode {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        println!(
            "[turbo-lean] AUDIT-SPEC ({}) on {}: ok={} audited={} tight={} vacuous={} trivial={} shadowed={} forbidden_scope={} stubs={} warnings={} ({:.3} ms)",
            report["policy"].as_str().unwrap_or("default"),
            report["file"].as_str().unwrap_or_default(),
            report["ok"],
            report["total_specs_audited"],
            report["tight_specs"],
            report["vacuous_specs"],
            report["trivial_specs"],
            report["shadowed_constants"].as_array().map_or(0, Vec::len),
            report["forbidden_scope_decls"].as_array().map_or(0, Vec::len),
            report["stub_defs"].as_array().map_or(0, Vec::len),
            report["warnings"].as_array().map_or(0, Vec::len),
            report["elapsed_ms"].as_f64().unwrap_or(0.0),
        );
    }
    anyhow::ensure!(
        report["ok"].as_bool() == Some(true),
        "Specification audit failed on {} (vacuous={}, trivial={}, shadowed={}, forbidden_scope={}, stubs={})",
        report["file"].as_str().unwrap_or_default(),
        report["vacuous_specs"],
        report["trivial_specs"],
        report["shadowed_constants"].as_array().map_or(0, Vec::len),
        report["forbidden_scope_decls"].as_array().map_or(0, Vec::len),
        report["stub_defs"].as_array().map_or(0, Vec::len),
    );
    Ok(())
}

