//! Specification auditor extracted mechanically from gpu_fastcheck.rs.

use super::*;

pub(super) fn inline_stmt_let_bindings(stmt: &str) -> String {
    let mut cur = stmt.trim().to_string();
    for _ in 0..16 {
        let trimmed = cur.trim_start();
        let Some(after_let) = trimmed
            .strip_prefix("let")
            .filter(|r| r.starts_with(char::is_whitespace))
        else {
            break;
        };
        let rest = after_let.trim_start();
        let name_end = rest
            .find(|c: char| !is_ident_continue(c))
            .unwrap_or(rest.len());
        if name_end == 0 {
            break;
        }
        let var_name = &rest[..name_end];
        let after_name = &rest[name_end..];
        let Some(eq_idx) = after_name.find(":=") else {
            break;
        };
        let after_eq = after_name[eq_idx + 2..].trim_start();
        // Find top-level `;` or `\n` terminating the `let` RHS
        let chars: Vec<char> = after_eq.chars().collect();
        let mut p_depth = 0usize;
        let mut split_char_idx = None;
        for (idx, &ch) in chars.iter().enumerate() {
            match ch {
                '(' | '{' | '[' | '⟨' => p_depth += 1,
                ')' | '}' | ']' | '⟩' => p_depth = p_depth.saturating_sub(1),
                ';' | '\n' if p_depth == 0 => {
                    split_char_idx = Some(idx);
                    break;
                }
                _ => {}
            }
        }
        let Some(sc_idx) = split_char_idx else {
            break;
        };
        let rhs: String = chars[..sc_idx].iter().collect();
        let body: String = chars[sc_idx + 1..].iter().collect();
        let rhs_wrapped = format!("({})", rhs.trim());
        cur = replace_ident_boundary(body.trim(), var_name, &rhs_wrapped);
    }
    cur
}

/// A literal or comment beginning at a UTF-8 byte boundary. Unterminated strings
/// and block comments consume the remainder so their contents cannot become code.
struct LeanLexicalSpan {
    end: usize,
    is_comment: bool,
}

fn skip_lean_lexeme(src: &str, start: usize) -> Option<LeanLexicalSpan> {
    let bytes = src.as_bytes();
    let mut i = start;
    let is_comment = src[start..].starts_with("--") || src[start..].starts_with("/-");
    match *bytes.get(start)? {
        b'-' if src[start..].starts_with("--") => {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
        }
        b'/' if src[start..].starts_with("/-") => {
            i += 2;
            let mut depth = 1usize;
            while i < bytes.len() && depth > 0 {
                if bytes[i..].starts_with(b"/-") {
                    depth += 1;
                    i += 2;
                } else if bytes[i..].starts_with(b"-/") {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
        }
        b'\'' => i = crate::splitter::scan_lean_char_lit_end(src, start)?,
        b'"' => {
            i += 1;
            while i < bytes.len() {
                match bytes[i] {
                    b'\\' => i = (i + 2).min(bytes.len()),
                    b'"' => {
                        i += 1;
                        break;
                    }
                    _ => i += 1,
                }
            }
        }
        b'r' if !src[..start]
            .chars()
            .next_back()
            .is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '\'') =>
        {
            i += 1;
            while bytes.get(i) == Some(&b'#') {
                i += 1;
            }
            let hashes = i - start - 1;
            if bytes.get(i) != Some(&b'"') {
                return None;
            }
            i += 1;
            while i < bytes.len() {
                if bytes[i] == b'"'
                    && bytes[i + 1..].starts_with(&bytes[start + 1..start + 1 + hashes])
                {
                    i += 1 + hashes;
                    break;
                }
                i += 1;
            }
        }
        _ => return None,
    }
    Some(LeanLexicalSpan { end: i, is_comment })
}

/// Audit-only stripping: preserve literal text, byte offsets, and newlines.
/// The splitter's existing shared stripper deliberately retains its behavior.
fn strip_audit_comments(src: &str) -> String {
    let mut out = src.as_bytes().to_vec();
    let mut i = 0;
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
            i += src[i..].chars().next().unwrap().len_utf8();
        }
    }
    String::from_utf8(out).expect("masking comments preserves UTF-8")
}

pub(super) fn decl_matches_requested_target(
    decl_name: &str,
    qualified_name: &str,
    target: &str,
) -> bool {
    let target = target.trim();
    if let Some(root_target) = target.strip_prefix("_root_.") {
        return qualified_name == root_target;
    }
    qualified_name == target
        || (!target.contains('.')
            && (decl_name == target || qualified_name.ends_with(&format!(".{}", target))))
}

pub(super) fn select_target_decl_unambiguously(
    decls: Vec<ExtractedDecl>,
    target_name: Option<&str>,
) -> Option<ExtractedDecl> {
    match target_name.map(str::trim) {
        Some(t) if !t.is_empty() && t != "auto" => {
            let mut matches: Vec<ExtractedDecl> = decls
                .into_iter()
                .filter(|d| decl_matches_requested_target(&d.name, &d.qualified_name, t))
                .collect();
            (matches.len() == 1).then(|| matches.swap_remove(0))
        }
        _ => decls.into_iter().next(),
    }
}

pub(super) fn extract_all_lean_theorems(
    clean_src: &str,
    target_name: Option<&str>,
) -> Vec<ExtractedDecl> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum LexScopeKind {
        Namespace,
        Section,
        Mutual,
    }
    let clean_src = strip_audit_comments(clean_src);
    let chars: Vec<char> = clean_src.chars().collect();
    let byte_offsets: Vec<usize> = clean_src.char_indices().map(|(offset, _)| offset).collect();
    let skip_at = |i: usize| {
        skip_lean_lexeme(&clean_src, byte_offsets[i])
            .map(|span| byte_offsets.partition_point(|offset| *offset < span.end))
    };
    let is_line_command_head = |pos: usize| -> bool {
        let mut p = pos;
        while p > 0 && chars[p - 1] != '\n' {
            p -= 1;
        }
        let mut cur = p;
        while cur < pos {
            while cur < pos && chars[cur].is_whitespace() {
                cur += 1;
            }
            if cur >= pos {
                return true;
            }
            if cur + 1 < pos && chars[cur] == '@' && chars[cur + 1] == '[' {
                let mut depth = 1usize;
                cur += 2;
                while cur < pos && depth > 0 {
                    if let Some(end) = skip_at(cur) {
                        cur = end;
                        continue;
                    }
                    if chars[cur] == '[' {
                        depth += 1;
                    } else if chars[cur] == ']' {
                        depth -= 1;
                    }
                    cur += 1;
                }
                continue;
            }
            if is_ident_start(chars[cur]) {
                let ws = cur;
                while cur < pos && is_ident_continue(chars[cur]) {
                    cur += 1;
                }
                let kw: String = chars[ws..cur].iter().collect();
                if matches!(
                    kw.as_str(),
                    "noncomputable"
                        | "private"
                        | "protected"
                        | "scoped"
                        | "local"
                        | "unsafe"
                        | "partial"
                        | "nonrec"
                        | "public"
                        | "meta"
                ) {
                    continue;
                }
                if matches!(
                    kw.as_str(),
                    "set_option" | "open" | "variable" | "universe" | "include" | "omit"
                ) {
                    let mut found_in = false;
                    while cur < pos {
                        if let Some(end) = skip_at(cur) {
                            cur = end;
                            continue;
                        }
                        if is_ident_start(chars[cur]) {
                            let is = cur;
                            while cur < pos && is_ident_continue(chars[cur]) {
                                cur += 1;
                            }
                            if chars[is..cur] == ['i', 'n'] {
                                found_in = true;
                                break;
                            }
                        } else {
                            cur += 1;
                        }
                    }
                    if found_in {
                        continue;
                    }
                }
            }
            return false;
        }
        true
    };
    let read_dotted_ident = |mut idx: usize, limit: usize| -> (String, usize) {
        while idx < limit && (chars[idx] == ' ' || chars[idx] == '\t') {
            idx += 1;
        }
        let s = idx;
        while idx < limit && (is_ident_continue(chars[idx]) || chars[idx] == '.') {
            idx += 1;
        }
        (chars[s..idx].iter().collect(), idx)
    };
    let n = chars.len();
    let mut i = 0;
    let mut scope_stack: Vec<(LexScopeKind, String)> = Vec::new();
    let mut all_decls: Vec<ExtractedDecl> = Vec::new();

    while i < n {
        if let Some(end) = skip_at(i) {
            i = end;
            continue;
        }
        if is_ident_start(chars[i]) {
            let start = i;
            let prev_is_dot_or_guillemet =
                start > 0 && matches!(chars[start - 1], '.' | '«');
            while i < n && is_ident_continue(chars[i]) {
                i += 1;
            }
            if prev_is_dot_or_guillemet {
                continue;
            }
            let word: String = chars[start..i].iter().collect();
            if is_line_command_head(start) {
                match word.as_str() {
                    "namespace" => {
                        let (ns_name, next_i) = read_dotted_ident(i, n);
                        i = next_i;
                        for seg in ns_name.split('.').filter(|s| !s.is_empty()) {
                            scope_stack.push((LexScopeKind::Namespace, seg.to_string()));
                        }
                        continue;
                    }
                    "section" => {
                        let (sec_name, next_i) = read_dotted_ident(i, n);
                        i = next_i;
                        if sec_name.is_empty() {
                            scope_stack.push((LexScopeKind::Section, String::new()));
                        } else {
                            for seg in sec_name.split('.').filter(|s| !s.is_empty()) {
                                scope_stack.push((LexScopeKind::Section, seg.to_string()));
                            }
                        }
                        continue;
                    }
                    "mutual" => {
                        scope_stack.push((LexScopeKind::Mutual, String::new()));
                        continue;
                    }
                    "end" => {
                        let (end_name, next_i) = read_dotted_ident(i, n);
                        i = next_i;
                        if end_name.is_empty() {
                            scope_stack.pop();
                        } else {
                            for seg in end_name.split('.').filter(|s| !s.is_empty()).rev() {
                                if let Some(pos) =
                                    scope_stack.iter().rposition(|(_, name)| name == seg)
                                {
                                    scope_stack.truncate(pos);
                                } else {
                                    scope_stack.pop();
                                }
                            }
                        }
                        continue;
                    }
                    _ => {}
                }
            }
            if (word == "theorem" || word == "lemma") && is_line_command_head(start) {
                while i < n && chars[i].is_whitespace() {
                    i += 1;
                }
                let name_start = i;
                while i < n && (is_ident_continue(chars[i]) || chars[i] == '.') {
                    i += 1;
                }
                if i == name_start {
                    continue;
                }
                let raw_decl_name: String = chars[name_start..i].iter().collect();
                let (decl_name, qualified_name) =
                    if let Some(root_stripped) = raw_decl_name.strip_prefix("_root_.") {
                        (root_stripped.to_string(), root_stripped.to_string())
                    } else {
                        let q = scope_stack
                            .iter()
                            .filter(|(k, _)| *k == LexScopeKind::Namespace)
                            .map(|(_, s)| s.as_str())
                            .chain(std::iter::once(raw_decl_name.as_str()))
                            .collect::<Vec<_>>()
                            .join(".");
                        (raw_decl_name, q)
                    };

                let mut binders = Vec::new();
                let mut instance_binders = Vec::new();
                let mut found_colon = false;
                while i < n {
                    while i < n && chars[i].is_whitespace() {
                        i += 1;
                    }
                    if i >= n {
                        break;
                    }
                    if let Some(end) = skip_at(i) {
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
                    if chars[i] == '(' || chars[i] == '{' || chars[i] == '[' {
                        let open = chars[i];
                        let close = match open {
                            '(' => ')',
                            '{' => '}',
                            '[' => ']',
                            _ => unreachable!(),
                        };
                        i += 1;
                        let b_start = i;
                        let mut depth = 1usize;
                        while i < n && depth > 0 {
                            if let Some(end) = skip_at(i) {
                                i = end;
                                continue;
                            }
                            if chars[i] == open {
                                depth += 1;
                            } else if chars[i] == close {
                                depth -= 1;
                            }
                            i += 1;
                        }
                        let inner: String = chars[b_start..i.saturating_sub(1)].iter().collect();
                        if open == '(' || open == '{' {
                            if let Some((vars_part, ty_part)) = split_top_level_colon(&inner) {
                                let var_names: Vec<String> = vars_part
                                    .split_whitespace()
                                    .map(|s| s.trim().to_string())
                                    .filter(|s| !s.is_empty())
                                    .collect();
                                if !var_names.is_empty() {
                                    binders.push((var_names, ty_part.trim().to_string()));
                                }
                            }
                        } else {
                            let inst_ty = split_top_level_colon(&inner)
                                .map(|(_, ty)| ty.trim())
                                .unwrap_or_else(|| inner.trim());
                            instance_binders.push(inst_ty.to_string());
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
                let mut in_stmt_match = false;
                let mut stmt_end = n;
                while i < n {
                    if let Some(end) = skip_at(i) {
                        i = end;
                        continue;
                    }
                    let c = chars[i];
                    if c == '(' || c == '{' || c == '[' {
                        paren_depth += 1;
                    } else if c == ')' || c == '}' || c == ']' {
                        paren_depth = paren_depth.saturating_sub(1);
                    } else if c == '⟨' {
                        angle_depth += 1;
                    } else if c == '⟩' {
                        angle_depth = angle_depth.saturating_sub(1);
                    } else if paren_depth == 0
                        && angle_depth == 0
                        && c == 'm'
                        && i + 5 < n
                        && chars[i + 1] == 'a'
                        && chars[i + 2] == 't'
                        && chars[i + 3] == 'c'
                        && chars[i + 4] == 'h'
                        && chars[i + 5].is_whitespace()
                        && (i == stmt_start || !is_ident_continue(chars[i - 1]))
                    {
                        in_stmt_match = true;
                        i += 5;
                        continue;
                    } else if paren_depth == 0
                        && angle_depth == 0
                        && c == 'l'
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
                        && c == ':'
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
                        && !in_stmt_match
                        && c == '|'
                        && i > stmt_start
                    {
                        // Pattern-matching theorem without `:=`
                        let prev_nl = chars[stmt_start..i].contains(&'\n');
                        if prev_nl {
                            stmt_end = i;
                            break;
                        }
                    }
                    i += 1;
                }
                let prop_str: String = chars[stmt_start..stmt_end].iter().collect();
                let trimmed = inline_stmt_let_bindings(prop_str.trim());
                if !trimmed.is_empty() {
                    all_decls.push(ExtractedDecl {
                        name: decl_name,
                        qualified_name,
                        binders,
                        instance_binders,
                        prop_str: trimmed,
                    });
                }
            }
        } else {
            i += 1;
        }
    }
    match target_name.map(str::trim) {
        Some(t) if !t.is_empty() && t != "auto" => {
            select_target_decl_unambiguously(all_decls, Some(t))
                .into_iter()
                .collect()
        }
        _ => all_decls,
    }
}

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

/// Extract 1-level local `def`/`abbrev` definitions (`name`, `params`, `body`) from clean Lean source
/// so `audit-spec` can delta-unfold predicate wrappers (e.g., `def Impossible (x : Nat) : Prop := x < 0`),
/// multi-line lowering definitions (`def evalLCNF ... :=\n  evalCode ...`), and tautological conclusion wrappers.
// Name, application parameters, body, and binder-type dependencies.
// Dependencies in types are real uses even when absent from an erased body.
pub(super) type LocalDefUnfolding = (String, Vec<String>, String, String);

pub(super) fn extract_local_def_unfoldings(clean_src: &str) -> Vec<LocalDefUnfolding> {
    let mut defs = Vec::new();
    let lines: Vec<&str> = clean_src.lines().collect();
    let mut current_ns = String::new();
    let mut idx = 0usize;

    while idx < lines.len() {
        let mut line = lines[idx].trim();
        if let Some(ns) = line.strip_prefix("namespace ") {
            let ns_name = ns.split_whitespace().next().unwrap_or("").trim();
            if !ns_name.is_empty() {
                current_ns = if current_ns.is_empty() {
                    ns_name.to_string()
                } else {
                    format!("{}.{}", current_ns, ns_name)
                };
            }
            idx += 1;
            continue;
        }
        if line == "end" || line.starts_with("end ") {
            let end_ns = line.strip_prefix("end").unwrap_or("").trim();
            if end_ns.is_empty() {
                current_ns.clear();
            } else if current_ns == end_ns {
                current_ns.clear();
            } else if let Some(prefix) = current_ns.strip_suffix(&format!(".{}", end_ns)) {
                current_ns = prefix.to_string();
            }
            idx += 1;
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
            combined.push(' ');
            combined.push_str(next_trim);
            idx += 1;
        }

        let Some((sig, body_raw)) = split_at_first_top_level_assign(&combined) else {
            continue;
        };
        if sig.ends_with(" where") || sig.contains(" where ") {
            continue;
        }
        let body = body_raw.trim();
        if body.is_empty()
            || body.starts_with("by ")
            || body.starts_with("do")
            || body.starts_with("Id.run")
            || body.ends_with(" do")
        {
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
        let mut params = Vec::new();
        let mut type_dependencies = String::new();
        let chars: Vec<char> = after_name.chars().collect();
        let mut i = 0;
        while i < chars.len() {
            while i < chars.len() && chars[i].is_whitespace() {
                i += 1;
            }
            if i >= chars.len()
                || (chars[i] == ':' && (i + 1 >= chars.len() || chars[i + 1] != '='))
            {
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
                    let binder = split_top_level_colon(&inner);
                    if let Some((_, ty)) = binder {
                        type_dependencies.push_str(ty);
                        type_dependencies.push(' ');
                    }
                    let vars_part = binder.map(|(v, _)| v).unwrap_or(inner.as_str());
                    let later_signature: String = chars[i..].iter().collect();
                    for v in vars_part.split_whitespace() {
                        // Inferred type parameters used by later parameter/result
                        // types are not runtime application arguments. Do not
                        // mistake their absence from an erased body for a stub.
                        // Unused ghost types and implicit value parameters stay
                        // subject to the ordinary unused-parameter policy.
                        if open == '{'
                            && binder.is_some_and(|(_, ty)| ty.trim() == "Type")
                            && replace_ident_boundary(&later_signature, v, "__TYPE__")
                                != later_signature
                        {
                            continue;
                        }
                        if !v.is_empty() {
                            params.push(v.to_string());
                        }
                    }
                }
            } else if is_ident_start(chars[i]) {
                let s = i;
                while i < chars.len() && is_ident_continue(chars[i]) {
                    i += 1;
                }
                params.push(chars[s..i].iter().collect());
            } else {
                i += 1;
            }
        }
        defs.push((def_name, params, body.to_string(), type_dependencies));
    }
    defs
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
            let next_ok =
                i + id_chars.len() == chars.len() || !is_ident_continue(chars[i + id_chars.len()]);
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

pub(super) fn strip_balanced_outer_parens(s: &str) -> &str {
    let mut cur = s.trim();
    loop {
        if cur.starts_with('(') && cur.ends_with(')') && cur.len() >= 2 {
            let inner = &cur[1..cur.len() - 1];
            let mut depth = 0i32;
            let mut balanced = true;
            for c in inner.chars() {
                if c == '(' {
                    depth += 1;
                } else if c == ')' {
                    depth -= 1;
                    if depth < 0 {
                        balanced = false;
                        break;
                    }
                }
            }
            if balanced && depth == 0 {
                cur = inner.trim();
                continue;
            }
        }
        break;
    }
    cur
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
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth = (depth - 1).max(0),
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
                if matches!(prev, Some('!' | '<' | '>' | ':' | '='))
                    || matches!(next, Some('=' | '>'))
                {
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
                if chars[i] == open {
                    depth += 1;
                } else if chars[i] == close {
                    depth -= 1;
                }
                i += 1;
            }
            let inner: String = chars[start..i.saturating_sub(1)].iter().collect();
            args.push(inner.trim().to_string());
        } else {
            let start = i;
            let mut depth = 0usize;
            while i < n {
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

pub(super) fn unfold_expr_single_step(expr: &str, local_defs: &[LocalDefUnfolding]) -> String {
    let inlined = inline_stmt_let_bindings(expr);
    let trimmed = strip_balanced_outer_parens(&inlined);
    let conjuncts = split_top_level_conjuncts(trimmed);
    if conjuncts.len() > 1 {
        return conjuncts
            .into_iter()
            .map(|c| unfold_expr_single_step(&c, local_defs))
            .collect::<Vec<_>>()
            .join(" ∧ ");
    }
    if let Some((lhs, rhs, op)) = split_top_level_rel(trimmed) {
        let u_lhs = unfold_expr_single_step(&lhs, local_defs);
        let u_rhs = unfold_expr_single_step(&rhs, local_defs);
        let fmt_l = if op == "→" && split_top_level_conjuncts(&u_lhs).len() > 1 {
            format!("({})", u_lhs)
        } else {
            u_lhs
        };
        let fmt_r = if op == "→" && split_top_level_conjuncts(&u_rhs).len() > 1 {
            format!("({})", u_rhs)
        } else {
            u_rhs
        };
        return format!("{} {} {}", fmt_l, op, fmt_r);
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
            let clean_inner = strip_balanced_outer_parens(&reconstructed);
            let u_inner = unfold_expr_single_step(clean_inner, local_defs);
            if u_inner != clean_inner {
                return format!("{} ({})", head_kw, u_inner);
            }
        }
    }
    for (def_name, params, body, _) in local_defs {
        let short = def_name.rsplit('.').next().unwrap_or(def_name.as_str());
        if body.len() > 240
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
                    if args.len() == params.len() && !params.is_empty() {
                        let mut unfolded = body.clone();
                        for (p, a) in params.iter().zip(args.iter()) {
                            let u_arg = unfold_expr_single_step(a, local_defs);
                            let rep = if u_arg.contains(char::is_whitespace) {
                                format!("({})", u_arg)
                            } else {
                                u_arg
                            };
                            unfolded = replace_ident_boundary(&unfolded, p, &rep);
                        }
                        return unfolded;
                    }
                }
            }
        }
    }
    if let Some(space_idx) = trimmed.find(char::is_whitespace) {
        let head = &trimmed[..space_idx];
        let rest = &trimmed[space_idx..];
        let args = split_lean_app_args(rest);
        if !args.is_empty() {
            let mut any_changed = false;
            let mut u_args = Vec::with_capacity(args.len());
            for a in &args {
                let ua = unfold_expr_single_step(a, local_defs);
                if &ua != a {
                    any_changed = true;
                }
                if ua.contains(char::is_whitespace) {
                    u_args.push(format!("({})", ua));
                } else {
                    u_args.push(ua);
                }
            }
            if any_changed {
                return format!("{} {}", head, u_args.join(" "));
            }
        }
    }
    trimmed.to_string()
}

/// Transitive fixed-point delta unfolder (up to 16 hops with cycle detection) so multi-hop
/// local `def`/`abbrev` wrappers cannot hide vacuous preconditions or trivial postconditions.
pub(super) fn unfold_expr_one_level(expr: &str, local_defs: &[LocalDefUnfolding]) -> String {
    let mut cur = expr.trim().to_string();
    for _hop in 0..8 {
        if cur.len() > 2048 {
            break;
        }
        let next = unfold_expr_single_step(&cur, local_defs);
        if next == cur {
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
        r.trim()
            .trim_start_matches('(')
            .trim_start_matches("fun ")
            .trim()
    } else {
        return false;
    };
    let Some((binder_part, body_part)) = rest.split_once(',').or_else(|| rest.split_once("=>"))
    else {
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

pub(super) fn is_syntactically_contradictory_hyp(hyp: &str) -> bool {
    let h = strip_balanced_outer_parens(strip_hypothesis_binder_name(hyp).trim());
    let conjuncts = split_top_level_conjuncts(h);
    if conjuncts.len() > 1 {
        if conjuncts
            .iter()
            .any(|c| is_syntactically_contradictory_hyp(c))
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
            if is_strict && (rt == "0" || lt == rt) {
                return true;
            }
            if !is_strict && lt == "1" && rt == "0" {
                return true;
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
        let mut cfg = crate::shm_cache::load_project_or_env_config(
            config_path_override,
            "TURBO_LEAN_AUDIT_SPEC_CONFIG",
            Some(file),
            &[],
            true,
            Self::parse_config_str,
        )
        .unwrap_or_default();
        if let Some(pol) = policy_override.filter(|s| !s.trim().is_empty()) {
            let preset = Self::from_preset(pol);
            cfg.policy = preset.policy;
            cfg.reject_conjunct_tautologies = preset.reject_conjunct_tautologies;
            cfg.reject_definitional_lowering_tautology =
                preset.reject_definitional_lowering_tautology;
            cfg.reject_identity_stubs = preset.reject_identity_stubs;
            cfg.reject_unused_param_defs = preset.reject_unused_param_defs;
            cfg.reject_size_only_parsers = preset.reject_size_only_parsers;
            for pr in preset.path_rules {
                if let Some(existing) = cfg
                    .path_rules
                    .iter_mut()
                    .find(|r| r.glob_pattern == pr.glob_pattern)
                {
                    for (dst, src) in [
                        (&mut existing.forbid_decl_kinds, pr.forbid_decl_kinds),
                        (&mut existing.allow_decl_names, pr.allow_decl_names),
                        (&mut existing.forbid_namespaces, pr.forbid_namespaces),
                    ] {
                        for item in src {
                            if !dst.contains(&item) {
                                dst.push(item);
                            }
                        }
                    }
                } else {
                    cfg.path_rules.push(pr);
                }
            }
        }
        for (dst, extras) in [
            (&mut cfg.forbid_namespaces, extra_forbid_namespaces),
            (&mut cfg.forbid_decl_kinds, extra_forbid_decl_kinds),
        ] {
            for item in extras.iter().map(|s| s.trim()).filter(|s| !s.is_empty()) {
                if !dst.iter().any(|x| x == item) {
                    dst.push(item.to_string());
                }
            }
        }
        cfg
    }

    pub fn parse_config_str(text: &str) -> Option<Self> {
        use crate::shm_cache::{
            for_each_toml_entry, parse_relaxed_bool, parse_relaxed_toml_string_array,
            unquote_toml_scalar,
        };
        let trimmed = text.trim();
        if trimmed.is_empty() {
            return None;
        }
        if trimmed.starts_with('{') {
            return serde_json::from_str::<Self>(trimmed).ok();
        }
        let (mut cfg, mut in_audit_spec, mut current_rule, mut parsed_any) =
            (Self::default(), false, None::<AuditSpecPathRule>, false);
        for_each_toml_entry(trimmed, |section, key, val| {
            if key.is_empty() {
                if let Some(r) = current_rule.take().filter(|r| !r.glob_pattern.is_empty()) {
                    cfg.path_rules.push(r);
                }
                let sec = section[1..section.len() - 1].trim();
                in_audit_spec = sec == "audit_spec" || sec == "audit-spec";
                if in_audit_spec {
                    parsed_any = true;
                } else if let Some(rest) = sec
                    .strip_prefix("audit_spec.path_rules.")
                    .or_else(|| sec.strip_prefix("audit-spec.path_rules."))
                {
                    parsed_any = true;
                    current_rule = Some(AuditSpecPathRule {
                        glob_pattern: unquote_toml_scalar(rest),
                        forbid_decl_kinds: Vec::new(),
                        allow_decl_names: Vec::new(),
                        forbid_namespaces: Vec::new(),
                    });
                }
                return;
            }
            if let Some(ref mut rule) = current_rule {
                match key {
                    "forbid_decl_kinds" => {
                        rule.forbid_decl_kinds = parse_relaxed_toml_string_array(val)
                    }
                    "allow_decl_names" => {
                        rule.allow_decl_names = parse_relaxed_toml_string_array(val)
                    }
                    "forbid_namespaces" => {
                        rule.forbid_namespaces = parse_relaxed_toml_string_array(val)
                    }
                    _ => {}
                }
            } else if in_audit_spec {
                match key {
                    "policy" => {
                        let preset = Self::from_preset(&unquote_toml_scalar(val));
                        cfg.policy = preset.policy;
                        cfg.reject_conjunct_tautologies = preset.reject_conjunct_tautologies;
                        cfg.reject_definitional_lowering_tautology =
                            preset.reject_definitional_lowering_tautology;
                        cfg.reject_identity_stubs = preset.reject_identity_stubs;
                        cfg.reject_unused_param_defs = preset.reject_unused_param_defs;
                        cfg.reject_size_only_parsers = preset.reject_size_only_parsers;
                        for pr in preset.path_rules {
                            if !cfg
                                .path_rules
                                .iter()
                                .any(|r| r.glob_pattern == pr.glob_pattern)
                            {
                                cfg.path_rules.push(pr);
                            }
                        }
                    }
                    "reject_conjunct_tautologies" => {
                        cfg.reject_conjunct_tautologies =
                            parse_relaxed_bool(val).unwrap_or(cfg.reject_conjunct_tautologies);
                    }
                    "reject_definitional_lowering_tautology" => {
                        cfg.reject_definitional_lowering_tautology = parse_relaxed_bool(val)
                            .unwrap_or(cfg.reject_definitional_lowering_tautology);
                    }
                    "reject_identity_stubs" => {
                        cfg.reject_identity_stubs =
                            parse_relaxed_bool(val).unwrap_or(cfg.reject_identity_stubs);
                    }
                    "reject_unused_param_defs" => {
                        cfg.reject_unused_param_defs =
                            parse_relaxed_bool(val).unwrap_or(cfg.reject_unused_param_defs);
                    }
                    "reject_size_only_parsers" => {
                        cfg.reject_size_only_parsers =
                            parse_relaxed_bool(val).unwrap_or(cfg.reject_size_only_parsers);
                    }
                    "forbid_decl_kinds" => {
                        cfg.forbid_decl_kinds = parse_relaxed_toml_string_array(val)
                    }
                    "forbid_namespaces" => {
                        cfg.forbid_namespaces = parse_relaxed_toml_string_array(val)
                    }
                    _ => {}
                }
            }
        });
        if let Some(r) = current_rule.take().filter(|r| !r.glob_pattern.is_empty()) {
            cfg.path_rules.push(r);
        }
        parsed_any.then_some(cfg)
    }

    pub fn effective_forbidden_for_path(
        &self,
        file: &Path,
    ) -> (Vec<String>, Vec<String>, Vec<String>) {
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
    local_defs: &[LocalDefUnfolding],
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
    for _pass in 0..4 {
        let prev = cur.clone();
        for (var, expr) in &subs {
            let wrapped = if expr.contains(char::is_whitespace) {
                format!("({})", expr)
            } else {
                expr.clone()
            };
            cur = replace_ident_boundary(&cur, var, &wrapped);
        }
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
/// This is a source-shape check, not a kernel proof or a token-occurrence waiver.
pub(super) fn relational_ignored_parameters(
    decl: &ExtractedDecl,
    conjunct: &str,
    local_defs: &[LocalDefUnfolding],
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
    let mut candidates = local_defs
        .iter()
        .filter(|(name, _, _, _)| name == head || name.rsplit('.').next() == Some(head.as_str()));
    let (name, params, body, dependencies) = candidates.next()?;
    if candidates.next().is_some() || lhs.len() != params.len() + 1 {
        return None;
    }
    let binder_type = |arg: &str| {
        let mut matches = decl
            .binders
            .iter()
            .filter(|(names, _)| names.iter().any(|n| n == arg));
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
        if a == b {
            continue;
        }
        if binder_type(a)? != binder_type(b)?
            || replace_ident_boundary(body, param, "__USED__") != *body
            || replace_ident_boundary(dependencies, param, "__USED__") != *dependencies
            || constraints.iter().any(|h| {
                [a, b]
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
    local_defs: &[LocalDefUnfolding],
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
        for (def_name, params, body, dependencies) in local_defs {
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
                referenced.push((
                    def_name.as_str(),
                    params.as_slice(),
                    body.as_str(),
                    dependencies.as_str(),
                ));
                next_frontier.push(body.clone());
            }
        }
        if next_frontier.is_empty() {
            break;
        }
        frontier = next_frontier;
    }

    let mut stub_findings = Vec::new();
    for (def_name, params, body, dependencies) in referenced {
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
        //    reject both underscore-prefixed parameters (`_code`) AND non-underscore parameters
        //    that never occur in `body`, UNLESS the theorem is a 2-call relational hyperproperty
        //    (`f ... v1 ... = f ... v2 ...`) where `f` is invoked on two distinct universally
        //    quantified binder variables `v1 != v2` specifically at that parameter index `p_idx`.
        if policy.reject_unused_param_defs && !params.is_empty() {
            let conclusions = split_top_level_implications(&decl.prop_str);
            let relations: Vec<_> =
                split_top_level_conjuncts(conclusions.last().map(String::as_str).unwrap_or(""))
                    .iter()
                    .filter_map(|c| relational_ignored_parameters(decl, c, local_defs))
                    .collect();
            for (p_idx, p) in params.iter().enumerate() {
                let pt = p.trim();
                let is_unused = !pt.is_empty()
                    && replace_ident_boundary(b_trim, pt, "__USED__") == b_trim
                    && replace_ident_boundary(dependencies, pt, "__USED__") == dependencies;
                if !is_unused
                    || relations
                        .iter()
                        .any(|(name, positions)| name == def_name && positions.contains(&p_idx))
                {
                    continue;
                }
                if pt.starts_with('_') {
                    stub_findings.push(format!(
                        "{}: local def `{}` ignores parameter `{}`",
                        decl.name, def_name, pt
                    ));
                } else {
                    stub_findings.push(format!(
                        "{}: local def `{}` never references parameter `{}` in its body",
                        decl.name, def_name, pt
                    ));
                }
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
    let mut current_ns = String::new();
    for (idx, raw_line) in clean_src.lines().enumerate() {
        let ln = idx + 1;
        let mut line = raw_line.trim();
        if line.is_empty() {
            continue;
        }
        if let Some(ns_rest) = line.strip_prefix("namespace ") {
            let ns = ns_rest.split_whitespace().next().unwrap_or("").trim();
            if !ns.is_empty() {
                current_ns = if current_ns.is_empty() {
                    ns.to_string()
                } else {
                    format!("{}.{}", current_ns, ns)
                };
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
            if end_ns.is_empty() || current_ns == end_ns {
                current_ns.clear();
            } else if let Some(prefix) = current_ns.strip_suffix(&format!(".{}", end_ns)) {
                current_ns = prefix.to_string();
            }
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
    local_defs: &[LocalDefUnfolding],
) -> ((bool, bool, String), String, String) {
    let (res, pos_w, neg_w, _, _) = audit_single_decl_spec_full_with_policy(
        decl,
        local_defs,
        &AuditSpecPolicyConfig::default(),
    );
    (res, pos_w, neg_w)
}

#[allow(dead_code)]
pub(super) fn audit_single_decl_spec_full(
    decl: &ExtractedDecl,
    local_defs: &[LocalDefUnfolding],
) -> ((bool, bool, String), String, String, Vec<String>) {
    let (res, pos_w, neg_w, drop_hyps, _) = audit_single_decl_spec_full_with_policy(
        decl,
        local_defs,
        &AuditSpecPolicyConfig::default(),
    );
    (res, pos_w, neg_w, drop_hyps)
}

pub(super) fn audit_single_decl_spec_full_with_policy(
    decl: &ExtractedDecl,
    local_defs: &[LocalDefUnfolding],
    policy: &AuditSpecPolicyConfig,
) -> (
    (bool, bool, String),
    String,
    String,
    Vec<String>,
    Vec<String>,
) {
    let mut hyp_strings = Vec::new();
    for (_, ty) in &decl.binders {
        if !is_known_binder_value_type(ty) {
            hyp_strings.push(unfold_expr_one_level(ty, local_defs));
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
        conclusion_str =
            substitute_equational_hypotheses(&conclusion_str, &hyp_strings, local_defs);
    }

    let mut is_vacuous = hyp_strings
        .iter()
        .any(|h| is_syntactically_contradictory_hyp(h));

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

    let mut pos_witness = "precondition_satisfiable(unconstrained_or_symbolic)".to_string();
    let mut droppable_hyps = Vec::new();
    if !is_vacuous && !hyp_strings.is_empty() {
        if let Some((rep, _, _)) = eval_extracted_decl_in_memory(&unfolded_decl, 256) {
            if rep.vacuous_precondition_warning || rep.satisfied_preconditions == 0 {
                is_vacuous = true;
            } else {
                pos_witness = format!(
                    "satisfied_states={}/{}",
                    rep.satisfied_preconditions, rep.n_states
                );
                // Hypothesis-drop mutation probe: drop each non-value binder hypothesis one by one
                // and check whether the postcondition still holds across all 256 states and has no
                // variable overlap with the conclusion (indicating a redundant hypothesis).
                for (b_idx, (_, ty)) in unfolded_decl.binders.iter().enumerate() {
                    if !is_known_binder_value_type(ty) {
                        let mut mutated = unfolded_decl.clone();
                        mutated.binders.remove(b_idx);
                        if let Some((m_rep, _, _)) = eval_extracted_decl_in_memory(&mutated, 256) {
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
                                    let _ =
                                        collect_expr_bound_vars(&h_ast, &val_params, &mut hyp_vars);
                                }
                                if let Ok(c_ast) = parse_lean_expr_str(&conclusion_str) {
                                    let _ = collect_expr_bound_vars(
                                        &c_ast,
                                        &val_params,
                                        &mut concl_vars,
                                    );
                                }
                                let disjoint =
                                    !hyp_vars.is_empty() && hyp_vars.is_disjoint(&concl_vars);
                                if disjoint
                                    || m_rep.satisfied_preconditions > rep.satisfied_preconditions
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

    let concl_imp_segments = split_top_level_implications(&conclusion_str);
    let inner_concl = concl_imp_segments
        .last()
        .map(|s| s.trim())
        .unwrap_or(conclusion_str.as_str());
    let concl_conjuncts = split_top_level_conjuncts(inner_concl);
    let raw_concl_imp_segments = split_top_level_implications(&decl.prop_str);
    let raw_inner_concl = raw_concl_imp_segments
        .last()
        .map(|s| s.trim())
        .unwrap_or(decl.prop_str.as_str());
    let raw_concl_conjuncts = split_top_level_conjuncts(raw_inner_concl);
    let relational = |c: &str| relational_ignored_parameters(decl, c, local_defs).is_some();
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

    let has_pos_witness = !is_vacuous;
    let has_neg_witness = !is_trivial_conclusion;
    let neg_witness = if has_neg_witness {
        format!("postcondition_discriminates({})", conclusion_str)
    } else if is_whole_trivial {
        "none(tautological_postcondition)".to_string()
    } else if !stub_findings.is_empty() {
        format!("none(referenced_stub_def: {})", stub_findings.join("; "))
    } else if has_conjunct_tautology {
        format!("none(conjunct_tautology_in: {})", conclusion_str)
    } else {
        "none(tautological_postcondition)".to_string()
    };
    let gate_ok = unsafe {
        crate::cluster::c_abi::turbo_spec_audit_witness_gate(
            u8::from(has_pos_witness),
            u8::from(has_neg_witness),
        ) != 0
    };
    let is_tight = gate_ok && !is_vacuous && !is_trivial_conclusion;
    let reason = if is_vacuous {
        "vacuous_precondition".to_string()
    } else if !stub_findings.is_empty() {
        "stubbed_definition_in_spec".to_string()
    } else if has_conjunct_tautology {
        "conjunct_tautological_postcondition".to_string()
    } else if is_trivial_conclusion {
        "trivial_tautological_postcondition".to_string()
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
    // Keep lexical context even for filtered declarations in large sources.
    extract_all_lean_theorems(src, decl_filter)
}

/// Schema version for the Blake3 content-addressed `audit-spec` per-file JSON cache.
pub const AUDIT_SPEC_CACHE_SCHEMA_VERSION: u32 = 13;

static AUDIT_SPEC_CACHE_TMP_SEQ: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(1);

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

pub(super) fn collect_external_local_def_lean_paths(src_path: &Path) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    let Some(parent) = src_path.parent() else {
        return paths;
    };
    for p in crate::lake_build::collect_lean_files(parent) {
        if p != *src_path {
            paths.push(p);
        }
    }
    if let Some(grandparent) = parent.parent() {
        if let Ok(entries) = fs::read_dir(grandparent) {
            for p in entries
                .flatten()
                .map(|e| e.path())
                .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("lean"))
            {
                if p != *src_path && !paths.contains(&p) {
                    paths.push(p);
                }
            }
        }
    }
    paths.sort();
    paths
}

pub(super) fn compute_audit_spec_cache_key_with_policy(
    decl_filter: Option<&str>,
    file_bytes: &[u8],
    policy: &AuditSpecPolicyConfig,
    forbid_kinds: &[String],
    allow_names: &[String],
    forbid_namespaces: &[String],
    local_defs_digest: &[u8; 32],
) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-lean-audit-spec-cache:");
    hasher.update(&AUDIT_SPEC_CACHE_SCHEMA_VERSION.to_le_bytes());
    hasher.update(b":");
    let df = decl_filter.unwrap_or("");
    hasher.update(&(df.len() as u64).to_le_bytes());
    hasher.update(df.as_bytes());
    hasher.update(b":");
    if let Ok(pol_json) =
        serde_json::to_vec(&(policy, forbid_kinds, allow_names, forbid_namespaces))
    {
        hasher.update(&(pol_json.len() as u64).to_le_bytes());
        hasher.update(&pol_json);
        hasher.update(b":");
    }
    hasher.update(local_defs_digest);
    hasher.update(b":");
    hasher.update(&(file_bytes.len() as u64).to_le_bytes());
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
    let t0 = Instant::now();
    let (eff_forbid_kinds, eff_allow_names, eff_forbid_namespaces) =
        policy.effective_forbidden_for_path(file);
    let mut cache_target_path: Option<PathBuf> = None;
    let mut preloaded_file_src: Option<String> = None;
    let mut preloaded_external_local_defs: Option<Vec<LocalDefUnfolding>> = None;
    if inline_src.is_none() && file.is_file() && !file.with_extension("").is_dir() {
        if let Ok(file_bytes) = fs::read(file) {
            if let Ok(file_src) = String::from_utf8(file_bytes.clone()) {
                let mut local_defs = extract_local_def_unfoldings(&strip_audit_comments(&file_src));
                for p in collect_external_local_def_lean_paths(file) {
                    if let Ok(sib_src) = fs::read_to_string(&p) {
                        local_defs.extend(extract_local_def_unfoldings(&strip_audit_comments(
                            &sib_src,
                        )));
                    }
                }
                if let Some(cache_dir) = resolve_audit_spec_cache_dir() {
                    let mut ld_hasher = blake3::Hasher::new();
                    for (name, params, body, type_deps) in &local_defs {
                        ld_hasher.update(&(name.len() as u64).to_le_bytes());
                        ld_hasher.update(name.as_bytes());
                        ld_hasher.update(&(params.len() as u64).to_le_bytes());
                        for p in params {
                            ld_hasher.update(&(p.len() as u64).to_le_bytes());
                            ld_hasher.update(p.as_bytes());
                        }
                        ld_hasher.update(&(body.len() as u64).to_le_bytes());
                        ld_hasher.update(body.as_bytes());
                        ld_hasher.update(&(type_deps.len() as u64).to_le_bytes());
                        ld_hasher.update(type_deps.as_bytes());
                    }
                    let ld_digest = *ld_hasher.finalize().as_bytes();
                    let hex_hash = compute_audit_spec_cache_key_with_policy(
                        decl_filter,
                        &file_bytes,
                        policy,
                        &eff_forbid_kinds,
                        &eff_allow_names,
                        &eff_forbid_namespaces,
                        &ld_digest,
                    );
                    let cache_path = cache_dir.join(format!("{}.json", hex_hash));
                    if let Ok(cached_bytes) = fs::read(&cache_path) {
                        if let Ok(mut cached_val) =
                            serde_json::from_slice::<serde_json::Value>(&cached_bytes)
                        {
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
                    cache_target_path = Some(cache_path);
                }
                preloaded_file_src = Some(file_src);
                preloaded_external_local_defs = Some(local_defs);
            }
        }
    }

    let sources: Vec<(PathBuf, String)> = if let Some(s) = inline_src {
        vec![(file.to_path_buf(), s.to_string())]
    } else if file.is_dir() {
        let v: Vec<(PathBuf, String)> = crate::lake_build::collect_lean_files(file)
            .into_iter()
            .filter_map(|p| fs::read_to_string(&p).ok().map(|s| (p, s)))
            .collect();
        if v.is_empty() {
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
        let mut v: Vec<(PathBuf, String)> = match preloaded_file_src
            .or_else(|| fs::read_to_string(file).ok())
        {
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
        let sub_dir = file.with_extension("");
        if sub_dir.is_dir() {
            v.extend(
                crate::lake_build::collect_lean_files(&sub_dir)
                    .into_iter()
                    .filter_map(|p| fs::read_to_string(&p).ok().map(|s| (p, s))),
            );
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
    let mut forbidden_scope_decls = Vec::new();
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
        let clean_src = strip_audit_comments(src);
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
        let local_defs = if let Some(preloaded) = preloaded_external_local_defs.take() {
            preloaded
        } else {
            let mut defs = extract_local_def_unfoldings(&clean_src);
            if inline_src.is_none() && src_path.is_file() {
                for p in collect_external_local_def_lean_paths(src_path) {
                    if let Ok(sib_src) = fs::read_to_string(&p) {
                        defs.extend(extract_local_def_unfoldings(&strip_audit_comments(
                            &sib_src,
                        )));
                    }
                }
            }
            defs
        };

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
            spec_details.push(serde_json::json!({
                "decl": d.name,
                "vacuous": is_vacuous,
                "trivial": is_trivial,
                "tight": is_tight,
                "assessment": reason,
                "pos_witness": pos_witness,
                "neg_witness": neg_witness,
                "droppable_hypotheses": drop_hyps,
                "stub_defs": decl_stubs,
            }));
        }
    }

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
    if total_specs_audited == 0 {
        warnings.push(format!(
            "no_specs_found: 0 theorem/lemma specifications recognized in {}",
            file.display()
        ));
    }
    let tier1_clean = vacuous_specs == 0
        && trivial_specs == 0
        && shadowed_constants.is_empty()
        && forbidden_scope_decls.is_empty()
        && stub_defs.is_empty();
    let verdict = if total_specs_audited == 0 {
        "no_specs_found"
    } else {
        "specs_audited"
    };
    let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
    let report = serde_json::json!({
        "status": "ok",
        "ok": tier1_clean,
        "verdict": verdict,
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
    if files.len() == 1 {
        return audit_spec_file_or_source_with_policy(&files[0], None, decl_filter, policy);
    }
    let t0 = Instant::now();
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .min(files.len().max(1));
    let next_idx = std::sync::atomic::AtomicUsize::new(0);
    let per_file_reports: Vec<serde_json::Value> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..workers)
            .map(|_| {
                let next_ref = &next_idx;
                s.spawn(move || {
                    let mut local = Vec::new();
                    loop {
                        let i = next_ref.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if i >= files.len() {
                            break;
                        }
                        local.push((
                            i,
                            audit_spec_file_or_source_with_policy(
                                &files[i],
                                None,
                                decl_filter,
                                policy,
                            ),
                        ));
                    }
                    local
                })
            })
            .collect();
        let mut indexed: Vec<(usize, serde_json::Value)> = handles
            .into_iter()
            .flat_map(|h| h.join().unwrap_or_default())
            .collect();
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
            || rep["ok"].as_bool() == Some(false) && rep["verdict"].as_str() == Some("error")
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

    let tier1_clean = !any_report_error
        && vacuous_specs == 0
        && trivial_specs == 0
        && shadowed_constants.is_empty()
        && forbidden_scope_decls.is_empty()
        && stub_defs.is_empty();
    let all_cache_hit = !per_file_reports.is_empty() && cache_hits == per_file_reports.len();
    let batch_verdict = if any_report_error {
        "error"
    } else if total_specs_audited == 0 {
        "no_specs_found"
    } else {
        "specs_audited"
    };
    if !any_report_error && total_specs_audited == 0 && warnings.is_empty() {
        warnings.push(serde_json::json!(format!(
            "no_specs_found: 0 theorem/lemma specifications recognized in {}",
            file_labels.join(", ")
        )));
    }
    let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
    let mut out = serde_json::json!({
        "status": if any_report_error { "error" } else { "ok" },
        "ok": tier1_clean,
        "verdict": batch_verdict,
        "policy": policy.policy,
        "file": file_labels.join(", "),
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
pub fn run_audit_spec_command(
    files: &[PathBuf],
    decl_filter: Option<&str>,
    json_mode: bool,
) -> Result<()> {
    run_audit_spec_command_with_options(files, decl_filter, json_mode, None, None, &[], &[], false)
}

pub fn apply_require_nonempty_to_audit_report(
    report: &mut serde_json::Value,
    require_nonempty: bool,
) {
    if !require_nonempty {
        return;
    }
    if let Some(reps) = report
        .get_mut("file_reports")
        .and_then(|v| v.as_array_mut())
    {
        for r in reps {
            if r.get("total_specs_audited").and_then(|v| v.as_u64()) == Some(0) {
                if let Some(ro) = r.as_object_mut() {
                    ro.insert("ok".to_string(), serde_json::json!(false));
                }
            }
        }
    }
    let zero_total = report.get("total_specs_audited").and_then(|v| v.as_u64()) == Some(0);
    let any_sub_failed = report
        .get("file_reports")
        .and_then(|v| v.as_array())
        .is_some_and(|arr| {
            arr.iter()
                .any(|r| r.get("ok").and_then(|v| v.as_bool()) == Some(false))
        });
    if zero_total || any_sub_failed {
        if let Some(obj) = report.as_object_mut() {
            obj.insert("ok".to_string(), serde_json::json!(false));
            if zero_total && obj.get("verdict").and_then(|v| v.as_str()) != Some("error") {
                obj.insert("verdict".to_string(), serde_json::json!("no_specs_found"));
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub fn run_audit_spec_command_with_options(
    files: &[PathBuf],
    decl_filter: Option<&str>,
    json_mode: bool,
    policy_override: Option<&str>,
    config_override: Option<&Path>,
    forbid_namespaces: &[String],
    forbid_decl_kinds: &[String],
    require_nonempty: bool,
) -> Result<()> {
    anyhow::ensure!(!files.is_empty(), "No files provided to audit-spec");
    for f in files {
        anyhow::ensure!(
            f.exists(),
            "Failed to read {}: path does not exist",
            f.display()
        );
    }
    let first_file = &files[0];
    let policy = AuditSpecPolicyConfig::load_for_target(
        first_file,
        policy_override,
        config_override,
        forbid_namespaces,
        forbid_decl_kinds,
    );
    let mut report = audit_spec_files_with_policy(files, decl_filter, &policy);
    apply_require_nonempty_to_audit_report(&mut report, require_nonempty);
    let nonempty_failed = require_nonempty && report["ok"].as_bool() == Some(false);
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
        if nonempty_failed {
            std::process::exit(1);
        }
    } else {
        println!(
            "[turbo-lean] AUDIT-SPEC ({}) on {}: ok={} verdict={} audited={} tight={} vacuous={} trivial={} shadowed={} forbidden_scope={} stubs={} warnings={} ({:.3} ms)",
            report["policy"].as_str().unwrap_or("default"),
            report["file"].as_str().unwrap_or_default(),
            report["ok"],
            report["verdict"].as_str().unwrap_or("specs_audited"),
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
        anyhow::ensure!(
            report["ok"].as_bool() == Some(true),
            "Specification audit failed on {} (verdict={}, audited={}, vacuous={}, trivial={}, shadowed={}, forbidden_scope={}, stubs={})",
            report["file"].as_str().unwrap_or_default(),
            report["verdict"].as_str().unwrap_or("specs_audited"),
            report["total_specs_audited"],
            report["vacuous_specs"],
            report["trivial_specs"],
            report["shadowed_constants"].as_array().map_or(0, Vec::len),
            report["forbidden_scope_decls"].as_array().map_or(0, Vec::len),
            report["stub_defs"].as_array().map_or(0, Vec::len),
        );
    }
    Ok(())
}

#[cfg(test)]
mod lexer_tests {
    use super::*;

    #[test]
    fn cert_checker_diagnostic_is_not_a_theorem() {
        let src = include_str!("../../../lean/LeanNative/Proofs/CertChecker.lean");
        assert!(extract_all_lean_theorems(src, None).is_empty());
    }

    #[test]
    fn theorem_lexer_skips_strings_and_nested_comments() {
        let src = r#"
def quote : Char := '"'
def message (x : String) := s!"claims a theorem '{x}' is missing"
def escaped := "quote: \" theorem fake : False := by contradiction"
-- theorem lineComment : False := by contradiction
/- theorem blockComment : False := by
  /- lemma nestedComment : False := by contradiction -/
  contradiction -/
theorem actual (x : Nat) : x = x := by rfl
lemma actualToo : True := by trivial
"#;
        let decls = extract_all_lean_theorems(src, None);
        assert_eq!(
            decls.iter().map(|d| d.name.as_str()).collect::<Vec<_>>(),
            ["actual", "actualToo"]
        );
        assert!(extract_all_lean_theorems(src, Some("fake")).is_empty());
        let large_src = format!("{}{}", " ".repeat(9000), src);
        assert!(extract_decls_fast(&large_src, Some("fake")).is_empty());
        assert_eq!(
            extract_decls_fast(&large_src, Some("actual"))[0].name,
            "actual"
        );
    }

    fn assert_only_actual(prefix: &str) {
        let src = format!("{prefix}\ntheorem actual : True := by trivial\n");
        let clean = strip_audit_comments(&src);
        assert_eq!(clean.len(), src.len());
        assert_eq!(clean.matches('\n').count(), src.matches('\n').count());
        for text in [&src, &clean] {
            let decls = extract_all_lean_theorems(text, None);
            assert_eq!(
                decls.iter().map(|d| d.name.as_str()).collect::<Vec<_>>(),
                ["actual"],
                "source: {text}"
            );
            assert_eq!(decls[0].prop_str, "True");
        }
        let large = format!("{}{src}", " ".repeat(9000));
        assert!(extract_decls_fast(&large, Some("fake")).is_empty());
        assert_eq!(extract_decls_fast(&large, Some("actual"))[0].name, "actual");
    }

    #[test]
    fn raw_embedded_quote_does_not_create_a_theorem() {
        assert_only_actual(
            r##"def message := r#"quoted " theorem fake : False := by contradiction"#"##,
        );
    }

    #[test]
    fn raw_trailing_backslash_does_not_hide_a_theorem() {
        assert_only_actual(r##"def message := r#"text\"#"##);
    }

    #[test]
    fn raw_two_hashes_require_the_full_closing_delimiter() {
        assert_only_actual(
            r###"def message := r##"text"# "theorem fake : False := by contradiction"##"###,
        );
    }

    #[test]
    fn raw_strings_support_any_hash_count_and_literal_backslashes() {
        for count in [0, 1, 2, 3, 16, 64] {
            let hashes = "#".repeat(count);
            assert_only_actual(&format!(
                "def message := r{hashes}\"theorem fake : False := by contradiction\\\"{hashes}"
            ));
        }
    }

    #[test]
    fn raw_comment_markers_are_preserved_by_audit_stripping() {
        for prefix in [
            r##"def message := r#"quoted " -- theorem fake : False := by contradiction"#"##,
            r##"def message := r#"quoted " /- theorem fake : False := by contradiction"#"##,
            r###"def message := r##"quoted "# /- -- theorem fake : False := by contradiction"##"###,
        ] {
            assert_eq!(strip_audit_comments(prefix), prefix);
            assert_only_actual(prefix);
        }
    }

    #[test]
    fn audit_lexer_handles_regular_strings_and_character_literals() {
        assert_only_actual(
            r##"
def quote : Char := '"'
def apostrophe : Char := '\''
def slash : Char := '\\'
def unicode : Char := 'λ'
def message := "escaped \" theorem fake : False := by contradiction -- /-"
def diagnostic (x : String) := s!"theorem '{x}' is missing"
"##,
        );
    }

    #[test]
    fn audit_lexer_skips_line_nested_block_and_doc_comments() {
        assert_only_actual(
            r##"
-- r#" '"' theorem fake : False := by contradiction
/- " r#" theorem fake : False := by contradiction
   /- lemma fake : False := by contradiction -/ -/
/-- theorem fake : False := by contradiction /- nested -/ -/
/-! lemma fake : False := by contradiction -/
"##,
        );
        let src = "-- λ theorem fake\n/- α\n /- β -/ -/";
        assert_eq!(
            strip_audit_comments(src),
            src.chars()
                .map(|c| {
                    if c == '\n' {
                        "\n".to_string()
                    } else {
                        " ".repeat(c.len_utf8())
                    }
                })
                .collect::<String>()
        );
    }

    #[test]
    fn theorem_literals_do_not_change_binder_or_statement_boundaries() {
        let src = r##"
theorem actual (x : String := r#") theorem fake : False :="#) :
  r#":= theorem fake : False :="# = r#":= theorem fake : False :="# := by rfl
theorem actualToo : True := by trivial
"##;
        let decls = extract_all_lean_theorems(src, None);
        assert_eq!(
            decls.iter().map(|d| d.name.as_str()).collect::<Vec<_>>(),
            ["actual", "actualToo"]
        );
        assert_eq!(
            decls[0].prop_str,
            r##"r#":= theorem fake : False :="# = r#":= theorem fake : False :="#"##
        );
    }

    #[test]
    fn unterminated_literals_and_comments_do_not_expose_theorems() {
        for src in [
            "\"theorem fake : False := by contradiction",
            "r###\"theorem fake : False := by contradiction\"##",
            "/- theorem fake : False := by contradiction /- nested -/",
        ] {
            assert!(extract_all_lean_theorems(src, None).is_empty());
        }
    }

    #[test]
    fn namespace_qualified_and_ambiguous_target_selection_fail_closed() {
        let src = "\
theorem a : False := by sorry
namespace N
  section S
    theorem a : True := by trivial
  end S
  namespace M
    theorem b : True := by trivial
  end M
end N
";
        let na = extract_all_lean_theorems(src, Some("N.a"));
        assert_eq!(na.len(), 1);
        assert_eq!(na[0].qualified_name, "N.a");
        assert_eq!(na[0].prop_str, "True");

        let root_a = extract_all_lean_theorems(src, Some("_root_.a"));
        assert_eq!(root_a.len(), 1);
        assert_eq!(root_a[0].qualified_name, "a");
        assert_eq!(root_a[0].prop_str, "False");

        assert!(extract_all_lean_theorems(src, Some("a")).is_empty());
        assert!(extract_all_lean_theorems(src, Some("M.b")).is_empty());

        let nmb = extract_all_lean_theorems(src, Some("N.M.b"));
        assert_eq!(nmb.len(), 1);
        assert_eq!(nmb[0].qualified_name, "N.M.b");
        assert_eq!(extract_all_lean_theorems(src, Some("b")).len(), 1);
    }
}
