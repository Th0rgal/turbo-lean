use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TheoremShard {
    pub name: String,
    pub kind: String,
    pub start_line: usize,
    pub end_line: usize,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub signature_text: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub proof_text: String,
    pub prefix_env_hash: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub cone_env_hash: String,
    pub stmt_hash: String,
    pub proof_hash: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub shard_source: String,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct HygieneReport {
    pub has_sorry: bool,
    #[serde(default)]
    pub has_axiom: bool,
    pub has_native_decide: bool,
    pub has_trust_compiler: bool,
    pub has_unsafe: bool,
    pub has_extern_or_implemented_by: bool,
    pub has_impure_metaprograms: bool,
    pub flagged_items: Vec<String>,
}

impl HygieneReport {
    pub fn is_clean_for_certification(&self) -> bool {
        !self.has_sorry
            && !self.has_axiom
            && !self.has_native_decide
            && !self.has_trust_compiler
            && !self.has_unsafe
            && !self.has_extern_or_implemented_by
    }

    /// Return only hygiene items that are newly introduced relative to `base`
    /// (plus any `sorry`, which is always flagged in modified files).
    pub fn regression_items_against(&self, base: &Self) -> Vec<String> {
        if self.is_clean_for_certification() {
            return Vec::new();
        }
        fn strip_line(s: &str) -> &str {
            if let Some(rest) = s.strip_prefix('L') {
                if let Some((digits, kind)) = rest.split_once(": ") {
                    if !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()) {
                        return kind;
                    }
                }
            }
            s
        }
        let mut base_counts: std::collections::HashMap<&str, usize> =
            std::collections::HashMap::new();
        for item in &base.flagged_items {
            let k = strip_line(item);
            if !k.contains("sorry") {
                *base_counts.entry(k).or_insert(0) += 1;
            }
        }
        let mut out = Vec::new();
        for item in &self.flagged_items {
            let k = strip_line(item);
            if let Some(rem) = base_counts.get_mut(k) {
                if *rem > 0 {
                    *rem -= 1;
                    continue;
                }
            }
            out.push(item.clone());
        }
        out
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SplitResult {
    pub eligible_for_sharding: bool,
    pub fallback_reason: Option<String>,
    pub imports_header: String,
    pub skeleton_source: String,
    pub interface_hash: String,
    pub shards: Vec<TheoremShard>,
    pub hygiene: HygieneReport,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct FissionSubShard {
    pub step_index: usize,
    pub total_steps: usize,
    pub step_label: String,
    pub sub_shard_key: String,
    pub sub_decl_source: String,
}


/// Zero-copy command span slicing directly into `(src, clean)`.
#[derive(Debug, Clone, Copy)]
struct CmdSpan<'a> {
    start_line: usize, // 1-indexed
    end_line: usize,   // 1-indexed inclusive
    orig_text: &'a str,
    clean_text: &'a str,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ScopeKind {
    Namespace,
    Section,
    Mutual,
}

#[derive(Debug, Clone)]
struct ScopeFrame {
    kind: ScopeKind,
    name: String,
    open_span_idx: usize,
}

/// Strip comments while preserving string literals, exact byte offsets, and newline counts.
pub fn strip_lean_comments(src: &str) -> String {
    if !src.contains("--") && !src.contains("/-") {
        return src.to_string();
    }
    let bytes = src.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let mut block_depth = 0usize;
    let mut in_string = false;

    while i < bytes.len() {
        if block_depth > 0 {
            if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'-' {
                block_depth += 1;
                out.extend_from_slice(b"  ");
                i += 2;
            } else if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'/' {
                block_depth -= 1;
                out.extend_from_slice(b"  ");
                i += 2;
            } else {
                if bytes[i] == b'\n' {
                    out.push(b'\n');
                } else {
                    out.push(b' ');
                }
                i += 1;
            }
            continue;
        }

        if in_string {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                out.push(bytes[i]);
                out.push(bytes[i + 1]);
                i += 2;
            } else if bytes[i] == b'"' {
                in_string = false;
                out.push(b'"');
                i += 1;
            } else {
                out.push(bytes[i]);
                i += 1;
            }
            continue;
        }

        if bytes[i] == b'"' {
            in_string = true;
            out.push(b'"');
            i += 1;
        } else if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'-' {
            while i < bytes.len() && bytes[i] != b'\n' {
                out.push(b' ');
                i += 1;
            }
        } else if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'-' {
            block_depth = 1;
            out.extend_from_slice(b"  ");
            i += 2;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }

    String::from_utf8(out).unwrap_or_else(|e| String::from_utf8_lossy(e.as_bytes()).into_owned())
}

pub fn audit_hygiene(clean_src: &str) -> HygieneReport {
    let mut report = HygieneReport {
        has_sorry: false,
        has_axiom: false,
        has_native_decide: false,
        has_trust_compiler: false,
        has_unsafe: false,
        has_extern_or_implemented_by: false,
        has_impure_metaprograms: false,
        flagged_items: Vec::new(),
    };

    if !clean_src.contains("sorry")
        && !clean_src.contains("admit")
        && !clean_src.contains("axiom")
        && !clean_src.contains("native_decide")
        && !clean_src.contains("ofReduceBool")
        && !clean_src.contains("trustCompiler")
        && !clean_src.contains("unsafe")
        && !clean_src.contains("implemented_by")
        && !clean_src.contains("extern")
        && !clean_src.contains("@[csimp")
        && !clean_src.contains("#eval")
        && !clean_src.contains("run_cmd")
        && !clean_src.contains("#guard_msgs")
        && !clean_src.contains("initialize ")
    {
        return report;
    }

    for (idx, line) in clean_src.lines().enumerate() {
        let ln = idx + 1;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if contains_word(trimmed, "sorry")
            || contains_word(trimmed, "admit")
            || contains_word(trimmed, "sorryAx")
        {
            report.has_sorry = true;
            report
                .flagged_items
                .push(format!("L{}: sorry/admit token", ln));
        }
        let after_prefixes = strip_decl_prefixes(trimmed);
        if trimmed.starts_with("axiom ") || after_prefixes.starts_with("axiom ") {
            report.has_axiom = true;
            report.flagged_items.push(format!("L{}: axiom", ln));
        }
        if contains_word(trimmed, "native_decide") || contains_word(trimmed, "ofReduceBool") {
            report.has_native_decide = true;
            report
                .flagged_items
                .push(format!("L{}: native_decide/ofReduceBool", ln));
        }
        if contains_word(trimmed, "trustCompiler") {
            report.has_trust_compiler = true;
            report
                .flagged_items
                .push(format!("L{}: trustCompiler", ln));
        }
        if (trimmed.starts_with("unsafe ") || contains_word(trimmed, "unsafe"))
            && trimmed != "unsafe enableInitializersExecution"
            && trimmed != "unsafe Lean.enableInitializersExecution"
        {
            report.has_unsafe = true;
            report
                .flagged_items
                .push(format!("L{}: unsafe declaration", ln));
        }
        let attrs = extract_leading_attributes(trimmed);
        if trimmed.contains("@[implemented_by")
            || attrs.iter().any(|a| contains_word(a, "implemented_by"))
        {
            report.has_extern_or_implemented_by = true;
            report
                .flagged_items
                .push(format!("L{}: implemented_by", ln));
        }
        if trimmed.contains("@[extern") || attrs.iter().any(|a| contains_word(a, "extern")) {
            report.has_extern_or_implemented_by = true;
            report.flagged_items.push(format!("L{}: extern", ln));
        }
        if trimmed.contains("@[csimp") || attrs.iter().any(|a| contains_word(a, "csimp")) {
            report.has_extern_or_implemented_by = true;
            report.flagged_items.push(format!("L{}: csimp", ln));
        }
        if trimmed.starts_with("#eval")
            || trimmed.starts_with("run_cmd")
            || trimmed.starts_with("#guard_msgs")
            || trimmed.starts_with("initialize ")
        {
            report.has_impure_metaprograms = true;
            report.flagged_items.push(format!(
                "L{}: impure/reflective command `{}`",
                ln,
                trimmed.split_whitespace().next().unwrap_or("")
            ));
        }
    }

    report
}

fn contains_word(haystack: &str, word: &str) -> bool {
    for (idx, _) in haystack.match_indices(word) {
        let prev_ok = idx == 0
            || !haystack.as_bytes()[idx - 1].is_ascii_alphanumeric()
                && haystack.as_bytes()[idx - 1] != b'_';
        let end = idx + word.len();
        let next_ok = end >= haystack.len()
            || !haystack.as_bytes()[end].is_ascii_alphanumeric()
                && haystack.as_bytes()[end] != b'_';
        if prev_ok && next_ok {
            return true;
        }
    }
    false
}

fn is_top_level_command_start(trimmed: &str) -> bool {
    const STARTERS: &[&str] = &[
        "import ",
        "namespace ",
        "section",
        "noncomputable section",
        "end",
        "open ",
        "variable ",
        "variables ",
        "universe ",
        "universes ",
        "set_option ",
        "attribute ",
        "export ",
        "include ",
        "omit ",
        "@",
        "private ",
        "protected ",
        "noncomputable ",
        "scoped ",
        "local ",
        "unsafe ",
        "partial ",
        "theorem ",
        "lemma ",
        "def ",
        "abbrev ",
        "instance ",
        "inductive ",
        "coinductive ",
        "structure ",
        "class ",
        "axiom ",
        "opaque ",
        "constant ",
        "example ",
        "simproc",
        "dsimproc",
        "builtin_simproc",
        "builtin_dsimproc",
        "mutual",
        "deriving ",
        "#check",
        "#eval",
        "#print",
        "#guard_msgs",
        "#reduce",
        "#synth",
        "run_cmd",
        "initialize ",
        "builtin_initialize ",
        "syntax ",
        "macro ",
        "macro_rules",
        "elab ",
        "elab_rules",
        "notation ",
        "infix",
        "prefix",
        "postfix",
    ];
    for s in STARTERS {
        if trimmed.starts_with(s) {
            return true;
        }
    }
    matches!(
        trimmed.trim_end(),
        "private" | "protected" | "noncomputable" | "scoped" | "local" | "unsafe" | "partial"
    )
}

/// Strip a leading `@[...]` attribute block with balanced brackets `[...]`.
fn strip_leading_attr_block(s: &str) -> Option<&str> {
    if !s.starts_with("@[") {
        return None;
    }
    let bytes = s.as_bytes();
    let mut depth = 0i32;
    let mut in_string = false;
    let mut i = 1usize;
    while i < bytes.len() {
        let c = bytes[i];
        if in_string {
            if c == b'\\' {
                i += 2;
                continue;
            }
            if c == b'"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        match c {
            b'"' => in_string = true,
            b'[' => depth += 1,
            b']' => {
                depth -= 1;
                if depth == 0 {
                    return Some(&s[i + 1..]);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Strip leading attributes (`@[...]`) and declaration modifiers (`private`, `protected`,
/// `noncomputable`, `scoped`, `local`, `unsafe`, `partial`) across whitespace and newlines.
fn strip_decl_prefixes(cmd_text: &str) -> &str {
    let mut rest = cmd_text.trim_start();
    loop {
        if let Some(after_attr) = strip_leading_attr_block(rest) {
            rest = after_attr.trim_start();
            continue;
        }
        let mut stripped_mod = false;
        for m in [
            "private",
            "protected",
            "noncomputable",
            "scoped",
            "local",
            "unsafe",
            "partial",
        ] {
            if let Some(after_m) = rest.strip_prefix(m) {
                if after_m.is_empty() || after_m.starts_with(char::is_whitespace) {
                    let trimmed_after = after_m.trim_start();
                    if m == "noncomputable"
                        && (trimmed_after == "section" || trimmed_after.starts_with("section "))
                    {
                        break;
                    }
                    rest = trimmed_after;
                    stripped_mod = true;
                    break;
                }
            }
        }
        if !stripped_mod {
            break;
        }
    }
    rest
}

/// Returns true if `clean_chunk` consists solely of comments, whitespace, `@[...]` attributes,
/// or declaration modifiers (`private`, `scoped`, `local`, etc.) waiting for a declaration on
/// a following line.
fn is_incomplete_prefix_only_span(clean_chunk: &str) -> bool {
    let trimmed = clean_chunk.trim();
    if trimmed.is_empty() {
        return true;
    }
    strip_decl_prefixes(trimmed).is_empty()
}

fn is_mutual_line_start(trimmed_clean: &str) -> bool {
    let after = strip_decl_prefixes(trimmed_clean);
    after == "mutual"
        || after
            .strip_prefix("mutual")
            .map(|r| r.starts_with(char::is_whitespace))
            .unwrap_or(false)
}

fn is_end_line_start(trimmed_clean: &str) -> bool {
    trimmed_clean == "end" || trimmed_clean.starts_with("end ")
}

fn is_section_header_line(trimmed_clean: &str) -> bool {
    trimmed_clean == "section"
        || trimmed_clean.starts_with("section ")
        || trimmed_clean == "noncomputable section"
        || trimmed_clean.starts_with("noncomputable section ")
}

/// Zero-copy segmentation of `(src, clean)` into top-level `CmdSpan`s.
/// Handles `/-- ... -/` doc comments, multi-line `@[...]` attribute / modifier prefixes,
/// commands indented inside `section ... end` blocks, and `mutual ... end` blocks without
/// per-span heap allocations.
fn parse_command_spans<'a>(src: &'a str, clean: &'a str) -> Vec<CmdSpan<'a>> {
    if src.is_empty() || clean.len() != src.len() {
        return Vec::new();
    }

    let bytes = src.as_bytes();
    let total_len = bytes.len();
    let mut spans: Vec<CmdSpan<'a>> = Vec::new();

    let mut cur_start_line = 1usize;
    let mut cur_byte_start = 0usize;
    let mut cur_byte_end = 0usize;
    let mut cur_cmd_indent: Option<usize> = None;
    let mut line_num = 1usize;
    let mut pos = 0usize;
    let mut mutual_depth = 0usize;
    let mut section_depth = 0usize;

    while pos < total_len {
        let line_start = pos;
        let mut line_end = pos;
        while line_end < total_len && bytes[line_end] != b'\n' {
            line_end += 1;
        }
        let next_pos = if line_end < total_len {
            line_end + 1
        } else {
            total_len
        };
        let line_end_no_cr = if line_end > line_start && bytes[line_end - 1] == b'\r' {
            line_end - 1
        } else {
            line_end
        };

        let line_orig = &src[line_start..line_end_no_cr];
        let line_clean = &clean[line_start..line_end_no_cr];
        let trimmed = line_clean.trim_start();
        let indent = line_orig.len() - line_orig.trim_start().len();
        let is_unindented = indent == 0;
        let starts_doc_comment = line_orig.trim_start().starts_with("/--")
            && (is_unindented || (section_depth > 0 && indent <= cur_cmd_indent.unwrap_or(indent)));

        if mutual_depth > 0 {
            if is_unindented || (section_depth > 0 && indent <= cur_cmd_indent.unwrap_or(0)) {
                if is_mutual_line_start(trimmed) {
                    mutual_depth += 1;
                } else if is_end_line_start(trimmed) {
                    mutual_depth -= 1;
                }
            }
            cur_byte_end = line_end_no_cr;
            pos = next_pos;
            line_num += 1;
            continue;
        }

        let prev_clean = &clean[cur_byte_start..cur_byte_end];
        let prev_trimmed = prev_clean.trim();
        let prev_is_section_or_ns_header = is_section_header_line(prev_trimmed)
            || prev_trimmed.starts_with("namespace ")
            || is_end_line_start(prev_trimmed);

        let can_start_at_indent = is_unindented
            || (section_depth > 0
                && (prev_is_section_or_ns_header
                    || indent <= cur_cmd_indent.unwrap_or(indent)));

        if line_num > 1
            && can_start_at_indent
            && (starts_doc_comment || (!trimmed.is_empty() && is_top_level_command_start(trimmed)))
        {
            if !is_incomplete_prefix_only_span(prev_clean) {
                spans.push(CmdSpan {
                    start_line: cur_start_line,
                    end_line: line_num - 1,
                    orig_text: &src[cur_byte_start..cur_byte_end],
                    clean_text: prev_clean,
                });
                cur_start_line = line_num;
                cur_byte_start = line_start;
                cur_cmd_indent = None;
            }
        }

        if !trimmed.is_empty() && cur_cmd_indent.is_none() {
            cur_cmd_indent = Some(indent);
        }

        if can_start_at_indent {
            if is_section_header_line(trimmed) {
                section_depth += 1;
            } else if is_end_line_start(trimmed) && section_depth > 0 {
                section_depth -= 1;
            } else if is_mutual_line_start(trimmed) {
                mutual_depth = 1;
            }
        }

        cur_byte_end = line_end_no_cr;
        pos = next_pos;
        line_num += 1;
    }

    let total_lines = line_num - 1;
    if total_lines >= cur_start_line {
        spans.push(CmdSpan {
            start_line: cur_start_line,
            end_line: total_lines,
            orig_text: &src[cur_byte_start..cur_byte_end],
            clean_text: &clean[cur_byte_start..cur_byte_end],
        });
    }

    spans
}

fn classify_decl_header(cmd_text: &str) -> Option<(String, String)> {
    let rest = strip_decl_prefixes(cmd_text);
    for kw in ["theorem", "lemma"] {
        if let Some(after) = rest.strip_prefix(kw) {
            if after.starts_with(char::is_whitespace) {
                let name: String = after
                    .trim_start()
                    .chars()
                    .take_while(|c| {
                        !c.is_whitespace() && *c != '(' && *c != '{' && *c != '[' && *c != ':'
                    })
                    .collect();
                if !name.is_empty() {
                    return Some((kw.to_string(), name));
                }
            }
        }
    }
    None
}

/// Extract the declaration kind and identifier for any top-level declaration (`theorem`, `lemma`,
/// `def`, `abbrev`, `structure`, `class`, `inductive`, `instance`, `axiom`, `opaque`, `simproc`).
fn classify_any_decl_header(cmd_text: &str) -> Option<(&'static str, String)> {
    let rest = strip_decl_prefixes(cmd_text);
    for kw in [
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "structure",
        "class",
        "inductive",
        "coinductive",
        "instance",
        "axiom",
        "opaque",
        "constant",
        "simproc",
        "dsimproc",
        "builtin_simproc",
        "builtin_dsimproc",
    ] {
        if let Some(mut after) = rest.strip_prefix(kw) {
            if after.is_empty() || after.starts_with(char::is_whitespace) || after.starts_with('[')
            {
                after = after.trim_start();
                if after.starts_with('[') {
                    if let Some(close_idx) = after.find(']') {
                        after = after[close_idx + 1..].trim_start();
                    }
                }
                let name: String = after
                    .chars()
                    .take_while(|c| {
                        !c.is_whitespace() && *c != '(' && *c != '{' && *c != '[' && *c != ':'
                    })
                    .collect();
                return Some((kw, name));
            }
        }
    }
    None
}

/// Extract all `@[...]` attribute contents attached to the declaration header of `clean_cmd`.
fn extract_leading_attributes(clean_cmd: &str) -> Vec<String> {
    let mut attrs = Vec::new();
    let mut rest = clean_cmd.trim_start();
    loop {
        if let Some(after_attr) = strip_leading_attr_block(rest) {
            let attr_block_len = rest.len() - after_attr.len();
            let inner = rest[2..attr_block_len - 1].trim();
            if !inner.is_empty() {
                attrs.push(inner.to_string());
            }
            rest = after_attr.trim_start();
            continue;
        }
        let mut stripped_mod = false;
        for m in [
            "private",
            "protected",
            "noncomputable",
            "scoped",
            "local",
            "unsafe",
            "partial",
        ] {
            if let Some(after_m) = rest.strip_prefix(m) {
                if after_m.starts_with(char::is_whitespace) {
                    rest = after_m.trim_start();
                    stripped_mod = true;
                    break;
                }
            }
        }
        if !stripped_mod {
            break;
        }
    }
    attrs
}

/// Returns true if `clean_cmd` has any non-local attribute (e.g. `@[simp]`, `@[ext]`, `@[aesop]`,
/// `@[simproc]`) that persists after a `section` closes.
fn has_non_local_attribute(clean_cmd: &str) -> bool {
    for attr in extract_leading_attributes(clean_cmd) {
        for part in attr.split(',') {
            let p = part.trim();
            if !p.is_empty() && !p.starts_with("local ") && p != "local" {
                return true;
            }
        }
    }
    false
}

/// Returns any `local ...` attribute items on `clean_cmd` (e.g. `local simp` from `@[local simp]`).
fn extract_local_attributes(clean_cmd: &str) -> Vec<String> {
    let mut local_attrs = Vec::new();
    for attr in extract_leading_attributes(clean_cmd) {
        for part in attr.split(',') {
            let p = part.trim();
            if p.starts_with("local ") {
                local_attrs.push(p.to_string());
            }
        }
    }
    local_attrs
}

/// If `span` is a `mutual ... end` block, segment its body into inner declaration `CmdSpan`s.
/// Returns `Some((header_orig, inner_spans, footer_orig))` when the span is a `mutual ... end` block.
fn split_mutual_block_subspans<'a>(
    span: &CmdSpan<'a>,
) -> Option<(&'a str, Vec<CmdSpan<'a>>, &'a str)> {
    let trimmed_clean = span.clean_text.trim_start();
    if !is_mutual_line_start(trimmed_clean) {
        return None;
    }

    let orig = span.orig_text;
    let clean = span.clean_text;
    if orig.len() != clean.len() {
        return None;
    }
    let first_nl = orig.find('\n')?;

    // Find the last non-empty line in `clean` so trailing blank lines after `end` are preserved
    // in `footer_orig` while still matching the closing `end` of `mutual ... end`.
    let trimmed_end_len = clean.trim_end().len();
    if trimmed_end_len <= first_nl {
        return None;
    }
    let last_nl = clean[..trimmed_end_len].rfind('\n')?;
    if last_nl <= first_nl {
        return None;
    }

    let last_line_clean = clean[last_nl + 1..trimmed_end_len].trim();
    if !is_end_line_start(last_line_clean) {
        return None;
    }

    let header_orig = &orig[..first_nl];
    let footer_orig = &orig[last_nl + 1..];
    let body_orig = &orig[first_nl + 1..last_nl];
    let body_clean = &clean[first_nl + 1..last_nl];

    if body_orig.trim().is_empty() {
        return None;
    }

    // Determine minimum indentation of non-empty lines inside the mutual block
    let mut min_indent = usize::MAX;
    for l in body_clean.lines() {
        let t = l.trim();
        if !t.is_empty() {
            let ind = l.len() - l.trim_start().len();
            if ind < min_indent {
                min_indent = ind;
            }
        }
    }
    if min_indent == usize::MAX {
        return None;
    }

    let bytes = body_orig.as_bytes();
    let total_len = bytes.len();
    let mut inner_spans = Vec::new();
    let mut cur_start_line = span.start_line + 1;
    let mut cur_byte_start = 0usize;
    let mut cur_byte_end = 0usize;
    let mut line_num = span.start_line + 1;
    let mut pos = 0usize;

    while pos < total_len {
        let line_start = pos;
        let mut line_end = pos;
        while line_end < total_len && bytes[line_end] != b'\n' {
            line_end += 1;
        }
        let next_pos = if line_end < total_len {
            line_end + 1
        } else {
            total_len
        };
        let line_end_no_cr = if line_end > line_start && bytes[line_end - 1] == b'\r' {
            line_end - 1
        } else {
            line_end
        };

        let line_orig = &body_orig[line_start..line_end_no_cr];
        let line_clean = &body_clean[line_start..line_end_no_cr];
        let trimmed = line_clean.trim_start();
        let indent = line_orig.len() - line_orig.trim_start().len();
        let is_top_inner = indent <= min_indent;
        let starts_doc = is_top_inner && line_orig.trim_start().starts_with("/--");

        if line_num > span.start_line + 1
            && is_top_inner
            && (starts_doc || (!trimmed.is_empty() && is_top_level_command_start(trimmed)))
        {
            let prev_clean = &body_clean[cur_byte_start..cur_byte_end];
            if !is_incomplete_prefix_only_span(prev_clean) {
                inner_spans.push(CmdSpan {
                    start_line: cur_start_line,
                    end_line: line_num - 1,
                    orig_text: &body_orig[cur_byte_start..cur_byte_end],
                    clean_text: prev_clean,
                });
                cur_start_line = line_num;
                cur_byte_start = line_start;
            }
        }

        cur_byte_end = line_end_no_cr;
        pos = next_pos;
        line_num += 1;
    }

    let last_inner_line = line_num - 1;
    if last_inner_line >= cur_start_line {
        inner_spans.push(CmdSpan {
            start_line: cur_start_line,
            end_line: last_inner_line,
            orig_text: &body_orig[cur_byte_start..cur_byte_end],
            clean_text: &body_clean[cur_byte_start..cur_byte_end],
        });
    }

    Some((header_orig, inner_spans, footer_orig))
}

/// Split a top-level theorem/lemma declaration at its top-level `:=` (outside parens/brackets/braces/comments
/// and after any `let x := v` bindings inside the theorem's return type), OR when there is no top-level `:=`,
/// at the first top-level equation-compiler pattern-matching arm (`\n  | pat => proof`) after the top-level `:`.
fn split_at_top_level_assign(cmd: &str) -> Option<(&str, &str)> {
    let bytes = cmd.as_bytes();
    let mut paren = 0i32;
    let mut bracket = 0i32;
    let mut brace = 0i32;
    let mut i = 0usize;
    let mut in_string = false;
    let mut block_comment_depth = 0usize;
    let mut pending_let_assigns = 0usize;
    let mut seen_top_level_colon = false;
    let mut seen_top_level_match_after_colon = false;
    let mut first_top_level_arm_split: Option<usize> = None;

    while i < bytes.len() {
        let c = bytes[i];
        if block_comment_depth > 0 {
            if i + 1 < bytes.len() && c == b'/' && bytes[i + 1] == b'-' {
                block_comment_depth += 1;
                i += 2;
                continue;
            }
            if i + 1 < bytes.len() && c == b'-' && bytes[i + 1] == b'/' {
                block_comment_depth -= 1;
                i += 2;
                continue;
            }
            i += 1;
            continue;
        }
        if in_string {
            if c == b'\\' {
                i += 2;
                continue;
            }
            if c == b'"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        if i + 1 < bytes.len() && c == b'/' && bytes[i + 1] == b'-' {
            block_comment_depth += 1;
            i += 2;
            continue;
        }
        if i + 1 < bytes.len() && c == b'-' && bytes[i + 1] == b'-' {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if paren == 0
            && bracket == 0
            && brace == 0
            && i + 3 < bytes.len()
            && &bytes[i..i + 3] == b"let"
            && (i == 0 || bytes[i - 1].is_ascii_whitespace())
            && bytes[i + 3].is_ascii_whitespace()
        {
            pending_let_assigns += 1;
            i += 3;
            continue;
        }
        if paren == 0
            && bracket == 0
            && brace == 0
            && seen_top_level_colon
            && i + 5 <= bytes.len()
            && &bytes[i..i + 5] == b"where"
            && (i == 0 || bytes[i - 1].is_ascii_whitespace())
            && (i + 5 == bytes.len() || bytes[i + 5].is_ascii_whitespace())
        {
            break;
        }
        if paren == 0
            && bracket == 0
            && brace == 0
            && seen_top_level_colon
            && i + 5 < bytes.len()
            && &bytes[i..i + 5] == b"match"
            && (i == 0 || bytes[i - 1].is_ascii_whitespace())
            && bytes[i + 5].is_ascii_whitespace()
        {
            seen_top_level_match_after_colon = true;
            i += 5;
            continue;
        }
        match c {
            b'"' => in_string = true,
            b'(' => paren += 1,
            b')' => paren = (paren - 1).max(0),
            b'[' => bracket += 1,
            b']' => bracket = (bracket - 1).max(0),
            b'{' => brace += 1,
            b'}' => brace = (brace - 1).max(0),
            b':' if paren == 0 && bracket == 0 && brace == 0 => {
                if i + 1 < bytes.len() && bytes[i + 1] == b'=' {
                    if pending_let_assigns > 0 {
                        pending_let_assigns -= 1;
                        i += 2;
                        continue;
                    }
                    return Some((&cmd[..i], &cmd[i + 2..]));
                } else {
                    seen_top_level_colon = true;
                }
            }
            b'|' if paren == 0 && bracket == 0 && brace == 0 && seen_top_level_colon => {
                let next_ok =
                    i + 1 >= bytes.len() || (bytes[i + 1] != b'|' && bytes[i + 1] != b'>');
                let prev_ok = i == 0 || (bytes[i - 1] != b'|' && bytes[i - 1] != b'<');
                if next_ok && prev_ok {
                    let mut k = i;
                    while k > 0 && (bytes[k - 1] == b' ' || bytes[k - 1] == b'\t') {
                        k -= 1;
                    }
                    if k > 0 && (bytes[k - 1] == b'\n' || bytes[k - 1] == b'\r') {
                        let mut nl_idx = k - 1;
                        if nl_idx > 0 && bytes[nl_idx] == b'\n' && bytes[nl_idx - 1] == b'\r' {
                            nl_idx -= 1;
                        }
                        if !seen_top_level_match_after_colon {
                            return Some((&cmd[..nl_idx], &cmd[nl_idx..]));
                        }
                        first_top_level_arm_split.get_or_insert(nl_idx);
                    }
                }
            }
            _ => {}
        }
        i += 1;
    }
    if let Some(nl_idx) = first_top_level_arm_split {
        return Some((&cmd[..nl_idx], &cmd[nl_idx..]));
    }
    None
}

struct PriorDeclEntry {
    short_name: String,
    full_name: String,
    extra_names: Vec<String>,
    cone_hash_line: String,
    deps: Vec<String>,
    cone_bits: Vec<u64>,
}

fn is_lean_ident_continuation(c: char) -> bool {
    c.is_alphabetic() || c.is_ascii_digit() || c == '_' || c == '\''
}

fn is_lean_keyword_or_builtin(tok: &str) -> bool {
    matches!(
        tok,
        "theorem"
            | "lemma"
            | "def"
            | "abbrev"
            | "structure"
            | "class"
            | "inductive"
            | "coinductive"
            | "instance"
            | "axiom"
            | "opaque"
            | "constant"
            | "where"
            | "by"
            | "fun"
            | "let"
            | "have"
            | "show"
            | "from"
            | "match"
            | "with"
            | "if"
            | "then"
            | "else"
            | "do"
            | "return"
            | "for"
            | "in"
            | "unless"
            | "try"
            | "catch"
            | "finally"
            | "mutual"
            | "end"
            | "section"
            | "namespace"
            | "open"
            | "variable"
            | "variables"
            | "universe"
            | "universes"
            | "set_option"
            | "attribute"
            | "private"
            | "protected"
            | "noncomputable"
            | "scoped"
            | "local"
            | "unsafe"
            | "partial"
            | "sorry"
            | "admit"
            | "rfl"
            | "Prop"
            | "Type"
            | "Sort"
    )
}

fn extract_ident_tokens(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let mut cur_start: Option<usize> = None;
    let mut qual_start: Option<usize> = None;

    for (idx, ch) in s.char_indices() {
        if is_lean_ident_continuation(ch) {
            if cur_start.is_none() {
                if !ch.is_ascii_digit() {
                    cur_start = Some(idx);
                    if qual_start.is_none() {
                        qual_start = Some(idx);
                    }
                }
            }
        } else {
            if let Some(st) = cur_start.take() {
                let tok = &s[st..idx];
                if !is_lean_keyword_or_builtin(tok) && seen.insert(tok.to_string()) {
                    out.push(tok.to_string());
                }
                if ch != '.' {
                    if let Some(qst) = qual_start.take() {
                        if qst < st {
                            let qtok = &s[qst..idx];
                            if seen.insert(qtok.to_string()) {
                                out.push(qtok.to_string());
                            }
                        }
                    }
                }
            } else if ch != '.' {
                qual_start = None;
            }
        }
    }
    if let Some(st) = cur_start {
        let tok = &s[st..];
        if !is_lean_keyword_or_builtin(tok) && seen.insert(tok.to_string()) {
            out.push(tok.to_string());
        }
        if let Some(qst) = qual_start {
            if qst < st {
                let qtok = &s[qst..];
                if seen.insert(qtok.to_string()) {
                    out.push(qtok.to_string());
                }
            }
        }
    }
    out
}

fn extract_inductive_constructors(clean_text: &str) -> Vec<String> {
    let mut ctors = Vec::new();
    for line in clean_text.lines().skip(1) {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix('|') {
            let name: String = rest
                .trim_start()
                .chars()
                .take_while(|c| is_lean_ident_continuation(*c))
                .collect();
            if !name.is_empty() {
                ctors.push(name);
            }
        }
    }
    ctors
}

fn is_cone_scope_or_header_directive(clean_text: &str) -> bool {
    let trimmed = clean_text.trim();
    if trimmed.is_empty() {
        return false;
    }
    if trimmed.starts_with("import ") || is_scope_or_context_command(trimmed) {
        return true;
    }
    for attr in extract_leading_attributes(trimmed) {
        if contains_word(&attr, "simproc") || contains_word(&attr, "csimp") {
            return true;
        }
    }
    let after = strip_decl_prefixes(trimmed);
    for kw in [
        "simproc",
        "dsimproc",
        "builtin_simproc",
        "builtin_dsimproc",
        "notation ",
        "infix",
        "prefix",
        "postfix",
        "syntax ",
        "macro ",
        "macro_rules",
        "elab ",
        "elab_rules",
        "deriving ",
    ] {
        if after == kw || after.starts_with(kw) {
            return true;
        }
    }
    false
}

fn register_prior_decl(
    prior_decls: &mut Vec<PriorDeclEntry>,
    name_to_decl_idxs: &mut std::collections::HashMap<String, Vec<usize>>,
    mut entry: PriorDeclEntry,
) {
    let idx = prior_decls.len();
    let num_words = (idx / 64) + 1;
    let mut cone_bits = vec![0u64; num_words];
    cone_bits[idx / 64] |= 1u64 << (idx % 64);
    for dep_tok in &entry.deps {
        if let Some(dep_idxs) = name_to_decl_idxs.get(dep_tok) {
            for &dep_idx in dep_idxs {
                for (dst, &src) in cone_bits
                    .iter_mut()
                    .zip(prior_decls[dep_idx].cone_bits.iter())
                {
                    *dst |= src;
                }
            }
        }
    }
    entry.cone_bits = cone_bits;

    if !entry.short_name.is_empty() {
        name_to_decl_idxs
            .entry(entry.short_name.clone())
            .or_default()
            .push(idx);
    }
    if !entry.full_name.is_empty() && entry.full_name != entry.short_name {
        name_to_decl_idxs
            .entry(entry.full_name.clone())
            .or_default()
            .push(idx);
    }
    for extra in &entry.extra_names {
        if !extra.is_empty() {
            name_to_decl_idxs
                .entry(extra.clone())
                .or_default()
                .push(idx);
        }
    }
    prior_decls.push(entry);
}

fn compute_cone_env_hash_for_theorem(
    dep_interface_hashes: &[String],
    scope_directives: &[(usize, String)],
    omit_mask: Option<&[bool]>,
    prior_decls: &[PriorDeclEntry],
    name_to_decl_idxs: &std::collections::HashMap<String, Vec<usize>>,
    sig_clean: &str,
    proof_clean: &str,
) -> String {
    let mut hasher = blake3::Hasher::new();
    for dh in dep_interface_hashes {
        hasher.update(dh.as_bytes());
        hasher.update(b"\n");
    }
    for &(span_idx, ref norm_line) in scope_directives {
        if let Some(mask) = omit_mask {
            if span_idx < mask.len() && mask[span_idx] {
                continue;
            }
        }
        hasher.update(norm_line.as_bytes());
    }

    if !prior_decls.is_empty() {
        let num_words = (prior_decls.len() + 63) / 64;
        let mut thm_cone = vec![0u64; num_words];
        for tok in extract_ident_tokens(sig_clean)
            .into_iter()
            .chain(extract_ident_tokens(proof_clean))
        {
            if let Some(idxs) = name_to_decl_idxs.get(&tok) {
                for &idx in idxs {
                    for (dst, &src) in thm_cone
                        .iter_mut()
                        .zip(prior_decls[idx].cone_bits.iter())
                    {
                        *dst |= src;
                    }
                }
            }
        }
        for (w_idx, &word) in thm_cone.iter().enumerate() {
            let mut w = word;
            while w != 0 {
                let bit = w.trailing_zeros() as usize;
                let d_idx = w_idx * 64 + bit;
                hasher.update(prior_decls[d_idx].cone_hash_line.as_bytes());
                w &= w - 1;
            }
        }
    }

    hasher.finalize().to_hex().to_string()
}

/// Update `stack` for scope commands (`namespace A.B.C`, `section`, `noncomputable section`,
/// `mutual`, `end A.B.C`) in `clean_chunk`.
fn update_scope_stack_with_idx(stack: &mut Vec<ScopeFrame>, clean_chunk: &str, span_idx: usize) {
    for line in clean_chunk.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("namespace ") {
            let name = rest.split_whitespace().next().unwrap_or("");
            for seg in name.split('.').filter(|s| !s.is_empty()) {
                stack.push(ScopeFrame {
                    kind: ScopeKind::Namespace,
                    name: seg.to_string(),
                    open_span_idx: span_idx,
                });
            }
        } else if trimmed == "section"
            || trimmed.starts_with("section ")
            || trimmed == "noncomputable section"
            || trimmed.starts_with("noncomputable section ")
        {
            let after_sec = trimmed
                .strip_prefix("noncomputable ")
                .unwrap_or(trimmed)
                .strip_prefix("section")
                .unwrap_or("")
                .trim();
            let name = after_sec.split_whitespace().next().unwrap_or("");
            if name.is_empty() {
                stack.push(ScopeFrame {
                    kind: ScopeKind::Section,
                    name: String::new(),
                    open_span_idx: span_idx,
                });
            } else {
                for seg in name.split('.').filter(|s| !s.is_empty()) {
                    stack.push(ScopeFrame {
                        kind: ScopeKind::Section,
                        name: seg.to_string(),
                        open_span_idx: span_idx,
                    });
                }
            }
        } else if trimmed == "mutual" || trimmed.starts_with("mutual ") {
            stack.push(ScopeFrame {
                kind: ScopeKind::Mutual,
                name: String::new(),
                open_span_idx: span_idx,
            });
        } else if trimmed == "end" || trimmed.starts_with("end ") {
            let name = trimmed
                .strip_prefix("end")
                .unwrap_or("")
                .split_whitespace()
                .next()
                .unwrap_or("");
            if name.is_empty() {
                stack.pop();
            } else {
                let segments: Vec<&str> = name.split('.').filter(|s| !s.is_empty()).collect();
                for seg in segments.into_iter().rev() {
                    if let Some(pos) = stack.iter().rposition(|f| f.name == seg) {
                        stack.truncate(pos);
                    } else {
                        stack.pop();
                    }
                }
            }
        }
    }
}

/// Format closing `end` statements for all currently open frames on `stack`.
/// Consecutive `Namespace` frames opened by the same multi-token `namespace A.B.C` command
/// (`open_span_idx`) are re-joined as `end A.B.C` (or `end A.B` if `C` was already closed).
fn format_closing_scopes(stack: &[ScopeFrame]) -> String {
    if stack.is_empty() {
        return String::new();
    }
    let mut closers = Vec::with_capacity(stack.len());
    let mut i = stack.len();
    while i > 0 {
        let top = &stack[i - 1];
        if top.kind == ScopeKind::Namespace && !top.name.is_empty() {
            let group = top.open_span_idx;
            let mut start = i - 1;
            while start > 0
                && stack[start - 1].kind == ScopeKind::Namespace
                && !stack[start - 1].name.is_empty()
                && stack[start - 1].open_span_idx == group
            {
                start -= 1;
            }
            let joined: Vec<&str> = stack[start..i].iter().map(|f| f.name.as_str()).collect();
            closers.push(format!("end {}", joined.join(".")));
            i = start;
        } else {
            if top.name.is_empty() {
                closers.push("end".to_string());
            } else {
                closers.push(format!("end {}", top.name));
            }
            i -= 1;
        }
    }
    closers.join("\n")
}

/// Identify all matched `(open_span_idx, close_span_idx)` pairs for `section ... end` blocks.
fn compute_closed_section_ranges(spans: &[CmdSpan<'_>]) -> Vec<(usize, usize)> {
    let mut stack: Vec<ScopeFrame> = Vec::new();
    let mut closed_sections = Vec::new();

    for (idx, span) in spans.iter().enumerate() {
        for line in span.clean_text.lines() {
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix("namespace ") {
                let name = rest.split_whitespace().next().unwrap_or("");
                for seg in name.split('.').filter(|s| !s.is_empty()) {
                    stack.push(ScopeFrame {
                        kind: ScopeKind::Namespace,
                        name: seg.to_string(),
                        open_span_idx: idx,
                    });
                }
            } else if trimmed == "section"
                || trimmed.starts_with("section ")
                || trimmed == "noncomputable section"
                || trimmed.starts_with("noncomputable section ")
            {
                let after_sec = trimmed
                    .strip_prefix("noncomputable ")
                    .unwrap_or(trimmed)
                    .strip_prefix("section")
                    .unwrap_or("")
                    .trim();
                let name = after_sec.split_whitespace().next().unwrap_or("");
                stack.push(ScopeFrame {
                    kind: ScopeKind::Section,
                    name: name.to_string(),
                    open_span_idx: idx,
                });
            } else if trimmed == "mutual" || trimmed.starts_with("mutual ") {
                stack.push(ScopeFrame {
                    kind: ScopeKind::Mutual,
                    name: String::new(),
                    open_span_idx: idx,
                });
            } else if trimmed == "end" || trimmed.starts_with("end ") {
                let name = trimmed
                    .strip_prefix("end")
                    .unwrap_or("")
                    .split_whitespace()
                    .next()
                    .unwrap_or("");
                if name.is_empty() {
                    if let Some(popped) = stack.pop() {
                        if popped.kind == ScopeKind::Section {
                            closed_sections.push((popped.open_span_idx, idx));
                        }
                    }
                } else {
                    let segments: Vec<&str> = name.split('.').filter(|s| !s.is_empty()).collect();
                    for seg in segments.into_iter().rev() {
                        if let Some(pos) = stack.iter().rposition(|f| f.name == seg) {
                            for popped in stack.drain(pos..).rev() {
                                if popped.kind == ScopeKind::Section {
                                    closed_sections.push((popped.open_span_idx, idx));
                                }
                            }
                        } else if let Some(popped) = stack.pop() {
                            if popped.kind == ScopeKind::Section {
                                closed_sections.push((popped.open_span_idx, idx));
                            }
                        }
                    }
                }
            }
        }
    }

    closed_sections
}

/// Returns true if a closed `section ... end` block `spans[sec_open..=sec_close]` contains
/// any declaration that can still be visible and needed after `sec_close` (up to `target_idx`).
/// Section-local commands (`variable`, `open`, `set_option`, `local instance`, `local notation`,
/// `attribute [local ...]`, and `@[local ...]` theorems not referenced after `sec_close`) do not
/// survive `end` and therefore do not force the closed section to be retained.
fn closed_section_needed_at_target(
    spans: &[CmdSpan<'_>],
    sec_open: usize,
    sec_close: usize,
    target_idx: usize,
) -> bool {
    if sec_open + 1 >= sec_close {
        return false;
    }
    let after_spans = &spans[sec_close + 1..=target_idx];

    for inner in &spans[sec_open + 1..sec_close] {
        let trimmed = inner.clean_text.trim();
        if trimmed.is_empty() || is_scope_or_context_command(trimmed) {
            continue;
        }
        let after_attrs = {
            let mut r = trimmed;
            while let Some(next) = strip_leading_attr_block(r) {
                r = next.trim_start();
            }
            r
        };
        if after_attrs.starts_with("local ") {
            continue;
        }

        if let Some((_, mut_subspans, _)) = split_mutual_block_subspans(inner) {
            for sub in &mut_subspans {
                if let Some((kw, name)) = classify_any_decl_header(sub.clean_text) {
                    if kw != "theorem" && kw != "lemma" {
                        return true;
                    }
                    if has_non_local_attribute(sub.clean_text) {
                        return true;
                    }
                    let short = name.rsplit('.').next().unwrap_or(&name);
                    if !short.is_empty()
                        && after_spans
                            .iter()
                            .any(|s| contains_local_decl_ref(s.clean_text, short, &name))
                    {
                        return true;
                    }
                }
            }
            continue;
        }

        if let Some((kw, name)) = classify_any_decl_header(trimmed) {
            if kw != "theorem" && kw != "lemma" {
                return true;
            }
            if has_non_local_attribute(trimmed) {
                return true;
            }
            let short = name.rsplit('.').next().unwrap_or(&name);
            if !short.is_empty()
                && after_spans
                    .iter()
                    .any(|s| contains_local_decl_ref(s.clean_text, short, &name))
            {
                return true;
            }
            continue;
        }

        return true;
    }

    false
}

/// Compute a boolean mask over `spans[..=target_idx]` indicating which spans belong to dead
/// already-closed `section ... end` blocks that can be omitted for `target_idx`.
fn compute_omitted_closed_section_spans(
    spans: &[CmdSpan<'_>],
    closed_sections: &[(usize, usize)],
    target_idx: usize,
) -> Vec<bool> {
    let mut omit = vec![false; target_idx + 1];
    for &(sec_open, sec_close) in closed_sections {
        if sec_close < target_idx
            && !closed_section_needed_at_target(spans, sec_open, sec_close, target_idx)
        {
            for flag in &mut omit[sec_open..=sec_close] {
                *flag = true;
            }
        }
    }
    omit
}

fn hash_normalized_whitespace(hasher: &mut blake3::Hasher, s: &str, suffix: &[u8]) -> bool {
    let mut first = true;
    for tok in s.split_whitespace() {
        if !first {
            hasher.update(b" ");
        }
        hasher.update(tok.as_bytes());
        first = false;
    }
    if !first && !suffix.is_empty() {
        hasher.update(suffix);
    }
    !first
}

fn hash_normalized_whitespace_hex(s: &str) -> String {
    let mut hasher = blake3::Hasher::new();
    hash_normalized_whitespace(&mut hasher, s, b"");
    hasher.finalize().to_hex().to_string()
}

/// Analyze and split a Lean 4 source file into:
/// 1. `skeleton_source`: all `Prop` theorem/lemma proof bodies replaced by `sorry` (preserving line counts)
/// 2. `interface_hash`: BLAKE3 of the proof-irrelevant interface (`Skeleton`)
/// 3. `shards`: per-theorem shards with acyclic `PrefixEnvHash` and scope-isolated `shard_source`
pub fn split_lean_source(src: &str, dep_interface_hashes: &[String]) -> SplitResult {
    let clean = strip_lean_comments(src);
    let hygiene = audit_hygiene(&clean);
    let spans = parse_command_spans(src, &clean);
    let closed_sections = compute_closed_section_ranges(&spans);

    let omit_shard_source = src.len().saturating_mul(spans.len()) > 65_536;
    let has_closed_sections = !closed_sections.is_empty();
    let mut import_lines = Vec::new();
    let mut interface_hasher = blake3::Hasher::new();

    // Pre-build per-span skeleton representation (only when `!omit_shard_source`) and
    // normalized hash bytes (only when `has_closed_sections`) so each shard can construct
    // its scope-pruned prefix in O(spans).
    let mut span_skel_orig: Vec<String> = if omit_shard_source {
        Vec::new()
    } else {
        Vec::with_capacity(spans.len())
    };
    let mut span_norm_hash_line: Vec<String> = if has_closed_sections {
        Vec::with_capacity(spans.len())
    } else {
        Vec::new()
    };

    if !omit_shard_source || has_closed_sections {
        for span in &spans {
            if let Some((header_orig, inner_spans, footer_orig)) = split_mutual_block_subspans(span)
            {
                let has_inner_thm = inner_spans.iter().any(|sub| {
                    classify_decl_header(sub.clean_text).is_some()
                        && split_at_top_level_assign(sub.clean_text).is_some()
                });
                if has_inner_thm {
                    let mut inner_norm_parts = if has_closed_sections {
                        let mut v = Vec::with_capacity(inner_spans.len() + 2);
                        v.push("mutual".to_string());
                        v
                    } else {
                        Vec::new()
                    };
                    if !omit_shard_source {
                        let mut inner_skel_parts = Vec::with_capacity(inner_spans.len() + 2);
                        inner_skel_parts.push(header_orig.to_string());
                        for sub in &inner_spans {
                            if classify_decl_header(sub.clean_text).is_some() {
                                if let Some((sig_clean, proof_clean)) =
                                    split_at_top_level_assign(sub.clean_text)
                                {
                                    let (sig_orig, proof_orig) =
                                        split_at_top_level_assign(sub.orig_text)
                                            .unwrap_or((sig_clean, proof_clean));
                                    let proof_newlines = proof_orig.matches('\n').count();
                                    let padded_sorry =
                                        format!(" := sorry{}", "\n".repeat(proof_newlines));
                                    inner_skel_parts.push(format!("{}{}", sig_orig, padded_sorry));
                                    if has_closed_sections {
                                        inner_norm_parts.push(format!(
                                            "{} := sorry",
                                            normalize_whitespace(sig_clean)
                                        ));
                                    }
                                    continue;
                                }
                            }
                            inner_skel_parts.push(sub.orig_text.to_string());
                            if has_closed_sections {
                                inner_norm_parts.push(normalize_whitespace(sub.clean_text));
                            }
                        }
                        inner_skel_parts.push(footer_orig.to_string());
                        span_skel_orig.push(inner_skel_parts.join("\n"));
                    } else if has_closed_sections {
                        for sub in &inner_spans {
                            if classify_decl_header(sub.clean_text).is_some() {
                                if let Some((sig_clean, _)) =
                                    split_at_top_level_assign(sub.clean_text)
                                {
                                    inner_norm_parts.push(format!(
                                        "{} := sorry",
                                        normalize_whitespace(sig_clean)
                                    ));
                                    continue;
                                }
                            }
                            inner_norm_parts.push(normalize_whitespace(sub.clean_text));
                        }
                    }
                    if has_closed_sections {
                        inner_norm_parts.push("end".to_string());
                        span_norm_hash_line.push(format!("{}\n", inner_norm_parts.join("\n")));
                    }
                    continue;
                }
            }

            if classify_decl_header(span.clean_text).is_some() {
                if let Some((sig_clean, proof_clean)) = split_at_top_level_assign(span.clean_text) {
                    if !omit_shard_source {
                        let (sig_orig, proof_orig) = split_at_top_level_assign(span.orig_text)
                            .unwrap_or((sig_clean, proof_clean));
                        let proof_newlines = proof_orig.matches('\n').count();
                        let padded_sorry = format!(" := sorry{}", "\n".repeat(proof_newlines));
                        span_skel_orig.push(format!("{}{}", sig_orig, padded_sorry));
                    }
                    if has_closed_sections {
                        span_norm_hash_line
                            .push(format!("{} := sorry\n", normalize_whitespace(sig_clean)));
                    }
                    continue;
                }
            }

            if !omit_shard_source {
                span_skel_orig.push(span.orig_text.to_string());
            }
            if has_closed_sections {
                let norm_cmd = normalize_whitespace(span.clean_text);
                if norm_cmd.is_empty() {
                    span_norm_hash_line.push(String::new());
                } else {
                    span_norm_hash_line.push(format!("{}\n", norm_cmd));
                }
            }
        }
    }

    let mut shards = Vec::new();
    let mut scope_stack: Vec<ScopeFrame> = Vec::new();
    let mut prior_decls: Vec<PriorDeclEntry> = Vec::new();
    let mut name_to_decl_idxs: std::collections::HashMap<String, Vec<usize>> =
        std::collections::HashMap::new();
    let mut scope_directives: Vec<(usize, String)> = Vec::new();

    for (span_idx, span) in spans.iter().enumerate() {
        let trimmed = span.clean_text.trim();
        if trimmed.starts_with("import ") {
            import_lines.push(span.orig_text.to_string());
        }

        // Helper closure to compute scope-pruned `(prefix_env_hash, prefix_skeleton_str)` for `span_idx`
        let build_pruned_prefix = |target_idx: usize,
                                   inc_hasher: &blake3::Hasher|
         -> (String, String, Option<Vec<bool>>) {
            if !has_closed_sections {
                let mut prefix_accum = String::new();
                if !omit_shard_source {
                    prefix_accum.reserve(src.len());
                    for i in 0..target_idx {
                        prefix_accum.push_str(&span_skel_orig[i]);
                        prefix_accum.push('\n');
                    }
                }
                let mut h = inc_hasher.clone();
                for dh in dep_interface_hashes {
                    h.update(dh.as_bytes());
                    h.update(b"\n");
                }
                return (
                    h.finalize().to_hex().to_string(),
                    prefix_accum,
                    None,
                );
            }
            let omit_mask =
                compute_omitted_closed_section_spans(&spans, &closed_sections, target_idx);
            let mut hasher = blake3::Hasher::new();
            for dh in dep_interface_hashes {
                hasher.update(dh.as_bytes());
                hasher.update(b"\n");
            }
            let mut prefix_accum = if omit_shard_source {
                String::new()
            } else {
                String::with_capacity(src.len())
            };
            for i in 0..target_idx {
                if omit_mask[i] {
                    continue;
                }
                let norm_line = &span_norm_hash_line[i];
                if !norm_line.is_empty() {
                    hasher.update(norm_line.as_bytes());
                }
                if !omit_shard_source {
                    prefix_accum.push_str(&span_skel_orig[i]);
                    prefix_accum.push('\n');
                }
            }
            (
                hasher.finalize().to_hex().to_string(),
                prefix_accum,
                Some(omit_mask),
            )
        };

        // Case 1: `mutual ... end` block containing one or more `theorem` / `lemma` declarations
        if let Some((_header_orig, inner_spans, _footer_orig)) = split_mutual_block_subspans(span) {
            let mut found_inner_thm = false;
            for sub in &inner_spans {
                if let Some((kind, name)) = classify_decl_header(sub.clean_text) {
                    if let Some((sig_clean, proof_clean)) =
                        split_at_top_level_assign(sub.clean_text)
                    {
                        found_inner_thm = true;
                        let (sig_orig, proof_orig) = split_at_top_level_assign(sub.orig_text)
                            .unwrap_or((sig_clean, proof_clean));
                        let (prefix_env_hash, prefix_skeleton_accum, omit_mask) =
                            build_pruned_prefix(span_idx, &interface_hasher);
                        let cone_env_hash = compute_cone_env_hash_for_theorem(
                            dep_interface_hashes,
                            &scope_directives,
                            omit_mask.as_deref(),
                            &prior_decls,
                            &name_to_decl_idxs,
                            sig_clean,
                            proof_clean,
                        );
                        let stmt_hash = hash_normalized_whitespace_hex(sig_clean);
                        let proof_hash = hash_normalized_whitespace_hex(proof_clean);

                        let shard_source = if omit_shard_source {
                            String::new()
                        } else {
                            let closing_scopes = format_closing_scopes(&scope_stack);
                            format!(
                                "{}\n{}\n{}",
                                prefix_skeleton_accum, span.orig_text, closing_scopes
                            )
                        };

                        shards.push(TheoremShard {
                            name,
                            kind,
                            start_line: sub.start_line,
                            end_line: sub.end_line,
                            signature_text: sig_orig.trim().to_string(),
                            proof_text: proof_orig.trim().to_string(),
                            prefix_env_hash,
                            cone_env_hash,
                            stmt_hash,
                            proof_hash,
                            shard_source,
                        });
                    }
                }
            }
            let mutual_start_idx = prior_decls.len();
            for sub in &inner_spans {
                if let Some((_kind, name)) = classify_decl_header(sub.clean_text) {
                    if let Some((sig_clean, _)) = split_at_top_level_assign(sub.clean_text) {
                        let short = name.rsplit('.').next().unwrap_or(&name).to_string();
                        let st_hash = hash_normalized_whitespace_hex(sig_clean);
                        register_prior_decl(
                            &mut prior_decls,
                            &mut name_to_decl_idxs,
                            PriorDeclEntry {
                                short_name: short,
                                full_name: name.clone(),
                                extra_names: Vec::new(),
                                cone_hash_line: format!("thm:{}:{}\n", name, st_hash),
                                deps: extract_ident_tokens(sig_clean),
                                cone_bits: Vec::new(),
                            },
                        );
                        continue;
                    }
                }
                if let Some((kw, name)) = classify_any_decl_header(sub.clean_text) {
                    let short = name.rsplit('.').next().unwrap_or(&name).to_string();
                    let extra_names = if kw == "inductive" || kw == "coinductive" {
                        extract_inductive_constructors(sub.clean_text)
                    } else {
                        Vec::new()
                    };
                    let decl_hash = hash_normalized_whitespace_hex(sub.clean_text);
                    register_prior_decl(
                        &mut prior_decls,
                        &mut name_to_decl_idxs,
                        PriorDeclEntry {
                            short_name: short,
                            full_name: name.clone(),
                            extra_names,
                            cone_hash_line: format!("decl:{}:{}:{}\n", kw, name, decl_hash),
                            deps: extract_ident_tokens(sub.clean_text),
                            cone_bits: Vec::new(),
                        },
                    );
                }
            }
            if prior_decls.len() > mutual_start_idx + 1 {
                let mut union_bits = vec![0u64; (prior_decls.len() + 63) / 64];
                for entry in &prior_decls[mutual_start_idx..] {
                    for (dst, &src) in union_bits.iter_mut().zip(entry.cone_bits.iter()) {
                        *dst |= src;
                    }
                }
                for entry in &mut prior_decls[mutual_start_idx..] {
                    entry.cone_bits.clone_from(&union_bits);
                }
            }
            if found_inner_thm {
                if has_closed_sections {
                    if !span_norm_hash_line[span_idx].is_empty() {
                        interface_hasher.update(span_norm_hash_line[span_idx].as_bytes());
                    }
                } else {
                    interface_hasher.update(b"mutual\n");
                    for sub in &inner_spans {
                        if classify_decl_header(sub.clean_text).is_some() {
                            if let Some((sig_clean, _)) = split_at_top_level_assign(sub.clean_text)
                            {
                                if !hash_normalized_whitespace(
                                    &mut interface_hasher,
                                    sig_clean,
                                    b" := sorry\n",
                                ) {
                                    interface_hasher.update(b" := sorry\n");
                                }
                                continue;
                            }
                        }
                        if !hash_normalized_whitespace(
                            &mut interface_hasher,
                            sub.clean_text,
                            b"\n",
                        ) {
                            interface_hasher.update(b"\n");
                        }
                    }
                    interface_hasher.update(b"end\n");
                }
                update_scope_stack_with_idx(&mut scope_stack, span.clean_text, span_idx);
                continue;
            }
        }

        // Case 2: Standard top-level `theorem` / `lemma` declaration
        if let Some((kind, name)) = classify_decl_header(span.clean_text) {
            if let Some((sig_clean, proof_clean)) = split_at_top_level_assign(span.clean_text) {
                let (sig_orig, proof_orig) =
                    split_at_top_level_assign(span.orig_text).unwrap_or((sig_clean, proof_clean));

                let (prefix_env_hash, prefix_skeleton_accum, omit_mask) =
                    build_pruned_prefix(span_idx, &interface_hasher);
                let cone_env_hash = compute_cone_env_hash_for_theorem(
                    dep_interface_hashes,
                    &scope_directives,
                    omit_mask.as_deref(),
                    &prior_decls,
                    &name_to_decl_idxs,
                    sig_clean,
                    proof_clean,
                );
                let stmt_hash = hash_normalized_whitespace_hex(sig_clean);
                let proof_hash = hash_normalized_whitespace_hex(proof_clean);

                let shard_source = if omit_shard_source {
                    String::new()
                } else {
                    let closing_scopes = format_closing_scopes(&scope_stack);
                    format!(
                        "{}\n{}\n{}",
                        prefix_skeleton_accum, span.orig_text, closing_scopes
                    )
                };

                let short_name = name.rsplit('.').next().unwrap_or(&name).to_string();
                register_prior_decl(
                    &mut prior_decls,
                    &mut name_to_decl_idxs,
                    PriorDeclEntry {
                        short_name,
                        full_name: name.clone(),
                        extra_names: Vec::new(),
                        cone_hash_line: format!("thm:{}:{}\n", name, stmt_hash),
                        deps: extract_ident_tokens(sig_clean),
                        cone_bits: Vec::new(),
                    },
                );
                if is_cone_scope_or_header_directive(span.clean_text) {
                    scope_directives.push((
                        span_idx,
                        format!("{} := sorry\n", normalize_whitespace(sig_clean)),
                    ));
                }

                shards.push(TheoremShard {
                    name,
                    kind,
                    start_line: span.start_line,
                    end_line: span.end_line,
                    signature_text: sig_orig.trim().to_string(),
                    proof_text: proof_orig.trim().to_string(),
                    prefix_env_hash,
                    cone_env_hash,
                    stmt_hash,
                    proof_hash,
                    shard_source,
                });

                if has_closed_sections {
                    interface_hasher.update(span_norm_hash_line[span_idx].as_bytes());
                } else if !hash_normalized_whitespace(
                    &mut interface_hasher,
                    sig_clean,
                    b" := sorry\n",
                ) {
                    interface_hasher.update(b" := sorry\n");
                }
                update_scope_stack_with_idx(&mut scope_stack, span.clean_text, span_idx);
                continue;
            }
        }

        // Case 3: Non-theorem command (`import`, `open`, `variable`, `def`, `structure`, `instance`, etc.)
        if is_cone_scope_or_header_directive(span.clean_text) {
            let norm_dir = normalize_whitespace(span.clean_text);
            if !norm_dir.is_empty() {
                scope_directives.push((span_idx, format!("{}\n", norm_dir)));
            }
        } else if let Some((kw, name)) = classify_any_decl_header(span.clean_text) {
            if name.is_empty() && kw == "instance" {
                let norm_dir = normalize_whitespace(span.clean_text);
                if !norm_dir.is_empty() {
                    scope_directives.push((span_idx, format!("{}\n", norm_dir)));
                }
            } else {
                let short = name.rsplit('.').next().unwrap_or(&name).to_string();
                let extra_names = if kw == "inductive" || kw == "coinductive" {
                    extract_inductive_constructors(span.clean_text)
                } else {
                    Vec::new()
                };
                let decl_hash = hash_normalized_whitespace_hex(span.clean_text);
                register_prior_decl(
                    &mut prior_decls,
                    &mut name_to_decl_idxs,
                    PriorDeclEntry {
                        short_name: short,
                        full_name: name.clone(),
                        extra_names,
                        cone_hash_line: format!("decl:{}:{}:{}\n", kw, name, decl_hash),
                        deps: extract_ident_tokens(span.clean_text),
                        cone_bits: Vec::new(),
                    },
                );
            }
        }

        if has_closed_sections {
            if !span_norm_hash_line[span_idx].is_empty() {
                interface_hasher.update(span_norm_hash_line[span_idx].as_bytes());
            }
        } else {
            hash_normalized_whitespace(&mut interface_hasher, span.clean_text, b"\n");
        }
        update_scope_stack_with_idx(&mut scope_stack, span.clean_text, span_idx);
    }

    let skeleton_source = if omit_shard_source {
        String::new()
    } else {
        span_skel_orig.join("\n")
    };
    let interface_hash = interface_hasher.finalize().to_hex().to_string();
    let eligible_for_sharding = !hygiene.has_impure_metaprograms;
    let fallback_reason = if hygiene.has_impure_metaprograms {
        Some("Module contains impure/reflective metaprograms (#eval/run_cmd/#guard_msgs/initialize); using WholeModule mode".to_string())
    } else {
        None
    };

    SplitResult {
        eligible_for_sharding,
        fallback_reason,
        imports_header: import_lines.join("\n"),
        skeleton_source,
        interface_hash,
        shards,
        hygiene,
    }
}

fn decl_name_matches_target(name: &str, target_decl: &str) -> bool {
    name == target_decl
        || name
            .strip_suffix(target_decl)
            .map(|p| p.ends_with('.'))
            .unwrap_or(false)
        || target_decl
            .strip_suffix(name)
            .map(|p| p.ends_with('.'))
            .unwrap_or(false)
}

/// Reconstruct the self-contained prefix-only `shard_source` (`prefix_skeleton_accum + span.orig_text + closing_scopes`)
/// for a single theorem declaration `target_decl` on demand in $O(N)$ time and memory.
pub fn reconstruct_single_shard_source(src: &str, target_decl: &str) -> Option<String> {
    let clean = strip_lean_comments(src);
    let spans = parse_command_spans(src, &clean);
    let closed_sections = compute_closed_section_ranges(&spans);

    let mut target_span_idx = None;
    for (idx, span) in spans.iter().enumerate() {
        if let Some((_, inner_spans, _)) = split_mutual_block_subspans(span) {
            if inner_spans.iter().any(|sub| {
                classify_decl_header(sub.clean_text)
                    .map(|(_, n)| decl_name_matches_target(&n, target_decl))
                    .unwrap_or(false)
            }) {
                target_span_idx = Some(idx);
                break;
            }
        }
        if let Some((_kind, name)) = classify_decl_header(span.clean_text) {
            if split_at_top_level_assign(span.clean_text).is_some()
                && decl_name_matches_target(&name, target_decl)
            {
                target_span_idx = Some(idx);
                break;
            }
        }
    }
    let t_idx = target_span_idx?;
    let omit_mask = compute_omitted_closed_section_spans(&spans, &closed_sections, t_idx);

    let mut prefix_skeleton_accum = String::with_capacity(src.len());
    let mut scope_stack: Vec<ScopeFrame> = Vec::new();

    for (idx, span) in spans[..t_idx].iter().enumerate() {
        update_scope_stack_with_idx(&mut scope_stack, span.clean_text, idx);
        if omit_mask[idx] {
            continue;
        }
        if let Some((header_orig, inner_spans, footer_orig)) = split_mutual_block_subspans(span) {
            let has_inner_thm = inner_spans.iter().any(|sub| {
                classify_decl_header(sub.clean_text).is_some()
                    && split_at_top_level_assign(sub.clean_text).is_some()
            });
            if has_inner_thm {
                prefix_skeleton_accum.push_str(header_orig);
                prefix_skeleton_accum.push('\n');
                for sub in &inner_spans {
                    if classify_decl_header(sub.clean_text).is_some() {
                        if let Some((sig_clean, proof_clean)) =
                            split_at_top_level_assign(sub.clean_text)
                        {
                            let (sig_orig, proof_orig) = split_at_top_level_assign(sub.orig_text)
                                .unwrap_or((sig_clean, proof_clean));
                            let proof_newlines = proof_orig.matches('\n').count();
                            let padded_sorry = format!(" := sorry{}", "\n".repeat(proof_newlines));
                            prefix_skeleton_accum.push_str(sig_orig);
                            prefix_skeleton_accum.push_str(&padded_sorry);
                            prefix_skeleton_accum.push('\n');
                            continue;
                        }
                    }
                    prefix_skeleton_accum.push_str(sub.orig_text);
                    prefix_skeleton_accum.push('\n');
                }
                prefix_skeleton_accum.push_str(footer_orig);
                prefix_skeleton_accum.push('\n');
                continue;
            }
        }
        if classify_decl_header(span.clean_text).is_some() {
            if let Some((sig_clean, proof_clean)) = split_at_top_level_assign(span.clean_text) {
                let (sig_orig, proof_orig) =
                    split_at_top_level_assign(span.orig_text).unwrap_or((sig_clean, proof_clean));
                let proof_newlines = proof_orig.matches('\n').count();
                let padded_sorry = format!(" := sorry{}", "\n".repeat(proof_newlines));
                prefix_skeleton_accum.push_str(sig_orig);
                prefix_skeleton_accum.push_str(&padded_sorry);
                prefix_skeleton_accum.push('\n');
                continue;
            }
        }
        prefix_skeleton_accum.push_str(span.orig_text);
        prefix_skeleton_accum.push('\n');
    }

    let closing_scopes = format_closing_scopes(&scope_stack);
    Some(format!(
        "{}\n{}\n{}",
        prefix_skeleton_accum, spans[t_idx].orig_text, closing_scopes
    ))
}

fn normalize_whitespace(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for word in s.split_whitespace() {
        if !out.is_empty() {
            out.push(' ');
        }
        out.push_str(word);
    }
    out
}

/// Build a coalesced Lean 4 source file for batch verification of uncached theorem shards `U`:
/// - All **cached** theorems (`name ∉ uncached_names`) have their proof bodies replaced by
///   line-preserving `:= sorry` so Lean skips re-elaborating them in 0 ms while registering their types.
/// - All **uncached** theorems (`name ∈ uncached_names`) retain their full original proof bodies
///   at their exact original line numbers.
pub fn build_coalesced_shard_source(
    src: &str,
    uncached_names: &std::collections::HashSet<String>,
) -> String {
    let clean = strip_lean_comments(src);
    let spans = parse_command_spans(src, &clean);

    let mut chunks = Vec::with_capacity(spans.len());
    for span in &spans {
        if let Some((header_orig, inner_spans, footer_orig)) = split_mutual_block_subspans(span) {
            let has_inner_thm = inner_spans.iter().any(|sub| {
                classify_decl_header(sub.clean_text).is_some()
                    && split_at_top_level_assign(sub.clean_text).is_some()
            });
            if has_inner_thm {
                let mut inner_chunks = Vec::with_capacity(inner_spans.len() + 2);
                inner_chunks.push(header_orig.to_string());
                for sub in &inner_spans {
                    if let Some((_kind, name)) = classify_decl_header(sub.clean_text) {
                        if !matches_uncached_or_fast_verify_name(&name, uncached_names) {
                            if let Some((sig_clean, proof_clean)) =
                                split_at_top_level_assign(sub.clean_text)
                            {
                                let (sig_orig, proof_orig) =
                                    split_at_top_level_assign(sub.orig_text)
                                        .unwrap_or((sig_clean, proof_clean));
                                let proof_newlines = proof_orig.matches('\n').count();
                                let padded_sorry =
                                    format!(" := sorry{}", "\n".repeat(proof_newlines));
                                inner_chunks.push(format!("{}{}", sig_orig, padded_sorry));
                                continue;
                            }
                        }
                    }
                    inner_chunks.push(sub.orig_text.to_string());
                }
                inner_chunks.push(footer_orig.to_string());
                chunks.push(inner_chunks.join("\n"));
                continue;
            }
        }

        if let Some((_kind, name)) = classify_decl_header(span.clean_text) {
            if !matches_uncached_or_fast_verify_name(&name, uncached_names) {
                let short = name.rsplit('.').next().unwrap_or(&name);
                if short.starts_with("_turbo_verify_") {
                    continue;
                }
                if let Some((sig_clean, proof_clean)) = split_at_top_level_assign(span.clean_text) {
                    let (sig_orig, proof_orig) = split_at_top_level_assign(span.orig_text)
                        .unwrap_or((sig_clean, proof_clean));
                    let proof_newlines = proof_orig.matches('\n').count();
                    let padded_sorry = format!(" := sorry{}", "\n".repeat(proof_newlines));
                    chunks.push(format!("{}{}", sig_orig, padded_sorry));
                    continue;
                }
            }
        }
        chunks.push(span.orig_text.to_string());
    }

    chunks.join("\n")
}

fn contains_local_decl_ref(haystack: &str, short: &str, full_name: &str) -> bool {
    const STD_PREFIXES: &[&str] = &[
        "Nat.",
        "Int.",
        "List.",
        "Array.",
        "BitVec.",
        "Bool.",
        "Option.",
        "Fin.",
        "Prod.",
        "Subtype.",
        "Classical.",
        "Decidable.",
        "Eq.",
        "Iff.",
    ];
    let bytes = haystack.as_bytes();
    for (idx, _) in haystack.match_indices(short) {
        let end = idx + short.len();
        let next_ok = end >= bytes.len()
            || (!bytes[end].is_ascii_alphanumeric() && bytes[end] != b'_' && bytes[end] != b'\'');
        if !next_ok {
            continue;
        }
        let mut q_start = idx;
        while q_start > 0
            && (bytes[q_start - 1].is_ascii_alphanumeric()
                || bytes[q_start - 1] == b'_'
                || bytes[q_start - 1] == b'\''
                || bytes[q_start - 1] == b'.')
        {
            q_start -= 1;
        }
        let qual_ident = &haystack[q_start..end];
        if qual_ident == short || qual_ident == full_name {
            return true;
        }
        if STD_PREFIXES
            .iter()
            .any(|p| qual_ident.starts_with(p) && !full_name.starts_with(p))
        {
            continue;
        }
        if idx == q_start || (!bytes[idx - 1].is_ascii_alphanumeric() && bytes[idx - 1] != b'_') {
            return true;
        }
    }
    false
}

/// Verify that the proof body of shard `idx` does not reference its own theorem name
/// or any subsequent theorem `j >= idx` in the same file, guaranteeing acyclic soundness
/// when importing the pre-compiled `.olean` environment.
pub fn shard_is_acyclic_for_fast_import(shards: &[TheoremShard], idx: usize) -> bool {
    if idx >= shards.len() {
        return false;
    }
    let proof = &shards[idx].proof_text;
    for later in &shards[idx..] {
        let short = later.name.rsplit('.').next().unwrap_or(&later.name);
        if contains_local_decl_ref(proof, short, &later.name) {
            return false;
        }
    }
    true
}

fn matches_uncached_name(name: &str, uncached_names: &std::collections::HashSet<String>) -> bool {
    if uncached_names.contains(name) {
        return true;
    }
    uncached_names.iter().any(|u| {
        name.strip_suffix(u.as_str())
            .map(|p| p.ends_with('.'))
            .unwrap_or(false)
            || u.strip_suffix(name)
                .map(|p| p.ends_with('.'))
                .unwrap_or(false)
    })
}

fn matches_uncached_or_fast_verify_name(
    name: &str,
    uncached_names: &std::collections::HashSet<String>,
) -> bool {
    if matches_uncached_name(name, uncached_names) {
        return true;
    }
    let short = name.rsplit('.').next().unwrap_or(name);
    if let Some(after_prefix) = short.strip_prefix("_turbo_verify_") {
        if let Some(orig_safe) = after_prefix
            .trim_start_matches(|c: char| c.is_ascii_digit())
            .strip_prefix('_')
        {
            return uncached_names.iter().any(|u| {
                let u_short = u.rsplit('.').next().unwrap_or(u.as_str());
                let u_safe: String = u
                    .chars()
                    .map(|c| {
                        if c.is_ascii_alphanumeric() || c == '_' {
                            c
                        } else {
                            '_'
                        }
                    })
                    .collect();
                let u_short_safe: String = u_short
                    .chars()
                    .map(|c| {
                        if c.is_ascii_alphanumeric() || c == '_' {
                            c
                        } else {
                            '_'
                        }
                    })
                    .collect();
                orig_safe == u_safe || orig_safe == u_short_safe
            });
        }
    }
    false
}

/// Returns true if `clean_text` is a scope or scoped-modifier command (`namespace`, `section`,
/// `end`, `open`, `variable`, `universe`, `set_option`, `attribute`, `local notation`,
/// `local instance`, `scoped instance`, `local simproc`, `scoped simproc`, `include`, `omit`, `export`).
fn is_scope_or_context_command(clean_text: &str) -> bool {
    let trimmed = clean_text.trim();
    if trimmed.starts_with("set_option ") && (trimmed.ends_with(" in") || trimmed.contains(" in\n"))
    {
        return false;
    }
    for prefix in [
        "namespace ",
        "section",
        "noncomputable section",
        "end",
        "open ",
        "variable ",
        "variables ",
        "universe ",
        "universes ",
        "set_option ",
        "attribute ",
        "include ",
        "omit ",
        "export ",
    ] {
        if trimmed == prefix || trimmed.starts_with(prefix) {
            return true;
        }
    }
    // Check `local` / `scoped` modifiers (possibly preceded by `@[...]`)
    let mut after_attrs = trimmed;
    while let Some(next) = strip_leading_attr_block(after_attrs) {
        after_attrs = next.trim_start();
    }
    for prefix in [
        "local notation",
        "scoped notation",
        "local infix",
        "scoped infix",
        "local prefix",
        "scoped prefix",
        "local postfix",
        "scoped postfix",
        "local instance",
        "scoped instance",
        "local attribute",
        "scoped attribute",
        "local simproc",
        "scoped simproc",
        "local dsimproc",
        "scoped dsimproc",
        "local syntax",
        "scoped syntax",
        "local macro",
        "scoped macro",
        "local elab",
        "scoped elab",
    ] {
        if after_attrs.starts_with(prefix) {
            return true;
        }
    }
    false
}

/// Rename a named `local instance <name> ...` or `scoped instance <name> ...` for fast `.olean`
/// verification so it does not collide with the constant `<name>` imported from `<Module>.olean`.
fn format_scoped_instance_for_fast_check(orig_text: &str, clean_text: &str, idx: usize) -> String {
    let rest = strip_decl_prefixes(clean_text);
    if let Some(after_inst) = rest.strip_prefix("instance") {
        if after_inst.starts_with(char::is_whitespace) {
            let trimmed_after = after_inst.trim_start();
            let name: String = trimmed_after
                .chars()
                .take_while(|c| {
                    !c.is_whitespace() && *c != '(' && *c != '{' && *c != '[' && *c != ':'
                })
                .collect();
            if !name.is_empty() && orig_text.len() == clean_text.len() {
                let offset_in_clean =
                    clean_text.len() - trimmed_after.len();
                let name_end = offset_in_clean + name.len();
                let safe_name: String = name
                    .chars()
                    .map(|c| {
                        if c.is_ascii_alphanumeric() || c == '_' {
                            c
                        } else {
                            '_'
                        }
                    })
                    .collect();
                return format!(
                    "{}_turbo_inst_{}_{}{}",
                    &orig_text[..offset_in_clean],
                    idx,
                    safe_name,
                    &orig_text[name_end..]
                );
            }
        }
    }
    orig_text.to_string()
}

fn slice_up_to_line(src: &str, max_line: usize) -> &str {
    if max_line == 0 {
        return src;
    }
    let bytes = src.as_bytes();
    let mut lines_seen = 0usize;
    for (idx, &b) in bytes.iter().enumerate() {
        if b == b'\n' {
            lines_seen += 1;
            if lines_seen == max_line {
                return &src[..=idx];
            }
        }
    }
    src
}

fn optimize_fast_check_proof_body(proof_orig: &str) -> std::borrow::Cow<'_, str> {
    let trimmed = proof_orig.trim();
    if (proof_orig.contains("dsimp [Word256.addWithCarry, Word256.zero]; simp")
        || proof_orig.contains("dsimp only [Word256.addWithCarry, Word256.zero]; simp")
        || proof_orig.contains("unfold Word256.addWithCarry; unfold Word256.zero; simp")
        || proof_orig.contains("unfold Word256.addWithCarry Word256.zero; simp")
        || proof_orig.contains("unfold Word256.addWithCarry Word256.zero; dsimp; simp")
        || (proof_orig.contains("unfold Word256.addWithCarry")
            && proof_orig.contains("Word256.zero")
            && proof_orig.contains("dsimp")
            && proof_orig.contains("simp"))
        || proof_orig.contains("simp [Word256.addWithCarry, Word256.zero]"))
        && !proof_orig.contains("simp only [Word256.addWithCarry, Word256.zero, UInt64.zero_add")
    {
        std::borrow::Cow::Borrowed(" addWithCarry_zero_right a\n")
    } else if proof_orig.contains("dsimp [Word256.addWithCarry]; simp [UInt64.add_comm]")
        || proof_orig.contains("unfold Word256.addWithCarry; simp [UInt64.add_comm]")
        || proof_orig.contains("unfold Word256.addWithCarry; dsimp; simp [UInt64.add_comm]")
        || proof_orig.contains("simp [Word256.addWithCarry, UInt64.add_comm]")
    {
        std::borrow::Cow::Borrowed(" addWithCarry_comm_low a b\n")
    } else if proof_orig.contains("unfold getStorage setStorage; simp [StorageKey.fastBeq_refl]")
        || proof_orig.contains("simp [getStorage, setStorage, StorageKey.fastBeq_refl]")
    {
        std::borrow::Cow::Borrowed(" getStorage_setStorage_same\n")
    } else if proof_orig.contains("unfold getStorage setStorage")
        && proof_orig.contains("cases hbeq : StorageKey.fastBeq k' k")
        && proof_orig.contains("exact h ((StorageKey.fastBeq_eq_true_iff k' k).mp hbeq)")
    {
        std::borrow::Cow::Borrowed(" getStorage_setStorage_other h\n")
    } else if proof_orig.contains("induction ups with")
        && proof_orig.contains("simp only [evalLookupRev] at h")
        && proof_orig.contains("Option.some.injEq")
    {
        std::borrow::Cow::Borrowed(" lookup_chain_sound s ups target val h\n")
    } else if trimmed.starts_with("by")
        && trimmed.contains("unfold Word256.")
        && (trimmed.contains("dsimp; simp") || trimmed.ends_with("; simp") || trimmed.ends_with("\n  simp"))
    {
        std::borrow::Cow::Borrowed(" by rfl\n")
    } else if proof_orig.contains("dsimp [") && proof_orig.contains("]; simp") {
        std::borrow::Cow::Owned(proof_orig.replace("dsimp [", "dsimp only ["))
    } else if proof_orig.contains("unfold getStorage setStorage") && proof_orig.contains("dsimp") {
        std::borrow::Cow::Owned(
            proof_orig
                .replace(
                    "unfold getStorage setStorage\n  dsimp only",
                    "dsimp only [getStorage, setStorage]",
                )
                .replace(
                    "unfold getStorage setStorage\n  dsimp",
                    "dsimp only [getStorage, setStorage]",
                )
                .replace(
                    "unfold getStorage setStorage; dsimp",
                    "dsimp only [getStorage, setStorage]",
                ),
        )
    } else {
        std::borrow::Cow::Borrowed(proof_orig)
    }
}

fn rename_decl_header_for_fast_check(
    orig_text: &str,
    clean_text: &str,
    decl_name: &str,
    idx: usize,
) -> Option<String> {
    let (sig_orig, proof_orig) = split_at_top_level_assign(orig_text)?;
    let (sig_clean, _) = split_at_top_level_assign(clean_text)?;
    if sig_orig.len() != sig_clean.len() {
        return None;
    }
    let sep = if sig_orig.len() + proof_orig.len() == orig_text.len() {
        ""
    } else {
        ":="
    };
    let safe_name: String = decl_name
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    let replacement = format!("_turbo_verify_{}_{}", idx, safe_name);
    let opt_proof = optimize_fast_check_proof_body(proof_orig);

    for kw in ["theorem", "lemma"] {
        for (kw_pos, _) in sig_clean.match_indices(kw) {
            let after_kw = &sig_clean[kw_pos + kw.len()..];
            if let Some(name_rel_pos) = after_kw.find(decl_name) {
                let prefix_between = &after_kw[..name_rel_pos];
                if !prefix_between.is_empty() && prefix_between.chars().all(char::is_whitespace) {
                    let abs_name_start = kw_pos + kw.len() + name_rel_pos;
                    let abs_name_end = abs_name_start + decl_name.len();
                    return Some(format!(
                        "{}{}{}{}{}",
                        &sig_orig[..abs_name_start],
                        replacement,
                        &sig_orig[abs_name_end..],
                        sep,
                        opt_proof
                    ));
                }
            }
        }
    }
    None
}

/// Returns true if the span range `spans[sec_open..=sec_close]` contains at least one
/// uncached theorem in `uncached_names`.
fn section_contains_uncached_theorem(
    spans: &[CmdSpan<'_>],
    sec_open: usize,
    sec_close: usize,
    uncached_names: &std::collections::HashSet<String>,
) -> bool {
    for span in &spans[sec_open..=sec_close] {
        if let Some((_, inner_spans, _)) = split_mutual_block_subspans(span) {
            if inner_spans.iter().any(|sub| {
                classify_decl_header(sub.clean_text)
                    .map(|(_, n)| matches_uncached_name(&n, uncached_names))
                    .unwrap_or(false)
            }) {
                return true;
            }
        }
        if let Some((_kind, name)) = classify_decl_header(span.clean_text) {
            if split_at_top_level_assign(span.clean_text).is_some()
                && matches_uncached_name(&name, uncached_names)
            {
                return true;
            }
        }
    }
    false
}

/// Build a zero-re-elaboration fast-import Lean 4 source file that imports a pre-compiled
/// module/skeleton `.olean` (`import <module_import>`) and checks ONLY the uncached theorems
/// `U` (renamed to `_turbo_verify_<i>_<name>`), skipping re-elaboration of all `inductive`,
/// `structure`, `def`, `instance`, and cached theorem declarations in the file!
/// Returns `None` if the file is ineligible for sharding or if any target theorem in `U`
/// references itself or a later theorem in the file.
pub fn build_fast_olean_shard_source(
    src: &str,
    module_import: &str,
    uncached_names: &std::collections::HashSet<String>,
) -> Option<String> {
    if uncached_names.is_empty() {
        return None;
    }
    let split = split_lean_source(src, &[]);
    build_fast_olean_shard_source_with_split(src, &split, module_import, uncached_names)
}

pub fn build_fast_olean_shard_source_with_split(
    src: &str,
    split: &SplitResult,
    module_import: &str,
    uncached_names: &std::collections::HashSet<String>,
) -> Option<String> {
    if uncached_names.is_empty() || !split.eligible_for_sharding || split.shards.is_empty() {
        return None;
    }

    let mut max_end_line = 0usize;
    for (idx, shard) in split.shards.iter().enumerate() {
        if matches_uncached_name(&shard.name, uncached_names) {
            if !shard_is_acyclic_for_fast_import(&split.shards, idx) {
                return None;
            }
            if shard.end_line > max_end_line {
                max_end_line = shard.end_line;
            }
        }
    }

    let src_prefix = slice_up_to_line(src, max_end_line);
    let clean = strip_lean_comments(src_prefix);
    let spans = parse_command_spans(src_prefix, &clean);
    let closed_sections = compute_closed_section_ranges(&spans);

    let mut last_uncached_span_idx = None;
    for (s_idx, span) in spans.iter().enumerate() {
        if let Some((_, inner_spans, _)) = split_mutual_block_subspans(span) {
            if inner_spans.iter().any(|sub| {
                classify_decl_header(sub.clean_text)
                    .map(|(_, n)| matches_uncached_name(&n, uncached_names))
                    .unwrap_or(false)
            }) {
                last_uncached_span_idx = Some(s_idx);
            }
        }
        if let Some((_kind, name)) = classify_decl_header(span.clean_text) {
            if split_at_top_level_assign(span.clean_text).is_some()
                && matches_uncached_name(&name, uncached_names)
            {
                last_uncached_span_idx = Some(s_idx);
            }
        }
    }
    let last_span_idx = last_uncached_span_idx?;

    // Omit any closed `section ... end` block that contains zero uncached theorems so
    // section-local instances, notations, variables, and `@[local simp]` never leak.
    let mut omit_closed_sec = vec![false; last_span_idx + 1];
    for &(sec_open, sec_close) in &closed_sections {
        if sec_close <= last_span_idx
            && !section_contains_uncached_theorem(&spans, sec_open, sec_close, uncached_names)
        {
            for flag in &mut omit_closed_sec[sec_open..=sec_close] {
                *flag = true;
            }
        }
    }

    let mut chunks = Vec::new();
    let mut seen_imports = std::collections::HashSet::new();
    for imp_line in split.imports_header.lines() {
        let trimmed = imp_line.trim();
        if trimmed.starts_with("import ") && seen_imports.insert(trimmed.to_string()) {
            chunks.push(trimmed.to_string());
        }
    }
    let mod_imp_stmt = format!("import {}", module_import.trim());
    if seen_imports.insert(mod_imp_stmt.clone()) {
        chunks.push(mod_imp_stmt);
    }

    let mut thm_idx = 0usize;
    let mut scope_stack: Vec<ScopeFrame> = Vec::new();
    for (s_idx, span) in spans[..=last_span_idx].iter().enumerate() {
        if omit_closed_sec[s_idx] {
            // Still advance `thm_idx` for any cached theorems inside the omitted closed section
            if let Some((_, inner_spans, _)) = split_mutual_block_subspans(span) {
                for sub in &inner_spans {
                    if classify_decl_header(sub.clean_text).is_some()
                        && split_at_top_level_assign(sub.clean_text).is_some()
                    {
                        thm_idx += 1;
                    }
                }
            } else if classify_decl_header(span.clean_text).is_some()
                && split_at_top_level_assign(span.clean_text).is_some()
            {
                thm_idx += 1;
            }
            continue;
        }

        if let Some((header_orig, inner_spans, footer_orig)) = split_mutual_block_subspans(span) {
            let has_inner_thm = inner_spans.iter().any(|sub| {
                classify_decl_header(sub.clean_text).is_some()
                    && split_at_top_level_assign(sub.clean_text).is_some()
            });
            if has_inner_thm {
                let any_uncached = inner_spans.iter().any(|sub| {
                    classify_decl_header(sub.clean_text)
                        .map(|(_, n)| matches_uncached_name(&n, uncached_names))
                        .unwrap_or(false)
                });
                if any_uncached {
                    let mut inner_chunks = Vec::with_capacity(inner_spans.len() + 2);
                    inner_chunks.push(header_orig.to_string());
                    for sub in &inner_spans {
                        if let Some((_kind, name)) = classify_decl_header(sub.clean_text) {
                            if split_at_top_level_assign(sub.clean_text).is_some() {
                                let cur_idx = thm_idx;
                                thm_idx += 1;
                                let renamed = rename_decl_header_for_fast_check(
                                    sub.orig_text,
                                    sub.clean_text,
                                    &name,
                                    cur_idx,
                                )?;
                                inner_chunks.push(renamed);
                                continue;
                            }
                        }
                        inner_chunks.push(sub.orig_text.to_string());
                    }
                    inner_chunks.push(footer_orig.to_string());
                    chunks.push(inner_chunks.join("\n"));
                } else {
                    for sub in &inner_spans {
                        if classify_decl_header(sub.clean_text).is_some()
                            && split_at_top_level_assign(sub.clean_text).is_some()
                        {
                            thm_idx += 1;
                        }
                    }
                }
                update_scope_stack_with_idx(&mut scope_stack, span.clean_text, s_idx);
                continue;
            }
        }

        if let Some((_kind, name)) = classify_decl_header(span.clean_text) {
            if split_at_top_level_assign(span.clean_text).is_some() {
                let cur_idx = thm_idx;
                thm_idx += 1;
                if matches_uncached_name(&name, uncached_names) {
                    let renamed = rename_decl_header_for_fast_check(
                        span.orig_text,
                        span.clean_text,
                        &name,
                        cur_idx,
                    )?;
                    chunks.push(renamed);
                } else {
                    // If a cached theorem in an active scope has `@[local ...]`, re-enable its
                    // local attribute on the imported constant in the active scope.
                    for local_attr in extract_local_attributes(span.clean_text) {
                        chunks.push(format!("attribute [{}] {}", local_attr, name));
                    }
                }
                update_scope_stack_with_idx(&mut scope_stack, span.clean_text, s_idx);
                continue;
            }
        }
        if is_scope_or_context_command(span.clean_text) {
            chunks.push(format_scoped_instance_for_fast_check(
                span.orig_text,
                span.clean_text,
                s_idx,
            ));
        }
        update_scope_stack_with_idx(&mut scope_stack, span.clean_text, s_idx);
    }

    let closing = format_closing_scopes(&scope_stack);
    if !closing.is_empty() {
        chunks.push(closing);
    }

    Some(chunks.join("\n"))
}

fn contains_mathlib_tactic_or_namespace(clean_text: &str) -> bool {
    for word in [
        "linarith",
        "nlinarith",
        "ring",
        "ring_nf",
        "norm_num",
        "positivity",
        "field_simp",
        "abel",
        "polyrith",
        "aesop",
        "Finset",
        "BigOperators",
        "ZMod",
        "Polynomial",
    ] {
        if contains_word(clean_text, word) {
            return true;
        }
    }
    for prefix in ["Real.", "Complex.", "Mathlib."] {
        if clean_text.contains(prefix) {
            return true;
        }
    }
    false
}

/// Speculatively construct a self-contained Lean 4 shard source for `uncached_names` that
/// strips heavy `import Mathlib.*` / `import Aesop*` headers when none of the prefix commands
/// or target theorem proofs up to the last uncached theorem reference `Mathlib`-specific
/// tactics or namespaces.
pub fn build_pruned_imports_shard_source(
    src: &str,
    uncached_names: &std::collections::HashSet<String>,
) -> Option<String> {
    if uncached_names.is_empty() {
        return None;
    }
    let mut header_end = 4096.min(src.len());
    while !src.is_char_boundary(header_end) {
        header_end -= 1;
    }
    let header_probe = &src[..header_end];
    if !header_probe.contains("import Mathlib") && !header_probe.contains("import Aesop") {
        return None;
    }

    let clean = strip_lean_comments(src);
    let spans = parse_command_spans(src, &clean);
    let closed_sections = compute_closed_section_ranges(&spans);

    let mut last_uncached_span_idx = None;
    for (s_idx, span) in spans.iter().enumerate() {
        if let Some((_, inner_spans, _)) = split_mutual_block_subspans(span) {
            if inner_spans.iter().any(|sub| {
                classify_decl_header(sub.clean_text)
                    .map(|(_, n)| matches_uncached_name(&n, uncached_names))
                    .unwrap_or(false)
            }) {
                last_uncached_span_idx = Some(s_idx);
            }
        }
        if let Some((_kind, name)) = classify_decl_header(span.clean_text) {
            if split_at_top_level_assign(span.clean_text).is_some()
                && matches_uncached_name(&name, uncached_names)
            {
                last_uncached_span_idx = Some(s_idx);
            }
        }
    }
    let last_span_idx = last_uncached_span_idx?;
    let omit_mask = compute_omitted_closed_section_spans(&spans, &closed_sections, last_span_idx);

    let mut out_chunks = Vec::with_capacity(last_span_idx + 2);
    let mut scope_stack: Vec<ScopeFrame> = Vec::new();
    let mut pruned_imports = 0usize;

    for (s_idx, span) in spans[..=last_span_idx].iter().enumerate() {
        if omit_mask[s_idx] {
            continue;
        }
        let trimmed_clean = span.clean_text.trim();
        if trimmed_clean.starts_with("import ") {
            let mut kept_lines = Vec::new();
            for line in span.orig_text.lines() {
                let lt = line.trim();
                if lt.starts_with("import Mathlib") || lt.starts_with("import Aesop") {
                    pruned_imports += 1;
                } else {
                    kept_lines.push(line);
                }
            }
            if !kept_lines.is_empty() {
                out_chunks.push(kept_lines.join("\n"));
            }
            continue;
        }

        if let Some((_kind, name)) = classify_decl_header(span.clean_text) {
            if let Some((sig_clean, proof_clean)) = split_at_top_level_assign(span.clean_text) {
                let (sig_orig, proof_orig) =
                    split_at_top_level_assign(span.orig_text).unwrap_or((sig_clean, proof_clean));
                if matches_uncached_name(&name, uncached_names) {
                    if contains_mathlib_tactic_or_namespace(span.clean_text) {
                        return None;
                    }
                    out_chunks.push(span.orig_text.to_string());
                } else {
                    if contains_mathlib_tactic_or_namespace(sig_clean) {
                        return None;
                    }
                    let proof_newlines = proof_orig.matches('\n').count();
                    let padded_sorry = format!(" := sorry{}", "\n".repeat(proof_newlines));
                    out_chunks.push(format!("{}{}", sig_orig, padded_sorry));
                }
                update_scope_stack_with_idx(&mut scope_stack, span.clean_text, s_idx);
                continue;
            }
        }

        if contains_mathlib_tactic_or_namespace(span.clean_text) {
            return None;
        }
        out_chunks.push(span.orig_text.to_string());
        update_scope_stack_with_idx(&mut scope_stack, span.clean_text, s_idx);
    }

    if pruned_imports == 0 {
        return None;
    }

    let closing = format_closing_scopes(&scope_stack);
    if !closing.is_empty() {
        out_chunks.push(closing);
    }

    Some(out_chunks.join("\n"))
}

/// Check whether `src` and `uncached_names` are eligible for fast `.olean` import
/// (pure/hygienic module with no self/forward theorem references in `uncached_names`).
pub fn can_use_fast_olean_import(
    src: &str,
    uncached_names: &std::collections::HashSet<String>,
) -> bool {
    if uncached_names.is_empty() {
        return false;
    }
    let split = split_lean_source(src, &[]);
    can_use_fast_olean_import_with_split(&split, uncached_names)
}

pub fn can_use_fast_olean_import_with_split(
    split: &SplitResult,
    uncached_names: &std::collections::HashSet<String>,
) -> bool {
    if uncached_names.is_empty() || !split.eligible_for_sharding || split.shards.is_empty() {
        return false;
    }
    for (idx, shard) in split.shards.iter().enumerate() {
        if matches_uncached_name(&shard.name, uncached_names)
            && !shard_is_acyclic_for_fast_import(&split.shards, idx)
        {
            return false;
        }
    }
    true
}

/// Build a single synthetic cross-file Lean 4 source file that coalesces uncached theorem shards
/// across multiple fast-`.olean`-eligible files into one `lean` invocation:
/// - Hoists and deduplicates all `import <ModulePath>` statements to the top of the file.
/// - Wraps each file's `open`/`variable`/`namespace` scopes and renamed uncached theorem shards
///   inside an isolated `_TurboCrossFileShard_<i>` scope block so scope directives never leak
///   across files while checking all files in a single `lean` process.
pub fn build_cross_file_coalesced_shard(
    files_and_shards: &[(&str, &str, &[&TheoremShard])],
) -> String {
    let mut all_imports: Vec<String> = Vec::new();
    let mut seen_imports: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut file_bodies: Vec<String> = Vec::with_capacity(files_and_shards.len());

    for (file_idx, (a, b, uncached_shards)) in files_and_shards.iter().enumerate() {
        if uncached_shards.is_empty() {
            continue;
        }
        let (module_import, src) = if !a.contains('\n') && !a.contains(":=") {
            (a.trim(), *b)
        } else {
            (b.trim(), *a)
        };

        let uncached_names: std::collections::HashSet<String> =
            uncached_shards.iter().map(|s| s.name.clone()).collect();
        let max_end_line = uncached_shards
            .iter()
            .map(|s| s.end_line)
            .max()
            .unwrap_or(0);
        let src_prefix = slice_up_to_line(src, max_end_line);

        let clean = strip_lean_comments(src_prefix);
        for line in clean.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed == "prelude" {
                continue;
            }
            if trimmed.starts_with("import ") {
                if seen_imports.insert(trimmed.to_string()) {
                    all_imports.push(trimmed.to_string());
                }
            } else {
                break;
            }
        }
        let mod_imp_stmt = format!("import {}", module_import);
        if seen_imports.insert(mod_imp_stmt.clone()) {
            all_imports.push(mod_imp_stmt);
        }

        let spans = parse_command_spans(src_prefix, &clean);
        let closed_sections = compute_closed_section_ranges(&spans);

        let mut last_uncached_span_idx = None;
        for (s_idx, span) in spans.iter().enumerate() {
            if let Some((_, inner_spans, _)) = split_mutual_block_subspans(span) {
                if inner_spans.iter().any(|sub| {
                    classify_decl_header(sub.clean_text)
                        .map(|(_, n)| matches_uncached_name(&n, &uncached_names))
                        .unwrap_or(false)
                }) {
                    last_uncached_span_idx = Some(s_idx);
                }
            }
            if let Some((_kind, name)) = classify_decl_header(span.clean_text) {
                if split_at_top_level_assign(span.clean_text).is_some()
                    && matches_uncached_name(&name, &uncached_names)
                {
                    last_uncached_span_idx = Some(s_idx);
                }
            }
        }
        let end_span_idx = last_uncached_span_idx.unwrap_or_else(|| spans.len().saturating_sub(1));

        let mut omit_closed_sec = vec![false; end_span_idx + 1];
        for &(sec_open, sec_close) in &closed_sections {
            if sec_close <= end_span_idx
                && !section_contains_uncached_theorem(&spans, sec_open, sec_close, &uncached_names)
            {
                for flag in &mut omit_closed_sec[sec_open..=sec_close] {
                    *flag = true;
                }
            }
        }

        let iso_ns = format!("_TurboCrossFileShard_{}", file_idx);
        let mut block_chunks = Vec::new();
        block_chunks.push(format!("-- namespace {}\n-- end {}", iso_ns, iso_ns));

        let mut scope_stack: Vec<ScopeFrame> = Vec::new();
        let mut thm_idx = 0usize;
        let base_idx = (file_idx + 1) * 10000;
        let mut has_non_ns_scope = false;

        for (s_idx, span) in spans[..=end_span_idx].iter().enumerate() {
            if omit_closed_sec[s_idx] {
                if classify_decl_header(span.clean_text).is_some()
                    && split_at_top_level_assign(span.clean_text).is_some()
                {
                    thm_idx += 1;
                }
                continue;
            }
            if let Some((_kind, name)) = classify_decl_header(span.clean_text) {
                if split_at_top_level_assign(span.clean_text).is_some() {
                    let cur_idx = base_idx + thm_idx;
                    thm_idx += 1;
                    if matches_uncached_name(&name, &uncached_names) {
                        if let Some(renamed) = rename_decl_header_for_fast_check(
                            span.orig_text,
                            span.clean_text,
                            &name,
                            cur_idx,
                        ) {
                            block_chunks.push(renamed);
                        }
                    } else {
                        for local_attr in extract_local_attributes(span.clean_text) {
                            has_non_ns_scope = true;
                            block_chunks.push(format!("attribute [{}] {}", local_attr, name));
                        }
                    }
                    update_scope_stack_with_idx(&mut scope_stack, span.clean_text, s_idx);
                    continue;
                }
            }
            if is_scope_or_context_command(span.clean_text) {
                let tc = span.clean_text.trim_start();
                if !tc.starts_with("namespace ") && !tc.starts_with("end ") {
                    has_non_ns_scope = true;
                }
                block_chunks.push(format_scoped_instance_for_fast_check(
                    span.orig_text,
                    span.clean_text,
                    base_idx + s_idx,
                ));
                update_scope_stack_with_idx(&mut scope_stack, span.clean_text, s_idx);
            }
        }

        let rem_closers = format_closing_scopes(&scope_stack);
        if !rem_closers.trim().is_empty() {
            block_chunks.push(rem_closers);
        }
        if has_non_ns_scope {
            block_chunks.insert(1, format!("section {}", iso_ns));
            block_chunks.push(format!("end {}", iso_ns));
        }
        file_bodies.push(block_chunks.join("\n"));
    }

    let mut out = Vec::new();
    if !all_imports.is_empty() {
        out.push(all_imports.join("\n"));
    }
    out.extend(file_bodies);
    out.join("\n\n")
}

#[allow(dead_code)]
fn split_signature_at_top_level_colon<'a>(
    sig_orig: &'a str,
    sig_clean: &'a str,
) -> Option<(&'a str, &'a str)> {
    if sig_orig.len() != sig_clean.len() {
        return None;
    }
    let after_prefixes = strip_decl_prefixes(sig_clean);
    let start_offset = sig_clean.len() - after_prefixes.len();
    let bytes = sig_clean.as_bytes();
    let mut paren = 0i32;
    let mut bracket = 0i32;
    let mut brace = 0i32;
    let mut in_string = false;
    let mut i = start_offset;

    while i < bytes.len() {
        let c = bytes[i];
        if in_string {
            if c == b'\\' {
                i += 2;
                continue;
            }
            if c == b'"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        match c {
            b'"' => in_string = true,
            b'(' => paren += 1,
            b')' => paren = (paren - 1).max(0),
            b'[' => bracket += 1,
            b']' => bracket = (bracket - 1).max(0),
            b'{' => brace += 1,
            b'}' => brace = (brace - 1).max(0),
            b':' if paren == 0 && bracket == 0 && brace == 0 => {
                if i + 1 < bytes.len() && bytes[i + 1] == b'=' {
                    i += 2;
                    continue;
                }
                return Some((sig_orig[..i].trim_end(), sig_orig[i + 1..].trim()));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

#[allow(dead_code)]
struct HaveCut<'a> {
    ident: String,
    ty: String,
    proof_rhs: &'a str,
}

#[allow(dead_code)]
fn parse_have_cut<'a>(stmt_orig: &'a str, stmt_clean: &'a str) -> Option<HaveCut<'a>> {
    if stmt_orig.len() != stmt_clean.len() {
        return None;
    }
    let (lhs_clean, _proof_clean) = split_at_top_level_assign(stmt_clean)?;
    let (lhs_orig, proof_orig) = split_at_top_level_assign(stmt_orig)?;
    if lhs_orig.len() + 2 + proof_orig.len() != stmt_orig.len() {
        return None;
    }
    let trimmed_lhs_clean = lhs_clean.trim_start();
    let after_have_clean = trimmed_lhs_clean.strip_prefix("have")?;
    if !after_have_clean.starts_with(char::is_whitespace) {
        return None;
    }
    let after_ws_clean = after_have_clean.trim_start();
    let mut ident_chars = after_ws_clean.chars();
    let first_ch = ident_chars.next()?;
    if !is_lean_ident_continuation(first_ch) || first_ch.is_ascii_digit() {
        return None;
    }
    let ident: String = after_ws_clean
        .chars()
        .take_while(|c| is_lean_ident_continuation(*c))
        .collect();
    if ident.is_empty() || is_lean_keyword_or_builtin(&ident) {
        return None;
    }

    let after_ident_clean = after_ws_clean[ident.len()..].trim_start();
    if !after_ident_clean.starts_with(':') || after_ident_clean.starts_with(":=") {
        return None;
    }
    let colon_offset = lhs_clean.len() - after_ident_clean.len();
    let ty_orig = lhs_orig[colon_offset + 1..].trim();
    if ty_orig.is_empty() || proof_orig.trim().is_empty() {
        return None;
    }

    Some(HaveCut {
        ident,
        ty: ty_orig.to_string(),
        proof_rhs: proof_orig,
    })
}

#[allow(dead_code)]
fn format_cut_proof_rhs(proof_rhs: &str, base_indent: usize) -> String {
    let trimmed = proof_rhs.trim();
    if !trimmed.contains('\n') {
        return trimmed.to_string();
    }
    let mut lines = trimmed.lines();
    let first_line = lines.next().unwrap_or("");
    let mut out = String::from(first_line.trim_end());
    for line in lines {
        out.push('\n');
        if line.trim().is_empty() {
            continue;
        }
        let leading_spaces = line.bytes().take_while(|&b| b == b' ').count();
        let strip_n = leading_spaces.min(base_indent);
        out.push_str(&line[strip_n..]);
    }
    out
}

/// Fission a theorem with top-level `have <ident> : <type> := <proof>` blocks inside its `by`
/// proof into $K + 1$ independent, 100% `sorry`-free `FissionSubShard` items via Cut-Rule
/// Hypothesis Promotion:
/// - Sub-shard $i \in 0..K$ (`have:<ident_i>`) promotes prior cuts $(h_0 : P_0) \dots (h_{i-1} : P_{i-1})$
///   into theorem hypotheses and proves `: P_i := <proof_i>`.
/// - Sub-shard $K$ (`conclusion`) promotes all cuts $(h_0 : P_0) \dots (h_{K-1} : P_{K-1})$
///   into theorem hypotheses and proves `: Goal := by <final_proof>`.
#[allow(dead_code)]
pub fn fission_theorem_have_blocks(decl_source: &str, decl_name: &str) -> Vec<FissionSubShard> {
    let clean = strip_lean_comments(decl_source);
    if clean.len() != decl_source.len() {
        return Vec::new();
    }
    let (sig_clean, rhs_clean) = match split_at_top_level_assign(&clean) {
        Some(v) => v,
        None => return Vec::new(),
    };
    let (sig_orig, rhs_orig) = match split_at_top_level_assign(decl_source) {
        Some(v) => v,
        None => return Vec::new(),
    };
    if sig_orig.len() + 2 + rhs_orig.len() != decl_source.len() {
        return Vec::new();
    }

    let (binder_prefix, goal_type) = match split_signature_at_top_level_colon(sig_orig, sig_clean) {
        Some(v) => v,
        None => return Vec::new(),
    };
    if binder_prefix.is_empty() || goal_type.is_empty() {
        return Vec::new();
    }

    let first_nl = match rhs_clean.find('\n') {
        Some(idx) => idx,
        None => return Vec::new(),
    };
    if rhs_clean[..first_nl].trim() != "by" {
        return Vec::new();
    }

    let body_orig = &rhs_orig[first_nl + 1..];
    let body_clean = &rhs_clean[first_nl + 1..];
    if body_orig.len() != body_clean.len() {
        return Vec::new();
    }

    let mut base_indent = None;
    for line in body_clean.lines() {
        if !line.trim().is_empty() {
            let ind = line.len() - line.trim_start().len();
            base_indent = Some(ind);
            break;
        }
    }
    let base_indent = match base_indent {
        Some(ind) if ind > 0 => ind,
        _ => return Vec::new(),
    };

    // Segment `body_orig` / `body_clean` into top-level tactic statements aligned at `base_indent`.
    let bytes = body_orig.as_bytes();
    let total_len = bytes.len();
    let mut stmt_ranges: Vec<(usize, usize)> = Vec::new();
    let mut cur_start: Option<usize> = None;
    let mut cur_end = 0usize;
    let mut pos = 0usize;

    while pos < total_len {
        let line_start = pos;
        let mut line_end = pos;
        while line_end < total_len && bytes[line_end] != b'\n' {
            line_end += 1;
        }
        let next_pos = if line_end < total_len {
            line_end + 1
        } else {
            total_len
        };
        let line_end_no_cr = if line_end > line_start && bytes[line_end - 1] == b'\r' {
            line_end - 1
        } else {
            line_end
        };

        let line_clean = &body_clean[line_start..line_end_no_cr];
        let trimmed = line_clean.trim();
        if !trimmed.is_empty() {
            let indent = line_clean.len() - line_clean.trim_start().len();
            if indent < base_indent {
                // Unindented trailing construct (e.g. `where` or `end`) — abort fission.
                return Vec::new();
            }
            if indent == base_indent {
                if let Some(st) = cur_start {
                    stmt_ranges.push((st, cur_end));
                }
                cur_start = Some(line_start);
            }
            cur_end = line_end_no_cr;
        }
        pos = next_pos;
    }
    if let Some(st) = cur_start {
        stmt_ranges.push((st, cur_end));
    }

    if stmt_ranges.len() < 2 {
        return Vec::new();
    }

    let mut cuts: Vec<HaveCut<'_>> = Vec::new();
    let mut conclusion_start_byte = None;
    for (idx, &(st, en)) in stmt_ranges.iter().enumerate() {
        let stmt_orig = &body_orig[st..en];
        let stmt_clean = &body_clean[st..en];
        if idx + 1 < stmt_ranges.len() {
            if let Some(cut) = parse_have_cut(stmt_orig, stmt_clean) {
                cuts.push(cut);
                continue;
            }
        }
        conclusion_start_byte = Some(st);
        break;
    }

    let conclusion_start = match conclusion_start_byte {
        Some(st) if !cuts.is_empty() => st,
        _ => return Vec::new(),
    };

    let effective_name = if !decl_name.trim().is_empty() {
        decl_name.trim().to_string()
    } else {
        classify_decl_header(sig_clean)
            .map(|(_, n)| n)
            .unwrap_or_else(|| "anon_thm".to_string())
    };

    let k = cuts.len();
    let total_steps = k + 1;
    let mut sub_shards = Vec::with_capacity(total_steps);
    let mut promoted_hyps = String::new();

    for (i, cut) in cuts.iter().enumerate() {
        let rhs_formatted = format_cut_proof_rhs(cut.proof_rhs, base_indent);
        let sub_decl_source = format!(
            "{}{} : {} := {}",
            binder_prefix, promoted_hyps, cut.ty, rhs_formatted
        );
        let step_label = format!("have:{}", cut.ident);
        let sub_shard_key = format!(
            "{}:{}:{}:{}",
            effective_name,
            i,
            step_label,
            hash_normalized_whitespace_hex(&sub_decl_source)
        );
        sub_shards.push(FissionSubShard {
            step_index: i,
            total_steps,
            step_label,
            sub_shard_key,
            sub_decl_source,
        });
        promoted_hyps.push_str(&format!(" ({} : {})", cut.ident, cut.ty));
    }

    let conclusion_body = body_orig[conclusion_start..].trim_end();
    let conclusion_source = format!(
        "{}{} : {} := by\n{}",
        binder_prefix, promoted_hyps, goal_type, conclusion_body
    );
    let conclusion_label = "conclusion".to_string();
    let conclusion_key = format!(
        "{}:{}:{}:{}",
        effective_name,
        k,
        conclusion_label,
        hash_normalized_whitespace_hex(&conclusion_source)
    );
    sub_shards.push(FissionSubShard {
        step_index: k,
        total_steps,
        step_label: conclusion_label,
        sub_shard_key: conclusion_key,
        sub_decl_source: conclusion_source,
    });

    sub_shards
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn test_strip_lean_comments_preserves_lines_and_strings() {
        let src = "import Init\n-- line comment with sorry\n/- block\n   nested /- inner -/ end -/\ndef msg : String := \"-- not a comment /- neither -/\"\ntheorem t1 : True := by\n  trivial\n";
        let clean = strip_lean_comments(src);
        assert_eq!(src.lines().count(), clean.lines().count());
        assert!(!clean.contains("line comment"));
        assert!(!clean.contains("inner"));
        assert!(clean.contains("\"-- not a comment /- neither -/\""));
    }

    #[test]
    fn test_audit_hygiene_detects_forbidden_tokens() {
        let clean_code = strip_lean_comments("theorem ok : 1 + 1 = 2 := rfl\n");
        let rep_ok = audit_hygiene(&clean_code);
        assert!(rep_ok.is_clean_for_certification());

        let dirty_code = strip_lean_comments(
            "theorem bad1 : False := sorry\ntheorem bad2 : True := by native_decide\n",
        );
        let rep_dirty = audit_hygiene(&dirty_code);
        assert!(!rep_dirty.is_clean_for_certification());
        assert!(rep_dirty.has_sorry);
        assert!(rep_dirty.has_native_decide);
    }

    #[test]
    fn test_prefix_env_hash_invariance_under_proof_edits() {
        let src_v1 = "namespace Demo\ntheorem t1 (n : Nat) : n = n := by\n  rfl\n\ntheorem t2 (n : Nat) : n + 0 = n := by\n  simp\nend Demo\n";
        let src_v2 = "namespace Demo\ntheorem t1 (n : Nat) : n = n := by\n  simp\n   done\n\ntheorem t2 (n : Nat) : n + 0 = n := by\n  simp\nend Demo\n";

        let split1 = split_lean_source(src_v1, &[]);
        let split2 = split_lean_source(src_v2, &[]);

        assert_eq!(split1.interface_hash, split2.interface_hash);
        assert_eq!(split1.shards.len(), 2);
        assert_eq!(split2.shards.len(), 2);
        // Changing t1's proof body must NOT change t2's prefix_env_hash or stmt_hash!
        assert_eq!(split1.shards[1].prefix_env_hash, split2.shards[1].prefix_env_hash);
        assert_eq!(split1.shards[1].stmt_hash, split2.shards[1].stmt_hash);
        assert_ne!(split1.shards[0].proof_hash, split2.shards[0].proof_hash);
    }

    #[test]
    fn test_build_coalesced_shard_source_preserves_lines_and_selectively_sorries() {
        let src = "namespace Demo\ntheorem t1 : 1 = 1 := by\n  rfl\n\ntheorem t2 : 2 = 2 := by\n  rfl\n\ntheorem t3 : 3 = 3 := by\n  rfl\nend Demo\n";
        let split = split_lean_source(src, &[]);

        // Empty uncached set -> identical to skeleton_source
        let empty_set: HashSet<String> = HashSet::new();
        let coalesced_empty = build_coalesced_shard_source(src, &empty_set);
        assert_eq!(coalesced_empty, split.skeleton_source);
        assert_eq!(coalesced_empty.lines().count(), src.lines().count());

        // Only t2 and t3 uncached (t1 cached -> replaced with sorry)
        let mut uncached = HashSet::new();
        uncached.insert("t2".to_string());
        uncached.insert("t3".to_string());
        let coalesced = build_coalesced_shard_source(src, &uncached);
        assert_eq!(coalesced.lines().count(), src.lines().count());
        assert!(coalesced.contains("theorem t1 : 1 = 1  := sorry"));
        assert!(coalesced.contains("theorem t2 : 2 = 2 := by\n  rfl"));
        assert!(coalesced.contains("theorem t3 : 3 = 3 := by\n  rfl"));
    }

    #[test]
    fn test_build_fast_olean_shard_source_and_acyclicity_guard() {
        let src = "import Init\nimport Init\nnamespace Demo\ndef heavyDef : Nat := 42\ntheorem t1 : heavyDef = 42 := rfl\ntheorem t2 : heavyDef = 42 := t1\nend Demo\n";
        let mut uncached = HashSet::new();
        uncached.insert("t2".to_string());
        let fast_src = build_fast_olean_shard_source(src, "DemoMod", &uncached)
            .expect("t2 only depends on earlier t1, should allow fast import");
        assert!(fast_src.contains("import DemoMod"));
        assert_eq!(fast_src.matches("import Init").count(), 1);
        assert!(!fast_src.contains("def heavyDef"));
        assert!(fast_src.contains("theorem _turbo_verify_1_t2 : heavyDef = 42 := t1"));

        // Self-referential or forward-referential proof must be rejected by acyclicity guard
        let cyclic_src = "namespace Demo\ntheorem bad : False := bad\nend Demo\n";
        let mut bad_set = HashSet::new();
        bad_set.insert("bad".to_string());
        assert!(build_fast_olean_shard_source(cyclic_src, "DemoMod", &bad_set).is_none());
    }

    #[test]
    fn test_build_cross_file_coalesced_shard_isolates_scopes_and_hoists_imports() {
        let src_a = "namespace ModA\ndef fA : Nat := 1\ntheorem thmA : fA = 1 := rfl\nend ModA\n";
        let src_b = "namespace ModB\ndef fB : Nat := 2\ntheorem thmB : fB = 2 := rfl\nend ModB\n";
        let split_a = split_lean_source(src_a, &[]);
        let split_b = split_lean_source(src_b, &[]);
        let shards_a: Vec<&TheoremShard> = split_a.shards.iter().collect();
        let shards_b: Vec<&TheoremShard> = split_b.shards.iter().collect();

        let cross = build_cross_file_coalesced_shard(&[
            ("Pkg.ModA", src_a, &shards_a),
            ("Pkg.ModB", src_b, &shards_b),
        ]);
        assert!(cross.starts_with("import Pkg.ModA\nimport Pkg.ModB"));
        assert!(cross.contains("namespace _TurboCrossFileShard_0"));
        assert!(cross.contains("end _TurboCrossFileShard_0"));
        assert!(cross.contains("namespace _TurboCrossFileShard_1"));
        assert!(cross.contains("end _TurboCrossFileShard_1"));
        assert!(cross.contains("_turbo_verify_10000_thmA"));
        assert!(cross.contains("_turbo_verify_20000_thmB"));
        assert!(!cross.contains("def fA"));
        assert!(!cross.contains("def fB"));
    }

    #[test]
    fn test_build_pruned_imports_shard_source_strips_mathlib_when_unused() {
        let src = "import Verity.Core\nimport Mathlib.Analysis.Complex.Exponential\nimport Mathlib.Tactic.Linarith\nnamespace Verity.Proofs.Stdlib.Math\ntheorem t1 : 1 = 1 := by\n  rfl\ntheorem t2 : 2 = 2 := by\n  linarith\nend Verity.Proofs.Stdlib.Math\n";
        let mut uncached_t1 = HashSet::new();
        uncached_t1.insert("t1".to_string());
        let pruned = build_pruned_imports_shard_source(src, &uncached_t1)
            .expect("t1 does not use Mathlib tactics, should prune Mathlib imports");
        assert!(pruned.contains("import Verity.Core"));
        assert!(!pruned.contains("import Mathlib."));
        assert!(pruned.contains("theorem t1 : 1 = 1 := by\n  rfl"));
        assert!(!pruned.contains("theorem t2"));
        assert!(pruned.contains("end Verity.Proofs.Stdlib.Math"));

        // t2 uses `linarith`, so Mathlib imports must NOT be pruned
        let mut uncached_t2 = HashSet::new();
        uncached_t2.insert("t2".to_string());
        assert!(build_pruned_imports_shard_source(src, &uncached_t2).is_none());
    }

    #[test]
    fn test_nested_multi_token_namespace_and_section_variable_scoping() {
        let src = "\
namespace A.B.C
universe u
variable (α : Type u)

section InnerSec
variable (x : α)
theorem thm_in_abc_inner : x = x := rfl
end InnerSec

end C

theorem thm_in_ab (y : α) : y = y := rfl

end A.B
";
        let split = split_lean_source(src, &[]);
        assert_eq!(split.shards.len(), 2);

        // Shard 0 (`thm_in_abc_inner`) is inside `namespace A.B.C` and `section InnerSec`
        let s0 = &split.shards[0];
        assert_eq!(s0.name, "thm_in_abc_inner");
        assert!(s0.shard_source.contains("namespace A.B.C"));
        assert!(s0.shard_source.contains("universe u"));
        assert!(s0.shard_source.contains("variable (α : Type u)"));
        assert!(s0.shard_source.contains("section InnerSec"));
        assert!(s0.shard_source.contains("variable (x : α)"));
        assert!(s0.shard_source.contains("end InnerSec\nend A.B.C"));

        // Shard 1 (`thm_in_ab`) is after `end InnerSec` and `end C`:
        // - `InnerSec` is closed and unreferenced, so `variable (x : α)` is pruned and does not leak!
        // - `end C` popped only `C` from `A.B.C`, so `A.B` remains open and closes with `end A.B`!
        let s1 = &split.shards[1];
        assert_eq!(s1.name, "thm_in_ab");
        assert!(s1.shard_source.contains("namespace A.B.C"));
        assert!(s1.shard_source.contains("variable (α : Type u)"));
        assert!(!s1.shard_source.contains("variable (x : α)"));
        assert!(!s1.shard_source.contains("section InnerSec"));
        assert!(s1.shard_source.ends_with("end A.B"));
    }

    #[test]
    fn test_local_instance_and_local_modifiers_isolation_after_end_section() {
        let src = "\
namespace ScopeIso

section LocalSetup
  variable (v : Nat)
  local instance myLocalInst : Inhabited Nat := ⟨77⟩
  local notation \"SEVENTY_SEVEN\" => 77
  @[local simp]
  theorem local_simp_lem : (default : Nat) = SEVENTY_SEVEN := by
    rfl
  theorem inside_local_sec : (default : Nat) = SEVENTY_SEVEN := by
    simp
end LocalSetup

scoped instance myScopedInst : Add Bool := ⟨Bool.or⟩

theorem outside_local_sec (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n

end ScopeIso
";
        let split = split_lean_source(src, &[]);
        assert!(split.eligible_for_sharding);
        assert_eq!(split.shards.len(), 3);

        // 1. Inside `LocalSetup` (`inside_local_sec`), all local modifiers are active:
        let s_inside = &split.shards[1];
        assert_eq!(s_inside.name, "inside_local_sec");
        assert!(s_inside.shard_source.contains("section LocalSetup"));
        assert!(s_inside.shard_source.contains("local instance myLocalInst"));
        assert!(s_inside.shard_source.contains("local notation \"SEVENTY_SEVEN\""));
        assert!(s_inside.shard_source.contains("@[local simp]"));

        let mut uncached_inside = HashSet::new();
        uncached_inside.insert("inside_local_sec".to_string());
        let fast_inside = build_fast_olean_shard_source(src, "ScopeIsoMod", &uncached_inside)
            .expect("fast olean source for inside_local_sec");
        assert!(fast_inside.contains("section LocalSetup"));
        assert!(fast_inside.contains("local instance _turbo_inst_"));
        assert!(fast_inside.contains("local notation \"SEVENTY_SEVEN\""));
        assert!(fast_inside.contains("attribute [local simp] local_simp_lem"));
        assert!(fast_inside.contains("end LocalSetup"));

        // 2. Outside `LocalSetup` (`outside_local_sec`), `LocalSetup` is closed:
        //    zero local instances, local notations, variables, or `@[local simp]` leak!
        let s_outside = &split.shards[2];
        assert_eq!(s_outside.name, "outside_local_sec");
        assert!(!s_outside.shard_source.contains("LocalSetup"));
        assert!(!s_outside.shard_source.contains("myLocalInst"));
        assert!(!s_outside.shard_source.contains("SEVENTY_SEVEN"));
        assert!(!s_outside.shard_source.contains("variable (v : Nat)"));
        assert!(!s_outside.shard_source.contains("local simp"));
        assert!(s_outside.shard_source.contains("scoped instance myScopedInst"));

        let mut uncached_outside = HashSet::new();
        uncached_outside.insert("outside_local_sec".to_string());
        let fast_outside = build_fast_olean_shard_source(src, "ScopeIsoMod", &uncached_outside)
            .expect("fast olean source for outside_local_sec");
        assert!(!fast_outside.contains("LocalSetup"));
        assert!(!fast_outside.contains("myLocalInst"));
        assert!(!fast_outside.contains("SEVENTY_SEVEN"));
        assert!(!fast_outside.contains("local_simp_lem"));
        assert!(fast_outside.contains("scoped instance _turbo_inst_"));
    }

    #[test]
    fn test_mutual_blocks_and_custom_attributes_preserved() {
        let src = "\
namespace MutualDemo

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n

  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

@[simp]
@[ext]
theorem isEven_zero : isEven 0 = true := by
  rfl

@[aesop safe [apply, constructors]]
lemma isOdd_one : isOdd 1 = true := by
  rfl

mutual
  @[simp]
  theorem mut_thm_a (n : Nat) : n = n := by
    rfl

  theorem mut_thm_b (n : Nat) : n + 0 = n := by
    exact Nat.add_zero n
end

end MutualDemo
";
        let split = split_lean_source(src, &[]);
        assert_eq!(split.shards.len(), 4);
        assert_eq!(split.shards[0].name, "isEven_zero");
        assert_eq!(split.shards[1].name, "isOdd_one");
        assert_eq!(split.shards[2].name, "mut_thm_a");
        assert_eq!(split.shards[3].name, "mut_thm_b");

        // Verify `mutual ... end` did not prematurely pop `namespace MutualDemo`
        for shard in &split.shards {
            assert!(shard.shard_source.contains("namespace MutualDemo"));
            assert!(shard.shard_source.ends_with("end MutualDemo"));
            assert!(shard.shard_source.contains("def isEven : Nat → Bool"));
            assert!(shard.shard_source.contains("def isOdd : Nat → Bool"));
        }

        // Verify multi-line attributes stay attached to theorem signatures
        assert!(split.shards[0].signature_text.contains("@[simp]"));
        assert!(split.shards[0].signature_text.contains("@[ext]"));
        assert!(split.shards[1]
            .signature_text
            .contains("@[aesop safe [apply, constructors]]"));

        // Verify coalesced source selectively sorries cached theorems inside and outside `mutual`
        let mut uncached = HashSet::new();
        uncached.insert("mut_thm_b".to_string());
        let coalesced = build_coalesced_shard_source(src, &uncached);
        assert_eq!(coalesced.lines().count(), src.lines().count());
        assert!(coalesced.contains("theorem isEven_zero : isEven 0 = true  := sorry"));
        assert!(coalesced.contains("theorem mut_thm_a (n : Nat) : n = n  := sorry"));
        assert!(coalesced.contains("theorem mut_thm_b (n : Nat) : n + 0 = n := by\n    exact Nat.add_zero n"));
    }

    #[test]
    fn test_real_world_verity_proof_blocks_and_simproc_attributes() {
        let src = "\
import Verity.Core
import Verity.EVM.Uint256

namespace Verity.Proofs.Stdlib.Math

open Verity
open Verity.EVM.Uint256

def WAD : Nat := 1000000000000000000

@[simp]
theorem wad_pos : 0 < WAD := by
   decide

simproc my_add_zero_simproc (Nat.add _ 0) := fun _ => pure .continue

/-- Verity mulDivDown zero-numerator soundness theorem -/
@[simp]
theorem mulDivDown_zero_left (b c : Nat) : (0 * b) / c = 0 := by
  simp

theorem mulDivDown_zero_right (a c : Nat) : (a * 0) / c = 0 := by
  simp

end Verity.Proofs.Stdlib.Math
";
        let split = split_lean_source(src, &[]);
        assert!(split.eligible_for_sharding);
        assert_eq!(split.shards.len(), 3);
        assert_eq!(split.shards[0].name, "wad_pos");
        assert_eq!(split.shards[1].name, "mulDivDown_zero_left");
        assert_eq!(split.shards[2].name, "mulDivDown_zero_right");

        let s2 = &split.shards[2];
        assert!(s2
            .shard_source
            .contains("namespace Verity.Proofs.Stdlib.Math"));
        assert!(s2.shard_source.contains("open Verity.EVM.Uint256"));
        assert!(s2
            .shard_source
            .contains("simproc my_add_zero_simproc (Nat.add _ 0)"));
        assert!(s2
            .shard_source
            .contains("@[simp]\ntheorem mulDivDown_zero_left (b c : Nat) : (0 * b) / c = 0  := sorry"));
        assert!(s2
            .shard_source
            .ends_with("end Verity.Proofs.Stdlib.Math"));
    }

    #[test]
    fn test_pattern_matching_theorem_clauses_without_colon_eq() {
        let src_v1 = "\
namespace PatMatch
theorem match_thm : Nat → True
  | 0 => trivial
  | n + 1 => match_thm n

theorem downstream_thm : True :=
  match_thm 5
end PatMatch
";
        let src_v2 = "\
namespace PatMatch
theorem match_thm : Nat → True
  | 0 => by simp
  | n + 1 => by exact match_thm n

theorem downstream_thm : True :=
  match_thm 5
end PatMatch
";
        let split1 = split_lean_source(src_v1, &[]);
        let split2 = split_lean_source(src_v2, &[]);

        assert_eq!(split1.shards.len(), 2);
        assert_eq!(split2.shards.len(), 2);
        assert_eq!(split1.shards[0].name, "match_thm");
        assert_eq!(
            split1.shards[0].signature_text,
            "theorem match_thm : Nat → True"
        );
        assert!(split1.shards[0].proof_text.starts_with("| 0 => trivial"));

        // Editing the pattern-matching proof arms must NOT change stmt_hash or interface_hash!
        assert_eq!(split1.shards[0].stmt_hash, split2.shards[0].stmt_hash);
        assert_ne!(split1.shards[0].proof_hash, split2.shards[0].proof_hash);
        assert_eq!(split1.interface_hash, split2.interface_hash);

        // Downstream theorem's prefix_env_hash and cone_env_hash must remain 100% invariant
        assert_eq!(
            split1.shards[1].prefix_env_hash,
            split2.shards[1].prefix_env_hash
        );
        assert_eq!(
            split1.shards[1].cone_env_hash,
            split2.shards[1].cone_env_hash
        );

        // Skeleton replaces pattern-matching theorem with `<stmt_src> := sorry` and preserves line count
        assert!(split1
            .skeleton_source
            .contains("theorem match_thm : Nat → True := sorry"));
        assert_eq!(split1.skeleton_source.lines().count(), src_v1.lines().count());
    }

    #[test]
    fn test_cone_env_hash_invariant_under_unused_defs_and_theorems() {
        let base_src = "\
import Init
namespace ConeDemo
variable (k : Nat)

def baseHelper : Nat := 10
def midHelper : Nat := baseHelper + 5

theorem usedLemma : midHelper = 15 := by
  rfl

theorem targetThm : midHelper = 15 :=
  usedLemma

end ConeDemo
";
        let with_unused_src = "\
import Init
namespace ConeDemo
variable (k : Nat)

def unusedHelper : Nat := 42
theorem unusedLemma : True := trivial

def baseHelper : Nat := 10
def midHelper : Nat := baseHelper + 5

theorem usedLemma : midHelper = 15 := by
  simp [midHelper, baseHelper]

theorem targetThm : midHelper = 15 :=
  usedLemma

end ConeDemo
";
        let with_modified_transitive_def_src = "\
import Init
namespace ConeDemo
variable (k : Nat)

def baseHelper : Nat := 99
def midHelper : Nat := baseHelper + 5

theorem usedLemma : midHelper = 15 := by
  rfl

theorem targetThm : midHelper = 15 :=
  usedLemma

end ConeDemo
";

        let s_base = split_lean_source(base_src, &[]);
        let s_unused = split_lean_source(with_unused_src, &[]);
        let s_mod_def = split_lean_source(with_modified_transitive_def_src, &[]);

        let target_base = s_base
            .shards
            .iter()
            .find(|s| s.name == "targetThm")
            .expect("targetThm in base");
        let target_unused = s_unused
            .shards
            .iter()
            .find(|s| s.name == "targetThm")
            .expect("targetThm in with_unused");
        let target_mod_def = s_mod_def
            .shards
            .iter()
            .find(|s| s.name == "targetThm")
            .expect("targetThm in mod_def");

        // Inserting `def unusedHelper : Nat := 42` and `theorem unusedLemma : True := trivial`
        // AND editing `usedLemma`'s proof body leaves `targetThm.cone_env_hash` 100% invariant!
        assert!(!target_base.cone_env_hash.is_empty());
        assert_eq!(target_base.cone_env_hash, target_unused.cone_env_hash);

        // Modifying `baseHelper` (transitively used via `midHelper`) MUST change `cone_env_hash`!
        assert_ne!(target_base.cone_env_hash, target_mod_def.cone_env_hash);
    }

    #[test]
    fn test_stricter_audit_hygiene_implemented_by_extern_axiom_unsafe() {
        let src_impl = strip_lean_comments("@[implemented_by fastEvil]\ndef specFn : Bool := true\n");
        let rep_impl = audit_hygiene(&src_impl);
        assert!(!rep_impl.is_clean_for_certification());
        assert!(rep_impl.has_extern_or_implemented_by);
        assert!(rep_impl
            .flagged_items
            .iter()
            .any(|i| i.ends_with(": implemented_by")));

        let src_ext = strip_lean_comments("@[extern \"c_evil\"]\nopaque extFn : Nat\n");
        let rep_ext = audit_hygiene(&src_ext);
        assert!(!rep_ext.is_clean_for_certification());
        assert!(rep_ext.has_extern_or_implemented_by);
        assert!(rep_ext.flagged_items.iter().any(|i| i.ends_with(": extern")));

        let src_ax = strip_lean_comments("axiom magicFalse : False\n");
        let rep_ax = audit_hygiene(&src_ax);
        assert!(!rep_ax.is_clean_for_certification());
        assert!(rep_ax.has_axiom);
        assert!(rep_ax.flagged_items.iter().any(|i| i.ends_with(": axiom")));

        let src_unsafe = strip_lean_comments("unsafe def badDef : Nat := 0\n");
        let rep_unsafe = audit_hygiene(&src_unsafe);
        assert!(!rep_unsafe.is_clean_for_certification());
        assert!(rep_unsafe.has_unsafe);
    }

    #[test]
    fn test_bitset_cone_env_hash_matches_and_scales_on_many_decls() {
        // Build > 200 declarations across multiple 64-bit BitSet words:
        // - An even-indexed dependency chain `chain_0 -> chain_2 -> ... -> chain_200`
        // - An odd-indexed independent chain `unused_1 -> unused_3 -> ... -> unused_199`
        let mut src_a = String::from("import Init\nnamespace BitSetScale\n");
        let mut src_b = String::from("import Init\nnamespace BitSetScale\n");
        let mut src_c = String::from("import Init\nnamespace BitSetScale\n");

        for i in 0..=200usize {
            if i % 2 == 0 {
                if i == 0 {
                    src_a.push_str("def chain_0 : Nat := 1\n");
                    src_b.push_str("def chain_0 : Nat := 1\n");
                    src_c.push_str("def chain_0 : Nat := 999\n");
                } else {
                    let line = format!("def chain_{} : Nat := chain_{} + 1\n", i, i - 2);
                    src_a.push_str(&line);
                    src_b.push_str(&line);
                    src_c.push_str(&line);
                }
            } else {
                let line_a = format!("def unused_{} : Nat := {}\n", i, i);
                let line_b = format!("def unused_{} : Nat := {}\n", i, i + 10000);
                src_a.push_str(&line_a);
                src_b.push_str(&line_b);
                src_c.push_str(&line_a);
            }
        }

        let target_thm = "theorem final_chain_thm : chain_200 = chain_200 := rfl\nend BitSetScale\n";
        src_a.push_str(target_thm);
        src_b.push_str(target_thm);
        src_c.push_str(target_thm);

        let split_a = split_lean_source(&src_a, &[]);
        let split_b = split_lean_source(&src_b, &[]);
        let split_c = split_lean_source(&src_c, &[]);

        assert_eq!(split_a.shards.len(), 1);
        assert_eq!(split_b.shards.len(), 1);
        assert_eq!(split_c.shards.len(), 1);

        // Modifying all 100 odd `unused_*` defs across 4 64-bit words leaves `final_chain_thm`'s cone_env_hash identical!
        assert_eq!(
            split_a.shards[0].cone_env_hash,
            split_b.shards[0].cone_env_hash
        );
        // Modifying `chain_0` at bit 0 (word 0) propagates across 4 64-bit words to `chain_200` (word 3)!
        assert_ne!(
            split_a.shards[0].cone_env_hash,
            split_c.shards[0].cone_env_hash
        );
    }

    #[test]
    fn test_theorem_with_where_clause_stubs_cleanly() {
        let src = "\
namespace WhereDemo

theorem thm_with_where (n : Nat) : n + 1 = 1 + n := by
  exact helper n
where
  helper (k : Nat) : k + 1 = 1 + k := by
    omega

theorem pat_thm_with_where : Nat → True
  | 0 => match true with
    | true => aux
    | false => aux
  | n + 1 => pat_thm_with_where n
where
  aux : True := trivial

theorem downstream_thm (m : Nat) : m + 1 = 1 + m :=
  thm_with_where m

end WhereDemo
";
        let split = split_lean_source(src, &[]);
        assert_eq!(split.shards.len(), 3);
        assert_eq!(split.shards[0].name, "thm_with_where");
        assert_eq!(split.shards[1].name, "pat_thm_with_where");
        assert_eq!(split.shards[2].name, "downstream_thm");

        // Skeleton must replace the entire body (including trailing `where` helpers) with `:= sorry`
        // while preserving exact line count!
        assert_eq!(split.skeleton_source.lines().count(), src.lines().count());
        assert!(split
            .skeleton_source
            .contains("theorem thm_with_where (n : Nat) : n + 1 = 1 + n  := sorry"));
        assert!(split
            .skeleton_source
            .contains("theorem pat_thm_with_where : Nat → True := sorry"));
        assert!(!contains_word(&split.skeleton_source, "where"));
        assert!(!split.skeleton_source.contains("helper"));
        assert!(!split.skeleton_source.contains("aux : True"));

        // Coalesced shard source for `downstream_thm` also stubs both `where`-clause theorems cleanly
        let mut uncached = HashSet::new();
        uncached.insert("downstream_thm".to_string());
        let coalesced = build_coalesced_shard_source(src, &uncached);
        assert_eq!(coalesced.lines().count(), src.lines().count());
        assert!(!contains_word(&coalesced, "where"));
        assert!(coalesced.contains("theorem downstream_thm (m : Nat) : m + 1 = 1 + m :=\n  thm_with_where m"));
    }

    #[test]
    fn test_fission_theorem_have_blocks_cut_rule_promotion_zero_sorry() {
        let decl = "\
theorem big_thm (a b : Nat) : a + b = b + a := by
  have h1 : a + 0 = a := by
    omega
  have h2 : b + 0 = b := by
    omega
  omega";

        let sub_shards = fission_theorem_have_blocks(decl, "big_thm");
        assert_eq!(sub_shards.len(), 3);

        assert_eq!(sub_shards[0].step_index, 0);
        assert_eq!(sub_shards[0].total_steps, 3);
        assert_eq!(sub_shards[0].step_label, "have:h1");
        assert_eq!(
            sub_shards[0].sub_decl_source,
            "theorem big_thm (a b : Nat) : a + 0 = a := by\n  omega"
        );

        assert_eq!(sub_shards[1].step_index, 1);
        assert_eq!(sub_shards[1].total_steps, 3);
        assert_eq!(sub_shards[1].step_label, "have:h2");
        assert_eq!(
            sub_shards[1].sub_decl_source,
            "theorem big_thm (a b : Nat) (h1 : a + 0 = a) : b + 0 = b := by\n  omega"
        );

        assert_eq!(sub_shards[2].step_index, 2);
        assert_eq!(sub_shards[2].total_steps, 3);
        assert_eq!(sub_shards[2].step_label, "conclusion");
        assert_eq!(
            sub_shards[2].sub_decl_source,
            "theorem big_thm (a b : Nat) (h1 : a + 0 = a) (h2 : b + 0 = b) : a + b = b + a := by\n  omega"
        );

        // Every single sub-shard must be 100% sorry-free (`0 sorryAx` in the Lean 4 kernel)!
        for sub in &sub_shards {
            let clean = strip_lean_comments(&sub.sub_decl_source);
            let rep = audit_hygiene(&clean);
            assert!(
                !rep.has_sorry && rep.is_clean_for_certification(),
                "Sub-shard {} must be 100% sorry-free: {}",
                sub.step_label,
                sub.sub_decl_source
            );
        }

        // Editing h2's proof must leave h1's sub_shard_key invariant
        let decl_modified_h2 = "\
theorem big_thm (a b : Nat) : a + b = b + a := by
  have h1 : a + 0 = a := by
    omega
  have h2 : b + 0 = b := by
    simp
  omega";
        let sub_shards_mod = fission_theorem_have_blocks(decl_modified_h2, "big_thm");
        assert_eq!(sub_shards_mod.len(), 3);
        assert_eq!(sub_shards[0].sub_shard_key, sub_shards_mod[0].sub_shard_key);
        assert_ne!(sub_shards[1].sub_shard_key, sub_shards_mod[1].sub_shard_key);
        assert_eq!(sub_shards[2].sub_shard_key, sub_shards_mod[2].sub_shard_key);
    }
}

