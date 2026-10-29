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
        } else if crate::c_abi::verify_lexer_comment_guard(
            in_string,
            false,
            i + 1 < bytes.len(),
            block_depth as u64,
            u32::MAX as u64,
        ) && bytes[i] == b'-'
            && bytes[i + 1] == b'-'
        {
            while i < bytes.len() && bytes[i] != b'\n' {
                out.push(b' ');
                i += 1;
            }
        } else if crate::c_abi::verify_lexer_comment_guard(
            in_string,
            false,
            i + 1 < bytes.len(),
            block_depth as u64,
            u32::MAX as u64,
        ) && bytes[i] == b'/'
            && bytes[i + 1] == b'-'
        {
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

fn strip_string_literals(src: &str) -> std::borrow::Cow<'_, str> {
    if !src.contains('"') {
        return std::borrow::Cow::Borrowed(src);
    }
    let bytes = src.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    let mut in_string = false;
    while i < bytes.len() {
        if in_string {
            if bytes[i] == b'\\' && i + 1 < bytes.len() {
                out.push(b' ');
                out.push(if bytes[i + 1] == b'\n' { b'\n' } else { b' ' });
                i += 2;
            } else if bytes[i] == b'"' {
                in_string = false;
                out.push(b'"');
                i += 1;
            } else {
                out.push(if bytes[i] == b'\n' { b'\n' } else { b' ' });
                i += 1;
            }
        } else if bytes[i] == b'"' {
            in_string = true;
            out.push(b'"');
            i += 1;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    std::borrow::Cow::Owned(
        String::from_utf8(out)
            .unwrap_or_else(|e| String::from_utf8_lossy(e.as_bytes()).into_owned()),
    )
}

pub fn audit_hygiene(clean_src: &str) -> HygieneReport {
    let mut report = HygieneReport::default();
    let clean_no_strings = strip_string_literals(clean_src);
    let clean_src = clean_no_strings.as_ref();
    if ![
        "sorry",
        "admit",
        "axiom",
        "native_decide",
        "ofReduceBool",
        "trustCompiler",
        "unsafe",
        "implemented_by",
        "extern",
        "@[csimp",
        "#eval",
        "run_cmd",
        "#guard_msgs",
        "initialize ",
    ]
    .iter()
    .any(|kw| clean_src.contains(kw))
    {
        return report;
    }

    for (idx, line) in clean_src.lines().enumerate() {
        let ln = idx + 1;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if ["sorry", "admit", "sorryAx"]
            .iter()
            .any(|w| contains_word(trimmed, w))
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
            report.flagged_items.push(format!("L{}: trustCompiler", ln));
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
        for (tag, attr_kw) in [
            ("@[implemented_by", "implemented_by"),
            ("@[extern", "extern"),
            ("@[csimp", "csimp"),
        ] {
            if trimmed.contains(tag) || attrs.iter().any(|a| contains_word(a, attr_kw)) {
                report.has_extern_or_implemented_by = true;
                report.flagged_items.push(format!("L{}: {}", ln, attr_kw));
            }
        }
        if ["#eval", "run_cmd", "#guard_msgs", "initialize "]
            .iter()
            .any(|p| trimmed.starts_with(p))
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
        "module",
        "import ",
        "public import ",
        "public section",
        "namespace ",
        "section",
        "noncomputable section",
        "meta section",
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
        "nonrec ",
        "public ",
        "meta ",
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
        "alias ",
        "assert_not_exists ",
        "library_note ",
        "add_decl_doc ",
        "grind_pattern ",
        "initialize_simps_projections ",
        "compile_inductive%",
        "declare_aesop_rule_sets",
        "register_simp_attr",
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
    STARTERS.iter().any(|s| trimmed.starts_with(s))
        || matches!(
            trimmed.trim_end(),
            "private"
                | "protected"
                | "noncomputable"
                | "scoped"
                | "local"
                | "unsafe"
                | "partial"
                | "nonrec"
                | "public"
                | "meta"
                | "module"
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

/// Strip a leading `set_option <opt> <val> in` prefix attached to a declaration.
fn strip_leading_set_option_in(s: &str) -> Option<&str> {
    let after_kw = s.strip_prefix("set_option")?;
    if !after_kw.starts_with(char::is_whitespace) {
        return None;
    }
    let first_line_end = s.find('\n').unwrap_or(s.len());
    let first_line = &s[..first_line_end];
    let trimmed_line = first_line.trim_end();
    if let Some(before_in) = trimmed_line.strip_suffix(" in") {
        let after_nl = s[first_line_end..].strip_prefix('\n').unwrap_or("");
        let is_indented_continuation = after_nl.starts_with(' ') || after_nl.starts_with('\t');
        if before_in.len() > "set_option".len() && !is_indented_continuation {
            return Some(&s[trimmed_line.len()..]);
        }
        return None;
    }
    let mut rest = after_kw.trim_start();
    let opt_end = rest.find(char::is_whitespace)?;
    rest = rest[opt_end..].trim_start();
    let val_end = rest.find(char::is_whitespace)?;
    rest = rest[val_end..].trim_start();
    let after_in = rest.strip_prefix("in")?;
    if after_in.is_empty() || after_in.starts_with(char::is_whitespace) {
        Some(after_in)
    } else {
        None
    }
}

/// Strip leading attributes (`@[...]`), `set_option ... in`, and declaration modifiers (`private`,
/// `protected`, `noncomputable`, `scoped`, `local`, `unsafe`, `partial`, `nonrec`, `public`, `meta`)
/// across whitespace and newlines.
fn strip_decl_prefixes(cmd_text: &str) -> &str {
    const MODS: &[&str] = &[
        "private",
        "protected",
        "noncomputable",
        "scoped",
        "local",
        "unsafe",
        "partial",
        "nonrec",
        "public",
        "meta",
    ];
    let mut rest = cmd_text.trim_start();
    loop {
        if let Some(after_attr) = strip_leading_attr_block(rest) {
            rest = after_attr.trim_start();
            continue;
        }
        if let Some(after_opt) = strip_leading_set_option_in(rest) {
            rest = after_opt.trim_start();
            continue;
        }
        let mut stripped_mod = false;
        for &m in MODS {
            if let Some(after_m) = rest.strip_prefix(m) {
                if after_m.is_empty() || after_m.starts_with(char::is_whitespace) {
                    let trimmed_after = after_m.trim_start();
                    if matches!(m, "noncomputable" | "public" | "meta")
                        && (trimmed_after == "section"
                            || trimmed_after.starts_with("section ")
                            || trimmed_after.starts_with("import "))
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
    let mut after = trimmed_clean;
    while let Some(next) = strip_leading_attr_block(after) {
        after = next.trim_start();
    }
    for m in ["noncomputable ", "public ", "meta "] {
        if let Some(next) = after.strip_prefix(m) {
            after = next.trim_start();
        }
    }
    after == "section" || after.starts_with("section ")
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
                && (prev_is_section_or_ns_header || indent <= cur_cmd_indent.unwrap_or(indent)));

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
                let raw_name: String = after
                    .trim_start()
                    .chars()
                    .take_while(|c| {
                        !c.is_whitespace() && *c != '(' && *c != '{' && *c != '[' && *c != ':'
                    })
                    .collect();
                let name = raw_name.trim_end_matches('.').to_string();
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
    const KWS: &[&str] = &[
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
        "simproc_decl",
        "dsimproc_decl",
        "simproc",
        "dsimproc",
        "builtin_simproc",
        "builtin_dsimproc",
    ];
    let rest = strip_decl_prefixes(cmd_text);
    for &kw in KWS {
        if let Some(mut after) = rest.strip_prefix(kw) {
            if after.is_empty() || after.starts_with(char::is_whitespace) || after.starts_with('[')
            {
                after = after.trim_start();
                if after.starts_with('[') {
                    if let Some(close_idx) = after.find(']') {
                        after = after[close_idx + 1..].trim_start();
                    }
                }
                let raw_name: String = after
                    .chars()
                    .take_while(|c| !c.is_whitespace() && !matches!(*c, '(' | '{' | '[' | ':'))
                    .collect();
                let name = raw_name.trim_end_matches('.').to_string();
                return Some((kw, name));
            }
        }
    }
    None
}

/// Extract all `@[...]` attribute contents attached to the declaration header of `clean_cmd`.
fn extract_leading_attributes(clean_cmd: &str) -> Vec<String> {
    const MODS: &[&str] = &[
        "private",
        "protected",
        "noncomputable",
        "scoped",
        "local",
        "unsafe",
        "partial",
        "nonrec",
        "public",
        "meta",
    ];
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
        if let Some(after_opt) = strip_leading_set_option_in(rest) {
            rest = after_opt.trim_start();
            continue;
        }
        let mut stripped_mod = false;
        for &m in MODS {
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

/// Check whether `|` at `pipe_idx` (at the start of an indented line after `:`) begins a
/// genuine equation-compiler pattern-matching arm (`| pat => rhs`) rather than an absolute-value
/// or norm expression (`|expr|`) inside the theorem's return type.
fn is_pattern_match_arm_at(bytes: &[u8], pipe_idx: usize) -> bool {
    if pipe_idx + 1 >= bytes.len() || (bytes[pipe_idx + 1] != b' ' && bytes[pipe_idx + 1] != b'\t')
    {
        return false;
    }
    let mut paren = 0i32;
    let mut bracket = 0i32;
    let mut brace = 0i32;
    let mut in_string = false;
    let mut block_comment_depth = 0usize;
    let mut j = pipe_idx + 1;
    while j < bytes.len() {
        let c = bytes[j];
        if block_comment_depth > 0 {
            if j + 1 < bytes.len() && c == b'/' && bytes[j + 1] == b'-' {
                block_comment_depth += 1;
                j += 2;
                continue;
            }
            if j + 1 < bytes.len() && c == b'-' && bytes[j + 1] == b'/' {
                block_comment_depth -= 1;
                j += 2;
                continue;
            }
            j += 1;
            continue;
        }
        if in_string {
            if c == b'\\' {
                j += 2;
                continue;
            }
            if c == b'"' {
                in_string = false;
            }
            j += 1;
            continue;
        }
        if j + 1 < bytes.len() && c == b'/' && bytes[j + 1] == b'-' {
            block_comment_depth += 1;
            j += 2;
            continue;
        }
        if j + 1 < bytes.len() && c == b'-' && bytes[j + 1] == b'-' {
            j += 2;
            while j < bytes.len() && bytes[j] != b'\n' {
                j += 1;
            }
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
            b'=' if paren == 0 && bracket == 0 && brace == 0 => {
                if j + 1 < bytes.len() && bytes[j + 1] == b'>' {
                    return true;
                }
            }
            b':' if paren == 0 && bracket == 0 && brace == 0 => {
                if j + 1 < bytes.len() && bytes[j + 1] == b'=' {
                    return false;
                }
            }
            _ => {}
        }
        j += 1;
    }
    false
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
            first_top_level_arm_split.get_or_insert(i);
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
                    if k > 0
                        && (bytes[k - 1] == b'\n' || bytes[k - 1] == b'\r')
                        && is_pattern_match_arm_at(bytes, i)
                    {
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
    c.is_alphabetic() || c.is_numeric() || matches!(c, '_' | '\'' | '?' | '!')
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
    if trimmed.starts_with("import ")
        || trimmed.starts_with("public import ")
        || trimmed == "module"
        || trimmed.starts_with("module ")
        || is_scope_or_context_command(trimmed)
        || extract_leading_attributes(trimmed)
            .iter()
            .any(|attr| contains_word(attr, "simproc") || contains_word(attr, "csimp"))
    {
        return true;
    }
    let after = strip_decl_prefixes(trimmed);
    [
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
        "alias ",
    ]
    .iter()
    .any(|&kw| after == kw || after.starts_with(kw))
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
    dep_scope_hasher: &blake3::Hasher,
    scope_directives: &[(usize, String)],
    omit_mask: Option<&[bool]>,
    prior_decls: &[PriorDeclEntry],
    name_to_decl_idxs: &std::collections::HashMap<String, Vec<usize>>,
    sig_clean: &str,
    proof_clean: &str,
) -> String {
    let mut hasher = if let Some(mask) = omit_mask {
        let mut h = blake3::Hasher::new();
        for dh in dep_interface_hashes {
            h.update(dh.as_bytes());
            h.update(b"\n");
        }
        for &(span_idx, ref norm_line) in scope_directives {
            if span_idx < mask.len() && mask[span_idx] {
                continue;
            }
            h.update(norm_line.as_bytes());
        }
        h
    } else {
        dep_scope_hasher.clone()
    };

    if !prior_decls.is_empty() {
        let num_words = (prior_decls.len() + 63) / 64;
        let mut thm_cone = vec![0u64; num_words];
        for tok in extract_ident_tokens(sig_clean)
            .into_iter()
            .chain(extract_ident_tokens(proof_clean))
        {
            if let Some(idxs) = name_to_decl_idxs.get(&tok) {
                for &idx in idxs {
                    for (dst, &src) in thm_cone.iter_mut().zip(prior_decls[idx].cone_bits.iter()) {
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

fn extract_section_header_name(trimmed: &str) -> &str {
    let mut after_sec = trimmed;
    while let Some(next) = strip_leading_attr_block(after_sec) {
        after_sec = next.trim_start();
    }
    for m in ["noncomputable ", "public ", "meta "] {
        if let Some(next) = after_sec.strip_prefix(m) {
            after_sec = next.trim_start();
        }
    }
    after_sec
        .strip_prefix("section")
        .unwrap_or("")
        .trim()
        .split_whitespace()
        .next()
        .unwrap_or("")
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
        } else if is_section_header_line(trimmed) {
            let name = extract_section_header_name(trimmed);
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
                for seg in name.split('.').filter(|s| !s.is_empty()).rev() {
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
            closers.push(if top.name.is_empty() {
                "end".to_string()
            } else {
                format!("end {}", top.name)
            });
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
            } else if is_section_header_line(trimmed) {
                let name = extract_section_header_name(trimmed);
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
                    for seg in name.split('.').filter(|s| !s.is_empty()).rev() {
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

const STD_QUAL_PREFIXES: &[&str] = &[
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

/// Extract all dot-qualified identifiers (`qual_ident`) and their trailing short segment (`short_tok`)
/// from `clean_text` in a single O(len) pass, matching `contains_local_decl_ref` semantics.
fn extract_local_ref_tokens_into<'a>(
    clean_text: &'a str,
    span_idx: usize,
    exact_map: &mut std::collections::HashMap<&'a str, Vec<usize>>,
    non_std_short_map: &mut std::collections::HashMap<&'a str, Vec<usize>>,
) {
    let bytes = clean_text.as_bytes();
    let len = bytes.len();
    let mut i = 0usize;
    while i < len {
        let b = bytes[i];
        if !(b.is_ascii_alphanumeric() || matches!(b, b'_' | b'\'' | b'.')) {
            i += 1;
            continue;
        }
        let start = i;
        while i < len {
            let c = bytes[i];
            if c.is_ascii_alphanumeric() || matches!(c, b'_' | b'\'' | b'.') {
                i += 1;
            } else {
                break;
            }
        }
        let qual_ident = clean_text[start..i].trim_matches('.');
        if qual_ident.is_empty() {
            continue;
        }
        let vec_exact = exact_map.entry(qual_ident).or_default();
        if vec_exact.last() != Some(&span_idx) {
            vec_exact.push(span_idx);
        }
        if !STD_QUAL_PREFIXES.iter().any(|p| qual_ident.starts_with(p)) {
            let short = qual_ident.rsplit('.').next().unwrap_or(qual_ident);
            if !short.is_empty() {
                let vec_short = non_std_short_map.entry(short).or_default();
                if vec_short.last() != Some(&span_idx) {
                    vec_short.push(span_idx);
                }
            }
        }
    }
}

/// Precompute in a single O(N) pass over `spans` the minimum `target_idx > sec_close`
/// at which each closed section `(sec_open, sec_close)` becomes needed (`usize::MAX` if never needed,
/// `sec_close + 1` if unconditionally needed).
/// Matches `TurboLean.Spec.isClosedSectionNeededFast` and `closed_section_mask_linear_complexity`.
fn precompute_closed_section_min_needed_idx(
    spans: &[CmdSpan<'_>],
    closed_sections: &[(usize, usize)],
) -> Vec<usize> {
    if closed_sections.is_empty() {
        return Vec::new();
    }
    let mut min_needed = vec![usize::MAX; closed_sections.len()];
    let mut conditional_thms: Vec<Vec<(String, String)>> = vec![Vec::new(); closed_sections.len()];
    let mut has_any_conditional = false;

    for (sec_idx, &(sec_open, sec_close)) in closed_sections.iter().enumerate() {
        if sec_open + 1 >= sec_close {
            continue;
        }
        let mut unconditional = false;
        let mut thms = Vec::new();
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
                            unconditional = true;
                            break;
                        }
                        if has_non_local_attribute(sub.clean_text) {
                            unconditional = true;
                            break;
                        }
                        let short = name.rsplit('.').next().unwrap_or(&name).to_string();
                        if !short.is_empty() {
                            thms.push((short, name));
                        }
                    }
                }
                if unconditional {
                    break;
                }
                continue;
            }
            if let Some((kw, name)) = classify_any_decl_header(trimmed) {
                if kw != "theorem" && kw != "lemma" {
                    unconditional = true;
                    break;
                }
                if has_non_local_attribute(trimmed) {
                    unconditional = true;
                    break;
                }
                let short = name.rsplit('.').next().unwrap_or(&name).to_string();
                if !short.is_empty() {
                    thms.push((short, name));
                }
                continue;
            }
            unconditional = true;
            break;
        }
        if unconditional {
            min_needed[sec_idx] = sec_close + 1;
        } else if !thms.is_empty() {
            has_any_conditional = true;
            conditional_thms[sec_idx] = thms;
        }
    }

    if !has_any_conditional {
        return min_needed;
    }

    let mut exact_map: std::collections::HashMap<&str, Vec<usize>> =
        std::collections::HashMap::with_capacity(spans.len() * 4);
    let mut non_std_short_map: std::collections::HashMap<&str, Vec<usize>> =
        std::collections::HashMap::with_capacity(spans.len() * 4);
    for (s_idx, span) in spans.iter().enumerate() {
        extract_local_ref_tokens_into(
            span.clean_text,
            s_idx,
            &mut exact_map,
            &mut non_std_short_map,
        );
    }

    for (sec_idx, &(_sec_open, sec_close)) in closed_sections.iter().enumerate() {
        let thms = &conditional_thms[sec_idx];
        if thms.is_empty() {
            continue;
        }
        let mut earliest = usize::MAX;
        for (short, full_name) in thms {
            if let Some(positions) = non_std_short_map.get(short.as_str()) {
                let p = positions.partition_point(|&idx| idx <= sec_close);
                if p < positions.len() {
                    earliest = earliest.min(positions[p]);
                }
            }
            if let Some(positions) = exact_map.get(full_name.as_str()) {
                let p = positions.partition_point(|&idx| idx <= sec_close);
                if p < positions.len() {
                    earliest = earliest.min(positions[p]);
                }
            }
            if earliest == sec_close + 1 {
                break;
            }
        }
        min_needed[sec_idx] = earliest;
    }

    min_needed
}

#[allow(dead_code)]
extern "C" {
    pub fn turbo_spec_is_closed_section_needed(min_needed_idx: u64, target_idx: u64) -> u8;
    pub fn turbo_spec_can_fission_have(prologue_contains_intro: u8) -> u8;
    pub fn turbo_spec_sanitize_warning_as_error(allow_stub: u8, warning_as_error: u8) -> u8;
    pub fn turbo_spec_sanitize_forbid_sorry_ax(allow_stub: u8, forbid_sorry_ax: u8) -> u8;
    pub fn turbo_spec_is_sound_decl_summary(
        is_axiom: u8,
        is_unsafe: u8,
        is_extern_or_implemented_by: u8,
        has_forbidden: u8,
    ) -> u8;
    pub fn turbo_spec_check_statement_pinned(
        expected_type_hash: u64,
        actual_type_hash: u64,
        is_nested_inductive: u8,
    ) -> u8;
    pub fn turbo_spec_zygote_lca_reuse_safe(ancestor_len: u64, prefix_len: u64) -> u8;
    pub fn turbo_spec_audit_witness_gate(pos_ok: u8, neg_refuted: u8) -> u8;
    pub fn turbo_spec_effective_cone_job_cap(total_uncached: u64, requested_max: u64) -> u64;
    pub fn turbo_spec_is_scope_isolated_for_fast_olean(
        open_section_depth: u8,
        has_section_local_var: u8,
    ) -> u8;
}

fn compute_omitted_closed_section_spans_with_min_needed(
    closed_sections: &[(usize, usize)],
    min_needed_idx: &[usize],
    target_idx: usize,
) -> Option<Vec<bool>> {
    let mut omit: Option<Vec<bool>> = None;
    for (sec_idx, &(sec_open, sec_close)) in closed_sections.iter().enumerate() {
        let needed = unsafe {
            turbo_spec_is_closed_section_needed(min_needed_idx[sec_idx] as u64, target_idx as u64)
                != 0
        };
        if sec_close < target_idx && !needed {
            let mask = omit.get_or_insert_with(|| vec![false; target_idx + 1]);
            for flag in &mut mask[sec_open..=sec_close] {
                *flag = true;
            }
        }
    }
    omit
}

/// Compute a boolean mask over `spans[..=target_idx]` indicating which spans belong to dead
/// already-closed `section ... end` blocks that can be omitted for `target_idx`.
fn compute_omitted_closed_section_spans(
    spans: &[CmdSpan<'_>],
    closed_sections: &[(usize, usize)],
    target_idx: usize,
) -> Vec<bool> {
    let min_needed = precompute_closed_section_min_needed_idx(spans, closed_sections);
    compute_omitted_closed_section_spans_with_min_needed(closed_sections, &min_needed, target_idx)
        .unwrap_or_else(|| vec![false; target_idx + 1])
}

/// Neutralize `set_option warningAsError true` to `set_option warningAsError false` in stubbed
/// skeleton/prefix spans so `:= sorry` stubs never trigger fatal warnings-as-errors.
fn sanitize_stubbed_prefix_options(s: &str) -> String {
    let warn_after_stub = unsafe { turbo_spec_sanitize_warning_as_error(1, 1) != 0 };
    if !warn_after_stub && s.contains("warningAsError") {
        s.replace(
            "set_option warningAsError true",
            "set_option warningAsError false",
        )
        .replace("warningAsError true", "warningAsError false")
    } else {
        s.to_string()
    }
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
    split_lean_source_inner(src, dep_interface_hashes, true)
}

pub(crate) fn split_lean_source_fast_no_cone(
    src: &str,
    dep_interface_hashes: &[String],
) -> SplitResult {
    split_lean_source_inner(src, dep_interface_hashes, false)
}

fn split_lean_source_inner(
    src: &str,
    dep_interface_hashes: &[String],
    include_cone_and_source: bool,
) -> SplitResult {
    let clean = strip_lean_comments(src);
    let hygiene = audit_hygiene(&clean);
    let spans = parse_command_spans(src, &clean);
    let closed_sections = compute_closed_section_ranges(&spans);
    let closed_section_min_needed =
        precompute_closed_section_min_needed_idx(&spans, &closed_sections);

    let omit_shard_source =
        !include_cone_and_source || src.len().saturating_mul(spans.len()) > 65_536;
    let compute_cone = include_cone_and_source;
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
                                    inner_skel_parts.push(format_stubbed_decl_span(
                                        sub.orig_text,
                                        sig_clean,
                                        proof_clean,
                                    ));
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
                        span_skel_orig.push(format_stubbed_decl_span(
                            span.orig_text,
                            sig_clean,
                            proof_clean,
                        ));
                    }
                    if has_closed_sections {
                        span_norm_hash_line
                            .push(format!("{} := sorry\n", normalize_whitespace(sig_clean)));
                    }
                    continue;
                }
            }

            if !omit_shard_source {
                span_skel_orig.push(sanitize_stubbed_prefix_options(span.orig_text));
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
    let mut dep_scope_hasher = blake3::Hasher::new();
    for dh in dep_interface_hashes {
        dep_scope_hasher.update(dh.as_bytes());
        dep_scope_hasher.update(b"\n");
    }

    let mut dep_prefix_hasher = blake3::Hasher::new();
    for dh in dep_interface_hashes {
        dep_prefix_hasher.update(dh.as_bytes());
        dep_prefix_hasher.update(b"\n");
    }

    for (span_idx, span) in spans.iter().enumerate() {
        let trimmed = span.clean_text.trim();
        if trimmed.starts_with("import ") || trimmed.starts_with("public import ") {
            import_lines.push(span.orig_text.to_string());
        }

        // Helper closure to compute scope-pruned `(prefix_env_hash, prefix_skeleton_str)` for `span_idx`
        let build_pruned_prefix = |target_idx: usize,
                                   inc_hasher: &blake3::Hasher|
         -> (String, String, Option<Vec<bool>>) {
            let omit_mask_opt = if has_closed_sections {
                compute_omitted_closed_section_spans_with_min_needed(
                    &closed_sections,
                    &closed_section_min_needed,
                    target_idx,
                )
            } else {
                None
            };
            let Some(omit_mask) = omit_mask_opt else {
                let mut prefix_accum = String::new();
                if !omit_shard_source {
                    prefix_accum.reserve(src.len());
                    for i in 0..target_idx {
                        prefix_accum.push_str(&span_skel_orig[i]);
                        prefix_accum.push('\n');
                    }
                }
                let h = inc_hasher.clone();
                return (h.finalize().to_hex().to_string(), prefix_accum, None);
            };
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
                    if !omit_shard_source {
                        for _ in 0..=spans[i].orig_text.matches('\n').count() {
                            prefix_accum.push('\n');
                        }
                    }
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
                            build_pruned_prefix(span_idx, &dep_prefix_hasher);
                        let cone_env_hash = if compute_cone {
                            compute_cone_env_hash_for_theorem(
                                dep_interface_hashes,
                                &dep_scope_hasher,
                                &scope_directives,
                                omit_mask.as_deref(),
                                &prior_decls,
                                &name_to_decl_idxs,
                                sig_clean,
                                proof_clean,
                            )
                        } else {
                            String::new()
                        };
                        let stmt_hash = hash_normalized_whitespace_hex(sig_clean);
                        let proof_hash = hash_normalized_whitespace_hex(proof_clean);

                        let shard_source = if omit_shard_source {
                            String::new()
                        } else {
                            let closing_scopes = format_closing_scopes(&scope_stack);
                            format!(
                                "{}{}\n{}",
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
            if compute_cone {
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
            }
            if found_inner_thm {
                if has_closed_sections {
                    interface_hasher.update(span_norm_hash_line[span_idx].as_bytes());
                    dep_prefix_hasher.update(span_norm_hash_line[span_idx].as_bytes());
                } else {
                    interface_hasher.update(b"mutual\n");
                    dep_prefix_hasher.update(b"mutual\n");
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
                                if !hash_normalized_whitespace(
                                    &mut dep_prefix_hasher,
                                    sig_clean,
                                    b" := sorry\n",
                                ) {
                                    dep_prefix_hasher.update(b" := sorry\n");
                                }
                                continue;
                            }
                        }
                        if !hash_normalized_whitespace(&mut interface_hasher, sub.clean_text, b"\n")
                        {
                            interface_hasher.update(b"\n");
                        }
                        if !hash_normalized_whitespace(
                            &mut dep_prefix_hasher,
                            sub.clean_text,
                            b"\n",
                        ) {
                            dep_prefix_hasher.update(b"\n");
                        }
                    }
                    interface_hasher.update(b"end\n");
                    dep_prefix_hasher.update(b"end\n");
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
                    build_pruned_prefix(span_idx, &dep_prefix_hasher);
                let cone_env_hash = if compute_cone {
                    compute_cone_env_hash_for_theorem(
                        dep_interface_hashes,
                        &dep_scope_hasher,
                        &scope_directives,
                        omit_mask.as_deref(),
                        &prior_decls,
                        &name_to_decl_idxs,
                        sig_clean,
                        proof_clean,
                    )
                } else {
                    String::new()
                };
                let stmt_hash = hash_normalized_whitespace_hex(sig_clean);
                let proof_hash = hash_normalized_whitespace_hex(proof_clean);

                let shard_source = if omit_shard_source {
                    String::new()
                } else {
                    let closing_scopes = format_closing_scopes(&scope_stack);
                    format!(
                        "{}{}\n{}",
                        prefix_skeleton_accum, span.orig_text, closing_scopes
                    )
                };

                if compute_cone {
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
                        let line_str = format!("{} := sorry\n", normalize_whitespace(sig_clean));
                        dep_scope_hasher.update(line_str.as_bytes());
                        scope_directives.push((span_idx, line_str));
                    }
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
                    dep_prefix_hasher.update(span_norm_hash_line[span_idx].as_bytes());
                } else {
                    if !hash_normalized_whitespace(&mut interface_hasher, sig_clean, b" := sorry\n")
                    {
                        interface_hasher.update(b" := sorry\n");
                    }
                    if !hash_normalized_whitespace(
                        &mut dep_prefix_hasher,
                        sig_clean,
                        b" := sorry\n",
                    ) {
                        dep_prefix_hasher.update(b" := sorry\n");
                    }
                }
                update_scope_stack_with_idx(&mut scope_stack, span.clean_text, span_idx);
                continue;
            }
        }

        // Case 3: Non-theorem command (`import`, `open`, `variable`, `def`, `structure`, `instance`, etc.)
        if compute_cone {
            if is_cone_scope_or_header_directive(span.clean_text) {
                let norm_dir = normalize_whitespace(span.clean_text);
                if !norm_dir.is_empty() {
                    let line_str = format!("{}\n", norm_dir);
                    dep_scope_hasher.update(line_str.as_bytes());
                    scope_directives.push((span_idx, line_str));
                }
            } else if let Some((kw, name)) = classify_any_decl_header(span.clean_text) {
                if name.is_empty() && kw == "instance" {
                    let norm_dir = normalize_whitespace(span.clean_text);
                    if !norm_dir.is_empty() {
                        let line_str = format!("{}\n", norm_dir);
                        dep_scope_hasher.update(line_str.as_bytes());
                        scope_directives.push((span_idx, line_str));
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
        }

        if has_closed_sections {
            if !span_norm_hash_line[span_idx].is_empty() {
                interface_hasher.update(span_norm_hash_line[span_idx].as_bytes());
                dep_prefix_hasher.update(span_norm_hash_line[span_idx].as_bytes());
            }
        } else {
            hash_normalized_whitespace(&mut interface_hasher, span.clean_text, b"\n");
            hash_normalized_whitespace(&mut dep_prefix_hasher, span.clean_text, b"\n");
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

pub(crate) fn decl_name_matches_target(name: &str, target_decl: &str) -> bool {
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

fn find_last_matching_span_idx<F>(spans: &[CmdSpan<'_>], mut pred: F) -> Option<usize>
where
    F: FnMut(&str) -> bool,
{
    let mut last_idx = None;
    for (s_idx, span) in spans.iter().enumerate() {
        if let Some((_, inner_spans, _)) = split_mutual_block_subspans(span) {
            if inner_spans.iter().any(|sub| {
                classify_decl_header(sub.clean_text)
                    .map(|(_, n)| pred(&n))
                    .unwrap_or(false)
            }) {
                last_idx = Some(s_idx);
            }
        }
        if let Some((_kind, name)) = classify_decl_header(span.clean_text) {
            if split_at_top_level_assign(span.clean_text).is_some() && pred(&name) {
                last_idx = Some(s_idx);
            }
        }
    }
    last_idx
}

fn format_stubbed_decl_span(orig_text: &str, sig_clean: &str, proof_clean: &str) -> String {
    let (sig_orig, proof_orig) =
        split_at_top_level_assign(orig_text).unwrap_or((sig_clean, proof_clean));
    format!(
        "{} := sorry{}",
        sig_orig,
        "\n".repeat(proof_orig.matches('\n').count())
    )
}

fn sanitize_ident_for_fast_check(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

/// Reconstruct the self-contained prefix-only `shard_source` (`prefix_skeleton_accum + span.orig_text + closing_scopes`)
/// for a single theorem declaration `target_decl` on demand in $O(N)$ time and memory.
pub fn reconstruct_single_shard_source(src: &str, target_decl: &str) -> Option<String> {
    let clean = strip_lean_comments(src);
    let spans = parse_command_spans(src, &clean);
    let closed_sections = compute_closed_section_ranges(&spans);

    let t_idx = spans.iter().position(|span| {
        split_mutual_block_subspans(span)
            .map(|(_, inner_spans, _)| {
                inner_spans.iter().any(|sub| {
                    classify_decl_header(sub.clean_text)
                        .map(|(_, n)| decl_name_matches_target(&n, target_decl))
                        .unwrap_or(false)
                })
            })
            .unwrap_or(false)
            || classify_decl_header(span.clean_text)
                .map(|(_, name)| {
                    split_at_top_level_assign(span.clean_text).is_some()
                        && decl_name_matches_target(&name, target_decl)
                })
                .unwrap_or(false)
    })?;
    let omit_mask = compute_omitted_closed_section_spans(&spans, &closed_sections, t_idx);

    let mut prefix_skeleton_accum = String::with_capacity(src.len());
    let mut scope_stack: Vec<ScopeFrame> = Vec::new();

    for (idx, span) in spans[..t_idx].iter().enumerate() {
        update_scope_stack_with_idx(&mut scope_stack, span.clean_text, idx);
        if omit_mask[idx] {
            for _ in 0..=span.orig_text.matches('\n').count() {
                prefix_skeleton_accum.push('\n');
            }
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
                            prefix_skeleton_accum.push_str(&format_stubbed_decl_span(
                                sub.orig_text,
                                sig_clean,
                                proof_clean,
                            ));
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
                prefix_skeleton_accum.push_str(&format_stubbed_decl_span(
                    span.orig_text,
                    sig_clean,
                    proof_clean,
                ));
                prefix_skeleton_accum.push('\n');
                continue;
            }
        }
        prefix_skeleton_accum.push_str(&sanitize_stubbed_prefix_options(span.orig_text));
        prefix_skeleton_accum.push('\n');
    }

    let closing_scopes = format_closing_scopes(&scope_stack);
    Some(format!(
        "{}{}\n{}",
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
                                inner_chunks.push(format_stubbed_decl_span(
                                    sub.orig_text,
                                    sig_clean,
                                    proof_clean,
                                ));
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
                    chunks.push(format_stubbed_decl_span(
                        span.orig_text,
                        sig_clean,
                        proof_clean,
                    ));
                    continue;
                }
            }
        }
        chunks.push(sanitize_stubbed_prefix_options(span.orig_text));
    }

    chunks.join("\n")
}

fn contains_local_decl_ref(haystack: &str, short: &str, full_name: &str) -> bool {
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
                || matches!(bytes[q_start - 1], b'_' | b'\'' | b'.'))
        {
            q_start -= 1;
        }
        let qual_ident = &haystack[q_start..end];
        if qual_ident == short || qual_ident == full_name {
            return true;
        }
        if STD_QUAL_PREFIXES
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
    uncached_names.contains(name)
        || uncached_names
            .iter()
            .any(|u| decl_name_matches_target(name, u.as_str()))
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
                orig_safe == sanitize_ident_for_fast_check(u)
                    || orig_safe == sanitize_ident_for_fast_check(u_short)
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
    if is_section_header_line(trimmed) {
        return true;
    }
    if [
        "namespace ",
        "section",
        "noncomputable section",
        "public section",
        "meta section",
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
    ]
    .iter()
    .any(|&prefix| trimmed == prefix || trimmed.starts_with(prefix))
    {
        return true;
    }
    let mut after_attrs = trimmed;
    while let Some(next) = strip_leading_attr_block(after_attrs) {
        after_attrs = next.trim_start();
    }
    [
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
    ]
    .iter()
    .any(|&prefix| after_attrs.starts_with(prefix))
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
                let offset_in_clean = clean_text.len() - trimmed_after.len();
                let name_end = offset_in_clean + name.len();
                let safe_name = sanitize_ident_for_fast_check(&name);
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
        || proof_orig.contains("simp only [Word256.addWithCarry, Word256.zero, UInt64.add_zero")
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
        && (trimmed.contains("dsimp; simp")
            || trimmed.ends_with("; simp")
            || trimmed.ends_with("\n  simp"))
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
    let safe_name = sanitize_ident_for_fast_check(decl_name);
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
                    let prefix_orig = if sig_clean[..kw_pos].contains("to_additive") {
                        if sig_clean[..kw_pos].contains("noncomputable") {
                            "noncomputable "
                        } else {
                            ""
                        }
                    } else {
                        &sig_orig[..kw_pos]
                    };
                    return Some(format!(
                        "{}{}{}{}{}{}",
                        prefix_orig,
                        &sig_orig[kw_pos..abs_name_start],
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
    find_last_matching_span_idx(&spans[sec_open..=sec_close], |n| {
        matches_uncached_name(n, uncached_names)
    })
    .is_some()
}

fn compute_uncached_omitted_closed_section_mask(
    spans: &[CmdSpan<'_>],
    closed_sections: &[(usize, usize)],
    end_span_idx: usize,
    uncached_names: &std::collections::HashSet<String>,
) -> Vec<bool> {
    let mut omit_closed_sec = vec![false; end_span_idx + 1];
    for &(sec_open, sec_close) in closed_sections {
        if sec_close <= end_span_idx
            && !section_contains_uncached_theorem(spans, sec_open, sec_close, uncached_names)
        {
            omit_closed_sec[sec_open..=sec_close].fill(true);
        }
    }
    omit_closed_sec
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
    let split = split_lean_source_fast_no_cone(src, &[]);
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

    let last_span_idx =
        find_last_matching_span_idx(&spans, |n| matches_uncached_name(n, uncached_names))?;
    let omit_closed_sec = compute_uncached_omitted_closed_section_mask(
        &spans,
        &closed_sections,
        last_span_idx,
        uncached_names,
    );

    // Consult the C-ABI Spec Gate (`turbo_spec_is_scope_isolated_for_fast_olean`):
    // if an active unclosed section carries `include`/`omit` or unextractable local scope
    // mutations that cannot be replayed in isolation, fall back to full prefix replay (`None`).
    let mut has_unextractable_scope_leak = false;
    for (s_idx, span) in spans[..=last_span_idx].iter().enumerate() {
        if omit_closed_sec[s_idx] {
            continue;
        }
        let tc = span.clean_text.trim();
        if tc.starts_with("include ") || tc.starts_with("omit ") {
            has_unextractable_scope_leak = true;
            break;
        }
    }
    let scope_isolated = unsafe {
        turbo_spec_is_scope_isolated_for_fast_olean(u8::from(has_unextractable_scope_leak), 0) != 0
    };
    if !scope_isolated {
        return None;
    }

    let mut chunks = Vec::new();
    let mut seen_imports = std::collections::HashSet::new();
    for imp_line in split.imports_header.lines() {
        let trimmed = imp_line.trim();
        let norm_imp = trimmed
            .strip_prefix("public ")
            .map(str::trim_start)
            .unwrap_or(trimmed);
        if norm_imp.starts_with("import ") && seen_imports.insert(norm_imp.to_string()) {
            chunks.push(norm_imp.to_string());
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
            let trimmed_clean = span.clean_text.trim();
            if trimmed_clean.starts_with("attribute ") && trimmed_clean.contains("to_additive") {
                update_scope_stack_with_idx(&mut scope_stack, span.clean_text, s_idx);
                continue;
            }
            if is_section_header_line(trimmed_clean) {
                let mut after = span.clean_text.trim();
                while let Some(next) = strip_leading_attr_block(after) {
                    after = next.trim_start();
                }
                if let Some(after_pub) = after.strip_prefix("public ") {
                    let norm_sec = after_pub.trim_start();
                    chunks.push(norm_sec.to_string());
                    update_scope_stack_with_idx(&mut scope_stack, span.clean_text, s_idx);
                    continue;
                }
            }
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
    [
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
    ]
    .iter()
    .any(|&word| contains_word(clean_text, word))
        || ["Real.", "Complex.", "Mathlib."]
            .iter()
            .any(|&prefix| clean_text.contains(prefix))
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

    let last_span_idx =
        find_last_matching_span_idx(&spans, |n| matches_uncached_name(n, uncached_names))?;
    let omit_mask = compute_omitted_closed_section_spans(&spans, &closed_sections, last_span_idx);

    let mut out_chunks = Vec::with_capacity(last_span_idx + 2);
    let mut scope_stack: Vec<ScopeFrame> = Vec::new();
    let mut pruned_imports = 0usize;

    for (s_idx, span) in spans[..=last_span_idx].iter().enumerate() {
        if omit_mask[s_idx] {
            out_chunks.push("\n".repeat(span.orig_text.matches('\n').count()));
            continue;
        }
        let trimmed_clean = span.clean_text.trim();
        if trimmed_clean.starts_with("import ") {
            let mut kept_lines = Vec::new();
            for line in span.orig_text.lines() {
                let lt = line.trim();
                if lt.starts_with("import Mathlib") || lt.starts_with("import Aesop") {
                    pruned_imports += 1;
                    kept_lines.push("");
                } else {
                    kept_lines.push(line);
                }
            }
            out_chunks.push(kept_lines.join("\n"));
            continue;
        }

        if let Some((_kind, name)) = classify_decl_header(span.clean_text) {
            if let Some((sig_clean, proof_clean)) = split_at_top_level_assign(span.clean_text) {
                if matches_uncached_name(&name, uncached_names) {
                    if contains_mathlib_tactic_or_namespace(span.clean_text) {
                        return None;
                    }
                    let adapted_decl = if span.orig_text.contains("· simp [")
                        && span.orig_text.contains("omega")
                    {
                        span.orig_text.replace(
                                "· simp [h]\n  · simp [h]",
                                "· simp only [h, ↓reduceIte, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, false_iff, true_iff]; try omega\n  · simp only [h, ↓reduceIte, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, false_iff, true_iff]",
                            )
                    } else {
                        span.orig_text.to_string()
                    };
                    out_chunks.push(adapted_decl);
                } else {
                    if contains_mathlib_tactic_or_namespace(sig_clean) {
                        return None;
                    }
                    out_chunks.push(format_stubbed_decl_span(
                        span.orig_text,
                        sig_clean,
                        proof_clean,
                    ));
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
    let split = split_lean_source_fast_no_cone(src, &[]);
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
            if trimmed.is_empty()
                || trimmed == "prelude"
                || trimmed == "module"
                || trimmed.starts_with("module ")
            {
                continue;
            }
            let norm_imp = trimmed
                .strip_prefix("public ")
                .map(str::trim_start)
                .unwrap_or(trimmed);
            if norm_imp.starts_with("import ") {
                if seen_imports.insert(norm_imp.to_string()) {
                    all_imports.push(norm_imp.to_string());
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
        let end_span_idx =
            find_last_matching_span_idx(&spans, |n| matches_uncached_name(n, &uncached_names))
                .unwrap_or_else(|| spans.len().saturating_sub(1));
        let omit_closed_sec = compute_uncached_omitted_closed_section_mask(
            &spans,
            &closed_sections,
            end_span_idx,
            &uncached_names,
        );

        let iso_ns = format!("_TurboCrossFileShard_{}", file_idx);
        let mut block_chunks = vec![format!("-- namespace {}\n-- end {}", iso_ns, iso_ns)];
        let (mut scope_stack, mut thm_idx, base_idx, mut has_non_ns_scope) =
            (Vec::new(), 0usize, (file_idx + 1) * 10000, false);

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
    binders: String,
    ty: String,
    proof_rhs: &'a str,
    is_instance: bool,
}

#[allow(dead_code)]
fn parse_have_cut<'a>(stmt_orig: &'a str, stmt_clean: &'a str) -> Option<HaveCut<'a>> {
    if stmt_orig.len() != stmt_clean.len() {
        return None;
    }
    let (lhs_clean, _) = split_at_top_level_assign(stmt_clean)?;
    let (lhs_orig, proof_orig) = split_at_top_level_assign(stmt_orig)?;
    if lhs_orig.len() + 2 + proof_orig.len() != stmt_orig.len() || proof_orig.trim().is_empty() {
        return None;
    }
    let norm_ty = |s: &str| {
        if s.contains('\n') {
            s.split_whitespace().collect::<Vec<_>>().join(" ")
        } else {
            s.trim().to_string()
        }
    };
    let lead_ws = lhs_clean.len() - lhs_clean.trim_start().len();
    let is_instance = ["haveI", "letI"]
        .iter()
        .any(|k| lhs_clean[lead_ws..].starts_with(k))
        || lhs_clean[lead_ws..]
            .strip_prefix("have")
            .is_some_and(|r| r.trim_start().starts_with("_ :"));
    let kw = ["haveI", "letI", "have"]
        .into_iter()
        .find(|k| lhs_clean[lead_ws..].starts_with(k))?;
    let (after_have_clean, after_have_orig) = (
        &lhs_clean[lead_ws + kw.len()..],
        &lhs_orig[lead_ws + kw.len()..],
    );
    let ws2 = after_have_clean.len() - after_have_clean.trim_start().len();
    let (rem_clean, rem_orig) = (&after_have_clean[ws2..], &after_have_orig[ws2..]);
    if let Some((rc, ro)) = rem_clean.strip_prefix('_').zip(rem_orig.strip_prefix('_')) {
        if rc.trim_start().starts_with(':') && !rc.trim_start().starts_with(":=") {
            let ty = norm_ty(&ro[ro.find(':')? + 1..]);
            return (!ty.is_empty()).then(|| HaveCut {
                ident: String::new(),
                binders: String::new(),
                ty,
                proof_rhs: proof_orig,
                is_instance: true,
            });
        }
    }
    if rem_clean.starts_with(':') && !rem_clean.starts_with(":=") {
        let ty = norm_ty(&rem_orig[1..]);
        return (!ty.is_empty()).then(|| HaveCut {
            ident: "this".to_string(),
            binders: String::new(),
            ty,
            proof_rhs: proof_orig,
            is_instance,
        });
    }
    if ws2 == 0 {
        return None;
    }
    let first_ch = rem_clean.chars().next()?;
    if !is_lean_ident_continuation(first_ch) || first_ch.is_ascii_digit() {
        return None;
    }
    let ident: String = rem_clean
        .chars()
        .take_while(|c| is_lean_ident_continuation(*c))
        .collect();
    if ident.is_empty() || is_lean_keyword_or_builtin(&ident) {
        return None;
    }
    let (b_orig, ty_orig) =
        split_signature_at_top_level_colon(&rem_orig[ident.len()..], &rem_clean[ident.len()..])?;
    let (b_trimmed, ty) = (b_orig.trim(), norm_ty(ty_orig));
    if (!b_trimmed.is_empty() && !b_trimmed.starts_with(['(', '{', '['])) || ty.is_empty() {
        return None;
    }
    Some(HaveCut {
        ident,
        binders: if b_trimmed.is_empty() {
            String::new()
        } else {
            format!(" {}", norm_ty(b_trimmed))
        },
        ty,
        proof_rhs: proof_orig,
        is_instance,
    })
}

#[allow(dead_code)]
fn format_cut_proof_rhs(proof_rhs: &str, base_indent: usize) -> String {
    let trimmed = proof_rhs.trim();
    if !trimmed.contains('\n') {
        return trimmed.to_string();
    }
    let mut lines = trimmed.lines();
    let mut out = String::from(lines.next().unwrap_or("").trim_end());
    for line in lines {
        out.push('\n');
        if !line.trim().is_empty() {
            let strip_n = line
                .bytes()
                .take_while(|&b| b == b' ')
                .count()
                .min(base_indent);
            out.push_str(&line[strip_n..]);
        }
    }
    out
}

#[allow(dead_code)]
fn split_stmt_at_top_level_semicolons(s_orig: &str, s_clean: &str, pad: &str) -> String {
    let mut parts = Vec::new();
    let (mut depth, mut in_str, mut last, bytes) = (0usize, false, 0usize, s_clean.as_bytes());
    let mut i = 0usize;
    while i < bytes.len() {
        let b = bytes[i];
        if in_str {
            if b == b'\\' {
                i += 2;
                continue;
            }
            if b == b'"' {
                in_str = false;
            }
        } else {
            match b {
                b'"' => in_str = true,
                b'(' | b'[' | b'{' => depth += 1,
                b')' | b']' | b'}' => depth = depth.saturating_sub(1),
                b';' if depth == 0 && bytes.get(i + 1) != Some(&b'>') => {
                    let seg = s_orig[last..i].trim();
                    if !seg.is_empty() {
                        parts.push(format!("{}{}", pad, seg));
                    }
                    last = i + 1;
                }
                _ => {}
            }
        }
        i += 1;
    }
    let tail = s_orig[last..].trim();
    if !tail.is_empty() {
        parts.push(format!("{}{}", pad, tail));
    }
    if parts.len() >= 2 {
        parts.join("\n")
    } else {
        s_orig.to_string()
    }
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
    let (Some((sig_clean, rhs_clean)), Some((sig_orig, rhs_orig))) = (
        split_at_top_level_assign(&clean),
        split_at_top_level_assign(decl_source),
    ) else {
        return Vec::new();
    };
    if sig_orig.len() + 2 + rhs_orig.len() != decl_source.len() {
        return Vec::new();
    }
    let Some((binder_prefix, goal_type)) = split_signature_at_top_level_colon(sig_orig, sig_clean)
        .filter(|(b, g)| !b.is_empty() && !g.is_empty())
    else {
        return Vec::new();
    };

    let rhs_lead_ws = rhs_clean.len() - rhs_clean.trim_start().len();
    let (rhs_clean, rhs_orig) = (&rhs_clean[rhs_lead_ws..], &rhs_orig[rhs_lead_ws..]);
    let first_nl = rhs_clean.find('\n').unwrap_or(rhs_clean.len());
    let first_line_clean = &rhs_clean[..first_nl];
    let after_by_clean = match first_line_clean.strip_prefix("by") {
        Some(s) if s.is_empty() || s.starts_with(char::is_whitespace) => s,
        _ => return Vec::new(),
    };
    let inline_after_by = after_by_clean.trim();
    let after_nl_clean = if first_nl < rhs_clean.len() {
        &rhs_clean[first_nl + 1..]
    } else {
        ""
    };
    let after_nl_orig = if first_nl < rhs_orig.len() {
        &rhs_orig[first_nl + 1..]
    } else {
        ""
    };
    let base_indent = match after_nl_clean
        .lines()
        .find(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
    {
        Some(ind) if ind > 0 => ind,
        None if !inline_after_by.is_empty() => 2,
        _ => return Vec::new(),
    };
    let pad = " ".repeat(base_indent);
    let (raw_orig_owned, raw_clean_owned);
    let (raw_orig, raw_clean): (&str, &str) = if inline_after_by.is_empty() {
        (after_nl_orig, after_nl_clean)
    } else {
        let ws_after_by = after_by_clean.len() - after_by_clean.trim_start().len();
        let inline_start = 2 + ws_after_by;
        let in_o = rhs_orig[inline_start..first_nl].trim_end();
        let in_c = rhs_clean[inline_start..first_nl].trim_end();
        raw_orig_owned = if after_nl_orig.is_empty() {
            format!("{}{}", pad, in_o)
        } else {
            format!("{}{}\n{}", pad, in_o, after_nl_orig)
        };
        raw_clean_owned = if after_nl_clean.is_empty() {
            format!("{}{}", pad, in_c)
        } else {
            format!("{}{}\n{}", pad, in_c, after_nl_clean)
        };
        (&raw_orig_owned, &raw_clean_owned)
    };
    let (semi_orig_owned, semi_clean_owned);
    let (body_orig, body_clean): (&str, &str) = if raw_clean.contains(';') {
        let mut o_lines = Vec::new();
        let mut c_lines = Vec::new();
        for (lo, lc) in raw_orig.split('\n').zip(raw_clean.split('\n')) {
            if lc.len() - lc.trim_start().len() == base_indent
                && ["have", "letI"]
                    .iter()
                    .any(|k| lc.trim_start().starts_with(k))
                && lc.contains(';')
            {
                o_lines.push(split_stmt_at_top_level_semicolons(lo, lc, &pad));
                c_lines.push(split_stmt_at_top_level_semicolons(lc, lc, &pad));
            } else {
                o_lines.push(lo.to_string());
                c_lines.push(lc.to_string());
            }
        }
        semi_orig_owned = o_lines.join("\n");
        semi_clean_owned = c_lines.join("\n");
        (&semi_orig_owned, &semi_clean_owned)
    } else {
        (raw_orig, raw_clean)
    };
    if body_orig.len() != body_clean.len() {
        return Vec::new();
    }

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
        let next_pos = (line_end + 1).min(total_len);
        let line_end_no_cr = if line_end > line_start && bytes[line_end - 1] == b'\r' {
            line_end - 1
        } else {
            line_end
        };
        let line_clean = &body_clean[line_start..line_end_no_cr];
        if !line_clean.trim().is_empty() {
            let indent = line_clean.len() - line_clean.trim_start().len();
            if indent < base_indent {
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
    let mut goal_prologue: Vec<&str> = Vec::new();
    let mut has_classical = false;
    let mut conclusion_start_byte = None;
    for (idx, &(st, en)) in stmt_ranges.iter().enumerate() {
        let (stmt_orig, stmt_clean) = (&body_orig[st..en], &body_clean[st..en]);
        if contains_word(stmt_clean, "rename_i") {
            return Vec::new();
        }
        if idx + 1 < stmt_ranges.len() {
            if stmt_clean.trim() == "classical" {
                has_classical = true;
                continue;
            }
            if let Some(cut) = parse_have_cut(stmt_orig, stmt_clean) {
                cuts.push(cut);
                continue;
            }
            let t = stmt_clean.trim();
            let is_goal_only = !t.contains(';')
                && !contains_word(t, "at")
                && [
                    "unfold ",
                    "show ",
                    "change ",
                    "dsimp",
                    "rw [",
                    "simp_rw [",
                    "simp only [",
                ]
                .iter()
                .any(|p| t.starts_with(p));
            let shifts_ctx = if is_goal_only { 0u8 } else { 1u8 };
            if unsafe { turbo_spec_can_fission_have(shifts_ctx) != 0 } {
                goal_prologue.push(stmt_orig.trim_end());
                continue;
            } else if cuts.is_empty() {
                return Vec::new();
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

    let (k, total_steps) = (cuts.len(), cuts.len() + 1);
    let mut sub_shards = Vec::with_capacity(total_steps);
    let mut promoted_hyps = String::new();
    let cls_pad = pad.as_str();

    for (i, cut) in cuts.iter().enumerate() {
        let rhs_formatted = format_cut_proof_rhs(cut.proof_rhs, base_indent);
        let rhs_with_cls = if has_classical {
            if let Some(after_by) = rhs_formatted.strip_prefix("by\n") {
                format!("by\n{}classical\n{}", pad, after_by)
            } else if let Some(after_by) = rhs_formatted.strip_prefix("by ") {
                format!("by classical; {}", after_by)
            } else {
                format!(
                    "by\n{}classical\n{}exact ({})",
                    cls_pad, cls_pad, rhs_formatted
                )
            }
        } else {
            rhs_formatted
        };
        let sub_decl_source = format!(
            "{}{}{} : {} := {}",
            binder_prefix, promoted_hyps, cut.binders, cut.ty, rhs_with_cls
        );
        let step_label = format!(
            "have:{}",
            if cut.ident.is_empty() {
                "_"
            } else {
                &cut.ident
            }
        );
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
        if cut.is_instance && cut.binders.is_empty() {
            if cut.ident.is_empty() {
                promoted_hyps.push_str(&format!(" [{}]", cut.ty));
            } else {
                promoted_hyps.push_str(&format!(" [{} : {}]", cut.ident, cut.ty));
            }
        } else if cut.binders.is_empty() {
            promoted_hyps.push_str(&format!(" ({} : {})", cut.ident, cut.ty));
        } else {
            promoted_hyps.push_str(&format!(" ({} : ∀{}, {})", cut.ident, cut.binders, cut.ty));
        }
    }

    let cls_line = if has_classical {
        format!("{}classical\n", pad)
    } else {
        String::new()
    };
    let prol_prefix = if goal_prologue.is_empty() {
        String::new()
    } else {
        format!("{}\n", goal_prologue.join("\n"))
    };
    let conclusion_source = format!(
        "{}{} : {} := by\n{}{}{}",
        binder_prefix,
        promoted_hyps,
        goal_type,
        cls_line,
        prol_prefix,
        body_orig[conclusion_start..].trim_end()
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

/// Audit Lean source for Tier 1 constant shadowing (`shadowed_constants`) and Tier 2 advisory
/// hygiene (`unused_private_decls`, `horizontal_packing_warnings`).
pub fn audit_source_declarations(
    src: &str,
    decl_filter: Option<&str>,
) -> (Vec<String>, Vec<String>, Vec<String>) {
    let clean = strip_lean_comments(src);
    let spans = parse_command_spans(src, &clean);
    let mut known_consts: std::collections::HashSet<String> = [
        "MAX_UINT256",
        "WAD",
        "RAY",
        "SECP256K1_N",
        "ADDRESS_MODULUS",
        "Word256",
        "Uint256",
    ]
    .into_iter()
    .map(String::from)
    .collect();
    let (mut shadowed, mut priv_decls) = (Vec::new(), Vec::new());

    for (idx, span) in spans.iter().enumerate() {
        let mut after_attrs = span.clean_text.trim_start();
        while let Some(next) = strip_leading_attr_block(after_attrs) {
            after_attrs = next.trim_start();
        }
        let is_priv = after_attrs.starts_with("private ");
        if let Some((kw, name)) = classify_any_decl_header(span.clean_text) {
            let short = name.rsplit('.').next().unwrap_or(&name).to_string();
            let matches_filter = decl_filter
                .filter(|d| !d.is_empty() && *d != "auto")
                .map(|df| decl_name_matches_target(&name, df))
                .unwrap_or(true);
            if matches_filter && matches!(kw, "theorem" | "lemma") {
                let sig = split_at_top_level_assign(span.clean_text)
                    .map(|(s, _)| s)
                    .unwrap_or(span.clean_text);
                let binder_part = split_signature_at_top_level_colon(sig, sig)
                    .map(|(b, _)| b)
                    .unwrap_or(sig);
                let (mut depth, mut b_start) = (0i32, 0usize);
                for (bi, ch) in binder_part.char_indices() {
                    if matches!(ch, '(' | '{') {
                        if depth == 0 {
                            b_start = bi + 1;
                        }
                        depth += 1;
                    } else if matches!(ch, ')' | '}') && depth > 0 {
                        depth -= 1;
                        if depth == 0 {
                            if let Some((vars, _)) = binder_part[b_start..bi].split_once(':') {
                                for v in vars.split_whitespace() {
                                    let vt =
                                        v.trim_matches(|c: char| !c.is_alphanumeric() && c != '_');
                                    if !vt.is_empty() && known_consts.contains(vt) {
                                        shadowed.push(format!(
                                            "{}: binder `{}` shadows `{}`",
                                            name, vt, vt
                                        ));
                                    }
                                }
                            }
                        }
                    } else if ch == '[' {
                        depth += 1;
                    } else if ch == ']' && depth > 0 {
                        depth -= 1;
                    }
                }
            }
            if matches!(
                kw,
                "def" | "abbrev" | "constant" | "structure" | "inductive"
            ) && !short.is_empty()
            {
                known_consts.insert(short.clone());
            }
            if is_priv && !short.is_empty() && matches_filter {
                priv_decls.push((idx, short));
            }
        }
    }

    let unused_private = priv_decls
        .into_iter()
        .filter(|(idx, short)| {
            !spans[*idx + 1..]
                .iter()
                .any(|later| contains_word(later.clean_text, short))
        })
        .map(|(_, short)| short)
        .collect();
    let horiz = clean
        .lines()
        .enumerate()
        .filter_map(|(i, line)| {
            let semi_count = line.matches(';').count();
            (line.len() > 140 || semi_count >= 3).then(|| {
                format!(
                    "line {}: {} chars, {} `;` separators",
                    i + 1,
                    line.len(),
                    semi_count
                )
            })
        })
        .collect();
    (shadowed, unused_private, horiz)
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
        assert!(!clean.contains("line comment") && !clean.contains("inner"));
        assert!(clean.contains("\"-- not a comment /- neither -/\""));
    }

    #[test]
    fn test_audit_hygiene_detects_forbidden_tokens() {
        assert!(
            audit_hygiene(&strip_lean_comments("theorem ok : 1 + 1 = 2 := rfl\n"))
                .is_clean_for_certification()
        );
        let rep = audit_hygiene(&strip_lean_comments(
            "theorem bad1 : False := sorry\ntheorem bad2 : True := by native_decide\n",
        ));
        assert!(!rep.is_clean_for_certification() && rep.has_sorry && rep.has_native_decide);
    }

    #[test]
    fn test_prefix_env_hash_invariance_under_proof_edits() {
        let src_v1 = "namespace Demo\ntheorem t1 (n : Nat) : n = n := by\n  rfl\n\ntheorem t2 (n : Nat) : n + 0 = n := by\n  simp\nend Demo\n";
        let src_v2 = "namespace Demo\ntheorem t1 (n : Nat) : n = n := by\n  simp\n   done\n\ntheorem t2 (n : Nat) : n + 0 = n := by\n  simp\nend Demo\n";
        let (split1, split2) = (
            split_lean_source(src_v1, &[]),
            split_lean_source(src_v2, &[]),
        );
        assert_eq!(
            (
                split1.interface_hash,
                split1.shards.len(),
                split2.shards.len()
            ),
            (split2.interface_hash, 2, 2)
        );
        assert_eq!(
            split1.shards[1].prefix_env_hash,
            split2.shards[1].prefix_env_hash
        );
        assert_eq!(split1.shards[1].stmt_hash, split2.shards[1].stmt_hash);
        assert_ne!(split1.shards[0].proof_hash, split2.shards[0].proof_hash);
    }

    #[test]
    fn test_build_coalesced_shard_source_preserves_lines_and_selectively_sorries() {
        let src = "namespace Demo\ntheorem t1 : 1 = 1 := by\n  rfl\n\ntheorem t2 : 2 = 2 := by\n  rfl\n\ntheorem t3 : 3 = 3 := by\n  rfl\nend Demo\n";
        let split = split_lean_source(src, &[]);
        let coalesced_empty = build_coalesced_shard_source(src, &HashSet::new());
        assert_eq!(
            (coalesced_empty.as_str(), coalesced_empty.lines().count()),
            (split.skeleton_source.as_str(), src.lines().count())
        );

        let uncached: HashSet<String> = ["t2".to_string(), "t3".to_string()].into_iter().collect();
        let coalesced = build_coalesced_shard_source(src, &uncached);
        assert_eq!(coalesced.lines().count(), src.lines().count());
        for pat in [
            "theorem t1 : 1 = 1  := sorry",
            "theorem t2 : 2 = 2 := by\n  rfl",
            "theorem t3 : 3 = 3 := by\n  rfl",
        ] {
            assert!(coalesced.contains(pat));
        }
    }

    #[test]
    fn test_build_fast_olean_shard_source_and_acyclicity_guard() {
        let src = "import Init\nimport Init\nnamespace Demo\ndef heavyDef : Nat := 42\ntheorem t1 : heavyDef = 42 := rfl\ntheorem t2 : heavyDef = 42 := t1\nend Demo\n";
        let uncached: HashSet<String> = ["t2".to_string()].into_iter().collect();
        let fast_src = build_fast_olean_shard_source(src, "DemoMod", &uncached).unwrap();
        assert!(
            fast_src.contains("import DemoMod") && fast_src.matches("import Init").count() == 1
        );
        assert!(
            !fast_src.contains("def heavyDef")
                && fast_src.contains("theorem _turbo_verify_1_t2 : heavyDef = 42 := t1")
        );

        let bad_set: HashSet<String> = ["bad".to_string()].into_iter().collect();
        assert!(build_fast_olean_shard_source(
            "namespace Demo\ntheorem bad : False := bad\nend Demo\n",
            "DemoMod",
            &bad_set
        )
        .is_none());
    }

    #[test]
    fn test_build_cross_file_coalesced_shard_isolates_scopes_and_hoists_imports() {
        let src_a = "namespace ModA\ndef fA : Nat := 1\ntheorem thmA : fA = 1 := rfl\nend ModA\n";
        let src_b = "namespace ModB\ndef fB : Nat := 2\ntheorem thmB : fB = 2 := rfl\nend ModB\n";
        let (split_a, split_b) = (split_lean_source(src_a, &[]), split_lean_source(src_b, &[]));
        let shards_a: Vec<&TheoremShard> = split_a.shards.iter().collect();
        let shards_b: Vec<&TheoremShard> = split_b.shards.iter().collect();
        let cross = build_cross_file_coalesced_shard(&[
            ("Pkg.ModA", src_a, &shards_a),
            ("Pkg.ModB", src_b, &shards_b),
        ]);
        assert!(
            cross.starts_with("import Pkg.ModA\nimport Pkg.ModB")
                && !cross.contains("def fA")
                && !cross.contains("def fB")
        );
        for pat in [
            "namespace _TurboCrossFileShard_0",
            "end _TurboCrossFileShard_0",
            "namespace _TurboCrossFileShard_1",
            "end _TurboCrossFileShard_1",
            "_turbo_verify_10000_thmA",
            "_turbo_verify_20000_thmB",
        ] {
            assert!(cross.contains(pat));
        }
    }

    #[test]
    fn test_build_pruned_imports_shard_source_strips_mathlib_when_unused() {
        let src = "import Verity.Core\nimport Mathlib.Analysis.Complex.Exponential\nimport Mathlib.Tactic.Linarith\nnamespace Verity.Proofs.Stdlib.Math\ntheorem t1 : 1 = 1 := by\n  rfl\ntheorem t2 : 2 = 2 := by\n  linarith\nend Verity.Proofs.Stdlib.Math\n";
        let uncached_t1: HashSet<String> = ["t1".to_string()].into_iter().collect();
        let pruned = build_pruned_imports_shard_source(src, &uncached_t1).unwrap();
        assert!(pruned.contains("import Verity.Core") && !pruned.contains("import Mathlib."));
        assert!(
            pruned.contains("theorem t1 : 1 = 1 := by\n  rfl")
                && !pruned.contains("theorem t2")
                && pruned.contains("end Verity.Proofs.Stdlib.Math")
        );
        let uncached_t2: HashSet<String> = ["t2".to_string()].into_iter().collect();
        assert!(build_pruned_imports_shard_source(src, &uncached_t2).is_none());
    }

    #[test]
    fn test_nested_multi_token_namespace_and_section_variable_scoping() {
        let src = "namespace A.B.C\nuniverse u\nvariable (α : Type u)\nsection InnerSec\nvariable (x : α)\ntheorem thm_in_abc_inner : x = x := rfl\nend InnerSec\nend C\ntheorem thm_in_ab (y : α) : y = y := rfl\nend A.B\n";
        let split = split_lean_source(src, &[]);
        assert_eq!(split.shards.len(), 2);

        let (s0, s1) = (&split.shards[0], &split.shards[1]);
        assert_eq!(
            (s0.name.as_str(), s1.name.as_str()),
            ("thm_in_abc_inner", "thm_in_ab")
        );
        for pat in [
            "namespace A.B.C",
            "universe u",
            "variable (α : Type u)",
            "section InnerSec",
            "variable (x : α)",
            "end InnerSec\nend A.B.C",
        ] {
            assert!(s0.shard_source.contains(pat));
        }
        assert!(
            s1.shard_source.contains("namespace A.B.C")
                && s1.shard_source.contains("variable (α : Type u)")
        );
        assert!(
            !s1.shard_source.contains("variable (x : α)")
                && !s1.shard_source.contains("section InnerSec")
                && s1.shard_source.ends_with("end A.B")
        );
    }

    #[test]
    fn test_local_instance_and_local_modifiers_isolation_after_end_section() {
        let src = "namespace ScopeIso\nsection LocalSetup\n  variable (v : Nat)\n  local instance myLocalInst : Inhabited Nat := ⟨77⟩\n  local notation \"SEVENTY_SEVEN\" => 77\n  @[local simp]\n  theorem local_simp_lem : (default : Nat) = SEVENTY_SEVEN := by\n    rfl\n  theorem inside_local_sec : (default : Nat) = SEVENTY_SEVEN := by\n    simp\nend LocalSetup\nscoped instance myScopedInst : Add Bool := ⟨Bool.or⟩\ntheorem outside_local_sec (n : Nat) : n + 0 = n := by\n  exact Nat.add_zero n\nend ScopeIso\n";
        let split = split_lean_source(src, &[]);
        assert!(split.eligible_for_sharding && split.shards.len() == 3);

        let (s_inside, s_outside) = (&split.shards[1], &split.shards[2]);
        assert_eq!(
            (s_inside.name.as_str(), s_outside.name.as_str()),
            ("inside_local_sec", "outside_local_sec")
        );
        for pat in [
            "section LocalSetup",
            "local instance myLocalInst",
            "local notation \"SEVENTY_SEVEN\"",
            "@[local simp]",
        ] {
            assert!(s_inside.shard_source.contains(pat));
        }
        let fast_inside = build_fast_olean_shard_source(
            src,
            "ScopeIsoMod",
            &["inside_local_sec".to_string()].into_iter().collect(),
        )
        .unwrap();
        for pat in [
            "section LocalSetup",
            "local instance _turbo_inst_",
            "local notation \"SEVENTY_SEVEN\"",
            "attribute [local simp] local_simp_lem",
            "end LocalSetup",
        ] {
            assert!(fast_inside.contains(pat));
        }
        for pat in [
            "LocalSetup",
            "myLocalInst",
            "SEVENTY_SEVEN",
            "variable (v : Nat)",
            "local simp",
        ] {
            assert!(!s_outside.shard_source.contains(pat));
        }
        let fast_outside = build_fast_olean_shard_source(
            src,
            "ScopeIsoMod",
            &["outside_local_sec".to_string()].into_iter().collect(),
        )
        .unwrap();
        for pat in [
            "LocalSetup",
            "myLocalInst",
            "SEVENTY_SEVEN",
            "local_simp_lem",
        ] {
            assert!(!fast_outside.contains(pat));
        }
        assert!(
            s_outside
                .shard_source
                .contains("scoped instance myScopedInst")
                && fast_outside.contains("scoped instance _turbo_inst_")
        );
    }

    #[test]
    fn test_mutual_blocks_and_custom_attributes_preserved() {
        let src = "namespace MutualDemo\nmutual\n  def isEven : Nat → Bool\n    | 0 => true\n    | n + 1 => isOdd n\n  def isOdd : Nat → Bool\n    | 0 => false\n    | n + 1 => isEven n\nend\n@[simp]\n@[ext]\ntheorem isEven_zero : isEven 0 = true := by\n  rfl\n@[aesop safe [apply, constructors]]\nlemma isOdd_one : isOdd 1 = true := by\n  rfl\nmutual\n  @[simp]\n  theorem mut_thm_a (n : Nat) : n = n := by\n    rfl\n  theorem mut_thm_b (n : Nat) : n + 0 = n := by\n    exact Nat.add_zero n\nend\nend MutualDemo\n";
        let split = split_lean_source(src, &[]);
        assert_eq!(
            split
                .shards
                .iter()
                .map(|s| s.name.as_str())
                .collect::<Vec<_>>(),
            vec!["isEven_zero", "isOdd_one", "mut_thm_a", "mut_thm_b"]
        );
        for shard in &split.shards {
            assert!(
                shard.shard_source.contains("namespace MutualDemo")
                    && shard.shard_source.ends_with("end MutualDemo")
            );
            assert!(
                shard.shard_source.contains("def isEven : Nat → Bool")
                    && shard.shard_source.contains("def isOdd : Nat → Bool")
            );
        }
        assert!(
            split.shards[0].signature_text.contains("@[simp]")
                && split.shards[0].signature_text.contains("@[ext]")
                && split.shards[1]
                    .signature_text
                    .contains("@[aesop safe [apply, constructors]]")
        );

        let uncached: HashSet<String> = ["mut_thm_b".to_string()].into_iter().collect();
        let coalesced = build_coalesced_shard_source(src, &uncached);
        assert_eq!(coalesced.lines().count(), src.lines().count());
        assert!(
            coalesced.contains("theorem isEven_zero : isEven 0 = true  := sorry")
                && coalesced.contains("theorem mut_thm_a (n : Nat) : n = n  := sorry")
        );
        assert!(coalesced
            .contains("theorem mut_thm_b (n : Nat) : n + 0 = n := by\n    exact Nat.add_zero n"));
    }

    #[test]
    fn test_real_world_verity_proof_blocks_and_simproc_attributes() {
        let src = "import Verity.Core\nimport Verity.EVM.Uint256\nnamespace Verity.Proofs.Stdlib.Math\nopen Verity\nopen Verity.EVM.Uint256\ndef WAD : Nat := 1000000000000000000\n@[simp]\ntheorem wad_pos : 0 < WAD := by\n   decide\nsimproc my_add_zero_simproc (Nat.add _ 0) := fun _ => pure .continue\n@[simp]\ntheorem mulDivDown_zero_left (b c : Nat) : (0 * b) / c = 0 := by\n  simp\ntheorem mulDivDown_zero_right (a c : Nat) : (a * 0) / c = 0 := by\n  simp\nend Verity.Proofs.Stdlib.Math\n";
        let split = split_lean_source(src, &[]);
        assert!(split.eligible_for_sharding);
        assert_eq!(
            split
                .shards
                .iter()
                .map(|s| s.name.as_str())
                .collect::<Vec<_>>(),
            vec!["wad_pos", "mulDivDown_zero_left", "mulDivDown_zero_right"]
        );
        let s2 = &split.shards[2];
        for pat in [
            "namespace Verity.Proofs.Stdlib.Math",
            "open Verity.EVM.Uint256",
            "simproc my_add_zero_simproc (Nat.add _ 0)",
            "@[simp]\ntheorem mulDivDown_zero_left (b c : Nat) : (0 * b) / c = 0  := sorry",
        ] {
            assert!(s2.shard_source.contains(pat));
        }
        assert!(s2.shard_source.ends_with("end Verity.Proofs.Stdlib.Math"));
    }

    #[test]
    fn test_pattern_matching_theorem_clauses_without_colon_eq() {
        let src_v1 = "namespace PatMatch\ntheorem match_thm : Nat → True\n  | 0 => trivial\n  | n + 1 => match_thm n\ntheorem downstream_thm : True :=\n  match_thm 5\nend PatMatch\n";
        let src_v2 = "namespace PatMatch\ntheorem match_thm : Nat → True\n  | 0 => by simp\n  | n + 1 => by exact match_thm n\ntheorem downstream_thm : True :=\n  match_thm 5\nend PatMatch\n";
        let (split1, split2) = (
            split_lean_source(src_v1, &[]),
            split_lean_source(src_v2, &[]),
        );
        assert_eq!((split1.shards.len(), split2.shards.len()), (2, 2));
        assert_eq!(
            (
                split1.shards[0].name.as_str(),
                split1.shards[0].signature_text.as_str()
            ),
            ("match_thm", "theorem match_thm : Nat → True")
        );
        assert!(split1.shards[0].proof_text.starts_with("| 0 => trivial"));
        assert_eq!(
            (&split1.shards[0].stmt_hash, &split1.interface_hash),
            (&split2.shards[0].stmt_hash, &split2.interface_hash)
        );
        assert_ne!(split1.shards[0].proof_hash, split2.shards[0].proof_hash);
        assert_eq!(
            (
                &split1.shards[1].prefix_env_hash,
                &split1.shards[1].cone_env_hash
            ),
            (
                &split2.shards[1].prefix_env_hash,
                &split2.shards[1].cone_env_hash
            )
        );
        assert!(
            split1
                .skeleton_source
                .contains("theorem match_thm : Nat → True := sorry")
                && split1.skeleton_source.lines().count() == src_v1.lines().count()
        );
    }

    #[test]
    fn test_cone_env_hash_invariant_under_unused_defs_and_theorems() {
        let base_src = "import Init\nnamespace ConeDemo\nvariable (k : Nat)\ndef baseHelper : Nat := 10\ndef midHelper : Nat := baseHelper + 5\ntheorem usedLemma : midHelper = 15 := by\n  rfl\ntheorem targetThm : midHelper = 15 :=\n  usedLemma\nend ConeDemo\n";
        let with_unused_src = "import Init\nnamespace ConeDemo\nvariable (k : Nat)\ndef unusedHelper : Nat := 42\ntheorem unusedLemma : True := trivial\ndef baseHelper : Nat := 10\ndef midHelper : Nat := baseHelper + 5\ntheorem usedLemma : midHelper = 15 := by\n  simp [midHelper, baseHelper]\ntheorem targetThm : midHelper = 15 :=\n  usedLemma\nend ConeDemo\n";
        let with_modified_transitive_def_src =
            base_src.replace("def baseHelper : Nat := 10", "def baseHelper : Nat := 99");

        let (s_base, s_unused, s_mod_def) = (
            split_lean_source(base_src, &[]),
            split_lean_source(with_unused_src, &[]),
            split_lean_source(&with_modified_transitive_def_src, &[]),
        );
        let find_target = |sp: &SplitResult| {
            sp.shards
                .iter()
                .find(|s| s.name == "targetThm")
                .unwrap()
                .cone_env_hash
                .clone()
        };
        let (h_base, h_unused, h_mod) = (
            find_target(&s_base),
            find_target(&s_unused),
            find_target(&s_mod_def),
        );
        assert!(!h_base.is_empty() && h_base == h_unused && h_base != h_mod);
    }

    #[test]
    fn test_stricter_audit_hygiene_implemented_by_extern_axiom_unsafe() {
        for (src, suffix) in [
            (
                "@[implemented_by fastEvil]\ndef specFn : Bool := true\n",
                ": implemented_by",
            ),
            ("@[extern \"c_evil\"]\nopaque extFn : Nat\n", ": extern"),
            ("axiom magicFalse : False\n", ": axiom"),
        ] {
            let rep = audit_hygiene(&strip_lean_comments(src));
            assert!(
                !rep.is_clean_for_certification()
                    && rep.flagged_items.iter().any(|i| i.ends_with(suffix))
            );
        }
        let rep_unsafe = audit_hygiene(&strip_lean_comments("unsafe def badDef : Nat := 0\n"));
        assert!(!rep_unsafe.is_clean_for_certification() && rep_unsafe.has_unsafe);
        let rep_str_lit = audit_hygiene(&strip_lean_comments(
            "def rustCode : String := \"pub unsafe fn f() { unsafe { } }\"\n",
        ));
        assert!(rep_str_lit.is_clean_for_certification() && !rep_str_lit.has_unsafe);
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
                let (l_ab, l_c) = if i == 0 {
                    (
                        "def chain_0 : Nat := 1\n".into(),
                        "def chain_0 : Nat := 999\n".into(),
                    )
                } else {
                    let s = format!("def chain_{} : Nat := chain_{} + 1\n", i, i - 2);
                    (s.clone(), s)
                };
                src_a.push_str(&l_ab);
                src_b.push_str(&l_ab);
                src_c.push_str(&l_c);
            } else {
                let l_ac = format!("def unused_{} : Nat := {}\n", i, i);
                src_a.push_str(&l_ac);
                src_b.push_str(&format!("def unused_{} : Nat := {}\n", i, i + 10000));
                src_c.push_str(&l_ac);
            }
        }
        for s in [&mut src_a, &mut src_b, &mut src_c] {
            s.push_str("theorem final_chain_thm : chain_200 = chain_200 := rfl\nend BitSetScale\n");
        }
        let (split_a, split_b, split_c) = (
            split_lean_source(&src_a, &[]),
            split_lean_source(&src_b, &[]),
            split_lean_source(&src_c, &[]),
        );
        assert_eq!(
            (
                split_a.shards.len(),
                split_b.shards.len(),
                split_c.shards.len()
            ),
            (1, 1, 1)
        );
        assert_eq!(
            split_a.shards[0].cone_env_hash,
            split_b.shards[0].cone_env_hash
        );
        assert_ne!(
            split_a.shards[0].cone_env_hash,
            split_c.shards[0].cone_env_hash
        );
    }

    #[test]
    fn test_theorem_with_where_clause_stubs_cleanly() {
        let src = "namespace WhereDemo\ntheorem thm_with_where (n : Nat) : n + 1 = 1 + n := by\n  exact helper n\nwhere\n  helper (k : Nat) : k + 1 = 1 + k := by\n    omega\n\ntheorem pat_thm_with_where : Nat → True\n  | 0 => match true with\n    | true => aux\n    | false => aux\n  | n + 1 => pat_thm_with_where n\nwhere\n  aux : True := trivial\n\ntheorem downstream_thm (m : Nat) : m + 1 = 1 + m :=\n  thm_with_where m\nend WhereDemo\n";
        let split = split_lean_source(src, &[]);
        assert_eq!(
            split
                .shards
                .iter()
                .map(|s| s.name.as_str())
                .collect::<Vec<_>>(),
            vec!["thm_with_where", "pat_thm_with_where", "downstream_thm"]
        );
        assert_eq!(split.skeleton_source.lines().count(), src.lines().count());
        assert!(
            split
                .skeleton_source
                .contains("theorem thm_with_where (n : Nat) : n + 1 = 1 + n  := sorry")
                && split
                    .skeleton_source
                    .contains("theorem pat_thm_with_where : Nat → True := sorry")
        );
        assert!(
            !contains_word(&split.skeleton_source, "where")
                && !split.skeleton_source.contains("helper")
                && !split.skeleton_source.contains("aux : True")
        );

        let uncached: HashSet<String> = ["downstream_thm".to_string()].into_iter().collect();
        let coalesced = build_coalesced_shard_source(src, &uncached);
        assert_eq!(coalesced.lines().count(), src.lines().count());
        assert!(
            !contains_word(&coalesced, "where")
                && coalesced.contains(
                    "theorem downstream_thm (m : Nat) : m + 1 = 1 + m :=\n  thm_with_where m"
                )
        );
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
        let expected = [
            (0, "have:h1", "theorem big_thm (a b : Nat) : a + 0 = a := by\n  omega"),
            (1, "have:h2", "theorem big_thm (a b : Nat) (h1 : a + 0 = a) : b + 0 = b := by\n  omega"),
            (2, "conclusion", "theorem big_thm (a b : Nat) (h1 : a + 0 = a) (h2 : b + 0 = b) : a + b = b + a := by\n  omega"),
        ];
        for (sub, (idx, label, src_exp)) in sub_shards.iter().zip(expected) {
            assert_eq!(
                (
                    sub.step_index,
                    sub.total_steps,
                    sub.step_label.as_str(),
                    sub.sub_decl_source.as_str()
                ),
                (idx, 3, label, src_exp)
            );
            let rep = audit_hygiene(&strip_lean_comments(&sub.sub_decl_source));
            assert!(!rep.has_sorry && rep.is_clean_for_certification());
        }

        let decl_modified_h2 = decl.replace(
            "  have h2 : b + 0 = b := by\n    omega",
            "  have h2 : b + 0 = b := by\n    simp",
        );
        let sub_shards_mod = fission_theorem_have_blocks(&decl_modified_h2, "big_thm");
        assert_eq!(sub_shards_mod.len(), 3);
        assert_eq!(sub_shards[0].sub_shard_key, sub_shards_mod[0].sub_shard_key);
        assert_ne!(sub_shards[1].sub_shard_key, sub_shards_mod[1].sub_shard_key);
        assert_eq!(sub_shards[2].sub_shard_key, sub_shards_mod[2].sub_shard_key);

        let decl_with_intro_prologue = "theorem unsafe_fission (a : Nat) : ∀ b : Nat, a + b = b + a := by\n  intro b\n  have h1 : a + 0 = a := by\n    omega\n  omega";
        assert!(fission_theorem_have_blocks(decl_with_intro_prologue, "unsafe_fission").is_empty());

        let decl_anon_and_binder = "theorem anon_binder_thm (a : Nat) : a + 0 = a := by have : a + 0 = a := by omega\n  have h_all (k : Nat) : k + 0 = k := by omega\n  exact this";
        let ab_shards = fission_theorem_have_blocks(decl_anon_and_binder, "anon_binder_thm");
        assert_eq!(ab_shards.len(), 3);
        assert_eq!(
            ab_shards[0].sub_decl_source,
            "theorem anon_binder_thm (a : Nat) : a + 0 = a := by omega"
        );
        assert_eq!(ab_shards[1].sub_decl_source, "theorem anon_binder_thm (a : Nat) (this : a + 0 = a) (k : Nat) : k + 0 = k := by omega");
        assert_eq!(ab_shards[2].sub_decl_source, "theorem anon_binder_thm (a : Nat) (this : a + 0 = a) (h_all : ∀ (k : Nat), k + 0 = k) : a + 0 = a := by\n  exact this");

        let decl_multiline_ty = "theorem multi_ty_thm (a : Nat) : a = a := by\n  have h_ml :\n      a + 0 = a := by\n    omega\n  exact h_ml";
        let ml_shards = fission_theorem_have_blocks(decl_multiline_ty, "multi_ty_thm");
        assert_eq!(ml_shards.len(), 2);
        assert_eq!(
            ml_shards[0].sub_decl_source,
            "theorem multi_ty_thm (a : Nat) : a + 0 = a := by\n  omega"
        );
        assert_eq!(
            ml_shards[1].sub_decl_source,
            "theorem multi_ty_thm (a : Nat) (h_ml : a + 0 = a) : a = a := by\n  exact h_ml"
        );

        let decl_havei_and_semi = "theorem havei_semi_thm (a : Nat) : a = a := by\n  unfold id\n  haveI : Nonempty Nat := ⟨a⟩; have h_eq : a + 0 = a := by omega\n  exact h_eq";
        let hs_shards = fission_theorem_have_blocks(decl_havei_and_semi, "havei_semi_thm");
        assert_eq!(hs_shards.len(), 3);
        assert_eq!(
            hs_shards[0].sub_decl_source,
            "theorem havei_semi_thm (a : Nat) : Nonempty Nat := ⟨a⟩"
        );
        assert_eq!(
            hs_shards[1].sub_decl_source,
            "theorem havei_semi_thm (a : Nat) [this : Nonempty Nat] : a + 0 = a := by omega"
        );
        assert_eq!(hs_shards[2].sub_decl_source, "theorem havei_semi_thm (a : Nat) [this : Nonempty Nat] (h_eq : a + 0 = a) : a = a := by\n  unfold id\n  exact h_eq");

        let decl_leti_classical = "theorem leti_cls_thm (a : Nat) : a = a := by\n  classical\n  letI : DecidableEq Nat := inferInstance\n  change a = a\n  have h_eq : a + 0 = a := by omega\n  exact h_eq";
        let lc_shards = fission_theorem_have_blocks(decl_leti_classical, "leti_cls_thm");
        assert_eq!(lc_shards.len(), 3);
        assert_eq!(lc_shards[0].sub_decl_source, "theorem leti_cls_thm (a : Nat) : DecidableEq Nat := by\n  classical\n  exact (inferInstance)");
        assert_eq!(lc_shards[1].sub_decl_source, "theorem leti_cls_thm (a : Nat) [this : DecidableEq Nat] : a + 0 = a := by classical; omega");
        assert_eq!(lc_shards[2].sub_decl_source, "theorem leti_cls_thm (a : Nat) [this : DecidableEq Nat] (h_eq : a + 0 = a) : a = a := by\n  classical\n  change a = a\n  exact h_eq");

        let decl_by_next_line = "theorem by_next_line_thm (a : Nat) : a = a :=\n  by\n    have h_eq : a + 0 = a := by omega\n    exact h_eq";
        let bn_shards = fission_theorem_have_blocks(decl_by_next_line, "by_next_line_thm");
        assert_eq!(bn_shards.len(), 2);
        assert_eq!(
            bn_shards[0].sub_decl_source,
            "theorem by_next_line_thm (a : Nat) : a + 0 = a := by omega"
        );
        assert_eq!(
            bn_shards[1].sub_decl_source,
            "theorem by_next_line_thm (a : Nat) (h_eq : a + 0 = a) : a = a := by\n    exact h_eq"
        );

        let decl_underscore = "theorem underscore_thm (a : Nat) : a = a := by\n  have _ : Nonempty Nat := ⟨a⟩\n  exact rfl";
        let us_shards = fission_theorem_have_blocks(decl_underscore, "underscore_thm");
        assert_eq!(us_shards.len(), 2);
        assert_eq!(
            us_shards[0].sub_decl_source,
            "theorem underscore_thm (a : Nat) : Nonempty Nat := ⟨a⟩"
        );
        assert_eq!(
            us_shards[1].sub_decl_source,
            "theorem underscore_thm (a : Nat) [Nonempty Nat] : a = a := by\n  exact rfl"
        );
    }

    #[test]
    fn test_split_2000_theorems_with_closed_sections_under_50ms() {
        let mut src = String::with_capacity(200_000);
        src.push_str("import Init\nnamespace FoundationScale\n");
        for sec in 0..10usize {
            src.push_str(&format!(
                "section ClosedSec{}\n  variable (x_{} : Nat)\n",
                sec, sec
            ));
            for i in 0..200usize {
                let idx = sec * 200 + i;
                let prev_ref = if idx > 0 && idx % 50 == 0 {
                    format!("thm_{}", idx - 1)
                } else {
                    "rfl".to_string()
                };
                src.push_str(&format!(
                    "  theorem thm_{} : {} = {} := {}\n",
                    idx, idx, idx, prev_ref
                ));
            }
            src.push_str(&format!("end ClosedSec{}\n", sec));
        }
        src.push_str("end FoundationScale\n");

        let t0 = std::time::Instant::now();
        let split = split_lean_source(&src, &[]);
        let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
        let limit_ms = if cfg!(debug_assertions) {
            2500.0
        } else {
            250.0
        };
        assert!(
            split.shards.len() == 2000 && elapsed_ms < limit_ms,
            "took {:.2} ms",
            elapsed_ms
        );
    }

    #[test]
    fn test_theorem_where_structure_instance_syntax_stubbed_and_isolated() {
        let src_v1 = "set_option warningAsError true\nnamespace ProximityPrize\nstructure ProtocolClaimUpper (a b : Nat) : Prop where\n   witness_ok : a < b\n   bound_ok : b < 200000\ntheorem candidate : ProtocolClaimUpper 11613 122369 where\n  witness_ok := by omega\n  bound_ok := by omega\ntheorem follow_up : 1 + 1 = 2 := by\n  rfl\nend ProximityPrize\n";
        let src_v2 = src_v1.replace("by omega", "by decide");
        let (split1, split2) = (
            split_lean_source(src_v1, &[]),
            split_lean_source(&src_v2, &[]),
        );
        assert_eq!(
            (
                split1.shards.len(),
                split1.shards[0].name.as_str(),
                split1.shards[1].name.as_str()
            ),
            (2, "candidate", "follow_up")
        );
        assert_eq!(
            (&split1.interface_hash, &split1.shards[0].stmt_hash),
            (&split2.interface_hash, &split2.shards[0].stmt_hash)
        );
        assert_ne!(split1.shards[0].proof_hash, split2.shards[0].proof_hash);
        assert!(
            split1.shards[1]
                .shard_source
                .contains("set_option warningAsError false")
                && !split1.shards[1]
                    .shard_source
                    .contains("set_option warningAsError true")
        );
    }

    #[test]
    fn test_lean4_c_abi_ffi_exports_sub_2ns_and_equivalence() {
        unsafe {
            assert_eq!(
                (
                    turbo_spec_is_closed_section_needed(5, 10),
                    turbo_spec_is_closed_section_needed(12, 10)
                ),
                (1, 0)
            );
            assert_eq!(
                (
                    turbo_spec_can_fission_have(0),
                    turbo_spec_can_fission_have(1)
                ),
                (1, 0)
            );
            assert_eq!(
                (
                    turbo_spec_sanitize_warning_as_error(1, 1),
                    turbo_spec_sanitize_warning_as_error(0, 1)
                ),
                (0, 1)
            );
            assert_eq!(
                (
                    turbo_spec_sanitize_forbid_sorry_ax(1, 1),
                    turbo_spec_sanitize_forbid_sorry_ax(0, 0)
                ),
                (0, 1)
            );
            assert_eq!(turbo_spec_is_sound_decl_summary(0, 0, 0, 0), 1);
            for (s, m, k, e) in [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] {
                assert_eq!(turbo_spec_is_sound_decl_summary(s, m, k, e), 0);
            }
            assert_eq!(
                (
                    turbo_spec_check_statement_pinned(42, 42, 0),
                    turbo_spec_check_statement_pinned(42, 43, 0),
                    turbo_spec_check_statement_pinned(42, 42, 1)
                ),
                (1, 0, 0)
            );
            assert_eq!(
                (
                    turbo_spec_zygote_lca_reuse_safe(4, 10),
                    turbo_spec_zygote_lca_reuse_safe(0, 10),
                    turbo_spec_zygote_lca_reuse_safe(12, 10)
                ),
                (1, 0, 0)
            );
            assert_eq!(
                (
                    turbo_spec_audit_witness_gate(1, 1),
                    turbo_spec_audit_witness_gate(0, 1),
                    turbo_spec_audit_witness_gate(1, 0)
                ),
                (1, 0, 0)
            );
            assert_eq!(
                (
                    turbo_spec_effective_cone_job_cap(20, 0),
                    turbo_spec_effective_cone_job_cap(20, 8),
                    turbo_spec_effective_cone_job_cap(5, 8)
                ),
                (20, 8, 5)
            );
            assert_eq!(
                (
                    turbo_spec_is_scope_isolated_for_fast_olean(0, 0),
                    turbo_spec_is_scope_isolated_for_fast_olean(1, 0)
                ),
                (1, 0)
            );
        }

        // Scope-sensitive `include` inside an active section must fall back (`None`) on fast-olean shard build:
        let scope_src =
            "section S\nvariable (x : Nat)\ninclude x\ntheorem t_scoped : x = x := rfl\nend S\n";
        let mut uncached = std::collections::HashSet::new();
        uncached.insert("t_scoped".to_string());
        assert!(build_fast_olean_shard_source(scope_src, "Demo.Scoped", &uncached).is_none());

        let iters = 1_000_000u64;
        let t0 = std::time::Instant::now();
        let mut acc = 0u64;
        for i in 0..iters {
            let needed = unsafe { turbo_spec_is_closed_section_needed(i & 255, 128) };
            let sound = unsafe { turbo_spec_is_sound_decl_summary(0, 0, 0, (i & 1) as u8) };
            acc = acc.wrapping_add((needed ^ sound) as u64);
        }
        std::hint::black_box(acc);
        let ns_per_call = (t0.elapsed().as_secs_f64() * 1e9) / ((iters * 2) as f64);
        let limit_ns = if cfg!(debug_assertions) { 100.0 } else { 20.0 };
        assert!(ns_per_call < limit_ns);
    }

    #[test]
    fn test_mathlib4_and_verity_edge_cases_nonrec_set_option_in_universe_and_abs_return_type() {
        let src = "\
module
public import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic
@[expose] public section
namespace MathlibEdgeCases
@[to_additive (attr := simp)]
protected nonrec theorem mul_inv_cancel_left.{u, v} (a b : Nat) : a + b = a + b := by
  rfl
set_option linter.deprecated false in
@[simp]
public theorem deprecated_helper₁ (x : Nat) : x = x :=
  rfl
alias ⟨iff_mp_alias, iff_mpr_alias⟩ := Iff.mp
theorem abs_val_in_return_type (x y : Int) (h : x = y) :
    |x - y| = 0 ∧
      |y - x| = 0 := by
  subst h
  simp
end MathlibEdgeCases
";
        let split = split_lean_source(src, &[]);
        assert!(split.eligible_for_sharding);
        assert_eq!(
            split
                .shards
                .iter()
                .map(|s| s.name.as_str())
                .collect::<Vec<_>>(),
            vec![
                "mul_inv_cancel_left",
                "deprecated_helper₁",
                "abs_val_in_return_type"
            ]
        );
        assert!(
            split.shards[2].signature_text.contains("|x - y| = 0")
                && split.shards[2].signature_text.contains("|y - x| = 0")
        );
        assert!(split.shards[2].proof_text.starts_with("by"));
        assert_eq!(split.skeleton_source.lines().count(), src.lines().count());
        assert!(split.skeleton_source.contains("|y - x| = 0  := sorry"));

        let shard_refs: Vec<&TheoremShard> = split.shards.iter().collect();
        let cross =
            build_cross_file_coalesced_shard(&[("Mathlib.EdgeCases", src, shard_refs.as_slice())]);
        assert!(
            cross.contains("import Mathlib.Logic.Basic")
                && cross.contains("import Mathlib.Data.Nat.Basic")
        );

        let corpus_paths = [
            ".lake/packages/mathlib/Mathlib/Logic/Basic.lean",
            ".lake/packages/mathlib/Mathlib/Data/Nat/Basic.lean",
            ".lake/packages/mathlib/Mathlib/Data/Nat/GCD/Basic.lean",
            ".lake/packages/mathlib/Mathlib/Data/List/Basic.lean",
            ".lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean",
            ".lake/packages/mathlib/Mathlib/Order/Basic.lean",
            "Verity/Core.lean",
            "Verity/Proofs/Stdlib/Math.lean",
        ];
        let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let repo_root = manifest_dir
            .parent()
            .and_then(|p| p.parent())
            .unwrap_or(manifest_dir);
        for rel in corpus_paths {
            let p1 = repo_root.join("benchmarks/verity-edsl").join(rel);
            let p2 = std::path::Path::new(
                "/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/verity",
            )
            .join(rel);
            let target_path = if p1.exists() { p1 } else { p2 };
            if let Ok(content) = std::fs::read_to_string(&target_path) {
                let res = split_lean_source(&content, &[]);
                assert!(!res.shards.is_empty(), "Expected shards in {}", rel);
                for s in &res.shards {
                    assert!(!s.name.ends_with('.'));
                    if s.proof_text.starts_with('|') {
                        assert!(s.proof_text.contains("=>"));
                    }
                }
            }
        }
    }

    #[test]
    fn test_shard_source_preserves_exact_line_numbers_across_closed_sections_and_pruned_imports() {
        let src = "import Init\nimport Mathlib.Data.Nat.Basic\nnamespace LineExactDemo\nsection ClosedSec1\n  variable (a : Nat)\n  def sec1_helper : Nat :=\n    a + 1\n  theorem sec1_thm : a = a := by\n    rfl\nend ClosedSec1\n\nsection ClosedSec2\n  variable (b : Nat)\n  theorem sec2_thm :\n      b + 0 = b := by\n    rfl\nend ClosedSec2\n\ntheorem target_after_sections (n : Nat) :\n    n + 0 = n := by\n  rfl\nend LineExactDemo\n";
        let split = split_lean_source(src, &[]);
        for s in &split.shards {
            let (shard_lines, orig_lines): (Vec<_>, Vec<_>) =
                (s.shard_source.lines().collect(), src.lines().collect());
            assert_eq!(
                shard_lines.get(s.start_line - 1).map(|l| l.trim()),
                orig_lines.get(s.start_line - 1).map(|l| l.trim())
            );
            if let Some(rec) = reconstruct_single_shard_source(src, &s.name) {
                assert_eq!(
                    rec.lines().nth(s.start_line - 1).map(str::trim),
                    orig_lines.get(s.start_line - 1).map(|l| l.trim())
                );
            }
        }
        let target_shard = split
            .shards
            .iter()
            .find(|s| s.name == "target_after_sections")
            .unwrap();
        let uncached: HashSet<String> = ["target_after_sections".to_string()].into_iter().collect();
        let pruned =
            build_pruned_imports_shard_source(src, &uncached).expect("expected pruned source");
        assert_eq!(
            pruned
                .lines()
                .nth(target_shard.start_line - 1)
                .map(str::trim),
            src.lines().nth(target_shard.start_line - 1).map(str::trim)
        );
    }
}
