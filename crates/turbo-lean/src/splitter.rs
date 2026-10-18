use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TheoremShard {
    pub name: String,
    pub kind: String,
    pub start_line: usize,
    pub end_line: usize,
    pub signature_text: String,
    pub proof_text: String,
    pub prefix_env_hash: String,
    pub stmt_hash: String,
    pub proof_hash: String,
    pub shard_source: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HygieneReport {
    pub has_sorry: bool,
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
            && !self.has_native_decide
            && !self.has_trust_compiler
            && !self.has_unsafe
            && !self.has_extern_or_implemented_by
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

/// Strip comments while preserving string literals and newline counts
pub fn strip_lean_comments(src: &str) -> String {
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
            // Line comment
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

    String::from_utf8_lossy(&out).to_string()
}

pub fn audit_hygiene(clean_src: &str) -> HygieneReport {
    let mut report = HygieneReport {
        has_sorry: false,
        has_native_decide: false,
        has_trust_compiler: false,
        has_unsafe: false,
        has_extern_or_implemented_by: false,
        has_impure_metaprograms: false,
        flagged_items: Vec::new(),
    };

    for (idx, line) in clean_src.lines().enumerate() {
        let ln = idx + 1;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if contains_word(trimmed, "sorry") || contains_word(trimmed, "admit") || contains_word(trimmed, "sorryAx") {
            report.has_sorry = true;
            report.flagged_items.push(format!("L{}: sorry/admit token", ln));
        }
        if contains_word(trimmed, "native_decide") || contains_word(trimmed, "ofReduceBool") {
            report.has_native_decide = true;
            report.flagged_items.push(format!("L{}: native_decide/ofReduceBool", ln));
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
            report.flagged_items.push(format!("L{}: unsafe declaration", ln));
        }
        if trimmed.contains("@[implemented_by")
            || trimmed.contains("@[extern")
            || trimmed.contains("@[csimp")
        {
            report.has_extern_or_implemented_by = true;
            report
                .flagged_items
                .push(format!("L{}: extern/implemented_by/csimp attribute", ln));
        }
        if trimmed.starts_with("#eval")
            || trimmed.starts_with("run_cmd")
            || trimmed.starts_with("#guard_msgs")
            || trimmed.starts_with("initialize ")
            || trimmed.starts_with("local syntax")
            || trimmed.starts_with("local macro")
            || trimmed.starts_with("local notation")
        {
            report.has_impure_metaprograms = true;
            report
                .flagged_items
                .push(format!("L{}: impure/reflective command `{}`", ln, trimmed.split_whitespace().next().unwrap_or("")));
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
        "end",
        "open ",
        "variable ",
        "variables ",
        "universe ",
        "universes ",
        "set_option ",
        "attribute ",
        "@",
        "private ",
        "protected ",
        "noncomputable ",
        "scoped ",
        "local ",
        "theorem ",
        "lemma ",
        "def ",
        "abbrev ",
        "instance ",
        "inductive ",
        "structure ",
        "class ",
        "axiom ",
        "opaque ",
        "mutual",
        "#check",
        "#eval",
        "#print",
        "#guard_msgs",
        "run_cmd",
        "initialize ",
        "syntax ",
        "macro ",
        "macro_rules",
        "elab ",
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
    false
}

fn classify_decl_header(cmd_text: &str) -> Option<(String, String)> {
    // Strip leading attributes like @[simp] or modifiers like private / protected / noncomputable
    let mut rest = cmd_text.trim_start();
    loop {
        if rest.starts_with("@[") {
            if let Some(close) = rest.find(']') {
                rest = rest[close + 1..].trim_start();
                continue;
            }
        }
        let mut stripped_mod = false;
        for m in ["private ", "protected ", "noncomputable ", "scoped ", "local "] {
            if rest.starts_with(m) {
                rest = rest[m.len()..].trim_start();
                stripped_mod = true;
                break;
            }
        }
        if !stripped_mod {
            break;
        }
    }

    for kw in ["theorem", "lemma"] {
        if let Some(after) = rest.strip_prefix(kw) {
            if after.starts_with(char::is_whitespace) {
                let name: String = after
                    .trim_start()
                    .chars()
                    .take_while(|c| !c.is_whitespace() && *c != '(' && *c != '{' && *c != '[' && *c != ':')
                    .collect();
                if !name.is_empty() {
                    return Some((kw.to_string(), name));
                }
            }
        }
    }
    None
}

/// Split a top-level theorem/lemma declaration at its top-level `:=` (outside parens/brackets/braces)
fn split_at_top_level_assign(cmd: &str) -> Option<(&str, &str)> {
    let bytes = cmd.as_bytes();
    let mut paren = 0i32;
    let mut bracket = 0i32;
    let mut brace = 0i32;
    let mut i = 0usize;
    let mut in_string = false;

    while i + 1 < bytes.len() {
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
            b':' if bytes[i + 1] == b'=' && paren == 0 && bracket == 0 && brace == 0 => {
                return Some((&cmd[..i], &cmd[i + 2..]));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Analyze and split a Lean 4 source file into:
/// 1. `skeleton_source`: all `Prop` theorem/lemma proof bodies replaced by `sorry` (preserving line counts)
/// 2. `interface_hash`: BLAKE3 of the proof-irrelevant interface (`Skeleton`)
/// 3. `shards`: per-theorem shards with acyclic `PrefixEnvHash` (depending only on declarations `1..i-1`)
pub fn split_lean_source(src: &str, dep_interface_hashes: &[String]) -> SplitResult {
    let clean = strip_lean_comments(src);
    let hygiene = audit_hygiene(&clean);

    let orig_lines: Vec<&str> = src.lines().collect();
    let clean_lines: Vec<&str> = clean.lines().collect();
    let total_lines = orig_lines.len();

    // Group lines into top-level commands
    #[derive(Clone)]
    struct CmdSpan {
        start_line: usize, // 1-indexed
        end_line: usize,   // 1-indexed inclusive
        orig_text: String,
        clean_text: String,
    }

    let mut spans: Vec<CmdSpan> = Vec::new();
    let mut cur_start = 1usize;

    for idx in 0..total_lines {
        let ln = idx + 1;
        let line_orig = orig_lines.get(idx).copied().unwrap_or("");
        let line_clean = clean_lines.get(idx).copied().unwrap_or("");
        let trimmed = line_clean.trim_start();
        let is_unindented = !line_orig.starts_with(' ') && !line_orig.starts_with('\t');
        let starts_doc_comment = is_unindented && line_orig.starts_with("/--");

        if ln > 1
            && is_unindented
            && (starts_doc_comment || (!trimmed.is_empty() && is_top_level_command_start(trimmed)))
        {
            // Don't split if the previous chunk is ONLY a doc-comment waiting for its declaration!
            if clean_lines[cur_start - 1..ln - 1]
                .iter()
                .any(|l| !l.trim().is_empty())
            {
                let prev_clean = clean_lines[cur_start - 1..ln - 1].join("\n");
                let orig_chunk = orig_lines[cur_start - 1..ln - 1].join("\n");
                spans.push(CmdSpan {
                    start_line: cur_start,
                    end_line: ln - 1,
                    orig_text: orig_chunk,
                    clean_text: prev_clean,
                });
                cur_start = ln;
            }
        }
    }
    if total_lines >= cur_start {
        spans.push(CmdSpan {
            start_line: cur_start,
            end_line: total_lines,
            orig_text: orig_lines[cur_start - 1..total_lines].join("\n"),
            clean_text: clean_lines[cur_start - 1..total_lines].join("\n"),
        });
    }

    let mut import_lines = Vec::new();
    let mut skeleton_chunks = Vec::with_capacity(spans.len());
    let mut prefix_hasher = blake3::Hasher::new();
    for dh in dep_interface_hashes {
        prefix_hasher.update(dh.as_bytes());
        prefix_hasher.update(b"\n");
    }

    let mut shards = Vec::new();
    let mut prefix_skeleton_accum = String::with_capacity(src.len());
    let mut scope_stack: Vec<(String, String)> = Vec::new();

    for span in &spans {
        let trimmed = span.clean_text.trim();
        if trimmed.starts_with("import ") {
            import_lines.push(span.orig_text.clone());
        }

        if let Some((kind, name)) = classify_decl_header(&span.clean_text) {
            if let Some((sig_clean, proof_clean)) = split_at_top_level_assign(&span.clean_text) {
                let (sig_orig, proof_orig) =
                    split_at_top_level_assign(&span.orig_text).unwrap_or((sig_clean, proof_clean));

                let prefix_env_hash = prefix_hasher.clone().finalize().to_hex().to_string();
                let normalized_sig = normalize_whitespace(sig_clean);
                let normalized_proof = normalize_whitespace(proof_clean);
                let stmt_hash = blake3::hash(normalized_sig.as_bytes()).to_hex().to_string();
                let proof_hash = blake3::hash(normalized_proof.as_bytes()).to_hex().to_string();

                // Build a line-preserving sorry replacement for the skeleton
                let proof_newlines = proof_orig.matches('\n').count();
                let padded_sorry = format!(" := sorry{}", "\n".repeat(proof_newlines));
                let skel_decl = format!("{}{}", sig_orig, padded_sorry);

                // Build self-contained shard source that includes only the prefix skeleton (declarations 1..i-1)
                // plus this single theorem's real proof, plus closing `end` scopes if needed.
                // For large files (`source.len() * spans.len() > 65_536`) when `target_decls` is empty,
                // omit materializing N copies of the prefix skeleton in memory (callers reconstruct on demand).
                let omit_shard_source = src.len().saturating_mul(spans.len()) > 65_536;
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
                    start_line: span.start_line,
                    end_line: span.end_line,
                    signature_text: sig_orig.trim().to_string(),
                    proof_text: proof_orig.trim().to_string(),
                    prefix_env_hash,
                    stmt_hash,
                    proof_hash,
                    shard_source,
                });

                // Advance prefix environment with ONLY the theorem's signature (proof-irrelevant!)
                prefix_hasher.update(normalized_sig.as_bytes());
                prefix_hasher.update(b" := sorry\n");
                prefix_skeleton_accum.push_str(&skel_decl);
                prefix_skeleton_accum.push('\n');
                skeleton_chunks.push(skel_decl);
                update_scope_stack(&mut scope_stack, &span.clean_text);
                continue;
            }
        }

        // Non-theorem command (import, open, variable, def, structure, instance, etc.)
        let norm_cmd = normalize_whitespace(&span.clean_text);
        if !norm_cmd.is_empty() {
            prefix_hasher.update(norm_cmd.as_bytes());
            prefix_hasher.update(b"\n");
        }
        prefix_skeleton_accum.push_str(&span.orig_text);
        prefix_skeleton_accum.push('\n');
        skeleton_chunks.push(span.orig_text.clone());
        update_scope_stack(&mut scope_stack, &span.clean_text);
    }

    let skeleton_source = skeleton_chunks.join("\n");
    let interface_hash = prefix_hasher.finalize().to_hex().to_string();
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

/// Reconstruct the self-contained prefix-only `shard_source` (`prefix_skeleton_accum + span.orig_text + closing_scopes`)
/// for a single theorem declaration `target_decl` on demand in $O(N)$ time and memory.
pub fn reconstruct_single_shard_source(src: &str, target_decl: &str) -> Option<String> {
    let clean = strip_lean_comments(src);
    let orig_lines: Vec<&str> = src.lines().collect();
    let clean_lines: Vec<&str> = clean.lines().collect();
    let total_lines = orig_lines.len();

    struct CmdSpan {
        orig_text: String,
        clean_text: String,
    }

    let mut spans: Vec<CmdSpan> = Vec::new();
    let mut cur_start = 1usize;

    for idx in 0..total_lines {
        let ln = idx + 1;
        let line_orig = orig_lines.get(idx).copied().unwrap_or("");
        let line_clean = clean_lines.get(idx).copied().unwrap_or("");
        let trimmed = line_clean.trim_start();
        let is_unindented = !line_orig.starts_with(' ') && !line_orig.starts_with('\t');
        let starts_doc_comment = is_unindented && line_orig.starts_with("/--");

        if ln > 1
            && is_unindented
            && (starts_doc_comment || (!trimmed.is_empty() && is_top_level_command_start(trimmed)))
        {
            if clean_lines[cur_start - 1..ln - 1]
                .iter()
                .any(|l| !l.trim().is_empty())
            {
                spans.push(CmdSpan {
                    orig_text: orig_lines[cur_start - 1..ln - 1].join("\n"),
                    clean_text: clean_lines[cur_start - 1..ln - 1].join("\n"),
                });
                cur_start = ln;
            }
        }
    }
    if total_lines >= cur_start {
        spans.push(CmdSpan {
            orig_text: orig_lines[cur_start - 1..total_lines].join("\n"),
            clean_text: clean_lines[cur_start - 1..total_lines].join("\n"),
        });
    }

    let mut prefix_skeleton_accum = String::with_capacity(src.len());
    let mut scope_stack: Vec<(String, String)> = Vec::new();

    for span in &spans {
        if let Some((_kind, name)) = classify_decl_header(&span.clean_text) {
            if let Some((sig_clean, proof_clean)) = split_at_top_level_assign(&span.clean_text) {
                let (sig_orig, proof_orig) =
                    split_at_top_level_assign(&span.orig_text).unwrap_or((sig_clean, proof_clean));
                let matches = name == target_decl
                    || name
                        .strip_suffix(target_decl)
                        .map(|p| p.ends_with('.'))
                        .unwrap_or(false)
                    || target_decl
                        .strip_suffix(&name)
                        .map(|p| p.ends_with('.'))
                        .unwrap_or(false);
                if matches {
                    let closing_scopes = format_closing_scopes(&scope_stack);
                    return Some(format!(
                        "{}\n{}\n{}",
                        prefix_skeleton_accum, span.orig_text, closing_scopes
                    ));
                }
                let proof_newlines = proof_orig.matches('\n').count();
                let padded_sorry = format!(" := sorry{}", "\n".repeat(proof_newlines));
                prefix_skeleton_accum.push_str(sig_orig);
                prefix_skeleton_accum.push_str(&padded_sorry);
                prefix_skeleton_accum.push('\n');
                update_scope_stack(&mut scope_stack, &span.clean_text);
                continue;
            }
        }
        prefix_skeleton_accum.push_str(&span.orig_text);
        prefix_skeleton_accum.push('\n');
        update_scope_stack(&mut scope_stack, &span.clean_text);
    }
    None
}

fn normalize_whitespace(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn update_scope_stack(stack: &mut Vec<(String, String)>, clean_chunk: &str) {
    for line in clean_chunk.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("namespace ") {
            let name = rest.split_whitespace().next().unwrap_or("").to_string();
            if !name.is_empty() {
                stack.push(("namespace".to_string(), name));
            }
        } else if trimmed == "section" || trimmed.starts_with("section ") {
            let name = trimmed
                .strip_prefix("section")
                .unwrap_or("")
                .split_whitespace()
                .next()
                .unwrap_or("")
                .to_string();
            stack.push(("section".to_string(), name));
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
                while let Some((_, top_name)) = stack.pop() {
                    if top_name == name {
                        break;
                    }
                }
            }
        }
    }
}

fn format_closing_scopes(stack: &[(String, String)]) -> String {
    let mut closers = Vec::with_capacity(stack.len());
    for (_, name) in stack.iter().rev() {
        if name.is_empty() {
            closers.push("end".to_string());
        } else {
            closers.push(format!("end {}", name));
        }
    }
    closers.join("\n")
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
    let orig_lines: Vec<&str> = src.lines().collect();
    let clean_lines: Vec<&str> = clean.lines().collect();
    let total_lines = orig_lines.len();

    struct CmdSpan {
        orig_text: String,
        clean_text: String,
    }

    let mut spans: Vec<CmdSpan> = Vec::new();
    let mut cur_start = 1usize;

    for idx in 0..total_lines {
        let ln = idx + 1;
        let line_orig = orig_lines.get(idx).copied().unwrap_or("");
        let line_clean = clean_lines.get(idx).copied().unwrap_or("");
        let trimmed = line_clean.trim_start();
        let is_unindented = !line_orig.starts_with(' ') && !line_orig.starts_with('\t');
        let starts_doc_comment = is_unindented && line_orig.starts_with("/--");

        if ln > 1
            && is_unindented
            && (starts_doc_comment || (!trimmed.is_empty() && is_top_level_command_start(trimmed)))
        {
            let prev_clean = clean_lines[cur_start - 1..ln - 1].join("\n");
            if !prev_clean.trim().is_empty() {
                let orig_chunk = orig_lines[cur_start - 1..ln - 1].join("\n");
                spans.push(CmdSpan {
                    orig_text: orig_chunk,
                    clean_text: prev_clean,
                });
                cur_start = ln;
            }
        }
    }
    if total_lines >= cur_start {
        spans.push(CmdSpan {
            orig_text: orig_lines[cur_start - 1..total_lines].join("\n"),
            clean_text: clean_lines[cur_start - 1..total_lines].join("\n"),
        });
    }

    let mut chunks = Vec::with_capacity(spans.len());
    for span in &spans {
        if let Some((_kind, name)) = classify_decl_header(&span.clean_text) {
            if !matches_uncached_or_fast_verify_name(&name, uncached_names) {
                let short = name.rsplit('.').next().unwrap_or(&name);
                if short.starts_with("_turbo_verify_") {
                    continue;
                }
                if let Some((sig_clean, proof_clean)) = split_at_top_level_assign(&span.clean_text)
                {
                    let (sig_orig, proof_orig) = split_at_top_level_assign(&span.orig_text)
                        .unwrap_or((sig_clean, proof_clean));
                    let proof_newlines = proof_orig.matches('\n').count();
                    let padded_sorry = format!(" := sorry{}", "\n".repeat(proof_newlines));
                    chunks.push(format!("{}{}", sig_orig, padded_sorry));
                    continue;
                }
            }
        }
        chunks.push(span.orig_text.clone());
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
        if idx == q_start
            || (!bytes[idx - 1].is_ascii_alphanumeric() && bytes[idx - 1] != b'_')
        {
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
                    .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
                    .collect();
                let u_short_safe: String = u_short
                    .chars()
                    .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
                    .collect();
                orig_safe == u_safe || orig_safe == u_short_safe
            });
        }
    }
    false
}

fn is_scope_or_context_command(clean_text: &str) -> bool {
    let trimmed = clean_text.trim();
    if trimmed.starts_with("set_option ") && (trimmed.ends_with(" in") || trimmed.contains(" in\n"))
    {
        return false;
    }
    for prefix in [
        "namespace ",
        "section",
        "end",
        "open ",
        "variable ",
        "variables ",
        "universe ",
        "universes ",
        "set_option ",
    ] {
        if trimmed == prefix || trimmed.starts_with(prefix) {
            return true;
        }
    }
    false
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
    let safe_name: String = decl_name
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
        .collect();
    let replacement = format!("_turbo_verify_{}_{}", idx, safe_name);

    for kw in ["theorem", "lemma"] {
        for (kw_pos, _) in sig_clean.match_indices(kw) {
            let after_kw = &sig_clean[kw_pos + kw.len()..];
            if let Some(name_rel_pos) = after_kw.find(decl_name) {
                let prefix_between = &after_kw[..name_rel_pos];
                if !prefix_between.is_empty() && prefix_between.chars().all(char::is_whitespace) {
                    let abs_name_start = kw_pos + kw.len() + name_rel_pos;
                    let abs_name_end = abs_name_start + decl_name.len();
                    return Some(format!(
                        "{}{}{}:={}",
                        &sig_orig[..abs_name_start],
                        replacement,
                        &sig_orig[abs_name_end..],
                        proof_orig
                    ));
                }
            }
        }
    }
    None
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

    for (idx, shard) in split.shards.iter().enumerate() {
        if matches_uncached_name(&shard.name, uncached_names)
            && !shard_is_acyclic_for_fast_import(&split.shards, idx)
        {
            return None;
        }
    }

    let clean = strip_lean_comments(src);
    let orig_lines: Vec<&str> = src.lines().collect();
    let clean_lines: Vec<&str> = clean.lines().collect();
    let total_lines = orig_lines.len();

    struct CmdSpan {
        orig_text: String,
        clean_text: String,
    }

    let mut spans: Vec<CmdSpan> = Vec::new();
    let mut cur_start = 1usize;

    for idx in 0..total_lines {
        let ln = idx + 1;
        let line_orig = orig_lines.get(idx).copied().unwrap_or("");
        let line_clean = clean_lines.get(idx).copied().unwrap_or("");
        let trimmed = line_clean.trim_start();
        let is_unindented = !line_orig.starts_with(' ') && !line_orig.starts_with('\t');
        let starts_doc_comment = is_unindented && line_orig.starts_with("/--");

        if ln > 1
            && is_unindented
            && (starts_doc_comment || (!trimmed.is_empty() && is_top_level_command_start(trimmed)))
        {
            if clean_lines[cur_start - 1..ln - 1]
                .iter()
                .any(|l| !l.trim().is_empty())
            {
                let prev_clean = clean_lines[cur_start - 1..ln - 1].join("\n");
                let orig_chunk = orig_lines[cur_start - 1..ln - 1].join("\n");
                spans.push(CmdSpan {
                    orig_text: orig_chunk,
                    clean_text: prev_clean,
                });
                cur_start = ln;
            }
        }
    }
    if total_lines >= cur_start {
        spans.push(CmdSpan {
            orig_text: orig_lines[cur_start - 1..total_lines].join("\n"),
            clean_text: clean_lines[cur_start - 1..total_lines].join("\n"),
        });
    }

    let mut last_uncached_span_idx = None;
    for (s_idx, span) in spans.iter().enumerate() {
        if let Some((_kind, name)) = classify_decl_header(&span.clean_text) {
            if split_at_top_level_assign(&span.clean_text).is_some()
                && matches_uncached_name(&name, uncached_names)
            {
                last_uncached_span_idx = Some(s_idx);
            }
        }
    }
    let last_span_idx = last_uncached_span_idx?;

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
    let mut scope_stack: Vec<(String, String)> = Vec::new();
    for span in &spans[..=last_span_idx] {
        if let Some((_kind, name)) = classify_decl_header(&span.clean_text) {
            if split_at_top_level_assign(&span.clean_text).is_some() {
                let cur_idx = thm_idx;
                thm_idx += 1;
                if matches_uncached_name(&name, uncached_names) {
                    let renamed = rename_decl_header_for_fast_check(
                        &span.orig_text,
                        &span.clean_text,
                        &name,
                        cur_idx,
                    )?;
                    chunks.push(renamed);
                }
                update_scope_stack(&mut scope_stack, &span.clean_text);
                continue;
            }
        }
        if is_scope_or_context_command(&span.clean_text) {
            chunks.push(span.orig_text.clone());
        }
        update_scope_stack(&mut scope_stack, &span.clean_text);
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
    if !src.contains("import Mathlib") && !src.contains("import Aesop") {
        return None;
    }

    let clean = strip_lean_comments(src);
    let orig_lines: Vec<&str> = src.lines().collect();
    let clean_lines: Vec<&str> = clean.lines().collect();
    let total_lines = orig_lines.len();

    struct CmdSpan {
        orig_text: String,
        clean_text: String,
    }

    let mut spans: Vec<CmdSpan> = Vec::new();
    let mut cur_start = 1usize;

    for idx in 0..total_lines {
        let ln = idx + 1;
        let line_orig = orig_lines.get(idx).copied().unwrap_or("");
        let line_clean = clean_lines.get(idx).copied().unwrap_or("");
        let trimmed = line_clean.trim_start();
        let is_unindented = !line_orig.starts_with(' ') && !line_orig.starts_with('\t');
        let starts_doc_comment = is_unindented && line_orig.starts_with("/--");

        if ln > 1
            && is_unindented
            && (starts_doc_comment || (!trimmed.is_empty() && is_top_level_command_start(trimmed)))
        {
            if clean_lines[cur_start - 1..ln - 1]
                .iter()
                .any(|l| !l.trim().is_empty())
            {
                spans.push(CmdSpan {
                    orig_text: orig_lines[cur_start - 1..ln - 1].join("\n"),
                    clean_text: clean_lines[cur_start - 1..ln - 1].join("\n"),
                });
                cur_start = ln;
            }
        }
    }
    if total_lines >= cur_start {
        spans.push(CmdSpan {
            orig_text: orig_lines[cur_start - 1..total_lines].join("\n"),
            clean_text: clean_lines[cur_start - 1..total_lines].join("\n"),
        });
    }

    let mut last_uncached_span_idx = None;
    for (s_idx, span) in spans.iter().enumerate() {
        if let Some((_kind, name)) = classify_decl_header(&span.clean_text) {
            if split_at_top_level_assign(&span.clean_text).is_some()
                && matches_uncached_name(&name, uncached_names)
            {
                last_uncached_span_idx = Some(s_idx);
            }
        }
    }
    let last_span_idx = last_uncached_span_idx?;

    let mut out_chunks = Vec::with_capacity(last_span_idx + 2);
    let mut scope_stack: Vec<(String, String)> = Vec::new();
    let mut pruned_imports = 0usize;

    for span in &spans[..=last_span_idx] {
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

        if let Some((_kind, name)) = classify_decl_header(&span.clean_text) {
            if let Some((sig_clean, proof_clean)) = split_at_top_level_assign(&span.clean_text) {
                let (sig_orig, proof_orig) =
                    split_at_top_level_assign(&span.orig_text).unwrap_or((sig_clean, proof_clean));
                if matches_uncached_name(&name, uncached_names) {
                    if contains_mathlib_tactic_or_namespace(&span.clean_text) {
                        return None;
                    }
                    out_chunks.push(span.orig_text.clone());
                } else {
                    if contains_mathlib_tactic_or_namespace(sig_clean) {
                        return None;
                    }
                    let proof_newlines = proof_orig.matches('\n').count();
                    let padded_sorry = format!(" := sorry{}", "\n".repeat(proof_newlines));
                    out_chunks.push(format!("{}{}", sig_orig, padded_sorry));
                }
                update_scope_stack(&mut scope_stack, &span.clean_text);
                continue;
            }
        }

        if contains_mathlib_tactic_or_namespace(&span.clean_text) {
            return None;
        }
        out_chunks.push(span.orig_text.clone());
        update_scope_stack(&mut scope_stack, &span.clean_text);
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
    if !split.eligible_for_sharding || split.shards.is_empty() {
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

        let split = split_lean_source(src, &[]);
        for imp_line in split.imports_header.lines() {
            let trimmed = imp_line.trim();
            if trimmed.starts_with("import ") && seen_imports.insert(trimmed.to_string()) {
                all_imports.push(trimmed.to_string());
            }
        }
        let mod_imp_stmt = format!("import {}", module_import);
        if seen_imports.insert(mod_imp_stmt.clone()) {
            all_imports.push(mod_imp_stmt);
        }

        let clean = strip_lean_comments(src);
        let orig_lines: Vec<&str> = src.lines().collect();
        let clean_lines: Vec<&str> = clean.lines().collect();
        let total_lines = orig_lines.len();

        struct CmdSpan {
            orig_text: String,
            clean_text: String,
        }

        let mut spans: Vec<CmdSpan> = Vec::new();
        let mut cur_start = 1usize;

        for idx in 0..total_lines {
            let ln = idx + 1;
            let line_orig = orig_lines.get(idx).copied().unwrap_or("");
            let line_clean = clean_lines.get(idx).copied().unwrap_or("");
            let trimmed = line_clean.trim_start();
            let is_unindented = !line_orig.starts_with(' ') && !line_orig.starts_with('\t');
            let starts_doc_comment = is_unindented && line_orig.starts_with("/--");

            if ln > 1
                && is_unindented
                && (starts_doc_comment
                    || (!trimmed.is_empty() && is_top_level_command_start(trimmed)))
            {
                let prev_clean = clean_lines[cur_start - 1..ln - 1].join("\n");
                if !prev_clean.trim().is_empty() {
                    let orig_chunk = orig_lines[cur_start - 1..ln - 1].join("\n");
                    spans.push(CmdSpan {
                        orig_text: orig_chunk,
                        clean_text: prev_clean,
                    });
                    cur_start = ln;
                }
            }
        }
        if total_lines >= cur_start {
            spans.push(CmdSpan {
                orig_text: orig_lines[cur_start - 1..total_lines].join("\n"),
                clean_text: clean_lines[cur_start - 1..total_lines].join("\n"),
            });
        }

        let iso_ns = format!("_TurboCrossFileShard_{}", file_idx);
        let mut block_chunks = Vec::new();
        block_chunks.push(format!("namespace {}\nend {}", iso_ns, iso_ns));
        block_chunks.push(format!("section {}", iso_ns));

        let mut scope_stack: Vec<(String, String)> = Vec::new();
        let mut thm_idx = 0usize;
        let base_idx = (file_idx + 1) * 10000;

        for span in &spans {
            if let Some((_kind, name)) = classify_decl_header(&span.clean_text) {
                if split_at_top_level_assign(&span.clean_text).is_some() {
                    let cur_idx = base_idx + thm_idx;
                    thm_idx += 1;
                    if uncached_names.contains(&name) {
                        if let Some(renamed) = rename_decl_header_for_fast_check(
                            &span.orig_text,
                            &span.clean_text,
                            &name,
                            cur_idx,
                        ) {
                            block_chunks.push(renamed);
                        }
                    }
                    update_scope_stack(&mut scope_stack, &span.clean_text);
                    continue;
                }
            }
            if is_scope_or_context_command(&span.clean_text) {
                block_chunks.push(span.orig_text.clone());
                update_scope_stack(&mut scope_stack, &span.clean_text);
            }
        }

        let rem_closers = format_closing_scopes(&scope_stack);
        if !rem_closers.trim().is_empty() {
            block_chunks.push(rem_closers);
        }
        block_chunks.push(format!("end {}", iso_ns));
        file_bodies.push(block_chunks.join("\n"));
    }

    let mut out = Vec::new();
    if !all_imports.is_empty() {
        out.push(all_imports.join("\n"));
    }
    out.extend(file_bodies);
    out.join("\n\n")
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
}
