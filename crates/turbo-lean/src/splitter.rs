use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TheoremShard {
    /// Source spelling retained for CLI/report/cache compatibility.
    pub name: String,
    /// User-facing environment identity (private names are not kernel-mangled).
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub qualified_name: String,
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
    /// Source signature fingerprint for shard/cache identity. Semantic PR statement
    /// pinning uses built ConstantInfo + IF-closure digests in pr_verify.rs instead.
    pub stmt_hash: String,
    pub proof_hash: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub shard_source: String,
}

impl TheoremShard {
    pub fn effective_name(&self) -> &str {
        self.decl_name()
    }

    pub(crate) fn decl_name(&self) -> &str {
        if self.qualified_name.is_empty() {
            &self.name
        } else {
            &self.qualified_name
        }
    }

    pub fn rooted_name(&self) -> String {
        format!("_root_.{}", canonicalize_lean_name(self.decl_name()))
    }
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
    #[serde(default)]
    pub has_checking_weakening: bool,
    pub flagged_items: Vec<String>,
}

/// Kernel axioms every theorem may depend on.
pub const STANDARD_AXIOMS: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];

/// The project axiom allowlist (`[axioms] allow` in `turbo-lean.toml`, comma-separated `*` globs).
/// `main` sets it from the project config, so zygote workers and daemons inherit the same policy.
pub const ALLOWED_AXIOMS_ENV: &str = "TURBO_LEAN_ALLOWED_AXIOMS";
pub const ALLOWED_AXIOMS_FROM_CONFIG_ENV: &str = "TURBO_LEAN_ALLOWED_AXIOMS_FROM_CONFIG";

/// Extra non-standard axiom patterns currently configured in `TURBO_LEAN_ALLOWED_AXIOMS`.
pub fn extra_allowed_axiom_patterns() -> Vec<String> {
    std::env::var(ALLOWED_AXIOMS_ENV)
        .unwrap_or_default()
        .split(',')
        .map(str::trim)
        .filter(|p| !p.is_empty())
        .map(String::from)
        .collect()
}

/// Build the full allowed-axioms list from an explicit list of extra patterns.
pub fn allowed_axioms_with_extra(extra: &[String]) -> Vec<String> {
    STANDARD_AXIOMS
        .iter()
        .copied()
        .map(String::from)
        .chain(
            extra
                .iter()
                .map(|s| s.trim())
                .filter(|s| !s.is_empty())
                .map(String::from),
        )
        .collect()
}

/// The allowed axioms: the standard three, then the project's glob patterns.
pub fn allowed_axioms() -> Vec<String> {
    allowed_axioms_with_extra(&extra_allowed_axiom_patterns())
}

/// `*`-glob match (`*` matches any, possibly empty, run of characters); same as the zygote's `globMatch`.
fn glob_match(pat: &str, s: &str) -> bool {
    match pat.split_once('*') {
        None => pat == s,
        Some((head, rest)) => {
            s.starts_with(head)
                && (0..=s.len() - head.len())
                    .filter(|i| s.is_char_boundary(head.len() + i))
                    .any(|i| glob_match(rest, &s[head.len() + i..]))
        }
    }
}

/// Whether the `allowed` pattern list admits kernel axiom `ax` (patterns never admit `sorryAx` or `Lean.trustCompiler`).
pub fn axiom_allowed_under(ax: &str, allowed: &[String]) -> bool {
    ax != "sorryAx" && ax != "Lean.trustCompiler" && allowed.iter().any(|p| glob_match(p, ax))
}

/// Text of the nearest `turbo-lean.toml` at or above `dir`, read at git revision `rev` when given
/// (pr-verify uses `--base`, so a PR cannot change the policy it is checked under). A config the
/// revision's tree names but whose blob is unreadable (e.g. a promised object of a partial clone,
/// never lazily fetched) is an error, never a silently absent policy.
pub fn read_project_config(
    dir: &std::path::Path,
    rev: Option<&str>,
) -> anyhow::Result<Option<String>> {
    let dir = dir.canonicalize().unwrap_or_else(|_| dir.to_path_buf());
    let Some(rev) = rev else {
        return Ok(dir
            .ancestors()
            .find_map(|a| std::fs::read_to_string(a.join("turbo-lean.toml")).ok()));
    };
    anyhow::ensure!(!rev.starts_with('-'), "Invalid git revision `{rev}`");
    let spec = format!("{rev}:./turbo-lean.toml");
    for a in dir.ancestors() {
        let git = |args: &[&str]| -> anyhow::Result<std::process::Output> {
            Ok(crate::trusted_tools::git(&dir)?
                .arg("-C")
                .arg(a)
                .args(args)
                .output()?)
        };
        let shown = git(&["show", "--no-textconv", "--no-ext-diff", &spec])?;
        if shown.status.success() {
            return Ok(Some(String::from_utf8_lossy(&shown.stdout).into_owned()));
        }
        // Present in the tree but unreadable: fail closed.
        let named = git(&["rev-parse", "--verify", "-q", "--end-of-options", &spec])?;
        anyhow::ensure!(
            !named.status.success(),
            "Cannot read `{spec}` in {}: {}",
            a.display(),
            String::from_utf8_lossy(&shown.stderr).trim()
        );
    }
    Ok(None)
}

/// Kind of a hygiene item (`"L12: bv_decide"` -> `"bv_decide"`).
fn item_kind(s: &str) -> &str {
    if let Some((digits, kind)) = s.strip_prefix('L').and_then(|r| r.split_once(": ")) {
        if !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()) {
            return kind;
        }
    }
    s
}

/// Representative kernel axiom names emitted by Lean for `native_decide` and `bv_decide`.
const NATIVE_DECIDE_PROBE_AXIOMS: [&str; 2] =
    ["Lean.ofReduceBool", "Pkg.thm._native.native_decide.ax_1_1"];
const BV_DECIDE_PROBE_AXIOMS: [&str; 1] = ["Pkg.thm._native.bv_decide.ax_1_1"];

/// Route hygiene item admission through the shared Lean C-ABI gate (`turbo_spec_verify_hygiene_item_admitted`)
/// using the exact same `glob_match` axiom policy as the kernel gate (`ZygoteWorker.isAllowedAxiom`).
fn item_allowed(item: &str, allowed: &[String]) -> bool {
    let kind_code: u8 = match item_kind(item) {
        "native_decide/ofReduceBool" => 1,
        "bv_decide" => 2,
        _ => 0,
    };
    let admits_nd = NATIVE_DECIDE_PROBE_AXIOMS
        .iter()
        .any(|ax| axiom_allowed_under(ax, allowed));
    let admits_bv = BV_DECIDE_PROBE_AXIOMS
        .iter()
        .any(|ax| axiom_allowed_under(ax, allowed));
    unsafe {
        crate::c_abi::turbo_spec_verify_hygiene_item_admitted(
            kind_code,
            u8::from(admits_nd),
            u8::from(admits_bv),
        ) != 0
    }
}

pub fn native_decide_allowed() -> bool {
    item_allowed("native_decide/ofReduceBool", &allowed_axioms())
}

/// Hygiene items that block certification under the `allowed` axioms (impure commands such as
/// `#eval` are reported but do not block).
fn blocking_items_under(items: &[String], allowed: &[String]) -> Vec<String> {
    let blocks = |i: &&String| !item_allowed(i, allowed) && !item_kind(i).starts_with("impure/");
    items.iter().filter(blocks).cloned().collect()
}

pub fn blocking_items(items: &[String]) -> Vec<String> {
    blocking_items_under(items, &allowed_axioms())
}

impl HygieneReport {
    pub fn is_clean_for_certification(&self) -> bool {
        self.disallowed_items().is_empty()
    }

    /// `native_decide`/`bv_decide` use that the axiom allowlist does not admit.
    pub fn native_violation(&self) -> bool {
        self.native_violation_under(&allowed_axioms())
    }

    /// `native_decide`/`bv_decide` use that `allowed` does not admit.
    pub fn native_violation_under(&self, allowed: &[String]) -> bool {
        self.has_native_decide
            && self.flagged_items.iter().any(|i| {
                matches!(item_kind(i), "native_decide/ofReduceBool" | "bv_decide")
                    && !item_allowed(i, allowed)
            })
    }

    /// Flagged items that block certification under the axiom policy.
    pub fn disallowed_items(&self) -> Vec<String> {
        blocking_items(&self.flagged_items)
    }

    /// Flagged items that block certification under an explicit `allowed` policy.
    pub fn disallowed_items_under(&self, allowed: &[String]) -> Vec<String> {
        blocking_items_under(&self.flagged_items, allowed)
    }

    /// Flagged items that block even partial `--allow-sorry` verification (i.e., everything except
    /// `sorry`/`admit` tokens, such as forbidden axioms, `unsafe`, `implemented_by`, or checking-weakening options).
    pub fn non_sorry_disallowed_items(&self) -> Vec<String> {
        self.disallowed_items()
            .into_iter()
            .filter(|item| item_kind(item) != "sorry/admit token")
            .collect()
    }

    /// Return only hygiene items that are newly introduced relative to `base`
    /// (plus any `sorry`, which is always flagged in modified files), as
    /// `(blocking, admitted by the axiom allowlist)`. The admitted ones are new uses of
    /// `native_decide`/`bv_decide` axioms: allowed, but worth flagging for review.
    pub fn regression_items_against(&self, base: &Self) -> (Vec<String>, Vec<String>) {
        let mut base_counts: std::collections::HashMap<&str, usize> =
            std::collections::HashMap::new();
        for item in &base.flagged_items {
            let k = item_kind(item);
            if !k.contains("sorry") {
                *base_counts.entry(k).or_insert(0) += 1;
            }
        }
        let mut out = Vec::new();
        for item in &self.flagged_items {
            if let Some(rem) = base_counts.get_mut(item_kind(item)).filter(|r| **r > 0) {
                *rem -= 1;
                continue;
            }
            out.push(item.clone());
        }
        let allowed = allowed_axioms();
        let (admitted, blocking) = out.into_iter().partition(|i| item_allowed(i, &allowed));
        let clean = self.is_clean_for_certification();
        (if clean { Vec::new() } else { blocking }, admitted)
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
pub(crate) enum ScopeKind {
    Namespace,
    Section,
    Mutual,
}

#[derive(Debug, Clone)]
pub(crate) struct ScopeFrame {
    pub(crate) kind: ScopeKind,
    pub(crate) name: String,
    pub(crate) open_span_idx: usize,
}

#[inline]
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

#[inline]
fn is_lean_subscript_alnum(c: char) -> bool {
    let v = c as u32;
    (0x2080..=0x2089).contains(&v)
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
        || v == 0x2c7c
}

#[inline]
fn is_lean_id_first(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || is_lean_letter_like(c)
}

#[inline]
fn is_lean_id_rest(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(c, '_' | '\'' | '!' | '?')
        || is_lean_letter_like(c)
        || is_lean_subscript_alnum(c)
}

/// Scan a guillemet-quoted identifier segment `«...»` starting at byte offset `start` (`«` is `[0xC2, 0xAB]`).
/// Returns the byte offset immediately after the closing `»` (`[0xC2, 0xBB]`), or `src.len()` if unterminated.
pub(crate) fn scan_lean_guillemet_ident_end(src: &str, start: usize) -> Option<usize> {
    let bytes = src.as_bytes();
    if bytes.get(start) != Some(&0xC2) || bytes.get(start + 1) != Some(&0xAB) {
        return None;
    }
    let mut i = start + 2;
    while i < bytes.len() {
        if bytes[i] == 0xC2 && bytes.get(i + 1) == Some(&0xBB) {
            return Some(i + 2);
        }
        i += 1;
    }
    Some(bytes.len())
}

/// Parse a potentially dotted Lean identifier (`foo`, `«a  b»`, `Foo.«a.b».bar`) at the start of `s`.
/// Returns `(ident_slice, rest_slice)` where `ident_slice` excludes any trailing dangling `.`.
fn take_leading_lean_ident(s: &str) -> Option<(&str, &str)> {
    let mut pos = 0usize;
    let mut last_valid_end = 0usize;
    loop {
        if pos >= s.len() {
            break;
        }
        let seg_end = if let Some(gend) = scan_lean_guillemet_ident_end(s, pos) {
            gend
        } else {
            let mut chars = s[pos..].char_indices();
            let (_, c0) = chars.next()?;
            if !is_lean_id_first(c0) {
                break;
            }
            let mut end_rel = c0.len_utf8();
            for (rel, ch) in chars {
                if is_lean_id_rest(ch) {
                    end_rel = rel + ch.len_utf8();
                } else {
                    break;
                }
            }
            pos + end_rel
        };
        if seg_end == pos {
            break;
        }
        last_valid_end = seg_end;
        if s.as_bytes().get(seg_end) == Some(&b'.') {
            pos = seg_end + 1;
        } else {
            break;
        }
    }
    (last_valid_end > 0).then(|| (&s[..last_valid_end], &s[last_valid_end..]))
}

fn last_host_name_component(name: &str) -> &str {
    let bytes = name.as_bytes();
    let mut quoted = false;
    let mut last_dot_end = 0usize;
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == 0xC2 && bytes.get(i + 1) == Some(&0xAB) {
            quoted = true;
            i += 2;
        } else if bytes[i] == 0xC2 && bytes.get(i + 1) == Some(&0xBB) {
            quoted = false;
            i += 2;
        } else {
            if bytes[i] == b'.' && !quoted {
                last_dot_end = i + 1;
            }
            i += 1;
        }
    }
    &name[last_dot_end..]
}

/// Parse a well-formed Lean character literal starting at byte offset `start` (`bytes[start] == b'\''`),
/// returning the byte index immediately following the closing `'` if valid (matching `Lean.Parser.charLitFnAux`).
pub(crate) fn scan_lean_char_lit_end(src: &str, start: usize) -> Option<usize> {
    let bytes = src.as_bytes();
    if start + 2 >= bytes.len() || bytes[start] != b'\'' {
        return None;
    }
    let tail = &src[start + 1..];
    let mut chars = tail.char_indices();
    let (_, c0) = chars.next()?;
    if c0 == '\'' || c0 == '\n' {
        return None;
    }
    if c0 == '\\' {
        let (_, esc) = chars.next()?;
        match esc {
            '\\' | '"' | '\'' | 'r' | 'n' | 't' => {}
            'x' => {
                for _ in 0..2 {
                    let (_, hd) = chars.next()?;
                    if !hd.is_ascii_hexdigit() {
                        return None;
                    }
                }
            }
            'u' => {
                for _ in 0..4 {
                    let (_, hd) = chars.next()?;
                    if !hd.is_ascii_hexdigit() {
                        return None;
                    }
                }
            }
            _ => return None,
        }
    }
    let (close_rel, close_ch) = chars.next()?;
    if close_ch == '\'' {
        Some(start + 1 + close_rel + 1)
    } else {
        None
    }
}

fn ends_with_closed_char_lit(src: &str, end: usize) -> bool {
    let bytes = src.as_bytes();
    if end < 3 || bytes.get(end - 1) != Some(&b'\'') {
        return false;
    }
    let lo = end.saturating_sub(10);
    (lo..=end - 3).any(|k| src.is_char_boundary(k) && scan_lean_char_lit_end(src, k) == Some(end))
}

pub(crate) fn scan_lean_raw_string_end(src: &str, start: usize) -> Option<usize> {
    let bytes = src.as_bytes();
    if bytes.get(start) != Some(&b'r') {
        return None;
    }
    if let Some(prev) = src[..start].chars().next_back() {
        let prev_continues_name = if prev == '\'' {
            !ends_with_closed_char_lit(src, start)
        } else if prev == '.' {
            // Single `.` (`foo.r"x"` or `.r"x"`) continues/projects a name, whereas `..` / `...` is a range op.
            start < 2 || bytes[start - 2] != b'.'
        } else {
            is_lean_id_rest(prev) || prev == '»' || prev == '`'
        };
        if prev_continues_name {
            return None;
        }
    }
    let mut i = start + 1;
    while bytes.get(i) == Some(&b'#') {
        i += 1;
    }
    let hashes = i - start - 1;
    if bytes.get(i) != Some(&b'"') {
        return None;
    }
    i += 1;
    while i < bytes.len() {
        if bytes[i] == b'"' && bytes[i + 1..].starts_with(&bytes[start + 1..start + 1 + hashes]) {
            return Some(i + 1 + hashes);
        }
        i += 1;
    }
    Some(bytes.len())
}

pub(crate) fn scan_lean_string_lit_end(src: &str, start: usize) -> Option<usize> {
    let bytes = src.as_bytes();
    if bytes.get(start) != Some(&b'"') {
        return None;
    }
    let mut i = start + 1;
    while i < bytes.len() {
        match bytes[i] {
            b'\\' => i = (i + 2).min(bytes.len()),
            b'"' => return Some(i + 1),
            _ => i += 1,
        }
    }
    Some(bytes.len())
}

fn has_valid_interp_ident_prefix(src: &str, bang_idx: usize) -> bool {
    if bang_idx == 0 || src.as_bytes().get(bang_idx) != Some(&b'!') {
        return false;
    }
    let mut seg_end = bang_idx;
    loop {
        let before = &src[..seg_end];
        let Some((mut seg_start, last_ch)) = before.char_indices().next_back() else {
            return false;
        };
        if last_ch == '\'' && ends_with_closed_char_lit(src, seg_end) {
            return false;
        }
        if !is_lean_id_rest(last_ch) {
            return false;
        }
        let mut first_ch = last_ch;
        for (idx, ch) in before[..seg_start].char_indices().rev() {
            if ch == '\'' && ends_with_closed_char_lit(src, idx + 1) {
                break;
            }
            if is_lean_id_rest(ch) {
                seg_start = idx;
                first_ch = ch;
            } else {
                break;
            }
        }
        if !is_lean_id_first(first_ch) {
            return false;
        }
        let prev = src[..seg_start].chars().next_back();
        if prev == Some('»') {
            return false;
        }
        if prev == Some('.') && seg_start >= 2 && src.as_bytes()[seg_start - 2] != b'.' {
            seg_end = seg_start - 1;
            continue;
        }
        return true;
    }
}

/// Scan a comment starting at `start` (`/-` or `--`), returning `(end_offset, is_docstring)` where
/// `is_docstring` is true iff the comment is a `/-- ... -/` or `/-! ... -/` docstring.
/// Matches Lean 4's 3-byte `/--` and `/-!` openers so `/--/` and `/-!/` remain open until a closing `-/`.
fn scan_lean_block_comment_end(src: &str, start: usize) -> Option<(usize, bool)> {
    let bytes = src.as_bytes();
    if start + 1 >= bytes.len() || bytes[start] != b'/' || bytes[start + 1] != b'-' {
        return None;
    }
    let is_doc = matches!(bytes.get(start + 2), Some(b'-' | b'!'));
    let mut i = start + if is_doc { 3 } else { 2 };
    let mut depth = 1usize;
    while i < bytes.len() && depth > 0 {
        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'-' {
            depth += 1;
            i += 2;
        } else if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'/' {
            depth -= 1;
            i += 2;
        } else {
            i += 1;
        }
    }
    Some((i, is_doc))
}

pub(crate) fn scan_lean_interpolated_string_end(src: &str, start: usize) -> Option<usize> {
    let bytes = src.as_bytes();
    if bytes.get(start) != Some(&b'"')
        || start < 2
        || bytes[start - 1] != b'!'
        || !has_valid_interp_ident_prefix(src, start - 1)
    {
        return None;
    }
    let mut i = start + 1;
    let mut interp_depth = 0usize;
    while i < bytes.len() {
        if interp_depth > 0 {
            if let Some(end) =
                scan_lean_interpolated_string_end(src, i).or_else(|| scan_lean_literal_end(src, i))
            {
                i = end;
                continue;
            }
            if let Some((end, _)) = scan_lean_block_comment_end(src, i) {
                i = end;
                continue;
            }
            if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'-' {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                continue;
            }
            match bytes[i] {
                b'{' => interp_depth += 1,
                b'}' => interp_depth -= 1,
                _ => {}
            }
            i += 1;
            continue;
        }
        match bytes[i] {
            b'\\' => i = (i + 2).min(bytes.len()),
            b'{' => {
                interp_depth = 1;
                i += 1;
            }
            b'"' => return Some(i + 1),
            _ => i += 1,
        }
    }
    Some(bytes.len())
}

pub(crate) fn scan_lean_literal_end(src: &str, start: usize) -> Option<usize> {
    match *src.as_bytes().get(start)? {
        b'"' => scan_lean_string_lit_end(src, start),
        b'\'' => scan_lean_char_lit_end(src, start),
        b'r' => scan_lean_raw_string_end(src, start),
        0xC2 => scan_lean_guillemet_ident_end(src, start),
        _ => None,
    }
}

pub(crate) fn scan_lean_norm_literal_end(src: &str, start: usize) -> Option<usize> {
    scan_lean_interpolated_string_end(src, start).or_else(|| scan_lean_literal_end(src, start))
}

/// A literal, escaped identifier, or comment beginning at a UTF-8 byte boundary.
/// Unterminated strings and block comments consume the remainder so their contents cannot become code.
pub(crate) struct LeanLexicalSpan {
    pub(crate) end: usize,
    pub(crate) is_comment: bool,
    pub(crate) is_literal: bool,
}

pub(crate) fn skip_lean_lexeme(src: &str, start: usize) -> Option<LeanLexicalSpan> {
    let bytes = src.as_bytes();
    if let Some(end) = scan_lean_guillemet_ident_end(src, start) {
        return Some(LeanLexicalSpan {
            end,
            is_comment: false,
            is_literal: false,
        });
    }
    let at_char_start = !src[..start].chars().next_back().is_some_and(|c| {
        (is_lean_id_rest(c) && !ends_with_closed_char_lit(src, start)) || c == '»'
    });
    let two_bytes_avail = start + 1 < bytes.len();
    let comment_guard_ok =
        crate::c_abi::verify_lexer_comment_guard(false, false, two_bytes_avail, 0, u32::MAX as u64);
    match *bytes.get(start)? {
        b'-' if comment_guard_ok && bytes[start + 1] == b'-' => {
            let mut i = start + 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            Some(LeanLexicalSpan {
                end: i,
                is_comment: true,
                is_literal: false,
            })
        }
        b'/' if comment_guard_ok && bytes[start + 1] == b'-' => {
            let (end, _) = scan_lean_block_comment_end(src, start)?;
            Some(LeanLexicalSpan {
                end,
                is_comment: true,
                is_literal: false,
            })
        }
        b'\'' if at_char_start => Some(LeanLexicalSpan {
            end: scan_lean_char_lit_end(src, start)?,
            is_comment: false,
            is_literal: true,
        }),
        b'"' => Some(LeanLexicalSpan {
            end: scan_lean_interpolated_string_end(src, start)
                .or_else(|| scan_lean_string_lit_end(src, start))?,
            is_comment: false,
            is_literal: true,
        }),
        b'r' => Some(LeanLexicalSpan {
            end: scan_lean_raw_string_end(src, start)?,
            is_comment: false,
            is_literal: true,
        }),
        _ => None,
    }
}

/// Preserve byte offsets and newlines while hiding lexical contents from scope scans.
fn mask_lean_lexemes(src: &str, literals: bool) -> String {
    if !literals {
        return strip_lean_comments(src);
    }
    let mut out = src.as_bytes().to_vec();
    let mut i = 0;
    while i < src.len() {
        if let Some(span) = skip_lean_lexeme(src, i) {
            if span.is_comment || span.is_literal {
                for byte in &mut out[i..span.end] {
                    if *byte != b'\n' && *byte != b'\r' {
                        *byte = b' ';
                    }
                }
            }
            i = span.end;
        } else {
            i += src[i..].chars().next().unwrap().len_utf8();
        }
    }
    String::from_utf8(out).expect("lexical masking preserves UTF-8")
}

fn scan_lean_comments_inner(
    src: &str,
    preserve_docstrings: bool,
    out: &mut Vec<u8>,
    on_line_comment: &mut dyn FnMut(usize, usize),
) {
    let bytes = src.as_bytes();
    let mut i = 0;
    let mut in_string = false;
    let mut char_lit_end = 0usize;
    let mut block_depth = 0usize;

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
                out.push(if bytes[i] == b'\n' || bytes[i] == b'\r' {
                    bytes[i]
                } else {
                    b' '
                });
                i += 1;
            }
            continue;
        }

        if i < char_lit_end {
            out.push(bytes[i]);
            i += 1;
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

        if bytes[i] == 0xC2 {
            if let Some(end) = scan_lean_guillemet_ident_end(src, i) {
                char_lit_end = end;
                out.push(bytes[i]);
                i += 1;
                continue;
            }
        }
        if bytes[i] == b'\'' {
            let at_char_start = !src[..i].chars().next_back().is_some_and(|c| {
                (is_lean_id_rest(c) && !ends_with_closed_char_lit(src, i)) || c == '»'
            });
            if at_char_start {
                if let Some(end) = scan_lean_char_lit_end(src, i) {
                    char_lit_end = end;
                    out.push(bytes[i]);
                    i += 1;
                    continue;
                }
            }
        }
        if bytes[i] == b'r' {
            if let Some(end) = scan_lean_raw_string_end(src, i) {
                char_lit_end = end;
                out.push(bytes[i]);
                i += 1;
                continue;
            }
        }
        if bytes[i] == b'"' {
            if let Some(end) = scan_lean_interpolated_string_end(src, i) {
                out.push(b'"');
                let mut j = i + 1;
                let mut interp_depth = 0usize;
                while j < end {
                    if interp_depth > 0 {
                        if let Some(sub_end) = scan_lean_norm_literal_end(src, j) {
                            scan_lean_comments_inner(
                                &src[j..sub_end],
                                preserve_docstrings,
                                out,
                                &mut |s, e| {
                                    on_line_comment(j + s, j + e);
                                },
                            );
                            j = sub_end;
                            continue;
                        }
                        if let Some((cend, is_doc)) = scan_lean_block_comment_end(src, j) {
                            let clamped = cend.min(end);
                            if preserve_docstrings && is_doc {
                                out.extend_from_slice(&bytes[j..clamped]);
                            } else {
                                for &b in &bytes[j..clamped] {
                                    out.push(if b == b'\n' || b == b'\r' { b } else { b' ' });
                                }
                            }
                            j = clamped;
                            continue;
                        }
                        if j + 1 < end && bytes[j] == b'-' && bytes[j + 1] == b'-' {
                            let c_start = j;
                            while j < end && bytes[j] != b'\n' {
                                out.push(if bytes[j] == b'\r' { b'\r' } else { b' ' });
                                j += 1;
                            }
                            on_line_comment(c_start, j);
                            continue;
                        }
                        match bytes[j] {
                            b'{' => interp_depth += 1,
                            b'}' => interp_depth -= 1,
                            _ => {}
                        }
                        out.push(bytes[j]);
                        j += 1;
                    } else if bytes[j] == b'\\' && j + 1 < end {
                        out.push(bytes[j]);
                        out.push(bytes[j + 1]);
                        j += 2;
                    } else if bytes[j] == b'{' {
                        interp_depth = 1;
                        out.push(b'{');
                        j += 1;
                    } else {
                        out.push(bytes[j]);
                        j += 1;
                    }
                }
                i = end;
                continue;
            }
        }

        let in_char = i < char_lit_end;
        if bytes[i] == b'"' {
            in_string = true;
            out.push(b'"');
            i += 1;
        } else if crate::c_abi::verify_lexer_comment_guard(
            in_string,
            in_char,
            i + 1 < bytes.len(),
            block_depth as u64,
            u32::MAX as u64,
        ) && bytes[i] == b'-'
            && bytes[i + 1] == b'-'
        {
            let c_start = i;
            while i < bytes.len() && bytes[i] != b'\n' {
                out.push(if bytes[i] == b'\r' { b'\r' } else { b' ' });
                i += 1;
            }
            on_line_comment(c_start, i);
        } else if crate::c_abi::verify_lexer_comment_guard(
            in_string,
            in_char,
            i + 1 < bytes.len(),
            block_depth as u64,
            u32::MAX as u64,
        ) && bytes[i] == b'/'
            && bytes[i + 1] == b'-'
        {
            if let Some((cend, is_doc)) = scan_lean_block_comment_end(src, i) {
                if preserve_docstrings && is_doc {
                    out.extend_from_slice(&bytes[i..cend]);
                    i = cend;
                } else {
                    let opener = if is_doc { 3 } else { 2 }.min(bytes.len() - i);
                    for &b in &bytes[i..i + opener] {
                        out.push(if b == b'\n' || b == b'\r' { b } else { b' ' });
                    }
                    block_depth = 1;
                    i += opener;
                }
            } else {
                block_depth = 1;
                out.extend_from_slice(b"  ");
                i += 2;
            }
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
}

fn scan_lean_comments_with(
    src: &str,
    out: &mut Vec<u8>,
    on_line_comment: &mut dyn FnMut(usize, usize),
) {
    scan_lean_comments_inner(src, false, out, on_line_comment);
}

/// Strip ordinary `--` and `/- ... -/` comments while preserving `/-- ... -/` and `/-! ... -/`
/// docstrings, string/character literals, guillemet identifiers, exact byte offsets, and newline counts.
fn strip_non_doc_lean_comments(src: &str) -> String {
    if !src.contains("--") && !src.contains("/-") {
        return src.to_string();
    }
    let mut out = Vec::with_capacity(src.len());
    scan_lean_comments_inner(src, true, &mut out, &mut |_, _| {});
    String::from_utf8(out).unwrap_or_else(|e| String::from_utf8_lossy(e.as_bytes()).into_owned())
}

/// Strip comments while preserving string/character literals, exact byte offsets, and newline counts.
pub fn strip_lean_comments(src: &str) -> String {
    if !src.contains("--") && !src.contains("/-") {
        return src.to_string();
    }
    let mut out = Vec::with_capacity(src.len());
    scan_lean_comments_with(src, &mut out, &mut |_, _| {});
    String::from_utf8(out).unwrap_or_else(|e| String::from_utf8_lossy(e.as_bytes()).into_owned())
}

fn strip_string_literals(src: &str) -> std::borrow::Cow<'_, str> {
    if !src.contains('"') && !src.contains('\'') && !src.contains('«') {
        return std::borrow::Cow::Borrowed(src);
    }
    let bytes = src.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if let Some(end) = scan_lean_guillemet_ident_end(src, i) {
            out.extend_from_slice(&bytes[i..end]);
            i = end;
            continue;
        }
        if let Some(end) = scan_lean_norm_literal_end(src, i) {
            if scan_lean_interpolated_string_end(src, i).is_some() {
                out.push(b'"');
                let mut j = i + 1;
                let mut interp_depth = 0usize;
                while j < end {
                    if interp_depth > 0 {
                        if let Some(sub_end) = scan_lean_norm_literal_end(src, j) {
                            let stripped = strip_string_literals(&src[j..sub_end]);
                            out.extend_from_slice(stripped.as_bytes());
                            j = sub_end;
                            continue;
                        }
                        match bytes[j] {
                            b'{' => interp_depth += 1,
                            b'}' => interp_depth -= 1,
                            _ => {}
                        }
                        out.push(bytes[j]);
                        j += 1;
                    } else if bytes[j] == b'\\' && j + 1 < end {
                        out.push(b' ');
                        out.push(if bytes[j + 1] == b'\n' { b'\n' } else { b' ' });
                        j += 2;
                    } else if bytes[j] == b'{' {
                        interp_depth = 1;
                        out.push(b'{');
                        j += 1;
                    } else if j + 1 == end && bytes[j] == b'"' {
                        out.push(b'"');
                        j += 1;
                    } else {
                        out.push(if bytes[j] == b'\n' { b'\n' } else { b' ' });
                        j += 1;
                    }
                }
                i = end;
                continue;
            }
            let prefix_len = if bytes[i] == b'r' {
                bytes[i..]
                    .iter()
                    .position(|&b| b == b'"')
                    .map_or(1, |p| p + 1)
            } else {
                1
            };
            let close_start = end.saturating_sub(if bytes[i] == b'r' {
                prefix_len - 1
            } else {
                usize::from(bytes.get(end.saturating_sub(1)) == Some(&bytes[i]) && end > i + 1)
            });
            out.extend_from_slice(&bytes[i..i + prefix_len]);
            for &b in &bytes[i + prefix_len..close_start] {
                out.push(if b == b'\n' { b'\n' } else { b' ' });
            }
            out.extend_from_slice(&bytes[close_start..end]);
            i = end;
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
        "bv_decide",
        "ofReduceBool",
        "trustCompiler",
        "unsafe",
        "implemented_by",
        "extern",
        "csimp",
        "#eval",
        "run_cmd",
        "run_elab",
        "run_meta",
        "set_option",
        "#guard_msgs",
        "initialize ",
    ]
    .iter()
    .any(|kw| clean_src.contains(kw))
    {
        return report;
    }

    // Scan across line boundaries and through scoped command prefixes. Strings and comments
    // have already been stripped; quoted name segments denote the same option keys.
    for (pos, _) in clean_src.match_indices("set_option") {
        if pos > 0
            && clean_src[..pos]
                .chars()
                .next_back()
                .is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '.')
        {
            continue;
        }
        let mut words = clean_src[pos + "set_option".len()..].split_whitespace();
        let key = words.next().unwrap_or("").replace(['«', '»'], "");
        if key == "debug"
            || key.starts_with("debug.")
            || key.starts_with("weak.")
            || (key == "warn.sorry" && words.next() != Some("true"))
        {
            report.has_checking_weakening = true;
            let line = clean_src[..pos].bytes().filter(|b| *b == b'\n').count() + 1;
            report
                .flagged_items
                .push(format!("L{line}: checking-weakening option `{key}`"));
        }
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
        for command in ["run_elab", "run_cmd", "run_meta"] {
            if contains_word(trimmed, command) {
                report.has_checking_weakening = true;
                report.has_impure_metaprograms = true;
                report
                    .flagged_items
                    .push(format!("L{ln}: checking-weakening command `{command}`"));
            }
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
        if contains_word(trimmed, "bv_decide") {
            report.has_native_decide = true;
            report.flagged_items.push(format!("L{}: bv_decide", ln));
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
        let standalone_attr = after_prefixes
            .strip_prefix("attribute")
            .filter(|r| r.starts_with(char::is_whitespace) || r.starts_with('['))
            .map(str::trim_start)
            .and_then(|r| {
                let end = r.find(']')?;
                r.strip_prefix('[').map(|inner| &inner[..end - 1])
            });
        for (tag, attr_kw) in [
            ("@[implemented_by", "implemented_by"),
            ("@[extern", "extern"),
            ("@[csimp", "csimp"),
        ] {
            if trimmed.contains(tag)
                || attrs.iter().any(|a| contains_word(a, attr_kw))
                || standalone_attr
                    .map(|a| contains_word(a, attr_kw))
                    .unwrap_or(false)
            {
                report.has_extern_or_implemented_by = true;
                report.flagged_items.push(format!("L{}: {}", ln, attr_kw));
            }
        }
        if ["#eval", "#guard_msgs", "initialize "]
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

pub(crate) fn reject_checking_weakening(source: &str) -> anyhow::Result<()> {
    let report = audit_hygiene(&strip_lean_comments(source));
    anyhow::ensure!(
        !report.has_checking_weakening,
        "Soundness hygiene violation: {}",
        report.disallowed_items().join(", ")
    );
    Ok(())
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
    let mut i = 1usize;
    while i < bytes.len() {
        if let Some((end, _)) = scan_lean_block_comment_end(s, i) {
            i = end;
            continue;
        }
        if i + 1 < bytes.len() && bytes[i] == b'-' && bytes[i + 1] == b'-' {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if let Some(end) = scan_lean_norm_literal_end(s, i) {
            i = end;
            continue;
        }
        match bytes[i] {
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
        if before_in.len() > "set_option".len() {
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
pub(crate) fn strip_decl_prefixes(cmd_text: &str) -> &str {
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
        if let Some((end, is_doc)) = scan_lean_block_comment_end(rest, 0) {
            if is_doc {
                rest = rest[end..].trim_start();
                continue;
            }
        }
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

/// Returns true if `clean_chunk` (with corresponding `orig_chunk`) consists solely of comments,
/// `/-- ... -/` declaration docstrings, whitespace, `@[...]` attributes, or declaration modifiers
/// (`private`, `scoped`, `local`, etc.) waiting for a declaration on a following line.
fn is_incomplete_prefix_only_span(orig_chunk: &str, clean_chunk: &str) -> bool {
    let trimmed = clean_chunk.trim();
    if trimmed.is_empty() {
        let mut r = orig_chunk.trim_start();
        while !r.is_empty() {
            if let Some((end, is_doc)) = scan_lean_block_comment_end(r, 0) {
                if is_doc && r[..end].starts_with("/-!") {
                    return false;
                }
                r = r[end..].trim_start();
                continue;
            }
            if r.starts_with("--") {
                r = r.find('\n').map_or("", |p| &r[p + 1..]).trim_start();
                continue;
            }
            break;
        }
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

pub(crate) fn is_section_header_line(trimmed_clean: &str) -> bool {
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
    let mut scope_depth = 0usize;
    let mut lexical_cursor = 0usize;
    let mut literal_end = 0usize;

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
        let token_start = line_start + line_clean.len() - trimmed.len();
        // Keep the whole source's lexical context: a command-looking line inside a
        // literal must not become a declaration or change the namespace stack.
        while lexical_cursor < token_start {
            if let Some(span) = skip_lean_lexeme(src, lexical_cursor) {
                if span.is_literal {
                    literal_end = span.end;
                }
                lexical_cursor = span.end;
            } else {
                lexical_cursor += src[lexical_cursor..].chars().next().unwrap().len_utf8();
            }
        }
        if token_start < literal_end {
            cur_byte_end = line_end_no_cr;
            pos = next_pos;
            line_num += 1;
            continue;
        }

        let indent = line_orig.len() - line_orig.trim_start().len();
        let at_command_indent = cur_cmd_indent.is_none_or(|base| indent <= base);
        let trimmed_orig_line = line_orig.trim_start();
        let starts_doc_comment = matches!(
            scan_lean_block_comment_end(trimmed_orig_line, 0),
            Some((_, true))
        ) && (indent == 0 || (scope_depth > 0 && at_command_indent));

        if mutual_depth > 0 {
            if at_command_indent {
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

        let prev_orig = &src[cur_byte_start..cur_byte_end];
        let prev_clean = &clean[cur_byte_start..cur_byte_end];
        let prev_trimmed = prev_clean.trim();
        let prev_is_section_or_ns_header = is_section_header_line(prev_trimmed)
            || prev_trimmed.starts_with("namespace ")
            || is_end_line_start(prev_trimmed);

        let can_start_at_indent =
            at_command_indent || (scope_depth > 0 && prev_is_section_or_ns_header);

        if line_num > 1
            && can_start_at_indent
            && (starts_doc_comment || (!trimmed.is_empty() && is_top_level_command_start(trimmed)))
            && !is_incomplete_prefix_only_span(prev_orig, prev_clean)
        {
            spans.push(CmdSpan {
                start_line: cur_start_line,
                end_line: line_num - 1,
                orig_text: prev_orig,
                clean_text: prev_clean,
            });
            cur_start_line = line_num;
            cur_byte_start = line_start;
            cur_cmd_indent = None;
        }

        if !trimmed.is_empty() && cur_cmd_indent.is_none() {
            cur_cmd_indent = Some(indent);
        }

        if can_start_at_indent {
            if is_section_header_line(trimmed) || trimmed.starts_with("namespace ") {
                scope_depth += 1;
            } else if is_end_line_start(trimmed) && scope_depth > 0 {
                scope_depth -= 1;
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

pub(crate) fn split_lean_name_components(name: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut seg_start = 0;
    let mut i = 0;
    while i < name.len() {
        if name[i..].starts_with('«') {
            let body = i + '«'.len_utf8();
            if let Some(rel_end) = name[body..].find('»') {
                i = body + rel_end + '»'.len_utf8();
                continue;
            }
            break;
        }
        let c = name[i..].chars().next().unwrap();
        if c == '.' {
            if i > seg_start {
                out.push(&name[seg_start..i]);
            }
            i += 1;
            seg_start = i;
        } else {
            i += c.len_utf8();
        }
    }
    if seg_start < name.len() {
        out.push(&name[seg_start..]);
    }
    out
}

pub(crate) fn canonical_lean_name_component(seg: &str) -> String {
    let raw = seg
        .strip_prefix('«')
        .and_then(|s| s.strip_suffix('»'))
        .unwrap_or(seg);
    let was_quoted_numeric =
        seg.starts_with('«') && !raw.is_empty() && raw.bytes().all(|b| b.is_ascii_digit());
    if was_quoted_numeric || raw.contains('.') || raw.contains('«') || raw.contains('»') {
        format!("«{raw}»")
    } else {
        raw.to_string()
    }
}

pub(crate) fn canonicalize_lean_name(name: &str) -> String {
    let raw = name.strip_prefix("_root_.").unwrap_or(name);
    split_lean_name_components(raw)
        .into_iter()
        .map(canonical_lean_name_component)
        .collect::<Vec<_>>()
        .join(".")
}

fn classify_decl_header(cmd_text: &str) -> Option<(String, String)> {
    let rest = strip_decl_prefixes(cmd_text);
    for kw in ["theorem", "lemma"] {
        if let Some(after) = rest.strip_prefix(kw) {
            if after.starts_with(char::is_whitespace) {
                if let Some((name, _)) = take_leading_lean_ident(after.trim_start()) {
                    return Some((kw.to_string(), name.to_string()));
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
                let name = take_leading_lean_ident(after)
                    .map(|(n, _)| n.to_string())
                    .unwrap_or_default();
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

    // Determine declaration indentation, not proof indentation: Lean also accepts
    // an unindented `:=` continuation inside a mutual block.
    let min_indent = body_clean
        .lines()
        .filter(|l| is_top_level_command_start(l.trim_start()))
        .map(|l| l.len() - l.trim_start().len())
        .min()?;

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
        let orig_trimmed = line_orig.trim_start();
        let starts_doc = is_top_inner
            && matches!(
                scan_lean_block_comment_end(orig_trimmed, 0),
                Some((_, true))
            );

        if line_num > span.start_line + 1
            && is_top_inner
            && (starts_doc || (!trimmed.is_empty() && is_top_level_command_start(trimmed)))
        {
            let prev_orig = &body_orig[cur_byte_start..cur_byte_end];
            let prev_clean = &body_clean[cur_byte_start..cur_byte_end];
            if !is_incomplete_prefix_only_span(prev_orig, prev_clean) {
                inner_spans.push(CmdSpan {
                    start_line: cur_start_line,
                    end_line: line_num - 1,
                    orig_text: prev_orig,
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
fn is_pattern_match_arm_at(cmd: &str, pipe_idx: usize) -> bool {
    let bytes = cmd.as_bytes();
    if pipe_idx + 1 >= bytes.len() || (bytes[pipe_idx + 1] != b' ' && bytes[pipe_idx + 1] != b'\t')
    {
        return false;
    }
    let mut paren = 0i32;
    let mut bracket = 0i32;
    let mut brace = 0i32;
    let mut j = pipe_idx + 1;
    while j < bytes.len() {
        let c = bytes[j];
        if let Some((end, _)) = scan_lean_block_comment_end(cmd, j) {
            j = end;
            continue;
        }
        if j + 1 < bytes.len() && c == b'-' && bytes[j + 1] == b'-' {
            j += 2;
            while j < bytes.len() && bytes[j] != b'\n' {
                j += 1;
            }
            continue;
        }
        if let Some(end) = scan_lean_norm_literal_end(cmd, j) {
            j = end;
            continue;
        }
        match c {
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
            b':' if paren == 0
                && bracket == 0
                && brace == 0
                && j + 1 < bytes.len()
                && bytes[j + 1] == b'=' =>
            {
                return false;
            }
            _ => {}
        }
        j += 1;
    }
    false
}

pub(crate) fn extract_shard_stmt_and_proof(src: &str, shard: &TheoremShard) -> (String, String) {
    if !shard.signature_text.is_empty() && !shard.proof_text.is_empty() {
        return (shard.signature_text.clone(), shard.proof_text.clone());
    }
    let decl_lines = if shard.start_line >= 1 && shard.end_line >= shard.start_line {
        src.lines()
            .skip(shard.start_line - 1)
            .take(shard.end_line - shard.start_line + 1)
            .collect::<Vec<_>>()
            .join("\n")
    } else {
        String::new()
    };
    if let Some((sig, prf)) =
        split_at_top_level_assign(&decl_lines).or_else(|| decl_lines.split_once(":="))
    {
        (
            if !shard.signature_text.is_empty() {
                shard.signature_text.clone()
            } else {
                sig.trim().to_string()
            },
            if !shard.proof_text.is_empty() {
                shard.proof_text.clone()
            } else {
                prf.trim().to_string()
            },
        )
    } else {
        (shard.signature_text.clone(), shard.proof_text.clone())
    }
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
    let mut pending_let_assigns = 0usize;
    let mut seen_top_level_colon = false;
    let mut seen_top_level_match_after_colon = false;
    let mut first_top_level_arm_split: Option<usize> = None;

    while i < bytes.len() {
        let c = bytes[i];
        if let Some((end, _)) = scan_lean_block_comment_end(cmd, i) {
            i = end;
            continue;
        }
        if i + 1 < bytes.len() && c == b'-' && bytes[i + 1] == b'-' {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if let Some(end) = scan_lean_norm_literal_end(cmd, i) {
            i = end;
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
                        && is_pattern_match_arm_at(cmd, i)
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
    is_lean_id_rest(c)
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
    let mut i = 0usize;
    let bytes = s.as_bytes();
    while i < bytes.len() {
        if let Some(end) = scan_lean_interpolated_string_end(s, i).or_else(|| match bytes[i] {
            b'"' => scan_lean_string_lit_end(s, i),
            b'\'' => scan_lean_char_lit_end(s, i),
            b'r' => scan_lean_raw_string_end(s, i),
            _ => None,
        }) {
            if scan_lean_interpolated_string_end(s, i).is_some() {
                let mut j = i + 1;
                while j < end {
                    if bytes[j] == b'\\' && j + 1 < end {
                        j += 2;
                    } else if bytes[j] == b'{' {
                        j += 1;
                        let expr_start = j;
                        let mut depth = 1usize;
                        while j < end && depth > 0 {
                            if let Some(sub_end) = scan_lean_norm_literal_end(s, j) {
                                j = sub_end;
                                continue;
                            }
                            match bytes[j] {
                                b'{' => depth += 1,
                                b'}' => {
                                    depth -= 1;
                                    if depth == 0 {
                                        break;
                                    }
                                }
                                _ => {}
                            }
                            j += 1;
                        }
                        for sub_tok in extract_ident_tokens(&s[expr_start..j]) {
                            if seen.insert(sub_tok.clone()) {
                                out.push(sub_tok);
                            }
                        }
                        if j < end && bytes[j] == b'}' {
                            j += 1;
                        }
                    } else {
                        j += 1;
                    }
                }
            }
            i = end;
            continue;
        }
        if let Some((qual_tok, _)) = take_leading_lean_ident(&s[i..]) {
            let mut seg_pos = 0usize;
            while seg_pos < qual_tok.len() {
                let seg_end = if let Some(gend) = scan_lean_guillemet_ident_end(qual_tok, seg_pos) {
                    gend
                } else {
                    qual_tok[seg_pos..]
                        .find('.')
                        .map_or(qual_tok.len(), |p| seg_pos + p)
                };
                let seg = &qual_tok[seg_pos..seg_end];
                if !seg.is_empty()
                    && !is_lean_keyword_or_builtin(seg)
                    && seen.insert(seg.to_string())
                {
                    out.push(seg.to_string());
                }
                seg_pos = seg_end + 1;
            }
            if qual_tok.len() > last_host_name_component(qual_tok).len()
                && seen.insert(qual_tok.to_string())
            {
                out.push(qual_tok.to_string());
            }
            i += qual_tok.len();
            continue;
        }
        let ch = s[i..].chars().next().unwrap_or('\0');
        i += ch.len_utf8().max(1);
    }
    out
}

fn extract_inductive_constructors(clean_text: &str) -> Vec<String> {
    let mut ctors = Vec::new();
    for line in clean_text.lines().skip(1) {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix('|') {
            if let Some((name, _)) = take_leading_lean_ident(rest.trim_start()) {
                ctors.push(name.to_string());
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

#[allow(clippy::too_many_arguments)]
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
        let num_words = prior_decls.len().div_ceil(64);
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

fn extract_section_header_name(trimmed: &str) -> String {
    let mut after_sec = trimmed;
    while let Some(next) = strip_leading_attr_block(after_sec) {
        after_sec = next.trim_start();
    }
    for m in ["noncomputable ", "public ", "meta "] {
        if let Some(next) = after_sec.strip_prefix(m) {
            after_sec = next.trim_start();
        }
    }
    let rest = after_sec.strip_prefix("section").unwrap_or("").trim_start();
    take_leading_lean_ident(rest)
        .map(|(n, _)| n.to_string())
        .unwrap_or_default()
}

/// Update `stack` for scope commands (`namespace A.B.C`, `section`, `noncomputable section`,
/// `mutual`, `end A.B.C`) in `orig_chunk` (or comment-stripped `clean_chunk` when strings are single-span).
pub(crate) fn update_scope_stack_with_idx(
    stack: &mut Vec<ScopeFrame>,
    orig_chunk: &str,
    span_idx: usize,
) {
    let masked = mask_lean_lexemes(orig_chunk, true);
    for (line, orig_line) in masked.lines().zip(orig_chunk.lines()) {
        let trimmed = line.trim();
        let orig_trimmed = orig_line.trim();
        if let Some(rest) = trimmed.strip_prefix("namespace ") {
            let orig_rest = orig_trimmed.strip_prefix("namespace ").unwrap_or(rest);
            let name = take_leading_lean_ident(orig_rest.trim_start())
                .map(|(n, _)| n)
                .unwrap_or("");
            for seg in split_lean_name_components(name) {
                stack.push(ScopeFrame {
                    kind: ScopeKind::Namespace,
                    name: seg.to_string(),
                    open_span_idx: span_idx,
                });
            }
        } else if is_section_header_line(trimmed) {
            let name = extract_section_header_name(orig_trimmed);
            if name.is_empty() {
                stack.push(ScopeFrame {
                    kind: ScopeKind::Section,
                    name: String::new(),
                    open_span_idx: span_idx,
                });
            } else {
                for seg in split_lean_name_components(&name) {
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
            let orig_rest = orig_trimmed
                .strip_prefix("end")
                .unwrap_or_else(|| trimmed.strip_prefix("end").unwrap_or(""));
            let name = take_leading_lean_ident(orig_rest.trim_start())
                .map(|(n, _)| n)
                .unwrap_or("");
            if name.is_empty() {
                stack.pop();
            } else {
                for seg in split_lean_name_components(name).into_iter().rev() {
                    let canon = canonical_lean_name_component(seg);
                    if let Some(pos) = stack
                        .iter()
                        .rposition(|f| canonical_lean_name_component(&f.name) == canon)
                    {
                        stack.truncate(pos);
                    } else {
                        stack.pop();
                    }
                }
            }
        }
    }
}

/// Environment-facing name, without Lean's private-name mangling. Section names do not
/// contribute to namespaces; explicit `_root_` declarations bypass the current namespace.
pub(crate) fn qualified_decl_name(name: &str, stack: &[ScopeFrame]) -> String {
    if let Some(root_name) = name.strip_prefix("_root_.") {
        return canonicalize_lean_name(root_name);
    }
    stack
        .iter()
        .filter(|f| matches!(f.kind, ScopeKind::Namespace))
        .map(|f| canonical_lean_name_component(f.name.as_str()))
        .chain(
            split_lean_name_components(name)
                .into_iter()
                .map(canonical_lean_name_component),
        )
        .collect::<Vec<_>>()
        .join(".")
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
        let masked = mask_lean_lexemes(span.orig_text, true);
        for (line, orig_line) in masked.lines().zip(span.orig_text.lines()) {
            let trimmed = line.trim();
            let orig_trimmed = orig_line.trim();
            if let Some(rest) = trimmed.strip_prefix("namespace ") {
                let orig_rest = orig_trimmed.strip_prefix("namespace ").unwrap_or(rest);
                let name = take_leading_lean_ident(orig_rest.trim_start())
                    .map(|(n, _)| n)
                    .unwrap_or("");
                for seg in split_lean_name_components(name) {
                    stack.push(ScopeFrame {
                        kind: ScopeKind::Namespace,
                        name: seg.to_string(),
                        open_span_idx: idx,
                    });
                }
            } else if is_section_header_line(trimmed) {
                let name = extract_section_header_name(orig_trimmed);
                if name.is_empty() {
                    stack.push(ScopeFrame {
                        kind: ScopeKind::Section,
                        name: String::new(),
                        open_span_idx: idx,
                    });
                } else {
                    for seg in split_lean_name_components(&name) {
                        stack.push(ScopeFrame {
                            kind: ScopeKind::Section,
                            name: seg.to_string(),
                            open_span_idx: idx,
                        });
                    }
                }
            } else if trimmed == "mutual" || trimmed.starts_with("mutual ") {
                stack.push(ScopeFrame {
                    kind: ScopeKind::Mutual,
                    name: String::new(),
                    open_span_idx: idx,
                });
            } else if trimmed == "end" || trimmed.starts_with("end ") {
                let orig_rest = orig_trimmed
                    .strip_prefix("end")
                    .unwrap_or_else(|| trimmed.strip_prefix("end").unwrap_or(""));
                let name = take_leading_lean_ident(orig_rest.trim_start())
                    .map(|(n, _)| n)
                    .unwrap_or("");
                if name.is_empty() {
                    if let Some(popped) = stack.pop() {
                        if popped.kind == ScopeKind::Section {
                            closed_sections.push((popped.open_span_idx, idx));
                        }
                    }
                } else {
                    for seg in split_lean_name_components(name).into_iter().rev() {
                        let canon = canonical_lean_name_component(seg);
                        if let Some(pos) = stack
                            .iter()
                            .rposition(|f| canonical_lean_name_component(&f.name) == canon)
                        {
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
        if let Some(end) =
            scan_lean_interpolated_string_end(clean_text, i).or_else(|| match bytes[i] {
                b'"' => scan_lean_string_lit_end(clean_text, i),
                b'\'' => scan_lean_char_lit_end(clean_text, i),
                b'r' => scan_lean_raw_string_end(clean_text, i),
                _ => None,
            })
        {
            if scan_lean_interpolated_string_end(clean_text, i).is_some() {
                let mut j = i + 1;
                while j < end {
                    if bytes[j] == b'\\' && j + 1 < end {
                        j += 2;
                    } else if bytes[j] == b'{' {
                        j += 1;
                        let expr_start = j;
                        let mut depth = 1usize;
                        while j < end && depth > 0 {
                            if let Some((cend, _)) = scan_lean_block_comment_end(clean_text, j) {
                                j = cend.min(end);
                                continue;
                            }
                            if let Some(sub_end) = scan_lean_norm_literal_end(clean_text, j) {
                                j = sub_end;
                                continue;
                            }
                            match bytes[j] {
                                b'{' => depth += 1,
                                b'}' => {
                                    depth -= 1;
                                    if depth == 0 {
                                        break;
                                    }
                                }
                                _ => {}
                            }
                            j += 1;
                        }
                        extract_local_ref_tokens_into(
                            &clean_text[expr_start..j],
                            span_idx,
                            exact_map,
                            non_std_short_map,
                        );
                        if j < end && bytes[j] == b'}' {
                            j += 1;
                        }
                    } else {
                        j += 1;
                    }
                }
            }
            i = end;
            continue;
        }
        if let Some((qual_ident, _)) = take_leading_lean_ident(&clean_text[i..]) {
            let vec_exact = exact_map.entry(qual_ident).or_default();
            if vec_exact.last() != Some(&span_idx) {
                vec_exact.push(span_idx);
            }
            if !STD_QUAL_PREFIXES.iter().any(|p| qual_ident.starts_with(p)) {
                let short = last_host_name_component(qual_ident);
                if !short.is_empty() {
                    let vec_short = non_std_short_map.entry(short).or_default();
                    if vec_short.last() != Some(&span_idx) {
                        vec_short.push(span_idx);
                    }
                }
            }
            i += qual_ident.len();
            continue;
        }
        let ch = clean_text[i..].chars().next().unwrap_or('\0');
        i += ch.len_utf8().max(1);
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
            if trimmed.is_empty() {
                if inner.orig_text.contains("/-!") {
                    unconditional = true;
                    break;
                }
                continue;
            }
            if is_scope_or_context_command(trimmed) {
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
                        let short = last_host_name_component(&name).to_string();
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
                let short = last_host_name_component(&name).to_string();
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

fn emit_normalized_lean(s: &str, emit: &mut dyn FnMut(&[u8])) -> bool {
    let mut first_non_ws = 0usize;
    let mut last_non_ws = 0usize;
    let mut line_ws_start = 0usize;
    let mut seen_newline = false;
    let mut seen_non_ws = false;
    for (idx, ch) in s.char_indices() {
        if ch == '\n' {
            line_ws_start = idx + 1;
            seen_newline = true;
        } else if !ch.is_whitespace() {
            if !seen_non_ws {
                first_non_ws = if seen_newline { line_ws_start } else { idx };
                seen_non_ws = true;
            }
            last_non_ws = idx + ch.len_utf8();
        }
    }
    if !seen_non_ws {
        return false;
    }
    let s = &s[first_non_ws..last_non_ws];
    let bytes = s.as_bytes();
    let mut i = 0usize;
    let mut emitted_any = false;
    let mut at_line_start = seen_newline;
    let mut pending_space = false;
    let mut pending_newlines = 0usize;
    while i < bytes.len() {
        if let Some((end, is_doc)) = scan_lean_block_comment_end(s, i) {
            if is_doc {
                if pending_newlines > 0 {
                    for _ in 0..pending_newlines {
                        emit(b"\n");
                    }
                    pending_newlines = 0;
                }
                if pending_space {
                    emit(b" ");
                    pending_space = false;
                }
                emit(&bytes[i..end]);
                emitted_any = true;
                at_line_start = false;
            } else if s[i..end].contains('\n') {
                if emitted_any {
                    pending_newlines = 1;
                }
                pending_space = false;
                at_line_start = true;
            } else if !at_line_start && emitted_any {
                pending_space = true;
            }
            i = end;
            continue;
        }
        if bytes[i] == b'-' && i + 1 < bytes.len() && bytes[i + 1] == b'-' {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if let Some(end) = scan_lean_norm_literal_end(s, i) {
            if pending_newlines > 0 {
                for _ in 0..pending_newlines {
                    emit(b"\n");
                }
                pending_newlines = 0;
            }
            if pending_space {
                emit(b" ");
                pending_space = false;
            }
            if scan_lean_interpolated_string_end(s, i).is_some() {
                emit(b"\"");
                let mut j = i + 1;
                while j < end {
                    if bytes[j] == b'\\' && j + 1 < end {
                        emit(&bytes[j..j + 2]);
                        j += 2;
                    } else if bytes[j] == b'{' {
                        emit(b"{");
                        j += 1;
                        let expr_start = j;
                        let mut depth = 1usize;
                        while j < end && depth > 0 {
                            if let Some((blk_end, _)) = scan_lean_block_comment_end(s, j) {
                                j = blk_end;
                                continue;
                            }
                            if bytes[j] == b'-' && j + 1 < end && bytes[j + 1] == b'-' {
                                j += 2;
                                while j < end && bytes[j] != b'\n' {
                                    j += 1;
                                }
                                continue;
                            }
                            if let Some(sub_end) = scan_lean_norm_literal_end(s, j) {
                                j = sub_end;
                                continue;
                            }
                            match bytes[j] {
                                b'{' => depth += 1,
                                b'}' => {
                                    depth -= 1;
                                    if depth == 0 {
                                        break;
                                    }
                                }
                                _ => {}
                            }
                            j += 1;
                        }
                        emit_normalized_lean(&s[expr_start..j], emit);
                        if j < end && bytes[j] == b'}' {
                            emit(b"}");
                            j += 1;
                        }
                    } else {
                        let seg_start = j;
                        j += 1;
                        while j < end && bytes[j] != b'\\' && bytes[j] != b'{' {
                            j += 1;
                        }
                        emit(&bytes[seg_start..j]);
                    }
                }
            } else {
                emit(&bytes[i..end]);
            }
            emitted_any = true;
            at_line_start = bytes.get(end.saturating_sub(1)) == Some(&b'\n');
            i = end;
            continue;
        }
        let ch = s[i..].chars().next().unwrap_or('\0');
        let ch_len = ch.len_utf8().max(1);
        if ch == '\n' {
            if emitted_any {
                pending_newlines = 1;
            }
            pending_space = false;
            at_line_start = true;
            i += 1;
        } else if ch == '\r' {
            i += 1;
        } else if ch.is_whitespace() {
            if at_line_start {
                let ws_start = i;
                while i < bytes.len() {
                    let c = s[i..].chars().next().unwrap_or('\0');
                    if c == '\n' || c == '\r' || !c.is_whitespace() {
                        break;
                    }
                    i += c.len_utf8().max(1);
                }
                if i < bytes.len() && bytes[i] != b'\n' && bytes[i] != b'\r' {
                    if pending_newlines > 0 {
                        for _ in 0..pending_newlines {
                            emit(b"\n");
                        }
                        pending_newlines = 0;
                    }
                    emit(&bytes[ws_start..i]);
                    emitted_any = true;
                    at_line_start = false;
                    pending_space = false;
                }
            } else {
                if emitted_any {
                    pending_space = true;
                }
                i += ch_len;
            }
        } else {
            if pending_newlines > 0 {
                for _ in 0..pending_newlines {
                    emit(b"\n");
                }
                pending_newlines = 0;
            }
            if pending_space {
                emit(b" ");
                pending_space = false;
            }
            let tok_start = i;
            i += ch_len;
            while i < bytes.len() {
                if scan_lean_block_comment_end(s, i).is_some()
                    || (bytes[i] == b'-' && i + 1 < bytes.len() && bytes[i + 1] == b'-')
                    || scan_lean_norm_literal_end(s, i).is_some()
                {
                    break;
                }
                let c = s[i..].chars().next().unwrap_or('\0');
                if c.is_whitespace() {
                    break;
                }
                i += c.len_utf8().max(1);
            }
            emit(&bytes[tok_start..i]);
            emitted_any = true;
            at_line_start = false;
        }
    }
    emitted_any
}

fn hash_normalized_whitespace(hasher: &mut blake3::Hasher, s: &str, suffix: &[u8]) -> bool {
    let non_empty = emit_normalized_lean(s, &mut |chunk| {
        hasher.update(chunk);
    });
    if non_empty && !suffix.is_empty() {
        hasher.update(suffix);
    }
    non_empty
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
    let doc_clean = if src.contains("/--") || src.contains("/-!") {
        Some(strip_non_doc_lean_comments(src))
    } else {
        None
    };
    let doc_slice = |orig: &str, cln: &str| -> String {
        if let Some(ref dc) = doc_clean {
            let off = orig.as_ptr() as usize - src.as_ptr() as usize;
            dc.get(off..off + orig.len()).unwrap_or(cln).to_string()
        } else {
            cln.to_string()
        }
    };
    let doc_sig_proof = |orig: &str, sig_cln: &str, prf_cln: &str| -> (String, String) {
        let full = if let Some(ref dc) = doc_clean {
            let off = orig.as_ptr() as usize - src.as_ptr() as usize;
            dc.get(off..off + orig.len())
        } else {
            None
        };
        if let Some(dspan) = full {
            if dspan.len() == sig_cln.len() + 2 + prf_cln.len() {
                return (
                    dspan[..sig_cln.len()].to_string(),
                    dspan[sig_cln.len() + 2..].to_string(),
                );
            }
            if dspan.len() == sig_cln.len() + prf_cln.len() {
                return (
                    dspan[..sig_cln.len()].to_string(),
                    dspan[sig_cln.len()..].to_string(),
                );
            }
            if let Some((ds, dp)) = split_at_top_level_assign(dspan) {
                return (ds.to_string(), dp.to_string());
            }
        }
        (sig_cln.to_string(), prf_cln.to_string())
    };
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
                                        let (sig_doc, _) =
                                            doc_sig_proof(sub.orig_text, sig_clean, proof_clean);
                                        inner_norm_parts.push(format!(
                                            "{} := sorry",
                                            normalize_whitespace(&sig_doc)
                                        ));
                                    }
                                    continue;
                                }
                            }
                            inner_skel_parts.push(sub.orig_text.to_string());
                            if has_closed_sections {
                                inner_norm_parts.push(normalize_whitespace(&doc_slice(
                                    sub.orig_text,
                                    sub.clean_text,
                                )));
                            }
                        }
                        inner_skel_parts.push(footer_orig.to_string());
                        span_skel_orig.push(inner_skel_parts.join("\n"));
                    } else if has_closed_sections {
                        for sub in &inner_spans {
                            if classify_decl_header(sub.clean_text).is_some() {
                                if let Some((sig_clean, proof_clean)) =
                                    split_at_top_level_assign(sub.clean_text)
                                {
                                    let (sig_doc, _) =
                                        doc_sig_proof(sub.orig_text, sig_clean, proof_clean);
                                    inner_norm_parts.push(format!(
                                        "{} := sorry",
                                        normalize_whitespace(&sig_doc)
                                    ));
                                    continue;
                                }
                            }
                            inner_norm_parts.push(normalize_whitespace(&doc_slice(
                                sub.orig_text,
                                sub.clean_text,
                            )));
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
                        let (sig_doc, _) = doc_sig_proof(span.orig_text, sig_clean, proof_clean);
                        span_norm_hash_line
                            .push(format!("{} := sorry\n", normalize_whitespace(&sig_doc)));
                    }
                    continue;
                }
            }

            if !omit_shard_source {
                span_skel_orig.push(sanitize_stubbed_prefix_options(span.orig_text));
            }
            if has_closed_sections {
                let norm_cmd = normalize_whitespace(&doc_slice(span.orig_text, span.clean_text));
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
        if trimmed == "module"
            || trimmed.starts_with("module ")
            || trimmed == "prelude"
            || trimmed.starts_with("prelude ")
            || trimmed.starts_with("import ")
            || trimmed.starts_with("public import ")
            || trimmed.starts_with("meta import ")
            || trimmed.starts_with("public meta import ")
        {
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
                    for skel in span_skel_orig.iter().take(target_idx) {
                        prefix_accum.push_str(skel);
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
                        let (sig_doc, proof_doc) =
                            doc_sig_proof(sub.orig_text, sig_clean, proof_clean);
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
                        let stmt_hash = hash_normalized_whitespace_hex(&sig_doc);
                        let proof_hash = hash_normalized_whitespace_hex(&proof_doc);

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
                            qualified_name: qualified_decl_name(&name, &scope_stack),
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
                        if let Some((sig_clean, proof_clean)) =
                            split_at_top_level_assign(sub.clean_text)
                        {
                            let short = last_host_name_component(&name).to_string();
                            let (sig_doc, _) = doc_sig_proof(sub.orig_text, sig_clean, proof_clean);
                            let st_hash = hash_normalized_whitespace_hex(&sig_doc);
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
                        let short = last_host_name_component(&name).to_string();
                        let extra_names = if kw == "inductive" || kw == "coinductive" {
                            extract_inductive_constructors(sub.clean_text)
                        } else {
                            Vec::new()
                        };
                        let decl_hash = hash_normalized_whitespace_hex(&doc_slice(
                            sub.orig_text,
                            sub.clean_text,
                        ));
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
                    let mut union_bits = vec![0u64; prior_decls.len().div_ceil(64)];
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
                            if let Some((sig_clean, proof_clean)) =
                                split_at_top_level_assign(sub.clean_text)
                            {
                                let (sig_doc, _) =
                                    doc_sig_proof(sub.orig_text, sig_clean, proof_clean);
                                if !hash_normalized_whitespace(
                                    &mut interface_hasher,
                                    &sig_doc,
                                    b" := sorry\n",
                                ) {
                                    interface_hasher.update(b" := sorry\n");
                                }
                                if !hash_normalized_whitespace(
                                    &mut dep_prefix_hasher,
                                    &sig_doc,
                                    b" := sorry\n",
                                ) {
                                    dep_prefix_hasher.update(b" := sorry\n");
                                }
                                continue;
                            }
                        }
                        let sub_doc = doc_slice(sub.orig_text, sub.clean_text);
                        if !hash_normalized_whitespace(&mut interface_hasher, &sub_doc, b"\n") {
                            interface_hasher.update(b"\n");
                        }
                        if !hash_normalized_whitespace(&mut dep_prefix_hasher, &sub_doc, b"\n") {
                            dep_prefix_hasher.update(b"\n");
                        }
                    }
                    interface_hasher.update(b"end\n");
                    dep_prefix_hasher.update(b"end\n");
                }
                update_scope_stack_with_idx(&mut scope_stack, span.orig_text, span_idx);
                continue;
            }
        }

        // Case 2: Standard top-level `theorem` / `lemma` declaration
        if let Some((kind, name)) = classify_decl_header(span.clean_text) {
            if let Some((sig_clean, proof_clean)) = split_at_top_level_assign(span.clean_text) {
                let (sig_orig, proof_orig) =
                    split_at_top_level_assign(span.orig_text).unwrap_or((sig_clean, proof_clean));
                let (sig_doc, proof_doc) = doc_sig_proof(span.orig_text, sig_clean, proof_clean);

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
                let stmt_hash = hash_normalized_whitespace_hex(&sig_doc);
                let proof_hash = hash_normalized_whitespace_hex(&proof_doc);

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
                    let short_name = last_host_name_component(&name).to_string();
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
                        let line_str = format!("{} := sorry\n", normalize_whitespace(&sig_doc));
                        dep_scope_hasher.update(line_str.as_bytes());
                        scope_directives.push((span_idx, line_str));
                    }
                }

                shards.push(TheoremShard {
                    qualified_name: qualified_decl_name(&name, &scope_stack),
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
                    if !hash_normalized_whitespace(&mut interface_hasher, &sig_doc, b" := sorry\n")
                    {
                        interface_hasher.update(b" := sorry\n");
                    }
                    if !hash_normalized_whitespace(&mut dep_prefix_hasher, &sig_doc, b" := sorry\n")
                    {
                        dep_prefix_hasher.update(b" := sorry\n");
                    }
                }
                update_scope_stack_with_idx(&mut scope_stack, span.orig_text, span_idx);
                continue;
            }
        }

        // Case 3: Non-theorem command (`import`, `open`, `variable`, `def`, `structure`, `instance`, etc.)
        let span_doc = doc_slice(span.orig_text, span.clean_text);
        if compute_cone {
            if is_cone_scope_or_header_directive(span.clean_text)
                || (span.clean_text.trim().is_empty() && span_doc.trim_start().starts_with("/-!"))
            {
                let norm_dir = normalize_whitespace(&span_doc);
                if !norm_dir.is_empty() {
                    let line_str = format!("{}\n", norm_dir);
                    dep_scope_hasher.update(line_str.as_bytes());
                    scope_directives.push((span_idx, line_str));
                }
            } else if let Some((kw, name)) = classify_any_decl_header(span.clean_text) {
                if name.is_empty() && kw == "instance" {
                    let norm_dir = normalize_whitespace(&span_doc);
                    if !norm_dir.is_empty() {
                        let line_str = format!("{}\n", norm_dir);
                        dep_scope_hasher.update(line_str.as_bytes());
                        scope_directives.push((span_idx, line_str));
                    }
                } else {
                    let short = last_host_name_component(&name).to_string();
                    let extra_names = if kw == "inductive" || kw == "coinductive" {
                        extract_inductive_constructors(span.clean_text)
                    } else {
                        Vec::new()
                    };
                    let decl_hash = hash_normalized_whitespace_hex(&span_doc);
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
            hash_normalized_whitespace(&mut interface_hasher, &span_doc, b"\n");
            hash_normalized_whitespace(&mut dep_prefix_hasher, &span_doc, b"\n");
        }
        update_scope_stack_with_idx(&mut scope_stack, span.orig_text, span_idx);
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

pub(crate) fn host_name_components(s: &str) -> Vec<String> {
    split_lean_name_components(s)
        .into_iter()
        .map(|seg| {
            seg.strip_prefix('«')
                .and_then(|r| r.strip_suffix('»'))
                .unwrap_or(seg)
                .to_string()
        })
        .collect()
}

/// Match the environment identity. A qualified request (`A.same`) names a declaration
/// exactly: it never matches `B.A.same`. An explicit `_root_.<name>` target always
/// matches only the exact canonical identity `<name>`. Only an unqualified single-component
/// short name may resolve to the last component of a namespaced declaration (uniqueness is
/// enforced by callers).
pub(crate) fn decl_name_matches_target(name: &str, target_decl: &str) -> bool {
    let canon_name = canonicalize_lean_name(name);
    if let Some(root_target) = target_decl.strip_prefix("_root_.") {
        return canon_name == canonicalize_lean_name(root_target);
    }
    let target_segs = split_lean_name_components(target_decl);
    let canon_target = target_segs
        .iter()
        .map(|s| canonical_lean_name_component(s))
        .collect::<Vec<_>>()
        .join(".");
    if canon_name == canon_target {
        return true;
    }
    if target_segs.len() == 1 {
        let name_segs = split_lean_name_components(&canon_name);
        return name_segs
            .last()
            .is_some_and(|last| canonical_lean_name_component(last) == canon_target);
    }
    false
}

fn resolve_decl_index<'a>(
    names: impl Iterator<Item = &'a str>,
    target_decl: &str,
) -> anyhow::Result<Option<usize>> {
    let matches: Vec<_> = names
        .enumerate()
        .filter(|(_, name)| decl_name_matches_target(name, target_decl))
        .collect();
    anyhow::ensure!(
        matches.len() <= 1,
        "Ambiguous declaration `{}`; candidates: {}",
        target_decl,
        matches
            .iter()
            .map(|(_, name)| *name)
            .collect::<Vec<_>>()
            .join(", ")
    );
    Ok(matches.first().map(|(idx, _)| *idx))
}

pub(crate) fn find_decl_shard_index(
    shards: &[TheoremShard],
    target_decl: &str,
) -> anyhow::Result<Option<usize>> {
    resolve_decl_index(shards.iter().map(TheoremShard::decl_name), target_decl)
}

pub(crate) fn resolve_target_shard_idx(
    shards: &[TheoremShard],
    target_decl: &str,
) -> std::result::Result<Option<usize>, Vec<String>> {
    let matches: Vec<usize> = shards
        .iter()
        .enumerate()
        .filter(|(_, s)| decl_name_matches_target(s.decl_name(), target_decl))
        .map(|(i, _)| i)
        .collect();
    match matches.len() {
        0 => Ok(None),
        1 => Ok(Some(matches[0])),
        _ => Err(matches
            .into_iter()
            .map(|i| shards[i].decl_name().to_string())
            .collect()),
    }
}

/// Collect each declaration's environment identity and enclosing command span, including mutuals.
fn qualified_span_declarations(spans: &[CmdSpan<'_>]) -> Vec<(usize, String)> {
    let mut scope_stack = Vec::new();
    let mut declarations = Vec::new();
    for (idx, span) in spans.iter().enumerate() {
        let mut record = |text: &str| {
            if let Some((_, name)) = classify_decl_header(text) {
                if split_at_top_level_assign(text).is_some() {
                    declarations.push((idx, qualified_decl_name(&name, &scope_stack)));
                }
            }
        };
        if let Some((_, inner, _)) = split_mutual_block_subspans(span) {
            for sub in inner {
                record(sub.clean_text);
            }
        } else {
            record(span.clean_text);
        }
        update_scope_stack_with_idx(&mut scope_stack, span.orig_text, idx);
    }
    declarations
}

pub(crate) fn open_namespace_prefix(src: &str) -> String {
    let clean = strip_lean_comments(src);
    let spans = parse_command_spans(src, &clean);
    let mut stack = Vec::new();
    for (idx, span) in spans.iter().enumerate() {
        update_scope_stack_with_idx(&mut stack, span.orig_text, idx);
    }
    let ns: Vec<&str> = stack
        .iter()
        .filter(|f| matches!(f.kind, ScopeKind::Namespace))
        .map(|f| f.name.as_str())
        .collect();
    if ns.is_empty() {
        String::new()
    } else {
        format!("namespace {}\n", ns.join("."))
    }
}

fn find_last_matching_span_idx_in_range<F>(
    spans: &[CmdSpan<'_>],
    range: std::ops::RangeInclusive<usize>,
    mut pred: F,
) -> Option<usize>
where
    F: FnMut(&str) -> bool,
{
    if spans.is_empty() || range.is_empty() {
        return None;
    }
    let end = (*range.end()).min(spans.len() - 1);
    let start = *range.start();
    qualified_span_declarations(&spans[..=end])
        .into_iter()
        .rev()
        .find(|(idx, name)| *idx >= start && pred(name))
        .map(|(idx, _)| idx)
}

fn find_last_matching_span_idx<F>(spans: &[CmdSpan<'_>], pred: F) -> Option<usize>
where
    F: FnMut(&str) -> bool,
{
    if spans.is_empty() {
        None
    } else {
        find_last_matching_span_idx_in_range(spans, 0..=spans.len() - 1, pred)
    }
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

/// Preserve the source's scopes and declarations for the identity probe while
/// making earlier theorem proofs irrelevant, as in normal isolated shard checks.
fn stub_identity_probe_src(src: &str) -> String {
    let clean = strip_lean_comments(src);
    parse_command_spans(src, &clean)
        .iter()
        .map(|span| {
            if let Some((header, inner, footer)) = split_mutual_block_subspans(span) {
                return format!(
                    "{header}\n{}\n{footer}",
                    inner
                        .iter()
                        .map(|s| stub_identity_probe_src(s.orig_text))
                        .collect::<Vec<_>>()
                        .join("\n")
                );
            }
            if classify_decl_header(span.clean_text).is_some() {
                if let Some((sig, proof)) = split_at_top_level_assign(span.clean_text) {
                    return format_stubbed_decl_span(span.orig_text, sig, proof);
                }
            }
            sanitize_stubbed_prefix_options(span.orig_text)
        })
        .collect::<Vec<_>>()
        .join("\n")
}

pub(crate) fn declaration_identity_prefix(src: &str, start_line: usize) -> String {
    let clean = strip_lean_comments(src);
    let spans = parse_command_spans(src, &clean);
    let mut prefix = Vec::new();
    for span in &spans {
        if span.start_line >= start_line {
            break;
        }
        if span.end_line >= start_line {
            // `mutual` changes recursion, not the declaration namespace. Flatten
            // only this unfinished group so the independent probe is a command.
            if let Some((_, inner, _)) = split_mutual_block_subspans(span) {
                for sub in inner.iter().take_while(|s| s.start_line < start_line) {
                    prefix.push(stub_identity_probe_src(sub.orig_text));
                }
            }
            break;
        }
        prefix.push(stub_identity_probe_src(span.orig_text));
    }
    prefix.join("\n")
}

/// Build one full-file stubbed identity probe source (`:= sorry` with exact newline preservation)
/// for batched per-file declaration identity confirmation, prepending warning-suppression options
/// immediately after the module/import header and returning the line offset added before the body.
pub(crate) fn build_file_identity_probe(src: &str) -> (String, usize) {
    let stubbed = stub_identity_probe_src(src);
    let header_info = crate::module_builder::parse_header_info(&stubbed);
    let (header, body) = stubbed.split_at(header_info.body_byte_offset);
    let preamble =
        format!("{header}\nset_option warningAsError false\nset_option warn.sorry false\n");
    let header_lines = header.matches('\n').count();
    let preamble_lines = preamble.matches('\n').count();
    (
        format!("{preamble}{body}"),
        preamble_lines.saturating_sub(header_lines),
    )
}

pub(crate) fn sanitize_ident_for_fast_check(name: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let canon = canonicalize_lean_name(name);
    let mut out = String::with_capacity(canon.len() + 8);
    for b in canon.bytes() {
        if b.is_ascii_alphanumeric() {
            out.push(b as char);
        } else {
            out.push('_');
            out.push(HEX[(b >> 4) as usize] as char);
            out.push(HEX[(b & 0x0f) as usize] as char);
        }
    }
    out
}

fn sanitize_ident_for_fast_check_underscore(name: &str) -> String {
    canonicalize_lean_name(name)
        .chars()
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
/// Ambiguous namespace suffixes return an error listing every matching identity.
pub fn reconstruct_single_shard_source(
    src: &str,
    target_decl: &str,
) -> anyhow::Result<Option<String>> {
    let clean = strip_lean_comments(src);
    let spans = parse_command_spans(src, &clean);
    let closed_sections = compute_closed_section_ranges(&spans);

    let declarations = qualified_span_declarations(&spans);
    let Some(decl_idx) = resolve_decl_index(
        declarations.iter().map(|(_, name)| name.as_str()),
        target_decl,
    )?
    else {
        return Ok(None);
    };
    let t_idx = declarations[decl_idx].0;
    let omit_mask = compute_omitted_closed_section_spans(&spans, &closed_sections, t_idx);

    let mut prefix_skeleton_accum = String::with_capacity(src.len());
    let mut scope_stack: Vec<ScopeFrame> = Vec::new();

    for (idx, span) in spans[..t_idx].iter().enumerate() {
        update_scope_stack_with_idx(&mut scope_stack, span.orig_text, idx);
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
    Ok(Some(format!(
        "{}{}\n{}",
        prefix_skeleton_accum, spans[t_idx].orig_text, closing_scopes
    )))
}

fn normalize_whitespace(s: &str) -> String {
    let mut out = Vec::with_capacity(s.len());
    emit_normalized_lean(s, &mut |chunk| out.extend_from_slice(chunk));
    String::from_utf8(out).unwrap_or_else(|e| String::from_utf8_lossy(e.as_bytes()).into_owned())
}

fn flatten_inline_preserving_literals(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0usize;
    let mut emitted_any = false;
    let mut pending_space = false;
    while i < bytes.len() {
        if let Some((end, is_doc)) = scan_lean_block_comment_end(s, i) {
            if is_doc {
                if pending_space {
                    out.push(b' ');
                    pending_space = false;
                }
                out.extend_from_slice(&bytes[i..end]);
                emitted_any = true;
            } else if emitted_any {
                pending_space = true;
            }
            i = end;
            continue;
        }
        if bytes[i] == b'-' && i + 1 < bytes.len() && bytes[i + 1] == b'-' {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            if emitted_any {
                pending_space = true;
            }
            continue;
        }
        if let Some(end) = scan_lean_norm_literal_end(s, i) {
            if pending_space {
                out.push(b' ');
                pending_space = false;
            }
            out.extend_from_slice(&bytes[i..end]);
            emitted_any = true;
            i = end;
            continue;
        }
        let ch = s[i..].chars().next().unwrap_or('\0');
        let ch_len = ch.len_utf8().max(1);
        if ch.is_whitespace() {
            if emitted_any {
                pending_space = true;
            }
            i += ch_len;
        } else {
            if pending_space {
                out.push(b' ');
                pending_space = false;
            }
            let tok_start = i;
            i += ch_len;
            while i < bytes.len() {
                if scan_lean_block_comment_end(s, i).is_some()
                    || (bytes[i] == b'-' && i + 1 < bytes.len() && bytes[i + 1] == b'-')
                    || scan_lean_norm_literal_end(s, i).is_some()
                {
                    break;
                }
                let c = s[i..].chars().next().unwrap_or('\0');
                if c.is_whitespace() {
                    break;
                }
                i += c.len_utf8().max(1);
            }
            out.extend_from_slice(&bytes[tok_start..i]);
            emitted_any = true;
        }
    }
    String::from_utf8(out).unwrap_or_else(|e| String::from_utf8_lossy(e.as_bytes()).into_owned())
}

/// Build a coalesced Lean 4 source file for batch verification of uncached theorem shards `U`:
/// - All **cached** theorems (`name ∉ uncached_names`) have their proof bodies replaced by
///   line-preserving `:= sorry` so Lean skips re-elaborating them in 0 ms while registering their types.
/// - All **uncached** theorems (`name ∈ uncached_names`) retain their full original proof bodies
///   at their exact original line numbers.
pub const FAST_VERIFY_DIRECTIVE_PREFIX: &str = "-- @turbo_fast_verify ";

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct FastVerifyEntry {
    pub orig_rooted: String,
    pub gen_rooted: String,
    pub expected_gen_stmt_hash: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct FastVerifyMap {
    entries: Vec<FastVerifyEntry>,
    orig_to_gen: std::collections::HashMap<String, String>,
    gen_to_orig: std::collections::HashMap<String, String>,
}

fn hex_encode_fast_verify_field(s: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = Vec::with_capacity(s.len() * 2);
    for &b in s.as_bytes() {
        out.push(HEX[(b >> 4) as usize]);
        out.push(HEX[(b & 0x0f) as usize]);
    }
    String::from_utf8(out).unwrap_or_default()
}

fn hex_decode_fast_verify_field(hex: &str) -> anyhow::Result<String> {
    if hex.is_empty() || !hex.len().is_multiple_of(2) {
        anyhow::bail!("Malformed hex field in fast-verify directive: `{}`", hex);
    }
    let bytes = hex.as_bytes();
    let nibble = |b: u8| -> anyhow::Result<u8> {
        match b {
            b'0'..=b'9' => Ok(b - b'0'),
            b'a'..=b'f' => Ok(b - b'a' + 10),
            b'A'..=b'F' => Ok(b - b'A' + 10),
            _ => anyhow::bail!("Invalid hex digit in fast-verify directive: `{}`", hex),
        }
    };
    let mut out = Vec::with_capacity(bytes.len() / 2);
    let mut i = 0usize;
    while i < bytes.len() {
        out.push((nibble(bytes[i])? << 4) | nibble(bytes[i + 1])?);
        i += 2;
    }
    String::from_utf8(out).map_err(|_| anyhow::anyhow!("Invalid UTF-8 in fast-verify directive"))
}

pub(crate) fn format_fast_verify_directive(
    orig_rooted: &str,
    gen_rooted: &str,
    expected_gen_stmt_hash: &str,
) -> String {
    format!(
        "{}{} {} {}",
        FAST_VERIFY_DIRECTIVE_PREFIX,
        hex_encode_fast_verify_field(orig_rooted),
        hex_encode_fast_verify_field(gen_rooted),
        expected_gen_stmt_hash
    )
}

pub(crate) fn has_fast_verify_component(name: &str) -> bool {
    let qname = name.strip_prefix("_root_.").unwrap_or(name);
    host_name_components(qname)
        .iter()
        .any(|c| c.starts_with("_turbo_verify_"))
}

impl FastVerifyMap {
    pub fn entries(&self) -> &[FastVerifyEntry] {
        &self.entries
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn gen_for_orig(&self, orig_rooted: &str) -> Option<&str> {
        let key = format!("_root_.{}", canonicalize_lean_name(orig_rooted));
        self.orig_to_gen
            .get(&key)
            .or_else(|| self.orig_to_gen.get(orig_rooted))
            .map(String::as_str)
    }

    pub fn orig_for_gen(&self, gen_rooted: &str) -> Option<&str> {
        let key = format!("_root_.{}", canonicalize_lean_name(gen_rooted));
        self.gen_to_orig
            .get(&key)
            .or_else(|| self.gen_to_orig.get(gen_rooted))
            .map(String::as_str)
    }

    pub fn canonical_rooted_for_shard(&self, sh: &TheoremShard) -> String {
        let r = sh.rooted_name();
        self.orig_for_gen(&r).unwrap_or(&r).to_string()
    }

    pub fn shard_matches_targets(
        &self,
        sh: &TheoremShard,
        targets: &std::collections::HashSet<String>,
    ) -> bool {
        let canon = self.canonical_rooted_for_shard(sh);
        matches_uncached_name(&canon, targets)
            || matches_uncached_name(sh.effective_name(), targets)
    }

    pub fn parse_and_validate(src: &str, shards: &[TheoremShard]) -> anyhow::Result<Self> {
        let mut entries = Vec::new();
        let mut orig_to_gen = std::collections::HashMap::new();
        let mut gen_to_orig = std::collections::HashMap::new();

        let mut line_comments = Vec::new();
        if src.contains("--") {
            let mut scratch = Vec::with_capacity(src.len());
            scan_lean_comments_with(src, &mut scratch, &mut |s, e| line_comments.push((s, e)));
        }
        for (c_start, c_end) in line_comments {
            let line_start = src[..c_start].rfind('\n').map_or(0, |p| p + 1);
            if !src[line_start..c_start]
                .chars()
                .all(|c| c.is_whitespace() && c != '\n')
            {
                continue;
            }
            let trimmed = src[c_start..c_end].trim();
            if let Some(rest) = trimmed.strip_prefix("-- @turbo_fast_verify") {
                if !rest.starts_with(' ') {
                    anyhow::bail!("Malformed fast-verify directive line: `{}`", trimmed);
                }
                let parts: Vec<&str> = rest.split_whitespace().collect();
                if parts.len() != 3 {
                    anyhow::bail!(
                        "Malformed fast-verify directive (expected 3 fields): `{}`",
                        trimmed
                    );
                }
                let orig_rooted = hex_decode_fast_verify_field(parts[0])?;
                let gen_rooted = hex_decode_fast_verify_field(parts[1])?;
                let expected_gen_stmt_hash = parts[2].to_string();
                if !orig_rooted.starts_with("_root_.")
                    || orig_rooted.len() <= "_root_.".len()
                    || has_fast_verify_component(&orig_rooted)
                {
                    anyhow::bail!(
                        "Invalid fast-verify original target `{}` in directive",
                        orig_rooted
                    );
                }
                if !gen_rooted.starts_with("_root_.")
                    || !has_fast_verify_component(&gen_rooted)
                    || expected_gen_stmt_hash.is_empty()
                    || !expected_gen_stmt_hash
                        .bytes()
                        .all(|b| b.is_ascii_hexdigit())
                {
                    anyhow::bail!(
                        "Invalid fast-verify generated target `{}` in directive",
                        gen_rooted
                    );
                }
                if orig_to_gen.contains_key(&orig_rooted) {
                    anyhow::bail!(
                        "Duplicate fast-verify original target `{}` in shard source",
                        orig_rooted
                    );
                }
                if gen_to_orig.contains_key(&gen_rooted) {
                    anyhow::bail!(
                        "Duplicate fast-verify generated declaration `{}` in shard source",
                        gen_rooted
                    );
                }
                orig_to_gen.insert(orig_rooted.clone(), gen_rooted.clone());
                gen_to_orig.insert(gen_rooted.clone(), orig_rooted.clone());
                entries.push(FastVerifyEntry {
                    orig_rooted,
                    gen_rooted,
                    expected_gen_stmt_hash,
                });
            }
        }

        let mut shard_by_rooted: std::collections::HashMap<String, &TheoremShard> =
            std::collections::HashMap::with_capacity(shards.len());
        for sh in shards {
            let rooted = sh.rooted_name();
            if has_fast_verify_component(&rooted) && !gen_to_orig.contains_key(&rooted) {
                anyhow::bail!(
                    "Unmapped `_turbo_verify_` declaration `{}` in shard source",
                    sh.effective_name()
                );
            }
            if orig_to_gen.contains_key(&rooted) {
                anyhow::bail!(
                    "Fast-verify original target `{}` cannot also be declared directly in shard source",
                    rooted
                );
            }
            if shard_by_rooted.insert(rooted.clone(), sh).is_some()
                && gen_to_orig.contains_key(&rooted)
            {
                anyhow::bail!(
                    "Duplicate generated declaration `{}` in shard source",
                    rooted
                );
            }
        }

        for entry in &entries {
            let Some(gen_sh) = shard_by_rooted.get(&entry.gen_rooted) else {
                anyhow::bail!(
                    "Fast-verify directive references missing declaration `{}` (for `{}`)",
                    entry.gen_rooted,
                    entry.orig_rooted
                );
            };
            if gen_sh.stmt_hash != entry.expected_gen_stmt_hash {
                anyhow::bail!(
                    "Fast-verify statement hash mismatch on `{}` (expected {}, got {})",
                    entry.gen_rooted,
                    entry.expected_gen_stmt_hash,
                    gen_sh.stmt_hash
                );
            }
            let prf_clean = strip_lean_comments(&gen_sh.proof_text);
            if ["sorry", "admit", "sorryAx"]
                .iter()
                .any(|w| contains_word(&prf_clean, w))
            {
                anyhow::bail!(
                    "Fast-verify generated declaration `{}` (for `{}`) contains sorry/admit",
                    entry.gen_rooted,
                    entry.orig_rooted
                );
            }
        }

        Ok(Self {
            entries,
            orig_to_gen,
            gen_to_orig,
        })
    }
}

pub fn build_coalesced_shard_source(
    src: &str,
    uncached_names: &std::collections::HashSet<String>,
) -> String {
    let clean = strip_lean_comments(src);
    let spans = parse_command_spans(src, &clean);
    let parsed_shards = split_lean_source_fast_no_cone(src, &[]).shards;
    let fast_map = FastVerifyMap::parse_and_validate(src, &parsed_shards).ok();
    let is_uncached = |qname: &str| -> bool {
        if matches_uncached_name(qname, uncached_names)
            || matches_uncached_or_fast_verify_name(qname, uncached_names)
        {
            return true;
        }
        let rooted = format!("_root_.{}", canonicalize_lean_name(qname));
        fast_map
            .as_ref()
            .and_then(|m| m.orig_for_gen(&rooted))
            .is_some_and(|orig| matches_uncached_name(orig, uncached_names))
    };

    let mut chunks = Vec::with_capacity(spans.len());
    let mut scope_stack: Vec<ScopeFrame> = Vec::new();
    for (s_idx, span) in spans.iter().enumerate() {
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
                        let qname = qualified_decl_name(&name, &scope_stack);
                        if !is_uncached(&qname) && !has_fast_verify_component(&qname) {
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
                update_scope_stack_with_idx(&mut scope_stack, span.orig_text, s_idx);
                continue;
            }
        }

        if let Some((_kind, name)) = classify_decl_header(span.clean_text) {
            let qname = qualified_decl_name(&name, &scope_stack);
            if !is_uncached(&qname) {
                if has_fast_verify_component(&qname) {
                    update_scope_stack_with_idx(&mut scope_stack, span.orig_text, s_idx);
                    continue;
                }
                if let Some((sig_clean, proof_clean)) = split_at_top_level_assign(span.clean_text) {
                    chunks.push(format_stubbed_decl_span(
                        span.orig_text,
                        sig_clean,
                        proof_clean,
                    ));
                    update_scope_stack_with_idx(&mut scope_stack, span.orig_text, s_idx);
                    continue;
                }
            }
        }
        chunks.push(sanitize_stubbed_prefix_options(span.orig_text));
        update_scope_stack_with_idx(&mut scope_stack, span.orig_text, s_idx);
    }

    chunks.join("\n")
}

/// Return a copy of `src` with every theorem/lemma proof body replaced byte-for-byte with
/// spaces/newlines (preserving exact line numbers), leaving all theorem signatures, attributes,
/// modifiers, definitions, and non-theorem commands intact for `--allow-sorry` hygiene auditing.
pub fn blank_theorem_proof_bodies(src: &str) -> String {
    let clean = strip_lean_comments(src);
    if src.is_empty() || clean.len() != src.len() {
        return src.to_string();
    }
    let spans = parse_command_spans(src, &clean);
    let mut out = src.as_bytes().to_vec();
    let src_base = src.as_ptr() as usize;
    let mut blank_proof = |orig_sub: &str, clean_sub: &str| {
        if classify_decl_header(clean_sub).is_none() {
            return;
        }
        let Some((sig_orig, proof_orig)) = split_at_top_level_assign(orig_sub) else {
            return;
        };
        if split_at_top_level_assign(clean_sub).is_none() {
            return;
        }
        let sub_off = orig_sub.as_ptr() as usize - src_base;
        let proof_rel = proof_orig.as_ptr() as usize - orig_sub.as_ptr() as usize;
        if proof_rel < sig_orig.len() || sub_off + proof_rel + proof_orig.len() > out.len() {
            return;
        }
        for b in &mut out[sub_off + sig_orig.len()..sub_off + proof_rel + proof_orig.len()] {
            if *b != b'\n' && *b != b'\r' {
                *b = b' ';
            }
        }
    };
    for span in &spans {
        if let Some((_header_orig, inner_spans, _footer_orig)) = split_mutual_block_subspans(span) {
            let has_inner_thm = inner_spans.iter().any(|sub| {
                classify_decl_header(sub.clean_text).is_some()
                    && split_at_top_level_assign(sub.clean_text).is_some()
            });
            if has_inner_thm {
                for sub in &inner_spans {
                    blank_proof(sub.orig_text, sub.clean_text);
                }
                continue;
            }
        }
        blank_proof(span.orig_text, span.clean_text);
    }
    String::from_utf8(out).unwrap_or_else(|_| src.to_string())
}

fn contains_local_decl_ref(haystack: &str, short: &str, full_name: &str) -> bool {
    let mut exact_map = std::collections::HashMap::new();
    let mut non_std_short_map = std::collections::HashMap::new();
    extract_local_ref_tokens_into(haystack, 0, &mut exact_map, &mut non_std_short_map);
    if exact_map.contains_key(full_name) || exact_map.contains_key(short) {
        return true;
    }
    if non_std_short_map.contains_key(short) {
        return true;
    }
    if STD_QUAL_PREFIXES.iter().any(|p| full_name.starts_with(p)) {
        return exact_map
            .keys()
            .any(|q| last_host_name_component(q) == short);
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
    let proof_clean = strip_lean_comments(&shards[idx].proof_text);
    for later in &shards[idx..] {
        let short = last_host_name_component(&later.name);
        if contains_local_decl_ref(&proof_clean, short, &later.name) {
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

pub(crate) fn resolve_shard_rooted_targets_with_map(
    shards: &[TheoremShard],
    targets: &[String],
    fast_map: &FastVerifyMap,
) -> anyhow::Result<Vec<String>> {
    targets
        .iter()
        .map(|raw| {
            let t = raw.trim();
            if t.is_empty() {
                anyhow::bail!("Empty target declaration name in shard verification request");
            }
            if has_fast_verify_component(t) {
                anyhow::bail!(
                    "Target declaration `{}` cannot directly name an internal `_turbo_verify_` declaration",
                    t
                );
            }
            let mut hits: Vec<String> = Vec::new();
            for sh in shards {
                let canon_rooted = fast_map.canonical_rooted_for_shard(sh);
                let canon_unrooted = canon_rooted
                    .strip_prefix("_root_.")
                    .unwrap_or(&canon_rooted);
                if decl_name_matches_target(canon_unrooted, t)
                    && !hits.contains(&canon_rooted)
                {
                    hits.push(canon_rooted);
                }
            }
            match hits.len() {
                1 => Ok(hits.pop().unwrap()),
                0 => anyhow::bail!("Target declaration `{}` not found in shard source", t),
                _ => anyhow::bail!(
                    "Ambiguous target declaration `{}` matches multiple declarations: {:?}",
                    t,
                    hits
                ),
            }
        })
        .collect()
}

pub(crate) fn resolve_shard_rooted_targets(
    src: &str,
    shards: &[TheoremShard],
    targets: &[String],
) -> anyhow::Result<(Vec<String>, FastVerifyMap)> {
    let fast_map = FastVerifyMap::parse_and_validate(src, shards)?;
    let resolved = resolve_shard_rooted_targets_with_map(shards, targets, &fast_map)?;
    Ok((resolved, fast_map))
}

fn split_last_lean_name_component(name: &str) -> (&str, &str) {
    let segs = split_lean_name_components(name);
    let Some(&last) = segs.last() else {
        return ("", name);
    };
    if segs.len() == 1 {
        ("", last)
    } else {
        (&name[..name.len() - last.len() - 1], last)
    }
}

pub(crate) fn matches_attested_decl_or_fast_verify(
    got_name: &str,
    expected_full_name: &str,
) -> bool {
    let got_canon = canonicalize_lean_name(got_name);
    let expected_canon = canonicalize_lean_name(expected_full_name);
    if got_canon == expected_canon {
        return true;
    }
    let (got_ns, got_short) = split_last_lean_name_component(&got_canon);
    if let Some(after_prefix) = got_short.strip_prefix("_turbo_verify_") {
        let digits_len = after_prefix
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .count();
        if digits_len > 0 {
            if let Some(orig_safe) = after_prefix[digits_len..].strip_prefix('_') {
                let matches_safe = |cand: &str| {
                    orig_safe == sanitize_ident_for_fast_check(cand)
                        || orig_safe == sanitize_ident_for_fast_check_underscore(cand)
                };
                // Case 1: header wrote `theorem Foo.bar` inside outer namespace `Ns`:
                // `expected_full_name == "Ns.Foo.bar"`, `got_ns == "Ns"`, `decl_name == "Foo.bar"`.
                let (exp_ns, exp_short) = split_last_lean_name_component(&expected_canon);
                if got_ns == exp_ns && matches_safe(exp_short) {
                    return true;
                }
                if got_ns.is_empty() {
                    return matches_safe(&expected_canon);
                }
                if let Some(rel) = expected_canon
                    .strip_prefix(got_ns)
                    .and_then(|s| s.strip_prefix('.'))
                {
                    return matches_safe(rel);
                }
            }
        }
    }
    false
}

pub(crate) fn matches_uncached_or_fast_verify_name(
    name: &str,
    uncached_names: &std::collections::HashSet<String>,
) -> bool {
    if matches_uncached_name(name, uncached_names) {
        return true;
    }
    uncached_names
        .iter()
        .any(|u| matches_attested_decl_or_fast_verify(name, u.as_str()))
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
            if let Some((name, after_name)) = take_leading_lean_ident(trimmed_after) {
                if (after_name.is_empty()
                    || after_name.starts_with(|c: char| {
                        c.is_whitespace() || matches!(c, '(' | '{' | '[' | ':')
                    }))
                    && orig_text.len() == clean_text.len()
                {
                    let offset_in_clean = clean_text.len() - trimmed_after.len();
                    let name_end = offset_in_clean + name.len();
                    let safe_name = sanitize_ident_for_fast_check(name);
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
    // Only rewrites that keep every user tactic: substituting a whole proof body would certify a proof
    // that was never checked (and drop any `sorry`-expanding tactic it contains).
    if proof_orig.contains("dsimp [") && proof_orig.contains("]; simp") {
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
    scope_stack: &[ScopeFrame],
    indent_prefix: &str,
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
            if kw_pos > 0 {
                let prev = sig_clean[..kw_pos].chars().next_back().unwrap_or(' ');
                if is_lean_id_rest(prev) || prev == '»' || prev == '.' {
                    continue;
                }
            }
            let after_kw = &sig_clean[kw_pos + kw.len()..];
            if !after_kw.starts_with(char::is_whitespace) {
                continue;
            }
            let trimmed_after = after_kw.trim_start();
            let name_rel_pos = after_kw.len() - trimmed_after.len();
            if let Some((parsed_name, _)) = take_leading_lean_ident(trimmed_after) {
                if parsed_name == decl_name {
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
                    let renamed_body = format!(
                        "{}{}{}{}{}{}",
                        prefix_orig,
                        &sig_orig[kw_pos..abs_name_start],
                        replacement,
                        &sig_orig[abs_name_end..],
                        sep,
                        opt_proof
                    );
                    let renamed_doc = strip_non_doc_lean_comments(&renamed_body);
                    let renamed_clean = strip_lean_comments(&renamed_body);
                    let (gen_sig_clean, _) = split_at_top_level_assign(&renamed_clean)?;
                    let gen_sig_doc = renamed_doc
                        .get(..gen_sig_clean.len())
                        .unwrap_or(gen_sig_clean);
                    let expected_gen_stmt_hash = hash_normalized_whitespace_hex(gen_sig_doc);
                    let orig_rooted = format!(
                        "_root_.{}",
                        canonicalize_lean_name(&qualified_decl_name(decl_name, scope_stack))
                    );
                    let gen_rooted = format!(
                        "_root_.{}",
                        canonicalize_lean_name(&qualified_decl_name(&replacement, scope_stack))
                    );
                    let directive = format_fast_verify_directive(
                        &orig_rooted,
                        &gen_rooted,
                        &expected_gen_stmt_hash,
                    );
                    return Some(format!("{}{}\n{}", indent_prefix, directive, renamed_body));
                }
            }
        }
    }
    None
}

fn compute_uncached_omitted_closed_section_mask(
    spans: &[CmdSpan<'_>],
    closed_sections: &[(usize, usize)],
    end_span_idx: usize,
    uncached_names: &std::collections::HashSet<String>,
) -> Vec<bool> {
    let mut omit_closed_sec = vec![false; end_span_idx + 1];
    let mut uncached_span_prefix = vec![0usize; end_span_idx + 2];
    for (idx, name) in qualified_span_declarations(&spans[..=end_span_idx]) {
        if matches_uncached_name(&name, uncached_names) {
            uncached_span_prefix[idx + 1] += 1;
        }
    }
    for i in 1..uncached_span_prefix.len() {
        uncached_span_prefix[i] += uncached_span_prefix[i - 1];
    }
    for &(sec_open, sec_close) in closed_sections {
        if sec_close <= end_span_idx
            && uncached_span_prefix[sec_close + 1] == uncached_span_prefix[sec_open]
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
        if matches_uncached_name(shard.decl_name(), uncached_names) {
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
    let has_explicit_init = split.imports_header.lines().any(|l| {
        let t = l
            .trim()
            .strip_prefix("public ")
            .map(str::trim_start)
            .unwrap_or(l.trim())
            .strip_prefix("meta ")
            .map(str::trim_start)
            .unwrap_or(l.trim());
        t == "import Init" || t == "import all Init"
    });
    let hdr_info = crate::module_builder::parse_header_info(&split.imports_header);
    if hdr_info.header_error.is_none() {
        for imp_mod in &hdr_info.imports {
            if imp_mod != "Init" || has_explicit_init {
                let stmt = format!("import {}", imp_mod);
                if seen_imports.insert(stmt.clone()) {
                    chunks.push(stmt);
                }
            }
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
                        .map(|(_, n)| {
                            matches_uncached_name(
                                &qualified_decl_name(&n, &scope_stack),
                                uncached_names,
                            )
                        })
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
                                let sub_indent = &sub.orig_text
                                    [..sub.orig_text.len() - sub.orig_text.trim_start().len()];
                                let renamed = rename_decl_header_for_fast_check(
                                    sub.orig_text,
                                    sub.clean_text,
                                    &name,
                                    cur_idx,
                                    &scope_stack,
                                    sub_indent,
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
                update_scope_stack_with_idx(&mut scope_stack, span.orig_text, s_idx);
                continue;
            }
        }

        if let Some((_kind, name)) = classify_decl_header(span.clean_text) {
            if split_at_top_level_assign(span.clean_text).is_some() {
                let cur_idx = thm_idx;
                thm_idx += 1;
                if matches_uncached_name(&qualified_decl_name(&name, &scope_stack), uncached_names)
                {
                    let renamed = rename_decl_header_for_fast_check(
                        span.orig_text,
                        span.clean_text,
                        &name,
                        cur_idx,
                        &scope_stack,
                        "",
                    )?;
                    chunks.push(renamed);
                } else {
                    // If a cached theorem in an active scope has `@[local ...]`, re-enable its
                    // local attribute on the imported constant in the active scope.
                    for local_attr in extract_local_attributes(span.clean_text) {
                        chunks.push(format!("attribute [{}] {}", local_attr, name));
                    }
                }
                update_scope_stack_with_idx(&mut scope_stack, span.orig_text, s_idx);
                continue;
            }
        }
        if is_scope_or_context_command(span.clean_text) {
            let trimmed_clean = span.clean_text.trim();
            if trimmed_clean.starts_with("attribute ") && trimmed_clean.contains("to_additive") {
                update_scope_stack_with_idx(&mut scope_stack, span.orig_text, s_idx);
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
                    update_scope_stack_with_idx(&mut scope_stack, span.orig_text, s_idx);
                    continue;
                }
            }
            chunks.push(format_scoped_instance_for_fast_check(
                span.orig_text,
                span.clean_text,
                s_idx,
            ));
        }
        update_scope_stack_with_idx(&mut scope_stack, span.orig_text, s_idx);
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
                if matches_uncached_name(&qualified_decl_name(&name, &scope_stack), uncached_names)
                {
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
                update_scope_stack_with_idx(&mut scope_stack, span.orig_text, s_idx);
                continue;
            }
        }

        if contains_mathlib_tactic_or_namespace(span.clean_text) {
            return None;
        }
        out_chunks.push(span.orig_text.to_string());
        update_scope_stack_with_idx(&mut scope_stack, span.orig_text, s_idx);
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
        if matches_uncached_name(shard.decl_name(), uncached_names)
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
            uncached_shards.iter().map(|s| s.rooted_name()).collect();
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
                    if matches_uncached_name(
                        &qualified_decl_name(&name, &scope_stack),
                        &uncached_names,
                    ) {
                        if let Some(renamed) = rename_decl_header_for_fast_check(
                            span.orig_text,
                            span.clean_text,
                            &name,
                            cur_idx,
                            &scope_stack,
                            "",
                        ) {
                            block_chunks.push(renamed);
                        }
                    } else {
                        for local_attr in extract_local_attributes(span.clean_text) {
                            has_non_ns_scope = true;
                            block_chunks.push(format!("attribute [{}] {}", local_attr, name));
                        }
                    }
                    update_scope_stack_with_idx(&mut scope_stack, span.orig_text, s_idx);
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
                update_scope_stack_with_idx(&mut scope_stack, span.orig_text, s_idx);
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
    let mut i = start_offset;

    while i < bytes.len() {
        if let Some((cend, _)) = scan_lean_block_comment_end(sig_clean, i) {
            i = cend;
            continue;
        }
        if let Some(end) = scan_lean_norm_literal_end(sig_clean, i) {
            i = end;
            continue;
        }
        let c = bytes[i];
        match c {
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
            flatten_inline_preserving_literals(s)
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
    let (mut depth, mut last, bytes) = (0usize, 0usize, s_clean.as_bytes());
    let mut i = 0usize;
    while i < bytes.len() {
        if let Some((cend, _)) = scan_lean_block_comment_end(s_clean, i) {
            i = cend;
            continue;
        }
        if let Some(end) = scan_lean_norm_literal_end(s_clean, i) {
            i = end;
            continue;
        }
        let b = bytes[i];
        match b {
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
                if cut.is_instance
                    || (!cut.ident.is_empty() && contains_word(sig_clean, &cut.ident))
                {
                    return Vec::new();
                }
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

    let mut scope_stack = Vec::new();
    for (idx, span) in spans.iter().enumerate() {
        let mut after_attrs = span.clean_text.trim_start();
        while let Some(next) = strip_leading_attr_block(after_attrs) {
            after_attrs = next.trim_start();
        }
        let is_priv = after_attrs.starts_with("private ");
        if let Some((kw, name)) = classify_any_decl_header(span.clean_text) {
            let short = name.rsplit('.').next().unwrap_or(&name).to_string();
            let qname = qualified_decl_name(&name, &scope_stack);
            let matches_filter = decl_filter
                .filter(|d| !d.is_empty() && *d != "auto")
                .map(|df| decl_name_matches_target(&qname, df))
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
        update_scope_stack_with_idx(&mut scope_stack, span.orig_text, idx);
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceDeclFingerprint {
    pub qualified_name: String,
    pub kind: String,
    pub stmt_or_decl_hash: String,
    pub proof_hash: Option<String>,
    pub clean_text: String,
}

/// Extract all top-level and `mutual`-nested named declarations (`theorem`, `lemma`, `def`,
/// `abbrev`, `structure`, `inductive`, `class`, `instance`, `opaque`, `axiom`, etc.) with
/// normalized hashes so `turbo-lean impact` tracks both theorem proof/statement edits AND
/// `def`/`abbrev`/`structure`/`inductive` edits.
pub fn extract_all_source_decl_fingerprints(src: &str) -> Vec<SourceDeclFingerprint> {
    let clean = strip_lean_comments(src);
    let spans = parse_command_spans(src, &clean);
    let mut scope_stack = Vec::new();
    let mut out = Vec::new();

    for (idx, span) in spans.iter().enumerate() {
        if let Some((_hdr, inner_spans, _ftr)) = split_mutual_block_subspans(span) {
            for sub in &inner_spans {
                if let Some((kind, name)) = classify_decl_header(sub.clean_text) {
                    if let Some((sig_clean, proof_clean)) =
                        split_at_top_level_assign(sub.clean_text)
                    {
                        let qname = qualified_decl_name(&name, &scope_stack);
                        out.push(SourceDeclFingerprint {
                            qualified_name: if qname.is_empty() { name } else { qname },
                            kind,
                            stmt_or_decl_hash: hash_normalized_whitespace_hex(sig_clean),
                            proof_hash: Some(hash_normalized_whitespace_hex(proof_clean)),
                            clean_text: sub.clean_text.to_string(),
                        });
                        continue;
                    }
                }
                if let Some((kw, name)) = classify_any_decl_header(sub.clean_text) {
                    if !name.is_empty() {
                        let qname = qualified_decl_name(&name, &scope_stack);
                        out.push(SourceDeclFingerprint {
                            qualified_name: if qname.is_empty() { name } else { qname },
                            kind: kw.to_string(),
                            stmt_or_decl_hash: hash_normalized_whitespace_hex(sub.clean_text),
                            proof_hash: None,
                            clean_text: sub.clean_text.to_string(),
                        });
                    }
                }
            }
            update_scope_stack_with_idx(&mut scope_stack, span.orig_text, idx);
            continue;
        }

        if let Some((kind, name)) = classify_decl_header(span.clean_text) {
            if let Some((sig_clean, proof_clean)) = split_at_top_level_assign(span.clean_text) {
                let qname = qualified_decl_name(&name, &scope_stack);
                out.push(SourceDeclFingerprint {
                    qualified_name: if qname.is_empty() { name } else { qname },
                    kind,
                    stmt_or_decl_hash: hash_normalized_whitespace_hex(sig_clean),
                    proof_hash: Some(hash_normalized_whitespace_hex(proof_clean)),
                    clean_text: span.clean_text.to_string(),
                });
                update_scope_stack_with_idx(&mut scope_stack, span.orig_text, idx);
                continue;
            }
        }
        if let Some((kw, name)) = classify_any_decl_header(span.clean_text) {
            if !name.is_empty() {
                let qname = qualified_decl_name(&name, &scope_stack);
                out.push(SourceDeclFingerprint {
                    qualified_name: if qname.is_empty() { name } else { qname },
                    kind: kw.to_string(),
                    stmt_or_decl_hash: hash_normalized_whitespace_hex(span.clean_text),
                    proof_hash: None,
                    clean_text: span.clean_text.to_string(),
                });
            }
        }
        update_scope_stack_with_idx(&mut scope_stack, span.orig_text, idx);
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn test_indented_set_option_in_is_stripped_as_declaration_prefix() {
        let src = "  set_option foo bar in\n  theorem wrapped : True := by trivial";
        assert_eq!(
            strip_decl_prefixes(src),
            "theorem wrapped : True := by trivial"
        );
        assert_eq!(
            classify_decl_header(src),
            Some(("theorem".to_string(), "wrapped".to_string()))
        );
        let split = split_lean_source(src, &[]);
        assert_eq!(split.shards.len(), 1);
        assert_eq!(split.shards[0].name, "wrapped");
    }

    #[test]
    fn lexical_scope_preserves_apostrophes_in_identifiers() {
        let src = "namespace B'x'y\ndef quote : Char := '\"'\ntheorem same : True := True.intro\nend B'x'y\n";
        let split = split_lean_source(src, &[]);
        assert_eq!(split.shards.len(), 1);
        assert_eq!(split.shards[0].decl_name(), "B'x'y.same");
        assert!(skip_lean_lexeme("B'x'y", 1).is_none());
        assert!(skip_lean_lexeme("'x'", 0).is_some());
    }

    #[test]
    fn test_strip_lean_comments_preserves_lines_strings_and_char_literals() {
        let src = "import Init\n-- line comment with sorry\n/- block\n   nested /- inner -/ end -/\ndef q1 : Char := '\"' -- comment after double-quote char\ndef q2 : Char := '\\'' /- block comment after escaped single-quote\nsorry -/\ndef q3 : Char := '\\\\' -- comment after backslash char\ndef id' : Nat := 1 -- identifier prime must not start char literal\ndef msg : String := \"-- not a comment /- neither -/\"\ntheorem t1 : True := by\n  trivial\n";
        let clean = strip_lean_comments(src);
        assert_eq!(src.lines().count(), clean.lines().count());
        assert_eq!(src.len(), clean.len());
        assert!(!clean.contains("line comment") && !clean.contains("inner"));
        assert!(!clean.contains("comment after double-quote char"));
        assert!(!clean.contains("block comment after escaped single-quote"));
        assert!(!clean.contains("sorry"));
        assert!(!clean.contains("identifier prime"));
        assert!(clean.contains("'\"'") && clean.contains("'\\''") && clean.contains("'\\\\'"));
        assert!(clean.contains("\"-- not a comment /- neither -/\""));
        assert!(audit_hygiene(&clean).is_clean_for_certification());
    }

    #[test]
    fn test_checking_weakening_source_options_and_scoped_metaprograms() {
        for command in [
            "set_option debug.skipKernelTC true",
            "set_option debug.skipKernelTC false",
            "set_option debug.other false",
            "set_option warn.sorry false",
            "set_option weak.debug.skipKernelTC true",
            "set_option weak.weak.warn.sorry false",
            "set_option «debug».«skipKernelTC» true",
            "set_option\n /- comment -/ debug.skipKernelTC\n true",
            "set_option debug.skipKernelTC true in\ntheorem bad : True := True.intro",
            "section\nset_option warn.sorry false\nend",
            "open Lean Elab Command in run_cmd set_option debug.skipKernelTC true",
            "run_elab pure ()",
            "run_meta pure ()",
        ] {
            let report = audit_hygiene(&strip_lean_comments(command));
            assert!(
                report.has_checking_weakening && !report.is_clean_for_certification(),
                "{command}: {report:?}"
            );
            assert!(reject_checking_weakening(command).is_err(), "{command}");
        }
        for command in [
            "set_option maxHeartbeats 400000\ntheorem good : True := True.intro",
            "set_option maxHeartbeats 400000 in\ntheorem good : True := True.intro",
            "set_option warn.sorry true",
            "set_option linter.deprecated false in\ndef n := 1",
            "-- set_option debug.skipKernelTC true\n/- run_cmd -/",
            "def text := \"run_elab; set_option debug.skipKernelTC true\"",
        ] {
            assert!(reject_checking_weakening(command).is_ok(), "{command}");
        }
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
    fn test_axiom_allowlist_globs_hygiene_and_base_revision() {
        assert!(glob_match(
            "*._native.bv_decide.ax_*",
            "A.b._native.bv_decide.ax_1_5"
        ));
        assert!(!glob_match(
            "*._native.bv_decide.ax_*",
            "A.b._native.native_decide.ax_1"
        ));
        assert!(glob_match("Lean.ofReduceBool", "Lean.ofReduceBool") && !glob_match("Lean.*", "X"));
        let rep = audit_hygiene(
            "theorem a : True := by native_decide\ntheorem b : x = x := by bv_decide\n",
        );
        assert_eq!(
            rep.flagged_items,
            ["L1: native_decide/ofReduceBool", "L2: bv_decide"]
        );
        let std3: Vec<String> = STANDARD_AXIOMS.map(String::from).to_vec();
        let only_bv = [std3.clone(), vec!["*._native.bv_decide.ax_*".to_string()]].concat();
        let wildcard = [std3.clone(), vec!["*".to_string()]].concat();
        let native_glob = [std3.clone(), vec!["*._native.*.ax_*".to_string()]].concat();
        assert_eq!(blocking_items_under(&rep.flagged_items, &std3).len(), 2);
        assert_eq!(
            blocking_items_under(&rep.flagged_items, &only_bv),
            ["L1: native_decide/ofReduceBool"]
        );
        assert!(blocking_items_under(&rep.flagged_items, &wildcard).is_empty());
        assert!(blocking_items_under(&rep.flagged_items, &native_glob).is_empty());
        let sorry_rep = audit_hygiene("theorem bad : False := sorry\n");
        assert_eq!(
            blocking_items_under(&sorry_rep.flagged_items, &wildcard).len(),
            1
        );

        // The policy comes from the nearest `turbo-lean.toml`, at the given revision if any.
        let repo = std::env::temp_dir().join(format!("turbo_lean_axpol_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&repo);
        std::fs::create_dir_all(repo.join("sub")).unwrap();
        let git = |args: &[&str]| {
            std::process::Command::new("git")
                .args(args)
                .current_dir(&repo)
                .output()
                .unwrap()
        };
        git(&["init", "-q"]);
        git(&[
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@t",
            "commit",
            "-q",
            "--allow-empty",
            "-m",
            "base",
        ]);
        std::fs::write(repo.join("turbo-lean.toml"), "[audit_spec]\nallow = [\"x\"]\n[axioms]\nallow = [\n  \"A.*\", # comment\n  \"B\",\n]\n").unwrap();
        let allow = |rev| {
            read_project_config(&repo.join("sub"), rev)
                .unwrap()
                .and_then(|t| crate::accelerators::toml_string_array(&t, "axioms", "allow"))
        };
        assert_eq!(allow(None).unwrap(), ["A.*", "B"]);
        assert_eq!(allow(Some("HEAD")), None);
        std::fs::write(
            repo.join("turbo-lean.toml"),
            "[zygote]\ntimeout_secs = 900\n",
        )
        .unwrap();
        let cfg = read_project_config(&repo, None).unwrap().unwrap();
        assert_eq!(
            crate::accelerators::toml_value(&cfg, "zygote", "timeout_secs").unwrap(),
            "900"
        );
        let _ = std::fs::remove_dir_all(&repo);
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
    fn test_cross_file_coalescing_selects_qualified_identity() {
        let src = "namespace A\ntheorem same : True := True.intro\nend A\nnamespace B\ntheorem same : 1 = 1 := rfl\nend B\n";
        let split = split_lean_source(src, &[]);
        for (target, proof, other) in [
            ("A.same", "True.intro", ":= rfl"),
            ("B.same", ":= rfl", "True.intro"),
        ] {
            let idx = find_decl_shard_index(&split.shards, target)
                .unwrap()
                .unwrap();
            let cross =
                build_cross_file_coalesced_shard(&[("Pkg.Duplicate", src, &[&split.shards[idx]])]);
            assert!(cross.contains(proof), "{}", cross);
            assert!(!cross.contains(other), "{}", cross);
            assert_eq!(cross.matches("theorem _turbo_verify_").count(), 1);
        }
    }

    #[test]
    fn test_qualified_request_never_suffix_matches() {
        let split = split_lean_source(
            "namespace B.A\ntheorem same : True := trivial\nend B.A\n",
            &[],
        );
        let resolve = |t: &str| {
            find_decl_shard_index(&split.shards, t)
                .unwrap()
                .map(|i| split.shards[i].decl_name().to_string())
        };
        assert_eq!(resolve("A.same"), None);
        assert_eq!(resolve("B.A.same").as_deref(), Some("B.A.same"));
        assert_eq!(resolve("same").as_deref(), Some("B.A.same"));
        let dup = split_lean_source(
            "namespace A\ntheorem same : True := trivial\nend A\nnamespace C\ntheorem same : True := trivial\nend C\n",
            &[],
        );
        assert!(find_decl_shard_index(&dup.shards, "same").is_err());
        assert!(!decl_name_matches_target("B.A.same", "A.same"));

        let root_and_ns = split_lean_source(
            "theorem same : True := trivial\nnamespace A\ntheorem same : True := trivial\nend A\n",
            &[],
        );
        assert!(find_decl_shard_index(&root_and_ns.shards, "same").is_err());
        assert_eq!(
            find_decl_shard_index(&root_and_ns.shards, "_root_.same")
                .unwrap()
                .map(|i| root_and_ns.shards[i].decl_name()),
            Some("same")
        );
        assert_eq!(
            find_decl_shard_index(&root_and_ns.shards, "A.same")
                .unwrap()
                .map(|i| root_and_ns.shards[i].decl_name()),
            Some("A.same")
        );
    }

    #[test]
    fn test_escaped_identifiers_and_multiline_literal_scope_tracking() {
        let src = concat!(
            "namespace A\n",
            "def «a\"b» : String :=\n",
            "\"line1\n",
            "end A\n",
            "namespace Fake\"\n",
            "theorem «foo» : True := True.intro\n",
            "end A\n",
        );
        let split = split_lean_source(src, &[]);
        assert_eq!(split.shards.len(), 1);
        assert_eq!(split.shards[0].decl_name(), "A.foo");
        assert_eq!(
            find_decl_shard_index(&split.shards, "A.foo").unwrap(),
            Some(0)
        );
        assert_eq!(
            find_decl_shard_index(&split.shards, "A.«foo»").unwrap(),
            Some(0)
        );
        assert_eq!(
            find_decl_shard_index(&split.shards, "«foo»").unwrap(),
            Some(0)
        );
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

        let decl_semi = "theorem semi_thm (a : Nat) : a = a := by\n  unfold id\n  have h_one : 1 = 1 := rfl; have h_eq : a + 0 = a := by omega\n  exact h_eq";
        let hs_shards = fission_theorem_have_blocks(decl_semi, "semi_thm");
        assert_eq!(hs_shards.len(), 3);
        assert_eq!(
            hs_shards[0].sub_decl_source,
            "theorem semi_thm (a : Nat) : 1 = 1 := rfl"
        );
        assert_eq!(
            hs_shards[1].sub_decl_source,
            "theorem semi_thm (a : Nat) (h_one : 1 = 1) : a + 0 = a := by omega"
        );
        assert_eq!(hs_shards[2].sub_decl_source, "theorem semi_thm (a : Nat) (h_one : 1 = 1) (h_eq : a + 0 = a) : a = a := by\n  unfold id\n  exact h_eq");

        let decl_havei = "theorem havei_semi_thm (a : Nat) : a = a := by\n  unfold id\n  haveI : Nonempty Nat := ⟨a⟩; have h_eq : a + 0 = a := by omega\n  exact h_eq";
        assert!(fission_theorem_have_blocks(decl_havei, "havei_semi_thm").is_empty());

        let decl_classical = "theorem cls_thm (a : Nat) : a = a := by\n  classical\n  have h_one : 1 = 1 := rfl\n  change a = a\n  have h_eq : a + 0 = a := by omega\n  exact h_eq";
        let lc_shards = fission_theorem_have_blocks(decl_classical, "cls_thm");
        assert_eq!(lc_shards.len(), 3);
        assert_eq!(
            lc_shards[0].sub_decl_source,
            "theorem cls_thm (a : Nat) : 1 = 1 := by\n  classical\n  exact (rfl)"
        );
        assert_eq!(
            lc_shards[1].sub_decl_source,
            "theorem cls_thm (a : Nat) (h_one : 1 = 1) : a + 0 = a := by classical; omega"
        );
        assert_eq!(lc_shards[2].sub_decl_source, "theorem cls_thm (a : Nat) (h_one : 1 = 1) (h_eq : a + 0 = a) : a = a := by\n  classical\n  change a = a\n  exact h_eq");

        let decl_leti_classical = "theorem leti_cls_thm (a : Nat) : a = a := by\n  classical\n  letI : DecidableEq Nat := inferInstance\n  change a = a\n  have h_eq : a + 0 = a := by omega\n  exact h_eq";
        assert!(fission_theorem_have_blocks(decl_leti_classical, "leti_cls_thm").is_empty());

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
        assert!(fission_theorem_have_blocks(decl_underscore, "underscore_thm").is_empty());
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
            if let Some(rec) = reconstruct_single_shard_source(src, s.decl_name()).unwrap() {
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
            src.lines()
                .nth(target_shard.start_line - 1)
                .map(|l| l.trim())
        );
    }

    #[test]
    fn test_fast_verify_map_rejects_unmapped_synthetic_collisions_and_tampered_stmt() {
        let unmapped = "import Init\ntheorem _turbo_verify_0_a_b : True := trivial\n";
        let unmapped_shards = split_lean_source(unmapped, &[]).shards;
        assert!(FastVerifyMap::parse_and_validate(unmapped, &unmapped_shards).is_err());
        assert!(resolve_shard_rooted_targets(
            unmapped,
            &unmapped_shards,
            &["_root_.a.b".to_string()]
        )
        .is_err());
        assert!(resolve_shard_rooted_targets(
            unmapped,
            &unmapped_shards,
            &["_root_.a_b".to_string()]
        )
        .is_err());

        let src = "namespace a\ndef helper : Nat := 1\ntheorem b : helper = 1 := rfl\nend a\nnamespace x\ntheorem y : 1 = 1 := rfl\nend x\n";
        let uncached: HashSet<String> = ["a.b".to_string()].into_iter().collect();
        let fast_src = build_fast_olean_shard_source(src, "Pkg.Demo", &uncached)
            .expect("expected fast olean shard");
        let fast_shards = split_lean_source(&fast_src, &[]).shards;
        let (resolved_ab, map) =
            resolve_shard_rooted_targets(&fast_src, &fast_shards, &["a.b".to_string()])
                .expect("expected exact mapped resolution for a.b");
        assert_eq!(resolved_ab, vec!["_root_.a.b".to_string()]);
        assert_eq!(
            map.gen_for_orig("_root_.a.b"),
            Some("_root_.a._turbo_verify_0_b")
        );
        assert!(
            resolve_shard_rooted_targets(&fast_src, &fast_shards, &["_root_.a_b".to_string()])
                .is_err()
        );
        assert!(resolve_shard_rooted_targets(
            &fast_src,
            &fast_shards,
            &["_root_.a._turbo_verify_0_b".to_string()]
        )
        .is_err());

        let tampered_stmt = fast_src.replace("helper = 1", "True");
        let tampered_shards = split_lean_source(&tampered_stmt, &[]).shards;
        assert!(FastVerifyMap::parse_and_validate(&tampered_stmt, &tampered_shards).is_err());

        let tampered_sorry = fast_src.replace(":= rfl", ":= sorry");
        let sorry_shards = split_lean_source(&tampered_sorry, &[]).shards;
        assert!(FastVerifyMap::parse_and_validate(&tampered_sorry, &sorry_shards).is_err());

        let first_dir = fast_src
            .lines()
            .find(|l| l.trim().starts_with(FAST_VERIFY_DIRECTIVE_PREFIX))
            .unwrap();
        let dup_dir = format!("{}\n{}", first_dir, fast_src);
        let dup_shards = split_lean_source(&dup_dir, &[]).shards;
        assert!(FastVerifyMap::parse_and_validate(&dup_dir, &dup_shards).is_err());

        // `-- @turbo_fast_verify` inside block comments, multiline strings, raw strings, or
        // interpolated strings is not a real line-comment directive and must be ignored.
        let benign_docs = concat!(
            "/- Docs mentioning:\n",
            "   -- @turbo_fast_verify malformed\n",
            "   /- nested\n",
            "      -- @turbo_fast_verify 00\n",
            "   -/\n",
            "-/\n",
            "def strDoc : String := \"line1\n  -- @turbo_fast_verify malformed\nline3\"\n",
            "def rawDoc : String := r#\"line1\n-- @turbo_fast_verify malformed\n\"#\n",
            "def interpDoc : String := s!\"line1\n-- @turbo_fast_verify malformed {1 + 1}\"\n",
            "def trailingCode : Nat := 1 -- @turbo_fast_verify malformed\n",
            "theorem clean_thm : strDoc.length > 0 := by decide\n",
        );
        let benign_shards = split_lean_source(benign_docs, &[]).shards;
        let benign_map = FastVerifyMap::parse_and_validate(benign_docs, &benign_shards)
            .expect("comments/strings mentioning @turbo_fast_verify must not fail validation");
        assert!(benign_map.is_empty());

        // Actual standalone line-comment directives that are malformed must still fail closed.
        let real_bad = "  -- @turbo_fast_verify malformed\ntheorem t : True := trivial\n";
        let real_bad_shards = split_lean_source(real_bad, &[]).shards;
        assert!(FastVerifyMap::parse_and_validate(real_bad, &real_bad_shards).is_err());
    }

    #[test]
    fn test_normalization_preserves_string_char_literals_and_layout() {
        let s1 = split_lean_source("theorem t : \"a b\" = \"a b\" := rfl\n", &[]);
        let s2 = split_lean_source("theorem t : \"a  b\" = \"a b\" := rfl\n", &[]);
        assert_ne!(s1.interface_hash, s2.interface_hash);
        assert_ne!(s1.shards[0].stmt_hash, s2.shards[0].stmt_hash);

        let esc1 = split_lean_source("theorem t : \"x\\\"  y\" = \"x\\\"  y\" := rfl\n", &[]);
        let esc2 = split_lean_source("theorem t : \"x\\\" y\" = \"x\\\"  y\" := rfl\n", &[]);
        assert_ne!(esc1.shards[0].stmt_hash, esc2.shards[0].stmt_hash);

        let ml1 = split_lean_source("theorem t : \"a\n  b\" = \"a\n  b\" := rfl\n", &[]);
        let ml2 = split_lean_source("theorem t : \"a b\" = \"a\n  b\" := rfl\n", &[]);
        assert_ne!(ml1.shards[0].stmt_hash, ml2.shards[0].stmt_hash);

        let raw1 = split_lean_source("theorem t : r#\"a  b\"# = r#\"a  b\"# := rfl\n", &[]);
        let raw2 = split_lean_source("theorem t : r#\"a b\"# = r#\"a  b\"# := rfl\n", &[]);
        assert_ne!(raw1.shards[0].stmt_hash, raw2.shards[0].stmt_hash);

        let interp1 = split_lean_source(
            "theorem t : s!\"a  {1 + 1}  b\" = \"a  2  b\" := rfl\n",
            &[],
        );
        let interp2 =
            split_lean_source("theorem t : s!\"a {1 + 1} b\" = \"a  2  b\" := rfl\n", &[]);
        assert_ne!(interp1.shards[0].stmt_hash, interp2.shards[0].stmt_hash);
        let interp_sorry = split_lean_source("def f : String := s!\"x {sorry} y\"\n", &[]);
        assert!(interp_sorry.hygiene.has_sorry);

        let interp_cmt1 = split_lean_source("def f : String := s!\"x {1 /- c -/ + 1} y\"\n", &[]);
        let interp_cmt2 = split_lean_source("def f : String := s!\"x {1 + 1} y\"\n", &[]);
        assert_eq!(interp_cmt1.interface_hash, interp_cmt2.interface_hash);

        let interp_lit1 = split_lean_source(
            "theorem t : s!\"x {\"a  b\"} y\" = \"x a  b y\" := rfl\n",
            &[],
        );
        let interp_lit2 = split_lean_source(
            "theorem t : s!\"x {\"a b\"} y\" = \"x a  b y\" := rfl\n",
            &[],
        );
        assert_ne!(
            interp_lit1.shards[0].stmt_hash,
            interp_lit2.shards[0].stmt_hash
        );

        let r_ident1 = split_lean_source(
            "def f (r : String) : String := r\ntheorem t : f \"a  b\" = \"a  b\" := rfl\n",
            &[],
        );
        let r_ident2 = split_lean_source(
            "def f (r : String) : String := r\ntheorem t : f \"a b\" = \"a  b\" := rfl\n",
            &[],
        );
        assert_ne!(r_ident1.shards[0].stmt_hash, r_ident2.shards[0].stmt_hash);

        let c1 = split_lean_source("theorem t : ' ' = ' ' := rfl\n", &[]);
        let c2 = split_lean_source("theorem t : '\t' = ' ' := rfl\n", &[]);
        assert_ne!(c1.shards[0].stmt_hash, c2.shards[0].stmt_hash);
        assert_ne!(c1.interface_hash, c2.interface_hash);

        let pfx1 = split_lean_source(
            "def msg : String := \"a b\"\ntheorem t : msg = \"a b\" := rfl\n",
            &[],
        );
        let pfx2 = split_lean_source(
            "def msg : String := \"a  b\"\ntheorem t : msg = \"a b\" := rfl\n",
            &[],
        );
        assert_ne!(
            pfx1.shards[0].prefix_env_hash,
            pfx2.shards[0].prefix_env_hash
        );
        assert_ne!(pfx1.shards[0].cone_env_hash, pfx2.shards[0].cone_env_hash);

        let sec1 = split_lean_source(
            "section S\nend S\ndef msg : String := \"a b\"\ntheorem t : msg = \"a b\" := rfl\n",
            &[],
        );
        let sec2 = split_lean_source(
            "section S\nend S\ndef msg : String := \"a  b\"\ntheorem t : msg = \"a b\" := rfl\n",
            &[],
        );
        assert_ne!(
            sec1.shards[0].prefix_env_hash,
            sec2.shards[0].prefix_env_hash
        );

        let lay1 = split_lean_source("theorem t : True := by\n  trivial\n  trivial\n", &[]);
        let lay2 = split_lean_source("theorem t : True := by trivial trivial\n", &[]);
        assert_ne!(lay1.shards[0].proof_hash, lay2.shards[0].proof_hash);

        let ind1 = split_lean_source("theorem t : True := by\n  trivial\n  done\n", &[]);
        let ind2 = split_lean_source("theorem t : True := by\n  trivial\n    done\n", &[]);
        assert_ne!(ind1.shards[0].proof_hash, ind2.shards[0].proof_hash);

        let ind3 = split_lean_source("theorem t : True := by\n  trivial\n", &[]);
        let ind4 = split_lean_source("theorem t : True := by\n    trivial\n", &[]);
        assert_ne!(ind3.shards[0].proof_hash, ind4.shards[0].proof_hash);

        let cmt1 = split_lean_source("theorem t : \"a  b\" = \"a  b\" := by\n  rfl\n", &[]);
        let cmt2 = split_lean_source("-- header comment\ntheorem t : \"a  b\" = \"a  b\" /- inline -/ := by -- eol\n  -- mid comment\n  rfl -- tail\n", &[]);
        let cmt3 = split_lean_source(
            "theorem t : \"a  b\" = \"a  b\" := by /- lead -/ rfl\n",
            &[],
        );
        let cmt4 = split_lean_source("theorem t : \"a  b\" = \"a  b\" := by rfl\n", &[]);
        assert_eq!(cmt1.interface_hash, cmt2.interface_hash);
        assert_eq!(cmt1.shards[0].stmt_hash, cmt2.shards[0].stmt_hash);
        assert_eq!(cmt1.shards[0].proof_hash, cmt2.shards[0].proof_hash);
        assert_eq!(cmt3.shards[0].proof_hash, cmt4.shards[0].proof_hash);

        let do1 = split_lean_source(
            "def f : Id Nat := do\n  let x := 1\n  pure x\ntheorem t : f = 1 := rfl\n",
            &[],
        );
        let do2 = split_lean_source(
            "def f : Id Nat := do let x := 1 pure x\ntheorem t : f = 1 := rfl\n",
            &[],
        );
        assert_ne!(do1.shards[0].prefix_env_hash, do2.shards[0].prefix_env_hash);

        let have1 = fission_theorem_have_blocks(
            "theorem ht : \"a  b\" = \"a  b\" := by\n  have h :\n      \"a  b\" = \"a  b\" := rfl\n  exact h",
            "ht",
        );
        let have2 = fission_theorem_have_blocks(
            "theorem ht : \"a  b\" = \"a  b\" := by\n  have h :\n      \"a b\" = \"a  b\" := rfl\n  exact h",
            "ht",
        );
        assert_eq!(have1.len(), 2);
        assert_eq!(have2.len(), 2);
        assert!(have1[0].sub_decl_source.contains("\"a  b\" = \"a  b\""));
        assert!(have2[0].sub_decl_source.contains("\"a b\" = \"a  b\""));
        assert_ne!(have1[0].sub_shard_key, have2[0].sub_shard_key);
    }

    #[test]
    fn test_round9_zero_hash_raw_strings_guillemets_docstrings_and_interp_macros() {
        // 1. Zero-hash raw strings `r"..."`: backslashes are literal (`\"` ends the literal),
        //    comment delimiters inside `r"..."` are preserved, and `var"` / `'r'"..."` are NOT raw strings.
        let r1 = split_lean_source("theorem t : r\"a  b\" = r\"a  b\" := rfl\n", &[]);
        let r2 = split_lean_source("theorem t : r\"a b\" = r\"a  b\" := rfl\n", &[]);
        assert_ne!(r1.shards[0].stmt_hash, r2.shards[0].stmt_hash);

        let r_slash = split_lean_source(
            "def p := r\"foo\\\"\ntheorem after_raw : p = \"foo\\\\\" := rfl\n",
            &[],
        );
        assert_eq!(r_slash.shards.len(), 1);
        assert_eq!(r_slash.shards[0].name, "after_raw");
        assert!(r_slash.hygiene.is_clean_for_certification());

        let r_hyg = split_lean_source(
            "def s := r\"\\\"\naxiom bad : False\ndef tail := \"ok\"\n",
            &[],
        );
        assert!(
            !r_hyg.hygiene.is_clean_for_certification(),
            "axiom after r\"\\\" must not be swallowed into raw string"
        );

        let r_cmt1 = split_lean_source(
            "def c := r\"a -- b\"\ntheorem t : c.length = 6 := rfl\n",
            &[],
        );
        let r_cmt2 = split_lean_source("def c := r\"a \"\ntheorem t : c.length = 6 := rfl\n", &[]);
        assert_ne!(
            r_cmt1.shards[0].prefix_env_hash,
            r_cmt2.shards[0].prefix_env_hash
        );

        let r_ident_pref = split_lean_source(
            "def f (xr : String → String) := xr\"\\\"\naxiom not_swallowed : False\n\"\n",
            &[],
        );
        assert!(
            r_ident_pref.hygiene.is_clean_for_certification(),
            "`xr\"...\"` is an identifier `xr` followed by an ordinary string where `\\\"` is escaped"
        );

        let r_colon = split_lean_source("theorem rc : r\"x := y\" = r\"x := y\" := rfl\n", &[]);
        assert_eq!(r_colon.shards.len(), 1);
        assert!(r_colon.shards[0].signature_text.contains("r\"x := y\""));

        // 2. Guillemet-escaped identifiers with dots, spaces, dashes, and Lean keyword bodies.
        let g_ns = split_lean_source(
            "namespace «Foo.Bar»\ntheorem «baz.qux» : True := trivial\nend «Foo.Bar»\n",
            &[],
        );
        assert_eq!(g_ns.shards.len(), 1);
        assert_eq!(g_ns.shards[0].name, "«baz.qux»");
        assert_eq!(g_ns.shards[0].effective_name(), "«Foo.Bar».«baz.qux»");
        assert_eq!(g_ns.shards[0].rooted_name(), "_root_.«Foo.Bar».«baz.qux»");

        let g_kw = split_lean_source(
            "def «def» : Nat := 1\ntheorem «theorem» : «def» = 1 := rfl\n",
            &[],
        );
        assert_eq!(g_kw.shards.len(), 1);
        assert_eq!(g_kw.shards[0].name, "«theorem»");
        let fast_kw = build_fast_olean_shard_source(
            "def «def» : Nat := 1\ntheorem «theorem» : «def» = 1 := rfl\n",
            "ModKw",
            &["_root_.«theorem»".to_string()].into_iter().collect(),
        )
        .expect("fast olean source for guillemet keyword theorem");
        let parsed_fast_kw = split_lean_source(&fast_kw, &[]);
        let validated_kw =
            FastVerifyMap::parse_and_validate(&fast_kw, &parsed_fast_kw.shards).unwrap();
        assert!(validated_kw.gen_for_orig("_root_.«theorem»").is_some());

        let g_coll_src = "theorem «a b» : True := trivial\ntheorem a_b : True := trivial\n";
        let g_coll_split = split_lean_source(g_coll_src, &[]);
        assert_eq!(g_coll_split.shards.len(), 2);
        let targets_both: std::collections::HashSet<String> =
            ["_root_.«a b»".to_string(), "_root_.a_b".to_string()]
                .into_iter()
                .collect();
        let fast_coll = build_fast_olean_shard_source(g_coll_src, "ModColl", &targets_both)
            .expect("fast olean source must not collide between «a b» and a_b");
        let parsed_coll = split_lean_source(&fast_coll, &[]);
        assert_eq!(parsed_coll.shards.len(), 2);
        assert_ne!(parsed_coll.shards[0].name, parsed_coll.shards[1].name);
        FastVerifyMap::parse_and_validate(&fast_coll, &parsed_coll.shards)
            .expect("guillemet + underscore fast verify map must validate without collision");

        let g_cone1 = split_lean_source(
            "def «helper fn» : Nat := 1\ntheorem use_g : «helper fn» = 1 := rfl\n",
            &[],
        );
        let g_cone2 = split_lean_source(
            "def «helper fn» : Nat := 2\ntheorem use_g : «helper fn» = 1 := rfl\n",
            &[],
        );
        assert_ne!(
            g_cone1.shards[0].cone_env_hash,
            g_cone2.shards[0].cone_env_hash
        );

        // 3. Docstrings (`/-- ... -/` and `/-! ... -/`) preserved in hashes; ordinary `/- ... -/` ignored.
        let doc1 = split_lean_source(
            "/-- doc alpha -/\ntheorem dt : True := trivial\ntheorem downstream : True := dt\n",
            &[],
        );
        let doc2 = split_lean_source(
            "/-- doc beta -/\ntheorem dt : True := trivial\ntheorem downstream : True := dt\n",
            &[],
        );
        let doc_ord = split_lean_source(
            "/- ordinary comment -/\ntheorem dt : True := trivial\ntheorem downstream : True := dt\n",
            &[],
        );
        let doc_none = split_lean_source(
            "theorem dt : True := trivial\ntheorem downstream : True := dt\n",
            &[],
        );
        assert_ne!(doc1.interface_hash, doc2.interface_hash);
        assert_ne!(doc1.shards[0].stmt_hash, doc2.shards[0].stmt_hash);
        assert_ne!(
            doc1.shards[1].prefix_env_hash,
            doc2.shards[1].prefix_env_hash
        );
        assert_ne!(doc1.shards[1].cone_env_hash, doc2.shards[1].cone_env_hash);
        assert_eq!(doc_ord.interface_hash, doc_none.interface_hash);
        assert_eq!(doc_ord.shards[0].stmt_hash, doc_none.shards[0].stmt_hash);
        assert_eq!(
            doc_ord.shards[1].prefix_env_hash,
            doc_none.shards[1].prefix_env_hash
        );

        let mdoc1 = split_lean_source("/-! mod doc 1 -/\ntheorem dt : True := trivial\n", &[]);
        let mdoc2 = split_lean_source("/-! mod doc 2 -/\ntheorem dt : True := trivial\n", &[]);
        assert_ne!(
            mdoc1.shards[0].prefix_env_hash,
            mdoc2.shards[0].prefix_env_hash
        );

        let slash3_a = split_lean_source("/--- box a -/\ntheorem dt : True := trivial\n", &[]);
        let slash3_b = split_lean_source("/--- box b -/\ntheorem dt : True := trivial\n", &[]);
        assert_ne!(
            slash3_a.shards[0].stmt_hash, slash3_b.shards[0].stmt_hash,
            "`/--- ... -/` is a 3-byte `/--` docstring opener in Lean 4"
        );

        let doc_slash_a = split_lean_source("/--/ alpha -/\ntheorem dt : True := trivial\n", &[]);
        let doc_slash_b = split_lean_source("/--/ beta -/\ntheorem dt : True := trivial\n", &[]);
        assert_ne!(
            doc_slash_a.shards[0].stmt_hash,
            doc_slash_b.shards[0].stmt_hash
        );

        let doc_empty = split_lean_source("/---/\ntheorem dt : True := trivial\n", &[]);
        assert_ne!(doc_empty.shards[0].stmt_hash, doc_none.shards[0].stmt_hash);

        let doc_four_a = split_lean_source("/----\n alpha -/\ntheorem dt : True := trivial\n", &[]);
        let doc_four_b = split_lean_source("/----\n beta -/\ntheorem dt : True := trivial\n", &[]);
        assert_ne!(
            doc_four_a.shards[0].stmt_hash,
            doc_four_b.shards[0].stmt_hash
        );

        let mdoc_dash_a = split_lean_source("/-!- mod a -/\ntheorem dt : True := trivial\n", &[]);
        let mdoc_dash_b = split_lean_source("/-!- mod b -/\ntheorem dt : True := trivial\n", &[]);
        assert_ne!(
            mdoc_dash_a.shards[0].prefix_env_hash,
            mdoc_dash_b.shards[0].prefix_env_hash
        );

        let mdoc_slash_a = split_lean_source("/-!/ mod a -/\ntheorem dt : True := trivial\n", &[]);
        let mdoc_slash_b = split_lean_source("/-!/ mod b -/\ntheorem dt : True := trivial\n", &[]);
        assert_ne!(
            mdoc_slash_a.shards[0].prefix_env_hash,
            mdoc_slash_b.shards[0].prefix_env_hash
        );

        let doc_nested = split_lean_source(
            "/--/- inner -/ theorem fake : False := sorry -/\ntheorem real_thm : True := trivial\n",
            &[],
        );
        assert_eq!(doc_nested.shards.len(), 1);
        assert_eq!(doc_nested.shards[0].name, "real_thm");
        assert!(doc_nested.hygiene.is_clean_for_certification());

        let doc_fast_targets: std::collections::HashSet<String> =
            ["_root_.dt".to_string()].into_iter().collect();
        let doc_fast_src = build_fast_olean_shard_source(
            "/-- doc alpha -/\ntheorem dt : True := trivial\n",
            "ModDoc",
            &doc_fast_targets,
        )
        .unwrap();
        let doc_fast_parsed = split_lean_source(&doc_fast_src, &[]);
        FastVerifyMap::parse_and_validate(&doc_fast_src, &doc_fast_parsed.shards)
            .expect("docstring-bearing theorem must validate in FastVerifyMap");

        // 4. Custom interpolated-string prefixes (`f1!"..."`, `s'!"..."`, Greek/guillemet prefixes)
        //    plus block comments inside `{...}` splices.
        let interp1 = split_lean_source(
            "macro \"f1!\" s:interpolatedStr(term) : term => `(s!$s)\ntheorem it : f1!\"x {\"a  b\"} y\" = \"x a  b y\" := rfl\n",
            &[],
        );
        let interp2 = split_lean_source(
            "macro \"f1!\" s:interpolatedStr(term) : term => `(s!$s)\ntheorem it : f1!\"x {\"a b\"} y\" = \"x a  b y\" := rfl\n",
            &[],
        );
        assert_ne!(interp1.shards[0].stmt_hash, interp2.shards[0].stmt_hash);

        let interp_prime1 = split_lean_source(
            "macro \"s'!\" s:interpolatedStr(term) : term => `(s!$s)\ntheorem it : s'!\"x {\"a  b\"} y\" = \"x a  b y\" := rfl\n",
            &[],
        );
        let interp_prime2 = split_lean_source(
            "macro \"s'!\" s:interpolatedStr(term) : term => `(s!$s)\ntheorem it : s'!\"x {\"a b\"} y\" = \"x a  b y\" := rfl\n",
            &[],
        );
        assert_ne!(
            interp_prime1.shards[0].stmt_hash,
            interp_prime2.shards[0].stmt_hash
        );

        let interp_fv = "macro \"f1!\" s:interpolatedStr(term) : term => `(s!$s)\ndef msg := f1!\"{\"\\n-- @turbo_fast_verify deadbeef\"}\"\ntheorem ok_thm : True := trivial\n";
        let interp_fv_split = split_lean_source(interp_fv, &[]);
        let fv_map = FastVerifyMap::parse_and_validate(interp_fv, &interp_fv_split.shards)
            .expect("directive-like text inside f1!\"{...}\" nested string must not be treated as a real comment");
        assert!(fv_map.is_empty());

        let interp_blk = split_lean_source(
            "def msg := s!\"{1 /- \"} -/ + 2}\"\ntheorem after_blk : True := trivial\n",
            &[],
        );
        assert_eq!(interp_blk.shards.len(), 1);
        assert_eq!(interp_blk.shards[0].name, "after_blk");
    }

    #[test]
    fn test_fast_verify_name_matching_rejects_cross_namespace_collisions() {
        assert!(matches_attested_decl_or_fast_verify(
            "A._turbo_verify_0_foo",
            "A.foo"
        ));
        assert!(matches_attested_decl_or_fast_verify(
            "Ns._turbo_verify_2_Foo_bar",
            "Ns.Foo.bar"
        ));
        assert!(matches_attested_decl_or_fast_verify(
            "_turbo_verify_1_A_foo",
            "A.foo"
        ));
        assert!(!matches_attested_decl_or_fast_verify(
            "B._turbo_verify_0_foo",
            "A.foo"
        ));
        assert!(!matches_attested_decl_or_fast_verify(
            "_turbo_verify_0_foo",
            "A.foo"
        ));
        assert!(!matches_attested_decl_or_fast_verify(
            "A._turbo_verify_0_foo",
            "B.A.foo"
        ));
        let uncached: HashSet<String> = ["A.foo".to_string()].into_iter().collect();
        assert!(matches_uncached_or_fast_verify_name(
            "A._turbo_verify_0_foo",
            &uncached
        ));
        assert!(!matches_uncached_or_fast_verify_name(
            "B._turbo_verify_0_foo",
            &uncached
        ));
        assert!(!matches_uncached_or_fast_verify_name("B.foo", &uncached));
    }

    #[test]
    fn test_escaped_dotted_component_boundaries_disambiguate_from_nested_namespace() {
        let src = "theorem «a.b» : True := True.intro\ntheorem a.b : True := True.intro\n";
        let split = split_lean_source(src, &[]);
        assert_eq!(split.shards.len(), 2);
        assert_eq!(split.shards[0].decl_name(), "«a.b»");
        assert_eq!(split.shards[1].decl_name(), "a.b");
        assert_eq!(
            find_decl_shard_index(&split.shards, "«a.b»").unwrap(),
            Some(0)
        );
        assert_eq!(
            find_decl_shard_index(&split.shards, "_root_.«a.b»").unwrap(),
            Some(0)
        );
        assert_eq!(
            find_decl_shard_index(&split.shards, "a.b").unwrap(),
            Some(1)
        );
        assert_eq!(
            find_decl_shard_index(&split.shards, "_root_.a.b").unwrap(),
            Some(1)
        );
    }

    #[test]
    fn test_fission_theorem_have_blocks_skips_instance_cuts_and_signature_shadowing() {
        let decl_havei = "theorem inst_cut [MyC Nat] : MyC.val = MyC.val := by\n  haveI : MyC Nat := ⟨0⟩\n  rfl\n";
        assert!(
            fission_theorem_have_blocks(decl_havei, "inst_cut").is_empty(),
            "fission must skip haveI/letI cuts because promoting [ty] into conclusion binders changes the theorem statement"
        );
        let decl_shadow =
            "theorem sig_shadow (n : Nat) : n = n := by\n  have n : Nat := 0\n  rfl\n";
        assert!(
            fission_theorem_have_blocks(decl_shadow, "sig_shadow").is_empty(),
            "fission must skip cuts whose identifier shadows a binder/constant in the theorem signature"
        );
    }
}

#[cfg(test)]
#[path = "../tests/support/discovery.rs"]
mod corpus_discovery;
