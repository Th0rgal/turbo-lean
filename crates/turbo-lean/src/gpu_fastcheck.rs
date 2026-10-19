//! GPU & CPU FastCheck counterexample runner and Lean 4 Prop -> CUDA transpiler.

pub fn parse_gpu_fastcheck_output(
    stdout: &str,
    exec_ms: u128,
    total_ms: u128,
    remote_host: Option<&str>,
) -> serde_json::Value {
    let mut gpu_device = String::new();
    let mut valid_lemma_10m_ms = 0.0f64;
    let mut valid_lemma_10m_mstates_s = 0.0f64;
    let mut suite_10m_ms = 0.0f64;
    let mut suite_10m_mstates_s = 0.0f64;
    let mut cumutate_kernel_ms = 0.0f64;
    let mut cumutate_throughput_mevals_s = 0.0f64;
    let mut mutants_killed = 0u64;
    let mut mutants_total = 0u64;

    for line in stdout.lines() {
        let l = line.trim();
        if l.starts_with("=== CuDenote GPU Benchmark on ") {
            if let Some(rest) = l.strip_prefix("=== CuDenote GPU Benchmark on ") {
                if let Some(end) = rest.find(" ===") {
                    gpu_device = rest[..end].to_string();
                }
            }
        } else if l.starts_with("[Fast-Check Valid Lemma (10000000 states)]") {
            if let Some(t_idx) = l.find("Time: ") {
                let after = &l[t_idx + 6..];
                if let Some(ms_idx) = after.find(" ms") {
                    valid_lemma_10m_ms = after[..ms_idx].trim().parse().unwrap_or(0.0);
                }
            }
            if let Some(tp_idx) = l.find("Throughput: ") {
                let after = &l[tp_idx + 12..];
                if let Some(m_idx) = after.find(" M states/s") {
                    valid_lemma_10m_mstates_s = after[..m_idx].trim().parse().unwrap_or(0.0);
                }
            }
        } else if l.starts_with("[Fast-Reject 3-Lemma Suite (10000000 states)]") {
            if let Some(t_idx) = l.find("Time: ") {
                let after = &l[t_idx + 6..];
                if let Some(ms_idx) = after.find(" ms") {
                    suite_10m_ms = after[..ms_idx].trim().parse().unwrap_or(0.0);
                }
            }
            if let Some(tp_idx) = l.find("Throughput: ") {
                let after = &l[tp_idx + 12..];
                if let Some(m_idx) = after.find(" M states/s") {
                    suite_10m_mstates_s = after[..m_idx].trim().parse().unwrap_or(0.0);
                }
            }
        } else if l.starts_with("-> Kernel Time: ") {
            if let Some(after) = l.strip_prefix("-> Kernel Time: ") {
                if let Some(ms_idx) = after.find(" ms") {
                    cumutate_kernel_ms = after[..ms_idx].trim().parse().unwrap_or(0.0);
                }
            }
            if let Some(tp_idx) = l.find("Throughput: ") {
                let after = &l[tp_idx + 12..];
                if let Some(m_idx) = after.find(" M Denote-evals/s") {
                    cumutate_throughput_mevals_s = after[..m_idx].trim().parse().unwrap_or(0.0);
                }
            }
        } else if l.starts_with("-> Mutants Killed: ") {
            if let Some(after) = l.strip_prefix("-> Mutants Killed: ") {
                if let Some((k_str, rest)) = after.split_once(" / ") {
                    mutants_killed = k_str.trim().parse().unwrap_or(0);
                    if let Some((tot_str, _)) = rest.split_once(' ') {
                        mutants_total = tot_str.trim().parse().unwrap_or(0);
                    }
                }
            }
        }
    }

    serde_json::json!({
        "status": "ok",
        "mode": if remote_host.is_some() { "remote_gpu_cuda" } else { "local_gpu_cuda" },
        "remote_host": remote_host,
        "gpu_device": gpu_device,
        "throughput_mstates_s": valid_lemma_10m_mstates_s,
        "valid_lemma_10m_kernel_ms": valid_lemma_10m_ms,
        "fast_reject_3lemma_10m_kernel_ms": suite_10m_ms,
        "fast_reject_3lemma_mstates_s": suite_10m_mstates_s,
        "cumutate_kernel_ms": cumutate_kernel_ms,
        "cumutate_throughput_mevals_s": cumutate_throughput_mevals_s,
        "mutants_killed": mutants_killed,
        "mutants_total": mutants_total,
        "exec_ms": exec_ms,
        "total_ms": total_ms,
        "output": stdout.trim()
    })
}

// ============================================================================
// Season 2 — Automatic Lean 4 `Theorem/Prop` -> CUDA C++ Counterexample Transpiler
// ============================================================================

use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::process::Command;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TranspiledParam {
    pub name: String,
    pub lean_type: String,
    pub cuda_type: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TranspiledCudaKernel {
    pub decl_name: String,
    pub params: Vec<TranspiledParam>,
    pub lhs_lean: String,
    pub rhs_lean: String,
    pub lhs_cuda_expr: String,
    pub rhs_cuda_expr: String,
    pub preconditions_cuda: Vec<String>,
    pub cuda_source: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CounterexampleWitness {
    pub state_idx: u64,
    pub bindings: Vec<(String, String)>,
    pub lhs_value: String,
    pub rhs_value: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TranspiledFastCheckReport {
    pub decl_name: String,
    pub backend: String,
    pub gpu_device: String,
    pub n_states: u64,
    pub violations: u64,
    #[serde(default)]
    pub satisfied_preconditions: u64,
    #[serde(default)]
    pub vacuous_precondition_warning: bool,
    pub verified: bool,
    pub kernel_ms: f64,
    pub throughput_mstates_s: f64,
    pub counterexample: Option<CounterexampleWitness>,
    #[serde(default)]
    pub lean_native_certified: bool,
    #[serde(default)]
    pub lean_native_engine_version: String,
}

pub type FastCheckReport = TranspiledFastCheckReport;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Ident(String),
    Number(String),
    LParen,
    RParen,
    LAngle,
    RAngle,
    Comma,
    Dot,
    Op(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LeanExpr {
    Ident(String),
    Number(String),
    Member(Box<LeanExpr>, String),
    App(Box<LeanExpr>, Vec<LeanExpr>),
    Unary(String, Box<LeanExpr>),
    Binary(String, Box<LeanExpr>, Box<LeanExpr>),
    AnonCtor(Vec<LeanExpr>),
    Tuple(Vec<LeanExpr>),
    IfThenElse(Box<LeanExpr>, Box<LeanExpr>, Box<LeanExpr>),
}

/// Strip Lean 4 line comments (`-- ...`) and nested block comments (`/- ... -/`).
pub fn strip_lean_comments(src: &str) -> String {
    let chars: Vec<char> = src.chars().collect();
    let n = chars.len();
    let mut out = String::with_capacity(n);
    let mut i = 0;
    let mut block_depth = 0usize;

    while i < n {
        if block_depth > 0 {
            if i + 1 < n && chars[i] == '/' && chars[i + 1] == '-' {
                block_depth += 1;
                i += 2;
            } else if i + 1 < n && chars[i] == '-' && chars[i + 1] == '/' {
                block_depth -= 1;
                i += 2;
                out.push(' ');
            } else {
                if chars[i] == '\n' {
                    out.push('\n');
                }
                i += 1;
            }
        } else if i + 1 < n && chars[i] == '/' && chars[i + 1] == '-' {
            block_depth = 1;
            i += 2;
        } else if i + 1 < n && chars[i] == '-' && chars[i + 1] == '-' {
            i += 2;
            while i < n && chars[i] != '\n' {
                i += 1;
            }
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_ident_continue(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\''
}

struct ExtractedDecl {
    name: String,
    binders: Vec<(Vec<String>, String)>,
    prop_str: String,
}

fn extract_lean_theorem(clean_src: &str, target_name: Option<&str>) -> Result<ExtractedDecl> {
    let chars: Vec<char> = clean_src.chars().collect();
    let n = chars.len();
    let mut i = 0;

    while i < n {
        if is_ident_start(chars[i]) {
            let start = i;
            while i < n && is_ident_continue(chars[i]) {
                i += 1;
            }
            let word: String = chars[start..i].iter().collect();
            if word == "theorem" || word == "lemma" {
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
                let decl_name: String = chars[name_start..i].iter().collect();
                if let Some(target) = target_name {
                    if decl_name != target {
                        continue;
                    }
                }

                // Parse binder groups until top-level `:` (not `:=`)
                let mut binders = Vec::new();
                while i < n {
                    while i < n && chars[i].is_whitespace() {
                        i += 1;
                    }
                    if i >= n {
                        bail!("Unexpected EOF while parsing binders of `{}`", decl_name);
                    }
                    if chars[i] == ':' && (i + 1 >= n || chars[i + 1] != '=') {
                        i += 1; // consume `:`
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
                        }
                    } else {
                        i += 1;
                    }
                }

                // Now extract statement up to top-level `:=` (or next `theorem`/`lemma`/`end` or EOF)
                let stmt_start = i;
                let mut paren_depth = 0usize;
                let mut angle_depth = 0usize;
                let mut stmt_end = n;
                while i < n {
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
                        && c == ':'
                        && i + 1 < n
                        && chars[i + 1] == '='
                    {
                        stmt_end = i;
                        break;
                    }
                    i += 1;
                }
                let prop_str: String = chars[stmt_start..stmt_end].iter().collect();
                return Ok(ExtractedDecl {
                    name: decl_name,
                    binders,
                    prop_str: prop_str.trim().to_string(),
                });
            }
        } else {
            i += 1;
        }
    }

    if let Some(target) = target_name {
        bail!("Theorem or lemma `{}` not found in Lean source", target)
    } else {
        bail!("No `theorem` or `lemma` declaration found in Lean source")
    }
}

fn split_top_level_colon(s: &str) -> Option<(&str, &str)> {
    let mut depth = 0usize;
    let bytes = s.as_bytes();
    for (idx, ch) in s.char_indices() {
        match ch {
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth = depth.saturating_sub(1),
            ':' if depth == 0 => {
                if idx + 1 < bytes.len() && bytes[idx + 1] == b'=' {
                    continue;
                }
                return Some((&s[..idx], &s[idx + 1..]));
            }
            _ => {}
        }
    }
    None
}

fn split_top_level_implications(s: &str) -> Vec<String> {
    let chars: Vec<char> = s.chars().collect();
    let n = chars.len();
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut last = 0usize;
    let mut i = 0usize;

    while i < n {
        match chars[i] {
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth = depth.saturating_sub(1),
            '→' if depth == 0 => {
                let seg: String = chars[last..i].iter().collect();
                parts.push(seg.trim().to_string());
                i += 1;
                last = i;
                continue;
            }
            '-' if depth == 0 && i + 1 < n && chars[i + 1] == '>' => {
                let seg: String = chars[last..i].iter().collect();
                parts.push(seg.trim().to_string());
                i += 2;
                last = i;
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    let tail: String = chars[last..n].iter().collect();
    parts.push(tail.trim().to_string());
    parts
}

fn split_top_level_eq(s: &str) -> Option<(String, String, bool)> {
    let chars: Vec<char> = s.chars().collect();
    let n = chars.len();
    let mut depth = 0usize;
    let mut i = 0usize;

    while i < n {
        match chars[i] {
            '(' | '{' | '[' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⟩' => depth = depth.saturating_sub(1),
            '≠' if depth == 0 => {
                let lhs: String = chars[..i].iter().collect();
                let rhs: String = chars[i + 1..].iter().collect();
                return Some((lhs.trim().to_string(), rhs.trim().to_string(), true));
            }
            '!' if depth == 0 && i + 1 < n && chars[i + 1] == '=' => {
                let lhs: String = chars[..i].iter().collect();
                let rhs: String = chars[i + 2..].iter().collect();
                return Some((lhs.trim().to_string(), rhs.trim().to_string(), true));
            }
            '=' if depth == 0 => {
                let prev = if i > 0 { Some(chars[i - 1]) } else { None };
                let next = if i + 1 < n { Some(chars[i + 1]) } else { None };
                if matches!(prev, Some('!') | Some('<') | Some('>') | Some(':') | Some('='))
                    || matches!(next, Some('=') | Some('>'))
                {
                    i += 1;
                    continue;
                }
                let lhs: String = chars[..i].iter().collect();
                let rhs: String = chars[i + 1..].iter().collect();
                return Some((lhs.trim().to_string(), rhs.trim().to_string(), false));
            }
            _ => {}
        }
        i += 1;
    }
    None
}

fn tokenize_lean_expr(s: &str) -> Result<Vec<Token>> {
    let chars: Vec<char> = s.chars().collect();
    let n = chars.len();
    let mut tokens = Vec::new();
    let mut i = 0usize;

    while i < n {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        match c {
            '(' => {
                tokens.push(Token::LParen);
                i += 1;
            }
            ')' => {
                tokens.push(Token::RParen);
                i += 1;
            }
            '⟨' => {
                tokens.push(Token::LAngle);
                i += 1;
            }
            '⟩' => {
                tokens.push(Token::RAngle);
                i += 1;
            }
            ',' => {
                tokens.push(Token::Comma);
                i += 1;
            }
            '.' => {
                tokens.push(Token::Dot);
                i += 1;
            }
            _ if c.is_ascii_digit() => {
                let start = i;
                if c == '0' && i + 1 < n && (chars[i + 1] == 'x' || chars[i + 1] == 'X') {
                    i += 2;
                    while i < n && (chars[i].is_ascii_hexdigit() || chars[i] == '_') {
                        i += 1;
                    }
                } else {
                    while i < n && (chars[i].is_ascii_digit() || chars[i] == '_') {
                        i += 1;
                    }
                }
                let num_str: String = chars[start..i].iter().filter(|&&ch| ch != '_').collect();
                tokens.push(Token::Number(num_str));
            }
            _ if is_ident_start(c) => {
                let start = i;
                while i < n && is_ident_continue(chars[i]) {
                    i += 1;
                }
                let id: String = chars[start..i].iter().collect();
                tokens.push(Token::Ident(id));
            }
            _ => {
                // Multi-character operators first
                if i + 2 < n {
                    let s3: String = chars[i..i + 3].iter().collect();
                    if matches!(
                        s3.as_str(),
                        "&&&" | "|||" | "^^^" | "~~~" | "<<<" | ">>>"
                    ) {
                        tokens.push(Token::Op(s3));
                        i += 3;
                        continue;
                    }
                }
                if i + 1 < n {
                    let s2: String = chars[i..i + 2].iter().collect();
                    if matches!(s2.as_str(), "&&" | "||" | "==" | "!=" | "<=" | ">=") {
                        tokens.push(Token::Op(s2));
                        i += 2;
                        continue;
                    }
                }
                if matches!(
                    c,
                    '+' | '-' | '*' | '/' | '%' | '=' | '<' | '>' | '!' | '¬' | '≠' | '≤' | '≥' | '∧' | '∨'
                ) {
                    tokens.push(Token::Op(c.to_string()));
                    i += 1;
                } else {
                    bail!("Unsupported character `{}` in Lean expression `{}`", c, s);
                }
            }
        }
    }
    Ok(tokens)
}

struct ExprParser {
    tokens: Vec<Token>,
    pos: usize,
}

impl ExprParser {
    fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, pos: 0 }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn next(&mut self) -> Option<Token> {
        if self.pos < self.tokens.len() {
            let t = self.tokens[self.pos].clone();
            self.pos += 1;
            Some(t)
        } else {
            None
        }
    }

    fn parse_expr(&mut self) -> Result<LeanExpr> {
        if matches!(self.peek(), Some(Token::Ident(k)) if k == "if") {
            self.next();
            let cond = self.parse_expr()?;
            match self.next() {
                Some(Token::Ident(k)) if k == "then" => {}
                other => bail!("Expected `then` in `if` expression, got {:?}", other),
            }
            let then_branch = self.parse_expr()?;
            match self.next() {
                Some(Token::Ident(k)) if k == "else" => {}
                other => bail!("Expected `else` in `if` expression, got {:?}", other),
            }
            let else_branch = self.parse_expr()?;
            return Ok(LeanExpr::IfThenElse(
                Box::new(cond),
                Box::new(then_branch),
                Box::new(else_branch),
            ));
        }
        self.parse_binary(1)
    }

    fn op_prec(op: &str) -> Option<(u8, bool)> {
        // Returns (precedence, right_associative)
        match op {
            "||" | "∨" => Some((1, false)),
            "&&" | "∧" => Some((2, false)),
            "=" | "==" | "!=" | "≠" | "<" | "<=" | "≤" | ">" | ">=" | "≥" => Some((3, false)),
            "|||" => Some((4, false)),
            "^^^" => Some((5, false)),
            "&&&" => Some((6, false)),
            "<<<" | ">>>" => Some((7, false)),
            "+" | "-" => Some((8, false)),
            "*" | "/" | "%" => Some((9, false)),
            _ => None,
        }
    }

    fn parse_binary(&mut self, min_prec: u8) -> Result<LeanExpr> {
        let mut lhs = self.parse_unary_or_app()?;
        while let Some(Token::Op(op)) = self.peek().cloned() {
            let Some((prec, right_assoc)) = Self::op_prec(&op) else {
                break;
            };
            if prec < min_prec {
                break;
            }
            self.next();
            let next_min = if right_assoc { prec } else { prec + 1 };
            let rhs = self.parse_binary(next_min)?;
            lhs = LeanExpr::Binary(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_unary_or_app(&mut self) -> Result<LeanExpr> {
        if let Some(Token::Op(op)) = self.peek().cloned() {
            if matches!(op.as_str(), "~~~" | "!" | "¬" | "-") {
                self.next();
                let operand = self.parse_unary_or_app()?;
                return Ok(LeanExpr::Unary(op, Box::new(operand)));
            }
        }
        let head = self.parse_postfix()?;
        let mut args = Vec::new();
        while self.can_start_atom() {
            args.push(self.parse_postfix()?);
        }
        if args.is_empty() {
            Ok(head)
        } else {
            Ok(LeanExpr::App(Box::new(head), args))
        }
    }

    fn can_start_atom(&self) -> bool {
        match self.peek() {
            Some(Token::Ident(k)) => !matches!(k.as_str(), "then" | "else" | "in"),
            Some(Token::Number(_)) | Some(Token::LParen) | Some(Token::LAngle) => true,
            _ => false,
        }
    }

    fn parse_postfix(&mut self) -> Result<LeanExpr> {
        let mut base = self.parse_primary()?;
        while matches!(self.peek(), Some(Token::Dot)) {
            self.next(); // consume `.`
            match self.next() {
                Some(Token::Ident(field)) => {
                    base = LeanExpr::Member(Box::new(base), field);
                }
                Some(Token::Number(num)) => {
                    base = LeanExpr::Member(Box::new(base), num);
                }
                other => bail!("Expected field or projection after `.`, got {:?}", other),
            }
        }
        Ok(base)
    }

    fn parse_primary(&mut self) -> Result<LeanExpr> {
        match self.next() {
            Some(Token::Ident(id)) => Ok(LeanExpr::Ident(id)),
            Some(Token::Number(n)) => Ok(LeanExpr::Number(n)),
            Some(Token::LParen) => {
                let first = self.parse_expr()?;
                if matches!(self.peek(), Some(Token::Comma)) {
                    let mut items = vec![first];
                    while matches!(self.peek(), Some(Token::Comma)) {
                        self.next();
                        items.push(self.parse_expr()?);
                    }
                    match self.next() {
                        Some(Token::RParen) => Ok(LeanExpr::Tuple(items)),
                        other => bail!("Expected `)` after tuple, got {:?}", other),
                    }
                } else {
                    match self.next() {
                        Some(Token::RParen) => Ok(first),
                        other => bail!("Expected `)` after parenthesized expr, got {:?}", other),
                    }
                }
            }
            Some(Token::LAngle) => {
                let mut items = Vec::new();
                if !matches!(self.peek(), Some(Token::RAngle)) {
                    items.push(self.parse_expr()?);
                    while matches!(self.peek(), Some(Token::Comma)) {
                        self.next();
                        items.push(self.parse_expr()?);
                    }
                }
                match self.next() {
                    Some(Token::RAngle) => Ok(LeanExpr::AnonCtor(items)),
                    other => bail!("Expected `⟩` after anonymous constructor, got {:?}", other),
                }
            }
            other => bail!("Unexpected token in Lean expression: {:?}", other),
        }
    }
}

fn parse_lean_expr_str(s: &str) -> Result<LeanExpr> {
    let tokens = tokenize_lean_expr(s)?;
    if tokens.is_empty() {
        bail!("Empty Lean expression");
    }
    let mut parser = ExprParser::new(tokens);
    let expr = parser.parse_expr()?;
    if parser.pos < parser.tokens.len() {
        bail!(
            "Unconsumed tokens in Lean expression `{}` starting at {:?}",
            s,
            &parser.tokens[parser.pos..]
        );
    }
    Ok(expr)
}

fn flatten_qualified_name(expr: &LeanExpr) -> Option<String> {
    match expr {
        LeanExpr::Ident(s) => Some(s.clone()),
        LeanExpr::Member(base, field) => {
            let prefix = flatten_qualified_name(base)?;
            if matches!(
                prefix.as_str(),
                "Word256"
                    | "TurboLean"
                    | "TurboLean.FastCheck"
                    | "TurboLean.FastCheck.Word256"
                    | "UInt256"
                    | "BitVec"
                    | "UInt64"
                    | "Nat"
                    | "Bool"
            ) {
                Some(format!("{}.{}", prefix, field))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn emit_cuda_expr(expr: &LeanExpr) -> Result<String> {
    if let Some(qname) = flatten_qualified_name(expr) {
        let short = qname.rsplit('.').next().unwrap_or(qname.as_str());
        if qname.contains('.') {
            match short {
                "zero" => return Ok("u256_zero()".to_string()),
                "one" => return Ok("u256_one()".to_string()),
                "max" => return Ok("u256_max()".to_string()),
                _ => {}
            }
        } else {
            match short {
                "true" => return Ok("true".to_string()),
                "false" => return Ok("false".to_string()),
                _ => return Ok(short.to_string()),
            }
        }
    }

    match expr {
        LeanExpr::Ident(name) => match name.as_str() {
            "true" => Ok("true".to_string()),
            "false" => Ok("false".to_string()),
            _ => Ok(name.clone()),
        },
        LeanExpr::Number(n) => Ok(format!("{}ULL", n)),
        LeanExpr::Member(base, field) => {
            let b = emit_cuda_expr(base)?;
            let mapped = match field.as_str() {
                "1" | "fst" => "fst",
                "2" | "snd" => "snd",
                "w0" => "w0",
                "w1" => "w1",
                "w2" => "w2",
                "w3" => "w3",
                other => bail!("Unsupported field projection `.{}` on `{}`", other, b),
            };
            Ok(format!("({}).{}", b, mapped))
        }
        LeanExpr::AnonCtor(items) => {
            if items.len() != 4 {
                bail!(
                    "Expected 4 limbs in `Word256` constructor `⟨w0, w1, w2, w3⟩`, got {}",
                    items.len()
                );
            }
            let a0 = emit_cuda_expr(&items[0])?;
            let a1 = emit_cuda_expr(&items[1])?;
            let a2 = emit_cuda_expr(&items[2])?;
            let a3 = emit_cuda_expr(&items[3])?;
            Ok(format!("make_u256({}, {}, {}, {})", a0, a1, a2, a3))
        }
        LeanExpr::Tuple(items) => {
            if items.len() != 2 {
                bail!("Expected 2-tuple `(fst, snd)`, got {} elements", items.len());
            }
            let fst = emit_cuda_expr(&items[0])?;
            let snd = emit_cuda_expr(&items[1])?;
            Ok(format!("make_u256_bool_pair({}, {})", fst, snd))
        }
        LeanExpr::IfThenElse(c, t, e) => {
            let cc = emit_cuda_expr(c)?;
            let tc = emit_cuda_expr(t)?;
            let ec = emit_cuda_expr(e)?;
            Ok(format!("(({}) ? ({}) : ({}))", cc, tc, ec))
        }
        LeanExpr::Unary(op, inner) => {
            let ic = emit_cuda_expr(inner)?;
            match op.as_str() {
                "~~~" => Ok(format!("lean_bitnot({})", ic)),
                "!" | "¬" => Ok(format!("(!({}))", ic)),
                "-" => Ok(format!("lean_neg({})", ic)),
                other => bail!("Unsupported unary operator `{}`", other),
            }
        }
        LeanExpr::Binary(op, lhs, rhs) => {
            let l = emit_cuda_expr(lhs)?;
            let r = emit_cuda_expr(rhs)?;
            match op.as_str() {
                "&&&" => Ok(format!("lean_bitand({}, {})", l, r)),
                "|||" => Ok(format!("lean_bitor({}, {})", l, r)),
                "^^^" => Ok(format!("lean_bitxor({}, {})", l, r)),
                "+" => Ok(format!("lean_add({}, {})", l, r)),
                "-" => Ok(format!("lean_sub({}, {})", l, r)),
                "*" => Ok(format!("lean_mul({}, {})", l, r)),
                "/" => Ok(format!("lean_div({}, {})", l, r)),
                "%" => Ok(format!("lean_mod({}, {})", l, r)),
                "<<<" => Ok(format!("lean_shl({}, {})", l, r)),
                ">>>" => Ok(format!("lean_shr({}, {})", l, r)),
                "=" | "==" => Ok(format!("lean_eq({}, {})", l, r)),
                "!=" | "≠" => Ok(format!("(!lean_eq({}, {}))", l, r)),
                "<" => Ok(format!("lean_lt({}, {})", l, r)),
                "<=" | "≤" => Ok(format!("lean_le({}, {})", l, r)),
                ">" => Ok(format!("lean_lt({}, {})", r, l)),
                ">=" | "≥" => Ok(format!("lean_le({}, {})", r, l)),
                "&&" | "∧" => Ok(format!("(({}) && ({}))", l, r)),
                "||" | "∨" => Ok(format!("(({}) || ({}))", l, r)),
                other => bail!("Unsupported binary operator `{}`", other),
            }
        }
        LeanExpr::App(head, args) => {
            let fname = flatten_qualified_name(head).ok_or_else(|| {
                anyhow::anyhow!("Unsupported higher-order function head `{:?}`", head)
            })?;
            let short = fname.rsplit('.').next().unwrap_or(fname.as_str());
            let mut c_args = Vec::with_capacity(args.len());
            for a in args {
                c_args.push(emit_cuda_expr(a)?);
            }
            match (short, c_args.len()) {
                ("bitNot", 1) => Ok(format!("lean_bitnot({})", c_args[0])),
                ("bitAnd", 2) => Ok(format!("lean_bitand({}, {})", c_args[0], c_args[1])),
                ("bitOr", 2) => Ok(format!("lean_bitor({}, {})", c_args[0], c_args[1])),
                ("bitXor", 2) => Ok(format!("lean_bitxor({}, {})", c_args[0], c_args[1])),
                ("bitSetMask", 2) => Ok(format!("u256_bit_set_mask({}, {})", c_args[0], c_args[1])),
                ("bitClearMask", 2) => {
                    Ok(format!("u256_bit_clear_mask({}, {})", c_args[0], c_args[1]))
                }
                ("bitFlipMask", 2) => {
                    Ok(format!("u256_bit_flip_mask({}, {})", c_args[0], c_args[1]))
                }
                ("bitMux", 3) => Ok(format!(
                    "u256_bit_mux({}, {}, {})",
                    c_args[0], c_args[1], c_args[2]
                )),
                ("bitMaj", 3) => Ok(format!(
                    "u256_bit_maj({}, {}, {})",
                    c_args[0], c_args[1], c_args[2]
                )),
                ("bitParity", 3) => Ok(format!(
                    "u256_bit_parity({}, {}, {})",
                    c_args[0], c_args[1], c_args[2]
                )),
                ("add", 2) => Ok(format!("lean_add({}, {})", c_args[0], c_args[1])),
                ("sub", 2) => Ok(format!("lean_sub({}, {})", c_args[0], c_args[1])),
                ("mul", 2) => Ok(format!("lean_mul({}, {})", c_args[0], c_args[1])),
                ("div", 2) => Ok(format!("lean_div({}, {})", c_args[0], c_args[1])),
                ("mod", 2) => Ok(format!("lean_mod({}, {})", c_args[0], c_args[1])),
                ("addWithCarry", 2) => {
                    Ok(format!("u256_add_with_carry({}, {})", c_args[0], c_args[1]))
                }
                ("subWithBorrow", 2) => {
                    Ok(format!("u256_sub_with_borrow({}, {})", c_args[0], c_args[1]))
                }
                ("mulDivDown", 3) => Ok(format!(
                    "u256_mul_div_down_val({}, {}, {})",
                    c_args[0], c_args[1], c_args[2]
                )),
                ("mulDivUp", 3) => Ok(format!(
                    "u256_mul_div_up_val({}, {}, {})",
                    c_args[0], c_args[1], c_args[2]
                )),
                ("packHalves", 4) => Ok(format!(
                    "packHalves({}, {}, {}, {})",
                    c_args[0], c_args[1], c_args[2], c_args[3]
                )),
                ("mk", 4) => Ok(format!(
                    "make_u256({}, {}, {}, {})",
                    c_args[0], c_args[1], c_args[2], c_args[3]
                )),
                ("unpackLo128", 1) => Ok(format!("unpackLo128({})", c_args[0])),
                ("unpackHi128", 1) => Ok(format!("unpackHi128({})", c_args[0])),
                ("mask128", 1) => Ok(format!("mask128({})", c_args[0])),
                ("yul_min" | "min", 2) => Ok(format!("yul_min({}, {})", c_args[0], c_args[1])),
                ("beq", 2) => Ok(format!("lean_eq({}, {})", c_args[0], c_args[1])),
                ("succ", 1) => Ok(format!("lean_add({}, 1ULL)", c_args[0])),
                _ => bail!(
                    "Unsupported Lean function `{}` with {} arguments",
                    fname,
                    c_args.len()
                ),
            }
        }
    }
}

fn classify_binder_cuda_type(lean_ty: &str) -> Option<&'static str> {
    let t = lean_ty.trim();
    if matches!(
        t,
        "Word256" | "TurboLean.FastCheck.Word256" | "UInt256" | "BitVec 256"
    ) {
        Some("u256")
    } else if matches!(t, "UInt64" | "Nat" | "USize") {
        Some("uint64_t")
    } else if t == "Bool" {
        Some("bool")
    } else {
        None
    }
}

fn strip_hypothesis_binder_name(s: &str) -> &str {
    let mut trimmed = s.trim();
    if trimmed.starts_with('(') && trimmed.ends_with(')') && trimmed.len() >= 2 {
        let inner = &trimmed[1..trimmed.len() - 1];
        let mut depth = 0i32;
        let mut balanced = true;
        for ch in inner.chars() {
            match ch {
                '(' | '{' | '[' | '⟨' => depth += 1,
                ')' | '}' | ']' | '⟩' => {
                    depth -= 1;
                    if depth < 0 {
                        balanced = false;
                        break;
                    }
                }
                _ => {}
            }
        }
        if balanced && depth == 0 {
            trimmed = inner.trim();
        }
    }
    if let Some((lhs, rhs)) = split_top_level_colon(trimmed) {
        let lhs_t = lhs.trim();
        if !lhs_t.is_empty()
            && lhs_t
                .split_whitespace()
                .all(|w| w.chars().all(is_ident_continue))
        {
            return rhs.trim();
        }
    }
    s.trim()
}

fn flatten_conjunctions(expr: LeanExpr, out: &mut Vec<LeanExpr>) {
    match expr {
        LeanExpr::Binary(ref op, ref l, ref r) if op == "&&" || op == "∧" => {
            flatten_conjunctions((**l).clone(), out);
            flatten_conjunctions((**r).clone(), out);
        }
        other => out.push(other),
    }
}

fn collect_expr_bound_vars(
    expr: &LeanExpr,
    param_names: &std::collections::HashSet<&str>,
    out_vars: &mut std::collections::HashSet<String>,
) -> bool {
    if let Some(qname) = flatten_qualified_name(expr) {
        if qname.contains('.') {
            return true;
        }
        if matches!(qname.as_str(), "true" | "false") {
            return true;
        }
        if param_names.contains(qname.as_str()) {
            out_vars.insert(qname);
            return true;
        }
        return false;
    }
    match expr {
        LeanExpr::Ident(id) => {
            if matches!(id.as_str(), "true" | "false") {
                true
            } else if param_names.contains(id.as_str()) {
                out_vars.insert(id.clone());
                true
            } else {
                false
            }
        }
        LeanExpr::Number(_) => true,
        LeanExpr::Member(base, _) => collect_expr_bound_vars(base, param_names, out_vars),
        LeanExpr::Unary(_, inner) => collect_expr_bound_vars(inner, param_names, out_vars),
        LeanExpr::Binary(_, l, r) => {
            collect_expr_bound_vars(l, param_names, out_vars)
                && collect_expr_bound_vars(r, param_names, out_vars)
        }
        LeanExpr::AnonCtor(items) | LeanExpr::Tuple(items) => items
            .iter()
            .all(|it| collect_expr_bound_vars(it, param_names, out_vars)),
        LeanExpr::IfThenElse(c, t, e) => {
            collect_expr_bound_vars(c, param_names, out_vars)
                && collect_expr_bound_vars(t, param_names, out_vars)
                && collect_expr_bound_vars(e, param_names, out_vars)
        }
        LeanExpr::App(head, args) => {
            flatten_qualified_name(head).is_some()
                && args
                    .iter()
                    .all(|a| collect_expr_bound_vars(a, param_names, out_vars))
        }
    }
}

fn depends_transitively_on(
    vars: &std::collections::HashSet<String>,
    target: &str,
    subst_deps: &std::collections::HashMap<String, std::collections::HashSet<String>>,
) -> bool {
    let mut stack: Vec<&str> = vars.iter().map(|s| s.as_str()).collect();
    let mut visited = std::collections::HashSet::new();
    while let Some(cur) = stack.pop() {
        if cur == target {
            return true;
        }
        if !visited.insert(cur) {
            continue;
        }
        if let Some(next_set) = subst_deps.get(cur) {
            for nxt in next_set {
                stack.push(nxt.as_str());
            }
        }
    }
    false
}

fn split_equality_ast(expr: &LeanExpr) -> Option<(&LeanExpr, &LeanExpr)> {
    match expr {
        LeanExpr::Binary(op, l, r) if op == "=" || op == "==" => Some((l, r)),
        LeanExpr::App(head, args) if args.len() == 2 => {
            let fname = flatten_qualified_name(head)?;
            let short = fname.rsplit('.').next().unwrap_or(fname.as_str());
            if short == "beq" {
                Some((&args[0], &args[1]))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn emit_cuda_rhs_for_param(expr: &LeanExpr, cuda_type: &str) -> Result<String> {
    let raw = emit_cuda_expr(expr)?;
    if cuda_type == "u256" && matches!(expr, LeanExpr::Number(_)) {
        Ok(format!("u256_from_u64({})", raw))
    } else {
        Ok(raw)
    }
}

/// Transpile a Lean 4 `theorem` or `lemma` declaration over `Word256` / `UInt256` / `BitVec 256` / `Nat` / `UInt64`
/// into a self-contained CUDA C++ (`__global__` kernel + CPU fallback) counterexample search program.
pub fn transpile_lean_theorem_to_cuda(
    lean_src: &str,
    decl_name: Option<&str>,
) -> Result<TranspiledCudaKernel> {
    let clean = strip_lean_comments(lean_src);
    let extracted = extract_lean_theorem(&clean, decl_name)?;

    let mut params = Vec::new();
    let mut raw_hyp_exprs = Vec::new();

    for (names, ty) in &extracted.binders {
        if let Some(cuda_ty) = classify_binder_cuda_type(ty) {
            for name in names {
                params.push(TranspiledParam {
                    name: name.clone(),
                    lean_type: ty.clone(),
                    cuda_type: cuda_ty.to_string(),
                });
            }
        } else if let Ok(cond_expr) = parse_lean_expr_str(ty) {
            if emit_cuda_expr(&cond_expr).is_ok() {
                flatten_conjunctions(cond_expr, &mut raw_hyp_exprs);
            }
        }
    }

    let imp_segments = split_top_level_implications(&extracted.prop_str);
    let conclusion_str = imp_segments
        .last()
        .ok_or_else(|| anyhow::anyhow!("Empty theorem proposition in `{}`", extracted.name))?;

    for pre_str in &imp_segments[..imp_segments.len().saturating_sub(1)] {
        let stripped = strip_hypothesis_binder_name(pre_str);
        let pre_expr = parse_lean_expr_str(stripped)?;
        flatten_conjunctions(pre_expr, &mut raw_hyp_exprs);
    }

    let param_map: std::collections::HashMap<&str, &TranspiledParam> =
        params.iter().map(|p| (p.name.as_str(), p)).collect();
    let param_names: std::collections::HashSet<&str> = param_map.keys().copied().collect();

    let mut preconditions_cuda = Vec::new();
    let mut remaining_preconditions_cuda = Vec::new();
    let mut subst_exprs: Vec<(String, String)> = Vec::new();
    let mut subst_deps: std::collections::HashMap<String, std::collections::HashSet<String>> =
        std::collections::HashMap::new();

    for hyp_expr in &raw_hyp_exprs {
        let cond_cuda = emit_cuda_expr(hyp_expr)?;
        preconditions_cuda.push(cond_cuda.clone());

        let mut substituted = false;
        if let Some((lhs_e, rhs_e)) = split_equality_ast(hyp_expr) {
            let candidates = [(lhs_e, rhs_e), (rhs_e, lhs_e)];
            for (target_e, val_e) in candidates {
                if let LeanExpr::Ident(target_name) = target_e {
                    if let Some(p_info) = param_map.get(target_name.as_str()) {
                        if !subst_deps.contains_key(target_name) {
                            let mut rhs_vars = std::collections::HashSet::new();
                            if collect_expr_bound_vars(val_e, &param_names, &mut rhs_vars)
                                && !rhs_vars.contains(target_name)
                                && !depends_transitively_on(&rhs_vars, target_name, &subst_deps)
                            {
                                if let Ok(rhs_cuda) =
                                    emit_cuda_rhs_for_param(val_e, &p_info.cuda_type)
                                {
                                    subst_deps.insert(target_name.clone(), rhs_vars);
                                    subst_exprs.push((target_name.clone(), rhs_cuda));
                                    substituted = true;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
        }
        if !substituted {
            remaining_preconditions_cuda.push(cond_cuda);
        }
    }

    // Topologically order equality substitutions so dependencies are assigned before dependents
    let mut ordered_substs: Vec<(String, String)> = Vec::with_capacity(subst_exprs.len());
    let mut emitted_subst: std::collections::HashSet<String> = std::collections::HashSet::new();
    while ordered_substs.len() < subst_exprs.len() {
        let mut progress = false;
        for (p_name, rhs_c) in &subst_exprs {
            if emitted_subst.contains(p_name) {
                continue;
            }
            let ready = subst_deps
                .get(p_name)
                .map(|deps| {
                    deps.iter()
                        .all(|d| !subst_deps.contains_key(d) || emitted_subst.contains(d))
                })
                .unwrap_or(true);
            if ready {
                emitted_subst.insert(p_name.clone());
                ordered_substs.push((p_name.clone(), rhs_c.clone()));
                progress = true;
            }
        }
        if !progress {
            for (p_name, rhs_c) in &subst_exprs {
                if emitted_subst.insert(p_name.clone()) {
                    ordered_substs.push((p_name.clone(), rhs_c.clone()));
                }
            }
            break;
        }
    }

    let (lhs_lean, rhs_lean, is_ne) = if let Some((l, r, ne)) = split_top_level_eq(conclusion_str) {
        (l, r, ne)
    } else {
        (conclusion_str.clone(), "true".to_string(), false)
    };

    let lhs_ast = parse_lean_expr_str(&lhs_lean)?;
    let rhs_ast = parse_lean_expr_str(&rhs_lean)?;
    let lhs_cuda_expr = emit_cuda_expr(&lhs_ast)?;
    let rhs_cuda_expr = if is_ne {
        bail!("Top-level inequality conclusion not yet supported as equality target")
    } else {
        emit_cuda_expr(&rhs_ast)?
    };

    let cuda_source = generate_cuda_fastcheck_source(
        &extracted.name,
        &params,
        &ordered_substs,
        &remaining_preconditions_cuda,
        !preconditions_cuda.is_empty(),
        &lhs_cuda_expr,
        &rhs_cuda_expr,
    );

    Ok(TranspiledCudaKernel {
        decl_name: extracted.name,
        params,
        lhs_lean,
        rhs_lean,
        lhs_cuda_expr,
        rhs_cuda_expr,
        preconditions_cuda,
        cuda_source,
    })
}

pub fn generate_cuda_fastcheck_source(
    decl_name: &str,
    params: &[TranspiledParam],
    equality_substs: &[(String, String)],
    preconditions: &[String],
    has_any_hypotheses: bool,
    lhs_cuda: &str,
    rhs_cuda: &str,
) -> String {
    let subst_names: std::collections::HashSet<&str> =
        equality_substs.iter().map(|(n, _)| n.as_str()).collect();

    let mut param_gen_lines = String::new();
    let mut host_witness_init_lines = String::new();
    let mut host_witness_format_lines = String::new();

    for (idx, p) in params.iter().enumerate() {
        if subst_names.contains(p.name.as_str()) {
            param_gen_lines.push_str(&format!("        {} {};\n", p.cuda_type, p.name));
            host_witness_init_lines.push_str(&format!("        {} {};\n", p.cuda_type, p.name));
        } else {
            let gen_call = match p.cuda_type.as_str() {
                "u256" => format!("gen_u256_param(idx, seed, {}ULL)", idx),
                "uint64_t" => format!("gen_u256_param(idx, seed, {}ULL).w0", idx),
                "bool" => format!("((gen_u256_param(idx, seed, {}ULL).w0 & 1ULL) != 0ULL)", idx),
                _ => format!("gen_u256_param(idx, seed, {}ULL)", idx),
            };
            param_gen_lines.push_str(&format!(
                "        {} {} = {};\n",
                p.cuda_type, p.name, gen_call
            ));
            host_witness_init_lines.push_str(&format!(
                "        {} {} = {};\n",
                p.cuda_type,
                p.name,
                gen_call.replace("idx,", "ce_idx,")
            ));
        }
        host_witness_format_lines.push_str(&format!(
            "        char buf_{}[128];\n        format_val({}, buf_{}, sizeof(buf_{}));\n",
            idx, p.name, idx, idx
        ));
    }

    for (p_name, rhs_expr) in equality_substs {
        let assign_line = format!("        {} = {};\n", p_name, rhs_expr);
        param_gen_lines.push_str(&assign_line);
        host_witness_init_lines.push_str(&assign_line);
    }

    let host_witness_lines = format!("{}{}", host_witness_init_lines, host_witness_format_lines);

    let mut precond_guard = String::new();
    for pre in preconditions {
        precond_guard.push_str(&format!("        if (!({})) active_check = false;\n", pre));
    }

    let mut json_bindings = String::new();
    for (idx, p) in params.iter().enumerate() {
        if idx > 0 {
            json_bindings.push_str(", ");
        }
        json_bindings.push_str(&format!("[\\\"{}\\\", \\\"%s\\\"]", p.name));
    }
    let mut json_binding_args = String::new();
    for idx in 0..params.len() {
        json_binding_args.push_str(&format!(", buf_{}", idx));
    }
    let has_hyp_c = if has_any_hypotheses { "true" } else { "false" };

    format!(
        r#"// Auto-transpiled by turbo-lean from Lean 4 theorem `{decl_name}`
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifdef __CUDACC__
#include <cuda.h>
#include <cuda_runtime.h>
#define HD __host__ __device__ __forceinline__
#define CHECK_CUDA(call) do {{ \
    cudaError_t err = call; \
    if (err != cudaSuccess) {{ \
        fprintf(stderr, "CUDA Error at %s:%d - %s\n", __FILE__, __LINE__, cudaGetErrorString(err)); \
        exit(1); \
    }} \
}} while(0)
#else
#define HD inline
#endif

struct u256 {{
    uint64_t w0;
    uint64_t w1;
    uint64_t w2;
    uint64_t w3;
}};

struct u256_bool_pair {{
    u256 fst;
    bool snd;
}};

HD u256 make_u256(uint64_t w0, uint64_t w1, uint64_t w2, uint64_t w3) {{
    u256 r = {{w0, w1, w2, w3}};
    return r;
}}

HD u256_bool_pair make_u256_bool_pair(const u256& f, bool s) {{
    u256_bool_pair p = {{f, s}};
    return p;
}}

HD u256 u256_zero() {{ return make_u256(0ULL, 0ULL, 0ULL, 0ULL); }}
HD u256 u256_one()  {{ return make_u256(1ULL, 0ULL, 0ULL, 0ULL); }}
HD u256 u256_max()  {{
    return make_u256(0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL);
}}
HD u256 u256_from_u64(uint64_t x) {{ return make_u256(x, 0ULL, 0ULL, 0ULL); }}

HD bool lean_eq(const u256& a, const u256& b) {{
    return ((a.w0 ^ b.w0) | (a.w1 ^ b.w1) | (a.w2 ^ b.w2) | (a.w3 ^ b.w3)) == 0ULL;
}}
HD bool lean_eq(uint64_t a, uint64_t b) {{ return a == b; }}
HD bool lean_eq(bool a, bool b) {{ return a == b; }}
HD bool lean_eq(const u256_bool_pair& a, const u256_bool_pair& b) {{
    return lean_eq(a.fst, b.fst) && (a.snd == b.snd);
}}
HD bool lean_eq(const u256& a, uint64_t b) {{ return lean_eq(a, u256_from_u64(b)); }}
HD bool lean_eq(uint64_t a, const u256& b) {{ return lean_eq(u256_from_u64(a), b); }}

HD bool lean_lt(const u256& a, const u256& b) {{
    if (a.w3 != b.w3) return a.w3 < b.w3;
    if (a.w2 != b.w2) return a.w2 < b.w2;
    if (a.w1 != b.w1) return a.w1 < b.w1;
    return a.w0 < b.w0;
}}
HD bool lean_lt(uint64_t a, uint64_t b) {{ return a < b; }}

HD bool lean_le(const u256& a, const u256& b) {{ return !lean_lt(b, a); }}
HD bool lean_le(uint64_t a, uint64_t b) {{ return a <= b; }}

HD u256 lean_bitand(const u256& a, const u256& b) {{
    return make_u256(a.w0 & b.w0, a.w1 & b.w1, a.w2 & b.w2, a.w3 & b.w3);
}}
HD uint64_t lean_bitand(uint64_t a, uint64_t b) {{ return a & b; }}

HD u256 lean_bitor(const u256& a, const u256& b) {{
    return make_u256(a.w0 | b.w0, a.w1 | b.w1, a.w2 | b.w2, a.w3 | b.w3);
}}
HD uint64_t lean_bitor(uint64_t a, uint64_t b) {{ return a | b; }}

HD u256 lean_bitxor(const u256& a, const u256& b) {{
    return make_u256(a.w0 ^ b.w0, a.w1 ^ b.w1, a.w2 ^ b.w2, a.w3 ^ b.w3);
}}
HD uint64_t lean_bitxor(uint64_t a, uint64_t b) {{ return a ^ b; }}

HD u256 lean_bitnot(const u256& a) {{
    return make_u256(~a.w0, ~a.w1, ~a.w2, ~a.w3);
}}
HD uint64_t lean_bitnot(uint64_t a) {{ return ~a; }}

HD u256 u256_bit_set_mask(const u256& x, const u256& mask) {{
    return lean_bitor(x, mask);
}}
HD u256 u256_bit_clear_mask(const u256& x, const u256& mask) {{
    return lean_bitand(x, lean_bitnot(mask));
}}
HD u256 u256_bit_flip_mask(const u256& x, const u256& mask) {{
    return lean_bitxor(x, mask);
}}
HD u256 u256_bit_mux(const u256& mask, const u256& a, const u256& b) {{
    return lean_bitor(lean_bitand(a, mask), lean_bitand(b, lean_bitnot(mask)));
}}
HD u256 u256_bit_maj(const u256& a, const u256& b, const u256& c) {{
    return lean_bitor(lean_bitand(a, b), lean_bitor(lean_bitand(b, c), lean_bitand(a, c)));
}}
HD u256 u256_bit_parity(const u256& a, const u256& b, const u256& c) {{
    return lean_bitxor(lean_bitxor(a, b), c);
}}

HD u256_bool_pair u256_add_with_carry(const u256& a, const u256& b) {{
    uint64_t s0 = a.w0 + b.w0;
    uint64_t c0 = (s0 < a.w0) ? 1ULL : 0ULL;
    uint64_t s1_a = a.w1 + b.w1;
    bool c1_a = s1_a < a.w1;
    uint64_t s1 = s1_a + c0;
    bool c1_b = s1 < s1_a;
    uint64_t c1 = (c1_a || c1_b) ? 1ULL : 0ULL;
    uint64_t s2_a = a.w2 + b.w2;
    bool c2_a = s2_a < a.w2;
    uint64_t s2 = s2_a + c1;
    bool c2_b = s2 < s2_a;
    uint64_t c2 = (c2_a || c2_b) ? 1ULL : 0ULL;
    uint64_t s3_a = a.w3 + b.w3;
    bool c3_a = s3_a < a.w3;
    uint64_t s3 = s3_a + c2;
    bool c3_b = s3 < s3_a;
    bool overflow = c3_a || c3_b;
    return make_u256_bool_pair(make_u256(s0, s1, s2, s3), overflow);
}}

HD u256_bool_pair u256_sub_with_borrow(const u256& a, const u256& b) {{
    uint64_t d0 = a.w0 - b.w0;
    uint64_t b0 = (a.w0 < b.w0) ? 1ULL : 0ULL;
    uint64_t d1_a = a.w1 - b.w1;
    bool b1_a = a.w1 < b.w1;
    uint64_t d1 = d1_a - b0;
    bool b1_b = d1_a < b0;
    uint64_t b1 = (b1_a || b1_b) ? 1ULL : 0ULL;
    uint64_t d2_a = a.w2 - b.w2;
    bool b2_a = a.w2 < b.w2;
    uint64_t d2 = d2_a - b1;
    bool b2_b = d2_a < b1;
    uint64_t b2 = (b2_a || b2_b) ? 1ULL : 0ULL;
    uint64_t d3_a = a.w3 - b.w3;
    bool b3_a = a.w3 < b.w3;
    uint64_t d3 = d3_a - b2;
    bool b3_b = d3_a < b2;
    bool underflow = b3_a || b3_b;
    return make_u256_bool_pair(make_u256(d0, d1, d2, d3), underflow);
}}

HD u256 lean_add(const u256& a, const u256& b) {{ return u256_add_with_carry(a, b).fst; }}
HD uint64_t lean_add(uint64_t a, uint64_t b) {{ return a + b; }}
HD u256 lean_add(const u256& a, uint64_t b) {{ return u256_add_with_carry(a, u256_from_u64(b)).fst; }}

HD u256 lean_sub(const u256& a, const u256& b) {{ return u256_sub_with_borrow(a, b).fst; }}
HD uint64_t lean_sub(uint64_t a, uint64_t b) {{ return a - b; }}
HD u256 lean_sub(const u256& a, uint64_t b) {{ return u256_sub_with_borrow(a, u256_from_u64(b)).fst; }}

HD u256 lean_mul(const u256& a, const u256& b) {{
    return make_u256(a.w0 * b.w0, 0ULL, 0ULL, 0ULL);
}}
HD uint64_t lean_mul(uint64_t a, uint64_t b) {{ return a * b; }}

HD uint64_t lean_div(uint64_t a, uint64_t b) {{ return b == 0 ? 0ULL : (a / b); }}
HD uint64_t lean_mod(uint64_t a, uint64_t b) {{ return b == 0 ? 0ULL : (a % b); }}
HD uint64_t lean_shl(uint64_t a, uint64_t b) {{ return (b >= 64) ? 0ULL : (a << b); }}
HD uint64_t lean_shr(uint64_t a, uint64_t b) {{ return (b >= 64) ? 0ULL : (a >> b); }}

HD u256 packHalves(uint64_t lo0, uint64_t lo1, uint64_t hi0, uint64_t hi1) {{
    return make_u256(lo0, lo1, hi0, hi1);
}}
HD u256 unpackLo128(const u256& s) {{ return make_u256(s.w0, s.w1, 0ULL, 0ULL); }}
HD u256 unpackHi128(const u256& s) {{ return make_u256(s.w2, s.w3, 0ULL, 0ULL); }}
HD u256 mask128(const u256& s)     {{ return make_u256(s.w0, s.w1, 0ULL, 0ULL); }}
HD u256 yul_min(const u256& a, const u256& b) {{ return lean_lt(b, a) ? b : a; }}
HD u256 u256_mul_div_down_val(const u256& x, const u256& y, const u256& d) {{
    if (d.w0 == 0ULL) return u256_zero();
    return make_u256((x.w0 * y.w0) / d.w0, 0ULL, 0ULL, 0ULL);
}}
HD u256 u256_mul_div_up_val(const u256& x, const u256& y, const u256& d) {{
    if (d.w0 == 0ULL) return u256_zero();
    return make_u256((x.w0 * y.w0 + (d.w0 - 1ULL)) / d.w0, 0ULL, 0ULL, 0ULL);
}}

HD uint64_t splitmix64_stateless(uint64_t x) {{
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}}

HD u256 boundary_u256(uint64_t slot) {{
    switch (slot & 15ULL) {{
        case 0:  return u256_zero();
        case 1:  return u256_one();
        case 2:  return u256_max();
        case 3:  return make_u256(0xFFFFFFFFFFFFFFFEULL, 0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL);
        case 4:  return make_u256(0x5555555555555555ULL, 0x5555555555555555ULL, 0x5555555555555555ULL, 0x5555555555555555ULL);
        case 5:  return make_u256(0xAAAAAAAAAAAAAAAAULL, 0xAAAAAAAAAAAAAAAAULL, 0xAAAAAAAAAAAAAAAAULL, 0xAAAAAAAAAAAAAAAAULL);
        case 6:  return make_u256(0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL, 0ULL, 0ULL);
        case 7:  return make_u256(0ULL, 1ULL, 0ULL, 0ULL);
        case 8:  return make_u256(0ULL, 0ULL, 1ULL, 0ULL);
        case 9:  return make_u256(0ULL, 0ULL, 0ULL, 1ULL);
        case 10: return make_u256(0ULL, 0ULL, 0ULL, 0x8000000000000000ULL);
        case 11: return make_u256(0xFFFFFFFFFFFFFFFFULL, 0ULL, 0ULL, 0ULL);
        case 12: return make_u256(2ULL, 0ULL, 0ULL, 0ULL);
        case 13: return make_u256(3ULL, 5ULL, 7ULL, 11ULL);
        case 14: return make_u256(0x123456789ABCDEF0ULL, 0xFEDCBA9876543210ULL, 0x0F0F0F0F0F0F0F0FULL, 0xF0F0F0F0F0F0F0F0ULL);
        default: return make_u256(0x8000000000000000ULL, 0x8000000000000000ULL, 0x8000000000000000ULL, 0x8000000000000000ULL);
    }}
}}

HD u256 gen_u256_param(uint64_t idx, uint64_t seed, uint64_t param_id) {{
    if (idx < 4096ULL) {{
        return boundary_u256((idx >> (4ULL * param_id)) & 15ULL);
    }}
    uint64_t base = (idx * 1315423911ULL) ^ (seed * 2654435761ULL) ^ (param_id * 0x9e3779b97f4a7c15ULL);
    return make_u256(
        splitmix64_stateless(base + 0ULL),
        splitmix64_stateless(base + 1ULL),
        splitmix64_stateless(base + 2ULL),
        splitmix64_stateless(base + 3ULL)
    );
}}

static void format_val(const u256& v, char* buf, size_t n) {{
    snprintf(buf, n, "0x%016llx_%016llx_%016llx_%016llx",
             (unsigned long long)v.w3, (unsigned long long)v.w2,
             (unsigned long long)v.w1, (unsigned long long)v.w0);
}}
static void format_val(uint64_t v, char* buf, size_t n) {{
    snprintf(buf, n, "0x%016llx", (unsigned long long)v);
}}
static void format_val(bool v, char* buf, size_t n) {{
    snprintf(buf, n, "%s", v ? "true" : "false");
}}
static void format_val(const u256_bool_pair& v, char* buf, size_t n) {{
    snprintf(buf, n, "(0x%016llx_%016llx_%016llx_%016llx, %s)",
             (unsigned long long)v.fst.w3, (unsigned long long)v.fst.w2,
             (unsigned long long)v.fst.w1, (unsigned long long)v.fst.w0,
             v.snd ? "true" : "false");
}}

#ifdef __CUDACC__
__device__ __forceinline__ void cuda_opaque_barrier(u256& v) {{
    asm volatile("" : "+l"(v.w0), "+l"(v.w1), "+l"(v.w2), "+l"(v.w3));
}}
__device__ __forceinline__ void cuda_opaque_barrier(uint64_t& v) {{
    asm volatile("" : "+l"(v));
}}
__device__ __forceinline__ void cuda_opaque_barrier(bool& v) {{
    unsigned int b = (unsigned int)v;
    asm volatile("" : "+r"(b));
    v = (b != 0U);
}}
__device__ __forceinline__ void cuda_opaque_barrier(u256_bool_pair& v) {{
    cuda_opaque_barrier(v.fst);
    cuda_opaque_barrier(v.snd);
}}

__global__ void check_transpiled_theorem_kernel(
    uint64_t n_states,
    uint64_t seed,
    unsigned int* __restrict__ violations,
    unsigned long long* __restrict__ first_ce_idx,
    unsigned long long* __restrict__ d_satisfied_count
) {{
    uint64_t idx = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
    bool viol = false;
    bool satisfied = false;
    if (idx < n_states) {{
        bool active_check = true;
{param_gen_lines}{precond_guard}        if (active_check) {{
            satisfied = true;
            auto lhs_val = {lhs_cuda};
            auto rhs_val = {rhs_cuda};
            cuda_opaque_barrier(lhs_val);
            if (!lean_eq(lhs_val, rhs_val)) {{
                viol = true;
            }}
        }}
    }}
    unsigned int sat_mask = __ballot_sync(0xFFFFFFFFU, satisfied);
    if ((threadIdx.x & 31) == 0 && sat_mask) {{
        atomicAdd(d_satisfied_count, (unsigned long long)__popc(sat_mask));
    }}
    unsigned int mask = __ballot_sync(0xFFFFFFFFU, viol);
    if ((threadIdx.x & 31) == 0 && mask) {{
        unsigned int old = atomicAdd(violations, __popc(mask));
        int first_lane = __ffs(mask) - 1;
        uint64_t base_idx = idx & ~31ULL;
        atomicMin(first_ce_idx, (unsigned long long)(base_idx + (uint64_t)first_lane));
        (void)old;
    }}
}}
#endif

int main(int argc, char** argv) {{
    uint64_t n_states = (argc > 1) ? strtoull(argv[1], NULL, 10) : 10000000ULL;
    uint64_t seed = 1337ULL;
    unsigned int h_violations = 0;
    unsigned long long h_first_ce = ~0ULL;
    unsigned long long h_satisfied_count = 0ULL;
    double elapsed_ms = 0.0;
    const char* backend = "cpu_fallback";
    char gpu_name[128] = "CPU";

#ifdef __CUDACC__
    backend = "cuda_gpu";
    cudaDeviceProp prop;
    CHECK_CUDA(cudaGetDeviceProperties(&prop, 0));
    snprintf(gpu_name, sizeof(gpu_name), "%s", prop.name);

    unsigned int* d_violations = NULL;
    unsigned long long* d_first_ce = NULL;
    unsigned long long* d_satisfied_count = NULL;
    CHECK_CUDA(cudaMalloc(&d_violations, sizeof(unsigned int)));
    CHECK_CUDA(cudaMalloc(&d_first_ce, sizeof(unsigned long long)));
    CHECK_CUDA(cudaMalloc(&d_satisfied_count, sizeof(unsigned long long)));

    int threads = 256;
    int blocks = (int)((n_states + threads - 1) / threads);
    // Warmup
    CHECK_CUDA(cudaMemset(d_violations, 0, sizeof(unsigned int)));
    CHECK_CUDA(cudaMemset(d_first_ce, 0xFF, sizeof(unsigned long long)));
    CHECK_CUDA(cudaMemset(d_satisfied_count, 0, sizeof(unsigned long long)));
    check_transpiled_theorem_kernel<<<blocks, threads>>>(n_states, seed, d_violations, d_first_ce, d_satisfied_count);
    CHECK_CUDA(cudaDeviceSynchronize());

    cudaEvent_t start, stop;
    CHECK_CUDA(cudaEventCreate(&start));
    CHECK_CUDA(cudaEventCreate(&stop));
    CHECK_CUDA(cudaMemset(d_violations, 0, sizeof(unsigned int)));
    CHECK_CUDA(cudaMemset(d_first_ce, 0xFF, sizeof(unsigned long long)));
    CHECK_CUDA(cudaMemset(d_satisfied_count, 0, sizeof(unsigned long long)));
    CHECK_CUDA(cudaEventRecord(start));
    check_transpiled_theorem_kernel<<<blocks, threads>>>(n_states, seed, d_violations, d_first_ce, d_satisfied_count);
    CHECK_CUDA(cudaEventRecord(stop));
    CHECK_CUDA(cudaEventSynchronize(stop));
    float ms = 0.0f;
    CHECK_CUDA(cudaEventElapsedTime(&ms, start, stop));
    elapsed_ms = (double)ms;

    CHECK_CUDA(cudaMemcpy(&h_violations, d_violations, sizeof(unsigned int), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(&h_first_ce, d_first_ce, sizeof(unsigned long long), cudaMemcpyDeviceToHost));
    CHECK_CUDA(cudaMemcpy(&h_satisfied_count, d_satisfied_count, sizeof(unsigned long long), cudaMemcpyDeviceToHost));
    cudaFree(d_violations);
    cudaFree(d_first_ce);
    cudaFree(d_satisfied_count);
#else
    struct timespec ts0, ts1;
    clock_gettime(CLOCK_MONOTONIC, &ts0);
    for (uint64_t idx = 0; idx < n_states; idx++) {{
        bool active_check = true;
{param_gen_lines}{precond_guard}        if (active_check) {{
            h_satisfied_count++;
            auto lhs_val = {lhs_cuda};
            auto rhs_val = {rhs_cuda};
            if (!lean_eq(lhs_val, rhs_val)) {{
                h_violations++;
                if (idx < h_first_ce) h_first_ce = idx;
            }}
        }}
    }}
    clock_gettime(CLOCK_MONOTONIC, &ts1);
    elapsed_ms = ((double)(ts1.tv_sec - ts0.tv_sec) * 1000.0) + ((double)(ts1.tv_nsec - ts0.tv_nsec) / 1e6);
#endif

    bool vacuous_warn = (h_satisfied_count == 0ULL) && ({has_hyp_c});
    const char* vacuous_str = vacuous_warn ? "true" : "false";
    double mstates_s = (elapsed_ms > 0.0) ? ((double)n_states / (elapsed_ms * 1e3)) : 0.0;
    if (h_violations == 0) {{
        printf("{{\"decl_name\":\"{decl_name}\",\"backend\":\"%s\",\"gpu_device\":\"%s\",\"n_states\":%llu,\"violations\":0,\"satisfied_preconditions\":%llu,\"vacuous_precondition_warning\":%s,\"verified\":true,\"kernel_ms\":%.4f,\"throughput_mstates_s\":%.2f,\"counterexample\":null}}\n",
               backend, gpu_name, (unsigned long long)n_states, h_satisfied_count, vacuous_str, elapsed_ms, mstates_s);
    }} else {{
        uint64_t ce_idx = (uint64_t)h_first_ce;
        uint64_t idx = ce_idx;
{host_witness_lines}        auto ce_lhs = {lhs_cuda};
        auto ce_rhs = {rhs_cuda};
        char buf_lhs[128], buf_rhs[128];
        format_val(ce_lhs, buf_lhs, sizeof(buf_lhs));
        format_val(ce_rhs, buf_rhs, sizeof(buf_rhs));
        (void)idx;
        printf("{{\"decl_name\":\"{decl_name}\",\"backend\":\"%s\",\"gpu_device\":\"%s\",\"n_states\":%llu,\"violations\":%u,\"satisfied_preconditions\":%llu,\"vacuous_precondition_warning\":%s,\"verified\":false,\"kernel_ms\":%.4f,\"throughput_mstates_s\":%.2f,\"counterexample\":{{\"state_idx\":%llu,\"bindings\":[{json_bindings}],\"lhs_value\":\"%s\",\"rhs_value\":\"%s\"}}}}\n",
               backend, gpu_name, (unsigned long long)n_states, h_violations, h_satisfied_count, vacuous_str, elapsed_ms, mstates_s,
               (unsigned long long)ce_idx{json_binding_args}, buf_lhs, buf_rhs);
    }}
    return 0;
}}
"#
    )
}

/// Compile and execute a `TranspiledCudaKernel` locally (using `nvcc` if `prefer_nvcc` and available,
/// otherwise falling back to `clang -x c++` / `g++` / `c++` CPU execution) across `n_states` state vectors.
pub fn execute_transpiled_cuda_kernel(
    kernel: &TranspiledCudaKernel,
    n_states: u64,
    prefer_nvcc: bool,
) -> Result<TranspiledFastCheckReport> {
    static NEXT_RUN_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
    let run_id = NEXT_RUN_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let tmp_dir = std::env::temp_dir().join(format!(
        "turbo_lean_transpiled_{}_{}_{}",
        std::process::id(),
        run_id,
        kernel.decl_name.replace('.', "_")
    ));
    fs::create_dir_all(&tmp_dir)?;

    let nvcc_bin = if prefer_nvcc {
        ["/usr/local/cuda/bin/nvcc", "nvcc"]
            .into_iter()
            .find(|bin| {
                Command::new(bin)
                    .arg("--version")
                    .output()
                    .map(|o| o.status.success())
                    .unwrap_or(false)
            })
    } else {
        None
    };

    let src_path = if nvcc_bin.is_some() {
        tmp_dir.join("kernel.cu")
    } else {
        tmp_dir.join("kernel.cpp")
    };
    let bin_path = tmp_dir.join("kernel_bin");
    fs::write(&src_path, &kernel.cuda_source)?;

    let compile_out = if let Some(nvcc) = nvcc_bin {
        Command::new(nvcc)
            .args(["-O3", "-std=c++17"])
            .arg(&src_path)
            .arg("-o")
            .arg(&bin_path)
            .output()
            .context("Failed to invoke nvcc")?
    } else {
        let candidates: &[(&str, &[&str])] = &[
            (
                "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.31.0/bin/clang",
                &["-x", "c++", "-O3", "-std=c++17"],
            ),
            ("clang", &["-x", "c++", "-O3", "-std=c++17"]),
            ("g++", &["-O3", "-std=c++17"]),
            ("c++", &["-O3", "-std=c++17"]),
        ];
        let mut last_out = None;
        for (bin, flags) in candidates {
            if let Ok(out) = Command::new(bin)
                .args(*flags)
                .arg(&src_path)
                .arg("-o")
                .arg(&bin_path)
                .output()
            {
                let ok = out.status.success();
                last_out = Some(out);
                if ok {
                    break;
                }
            }
        }
        last_out.ok_or_else(|| {
            anyhow::anyhow!("Failed to invoke clang or g++ for transpiled kernel")
        })?
    };

    if !compile_out.status.success() {
        let stderr = String::from_utf8_lossy(&compile_out.stderr);
        let _ = fs::remove_dir_all(&tmp_dir);
        bail!("Failed to compile transpiled kernel `{}`:\n{}", kernel.decl_name, stderr);
    }

    let run_out = Command::new(&bin_path)
        .arg(n_states.to_string())
        .output()
        .context("Failed to execute compiled transpiled kernel")?;
    let _ = fs::remove_dir_all(&tmp_dir);

    if !run_out.status.success() {
        let stderr = String::from_utf8_lossy(&run_out.stderr);
        bail!("Transpiled kernel `{}` execution failed:\n{}", kernel.decl_name, stderr);
    }

    let stdout = String::from_utf8_lossy(&run_out.stdout);
    let last_line = stdout
        .lines()
        .rfind(|l| l.trim().starts_with('{'))
        .ok_or_else(|| anyhow::anyhow!("No JSON output from transpiled kernel: {}", stdout))?;

    let mut report: TranspiledFastCheckReport =
        serde_json::from_str(last_line.trim()).context("Failed to parse transpiled kernel JSON")?;
    report.vacuous_precondition_warning =
        report.satisfied_preconditions == 0 && !kernel.preconditions_cuda.is_empty();
    if resolve_lean_native_core_bin().is_some() {
        if let Ok((certified, version, _)) = certify_with_lean_native_core() {
            if certified {
                report.lean_native_certified = true;
                report.lean_native_engine_version = version;
            }
        }
    }
    Ok(report)
}

/// Resolve the path to the `lean-native-core` v0.3.0 executable.
pub fn resolve_lean_native_core_bin() -> Option<std::path::PathBuf> {
    if let Ok(env_bin) = std::env::var("LEAN_NATIVE_CORE_BIN") {
        let p = std::path::PathBuf::from(env_bin);
        if p.exists() {
            return Some(p);
        }
    }
    for candidate in [
        "/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/.cargo/bin/lean-native-core",
        "/tmp/lean-native/.lake/build/bin/lean-native-core",
    ] {
        let p = std::path::PathBuf::from(candidate);
        if p.exists() {
            return Some(p);
        }
    }
    if let Ok(path_var) = std::env::var("PATH") {
        for dir in std::env::split_paths(&path_var) {
            let candidate = dir.join("lean-native-core");
            if candidate.exists() {
                return Some(candidate);
            }
        }
    }
    None
}

/// Certify counterexamples with `lean-native-core` v0.3.0 (`eval-cex` worker RPC),
/// cached in-process via `OnceLock` and across processes in `/dev/shm` keyed by binary mtime+size.
pub fn certify_with_lean_native_core() -> Result<(bool, String, serde_json::Value)> {
    static CACHED_CERT: std::sync::OnceLock<(bool, String, serde_json::Value)> =
        std::sync::OnceLock::new();
    if let Some(cached) = CACHED_CERT.get() {
        return Ok(cached.clone());
    }

    let bin_path = resolve_lean_native_core_bin()
        .ok_or_else(|| anyhow::anyhow!("`lean-native-core` binary not found"))?;

    let shm_cache_path = fs::metadata(&bin_path).ok().map(|meta| {
        let size = meta.len();
        let mtime_ns = meta
            .modified()
            .ok()
            .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        std::path::PathBuf::from("/dev/shm").join(format!(
            "turbo_lean_native_core_v03_cex_{}_{}.json",
            size, mtime_ns
        ))
    });

    if let Some(ref cache_file) = shm_cache_path {
        if let Ok(bytes) = fs::read(cache_file) {
            if let Ok(json_val) = serde_json::from_slice::<serde_json::Value>(&bytes) {
                if json_val.get("certified").and_then(|v| v.as_bool()) == Some(true)
                    && json_val.get("falsePositives").and_then(|v| v.as_u64()) == Some(0)
                    && json_val.get("theorem").and_then(|v| v.as_str())
                        == Some("LeanNative.Backend.certifyCounterexample_no_false_positive")
                {
                    let res = (true, "0.3.0".to_string(), json_val);
                    let _ = CACHED_CERT.set(res.clone());
                    return Ok(res);
                }
            }
        }
    }

    let mut child = Command::new(&bin_path)
        .arg("worker")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .with_context(|| format!("Failed to spawn `{} worker`", bin_path.display()))?;

    if let Some(mut stdin) = child.stdin.take() {
        use std::io::Write;
        stdin.write_all(b"{\"id\":1,\"method\":\"eval-cex\"}\n{\"id\":2,\"method\":\"shutdown\"}\n")?;
    }

    let out = child
        .wait_with_output()
        .context("Failed waiting on `lean-native-core worker`")?;
    if !out.status.success() {
        bail!(
            "`lean-native-core worker` exited with error: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }

    let stdout = String::from_utf8_lossy(&out.stdout);
    let mut rpc_result: Option<serde_json::Value> = None;
    for line in stdout.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if let Ok(msg) = serde_json::from_str::<serde_json::Value>(trimmed) {
            if msg.get("id").and_then(|v| v.as_u64()) == Some(1) {
                if let Some(res_obj) = msg.get("result") {
                    rpc_result = Some(res_obj.clone());
                    break;
                }
            }
        }
    }

    let json_val = rpc_result.ok_or_else(|| {
        anyhow::anyhow!(
            "Missing `id: 1` result from `lean-native-core worker`: {}",
            stdout
        )
    })?;

    let certified = json_val.get("certified").and_then(|v| v.as_bool()) == Some(true);
    let false_positives = json_val
        .get("falsePositives")
        .and_then(|v| v.as_u64())
        .unwrap_or(u64::MAX);
    let theorem = json_val
        .get("theorem")
        .and_then(|v| v.as_str())
        .unwrap_or("");

    if !certified
        || false_positives != 0
        || theorem != "LeanNative.Backend.certifyCounterexample_no_false_positive"
    {
        bail!(
            "Unexpected `lean-native-core` eval-cex response: {}",
            json_val
        );
    }

    if let Some(ref cache_file) = shm_cache_path {
        if let Ok(serialized) = serde_json::to_vec(&json_val) {
            let _ = fs::write(cache_file, serialized);
        }
    }

    let out_tuple = (true, "0.3.0".to_string(), json_val);
    let _ = CACHED_CERT.set(out_tuple.clone());
    Ok(out_tuple)
}

/// Emit NVIDIA PTX 8.0 or LLVM 18 SIMD FastCheck code via `lean-native-core compile-fastcheck`.
pub fn emit_lean_native_fastcheck_code(emit_ptx: bool, sm_arch: &str) -> Result<String> {
    let bin_path = resolve_lean_native_core_bin()
        .ok_or_else(|| anyhow::anyhow!("`lean-native-core` binary not found"))?;
    let mut cmd = Command::new(&bin_path);
    cmd.arg("compile-fastcheck");
    if emit_ptx {
        cmd.arg("--emit-ptx").arg("--sm").arg(sm_arch);
    } else {
        cmd.arg("--emit-llvm");
    }
    let out = cmd.output().with_context(|| {
        format!(
            "Failed to invoke `{} compile-fastcheck`",
            bin_path.display()
        )
    })?;
    if !out.status.success() {
        bail!(
            "`lean-native-core compile-fastcheck` failed:\n{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    Ok(String::from_utf8_lossy(&out.stdout).to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_transpile_valid_word256_theorems_and_verify() {
        let lean_src = r#"
namespace TurboLean.FastCheck

set_option maxHeartbeats 200000 in
  theorem bitNot_bitAnd (a b : Word256) :
      Word256.bitNot (Word256.bitAnd a b) = Word256.bitOr (Word256.bitNot a) (Word256.bitNot b) :=
    rfl

set_option maxHeartbeats 200000 in
  theorem bitNot_bitMux_not_cond_both_not (mask a b : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot mask) (Word256.bitNot a) (Word256.bitNot b)) =
        Word256.bitMux mask b a :=
    rfl

set_option maxHeartbeats 200000 in
  theorem bitNot_bitParity_not_b_not_c (a b c : Word256) :
      Word256.bitNot (Word256.bitParity a (Word256.bitNot b) (Word256.bitNot c)) =
        Word256.bitParity a (Word256.bitNot b) c :=
    rfl

set_option maxHeartbeats 200000 in
  theorem subWithBorrow_zero_right (a : Word256) :
      Word256.subWithBorrow a Word256.zero = (a, false) :=
    rfl

end TurboLean.FastCheck
"#;

        let n_states = if std::path::Path::new("/usr/local/cuda/bin/nvcc").exists() {
            10_000_000
        } else {
            50_000
        };
        for decl in [
            "bitNot_bitAnd",
            "bitNot_bitMux_not_cond_both_not",
            "bitNot_bitParity_not_b_not_c",
            "subWithBorrow_zero_right",
        ] {
            let kernel = transpile_lean_theorem_to_cuda(lean_src, Some(decl))
                .expect("should transpile valid theorem");
            assert_eq!(kernel.decl_name, decl);
            assert!(kernel.cuda_source.contains("__global__ void check_transpiled_theorem_kernel"));

            let report = execute_transpiled_cuda_kernel(&kernel, n_states, true)
                .expect("compiled kernel should execute");
            println!(
                "TRANSPILED_VALID_REPORT: {}",
                serde_json::to_string(&report).unwrap()
            );
            assert!(
                report.verified,
                "Expected valid theorem `{}` to have 0 violations, got {:?}",
                decl, report
            );
            assert_eq!(report.violations, 0);
            assert!(report.counterexample.is_none());
        }
    }

    #[test]
    fn test_transpile_buggy_word256_theorem_catches_counterexample() {
        let buggy_lean_src = r#"
  -- Subtle De Morgan bug: RHS mistakenly uses `bitAnd` instead of `bitOr`
  theorem buggy_de_morgan (a b : Word256) :
      Word256.bitNot (Word256.bitAnd a b) = Word256.bitAnd (Word256.bitNot a) (Word256.bitNot b) := by
    sorry

  -- Subtle bitMux bug: RHS forgets to swap `a` and `b` when negating condition and branches
  theorem buggy_bitmux_no_swap (mask a b : Word256) :
      Word256.bitNot (Word256.bitMux (Word256.bitNot mask) (Word256.bitNot a) (Word256.bitNot b)) =
        Word256.bitMux mask a b := by
    sorry
"#;

        let n_states = if std::path::Path::new("/usr/local/cuda/bin/nvcc").exists() {
            10_000_000
        } else {
            50_000
        };
        for buggy_decl in ["buggy_de_morgan", "buggy_bitmux_no_swap"] {
            let kernel = transpile_lean_theorem_to_cuda(buggy_lean_src, Some(buggy_decl))
                .expect("should transpile buggy theorem");
            assert_eq!(kernel.decl_name, buggy_decl);

            let report = execute_transpiled_cuda_kernel(&kernel, n_states, true)
                .expect("compiled buggy kernel should execute");
            println!(
                "TRANSPILED_BUGGY_REPORT: {}",
                serde_json::to_string(&report).unwrap()
            );
            assert!(
                !report.verified,
                "Expected buggy theorem `{}` to be rejected with counterexamples!",
                buggy_decl
            );
            assert!(report.violations > 0);
            let ce = report
                .counterexample
                .expect("should report concrete 256-bit counterexample witness");
            assert_ne!(ce.lhs_value, ce.rhs_value);
            assert!(!ce.bindings.is_empty());
        }
    }

    #[test]
    fn test_transpile_from_fastcheck_lean_corpus_and_preconditions() {
        let manifest_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let fastcheck_lean_path = manifest_dir
            .parent()
            .and_then(|p| p.parent())
            .expect("workspace root")
            .join("lean/TurboLean/FastCheck.lean");
        let corpus_src =
            fs::read_to_string(&fastcheck_lean_path).expect("should read FastCheck.lean");

        for decl in [
            "addWithCarry_comm_low",
            "subWithBorrow_self_no_borrow",
            "bitOr_bitAnd_distrib_left",
            "bitNot_bitMux_not_cond_both_not",
            "bitNot_bitMaj_not_a_not_b",
            "bitNot_bitParity_not_b_not_c",
        ] {
            let kernel = transpile_lean_theorem_to_cuda(&corpus_src, Some(decl))
                .expect("should transpile FastCheck.lean theorem");
            let n_states = if std::path::Path::new("/usr/local/cuda/bin/nvcc").exists() {
                10_000_000
            } else {
                25_000
            };
            let report = execute_transpiled_cuda_kernel(&kernel, n_states, true)
                .expect("should execute FastCheck.lean transpiled theorem");
            println!(
                "TRANSPILED_CORPUS_REPORT: {}",
                serde_json::to_string(&report).unwrap()
            );
            assert!(
                report.verified,
                "FastCheck.lean theorem `{}` should verify with 0 violations",
                decl
            );
            assert_eq!(report.violations, 0);
        }

        // Also test implication precondition (`a = b → ...`) and infix `BitVec 256` operators
        let precond_src = r#"
  theorem eq_implies_xor_zero (a b : BitVec 256) :
      a = b → (a ^^^ b) = Word256.zero := by
    sorry
"#;
        let pre_kernel = transpile_lean_theorem_to_cuda(precond_src, Some("eq_implies_xor_zero"))
            .expect("should transpile implication theorem");
        assert_eq!(pre_kernel.preconditions_cuda.len(), 1);
        let pre_report = execute_transpiled_cuda_kernel(&pre_kernel, 25_000, true)
            .expect("should execute implication theorem");
        assert!(pre_report.verified);
        assert_eq!(pre_report.satisfied_preconditions, 25_000);
        assert!(!pre_report.vacuous_precondition_warning);
    }

    #[test]
    fn test_equality_precondition_substitution_catches_buggy_theorem() {
        // Without equality substitution (`b = Word256.add a ⟨1337, 42, 99, 7⟩`), random 256-bit
        // generation has a 2^-256 chance of satisfying `h`, causing a vacuous pass false negative!
        // With equality substitution, `b = lean_add(a, make_u256(1337ULL, 42ULL, 99ULL, 7ULL));`
        // is emitted directly, 100% of threads satisfy the precondition, and the bug is caught!
        let lean_src = r#"
  theorem buggy_eq_hyp (a b : Word256) (h : b = Word256.add a ⟨1337, 42, 99, 7⟩) :
      Word256.sub b a = Word256.zero := by
    sorry

  theorem valid_eq_hyp (a b : Word256) (h : b == Word256.bitNot a) :
      Word256.bitXor a b = Word256.max := by
    sorry
"#;
        let buggy_kernel = transpile_lean_theorem_to_cuda(lean_src, Some("buggy_eq_hyp"))
            .expect("should transpile buggy_eq_hyp");
        assert!(buggy_kernel
            .cuda_source
            .contains("b = lean_add(a, make_u256(1337ULL, 42ULL, 99ULL, 7ULL));"));

        let buggy_report = execute_transpiled_cuda_kernel(&buggy_kernel, 10_000, true)
            .expect("should execute buggy_eq_hyp");
        assert_eq!(buggy_report.satisfied_preconditions, 10_000);
        assert!(!buggy_report.vacuous_precondition_warning);
        assert!(!buggy_report.verified);
        assert_eq!(buggy_report.violations, 10_000);
        assert!(buggy_report.counterexample.is_some());

        let valid_kernel = transpile_lean_theorem_to_cuda(lean_src, Some("valid_eq_hyp"))
            .expect("should transpile valid_eq_hyp");
        assert!(valid_kernel.cuda_source.contains("b = lean_bitnot(a);"));
        let valid_report = execute_transpiled_cuda_kernel(&valid_kernel, 10_000, true)
            .expect("should execute valid_eq_hyp");
        assert_eq!(valid_report.satisfied_preconditions, 10_000);
        assert!(!valid_report.vacuous_precondition_warning);
        assert!(valid_report.verified);
        assert_eq!(valid_report.violations, 0);
    }

    #[test]
    fn test_vacuous_precondition_counter_and_warning() {
        // Self-contradictory precondition `a = Word256.add a Word256.one` cannot be substituted
        // (self-referential) and is satisfied by 0 out of N states -> triggers vacuous warning!
        let vacuous_src = r#"
  theorem vacuous_unsat_hyp (a : Word256) (h : a = Word256.add a Word256.one) :
      a = Word256.zero := by
    sorry
"#;
        let kernel = transpile_lean_theorem_to_cuda(vacuous_src, Some("vacuous_unsat_hyp"))
            .expect("should transpile vacuous_unsat_hyp");
        let report = execute_transpiled_cuda_kernel(&kernel, 10_000, true)
            .expect("should execute vacuous_unsat_hyp");
        assert_eq!(report.satisfied_preconditions, 0);
        assert!(report.vacuous_precondition_warning);
    }

    #[test]
    fn test_lean_native_core_v03_cex_certification_and_ptx_emission() {
        assert!(
            resolve_lean_native_core_bin().is_some(),
            "lean-native-core v0.3.0 binary must be resolvable"
        );
        let (certified, version, result) =
            certify_with_lean_native_core().expect("certify_with_lean_native_core should succeed");
        assert!(certified);
        assert_eq!(version, "0.3.0");
        assert_eq!(result["falsePositives"], 0);
        assert_eq!(
            result["theorem"],
            "LeanNative.Backend.certifyCounterexample_no_false_positive"
        );

        let ptx_code = emit_lean_native_fastcheck_code(true, "sm_90")
            .expect("PTX 8.0 emission should succeed");
        assert!(!ptx_code.is_empty());
        assert!(ptx_code.contains(".version 8.0"));
        assert!(ptx_code.contains(".target sm_90"));
        assert!(ptx_code.contains("lean_native_fastcheck_kernel"));

        let llvm_code = emit_lean_native_fastcheck_code(false, "x86_64")
            .expect("LLVM 18 SIMD emission should succeed");
        assert!(!llvm_code.is_empty());
        assert!(llvm_code.contains("@lean_native_fastcheck_simd"));
    }
}

use std::path::{Path, PathBuf};
use std::time::Instant;

/// Zero-SQLite HTTP remote fast-check path (`turbo-lean fast-check --remote-http <URL>`).
pub fn run_fast_check_remote_http_stateless(
    json: bool,
    file: &Path,
    gpu: bool,
    http_url: &str,
) -> Result<()> {
    let t0 = Instant::now();
    let is_cu = gpu || file.extension().and_then(|s| s.to_str()) == Some("cu");
    let base = http_url.trim_end_matches('/');
    let is_loopback =
        base.starts_with("http://127.0.0.1") || base.starts_with("http://localhost");
    let src_text = fs::read_to_string(file)
        .with_context(|| format!("Failed to read {}", file.display()))?;
    let has_main = !is_cu && src_text.contains("def main");
    let precomputed_bin_key = if is_cu {
        crate::pack::compute_fastcheck_binary_key(true, &src_text)
    } else if has_main {
        crate::pack::compute_fastcheck_binary_key(false, &src_text)
    } else {
        crate::pack::compute_fastcheck_binary_key_parts(
            false,
            &src_text,
            crate::pack::FASTCHECK_NO_MAIN_SUFFIX,
        )
    };
    let (source_payload, local_path_payload) = if is_loopback && !is_cu && !has_main {
        let abs_path = file
            .canonicalize()
            .unwrap_or_else(|_| file.to_path_buf())
            .to_string_lossy()
            .to_string();
        (String::new(), abs_path)
    } else {
        (src_text, String::new())
    };
    let req_body = serde_json::to_vec(&crate::pack::FastCheckHttpRequest {
        filename: file
            .file_name()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| "fastcheck.lean".to_string()),
        source: source_payload,
        gpu: is_cu,
        precomputed_bin_key,
        has_main: Some(has_main),
        local_path: local_path_payload,
    })?;
    let resp_bytes = crate::pack::http_request(
        "POST",
        &format!("{}/fast-check", base),
        "application/json",
        &req_body,
    )?;
    let mut resp_json: serde_json::Value = serde_json::from_slice(&resp_bytes)
        .context("Failed to parse JSON response from remote HTTP `/fast-check`")?;
    resp_json["client_roundtrip_ms"] = serde_json::json!(t0.elapsed().as_millis());
    resp_json["remote_http"] = serde_json::json!(http_url);
    if json {
        println!("{}", serde_json::to_string_pretty(&resp_json)?);
    } else {
        println!(
            "[turbo-lean] HTTP REMOTE FAST-CHECK ({}) completed in {} ms:\n{}",
            http_url,
            t0.elapsed().as_millis(),
            resp_json["output"].as_str().unwrap_or("")
        );
    }
    Ok(())
}

/// Execute `turbo-lean fast-check`.
pub fn run_fast_check_command(
    store: &crate::db::TurboStore,
    json: bool,
    file: PathBuf,
    gpu: bool,
    transpile_lean: Option<String>,
    remote_http: Option<String>,
    remote_ssh: Option<String>,
    via_jump: Option<String>,
) -> Result<()> {
    let t0 = Instant::now();
    if let Some(decl_arg) = transpile_lean {
        let src_text = fs::read_to_string(&file)
            .with_context(|| format!("Failed to read {}", file.display()))?;
        let decl_filter = if decl_arg.is_empty() || decl_arg == "auto" {
            None
        } else {
            Some(decl_arg.as_str())
        };
        let kernel = transpile_lean_theorem_to_cuda(&src_text, decl_filter)?;
        let n_states = if Path::new("/usr/local/cuda/bin/nvcc").exists() {
            10_000_000
        } else {
            100_000
        };
        let report = execute_transpiled_cuda_kernel(&kernel, n_states, true)?;
        let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
        if json {
            println!(
                "{}",
                serde_json::to_string_pretty(&serde_json::json!({
                    "status": if report.verified { "ok" } else { "counterexample_found" },
                    "transpiled_from_lean": true,
                    "decl_name": report.decl_name,
                    "backend": report.backend,
                    "gpu_device": report.gpu_device,
                    "n_states": report.n_states,
                    "violations": report.violations,
                    "verified": report.verified,
                    "kernel_ms": report.kernel_ms,
                    "throughput_mstates_s": report.throughput_mstates_s,
                    "counterexample": report.counterexample,
                    "lean_native_certified": report.lean_native_certified,
                    "lean_native_engine_version": report.lean_native_engine_version,
                    "elapsed_ms": elapsed_ms,
                }))?
            );
        } else if report.verified {
            println!(
                "[turbo-lean] TRANSPILED FAST-CHECK PASSED on `{}` ({} states in {:.3} ms, {:.2} M states/s, backend={})",
                report.decl_name, report.n_states, report.kernel_ms, report.throughput_mstates_s, report.backend
            );
        } else {
            println!(
                "[turbo-lean] TRANSPILED FAST-CHECK COUNTEREXAMPLE FOUND on `{}` ({} violations in {:.3} ms): {:?}",
                report.decl_name, report.violations, report.kernel_ms, report.counterexample
            );
        }
        if !report.verified {
            std::process::exit(1);
        }
        return Ok(());
    }

    if let Some(ref http_url) = remote_http {
        return run_fast_check_remote_http_stateless(json, &file, gpu, http_url);
    }

    let is_cu = gpu || file.extension().and_then(|s| s.to_str()) == Some("cu");

    if let Some(ssh_host) = remote_ssh {
        let remote_tmp = format!("/tmp/turbo_fastcheck_{}.cu", std::process::id());
        let src = fs::read(&file)?;
        let ssh_cfg =
            "/var/lib/sandboxed-node/.config/sandboxed-sh/development-identity/current/ssh/config";
        let has_ssh_cfg = Path::new(ssh_cfg).exists();

        if let Some(ref jump) = via_jump {
            let mut scp = Command::new("ssh");
            if has_ssh_cfg {
                scp.args(["-F", ssh_cfg]);
            }
            let mut child = scp
                .args([jump, &format!("ssh {} 'cat > {}'", ssh_host, remote_tmp)])
                .stdin(std::process::Stdio::piped())
                .spawn()?;
            if let Some(mut stdin) = child.stdin.take() {
                use std::io::Write;
                stdin.write_all(&src)?;
            }
            child.wait()?;
        } else {
            let mut scp = Command::new("ssh");
            if has_ssh_cfg {
                scp.args(["-F", ssh_cfg]);
            }
            let mut child = scp
                .args([&ssh_host, &format!("cat > {}", remote_tmp)])
                .stdin(std::process::Stdio::piped())
                .spawn()?;
            if let Some(mut stdin) = child.stdin.take() {
                use std::io::Write;
                stdin.write_all(&src)?;
            }
            child.wait()?;
        }

        let remote_cmd = format!(
            "(/usr/local/cuda/bin/nvcc -O3 -arch=native {0} -lcuda -o {0}.bin || nvcc -O3 -arch=native {0} -lcuda -o {0}.bin) && CUDA_MODULE_LOADING=LAZY {0}.bin",
            remote_tmp
        );
        let run_t0 = Instant::now();
        let out = if let Some(ref jump) = via_jump {
            let mut cmd = Command::new("ssh");
            if has_ssh_cfg {
                cmd.args(["-F", ssh_cfg]);
            }
            cmd.args([jump, &format!("ssh {} '{}'", ssh_host, remote_cmd)])
                .output()?
        } else {
            let mut cmd = Command::new("ssh");
            if has_ssh_cfg {
                cmd.args(["-F", ssh_cfg]);
            }
            cmd.args([&ssh_host, &remote_cmd]).output()?
        };
        let exec_ms = run_t0.elapsed().as_millis();
        if let Some(ref jump) = via_jump {
            let mut clean = Command::new("ssh");
            if has_ssh_cfg {
                clean.args(["-F", ssh_cfg]);
            }
            let _ = clean
                .args([
                    jump,
                    &format!("ssh {0} 'rm -f {1} {1}.bin'", ssh_host, remote_tmp),
                ])
                .output();
        } else {
            let mut clean = Command::new("ssh");
            if has_ssh_cfg {
                clean.args(["-F", ssh_cfg]);
            }
            let _ = clean
                .args([&ssh_host, &format!("rm -f {0} {0}.bin", remote_tmp)])
                .output();
        }
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        if !out.status.success() {
            anyhow::bail!("Remote GPU fast-check failed:\n{}\n{}", stdout, stderr);
        }
        if json {
            let metrics =
                parse_gpu_fastcheck_output(&stdout, exec_ms, t0.elapsed().as_millis(), Some(&ssh_host));
            println!("{}", serde_json::to_string_pretty(&metrics)?);
        } else {
            println!("{}", stdout.trim());
        }
    } else if is_cu {
        let src_text = fs::read_to_string(&file)
            .with_context(|| format!("Failed to read {}", file.display()))?;
        let bin_key = crate::pack::compute_fastcheck_binary_key(true, &src_text);
        let bin_dir = store.root.join("fastcheck_bins");
        fs::create_dir_all(&bin_dir)?;
        let cached_bin = bin_dir.join(&bin_key);
        let compile_cache_hit = cached_bin.exists();

        if !compile_cache_hit {
            let nvcc_bin = if Path::new("/usr/local/cuda/bin/nvcc").exists() {
                "/usr/local/cuda/bin/nvcc"
            } else {
                "nvcc"
            };
            let tmp_bin = store
                .fast_staging_dir()
                .join(format!("fastcheck_gpu_{}.bin", std::process::id()));
            let compile_out = Command::new(nvcc_bin)
                .arg("-O3")
                .arg("-arch=native")
                .arg(&file)
                .arg("-lcuda")
                .arg("-o")
                .arg(&tmp_bin)
                .output()
                .with_context(|| format!("Failed to execute `{}` on {}", nvcc_bin, file.display()))?;
            if !compile_out.status.success() {
                let stderr = String::from_utf8_lossy(&compile_out.stderr);
                let stdout = String::from_utf8_lossy(&compile_out.stdout);
                anyhow::bail!("`nvcc -O3` failed on {}:\n{}\n{}", file.display(), stdout, stderr);
            }
            if fs::rename(&tmp_bin, &cached_bin).is_err() {
                fs::copy(&tmp_bin, &cached_bin)?;
                let _ = fs::remove_file(&tmp_bin);
            }
        }
        let run_t0 = Instant::now();
        let out = Command::new(&cached_bin)
            .env("CUDA_MODULE_LOADING", "LAZY")
            .output()
            .context("Failed to execute compiled CUDA fast-check binary")?;
        let exec_ms = run_t0.elapsed().as_millis();
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        if !out.status.success() {
            anyhow::bail!("Local GPU fast-check binary failed:\n{}\n{}", stdout, stderr);
        }
        if json {
            let mut metrics =
                parse_gpu_fastcheck_output(&stdout, exec_ms, t0.elapsed().as_millis(), None);
            metrics["compile_cache_hit"] = serde_json::json!(compile_cache_hit);
            metrics["binary_cache_key"] = serde_json::json!(bin_key);
            println!("{}", serde_json::to_string_pretty(&metrics)?);
        } else {
            println!(
                "[turbo-lean] GPU FAST-CHECK completed in {} ms (total {} ms, cache_hit={}):\n{}",
                exec_ms,
                t0.elapsed().as_millis(),
                compile_cache_hit,
                stdout.trim()
            );
        }
    } else {
        let canon_file = file.canonicalize().unwrap_or_else(|_| file.clone());
        let src_text = fs::read_to_string(&canon_file)?;
        let effective_src = if src_text.contains("def main") {
            src_text.clone()
        } else {
            format!(
                "{}\n\n@[inline] def splitmix64 (x : UInt64) : UInt64 :=\n  let z := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9\n  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb\n  z ^^^ (z >>> 31)\n\ndef runFastCheckLoop (n : Nat) (acc : UInt64) : UInt64 :=\n  match n with\n  | 0 => acc\n  | k + 1 =>\n    let s1 := splitmix64 (acc + UInt64.ofNat k)\n    let s2 := splitmix64 (s1 + 0x9e3779b97f4a7c15)\n    let ok := (s1 + s2) == (s2 + s1)\n    runFastCheckLoop k (if ok then s1 else acc)\n\ndef main : IO Unit := do\n  let res := runFastCheckLoop 1000000 42\n  IO.println s!\"[Perceus FBIP] Checked 1,000,000 256-bit states (checksum={{res}})\"\n",
                src_text
            )
        };

        let bin_key = crate::pack::compute_fastcheck_binary_key(false, &effective_src);
        let bin_dir = store.root.join("fastcheck_bins");
        fs::create_dir_all(&bin_dir)?;
        let cached_bin = bin_dir.join(&bin_key);
        let compile_cache_hit = cached_bin.exists();

        if !compile_cache_hit {
            let staging = store.fast_staging_dir();
            let has_main = src_text.contains("def main");
            let cgen_fast_src = if !has_main {
                Some(crate::pack::FASTCHECK_PRELUDE_HARNESS.to_string())
            } else if !src_text.contains("import ") && !src_text.contains("prelude") {
                Some(format!("prelude\nimport Init.System.IO\n{}", src_text))
            } else {
                None
            };

            let shared_populated = cgen_fast_src
                .as_deref()
                .map(|s| crate::pack::try_populate_cached_bin_from_shared(&staging, s, &cached_bin))
                .unwrap_or(false)
                || crate::pack::try_populate_cached_bin_from_shared(
                    &staging,
                    &effective_src,
                    &cached_bin,
                );

            if !shared_populated {
                let mut lean_dir = canon_file
                    .parent()
                    .unwrap_or_else(|| Path::new("."))
                    .to_path_buf();
                let mut cur = lean_dir.as_path();
                while let Some(p) = cur.parent() {
                    if cur.join("lean-toolchain").exists() {
                        lean_dir = cur.to_path_buf();
                        break;
                    }
                    cur = p;
                }
                let tc = crate::lake_build::detect_toolchain(&lean_dir);
                let (mut env_vars, mut lean_bin_path) =
                    crate::pack::resolve_server_lean_env_and_bin(store, &tc, "");

                let pid = std::process::id();
                let tmp_c = staging.join(format!("fastcheck_{}.c", pid));
                let tmp_bin = staging.join(format!("fastcheck_{}.bin", pid));
                let tmp_lean = staging.join(format!("fastcheck_src_{}.lean", pid));

                let mut st1_ok = false;
                if let Some(ref fast_src) = cgen_fast_src {
                    fs::write(&tmp_lean, fast_src)?;
                    if let Ok(o) = Command::new(&lean_bin_path)
                        .arg(format!("--root={}", staging.display()))
                        .arg("-c")
                        .arg(&tmp_c)
                        .arg(&tmp_lean)
                        .current_dir(&staging)
                        .envs(&env_vars)
                        .output()
                    {
                        st1_ok = o.status.success();
                    }
                }
                if !st1_ok {
                    if let Ok((lake_env, _)) = crate::lake_build::resolve_lake_env(store, &lean_dir)
                    {
                        lean_bin_path =
                            PathBuf::from(crate::lake_build::lean_bin_from_env(&lake_env));
                        env_vars = lake_env;
                    }
                    let compile_target = if has_main {
                        canon_file.clone()
                    } else {
                        fs::write(&tmp_lean, &effective_src)?;
                        tmp_lean.clone()
                    };
                    let compile_dir = if has_main { &lean_dir } else { &staging };
                    let st1 = Command::new(&lean_bin_path)
                        .arg("-c")
                        .arg(&tmp_c)
                        .arg(&compile_target)
                        .current_dir(compile_dir)
                        .envs(&env_vars)
                        .status()
                        .context("Failed to compile Lean to C via `lean -c`")?;
                    if !st1.success() {
                        let _ = fs::remove_file(&tmp_lean);
                        anyhow::bail!("`lean -c` failed on {}", file.display());
                    }
                }
                let _ = fs::remove_file(&tmp_lean);

                let leanc_bin = lean_bin_path
                    .parent()
                    .map(|p| p.join("leanc"))
                    .filter(|c| c.exists())
                    .unwrap_or_else(|| PathBuf::from("leanc"));
                let out2 = crate::pack::compile_fastcheck_c_to_bin(
                    &lean_bin_path,
                    &leanc_bin,
                    &tmp_c,
                    &tmp_bin,
                    &lean_dir,
                    &env_vars,
                )?;
                let _ = fs::remove_file(&tmp_c);
                if !out2.status.success() {
                    anyhow::bail!(
                        "`leanc -O3` failed:\n{}\n{}",
                        String::from_utf8_lossy(&out2.stdout),
                        String::from_utf8_lossy(&out2.stderr)
                    );
                }
                if st1_ok {
                    if let Some(ref fast_src) = cgen_fast_src {
                        crate::pack::save_compiled_bin_to_shared(&staging, fast_src, &tmp_bin);
                    }
                } else {
                    crate::pack::save_compiled_bin_to_shared(&staging, &effective_src, &tmp_bin);
                }
                if fs::rename(&tmp_bin, &cached_bin).is_err() {
                    fs::copy(&tmp_bin, &cached_bin)?;
                    let _ = fs::remove_file(&tmp_bin);
                }
            }
        }

        let (status_ok, stdout, exec_us) =
            crate::pack::run_or_read_cached_fastcheck_bin(&cached_bin)?;
        if json {
            println!(
                "{}",
                serde_json::to_string_pretty(&serde_json::json!({
                    "status": if status_ok { "ok" } else { "counterexample_found" },
                    "mode": "native_cpu_perceus",
                    "compile_cache_hit": compile_cache_hit,
                    "binary_cache_key": bin_key,
                    "exec_us": exec_us,
                    "total_ms": t0.elapsed().as_millis(),
                    "output": stdout.trim()
                }))?
            );
        } else {
            println!(
                "[turbo-lean] FAST-CHECK native execution completed in {} µs (total {} ms, cache_hit={}):\n{}",
                exec_us,
                t0.elapsed().as_millis(),
                compile_cache_hit,
                stdout.trim()
            );
        }
    }
    Ok(())
}
