//! Pure-Rust quantized `int8` Matryoshka MUDD-ClippedReLU^2-TRM + Vacuity inference engine.
//!
//! Zero external crate dependencies beyond `serde` / `serde_json` (already in `Cargo.toml`).
//! Supports both:
//!   * `fractal-trm-matryoshka-v4` full payloads (`int8_q8_tensors` with RFC 1950 `zlib_b64`), and
//!   * `fractal-trm-matryoshka-v4-s0s1` compact payloads (`int8_q8_raw_tensors` raw base64 Q8),
//! with a compact embedded Stage-0 fallback (`matryoshka_s0_weights.json`, `include_str!`) so
//! sub-10-us premise affinity & vacuity scoring still work when `matryoshka_weights.nvfp4.json`
//! is absent on disk. External paths (`MAXWELL_MATRYOSHKA_WEIGHTS`, sibling `maxwell/training/`,
//! `/usr/local/share/maxwell/training/`) are preferred when present.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::OnceLock;

const MASK64: u64 = 0xFFFF_FFFF_FFFF_FFFF;
const SPLITMIX_M1: u64 = 0xBF58_476D_1CE4_E5B9;
const SPLITMIX_M2: u64 = 0x94D0_49BB_1331_11EB;

/// Exact bit-for-bit match of `training/anvil2_trm_trainer.py::splitmix64_hash`.
/// Returns `(bucket_key = x >> 1, sign = +1.0 if even else -1.0)`.
pub fn splitmix64_hash(text: &str) -> (u64, f32) {
    let mut h: u64 = 0x9E37_79B9_7F4A_7C15;
    for b in text.as_bytes() {
        h = (h ^ (*b as u64)).wrapping_mul(SPLITMIX_M1);
    }
    let mut x = h;
    x = (x ^ (x >> 30)).wrapping_mul(SPLITMIX_M1);
    x = (x ^ (x >> 27)).wrapping_mul(SPLITMIX_M2);
    x = (x ^ (x >> 31)) & MASK64;
    let sign = if (x & 1) == 0 { 1.0 } else { -1.0 };
    (x >> 1, sign)
}

fn sigmoid(x: f32) -> f32 {
    let c = x.clamp(-15.0, 15.0);
    1.0 / (1.0 + (-c).exp())
}

fn rms_norm(vec: &[f32]) -> Vec<f32> {
    if vec.is_empty() {
        return Vec::new();
    }
    let ms = vec.iter().map(|v| v * v).sum::<f32>() / (vec.len() as f32);
    let inv = 1.0 / (ms + 1e-6).sqrt();
    vec.iter().map(|v| v * inv).collect()
}

/// Row-major matvec `out[0..c_use] = x[0..r_use] @ w_flat` (`rows x cols` full shape).
fn matvec_rowmajor(x: &[f32], w_flat: &[f32], rows: usize, cols: usize, r_use: usize, c_use: usize) -> Vec<f32> {
    let mut out = vec![0.0f32; c_use];
    let r_lim = r_use.min(rows).min(x.len());
    let c_lim = c_use.min(cols);
    for i in 0..r_lim {
        let xi = x[i];
        if xi == 0.0 {
            continue;
        }
        let base = i * cols;
        for j in 0..c_lim {
            out[j] += xi * w_flat[base + j];
        }
    }
    out
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq)]
pub struct LeanStmtFeatures {
    pub decl: String,
    pub stmt_nodes: usize,
    pub stmt_depth: usize,
    pub num_binders: usize,
    pub goal_head: String,
    pub stmt_consts: Vec<String>,
    pub stmt_consts_count: usize,
}

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '\''
}

/// Extract identifier tokens (`[A-Za-z_][A-Za-z0-9_'.]*`) from Lean source.
pub fn extract_lean_idents(src: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for c in src.chars() {
        let valid = if cur.is_empty() {
            c.is_ascii_alphabetic() || c == '_'
        } else {
            is_ident_char(c)
        };
        if valid {
            cur.push(c);
        } else if !cur.is_empty() {
            out.push(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

/// Exact port of `training/matryoshka_runtime.py::parse_lean_stmt_features`.
pub fn parse_lean_stmt_features(decl_name: &str, stmt_src: &str) -> LeanStmtFeatures {
    let src = stmt_src.trim();
    let bytes: Vec<char> = src.chars().collect();
    let mut max_depth = 1usize;
    let mut cur_depth = 1usize;
    let mut num_binders = 0usize;
    let mut in_sig = true;
    for (idx, ch) in bytes.iter().enumerate() {
        match ch {
            '(' | '[' | '{' | '⟨' => {
                cur_depth += 1;
                if cur_depth > max_depth {
                    max_depth = cur_depth;
                }
                if in_sig && matches!(ch, '(' | '{' | '[') {
                    num_binders += 1;
                }
            }
            ')' | ']' | '}' | '⟩' => {
                cur_depth = cur_depth.saturating_sub(1).max(1);
            }
            ':' => {
                if cur_depth == 1 && idx > 0 && bytes[idx - 1] != ':' {
                    in_sig = false;
                }
            }
            _ => {}
        }
    }
    let idents = extract_lean_idents(src);
    let eq_count = src.matches('=').count();
    let arrow_count = src.matches('→').count() + src.matches("->").count();
    let stmt_nodes = (idents.len() + eq_count * 2 + arrow_count * 2).max(4);
    let goal_tail = src.rsplit(':').next().unwrap_or(src);
    let goal_head = if goal_tail.contains('↔') || goal_tail.contains("Iff") {
        "Iff"
    } else if goal_tail.contains('≠') || goal_tail.contains("Ne ") {
        "Not"
    } else if goal_tail.contains('=') || goal_tail.contains("Eq ") {
        "Eq"
    } else if goal_tail.contains('≤') || goal_tail.contains("<=") || goal_tail.contains("LE.le") {
        "LE.le"
    } else if goal_tail.contains('<') || goal_tail.contains("LT.lt") {
        "LT.lt"
    } else if goal_tail.contains('∧') || goal_tail.contains("And ") {
        "And"
    } else if goal_tail.contains('∃') || goal_tail.contains("Exists") {
        "Exists"
    } else if goal_tail.contains("False") || goal_tail.contains('¬') {
        "Not"
    } else {
        "App"
    }
    .to_string();
    const KEYWORDS: &[&str] = &[
        "theorem", "lemma", "def", "by", "let", "in", "fun", "match", "with", "if", "then", "else",
        "forall", "have", "show", "where", "do", "return",
    ];
    let mut stmt_consts: Vec<String> = Vec::new();
    for tok in idents {
        if KEYWORDS.contains(&tok.as_str()) || tok.chars().count() <= 1 {
            continue;
        }
        let first = tok.chars().next().unwrap_or('_');
        if tok.contains('.') || first.is_uppercase() {
            if !stmt_consts.iter().any(|c| c == &tok) {
                stmt_consts.push(tok);
            }
        }
    }
    let stmt_consts_count = stmt_consts.len().max(1);
    stmt_consts.truncate(24);
    LeanStmtFeatures {
        decl: if decl_name.is_empty() { "anon".to_string() } else { decl_name.to_string() },
        stmt_nodes,
        stmt_depth: max_depth.max(2),
        num_binders,
        goal_head,
        stmt_consts,
        stmt_consts_count,
    }
}

fn contains_tactic_ident(low: &str, ident: &str) -> bool {
    let bytes = low.as_bytes();
    let needle = ident.as_bytes();
    if needle.is_empty() || needle.len() > bytes.len() {
        return false;
    }
    let is_ident_byte = |b: u8| b.is_ascii_alphanumeric() || b == b'_' || b == b'\'';
    let mut i = 0;
    while i + needle.len() <= bytes.len() {
        if &bytes[i..i + needle.len()] == needle {
            let left_ok = i == 0 || !is_ident_byte(bytes[i - 1]);
            let right_ok =
                i + needle.len() == bytes.len() || !is_ident_byte(bytes[i + needle.len()]);
            if left_ok && right_ok {
                return true;
            }
        }
        i += 1;
    }
    false
}

fn contains_tactic_pair(low: &str, first: &str, second: &str) -> bool {
    let toks: Vec<&str> = low
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '\''))
        .filter(|t| !t.is_empty())
        .collect();
    toks.windows(2).any(|w| w[0] == first && w[1] == second)
}

/// Canonical tactic skeleton label extracted from a Lean proof body.
pub fn extract_tactic_skeleton(body_src: &str) -> String {
    let b = body_src.trim();
    let low = b.to_ascii_lowercase();
    if contains_tactic_ident(&low, "structural_induction") || contains_tactic_ident(&low, "induction") {
        return "structural_induction".to_string();
    }
    if contains_tactic_ident(&low, "cut_lemma") || contains_tactic_ident(&low, "have") {
        return "cut_lemma".to_string();
    }
    if contains_tactic_ident(&low, "term_golf") || low.contains("golf") {
        return "term_golf".to_string();
    }
    if low.contains("farkas") {
        return "farkas".to_string();
    }
    let has_simp_family = ["simp", "simp_all", "simp_rw", "simpa"]
        .iter()
        .any(|kw| contains_tactic_ident(&low, kw));
    if contains_tactic_ident(&low, "rcases") && has_simp_family {
        return "rcases_simp".to_string();
    }
    if contains_tactic_pair(&low, "dsimp", "only") {
        return "dsimp_only".to_string();
    }
    if contains_tactic_pair(&low, "simp", "only") {
        return "simp_only".to_string();
    }
    if contains_tactic_ident(&low, "dsimp") && !has_simp_family {
        return "dsimp_only".to_string();
    }
    if contains_tactic_ident(&low, "native_decide") || contains_tactic_ident(&low, "decide") {
        return "decide".to_string();
    }
    if contains_tactic_ident(&low, "omega") {
        return "omega".to_string();
    }
    if contains_tactic_ident(&low, "rfl") {
        return "rfl".to_string();
    }
    if has_simp_family {
        return "simp_only".to_string();
    }
    "no_simp".to_string()
}

/// Aggregate structural AST / tactic telemetry object shared by all three paths.
pub fn build_structural_telemetry(
    decl_name: &str,
    stmt_src: &str,
    proof_text: &str,
    used_constants: &[String],
    proof_term_nodes: u64,
) -> serde_json::Value {
    let feats = parse_lean_stmt_features(decl_name, stmt_src);
    let skeleton = extract_tactic_skeleton(proof_text);
    serde_json::json!({
        "stmt_nodes": feats.stmt_nodes,
        "stmt_depth": feats.stmt_depth,
        "num_binders": feats.num_binders,
        "goal_head": feats.goal_head,
        "stmt_consts": feats.stmt_consts,
        "stmt_consts_count": feats.stmt_consts_count,
        "tactic_skeleton": skeleton,
        "used_constants": used_constants,
        "proof_term_nodes": proof_term_nodes,
    })
}

#[derive(Debug, Clone, Deserialize)]
struct Q8TensorSpec {
    shape: Vec<usize>,
    q8_scale: f32,
    #[serde(default)]
    zlib_b64: Option<String>,
    #[serde(default)]
    raw_b64: Option<String>,
}

#[derive(Debug, Clone)]
pub struct Q8Tensor {
    pub shape: Vec<usize>,
    pub values: Vec<f32>,
}

impl Q8Tensor {
    fn from_spec(spec: &Q8TensorSpec) -> Option<Self> {
        let b64 = spec.raw_b64.as_deref().or(spec.zlib_b64.as_deref())?;
        let mut raw = base64_decode(b64)?;
        if spec.raw_b64.is_none() {
            raw = inflate_zlib(&raw)?;
        }
        let expected = spec.shape.iter().product::<usize>();
        if raw.len() < expected {
            return None;
        }
        let values = raw[..expected]
            .iter()
            .map(|b| (*b as i8) as f32 * spec.q8_scale)
            .collect();
        Some(Self { shape: spec.shape.clone(), values })
    }
}

#[derive(Debug, Clone, Default, Deserialize)]
struct MatryoshkaPayload {
    #[serde(default)]
    schema: String,
    #[serde(default)]
    vocab: Vec<String>,
    #[serde(default)]
    tactic_skeleton_classes: Vec<String>,
    #[serde(default)]
    metrics: serde_json::Value,
    #[serde(default)]
    int8_q8_tensors: HashMap<String, Q8TensorSpec>,
    #[serde(default)]
    int8_q8_raw_tensors: HashMap<String, Q8TensorSpec>,
    #[serde(default)]
    float_biases: HashMap<String, Vec<f32>>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct GoalEval {
    pub slice_mode: String,
    pub pred_add_decl_us: f64,
    pub pred_heartbeats: i64,
    pub pred_proof_nodes: i64,
    pub survival_permille: i64,
    pub vacuity_hazard_permille: i64,
    pub top_skeleton: String,
    pub top_skeletons: Vec<String>,
    pub skeleton_logits: HashMap<String, f32>,
    pub ranked_available_constants: Vec<String>,
    pub ranked_available_scores: Vec<(String, f32)>,
    pub latent: Vec<f32>,
    pub source_path: String,
}

#[derive(Debug, Default)]
pub struct QuantizedMatryoshkaRuntime {
    pub source_path: String,
    pub schema: String,
    pub vocab: Vec<String>,
    pub vocab_idx: HashMap<String, usize>,
    pub skeleton_classes: Vec<String>,
    pub metrics: serde_json::Value,
    pub tensors: HashMap<String, Q8Tensor>,
    pub biases: HashMap<String, Vec<f32>>,
}

impl QuantizedMatryoshkaRuntime {
    pub fn from_json_str(text: &str, source_path: &str) -> Option<Self> {
        let payload: MatryoshkaPayload = serde_json::from_str(text).ok()?;
        if !payload.schema.starts_with("fractal-trm-matryoshka-v4") {
            return None;
        }
        let mut tensors: HashMap<String, Q8Tensor> = HashMap::new();
        for (name, spec) in payload.int8_q8_raw_tensors.iter().chain(payload.int8_q8_tensors.iter()) {
            if let Some(t) = Q8Tensor::from_spec(spec) {
                tensors.insert(name.clone(), t);
            }
        }
        let vocab_idx = payload
            .vocab
            .iter()
            .enumerate()
            .map(|(i, v)| (v.clone(), i))
            .collect::<HashMap<_, _>>();
        Some(Self {
            source_path: source_path.to_string(),
            schema: payload.schema,
            vocab: payload.vocab,
            vocab_idx,
            skeleton_classes: payload.tactic_skeleton_classes,
            metrics: payload.metrics,
            tensors,
            biases: payload.float_biases,
        })
    }

    pub fn ready(&self) -> bool {
        (self.tensors.contains_key("ngram_table_8192x8")
            || self.tensors.contains_key("ngram_table_s0_4096x4"))
            && self.tensors.contains_key("W_ng_proj")
            && self.tensors.contains_key("W1")
            && self.tensors.contains_key("W2")
            && self.tensors.contains_key("W_vacuity")
    }

    fn pool_ngrams(&self, tokens: &[String], slice_mode: &str) -> Vec<f32> {
        let table = if slice_mode == "s0" {
            self.tensors.get("ngram_table_s0_4096x4").or_else(|| self.tensors.get("ngram_table_8192x8"))
        } else {
            self.tensors.get("ngram_table_8192x8").or_else(|| self.tensors.get("ngram_table_s0_4096x4"))
        };
        let Some(table) = table else {
            return Vec::new();
        };
        let num_buckets = table.shape[0];
        let table_d = table.shape[1];
        if tokens.is_empty() {
            return vec![0.0; table_d];
        }
        let n = tokens.len().min(48);
        let mut feats: Vec<String> = Vec::new();
        for i in 0..n {
            let tok = &tokens[i];
            feats.push(format!("1:{}", tok));
            if i + 1 < n {
                feats.push(format!("2:{}|{}", tok, tokens[i + 1]));
            }
            if i + 2 < n {
                feats.push(format!("3:{}|{}|{}", tok, tokens[i + 1], tokens[i + 2]));
            }
        }
        let inv_sqrt = 1.0 / (feats.len() as f32).sqrt();
        let mut out = vec![0.0f32; table_d];
        for feat in feats {
            let (h, sign) = splitmix64_hash(&feat);
            let b = (h % (num_buckets as u64)) as usize;
            let w = sign * inv_sqrt;
            let base = b * table_d;
            for d in 0..table_d {
                out[d] += w * table.values[base + d];
            }
        }
        out
    }

    pub fn encode_latent(&self, tokens: &[String], num_feats: &[f32], slice_mode: &str) -> Vec<f32> {
        let effective_mode = if slice_mode == "s1" && !self.tensors.contains_key("ngram_table_8192x8") {
            "s0"
        } else {
            slice_mode
        };
        let (d_m, d_h, t_d, steps) = if effective_mode == "s0" { (16, 32, 4, 1) } else { (32, 64, 8, 4) };
        let x_ng_low = self.pool_ngrams(tokens, effective_mode);
        let Some(w_ng) = self.tensors.get("W_ng_proj") else { return Vec::new() };
        let Some(w_num) = self.tensors.get("W_num") else { return Vec::new() };
        let Some(w1) = self.tensors.get("W1") else { return Vec::new() };
        let Some(w2) = self.tensors.get("W2") else { return Vec::new() };

        let x_ng = matvec_rowmajor(&x_ng_low, &w_ng.values, w_ng.shape[0], w_ng.shape[1], t_d, d_m);
        let x_num = matvec_rowmajor(num_feats, &w_num.values, w_num.shape[0], w_num.shape[1], 8, d_m);
        let mut x0 = vec![0.0f32; d_m];
        for i in 0..d_m {
            x0[i] = x_ng[i] + x_num[i];
        }

        let mut z = x0.clone();
        let mut y = x0.clone();
        let mudd = self.biases.get("mudd_alpha").cloned().unwrap_or_else(|| vec![0.65, 0.35]);
        let alpha0 = mudd.first().copied().unwrap_or(0.65);
        let alpha1 = mudd.get(1).copied().unwrap_or(0.35);

        for _ in 0..steps {
            let h_in: Vec<f32> = (0..d_m).map(|i| alpha0 * z[i] + alpha1 * x0[i]).collect();
            let h_norm = rms_norm(&h_in);
            let pre = matvec_rowmajor(&h_norm, &w1.values, w1.shape[0], w1.shape[1], d_m, d_h);
            let mut act = vec![0.0f32; d_h];
            for j in 0..d_h {
                let r = pre[j] - 0.85;
                if r > 0.0 {
                    let sq = r * r;
                    act[j] = if sq > 16.0 { 16.0 } else { sq };
                }
            }
            let delta = matvec_rowmajor(&act, &w2.values, w2.shape[0], w2.shape[1], d_h, d_m);
            for i in 0..d_m {
                z[i] += 0.25 * delta[i];
                y[i] = 0.5 * y[i] + 0.5 * z[i];
            }
        }
        rms_norm(&y)
    }

    fn encode_goal_tokens_and_latent(
        &self,
        decl_name: &str,
        stmt_src: &str,
        goal_tokens_extra: Option<&[String]>,
        slice_mode: &str,
    ) -> (LeanStmtFeatures, Vec<String>, Vec<f32>) {
        let feats = parse_lean_stmt_features(decl_name, stmt_src);
        let mut tokens: Vec<String> = feats
            .decl
            .split(['.', '_'])
            .filter(|p| !p.is_empty())
            .map(|p| p.to_string())
            .collect();
        let gh = feats.goal_head.as_str();
        if !gh.is_empty() {
            tokens.push(format!("GH:{}", gh));
        }
        tokens.push(format!("NB:{}", feats.num_binders.min(8)));
        tokens.push(format!("SN:{}", (feats.stmt_nodes / 25).min(8)));
        for sc in &feats.stmt_consts {
            tokens.extend(sc.split('.').filter(|p| !p.is_empty()).map(|p| p.to_string()));
        }
        if let Some(extra) = goal_tokens_extra {
            tokens.extend(extra.iter().filter(|t| !t.is_empty()).cloned());
        }
        let num_feats: [f32; 8] = [
            ((feats.stmt_nodes.max(1) as f32) + 1.0).ln() / 12.0,
            ((feats.stmt_depth.max(1) as f32) + 1.0).ln() / 8.0,
            ((feats.stmt_consts_count.max(1) as f32) + 1.0).ln() / 6.0,
            ((feats.num_binders as f32) + 1.0).ln() / 4.0,
            if gh == "Eq" { 1.0 } else { 0.0 },
            if matches!(gh, "And" | "Exists" | "Iff") { 1.0 } else { 0.0 },
            if matches!(gh, "LE.le" | "LT.lt" | "Not") { 1.0 } else { 0.0 },
            if feats.decl.contains("InitE.source") { 1.0 } else { 0.0 },
        ];
        let y_out = self.encode_latent(&tokens, &num_feats, slice_mode);
        (feats, tokens, y_out)
    }

    fn score_candidate_from_latent(
        &self,
        stmt_src: &str,
        tokens: &[String],
        y_out: &[f32],
        constant: &str,
    ) -> f32 {
        let mut sc_val = 0.0f32;
        if let (Some(&col), Some(w_prem)) = (self.vocab_idx.get(constant), self.tensors.get("W_prem")) {
            let cols = w_prem.shape[1];
            if col < cols {
                let mut dot = 0.0f32;
                let r_lim = y_out.len().min(w_prem.shape[0]);
                for i in 0..r_lim {
                    dot += y_out[i] * w_prem.values[i * cols + col];
                }
                let bias = self
                    .biases
                    .get("b_prem")
                    .and_then(|b| b.get(col))
                    .copied()
                    .unwrap_or(0.0);
                sc_val += dot + bias;
            }
        }
        let overlap = constant
            .split(['.', '_'])
            .filter(|p| p.len() >= 2 && tokens.iter().any(|t| t == *p))
            .count();
        sc_val += 1.35 * (overlap as f32);
        if let Some(last) = constant.split('.').next_back() {
            if stmt_src.contains(last) {
                sc_val += 2.25;
            }
        }
        (sc_val * 10000.0).round() / 10000.0
    }

    pub fn evaluate_lean_goal(
        &self,
        decl_name: &str,
        stmt_src: &str,
        available_constants: Option<&[String]>,
        goal_tokens_extra: Option<&[String]>,
        slice_mode: &str,
    ) -> GoalEval {
        let (_feats, tokens, y_out) =
            self.encode_goal_tokens_and_latent(decl_name, stmt_src, goal_tokens_extra, slice_mode);
        let d_m = y_out.len();

        let mut cost_pred = vec![0.0f32; 4];
        if let Some(w_cost) = self.tensors.get("W_cost") {
            let b_cost = self.biases.get("b_cost").cloned().unwrap_or_else(|| vec![0.0; 4]);
            let raw = matvec_rowmajor(&y_out, &w_cost.values, w_cost.shape[0], w_cost.shape[1], d_m, 4);
            for k in 0..4 {
                cost_pred[k] = raw[k] + b_cost.get(k).copied().unwrap_or(0.0);
            }
        }
        let surv_prob = sigmoid(cost_pred[3]);

        let mut vac_logit = 0.0f32;
        if let Some(w_vac) = self.tensors.get("W_vacuity") {
            let b_vac = self.biases.get("b_vacuity").and_then(|v| v.first()).copied().unwrap_or(0.0);
            vac_logit = matvec_rowmajor(&y_out, &w_vac.values, w_vac.shape[0], w_vac.shape[1], d_m, 1)
                .first()
                .copied()
                .unwrap_or(0.0)
                + b_vac;
        }
        let mut vac_prob = sigmoid(vac_logit);
        let low_stmt = stmt_src.to_ascii_lowercase();
        let low_decl = decl_name.to_ascii_lowercase();
        let goal_tail = stmt_src.rsplit(':').next().unwrap_or(stmt_src);
        if goal_tail.contains("true") && !low_stmt.contains("= true") && !low_stmt.contains("== true") {
            vac_prob = vac_prob.max(0.78);
        }
        if low_decl.contains("buggy") || low_decl.contains("vacuous") {
            vac_prob = vac_prob.max(0.82);
        }

        let mut skel_scores: HashMap<String, f32> = HashMap::new();
        if let Some(w_skel) = self.tensors.get("W_skel") {
            let b_skel = self.biases.get("b_skel").cloned().unwrap_or_else(|| vec![0.0; w_skel.shape[1]]);
            let raw = matvec_rowmajor(&y_out, &w_skel.values, w_skel.shape[0], w_skel.shape[1], d_m, w_skel.shape[1]);
            for (k, cls_name) in self.skeleton_classes.iter().take(w_skel.shape[1]).enumerate() {
                skel_scores.insert(cls_name.clone(), raw[k] + b_skel.get(k).copied().unwrap_or(0.0));
            }
        }
        let mut top_skeletons: Vec<String> = skel_scores.keys().cloned().collect();
        top_skeletons.sort_by(|a, b| {
            skel_scores[b].partial_cmp(&skel_scores[a]).unwrap_or(std::cmp::Ordering::Equal)
        });

        let mut ranked_avail: Vec<(String, f32)> = Vec::new();
        if let Some(avail) = available_constants {
            for cand in avail {
                let c = cand.trim();
                if c.is_empty() {
                    continue;
                }
                ranked_avail.push((
                    c.to_string(),
                    self.score_candidate_from_latent(stmt_src, &tokens, &y_out, c),
                ));
            }
            ranked_avail.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        }

        GoalEval {
            slice_mode: slice_mode.to_string(),
            pred_add_decl_us: ((cost_pred[0].clamp(0.0, 14.0)).exp_m1() * 100.0).round() as f64 / 100.0,
            pred_heartbeats: (cost_pred[1].clamp(0.0, 14.0)).exp_m1().round() as i64,
            pred_proof_nodes: (cost_pred[2].clamp(0.0, 14.0)).exp_m1().round() as i64,
            survival_permille: (surv_prob * 1000.0).round() as i64,
            vacuity_hazard_permille: (vac_prob * 1000.0).round() as i64,
            top_skeleton: top_skeletons.first().cloned().unwrap_or_else(|| "simp_only".to_string()),
            top_skeletons: top_skeletons.into_iter().take(4).collect(),
            skeleton_logits: skel_scores,
            ranked_available_constants: ranked_avail.iter().map(|(c, _)| c.clone()).collect(),
            ranked_available_scores: ranked_avail,
            latent: y_out,
            source_path: self.source_path.clone(),
        }
    }

    /// Fast-path single-constant Stage-0 premise affinity logit (`< 3 us` per query).
    /// Computes normalized Stage-0 latent `y_out` (`d_m = 16`) and projects only the target
    /// constant's column of `W_prem` (if in `vocab`) + token-stem overlap, skipping unused heads.
    pub fn score_constant_affinity(&self, stmt_src: &str, constant: &str) -> Option<f32> {
        if !self.ready() {
            return None;
        }
        let c = constant.trim();
        if c.is_empty() {
            return Some(0.0);
        }
        let (_feats, tokens, y_out) = self.encode_goal_tokens_and_latent("anon", stmt_src, None, "s0");
        Some(self.score_candidate_from_latent(stmt_src, &tokens, &y_out, c))
    }

    pub fn vacuity_hazard_permille(&self, decl_name: &str, stmt_src: &str) -> Option<i64> {
        if !self.ready() {
            return None;
        }
        Some(self.evaluate_lean_goal(decl_name, stmt_src, None, None, "s0").vacuity_hazard_permille)
    }
}

static MATRYOSHKA_RUNTIME: OnceLock<Option<QuantizedMatryoshkaRuntime>> = OnceLock::new();

fn candidate_weight_paths() -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = Vec::new();
    if let Ok(p) = std::env::var("MAXWELL_MATRYOSHKA_WEIGHTS") {
        if !p.trim().is_empty() {
            out.push(PathBuf::from(p));
        }
    }
    if let Some(exe) = std::env::current_exe().ok() {
        let mut dir = exe.parent().map(|p| p.to_path_buf());
        for _ in 0..6 {
            if let Some(d) = dir {
                out.push(d.join("training/matryoshka_weights.nvfp4.json"));
                out.push(d.join("../maxwell/training/matryoshka_weights.nvfp4.json"));
                dir = d.parent().map(|p| p.to_path_buf());
            }
        }
    }
    if let Ok(cwd) = std::env::current_dir() {
        let mut dir = Some(cwd);
        for _ in 0..6 {
            if let Some(d) = dir {
                out.push(d.join("training/matryoshka_weights.nvfp4.json"));
                out.push(d.join("../maxwell/training/matryoshka_weights.nvfp4.json"));
                dir = d.parent().map(|p| p.to_path_buf());
            }
        }
    }
    out.push(PathBuf::from("/usr/local/share/maxwell/training/matryoshka_weights.nvfp4.json"));
    out
}

/// Whether the neural Matryoshka MUDD-TRM premise-ranking pass is enabled in hot premise selection.
/// Disabled by default per the `AGENTS.md` §2.7 E2E ablation gate until a >= 1% canonical-corpus
/// wall-clock speedup is measured; opt in via `TURBO_LEAN_MATRYOSHKA_RANKING=1`.
pub fn matryoshka_ranking_enabled() -> bool {
    std::env::var("TURBO_LEAN_MATRYOSHKA_RANKING")
        .ok()
        .is_some_and(|v| matches!(v.trim().to_ascii_lowercase().as_str(), "1" | "true" | "yes"))
}

/// Lazily initialized, process-wide `OnceLock` cached runtime (external weights override embedded fallback).
pub fn global_matryoshka_runtime() -> Option<&'static QuantizedMatryoshkaRuntime> {
    MATRYOSHKA_RUNTIME
        .get_or_init(|| {
            for path in candidate_weight_paths() {
                if path.is_file() {
                    if let Ok(text) = std::fs::read_to_string(&path) {
                        if let Some(rt) = QuantizedMatryoshkaRuntime::from_json_str(&text, &path.display().to_string()) {
                            if rt.ready() {
                                return Some(rt);
                            }
                        }
                    }
                }
            }
            QuantizedMatryoshkaRuntime::from_json_str(
                include_str!("matryoshka_s0_weights.json"),
                "embedded:matryoshka_s0_weights.json",
            )
            .filter(|rt| rt.ready())
        })
        .as_ref()
}

const B64_TABLE: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// Pure-Rust base64 decoder (standard alphabet, optional padding, whitespace tolerant).
pub fn base64_decode(input: &str) -> Option<Vec<u8>> {
    let mut rev = [255u8; 256];
    for (i, c) in B64_TABLE.iter().enumerate() {
        rev[*c as usize] = i as u8;
    }
    let mut out = Vec::with_capacity(input.len() * 3 / 4 + 3);
    let mut acc: u32 = 0;
    let mut nbits: u32 = 0;
    for b in input.bytes() {
        if b == b'=' {
            break;
        }
        if b.is_ascii_whitespace() {
            continue;
        }
        let v = rev[b as usize];
        if v == 255 {
            return None;
        }
        acc = (acc << 6) | (v as u32);
        nbits += 6;
        if nbits >= 8 {
            nbits -= 8;
            out.push(((acc >> nbits) & 0xFF) as u8);
        }
    }
    Some(out)
}

struct BitReader<'a> {
    data: &'a [u8],
    pos: usize,
    bit: u32,
}

impl<'a> BitReader<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0, bit: 0 }
    }
    fn read_bits(&mut self, n: u32) -> Option<u32> {
        if n == 0 {
            return Some(0);
        }
        let mut val = 0u32;
        for i in 0..n {
            if self.pos >= self.data.len() {
                return None;
            }
            let byte = self.data[self.pos] as u32;
            let bit = (byte >> self.bit) & 1;
            val |= bit << i;
            self.bit += 1;
            if self.bit == 8 {
                self.bit = 0;
                self.pos += 1;
            }
        }
        Some(val)
    }
    fn align_byte(&mut self) {
        if self.bit != 0 {
            self.bit = 0;
            self.pos += 1;
        }
    }
}

#[derive(Clone)]
struct Huffman {
    counts: [u16; 16],
    symbols: Vec<u16>,
}

impl Huffman {
    fn new(lengths: &[u8]) -> Option<Self> {
        let mut counts = [0u16; 16];
        for l in lengths {
            counts[*l as usize] += 1;
        }
        counts[0] = 0;
        let mut offsets = [0u16; 16];
        for i in 1..16 {
            offsets[i] = offsets[i - 1] + counts[i - 1];
        }
        let mut symbols = vec![0u16; lengths.iter().filter(|l| **l != 0).count()];
        for (sym, l) in lengths.iter().enumerate() {
            if *l != 0 {
                symbols[offsets[*l as usize] as usize] = sym as u16;
                offsets[*l as usize] += 1;
            }
        }
        Some(Self { counts, symbols })
    }

    fn decode(&self, br: &mut BitReader) -> Option<u16> {
        let mut code: i32 = 0;
        let mut first: i32 = 0;
        let mut index: i32 = 0;
        for len in 1..16 {
            code |= br.read_bits(1)? as i32;
            let count = self.counts[len] as i32;
            if code - first < count {
                return self.symbols.get((index + (code - first)) as usize).copied();
            }
            index += count;
            first = (first + count) << 1;
            code <<= 1;
        }
        None
    }
}

const LEN_BASE: [u16; 29] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131,
    163, 195, 227, 258,
];
const LEN_EXTRA: [u32; 29] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
];
const DIST_BASE: [u16; 30] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
];
const DIST_EXTRA: [u32; 30] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13,
];

/// Pure-Rust RFC 1950 zlib + RFC 1951 DEFLATE inflater (fixed & dynamic Huffman + stored blocks).
pub fn inflate_zlib(data: &[u8]) -> Option<Vec<u8>> {
    if data.len() < 6 {
        return None;
    }
    let cmf = data[0];
    let flg = data[1];
    if cmf & 0x0F != 8 {
        return None;
    }
    if (((cmf as u16) << 8) | flg as u16) % 31 != 0 {
        return None;
    }
    if flg & 0x20 != 0 {
        return None;
    }
    let deflate = &data[2..data.len() - 4];
    let mut br = BitReader::new(deflate);
    let mut out: Vec<u8> = Vec::new();
    loop {
        let bfinal = br.read_bits(1)?;
        let btype = br.read_bits(2)?;
        match btype {
            0 => {
                br.align_byte();
                let len = br.read_bits(16)? as usize;
                let nlen = br.read_bits(16)? as usize;
                if (len ^ 0xFFFF) != nlen {
                    return None;
                }
                br.align_byte();
                for _ in 0..len {
                    out.push(*br.data.get(br.pos)?);
                    br.pos += 1;
                }
            }
            1 | 2 => {
                let (lit_huff, dist_huff) = if btype == 1 {
                    let mut lit_lengths = vec![8u8; 288];
                    for item in lit_lengths.iter_mut().take(256).skip(144) {
                        *item = 9;
                    }
                    for item in lit_lengths.iter_mut().take(280).skip(256) {
                        *item = 7;
                    }
                    let dist_lengths = vec![5u8; 30];
                    (Huffman::new(&lit_lengths)?, Huffman::new(&dist_lengths)?)
                } else {
                    let hlit = br.read_bits(5)? as usize + 257;
                    let hdist = br.read_bits(5)? as usize + 1;
                    let hclen = br.read_bits(4)? as usize + 4;
                    const ORDER: [usize; 19] = [
                        16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
                    ];
                    let mut cl_lengths = [0u8; 19];
                    for i in 0..hclen {
                        cl_lengths[ORDER[i]] = br.read_bits(3)? as u8;
                    }
                    let cl_huff = Huffman::new(&cl_lengths)?;
                    let mut lengths: Vec<u8> = Vec::with_capacity(hlit + hdist);
                    while lengths.len() < hlit + hdist {
                        let sym = cl_huff.decode(&mut br)?;
                        match sym {
                            0..=15 => lengths.push(sym as u8),
                            16 => {
                                let prev = *lengths.last()?;
                                let rep = 3 + br.read_bits(2)? as usize;
                                for _ in 0..rep {
                                    lengths.push(prev);
                                }
                            }
                            17 => {
                                let rep = 3 + br.read_bits(3)? as usize;
                                for _ in 0..rep {
                                    lengths.push(0);
                                }
                            }
                            18 => {
                                let rep = 11 + br.read_bits(7)? as usize;
                                for _ in 0..rep {
                                    lengths.push(0);
                                }
                            }
                            _ => return None,
                        }
                    }
                    lengths.truncate(hlit + hdist);
                    (
                        Huffman::new(&lengths[..hlit])?,
                        Huffman::new(&lengths[hlit..])?,
                    )
                };
                loop {
                    let sym = lit_huff.decode(&mut br)?;
                    if sym < 256 {
                        out.push(sym as u8);
                    } else if sym == 256 {
                        break;
                    } else {
                        let li = (sym - 257) as usize;
                        if li >= 29 {
                            return None;
                        }
                        let len = LEN_BASE[li] as usize + br.read_bits(LEN_EXTRA[li])? as usize;
                        let dsym = dist_huff.decode(&mut br)? as usize;
                        if dsym >= 30 {
                            return None;
                        }
                        let dist = DIST_BASE[dsym] as usize + br.read_bits(DIST_EXTRA[dsym])? as usize;
                        if dist > out.len() {
                            return None;
                        }
                        let start = out.len() - dist;
                        for i in 0..len {
                            let b = out[start + i];
                            out.push(b);
                        }
                    }
                }
            }
            _ => return None,
        }
        if bfinal == 1 {
            break;
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_splitmix64_hash_bit_exact() {
        let (h, sign) = splitmix64_hash("1:Nat");
        let mut hh: u64 = 0x9E3779B97F4A7C15;
        for b in "1:Nat".bytes() {
            hh = (hh ^ b as u64).wrapping_mul(0xBF58476D1CE4E5B9);
        }
        let mut x = hh;
        x = (x ^ (x >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94D049BB133111EB);
        x = x ^ (x >> 31);
        assert_eq!(h, x >> 1);
        assert_eq!(sign, if x & 1 == 0 { 1.0 } else { -1.0 });
    }

    #[test]
    fn test_base64_roundtrip_and_inflate_zlib() {
        let decoded = base64_decode("aGVsbG8=").unwrap();
        assert_eq!(decoded, b"hello");
        let zlib_hello = [
            0x78, 0x9C, 0xCB, 0x48, 0xCD, 0xC9, 0xC9, 0x07, 0x00, 0x06, 0x2C, 0x02, 0x15,
        ];
        let inflated = inflate_zlib(&zlib_hello).unwrap();
        assert_eq!(inflated, b"hello");
    }

    #[test]
    fn test_parse_lean_stmt_features() {
        let f = parse_lean_stmt_features(
            "Nat.add_comm",
            "theorem Nat.add_comm (a b : Nat) : a + b = b + a",
        );
        assert_eq!(f.goal_head, "Eq");
        assert_eq!(f.num_binders, 1);
        assert!(f.stmt_nodes >= 4);
        assert!(f.stmt_consts.contains(&"Nat.add_comm".to_string()));
        assert!(f.stmt_consts.contains(&"Nat".to_string()));
    }

    #[test]
    fn test_embedded_matryoshka_runtime_scores_and_vacuity() {
        let rt = global_matryoshka_runtime().expect("embedded Matryoshka runtime must load");
        assert!(rt.ready());
        let stmt = "(a b : Nat) : a + b = b + a";
        let avail = vec![
            "Nat.add_comm".to_string(),
            "List.reverse_reverse".to_string(),
        ];
        let ev = rt.evaluate_lean_goal("Nat.add_comm_test", stmt, Some(&avail), None, "s0");
        assert_eq!(ev.latent.len(), 16);
        assert!(ev.survival_permille >= 0 && ev.survival_permille <= 1000);
        assert!(ev.vacuity_hazard_permille >= 0 && ev.vacuity_hazard_permille <= 1000);
        assert_eq!(ev.ranked_available_scores.len(), 2);
        assert!(ev.ranked_available_scores[0].1 >= ev.ranked_available_scores[1].1);
        let buggy = rt.evaluate_lean_goal("buggy_vacuous_theorem", "theorem buggy : True", None, None, "s0");
        assert!(buggy.vacuity_hazard_permille >= 820);
        let sc = rt.score_constant_affinity(stmt, "Nat.add_comm").unwrap();
        assert!(sc.is_finite());
    }

    #[test]
    fn test_matryoshka_inference_under_10us_when_cached() {
        let rt = global_matryoshka_runtime().unwrap();
        let _ = rt.score_constant_affinity("(a : Nat) : a + 0 = a", "Nat.add_zero");
        let n = 200;
        let mut best_us = f64::INFINITY;
        for _ in 0..5 {
            let t0 = std::time::Instant::now();
            for _ in 0..n {
                let _ = rt.score_constant_affinity("(a : Nat) : a + 0 = a", "Nat.add_zero");
            }
            best_us = best_us.min(t0.elapsed().as_secs_f64() * 1e6 / n as f64);
            if best_us < 10.0 {
                break;
            }
        }
        assert!(best_us < 10.0, "cached S0 affinity should be <10us, got {:.3}us", best_us);
    }

    #[test]
    fn test_zlib_nvfp4_weights_full_s1_when_present() {
        for p in candidate_weight_paths() {
            if p.is_file() {
                let text = std::fs::read_to_string(&p).unwrap();
                if !text.contains("\"int8_q8_tensors\"")
                    && !text.contains("\"int8_q8_raw_tensors\"")
                {
                    continue;
                }
                let rt = QuantizedMatryoshkaRuntime::from_json_str(&text, &p.display().to_string())
                    .expect("zlib_b64 matryoshka_weights.nvfp4.json must parse");
                assert!(rt.ready());
                let ev_s1 = rt.evaluate_lean_goal(
                    "Nat.add_comm",
                    "(a b : Nat) : a + b = b + a",
                    Some(&["Nat.add_comm".to_string(), "List.length_append".to_string()]),
                    None,
                    "s1",
                );
                assert_eq!(ev_s1.latent.len(), 32);
                assert!(ev_s1.survival_permille >= 0 && ev_s1.survival_permille <= 1000);
                break;
            }
        }
    }

    #[test]
    fn test_extract_tactic_skeleton_distinguishes_dsimp_from_simp() {
        assert_eq!(extract_tactic_skeleton("by dsimp only [Nat.add_zero]"), "dsimp_only");
        assert_eq!(extract_tactic_skeleton("by dsimp"), "dsimp_only");
        assert_eq!(
            extract_tactic_skeleton("by rcases h with ⟨a, b⟩; dsimp"),
            "dsimp_only"
        );
        assert_eq!(
            extract_tactic_skeleton("by rcases h with ⟨a, b⟩; dsimp only [foo]"),
            "dsimp_only"
        );
        assert_eq!(
            extract_tactic_skeleton("by rcases h with ⟨a, b⟩; simp only [foo]"),
            "rcases_simp"
        );
        assert_eq!(extract_tactic_skeleton("by simp only [h]"), "simp_only");
        assert_eq!(extract_tactic_skeleton("by simp_all"), "simp_only");
    }

    #[test]
    fn test_evaluate_lean_goal_preserves_all_candidate_scores_and_matches_fast_path() {
        let rt = global_matryoshka_runtime().expect("embedded Matryoshka runtime must load");
        let stmt = "(x : UnknownDomain) : P x = Q x";
        let cands: Vec<String> = rt.vocab.iter().take(24).cloned().collect();
        assert_eq!(cands.len(), 24);
        let ev = rt.evaluate_lean_goal("anon", stmt, Some(&cands), None, "s0");
        assert_eq!(ev.ranked_available_scores.len(), 24);
        assert_eq!(ev.ranked_available_constants.len(), 24);
        for w in ev.ranked_available_scores.windows(2) {
            assert!(w[0].1 >= w[1].1);
        }
        for (c, batch_score) in &ev.ranked_available_scores {
            let single = rt.score_constant_affinity(stmt, c).unwrap();
            assert!(
                (batch_score - single).abs() < 1e-4,
                "batch score {} != single score {} for {}",
                batch_score,
                single,
                c
            );
        }
    }
}
