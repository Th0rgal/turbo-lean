pub(super) fn insert_allow_sorry_fields(
    out_json: &mut serde_json::Value,
    allow_sorry: bool,
    used_sorry: bool,
    sorry_decls: &[String],
) {
    if allow_sorry {
        if let Some(obj) = out_json.as_object_mut() {
            obj.insert("allow_sorry".to_string(), serde_json::Value::Bool(true));
            obj.insert(
                "used_sorry".to_string(),
                serde_json::Value::Bool(used_sorry),
            );
            obj.insert(
                "sorry_count".to_string(),
                serde_json::json!(sorry_decls.len()),
            );
            obj.insert("sorry_decls".to_string(), serde_json::json!(sorry_decls));
        }
    }
}

fn parse_last_int_literal(s: &str) -> Option<i128> {
    s.split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .filter_map(|raw| {
            let tok = raw.replace('_', "");
            if let Some(h) = tok.strip_prefix("0x").or_else(|| tok.strip_prefix("0X")) {
                i128::from_str_radix(h, 16).ok()
            } else {
                tok.parse::<i128>().ok()
            }
        })
        .next_back()
}

fn strip_trailing_type_ascription(expr: &str) -> &str {
    let trimmed = expr.trim();
    [
        " : Prop",
        " : Type",
        " : Bool",
        " : Nat",
        " : Int",
        " : UInt64",
    ]
    .into_iter()
    .find_map(|s| trimmed.strip_suffix(s))
    .unwrap_or(trimmed)
    .trim()
}

/// Parse Lean 4 `type mismatch` error messages into structured `mismatch_diagnostics` JSON objects
/// containing `term`, `inferred_type`, `expected_type`, `inferred_rhs`, `expected_rhs`, and `numeric_delta`.
/// This allows LLM agents to immediately compute exact offset shifts (e.g., `+14` on EVM `pc` or stack depths)
/// in a single turn instead of burning 8–10 turns of trial-and-error.
pub fn extract_mismatch_diagnostics(err_text: &str) -> Vec<serde_json::Value> {
    let mut out = Vec::new();
    for chunk in err_text.split("type mismatch").skip(1) {
        let Some((term_part, after_has_type)) = chunk.split_once("has type") else {
            continue;
        };
        let Some((inferred_part, after_expected)) =
            after_has_type.split_once("but is expected to have type")
        else {
            continue;
        };
        let mut expected_lines = Vec::new();
        for line in after_expected.lines().map(str::trim) {
            if (line.is_empty() && !expected_lines.is_empty())
                || line.starts_with("<zygote")
                || line.contains(": error:")
                || line.contains(": warning:")
                || line.starts_with("---")
            {
                break;
            }
            if !line.is_empty() {
                expected_lines.push(line);
            }
        }
        let join_lines = |s: &str| {
            s.lines()
                .map(str::trim)
                .filter(|l| !l.is_empty())
                .collect::<Vec<_>>()
                .join(" ")
        };
        let (term, inferred_type, expected_type) = (
            join_lines(term_part),
            join_lines(inferred_part),
            expected_lines.join(" "),
        );
        if inferred_type.is_empty() || expected_type.is_empty() {
            continue;
        }
        let (inf_clean, exp_clean) = (
            strip_trailing_type_ascription(&inferred_type),
            strip_trailing_type_ascription(&expected_type),
        );
        let inf_rhs = inf_clean
            .rsplit_once('=')
            .map(|(_, r)| r.trim().to_string());
        let exp_rhs = exp_clean
            .rsplit_once('=')
            .map(|(_, r)| r.trim().to_string());
        let numeric_delta = match (&inf_rhs, &exp_rhs) {
            (Some(ir), Some(er)) => parse_last_int_literal(ir)
                .zip(parse_last_int_literal(er))
                .map(|(vi, ve)| ve - vi),
            _ => parse_last_int_literal(inf_clean)
                .zip(parse_last_int_literal(exp_clean))
                .filter(|(vi, ve)| vi != ve)
                .map(|(vi, ve)| ve - vi),
        };
        out.push(serde_json::json!({
            "term": term,
            "inferred_type": inferred_type,
            "expected_type": expected_type,
            "inferred_rhs": inf_rhs,
            "expected_rhs": exp_rhs,
            "numeric_delta": numeric_delta,
        }));
    }
    out
}

pub(super) fn format_mismatch_diagnostics_summary(diags: &[serde_json::Value]) -> String {
    let Some(d0) = diags.first() else {
        return String::new();
    };
    let term = d0.get("term").and_then(|v| v.as_str()).unwrap_or("?");
    let inf = d0
        .get("inferred_rhs")
        .or_else(|| d0.get("inferred_type"))
        .and_then(|v| v.as_str())
        .unwrap_or("?");
    let exp = d0
        .get("expected_rhs")
        .or_else(|| d0.get("expected_type"))
        .and_then(|v| v.as_str())
        .unwrap_or("?");
    let token_saver_line = if let Some(delta) = d0.get("numeric_delta").and_then(|v| v.as_i64()) {
        format!(
            "\n[TOKEN-SAVER FIX HINT] term=`{}` expected_rhs={} inferred_rhs={} numeric_delta={:+}",
            term, exp, inf, delta
        )
    } else {
        format!(
            "\n[TOKEN-SAVER FIX HINT] term=`{}` expected=`{}` inferred=`{}`",
            term, exp, inf
        )
    };
    serde_json::to_string(diags)
        .map(|j| {
            format!(
                "{}\n[turbo-lean mismatch_diagnostics] {}",
                token_saver_line, j
            )
        })
        .unwrap_or(token_saver_line)
}
