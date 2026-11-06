use anyhow::{bail, Context, Result};
use serde_json::{json, Value};
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use super::audit_spec::{
    audit_spec_file_or_source_with_policy, extract_all_lean_theorems, extract_local_def_unfoldings,
    inline_stmt_let_bindings, replace_ident_boundary, AuditSpecPolicyConfig,
};
use super::{
    is_known_binder_value_type, split_top_level_colon, split_top_level_implications,
    strip_lean_comments, ExtractedDecl,
};
use crate::splitter::{
    audit_hygiene, canonicalize_lean_name, decl_name_matches_target, extract_public_signature,
    qualified_decl_name, skip_lean_lexeme, ScopeFrame, ScopeKind,
};

const UNCHECKED: &[&str] = &[
    "transitive imported axioms (statement text is not elaborated and imports are not walked)",
    "semantic domain intent, including whether hypotheses are logically independent",
    "unmodeled FFI, native, and environment boundaries",
    "proof-term completeness beyond source tokens (sorry, admit, axiom, native_decide, extern)",
    "instance binders and section variable/include context are syntactic only; nonstandard ones are not evaluated",
];

const TOTAL_INSTANCE_HEADS: &[&str] = &[
    "BEq",
    "DecidableEq",
    "Hashable",
    "LE",
    "LT",
    "Ord",
    "Repr",
    "ToString",
];

const PRIMITIVE_LAWFUL_TYPES: &[&str] = &[
    "Bool", "Char", "Int", "Nat", "String", "UInt8", "UInt16", "UInt32", "UInt64", "USize",
];

const RESERVED_INSTANCE_AND_TYPE_NAMES: &[&str] = &[
    "BEq",
    "DecidableEq",
    "DecidablePred",
    "DecidableRel",
    "Hashable",
    "LE",
    "LT",
    "Ord",
    "Repr",
    "ToString",
    "LawfulBEq",
    "EquivBEq",
    "LawfulHashable",
    "Bool",
    "Char",
    "Int",
    "Nat",
    "String",
    "UInt8",
    "UInt16",
    "UInt32",
    "UInt64",
    "USize",
    "Unit",
    "PUnit",
    "True",
    "False",
    "Empty",
    "PEmpty",
    "Fin",
    "BitVec",
    "Word256",
    "UInt256",
    "Uint256",
    "Int256",
    "List",
    "Array",
    "Option",
    "Prod",
    "PProd",
    "Sigma",
    "PSigma",
    "Exists",
    "Subtype",
    "ULift",
    "PLift",
    "Thunk",
    "Fact",
    "Nonempty",
    "Inhabited",
    "ByteArray",
    "StorageKey",
    "ContractState",
];

pub fn run_spec_card_command(
    files: &[PathBuf],
    decl_filter: Option<&str>,
    json_mode: bool,
    policy_override: Option<&str>,
    config_override: Option<&Path>,
    public_only: bool,
) -> Result<()> {
    if let Err(err) = (|| -> Result<()> {
        anyhow::ensure!(!files.is_empty(), "No files provided to spec-card");
        for file in files {
            anyhow::ensure!(
                fs::symlink_metadata(file).is_ok(),
                "Failed to read {}: path does not exist",
                file.display()
            );
        }
        if let Some(policy) = policy_override {
            AuditSpecPolicyConfig::try_from_preset(policy)?;
        }
        if let Some(path) = config_override {
            AuditSpecPolicyConfig::try_load_for_target(Path::new(""), None, Some(path), &[], &[])?;
        }
        Ok(())
    })() {
        return emit_spec_card_error(json_mode, &format!("{err:#}"));
    }
    let started = Instant::now();
    let mut sources = Vec::new();
    for file in files {
        match load_sources(file) {
            Ok(loaded) => sources.extend(loaded),
            Err(err) => return emit_spec_card_error(json_mode, &format!("{err:#}")),
        }
    }
    sources.sort_by(|left, right| left.0.cmp(&right.0));
    sources.dedup_by(|left, right| left.0 == right.0);
    let mut cards = Vec::new();
    let mut matched = 0usize;
    let mut hidden_private = 0usize;
    let mut hygiene_dirty = false;
    let mut extraction_incomplete = false;
    let mut all_audits_ok = true;
    let mut any_audit_error = false;
    let mut resolved_policies = Vec::with_capacity(sources.len());
    for (path, src) in &sources {
        let policy = match AuditSpecPolicyConfig::try_load_for_target(
            path,
            policy_override,
            config_override,
            &[],
            &[],
        ) {
            Ok(policy) => policy,
            Err(err) => return emit_spec_card_error(json_mode, &format!("{err:#}")),
        };
        resolved_policies.push(policy.policy.clone());
        let audit = audit_spec_file_or_source_with_policy(path, Some(src), None, &policy);
        if audit.get("status").and_then(Value::as_str) == Some("error") {
            any_audit_error = true;
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
        if public_only && !visibility_known {
            extraction_incomplete = true;
        }
        let local_defs = extract_local_def_unfoldings(&clean);
        let prop_local_defs = extract_prop_local_defs(&clean);
        let details = audit
            .get("specs")
            .and_then(Value::as_array)
            .cloned()
            .unwrap_or_default();
        let all_decls = extract_all_lean_theorems(src, None);
        let scan = scan_decl_extras(src);
        if scan.has_malformed_scope || scan.has_unmodeled_syntax_env {
            extraction_incomplete = true;
        }
        let aligned_extras = all_decls.len() == scan.extras.len();
        if !aligned_extras {
            extraction_incomplete = true;
        }
        for (decl_idx, decl) in all_decls.into_iter().enumerate() {
            let extra = aligned_extras.then(|| &scan.extras[decl_idx]);
            let effective_name = extra.map_or(decl.name.as_str(), |row| row.name.as_str());
            let matches_filter = match decl_filter {
                Some(target) if !target.is_empty() && target != "auto" => {
                    decl_name_matches_target(effective_name, target)
                        || decl_name_matches_target(&decl.name, target)
                }
                _ => true,
            };
            if !matches_filter {
                continue;
            }
            matched += 1;
            let detail = details.iter().find(|row| {
                row.get("decl")
                    .and_then(Value::as_str)
                    .is_some_and(|name| name == effective_name || name == decl.name)
            });
            let visibility = visibility_of(
                effective_name,
                &public_names,
                visibility_known,
                public_sig.is_module,
                extra,
                scan.has_malformed_scope,
            );
            if public_only && visibility != "public" {
                if visibility == "unresolved"
                    || extra.is_none()
                    || extra.is_some_and(|row| {
                        row.saw_malformed_prefix
                            || row.saw_unparsed_binder
                            || row.saw_unparsed_telescope
                    })
                {
                    extraction_incomplete = true;
                }
                hidden_private += 1;
                continue;
            }
            if detail.is_none() || !detail_is_audit_ok(detail) {
                all_audits_ok = false;
            }
            let ctx = FileCardCtx {
                path,
                local_defs: &local_defs,
                prop_local_defs: &prop_local_defs,
                hygiene: &hygiene,
                audit: &audit,
                has_unmodeled_instance_env: scan.has_unmodeled_instance_env,
                has_unmodeled_syntax_env: scan.has_unmodeled_syntax_env,
                has_shadowed_value_types: scan.has_shadowed_value_types,
            };
            cards.push(card_for(
                &ctx,
                &decl,
                effective_name,
                visibility,
                extra,
                detail,
            ));
        }
    }
    let policy_mixed = resolved_policies
        .as_slice()
        .windows(2)
        .any(|pair| pair[0] != pair[1]);
    let policy_name = match resolved_policies.first() {
        Some(first) if !policy_mixed => first.clone(),
        Some(_) => "mixed".to_string(),
        None => policy_override.unwrap_or("default").to_string(),
    };
    let elapsed_ms = (started.elapsed().as_secs_f64() * 1000.0 * 1000.0).round() / 1000.0;
    let filter_miss = decl_filter.is_some() && matched == 0;
    let public_miss = public_only && matched > 0 && cards.is_empty();
    let incomplete = extraction_incomplete
        || cards.iter().any(|card| {
            card.pointer("/contract/extraction_complete")
                .and_then(Value::as_bool)
                == Some(false)
        });
    let all_cards_tight = cards
        .iter()
        .all(|card| card.get("verdict").and_then(Value::as_str) == Some("TIGHT"));
    let ok = !any_audit_error
        && all_audits_ok
        && all_cards_tight
        && !hygiene_dirty
        && !filter_miss
        && !public_miss
        && !incomplete
        && !policy_mixed;
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

fn emit_spec_card_error(json_mode: bool, message: &str) -> Result<()> {
    if json_mode {
        println!(
            "{}",
            serde_json::to_string_pretty(&json!({
                "status": "error",
                "ok": false,
                "analysis_tier": "source_syntactic",
                "unchecked_boundaries": UNCHECKED,
                "error": message,
                "summary": {
                    "files": 0,
                    "cards": 0,
                    "matched_decls": 0,
                    "hidden_by_public_only": 0,
                    "audit_ok": false,
                    "hygiene_clean": false,
                    "extraction_complete": false,
                    "policy": "unknown",
                    "elapsed_ms": 0.0,
                },
                "cards": [],
            }))?
        );
        std::process::exit(1);
    }
    bail!("{message}");
}

fn detail_is_audit_ok(detail: Option<&Value>) -> bool {
    detail.is_some_and(|row| {
        row.get("vacuous").and_then(Value::as_bool) != Some(true)
            && row.get("trivial").and_then(Value::as_bool) != Some(true)
            && row.get("tight").and_then(Value::as_bool) == Some(true)
    })
}

fn load_sources(file: &Path) -> Result<Vec<(PathBuf, String)>> {
    let meta =
        fs::symlink_metadata(file).with_context(|| format!("Failed to read {}", file.display()))?;
    anyhow::ensure!(
        !meta.file_type().is_symlink(),
        "Refusing to follow symlink {}",
        file.display()
    );
    if file.is_dir() {
        let paths = collect_source_paths(file)?;
        if paths.is_empty() {
            bail!("No readable Lean files found in {}", file.display());
        }
        let mut sources = Vec::with_capacity(paths.len());
        for path in paths {
            let src = fs::read_to_string(&path)
                .with_context(|| format!("Failed to read {}", path.display()))?;
            sources.push((path, src));
        }
        sources.sort_by(|left, right| left.0.cmp(&right.0));
        return Ok(sources);
    }
    let src =
        fs::read_to_string(file).with_context(|| format!("Failed to read {}", file.display()))?;
    let mut sources = vec![(file.to_path_buf(), src)];
    let sub_dir = file.with_extension("");
    if let Ok(sub_meta) = fs::symlink_metadata(&sub_dir) {
        anyhow::ensure!(
            !sub_meta.file_type().is_symlink(),
            "Refusing to follow symlink {}",
            sub_dir.display()
        );
        if sub_meta.is_dir() {
            for path in collect_source_paths(&sub_dir)? {
                let sub_src = fs::read_to_string(&path)
                    .with_context(|| format!("Failed to read {}", path.display()))?;
                sources.push((path, sub_src));
            }
            sources.sort_by(|left, right| left.0.cmp(&right.0));
        }
    }
    Ok(sources)
}

fn collect_source_paths(root: &Path) -> Result<Vec<PathBuf>> {
    let root_meta =
        fs::symlink_metadata(root).with_context(|| format!("Failed to read {}", root.display()))?;
    anyhow::ensure!(
        !root_meta.file_type().is_symlink(),
        "Refusing to follow symlink {}",
        root.display()
    );
    let mut out = Vec::new();
    let mut stack = vec![(root.to_path_buf(), 0usize)];
    while let Some((dir, depth)) = stack.pop() {
        let entries =
            fs::read_dir(&dir).with_context(|| format!("Failed to read {}", dir.display()))?;
        for entry in entries {
            let entry = entry.with_context(|| format!("Failed to read {}", dir.display()))?;
            let path = entry.path();
            let name = entry.file_name();
            let name_str = name.to_string_lossy();
            let meta = fs::symlink_metadata(&path)
                .with_context(|| format!("Failed to read {}", path.display()))?;
            anyhow::ensure!(
                !meta.file_type().is_symlink(),
                "Refusing to follow symlink {}",
                path.display()
            );
            if meta.is_dir() {
                if (depth > 0 && name_str.starts_with('.'))
                    || matches!(
                        name_str.as_ref(),
                        ".git"
                            | ".lake"
                            | ".elan"
                            | ".cargo"
                            | ".benchmark-tools"
                            | "target"
                            | "node_modules"
                    )
                {
                    continue;
                }
                stack.push((path, depth + 1));
            } else if meta.is_file()
                && path.extension().and_then(|ext| ext.to_str()) == Some("lean")
                && name_str != "lakefile.lean"
            {
                out.push(path);
            }
        }
    }
    out.sort();
    Ok(out)
}

struct DeclExtra {
    name: String,
    is_private: bool,
    explicit_public: bool,
    instance_binders: Vec<String>,
    ordered_type_params: Vec<BTreeSet<String>>,
    context_assumptions: Vec<String>,
    saw_malformed_prefix: bool,
    saw_unparsed_binder: bool,
    saw_unparsed_telescope: bool,
}

struct DeclScan {
    extras: Vec<DeclExtra>,
    has_malformed_scope: bool,
    has_unmodeled_instance_env: bool,
    has_unmodeled_syntax_env: bool,
    has_shadowed_value_types: bool,
}

enum PrefixAction {
    Assumption(String),
    UnmodeledEnv,
    ShadowedValueEnv,
    SyntaxEnv,
    Malformed,
    Ignore,
}

fn scan_decl_extras(src: &str) -> DeclScan {
    let masked = mask_comments(src);
    let chars: Vec<char> = masked.chars().collect();
    let byte_offsets: Vec<usize> = masked.char_indices().map(|(offset, _)| offset).collect();
    let n = chars.len();
    let mut i = 0usize;
    let mut scope: Vec<ScopeFrame> = Vec::new();
    let public_section_stack_init: Vec<bool> = Vec::new();
    let mut public_section_stack = public_section_stack_init;
    let mut meta_section_stack: Vec<bool> = Vec::new();
    let mut context: Vec<Vec<String>> = vec![Vec::new()];
    let mut at_cmd_head = true;
    let mut pending_private = false;
    let mut pending_public = false;
    let mut pending_meta = false;
    let mut pending_noncomputable = false;
    let mut pending_other_mod = false;
    let mut pending_attr_has_instance = false;
    let mut pending_assumptions: Vec<String> = Vec::new();
    let mut pending_saw_attr = false;
    let mut pending_malformed_prefix = false;
    let mut has_malformed_scope = false;
    let mut has_unmodeled_instance_env = false;
    let mut has_unmodeled_syntax_env = false;
    let mut has_shadowed_value_types = false;
    let mut out = Vec::new();
    while i < n {
        if let Some(end) = skip_any(&masked, &byte_offsets, i) {
            i = end;
            continue;
        }
        if chars[i] == '\n' {
            if !at_cmd_head {
                pending_private = false;
                pending_public = false;
                pending_meta = false;
                pending_noncomputable = false;
                pending_other_mod = false;
                pending_attr_has_instance = false;
                pending_assumptions.clear();
                pending_saw_attr = false;
                pending_malformed_prefix = false;
            }
            at_cmd_head = true;
            i += 1;
            continue;
        }
        if chars[i] == ';' {
            if at_cmd_head {
                has_malformed_scope = true;
                has_unmodeled_syntax_env = true;
                has_unmodeled_instance_env = true;
            }
            i += 1;
            continue;
        }
        if chars[i].is_whitespace() {
            i += 1;
            continue;
        }
        if at_cmd_head && chars[i] == '@' && i + 1 < n && chars[i + 1] == '[' {
            if pending_private
                || pending_public
                || pending_meta
                || pending_noncomputable
                || pending_other_mod
            {
                pending_malformed_prefix = true;
                has_malformed_scope = true;
            }
            if let Some(end) = matching_close(&masked, &byte_offsets, &chars, i + 1, '[', ']') {
                let inner: String = chars[i + 2..end - 1].iter().collect();
                if attr_mentions_instance_or_class(&inner) {
                    pending_attr_has_instance = true;
                }
                pending_saw_attr = true;
                i = end;
                continue;
            }
        }
        if at_cmd_head && chars[i] == '#' && i + 1 < n && is_ident_start(chars[i + 1]) {
            let hash_start = i;
            i += 1;
            while i < n && (is_ident_continue(chars[i]) || chars[i] == '!') {
                i += 1;
            }
            let hash_cmd: String = chars[hash_start..i].iter().collect();
            if hash_cmd == "#time" {
                continue;
            }
            if hash_cmd == "#with_exporting" {
                has_malformed_scope = true;
                continue;
            }
            if matches!(
                hash_cmd.as_str(),
                "#guard_msgs" | "#guard_panic" | "#info_trees"
            ) {
                i = scan_command_body(
                    &masked,
                    &byte_offsets,
                    &chars,
                    &hash_cmd,
                    i,
                    n,
                    line_col(&chars, hash_start),
                );
                at_cmd_head = consume_trailing_in(&masked, &byte_offsets, &chars, &mut i);
                continue;
            }
            if matches!(hash_cmd.as_str(), "#eval" | "#eval!") {
                has_unmodeled_instance_env = true;
                has_unmodeled_syntax_env = true;
            }
            pending_private = false;
            pending_public = false;
            pending_meta = false;
            pending_noncomputable = false;
            pending_other_mod = false;
            pending_attr_has_instance = false;
            pending_assumptions.clear();
            pending_saw_attr = false;
            pending_malformed_prefix = false;
            i = scan_command_body(
                &masked,
                &byte_offsets,
                &chars,
                &hash_cmd,
                i,
                n,
                line_col(&chars, hash_start),
            );
            at_cmd_head = consume_trailing_in(&masked, &byte_offsets, &chars, &mut i);
            continue;
        }
        if at_cmd_head {
            let mut chained = false;
            let mut base_cmd_col: Option<usize> = None;
            while let Some((after_in, kw, action)) = consume_in_command_prefix(
                &masked,
                &byte_offsets,
                &chars,
                i,
                base_cmd_col.unwrap_or_else(|| line_col(&chars, i)),
            ) {
                chained = true;
                base_cmd_col.get_or_insert_with(|| line_col(&chars, i));
                let prefix_allows_decl_mods = matches!(
                    kw,
                    "instance"
                        | "def"
                        | "abbrev"
                        | "class"
                        | "structure"
                        | "inductive"
                        | "coinductive"
                        | "axiom"
                        | "opaque"
                        | "constant"
                        | "example"
                        | "theorem"
                        | "lemma"
                ) || syntax_env_keyword(kw);
                if !prefix_allows_decl_mods
                    && (pending_private
                        || pending_public
                        || pending_meta
                        || pending_noncomputable
                        || pending_other_mod
                        || pending_saw_attr)
                {
                    has_malformed_scope = true;
                    pending_malformed_prefix = true;
                }
                if pending_attr_has_instance {
                    has_unmodeled_instance_env = true;
                }
                pending_private = false;
                pending_public = false;
                pending_meta = false;
                pending_noncomputable = false;
                pending_other_mod = false;
                pending_attr_has_instance = false;
                pending_saw_attr = false;
                match action {
                    PrefixAction::Assumption(assumption) => pending_assumptions.push(assumption),
                    PrefixAction::UnmodeledEnv => has_unmodeled_instance_env = true,
                    PrefixAction::ShadowedValueEnv => {
                        has_unmodeled_instance_env = true;
                        has_shadowed_value_types = true;
                    }
                    PrefixAction::SyntaxEnv => {
                        has_unmodeled_syntax_env = true;
                        has_unmodeled_instance_env = true;
                    }
                    PrefixAction::Malformed => has_malformed_scope = true,
                    PrefixAction::Ignore => {}
                }
                i = after_in;
                while i < n && chars[i].is_whitespace() && chars[i] != '\n' {
                    i += 1;
                }
            }
            if chained {
                continue;
            }
        }
        if chars[i] == '«' {
            if let Some(end) = skip_any_lexeme(&masked, &byte_offsets, i) {
                at_cmd_head = false;
                pending_private = false;
                pending_public = false;
                pending_meta = false;
                pending_noncomputable = false;
                pending_other_mod = false;
                pending_attr_has_instance = false;
                pending_assumptions.clear();
                pending_saw_attr = false;
                pending_malformed_prefix = false;
                i = end;
                continue;
            }
        }
        if !is_ident_start(chars[i]) {
            if at_cmd_head {
                has_malformed_scope = true;
                has_unmodeled_syntax_env = true;
                has_unmodeled_instance_env = true;
            }
            at_cmd_head = false;
            pending_private = false;
            pending_public = false;
            pending_meta = false;
            pending_noncomputable = false;
            pending_other_mod = false;
            pending_attr_has_instance = false;
            pending_assumptions.clear();
            pending_saw_attr = false;
            pending_malformed_prefix = false;
            i += 1;
            continue;
        }
        let start = i;
        while i < n && is_ident_continue(chars[i]) {
            i += 1;
        }
        let word: String = chars[start..i].iter().collect();
        if !at_cmd_head && !matches!(word.as_str(), "theorem" | "lemma") {
            continue;
        }
        if !at_cmd_head {
            has_malformed_scope = true;
        }
        if at_cmd_head
            && matches!(
                word.as_str(),
                "public"
                    | "private"
                    | "protected"
                    | "noncomputable"
                    | "scoped"
                    | "local"
                    | "unsafe"
                    | "partial"
                    | "nonrec"
                    | "meta"
            )
        {
            if word == "private" || word == "local" {
                pending_private = true;
                pending_public = false;
            } else if word == "public" {
                if pending_meta || pending_noncomputable || pending_other_mod {
                    pending_malformed_prefix = true;
                }
                pending_public = true;
                pending_private = false;
            } else if word == "meta" {
                pending_meta = true;
            } else if word == "noncomputable" {
                pending_noncomputable = true;
            } else {
                pending_other_mod = true;
            }
            if word == "scoped" && i < n && chars[i] == '[' {
                if let Some(end) = matching_close(&masked, &byte_offsets, &chars, i, '[', ']') {
                    i = end;
                }
            }
            continue;
        }
        let was_at_cmd_head = at_cmd_head;
        let decl_private = std::mem::replace(&mut pending_private, false);
        let decl_public = std::mem::replace(&mut pending_public, false);
        let decl_meta = std::mem::replace(&mut pending_meta, false);
        let decl_noncomputable = std::mem::replace(&mut pending_noncomputable, false);
        let decl_other_mod = std::mem::replace(&mut pending_other_mod, false);
        let decl_attr_has_instance = std::mem::replace(&mut pending_attr_has_instance, false);
        let decl_saw_attr = std::mem::replace(&mut pending_saw_attr, false);
        let decl_malformed_prefix = std::mem::replace(&mut pending_malformed_prefix, false);
        if decl_attr_has_instance {
            has_unmodeled_instance_env = true;
        }
        let decl_inline_assumptions = if matches!(word.as_str(), "theorem" | "lemma") {
            std::mem::take(&mut pending_assumptions)
        } else {
            Vec::new()
        };
        if !matches!(
            word.as_str(),
            "namespace" | "section" | "mutual" | "theorem" | "lemma"
        ) && word != "end"
        {
            pending_assumptions.clear();
        }
        at_cmd_head = false;
        match word.as_str() {
            "namespace" if i < n && chars[i].is_whitespace() => {
                if decl_public
                    || decl_private
                    || decl_saw_attr
                    || decl_other_mod
                    || decl_meta
                    || decl_noncomputable
                    || decl_malformed_prefix
                {
                    has_malformed_scope = true;
                }
                let (name, next, _crossed) = dotted_name_multiline(
                    &masked,
                    &byte_offsets,
                    &chars,
                    i,
                    n,
                    line_col(&chars, start),
                );
                if name.is_empty() {
                    has_malformed_scope = true;
                }
                i = next;
                let segs: Vec<&str> = crate::splitter::split_lean_name_components(&name);
                let inline = std::mem::take(&mut pending_assumptions);
                let last_idx = segs.len().saturating_sub(1);
                for (seg_idx, seg) in segs.into_iter().enumerate() {
                    scope.push(ScopeFrame {
                        kind: ScopeKind::Namespace,
                        name: seg.to_string(),
                        open_span_idx: 0,
                    });
                    public_section_stack.push(false);
                    meta_section_stack.push(false);
                    context.push(if seg_idx == last_idx {
                        inline.clone()
                    } else {
                        Vec::new()
                    });
                }
                at_cmd_head = true;
            }
            "section" => {
                if decl_private
                    || decl_other_mod
                    || decl_malformed_prefix
                    || (decl_saw_attr && !decl_public)
                    || (decl_meta && decl_saw_attr)
                    || (decl_meta && decl_noncomputable)
                {
                    has_malformed_scope = true;
                }
                let (name, next, _crossed) = if i < n && chars[i].is_whitespace() {
                    dotted_name_multiline(
                        &masked,
                        &byte_offsets,
                        &chars,
                        i,
                        n,
                        line_col(&chars, start),
                    )
                } else {
                    (String::new(), i, false)
                };
                if (decl_public || decl_meta || decl_noncomputable || decl_saw_attr)
                    && !name.is_empty()
                {
                    has_malformed_scope = true;
                }
                i = next;
                let segs: Vec<String> = if name.is_empty() {
                    vec![String::new()]
                } else {
                    crate::splitter::split_lean_name_components(&name)
                        .into_iter()
                        .map(str::to_string)
                        .collect()
                };
                let inline = std::mem::take(&mut pending_assumptions);
                let last_idx = segs.len().saturating_sub(1);
                for (seg_idx, seg) in segs.into_iter().enumerate() {
                    scope.push(ScopeFrame {
                        kind: ScopeKind::Section,
                        name: seg,
                        open_span_idx: 0,
                    });
                    public_section_stack.push(decl_public);
                    meta_section_stack.push(decl_meta);
                    context.push(if seg_idx == last_idx {
                        inline.clone()
                    } else {
                        Vec::new()
                    });
                }
                at_cmd_head = true;
            }
            "mutual" if i >= n || chars[i].is_whitespace() => {
                if decl_public
                    || decl_private
                    || decl_saw_attr
                    || decl_meta
                    || decl_noncomputable
                    || decl_other_mod
                    || decl_malformed_prefix
                {
                    has_malformed_scope = true;
                }
                scope.push(ScopeFrame {
                    kind: ScopeKind::Mutual,
                    name: String::new(),
                    open_span_idx: 0,
                });
                public_section_stack.push(false);
                meta_section_stack.push(false);
                context.push(std::mem::take(&mut pending_assumptions));
                at_cmd_head = true;
            }
            "end" if i >= n || chars[i].is_whitespace() => {
                if decl_public
                    || decl_private
                    || decl_saw_attr
                    || decl_meta
                    || decl_noncomputable
                    || decl_other_mod
                    || decl_malformed_prefix
                    || !pending_assumptions.is_empty()
                {
                    has_malformed_scope = true;
                    pending_assumptions.clear();
                }
                let (name, next, _crossed) = if i < n && chars[i].is_whitespace() {
                    dotted_name_multiline(
                        &masked,
                        &byte_offsets,
                        &chars,
                        i,
                        n,
                        line_col(&chars, start),
                    )
                } else {
                    (String::new(), i, false)
                };
                i = next;
                if pop_scope(
                    &mut scope,
                    &mut public_section_stack,
                    &mut meta_section_stack,
                    &mut context,
                    &name,
                ) {
                    has_malformed_scope = true;
                }
                at_cmd_head = true;
            }
            "variable" | "variables" | "include" | "omit" => {
                let body_start = i;
                i = scan_command_body(
                    &masked,
                    &byte_offsets,
                    &chars,
                    &word,
                    i,
                    n,
                    line_col(&chars, start),
                );
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
            "instance"
            | "deriving"
            | "notation"
            | "infix"
            | "infixl"
            | "infixr"
            | "prefix"
            | "postfix"
            | "macro"
            | "macro_rules"
            | "elab"
            | "elab_rules"
            | "syntax"
            | "run_cmd"
            | "run_elab"
            | "drun_elab"
            | "run_meta"
            | "unif_hint"
            | "binder_predicate"
            | "simproc"
            | "dsimproc"
            | "builtin_simproc"
            | "builtin_dsimproc"
            | "cbv_simproc"
            | "builtin_cbv_simproc"
            | "grind_pattern" => {
                if syntax_env_keyword(&word) {
                    has_unmodeled_syntax_env = true;
                }
                has_unmodeled_instance_env = true;
                i = scan_command_body(
                    &masked,
                    &byte_offsets,
                    &chars,
                    &word,
                    i,
                    n,
                    line_col(&chars, start),
                );
                if consume_trailing_in(&masked, &byte_offsets, &chars, &mut i) {
                    at_cmd_head = true;
                }
            }
            "attribute" => {
                let body_start = i;
                i = scan_command_body(
                    &masked,
                    &byte_offsets,
                    &chars,
                    &word,
                    i,
                    n,
                    line_col(&chars, start),
                );
                let body: String = chars[body_start..i].iter().collect();
                if attr_mentions_instance_or_class(&body) {
                    has_unmodeled_instance_env = true;
                }
                if consume_trailing_in(&masked, &byte_offsets, &chars, &mut i) {
                    at_cmd_head = true;
                }
            }
            "open" | "export" => {
                let body_start = i;
                i = scan_command_body(
                    &masked,
                    &byte_offsets,
                    &chars,
                    &word,
                    i,
                    n,
                    line_col(&chars, start),
                );
                let body: String = chars[body_start..i].iter().collect();
                if RESERVED_INSTANCE_AND_TYPE_NAMES
                    .iter()
                    .any(|reserved| ident_mentioned(&body, reserved))
                {
                    has_unmodeled_instance_env = true;
                    if word == "export" || body.contains('(') || ident_mentioned(&body, "renaming")
                    {
                        has_shadowed_value_types = true;
                    }
                }
                if consume_trailing_in(&masked, &byte_offsets, &chars, &mut i) {
                    at_cmd_head = true;
                }
            }
            "class" | "structure" | "inductive" | "coinductive" | "def" | "abbrev" | "opaque"
            | "constant" | "example" | "axiom" => {
                let (decl_name, next, _) = dotted_name_multiline(
                    &masked,
                    &byte_offsets,
                    &chars,
                    i,
                    n,
                    line_col(&chars, start),
                );
                i = next;
                let short = decl_name.rsplit('.').next().unwrap_or(decl_name.as_str());
                let short_canon = crate::splitter::canonical_lean_name_component(short);
                if RESERVED_INSTANCE_AND_TYPE_NAMES.contains(&short_canon.as_str()) {
                    has_unmodeled_instance_env = true;
                    has_shadowed_value_types = true;
                }
                i = scan_command_body(
                    &masked,
                    &byte_offsets,
                    &chars,
                    &word,
                    i,
                    n,
                    line_col(&chars, start),
                );
                if consume_trailing_in(&masked, &byte_offsets, &chars, &mut i) {
                    at_cmd_head = true;
                }
            }
            "theorem" | "lemma" => {
                let (raw_name, next, _) = dotted_name_multiline(
                    &masked,
                    &byte_offsets,
                    &chars,
                    i,
                    n,
                    line_col(&chars, start),
                );
                if raw_name.is_empty() {
                    continue;
                }
                i = next;
                let mut binders = Vec::new();
                let mut ordered_type_params: Vec<BTreeSet<String>> = Vec::new();
                let mut cur_type_params: BTreeSet<String> = BTreeSet::new();
                let mut saw_unparsed_binder = !was_at_cmd_head || decl_malformed_prefix;
                let mut found_colon = false;
                while i < n {
                    while i < n && chars[i].is_whitespace() {
                        i += 1;
                    }
                    if i >= n {
                        break;
                    }
                    if let Some(end) = skip_any_lexeme(&masked, &byte_offsets, i) {
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
                    if chars[i] == '[' {
                        let open_at = i;
                        if let Some(end) =
                            matching_close(&masked, &byte_offsets, &chars, i, '[', ']')
                        {
                            let inner: String = chars[open_at + 1..end - 1].iter().collect();
                            binders.push(normalize_ws(&inner));
                            ordered_type_params.push(cur_type_params.clone());
                            i = end;
                        } else {
                            saw_unparsed_binder = true;
                            break;
                        }
                    } else if chars[i] == '(' || chars[i] == '{' {
                        let close = if chars[i] == '(' { ')' } else { '}' };
                        let open_at = i;
                        if let Some(end) =
                            matching_close(&masked, &byte_offsets, &chars, i, chars[i], close)
                        {
                            let inner: String = chars[open_at + 1..end - 1].iter().collect();
                            if explicit_binder_is_unparsed(&inner) {
                                saw_unparsed_binder = true;
                            } else if let Some((vars_part, ty_part)) =
                                split_top_level_colon(inner.trim())
                            {
                                let ty_trimmed = ty_part.trim();
                                if is_universe_type(ty_trimmed) {
                                    for var in vars_part.split_whitespace() {
                                        if !var.is_empty() {
                                            cur_type_params.insert(var.to_string());
                                        }
                                    }
                                }
                            }
                            i = end;
                        } else {
                            saw_unparsed_binder = true;
                            break;
                        }
                    } else if chars[i] == '⦃' {
                        saw_unparsed_binder = true;
                        if let Some(end) =
                            matching_close(&masked, &byte_offsets, &chars, i, '⦃', '⦄')
                        {
                            i = end;
                        } else {
                            break;
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
                let mut stmt_end = n;
                let mut saw_unparsed_telescope = false;
                while i < n {
                    if let Some(end) = skip_any_lexeme(&masked, &byte_offsets, i) {
                        i = end;
                        continue;
                    }
                    let ch = chars[i];
                    if ch == '(' || ch == '{' || ch == '[' || ch == '⦃' {
                        paren_depth += 1;
                    } else if ch == ')' || ch == '}' || ch == ']' || ch == '⦄' {
                        paren_depth = paren_depth.saturating_sub(1);
                    } else if ch == '⟨' {
                        angle_depth += 1;
                    } else if ch == '⟩' {
                        angle_depth = angle_depth.saturating_sub(1);
                    } else if paren_depth == 0
                        && angle_depth == 0
                        && ch == 'l'
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
                        && ch == ':'
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
                        && ch == '|'
                        && i > stmt_start
                        && chars[stmt_start..i].contains(&'\n')
                    {
                        stmt_end = i;
                        break;
                    }
                    i += 1;
                }
                let prop_str: String = chars[stmt_start..stmt_end].iter().collect();
                if stmt_end == n || prop_escaped_decl_boundary(&prop_str) {
                    has_malformed_scope = true;
                    saw_unparsed_telescope = true;
                }
                let trimmed_prop = inline_stmt_let_bindings(prop_str.trim());
                if trimmed_prop.is_empty() {
                    continue;
                }
                if stmt_has_unparsed_telescope(&trimmed_prop)
                    || statement_let_is_unsafe(&prop_str, &trimmed_prop)
                {
                    saw_unparsed_telescope = true;
                }
                let mut assumptions: Vec<String> = context
                    .iter()
                    .flat_map(|frame| frame.iter().cloned())
                    .collect();
                assumptions.extend(decl_inline_assumptions);
                out.push(DeclExtra {
                    name: qualified_decl_name(&raw_name, &scope),
                    is_private: decl_private,
                    explicit_public: decl_public
                        || (public_section_stack.iter().any(|&flag| flag) && !decl_private),
                    instance_binders: binders,
                    ordered_type_params,
                    context_assumptions: assumptions,
                    saw_malformed_prefix: decl_malformed_prefix,
                    saw_unparsed_binder,
                    saw_unparsed_telescope,
                });
                let proof_cmd_col = line_col(&chars, start);
                i = scan_command_body(&masked, &byte_offsets, &chars, &word, i, n, proof_cmd_col);
                if consume_trailing_in(&masked, &byte_offsets, &chars, &mut i) {
                    at_cmd_head = true;
                }
            }
            _ => {
                if was_at_cmd_head && matches!(word.as_str(), "eval" | "eval!") {
                    has_unmodeled_instance_env = true;
                    has_unmodeled_syntax_env = true;
                }
                i = scan_command_body(
                    &masked,
                    &byte_offsets,
                    &chars,
                    &word,
                    i,
                    n,
                    line_col(&chars, start),
                );
                if consume_trailing_in(&masked, &byte_offsets, &chars, &mut i) {
                    at_cmd_head = true;
                }
            }
        }
    }
    DeclScan {
        extras: out,
        has_malformed_scope,
        has_unmodeled_instance_env,
        has_unmodeled_syntax_env,
        has_shadowed_value_types: has_shadowed_value_types || has_unmodeled_syntax_env,
    }
}

fn pop_scope(
    scope: &mut Vec<ScopeFrame>,
    public_section_stack: &mut Vec<bool>,
    meta_section_stack: &mut Vec<bool>,
    context: &mut Vec<Vec<String>>,
    name: &str,
) -> bool {
    if name.is_empty() {
        let Some(top) = scope.pop() else {
            return true;
        };
        public_section_stack.pop();
        meta_section_stack.pop();
        if context.len() > 1 {
            context.pop();
        }
        return !top.name.is_empty();
    }
    let mut malformed = false;
    for seg in crate::splitter::split_lean_name_components(name)
        .into_iter()
        .rev()
    {
        let canon = crate::splitter::canonical_lean_name_component(seg);
        if let Some(pos) = scope
            .iter()
            .rposition(|frame| frame_name_matches(&frame.name, &canon))
        {
            if pos + 1 != scope.len() {
                malformed = true;
            }
            scope.truncate(pos);
            public_section_stack.truncate(pos);
            meta_section_stack.truncate(pos);
            context.truncate(pos + 1);
        } else {
            malformed = true;
            if scope.pop().is_some() {
                public_section_stack.pop();
                meta_section_stack.pop();
                if context.len() > 1 {
                    context.pop();
                }
            }
        }
    }
    malformed
}

fn frame_name_matches(frame_name: &str, canon: &str) -> bool {
    crate::splitter::canonical_lean_name_component(frame_name) == canon
}

fn attr_mentions_instance_or_class(text: &str) -> bool {
    ident_mentioned(text, "instance")
        || ident_mentioned(text, "default_instance")
        || ident_mentioned(text, "class")
}

fn explicit_binder_is_unparsed(inner: &str) -> bool {
    let sanitized = mask_literals(inner);
    let trimmed = sanitized.trim();
    if trimmed.is_empty() {
        return true;
    }
    let Some((_, ty)) = split_top_level_colon(trimmed) else {
        return true;
    };
    let ty = ty.trim();
    ty.is_empty()
        || ty.contains(":=")
        || ident_mentioned(ty, "autoParam")
        || ident_mentioned(ty, "optParam")
        || ident_mentioned(ty, "outParam")
        || ident_mentioned(ty, "semiOutParam")
}

fn statement_let_is_unsafe(prop: &str, inlined: &str) -> bool {
    let clean_prop = mask_literals(prop);
    let clean_inlined = mask_literals(inlined);
    if ident_mentioned(&clean_prop, "have") || ident_mentioned(&clean_inlined, "let") {
        return true;
    }
    let mut cur = prop.trim();
    while let Some(after_let) = cur
        .strip_prefix("let")
        .filter(|rest| rest.starts_with(char::is_whitespace))
    {
        let rest = after_let.trim_start();
        let name_end = rest
            .find(|c: char| !is_ident_continue(c))
            .unwrap_or(rest.len());
        if name_end == 0 {
            return true;
        }
        let var_name = &rest[..name_end];
        let after_name = &rest[name_end..];
        let Some(eq_idx) = scan_top_level_colon_eq(after_name) else {
            return true;
        };
        let type_part = after_name[..eq_idx].trim();
        let after_eq = after_name[eq_idx + 2..].trim_start();
        let Some((rhs_end, _)) = scan_let_body_start(after_eq) else {
            return true;
        };
        let rhs = after_eq[..rhs_end].trim();
        if type_part.is_empty() {
            if !untyped_let_rhs_is_value(rhs) {
                return true;
            }
        } else {
            let Some(ty) = type_part.strip_prefix(':').map(str::trim) else {
                return true;
            };
            if ty.is_empty() || !is_safe_inlined_let_type(ty) {
                return true;
            }
        }
        let Some((_rhs_end, body_start)) = scan_let_body_start(after_eq) else {
            return true;
        };
        let body = after_eq[body_start..].trim_start();
        if !ident_mentioned(body, var_name) {
            return true;
        }
        cur = body;
    }
    false
}

fn scan_top_level_colon_eq(src: &str) -> Option<usize> {
    let bytes = src.as_bytes();
    let mut i = 0usize;
    let mut depth = 0usize;
    while i < bytes.len() {
        if let Some(span) = skip_lean_lexeme(src, i) {
            i = span.end;
            continue;
        }
        let ch = src[i..].chars().next()?;
        match ch {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            ':' if depth == 0 && bytes.get(i + 1) == Some(&b'=') => return Some(i),
            ';' if depth == 0 => return None,
            _ => {}
        }
        i += ch.len_utf8();
    }
    None
}

fn scan_let_body_start(src: &str) -> Option<(usize, usize)> {
    let mut i = 0usize;
    let mut depth = 0usize;
    while i < src.len() {
        if let Some(span) = skip_lean_lexeme(src, i) {
            i = span.end;
            continue;
        }
        let ch = src[i..].chars().next()?;
        match ch {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            ';' | '\n' if depth == 0 => return Some((i, i + 1)),
            _ if depth == 0
                && i > 0
                && src.as_bytes()[i - 1].is_ascii_whitespace()
                && src[i..].starts_with("in")
                && src[i + 2..].chars().next().is_some_and(char::is_whitespace) =>
            {
                return Some((i, i + 2));
            }
            _ => {}
        }
        i += ch.len_utf8();
    }
    None
}

fn starts_scoped_term(chars: &[char], i: usize) -> bool {
    (i == 0 || !is_ident_continue(chars[i - 1]))
        && (let_term_needs_in(chars, i)
            || token_is_keyword(chars, i, "open")
            || token_is_keyword(chars, i, "set_option"))
}

fn let_term_needs_in(chars: &[char], i: usize) -> bool {
    if !token_is_keyword(chars, i, "let") {
        return false;
    }
    let mut k = i + 3;
    let mut depth = 0usize;
    while k < chars.len() {
        match chars[k] {
            '(' | '[' | '{' | '⦃' | '⟨' => depth += 1,
            ')' | ']' | '}' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            ';' | '\n' if depth == 0 => return false,
            'i' if depth == 0
                && k > 0
                && chars[k - 1].is_whitespace()
                && token_is_keyword(chars, k, "in") =>
            {
                return true;
            }
            _ => {}
        }
        k += 1;
    }
    false
}

fn is_universe_type(ty: &str) -> bool {
    let cur = ty
        .trim()
        .strip_prefix("_root_.")
        .unwrap_or(ty.trim())
        .trim();
    if cur == "Type" || cur == "Sort" {
        return true;
    }
    let Some(rest) = cur
        .strip_prefix("Type ")
        .or_else(|| cur.strip_prefix("Sort "))
    else {
        return false;
    };
    let rest = rest.trim();
    !rest.is_empty()
        && !rest.contains(['→', '∀', '∃', '×', '=', '<', '>', ':', '(', '[', '{'])
        && !rest.contains("->")
}

fn is_ident_token(text: &str) -> bool {
    let mut chars = text.chars();
    chars.next().is_some_and(is_ident_start) && chars.all(is_ident_continue)
}

fn untyped_let_rhs_is_value(rhs: &str) -> bool {
    let clean = mask_literals(rhs);
    let trimmed = clean.trim();
    !trimmed.is_empty()
        && !trimmed.contains(['→', '∀', '∃', ':', '=', '<', '>', '∧', '∨', '¬', '↔'])
        && !trimmed.contains("->")
        && !ident_mentioned(trimmed, "False")
        && !ident_mentioned(trimmed, "True")
        && !ident_mentioned(trimmed, "Empty")
        && !ident_mentioned(trimmed, "PEmpty")
        && !ident_mentioned(trimmed, "fun")
        && !ident_mentioned(trimmed, "forall")
        && !trimmed.contains('λ')
}

fn conclusion_is_modeled(
    concl: &str,
    type_params: &BTreeSet<String>,
    prop_params: &BTreeSet<String>,
    value_params: &BTreeSet<String>,
    prop_local_defs: &[(String, Vec<String>, String)],
) -> bool {
    let conjuncts = split_top_level_and(concl);
    if conjuncts.len() > 1 {
        return conjuncts.iter().all(|part| {
            let mut inner = part.trim();
            if let Some(stripped) = strip_wrapping_parens(inner) {
                inner = stripped;
            }
            if let Some((lhs, rhs)) = split_arrow(inner) {
                if lhs.trim() == rhs.trim()
                    || ident_mentioned(&lhs, "False")
                    || ident_mentioned(&rhs, "True")
                {
                    return false;
                }
                let lhs_eq = split_top_level_eq_or_ne(&lhs);
                let rhs_eq = split_top_level_eq_or_ne(&rhs);
                let sym_eq = matches!(
                    (lhs_eq, rhs_eq),
                    (Some((l1, r1, ne1)), Some((l2, r2, ne2)))
                        if ne1 == ne2 && l1.trim() == r2.trim() && r1.trim() == l2.trim()
                );
                sym_eq
                    && proposition_is_modeled(
                        &lhs,
                        type_params,
                        prop_params,
                        value_params,
                        prop_local_defs,
                        0,
                    )
                    && proposition_is_modeled(
                        &rhs,
                        type_params,
                        prop_params,
                        value_params,
                        prop_local_defs,
                        0,
                    )
                    && !contains_any_arrow(&lhs)
                    && !contains_any_arrow(&rhs)
                    && !has_top_level_colon_in_binders(&lhs)
                    && !has_top_level_colon_in_binders(&rhs)
            } else {
                proposition_is_modeled(
                    inner,
                    type_params,
                    prop_params,
                    value_params,
                    prop_local_defs,
                    0,
                )
            }
        });
    }
    let mut inner = concl.trim();
    if let Some(stripped) = strip_wrapping_parens(inner) {
        inner = stripped;
    }
    if split_arrow(inner).is_some() || parenthesized_implication(inner) {
        return false;
    }
    proposition_is_modeled(
        inner,
        type_params,
        prop_params,
        value_params,
        prop_local_defs,
        0,
    )
}

fn conclusion_has_unmodeled_nested_arrow(concl: &str) -> bool {
    let conjuncts = split_top_level_and(concl);
    if conjuncts.len() > 1 {
        return conjuncts.iter().any(|part| {
            let mut inner = part.trim();
            if let Some(stripped) = strip_wrapping_parens(inner) {
                inner = stripped;
            }
            if let Some((lhs, rhs)) = split_arrow(inner) {
                contains_any_arrow(&lhs)
                    || contains_any_arrow(&rhs)
                    || has_top_level_colon_in_binders(&lhs)
                    || has_top_level_colon_in_binders(&rhs)
            } else {
                contains_arrow_inside_delimiters(inner)
            }
        });
    }
    contains_arrow_inside_delimiters(concl)
}

fn contains_any_arrow(text: &str) -> bool {
    text.contains('→') || text.contains("->")
}

fn contains_arrow_inside_delimiters(part: &str) -> bool {
    let chars: Vec<char> = part.chars().collect();
    let mut depth = 0usize;
    let mut idx = 0usize;
    while idx < chars.len() {
        match chars[idx] {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            '→' if depth > 0 => return true,
            '-' if depth > 0 && chars.get(idx + 1) == Some(&'>') => return true,
            _ => {}
        }
        idx += 1;
    }
    false
}

fn extract_prop_local_defs(clean_src: &str) -> Vec<(String, Vec<String>, String)> {
    let all = extract_local_def_unfoldings(clean_src);
    let masked = mask_literals(clean_src);
    let mut prop_names = BTreeSet::new();
    for line in masked.lines() {
        let trimmed = line.trim_start();
        let rest = trimmed
            .strip_prefix("private ")
            .or_else(|| trimmed.strip_prefix("public "))
            .or_else(|| trimmed.strip_prefix("protected "))
            .or_else(|| trimmed.strip_prefix("noncomputable "))
            .unwrap_or(trimmed);
        let Some(after_kw) = rest
            .strip_prefix("def ")
            .or_else(|| rest.strip_prefix("abbrev "))
        else {
            continue;
        };
        let Some(eq_idx) = scan_top_level_colon_eq(after_kw) else {
            continue;
        };
        let header = after_kw[..eq_idx].trim();
        let Some((_, ret_ty)) = split_top_level_colon(header) else {
            continue;
        };
        let ret_ty = ret_ty.trim();
        if ret_ty == "Prop" || ret_ty == "_root_.Prop" {
            let name: String = header
                .chars()
                .take_while(|c| is_ident_continue(*c) || *c == '.' || *c == '«' || *c == '»')
                .collect();
            if !name.is_empty() {
                prop_names.insert(name);
            }
        }
    }
    all.into_iter()
        .filter(|(name, _, _, _)| {
            let short = name.rsplit('.').next().unwrap_or(name);
            prop_names.contains(name) || prop_names.contains(short)
        })
        .map(|(name, params, body, _)| (name, params, body))
        .collect()
}

fn binder_type_is_modeled(
    ty: &str,
    type_params: &BTreeSet<String>,
    prop_params: &BTreeSet<String>,
    value_params: &BTreeSet<String>,
    prop_local_defs: &[(String, Vec<String>, String)],
) -> bool {
    if is_known_binder_value_type(ty) {
        return false;
    }
    hypothesis_is_modeled(ty, type_params, prop_params, value_params, prop_local_defs)
}

fn hypothesis_is_modeled(
    text: &str,
    type_params: &BTreeSet<String>,
    prop_params: &BTreeSet<String>,
    value_params: &BTreeSet<String>,
    prop_local_defs: &[(String, Vec<String>, String)],
) -> bool {
    let mut current = mask_literals(text);
    current = current.trim().to_string();
    while let Some(inner) = strip_wrapping_parens(&current) {
        current = inner.to_string();
    }
    let ty = split_top_level_colon(&current).map_or(current.as_str(), |(_, rhs)| rhs.trim());
    let mut ty = ty.trim().to_string();
    while let Some(inner) = strip_wrapping_parens(&ty) {
        ty = inner.to_string();
    }
    if ty.is_empty() {
        return false;
    }
    if prop_params.contains(ty.trim()) {
        return true;
    }
    proposition_is_modeled(
        &ty,
        type_params,
        prop_params,
        value_params,
        prop_local_defs,
        0,
    )
}

fn proposition_is_modeled(
    ty: &str,
    type_params: &BTreeSet<String>,
    prop_params: &BTreeSet<String>,
    value_params: &BTreeSet<String>,
    prop_local_defs: &[(String, Vec<String>, String)],
    depth: usize,
) -> bool {
    if depth > 8 {
        return false;
    }
    let mut cur = ty.trim().to_string();
    while let Some(inner) = strip_wrapping_parens(&cur) {
        cur = inner.to_string();
    }
    let cur = cur
        .strip_prefix("_root_.")
        .map(str::trim)
        .unwrap_or(cur.as_str())
        .to_string();
    if cur.is_empty()
        || cur.contains(['→', '∀', '∃', '{', '[', '⦃', 'λ'])
        || cur.contains("->")
        || ident_mentioned(&cur, "forall")
        || ident_mentioned(&cur, "fun")
        || ident_mentioned(&cur, "have")
        || ident_mentioned(&cur, "let")
    {
        return false;
    }
    if let Some((left, right)) = split_top_level_iff(&cur) {
        return proposition_is_modeled(
            &left,
            type_params,
            prop_params,
            value_params,
            prop_local_defs,
            depth + 1,
        ) && proposition_is_modeled(
            &right,
            type_params,
            prop_params,
            value_params,
            prop_local_defs,
            depth + 1,
        );
    }
    if let Some((left, right)) = split_top_level_or(&cur) {
        return proposition_is_modeled(
            &left,
            type_params,
            prop_params,
            value_params,
            prop_local_defs,
            depth + 1,
        ) && proposition_is_modeled(
            &right,
            type_params,
            prop_params,
            value_params,
            prop_local_defs,
            depth + 1,
        );
    }
    let conjuncts = split_top_level_and(&cur);
    if conjuncts.len() > 1 {
        return conjuncts.iter().all(|part| {
            proposition_is_modeled(
                part,
                type_params,
                prop_params,
                value_params,
                prop_local_defs,
                depth + 1,
            )
        });
    }
    if prop_params.contains(cur.as_str()) {
        return true;
    }
    if let Some(inner) = cur
        .strip_prefix('¬')
        .or_else(|| cur.strip_prefix("Not ").map(str::trim))
    {
        return proposition_is_modeled(
            inner,
            type_params,
            prop_params,
            value_params,
            prop_local_defs,
            depth + 1,
        );
    }
    if let Some((lhs, rhs, _)) = split_top_level_eq_or_ne(&cur) {
        return scalar_value_expr(lhs, value_params) && scalar_value_expr(rhs, value_params);
    }
    if let Some((lhs, rhs, _)) = split_top_level_rel_op(&cur) {
        return scalar_value_expr(&lhs, value_params) && scalar_value_expr(&rhs, value_params);
    }
    if matches!(cur.as_str(), "True" | "False") {
        return true;
    }
    local_prop_application(
        &cur,
        type_params,
        prop_params,
        value_params,
        prop_local_defs,
        depth,
    )
}

fn local_prop_application(
    expr: &str,
    type_params: &BTreeSet<String>,
    prop_params: &BTreeSet<String>,
    value_params: &BTreeSet<String>,
    prop_local_defs: &[(String, Vec<String>, String)],
    depth: usize,
) -> bool {
    let Some((head, args)) = split_type_application(expr) else {
        return false;
    };
    if head.contains('.') || !is_ident_token(head) {
        return false;
    };
    let Some((_, params, body)) = prop_local_defs.iter().rev().find(|(name, _, _)| {
        let short = name.rsplit('.').next().unwrap_or(name);
        name == head || (short == head && !name.contains('.'))
    }) else {
        return false;
    };
    if params.len() != args.len() {
        return false;
    }
    let mut unfolded = body.clone();
    for (param, arg) in params.iter().zip(args.iter()) {
        unfolded = replace_ident_boundary(&unfolded, param, arg);
    }
    proposition_is_modeled(
        &unfolded,
        type_params,
        prop_params,
        value_params,
        prop_local_defs,
        depth + 1,
    )
}

fn scalar_value_expr(expr: &str, value_params: &BTreeSet<String>) -> bool {
    let trimmed = expr.trim();
    if trimmed.is_empty()
        || trimmed.contains(['→', '∀', '∃', ':', '{', '[', '⦃', 'λ', '.', '@'])
        || trimmed.contains("->")
        || ident_mentioned(trimmed, "fun")
        || ident_mentioned(trimmed, "forall")
    {
        return false;
    }
    let mut saw_ident = false;
    let mut ident = String::new();
    let flush = |ident: &mut String, saw: &mut bool| {
        if ident.is_empty() {
            return true;
        }
        *saw = true;
        let ok = value_params.contains(ident)
            || matches!(ident.as_str(), "true" | "false")
            || ident.chars().all(|c| c.is_ascii_digit());
        ident.clear();
        ok
    };
    for ch in trimmed.chars() {
        if is_ident_continue(ch) {
            ident.push(ch);
        } else if !flush(&mut ident, &mut saw_ident) {
            return false;
        }
    }
    flush(&mut ident, &mut saw_ident) && saw_ident
}

fn split_top_level_or(src: &str) -> Option<(String, String)> {
    let chars: Vec<(usize, char)> = src.char_indices().collect();
    let mut depth = 0usize;
    let mut idx = 0usize;
    while idx < chars.len() {
        let (byte, ch) = chars[idx];
        match ch {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            '∨' if depth == 0 => {
                return Some((
                    src[..byte].trim().to_string(),
                    src[byte + ch.len_utf8()..].trim().to_string(),
                ));
            }
            '\\' if depth == 0 && chars.get(idx + 1).map(|(_, c)| *c) == Some('/') => {
                return Some((
                    src[..byte].trim().to_string(),
                    src[byte + 2..].trim().to_string(),
                ));
            }
            _ => {}
        }
        idx += 1;
    }
    None
}

fn split_top_level_iff(src: &str) -> Option<(String, String)> {
    let chars: Vec<(usize, char)> = src.char_indices().collect();
    let mut depth = 0usize;
    let mut idx = 0usize;
    while idx < chars.len() {
        let (byte, ch) = chars[idx];
        match ch {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            '↔' if depth == 0 => {
                return Some((
                    src[..byte].trim().to_string(),
                    src[byte + ch.len_utf8()..].trim().to_string(),
                ));
            }
            '<' if depth == 0
                && chars.get(idx + 1).map(|(_, c)| *c) == Some('-')
                && chars.get(idx + 2).map(|(_, c)| *c) == Some('>') =>
            {
                return Some((
                    src[..byte].trim().to_string(),
                    src[byte + 3..].trim().to_string(),
                ));
            }
            _ => {}
        }
        idx += 1;
    }
    None
}

fn split_top_level_rel_op(src: &str) -> Option<(String, String, &'static str)> {
    let chars: Vec<(usize, char)> = src.char_indices().collect();
    let mut depth = 0usize;
    let mut idx = 0usize;
    while idx < chars.len() {
        let (byte, ch) = chars[idx];
        match ch {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            '=' if depth == 0 && chars.get(idx + 1).map(|(_, c)| *c) == Some('=') => {
                return Some((
                    src[..byte].trim().to_string(),
                    src[byte + 2..].trim().to_string(),
                    "==",
                ));
            }
            '<' | '>' | '≤' | '≥' if depth == 0 => {
                let op = if ch == '<' {
                    "<"
                } else if ch == '>' {
                    ">"
                } else if ch == '≤' {
                    "≤"
                } else {
                    "≥"
                };
                return Some((
                    src[..byte].trim().to_string(),
                    src[byte + ch.len_utf8()..].trim().to_string(),
                    op,
                ));
            }
            _ => {}
        }
        idx += 1;
    }
    None
}

fn is_safe_inlined_let_type(ty: &str) -> bool {
    matches!(
        ty.trim(),
        "Nat"
            | "Int"
            | "Bool"
            | "String"
            | "Char"
            | "UInt8"
            | "UInt16"
            | "UInt32"
            | "UInt64"
            | "USize"
            | "Unit"
            | "PUnit"
    )
}

fn line_col(chars: &[char], idx: usize) -> usize {
    let mut col = 0usize;
    let mut i = idx;
    while i > 0 && chars[i - 1] != '\n' {
        i -= 1;
        col += 1;
    }
    col
}

fn next_significant(src: &str, byte_offsets: &[usize], chars: &[char], mut k: usize) -> usize {
    while k < chars.len() && chars[k].is_whitespace() && chars[k] != ';' {
        if let Some(end) = skip_any(src, byte_offsets, k) {
            k = end;
            continue;
        }
        k += 1;
    }
    k
}

fn token_is_keyword(chars: &[char], k: usize, kw: &str) -> bool {
    let needle: Vec<char> = kw.chars().collect();
    k + needle.len() <= chars.len()
        && chars[k..k + needle.len()] == needle[..]
        && (k + needle.len() >= chars.len() || !is_ident_continue(chars[k + needle.len()]))
}

fn is_top_level_command_token(chars: &[char], k: usize) -> bool {
    const COMMANDS: &[&str] = &[
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "instance",
        "class",
        "structure",
        "inductive",
        "coinductive",
        "axiom",
        "opaque",
        "constant",
        "example",
        "variable",
        "variables",
        "universe",
        "universes",
        "set_option",
        "namespace",
        "section",
        "end",
        "open",
        "attribute",
        "export",
        "include",
        "omit",
        "notation",
        "infix",
        "infixl",
        "infixr",
        "prefix",
        "postfix",
        "macro",
        "macro_rules",
        "elab",
        "elab_rules",
        "syntax",
        "mutual",
        "deriving",
        "run_cmd",
        "run_elab",
        "drun_elab",
        "run_meta",
        "unif_hint",
        "binder_predicate",
        "simproc",
        "dsimproc",
        "builtin_simproc",
        "builtin_dsimproc",
        "cbv_simproc",
        "builtin_cbv_simproc",
        "grind_pattern",
        "public",
        "private",
        "protected",
        "meta",
        "noncomputable",
        "local",
        "scoped",
        "unsafe",
        "partial",
        "nonrec",
    ];
    COMMANDS.iter().any(|kw| token_is_keyword(chars, k, kw))
}

fn is_top_level_command_start(chars: &[char], k: usize) -> bool {
    is_top_level_command_token(chars, k)
        || (chars.get(k) == Some(&'@') && chars.get(k + 1) == Some(&'['))
        || (chars.get(k) == Some(&'#') && chars.get(k + 1).is_some_and(|c| is_ident_start(*c)))
}

fn consume_trailing_in(src: &str, byte_offsets: &[usize], chars: &[char], idx: &mut usize) -> bool {
    let k = next_significant(src, byte_offsets, chars, *idx);
    if token_is_keyword(chars, k, "in") {
        *idx = k + 2;
        while *idx < chars.len() && chars[*idx].is_whitespace() && chars[*idx] != '\n' {
            *idx += 1;
        }
        return true;
    }
    false
}

fn command_line_continues(
    src: &str,
    byte_offsets: &[usize],
    chars: &[char],
    kw: &str,
    body_is_ws: bool,
    cmd_col: usize,
    newline_at: usize,
) -> bool {
    let k = next_significant(src, byte_offsets, chars, newline_at + 1);
    if k >= chars.len() {
        return false;
    }
    if token_is_keyword(chars, k, "in") {
        return true;
    }
    if kw == "attribute" && body_is_ws && chars[k] == '[' {
        return true;
    }
    if kw == "open"
        && body_is_ws
        && (token_is_keyword(chars, k, "scoped")
            || token_is_keyword(chars, k, "hiding")
            || token_is_keyword(chars, k, "renaming"))
    {
        return true;
    }
    if kw == "open" && body_is_ws && chars[k] == '(' {
        return false;
    }
    if term_body_command_keyword(kw)
        && line_col(chars, k) > cmd_col
        && (token_is_keyword(chars, k, "open") || token_is_keyword(chars, k, "set_option"))
    {
        return true;
    }
    if matches!(kw, "def" | "abbrev" | "example")
        && line_col(chars, k) > cmd_col
        && (token_is_keyword(chars, k, "theorem") || token_is_keyword(chars, k, "lemma"))
    {
        return true;
    }
    line_col(chars, k) > cmd_col && !is_top_level_command_start(chars, k)
}

fn term_body_command_keyword(kw: &str) -> bool {
    matches!(
        kw,
        "def" | "abbrev" | "theorem" | "lemma" | "instance" | "example" | "opaque"
    )
}

fn scan_command_body(
    src: &str,
    byte_offsets: &[usize],
    chars: &[char],
    kw: &str,
    start: usize,
    n: usize,
    cmd_col: usize,
) -> usize {
    let mut i = start;
    let mut depth = 0usize;
    let mut body_is_ws = true;
    let mut pending_let_in = false;
    while i < n {
        if let Some(end) = skip_any(src, byte_offsets, i) {
            i = end;
            continue;
        }
        match chars[i] {
            '(' | '[' | '{' | '⦃' | '⟨' => {
                depth += 1;
                body_is_ws = false;
            }
            ')' | ']' | '}' | '⦄' | '⟩' => {
                depth = depth.saturating_sub(1);
                body_is_ws = false;
            }
            'l' | 'o' | 's' if depth == 0 && starts_scoped_term(chars, i) => {
                pending_let_in = true;
                body_is_ws = false;
            }
            't' | 'l'
                if depth == 0
                    && (token_is_keyword(chars, i, "theorem")
                        || token_is_keyword(chars, i, "lemma")) =>
            {
                body_is_ws = false;
            }
            'i' if depth == 0
                && token_is_keyword(chars, i, "in")
                && i > 0
                && chars[i - 1].is_whitespace() =>
            {
                if pending_let_in {
                    pending_let_in = false;
                    body_is_ws = false;
                } else {
                    break;
                }
            }
            '\n' if depth == 0 => {
                if command_line_continues(src, byte_offsets, chars, kw, body_is_ws, cmd_col, i) {
                    body_is_ws = false;
                } else {
                    break;
                }
            }
            ';' if depth == 0 => {
                pending_let_in = false;
                body_is_ws = false;
            }
            ch if !ch.is_whitespace() => body_is_ws = false,
            _ => {}
        }
        i += 1;
    }
    i
}

fn syntax_env_keyword(word: &str) -> bool {
    matches!(
        word,
        "notation"
            | "infix"
            | "infixl"
            | "infixr"
            | "prefix"
            | "postfix"
            | "macro"
            | "macro_rules"
            | "elab"
            | "elab_rules"
            | "syntax"
            | "run_cmd"
            | "run_elab"
            | "drun_elab"
            | "run_meta"
            | "unif_hint"
            | "binder_predicate"
            | "simproc"
            | "dsimproc"
            | "builtin_simproc"
            | "builtin_dsimproc"
            | "cbv_simproc"
            | "builtin_cbv_simproc"
            | "grind_pattern"
    )
}

fn stmt_has_unparsed_telescope(prop: &str) -> bool {
    let clean = mask_literals(prop);
    let peeled = peel_implication_telescope(&clean);
    clean.contains('[')
        || clean.contains('{')
        || clean.contains('⦃')
        || clean.contains('∀')
        || ident_mentioned(&clean, "forall")
        || prop_escaped_decl_boundary(prop)
        || peeled
            .iter()
            .take(peeled.len().saturating_sub(1))
            .any(|part| {
                has_top_level_colon_in_binders(part)
                    || parenthesized_implication(part)
                    || contains_arrow_inside_delimiters(part)
            })
        || peeled.last().is_some_and(|concl| {
            has_top_level_colon_in_binders(concl)
                || parenthesized_implication(concl)
                || conclusion_has_unmodeled_nested_arrow(concl)
        })
}

fn prop_escaped_decl_boundary(prop: &str) -> bool {
    let mut i = 0usize;
    let mut depth = 0usize;
    while i < prop.len() {
        if let Some(span) = skip_lean_lexeme(prop, i) {
            i = span.end;
            continue;
        }
        let Some(ch) = prop[i..].chars().next() else {
            break;
        };
        match ch {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            _ if depth == 0 && is_ident_start(ch) => {
                let start = i;
                i += ch.len_utf8();
                while let Some(c) = prop[i..].chars().next() {
                    if is_ident_continue(c) {
                        i += c.len_utf8();
                    } else {
                        break;
                    }
                }
                if matches!(
                    &prop[start..i],
                    "where" | "theorem" | "lemma" | "def" | "abbrev" | "instance" | "axiom"
                ) {
                    return true;
                }
                continue;
            }
            _ => {}
        }
        i += ch.len_utf8();
    }
    false
}

fn peel_implication_telescope(prop: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = prop.trim().to_string();
    for _ in 0..64 {
        let split = split_top_level_implications(&current);
        if split.len() > 1 {
            parts.extend_from_slice(&split[..split.len() - 1]);
            current = split.last().cloned().unwrap_or_default();
            continue;
        }
        let mut unwrapped = current.as_str();
        while let Some(inner) = strip_wrapping_parens(unwrapped) {
            unwrapped = inner;
        }
        if unwrapped.len() != current.trim().len() && split_arrow(unwrapped).is_some() {
            current = unwrapped.to_string();
            continue;
        }
        break;
    }
    parts.push(current);
    parts
}

fn strip_wrapping_parens(text: &str) -> Option<&str> {
    let trimmed = text.trim();
    let chars: Vec<(usize, char)> = trimmed.char_indices().collect();
    if chars.first().map(|(_, ch)| *ch) != Some('(') || chars.last().map(|(_, ch)| *ch) != Some(')')
    {
        return None;
    }
    let mut depth = 0usize;
    for (idx, (_, ch)) in chars.iter().enumerate() {
        match ch {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => {
                depth = depth.saturating_sub(1);
                if depth == 0 && idx + 1 < chars.len() {
                    return None;
                }
            }
            _ => {}
        }
    }
    if depth != 0 {
        return None;
    }
    let last_byte = chars.last()?.0;
    Some(trimmed[1..last_byte].trim())
}

fn parenthesized_implication(part: &str) -> bool {
    let mut cur = part.trim();
    let mut stripped_any = false;
    while let Some(inner) = strip_wrapping_parens(cur) {
        stripped_any = true;
        cur = inner;
    }
    stripped_any && split_arrow(cur).is_some()
}

fn hypothesis_is_vacuous(text: &str) -> bool {
    let mut current = text.trim();
    while let Some(inner) = strip_wrapping_parens(current) {
        current = inner;
    }
    let ty = split_top_level_colon(current).map_or(current, |(_, rhs)| rhs.trim());
    type_is_vacuous(ty)
}

fn type_is_vacuous(ty: &str) -> bool {
    let mut cur = ty.trim();
    while let Some(inner) = strip_wrapping_parens(cur) {
        cur = inner;
    }
    let cur = cur.strip_prefix("_root_.").map_or(cur, str::trim);
    if matches!(
        cur,
        "Empty"
            | "PEmpty"
            | "False"
            | "false"
            | "Not True"
            | "¬ True"
            | "¬True"
            | "True = False"
            | "False = True"
            | "true = false"
            | "false = true"
    ) {
        return true;
    }
    if let Some(neg_inner) = cur
        .strip_prefix('¬')
        .or_else(|| cur.strip_prefix("Not ").map(str::trim))
    {
        if type_is_trivially_true(neg_inner) {
            return true;
        }
    }
    let conjuncts = split_top_level_and(cur);
    if conjuncts.len() > 1 && conjuncts.iter().any(|part| type_is_vacuous(part)) {
        return true;
    }
    if let Some((lhs, rhs, is_ne)) = split_top_level_eq_or_ne(cur) {
        if is_ne && lhs == rhs {
            return true;
        }
        if !is_ne {
            if let (Ok(lv), Ok(rv)) = (lhs.parse::<u128>(), rhs.parse::<u128>()) {
                if lv != rv {
                    return true;
                }
            }
        }
    }
    if let Some(body) = cur
        .strip_prefix('∃')
        .and_then(|rest| split_top_level_comma(rest))
    {
        if type_is_vacuous(body.1) {
            return true;
        }
    }
    if let Some((lhs, rhs)) = split_arrow(cur) {
        return type_is_inhabited_source(&lhs) && type_is_vacuous(&rhs);
    }
    if let Some((left, right)) = split_top_level_product_op(cur) {
        return type_is_vacuous(&left) || type_is_vacuous(&right);
    }
    if let Some(pred) = subtype_predicate(cur) {
        return type_is_vacuous(&pred);
    }
    let Some((head_raw, args)) = split_type_application(cur) else {
        return false;
    };
    let head = head_raw.rsplit('.').next().unwrap_or(head_raw);
    match (head, args.as_slice()) {
        ("Fin", [bound]) => !bound_is_positive_fin(bound),
        ("Nonempty" | "Inhabited" | "Fact" | "ULift" | "PLift" | "Thunk" | "id", [inner]) => {
            type_is_vacuous(inner)
        }
        ("Exists", [pred]) => lambda_body_is_vacuous(pred),
        ("Prod" | "PProd", [left, right]) => type_is_vacuous(left) || type_is_vacuous(right),
        ("Sigma" | "PSigma" | "Subtype", [left, right]) => {
            type_is_vacuous(left) || lambda_body_is_vacuous(right)
        }
        ("Sigma" | "PSigma", [pred]) => lambda_body_is_vacuous(pred),
        _ => false,
    }
}

fn type_is_trivially_true(ty: &str) -> bool {
    let inner = strip_wrapping_parens(ty).unwrap_or(ty).trim();
    if matches!(inner, "True" | "true") {
        return true;
    }
    if let Some((lhs, rhs, false)) = split_top_level_eq_or_ne(inner) {
        return lhs == rhs;
    }
    false
}

fn lambda_body_is_vacuous(expr: &str) -> bool {
    let mut cur = expr.trim();
    while let Some(inner) = strip_wrapping_parens(cur) {
        cur = inner;
    }
    if let Some(rest) = cur
        .strip_prefix("fun")
        .filter(|r| r.starts_with(char::is_whitespace) || r.starts_with('('))
        .or_else(|| cur.strip_prefix('λ'))
    {
        if let Some(arrow_pos) = find_top_level_fat_arrow(rest) {
            return type_is_vacuous(rest[arrow_pos + 2..].trim());
        }
    }
    type_is_vacuous(cur)
}

fn find_top_level_fat_arrow(src: &str) -> Option<usize> {
    let chars: Vec<(usize, char)> = src.char_indices().collect();
    let mut depth = 0usize;
    let mut idx = 0usize;
    while idx < chars.len() {
        match chars[idx].1 {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            '=' if depth == 0 && chars.get(idx + 1).map(|(_, c)| *c) == Some('>') => {
                return Some(chars[idx].0);
            }
            _ => {}
        }
        idx += 1;
    }
    None
}

fn split_top_level_comma(src: &str) -> Option<(&str, &str)> {
    let chars: Vec<(usize, char)> = src.char_indices().collect();
    let mut depth = 0usize;
    for (byte, ch) in chars {
        match ch {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => return Some((src[..byte].trim(), src[byte + 1..].trim())),
            _ => {}
        }
    }
    None
}

fn split_top_level_and(src: &str) -> Vec<String> {
    let chars: Vec<(usize, char)> = src.char_indices().collect();
    let mut depth = 0usize;
    let mut parts = Vec::new();
    let mut last_byte = 0usize;
    let mut idx = 0usize;
    while idx < chars.len() {
        let (byte, ch) = chars[idx];
        match ch {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            '∧' if depth == 0 => {
                parts.push(src[last_byte..byte].trim().to_string());
                last_byte = byte + ch.len_utf8();
            }
            '/' if depth == 0 && chars.get(idx + 1).map(|(_, c)| *c) == Some('\\') => {
                parts.push(src[last_byte..byte].trim().to_string());
                last_byte = byte + 2;
                idx += 1;
            }
            _ => {}
        }
        idx += 1;
    }
    parts.push(src[last_byte..].trim().to_string());
    parts
}

fn split_top_level_eq_or_ne(src: &str) -> Option<(&str, &str, bool)> {
    let chars: Vec<(usize, char)> = src.char_indices().collect();
    let mut depth = 0usize;
    let mut idx = 0usize;
    while idx < chars.len() {
        let (byte, ch) = chars[idx];
        match ch {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            '≠' if depth == 0 => {
                return Some((src[..byte].trim(), src[byte + ch.len_utf8()..].trim(), true));
            }
            '!' if depth == 0 && chars.get(idx + 1).map(|(_, c)| *c) == Some('=') => {
                return Some((src[..byte].trim(), src[byte + 2..].trim(), true));
            }
            '=' if depth == 0 => {
                let prev = idx
                    .checked_sub(1)
                    .and_then(|p| chars.get(p))
                    .map(|(_, c)| *c);
                let next = chars.get(idx + 1).map(|(_, c)| *c);
                if !matches!(prev, Some(':' | '<' | '>' | '!' | '='))
                    && !matches!(next, Some('=' | '>'))
                {
                    return Some((src[..byte].trim(), src[byte + 1..].trim(), false));
                }
            }
            _ => {}
        }
        idx += 1;
    }
    None
}

fn type_is_inhabited_source(ty: &str) -> bool {
    matches!(
        ty.trim().trim_start_matches("_root_.").trim(),
        "Nat" | "Int" | "Bool" | "String" | "Char" | "Unit" | "True" | "PUnit"
    )
}

fn split_arrow(ty: &str) -> Option<(String, String)> {
    let chars: Vec<char> = ty.chars().collect();
    let mut depth = 0usize;
    let mut idx = 0usize;
    while idx < chars.len() {
        match chars[idx] {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            '→' if depth == 0 => {
                return Some((
                    chars[..idx].iter().collect::<String>().trim().to_string(),
                    chars[idx + 1..]
                        .iter()
                        .collect::<String>()
                        .trim()
                        .to_string(),
                ));
            }
            '-' if depth == 0 && idx + 1 < chars.len() && chars[idx + 1] == '>' => {
                return Some((
                    chars[..idx].iter().collect::<String>().trim().to_string(),
                    chars[idx + 2..]
                        .iter()
                        .collect::<String>()
                        .trim()
                        .to_string(),
                ));
            }
            _ => {}
        }
        idx += 1;
    }
    None
}

fn safe_inhabited_value_binder_type(ty: &str, has_shadowed_value_types: bool) -> bool {
    if has_shadowed_value_types || type_is_vacuous(ty) {
        return false;
    }
    let mut cur = ty.trim();
    while let Some(inner) = strip_wrapping_parens(cur) {
        cur = inner;
    }
    let cur = cur.strip_prefix("_root_.").map_or(cur, str::trim);
    if matches!(
        cur,
        "Nat"
            | "Int"
            | "Bool"
            | "String"
            | "Char"
            | "UInt8"
            | "UInt16"
            | "UInt32"
            | "UInt64"
            | "USize"
            | "Word256"
            | "TurboLean.FastCheck.Word256"
            | "UInt256"
            | "Uint256"
            | "Int256"
            | "ByteArray"
            | "Unit"
            | "PUnit"
            | "StorageKey"
            | "TurboLean.Reflection.StorageKey"
            | "ContractState"
            | "TurboLean.Reflection.ContractState"
            | "Type"
    ) || is_universe_type(cur)
    {
        return true;
    }
    if let Some((lhs, rhs)) = split_top_level_product_op(cur) {
        return safe_inhabited_value_binder_type(&lhs, false)
            && safe_inhabited_value_binder_type(&rhs, false);
    }
    let Some((head_raw, args)) = split_type_application(cur) else {
        return false;
    };
    let head = head_raw.strip_prefix("_root_.").unwrap_or(head_raw);
    if head.contains('.') {
        return false;
    }
    match (head, args.as_slice()) {
        ("BitVec", [width]) => width_is_nonempty_bitvec(width),
        ("Fin", [bound]) => bound_is_positive_fin(bound),
        ("List" | "Array" | "Option", [_]) => true,
        ("Prod" | "PProd", [left, right]) => {
            safe_inhabited_value_binder_type(left, false)
                && safe_inhabited_value_binder_type(right, false)
        }
        _ => false,
    }
}

fn width_is_nonempty_bitvec(width: &str) -> bool {
    let w = strip_wrapping_parens(width).unwrap_or(width).trim();
    w.parse::<u64>().is_ok()
        || w.chars().next().is_some_and(is_ident_start) && w.chars().all(is_ident_continue)
}

fn bound_is_positive_fin(bound: &str) -> bool {
    let b = strip_wrapping_parens(bound).unwrap_or(bound).trim();
    if let Ok(val) = b.parse::<u64>() {
        return val > 0;
    }
    if let Some((lhs, rhs)) = b.rsplit_once('+') {
        if rhs.trim().parse::<u64>().is_ok_and(|inc| inc > 0) {
            let base = lhs.trim();
            return base.parse::<u64>().is_ok()
                || (base.chars().next().is_some_and(is_ident_start)
                    && base.chars().all(is_ident_continue));
        }
    }
    false
}

fn split_top_level_product_op(ty: &str) -> Option<(String, String)> {
    let chars: Vec<char> = ty.chars().collect();
    let mut depth = 0usize;
    for (idx, ch) in chars.iter().enumerate() {
        match ch {
            '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
            ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
            '×' if depth == 0 => {
                return Some((
                    chars[..idx].iter().collect::<String>().trim().to_string(),
                    chars[idx + 1..]
                        .iter()
                        .collect::<String>()
                        .trim()
                        .to_string(),
                ));
            }
            _ => {}
        }
    }
    None
}

fn split_type_application(ty: &str) -> Option<(&str, Vec<String>)> {
    let trimmed = ty.trim();
    if trimmed.contains('→') || trimmed.contains("->") {
        return None;
    }
    let mut tokens = Vec::new();
    let chars: Vec<(usize, char)> = trimmed.char_indices().collect();
    let mut idx = 0usize;
    while idx < chars.len() {
        while idx < chars.len() && chars[idx].1.is_whitespace() {
            idx += 1;
        }
        if idx >= chars.len() {
            break;
        }
        let start_byte = chars[idx].0;
        let mut depth = 0usize;
        while idx < chars.len() {
            match chars[idx].1 {
                '(' | '{' | '[' | '⦃' | '⟨' => depth += 1,
                ')' | '}' | ']' | '⦄' | '⟩' => depth = depth.saturating_sub(1),
                ch if depth == 0 && ch.is_whitespace() => break,
                _ => {}
            }
            idx += 1;
        }
        let end_byte = chars.get(idx).map_or(trimmed.len(), |(byte, _)| *byte);
        tokens.push(trimmed[start_byte..end_byte].to_string());
    }
    let head_len = tokens.first()?.len();
    let head = &trimmed[..head_len];
    Some((head, tokens.into_iter().skip(1).collect()))
}

fn subtype_predicate(ty: &str) -> Option<String> {
    let chars: Vec<char> = ty.trim().chars().collect();
    if chars.first() != Some(&'{') || chars.last() != Some(&'}') {
        return None;
    }
    let inner: String = chars[1..chars.len() - 1].iter().collect();
    let marker = inner.find("//")?;
    Some(inner[marker + 2..].trim().to_string())
}

fn has_top_level_colon_in_binders(part: &str) -> bool {
    let trimmed = part.trim();
    if split_top_level_colon(trimmed).is_some() {
        return true;
    }
    let chars: Vec<char> = trimmed.chars().collect();
    if chars.first() == Some(&'(') && chars.last() == Some(&')') {
        let mut depth = 0usize;
        let mut wraps_all = true;
        for (idx, ch) in chars.iter().enumerate() {
            match ch {
                '(' | '{' | '[' | '⦃' => depth += 1,
                ')' | '}' | ']' | '⦄' => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 && idx + 1 < chars.len() {
                        wraps_all = false;
                        break;
                    }
                }
                _ => {}
            }
        }
        if wraps_all {
            let inner: String = chars[1..chars.len() - 1].iter().collect();
            return has_top_level_colon_in_binders(&inner);
        }
    }
    false
}

fn mask_literals(src: &str) -> String {
    let mut out = src.as_bytes().to_vec();
    let mut i = 0usize;
    while i < src.len() {
        if let Some(span) = skip_lean_lexeme(src, i) {
            if span.is_literal && span.end > i + 1 {
                for byte in &mut out[i + 1..span.end - 1] {
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

fn skip_any(src: &str, byte_offsets: &[usize], idx: usize) -> Option<usize> {
    let byte = *byte_offsets.get(idx)?;
    let span = skip_lean_lexeme(src, byte)?;
    if !(span.is_comment || span.is_literal) {
        return None;
    }
    Some(byte_offsets.partition_point(|offset| *offset < span.end))
}

fn skip_any_lexeme(src: &str, byte_offsets: &[usize], idx: usize) -> Option<usize> {
    let byte = *byte_offsets.get(idx)?;
    let span = skip_lean_lexeme(src, byte)?;
    Some(byte_offsets.partition_point(|offset| *offset < span.end))
}

fn consume_in_command_prefix(
    src: &str,
    byte_offsets: &[usize],
    chars: &[char],
    start: usize,
    cmd_col: usize,
) -> Option<(usize, &'static str, PrefixAction)> {
    const PREFIXES: &[&str] = &[
        "set_option",
        "open",
        "universe",
        "universes",
        "variable",
        "variables",
        "include",
        "omit",
        "attribute",
        "export",
        "deriving",
        "instance",
        "notation",
        "infix",
        "infixl",
        "infixr",
        "prefix",
        "postfix",
        "macro",
        "macro_rules",
        "elab",
        "elab_rules",
        "syntax",
        "run_cmd",
        "run_elab",
        "drun_elab",
        "run_meta",
        "unif_hint",
        "binder_predicate",
        "simproc",
        "dsimproc",
        "builtin_simproc",
        "builtin_dsimproc",
        "cbv_simproc",
        "builtin_cbv_simproc",
        "grind_pattern",
        "def",
        "abbrev",
        "class",
        "structure",
        "inductive",
        "coinductive",
        "axiom",
        "opaque",
        "constant",
        "example",
        "theorem",
        "lemma",
        "#guard_msgs",
        "#guard_panic",
        "#info_trees",
    ];
    let byte_start = *byte_offsets.get(start)?;
    let tail = &src[byte_start..];
    if let Some(rest) = tail.strip_prefix("#time") {
        if rest.starts_with(char::is_whitespace) {
            let consumed = tail.len() - rest.len();
            return Some((
                byte_offsets.partition_point(|offset| *offset < byte_start + consumed),
                "#time",
                PrefixAction::Ignore,
            ));
        }
    }
    if let Some(rest) = tail.strip_prefix("#with_exporting") {
        if rest.starts_with(char::is_whitespace) {
            let consumed = tail.len() - rest.len();
            return Some((
                byte_offsets.partition_point(|offset| *offset < byte_start + consumed),
                "#with_exporting",
                PrefixAction::Malformed,
            ));
        }
    }
    let kw = *PREFIXES.iter().find(|&&kw| {
        tail.strip_prefix(kw)
            .is_some_and(|rest| rest.starts_with(char::is_whitespace) || rest.starts_with('('))
    })?;
    let mut i = start + kw.chars().count();
    let mut depth = 0usize;
    let mut body_is_ws = true;
    let mut pending_let_in = false;
    while i < chars.len() {
        if let Some(end) = skip_any(src, byte_offsets, i) {
            i = end;
            continue;
        }
        match chars[i] {
            '(' | '[' | '{' | '⦃' | '⟨' => {
                depth += 1;
                body_is_ws = false;
            }
            ')' | ']' | '}' | '⦄' | '⟩' => {
                depth = depth.saturating_sub(1);
                body_is_ws = false;
            }
            'l' | 'o' | 's' if depth == 0 && starts_scoped_term(chars, i) => {
                pending_let_in = true;
                body_is_ws = false;
            }
            't' | 'l'
                if depth == 0
                    && (token_is_keyword(chars, i, "theorem")
                        || token_is_keyword(chars, i, "lemma")) =>
            {
                body_is_ws = false;
            }
            ';' if depth == 0 => {
                pending_let_in = false;
                body_is_ws = false;
            }
            '\n' if depth == 0 => {
                if command_line_continues(src, byte_offsets, chars, kw, body_is_ws, cmd_col, i) {
                    body_is_ws = false;
                } else {
                    return None;
                }
            }
            'i' if depth == 0
                && token_is_keyword(chars, i, "in")
                && i > 0
                && chars[i - 1].is_whitespace() =>
            {
                if pending_let_in {
                    pending_let_in = false;
                    body_is_ws = false;
                } else {
                    let after = i + 2;
                    let raw: String = chars[start..after].iter().collect();
                    return Some((after, kw, classify_in_prefix(kw, &raw)));
                }
            }
            ch if !ch.is_whitespace() => body_is_ws = false,
            _ => {}
        }
        i += 1;
    }
    None
}

fn classify_in_prefix(kw: &str, raw: &str) -> PrefixAction {
    if matches!(kw, "variable" | "variables" | "include" | "omit") {
        return PrefixAction::Assumption(normalize_ws(raw));
    }
    if matches!(kw, "deriving" | "instance") {
        return PrefixAction::UnmodeledEnv;
    }
    if syntax_env_keyword(kw) {
        return PrefixAction::SyntaxEnv;
    }
    if kw == "attribute" && attr_mentions_instance_or_class(raw) {
        return PrefixAction::UnmodeledEnv;
    }
    if matches!(kw, "open" | "export")
        && RESERVED_INSTANCE_AND_TYPE_NAMES
            .iter()
            .any(|reserved| ident_mentioned(raw, reserved))
    {
        if kw == "export" || raw.contains('(') || ident_mentioned(raw, "renaming") {
            return PrefixAction::ShadowedValueEnv;
        }
        return PrefixAction::UnmodeledEnv;
    }
    if matches!(
        kw,
        "class" | "structure" | "inductive" | "coinductive" | "axiom" | "opaque"
    ) {
        return PrefixAction::ShadowedValueEnv;
    }
    if matches!(
        kw,
        "def" | "abbrev" | "constant" | "example" | "theorem" | "lemma"
    ) {
        if matches!(kw, "theorem" | "lemma") {
            return PrefixAction::ShadowedValueEnv;
        }
        let after_kw = raw.trim_start().trim_start_matches(kw).trim_start();
        let short: String = after_kw
            .chars()
            .take_while(|c| is_ident_continue(*c) || *c == '.' || *c == '«' || *c == '»')
            .collect();
        let short = short.rsplit('.').next().unwrap_or(short.as_str());
        let short_canon = crate::splitter::canonical_lean_name_component(short);
        if RESERVED_INSTANCE_AND_TYPE_NAMES.contains(&short_canon.as_str())
            || ident_mentioned(after_kw, "theorem")
            || ident_mentioned(after_kw, "lemma")
        {
            return PrefixAction::ShadowedValueEnv;
        }
    }
    PrefixAction::Ignore
}

fn dotted_name_multiline(
    src: &str,
    byte_offsets: &[usize],
    chars: &[char],
    mut pos: usize,
    n: usize,
    cmd_col: usize,
) -> (String, usize, bool) {
    let mut crossed = false;
    while pos < n && chars[pos].is_whitespace() && chars[pos] != '\n' {
        pos += 1;
    }
    if pos < n && chars[pos] == '\n' {
        let next = next_significant(src, byte_offsets, chars, pos + 1);
        if next < n && line_col(chars, next) > cmd_col && !is_top_level_command_start(chars, next) {
            pos = next;
            crossed = true;
        }
    }
    let (name, end) = dotted_name(src, byte_offsets, chars, pos, n);
    (name, end, crossed)
}

fn dotted_name(
    src: &str,
    byte_offsets: &[usize],
    chars: &[char],
    mut pos: usize,
    n: usize,
) -> (String, usize) {
    while pos < n && chars[pos].is_whitespace() && chars[pos] != '\n' {
        pos += 1;
    }
    let start = pos;
    while pos < n {
        if chars[pos] == '«' {
            if let Some(end) = skip_any_lexeme(src, byte_offsets, pos) {
                pos = end;
                continue;
            }
            break;
        }
        if is_ident_continue(chars[pos]) || chars[pos] == '.' {
            pos += 1;
        } else {
            break;
        }
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

fn matching_close(
    src: &str,
    byte_offsets: &[usize],
    chars: &[char],
    open_at: usize,
    open: char,
    close: char,
) -> Option<usize> {
    let mut depth = 0usize;
    let mut i = open_at;
    while i < chars.len() {
        if let Some(end) = skip_any(src, byte_offsets, i) {
            i = end;
            continue;
        }
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

fn instance_class_expr(text: &str) -> &str {
    split_top_level_colon(text).map_or_else(|| text.trim(), |(_, ty)| ty.trim())
}

fn instance_head_and_arg(text: &str) -> Option<(&str, &str)> {
    let class_expr = instance_class_expr(text);
    let mut parts = class_expr.split_whitespace();
    let head_raw = parts.next()?;
    let arg = parts.next()?;
    if parts.next().is_some() {
        return None;
    }
    let head = head_raw.rsplit('.').next()?;
    let valid_arg =
        arg.chars().next().is_some_and(is_ident_start) && arg.chars().all(is_ident_continue);
    valid_arg.then_some((head, arg))
}

fn has_matching_instance(all_binders: &[String], want_head: &str, want_arg: &str) -> bool {
    all_binders.iter().any(|other| {
        instance_head_and_arg(other).is_some_and(|(head, arg)| head == want_head && arg == want_arg)
    })
}

fn standard_instance(text: &str, all_binders: &[String], type_params: &BTreeSet<String>) -> bool {
    let class_expr = instance_class_expr(text);
    if class_expr.contains("→")
        || class_expr.contains("->")
        || class_expr.contains('∀')
        || class_expr.contains("forall")
    {
        return false;
    }
    let mut parts = class_expr.split_whitespace();
    let head_raw = parts.next().unwrap_or("");
    if head_raw.contains('.') && head_raw != "_root_" {
        return false;
    }
    let head = head_raw.rsplit('.').next().unwrap_or("");
    if matches!(head, "DecidablePred" | "DecidableRel") {
        return false;
    }
    let Some((head, arg)) = instance_head_and_arg(text) else {
        return false;
    };
    if TOTAL_INSTANCE_HEADS.contains(&head) {
        return true;
    }
    let allowed_lawful_target = PRIMITIVE_LAWFUL_TYPES.contains(&arg) || type_params.contains(arg);
    if !allowed_lawful_target {
        return false;
    }
    match head {
        "LawfulBEq" | "EquivBEq" => {
            PRIMITIVE_LAWFUL_TYPES.contains(&arg) || has_matching_instance(all_binders, "BEq", arg)
        }
        "LawfulHashable" => {
            PRIMITIVE_LAWFUL_TYPES.contains(&arg)
                || (has_matching_instance(all_binders, "BEq", arg)
                    && has_matching_instance(all_binders, "Hashable", arg))
        }
        _ => false,
    }
}

fn visibility_of(
    name: &str,
    public_names: &BTreeSet<String>,
    known: bool,
    is_module: bool,
    extra: Option<&DeclExtra>,
    malformed_scope: bool,
) -> &'static str {
    if !known {
        return "unresolved";
    }
    if extra.is_some_and(|row| row.is_private) {
        return "private";
    }
    if !is_module {
        return "public";
    }
    if extra.is_some_and(|row| row.explicit_public) {
        return "public";
    }
    if malformed_scope {
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
    prop_local_defs: &'a [(String, Vec<String>, String)],
    hygiene: &'a crate::splitter::HygieneReport,
    audit: &'a Value,
    has_unmodeled_instance_env: bool,
    has_unmodeled_syntax_env: bool,
    has_shadowed_value_types: bool,
}

fn card_for(
    ctx: &FileCardCtx<'_>,
    decl: &ExtractedDecl,
    effective_name: &str,
    visibility: &str,
    extra: Option<&DeclExtra>,
    detail: Option<&Value>,
) -> Value {
    let mut param_binders = Vec::new();
    let mut hypothesis_text = Vec::new();
    let mut seen_type_params: BTreeSet<String> = BTreeSet::new();
    let mut seen_prop_params: BTreeSet<String> = BTreeSet::new();
    let mut seen_value_params: BTreeSet<String> = BTreeSet::new();
    let mut unmodeled_binder = false;
    for (vars, ty) in &decl.binders {
        if !binder_type_is_modeled(
            ty,
            &seen_type_params,
            &seen_prop_params,
            &seen_value_params,
            ctx.prop_local_defs,
        ) && !(is_known_binder_value_type(ty)
            && safe_inhabited_value_binder_type(ty, ctx.has_shadowed_value_types))
            && !is_universe_type(ty)
            && ty.trim() != "Prop"
            && ty.trim() != "_root_.Prop"
            && !seen_type_params.contains(ty.trim())
        {
            unmodeled_binder = true;
        }
        if is_universe_type(ty) && vars.iter().all(|var| is_ident_token(var)) {
            seen_type_params.extend(vars.iter().cloned());
            param_binders.push(json!({"vars": vars, "type": ty}));
        } else if (ty.trim() == "Prop" || ty.trim() == "_root_.Prop")
            && vars.iter().all(|var| is_ident_token(var))
        {
            seen_prop_params.extend(vars.iter().cloned());
            param_binders.push(json!({"vars": vars, "type": ty}));
        } else if seen_type_params.contains(ty.trim())
            || (is_known_binder_value_type(ty)
                && safe_inhabited_value_binder_type(ty, ctx.has_shadowed_value_types))
        {
            seen_value_params.extend(vars.iter().cloned());
            param_binders.push(json!({"vars": vars, "type": ty}));
        } else if binder_type_is_modeled(
            ty,
            &seen_type_params,
            &seen_prop_params,
            &seen_value_params,
            ctx.prop_local_defs,
        ) {
            let names = vars.join(" ");
            hypothesis_text.push(format!("({names} : {ty})"));
        } else {
            unmodeled_binder = true;
            let names = vars.join(" ");
            hypothesis_text.push(format!("({names} : {ty})"));
        }
    }
    let parts = peel_implication_telescope(&decl.prop_str);
    let conclusion = if parts.len() <= 1 {
        parts.first().cloned().unwrap_or_default()
    } else {
        hypothesis_text.extend_from_slice(&parts[..parts.len() - 1]);
        parts.last().cloned().unwrap_or_default()
    };
    let vacuous_hypothesis = hypothesis_text
        .iter()
        .any(|text| hypothesis_is_vacuous(text));
    let unmodeled_hypothesis = !seen_prop_params.is_empty()
        || hypothesis_text.iter().any(|text| {
            !hypothesis_is_modeled(
                text,
                &seen_type_params,
                &seen_prop_params,
                &seen_value_params,
                ctx.prop_local_defs,
            )
        })
        || !conclusion_is_modeled(
            &conclusion,
            &seen_type_params,
            &seen_prop_params,
            &seen_value_params,
            ctx.prop_local_defs,
        );
    let instance_binders = extra
        .map(|row| row.instance_binders.clone())
        .unwrap_or_default();
    let context_assumptions = extra
        .map(|row| row.context_assumptions.clone())
        .unwrap_or_default();
    let mut extraction_warnings = Vec::new();
    let nonstandard: Vec<&str> = instance_binders
        .iter()
        .enumerate()
        .filter(|(idx, binder)| {
            let prior = extra.map_or(BTreeSet::new(), |row| {
                row.ordered_type_params
                    .get(*idx)
                    .cloned()
                    .unwrap_or_default()
            });
            !standard_instance(binder, &instance_binders, &prior)
        })
        .map(|(_, binder)| binder.as_str())
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
    if extra.is_none()
        || extra.is_some_and(|row| row.saw_unparsed_binder || row.saw_unparsed_telescope)
        || vacuous_hypothesis
        || unmodeled_binder
        || unmodeled_hypothesis
    {
        extraction_warnings.push(
            "declaration modifiers, attributes, or binders were not fully parsed".to_string(),
        );
    }
    if ctx.has_unmodeled_instance_env && !instance_binders.is_empty() {
        extraction_warnings.push(
            "file-local instances, notation, or shadowed standard names leave instance binders unverified"
                .to_string(),
        );
    }
    if ctx.has_unmodeled_syntax_env {
        extraction_warnings
            .push("file-level syntax, macros, or elaborators can rewrite statements".to_string());
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
        "decl": effective_name,
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
            "stub_defs": detail
                .and_then(|row| row.get("stub_defs"))
                .cloned()
                .or_else(|| ctx.audit.get("stub_defs").cloned())
                .unwrap_or(json!([])),
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

fn is_lean_subscript_alnum(c: char) -> bool {
    let v = c as u32;
    (0x2080..=0x2089).contains(&v)
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
        || v == 0x2c7c
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || is_lean_letter_like(c)
}

fn is_ident_continue(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || matches!(c, '_' | '\'' | '!' | '?')
        || is_lean_letter_like(c)
        || is_lean_subscript_alnum(c)
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
