use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use crate::splitter::{self, split_lean_source};

use super::*;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImpactReport {
    pub file: String,
    pub module_name: Option<String>,
    pub base_rev: Option<String>,
    pub is_module: bool,
    pub edit_class: String,
    pub public_signature_changed: bool,
    pub meta_signature_changed: bool,
    pub public_signature_digest: String,
    pub meta_signature_digest: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub baseline_public_signature_digest: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub baseline_meta_signature_digest: Option<String>,
    pub direct_dependents: Vec<String>,
    pub transitive_dependents: Vec<String>,
    pub pruned_dependents: Vec<String>,
    pub affected_modules: Vec<String>,
    pub affected_files: Vec<String>,
    pub estimated_declarations: usize,
    pub total_downstream_declarations: usize,
}

pub fn compute_impact_report(
    file: PathBuf,
    project_dir: Option<PathBuf>,
    rev: Option<String>,
) -> Result<ImpactReport> {
    let target_canon = file
        .canonicalize()
        .with_context(|| format!("Target file does not exist: {}", file.display()))?;
    anyhow::ensure!(
        target_canon.is_file(),
        "`turbo-lean impact` expects a `.lean` file path, got directory: {}",
        target_canon.display()
    );
    let root_guess = match project_dir {
        Some(p) => p,
        None => find_project_root(&target_canon),
    };
    let canon_dir = root_guess
        .canonicalize()
        .unwrap_or_else(|_| root_guess.clone());
    let rel_file = target_canon
        .strip_prefix(&canon_dir)
        .map(|p| p.to_string_lossy().replace('\\', "/"))
        .unwrap_or_else(|_| target_canon.to_string_lossy().replace('\\', "/"));

    let cur_src = fs::read_to_string(&target_canon)
        .with_context(|| format!("Failed to read {}", target_canon.display()))?;
    let cur_sig = splitter::extract_public_signature(&cur_src);
    let cur_split = split_lean_source(&cur_src, &[]);

    let explicit_rev = rev.is_some();
    let effective_rev = match rev {
        Some(r) => Some(r),
        None => {
            if canon_dir.join(".git").exists()
                || target_canon.ancestors().any(|a| a.join(".git").exists())
            {
                Some("HEAD".to_string())
            } else {
                None
            }
        }
    };
    let baseline_src = match effective_rev.as_deref() {
        Some(r) => read_git_baseline_source_checked(&target_canon, r, explicit_rev)?,
        None => None,
    };

    let (
        edit_class,
        pub_changed,
        meta_changed,
        base_pub_dig,
        base_meta_dig,
        cuts_off_pub,
        cuts_off_meta,
    ) = if let Some(ref b_src) = baseline_src {
        if b_src == &cur_src {
            (
                "unchanged".to_string(),
                false,
                false,
                Some(cur_sig.public_signature_digest.clone()),
                Some(cur_sig.meta_signature_digest.clone()),
                true,
                true,
            )
        } else {
            let base_split = split_lean_source(b_src, &[]);
            let base_sig = splitter::extract_public_signature(b_src);
            let proof_body_only = base_split.interface_hash == cur_split.interface_hash
                && base_split.shards.len() == cur_split.shards.len()
                && base_split
                    .shards
                    .iter()
                    .zip(cur_split.shards.iter())
                    .all(|(a, b)| a.decl_name() == b.decl_name() && a.stmt_hash == b.stmt_hash)
                && !cur_sig
                    .public_signature_digest
                    .starts_with("pubsig-invalid:")
                && !base_sig
                    .public_signature_digest
                    .starts_with("pubsig-invalid:")
                && cur_sig.public_signature_digest == base_sig.public_signature_digest
                && cur_sig.meta_signature_digest == base_sig.meta_signature_digest;
            if proof_body_only {
                (
                    "proof_body_only".to_string(),
                    false,
                    false,
                    Some(base_sig.public_signature_digest),
                    Some(base_sig.meta_signature_digest),
                    true,
                    true,
                )
            } else if cur_sig.is_module
                && base_sig.is_module
                && !cur_sig
                    .public_signature_digest
                    .starts_with("pubsig-invalid:")
                && !base_sig
                    .public_signature_digest
                    .starts_with("pubsig-invalid:")
                && cur_sig.public_signature_digest == base_sig.public_signature_digest
            {
                let meta_same = cur_sig.meta_signature_digest == base_sig.meta_signature_digest;
                let cls = if meta_same {
                    "private_module_edit"
                } else {
                    "meta_only_module_edit"
                };
                (
                    cls.to_string(),
                    false,
                    !meta_same,
                    Some(base_sig.public_signature_digest),
                    Some(base_sig.meta_signature_digest),
                    true,
                    meta_same,
                )
            } else {
                let pub_diff = cur_sig.public_signature_digest != base_sig.public_signature_digest;
                let meta_diff = cur_sig.meta_signature_digest != base_sig.meta_signature_digest;
                let cls = if cur_sig.is_module {
                    "public_signature_edit"
                } else {
                    "non_module_interface_edit"
                };
                (
                    cls.to_string(),
                    pub_diff || !cur_sig.is_module,
                    meta_diff || !cur_sig.is_module,
                    Some(base_sig.public_signature_digest),
                    Some(base_sig.meta_signature_digest),
                    false,
                    false,
                )
            }
        }
    } else {
        let cls = if cur_sig.is_module {
            "unbaselined_module"
        } else {
            "unbaselined_non_module"
        };
        (cls.to_string(), true, true, None, None, false, false)
    };

    let mut module_name: Option<String> = None;
    let mut direct_dependents: Vec<String> = Vec::new();
    let mut full_dependents: Vec<String> = Vec::new();
    let mut active_dependents: Vec<String> = Vec::new();
    let mut pruned_dependents: Vec<String> = Vec::new();
    let mut affected_modules: Vec<String> = Vec::new();
    let mut affected_files: Vec<String> = Vec::new();
    let mut mod_to_path: HashMap<String, PathBuf> = HashMap::new();

    if has_lake_config(&canon_dir) {
        let closure = compute_project_dependent_closure_inner(
            &canon_dir,
            std::slice::from_ref(&rel_file),
            false,
            true,
        )?;
        if let Some(m) = closure.edited_dag_modules.first() {
            module_name = Some(m.clone());
        } else {
            for (m, s) in &closure.standalone_all {
                if s.src_path == target_canon {
                    module_name = Some(m.clone());
                    break;
                }
            }
        }
        if let Some(ref dag) = closure.dag {
            for (m, n) in &dag.nodes {
                mod_to_path.insert(m.clone(), n.src_path.clone());
            }
        }
        for (m, s) in &closure.standalone_all {
            mod_to_path
                .entry(m.clone())
                .or_insert_with(|| s.src_path.clone());
        }

        let target_mod_opt = module_name.clone();
        if let Some(ref target_mod) = target_mod_opt {
            if let Some(ref dag) = closure.dag {
                for (m, n) in &dag.nodes {
                    if m != target_mod && n.direct_dag_deps.iter().any(|d| d == target_mod) {
                        direct_dependents.push(m.clone());
                    }
                }
            }
            for (m, s) in &closure.standalone_all {
                if m != target_mod && s.imports.iter().any(|d| d == target_mod) {
                    direct_dependents.push(m.clone());
                }
            }
            direct_dependents.sort();
            direct_dependents.dedup();
        }

        let mut full_set: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        if let Some(ref mods) = closure.dag_modules {
            for m in mods {
                if module_name.as_deref() != Some(m.as_str()) {
                    full_set.insert(m.clone());
                }
            }
        }
        for s in &closure.standalone_modules {
            if module_name.as_deref() != Some(s.module_name.as_str()) {
                full_set.insert(s.module_name.clone());
            }
        }
        full_dependents = full_set.iter().cloned().collect();

        if edit_class == "unchanged" {
            pruned_dependents = full_dependents.clone();
        } else if edit_class == "proof_body_only" {
            if let Some(ref tm) = target_mod_opt {
                affected_modules.push(tm.clone());
            }
            affected_files.push(rel_file.clone());
            pruned_dependents = full_dependents.clone();
        } else if let Some(dag) = closure
            .dag
            .as_ref()
            .filter(|_| cuts_off_pub && !closure.edited_dag_modules.is_empty())
        {
            let mut verdicts = HashMap::new();
            for m in &closure.edited_dag_modules {
                verdicts.insert(
                    m.clone(),
                    ModuleCutoffVerdict {
                        cuts_off_public: cuts_off_pub,
                        cuts_off_meta,
                    },
                );
            }
            // For static blast-radius prediction in `impact`, evaluate import-visibility graph
            // pruning purely from source headers (without requiring prebuilt on-disk `.olean`s).
            let shared_lib_mods: HashSet<&str> = dag
                .shared_libs
                .iter()
                .flat_map(|sl| sl.local_modules.iter().map(String::as_str))
                .collect();
            let edited_dag_set: HashSet<&str> = closure
                .edited_dag_modules
                .iter()
                .map(String::as_str)
                .collect();
            let mut dag_dirty: std::collections::BTreeSet<String> =
                closure.edited_dag_modules.iter().cloned().collect();
            let mut standalone_dirty: std::collections::BTreeSet<String> =
                std::collections::BTreeSet::new();
            let mut changed = true;
            while changed {
                changed = false;
                for (m, n) in &dag.nodes {
                    if dag_dirty.contains(m) {
                        continue;
                    }
                    let (vis_map, _) = crate::module_builder::compute_node_dep_visibility_map(
                        &closure.cfg,
                        dag,
                        n,
                    );
                    let trig = n.direct_dag_deps.iter().any(|d| {
                        if standalone_dirty.contains(d) {
                            return true;
                        }
                        if !dag_dirty.contains(d) {
                            return false;
                        }
                        let vis = if !n.is_module
                            || n.precompile_modules
                            || n.is_exe_target
                            || n.needs_dynlib
                            || shared_lib_mods.contains(m.as_str())
                        {
                            crate::module_builder::DepImportVisibility::All
                        } else {
                            vis_map
                                .get(d)
                                .copied()
                                .unwrap_or(crate::module_builder::DepImportVisibility::All)
                        };
                        if edited_dag_set.contains(d.as_str()) {
                            if let Some(v) = verdicts.get(d) {
                                return match vis {
                                    crate::module_builder::DepImportVisibility::PublicExport => {
                                        !v.cuts_off_public
                                    }
                                    crate::module_builder::DepImportVisibility::MetaExport => {
                                        !v.cuts_off_meta
                                    }
                                    crate::module_builder::DepImportVisibility::All => true,
                                };
                            }
                        }
                        true
                    });
                    if trig {
                        dag_dirty.insert(m.clone());
                        changed = true;
                    }
                }
                for (m, s) in &closure.standalone_all {
                    if standalone_dirty.contains(m) {
                        continue;
                    }
                    let trig = s.imports.iter().any(|d| {
                        if standalone_dirty.contains(d) {
                            return true;
                        }
                        if !dag_dirty.contains(d) {
                            return false;
                        }
                        let vis = if !s.is_module {
                            crate::module_builder::DepImportVisibility::All
                        } else {
                            s.import_visibilities
                                .get(d)
                                .copied()
                                .unwrap_or(crate::module_builder::DepImportVisibility::All)
                        };
                        if edited_dag_set.contains(d.as_str()) {
                            if let Some(v) = verdicts.get(d) {
                                return match vis {
                                    crate::module_builder::DepImportVisibility::PublicExport => {
                                        !v.cuts_off_public
                                    }
                                    crate::module_builder::DepImportVisibility::MetaExport => {
                                        !v.cuts_off_meta
                                    }
                                    crate::module_builder::DepImportVisibility::All => true,
                                };
                            }
                        }
                        true
                    });
                    if trig {
                        standalone_dirty.insert(m.clone());
                        changed = true;
                    }
                }
            }
            let mut active_set: std::collections::BTreeSet<String> =
                std::collections::BTreeSet::new();
            for m in dag_dirty.into_iter().chain(standalone_dirty) {
                affected_modules.push(m.clone());
                if module_name.as_deref() != Some(m.as_str()) {
                    active_set.insert(m);
                }
            }
            affected_modules.sort();
            affected_modules.dedup();
            active_dependents = active_set.iter().cloned().collect();
            pruned_dependents = full_set.difference(&active_set).cloned().collect();
        } else {
            if let Some(ref tm) = target_mod_opt {
                affected_modules.push(tm.clone());
            }
            for d in &full_dependents {
                affected_modules.push(d.clone());
            }
            affected_modules.sort();
            affected_modules.dedup();
            active_dependents = full_dependents.clone();
        }
    } else if edit_class != "unchanged" {
        affected_files.push(rel_file.clone());
    }

    if affected_files.is_empty() && !affected_modules.is_empty() {
        for m in &affected_modules {
            if let Some(p) = mod_to_path.get(m) {
                let rel = p
                    .strip_prefix(&canon_dir)
                    .map(|r| r.to_string_lossy().replace('\\', "/"))
                    .unwrap_or_else(|_| p.to_string_lossy().replace('\\', "/"));
                affected_files.push(rel);
            }
        }
        affected_files.sort();
        affected_files.dedup();
    }

    let count_decls_in_path = |p: &Path| -> usize {
        fs::read_to_string(p)
            .ok()
            .map(|s| split_lean_source(&s, &[]).shards.len())
            .unwrap_or(0)
    };
    let mut total_downstream_declarations = 0usize;
    for m in &full_dependents {
        if let Some(p) = mod_to_path.get(m) {
            total_downstream_declarations += count_decls_in_path(p);
        }
    }
    let estimated_declarations = if edit_class == "unchanged" {
        0
    } else if edit_class == "proof_body_only" {
        if let Some(ref b_src) = baseline_src {
            let base_split = split_lean_source(b_src, &[]);
            base_split
                .shards
                .iter()
                .zip(cur_split.shards.iter())
                .filter(|(a, b)| a.proof_hash != b.proof_hash)
                .count()
        } else {
            cur_split.shards.len()
        }
    } else if !affected_modules.is_empty() {
        affected_modules
            .iter()
            .filter_map(|m| mod_to_path.get(m))
            .map(|p| count_decls_in_path(p))
            .sum()
    } else {
        cur_split.shards.len()
    };

    Ok(ImpactReport {
        file: rel_file,
        module_name,
        base_rev: effective_rev,
        is_module: cur_sig.is_module,
        edit_class,
        public_signature_changed: pub_changed,
        meta_signature_changed: meta_changed,
        public_signature_digest: cur_sig.public_signature_digest,
        meta_signature_digest: cur_sig.meta_signature_digest,
        baseline_public_signature_digest: base_pub_dig,
        baseline_meta_signature_digest: base_meta_dig,
        direct_dependents,
        transitive_dependents: active_dependents,
        pruned_dependents,
        affected_modules,
        affected_files,
        estimated_declarations,
        total_downstream_declarations,
    })
}

/// Strictly read-only blast-radius and public-signature impact analyzer (`turbo-lean impact <file>`).
/// Never mutates the worktree, `.lake/build`, or `TurboStore`.
pub fn run_impact_command(
    json: bool,
    file: PathBuf,
    project_dir: Option<PathBuf>,
    rev: Option<String>,
) -> Result<()> {
    let report = compute_impact_report(file, project_dir, rev)?;
    if json {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        println!(
            "[turbo-lean] impact: {} (module: {}, edit_class: {})",
            report.file,
            report.module_name.as_deref().unwrap_or("<standalone>"),
            report.edit_class
        );
        println!(
            "  public_signature_changed: {} | meta_signature_changed: {} | is_module: {}",
            report.public_signature_changed, report.meta_signature_changed, report.is_module
        );
        println!(
            "  dependents: {} direct, {} active transitive ({} pruned by cutoff), ~{} declarations affected ({} total downstream)",
            report.direct_dependents.len(),
            report.transitive_dependents.len(),
            report.pruned_dependents.len(),
            report.estimated_declarations,
            report.total_downstream_declarations
        );
    }
    Ok(())
}
