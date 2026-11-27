use super::*;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct NativeBuildReport {
    pub modules_total: usize,
    pub modules_compiled: usize,
    pub modules_cached: usize,
    pub modules_up_to_date_reused: usize,
    pub waves_count: usize,
    pub config_digest: String,
    pub compiled_modules: Vec<String>,
    pub cached_modules: Vec<String>,
    #[serde(default)]
    pub cone_source_paths: Vec<PathBuf>,
    pub bwrap_used: bool,
    #[serde(skip)]
    pub staged_target_paths: Vec<PathBuf>,
}

pub fn run_seed_oleans_command(
    store: &mut TurboStore,
    json_output: bool,
    project_dir: PathBuf,
    targets: Vec<String>,
    jobs: usize,
) -> Result<()> {
    let t0 = std::time::Instant::now();
    let prev_jobs = std::env::var_os("TURBO_LEAN_JOBS");
    if jobs > 0 {
        std::env::set_var("TURBO_LEAN_JOBS", jobs.to_string());
    }
    let build_res = build_project_modules_native(
        store,
        &project_dir,
        &targets,
        "trusted",
        1,
        false,
        json_output,
        None,
    );
    match prev_jobs {
        Some(v) => std::env::set_var("TURBO_LEAN_JOBS", v),
        None if jobs > 0 => std::env::remove_var("TURBO_LEAN_JOBS"),
        None => {}
    }
    let report = build_res?;
    let elapsed_ms = t0.elapsed().as_millis() as u64;
    if json_output {
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
                "status": "seeded_oleans",
                "targets": targets,
                "modules_total": report.modules_total,
                "modules_up_to_date_reused": report.modules_up_to_date_reused,
                "modules_cached": report.modules_cached,
                "modules_compiled": report.modules_compiled,
                "config_digest": report.config_digest,
                "elapsed_ms": elapsed_ms,
            }))?
        );
    } else {
        println!(
            "[turbo-lean] SEED-OLEANS ({} modules: {} reused, {} cached, {} compiled in {} ms)",
            report.modules_total,
            report.modules_up_to_date_reused,
            report.modules_cached,
            report.modules_compiled,
            elapsed_ms,
        );
    }
    Ok(())
}
pub(crate) fn seed_verified_fresh_modules_into_disposable_snapshot(
    src_cfg: &ProjectConfig,
    dst_project: &Path,
    targets: &[String],
) -> Result<()> {
    let dst_cfg = resolve_project_config_with_trust(dst_project, false)?;
    if dst_cfg.lean_githash != src_cfg.lean_githash
        || dst_cfg.toolchain != src_cfg.toolchain
        || dst_cfg.canonical_config_digest != src_cfg.canonical_config_digest
    {
        return Ok(());
    }
    let dst_dag = build_module_dag_for_trusted_statement(&dst_cfg, targets)?;
    let src_root_lib = src_cfg
        .root_pkg
        .pkg_root
        .join(&src_cfg.root_pkg.build_dir)
        .join(&src_cfg.root_pkg.lean_lib_dir);
    let src_root_ir = src_cfg
        .root_pkg
        .pkg_root
        .join(&src_cfg.root_pkg.build_dir)
        .join(&src_cfg.root_pkg.ir_dir);
    let dst_root_lib = dst_cfg
        .root_pkg
        .pkg_root
        .join(&dst_cfg.root_pkg.build_dir)
        .join(&dst_cfg.root_pkg.lean_lib_dir);
    let dst_root_ir = dst_cfg
        .root_pkg
        .pkg_root
        .join(&dst_cfg.root_pkg.build_dir)
        .join(&dst_cfg.root_pkg.ir_dir);
    let expected_lean_gh_h = format!("{:016x}", lake_hash_bytes(dst_cfg.lean_githash.as_bytes()));
    let nil_hex = format!("{LAKE_NIL_HASH:016x}");
    let mut exp_memo: HashMap<(String, bool), LakeModuleExportInfo> = HashMap::new();
    let mut dirty_mods: HashSet<String> = HashSet::new();
    let copy_artifact = |src_p: &Path, dst_p: &Path| -> Result<()> {
        if let Some(parent) = dst_p.parent() {
            fs::create_dir_all(parent)?;
        }
        if dst_p.symlink_metadata().is_err() {
            let target = src_p.canonicalize().unwrap_or_else(|_| src_p.to_path_buf());
            fs::copy(&target, dst_p)?;
        }
        Ok(())
    };
    for wave in &dst_dag.waves {
        for mod_name in wave {
            let Some(node) = dst_dag.nodes.get(mod_name) else {
                dirty_mods.insert(mod_name.clone());
                continue;
            };
            if !node.is_root_pkg {
                continue;
            }
            if node.direct_dag_deps.iter().any(|d| dirty_mods.contains(d)) {
                dirty_mods.insert(mod_name.clone());
                continue;
            }
            let Ok(dst_src_raw) = fs::read_to_string(&node.src_path) else {
                dirty_mods.insert(mod_name.clone());
                continue;
            };
            if node_source_has_disallowed_elab_host_effects(&dst_cfg, node, &dst_src_raw) {
                dirty_mods.insert(mod_name.clone());
                continue;
            }
            let header = parse_header_info(&dst_src_raw);
            if header.header_error.is_some() {
                dirty_mods.insert(mod_name.clone());
                continue;
            }
            let rel_slash = module_name_to_rel_slash(mod_name);
            let src_olean = src_root_lib.join(format!("{}.olean", rel_slash));
            let sidecars_ok = verify_module_lake_sidecars_inner_opts_ext(
                &src_olean,
                node.needs_c.then_some(src_root_ir.as_path()),
                &rel_slash,
                &dst_src_raw,
                node.is_module,
                node.needs_c,
                false,
                true,
                !node.needs_c,
            );
            if sidecars_ok.is_err() {
                dirty_mods.insert(mod_name.clone());
                continue;
            }
            let Ok(tb) = fs::read(src_olean.with_extension("trace")) else {
                dirty_mods.insert(mod_name.clone());
                continue;
            };
            let Ok(tv) = serde_json::from_slice::<serde_json::Value>(&tb) else {
                dirty_mods.insert(mod_name.clone());
                continue;
            };
            let mut import_entries = Vec::new();
            let mut visiting = HashSet::new();
            let mut imp_dirty = false;
            for imp in &header.import_specs {
                if dirty_mods.contains(&imp.module) {
                    imp_dirty = true;
                    break;
                }
                let is_ws_or_pkg = dst_dag.nodes.contains_key(&imp.module)
                    || node
                        .external_olean_deps
                        .iter()
                        .any(|(m, _)| m == &imp.module)
                    || resolve_module_in_package(&dst_cfg.root_pkg, true, &imp.module).is_some()
                    || dst_cfg
                        .dep_pkgs
                        .iter()
                        .any(|dp| resolve_module_in_package(dp, false, &imp.module).is_some());
                if !is_ws_or_pkg {
                    if is_builtin_toolchain_module(
                        &dst_cfg.toolchain_lib_lean,
                        Some(&dst_cfg.lean_githash),
                        &imp.module,
                    ) {
                        continue;
                    }
                    imp_dirty = true;
                    break;
                }
                let Ok(exp_info) = compute_lake_export_info_opts(
                    &dst_cfg,
                    &dst_dag,
                    node,
                    &imp.module,
                    &mut exp_memo,
                    &mut visiting,
                    false,
                ) else {
                    imp_dirty = true;
                    break;
                };
                import_entries.extend(lake_import_trace_entries(node.is_module, imp, &exp_info));
            }
            if imp_dirty {
                dirty_mods.insert(mod_name.clone());
                continue;
            }
            if tv.get("inputs").is_none() {
                let raw_imp_dynlibs = compute_module_raw_import_dynlibs(&dst_dag, node);
                let actual_dep_h = tv
                    .get("depHash")
                    .and_then(|v| v.as_str())
                    .filter(|s| is_valid_16hex_hash(s))
                    .and_then(|s| u64::from_str_radix(s, 16).ok());
                let expected_dep_h = compute_expected_lake_module_dep_hash(
                    &dst_cfg,
                    &node.pkg_root,
                    &node.pkg_name,
                    &node.pkg_base_name,
                    &node.target_name,
                    node.is_exe_target,
                    &node.module_name,
                    node.is_module,
                    node.platform_independent,
                    &node.lean_options,
                    &node.strong_args,
                    &src_cfg.root_pkg.pkg_root.join(
                        node.src_path
                            .strip_prefix(&dst_cfg.root_pkg.pkg_root)
                            .unwrap_or(&node.src_path),
                    ),
                    lake_hash_text(&dst_src_raw),
                    import_entries,
                    &raw_imp_dynlibs,
                );
                if actual_dep_h.is_none() || actual_dep_h != expected_dep_h {
                    dirty_mods.insert(mod_name.clone());
                    continue;
                }
            } else {
                let nested = lake_trace_uses_nested_mod_deps(&dst_cfg.toolchain);
                let base_idx = if nested {
                    1usize
                } else if node.platform_independent == Some(false) {
                    3usize
                } else {
                    2usize
                };
                if tv
                    .pointer(&format!("/inputs/{}/1", base_idx))
                    .and_then(|v| v.as_str())
                    != Some(expected_lean_gh_h.as_str())
                {
                    dirty_mods.insert(mod_name.clone());
                    continue;
                }
                if tv
                    .pointer(&format!("/inputs/{}/0", base_idx + 2))
                    .and_then(|v| v.as_str())
                    != Some("options")
                    || tv
                        .pointer(&format!("/inputs/{}/1", base_idx + 2))
                        .is_none_or(|v| !verify_trace_options_value(&node.lean_options, v))
                {
                    dirty_mods.insert(mod_name.clone());
                    continue;
                }
                let expected_is_mod_h = format!(
                    "{:016x}",
                    lake_mix_hash(LAKE_NIL_HASH, if node.is_module { 11 } else { 13 })
                );
                if tv
                    .pointer(&format!("/inputs/{}/1", base_idx + 3))
                    .and_then(|v| v.as_str())
                    != Some(expected_is_mod_h.as_str())
                {
                    dirty_mods.insert(mod_name.clone());
                    continue;
                }
                let expected_lean_args_h = format!(
                    "{:016x}",
                    node.strong_args.iter().fold(LAKE_NIL_HASH, |acc, a| {
                        lake_mix_hash(acc, lake_hash_bytes(a.as_bytes()))
                    })
                );
                if tv
                    .pointer(&format!("/inputs/{}/1", base_idx + 6))
                    .and_then(|v| v.as_str())
                    != Some(expected_lean_args_h.as_str())
                {
                    dirty_mods.insert(mod_name.clone());
                    continue;
                }
                let base_pkg_name = if node.pkg_base_name.is_empty() {
                    &node.pkg_name
                } else {
                    &node.pkg_base_name
                };
                let pkg_base_ident = if base_pkg_name.contains('-') {
                    format!("«{}»", base_pkg_name)
                } else {
                    base_pkg_name.clone()
                };
                let mut extra_dep_entries = vec![serde_json::json!([
                    format!("@{}:extraDep", pkg_base_ident),
                    nil_hex
                ])];
                extra_dep_entries.extend(lake_needs_trace_entries(&dst_cfg, node));
                let expected_extra_h =
                    lake_input_hash(&serde_json::Value::Array(extra_dep_entries)).ok();
                let actual_extra_ptr = if nested {
                    "/inputs/0/1/0/1/0/1"
                } else {
                    "/inputs/0/1/0/1"
                };
                let actual_extra_h = tv
                    .pointer(actual_extra_ptr)
                    .and_then(|v| lake_input_hash(v).ok());
                if expected_extra_h.is_none() || expected_extra_h != actual_extra_h {
                    dirty_mods.insert(mod_name.clone());
                    continue;
                }
                let expected_imps_val = if import_entries.is_empty() {
                    serde_json::json!("00000000000006bb")
                } else {
                    serde_json::Value::Array(import_entries)
                };
                let expected_imps_h = lake_input_hash(&expected_imps_val).ok();
                let actual_imps_h = recorded_trace_imports_hash(&tv);
                if expected_imps_h.is_none() || expected_imps_h != actual_imps_h {
                    dirty_mods.insert(mod_name.clone());
                    continue;
                }
            }
            for suffix in [
                ".olean",
                ".olean.hash",
                ".olean.server",
                ".olean.server.hash",
                ".olean.private",
                ".olean.private.hash",
                ".ilean",
                ".ilean.hash",
                ".ir",
                ".ir.hash",
                ".ir.sig",
                ".ir.sig.hash",
                ".trace",
            ] {
                let s = src_root_lib.join(format!("{rel_slash}{suffix}"));
                if s.is_file() {
                    let d = dst_root_lib.join(format!("{rel_slash}{suffix}"));
                    copy_artifact(&s, &d)?;
                }
            }
            if node.needs_c {
                for suffix in [".c", ".c.hash"] {
                    let s = src_root_ir.join(format!("{rel_slash}{suffix}"));
                    if s.is_file() {
                        let d = dst_root_ir.join(format!("{rel_slash}{suffix}"));
                        copy_artifact(&s, &d)?;
                    }
                }
            }
        }
    }
    Ok(())
}

/// Compile `dirty_mods` (already in topological wave order) into `overlay_root/{lib/lean,ir}`
/// after seeding fresh non-dirty root-package artifacts so `overlay_lib_dir/<pkg>/` never shadows
/// sibling `.lake/build` modules under Lean's package-root `findOLean` rule, without mutating
/// `.lake/build`, returning `overlay_lib_dir`.
pub(crate) fn compile_overlay_modules_direct(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    dirty_mods: &[String],
    overlay_root: &Path,
) -> Result<PathBuf> {
    let overlay_lib_dir = overlay_root.join("lib/lean");
    let overlay_ir_dir = overlay_root.join("ir");
    fs::create_dir_all(&overlay_lib_dir)?;
    fs::create_dir_all(&overlay_ir_dir)?;
    let dirty_set: HashSet<&str> = dirty_mods.iter().map(String::as_str).collect();
    let mut overlay_dag = dag.clone();
    for (mod_name, orig_node) in &dag.nodes {
        if dirty_set.contains(mod_name.as_str()) {
            continue;
        }
        let rel_slash = module_name_to_rel_slash(mod_name);
        let dst_olean = overlay_lib_dir.join(format!("{rel_slash}.olean"));
        for (_, src_art) in olean_artifact_paths(&orig_node.olean_path) {
            if src_art.is_file() {
                let Some(file_name) = src_art.file_name() else {
                    continue;
                };
                let dst_art = dst_olean
                    .parent()
                    .map(|p| p.join(file_name))
                    .unwrap_or_else(|| overlay_lib_dir.join(file_name));
                if let Some(parent) = dst_art.parent() {
                    fs::create_dir_all(parent)?;
                }
                if !dst_art.exists() {
                    crate::zygote::copy_file_reflink(&src_art, &dst_art)?;
                }
            }
        }
        let mut seeded_node = orig_node.clone();
        seeded_node.pkg_root = overlay_root.to_path_buf();
        seeded_node.olean_path = dst_olean;
        seeded_node.ilean_path = overlay_lib_dir.join(format!("{rel_slash}.ilean"));
        overlay_dag.nodes.insert(mod_name.clone(), seeded_node);
    }
    let (base_lp, ld_lp) = build_lean_search_path(cfg, true);
    let overlay_lp = format!("{}:{}", overlay_lib_dir.display(), base_lp);
    for mod_name in dirty_mods {
        let orig_node = overlay_dag
            .nodes
            .get(mod_name)
            .ok_or_else(|| anyhow::anyhow!("Overlay module `{}` missing from DAG", mod_name))?
            .clone();
        let rel_slash = module_name_to_rel_slash(mod_name);
        let mut node = orig_node;
        node.pkg_root = overlay_root.to_path_buf();
        node.olean_path = overlay_lib_dir.join(format!("{}.olean", rel_slash));
        node.ilean_path = overlay_lib_dir.join(format!("{}.ilean", rel_slash));
        node.c_path = overlay_ir_dir.join(format!("{}.c", rel_slash));
        let staged = compile_single_module_staged(
            cfg,
            &overlay_dag,
            &node,
            &overlay_lp,
            &ld_lp,
            false,
            None,
            true,
            1,
        )?;
        let _ = publish_staged_module_compile_output(&node, staged)?;
        overlay_dag.nodes.insert(mod_name.clone(), node);
    }
    Ok(overlay_lib_dir)
}

pub(crate) fn compile_disposable_snapshot_dirty_modules_direct(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    dirty_mods: &[String],
) -> Result<()> {
    let root_lib_lean = cfg
        .root_pkg
        .pkg_root
        .join(&cfg.root_pkg.build_dir)
        .join(&cfg.root_pkg.lean_lib_dir);
    let root_ir_dir = cfg
        .root_pkg
        .pkg_root
        .join(&cfg.root_pkg.build_dir)
        .join(&cfg.root_pkg.ir_dir);
    fs::create_dir_all(&root_lib_lean)?;
    fs::create_dir_all(&root_ir_dir)?;
    let (lean_lp, ld_lp) = build_lean_search_path(cfg, false);
    for mod_name in dirty_mods {
        let node = dag
            .nodes
            .get(mod_name)
            .ok_or_else(|| anyhow::anyhow!("Snapshot module `{}` missing from DAG", mod_name))?;
        let rel_slash = module_name_to_rel_slash(mod_name);
        for suffix in [
            ".olean",
            ".olean.hash",
            ".olean.server",
            ".olean.server.hash",
            ".olean.private",
            ".olean.private.hash",
            ".ilean",
            ".ilean.hash",
            ".ir",
            ".ir.hash",
            ".ir.sig",
            ".ir.sig.hash",
            ".trace",
        ] {
            let p = root_lib_lean.join(format!("{rel_slash}{suffix}"));
            if p.symlink_metadata().is_ok() {
                let _ = fs::remove_file(&p);
            }
        }
        for suffix in [".c", ".c.hash"] {
            let p = root_ir_dir.join(format!("{rel_slash}{suffix}"));
            if p.symlink_metadata().is_ok() {
                let _ = fs::remove_file(&p);
            }
        }
        let staged =
            compile_single_module_staged(cfg, dag, node, &lean_lp, &ld_lp, false, None, true, 1)?;
        let _ = publish_staged_module_compile_output(node, staged)?;
    }
    Ok(())
}

pub(super) fn collect_module_artifact_paths(node: &ModuleNode) -> Vec<(&'static str, PathBuf)> {
    let mut list = vec![
        ("olean", node.olean_path.clone()),
        ("ilean", node.ilean_path.clone()),
    ];
    let srv = PathBuf::from(format!("{}.server", node.olean_path.display()));
    if srv.is_file() {
        list.push(("olean_server", srv));
    }
    let prv = PathBuf::from(format!("{}.private", node.olean_path.display()));
    if prv.is_file() {
        list.push(("olean_private", prv));
    }
    let ir = node.olean_path.with_extension("ir");
    if ir.is_file() {
        list.push(("ir", ir));
    }
    let ir_sig = PathBuf::from(format!(
        "{}.sig",
        node.olean_path.with_extension("ir").display()
    ));
    if ir_sig.is_file() {
        list.push(("ir_sig", ir_sig));
    }
    if node.needs_c && node.c_path.is_file() {
        list.push(("c", node.c_path.clone()));
    }
    list
}
pub(super) fn is_regular_nonempty_file(p: &Path) -> bool {
    let Ok(sym) = fs::symlink_metadata(p) else {
        return false;
    };
    !sym.file_type().is_symlink() && sym.file_type().is_file() && sym.len() > 0
}

pub(super) fn has_no_symlink_at(p: &Path) -> bool {
    match fs::symlink_metadata(p) {
        Ok(sym) => !sym.file_type().is_symlink(),
        Err(_) => true,
    }
}

pub(super) fn validate_materialized_module_artifacts(node: &ModuleNode, preserve_lake: bool) -> bool {
    let srv_path = PathBuf::from(format!("{}.server", node.olean_path.display()));
    let priv_path = PathBuf::from(format!("{}.private", node.olean_path.display()));
    let ir_path = node.olean_path.with_extension("ir");
    let ir_sig_path = PathBuf::from(format!("{}.sig", ir_path.display()));
    let ltar_path = node.c_path.with_extension("ltar");
    let bc_path = node.c_path.with_extension("bc");
    let ltar_hash_path = PathBuf::from(format!("{}.hash", ltar_path.display()));
    let bc_hash_path = PathBuf::from(format!("{}.hash", bc_path.display()));
    let path_exists_any = |p: &Path| fs::symlink_metadata(p).is_ok();
    if !has_no_symlink_at(&srv_path)
        || !has_no_symlink_at(&priv_path)
        || !has_no_symlink_at(&ir_path)
        || !has_no_symlink_at(&ir_sig_path)
        || !has_no_symlink_at(&node.c_path)
        || !has_no_symlink_at(&ltar_path)
        || !has_no_symlink_at(&bc_path)
        || !has_no_symlink_at(&ltar_hash_path)
        || !has_no_symlink_at(&bc_hash_path)
        || (!preserve_lake
            && (path_exists_any(&ltar_path)
                || path_exists_any(&bc_path)
                || path_exists_any(&ltar_hash_path)
                || path_exists_any(&bc_hash_path)))
    {
        return false;
    }
    let has_olean = is_regular_nonempty_file(&node.olean_path);
    let has_ilean = is_regular_nonempty_file(&node.ilean_path);
    let has_srv = is_regular_nonempty_file(&srv_path);
    let has_priv = is_regular_nonempty_file(&priv_path);
    let has_c = is_regular_nonempty_file(&node.c_path);
    c_abi::verify_module_artifact_set(
        has_olean,
        has_ilean,
        node.is_module,
        has_srv,
        has_priv,
        node.needs_c,
        has_c,
    )
}

pub(crate) fn module_co_export_path(node: &ModuleNode) -> PathBuf {
    PathBuf::from(format!("{}.o.export", node.c_path.display()))
}

pub(crate) fn module_setup_json_path(node: &ModuleNode) -> PathBuf {
    node.c_path.with_extension("setup.json")
}

pub(crate) fn module_dynlib_so_path(node: &ModuleNode) -> Option<PathBuf> {
    let rel_slash = module_name_to_rel_slash(&node.module_name);
    let suffix = format!("{}.olean", rel_slash);
    let olean_str = node.olean_path.to_string_lossy();
    let base_dir = if let Some(prefix) = olean_str.strip_suffix(&suffix) {
        PathBuf::from(prefix.trim_end_matches('/'))
    } else {
        node.olean_path.parent()?.to_path_buf()
    };
    let stem = lean_mk_module_initialization_stem(&node.module_name, Some(&node.pkg_name));
    let ext = cached_toolchain_shared_lib_ext().unwrap_or(if cfg!(target_os = "macos") {
        "dylib"
    } else if cfg!(target_os = "windows") {
        "dll"
    } else {
        "so"
    });
    Some(base_dir.join(format!("{}.{}", stem, ext)))
}

pub(crate) fn module_co_noexport_path(node: &ModuleNode) -> PathBuf {
    PathBuf::from(format!("{}.o.noexport", node.c_path.display()))
}

pub(super) fn wipe_module_c_object_artifacts(node: &ModuleNode) {
    for p in [module_co_export_path(node), module_co_noexport_path(node)] {
        let _ = fs::remove_file(&p);
        let _ = fs::remove_file(format!("{}.hash", p.display()));
        let _ = fs::remove_file(format!("{}.trace", p.display()));
    }
}

pub(super) fn wipe_existing_module_artifacts(node: &ModuleNode) {
    wipe_existing_module_artifacts_opts(node, false);
}

pub(super) fn wipe_existing_module_artifacts_opts(node: &ModuleNode, preserve_c_obj: bool) {
    let srv_path = PathBuf::from(format!("{}.server", node.olean_path.display()));
    let priv_path = PathBuf::from(format!("{}.private", node.olean_path.display()));
    let ir_path = node.olean_path.with_extension("ir");
    let ir_sig_path = PathBuf::from(format!("{}.sig", ir_path.display()));
    let ltar_path = node.c_path.with_extension("ltar");
    let bc_path = node.c_path.with_extension("bc");
    let setup_path = module_setup_json_path(node);
    for p in [
        &node.olean_path,
        &node.ilean_path,
        &srv_path,
        &priv_path,
        &ir_path,
        &ir_sig_path,
        &node.c_path,
        &ltar_path,
        &bc_path,
    ] {
        let _ = fs::remove_file(p);
        let _ = fs::remove_file(format!("{}.hash", p.display()));
        let _ = fs::remove_file(format!("{}.trace", p.display()));
    }
    if !preserve_c_obj {
        wipe_module_c_object_artifacts(node);
    }
    if let Some(so_path) = module_dynlib_so_path(node) {
        let _ = fs::remove_file(&so_path);
        let _ = fs::remove_file(format!("{}.hash", so_path.display()));
        let _ = fs::remove_file(format!("{}.trace", so_path.display()));
        let _ = fs::remove_file(format!("{}.rsp", so_path.display()));
    }
    let _ = fs::remove_file(&setup_path);
    let _ = fs::remove_file(node.olean_path.with_extension("trace"));
}

pub fn lake_murmur64a(data: &[u8], seed: u64) -> u64 {
    const M: u64 = 0xc6a4a7935bd1e995;
    const R: u32 = 47;
    let mut h = seed ^ (data.len() as u64).wrapping_mul(M);
    let (chunks, rem) = data.as_chunks::<8>();
    for chunk in chunks {
        let mut k = u64::from_le_bytes(*chunk);
        k = k.wrapping_mul(M);
        k ^= k >> R;
        k = k.wrapping_mul(M);
        h ^= k;
        h = h.wrapping_mul(M);
    }
    if !rem.is_empty() {
        let mut val = 0u64;
        for &b in rem.iter().rev() {
            val = (val << 8) | (b as u64);
        }
        h ^= val;
        h = h.wrapping_mul(M);
    }
    h ^= h >> R;
    h = h.wrapping_mul(M);
    h ^= h >> R;
    h
}

/// Lake's `Hash.nil` (`NilTrace`): the seed every mixed trace folds from, and the hash of an
/// empty job (e.g. a library `extraDep` without `needs`).
pub(crate) const LAKE_NIL_HASH: u64 = 1723;

#[inline]
pub fn lake_mix_hash(h: u64, mut k: u64) -> u64 {
    const M: u64 = 0xc6a4a7935bd1e995;
    k = k.wrapping_mul(M);
    k ^= k >> 47;
    k ^= M;
    (h ^ k).wrapping_mul(M)
}

#[inline]
pub fn lake_hash_bytes(data: &[u8]) -> u64 {
    lake_mix_hash(LAKE_NIL_HASH, lake_murmur64a(data, 11))
}

#[inline]
pub fn lake_hash_text(s: &str) -> u64 {
    if s.as_bytes().contains(&b'\r') {
        lake_hash_bytes(s.replace("\r\n", "\n").as_bytes())
    } else {
        lake_hash_bytes(s.as_bytes())
    }
}

pub fn lake_hash_name(mod_name: &str) -> u64 {
    let mut h = LAKE_NIL_HASH;
    for part in mod_name.split('.').filter(|p| !p.is_empty()) {
        h = lake_mix_hash(h, lake_murmur64a(part.as_bytes(), 11));
    }
    lake_mix_hash(LAKE_NIL_HASH, h)
}

pub fn lake_hash_pkg_id(pkg_name: &str) -> u64 {
    lake_mix_hash(
        LAKE_NIL_HASH,
        lake_mix_hash(lake_murmur64a(pkg_name.as_bytes(), 11), 13),
    )
}

pub(super) fn lake_input_hash(val: &serde_json::Value) -> Result<u64> {
    if let Some(s) = val.as_str() {
        if s.len() != 16 || !s.bytes().all(|b| b.is_ascii_hexdigit()) {
            anyhow::bail!("Malformed 16-hex trace input hash `{}`", s);
        }
        return Ok(u64::from_str_radix(s, 16)?);
    }
    if let Some(arr) = val.as_array() {
        let mut h = LAKE_NIL_HASH;
        for item in arr {
            let Some(pair) = item.as_array() else {
                anyhow::bail!("Malformed trace input entry (expected 2-element array)");
            };
            if pair.len() != 2 || !pair[0].is_string() {
                anyhow::bail!("Malformed trace input pair (expected [caption, hash_or_array])");
            }
            h = lake_mix_hash(h, lake_input_hash(&pair[1])?);
        }
        return Ok(h);
    }
    anyhow::bail!("Malformed trace input value (expected hex string or array)")
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct LakeModuleExportInfo {
    pub(crate) arts_trace: u64,
    pub(crate) meta_arts_trace: u64,
    pub(crate) all_arts_trace: u64,
    pub(crate) trans_trace: u64,
    pub(crate) meta_trans_trace: u64,
    pub(crate) all_trans_trace: u64,
    pub(crate) legacy_trans_trace: u64,
}

pub(super) fn verify_and_hash_artifact_bytes(
    artifact_path: &Path,
    check_existing_sidecar: bool,
    require_hash_file: bool,
) -> Result<u64> {
    if !has_no_symlink_at(artifact_path) || !is_regular_nonempty_file(artifact_path) {
        anyhow::bail!(
            "Artifact `{}` is missing, empty, or a symlink",
            artifact_path.display()
        );
    }
    let window = current_memo_window();
    let art_stat = path_olean_stat_sig(artifact_path);
    let hash_path = PathBuf::from(format!("{}.hash", artifact_path.display()));
    let sidecar_stat = if check_existing_sidecar {
        path_olean_stat_sig(&hash_path)
    } else {
        None
    };
    let memo = ARTIFACT_LAKE_HASH_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
    if let Some(ast) = art_stat {
        if crate::zygote::dev_records_subsecond_timestamps(&ast)
            && sidecar_stat.is_none_or(|s| crate::zygote::dev_records_subsecond_timestamps(&s))
            && (!require_hash_file || sidecar_stat.is_some())
        {
            if let Ok(g) = memo.lock() {
                if let Some(&(w, cached_ast, cached_sst, cached_h)) = g.get(artifact_path) {
                    if w == window
                        && cached_ast == ast
                        && (!check_existing_sidecar || cached_sst == sidecar_stat)
                    {
                        return Ok(cached_h);
                    }
                }
            }
        }
    }
    let read_started_ns = crate::zygote::wall_clock_ns();
    let (fd_pre, bytes, fd_post) = read_regular_file_bound_stat(artifact_path)?;
    if artifact_path.extension().and_then(|s| s.to_str()) == Some("olean")
        && (bytes.len() < 32 || !bytes.starts_with(b"olean"))
    {
        anyhow::bail!(
            "Artifact `{}` lacks valid Lean 4 .olean header magic",
            artifact_path.display()
        );
    }
    let actual_h = lake_hash_bytes(&bytes);
    let mut sidecar_fd_ok = true;
    if check_existing_sidecar {
        match read_regular_file_bound_stat(&hash_path) {
            Ok((spre, sbytes, spost)) => {
                sidecar_fd_ok = spre == spost && Some(spost) == sidecar_stat;
                let raw = std::str::from_utf8(&sbytes).with_context(|| {
                    format!("Non-UTF8 hash in sidecar `{}`", hash_path.display())
                })?;
                let trimmed = raw.trim();
                if trimmed.len() != 16 || !trimmed.bytes().all(|b| b.is_ascii_hexdigit()) {
                    anyhow::bail!("Malformed 16-hex hash in sidecar `{}`", hash_path.display());
                }
                let recorded_h = u64::from_str_radix(trimmed, 16)?;
                if recorded_h != actual_h {
                    anyhow::bail!(
                        "Sidecar hash mismatch for `{}` (recorded {:016x} != actual {:016x})",
                        artifact_path.display(),
                        recorded_h,
                        actual_h
                    );
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                if require_hash_file {
                    anyhow::bail!(
                        "Required dependency hash sidecar `{}` is missing",
                        hash_path.display()
                    );
                }
            }
            Err(e) => return Err(e.into()),
        }
    }
    if fd_pre == fd_post && sidecar_fd_ok {
        if let Some(post_ast) = path_olean_stat_sig(artifact_path) {
            let post_sst = if check_existing_sidecar {
                path_olean_stat_sig(&hash_path)
            } else {
                None
            };
            if post_ast == fd_post
                && Some(post_ast) == art_stat
                && post_sst == sidecar_stat
                && olean_stat_sig_trusted_at(&post_ast, read_started_ns)
                && post_sst.is_none_or(|s| olean_stat_sig_trusted_at(&s, read_started_ns))
            {
                if let Ok(mut g) = memo.lock() {
                    if current_memo_window() == window {
                        if g.len() >= 131_072 {
                            g.clear();
                        }
                        g.insert(
                            artifact_path.to_path_buf(),
                            (window, post_ast, post_sst, actual_h),
                        );
                    }
                }
            }
        }
    }
    Ok(actual_h)
}

pub(crate) fn compute_lake_export_info(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    requester: &ModuleNode,
    mod_name: &str,
    memo: &mut HashMap<(String, bool), LakeModuleExportInfo>,
    visiting: &mut HashSet<String>,
) -> Result<LakeModuleExportInfo> {
    compute_lake_export_info_opts(cfg, dag, requester, mod_name, memo, visiting, false)
}

pub(super) fn compute_lake_export_info_opts(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    requester: &ModuleNode,
    mod_name: &str,
    memo: &mut HashMap<(String, bool), LakeModuleExportInfo>,
    visiting: &mut HashSet<String>,
    allow_stale_src_in_dag: bool,
) -> Result<LakeModuleExportInfo> {
    let memo_key = (
        mod_name.to_string(),
        requester.needs_c && !allow_stale_src_in_dag,
    );
    if let Some(info) = memo.get(&memo_key).or_else(|| {
        (!memo_key.1)
            .then(|| memo.get(&(mod_name.to_string(), true)))
            .flatten()
    }) {
        return Ok(*info);
    }
    if !visiting.insert(mod_name.to_string()) {
        anyhow::bail!(
            "Import cycle detected while computing Lake export trace for `{}`",
            mod_name
        );
    }
    let resolved: Option<(Option<PathBuf>, PathBuf, bool)> =
        if let Some(n) = dag.nodes.get(mod_name) {
            Some((Some(n.src_path.clone()), n.olean_path.clone(), true))
        } else if let Some((_, ext_p)) = requester
            .external_olean_deps
            .iter()
            .find(|(m, _)| m == mod_name)
            .or_else(|| {
                dag.nodes
                    .values()
                    .flat_map(|n| n.external_olean_deps.iter())
                    .find(|(m, _)| m == mod_name)
            })
        {
            let src_opt = resolve_importable_module_in_package(&cfg.root_pkg, true, mod_name)
                .or_else(|| {
                    cfg.dep_pkgs
                        .iter()
                        .find_map(|dp| resolve_importable_module_in_package(dp, false, mod_name))
                })
                .map(|sp| sp.src_path);
            Some((src_opt, ext_p.clone(), false))
        } else {
            resolve_importable_module_in_package(&cfg.root_pkg, true, mod_name)
                .or_else(|| {
                    cfg.dep_pkgs
                        .iter()
                        .find_map(|dp| resolve_importable_module_in_package(dp, false, mod_name))
                })
                .map(|sp| {
                    let rel_slash = module_name_to_rel_slash(mod_name);
                    let olean_p = sp.build_lib_lean_dir.join(format!("{}.olean", rel_slash));
                    (Some(sp.src_path), olean_p, false)
                })
                .or_else(|| match resolve_import_site(cfg, mod_name) {
                    ImportSite::Prebuilt(pb_p) => Some((None, pb_p, false)),
                    _ => None,
                })
        };
    let Some((src_opt, olean_path, is_in_dag)) = resolved else {
        visiting.remove(mod_name);
        anyhow::bail!("Unresolved workspace/package import `{}`", mod_name);
    };
    let srv_path = PathBuf::from(format!("{}.server", olean_path.display()));
    let dep_src_info = match src_opt {
        Some(ref sp) if sp.is_file() => {
            let raw = fs::read_to_string(sp)?;
            let hdr = parse_header_info(&raw);
            if let Some(ref herr) = hdr.header_error {
                anyhow::bail!(
                    "Invalid module header in dependency `{}` ({}): {}",
                    mod_name,
                    sp.display(),
                    herr
                );
            }
            Some((sp.clone(), raw, hdr))
        }
        _ => None,
    };
    let is_mod = dep_src_info
        .as_ref()
        .map(|(_, _, h)| h.is_module)
        .unwrap_or_else(|| srv_path.is_file());
    let tv = verify_trace_outputs_against_artifacts_with_existing_c_ext(
        &olean_path,
        is_mod,
        allow_stale_src_in_dag || !requester.needs_c,
    )?;
    let (arts_trace, meta_arts_trace, all_arts_trace) =
        compute_module_arts_traces(&olean_path, is_mod, true)?;
    if !(allow_stale_src_in_dag && is_in_dag) {
        if let Some((_, ref src_raw, _)) = dep_src_info {
            if tv.get("inputs").is_some() {
                let expected_src_h = format!("{:016x}", lake_hash_text(src_raw));
                let src_matched = trace_recorded_src_hash(&tv) == Some(expected_src_h.as_str())
                    || tv
                        .pointer("/inputs/3/1")
                        .and_then(|v| v.as_str())
                        .is_some_and(|s| s == expected_src_h)
                    || tv
                        .pointer("/inputs/4/1")
                        .and_then(|v| v.as_str())
                        .is_some_and(|s| s == expected_src_h);
                if !src_matched {
                    anyhow::bail!(
                        "Dependency trace `{}` recorded source hash does not match `{}`",
                        olean_path.with_extension("trace").display(),
                        mod_name
                    );
                }
            }
        }
    }
    let mut trans_trace = LAKE_NIL_HASH;
    let mut meta_trans_trace = LAKE_NIL_HASH;
    let mut all_trans_trace = LAKE_NIL_HASH;
    let mut legacy_trans_trace = LAKE_NIL_HASH;
    if let Some((_, _, ref dh)) = dep_src_info {
        let mut import_entries = Vec::new();
        for sub_imp in &dh.import_specs {
            let is_ws_or_pkg = dag.nodes.contains_key(&sub_imp.module)
                || requester
                    .external_olean_deps
                    .iter()
                    .any(|(m, _)| m == &sub_imp.module)
                || dag.nodes.values().any(|n| {
                    n.external_olean_deps
                        .iter()
                        .any(|(m, _)| m == &sub_imp.module)
                })
                || resolve_importable_module_in_package(&cfg.root_pkg, true, &sub_imp.module)
                    .is_some()
                || cfg.dep_pkgs.iter().any(|dp| {
                    resolve_importable_module_in_package(dp, false, &sub_imp.module).is_some()
                })
                || matches!(
                    resolve_import_site(cfg, &sub_imp.module),
                    ImportSite::Module(_) | ImportSite::Prebuilt(_)
                );
            if !is_ws_or_pkg
                && is_builtin_toolchain_module(
                    &cfg.toolchain_lib_lean,
                    Some(&cfg.lean_githash),
                    &sub_imp.module,
                )
            {
                continue;
            }
            let sub_exp = compute_lake_export_info_opts(
                cfg,
                dag,
                requester,
                &sub_imp.module,
                memo,
                visiting,
                allow_stale_src_in_dag,
            )?;
            if !is_in_dag {
                import_entries.extend(lake_import_trace_entries(is_mod, sub_imp, &sub_exp));
            }
            fold_lake_export_traces(
                &mut trans_trace,
                &mut meta_trans_trace,
                &mut all_trans_trace,
                &mut legacy_trans_trace,
                sub_imp,
                &sub_exp,
            );
        }
        if !is_in_dag && tv.get("inputs").is_some() {
            if let Some(actual_imports_h) = recorded_trace_imports_hash(&tv) {
                let expected_imports_h = if import_entries.is_empty() {
                    LAKE_NIL_HASH
                } else {
                    lake_input_hash(&serde_json::Value::Array(import_entries))?
                };
                if actual_imports_h != expected_imports_h {
                    visiting.remove(mod_name);
                    anyhow::bail!(
                        "Dependency trace `{}` recorded import hash does not match current imports of `{}`",
                        olean_path.with_extension("trace").display(),
                        mod_name
                    );
                }
            }
        }
    } else {
        let mut pb_cache = LakeClosureCache::for_project(cfg);
        let pb_info = prebuilt_olean_export_info(cfg, false, &olean_path, &mut pb_cache)
            .ok_or_else(|| {
                anyhow::anyhow!(
                "Source-less dependency `{}` at {} failed transitive prebuilt trace verification",
                mod_name,
                olean_path.display()
            )
            })?;
        visiting.remove(mod_name);
        memo.insert(memo_key, pb_info);
        return Ok(pb_info);
    }
    visiting.remove(mod_name);
    let info = LakeModuleExportInfo {
        arts_trace,
        meta_arts_trace,
        all_arts_trace,
        trans_trace,
        meta_trans_trace,
        all_trans_trace,
        legacy_trans_trace,
    };
    memo.insert(memo_key, info);
    Ok(info)
}

#[inline]
pub(super) fn nonzero_u64_digest(raw: u64) -> u64 {
    if raw == 0 {
        1
    } else {
        raw
    }
}

pub(super) fn nonzero_blake3_u64(s: &str) -> u64 {
    if s.is_empty() {
        return 0;
    }
    let bytes = blake3::hash(s.as_bytes());
    let mut arr = [0u8; 8];
    arr.copy_from_slice(&bytes.as_bytes()[..8]);
    nonzero_u64_digest(u64::from_le_bytes(arr))
}

pub(super) fn relativize_diagnostic_file_path(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    raw_file: &str,
) -> String {
    let p = Path::new(raw_file);
    if p.is_absolute() {
        for base in [&node.pkg_root, &cfg.root_pkg.pkg_root] {
            if let Ok(rel) = p.strip_prefix(base) {
                let s = rel.to_string_lossy().replace('\\', "/");
                if !s.is_empty() {
                    return s;
                }
            }
        }
    }
    raw_file.replace('\\', "/")
}

pub(super) fn parse_lean_diagnostic_header<'a>(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    line: &'a str,
) -> Option<(&'static str, String, &'a str)> {
    for (needle, level) in [
        (": warning: ", "warning"),
        (": info: ", "info"),
        (": error: ", "error"),
    ] {
        let Some((lhs, msg_rest)) = line.split_once(needle) else {
            continue;
        };
        let Some((before_col, col_str)) = lhs.rsplit_once(':') else {
            continue;
        };
        let Some((file_part, line_str)) = before_col.rsplit_once(':') else {
            continue;
        };
        if !line_str.is_empty()
            && line_str.bytes().all(|b| b.is_ascii_digit())
            && !col_str.is_empty()
            && col_str.bytes().all(|b| b.is_ascii_digit())
            && !file_part.is_empty()
        {
            let rel_file = relativize_diagnostic_file_path(cfg, node, file_part);
            return Some((level, format!("{rel_file}:{line_str}:{col_str}"), msg_rest));
        }
    }
    None
}

pub(super) fn parse_lean_diagnostics_for_lake(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    raw_stdout: &str,
) -> (Vec<serde_json::Value>, String) {
    if raw_stdout.trim().is_empty() {
        return (Vec::new(), String::new());
    }
    let mut trace_log: Vec<serde_json::Value> = Vec::new();
    let mut formatted_stdout = String::new();
    let mut cur_entry: Option<(&'static str, String)> = None;
    let flush = |cur: &mut Option<(&'static str, String)>,
                 log_out: &mut Vec<serde_json::Value>,
                 stdout_out: &mut String| {
        if let Some((lvl, msg)) = cur.take() {
            let trimmed = msg.trim_end().to_string();
            stdout_out.push_str(lvl);
            stdout_out.push_str(": ");
            stdout_out.push_str(&trimmed);
            stdout_out.push('\n');
            log_out.push(serde_json::json!({
                "level": lvl,
                "message": trimmed,
            }));
        }
    };
    for raw_line in raw_stdout.lines() {
        let line = raw_line.strip_suffix('\r').unwrap_or(raw_line);
        if let Some((lvl, loc, msg_rest)) = parse_lean_diagnostic_header(cfg, node, line) {
            flush(&mut cur_entry, &mut trace_log, &mut formatted_stdout);
            cur_entry = Some((lvl, format!("{loc}: {msg_rest}")));
        } else if let Some((_, ref mut acc)) = cur_entry {
            acc.push('\n');
            acc.push_str(line);
        } else if !line.is_empty() {
            formatted_stdout.push_str(line);
            formatted_stdout.push('\n');
        }
    }
    flush(&mut cur_entry, &mut trace_log, &mut formatted_stdout);
    (trace_log, formatted_stdout)
}

pub(crate) fn format_lake_trace_log_stdout(trace_log: &[serde_json::Value]) -> String {
    let mut out = String::new();
    for entry in trace_log {
        let Some(lvl) = entry.get("level").and_then(|v| v.as_str()) else {
            continue;
        };
        if lvl == "trace" {
            continue;
        }
        let Some(msg) = entry.get("message").and_then(|v| v.as_str()) else {
            continue;
        };
        out.push_str(lvl);
        out.push_str(": ");
        out.push_str(msg.trim_end());
        out.push('\n');
    }
    out
}

pub(super) fn read_existing_trace_log(node: &ModuleNode) -> Vec<serde_json::Value> {
    let trace_path = node.olean_path.with_extension("trace");
    let Ok(bytes) = fs::read(&trace_path) else {
        return Vec::new();
    };
    let Ok(val) = serde_json::from_slice::<serde_json::Value>(&bytes) else {
        return Vec::new();
    };
    val.get("log")
        .and_then(|v| v.as_array())
        .cloned()
        .unwrap_or_default()
}

pub fn write_lake_module_hashes_and_trace(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    node: &ModuleNode,
    expected_artifact_digest: &str,
    audited_artifact_digest: Option<&str>,
    kernel_audit_clean: bool,
) -> Result<()> {
    let mut exp_memo: HashMap<(String, bool), LakeModuleExportInfo> = HashMap::new();
    write_lake_module_hashes_and_trace_with_memo(
        cfg,
        dag,
        node,
        expected_artifact_digest,
        audited_artifact_digest,
        kernel_audit_clean,
        &[],
        &mut exp_memo,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn write_lake_module_hashes_and_trace_with_memo(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    node: &ModuleNode,
    expected_artifact_digest: &str,
    audited_artifact_digest: Option<&str>,
    kernel_audit_clean: bool,
    trace_log: &[serde_json::Value],
    exp_memo: &mut HashMap<(String, bool), LakeModuleExportInfo>,
) -> Result<()> {
    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock
        .lock()
        .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
    let _flock_guard = acquire_publish_flock(&node.pkg_root, false)?;
    let srv_path = PathBuf::from(format!("{}.server", node.olean_path.display()));
    let priv_path = PathBuf::from(format!("{}.private", node.olean_path.display()));
    let ir_path = node.olean_path.with_extension("ir");
    let ir_sig_path = PathBuf::from(format!("{}.sig", ir_path.display()));
    let (src_raw, src_read_ok) = match fs::read_to_string(&node.src_path) {
        Ok(s) => (s, true),
        Err(_) => (String::new(), false),
    };
    let src_blake3_matches =
        src_read_ok && blake3::hash(src_raw.as_bytes()).to_hex().as_str() == node.src_blake3;
    let hygiene = splitter::audit_hygiene(&splitter::strip_lean_comments(&src_raw));
    let sorry_ok = !node.is_root_pkg || !hygiene.has_sorry;
    let axiom_ok = !hygiene.has_axiom
        || !node.is_root_pkg
        || splitter::HygieneReport::has_custom_axiom_policy();
    let checking_weakening_ok = if node_is_git_pinned_manifest_package(cfg, node) {
        !hygiene.has_checking_weakening_option
    } else {
        !hygiene.has_checking_weakening
    };
    let no_forbidden_proof_tokens = sorry_ok
        && axiom_ok
        && (!node.is_root_pkg || !hygiene.native_violation())
        && (!node.is_root_pkg || !hygiene.has_trust_compiler)
        && checking_weakening_ok;
    let skeleton_clean = src_blake3_matches && no_forbidden_proof_tokens;
    let is_stubbed_skeleton = !sorry_ok || !no_forbidden_proof_tokens || !src_blake3_matches;
    let olean_h_res = verify_and_hash_artifact_bytes(&node.olean_path, false, false);
    let ilean_h_res = verify_and_hash_artifact_bytes(&node.ilean_path, false, false);
    let c_h_res = if is_regular_nonempty_file(&node.c_path) {
        Some(verify_and_hash_artifact_bytes(&node.c_path, false, false))
    } else if node.needs_c {
        Some(Err(anyhow::anyhow!("Required .c artifact missing")))
    } else {
        None
    };
    let mod_companions_res = if node.is_module {
        Some((
            verify_and_hash_artifact_bytes(&srv_path, false, false),
            verify_and_hash_artifact_bytes(&priv_path, false, false),
            module_ir_sig_hash(&node.olean_path, false),
            verify_and_hash_artifact_bytes(&ir_path, false, false),
        ))
    } else {
        None
    };
    let actual_art_digest_opt =
        compute_olean_artifact_set_digest_locked(&node.olean_path, Some(&_flock_guard)).ok();
    let digest_matches = !expected_artifact_digest.is_empty()
        && actual_art_digest_opt.as_deref() == Some(expected_artifact_digest);
    let all_shards_certified =
        validate_materialized_module_artifacts(node, false) && sorry_ok && digest_matches;
    let artifact_hashes_match = digest_matches
        && olean_h_res.is_ok()
        && ilean_h_res.is_ok()
        && c_h_res.as_ref().is_none_or(|r| r.is_ok())
        && mod_companions_res
            .as_ref()
            .is_none_or(|(s, p, rs, r)| s.is_ok() && p.is_ok() && rs.is_ok() && r.is_ok());
    let header = parse_header_info(&src_raw);
    let mut import_entries = Vec::new();
    let mut dep_trace_fresh = header.header_error.is_none() && header.is_module == node.is_module;
    let mut visiting = HashSet::new();
    if dep_trace_fresh {
        for imp in &header.import_specs {
            let is_ws_or_pkg = dag.nodes.contains_key(&imp.module)
                || node
                    .external_olean_deps
                    .iter()
                    .any(|(m, _)| m == &imp.module)
                || dag
                    .nodes
                    .values()
                    .any(|n| n.external_olean_deps.iter().any(|(m, _)| m == &imp.module))
                || resolve_importable_module_in_package(&cfg.root_pkg, true, &imp.module).is_some()
                || cfg.dep_pkgs.iter().any(|dp| {
                    resolve_importable_module_in_package(dp, false, &imp.module).is_some()
                })
                || matches!(
                    resolve_import_site(cfg, &imp.module),
                    ImportSite::Module(_) | ImportSite::Prebuilt(_)
                );
            if !is_ws_or_pkg {
                if is_builtin_toolchain_module(
                    &cfg.toolchain_lib_lean,
                    Some(&cfg.lean_githash),
                    &imp.module,
                ) {
                    continue;
                }
                dep_trace_fresh = false;
                break;
            }
            match compute_lake_export_info(cfg, dag, node, &imp.module, exp_memo, &mut visiting) {
                Ok(exp_info) => {
                    import_entries.extend(lake_import_trace_entries(
                        node.is_module,
                        imp,
                        &exp_info,
                    ));
                }
                Err(_) => {
                    dep_trace_fresh = false;
                    break;
                }
            }
        }
    }
    let src_h = lake_hash_text(&src_raw);
    let raw_imp_dynlibs = if node.platform_independent == Some(true) {
        Vec::new()
    } else {
        compute_module_raw_import_dynlibs(dag, node)
    };
    let inputs_opt = build_expected_lake_module_inputs_value(
        cfg,
        &node.pkg_root,
        &node.pkg_name,
        &node.pkg_base_name,
        &node.target_name,
        node.is_exe_target,
        &node.module_name,
        node.is_module,
        node.platform_independent,
        &node.lean_options,
        &node.strong_args,
        &node.src_path,
        src_h,
        import_entries,
        &raw_imp_dynlibs,
    );
    if inputs_opt.is_none() {
        dep_trace_fresh = false;
    }
    let inputs = inputs_opt.unwrap_or_else(|| serde_json::Value::Array(Vec::new()));
    let dep_hash_opt = lake_input_hash(&inputs).ok();
    let stubbed_placeholder_count = if is_stubbed_skeleton { 1u64 } else { 0u64 };
    let total_shard_count = 1u64;
    let certified_shard_count = if all_shards_certified && artifact_hashes_match {
        1u64
    } else {
        0u64
    };
    let distinct_covered_shard_count = certified_shard_count;
    let expected_interface_digest = nonzero_blake3_u64(&node.src_blake3);
    let actual_interface_digest = if src_blake3_matches {
        nonzero_blake3_u64(blake3::hash(src_raw.as_bytes()).to_hex().as_str())
    } else {
        0
    };
    let expected_olean_digest = nonzero_blake3_u64(expected_artifact_digest);
    let actual_olean_digest = if artifact_hashes_match {
        actual_art_digest_opt
            .as_deref()
            .map(nonzero_blake3_u64)
            .unwrap_or(0)
    } else {
        0
    };
    let actual_ilean_digest = ilean_h_res
        .as_ref()
        .ok()
        .copied()
        .map(nonzero_u64_digest)
        .unwrap_or(0);
    let expected_ilean_digest = if artifact_hashes_match {
        actual_ilean_digest
    } else {
        0
    };
    let actual_c_digest = match c_h_res {
        Some(Ok(ch)) => nonzero_u64_digest(ch),
        _ => 0,
    };
    let expected_c_digest = if node.needs_c && artifact_hashes_match {
        actual_c_digest
    } else {
        0
    };
    let dep_trace_digest = if dep_trace_fresh {
        dep_hash_opt.map(nonzero_u64_digest).unwrap_or(0)
    } else {
        0
    };
    let audited_digest_u64 = audited_artifact_digest.map(nonzero_blake3_u64).unwrap_or(0);
    if !c_abi::verify_audit_materialize_gate(
        skeleton_clean,
        stubbed_placeholder_count,
        certified_shard_count,
        distinct_covered_shard_count,
        total_shard_count,
        expected_interface_digest,
        actual_interface_digest,
        expected_olean_digest,
        actual_olean_digest,
        expected_ilean_digest,
        actual_ilean_digest,
        node.needs_c,
        expected_c_digest,
        actual_c_digest,
        dep_trace_digest,
        audited_digest_u64,
        kernel_audit_clean,
    ) {
        let ltar_path = node.c_path.with_extension("ltar");
        let bc_path = node.c_path.with_extension("bc");
        for p in [
            &node.olean_path,
            &node.ilean_path,
            &srv_path,
            &priv_path,
            &ir_path,
            &ir_sig_path,
            &node.c_path,
            &ltar_path,
            &bc_path,
        ] {
            let _ = fs::remove_file(format!("{}.hash", p.display()));
        }
        let _ = fs::remove_file(node.olean_path.with_extension("trace"));
        anyhow::bail!(
            "Audit materialization gate `turbo_spec_verify_audit_materialize_gate` rejected sidecar emission for `{}` (skeleton_clean={}, all_shards_certified={}, is_stubbed={}, hashes_match={}, dep_trace_fresh={}, kernel_audit_clean={})",
            node.module_name,
            skeleton_clean,
            all_shards_certified,
            is_stubbed_skeleton,
            artifact_hashes_match,
            dep_trace_fresh,
            kernel_audit_clean
        );
    }
    let dep_hash = dep_hash_opt.ok_or_else(|| {
        anyhow::anyhow!(
            "Failed to compute Lake trace depHash for `{}`",
            node.module_name
        )
    })?;
    let olean_h = olean_h_res?;
    let ilean_h = ilean_h_res?;
    let mut sidecar_writes: Vec<(PathBuf, Vec<u8>)> = vec![
        (
            PathBuf::from(format!("{}.hash", node.olean_path.display())),
            format!("{:016x}", olean_h).into_bytes(),
        ),
        (
            PathBuf::from(format!("{}.hash", node.ilean_path.display())),
            format!("{:016x}", ilean_h).into_bytes(),
        ),
    ];
    let c_h_opt = match c_h_res {
        Some(Ok(ch)) => {
            sidecar_writes.push((
                PathBuf::from(format!("{}.hash", node.c_path.display())),
                format!("{:016x}", ch).into_bytes(),
            ));
            Some(ch)
        }
        _ => {
            let _ = fs::remove_file(format!("{}.hash", node.c_path.display()));
            None
        }
    };
    let mod_companion_hashes =
        if let Some((Ok(srv_h), Ok(priv_h), Ok(ir_sig_h_opt), Ok(ir_h))) = mod_companions_res {
            for (p, h) in [(&srv_path, srv_h), (&priv_path, priv_h), (&ir_path, ir_h)] {
                sidecar_writes.push((
                    PathBuf::from(format!("{}.hash", p.display())),
                    format!("{:016x}", h).into_bytes(),
                ));
            }
            if let Some(ir_sig_h) = ir_sig_h_opt {
                sidecar_writes.push((
                    PathBuf::from(format!("{}.hash", ir_sig_path.display())),
                    format!("{:016x}", ir_sig_h).into_bytes(),
                ));
            } else {
                let _ = fs::remove_file(format!("{}.hash", ir_sig_path.display()));
            }
            Some((srv_h, priv_h, ir_sig_h_opt, ir_h))
        } else {
            for p in [&srv_path, &priv_path, &ir_sig_path, &ir_path] {
                if is_regular_nonempty_file(p) {
                    if let Ok(h) = verify_and_hash_artifact_bytes(p, false, false) {
                        sidecar_writes.push((
                            PathBuf::from(format!("{}.hash", p.display())),
                            format!("{:016x}", h).into_bytes(),
                        ));
                    }
                } else {
                    let _ = fs::remove_file(format!("{}.hash", p.display()));
                }
            }
            None
        };
    let outputs_json = match (c_h_opt, mod_companion_hashes) {
        (Some(c_h), Some((srv_h, priv_h, Some(ir_sig_h), ir_h))) => serde_json::json!({
            "o": [
                format!("{:016x}.olean", olean_h),
                format!("{:016x}.olean.server", srv_h),
                format!("{:016x}.olean.private", priv_h)
            ],
            "m": true,
            "i": format!("{:016x}.ilean", ilean_h),
            "rs": format!("{:016x}.ir.sig", ir_sig_h),
            "r": format!("{:016x}.ir", ir_h),
            "c": format!("{:016x}.c", c_h)
        }),
        (Some(c_h), Some((srv_h, priv_h, None, ir_h))) => serde_json::json!({
            "o": [
                format!("{:016x}.olean", olean_h),
                format!("{:016x}.olean.server", srv_h),
                format!("{:016x}.olean.private", priv_h)
            ],
            "m": true,
            "i": format!("{:016x}.ilean", ilean_h),
            "r": format!("{:016x}.ir", ir_h),
            "c": format!("{:016x}.c", c_h)
        }),
        (Some(c_h), None) => serde_json::json!({
            "o": [format!("{:016x}.olean", olean_h)],
            "m": false,
            "i": format!("{:016x}.ilean", ilean_h),
            "c": format!("{:016x}.c", c_h)
        }),
        (None, _) => serde_json::Value::Null,
    };
    let trace_json = serde_json::json!({
        "synthetic": false,
        "schemaVersion": "2025-09-10",
        "outputs": outputs_json,
        "log": trace_log,
        "inputs": inputs,
        "depHash": format!("{:016x}", dep_hash)
    });
    let trace_path = node.olean_path.with_extension("trace");
    let trace_bytes = serde_json::to_vec(&trace_json)?;
    sidecar_writes.push((trace_path, trace_bytes));
    sidecar_writes.retain(|(dst_p, content)| !regular_file_matches_bytes_0644(dst_p, content));
    if sidecar_writes.is_empty() {
        return Ok(());
    }
    let pid = std::process::id();
    let seq = crate::pack::next_tmp_id();
    let mut staged_pairs: Vec<(PathBuf, PathBuf)> = Vec::with_capacity(sidecar_writes.len());
    for (dst_p, content) in sidecar_writes {
        let Some(parent) = dst_p.parent() else {
            anyhow::bail!("Sidecar destination `{}` has no parent", dst_p.display());
        };
        fs::create_dir_all(parent)?;
        let fname = dst_p
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("sidecar");
        let tmp_p = parent.join(format!(".turbo_stage_sidecar_{}_{}_{}", pid, seq, fname));
        let write_res: Result<()> = (|| {
            use std::io::Write;
            let mut f = create_fresh_file(&tmp_p)?;
            f.write_all(&content)?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                f.set_permissions(fs::Permissions::from_mode(0o644))?;
            }
            f.sync_all()?;
            Ok(())
        })();
        if let Err(e) = write_res {
            let _ = fs::remove_file(&tmp_p);
            for (sp, _) in &staged_pairs {
                let _ = fs::remove_file(sp);
            }
            return Err(e);
        }
        staged_pairs.push((tmp_p, dst_p));
    }
    for (tmp_p, dst_p) in &staged_pairs {
        if let Err(e) = fs::rename(tmp_p, dst_p) {
            for (sp, dp) in &staged_pairs {
                let _ = fs::remove_file(sp);
                let _ = fs::remove_file(dp);
            }
            return Err(e).with_context(|| {
                format!(
                    "Failed to atomically commit sidecar `{}` -> `{}`",
                    tmp_p.display(),
                    dst_p.display()
                )
            });
        }
    }
    Ok(())
}

pub(crate) fn compute_module_raw_import_dynlibs(
    dag: &ModuleDag,
    node: &ModuleNode,
) -> Vec<PathBuf> {
    let imps = if node.precompile_modules {
        compute_ordered_trans_imports(dag, node)
    } else {
        compute_ordered_precompile_imports(dag, node)
    };
    let mut out = Vec::new();
    let mut visited_libs: HashSet<String> = HashSet::new();
    for imp_name in imps {
        let Some(dn) = dag.nodes.get(&imp_name) else {
            continue;
        };
        if dn.is_exe_target {
            continue;
        }
        if visited_libs.contains(&dn.target_name) {
            continue;
        }
        if !node.is_exe_target && dn.target_name == node.target_name {
            if node.precompile_modules {
                if let Some(so_p) = module_dynlib_so_path(dn) {
                    out.push(so_p);
                }
            }
        } else if node.precompile_modules || dn.precompile_modules {
            visited_libs.insert(dn.target_name.clone());
            if let Some(sl) = dag
                .shared_libs
                .iter()
                .find(|s| s.pkg_root == dn.pkg_root && s.lib_name == dn.target_name)
            {
                out.push(sl.path.clone());
            }
        }
    }
    out
}

pub(super) fn compute_ordered_trans_imports(dag: &ModuleDag, node: &ModuleNode) -> Vec<String> {
    let mut out = Vec::new();
    let mut visited_mods: HashSet<String> = HashSet::new();
    let mut inserted: HashSet<String> = HashSet::new();
    fn walk(
        dag: &ModuleDag,
        cur: &str,
        out: &mut Vec<String>,
        visited_mods: &mut HashSet<String>,
        inserted: &mut HashSet<String>,
    ) {
        if !visited_mods.insert(cur.to_string()) {
            return;
        }
        let Some(dn) = dag.nodes.get(cur) else {
            return;
        };
        let mut seen_local: HashSet<&str> = HashSet::new();
        for imp in &dn.import_specs {
            let m = imp.module.as_str();
            if m != cur && seen_local.insert(m) && dag.nodes.contains_key(m) {
                walk(dag, m, out, visited_mods, inserted);
            }
        }
        if inserted.insert(cur.to_string()) {
            out.push(cur.to_string());
        }
    }
    let mut seen_root: HashSet<&str> = HashSet::new();
    for imp in &node.import_specs {
        let m = imp.module.as_str();
        if m != node.module_name && seen_root.insert(m) && dag.nodes.contains_key(m) {
            walk(dag, m, &mut out, &mut visited_mods, &mut inserted);
        }
    }
    out
}

pub(super) fn compute_ordered_precompile_imports(dag: &ModuleDag, node: &ModuleNode) -> Vec<String> {
    let mut out = Vec::new();
    let mut visited_mods: HashSet<String> = HashSet::new();
    let mut inserted: HashSet<String> = HashSet::new();
    fn walk(
        dag: &ModuleDag,
        cur: &str,
        out: &mut Vec<String>,
        visited_mods: &mut HashSet<String>,
        inserted: &mut HashSet<String>,
    ) {
        if !visited_mods.insert(cur.to_string()) {
            return;
        }
        let Some(dn) = dag.nodes.get(cur) else {
            return;
        };
        let mut seen_local: HashSet<&str> = HashSet::new();
        for imp in &dn.import_specs {
            let m = imp.module.as_str();
            if m != cur && seen_local.insert(m) && dag.nodes.contains_key(m) {
                walk(dag, m, out, visited_mods, inserted);
            }
        }
        if dn.precompile_modules && inserted.insert(cur.to_string()) {
            out.push(cur.to_string());
        }
    }
    let mut seen_root: HashSet<&str> = HashSet::new();
    for imp in &node.import_specs {
        let m = imp.module.as_str();
        if m != node.module_name && seen_root.insert(m) && dag.nodes.contains_key(m) {
            walk(dag, m, &mut out, &mut visited_mods, &mut inserted);
        }
    }
    out
}

pub(super) fn compute_module_dynlib_link_libs(dag: &ModuleDag, node: &ModuleNode) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut seen_direct: HashSet<String> = HashSet::new();
    let mut visited_libs: HashSet<String> = HashSet::new();
    for imp in &node.import_specs {
        if imp.module == node.module_name || !seen_direct.insert(imp.module.clone()) {
            continue;
        }
        let Some(dn) = dag.nodes.get(&imp.module) else {
            continue;
        };
        if dn.is_exe_target {
            continue;
        }
        if visited_libs.contains(&dn.target_name) {
            continue;
        }
        if !node.is_exe_target && dn.target_name == node.target_name {
            if let Some(so_p) = module_dynlib_so_path(dn) {
                out.push(so_p);
            }
        } else {
            visited_libs.insert(dn.target_name.clone());
            if let Some(sl) = dag
                .shared_libs
                .iter()
                .find(|s| s.pkg_root == dn.pkg_root && s.lib_name == dn.target_name)
            {
                out.push(sl.path.clone());
            }
        }
    }
    out
}

pub(super) fn compute_shared_lib_link_libs(dag: &ModuleDag, sl: &SharedLibSpec) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut visited_libs: HashSet<String> = HashSet::new();
    visited_libs.insert(sl.lib_name.clone());
    let mut seen_imps: HashSet<String> = HashSet::new();
    let mut ordered_imps = Vec::new();
    for local_mod in &sl.local_modules {
        let Some(local_node) = dag.nodes.get(local_mod) else {
            continue;
        };
        for imp in compute_ordered_trans_imports(dag, local_node) {
            if seen_imps.insert(imp.clone()) {
                ordered_imps.push(imp);
            }
        }
    }
    for imp_mod in ordered_imps {
        let Some(dn) = dag.nodes.get(&imp_mod) else {
            continue;
        };
        if dn.is_exe_target {
            continue;
        }
        if visited_libs.insert(dn.target_name.clone()) {
            if let Some(dep_sl) = dag
                .shared_libs
                .iter()
                .find(|s| s.pkg_root == dn.pkg_root && s.lib_name == dn.target_name)
            {
                out.push(dep_sl.path.clone());
            }
        }
    }
    out
}

pub(super) fn mk_load_order_paths(dag: &ModuleDag, paths: &[PathBuf]) -> Vec<(PathBuf, bool)> {
    let mut by_path: HashMap<PathBuf, &SharedLibSpec> = HashMap::new();
    for sl in &dag.shared_libs {
        by_path.insert(sl.path.clone(), sl);
    }
    let mut mod_by_dynlib: HashMap<PathBuf, &ModuleNode> = HashMap::new();
    for n in dag.nodes.values() {
        if let Some(so_p) = module_dynlib_so_path(n) {
            mod_by_dynlib.insert(so_p, n);
        }
    }
    let dynlib_name = |p: &Path| -> String {
        if let Some(sl) = by_path.get(p) {
            sl.stem.clone()
        } else if let Some(mn) = mod_by_dynlib.get(p) {
            lean_mk_module_initialization_stem(&mn.module_name, Some(&mn.pkg_name))
        } else {
            p.file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or_default()
                .to_string()
        }
    };
    let mut visited: HashSet<String> = HashSet::new();
    let mut order = Vec::new();
    #[allow(clippy::too_many_arguments)]
    fn go(
        dag: &ModuleDag,
        by_path: &HashMap<PathBuf, &SharedLibSpec>,
        mod_by_dynlib: &HashMap<PathBuf, &ModuleNode>,
        dynlib_name: &dyn Fn(&Path) -> String,
        p: &Path,
        visiting: &mut HashSet<String>,
        visited: &mut HashSet<String>,
        order: &mut Vec<(PathBuf, bool)>,
    ) {
        let name = dynlib_name(p);
        if visited.contains(&name) {
            return;
        }
        if !visiting.insert(name.clone()) {
            return;
        }
        if let Some(sl) = by_path.get(p) {
            for dep_p in compute_shared_lib_link_libs(dag, sl) {
                go(
                    dag,
                    by_path,
                    mod_by_dynlib,
                    dynlib_name,
                    &dep_p,
                    visiting,
                    visited,
                    order,
                );
            }
            order.push((sl.path.clone(), sl.is_plugin));
        } else if let Some(mn) = mod_by_dynlib.get(p) {
            for dep_p in compute_module_dynlib_link_libs(dag, mn) {
                go(
                    dag,
                    by_path,
                    mod_by_dynlib,
                    dynlib_name,
                    &dep_p,
                    visiting,
                    visited,
                    order,
                );
            }
            order.push((p.to_path_buf(), true));
        } else {
            order.push((p.to_path_buf(), true));
        }
        visiting.remove(&name);
        visited.insert(name);
    }
    let mut visiting = HashSet::new();
    for p in paths {
        go(
            dag,
            &by_path,
            &mod_by_dynlib,
            &dynlib_name,
            p,
            &mut visiting,
            &mut visited,
            &mut order,
        );
    }
    order
}

pub(super) fn compute_module_setup_load_order(
    dag: &ModuleDag,
    node: &ModuleNode,
) -> (Vec<PathBuf>, Vec<PathBuf>) {
    let raw = compute_module_raw_import_dynlibs(dag, node);
    let ordered = mk_load_order_paths(dag, &raw);
    let mut dynlibs = Vec::new();
    let mut plugins = Vec::new();
    for (p, is_plugin) in ordered {
        if is_plugin {
            plugins.push(p);
        } else {
            dynlibs.push(p);
        }
    }
    (dynlibs, plugins)
}

pub(super) fn build_setup_json(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    node: &ModuleNode,
    import_dynlib_paths: Option<&[PathBuf]>,
    import_plugin_paths: Option<&[PathBuf]>,
) -> Result<serde_json::Value> {
    let mut setup_options = serde_json::Map::new();
    for (k, v) in &node.lean_options {
        setup_options.insert(
            k.to_lean_string(),
            verification_lake_option(k, v).to_json_value(),
        );
    }
    let (mut dynlibs, mut plugins) = compute_module_setup_load_order(dag, node);
    if let Some(paths) = import_dynlib_paths {
        for p in paths {
            if !dynlibs.contains(p) && !plugins.contains(p) {
                dynlibs.push(p.clone());
            }
        }
    }
    if let Some(paths) = import_plugin_paths {
        for p in paths {
            if !plugins.contains(p) {
                plugins.push(p.clone());
            }
        }
    }
    if !dynlibs.is_empty() || !plugins.is_empty() {
        let (shared_ext, needs_lake_shared) = match query_toolchain_native_spec(&cfg.lean_bin) {
            Ok(spec) => (spec.shared_lib_ext(), spec.is_linux || spec.is_osx),
            Err(_) => (
                if cfg!(target_os = "macos") {
                    "dylib"
                } else if cfg!(target_os = "windows") {
                    "dll"
                } else {
                    "so"
                },
                cfg!(target_os = "linux") || cfg!(target_os = "macos"),
            ),
        };
        let lake_shared = cfg
            .toolchain_lib_lean
            .join(format!("libLake_shared.{}", shared_ext));
        if needs_lake_shared && lake_shared.is_file() && !plugins.iter().any(|p| p == &lake_shared)
        {
            plugins.insert(0, lake_shared);
        }
    }
    let non_module = !node.is_module;
    let resolve_mod_info = |m: &str| -> Option<(PathBuf, bool, Vec<ParsedImport>)> {
        if let Some(dn) = dag.nodes.get(m) {
            return Some((dn.olean_path.clone(), dn.is_module, dn.import_specs.clone()));
        }
        let olean_p = node
            .external_olean_deps
            .iter()
            .find(|(em, _)| em == m)
            .map(|(_, p)| p.clone())
            .or_else(|| {
                resolve_importable_module_in_package(&cfg.root_pkg, true, m)
                    .or_else(|| {
                        cfg.dep_pkgs
                            .iter()
                            .find_map(|dp| resolve_importable_module_in_package(dp, false, m))
                    })
                    .map(|sp| {
                        sp.build_lib_lean_dir
                            .join(format!("{}.olean", module_name_to_rel_slash(m)))
                    })
            })?;
        let src_opt = resolve_importable_module_in_package(&cfg.root_pkg, true, m)
            .or_else(|| {
                cfg.dep_pkgs
                    .iter()
                    .find_map(|dp| resolve_importable_module_in_package(dp, false, m))
            })
            .map(|sp| sp.src_path);
        let (is_mod, specs) = match src_opt {
            Some(sp) if sp.is_file() => {
                let raw = fs::read_to_string(&sp).unwrap_or_default();
                let hdr = parse_header_info(&raw);
                (hdr.is_module, hdr.import_specs)
            }
            _ => (
                PathBuf::from(format!("{}.server", olean_p.display())).is_file(),
                Vec::new(),
            ),
        };
        Some((olean_p, is_mod, specs))
    };
    let flat_import_arts = lake_trace_uses_nested_mod_deps(&cfg.toolchain);
    let make_arts = |olean_p: &Path, is_mod: bool, want_all: bool| -> serde_json::Value {
        let olean = olean_p.to_string_lossy().to_string();
        if flat_import_arts {
            if !is_mod {
                serde_json::json!([olean])
            } else {
                let ir = olean_p.with_extension("ir").to_string_lossy().to_string();
                let srv = format!("{}.server", olean_p.display());
                if want_all {
                    serde_json::json!([olean, ir, srv, format!("{}.private", olean_p.display())])
                } else {
                    serde_json::json!([olean, ir, srv])
                }
            }
        } else if !is_mod {
            serde_json::json!([[olean]])
        } else {
            let ir_p = olean_p.with_extension("ir");
            let mut olean_group = vec![olean, format!("{}.server", olean_p.display())];
            if want_all {
                olean_group.push(format!("{}.private", olean_p.display()));
            }
            serde_json::json!([
                olean_group,
                [format!("{}.sig", ir_p.display()), ir_p.to_string_lossy()]
            ])
        }
    };
    let mut import_arts = serde_json::Map::new();
    let mut is_mod_map: HashMap<String, bool> = HashMap::new();
    let mut has_priv_map: HashMap<String, bool> = HashMap::new();
    let mut walk_stack: Vec<(String, bool, bool)> = Vec::new();
    for imp in &node.import_specs {
        if imp.module == node.module_name {
            continue;
        }
        let Some((olean_p, is_mod, _)) = resolve_mod_info(&imp.module) else {
            continue;
        };
        let want_all = non_module || imp.import_all;
        let prev_priv = has_priv_map.get(&imp.module).copied().unwrap_or(false);
        let final_all = want_all || prev_priv;
        if !import_arts.contains_key(&imp.module) || final_all {
            import_arts.insert(imp.module.clone(), make_arts(&olean_p, is_mod, final_all));
            is_mod_map.insert(imp.module.clone(), is_mod);
            has_priv_map.insert(imp.module.clone(), is_mod && final_all);
        }
    }
    for imp in node.import_specs.iter().rev() {
        if imp.module == node.module_name {
            continue;
        }
        let Some((_, _, sub_specs)) = resolve_mod_info(&imp.module) else {
            continue;
        };
        let imp_all = non_module || imp.import_all;
        for sub in sub_specs.iter().rev() {
            if sub.module == imp.module {
                continue;
            }
            let reachable = imp_all || sub.is_exported;
            let c_all = non_module || (imp_all && sub.import_all);
            let c_meta = imp.is_meta || (reachable && sub.is_meta);
            if reachable || c_meta {
                walk_stack.push((sub.module.clone(), c_all, c_meta));
            }
        }
    }
    let mut all_visited: HashSet<String> = HashSet::new();
    let mut meta_visited: HashSet<String> = HashSet::new();
    while let Some((cur, import_all, needs_meta)) = walk_stack.pop() {
        let Some((olean_p, is_mod, sub_specs)) = resolve_mod_info(&cur) else {
            continue;
        };
        let do_all = import_all && !all_visited.contains(&cur);
        let do_meta = needs_meta && !meta_visited.contains(&cur);
        if import_arts.contains_key(&cur) {
            let ex_mod = is_mod_map.get(&cur).copied().unwrap_or(false);
            if !(ex_mod && (do_all || do_meta)) {
                continue;
            }
        }
        if import_all {
            all_visited.insert(cur.clone());
        }
        if needs_meta {
            meta_visited.insert(cur.clone());
        }
        let want_all =
            all_visited.contains(&cur) || has_priv_map.get(&cur).copied().unwrap_or(false);
        import_arts.insert(cur.clone(), make_arts(&olean_p, is_mod, want_all));
        is_mod_map.insert(cur.clone(), is_mod);
        has_priv_map.insert(cur.clone(), is_mod && want_all);
        for sub in sub_specs.iter().rev() {
            if sub.module == cur {
                continue;
            }
            let reachable = import_all || sub.is_exported;
            let child_import_all = non_module || (import_all && sub.import_all);
            let child_needs_meta = needs_meta || (reachable && sub.is_meta);
            if reachable || child_needs_meta {
                walk_stack.push((sub.module.clone(), child_import_all, child_needs_meta));
            }
        }
    }
    let dynlibs_json: Vec<String> = dynlibs
        .iter()
        .map(|p| p.to_string_lossy().to_string())
        .collect();
    let string_plugins =
        matches!(parse_toolchain_major_minor(&cfg.toolchain), Some((4, m)) if m < 31);
    let plugins_json: Vec<serde_json::Value> = plugins
        .iter()
        .map(|p| {
            if string_plugins {
                serde_json::Value::String(p.to_string_lossy().to_string())
            } else {
                serde_json::json!({"path": p.to_string_lossy()})
            }
        })
        .collect();
    Ok(serde_json::json!({
        "name": node.module_name,
        "package": node.pkg_name,
        "isModule": node.is_module,
        "options": setup_options,
        "importArts": import_arts,
        "dynlibs": dynlibs_json,
        "plugins": plugins_json
    }))
}

#[derive(Debug, Clone)]
pub(super) struct ToolchainNativeSpec {
    pub(super) target: String,
    pub(super) is_windows: bool,
    pub(super) is_osx: bool,
    pub(super) is_linux: bool,
    pub(super) c_flags: Vec<String>,
    pub(super) internal_c_flags: Vec<String>,
    pub(super) link_shared_flags: Vec<String>,
    pub(super) internal_linker_flags: Vec<String>,
}

impl ToolchainNativeSpec {
    pub(super) fn shared_lib_ext(&self) -> &'static str {
        if self.is_osx {
            "dylib"
        } else if self.is_windows {
            "dll"
        } else {
            "so"
        }
    }
}

pub(super) type ToolchainNativeCacheKey = (PathBuf, u64, Option<std::time::SystemTime>);

pub(super) static TOOLCHAIN_NATIVE_CACHE: OnceLock<
    Mutex<HashMap<ToolchainNativeCacheKey, ToolchainNativeSpec>>,
> = OnceLock::new();

pub(super) fn cached_toolchain_shared_lib_ext() -> Option<&'static str> {
    let guard = TOOLCHAIN_NATIVE_CACHE.get()?.lock().ok()?;
    guard
        .values()
        .next()
        .map(ToolchainNativeSpec::shared_lib_ext)
}

pub(super) fn query_toolchain_native_spec(lean_bin: &Path) -> Result<ToolchainNativeSpec> {
    let canon_bin = lean_bin
        .canonicalize()
        .unwrap_or_else(|_| lean_bin.to_path_buf());
    let (bin_len, bin_mtime) = fs::metadata(&canon_bin)
        .map(|m| (m.len(), m.modified().ok()))
        .unwrap_or((0, None));
    let cache_key = (canon_bin.clone(), bin_len, bin_mtime);
    let cache = TOOLCHAIN_NATIVE_CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    if let Ok(guard) = cache.lock() {
        if let Some(spec) = guard.get(&cache_key) {
            return Ok(spec.clone());
        }
    }
    const ROOT_SENTINEL: &str = "__TURBO_LEAN_SYSROOT_SENTINEL__";
    let script = [
        "import Lean.Compiler.FFI",
        "def main : IO Unit := do",
        "  IO.println s!\"TARGET\\t{System.Platform.target}\"",
        "  IO.println s!\"IS_WINDOWS\\t{System.Platform.isWindows}\"",
        "  IO.println s!\"IS_OSX\\t{System.Platform.isOSX}\"",
        "  IO.println s!\"IS_LINUX\\t{(System.Platform.target.splitOn \"-\").contains \"linux\"}\"",
        "  for f in Lean.Compiler.FFI.getCFlags'.push \"-Wno-unused-command-line-argument\" do",
        "    IO.println s!\"CFLAG\\t{f}\"",
        &format!("  for f in Lean.Compiler.FFI.getInternalCFlags \"{ROOT_SENTINEL}\" do"),
        "    IO.println s!\"INT_CFLAG\\t{f}\"",
        "  for f in Lean.Compiler.FFI.getLinkerFlags' (linkStatic := false) do",
        "    IO.println s!\"LINK_SHARED\\t{f}\"",
        &format!("  for f in Lean.Compiler.FFI.getInternalLinkerFlags \"{ROOT_SENTINEL}\" do"),
        "    IO.println s!\"INT_LINK\\t{f}\"",
        "",
    ]
    .join("\n");
    let mut query_cmd = Command::new(&canon_bin);
    scrub_untrusted_env(&mut query_cmd);
    query_cmd
        .env("PATH", verifier_path(&canon_bin))
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SRC_PATH")
        .env_remove("LEAN_SYSROOT")
        .arg("--stdin")
        .arg("--run")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    let mut child = query_cmd.spawn().with_context(|| {
        format!(
            "Failed to spawn `{}` to query Lean toolchain native C/linker flags",
            canon_bin.display()
        )
    })?;
    if let Some(mut stdin) = child.stdin.take() {
        use std::io::Write;
        stdin.write_all(script.as_bytes()).with_context(|| {
            format!(
                "Failed to pipe native config query into `{}`",
                canon_bin.display()
            )
        })?;
    }
    let out = child.wait_with_output().with_context(|| {
        format!(
            "Failed waiting for `{}` native config query",
            canon_bin.display()
        )
    })?;
    if !out.status.success() {
        anyhow::bail!(
            "`{} --stdin --run` failed querying `Lean.Compiler.FFI` flags: {} {}",
            canon_bin.display(),
            String::from_utf8_lossy(&out.stderr).trim(),
            String::from_utf8_lossy(&out.stdout).trim()
        );
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    let mut target = None;
    let mut is_windows = None;
    let mut is_osx = None;
    let mut is_linux = None;
    let mut c_flags = Vec::new();
    let mut internal_c_flags = Vec::new();
    let mut link_shared_flags = Vec::new();
    let mut internal_linker_flags = Vec::new();
    for line in stdout.lines() {
        let Some((tag, val)) = line.split_once('\t') else {
            continue;
        };
        match tag {
            "TARGET" => target = Some(val.to_string()),
            "IS_WINDOWS" => is_windows = Some(val == "true"),
            "IS_OSX" => is_osx = Some(val == "true"),
            "IS_LINUX" => is_linux = Some(val == "true"),
            "CFLAG" => c_flags.push(val.to_string()),
            "INT_CFLAG" => internal_c_flags.push(val.to_string()),
            "LINK_SHARED" => link_shared_flags.push(val.to_string()),
            "INT_LINK" => internal_linker_flags.push(val.to_string()),
            _ => {}
        }
    }
    let target = target.filter(|s| !s.is_empty()).ok_or_else(|| {
        anyhow::anyhow!(
            "Toolchain `{}` returned empty `System.Platform.target`",
            canon_bin.display()
        )
    })?;
    let spec = ToolchainNativeSpec {
        target,
        is_windows: is_windows.unwrap_or(cfg!(target_os = "windows")),
        is_osx: is_osx.unwrap_or(cfg!(target_os = "macos")),
        is_linux: is_linux.unwrap_or(cfg!(target_os = "linux")),
        c_flags,
        internal_c_flags,
        link_shared_flags,
        internal_linker_flags,
    };
    if let Ok(mut guard) = cache.lock() {
        guard.insert(cache_key, spec.clone());
    }
    Ok(spec)
}

pub(super) fn validate_cc_outside_workspace(cfg: &ProjectConfig, candidate: &Path) -> Result<PathBuf> {
    let mut resolved = crate::trusted_tools::outside_checkout(candidate, &cfg.root_pkg.pkg_root)?;
    for dp in &cfg.dep_pkgs {
        resolved = crate::trusted_tools::outside_checkout(&resolved, &dp.pkg_root)?;
    }
    Ok(resolved)
}

pub(super) type LakeCcSpec = (PathBuf, Vec<String>, Vec<String>, ToolchainNativeSpec, bool);

pub(super) fn lake_cc_and_flags(cfg: &ProjectConfig) -> Result<LakeCcSpec> {
    const ROOT_SENTINEL: &str = "__TURBO_LEAN_SYSROOT_SENTINEL__";
    let _tools = ToolchainExecutables::from_lean(&cfg.lean_bin)?;
    let canon_lean = cfg
        .lean_bin
        .canonicalize()
        .with_context(|| format!("Cannot resolve `{}`", cfg.lean_bin.display()))?;
    let sysroot = canon_lean
        .parent()
        .and_then(|p| p.parent())
        .ok_or_else(|| {
            anyhow::anyhow!("Cannot derive Lean sysroot from `{}`", canon_lean.display())
        })?
        .canonicalize()
        .with_context(|| {
            format!(
                "Cannot canonicalize Lean sysroot for `{}`",
                canon_lean.display()
            )
        })?;
    let sysroot_bin = sysroot.join("bin");
    let sysroot_str = sysroot.to_string_lossy();
    let spec = query_toolchain_native_spec(&canon_lean)?;
    let bundled_clang = if spec.is_windows {
        sysroot_bin.join("clang.exe")
    } else {
        sysroot_bin.join("clang")
    };
    let non_empty_env = |name: &str| -> Option<String> {
        std::env::var(name)
            .ok()
            .map(|v| v.trim().to_string())
            .filter(|v| !v.is_empty())
    };
    let (cc, custom_cc) = if let Some(lean_cc) = non_empty_env("LEAN_CC") {
        (
            validate_cc_outside_workspace(cfg, Path::new(&lean_cc))?,
            true,
        )
    } else if let Some(nix_cc) = option_env!("TURBO_LEAN_NIX_DEFAULT_CC").filter(|s| !s.is_empty())
    {
        (validate_cc_outside_workspace(cfg, Path::new(nix_cc))?, true)
    } else if bundled_clang.is_file() {
        let canon_clang = bundled_clang.canonicalize().with_context(|| {
            format!(
                "Cannot canonicalize toolchain bundled clang `{}`",
                bundled_clang.display()
            )
        })?;
        anyhow::ensure!(
            canon_clang.starts_with(&sysroot) && canon_clang.parent() == Some(sysroot_bin.as_path()),
            "Toolchain bundled clang `{}` escaped toolchain sysroot `{}`: fail-closed toolchain gate",
            canon_clang.display(),
            sysroot.display()
        );
        let validated = validate_cc_outside_workspace(cfg, &canon_clang)?;
        (validated, false)
    } else if let Some(cc_env) = non_empty_env("CC") {
        (
            validate_cc_outside_workspace(cfg, Path::new(&cc_env))?,
            true,
        )
    } else {
        let sys_cc = ["/usr/bin", "/bin", "/usr/local/bin", "/usr/sbin", "/sbin"]
            .into_iter()
            .find_map(|dir| {
                let cand = Path::new(dir).join("cc");
                let resolved =
                    crate::trusted_tools::system_executable(&cand, &cfg.root_pkg.pkg_root).ok()?;
                for dp in &cfg.dep_pkgs {
                    crate::trusted_tools::system_executable(&resolved, &dp.pkg_root).ok()?;
                }
                Some(resolved)
            })
            .ok_or_else(|| {
                anyhow::anyhow!("No trusted system executable found for fallback C compiler `cc`")
            })?;
        (sys_cc, true)
    };
    let mut cflags = spec.c_flags.clone();
    if !custom_cc {
        cflags.extend(
            spec.internal_c_flags
                .iter()
                .map(|f| f.replace(ROOT_SENTINEL, &sysroot_str)),
        );
    }
    let mut link_flags = vec![
        "-L".to_string(),
        sysroot.join("lib/lean").to_string_lossy().to_string(),
    ];
    if !custom_cc {
        link_flags.extend(
            spec.internal_linker_flags
                .iter()
                .map(|f| f.replace(ROOT_SENTINEL, &sysroot_str)),
        );
    }
    link_flags.extend(spec.link_shared_flags.iter().cloned());
    Ok((cc, cflags, link_flags, spec, custom_cc))
}

pub(super) fn regular_file_matches_bytes_0644(dst_p: &Path, content: &[u8]) -> bool {
    let Ok(meta) = fs::symlink_metadata(dst_p) else {
        return false;
    };
    if !meta.file_type().is_file() || meta.len() != content.len() as u64 {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        if meta.nlink() != 1 || (meta.permissions().mode() & 0o777) != 0o644 {
            return false;
        }
    }
    fs::read(dst_p).is_ok_and(|existing| existing == content)
}

pub(super) fn write_file_atomic(dst_p: &Path, content: &[u8]) -> Result<()> {
    if regular_file_matches_bytes_0644(dst_p, content) {
        return Ok(());
    }
    let Some(parent) = dst_p.parent() else {
        anyhow::bail!("Destination `{}` has no parent", dst_p.display());
    };
    fs::create_dir_all(parent)?;
    let pid = std::process::id();
    let seq = crate::pack::next_tmp_id();
    let fname = dst_p
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("native_out");
    let tmp_p = parent.join(format!(".turbo_stage_native_{}_{}_{}", pid, seq, fname));
    let res: Result<()> = (|| {
        use std::io::Write;
        let mut f = create_fresh_file(&tmp_p)?;
        f.write_all(content)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            f.set_permissions(fs::Permissions::from_mode(0o644))?;
        }
        f.sync_all()?;
        Ok(())
    })();
    if let Err(e) = res {
        let _ = fs::remove_file(&tmp_p);
        return Err(e);
    }
    fs::rename(&tmp_p, dst_p).with_context(|| {
        let _ = fs::remove_file(&tmp_p);
        format!(
            "Failed to atomically commit `{}` -> `{}`",
            tmp_p.display(),
            dst_p.display()
        )
    })?;
    Ok(())
}

pub(super) fn write_rsp_file(rsp_path: &Path, args: &[String]) -> Result<()> {
    let mut body = String::new();
    for arg in args {
        let escaped = arg.replace('\\', "\\\\").replace('"', "\\\"");
        body.push('"');
        body.push_str(&escaped);
        body.push_str("\"\n");
    }
    write_file_atomic(rsp_path, body.as_bytes())
}

pub(super) fn write_native_facet_trace(
    trace_path: &Path,
    outputs: serde_json::Value,
    inputs: serde_json::Value,
) -> Result<()> {
    let dep_hash = lake_input_hash(&inputs)?;
    let trace = serde_json::json!({
        "synthetic": false,
        "schemaVersion": "2025-09-10",
        "outputs": outputs,
        "log": [],
        "inputs": inputs,
        "depHash": format!("{:016x}", dep_hash)
    });
    write_file_atomic(trace_path, &serde_json::to_vec(&trace)?)
}

pub(super) fn build_module_co_export(cfg: &ProjectConfig, node: &ModuleNode) -> Result<PathBuf> {
    let co_path = module_co_export_path(node);
    let Some(parent) = co_path.parent() else {
        anyhow::bail!("`.c.o.export` path `{}` has no parent", co_path.display());
    };
    fs::create_dir_all(parent)?;
    let (cc, cflags, _link_flags, toolchain_native, _custom_cc) = lake_cc_and_flags(cfg)?;
    let sysroot = cfg
        .lean_bin
        .canonicalize()
        .with_context(|| format!("Cannot resolve `{}`", cfg.lean_bin.display()))?
        .parent()
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .ok_or_else(|| anyhow::anyhow!("Cannot derive Lean sysroot"))?;
    let Some(co_fname) = co_path.file_name() else {
        anyhow::bail!(
            "`.c.o.export` path `{}` has no file name",
            co_path.display()
        );
    };
    let pid = std::process::id();
    let seq = crate::pack::next_tmp_id();
    let tmp_dir = parent.join(format!(".turbo_tmp_co_dir_{}_{}", pid, seq));
    fs::create_dir(&tmp_dir).with_context(|| {
        format!(
            "Failed to create private staging directory `{}` for `{}`",
            tmp_dir.display(),
            co_path.display()
        )
    })?;
    let tmp_co = tmp_dir.join(co_fname);
    let co_res: Result<Vec<u8>> = (|| {
        let mut cmd = Command::new(&cc);
        scrub_untrusted_env(&mut cmd);
        cmd.env("PATH", verifier_path(&cfg.lean_bin))
            .arg("-c")
            .arg("-o")
            .arg(&tmp_co)
            .arg(&node.c_path)
            .arg("-I")
            .arg(sysroot.join("include"));
        for flag in &cflags {
            cmd.arg(flag);
        }
        cmd.arg("-O3").arg("-DNDEBUG").arg("-DLEAN_EXPORTING");
        let out = cmd.output().with_context(|| {
            format!(
                "Failed to spawn clang for `.c.o.export` of `{}`",
                node.module_name
            )
        })?;
        if !out.status.success() {
            anyhow::bail!(
                "clang failed building `.c.o.export` for `{}`: {}",
                node.module_name,
                String::from_utf8_lossy(&out.stderr)
            );
        }
        let co_bytes = fs::read(&tmp_co)
            .with_context(|| format!("Failed to read staged `{}`", tmp_co.display()))?;
        fs::rename(&tmp_co, &co_path)
            .with_context(|| format!("Failed to commit `{}`", co_path.display()))?;
        Ok(co_bytes)
    })();
    let _ = fs::remove_dir_all(&tmp_dir);
    let co_bytes = co_res?;
    let co_h = lake_hash_bytes(&co_bytes);
    write_file_atomic(
        &PathBuf::from(format!("{}.hash", co_path.display())),
        format!("{:016x}", co_h).as_bytes(),
    )?;
    let c_bytes = fs::read(&node.c_path)?;
    let c_h = lake_hash_bytes(&c_bytes);
    let ver_short = cfg
        .toolchain
        .rsplit(':')
        .next()
        .unwrap_or(&cfg.toolchain)
        .trim_start_matches('v');
    let lean_cap = format!("Lean {}, commit {}", ver_short, cfg.lean_githash);
    let lean_gh_h = lake_hash_bytes(cfg.lean_githash.as_bytes());
    let platform = toolchain_native.target.clone();
    let platform_h = lake_hash_bytes(platform.as_bytes());
    let trace_args = ["-O3", "-DNDEBUG", "-DLEAN_EXPORTING"];
    let trace_args_cap = format!("traceArgs: #[{}]", trace_args.join(", "));
    let trace_args_h = trace_args.iter().fold(1723u64, |acc, a| {
        lake_mix_hash(acc, lake_hash_bytes(a.as_bytes()))
    });
    let inputs = serde_json::json!([
        [
            format!("{}:c", node.module_name),
            [
                [node.c_path.to_string_lossy(), format!("{:016x}", c_h)],
                [lean_cap, format!("{:016x}", lean_gh_h)]
            ]
        ],
        [lean_cap, format!("{:016x}", lean_gh_h)],
        [trace_args_cap, format!("{:016x}", trace_args_h)],
        [platform, format!("{:016x}", platform_h)]
    ]);
    write_native_facet_trace(
        &PathBuf::from(format!("{}.trace", co_path.display())),
        serde_json::json!(format!("{:016x}.o", co_h)),
        inputs,
    )?;
    Ok(co_path)
}

pub(super) fn native_link_package_roots(dag: &ModuleDag, so_path: &Path) -> Result<BTreeSet<PathBuf>> {
    let mut roots = BTreeSet::new();
    let mut pending = Vec::new();
    if let Some(sl) = dag.shared_libs.iter().find(|s| s.path == so_path) {
        roots.insert(sl.pkg_root.clone());
        pending.extend(sl.local_modules.iter().cloned());
    } else if let Some(node) = dag
        .nodes
        .values()
        .find(|n| module_dynlib_so_path(n).as_deref() == Some(so_path))
    {
        pending.push(node.module_name.clone());
    } else {
        anyhow::bail!(
            "No owning package for shared object `{}`",
            so_path.display()
        );
    }
    let mut visited = HashSet::new();
    while let Some(name) = pending.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        let node = dag
            .nodes
            .get(&name)
            .with_context(|| format!("Missing native dependency `{name}`"))?;
        roots.insert(node.pkg_root.clone());
        for (_, path) in &node.external_olean_deps {
            if let Some(root) = infer_pkg_root_from_artifact_path(path) {
                roots.insert(root);
            }
        }
        pending.extend(node.direct_dag_deps.iter().cloned());
    }
    Ok(roots)
}

pub(super) fn build_shared_object(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    so_path: &Path,
    link_objs: &[PathBuf],
    link_libs: &[PathBuf],
) -> Result<()> {
    let Some(parent) = so_path.parent() else {
        anyhow::bail!("Shared object path `{}` has no parent", so_path.display());
    };
    fs::create_dir_all(parent)?;
    let (cc, _cflags, link_flags, toolchain_native, _custom_cc) = lake_cc_and_flags(cfg)?;
    let mut rsp_args: Vec<String> = link_objs
        .iter()
        .map(|p| p.to_string_lossy().to_string())
        .collect();
    let native_roots = native_link_package_roots(dag, so_path)?;
    for pkg in std::iter::once(&cfg.root_pkg)
        .chain(&cfg.dep_pkgs)
        .filter(|p| native_roots.contains(&p.pkg_root))
    {
        for ext in &pkg.extern_libs {
            let path = ext
                .static_artifact_path
                .as_ref()
                .context("Missing materialized native archive")?;
            let digest = blake3::hash(&fs::read(path)?).to_hex().to_string();
            anyhow::ensure!(
                ext.static_artifact_blake3.as_ref() == Some(&digest),
                "Native archive changed after materialization: {}",
                path.display()
            );
            rsp_args.push(path.to_string_lossy().into_owned());
        }
    }
    if toolchain_native.is_windows {
        let mut by_path: HashMap<PathBuf, &SharedLibSpec> = HashMap::new();
        for sl in &dag.shared_libs {
            by_path.insert(sl.path.clone(), sl);
        }
        let mut mod_by_dynlib: HashMap<PathBuf, &ModuleNode> = HashMap::new();
        for n in dag.nodes.values() {
            if let Some(so_p) = module_dynlib_so_path(n) {
                mod_by_dynlib.insert(so_p, n);
            }
        }
        let mut visited: HashSet<PathBuf> = HashSet::new();
        let mut order: Vec<PathBuf> = Vec::new();
        fn mk_link_order(
            dag: &ModuleDag,
            by_path: &HashMap<PathBuf, &SharedLibSpec>,
            mod_by_dynlib: &HashMap<PathBuf, &ModuleNode>,
            p: &Path,
            visiting: &mut HashSet<PathBuf>,
            visited: &mut HashSet<PathBuf>,
            order: &mut Vec<PathBuf>,
        ) -> Result<()> {
            order.push(p.to_path_buf());
            if visited.contains(p) {
                return Ok(());
            }
            if !visiting.insert(p.to_path_buf()) {
                anyhow::bail!("library dependency cycle involving `{}`", p.display());
            }
            visited.insert(p.to_path_buf());
            let deps = if let Some(sl) = by_path.get(p) {
                compute_shared_lib_link_libs(dag, sl)
            } else if let Some(mn) = mod_by_dynlib.get(p) {
                compute_module_dynlib_link_libs(dag, mn)
            } else {
                Vec::new()
            };
            for dep_p in deps {
                mk_link_order(
                    dag,
                    by_path,
                    mod_by_dynlib,
                    &dep_p,
                    visiting,
                    visited,
                    order,
                )?;
            }
            visiting.remove(p);
            Ok(())
        }
        for p in link_libs {
            let mut visiting = HashSet::new();
            mk_link_order(
                dag,
                &by_path,
                &mod_by_dynlib,
                p,
                &mut visiting,
                &mut visited,
                &mut order,
            )?;
        }
        for p in &order {
            if let Some(dir) = p.parent() {
                rsp_args.push(format!("-L{}", dir.display()));
            }
            if let Some(sl) = by_path.get(p) {
                rsp_args.push(format!("-l{}", sl.stem));
            } else if let Some(mn) = mod_by_dynlib.get(p) {
                let stem = lean_mk_module_initialization_stem(&mn.module_name, Some(&mn.pkg_name));
                rsp_args.push(format!("-l{}", stem));
            } else if let Some(stem) = p.file_stem().and_then(|s| s.to_str()) {
                let name = if toolchain_native.is_windows {
                    stem
                } else {
                    stem.strip_prefix("lib").unwrap_or(stem)
                };
                rsp_args.push(format!("-l{}", name));
            }
        }
    }
    rsp_args.extend(link_flags);
    let rsp_path = PathBuf::from(format!("{}.rsp", so_path.display()));
    write_rsp_file(&rsp_path, &rsp_args)?;
    let ext = toolchain_native.shared_lib_ext();
    let Some(so_fname) = so_path.file_name() else {
        anyhow::bail!(
            "Shared object path `{}` has no file name",
            so_path.display()
        );
    };
    let pid = std::process::id();
    let seq = crate::pack::next_tmp_id();
    let tmp_dir = parent.join(format!(".turbo_tmp_so_dir_{}_{}", pid, seq));
    fs::create_dir(&tmp_dir).with_context(|| {
        format!(
            "Failed to create private staging directory `{}` for `{}`",
            tmp_dir.display(),
            so_path.display()
        )
    })?;
    let tmp_so = tmp_dir.join(so_fname);
    let link_res: Result<Vec<u8>> = (|| {
        let mut cmd = Command::new(&cc);
        scrub_untrusted_env(&mut cmd);
        cmd.env("PATH", verifier_path(&cfg.lean_bin)).arg("-shared");
        if toolchain_native.is_osx {
            cmd.arg("-install_name").arg(so_path);
        }
        cmd.arg("-o")
            .arg(&tmp_so)
            .arg(format!("@{}", rsp_path.display()));
        let out = cmd.output().with_context(|| {
            format!(
                "Failed to spawn clang for shared library `{}`",
                so_path.display()
            )
        })?;
        if !out.status.success() {
            anyhow::bail!(
                "clang failed linking `{}`: {}",
                so_path.display(),
                String::from_utf8_lossy(&out.stderr)
            );
        }
        let so_bytes = fs::read(&tmp_so)
            .with_context(|| format!("Failed to read staged `{}`", tmp_so.display()))?;
        fs::rename(&tmp_so, so_path)
            .with_context(|| format!("Failed to commit `{}`", so_path.display()))?;
        Ok(so_bytes)
    })();
    let _ = fs::remove_dir_all(&tmp_dir);
    let so_bytes = link_res?;
    let so_h = lake_hash_bytes(&so_bytes);
    write_file_atomic(
        &PathBuf::from(format!("{}.hash", so_path.display())),
        format!("{:016x}", so_h).as_bytes(),
    )?;
    let mut obj_entries = Vec::new();
    for p in link_objs {
        let h = verify_and_hash_artifact_bytes(p, true, true)?;
        obj_entries.push(serde_json::json!([
            p.to_string_lossy(),
            format!("{:016x}", h)
        ]));
    }
    let mut lib_entries: Vec<serde_json::Value> = Vec::new();
    for p in link_libs {
        let h = verify_and_hash_artifact_bytes(p, true, true)?;
        lib_entries.push(serde_json::json!([
            p.to_string_lossy(),
            format!("{:016x}", h)
        ]));
    }
    let link_libs_json = if lib_entries.is_empty() {
        serde_json::Value::String("00000000000006bb".to_string())
    } else {
        serde_json::Value::Array(lib_entries)
    };
    let ver_short = cfg
        .toolchain
        .rsplit(':')
        .next()
        .unwrap_or(&cfg.toolchain)
        .trim_start_matches('v');
    let lean_cap = format!("Lean {}, commit {}", ver_short, cfg.lean_githash);
    let lean_gh_h = lake_hash_bytes(cfg.lean_githash.as_bytes());
    let platform = toolchain_native.target.clone();
    let platform_h = lake_hash_bytes(platform.as_bytes());
    let inputs = serde_json::json!([
        ["linkObjs", obj_entries],
        ["linkLibs", link_libs_json],
        ["traceArgs: #[]", "00000000000006bb"],
        [lean_cap, format!("{:016x}", lean_gh_h)],
        [platform, format!("{:016x}", platform_h)]
    ]);
    write_native_facet_trace(
        &PathBuf::from(format!("{}.trace", so_path.display())),
        serde_json::json!(format!("{:016x}.{}", so_h, ext)),
        inputs,
    )?;
    Ok(())
}

pub(super) fn build_wave_native_artifacts(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    canon_project_dir: &Path,
    wave: &[String],
    preserve_project: bool,
    completed_mods: &HashSet<String>,
    built_shared_libs: &mut HashSet<(PathBuf, String)>,
) -> Result<()> {
    if preserve_project {
        return Ok(());
    }
    for mod_name in wave {
        let Some(node) = dag.nodes.get(mod_name) else {
            continue;
        };
        if package_is_read_only(canon_project_dir, &node.pkg_root) {
            continue;
        }
        if node.needs_co_export {
            build_module_co_export(cfg, node)?;
        }
        if node.needs_dynlib {
            if let Some(so_path) = module_dynlib_so_path(node) {
                let co_path = module_co_export_path(node);
                let link_libs = compute_module_dynlib_link_libs(dag, node);
                build_shared_object(cfg, dag, &so_path, &[co_path], &link_libs)?;
            }
        }
    }
    for sl in &dag.shared_libs {
        let key = (sl.pkg_root.clone(), sl.lib_name.clone());
        if built_shared_libs.contains(&key) {
            continue;
        }
        if !sl.local_modules.iter().all(|m| completed_mods.contains(m)) {
            continue;
        }
        let Some(pkg) = std::iter::once(&cfg.root_pkg)
            .chain(&cfg.dep_pkgs)
            .find(|p| p.pkg_root == sl.pkg_root)
        else {
            continue;
        };
        if package_is_read_only(canon_project_dir, &pkg.pkg_root) {
            built_shared_libs.insert(key);
            continue;
        }
        let mut link_objs = Vec::with_capacity(sl.local_modules.len());
        for m in &sl.local_modules {
            if let Some(mn) = dag.nodes.get(m) {
                link_objs.push(module_co_export_path(mn));
            }
        }
        let link_libs = compute_shared_lib_link_libs(dag, sl);
        build_shared_object(cfg, dag, &sl.path, &link_objs, &link_libs)?;
        built_shared_libs.insert(key);
    }
    Ok(())
}

pub(super) static PUBLISH_LOCK: OnceLock<Mutex<()>> = OnceLock::new();

/// `#436` / P7: a package outside the project being built (e.g. `require x from "../x"`) or one
/// that opts out of worktree linking is read-only. Its Lake-built artifacts may be reused, but
/// nothing is compiled, published, wiped or locked under its `.lake`.
pub(super) fn package_is_read_only(canon_project_dir: &Path, pkg_root: &Path) -> bool {
    !pkg_root.starts_with(canon_project_dir)
        || crate::lake_build::worktree_auto_link_disabled(pkg_root)
}

/// Error for a module of a read-only package that would need a rebuild.
pub(super) fn read_only_package_rebuild_error(
    canon_project_dir: &Path,
    node: &ModuleNode,
    what: &str,
) -> anyhow::Error {
    if node.pkg_root.starts_with(canon_project_dir) {
        anyhow::anyhow!(
            "Worktree opt-out prevents {what} `{}`; build with Lake first",
            node.module_name
        )
    } else {
        anyhow::anyhow!(
            "Dependency `{}` at `{}` is outside this project, so turbo-lean never compiles or publishes into it, and its module `{}` is stale or unbuilt: run `lake build {}` in `{}` first",
            node.pkg_name,
            node.pkg_root.display(),
            node.module_name,
            node.target_name,
            node.pkg_root.display()
        )
    }
}

pub(super) fn acquire_publish_flock_mode(
    pkg_root: &Path,
    exclusive: bool,
    preserve_lake: bool,
) -> Result<crate::shm_cache::PublishFlockGuard> {
    crate::shm_cache::acquire_publish_flock(pkg_root, exclusive, preserve_lake).with_context(|| {
        format!(
            "Failed to acquire publication flock for `{}`",
            pkg_root.display()
        )
    })
}

pub(super) fn acquire_publish_flock(
    pkg_root: &Path,
    preserve_lake: bool,
) -> Result<crate::shm_cache::PublishFlockGuard> {
    acquire_publish_flock_mode(pkg_root, true, preserve_lake)
}

#[derive(Clone, Debug)]
pub(super) struct BackupRecord {
    pub(super) dst_path: PathBuf,
    pub(super) backup_file: Option<(PathBuf, blake3::Hash, u64)>,
}

/// Create a staging/backup file at a predictable path without following anything already
/// there: a planted symlink is removed (not its target), then the file is created exclusively.
pub(super) fn create_fresh_file(p: &Path) -> std::io::Result<fs::File> {
    if fs::symlink_metadata(p).is_ok() {
        fs::remove_file(p)?;
    }
    fs::OpenOptions::new().write(true).create_new(true).open(p)
}
pub(super) fn sync_parent_dir(p: &Path) -> Result<()> {
    #[cfg(unix)]
    if let Some(parent) = p.parent() {
        let df = fs::File::open(parent).with_context(|| {
            format!(
                "Failed to open parent directory `{}` for fsync",
                parent.display()
            )
        })?;
        df.sync_all()
            .with_context(|| format!("Failed to fsync parent directory `{}`", parent.display()))?;
    }
    #[cfg(not(unix))]
    let _ = p;
    Ok(())
}

pub(super) fn write_verified_copy_or_link(
    src_p: &Path,
    target_p: &Path,
    try_rename: bool,
    try_hard_link: bool,
) -> Result<(blake3::Hash, u64)> {
    let src_bytes =
        fs::read(src_p).with_context(|| format!("Failed to read `{}`", src_p.display()))?;
    let expected_len = src_bytes.len() as u64;
    let expected_hash = blake3::hash(&src_bytes);
    if fs::symlink_metadata(target_p).is_ok() {
        fs::remove_file(target_p).with_context(|| {
            format!(
                "Failed to remove pre-existing staging/backup file `{}`",
                target_p.display()
            )
        })?;
    }
    let linked_or_renamed = (try_rename && fs::rename(src_p, target_p).is_ok())
        || (try_hard_link && fs::hard_link(src_p, target_p).is_ok());
    if !linked_or_renamed {
        use std::io::Write;
        let mut f = create_fresh_file(target_p)
            .with_context(|| format!("Failed to create `{}`", target_p.display()))?;
        f.write_all(&src_bytes)
            .with_context(|| format!("Failed to write `{}`", target_p.display()))?;
        f.sync_all()
            .with_context(|| format!("Failed to fsync `{}`", target_p.display()))?;
    }
    let sym = fs::symlink_metadata(target_p)
        .with_context(|| format!("Failed to stat `{}`", target_p.display()))?;
    if sym.file_type().is_symlink() || !sym.file_type().is_file() || sym.len() != expected_len {
        anyhow::bail!(
            "Verified file check failed for `{}` (len={}, expected={})",
            target_p.display(),
            sym.len(),
            expected_len
        );
    }
    let written_bytes = fs::read(target_p).with_context(|| {
        format!(
            "Failed to re-read `{}` for verification",
            target_p.display()
        )
    })?;
    if blake3::hash(&written_bytes) != expected_hash {
        anyhow::bail!("Verified file BLAKE3 mismatch for `{}`", target_p.display());
    }
    sync_parent_dir(target_p)?;
    Ok((expected_hash, expected_len))
}

pub(super) fn rollback_publish_state(
    node: &ModuleNode,
    had_valid_pre_publish_set: bool,
    staged_renames: &[(PathBuf, PathBuf)],
    backups: &[BackupRecord],
) -> Result<()> {
    let mut errs: Vec<String> = Vec::new();
    for (stage_p, _) in staged_renames {
        match fs::symlink_metadata(stage_p) {
            Ok(_) => {
                if let Err(e) = fs::remove_file(stage_p) {
                    errs.push(format!(
                        "failed to remove staged file `{}`: {}",
                        stage_p.display(),
                        e
                    ));
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => {
                errs.push(format!(
                    "failed to stat staged file `{}`: {}",
                    stage_p.display(),
                    e
                ));
            }
        }
    }
    for rec in backups {
        match &rec.backup_file {
            Some((backup_p, expected_hash, expected_len)) => {
                let restore_res: Result<()> = (|| {
                    if fs::rename(backup_p, &rec.dst_path).is_err() {
                        write_verified_copy_or_link(backup_p, &rec.dst_path, false, false)?;
                        fs::remove_file(backup_p).with_context(|| {
                            format!(
                                "Failed to remove backup file `{}` after copy restore",
                                backup_p.display()
                            )
                        })?;
                    }
                    let sym = fs::symlink_metadata(&rec.dst_path)?;
                    if sym.file_type().is_symlink()
                        || !sym.file_type().is_file()
                        || sym.len() != *expected_len
                    {
                        anyhow::bail!(
                            "restored artifact `{}` failed size/type check",
                            rec.dst_path.display()
                        );
                    }
                    let restored_bytes = fs::read(&rec.dst_path)?;
                    if blake3::hash(&restored_bytes) != *expected_hash {
                        anyhow::bail!(
                            "restored artifact `{}` failed BLAKE3 verification",
                            rec.dst_path.display()
                        );
                    }
                    sync_parent_dir(&rec.dst_path)?;
                    Ok(())
                })();
                if let Err(e) = restore_res {
                    errs.push(format!(
                        "failed to restore `{}` from `{}`: {}",
                        rec.dst_path.display(),
                        backup_p.display(),
                        e
                    ));
                }
            }
            None => match fs::symlink_metadata(&rec.dst_path) {
                Ok(sym) if sym.file_type().is_file() || sym.file_type().is_symlink() => {
                    if let Err(e) = fs::remove_file(&rec.dst_path) {
                        errs.push(format!(
                            "failed to remove newly placed destination `{}` during rollback: {}",
                            rec.dst_path.display(),
                            e
                        ));
                    }
                }
                Ok(_) => {}
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                Err(e) => {
                    errs.push(format!(
                        "failed to stat destination `{}` during rollback: {}",
                        rec.dst_path.display(),
                        e
                    ));
                }
            },
        }
    }
    if errs.is_empty()
        && had_valid_pre_publish_set
        && !validate_materialized_module_artifacts(node, false)
    {
        errs.push(format!(
            "post-rollback artifact set validation failed for module `{}`",
            node.module_name
        ));
    }
    if !errs.is_empty() {
        wipe_existing_module_artifacts(node);
        anyhow::bail!(
            "publication state potentially inconsistent for module `{}` (unverified rollback errors: {})",
            node.module_name,
            errs.join("; ")
        );
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn publish_module_artifacts_atomic(
    tmp_dir: &Path,
    node: &ModuleNode,
    tmp_olean: &Path,
    tmp_ilean: &Path,
    tmp_srv: &Path,
    tmp_priv: &Path,
    tmp_ir: &Path,
    tmp_ir_sig: &Path,
    tmp_c: &Path,
) -> Result<()> {
    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock
        .lock()
        .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
    let _flock_guard = acquire_publish_flock(&node.pkg_root, false)?;
    let had_valid_pre_publish_set = validate_materialized_module_artifacts(node, false);
    let dst_srv = PathBuf::from(format!("{}.server", node.olean_path.display()));
    let dst_priv = PathBuf::from(format!("{}.private", node.olean_path.display()));
    let dst_ir = node.olean_path.with_extension("ir");
    let dst_ir_sig = PathBuf::from(format!("{}.sig", dst_ir.display()));
    let dst_ltar = node.c_path.with_extension("ltar");
    let dst_bc = node.c_path.with_extension("bc");
    let dst_ltar_hash = PathBuf::from(format!("{}.hash", dst_ltar.display()));
    let dst_bc_hash = PathBuf::from(format!("{}.hash", dst_bc.display()));
    let tmp_ltar = tmp_c.with_extension("ltar");
    let tmp_bc = tmp_c.with_extension("bc");
    let tmp_ltar_hash = PathBuf::from(format!("{}.hash", tmp_ltar.display()));
    let tmp_bc_hash = PathBuf::from(format!("{}.hash", tmp_bc.display()));
    let pairs: [(&Path, &Path, bool); 11] = [
        (tmp_olean, &node.olean_path, true),
        (tmp_ilean, &node.ilean_path, true),
        (tmp_srv, &dst_srv, node.is_module),
        (tmp_priv, &dst_priv, node.is_module),
        (tmp_ir, &dst_ir, node.is_module),
        (
            tmp_ir_sig,
            &dst_ir_sig,
            node.is_module && olean_requires_ir_sig(tmp_olean),
        ),
        (tmp_c, &node.c_path, node.needs_c),
        (&tmp_ltar, &dst_ltar, false),
        (&tmp_ltar_hash, &dst_ltar_hash, false),
        (&tmp_bc, &dst_bc, false),
        (&tmp_bc_hash, &dst_bc_hash, false),
    ];
    let pid = std::process::id();
    let seq = crate::pack::next_tmp_id();
    let mut staged_renames: Vec<(PathBuf, PathBuf)> = Vec::new();
    let mut backups: Vec<BackupRecord> = Vec::new();
    let mut stale_to_remove: Vec<PathBuf> = Vec::new();

    // Phase 1: Stage & verify all produced files into sibling `.turbo_stage_*` files in destination directories,
    // and back up ALL pre-existing regular destination files (both kept and stale-to-remove) into verified
    // `.turbo_backup_*` files (with `sync_all`, size, and BLAKE3 verification) for transactional rollback.
    let stage_res: Result<()> = (|| {
        for (src_p, dst_p, should_keep) in pairs {
            let dst_parent = dst_p.parent().ok_or_else(|| {
                anyhow::anyhow!("Destination artifact `{}` has no parent", dst_p.display())
            })?;
            fs::create_dir_all(dst_parent)?;
            let fname = dst_p
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or("artifact");
            let backup_file = match fs::symlink_metadata(dst_p) {
                Ok(dst_sym)
                    if !dst_sym.file_type().is_symlink() && dst_sym.file_type().is_file() =>
                {
                    let backup_p =
                        dst_parent.join(format!(".turbo_backup_{}_{}_{}", pid, seq, fname));
                    let (b_hash, b_len) =
                        write_verified_copy_or_link(dst_p, &backup_p, false, true)?;
                    Some((backup_p, b_hash, b_len))
                }
                Ok(dst_sym) if dst_sym.file_type().is_symlink() => {
                    anyhow::bail!(
                        "Refusing to overwrite symlinked destination artifact `{}`",
                        dst_p.display()
                    );
                }
                Ok(_) => None,
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
                Err(e) => return Err(e.into()),
            };
            backups.push(BackupRecord {
                dst_path: dst_p.to_path_buf(),
                backup_file,
            });
            if !should_keep {
                stale_to_remove.push(dst_p.to_path_buf());
                continue;
            }
            match fs::symlink_metadata(src_p) {
                Ok(sym) => {
                    if sym.file_type().is_symlink() || !src_p.starts_with(tmp_dir) {
                        anyhow::bail!(
                            "Refusing to publish symlink or out-of-sandbox artifact `{}`",
                            src_p.display()
                        );
                    }
                    if !sym.file_type().is_file() || sym.len() == 0 {
                        anyhow::bail!(
                            "Refusing to publish non-regular or empty artifact `{}`",
                            src_p.display()
                        );
                    }
                    let stage_p =
                        dst_parent.join(format!(".turbo_stage_{}_{}_{}", pid, seq, fname));
                    let _ = write_verified_copy_or_link(src_p, &stage_p, true, false)?;
                    staged_renames.push((stage_p, dst_p.to_path_buf()));
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                    stale_to_remove.push(dst_p.to_path_buf());
                }
                Err(e) => return Err(e.into()),
            }
        }
        Ok(())
    })();

    if let Err(e) = stage_res {
        for (stage_p, _) in &staged_renames {
            let _ = fs::remove_file(stage_p);
        }
        for rec in &backups {
            if let Some((ref backup_p, _, _)) = rec.backup_file {
                let _ = fs::remove_file(backup_p);
            }
        }
        return Err(e);
    }

    let fmt_rb = |staged_renames: &[(PathBuf, PathBuf)], backups: &[BackupRecord]| -> String {
        rollback_publish_state(node, had_valid_pre_publish_set, staged_renames, backups)
            .err()
            .map(|re| format!("; rollback error: {}", re))
            .unwrap_or_default()
    };

    // Phase 2a: Commit staged files via atomic in-place POSIX rename (`rename` replaces `dst_p` atomically),
    // rolling back and verifying all destinations from `backups` if any rename fails.
    for (stage_p, dst_p) in &staged_renames {
        if let Err(e) = fs::rename(stage_p, dst_p) {
            let sfx = fmt_rb(&staged_renames, &backups);
            return Err(e).with_context(|| {
                format!(
                    "Failed to atomically rename staged artifact `{}` -> `{}`{}",
                    stage_p.display(),
                    dst_p.display(),
                    sfx
                )
            });
        }
    }

    // Phase 2b: Transactionally remove any stale companion artifacts, rolling back if removal fails.
    for stale_p in &stale_to_remove {
        match fs::symlink_metadata(stale_p) {
            Ok(_) => {
                if let Err(e) = fs::remove_file(stale_p) {
                    let sfx = fmt_rb(&staged_renames, &backups);
                    return Err(e).with_context(|| {
                        format!(
                            "Failed to remove stale companion artifact `{}`{}",
                            stale_p.display(),
                            sfx
                        )
                    });
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => {
                let sfx = fmt_rb(&staged_renames, &backups);
                return Err(e).with_context(|| {
                    format!(
                        "Failed to stat stale companion artifact `{}`{}",
                        stale_p.display(),
                        sfx
                    )
                });
            }
        }
    }

    // Phase 3: Re-validate the published destination artifact set before removing backups
    if !validate_materialized_module_artifacts(node, false) {
        let sfx = fmt_rb(&staged_renames, &backups);
        anyhow::bail!(
            "Post-publish artifact set validation failed for module `{}`{}",
            node.module_name,
            sfx
        );
    }

    // Phase 4: Clean up backup files and verify their removal
    for rec in backups {
        if let Some((backup_p, _, _)) = rec.backup_file {
            if let Err(e) = fs::remove_file(&backup_p) {
                if e.kind() != std::io::ErrorKind::NotFound {
                    return Err(e).with_context(|| {
                        format!(
                            "Failed to remove temporary backup file `{}` after commit",
                            backup_p.display()
                        )
                    });
                }
            }
        }
    }
    Ok(())
}

pub(super) fn publish_staged_module_compile_output(
    node: &ModuleNode,
    staged: StagedModuleCompileOutput,
) -> Result<ModuleCompileOutput> {
    let (dur_ms, stdout_str, tmp_guard) = staged;
    let tmp_dir = &tmp_guard.0;
    let rel_slash = module_name_to_rel_slash(&node.module_name);
    let tmp_olean = tmp_dir.join(format!("{}.olean", rel_slash));
    let tmp_ilean = tmp_dir.join(format!("{}.ilean", rel_slash));
    let tmp_c = tmp_dir.join(format!("{}.c", rel_slash));
    let tmp_srv = PathBuf::from(format!("{}.server", tmp_olean.display()));
    let tmp_priv = PathBuf::from(format!("{}.private", tmp_olean.display()));
    let tmp_ir = tmp_olean.with_extension("ir");
    let tmp_ir_sig = PathBuf::from(format!("{}.sig", tmp_ir.display()));
    publish_module_artifacts_atomic(
        tmp_dir,
        node,
        &tmp_olean,
        &tmp_ilean,
        &tmp_srv,
        &tmp_priv,
        &tmp_ir,
        &tmp_ir_sig,
        &tmp_c,
    )?;
    let expected_dig = compute_olean_artifact_set_digest(&node.olean_path)?;
    Ok((dur_ms, stdout_str, expected_dig))
}

pub(super) fn normalize_lexical_path(p: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for comp in p.components() {
        match comp {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                if !out.pop() {
                    out.push(comp);
                }
            }
            _ => out.push(comp),
        }
    }
    out
}

/// Whether every cached file output of a module lands on one of `node`'s artifact paths.
pub(super) fn cas_outputs_bound_to_node(outputs: &[BlobEntry], target_root: &Path, node: &ModuleNode) -> bool {
    let expected: Vec<PathBuf> = olean_artifact_paths(&node.olean_path)
        .into_iter()
        .map(|(_, p)| {
            p.canonicalize()
                .unwrap_or_else(|_| normalize_lexical_path(&p))
        })
        .chain([node
            .c_path
            .canonicalize()
            .unwrap_or_else(|_| normalize_lexical_path(&node.c_path))])
        .collect();
    outputs
        .iter()
        .filter(|o| !o.rel_path.starts_with("thm:"))
        .all(|o| {
            let cand = target_root.join(&o.rel_path);
            let norm = cand
                .canonicalize()
                .unwrap_or_else(|_| normalize_lexical_path(&cand));
            expected.contains(&norm)
        })
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(super) fn store_module_artifacts_in_cas(
    store: &mut TurboStore,
    canon_project_dir: &Path,
    node: &ModuleNode,
    mod_action_key: &str,
    toolchain: &str,
    trust_domain: &str,
    pin_level: i64,
    dur_ms: i64,
) -> Result<Vec<BlobEntry>> {
    let base_dir = if node.pkg_root.starts_with(canon_project_dir) {
        canon_project_dir
    } else {
        &node.pkg_root
    };
    let blob_items = {
        let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
        let _guard = lock
            .lock()
            .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
        let preserve_lake = crate::lake_build::worktree_auto_link_disabled(canon_project_dir)
            || package_is_read_only(canon_project_dir, &node.pkg_root);
        let _flock_guard = acquire_publish_flock_mode(&node.pkg_root, false, preserve_lake)?;
        let artifact_files = collect_module_artifact_paths(node);
        let paths: Vec<_> = artifact_files.iter().map(|(_, p)| p.clone()).collect();
        _flock_guard.read_consistent(&paths, || {
            let mut items = Vec::with_capacity(artifact_files.len() + 1);
            for (kind, abs_path) in artifact_files {
                let bytes = fs::read(&abs_path)?;
                let hash = blake3::hash(&bytes).to_hex().to_string();
                let sz = bytes.len() as u64;
                let rel_path = abs_path
                    .strip_prefix(base_dir)
                    .unwrap_or(&abs_path)
                    .to_string_lossy()
                    .replace('\\', "/");
                items.push((hash, bytes, kind.to_string(), rel_path, sz));
            }
            let existing_log = read_existing_trace_log(node);
            if !existing_log.is_empty() {
                let bytes = serde_json::to_vec(&existing_log)?;
                let hash = blake3::hash(&bytes).to_hex().to_string();
                let sz = bytes.len() as u64;
                items.push((
                    hash,
                    bytes,
                    "trace_log".to_string(),
                    "thm:trace_log".to_string(),
                    sz,
                ));
            }
            Ok(items)
        })?
    };
    match store.acquire_singleflight(mod_action_key, toolchain, "module_unit", trust_domain)? {
        SingleflightOutcome::Leader(lease) => {
            let _pub_guard = crate::db::acquire_cas_publication_guard(&store.root)?;
            let entries =
                store.batch_store_immutable_blobs(&blob_items, trust_domain, pin_level)?;
            if let Err(e) = store.publish_action(&lease, &entries, dur_ms, 0, 0, trust_domain) {
                store.remove_singleflight_done(&lease.action_key);
                drop(lease);
                return Err(e);
            }
            Ok(entries)
        }
        SingleflightOutcome::CacheHit { outputs, .. } => Ok(outputs),
    }
}

/// Orchestrate native Lean module compilation across the resolved DAG without invoking `lake build`.
/// Uses per-module CAS (`module_unit`), bounded worker parallelism (`jobs`), temporary output
/// directories, and atomic publication.
#[cfg(test)]
#[derive(Debug, Clone)]
pub(crate) struct NativeSchedulerTestEvent {
    pub kind: String,
    pub modules: Vec<String>,
    pub at_ns: u64,
}

#[cfg(test)]
pub(super) type NativeSchedulerTestHook = dyn Fn(&str, &[String]) + Send + Sync;

#[cfg(test)]
pub(super) static TEST_NATIVE_SCHEDULER_EVENTS: OnceLock<Mutex<Option<Vec<NativeSchedulerTestEvent>>>> =
    OnceLock::new();

#[cfg(test)]
pub(super) static TEST_NATIVE_SCHEDULER_HOOK: OnceLock<
    Mutex<Option<std::sync::Arc<NativeSchedulerTestHook>>>,
> = OnceLock::new();

#[cfg(test)]
pub(super) static TEST_NATIVE_SCHEDULER_EPOCH: OnceLock<Instant> = OnceLock::new();

pub(super) fn record_scheduler_test_event(kind: &str, modules: &[String]) {
    #[cfg(test)]
    {
        let hook_opt = TEST_NATIVE_SCHEDULER_HOOK
            .get()
            .and_then(|l| l.lock().ok().and_then(|g| g.clone()));
        if let Some(hook) = hook_opt {
            hook(kind, modules);
        }
        let epoch = *TEST_NATIVE_SCHEDULER_EPOCH.get_or_init(Instant::now);
        let at_ns = epoch.elapsed().as_nanos() as u64;
        if let Some(lock) = TEST_NATIVE_SCHEDULER_EVENTS.get() {
            if let Ok(mut guard) = lock.lock() {
                if let Some(ref mut vec) = *guard {
                    vec.push(NativeSchedulerTestEvent {
                        kind: kind.to_string(),
                        modules: modules.to_vec(),
                        at_ns,
                    });
                }
            }
        }
    }
    #[cfg(not(test))]
    {
        let _ = (kind, modules);
    }
}

pub(super) fn compute_dag_schedule_edges(
    nodes: &BTreeMap<String, ModuleNode>,
    shared_libs: &[SharedLibSpec],
) -> (BTreeMap<String, usize>, BTreeMap<String, Vec<String>>) {
    let mut shared_local_map: HashMap<(PathBuf, String), Vec<String>> = HashMap::new();
    for s in shared_libs {
        shared_local_map.insert(
            (s.pkg_root.clone(), s.lib_name.clone()),
            s.local_modules.clone(),
        );
    }
    let mut in_degree: BTreeMap<String, usize> = BTreeMap::new();
    let mut dependents: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (m, node) in nodes {
        let deg = node
            .direct_dag_deps
            .iter()
            .filter(|d| nodes.contains_key(*d))
            .count();
        in_degree.insert(m.clone(), deg);
        for d in &node.direct_dag_deps {
            if nodes.contains_key(d) {
                dependents.entry(d.clone()).or_default().push(m.clone());
            }
        }
    }
    for list in dependents.values_mut() {
        list.sort();
        list.dedup();
    }
    if !shared_local_map.is_empty() {
        for m in nodes.keys().cloned().collect::<Vec<_>>() {
            let Some(node) = nodes.get(&m) else {
                continue;
            };
            let node_in_shared = shared_libs
                .iter()
                .any(|s| s.local_modules.iter().any(|lm| lm == &m));
            let mut visited_t: HashSet<String> = HashSet::new();
            let mut stack_t: Vec<String> = node.direct_dag_deps.clone();
            while let Some(dep_mod) = stack_t.pop() {
                if !visited_t.insert(dep_mod.clone()) {
                    continue;
                }
                let Some(dn) = nodes.get(&dep_mod) else {
                    continue;
                };
                stack_t.extend(dn.direct_dag_deps.iter().cloned());
                if !node.is_exe_target && !dn.is_exe_target && dn.target_name == node.target_name {
                    continue;
                }
                let is_direct_dep = node.direct_dag_deps.iter().any(|d| d == &dep_mod);
                if !(node.precompile_modules
                    || dn.precompile_modules
                    || node_in_shared
                    || (node.needs_dynlib && is_direct_dep))
                    || dn.is_exe_target
                {
                    continue;
                }
                let Some(locals) =
                    shared_local_map.get(&(dn.pkg_root.clone(), dn.target_name.clone()))
                else {
                    continue;
                };
                for local in locals {
                    if local == &m || !nodes.contains_key(local) {
                        continue;
                    }
                    let already = dependents
                        .get(local)
                        .is_some_and(|list| list.iter().any(|c| c == &m));
                    if !already {
                        *in_degree.entry(m.clone()).or_insert(0) += 1;
                        dependents.entry(local.clone()).or_default().push(m.clone());
                    }
                }
            }
        }
        for list in dependents.values_mut() {
            list.sort();
            list.dedup();
        }
    }
    (in_degree, dependents)
}

pub(super) type ModuleDepAndDynlibDigests = (Vec<(String, String)>, Vec<PathBuf>, Vec<(String, String)>);

pub(super) fn resolve_dep_module_visibility_spec(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    node: &ModuleNode,
    mod_name: &str,
) -> (bool, Option<Vec<ParsedImport>>) {
    if let Some(dn) = dag.nodes.get(mod_name) {
        return (dn.is_module, Some(dn.import_specs.clone()));
    }
    let src_opt = resolve_importable_module_in_package(&cfg.root_pkg, true, mod_name)
        .or_else(|| {
            cfg.dep_pkgs
                .iter()
                .find_map(|dp| resolve_importable_module_in_package(dp, false, mod_name))
        })
        .map(|sp| sp.src_path);
    if let Some(sp) = src_opt.filter(|p| p.is_file()) {
        if let Ok(raw) = fs::read_to_string(&sp) {
            let hdr = parse_header_info(&raw);
            return (hdr.is_module, Some(hdr.import_specs));
        }
    }
    let olean_opt = node
        .external_olean_deps
        .iter()
        .find(|(em, _)| em == mod_name)
        .map(|(_, p)| p.clone())
        .or_else(|| {
            resolve_importable_module_in_package(&cfg.root_pkg, true, mod_name)
                .or_else(|| {
                    cfg.dep_pkgs
                        .iter()
                        .find_map(|dp| resolve_importable_module_in_package(dp, false, mod_name))
                })
                .map(|sp| {
                    sp.build_lib_lean_dir
                        .join(format!("{}.olean", module_name_to_rel_slash(mod_name)))
                })
        });
    if let Some((specs, is_mod)) = olean_opt
        .as_ref()
        .and_then(|op| fs::read(op).ok())
        .and_then(|bytes| parse_olean_binary_imports(&bytes))
    {
        return (is_mod, Some(specs));
    }
    if !cfg.toolchain_lib_lean.as_os_str().is_empty() {
        let toolchain_olean = cfg
            .toolchain_lib_lean
            .join(format!("{}.olean", module_name_to_rel_slash(mod_name)));
        if toolchain_olean.is_file() {
            let tc_is_mod =
                PathBuf::from(format!("{}.server", toolchain_olean.display())).is_file();
            return (tc_is_mod, Some(Vec::new()));
        }
    }
    let is_mod = olean_opt
        .as_ref()
        .is_some_and(|op| PathBuf::from(format!("{}.server", op.display())).is_file());
    (is_mod, None)
}

pub(crate) fn compute_node_dep_visibility_map(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    node: &ModuleNode,
) -> (HashMap<String, DepImportVisibility>, HashMap<String, bool>) {
    let mut vis_map: HashMap<String, DepImportVisibility> = HashMap::new();
    let mut is_mod_map: HashMap<String, bool> = HashMap::new();
    let mut specs_cache: HashMap<String, (bool, Option<Vec<ParsedImport>>)> = HashMap::new();
    let mut get_info = |m: &str| -> (bool, Option<Vec<ParsedImport>>) {
        if let Some(cached) = specs_cache.get(m) {
            return cached.clone();
        }
        let info = resolve_dep_module_visibility_spec(cfg, dag, node, m);
        specs_cache.insert(m.to_string(), info.clone());
        info
    };

    if !node.is_module {
        for dep in &node.expected_all_deps {
            let (is_mod, _) = get_info(dep);
            is_mod_map.insert(dep.clone(), is_mod);
            vis_map.insert(dep.clone(), DepImportVisibility::All);
        }
        return (vis_map, is_mod_map);
    }

    let mut raise_vis = |m: &str, v: DepImportVisibility| -> bool {
        let prev = vis_map.get(m).copied();
        if prev.is_none_or(|p| v > p) {
            vis_map.insert(m.to_string(), v);
            true
        } else {
            false
        }
    };

    // Walk stack carries `(module, import_all, needs_meta)`, matching `build_setup_json`.
    let mut walk_stack: Vec<(String, bool, bool)> = Vec::new();
    for imp in &node.import_specs {
        if imp.module == node.module_name {
            continue;
        }
        let (is_mod, _) = get_info(&imp.module);
        is_mod_map.insert(imp.module.clone(), is_mod);
        let direct_vis = if !is_mod || imp.import_all {
            DepImportVisibility::All
        } else if imp.is_meta {
            DepImportVisibility::MetaExport
        } else {
            DepImportVisibility::PublicExport
        };
        raise_vis(&imp.module, direct_vis);
    }
    for imp in node.import_specs.iter().rev() {
        if imp.module == node.module_name {
            continue;
        }
        let (imp_is_mod, sub_specs_opt) = get_info(&imp.module);
        let Some(sub_specs) = sub_specs_opt else {
            // Fail closed: if transitive specs cannot be resolved, mark all remaining deps `All`.
            for dep in &node.expected_all_deps {
                let (dm, _) = get_info(dep);
                is_mod_map.insert(dep.clone(), dm);
                vis_map.insert(dep.clone(), DepImportVisibility::All);
            }
            return (vis_map, is_mod_map);
        };
        let imp_all = !imp_is_mod || imp.import_all;
        for sub in sub_specs.iter().rev() {
            if sub.module == imp.module {
                continue;
            }
            let reachable = imp_all || sub.is_exported;
            let c_all = imp_all && sub.import_all;
            let c_meta = imp.is_meta || (reachable && sub.is_meta);
            if reachable || c_meta {
                walk_stack.push((sub.module.clone(), c_all, c_meta));
            }
        }
    }

    while let Some((cur, import_all, needs_meta)) = walk_stack.pop() {
        let (is_mod, sub_specs_opt) = get_info(&cur);
        is_mod_map.insert(cur.clone(), is_mod);
        let eff_all = !is_mod || import_all;
        let target_vis = if eff_all {
            DepImportVisibility::All
        } else if needs_meta {
            DepImportVisibility::MetaExport
        } else {
            DepImportVisibility::PublicExport
        };
        if !raise_vis(&cur, target_vis) {
            continue;
        }
        let Some(sub_specs) = sub_specs_opt else {
            for dep in &node.expected_all_deps {
                let (dm, _) = get_info(dep);
                is_mod_map.insert(dep.clone(), dm);
                vis_map.insert(dep.clone(), DepImportVisibility::All);
            }
            return (vis_map, is_mod_map);
        };
        for sub in sub_specs.iter().rev() {
            if sub.module == cur {
                continue;
            }
            let reachable = eff_all || sub.is_exported;
            let child_import_all = eff_all && sub.import_all;
            let child_needs_meta = needs_meta || (reachable && sub.is_meta);
            if reachable || child_needs_meta {
                walk_stack.push((sub.module.clone(), child_import_all, child_needs_meta));
            }
        }
    }

    for dep in &node.expected_all_deps {
        let (is_mod, _) = get_info(dep);
        is_mod_map.entry(dep.clone()).or_insert(is_mod);
        vis_map
            .entry(dep.clone())
            .or_insert(DepImportVisibility::PublicExport);
    }
    (vis_map, is_mod_map)
}

pub(super) fn gather_module_dep_digests_and_dynlibs(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    node: &ModuleNode,
    tier_digests: &HashMap<String, ModuleArtifactTierDigests>,
) -> Result<ModuleDepAndDynlibDigests> {
    let (vis_map, is_mod_map) = compute_node_dep_visibility_map(cfg, dag, node);
    let select_dig = |m: &str, tiers: &ModuleArtifactTierDigests| -> String {
        let vis = vis_map.get(m).copied().unwrap_or(DepImportVisibility::All);
        let dep_is_mod = is_mod_map.get(m).copied().unwrap_or(false);
        tiers.for_visibility(vis, node.is_module && dep_is_mod)
    };
    let mut dep_digests_map: BTreeMap<String, String> = BTreeMap::new();
    let mut dep_work: VecDeque<&str> = VecDeque::new();
    for d in &node.direct_dag_deps {
        dep_work.push_back(d);
    }
    for (ext_m, _) in &node.external_olean_deps {
        if let Some(tiers) = tier_digests.get(ext_m) {
            dep_digests_map.insert(ext_m.clone(), select_dig(ext_m, tiers));
        }
    }
    while let Some(cur_dep) = dep_work.pop_front() {
        if dep_digests_map.contains_key(cur_dep) {
            continue;
        }
        let tiers = tier_digests.get(cur_dep).ok_or_else(|| {
            anyhow::anyhow!(
                "Internal DAG error: dependency `{}` of `{}` missing olean digest",
                cur_dep,
                node.module_name
            )
        })?;
        dep_digests_map.insert(cur_dep.to_string(), select_dig(cur_dep, tiers));
        if let Some(dep_node) = dag.nodes.get(cur_dep) {
            for sub_d in &dep_node.direct_dag_deps {
                if !dep_digests_map.contains_key(sub_d) {
                    dep_work.push_back(sub_d);
                }
            }
            for (ext_m, _) in &dep_node.external_olean_deps {
                if let Some(etiers) = tier_digests.get(ext_m) {
                    dep_digests_map
                        .entry(ext_m.clone())
                        .or_insert_with(|| select_dig(ext_m, etiers));
                }
            }
        }
    }
    let dep_digests_vec: Vec<(String, String)> = dep_digests_map.into_iter().collect();
    let raw_imp_dynlibs = compute_module_raw_import_dynlibs(dag, node);
    let mut dynlib_digests: Vec<(String, String)> = Vec::with_capacity(raw_imp_dynlibs.len());
    for dp in &raw_imp_dynlibs {
        let bytes = fs::read(dp).with_context(|| {
            format!(
                "Failed to read imported precompiled shared library `{}` for `{}`",
                dp.display(),
                node.module_name
            )
        })?;
        let tag = dp
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("dynlib")
            .to_string();
        dynlib_digests.push((tag, blake3::hash(&bytes).to_hex().to_string()));
    }
    Ok((dep_digests_vec, raw_imp_dynlibs, dynlib_digests))
}

pub(super) fn try_compute_initial_module_action_keys(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    node: &ModuleNode,
    preserve_project: bool,
    ext_tier_digests: &HashMap<String, ModuleArtifactTierDigests>,
    memo_on_disk_digests: &mut HashMap<String, Option<ModuleArtifactTierDigests>>,
) -> Option<(String, Option<String>)> {
    let (vis_map, is_mod_map) = compute_node_dep_visibility_map(cfg, dag, node);
    let select_dig = |m: &str, tiers: &ModuleArtifactTierDigests| -> String {
        let vis = vis_map.get(m).copied().unwrap_or(DepImportVisibility::All);
        let dep_is_mod = is_mod_map.get(m).copied().unwrap_or(false);
        tiers.for_visibility(vis, node.is_module && dep_is_mod)
    };
    let mut dep_digests_map: BTreeMap<String, String> = BTreeMap::new();
    let mut dep_work: VecDeque<&str> = VecDeque::new();
    for d in &node.direct_dag_deps {
        dep_work.push_back(d);
    }
    for (ext_m, _) in &node.external_olean_deps {
        let tiers = ext_tier_digests.get(ext_m)?;
        dep_digests_map.insert(ext_m.clone(), select_dig(ext_m, tiers));
    }
    while let Some(cur_dep) = dep_work.pop_front() {
        if dep_digests_map.contains_key(cur_dep) {
            continue;
        }
        let dep_node = dag.nodes.get(cur_dep)?;
        let tiers_opt = if let Some(cached) = memo_on_disk_digests.get(cur_dep) {
            cached.clone()
        } else {
            let preserve_dep = preserve_project
                || package_is_read_only(&cfg.root_pkg.pkg_root, &dep_node.pkg_root);
            let computed = if validate_materialized_module_artifacts(dep_node, preserve_dep) {
                compute_module_artifact_tier_digests_with_policy(&dep_node.olean_path, preserve_dep)
                    .ok()
            } else {
                None
            };
            memo_on_disk_digests.insert(cur_dep.to_string(), computed.clone());
            computed
        };
        let tiers = tiers_opt?;
        dep_digests_map.insert(cur_dep.to_string(), select_dig(cur_dep, &tiers));
        for sub_d in &dep_node.direct_dag_deps {
            if !dep_digests_map.contains_key(sub_d) {
                dep_work.push_back(sub_d);
            }
        }
        for (ext_m, _) in &dep_node.external_olean_deps {
            let etiers = ext_tier_digests.get(ext_m)?;
            dep_digests_map
                .entry(ext_m.clone())
                .or_insert_with(|| select_dig(ext_m, etiers));
        }
    }
    let dep_digests_vec: Vec<(String, String)> = dep_digests_map.into_iter().collect();
    let raw_imp_dynlibs = compute_module_raw_import_dynlibs(dag, node);
    let mut dynlib_digests: Vec<(String, String)> = Vec::with_capacity(raw_imp_dynlibs.len());
    for dp in &raw_imp_dynlibs {
        let bytes = fs::read(dp).ok()?;
        let tag = dp
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("dynlib")
            .to_string();
        dynlib_digests.push((tag, blake3::hash(&bytes).to_hex().to_string()));
    }
    let mod_key = compute_module_cas_key_with_dynlibs(
        cfg,
        node,
        &dep_digests_vec,
        node.needs_c,
        &dynlib_digests,
    )
    .ok()?;
    let fallback_c_key = if !node.needs_c {
        compute_module_cas_key_with_dynlibs(cfg, node, &dep_digests_vec, true, &dynlib_digests).ok()
    } else {
        None
    };
    Some((mod_key, fallback_c_key))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn compute_module_b_levels(
    store: &TurboStore,
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    tainted_elab_host_effect_mods: &HashSet<String>,
    dependents: &BTreeMap<String, Vec<String>>,
    trust_domain: &str,
    preserve_project: bool,
    ext_tier_digests: &HashMap<String, ModuleArtifactTierDigests>,
) -> HashMap<String, u64> {
    let mut memo_on_disk_digests: HashMap<String, Option<ModuleArtifactTierDigests>> =
        HashMap::new();
    let mut weights: HashMap<String, u64> = HashMap::with_capacity(dag.nodes.len());
    for (mod_name, node) in &dag.nodes {
        let mut cached_dur: Option<u64> = None;
        if !tainted_elab_host_effect_mods.contains(mod_name) {
            if let Some((mod_key, fallback_c_key)) = try_compute_initial_module_action_keys(
                cfg,
                dag,
                node,
                preserve_project,
                ext_tier_digests,
                &mut memo_on_disk_digests,
            ) {
                cached_dur = store.get_cached_action_duration_ms(&mod_key, trust_domain);
                if cached_dur.is_none() {
                    if let Some(ref c_key) = fallback_c_key {
                        cached_dur = store.get_cached_action_duration_ms(c_key, trust_domain);
                    }
                }
            }
        }
        let weight = cached_dur.unwrap_or_else(|| {
            fs::metadata(&node.src_path)
                .map(|m| m.len().max(1))
                .unwrap_or(1)
        });
        weights.insert(mod_name.clone(), weight.max(1));
    }
    let mut b_levels: HashMap<String, u64> = HashMap::with_capacity(dag.nodes.len());
    for mod_name in dag.topological_order.iter().rev() {
        let w = weights.get(mod_name).copied().unwrap_or(1);
        let max_dep = dependents
            .get(mod_name)
            .map(|deps| {
                deps.iter()
                    .filter_map(|v| b_levels.get(v).copied())
                    .max()
                    .unwrap_or(0)
            })
            .unwrap_or(0);
        b_levels.insert(mod_name.clone(), w.saturating_add(max_dep));
    }
    b_levels
}

pub(super) type StagedCasBlobItems = Vec<(String, Vec<u8>, String, String, u64)>;

pub(super) fn read_consistent_module_cas_blobs_locked(
    canon_project_dir: &Path,
    node: &ModuleNode,
) -> Result<StagedCasBlobItems> {
    let base_dir = if node.pkg_root.starts_with(canon_project_dir) {
        canon_project_dir
    } else {
        &node.pkg_root
    };
    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock
        .lock()
        .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
    let preserve_lake = crate::lake_build::worktree_auto_link_disabled(canon_project_dir)
        || package_is_read_only(canon_project_dir, &node.pkg_root);
    let _flock_guard = acquire_publish_flock_mode(&node.pkg_root, false, preserve_lake)?;
    let artifact_files = collect_module_artifact_paths(node);
    let paths: Vec<_> = artifact_files.iter().map(|(_, p)| p.clone()).collect();
    _flock_guard.read_consistent(&paths, || {
        let mut items = Vec::with_capacity(artifact_files.len());
        for (kind, abs_path) in artifact_files {
            let bytes = fs::read(&abs_path)?;
            let sz = bytes.len() as u64;
            let rel_path = abs_path
                .strip_prefix(base_dir)
                .unwrap_or(&abs_path)
                .to_string_lossy()
                .replace('\\', "/");
            items.push((String::new(), bytes, kind.to_string(), rel_path, sz));
        }
        Ok(items)
    })
}

pub(super) fn commit_staged_module_cas_entry(
    store: &mut TurboStore,
    mod_action_key: &str,
    toolchain: &str,
    trust_domain: &str,
    pin_level: i64,
    dur_ms: i64,
    blob_items: StagedCasBlobItems,
) -> Result<Vec<BlobEntry>> {
    match store.acquire_singleflight(mod_action_key, toolchain, "module_unit", trust_domain)? {
        SingleflightOutcome::Leader(lease) => {
            let _pub_guard = crate::db::acquire_cas_publication_guard(&store.root)?;
            let entries =
                store.batch_store_immutable_blobs(&blob_items, trust_domain, pin_level)?;
            if let Err(e) = store.publish_action(&lease, &entries, dur_ms, 0, 0, trust_domain) {
                store.remove_singleflight_done(&lease.action_key);
                drop(lease);
                return Err(e);
            }
            Ok(entries)
        }
        SingleflightOutcome::CacheHit { outputs, .. } => Ok(outputs),
    }
}

#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct HydrateTracesReport {
    pub packages_scanned: usize,
    pub packages_updated: usize,
    pub modules_scanned: usize,
    pub modules_verified: usize,
    pub entries_written: usize,
    pub modules_stale_or_unverified: usize,
    pub elapsed_ms: u128,
}

pub(super) fn discover_all_package_module_specs(
    pkg: &PackageConfig,
    is_root_pkg: bool,
) -> Vec<DiscoveredModuleSpec> {
    let mut seen_mods: HashSet<String> = HashSet::new();
    let mut out: Vec<DiscoveredModuleSpec> = Vec::new();
    let pkg_src_base = pkg.pkg_root.join(&pkg.src_dir);
    for lib in &pkg.libs {
        let lib_src = match &lib.src_dir {
            Some(sd) => pkg_src_base.join(sd),
            None => pkg_src_base.clone(),
        };
        let mut globs = lib.globs.clone();
        if globs.is_empty() {
            for r in &lib.roots {
                globs.push(GlobSpec::One(r.clone()));
            }
        }
        for g in &globs {
            if let Ok(pairs) = expand_glob_in_dir(&lib_src, g, false) {
                for (mod_name, _) in pairs {
                    if seen_mods.insert(mod_name.clone()) {
                        if let Some(spec) = resolve_module_in_package(pkg, is_root_pkg, &mod_name) {
                            out.push(spec);
                        }
                    }
                }
            }
        }
    }
    for exe in &pkg.exes {
        if !exe.root.is_empty() && seen_mods.insert(exe.root.clone()) {
            if let Some(spec) = resolve_module_in_package(pkg, is_root_pkg, &exe.root) {
                out.push(spec);
            }
        }
    }
    out
}

pub fn hydrate_project_traces(project_dir: &Path) -> Result<HydrateTracesReport> {
    hydrate_project_traces_with_store(project_dir, None)
}

pub(crate) fn hydrate_project_traces_with_store(
    project_dir: &Path,
    store_opt: Option<&TurboStore>,
) -> Result<HydrateTracesReport> {
    reset_lake_inputs_tag_memo();
    let t0 = std::time::Instant::now();
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    anyhow::ensure!(
        !crate::lake_build::worktree_auto_link_disabled(&canon_dir),
        "Worktree opt-out (`[worktree] auto_link = false` or `TURBO_LEAN_NO_WORKTREE_LINK=1`) prevents writing hydrated trace manifests in {}",
        canon_dir.display()
    );
    let cfg = resolve_project_config(&canon_dir)?;
    anyhow::ensure!(
        !cfg.lean_bin.as_os_str().is_empty() && cfg.lean_githash != "lean-not-installed",
        "Cannot hydrate verified traces in {} without an installed Lean toolchain (`{}`)",
        canon_dir.display(),
        cfg.toolchain
    );
    enforce_project_olean_githash_gate(
        &canon_dir,
        &cfg.toolchain,
        &cfg.lean_bin,
        &cfg.lean_githash,
        &[],
    )?;
    let expected_lake_inputs = workspace_lake_inputs_digest(&cfg)?;
    let allowed_axioms = crate::splitter::allowed_axioms();
    let kernel_policy_digest = crate::splitter::current_kernel_policy_digest();

    let mut report = HydrateTracesReport::default();
    let mut scanned_pkgs: Vec<&PackageConfig> = Vec::new();
    let mut pkg_specs: Vec<(&PackageConfig, bool, Vec<DiscoveredModuleSpec>)> = Vec::new();
    for (is_root, pkg) in
        std::iter::once((true, &cfg.root_pkg)).chain(cfg.dep_pkgs.iter().map(|dp| (false, dp)))
    {
        if package_is_read_only(&canon_dir, &pkg.pkg_root) {
            continue;
        }
        report.packages_scanned += 1;
        scanned_pkgs.push(pkg);
        let assurance = if is_root {
            discover_trusted_assurance_surface(&pkg.pkg_root, pkg, &allowed_axioms)
        } else {
            TrustedAssuranceSurface::default()
        };
        let specs = discover_all_package_module_specs(pkg, is_root);
        let built_specs: Vec<DiscoveredModuleSpec> = specs
            .into_iter()
            .filter(|s| {
                !assurance.mod_names.contains(&s.module_name) && spec_olean_path(s).is_file()
            })
            .collect();
        report.modules_scanned += built_specs.len();
        if !built_specs.is_empty() {
            pkg_specs.push((pkg, is_root, built_specs));
        }
    }

    let write_empty_manifests_with_root_inputs = |pkgs: &[&PackageConfig]| -> Result<()> {
        for pkg in pkgs {
            if package_is_read_only(&canon_dir, &pkg.pkg_root) {
                continue;
            }
            let build_dir = pkg.pkg_root.join(".lake/build");
            let manifest_path = build_dir.join(".turbo_verified_sources.json");
            if pkg.pkg_root == cfg.root_pkg.pkg_root && !expected_lake_inputs.is_empty() {
                let _ = fs::create_dir_all(&build_dir);
                let manifest = VerifiedDepManifest {
                    pkg_name: pkg.name.clone(),
                    toolchain: cfg.toolchain.clone(),
                    lean_githash: cfg.lean_githash.clone(),
                    pkg_config_digest: pkg.config_digest.clone(),
                    lake_inputs_digest: expected_lake_inputs.clone(),
                    workspace_config_digest: cfg.canonical_config_digest.clone(),
                    allowed_axioms: allowed_axioms.clone(),
                    kernel_policy_digest: kernel_policy_digest.clone(),
                    modules: BTreeMap::new(),
                    cfg: None,
                    dep_import_memo: DepImportMemo::default(),
                };
                let json_bytes = serde_json::to_vec(&manifest)?;
                let tmp_path = build_dir.join(format!(
                    ".turbo_verified_sources.{}.{}.tmp",
                    std::process::id(),
                    crate::pack::next_tmp_id()
                ));
                write_file_atomic(&tmp_path, &json_bytes)?;
                fs::rename(&tmp_path, &manifest_path)?;
            } else {
                let _ = fs::remove_file(&manifest_path);
            }
        }
        Ok(())
    };

    if pkg_specs.is_empty() {
        write_empty_manifests_with_root_inputs(&scanned_pkgs)?;
        report.elapsed_ms = t0.elapsed().as_millis();
        return Ok(report);
    }

    let mut cache = LakeClosureCache {
        ignore_mtime_skew: true,
        allow_stale_manifest_hydration: true,
        ..Default::default()
    };
    let mut verified_specs: Vec<(DiscoveredModuleSpec, PathBuf)> = Vec::new();
    for (_, _, specs) in &pkg_specs {
        for spec in specs {
            let mut visiting = HashSet::new();
            if lake_closure_export_info(&cfg, spec, false, &mut cache, &mut visiting).is_some() {
                verified_specs.push((spec.clone(), spec_olean_path(spec)));
            } else {
                report.modules_stale_or_unverified += 1;
            }
        }
    }

    if verified_specs.is_empty() {
        write_empty_manifests_with_root_inputs(&scanned_pkgs)?;
        report.elapsed_ms = t0.elapsed().as_millis();
        return Ok(report);
    }

    // Load existing package manifests to reuse stat-fingerprinted artifact digests in O(1) stat time.
    let mut existing_manifests: HashMap<PathBuf, VerifiedDepManifest> = HashMap::new();
    for (pkg, _, _) in &pkg_specs {
        let mpath = pkg
            .pkg_root
            .join(".lake/build/.turbo_verified_sources.json");
        if let Ok(bytes) = fs::read(&mpath) {
            if let Ok(m) = serde_json::from_slice::<VerifiedDepManifest>(&bytes) {
                if m.pkg_name == pkg.name
                    && m.toolchain == cfg.toolchain
                    && m.lean_githash == cfg.lean_githash
                    && m.pkg_config_digest == pkg.config_digest
                {
                    existing_manifests.insert(pkg.pkg_root.clone(), m);
                }
            }
        }
    }

    // Compute (src_blake3, imports, olean_artifact_digest, stat_fp) in parallel across verified modules.
    type ComputedMod = (
        PathBuf,
        String,
        String,
        bool,
        PathBuf,
        String,
        Vec<String>,
        String,
        String,
    );
    let n_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .min(verified_specs.len().max(1));
    let chunk_size = verified_specs.len().div_ceil(n_threads);
    let existing_ref = &existing_manifests;
    let computed_chunks: Vec<Vec<Option<ComputedMod>>> = std::thread::scope(|s| {
        let mut handles = Vec::with_capacity(n_threads);
        for chunk in verified_specs.chunks(chunk_size) {
            handles.push(s.spawn(move || {
                chunk
                    .iter()
                    .map(|(spec, olean_path)| {
                        let src_raw = fs::read_to_string(&spec.src_path).ok()?;
                        let hdr = parse_header_info(&src_raw);
                        if hdr.header_error.is_some() {
                            return None;
                        }
                        let src_b3 = blake3::hash(src_raw.as_bytes()).to_hex().to_string();
                        let rel_src = spec_rel_src(spec);
                        let trusted_fp_opt = olean_artifact_stat_fingerprint_for_store(olean_path);
                        let reused_dig = existing_ref
                            .get(&spec.pkg_root)
                            .and_then(|m| m.modules.get(&rel_src))
                            .and_then(|e| {
                                if !e.artifact_stat_fingerprint.is_empty()
                                    && trusted_fp_opt.as_deref()
                                        == Some(e.artifact_stat_fingerprint.as_str())
                                {
                                    Some(e.olean_artifact_digest.clone())
                                } else {
                                    None
                                }
                            });
                        let dig = match reused_dig {
                            Some(d) => d,
                            None => compute_olean_artifact_set_digest_with_policy(olean_path, true)
                                .ok()?,
                        };
                        let stat_fp = if spec.is_root_pkg {
                            String::new()
                        } else {
                            olean_artifact_stat_fingerprint_for_store(olean_path)
                                .filter(|s| Some(s.as_str()) == trusted_fp_opt.as_deref())
                                .unwrap_or_default()
                        };
                        Some((
                            spec.pkg_root.clone(),
                            spec.module_name.clone(),
                            rel_src,
                            spec.is_root_pkg,
                            olean_path.clone(),
                            src_b3,
                            hdr.imports,
                            dig,
                            stat_fp,
                        ))
                    })
                    .collect()
            }));
        }
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or_default())
            .collect()
    });
    let computed: Vec<Option<ComputedMod>> = computed_chunks.into_iter().flatten().collect();

    let mut mod_digests: HashMap<(PathBuf, String), String> = HashMap::new();
    let mut ready_mods: Vec<ComputedMod> = Vec::new();
    for item in computed.into_iter().flatten() {
        mod_digests.insert((item.0.clone(), item.1.clone()), item.7.clone());
        ready_mods.push(item);
    }

    let mut prebuilt_digests: HashMap<PathBuf, String> = HashMap::new();
    let mut updates_by_pkg: HashMap<PathBuf, Vec<(String, VerifiedDepModuleEntry)>> =
        HashMap::new();
    let mut replay_audit_ctx = store_opt.map(|st| {
        let (replay_lp, _) = build_lean_search_path(&cfg, false);
        let batch = ReplayLookupBatchCache::new(st, &cfg, &replay_lp);
        (st, replay_lp, batch)
    });

    for (
        pkg_root,
        mod_name,
        rel_src,
        is_root_pkg,
        olean_path,
        src_b3,
        imports,
        olean_dig,
        stat_fp,
    ) in ready_mods
    {
        let mut import_pins: BTreeMap<String, String> = BTreeMap::new();
        let mut all_pins_resolved = true;
        for imp in &imports {
            let site = match resolve_module_in_package(&cfg.root_pkg, true, imp) {
                Some(rs) => ImportSite::Module(Box::new(rs)),
                None => resolve_import_site(&cfg, imp),
            };
            match site {
                ImportSite::Toolchain => {}
                ImportSite::Module(sub_spec) => {
                    let sub_key = (sub_spec.pkg_root.clone(), sub_spec.module_name.clone());
                    let dig = if let Some(d) = mod_digests.get(&sub_key) {
                        d.clone()
                    } else if let Ok(d) = compute_olean_artifact_set_digest_with_policy(
                        &spec_olean_path(&sub_spec),
                        true,
                    ) {
                        mod_digests.insert(sub_key, d.clone());
                        d
                    } else {
                        all_pins_resolved = false;
                        break;
                    };
                    import_pins.insert(imp.clone(), dig);
                }
                ImportSite::Prebuilt(pb_path) => {
                    let dig = if let Some(d) = prebuilt_digests.get(&pb_path) {
                        d.clone()
                    } else if let Ok(d) =
                        compute_olean_artifact_set_digest_with_policy(&pb_path, true)
                    {
                        prebuilt_digests.insert(pb_path, d.clone());
                        d
                    } else {
                        all_pins_resolved = false;
                        break;
                    };
                    import_pins.insert(imp.clone(), dig);
                }
                ImportSite::Unresolved => {
                    all_pins_resolved = false;
                    break;
                }
            }
        }
        if !all_pins_resolved {
            report.modules_stale_or_unverified += 1;
            continue;
        }
        let prev_kernel_audited = existing_manifests
            .get(&pkg_root)
            .filter(|m| {
                m.allowed_axioms == allowed_axioms && m.kernel_policy_digest == kernel_policy_digest
            })
            .and_then(|m| m.modules.get(&rel_src))
            .is_some_and(|e| {
                e.kernel_audited && e.src_blake3 == src_b3 && e.olean_artifact_digest == olean_dig
            });
        let store_kernel_audited = is_root_pkg
            && !prev_kernel_audited
            && replay_audit_ctx.as_mut().is_some_and(|(st, lp, batch)| {
                batch.is_audited_in_store(st, &cfg, lp, &mod_name, &olean_path)
            });
        let entry = VerifiedDepModuleEntry {
            src_blake3: src_b3,
            olean_artifact_digest: olean_dig,
            lake_inputs_digest: expected_lake_inputs.clone(),
            // Never forge `kernel_audited = true` on root-package modules without replay:
            // preserve an existing matching `kernel_audited` bit (or a verified `TurboStore`
            // kernel audit when `store_opt` is provided); dependency packages only use
            // `.turbo_verified_sources.json` for freshness while `TurboStore` enforces replay.
            kernel_audited: if is_root_pkg {
                prev_kernel_audited || store_kernel_audited
            } else {
                false
            },
            import_olean_digests: import_pins,
            artifact_stat_fingerprint: stat_fp,
            ..Default::default()
        };
        report.modules_verified += 1;
        updates_by_pkg
            .entry(pkg_root)
            .or_default()
            .push((rel_src, entry));
    }

    for pkg in &scanned_pkgs {
        if package_is_read_only(&canon_dir, &pkg.pkg_root) {
            continue;
        }
        let build_dir = pkg.pkg_root.join(".lake/build");
        let manifest_path = build_dir.join(".turbo_verified_sources.json");
        let keep_empty_root_inputs =
            pkg.pkg_root == cfg.root_pkg.pkg_root && !expected_lake_inputs.is_empty();
        let entries = match updates_by_pkg.remove(&pkg.pkg_root) {
            Some(v) if !v.is_empty() || keep_empty_root_inputs => v,
            _ if keep_empty_root_inputs => Vec::new(),
            _ => {
                let _ = fs::remove_file(&manifest_path);
                continue;
            }
        };
        let _ = fs::create_dir_all(&build_dir);
        let mut manifest = VerifiedDepManifest {
            pkg_name: pkg.name.clone(),
            toolchain: cfg.toolchain.clone(),
            lean_githash: cfg.lean_githash.clone(),
            pkg_config_digest: pkg.config_digest.clone(),
            lake_inputs_digest: expected_lake_inputs.clone(),
            workspace_config_digest: cfg.canonical_config_digest.clone(),
            allowed_axioms: allowed_axioms.clone(),
            kernel_policy_digest: kernel_policy_digest.clone(),
            modules: BTreeMap::new(),
            cfg: None,
            dep_import_memo: DepImportMemo::default(),
        };
        for (rel_src, entry) in entries {
            manifest.modules.insert(rel_src, entry);
            report.entries_written += 1;
        }
        let json_bytes = serde_json::to_vec(&manifest)?;
        let tmp_path = build_dir.join(format!(
            ".turbo_verified_sources.json.tmp.{}.{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        {
            use std::io::Write;
            let mut f = create_fresh_file(&tmp_path)?;
            f.write_all(&json_bytes)?;
            f.sync_all()?;
        }
        fs::rename(&tmp_path, &manifest_path)?;
        report.packages_updated += 1;
    }

    report.elapsed_ms = t0.elapsed().as_millis();
    Ok(report)
}

/// Orchestrate native Lean module compilation across the resolved DAG without invoking `lake build`.
/// Uses per-module CAS (`module_unit`), bounded worker parallelism (`jobs`), temporary output
/// directories, and atomic publication.
#[allow(clippy::too_many_arguments)]
pub fn build_project_modules_native(
    store: &mut TurboStore,
    project_dir: &Path,
    targets: &[String],
    trust_domain: &str,
    pin_level: i64,
    is_untrusted: bool,
    json_output: bool,
    file_hashes_opt: Option<&BTreeMap<String, String>>,
) -> Result<NativeBuildReport> {
    build_project_modules_native_with_options(
        store,
        project_dir,
        targets,
        trust_domain,
        pin_level,
        is_untrusted,
        json_output,
        file_hashes_opt,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn build_project_modules_native_with_options(
    store: &mut TurboStore,
    project_dir: &Path,
    targets: &[String],
    trust_domain: &str,
    pin_level: i64,
    is_untrusted: bool,
    json_output: bool,
    _file_hashes_opt: Option<&BTreeMap<String, String>>,
    emit_lake_sidecars: bool,
) -> Result<NativeBuildReport> {
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let project_name = canon_dir
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "lean-project".to_string());
    let preserve_project = crate::lake_build::worktree_auto_link_disabled(&canon_dir);
    let profile_phases = std::env::var("TURBO_LEAN_PROFILE_PHASES")
        .ok()
        .is_some_and(|v| matches!(v.trim(), "1" | "true" | "yes"));
    let t_total = std::time::Instant::now();
    let t_cfg = std::time::Instant::now();
    let cfg = resolve_project_config_with_trust(&canon_dir, is_untrusted)?;
    let cfg_ms = t_cfg.elapsed().as_millis();
    let t_dag = std::time::Instant::now();
    let dag = build_module_dag_with_trust(&cfg, targets, is_untrusted)?;
    let dag_ms = t_dag.elapsed().as_millis();
    if profile_phases {
        eprintln!(
            "[turbo-lean][profile] after_dag: cfg={}ms dag={}ms dag_nodes={}",
            cfg_ms,
            dag_ms,
            dag.nodes.len()
        );
    }
    validate_build_write_dirs(&cfg, &dag, &canon_dir, is_untrusted)?;
    let mut report = NativeBuildReport {
        modules_total: dag.nodes.len(),
        modules_compiled: 0,
        modules_cached: 0,
        modules_up_to_date_reused: 0,
        waves_count: dag.waves.len(),
        config_digest: cfg.canonical_config_digest.clone(),
        compiled_modules: Vec::new(),
        cached_modules: Vec::new(),
        cone_source_paths: dag.nodes.values().map(|n| n.src_path.clone()).collect(),
        bwrap_used: false,
        staged_target_paths: Vec::new(),
    };
    if dag.nodes.is_empty() {
        return Ok(report);
    }
    // Opted-out packages must not acquire new build directories either.
    for pkg in std::iter::once(&cfg.root_pkg).chain(&cfg.dep_pkgs) {
        if !preserve_project && !package_is_read_only(&canon_dir, &pkg.pkg_root) {
            fs::create_dir_all(pkg.pkg_root.join(&pkg.build_dir).join(&pkg.lean_lib_dir))?;
            fs::create_dir_all(pkg.pkg_root.join(&pkg.build_dir).join(&pkg.native_lib_dir))?;
            fs::create_dir_all(pkg.pkg_root.join(&pkg.build_dir).join(&pkg.ir_dir))?;
        }
    }
    let (lean_path_env, ld_library_path_env) = build_lean_search_path(&cfg, is_untrusted);
    let bwrap_bin = if is_untrusted {
        probe_bwrap_sandbox(&canon_dir)
    } else {
        None
    };
    if is_untrusted {
        if bwrap_bin.is_none() {
            anyhow::bail!(
                "Untrusted module verification requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
            );
        }
        report.bwrap_used = true;
    } else {
        report.bwrap_used = bwrap_bin.is_some();
    }
    let base_jobs = std::env::var("TURBO_LEAN_JOBS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4)
        });
    let max_jobs = if is_untrusted {
        base_jobs.min(2)
    } else {
        base_jobs
    };
    // Map from module_name -> full olean artifact set digest (for freshness & post-audit checks)
    let mut olean_digests: HashMap<String, String> = HashMap::new();
    // Map from module_name -> 3-tier artifact digests (for visibility-aware Module CAS keys)
    let mut tier_digests: HashMap<String, ModuleArtifactTierDigests> = HashMap::new();
    // Pre-compute digests for external `.olean` dependencies (only populated when `!is_untrusted`)
    // and ensure every external `.olean` carries kernel-replay authority in `TurboStore` DB
    // (`.turbo_verified_sources.json` is freshness-only and never grants replay authority).
    let mut unverified_external_deps: BTreeSet<String> = dag
        .nodes
        .values()
        .flat_map(|n| n.prebuilt_olean_deps.iter().cloned())
        .collect();
    let t_ext = std::time::Instant::now();
    let mut unique_ext_paths: Vec<(String, PathBuf)> = Vec::new();
    let mut seen_ext_mods: HashSet<String> = HashSet::new();
    for node in dag.nodes.values() {
        for (ext_mod, ext_path) in &node.external_olean_deps {
            if seen_ext_mods.insert(ext_mod.clone()) {
                unique_ext_paths.push((ext_mod.clone(), ext_path.clone()));
            }
        }
    }
    if unique_ext_paths.len() >= 16 && max_jobs > 1 {
        let workers = max_jobs.min(8).min(unique_ext_paths.len());
        let next_idx = std::sync::atomic::AtomicUsize::new(0);
        let items_ref = unique_ext_paths.as_slice();
        let computed: Vec<Result<(String, ModuleArtifactTierDigests)>> = std::thread::scope(|s| {
            let handles: Vec<_> = (0..workers)
                .map(|_| {
                    let idx_ref = &next_idx;
                    let canon_ref = canon_dir.as_path();
                    s.spawn(move || {
                        let mut local = Vec::new();
                        loop {
                            let i = idx_ref.fetch_add(1, Ordering::Relaxed);
                            if i >= items_ref.len() {
                                break;
                            }
                            let (ref m, ref p) = items_ref[i];
                            local.push(
                                compute_module_artifact_tier_digests_parallel_safe(
                                    p,
                                    preserve_project || !p.starts_with(canon_ref),
                                )
                                .map(|td| (m.clone(), td)),
                            );
                        }
                        local
                    })
                })
                .collect();
            handles
                .into_iter()
                .flat_map(|h| {
                    h.join().unwrap_or_else(|_| {
                        vec![Err(anyhow::anyhow!(
                            "External `.olean` digest worker panicked"
                        ))]
                    })
                })
                .collect()
        });
        for item in computed {
            let (m, td) = item?;
            olean_digests.insert(m.clone(), td.full.clone());
            tier_digests.insert(m, td);
        }
    } else {
        for (ext_mod, ext_path) in &unique_ext_paths {
            let td = compute_module_artifact_tier_digests_with_policy(
                ext_path,
                preserve_project || !ext_path.starts_with(&canon_dir),
            )?;
            olean_digests.insert(ext_mod.clone(), td.full.clone());
            tier_digests.insert(ext_mod.clone(), td);
        }
    }
    let mut replay_batch = ReplayLookupBatchCache::new(store, &cfg, &lean_path_env);
    let mut checked_ext_replay: HashSet<(String, PathBuf)> = HashSet::new();
    for node in dag.nodes.values() {
        for (ext_mod, ext_path) in &node.external_olean_deps {
            if checked_ext_replay.insert((ext_mod.clone(), ext_path.clone()))
                && !replay_batch.is_replayed_in_store(store, &cfg, &lean_path_env, ext_path)
            {
                unverified_external_deps.insert(ext_mod.clone());
            }
        }
    }
    let ext_digests_ms = t_ext.elapsed().as_millis();
    let t_ext_replay = std::time::Instant::now();
    let unverified_ext_count = unverified_external_deps.len();
    if !unverified_external_deps.is_empty() {
        crate::zygote::kernel_replay_modules_with_zygote(
            store,
            &cfg,
            &unverified_external_deps.into_iter().collect::<Vec<_>>(),
            &lean_path_env,
        )
        .context("External dependency `.olean` failed independent kernel replay")?;
    }
    let ext_replay_ms = t_ext_replay.elapsed().as_millis();
    if profile_phases {
        eprintln!(
            "[turbo-lean][profile] after_ext: ext_digests={}ms unique_ext={} ext_replay={}ms(n={})",
            ext_digests_ms,
            olean_digests.len(),
            ext_replay_ms,
            unverified_ext_count
        );
    }
    // Pre-warm the Zygote kernel-reader binary on the caller thread before spawning background
    // audit/replay workers so workers never race to bootstrap it.
    crate::zygote::ensure_zygote_binary_at(
        &store.root,
        &cfg.lean_bin,
        &crate::zygote::build_auditor_bootstrap_env(&cfg),
    )?;

    let (mut in_degree, dependents) = compute_dag_schedule_edges(&dag.nodes, &dag.shared_libs);
    let mut spec_in_degree = in_degree.clone();
    let mut probe_olean_digests = olean_digests.clone();
    let mut probe_tier_digests = tier_digests.clone();
    let mut spec_unlocked: HashSet<String> = HashSet::new();
    let mut parked_for_compile: HashSet<String> = HashSet::new();
    let mut evaluated_mods: HashSet<String> = HashSet::new();
    let mut shared_lib_local_mods: HashSet<String> = HashSet::new();
    for s in &dag.shared_libs {
        for lm in &s.local_modules {
            shared_lib_local_mods.insert(lm.clone());
        }
    }
    let tainted_elab_host_effect_mods = compute_tainted_elab_host_effect_modules(&cfg, &dag);
    let b_levels = compute_module_b_levels(
        store,
        &cfg,
        &dag,
        &tainted_elab_host_effect_mods,
        &dependents,
        trust_domain,
        preserve_project,
        &tier_digests,
    );
    if profile_phases {
        eprintln!(
            "[turbo-lean][profile] after_blevels: elapsed={}ms",
            t_total.elapsed().as_millis()
        );
    }

    enum PendingAuditOrigin {
        CasRestored {
            dig: String,
            preserve_lake: bool,
            trace_log: Vec<serde_json::Value>,
        },
        WarmAdopted {
            dig: String,
            mod_key: String,
        },
        Compiled {
            dig: String,
            mod_key: String,
            dur_ms: i64,
            stdout_str: String,
        },
    }

    type AcceptedAuditStep = Option<(String, Option<(String, i64, Vec<serde_json::Value>)>)>;

    #[allow(clippy::enum_variant_names)]
    enum SchedulerEvent {
        CompileFinished {
            mod_name: String,
            mod_key: String,
            res: Result<StagedModuleCompileOutput>,
        },
        AuditBatchFinished {
            batch_mods: Vec<String>,
            res: Result<AuditBatchWorkerOutcome>,
        },
        CasHashFinished {
            mod_name: String,
            mod_key: String,
            dur_ms: i64,
            res: Result<StagedCasBlobItems>,
        },
    }

    struct CasHashJob {
        mod_name: String,
        mod_key: String,
        dur_ms: i64,
        raw_items: StagedCasBlobItems,
    }

    let mut completed_mods: HashSet<String> = HashSet::new();
    let mut built_shared_libs: HashSet<(PathBuf, String)> = HashSet::new();
    let mut shared_exp_memo: HashMap<(String, bool), LakeModuleExportInfo> = HashMap::new();
    let mut probe_manifest_cache: HashMap<PathBuf, Option<Result<VerifiedDepManifest, ()>>> =
        HashMap::new();
    let mut verified_manifest_cache: HashMap<PathBuf, (VerifiedDepManifest, bool)> = HashMap::new();
    let cached_ws_inputs_digest: Option<String> = workspace_lake_inputs_digest(&cfg).ok();
    let mut ready_to_evaluate: VecDeque<String> = VecDeque::new();
    for (mod_name, &deg) in &in_degree {
        if deg == 0 {
            ready_to_evaluate.push_back(mod_name.clone());
        }
    }

    let mut ready_compile_heap: BinaryHeap<(u64, Reverse<String>)> = BinaryHeap::new();
    let mut compile_keys: HashMap<String, String> = HashMap::new();
    let mut pending_audit_queue: VecDeque<String> = VecDeque::new();
    let mut pending_audit_meta: HashMap<String, PendingAuditOrigin> = HashMap::new();
    let mut audited_waiting_ancestors: HashMap<String, PerModuleAuditOutcome> = HashMap::new();
    let remote_cache_url = crate::pack::resolve_remote_cache_url();
    let remote_cache_token = crate::pack::resolve_remote_cache_token();
    let mut remote_manifest_cache: Option<crate::pack::DeltaManifest> = None;

    let store_root_buf = store.root.clone();
    let cfg_ref = &cfg;
    let dag_ref = &dag;
    let lp_ref = lean_path_env.as_str();
    let ld_ref = ld_library_path_env.as_str();
    let bwrap_ref = bwrap_bin.as_deref();
    let store_root_ref = store_root_buf.as_path();

    let wipe_node_locked = |node: &ModuleNode, preserve_lake: bool| -> Result<()> {
        if !preserve_lake {
            let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
            let _guard = lock
                .lock()
                .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
            let _flock_guard = acquire_publish_flock(&node.pkg_root, false)?;
            wipe_existing_module_artifacts(node);
        }
        Ok(())
    };

    let wipe_unverified_candidates = |meta: &HashMap<String, PendingAuditOrigin>| {
        let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
        if let Ok(_guard) = lock.lock() {
            for (cand_mod, origin) in meta {
                let preserve_cand = match origin {
                    PendingAuditOrigin::CasRestored { preserve_lake, .. } => *preserve_lake,
                    PendingAuditOrigin::WarmAdopted { .. }
                    | PendingAuditOrigin::Compiled { .. } => {
                        preserve_project
                            || dag
                                .nodes
                                .get(cand_mod)
                                .is_some_and(|n| package_is_read_only(&canon_dir, &n.pkg_root))
                    }
                };
                if !preserve_cand {
                    if let Some(node) = dag.nodes.get(cand_mod) {
                        if let Ok(_flock) = acquire_publish_flock(&node.pkg_root, false) {
                            wipe_existing_module_artifacts(node);
                        }
                    }
                }
            }
        }
    };

    let compile_pool_size = max_jobs.min(dag.nodes.len()).max(1);
    let compile_work_queue: std::sync::Mutex<VecDeque<(String, String)>> =
        std::sync::Mutex::new(VecDeque::new());
    let compile_work_cv = std::sync::Condvar::new();
    let compile_shutdown = std::sync::atomic::AtomicBool::new(false);
    let compile_work_queue_ref = &compile_work_queue;
    let compile_work_cv_ref = &compile_work_cv;
    let compile_shutdown_ref = &compile_shutdown;

    let explicit_audit_batch_cfg = std::env::var("TURBO_LEAN_AUDIT_BATCH_SIZE")
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .filter(|&v| v > 0);
    let audit_pool_size = if is_untrusted || explicit_audit_batch_cfg.is_some() {
        1
    } else {
        (max_jobs / 4).clamp(1, 2).min(dag.nodes.len()).max(1)
    };
    let audit_work_queue: std::sync::Mutex<VecDeque<Vec<String>>> =
        std::sync::Mutex::new(VecDeque::new());
    let audit_work_cv = std::sync::Condvar::new();
    let audit_shutdown = std::sync::atomic::AtomicBool::new(false);
    let audit_work_queue_ref = &audit_work_queue;
    let audit_work_cv_ref = &audit_work_cv;
    let audit_shutdown_ref = &audit_shutdown;

    let t_sched = std::time::Instant::now();
    let scheduler_res: Result<()> = std::thread::scope(|s| {
        let (event_tx, event_rx) = std::sync::mpsc::channel::<SchedulerEvent>();

        for _ in 0..compile_pool_size {
            let tx = event_tx.clone();
            let canon_dir_ref = canon_dir.as_path();
            s.spawn(move || loop {
                let job_opt = {
                    let mut guard = compile_work_queue_ref
                        .lock()
                        .unwrap_or_else(|e| e.into_inner());
                    while guard.is_empty() && !compile_shutdown_ref.load(Ordering::SeqCst) {
                        guard = compile_work_cv_ref
                            .wait(guard)
                            .unwrap_or_else(|e| e.into_inner());
                    }
                    if compile_shutdown_ref.load(Ordering::SeqCst) && guard.is_empty() {
                        None
                    } else {
                        guard.pop_front()
                    }
                };
                let Some((mod_name, mod_key)) = job_opt else {
                    break;
                };
                let node = dag_ref.nodes.get(&mod_name).expect("node in dag");
                let preserve_lake =
                    preserve_project || package_is_read_only(canon_dir_ref, &node.pkg_root);
                let res = compile_single_module_staged(
                    cfg_ref,
                    dag_ref,
                    node,
                    lp_ref,
                    ld_ref,
                    is_untrusted,
                    bwrap_ref,
                    preserve_lake,
                    compile_pool_size,
                );
                let _ = tx.send(SchedulerEvent::CompileFinished {
                    mod_name,
                    mod_key,
                    res,
                });
            });
        }

        let result_tx = event_tx.clone();
        for _ in 0..audit_pool_size {
            let tx = event_tx.clone();
            s.spawn(move || loop {
                let job_opt = {
                    let mut guard = audit_work_queue_ref
                        .lock()
                        .unwrap_or_else(|e| e.into_inner());
                    while guard.is_empty() && !audit_shutdown_ref.load(Ordering::SeqCst) {
                        guard = audit_work_cv_ref
                            .wait(guard)
                            .unwrap_or_else(|e| e.into_inner());
                    }
                    if audit_shutdown_ref.load(Ordering::SeqCst) && guard.is_empty() {
                        None
                    } else {
                        guard.pop_front()
                    }
                };
                let Some(batch_mods) = job_opt else {
                    break;
                };
                let res = run_audit_or_replay_batch_worker(
                    store_root_ref,
                    cfg_ref,
                    dag_ref,
                    &batch_mods,
                    lp_ref,
                    is_untrusted,
                );
                let _ = tx.send(SchedulerEvent::AuditBatchFinished { batch_mods, res });
            });
        }

        let (cas_tx, cas_rx) = std::sync::mpsc::channel::<CasHashJob>();
        {
            let tx = event_tx.clone();
            s.spawn(move || {
                while let Ok(mut job) = cas_rx.recv() {
                    record_scheduler_test_event(
                        "cas_hash_start",
                        std::slice::from_ref(&job.mod_name),
                    );
                    for item in &mut job.raw_items {
                        item.0 = blake3::hash(&item.1).to_hex().to_string();
                    }
                    record_scheduler_test_event(
                        "cas_hash_end",
                        std::slice::from_ref(&job.mod_name),
                    );
                    let _ = tx.send(SchedulerEvent::CasHashFinished {
                        mod_name: job.mod_name,
                        mod_key: job.mod_key,
                        dur_ms: job.dur_ms,
                        res: Ok(job.raw_items),
                    });
                }
            });
        }

        drop(event_tx);

        let mut in_flight_compiles: usize = 0;
        let mut in_flight_audits: usize = 0;
        let mut in_flight_cas: usize = 0;
        let mut fatal_err: Option<anyhow::Error> = None;

        loop {
            if fatal_err.is_none() {
                while let Some(mod_name) = ready_to_evaluate.pop_front() {
                    if !evaluated_mods.insert(mod_name.clone()) {
                        continue;
                    }
                    let eval_res: Result<()> = (|| {
                        let node = dag.nodes.get(&mod_name).expect("ready module in dag");
                        let verified_ready = in_degree.get(&mod_name).copied().unwrap_or(0) == 0;
                        let preserve_lake =
                            preserve_project || package_is_read_only(&canon_dir, &node.pkg_root);
                        let (dep_digests_vec, raw_imp_dynlibs, dynlib_digests) = {
                            let active_tiers = if verified_ready {
                                &tier_digests
                            } else {
                                &probe_tier_digests
                            };
                            gather_module_dep_digests_and_dynlibs(&cfg, &dag, node, active_tiers)?
                        };
                        let mod_key = compute_module_cas_key_with_dynlibs(
                            &cfg,
                            node,
                            &dep_digests_vec,
                            node.needs_c,
                            &dynlib_digests,
                        )?;
                        let fallback_c_key_opt = if !node.needs_c {
                            Some(compute_module_cas_key_with_dynlibs(
                                &cfg,
                                node,
                                &dep_digests_vec,
                                true,
                                &dynlib_digests,
                            )?)
                        } else {
                            None
                        };
                        let node_has_elab_host_effects = tainted_elab_host_effect_mods
                            .contains(&mod_name)
                            || fs::read_to_string(&node.src_path)
                                .map(|s| {
                                    node_source_has_disallowed_elab_host_effects(&cfg, node, &s)
                                })
                                .unwrap_or(true);
                        let mut cas_hit_outputs: Option<Vec<BlobEntry>> = None;
                        if !node_has_elab_host_effects {
                            if let Some(outputs) =
                                store.get_cached_action(&mod_key, trust_domain)?
                            {
                                cas_hit_outputs = Some(outputs);
                            } else if let Some(ref c_key) = fallback_c_key_opt {
                                if let Some(outputs) =
                                    store.get_cached_action(c_key, trust_domain)?
                                {
                                    cas_hit_outputs = Some(outputs);
                                }
                            }
                        }
                        if !node_has_elab_host_effects && cas_hit_outputs.is_none() {
                            if let Some(ref rem_url) = remote_cache_url {
                                let mut wanted = vec![mod_key.clone()];
                                if let Some(ref c_key) = fallback_c_key_opt {
                                    wanted.push(c_key.clone());
                                }
                                if crate::pack::try_pull_remote_module_action(
                                    store,
                                    rem_url,
                                    remote_cache_token.as_deref(),
                                    &mut remote_manifest_cache,
                                    &wanted,
                                    trust_domain,
                                    is_untrusted,
                                )
                                .unwrap_or(false)
                                {
                                    replay_batch.refresh_replay_hmac_key(store);
                                    if let Some(outputs) =
                                        store.get_cached_action(&mod_key, trust_domain)?
                                    {
                                        cas_hit_outputs = Some(outputs);
                                    } else if let Some(ref c_key) = fallback_c_key_opt {
                                        if let Some(outputs) =
                                            store.get_cached_action(c_key, trust_domain)?
                                        {
                                            cas_hit_outputs = Some(outputs);
                                        }
                                    }
                                }
                            }
                        }
                        let target_root = if node.pkg_root.starts_with(&canon_dir) {
                            &canon_dir
                        } else {
                            &node.pkg_root
                        };
                        let cas_hit_outputs = cas_hit_outputs
                            .filter(|o| cas_outputs_bound_to_node(o, target_root, node));
                        if let Some(outputs) = cas_hit_outputs {
                            let cas_restored_dig_opt = {
                                let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
                                let _guard = lock.lock().map_err(|_| {
                                    anyhow::anyhow!("Module artifact publication mutex poisoned")
                                })?;
                                let _flock_guard = acquire_publish_flock_mode(
                                    &node.pkg_root,
                                    !preserve_lake,
                                    preserve_lake,
                                )?;
                                let mut cas_trace_log: Option<Vec<serde_json::Value>> =
                                    Some(Vec::new());
                                for entry in
                                    outputs.iter().filter(|e| e.rel_path == "thm:trace_log")
                                {
                                    let parsed = store
                                        .ensure_blob_uncompressed(&entry.blob_hash)
                                        .ok()
                                        .and_then(|p| fs::read(p).ok())
                                        .filter(|b| {
                                            b.len() as u64 == entry.size_bytes
                                                && blake3::hash(b).to_hex().as_str()
                                                    == entry.blob_hash
                                        })
                                        .and_then(|b| {
                                            serde_json::from_slice::<Vec<serde_json::Value>>(&b)
                                                .ok()
                                        });
                                    match parsed {
                                        Some(log_entries) => cas_trace_log = Some(log_entries),
                                        None => {
                                            cas_trace_log = None;
                                            break;
                                        }
                                    }
                                }
                                if !preserve_lake && cas_trace_log.is_some() {
                                    let preserve_c_obj = node.needs_c
                                        && outputs.iter().find(|e| e.kind == "c").is_some_and(
                                            |c_entry| {
                                                fs::read(&node.c_path).is_ok_and(|b| {
                                                    b.len() as u64 == c_entry.size_bytes
                                                        && blake3::hash(&b).to_hex().as_str()
                                                            == c_entry.blob_hash
                                                })
                                            },
                                        );
                                    wipe_existing_module_artifacts_opts(node, preserve_c_obj);
                                    shared_exp_memo.remove(&(mod_name.clone(), false));
                                    shared_exp_memo.remove(&(mod_name.clone(), true));
                                    store.materialize_into_worktree(
                                        target_root,
                                        &project_name,
                                        &outputs,
                                    )?;
                                    if !node.needs_c {
                                        let _ = fs::remove_file(&node.c_path);
                                    }
                                }
                                let mut paths: Vec<_> = olean_artifact_paths(&node.olean_path)
                                    .into_iter()
                                    .map(|(_, p)| p)
                                    .collect();
                                let checked_outputs: Vec<BlobEntry> = outputs
                                    .into_iter()
                                    .filter(|e| {
                                        !e.rel_path.starts_with("thm:")
                                            && (node.needs_c || e.kind != "c")
                                    })
                                    .collect();
                                paths.extend(
                                    checked_outputs
                                        .iter()
                                        .map(|e| target_root.join(&e.rel_path)),
                                );
                                let restored = if let Some(trace_log) = cas_trace_log {
                                    _flock_guard.read_consistent(&paths, || {
                                        if preserve_lake {
                                            crate::db::reuse_worktree_outputs(
                                                target_root,
                                                &checked_outputs,
                                            )?;
                                        }
                                        let hashes_ok = validate_materialized_module_artifacts(
                                            node,
                                            preserve_lake,
                                        ) && checked_outputs.iter().all(|entry| {
                                            fs::read(target_root.join(&entry.rel_path)).is_ok_and(
                                                |bytes| {
                                                    bytes.len() as u64 == entry.size_bytes
                                                        && blake3::hash(&bytes).to_hex().as_str()
                                                            == entry.blob_hash
                                                },
                                            )
                                        });
                                        if hashes_ok {
                                            compute_module_artifact_tier_digests_locked(
                                                &node.olean_path,
                                                Some(&_flock_guard),
                                            )
                                            .map(|td| Some((td, trace_log)))
                                        } else {
                                            Ok(None)
                                        }
                                    })?
                                } else {
                                    None
                                };
                                if restored.is_none() && !preserve_lake {
                                    wipe_existing_module_artifacts(node);
                                    shared_exp_memo.remove(&(mod_name.clone(), false));
                                    shared_exp_memo.remove(&(mod_name.clone(), true));
                                    replay_batch.invalidate_memo();
                                }
                                restored
                            };
                            if let Some((cas_tiers, trace_log)) = cas_restored_dig_opt {
                                replay_batch.invalidate_memo();
                                let dig = cas_tiers.full.clone();
                                if !is_untrusted && !shared_lib_local_mods.contains(&mod_name) {
                                    probe_olean_digests.insert(mod_name.clone(), dig.clone());
                                    probe_tier_digests.insert(mod_name.clone(), cas_tiers);
                                    spec_unlocked.insert(mod_name.clone());
                                    if let Some(deps) = dependents.get(&mod_name) {
                                        for dep_child in deps {
                                            if let Some(sdeg) = spec_in_degree.get_mut(dep_child) {
                                                *sdeg = sdeg.saturating_sub(1);
                                                if *sdeg == 0 && !evaluated_mods.contains(dep_child)
                                                {
                                                    let child_ok = dag
                                                        .nodes
                                                        .get(dep_child)
                                                        .is_some_and(|cn| {
                                                            compute_module_raw_import_dynlibs(
                                                                &dag, cn,
                                                            )
                                                            .iter()
                                                            .all(|dp| dp.is_file())
                                                        });
                                                    if child_ok {
                                                        ready_to_evaluate
                                                            .push_back(dep_child.clone());
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                pending_audit_meta.insert(
                                    mod_name.clone(),
                                    PendingAuditOrigin::CasRestored {
                                        dig,
                                        preserve_lake,
                                        trace_log,
                                    },
                                );
                                pending_audit_queue.push_back(mod_name);
                                return Ok(());
                            }
                            if !verified_ready {
                                evaluated_mods.remove(&mod_name);
                                parked_for_compile.insert(mod_name);
                                return Ok(());
                            }
                            if preserve_lake {
                                return Err(read_only_package_rebuild_error(
                                    &canon_dir,
                                    node,
                                    "rebuilding invalid CAS outputs for",
                                ));
                            }
                        } else {
                            if !is_untrusted && !node_has_elab_host_effects {
                                let warm_opt = {
                                    let (active_digests, active_tiers) = if verified_ready {
                                        (&olean_digests, &tier_digests)
                                    } else {
                                        (&probe_olean_digests, &probe_tier_digests)
                                    };
                                    probe_warm_on_disk_module_candidate(
                                        &cfg,
                                        &dag,
                                        node,
                                        preserve_lake,
                                        active_digests,
                                        active_tiers,
                                        &raw_imp_dynlibs,
                                        &mut shared_exp_memo,
                                        &mut probe_manifest_cache,
                                        cached_ws_inputs_digest.as_deref(),
                                    )
                                };
                                if let Some(warm_dig) = warm_opt {
                                    if !shared_lib_local_mods.contains(&mod_name) {
                                        if let Ok(warm_tiers) =
                                            compute_module_artifact_tier_digests_with_policy(
                                                &node.olean_path,
                                                preserve_lake,
                                            )
                                            .and_then(
                                                |td| {
                                                    anyhow::ensure!(
                                                        td.full == warm_dig,
                                                        "warm tier digest mismatch"
                                                    );
                                                    Ok(td)
                                                },
                                            )
                                        {
                                            probe_olean_digests
                                                .insert(mod_name.clone(), warm_dig.clone());
                                            probe_tier_digests.insert(mod_name.clone(), warm_tiers);
                                            spec_unlocked.insert(mod_name.clone());
                                            if let Some(deps) = dependents.get(&mod_name) {
                                                for dep_child in deps {
                                                    if let Some(sdeg) =
                                                        spec_in_degree.get_mut(dep_child)
                                                    {
                                                        *sdeg = sdeg.saturating_sub(1);
                                                        if *sdeg == 0
                                                            && !evaluated_mods.contains(dep_child)
                                                        {
                                                            let child_ok = dag
                                                                .nodes
                                                                .get(dep_child)
                                                                .is_some_and(|cn| {
                                                                    compute_module_raw_import_dynlibs(
                                                                        &dag, cn,
                                                                    )
                                                                    .iter()
                                                                    .all(|dp| dp.is_file())
                                                                });
                                                            if child_ok {
                                                                ready_to_evaluate
                                                                    .push_back(dep_child.clone());
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    pending_audit_meta.insert(
                                        mod_name.clone(),
                                        PendingAuditOrigin::WarmAdopted {
                                            dig: warm_dig,
                                            mod_key,
                                        },
                                    );
                                    record_scheduler_test_event(
                                        "warm_adopted",
                                        std::slice::from_ref(&mod_name),
                                    );
                                    pending_audit_queue.push_back(mod_name);
                                    return Ok(());
                                }
                            }
                            if !verified_ready {
                                evaluated_mods.remove(&mod_name);
                                parked_for_compile.insert(mod_name);
                                return Ok(());
                            }
                            if preserve_lake {
                                return Err(read_only_package_rebuild_error(
                                    &canon_dir,
                                    node,
                                    "compiling uncached module",
                                ));
                            }
                            wipe_node_locked(node, preserve_lake)?;
                            shared_exp_memo.remove(&(mod_name.clone(), false));
                            shared_exp_memo.remove(&(mod_name.clone(), true));
                        }
                        let prio = b_levels.get(&mod_name).copied().unwrap_or(1);
                        compile_keys.insert(mod_name.clone(), mod_key);
                        ready_compile_heap.push((prio, Reverse(mod_name)));
                        Ok(())
                    })();
                    if let Err(e) = eval_res {
                        fatal_err = Some(e);
                        break;
                    }
                }
            }

            if fatal_err.is_none() {
                while in_flight_compiles < max_jobs {
                    let Some((_, Reverse(mod_name))) = ready_compile_heap.pop() else {
                        break;
                    };
                    let mod_key = compile_keys
                        .remove(&mod_name)
                        .expect("compile_keys contains ready module");
                    if let Some(node) = dag
                        .nodes
                        .get(&mod_name)
                        .filter(|n| preserve_project || package_is_read_only(&canon_dir, &n.pkg_root))
                    {
                        fatal_err = Some(read_only_package_rebuild_error(
                            &canon_dir,
                            node,
                            "compiling",
                        ));
                        break;
                    }
                    if !cfg.lean_bin.is_file() {
                        fatal_err = Some(anyhow::anyhow!(
                            "Cannot compile uncached Lean module `{}` for {} because no `lean` compiler binary is installed on this host (requested toolchain `{}`)",
                            mod_name,
                            project_dir.display(),
                            cfg.toolchain
                        ));
                        break;
                    }
                    if is_untrusted && bwrap_bin.is_none() {
                        fatal_err = Some(anyhow::anyhow!(
                            "Untrusted module compilation requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
                        ));
                        break;
                    }
                    record_scheduler_test_event(
                        "compile_dispatch",
                        std::slice::from_ref(&mod_name),
                    );
                    if profile_phases {
                        eprintln!(
                            "[turbo-lean][profile] compile_dispatch: {} (elapsed={}ms)",
                            mod_name,
                            t_total.elapsed().as_millis()
                        );
                    }
                    {
                        let mut guard =
                            compile_work_queue.lock().unwrap_or_else(|e| e.into_inner());
                        guard.push_back((mod_name, mod_key));
                    }
                    compile_work_cv.notify_one();
                    in_flight_compiles += 1;
                }
            }

            while fatal_err.is_none()
                && in_flight_audits < audit_pool_size
                && !pending_audit_queue.is_empty()
            {
                let batch_limit = match explicit_audit_batch_cfg {
                    Some(sz) => sz,
                    None if !is_untrusted => 128,
                    None => scheduler_audit_batch_size(),
                };
                let mut batch_mods = Vec::with_capacity(pending_audit_queue.len().min(batch_limit));
                let mut fast_verified_mods: Vec<(String, VerifiedFastStoreAuthority)> = Vec::new();
                let mut deferred_for_deps = Vec::new();
                while batch_mods.len() < batch_limit {
                    let Some(m) = pending_audit_queue.pop_front() else {
                        break;
                    };
                    if let Some(node) = dag.nodes.get(&m) {
                        let missing_dep_olean = node
                            .direct_dag_deps
                            .iter()
                            .any(|d| dag.nodes.get(d).is_some_and(|dn| !dn.olean_path.is_file()));
                        if missing_dep_olean {
                            deferred_for_deps.push(m);
                            continue;
                        }
                    }
                    if !is_untrusted && explicit_audit_batch_cfg.is_none() {
                        let expected_origin_dig = match pending_audit_meta.get(&m) {
                            Some(
                                PendingAuditOrigin::CasRestored { dig, .. }
                                | PendingAuditOrigin::WarmAdopted { dig, .. },
                            ) => Some(dig.clone()),
                            _ => None,
                        };
                        if let (Some(expected_dig), Some(node)) =
                            (expected_origin_dig, dag.nodes.get(&m))
                        {
                            let preserve_lake = preserve_project
                                || package_is_read_only(&canon_dir, &node.pkg_root);
                            let pre_dig_ok = compute_olean_artifact_set_digest_with_policy(
                                &node.olean_path,
                                preserve_lake,
                            )
                            .ok()
                            .as_deref()
                                == Some(expected_dig.as_str());
                            let fast_auth_opt = if pre_dig_ok {
                                let binds_policy =
                                    replay_batch.is_root_module_olean(&node.olean_path);
                                if node.is_root_pkg {
                                    replay_batch.verify_audited_in_store_authority(
                                        store,
                                        &cfg,
                                        &m,
                                        &node.olean_path,
                                        binds_policy,
                                        expected_dig.clone(),
                                    )
                                } else {
                                    replay_batch.verify_replayed_in_store_authority(
                                        store,
                                        &cfg,
                                        &node.olean_path,
                                        binds_policy,
                                        expected_dig.clone(),
                                    )
                                }
                            } else {
                                None
                            };
                            if let Some(fast_auth) = fast_auth_opt {
                                let post_dig_ok = compute_olean_artifact_set_digest_with_policy(
                                    &node.olean_path,
                                    preserve_lake,
                                )
                                .ok()
                                .as_deref()
                                    == Some(expected_dig.as_str())
                                    && replay_batch.verify_fast_store_authority(&fast_auth);
                                if post_dig_ok {
                                    fast_verified_mods.push((m, fast_auth));
                                    continue;
                                }
                            }
                        }
                    }
                    batch_mods.push(m);
                }
                let only_deferred = batch_mods.is_empty() && fast_verified_mods.is_empty();
                for dm in deferred_for_deps {
                    pending_audit_queue.push_back(dm);
                }
                if !fast_verified_mods.is_empty() {
                    if profile_phases {
                        eprintln!(
                            "[turbo-lean][profile] audit_fast_store_hit: n={} (elapsed={}ms)",
                            fast_verified_mods.len(),
                            t_total.elapsed().as_millis()
                        );
                    }
                    let mut fast_outcomes: AuditBatchWorkerOutcome =
                        HashMap::with_capacity(fast_verified_mods.len());
                    let mut fast_batch_names = Vec::with_capacity(fast_verified_mods.len());
                    for (m, fast_auth) in fast_verified_mods {
                        fast_outcomes.insert(
                            m.clone(),
                            (Ok(()), Some(ModuleAuditAuthority::FastStore(fast_auth))),
                        );
                        fast_batch_names.push(m);
                    }
                    in_flight_audits += 1;
                    let _ = result_tx.send(SchedulerEvent::AuditBatchFinished {
                        batch_mods: fast_batch_names,
                        res: Ok(fast_outcomes),
                    });
                }
                if !batch_mods.is_empty() {
                    let coalesce_snapshot = !is_untrusted
                        && explicit_audit_batch_cfg.is_none()
                        && (in_flight_compiles > 0 || !ready_compile_heap.is_empty())
                        && batch_mods.len() < 64
                        && !(in_flight_compiles < compile_pool_size
                            && batch_mods
                                .iter()
                                .any(|m| dependents.get(m).is_some_and(|deps| !deps.is_empty())));
                    if coalesce_snapshot {
                        for m in batch_mods.into_iter().rev() {
                            pending_audit_queue.push_front(m);
                        }
                        break;
                    }
                    if profile_phases {
                        eprintln!(
                            "[turbo-lean][profile] audit_dispatch: n={} (elapsed={}ms)",
                            batch_mods.len(),
                            t_total.elapsed().as_millis()
                        );
                    }
                    {
                        let mut guard = audit_work_queue.lock().unwrap_or_else(|e| e.into_inner());
                        guard.push_back(batch_mods);
                    }
                    audit_work_cv.notify_one();
                    in_flight_audits += 1;
                } else if only_deferred {
                    break;
                }
            }

            if fatal_err.is_some() {
                ready_to_evaluate.clear();
                ready_compile_heap.clear();
                compile_keys.clear();
                pending_audit_queue.clear();
                {
                    let mut guard = compile_work_queue.lock().unwrap_or_else(|e| e.into_inner());
                    let dropped = guard.len();
                    guard.clear();
                    in_flight_compiles = in_flight_compiles.saturating_sub(dropped);
                }
                {
                    let mut guard = audit_work_queue.lock().unwrap_or_else(|e| e.into_inner());
                    let dropped = guard.len();
                    guard.clear();
                    in_flight_audits = in_flight_audits.saturating_sub(dropped);
                }
            }

            let all_idle = in_flight_compiles == 0
                && in_flight_audits == 0
                && in_flight_cas == 0
                && (fatal_err.is_some()
                    || (ready_to_evaluate.is_empty()
                        && ready_compile_heap.is_empty()
                        && pending_audit_queue.is_empty()));
            if all_idle {
                break;
            }

            let ev = match event_rx.recv() {
                Ok(ev) => ev,
                Err(_) => {
                    if fatal_err.is_none() {
                        fatal_err = Some(anyhow::anyhow!(
                            "Native scheduler worker event channel closed prematurely"
                        ));
                    }
                    break;
                }
            };

            match ev {
                SchedulerEvent::CompileFinished {
                    mod_name,
                    mod_key,
                    res,
                } => {
                    in_flight_compiles = in_flight_compiles.saturating_sub(1);
                    if fatal_err.is_some() {
                        continue;
                    }
                    match res {
                        Ok(staged) => {
                            let node = dag.nodes.get(&mod_name).expect("compiled module in dag");
                            match publish_staged_module_compile_output(node, staged) {
                                Ok((dur_ms, stdout_str, dig)) => {
                                    shared_exp_memo.remove(&(mod_name.clone(), false));
                                    shared_exp_memo.remove(&(mod_name.clone(), true));
                                    replay_batch.invalidate_memo();
                                    pending_audit_meta.insert(
                                        mod_name.clone(),
                                        PendingAuditOrigin::Compiled {
                                            dig,
                                            mod_key,
                                            dur_ms,
                                            stdout_str,
                                        },
                                    );
                                    pending_audit_queue.push_back(mod_name);
                                }
                                Err(e) => {
                                    fatal_err = Some(e);
                                }
                            }
                        }
                        Err(e) => {
                            fatal_err = Some(e);
                        }
                    }
                }
                SchedulerEvent::AuditBatchFinished { batch_mods, res } => {
                    in_flight_audits = in_flight_audits.saturating_sub(1);
                    if fatal_err.is_some() {
                        continue;
                    }
                    let mut per_mod_outcomes = match res {
                        Ok(outcomes) => outcomes,
                        Err(e) => {
                            fatal_err = Some(e);
                            continue;
                        }
                    };
                    if let Err(e) = validate_materialized_artifacts(&cfg) {
                        fatal_err = Some(e);
                        continue;
                    }
                    let mut finalize_queue: VecDeque<(String, PerModuleAuditOutcome)> =
                        VecDeque::with_capacity(batch_mods.len());
                    for mod_name in batch_mods {
                        if !pending_audit_meta.contains_key(&mod_name) {
                            continue;
                        }
                        let mod_outcome = per_mod_outcomes.remove(&mod_name).unwrap_or_else(|| {
                            (
                                Err(anyhow::anyhow!(
                                    "Missing per-module audit outcome for `{}`",
                                    mod_name
                                )),
                                None,
                            )
                        });
                        if in_degree.get(&mod_name).copied().unwrap_or(0) == 0 {
                            finalize_queue.push_back((mod_name, mod_outcome));
                        } else {
                            audited_waiting_ancestors.insert(mod_name, mod_outcome);
                        }
                    }
                    let mut pending_snap_records: Vec<(
                        usize,
                        std::sync::Arc<crate::zygote::ClosureSnapshot>,
                        Vec<String>,
                        Vec<String>,
                    )> = Vec::new();
                    while let Some((mod_name, (mod_audit_res, snap_auth_opt))) =
                        finalize_queue.pop_front()
                    {
                        let Some(origin) = pending_audit_meta.remove(&mod_name) else {
                            continue;
                        };
                        let node = dag.nodes.get(&mod_name).expect("audited module in dag");
                        let preserve_lake =
                            preserve_project || package_is_read_only(&canon_dir, &node.pkg_root);
                        let auth_dig_opt = match snap_auth_opt.as_ref() {
                            Some(ModuleAuditAuthority::Snapshot((snap, _, _))) => {
                                crate::zygote::ensure_bound_audit_closure(
                                    snap,
                                    "sched_finalize_verify",
                                )
                                .ok()
                                .and_then(|_| {
                                    crate::zygote::snapshot_module_artifact_set_digest(
                                        snap, &mod_name,
                                    )
                                })
                            }
                            Some(ModuleAuditAuthority::FastStore(fast_auth)) => replay_batch
                                .verify_fast_store_authority(fast_auth)
                                .then(|| fast_auth.artifact_digest.clone()),
                            None => None,
                        };
                        let snap_matches_dig = |expected_dig: &str| -> bool {
                            auth_dig_opt.as_deref() == Some(expected_dig)
                        };

                        let step_res: Result<AcceptedAuditStep> = match origin {
                            PendingAuditOrigin::CasRestored {
                                dig,
                                preserve_lake: cas_preserve,
                                trace_log,
                            } => (|| {
                                if let Err(audit_err) = mod_audit_res {
                                    wipe_node_locked(node, cas_preserve)?;
                                    return Err(audit_err.context(format!(
                                            "In-kernel `.olean` audit rejected materialized CAS hit for module `{}`",
                                            mod_name
                                        )));
                                }
                                let post_audit_dig = compute_olean_artifact_set_digest_with_policy(
                                    &node.olean_path,
                                    cas_preserve,
                                )?;
                                if post_audit_dig != dig || !snap_matches_dig(&dig) {
                                    wipe_node_locked(node, cas_preserve)?;
                                    anyhow::bail!(
                                            "Artifact digest mutated during `.olean` kernel audit for `{}`",
                                            mod_name
                                        );
                                }
                                if !json_output && !trace_log.is_empty() {
                                    let formatted = format_lake_trace_log_stdout(&trace_log);
                                    if !formatted.trim().is_empty() {
                                        print!("{}", formatted);
                                    }
                                }
                                if !cas_preserve && emit_lake_sidecars {
                                    write_lake_module_hashes_and_trace_with_memo(
                                        &cfg,
                                        &dag,
                                        node,
                                        &dig,
                                        Some(&post_audit_dig),
                                        true,
                                        &trace_log,
                                        &mut shared_exp_memo,
                                    )?;
                                    if !is_untrusted {
                                        record_verified_dep_source_cached(
                                            &cfg,
                                            &dag,
                                            node,
                                            tainted_elab_host_effect_mods.contains(&mod_name),
                                            &dig,
                                            node.is_root_pkg,
                                            &olean_digests,
                                            &tier_digests,
                                            &mut verified_manifest_cache,
                                            true,
                                            cached_ws_inputs_digest.as_deref(),
                                        );
                                    }
                                    write_file_atomic(
                                        &module_setup_json_path(node),
                                        &serde_json::to_vec(&build_setup_json(
                                            &cfg, &dag, node, None, None,
                                        )?)?,
                                    )?;
                                }
                                report.modules_cached += 1;
                                report.cached_modules.push(mod_name.clone());
                                Ok(Some((dig, None)))
                            })(),
                            PendingAuditOrigin::WarmAdopted { dig, mod_key } => (|| {
                                let post_audit_dig =
                                    if mod_audit_res.is_ok() && snap_matches_dig(&dig) {
                                        compute_olean_artifact_set_digest_with_policy(
                                            &node.olean_path,
                                            preserve_lake,
                                        )
                                        .ok()
                                    } else {
                                        None
                                    };
                                if post_audit_dig.as_deref() != Some(dig.as_str()) {
                                    if spec_unlocked.remove(&mod_name) {
                                        let mut inv_stack: Vec<String> = vec![mod_name.clone()];
                                        let mut seen_inv: HashSet<String> = HashSet::new();
                                        seen_inv.insert(mod_name.clone());
                                        let mut to_invalidate: Vec<String> = Vec::new();
                                        while let Some(cur) = inv_stack.pop() {
                                            if let Some(deps) = dependents.get(&cur) {
                                                for d in deps {
                                                    if seen_inv.insert(d.clone()) {
                                                        to_invalidate.push(d.clone());
                                                        inv_stack.push(d.clone());
                                                    }
                                                }
                                            }
                                        }
                                        probe_olean_digests.remove(&mod_name);
                                        probe_tier_digests.remove(&mod_name);
                                        for d in &to_invalidate {
                                            probe_olean_digests.remove(d);
                                            probe_tier_digests.remove(d);
                                            spec_unlocked.remove(d);
                                            evaluated_mods.remove(d);
                                            parked_for_compile.remove(d);
                                            audited_waiting_ancestors.remove(d);
                                            if let Some(d_orig) = pending_audit_meta.remove(d) {
                                                let d_pres = match d_orig {
                                                    PendingAuditOrigin::CasRestored {
                                                        preserve_lake: p,
                                                        ..
                                                    } => p,
                                                    _ => {
                                                        preserve_project
                                                            || dag.nodes.get(d).is_some_and(|dn| {
                                                                package_is_read_only(
                                                                    &canon_dir,
                                                                    &dn.pkg_root,
                                                                )
                                                            })
                                                    }
                                                };
                                                if let Some(dn) = dag.nodes.get(d) {
                                                    let _ = wipe_node_locked(dn, d_pres);
                                                }
                                                shared_exp_memo.remove(&(d.clone(), false));
                                                shared_exp_memo.remove(&(d.clone(), true));
                                            }
                                        }
                                        if !to_invalidate.is_empty() {
                                            let inv_set: HashSet<&str> =
                                                to_invalidate.iter().map(|s| s.as_str()).collect();
                                            ready_to_evaluate
                                                .retain(|m| !inv_set.contains(m.as_str()));
                                            pending_audit_queue
                                                .retain(|m| !inv_set.contains(m.as_str()));
                                        }
                                        for (m_name, &vdeg) in &in_degree {
                                            if !completed_mods.contains(m_name) {
                                                let mut sdeg = vdeg;
                                                for sp in &spec_unlocked {
                                                    if !completed_mods.contains(sp)
                                                        && dependents
                                                            .get(sp)
                                                            .is_some_and(|l| l.contains(m_name))
                                                    {
                                                        sdeg = sdeg.saturating_sub(1);
                                                    }
                                                }
                                                spec_in_degree.insert(m_name.clone(), sdeg);
                                            }
                                        }
                                    }
                                    record_scheduler_test_event(
                                        "warm_fallback_to_compile",
                                        std::slice::from_ref(&mod_name),
                                    );
                                    wipe_node_locked(node, preserve_lake)?;
                                    shared_exp_memo.remove(&(mod_name.clone(), false));
                                    shared_exp_memo.remove(&(mod_name.clone(), true));
                                    replay_batch.invalidate_memo();
                                    let prio = b_levels.get(&mod_name).copied().unwrap_or(1);
                                    compile_keys.insert(mod_name.clone(), mod_key);
                                    ready_compile_heap.push((prio, Reverse(mod_name.clone())));
                                    return Ok(None);
                                }
                                if !preserve_lake && !node.needs_c {
                                    let c_hash_path =
                                        PathBuf::from(format!("{}.hash", node.c_path.display()));
                                    if fs::symlink_metadata(&node.c_path).is_ok()
                                        || fs::symlink_metadata(&c_hash_path).is_ok()
                                    {
                                        let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
                                        let _guard = lock.lock().map_err(|_| {
                                            anyhow::anyhow!(
                                                "Module artifact publication mutex poisoned"
                                            )
                                        })?;
                                        let _flock_guard =
                                            acquire_publish_flock(&node.pkg_root, false)?;
                                        let _ = fs::remove_file(&node.c_path);
                                        let _ = fs::remove_file(&c_hash_path);
                                    }
                                }
                                let existing_log = read_existing_trace_log(node);
                                if !json_output && !existing_log.is_empty() {
                                    let formatted = format_lake_trace_log_stdout(&existing_log);
                                    if !formatted.trim().is_empty() {
                                        print!("{}", formatted);
                                    }
                                }
                                if emit_lake_sidecars && !preserve_lake {
                                    write_lake_module_hashes_and_trace_with_memo(
                                        &cfg,
                                        &dag,
                                        node,
                                        &dig,
                                        Some(&dig),
                                        true,
                                        &existing_log,
                                        &mut shared_exp_memo,
                                    )?;
                                    record_verified_dep_source_cached(
                                        &cfg,
                                        &dag,
                                        node,
                                        tainted_elab_host_effect_mods.contains(&mod_name),
                                        &dig,
                                        node.is_root_pkg,
                                        &olean_digests,
                                        &tier_digests,
                                        &mut verified_manifest_cache,
                                        true,
                                        cached_ws_inputs_digest.as_deref(),
                                    );
                                    write_file_atomic(
                                        &module_setup_json_path(node),
                                        &serde_json::to_vec(&build_setup_json(
                                            &cfg, &dag, node, None, None,
                                        )?)?,
                                    )?;
                                }
                                report.modules_up_to_date_reused += 1;
                                let warm_cas_store_opt = (!tainted_elab_host_effect_mods
                                    .contains(&mod_name))
                                .then(|| {
                                    fs::read_to_string(&node.src_path)
                                        .ok()
                                        .filter(|s| {
                                            !node_source_has_disallowed_elab_host_effects(
                                                &cfg, node, s,
                                            )
                                        })
                                        .map(|_| (mod_key, 0, existing_log))
                                })
                                .flatten();
                                Ok(Some((dig, warm_cas_store_opt)))
                            })(
                            ),
                            PendingAuditOrigin::Compiled {
                                dig,
                                mod_key,
                                dur_ms,
                                stdout_str,
                            } => (|| {
                                if let Err(audit_err) = mod_audit_res {
                                    wipe_node_locked(node, preserve_lake)?;
                                    return Err(audit_err);
                                }
                                let post_audit_dig = compute_olean_artifact_set_digest_with_policy(
                                    &node.olean_path,
                                    preserve_lake,
                                )?;
                                if post_audit_dig != dig || !snap_matches_dig(&dig) {
                                    wipe_node_locked(node, preserve_lake)?;
                                    anyhow::bail!(
                                            "Artifact digest mutated during `.olean` kernel audit for `{}`",
                                            mod_name
                                        );
                                }
                                let (trace_log, formatted_stdout) =
                                    parse_lean_diagnostics_for_lake(&cfg, node, &stdout_str);
                                if !json_output && !formatted_stdout.trim().is_empty() {
                                    print!("{}", formatted_stdout);
                                }
                                if emit_lake_sidecars && !preserve_lake {
                                    write_lake_module_hashes_and_trace_with_memo(
                                        &cfg,
                                        &dag,
                                        node,
                                        &dig,
                                        Some(&post_audit_dig),
                                        true,
                                        &trace_log,
                                        &mut shared_exp_memo,
                                    )?;
                                    if !is_untrusted {
                                        record_verified_dep_source_cached(
                                            &cfg,
                                            &dag,
                                            node,
                                            tainted_elab_host_effect_mods.contains(&mod_name),
                                            &dig,
                                            node.is_root_pkg,
                                            &olean_digests,
                                            &tier_digests,
                                            &mut verified_manifest_cache,
                                            true,
                                            cached_ws_inputs_digest.as_deref(),
                                        );
                                    }
                                }
                                report.modules_compiled += 1;
                                report.compiled_modules.push(mod_name.clone());
                                let cas_store_opt = (!tainted_elab_host_effect_mods
                                    .contains(&mod_name))
                                .then(|| {
                                    fs::read_to_string(&node.src_path)
                                        .ok()
                                        .filter(|s| {
                                            !node_source_has_disallowed_elab_host_effects(
                                                &cfg, node, s,
                                            )
                                        })
                                        .map(|_| (mod_key, dur_ms, trace_log))
                                })
                                .flatten();
                                Ok(Some((dig, cas_store_opt)))
                            })(),
                        };

                        match step_res {
                            Ok(Some((accepted_dig, cas_req_opt))) => {
                                if !is_untrusted {
                                    if let Some(ModuleAuditAuthority::Snapshot((
                                        ref snap,
                                        record_rep,
                                        record_aud,
                                    ))) = snap_auth_opt
                                    {
                                        if record_rep || record_aud {
                                            let ptr = std::sync::Arc::as_ptr(snap) as usize;
                                            let entry_idx = pending_snap_records
                                                .iter()
                                                .position(|(p, _, _, _)| *p == ptr)
                                                .unwrap_or_else(|| {
                                                    let idx = pending_snap_records.len();
                                                    pending_snap_records.push((
                                                        ptr,
                                                        std::sync::Arc::clone(snap),
                                                        Vec::new(),
                                                        Vec::new(),
                                                    ));
                                                    idx
                                                });
                                            if record_rep {
                                                pending_snap_records[entry_idx]
                                                    .2
                                                    .push(mod_name.clone());
                                            }
                                            if record_aud {
                                                pending_snap_records[entry_idx]
                                                    .3
                                                    .push(mod_name.clone());
                                            }
                                        }
                                    }
                                }
                                if let Some((cas_key, cas_dur_ms, cas_trace_log)) = cas_req_opt {
                                    match read_consistent_module_cas_blobs_locked(&canon_dir, node)
                                    {
                                        Ok(mut raw_items) => {
                                            if !cas_trace_log.is_empty() {
                                                match serde_json::to_vec(&cas_trace_log) {
                                                    Ok(log_bytes) => {
                                                        let sz = log_bytes.len() as u64;
                                                        raw_items.push((
                                                            String::new(),
                                                            log_bytes,
                                                            "trace_log".to_string(),
                                                            "thm:trace_log".to_string(),
                                                            sz,
                                                        ));
                                                    }
                                                    Err(e) => {
                                                        fatal_err = Some(e.into());
                                                        break;
                                                    }
                                                }
                                            }
                                            if cas_tx
                                                .send(CasHashJob {
                                                    mod_name: mod_name.clone(),
                                                    mod_key: cas_key,
                                                    dur_ms: cas_dur_ms,
                                                    raw_items,
                                                })
                                                .is_ok()
                                            {
                                                in_flight_cas += 1;
                                            } else {
                                                fatal_err = Some(anyhow::anyhow!(
                                                    "Background CAS hashing worker terminated unexpectedly"
                                                ));
                                                break;
                                            }
                                        }
                                        Err(e) => {
                                            fatal_err = Some(e);
                                            break;
                                        }
                                    }
                                }
                                let accepted_tiers =
                                    match compute_module_artifact_tier_digests_with_policy(
                                        &node.olean_path,
                                        preserve_lake,
                                    ) {
                                        Ok(td) if td.full == accepted_dig => td,
                                        Ok(_) => {
                                            fatal_err = Some(anyhow::anyhow!(
                                                "Artifact tier digest mismatch after audit for `{}`",
                                                mod_name
                                            ));
                                            break;
                                        }
                                        Err(e) => {
                                            fatal_err = Some(e);
                                            break;
                                        }
                                    };
                                olean_digests.insert(mod_name.clone(), accepted_dig.clone());
                                probe_olean_digests.insert(mod_name.clone(), accepted_dig);
                                tier_digests.insert(mod_name.clone(), accepted_tiers.clone());
                                probe_tier_digests.insert(mod_name.clone(), accepted_tiers);
                                let was_spec = spec_unlocked.remove(&mod_name);
                                completed_mods.insert(mod_name.clone());
                                record_scheduler_test_event(
                                    "module_accepted",
                                    std::slice::from_ref(&mod_name),
                                );
                                if !is_untrusted && emit_lake_sidecars {
                                    if let Err(e) = build_wave_native_artifacts(
                                        &cfg,
                                        &dag,
                                        &canon_dir,
                                        std::slice::from_ref(&mod_name),
                                        preserve_project,
                                        &completed_mods,
                                        &mut built_shared_libs,
                                    ) {
                                        fatal_err = Some(e);
                                        break;
                                    }
                                    record_scheduler_test_event(
                                        "native_artifacts_ready",
                                        std::slice::from_ref(&mod_name),
                                    );
                                }
                                if let Some(deps) = dependents.get(&mod_name) {
                                    for dep_child in deps {
                                        if !was_spec {
                                            if let Some(sdeg) = spec_in_degree.get_mut(dep_child) {
                                                *sdeg = sdeg.saturating_sub(1);
                                            }
                                        }
                                        if let Some(deg) = in_degree.get_mut(dep_child) {
                                            *deg = deg.saturating_sub(1);
                                            if *deg == 0 {
                                                parked_for_compile.remove(dep_child);
                                                if let Some(wait_res) =
                                                    audited_waiting_ancestors.remove(dep_child)
                                                {
                                                    finalize_queue
                                                        .push_back((dep_child.clone(), wait_res));
                                                } else if !evaluated_mods.contains(dep_child) {
                                                    ready_to_evaluate.push_back(dep_child.clone());
                                                }
                                            } else if spec_in_degree
                                                .get(dep_child)
                                                .copied()
                                                .unwrap_or(1)
                                                == 0
                                                && !evaluated_mods.contains(dep_child)
                                                && !parked_for_compile.contains(dep_child)
                                            {
                                                let child_ok =
                                                    dag.nodes.get(dep_child).is_some_and(|cn| {
                                                        compute_module_raw_import_dynlibs(&dag, cn)
                                                            .iter()
                                                            .all(|dp| dp.is_file())
                                                    });
                                                if child_ok {
                                                    ready_to_evaluate.push_back(dep_child.clone());
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            Ok(None) => {}
                            Err(e) => {
                                fatal_err = Some(e);
                                break;
                            }
                        }
                    }
                    if fatal_err.is_none() && !pending_snap_records.is_empty() {
                        for (_, snap, rep_mods, aud_mods) in pending_snap_records {
                            if let Err(e) = crate::zygote::record_snapshot_modules_in_store(
                                store,
                                &cfg,
                                &snap,
                                &rep_mods,
                                &aud_mods,
                                &lean_path_env,
                                None,
                            ) {
                                fatal_err = Some(e);
                                break;
                            }
                        }
                        replay_batch.invalidate_memo();
                    }
                }
                SchedulerEvent::CasHashFinished {
                    mod_name,
                    mod_key,
                    dur_ms,
                    res,
                } => {
                    in_flight_cas = in_flight_cas.saturating_sub(1);
                    if fatal_err.is_some() {
                        continue;
                    }
                    match res {
                        Ok(hashed_items) => {
                            if let Err(e) = commit_staged_module_cas_entry(
                                store,
                                &mod_key,
                                &cfg.toolchain,
                                trust_domain,
                                pin_level,
                                dur_ms,
                                hashed_items,
                            ) {
                                fatal_err = Some(e);
                            } else if !is_untrusted && trust_domain == "trusted" {
                                if let Some(ref rem_url) = remote_cache_url {
                                    let replay_dig = dag.nodes.get(&mod_name).and_then(|n| {
                                        compute_replayed_olean_ilean_digest(&n.olean_path).ok()
                                    });
                                    let _ = crate::pack::try_push_remote_module_action(
                                        store,
                                        rem_url,
                                        remote_cache_token.as_deref(),
                                        &mut remote_manifest_cache,
                                        &mod_key,
                                        &mod_name,
                                        replay_dig.as_deref(),
                                        trust_domain,
                                        is_untrusted,
                                    );
                                }
                            }
                        }
                        Err(e) => {
                            fatal_err = Some(e);
                        }
                    }
                }
            }
        }

        compile_shutdown.store(true, Ordering::SeqCst);
        compile_work_cv.notify_all();
        audit_shutdown.store(true, Ordering::SeqCst);
        audit_work_cv.notify_all();
        drop(result_tx);
        drop(cas_tx);

        flush_all_verified_dep_manifests(&mut verified_manifest_cache);

        if let Some(err) = fatal_err {
            return Err(err);
        }
        if completed_mods.len() != dag.nodes.len() {
            anyhow::bail!(
                "Native module scheduler terminated before completing all DAG modules ({} of {} accepted)",
                completed_mods.len(),
                dag.nodes.len()
            );
        }
        Ok(())
    });

    let sched_ms = t_sched.elapsed().as_millis();
    if let Err(err) = scheduler_res {
        wipe_unverified_candidates(&pending_audit_meta);
        return Err(err);
    }
    let t_staged_paths = std::time::Instant::now();
    if !targets.is_empty() && emit_lake_sidecars {
        let mut staged = Vec::new();
        let mut seen_manifests = HashSet::new();
        for node in dag.nodes.values() {
            if !node.pkg_root.starts_with(&canon_dir) {
                continue;
            }
            let srv_path = PathBuf::from(format!("{}.server", node.olean_path.display()));
            let priv_path = PathBuf::from(format!("{}.private", node.olean_path.display()));
            let ir_path = node.olean_path.with_extension("ir");
            let ir_sig_path = PathBuf::from(format!("{}.sig", ir_path.display()));
            for p in [
                &node.olean_path,
                &node.ilean_path,
                &srv_path,
                &priv_path,
                &ir_path,
                &ir_sig_path,
            ] {
                staged.push(p.clone());
                staged.push(PathBuf::from(format!("{}.hash", p.display())));
            }
            if node.needs_c || node.c_path.is_file() {
                staged.push(node.c_path.clone());
                staged.push(PathBuf::from(format!("{}.hash", node.c_path.display())));
                let c_o_exp = PathBuf::from(format!("{}.o.export", node.c_path.display()));
                if c_o_exp.is_file() {
                    staged.push(PathBuf::from(format!("{}.hash", c_o_exp.display())));
                    staged.push(PathBuf::from(format!("{}.trace", c_o_exp.display())));
                    staged.push(c_o_exp);
                }
            }
            if let Some(so_p) = module_dynlib_so_path(node) {
                if so_p.is_file() {
                    staged.push(PathBuf::from(format!("{}.hash", so_p.display())));
                    staged.push(so_p.with_extension("trace"));
                    staged.push(so_p);
                }
            }
            staged.push(node.olean_path.with_extension("trace"));
            let setup_p = module_setup_json_path(node);
            if setup_p.is_file() {
                staged.push(setup_p);
            }
            if seen_manifests.insert(node.pkg_root.clone()) {
                staged.push(
                    node.pkg_root
                        .join(".lake/build/.turbo_verified_sources.json"),
                );
            }
        }
        for sl in &dag.shared_libs {
            if sl.path.starts_with(&canon_dir) && sl.path.is_file() {
                staged.push(PathBuf::from(format!("{}.hash", sl.path.display())));
                staged.push(sl.path.with_extension("trace"));
                staged.push(sl.path.clone());
            }
        }
        report.staged_target_paths = staged;
    }

    let topo_rank: HashMap<&str, usize> = dag
        .topological_order
        .iter()
        .enumerate()
        .map(|(idx, m)| (m.as_str(), idx))
        .collect();
    report
        .compiled_modules
        .sort_by_key(|m| topo_rank.get(m.as_str()).copied().unwrap_or(usize::MAX));
    report
        .cached_modules
        .sort_by_key(|m| topo_rank.get(m.as_str()).copied().unwrap_or(usize::MAX));
    validate_materialized_artifacts(&cfg)?;
    if profile_phases {
        eprintln!(
            "[turbo-lean][profile] module_builder: cfg={}ms dag={}ms ext_digests={}ms ext_replay={}ms(n={}) scheduler={}ms staged_paths={}ms total={}ms (dag_nodes={} unique_ext={} compiled={} cached={})",
            cfg_ms,
            dag_ms,
            ext_digests_ms,
            ext_replay_ms,
            unverified_ext_count,
            sched_ms,
            t_staged_paths.elapsed().as_millis(),
            t_total.elapsed().as_millis(),
            dag.nodes.len(),
            olean_digests.len(),
            report.modules_compiled,
            report.modules_cached
        );
    }
    Ok(report)
}

pub(super) fn compute_cas_outputs_artifact_and_replay_digests(
    outputs: &[BlobEntry],
) -> Option<(ModuleArtifactTierDigests, String)> {
    let find_hash = |suffix: &str| -> Option<&str> {
        outputs
            .iter()
            .find(|e| {
                e.rel_path == suffix.trim_start_matches('/')
                    || e.rel_path.ends_with(suffix)
                    || e.rel_path.ends_with(&suffix.replace('/', "\\"))
            })
            .map(|e| e.blob_hash.as_str())
    };
    let olean_hex = find_hash(".olean")?;
    let srv_hex = find_hash(".olean.server");
    let priv_hex = find_hash(".olean.private");
    let ilean_hex = find_hash(".ilean");
    let ir_hex = find_hash(".ir");
    let ir_sig_hex = find_hash(".ir.sig");

    let fold_tier = |domain: &[u8], items: &[(&str, Option<&str>)]| -> Option<String> {
        let mut h = blake3::Hasher::new();
        h.update(domain);
        for &(tag, hex_opt) in items {
            let present = hex_opt.is_some();
            if tag != "olean" {
                h.update(&[u8::from(present)]);
            }
            if let Some(hex_str) = hex_opt {
                let raw_hash = crate::pack::decode_hex_fixed::<32>(hex_str).ok()?;
                update_lp(&mut h, tag.as_bytes(), &raw_hash);
            } else {
                update_lp(&mut h, tag.as_bytes(), b"");
            }
        }
        Some(h.finalize().to_hex().to_string())
    };

    let full = fold_tier(
        b"olean-art-v2\n",
        &[
            ("olean", Some(olean_hex)),
            ("srv", srv_hex),
            ("priv", priv_hex),
            ("ilean", ilean_hex),
            ("ir", ir_hex),
            ("ir_sig", ir_sig_hex),
        ],
    )?;
    let dep_export = fold_tier(
        b"olean-export-v2\n",
        &[
            ("olean", Some(olean_hex)),
            ("ir", ir_hex),
            ("ir_sig", ir_sig_hex),
        ],
    )?;
    let dep_meta = fold_tier(
        b"olean-meta-v1\n",
        &[
            ("olean", Some(olean_hex)),
            ("ir", ir_hex),
            ("ir_sig", ir_sig_hex),
        ],
    )?;

    let mut rep_h = blake3::Hasher::new();
    rep_h.update(b"turbo-lean-replayed-olean-ilean-v1\n");
    for (tag, hex_opt) in [
        ("olean", Some(olean_hex)),
        ("ilean", ilean_hex),
        ("srv", srv_hex),
        ("priv", priv_hex),
    ] {
        let present = hex_opt.is_some();
        rep_h.update(&[u8::from(present)]);
        if let Some(hex_str) = hex_opt {
            let raw_hash = crate::pack::decode_hex_fixed::<32>(hex_str).ok()?;
            update_lp(&mut rep_h, tag.as_bytes(), &raw_hash);
        } else {
            update_lp(&mut rep_h, tag.as_bytes(), b"");
        }
    }

    Some((
        ModuleArtifactTierDigests {
            full,
            dep_export,
            dep_meta,
        },
        rep_h.finalize().to_hex().to_string(),
    ))
}

pub fn build_cone_export_filter(
    store: &TurboStore,
    project_dir: &Path,
    cone_target: &str,
) -> Result<crate::pack::ExportInclusionFilter> {
    let target = cone_target.trim();
    anyhow::ensure!(
        !target.is_empty(),
        "`--cone` target must be a non-empty module or library name"
    );
    let canon_dir = project_dir
        .canonicalize()
        .unwrap_or_else(|_| project_dir.to_path_buf());
    let cfg = resolve_project_config_with_trust(&canon_dir, false)?;
    // Use `is_untrusted = true` solely during cone DAG expansion so dependency-package
    // modules with fresh `.olean`s on disk are expanded as explicit `ModuleNode`s in
    // `dag.topological_order` (rather than pruned into `external_olean_deps`), ensuring
    // `--cone <Target>` exports portable `module_unit` actions for a cold destination machine.
    let dag = build_module_dag_with_trust(&cfg, &[target.to_string()], true)?;
    let preserve_project = crate::lake_build::worktree_auto_link_disabled(&canon_dir);

    let mut tier_digests: HashMap<String, ModuleArtifactTierDigests> = HashMap::new();
    let mut allowed_actions: HashSet<String> = HashSet::new();
    let mut allowed_replay_modules: HashSet<String> = HashSet::new();
    let mut allowed_replay_artifact_digests: HashSet<String> = HashSet::new();

    for node in dag.nodes.values() {
        allowed_replay_modules.insert(node.module_name.clone());
        for (ext_mod, ext_path) in &node.external_olean_deps {
            allowed_replay_modules.insert(ext_mod.clone());
            if !tier_digests.contains_key(ext_mod) {
                let preserve_ext = preserve_project || !ext_path.starts_with(&canon_dir);
                if let Ok(td) =
                    compute_module_artifact_tier_digests_with_policy(ext_path, preserve_ext)
                {
                    tier_digests.insert(ext_mod.clone(), td);
                }
                if let Ok(rd) = compute_replayed_olean_ilean_digest(ext_path) {
                    allowed_replay_artifact_digests.insert(rd);
                }
            }
        }
    }

    let tainted_elab_host_effect_mods = compute_tainted_elab_host_effect_modules(&cfg, &dag);
    for mod_name in &dag.topological_order {
        let Some(node) = dag.nodes.get(mod_name) else {
            continue;
        };
        let preserve_node =
            preserve_project || package_is_read_only(&canon_dir, &node.pkg_root);
        let Ok((dep_digests_vec, _, dynlib_digests)) =
            gather_module_dep_digests_and_dynlibs(&cfg, &dag, node, &tier_digests)
        else {
            if let Ok(disk_td) =
                compute_module_artifact_tier_digests_with_policy(&node.olean_path, preserve_node)
            {
                tier_digests.insert(mod_name.clone(), disk_td);
            }
            if let Ok(rd) = compute_replayed_olean_ilean_digest(&node.olean_path) {
                allowed_replay_artifact_digests.insert(rd);
            }
            continue;
        };
        let key_no_c = compute_module_cas_key_with_dynlibs(
            &cfg,
            node,
            &dep_digests_vec,
            false,
            &dynlib_digests,
        )?;
        let key_with_c = compute_module_cas_key_with_dynlibs(
            &cfg,
            node,
            &dep_digests_vec,
            true,
            &dynlib_digests,
        )?;
        let mut resolved_tiers: Option<ModuleArtifactTierDigests> = None;
        if !tainted_elab_host_effect_mods.contains(mod_name) {
            for cand_key in [&key_no_c, &key_with_c] {
                if let Ok(Some(outputs)) = store.get_cached_action(cand_key, "trusted") {
                    allowed_actions.insert(cand_key.clone());
                    if let Some((art_tiers, rep_dig)) =
                        compute_cas_outputs_artifact_and_replay_digests(&outputs)
                    {
                        let preferred_key = if node.needs_c { &key_with_c } else { &key_no_c };
                        if resolved_tiers.is_none() || cand_key == preferred_key {
                            resolved_tiers = Some(art_tiers);
                        }
                        allowed_replay_artifact_digests.insert(rep_dig);
                    }
                }
            }
        }
        if resolved_tiers.is_none() {
            if let Ok(disk_td) =
                compute_module_artifact_tier_digests_with_policy(&node.olean_path, preserve_node)
            {
                resolved_tiers = Some(disk_td);
            }
        }
        if let Ok(rd) = compute_replayed_olean_ilean_digest(&node.olean_path) {
            allowed_replay_artifact_digests.insert(rd);
        }
        if let Some(td) = resolved_tiers {
            tier_digests.insert(mod_name.clone(), td);
        }
    }

    Ok(crate::pack::ExportInclusionFilter {
        allowed_actions: Some(allowed_actions),
        allowed_replay_modules: Some(allowed_replay_modules),
        allowed_replay_artifact_digests: Some(allowed_replay_artifact_digests),
    })
}
