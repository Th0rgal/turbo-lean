use super::*;

#[derive(Debug, Clone, Serialize, Deserialize, Default, PartialEq, Eq)]
pub(crate) struct VerifiedDepModuleEntry {
    pub src_blake3: String,
    pub olean_artifact_digest: String,
    /// [`workspace_lake_inputs_digest`] when *this* entry was recorded.
    ///
    /// The manifest-level field says what the header was last stamped with, which is not the same
    /// claim: a writer that re-stamps the header while keeping entries it did not rebuild would
    /// promote them to "fresh" wholesale. Restating it per entry makes each entry answer for
    /// itself, so a reader never has to trust that the two agree.
    #[serde(default)]
    pub lake_inputs_digest: String,
    #[serde(default)]
    pub kernel_audited: bool,
    /// Artifact-set digests of the direct imports this `.olean` was elaborated against.
    /// Deliberately not `#[serde(default)]`: legacy entries without it fail closed.
    pub import_olean_digests: BTreeMap<String, String>,
    /// Export-tier (`.olean` + `.ir` + `.ir.sig`) digests of direct `module` imports when recorded.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub import_export_digests: BTreeMap<String, String>,
    /// Meta-tier (`.olean` + `.ir` + `.ir.sig`) digests of direct `module` imports when recorded.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub import_meta_digests: BTreeMap<String, String>,
    /// Export-tier digest of this module's own artifacts when `is_module == true`.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub olean_export_digest: String,
    /// Meta-tier digest of this module's own artifacts when `is_module == true`.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub olean_meta_digest: String,
    /// `olean_artifact_stat_fingerprint` when recorded (empty: always re-hash on use).
    #[serde(default)]
    pub artifact_stat_fingerprint: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub(crate) struct VerifiedDepManifest {
    pub pkg_name: String,
    pub toolchain: String,
    pub lean_githash: String,
    pub pkg_config_digest: String,
    /// [`workspace_lake_inputs_digest`] at the time the entries were recorded. `pkg_config_digest`
    /// deliberately excludes input *contents*, so without this every consumer of the manifest
    /// would accept `.olean` files elaborated against stale `input_dir` / `input_file` bytes.
    #[serde(default)]
    pub lake_inputs_digest: String,
    #[serde(default)]
    pub workspace_config_digest: String,
    #[serde(default)]
    pub allowed_axioms: Vec<String>,
    #[serde(default)]
    pub kernel_policy_digest: String,
    pub modules: BTreeMap<String, VerifiedDepModuleEntry>,
    /// Workspace configuration the manifest was validated against on load (never serialized).
    #[serde(skip)]
    pub cfg: Option<ProjectConfig>,
    /// Dependency-closure nodes `(package, module, pin)` already found consistent (never
    /// serialized).
    #[serde(skip)]
    pub dep_import_memo: DepImportMemo,
}

#[derive(Debug, Default)]
pub(crate) struct DepImportMemo(pub(super) Mutex<HashSet<(PathBuf, String, String)>>);

impl Clone for DepImportMemo {
    fn clone(&self) -> Self {
        Self::default()
    }
}

pub(crate) struct CachedPkgManifest {
    pub(crate) raw: Option<Result<VerifiedDepManifest, ()>>,
    pub(crate) validated: Option<VerifiedDepManifest>,
}

#[derive(Clone)]
pub(crate) struct CutoffPinBaseline {
    pub(crate) full_dig: String,
    pub(crate) export_dig: String,
    pub(crate) meta_dig: String,
    pub(crate) cuts_off_public: bool,
    pub(crate) cuts_off_meta: bool,
}

pub(crate) fn source_uses_include_str(src_raw: &str) -> bool {
    let comment_free = crate::splitter::strip_lean_comments(src_raw);
    let clean = crate::splitter::strip_string_literals(&comment_free);
    let unquoted = clean.replace(['«', '»'], "");
    ["include_str", "include_str?", "include_bin", "include_bin?"]
        .iter()
        .any(|seg| crate::splitter::contains_lean_ident_segment(&unquoted, seg))
}

pub(crate) fn module_directly_depends_on_lake_inputs(
    cfg: &ProjectConfig,
    _pkg_root: &Path,
    mod_name: &str,
    src_raw: &str,
) -> bool {
    !input_bearing_libs_for_module(cfg, mod_name).is_empty()
        || !input_bearing_exes_for_module(cfg, mod_name).is_empty()
        || source_uses_include_str(src_raw)
}

/// `--frozen-cone` (#339): trust a pre-materialized (hardlinked / CAS-restored) dependency cone.
///
/// A cone minted by `import` + `worktree-dedup` hardlinks artifacts that keep the pack's original
/// mtimes, while a fresh checkout or a `git` operation stamps sources and lakefiles newer, so the
/// raw `olean.mtime < source.mtime` staleness tests misclassify byte-identical artifacts as
/// stale. With this set, the mtime-skew gates stand down and freshness rests entirely on the
/// content-hash verification backing the verified-sources manifest (`src_blake3`,
/// `olean_artifact_digest`, per-edge `import_olean_digests` pins).
pub(crate) const FROZEN_CONE_ENV: &str = "TURBO_LEAN_FROZEN_CONE";

pub(crate) fn frozen_cone_enabled() -> bool {
    crate::shm_cache::parse_relaxed_bool(&std::env::var(FROZEN_CONE_ENV).unwrap_or_default())
        == Some(true)
}

#[derive(Default)]
pub(crate) struct LakeClosureCache {
    pub(super) manifests: HashMap<(PathBuf, bool), CachedPkgManifest>,
    pub(super) exp_memo: HashMap<(PathBuf, String, bool, bool), Option<LakeModuleExportInfo>>,
    pub(super) pb_exp_memo: HashMap<(PathBuf, bool, bool), Option<LakeModuleExportInfo>>,
    pub(super) pinned_memo: HashSet<(PathBuf, String, String, bool, bool)>,
    pub(super) cutoff_pins: HashMap<(PathBuf, String), CutoffPinBaseline>,
    pub(super) clean_git_pin_memo: HashMap<PathBuf, bool>,
    pub(super) input_dep_memo: HashMap<(PathBuf, String), bool>,
    pub(crate) post_lake_refresh: bool,
    pub(crate) ignore_mtime_skew: bool,
    pub(crate) allow_stale_manifest_hydration: bool,
}

impl LakeClosureCache {
    pub(crate) fn for_project(cfg: &ProjectConfig) -> Self {
        Self {
            ignore_mtime_skew: frozen_cone_enabled()
                || !crate::lake_build::worktree_auto_link_disabled(&cfg.root_pkg.pkg_root),
            ..Default::default()
        }
    }

    pub(crate) fn seed_module_export_info(
        &mut self,
        pkg_root: PathBuf,
        module_name: String,
        strict_policy: bool,
        info: LakeModuleExportInfo,
    ) {
        self.exp_memo.insert(
            (pkg_root.clone(), module_name.clone(), strict_policy, false),
            Some(info),
        );
        self.exp_memo
            .insert((pkg_root, module_name, strict_policy, true), Some(info));
    }

    pub(crate) fn seed_cutoff_module_pin(
        &mut self,
        pkg_root: PathBuf,
        module_name: String,
        baseline: CutoffPinBaseline,
    ) {
        self.cutoff_pins.insert((pkg_root, module_name), baseline);
    }

    pub(crate) fn matches_cutoff_pin(
        &self,
        pkg_root: &Path,
        module_name: &str,
        req: &ImportPinSpec<'_>,
    ) -> Option<bool> {
        let base = self
            .cutoff_pins
            .get(&(pkg_root.to_path_buf(), module_name.to_string()))?;
        let ok = match req.tier_pin {
            Some((DepImportVisibility::PublicExport, exp)) => {
                base.cuts_off_public
                    && !exp.is_empty()
                    && (exp == base.export_dig || req.full_pin == base.full_dig)
            }
            Some((DepImportVisibility::MetaExport, meta)) => {
                base.cuts_off_meta
                    && !meta.is_empty()
                    && (meta == base.meta_dig || req.full_pin == base.full_dig)
            }
            _ => false,
        };
        Some(ok)
    }

    pub(crate) fn allows_cutoff_parsed_import(
        &self,
        pkg_root: &Path,
        module_name: &str,
        is_importer_module: bool,
        sub_imp: &ParsedImport,
    ) -> Option<bool> {
        let base = self
            .cutoff_pins
            .get(&(pkg_root.to_path_buf(), module_name.to_string()))?;
        if !is_importer_module || sub_imp.import_all {
            return Some(false);
        }
        Some(if sub_imp.is_meta {
            base.cuts_off_meta
        } else {
            base.cuts_off_public
        })
    }

    pub(crate) fn load_pkg_manifest<'a>(
        &'a mut self,
        cfg: &ProjectConfig,
        spec: &DiscoveredModuleSpec,
        strict_policy: bool,
    ) -> Option<&'a CachedPkgManifest> {
        load_cached_pkg_manifest(&mut self.manifests, cfg, spec, strict_policy)
    }

    pub(crate) fn insert_pre_pkg_manifest(
        &mut self,
        pkg_root: PathBuf,
        strict_policy: bool,
        raw: Option<Result<VerifiedDepManifest, ()>>,
        validated: Option<VerifiedDepManifest>,
    ) {
        self.manifests.insert(
            (pkg_root, strict_policy),
            CachedPkgManifest { raw, validated },
        );
    }

    pub(crate) fn module_closure_depends_on_lake_inputs(
        &mut self,
        cfg: &ProjectConfig,
        spec: &DiscoveredModuleSpec,
    ) -> bool {
        let mut visiting = HashSet::new();
        self.module_closure_depends_on_lake_inputs_inner(cfg, spec, &mut visiting)
    }

    pub(super) fn module_closure_depends_on_lake_inputs_inner(
        &mut self,
        cfg: &ProjectConfig,
        spec: &DiscoveredModuleSpec,
        visiting: &mut HashSet<(PathBuf, String)>,
    ) -> bool {
        let key = (spec.pkg_root.clone(), spec.module_name.clone());
        if let Some(&cached) = self.input_dep_memo.get(&key) {
            return cached;
        }
        if !visiting.insert(key.clone()) {
            return true;
        }
        let had_cycle_ancestor = visiting.len() > 1;
        let res = (|| -> bool {
            let Ok(src_raw) = fs::read_to_string(&spec.src_path) else {
                return true;
            };
            if module_directly_depends_on_lake_inputs(
                cfg,
                &spec.pkg_root,
                &spec.module_name,
                &src_raw,
            ) {
                return true;
            }
            let hdr = parse_header_info(&src_raw);
            if hdr.header_error.is_some() {
                return true;
            }
            for imp in &hdr.imports {
                let site = match resolve_module_in_package(&cfg.root_pkg, true, imp) {
                    Some(rs) => ImportSite::Module(Box::new(rs)),
                    None => resolve_import_site(cfg, imp),
                };
                match site {
                    ImportSite::Toolchain => {}
                    ImportSite::Module(sub_spec) => {
                        if self
                            .module_closure_depends_on_lake_inputs_inner(cfg, &sub_spec, visiting)
                        {
                            return true;
                        }
                    }
                    ImportSite::Prebuilt(_) | ImportSite::Unresolved => return true,
                }
            }
            false
        })();
        visiting.remove(&key);
        if !res || !had_cycle_ancestor {
            self.input_dep_memo.insert(key, res);
        }
        res
    }
}

pub(super) fn load_cached_pkg_manifest<'a>(
    manifests: &'a mut HashMap<(PathBuf, bool), CachedPkgManifest>,
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
    strict_policy: bool,
) -> Option<&'a CachedPkgManifest> {
    let expected_lake_inputs = workspace_lake_inputs_digest(cfg).ok()?;
    let entry = manifests
        .entry((spec.pkg_root.clone(), strict_policy))
        .or_insert_with(|| {
            let raw = match fs::read(
                spec.pkg_root
                    .join(".lake/build/.turbo_verified_sources.json"),
            ) {
                Ok(bytes) => {
                    Some(serde_json::from_slice::<VerifiedDepManifest>(&bytes).map_err(|_| ()))
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
                Err(_) => Some(Err(())),
            };
            let validated = match raw.as_ref() {
                Some(Ok(m))
                    if m.pkg_name == spec.pkg_name
                        && m.toolchain == cfg.toolchain
                        && m.lean_githash == cfg.lean_githash
                        && m.pkg_config_digest == spec.pkg_config_digest
                        && m.lake_inputs_digest == expected_lake_inputs
                        && (!strict_policy
                            || (m.workspace_config_digest == cfg.canonical_config_digest
                                && m.allowed_axioms == crate::splitter::allowed_axioms()
                                && m.kernel_policy_digest
                                    == crate::splitter::current_kernel_policy_digest())) =>
                {
                    Some(m.clone())
                }
                _ => None,
            };
            CachedPkgManifest { raw, validated }
        });
    if matches!(entry.raw, Some(Err(()))) {
        None
    } else {
        Some(entry)
    }
}

pub(crate) enum ImportSite {
    Module(Box<DiscoveredModuleSpec>),
    Toolchain,
    Prebuilt(PathBuf),
    Unresolved,
}

pub(super) fn trusted_lean_path_dirs(cfg: &ProjectConfig) -> Vec<PathBuf> {
    let tc_opt = (!cfg.toolchain_lib_lean.as_os_str().is_empty())
        .then_some(cfg.toolchain_lib_lean.as_path());
    std::env::var_os("LEAN_PATH")
        .map(|lp| {
            std::env::split_paths(&lp)
                .filter(|p| p.is_dir() && !crate::zygote::is_toolchain_dir_match(p, tc_opt))
                .collect()
        })
        .unwrap_or_default()
}

pub(crate) fn resolve_import_site(cfg: &ProjectConfig, imp: &str) -> ImportSite {
    let mut deps = cfg
        .dep_pkgs
        .iter()
        .filter_map(|dp| resolve_module_in_package(dp, false, imp));
    match (deps.next(), deps.next()) {
        (Some(spec), None) => return ImportSite::Module(Box::new(spec)),
        (Some(_), Some(_)) => return ImportSite::Unresolved,
        _ => {}
    }
    let rel = format!("{}.olean", module_name_to_rel_slash(imp));
    if let Some(pb) = cfg
        .dep_pkgs
        .iter()
        .map(|dp| dp.pkg_root.join(&dp.build_dir).join(&dp.lean_lib_dir))
        .chain(trusted_lean_path_dirs(cfg))
        .map(|d| d.join(&rel))
        .find(|p| {
            p.is_file()
                && !is_verified_toolchain_olean_file(
                    &cfg.toolchain_lib_lean,
                    Some(&cfg.lean_githash),
                    p,
                )
        })
    {
        return ImportSite::Prebuilt(pb);
    }
    if is_builtin_toolchain_module(&cfg.toolchain_lib_lean, Some(&cfg.lean_githash), imp) {
        ImportSite::Toolchain
    } else {
        ImportSite::Unresolved
    }
}

pub(crate) fn spec_olean_path(spec: &DiscoveredModuleSpec) -> PathBuf {
    spec.build_lib_lean_dir.join(format!(
        "{}.olean",
        module_name_to_rel_slash(&spec.module_name)
    ))
}

pub(crate) fn spec_rel_src(spec: &DiscoveredModuleSpec) -> String {
    spec.src_path
        .strip_prefix(&spec.pkg_root)
        .unwrap_or(&spec.src_path)
        .to_string_lossy()
        .replace('\\', "/")
}

/// Required pin for a direct import of a verified module entry:
/// `full_pin` is always present for non-toolchain imports; `tier_pin` is optional
/// `(visibility, expected_tier_digest)` when a `module` importer recorded export/meta tier pins.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ImportPinSpec<'a> {
    pub full_pin: &'a str,
    pub tier_pin: Option<(DepImportVisibility, &'a str)>,
}

/// Aggregate required visibility for each direct import of `hdr`.
pub(crate) fn header_direct_import_visibilities(
    hdr: &HeaderInfo,
) -> HashMap<String, DepImportVisibility> {
    let mut map: HashMap<String, DepImportVisibility> = HashMap::new();
    if !hdr.is_module {
        for imp in &hdr.imports {
            map.insert(imp.clone(), DepImportVisibility::All);
        }
        return map;
    }
    for spec in &hdr.import_specs {
        let vis = if spec.import_all {
            DepImportVisibility::All
        } else if spec.is_meta {
            DepImportVisibility::MetaExport
        } else {
            DepImportVisibility::PublicExport
        };
        map.entry(spec.module.clone())
            .and_modify(|cur| *cur = (*cur).max(vis))
            .or_insert(vis);
    }
    map
}

pub(crate) fn entry_import_pin_spec<'a>(
    entry: &'a VerifiedDepModuleEntry,
    hdr: &HeaderInfo,
    vis_map: &HashMap<String, DepImportVisibility>,
    imp: &str,
) -> Option<ImportPinSpec<'a>> {
    let full_pin = entry.import_olean_digests.get(imp)?.as_str();
    let tier_pin = if hdr.is_module {
        match vis_map
            .get(imp)
            .copied()
            .unwrap_or(DepImportVisibility::All)
        {
            DepImportVisibility::PublicExport => entry
                .import_export_digests
                .get(imp)
                .filter(|s| !s.is_empty())
                .map(|s| (DepImportVisibility::PublicExport, s.as_str())),
            DepImportVisibility::MetaExport => entry
                .import_meta_digests
                .get(imp)
                .filter(|s| !s.is_empty())
                .map(|s| (DepImportVisibility::MetaExport, s.as_str())),
            DepImportVisibility::All => None,
        }
    } else {
        None
    };
    Some(ImportPinSpec { full_pin, tier_pin })
}

/// P0-4: whether `entry`'s `.olean` was elaborated against the current artifacts of its direct
/// imports. `pin_current(import, pin)` judges each import; only toolchain imports may be
/// unpinned, and every pin must name a current import.
pub(crate) fn verified_entry_imports_current(
    entry: &VerifiedDepModuleEntry,
    imports: &[String],
    mut pin_current: impl FnMut(&str, Option<&str>) -> bool,
) -> bool {
    entry
        .import_olean_digests
        .keys()
        .all(|k| imports.contains(k))
        && imports
            .iter()
            .all(|imp| pin_current(imp, entry.import_olean_digests.get(imp).map(String::as_str)))
}

/// Visibility-aware counterpart of [`verified_entry_imports_current`]: when `hdr.is_module`,
/// direct imports at `PublicExport` or `MetaExport` visibility carry their recorded tier pin.
pub(crate) fn verified_entry_imports_current_for_header(
    entry: &VerifiedDepModuleEntry,
    hdr: &HeaderInfo,
    mut pin_current: impl FnMut(&str, Option<ImportPinSpec<'_>>) -> bool,
) -> bool {
    let vis_map = header_direct_import_visibilities(hdr);
    entry
        .import_olean_digests
        .keys()
        .all(|k| hdr.imports.contains(k))
        && entry
            .import_export_digests
            .keys()
            .all(|k| hdr.imports.contains(k))
        && entry
            .import_meta_digests
            .keys()
            .all(|k| hdr.imports.contains(k))
        && hdr
            .imports
            .iter()
            .all(|imp| pin_current(imp, entry_import_pin_spec(entry, hdr, &vis_map, imp)))
}

/// Check-time judgement of an import pinned at `pin` from the root package, resolved as at build
/// time (root package first): prebuilt `.olean`s are re-digested; root- and dependency-package
/// modules must have a consistent closure (`dep_pkg_import_pins_consistent`), memoized per
/// manifest load when `strict_policy` is true.
pub(crate) fn import_pin_current(
    cfg: &ProjectConfig,
    memo: &DepImportMemo,
    imp: &str,
    pin: Option<ImportPinSpec<'_>>,
) -> bool {
    let mut cache = LakeClosureCache::for_project(cfg);
    import_pin_current_with_policy(cfg, memo, &mut cache, imp, pin, true)
}

/// Elaboration-freshness counterpart of `import_pin_current`: accepts mixed turbo + Lake closures
/// (without kernel-audit policy requirements) and never mutates the strict `DepImportMemo`.
pub(crate) fn import_pin_fresh_for_build(
    cfg: &ProjectConfig,
    cache: &mut LakeClosureCache,
    imp: &str,
    pin: Option<ImportPinSpec<'_>>,
) -> bool {
    let non_strict_memo = DepImportMemo::default();
    import_pin_current_with_policy(cfg, &non_strict_memo, cache, imp, pin, false)
}

pub(crate) fn import_pin_current_with_policy(
    cfg: &ProjectConfig,
    memo: &DepImportMemo,
    cache: &mut LakeClosureCache,
    imp: &str,
    pin: Option<ImportPinSpec<'_>>,
    strict_policy: bool,
) -> bool {
    let site = match resolve_module_in_package(&cfg.root_pkg, true, imp) {
        Some(spec) => ImportSite::Module(Box::new(spec)),
        None => resolve_import_site(cfg, imp),
    };
    match (site, pin) {
        (ImportSite::Toolchain, None) => true,
        (ImportSite::Prebuilt(olean), Some(pin_spec)) => {
            olean_digest_is(cfg, &olean, pin_spec.full_pin)
                && prebuilt_olean_export_info(cfg, strict_policy, &olean, cache).is_some()
        }
        (ImportSite::Module(spec), Some(pin_spec)) => {
            dep_pkg_import_pins_consistent(cfg, memo, cache, *spec, pin_spec, strict_policy)
        }
        _ => false,
    }
}

/// Check whether `entry` (whose full artifact set was already verified current at `olean_path`)
/// satisfies `pin_spec` for a module whose current header has `target_is_module`.
pub(super) fn entry_matches_import_pin_spec(
    olean_path: &Path,
    entry: &VerifiedDepModuleEntry,
    target_is_module: bool,
    pin_spec: &ImportPinSpec<'_>,
) -> bool {
    if entry.olean_artifact_digest == pin_spec.full_pin {
        return true;
    }
    if !target_is_module {
        return false;
    }
    let Some((vis, expected_tier)) = pin_spec.tier_pin else {
        return false;
    };
    if expected_tier.is_empty() {
        return false;
    }
    match vis {
        DepImportVisibility::PublicExport => {
            if !entry.olean_export_digest.is_empty() && entry.olean_export_digest != expected_tier {
                return false;
            }
            if !entry.artifact_stat_fingerprint.is_empty() && !entry.olean_export_digest.is_empty()
            {
                return true;
            }
            compute_dep_export_olean_digest_with_policy(olean_path, true)
                .is_ok_and(|d| d == expected_tier)
        }
        DepImportVisibility::MetaExport => {
            if !entry.olean_meta_digest.is_empty() && entry.olean_meta_digest != expected_tier {
                return false;
            }
            if !entry.artifact_stat_fingerprint.is_empty() && !entry.olean_meta_digest.is_empty() {
                return true;
            }
            compute_dep_meta_olean_digest_with_policy(olean_path, true)
                .is_ok_and(|d| d == expected_tier)
        }
        DepImportVisibility::All => false,
    }
}

/// Whether `olean`'s artifact set digests to `pin`, read-only (never creating `.turbo_publish.lock`).
pub(crate) fn olean_digest_is(_cfg: &ProjectConfig, olean: &Path, pin: &str) -> bool {
    compute_olean_artifact_set_digest_with_policy(olean, true).is_ok_and(|d| d == pin)
}

/// Device/inode/size/mtime/ctime fingerprint of an `.olean` artifact set, returned only when
/// every present artifact is a non-symlink regular file on a subsecond-timestamp filesystem
/// whose `ctime` already predates `now_ns - STAT_TRUST_WINDOW_NS`.
pub(super) fn olean_artifact_stat_fingerprint_for_store(olean: &Path) -> Option<String> {
    #[cfg(unix)]
    {
        let now_ns = crate::zygote::wall_clock_ns();
        let mut h = blake3::Hasher::new();
        for (tag, path) in olean_artifact_paths(olean) {
            h.update(tag.as_bytes());
            match fs::symlink_metadata(&path) {
                Ok(m) if !m.file_type().is_symlink() && m.is_file() => {
                    let sig = crate::zygote::OleanFileStatSig::from_meta(&m);
                    if !olean_stat_sig_trusted_at(&sig, now_ns) {
                        return None;
                    }
                    h.update(&sig.dev.to_le_bytes());
                    h.update(&sig.ino.to_le_bytes());
                    h.update(&sig.size.to_le_bytes());
                    h.update(&sig.mtime_sec.to_le_bytes());
                    h.update(&sig.mtime_nsec.to_le_bytes());
                    h.update(&sig.ctime_sec.to_le_bytes());
                    h.update(&sig.ctime_nsec.to_le_bytes());
                }
                Ok(_) => return None,
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                    h.update(b"-");
                }
                Err(_) => return None,
            }
        }
        Some(h.finalize().to_hex().to_string())
    }
    #[cfg(not(unix))]
    {
        let _ = olean;
        None
    }
}

/// Whether the `.olean` artifact set at `olean` still matches `entry`: by its recorded stat
/// fingerprint (once past the sub-tick cooldown window), else by re-hashing.
pub(crate) fn entry_artifacts_current(
    cfg: &ProjectConfig,
    olean: &Path,
    entry: &VerifiedDepModuleEntry,
) -> bool {
    (!entry.artifact_stat_fingerprint.is_empty()
        && olean_artifact_stat_fingerprint_for_store(olean).as_deref()
            == Some(entry.artifact_stat_fingerprint.as_str()))
        || olean_digest_is(cfg, olean, &entry.olean_artifact_digest)
}

/// After Lake refreshed dependency-package module `imp`, drop its now-outdated verified-sources
/// entry (or an unparseable manifest), so the module counts as Lake-managed from then on.
pub(crate) fn forget_refreshed_dep_module(cfg: &ProjectConfig, imp: &str) {
    let ImportSite::Module(root_spec) = resolve_import_site(cfg, imp) else {
        return;
    };
    let root_key = (root_spec.pkg_root.clone(), root_spec.module_name.clone());
    let mut visited = HashSet::new();
    let mut postorder: Vec<DiscoveredModuleSpec> = Vec::new();
    let mut stack = vec![(*root_spec, false)];
    while let Some((spec, expanded)) = stack.pop() {
        let key = (spec.pkg_root.clone(), spec.module_name.clone());
        if expanded {
            postorder.push(spec);
            continue;
        }
        if !visited.insert(key) {
            continue;
        }
        let sub_imps = fs::read_to_string(&spec.src_path)
            .ok()
            .map(|s| parse_header_info(&s))
            .filter(|h| h.header_error.is_none())
            .map(|h| h.imports)
            .unwrap_or_default();
        stack.push((spec, true));
        for sub in sub_imps {
            let site = match resolve_module_in_package(&cfg.root_pkg, true, &sub) {
                Some(rs) => ImportSite::Module(Box::new(rs)),
                None => resolve_import_site(cfg, &sub),
            };
            if let ImportSite::Module(sub_spec) = site {
                if !visited.contains(&(sub_spec.pkg_root.clone(), sub_spec.module_name.clone())) {
                    stack.push((*sub_spec, false));
                }
            }
        }
    }
    for spec in postorder {
        let path = spec
            .pkg_root
            .join(".lake/build/.turbo_verified_sources.json");
        let bytes = match fs::read(&path) {
            Ok(b) => b,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
            Err(_) => {
                let _ = fs::remove_file(&path);
                continue;
            }
        };
        let Ok(mut manifest) = serde_json::from_slice::<VerifiedDepManifest>(&bytes) else {
            let _ = fs::remove_file(&path);
            continue;
        };
        let rel = spec_rel_src(&spec);
        let is_root_imp = spec.pkg_root == root_key.0 && spec.module_name == root_key.1;
        let should_drop = manifest.modules.get(&rel).is_some_and(|entry| {
            let mut cache = LakeClosureCache::for_project(cfg);
            is_root_imp
                || !dep_pkg_import_pins_consistent(
                    cfg,
                    &DepImportMemo::default(),
                    &mut cache,
                    spec.clone(),
                    ImportPinSpec {
                        full_pin: &entry.olean_artifact_digest,
                        tier_pin: None,
                    },
                    false,
                )
        });
        if should_drop && manifest.modules.remove(&rel).is_some() {
            if let Ok(json) = serde_json::to_vec(&manifest) {
                let _ = fs::write(&path, json);
            }
        }
    }
}

pub(crate) fn root_module_lake_sidecars_current(cfg: &ProjectConfig, imp: &str) -> bool {
    let Some(spec) = resolve_module_in_package(&cfg.root_pkg, true, imp) else {
        return false;
    };
    let Ok(src) = fs::read_to_string(&spec.src_path) else {
        return false;
    };
    let hdr = parse_header_info(&src);
    let needs_c = spec.precompile_modules
        || spec.emit_c_default
        || spec.is_exe_target
        || hdr.has_c_export
        || global_emit_c_enabled();
    hdr.header_error.is_none()
        && verify_module_lake_sidecars_inner_opts_ext(
            &spec_olean_path(&spec),
            Some(&spec.build_ir_dir),
            &module_name_to_rel_slash(imp),
            &src,
            hdr.is_module,
            needs_c,
            false,
            true,
            !needs_c,
        )
        .is_ok()
}

/// Whether dependency-package module `imp` lacks a built `.olean` on disk.
pub(crate) fn dep_pkg_module_missing_olean(cfg: &ProjectConfig, imp: &str) -> bool {
    matches!(resolve_import_site(cfg, imp), ImportSite::Module(s) if !spec_olean_path(&s).is_file())
}

/// Whether root-package module `imp`'s existing on-disk `.olean` is stale against its Lake
/// `.trace` / sidecars and transitive import closure (when not already proven by a turbo manifest
/// entry). A missing `.olean` returns `false` so `build_missing` policy stays with the caller.
pub(crate) fn root_pkg_lake_module_stale(
    cfg: &ProjectConfig,
    cache: &mut LakeClosureCache,
    imp: &str,
) -> bool {
    let Some(spec) = resolve_module_in_package(&cfg.root_pkg, true, imp) else {
        return false;
    };
    let olean = spec_olean_path(&spec);
    if fs::symlink_metadata(&olean).is_err() {
        return false;
    }
    if cfg.lean_bin.as_os_str().is_empty() {
        return true;
    }
    let mut visiting = HashSet::new();
    lake_closure_export_info(cfg, &spec, false, cache, &mut visiting).is_none()
}

/// Whether dependency-package module `imp` may be stale before elaboration. A missing `.olean`
/// returns `false` (`dep_pkg_module_missing_olean` handles `build_missing`), unless the package
/// manifest is unreadable/corrupt or had a recorded entry whose artifacts vanished. Any present
/// `.olean` — whether recorded in `.turbo_verified_sources.json` or Lake-built without a manifest
/// entry — must prove its own artifacts, source/options, and entire transitive import closure
/// consistent, or fail closed (`true`).
pub(crate) fn dep_pkg_module_stale(
    cfg: &ProjectConfig,
    memo: &DepImportMemo,
    cache: &mut LakeClosureCache,
    imp: &str,
) -> bool {
    let spec = match resolve_import_site(cfg, imp) {
        ImportSite::Module(spec) => spec,
        ImportSite::Prebuilt(olean) => {
            return prebuilt_olean_export_info(cfg, false, &olean, cache).is_none()
        }
        // Two dependency packages own the name: no single closure is safe to elaborate against.
        ImportSite::Unresolved => return true,
        _ => return false,
    };
    let Some(cached_manifest) = load_cached_pkg_manifest(&mut cache.manifests, cfg, &spec, false)
    else {
        return true;
    };
    let olean = spec_olean_path(&spec);
    let olean_present = fs::symlink_metadata(&olean).is_ok();
    if let Some(entry) = cached_manifest
        .raw
        .as_ref()
        .and_then(|r| r.as_ref().ok())
        .and_then(|m| m.modules.get(&spec_rel_src(&spec)))
        .cloned()
    {
        return cfg.lean_bin.as_os_str().is_empty()
            || !dep_pkg_import_pins_consistent(
                cfg,
                memo,
                cache,
                *spec,
                ImportPinSpec {
                    full_pin: &entry.olean_artifact_digest,
                    tier_pin: None,
                },
                false,
            );
    }
    if !olean_present {
        return !cache.post_lake_refresh
            && !is_git_pinned_manifest_package(cfg, &spec)
            && package_by_root(cfg, &spec.pkg_root).is_some_and(|p| !p.inputs.is_empty());
    }
    if cfg.lean_bin.as_os_str().is_empty() {
        return true;
    }
    let mut visiting = HashSet::new();
    lake_closure_export_info(cfg, &spec, false, cache, &mut visiting).is_none()
}

pub(super) fn lake_import_trace_entries(
    parent_is_module: bool,
    imp: &ParsedImport,
    exp_info: &LakeModuleExportInfo,
) -> [serde_json::Value; 2] {
    if !parent_is_module {
        [
            serde_json::json!([
                format!("{} transitive imports (legacy)", imp.module),
                format!("{:016x}", exp_info.legacy_trans_trace)
            ]),
            serde_json::json!([
                format!("{}:importAllArts", imp.module),
                format!("{:016x}", exp_info.all_arts_trace)
            ]),
        ]
    } else if imp.import_all {
        [
            serde_json::json!([
                format!("{} transitive imports (all)", imp.module),
                format!("{:016x}", exp_info.all_trans_trace)
            ]),
            serde_json::json!([
                format!("{}:importAllArts", imp.module),
                format!("{:016x}", exp_info.all_arts_trace)
            ]),
        ]
    } else if imp.is_meta {
        [
            serde_json::json!([
                format!("{} transitive imports (meta)", imp.module),
                format!("{:016x}", exp_info.meta_trans_trace)
            ]),
            serde_json::json!([
                format!("{}:importArts (meta)", imp.module),
                format!("{:016x}", exp_info.meta_arts_trace)
            ]),
        ]
    } else {
        [
            serde_json::json!([
                format!("{} transitive imports (public)", imp.module),
                format!("{:016x}", exp_info.trans_trace)
            ]),
            serde_json::json!([
                format!("{}:importArts", imp.module),
                format!("{:016x}", exp_info.arts_trace)
            ]),
        ]
    }
}

pub(super) fn fold_lake_export_traces(
    trans_trace: &mut u64,
    meta_trans_trace: &mut u64,
    all_trans_trace: &mut u64,
    legacy_trans_trace: &mut u64,
    sub_imp: &ParsedImport,
    sub_exp: &LakeModuleExportInfo,
) {
    *legacy_trans_trace = lake_mix_hash(
        lake_mix_hash(*legacy_trans_trace, sub_exp.legacy_trans_trace),
        sub_exp.all_arts_trace,
    );
    *all_trans_trace = if sub_imp.import_all {
        lake_mix_hash(
            lake_mix_hash(*all_trans_trace, sub_exp.all_trans_trace),
            sub_exp.all_arts_trace,
        )
    } else if sub_imp.is_meta {
        lake_mix_hash(
            lake_mix_hash(*all_trans_trace, sub_exp.meta_trans_trace),
            sub_exp.meta_arts_trace,
        )
    } else {
        lake_mix_hash(
            lake_mix_hash(*all_trans_trace, sub_exp.trans_trace),
            sub_exp.arts_trace,
        )
    };
    *meta_trans_trace = lake_mix_hash(
        lake_mix_hash(*meta_trans_trace, sub_exp.meta_trans_trace),
        sub_exp.meta_arts_trace,
    );
    if sub_imp.is_exported {
        *trans_trace = if sub_imp.is_meta {
            lake_mix_hash(
                lake_mix_hash(*trans_trace, sub_exp.meta_trans_trace),
                sub_exp.meta_arts_trace,
            )
        } else {
            lake_mix_hash(
                lake_mix_hash(*trans_trace, sub_exp.trans_trace),
                sub_exp.arts_trace,
            )
        };
    }
}

pub(super) fn verify_trace_options_value(lean_options: &LeanOptionsMap, opt_val: &serde_json::Value) -> bool {
    if lean_options.is_empty() {
        return opt_val.as_str() == Some("00000000000006bb")
            || opt_val.as_array().is_some_and(Vec::is_empty);
    }
    let Some(arr) = opt_val.as_array() else {
        return false;
    };
    if arr.len() != lean_options.len() {
        return false;
    }
    let mut expected: BTreeSet<(String, String)> = BTreeSet::new();
    for (k, v) in lean_options {
        let cap = format!("-D{}={}", k.to_lean_string(), v.as_cli_flag_value());
        let hex = format!("{:016x}", lake_hash_text(&cap));
        expected.insert((cap, hex));
    }
    let mut seen: BTreeSet<(String, String)> = BTreeSet::new();
    for item in arr {
        let Some(p) = item.as_array() else {
            return false;
        };
        if p.len() != 2 {
            return false;
        }
        let (Some(c), Some(h)) = (p[0].as_str(), p[1].as_str()) else {
            return false;
        };
        let pair = (c.to_string(), h.to_string());
        if !expected.contains(&pair) || !seen.insert(pair) {
            return false;
        }
    }
    seen.len() == expected.len()
}

pub(super) fn verify_lake_trace_options_and_args(
    spec: &DiscoveredModuleSpec,
    tv: &serde_json::Value,
    opt_idx: usize,
) -> bool {
    let Some(inputs_arr) = tv.get("inputs").and_then(|v| v.as_array()) else {
        return false;
    };
    let Some(opt_pair) = inputs_arr.get(opt_idx).and_then(|v| v.as_array()) else {
        return false;
    };
    if opt_pair.len() != 2
        || opt_pair[0].as_str() != Some("options")
        || !verify_trace_options_value(&spec.lean_options, &opt_pair[1])
    {
        return false;
    }
    let Some(args_pair) = inputs_arr.get(opt_idx + 4).and_then(|v| v.as_array()) else {
        return false;
    };
    if args_pair.len() != 2 {
        return false;
    }
    let expected_args_cap = if spec.strong_args.is_empty() {
        "Module.leanArgs: #[]".to_string()
    } else {
        format!("Module.leanArgs: #[{}]", spec.strong_args.join(", "))
    };
    let expected_args_h = format!(
        "{:016x}",
        spec.strong_args
            .iter()
            .fold(LAKE_NIL_HASH, |acc, a| lake_mix_hash(
                acc,
                lake_hash_bytes(a.as_bytes())
            ))
    );
    args_pair[0].as_str() == Some(expected_args_cap.as_str())
        && args_pair[1].as_str() == Some(expected_args_h.as_str())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn build_expected_lake_module_inputs_value(
    cfg: &ProjectConfig,
    pkg_root: &Path,
    pkg_name: &str,
    pkg_base_name: &str,
    target_name: &str,
    is_exe_target: bool,
    module_name: &str,
    is_module: bool,
    platform_independent: Option<bool>,
    lean_options: &LeanOptionsMap,
    strong_args: &[String],
    src_path: &Path,
    src_h: u64,
    import_entries: Vec<serde_json::Value>,
    raw_imp_dynlibs: &[PathBuf],
) -> Option<serde_json::Value> {
    if cfg.lean_githash.is_empty() || cfg.lean_githash == "lean-not-installed" {
        return None;
    }
    let options_val = if lean_options.is_empty() {
        serde_json::json!("00000000000006bb")
    } else {
        let mut opt_entries = Vec::with_capacity(lean_options.len());
        for (k, v) in lean_options {
            let flag = format!("-D{}={}", k.to_lean_string(), v.as_cli_flag_value());
            opt_entries.push(serde_json::json!([
                flag,
                format!("{:016x}", lake_hash_text(&flag))
            ]));
        }
        serde_json::Value::Array(opt_entries)
    };
    let lean_args_h = strong_args.iter().fold(LAKE_NIL_HASH, |acc, a| {
        lake_mix_hash(acc, lake_hash_bytes(a.as_bytes()))
    });
    let base_pkg_name = if pkg_base_name.is_empty() {
        pkg_name
    } else {
        pkg_base_name
    };
    let pkg_base_ident = if base_pkg_name.contains('-') {
        format!("«{}»", base_pkg_name)
    } else {
        base_pkg_name.to_string()
    };
    let pkg_id_ident = if pkg_name.contains('-') {
        format!("«{}»", pkg_name)
    } else {
        pkg_name.to_string()
    };
    let ver_short = cfg
        .toolchain
        .rsplit(':')
        .next()
        .unwrap_or(&cfg.toolchain)
        .trim_start_matches('v');
    let lean_cap = format!("Lean {}, commit {}", ver_short, cfg.lean_githash.trim());
    let lean_gh_h = lake_hash_bytes(cfg.lean_githash.trim().as_bytes());
    let is_mod_h = lake_mix_hash(LAKE_NIL_HASH, if is_module { 11 } else { 13 });
    let lean_args_cap = if strong_args.is_empty() {
        "Module.leanArgs: #[]".to_string()
    } else {
        format!("Module.leanArgs: #[{}]", strong_args.join(", "))
    };
    let libs_trace_entry = if platform_independent == Some(true) {
        serde_json::json!([
            "libs",
            [
                ["import dynlibs", "00000000000006bb"],
                ["package external libraries", "00000000000006bb"],
                ["module dynlibs", "00000000000006bb"],
                ["module plugins", "00000000000006bb"]
            ]
        ])
    } else {
        let mut import_dynlib_entries = Vec::with_capacity(raw_imp_dynlibs.len());
        for p in raw_imp_dynlibs {
            let h = verify_and_hash_artifact_bytes(p, false, false).ok()?;
            import_dynlib_entries.push(serde_json::json!([
                p.to_string_lossy(),
                format!("{:016x}", h)
            ]));
        }
        let import_dynlibs_json = if import_dynlib_entries.is_empty() {
            serde_json::Value::String("00000000000006bb".to_string())
        } else {
            serde_json::Value::Array(import_dynlib_entries)
        };
        serde_json::json!([
            "libs",
            [
                ["import dynlibs", import_dynlibs_json],
                ["package external libraries", "00000000000006bb"],
                ["module dynlibs", "00000000000006bb"],
                ["module plugins", "00000000000006bb"]
            ]
        ])
    };
    let inputs_val = if import_entries.is_empty() {
        serde_json::json!("00000000000006bb")
    } else {
        serde_json::Value::Array(import_entries)
    };
    let mut extra_dep_entries = vec![serde_json::json!([
        format!("@{}:extraDep", pkg_base_ident),
        format!("{LAKE_NIL_HASH:016x}")
    ])];
    if let Some(pkg) = package_by_root(cfg, pkg_root) {
        let needs: &[String] = if is_exe_target {
            pkg.exes
                .iter()
                .find(|e| e.name == target_name && e.root == module_name)
                .map_or(&[], |e| e.needs.as_slice())
        } else {
            pkg.libs
                .iter()
                .find(|l| l.name == target_name && lib_can_build_module(l, module_name))
                .map_or(&[], |l| l.needs.as_slice())
        };
        extra_dep_entries.extend(
            needs
                .iter()
                .filter_map(|n| pkg.inputs.iter().find(|i| &i.name == n))
                .map(|i| {
                    serde_json::json!([pkg.pkg_root.join(&i.path).to_string_lossy(), i.lake_hash])
                }),
        );
    }
    let deps_entry = serde_json::json!([
        "deps",
        [
            [
                format!("{}/{}:extraDep", pkg_base_ident, target_name),
                extra_dep_entries
            ],
            ["imports", inputs_val]
        ]
    ]);
    let nested = lake_trace_uses_nested_mod_deps(&cfg.toolchain);
    let mut input_vec = if nested {
        let mut nested_entries = vec![deps_entry];
        if platform_independent != Some(true) {
            nested_entries.push(libs_trace_entry);
        }
        if platform_independent == Some(false) {
            let tc_spec = query_toolchain_native_spec(&cfg.lean_bin).ok()?;
            if tc_spec.target.is_empty() {
                return None;
            }
            let plat_h = lake_hash_bytes(tc_spec.target.as_bytes());
            nested_entries.push(serde_json::json!([
                tc_spec.target,
                format!("{:016x}", plat_h)
            ]));
        }
        vec![serde_json::json!([
            format!("{}:deps", module_name),
            nested_entries
        ])]
    } else {
        let mut top_entries = vec![deps_entry, libs_trace_entry];
        if platform_independent == Some(false) {
            let tc_spec = query_toolchain_native_spec(&cfg.lean_bin).ok()?;
            if tc_spec.target.is_empty() {
                return None;
            }
            let plat_h = lake_hash_bytes(tc_spec.target.as_bytes());
            top_entries.push(serde_json::json!([
                tc_spec.target,
                format!("{:016x}", plat_h)
            ]));
        }
        top_entries
    };
    input_vec.extend([
        serde_json::json!([lean_cap, format!("{:016x}", lean_gh_h)]),
        serde_json::json!([src_path.to_string_lossy(), format!("{:016x}", src_h)]),
        serde_json::json!(["options", options_val]),
        serde_json::json!([
            format!("isModule: {}", is_module),
            format!("{:016x}", is_mod_h)
        ]),
        serde_json::json!([
            format!("Module.name: {}", module_name),
            format!("{:016x}", lake_hash_name(module_name))
        ]),
        serde_json::json!([
            format!("Package.id?: (some {})", pkg_id_ident),
            format!("{:016x}", lake_hash_pkg_id(pkg_name))
        ]),
        serde_json::json!([lean_args_cap, format!("{:016x}", lean_args_h)]),
    ]);
    Some(serde_json::Value::Array(input_vec))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn compute_expected_lake_module_dep_hash(
    cfg: &ProjectConfig,
    pkg_root: &Path,
    pkg_name: &str,
    pkg_base_name: &str,
    target_name: &str,
    is_exe_target: bool,
    module_name: &str,
    is_module: bool,
    platform_independent: Option<bool>,
    lean_options: &LeanOptionsMap,
    strong_args: &[String],
    src_path: &Path,
    src_h: u64,
    import_entries: Vec<serde_json::Value>,
    raw_imp_dynlibs: &[PathBuf],
) -> Option<u64> {
    let inputs = build_expected_lake_module_inputs_value(
        cfg,
        pkg_root,
        pkg_name,
        pkg_base_name,
        target_name,
        is_exe_target,
        module_name,
        is_module,
        platform_independent,
        lean_options,
        strong_args,
        src_path,
        src_h,
        import_entries,
        raw_imp_dynlibs,
    )?;
    lake_input_hash(&inputs).ok()
}

#[allow(clippy::type_complexity)]
pub(super) static CLEAN_GIT_PIN_MEMO: OnceLock<Mutex<HashMap<(PathBuf, String), (u64, bool)>>> =
    OnceLock::new();
pub(super) static TRUSTED_SNAPSHOT_GIT_PIN_DIRS: OnceLock<Mutex<HashSet<(PathBuf, String)>>> = OnceLock::new();

pub(crate) fn mark_trusted_snapshot_git_pinned_dir(pkg_root: &Path, expected_rev: &str) {
    if let Ok(canon) = pkg_root.canonicalize() {
        let set = TRUSTED_SNAPSHOT_GIT_PIN_DIRS.get_or_init(|| Mutex::new(HashSet::new()));
        if let Ok(mut g) = set.lock() {
            if g.len() >= 1024 {
                g.clear();
            }
            g.insert((canon, expected_rev.trim().to_ascii_lowercase()));
        }
    }
}

pub(crate) fn unmark_trusted_snapshot_root(snapshot_root: &Path) {
    let canon = snapshot_root
        .canonicalize()
        .unwrap_or_else(|_| snapshot_root.to_path_buf());
    if let Some(set) = TRUSTED_SNAPSHOT_GIT_PIN_DIRS.get() {
        if let Ok(mut g) = set.lock() {
            g.retain(|(p, _)| !p.starts_with(&canon));
        }
    }
}

pub(crate) fn manifest_pinned_git_rev_for_pkg<'a>(
    cfg: &'a ProjectConfig,
    pkg_name: &str,
    pkg_base_name: &str,
    pkg_root: &Path,
) -> Option<&'a str> {
    let pkg_canon = pkg_root.canonicalize().ok();
    cfg.manifest_packages
        .iter()
        .find(|mp| {
            mp.pkg_type == "git"
                && mp
                    .rev
                    .as_deref()
                    .map(str::trim)
                    .is_some_and(|r| !r.is_empty() && !r.starts_with('-'))
                && (mp.name == pkg_name
                    || (!pkg_base_name.is_empty() && mp.name == pkg_base_name)
                    || mp.dir == pkg_root
                    || mp
                        .dir
                        .canonicalize()
                        .ok()
                        .zip(pkg_canon.as_ref())
                        .is_some_and(|(a, b)| a == *b))
        })
        .and_then(|mp| mp.rev.as_deref().map(str::trim))
}

pub(crate) fn package_gitlink_touches_lean(rel: &Path, pkg: &PackageConfig) -> bool {
    let norm = |p: &Path| -> PathBuf {
        p.components()
            .filter(|c| !matches!(c, std::path::Component::CurDir))
            .collect()
    };
    let rel = norm(rel);
    let has_lean_custom_target = pkg.precompile_modules
        || pkg.libs.iter().any(|l| {
            !l.custom_target_needs.is_empty()
                || l.precompile_modules == Some(true)
                || l.default_facets
                    .iter()
                    .any(|f| matches!(f.as_str(), "shared" | "LeanLib.sharedFacet"))
        })
        || pkg.exes.iter().any(|e| !e.custom_target_needs.is_empty())
        || pkg
            .custom_targets
            .iter()
            .any(|ct| pkg.default_targets.iter().any(|dt| dt == ct));
    if rel.as_os_str().is_empty()
        || pkg.unsupported.is_some()
        || (!pkg.custom_targets.is_empty() && has_lean_custom_target)
        || rel.extension().is_some_and(|e| e == "lean")
    {
        return true;
    }
    if let Some(name) = rel.file_name().and_then(|n| n.to_str()) {
        if matches!(
            name,
            "lakefile.lean" | "lakefile.toml" | "lake-manifest.json" | "lean-toolchain"
        ) || (rel.parent().is_some_and(|p| p.as_os_str().is_empty())
            && matches!(rel.file_stem().and_then(|s| s.to_str()), Some("lakefile")))
        {
            return true;
        }
    }
    let overlaps = |a: &Path, b: &Path| a.starts_with(b) || b.starts_with(a);
    let base = norm(&pkg.src_dir);
    for path in [&pkg.build_dir, &pkg.packages_dir] {
        let np = norm(path);
        let rel_np = np.strip_prefix(&pkg.pkg_root).unwrap_or(&np);
        if overlaps(&rel, rel_np) {
            return true;
        }
    }
    for inp in &pkg.inputs {
        let np = norm(&inp.path);
        let rel_np = np.strip_prefix(&pkg.pkg_root).unwrap_or(&np);
        if overlaps(&rel, rel_np) {
            return true;
        }
    }
    if pkg.libs.is_empty() && pkg.exes.is_empty() {
        return overlaps(&rel, &base);
    }
    let module_prefix = |root: &Path, module: &str| {
        let first = module.split('.').next().unwrap_or(module);
        norm(&root.join(first))
    };
    for lib in &pkg.libs {
        let root = match &lib.src_dir {
            Some(dir) => norm(&base.join(dir)),
            None => base.clone(),
        };
        if lib.globs.is_empty() && lib.roots.is_empty() && overlaps(&rel, &root) {
            return true;
        }
        let names = lib
            .roots
            .iter()
            .map(String::as_str)
            .chain(lib.globs.iter().map(|g| match g {
                GlobSpec::One(n) | GlobSpec::Submodules(n) | GlobSpec::AndSubmodules(n) => {
                    n.as_str()
                }
            }));
        for name in names {
            let prefix = module_prefix(&root, name);
            if overlaps(&rel, &prefix) || overlaps(&rel, &prefix.with_extension("lean")) {
                return true;
            }
        }
    }
    for exe in &pkg.exes {
        let root = match &exe.src_dir {
            Some(dir) => norm(&base.join(dir)),
            None => base.clone(),
        };
        let prefix = module_prefix(&root, &exe.root);
        if overlaps(&rel, &prefix) || overlaps(&rel, &prefix.with_extension("lean")) {
            return true;
        }
    }
    false
}

pub(crate) fn is_clean_pinned_git_checkout(
    pkg_root: &Path,
    expected_rev: &str,
    pkg_opt: Option<&PackageConfig>,
) -> bool {
    let expected = expected_rev.trim();
    if expected.is_empty()
        || expected.starts_with('-')
        || !matches!(expected.len(), 40 | 64)
        || !expected.bytes().all(|b| b.is_ascii_hexdigit())
    {
        return false;
    }
    let Ok(canon) = pkg_root.canonicalize() else {
        return false;
    };
    if !canon.join(".git").exists() {
        return TRUSTED_SNAPSHOT_GIT_PIN_DIRS
            .get()
            .and_then(|s| s.lock().ok())
            .is_some_and(|g| g.contains(&(canon, expected.to_ascii_lowercase())));
    }
    let cfg_tag = pkg_opt.map(|p| p.config_digest.clone()).unwrap_or_default();
    let window = current_memo_window();
    let key = (
        canon.clone(),
        format!("{}:{cfg_tag}", expected.to_ascii_lowercase()),
    );
    let memo = CLEAN_GIT_PIN_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
    if let Ok(guard) = memo.lock() {
        if let Some(&(cached_win, ok)) = guard.get(&key) {
            if cached_win == window {
                return ok;
            }
        }
    }
    let computed = (|| -> Option<bool> {
        let mut allowed_gitlinks: Vec<PathBuf> = Vec::new();
        if crate::trusted_tools::reject_gitlinks_filtered(
            &canon,
            &[expected],
            Path::new("."),
            |rel| {
                let touches = pkg_opt.is_none_or(|pkg| package_gitlink_touches_lean(rel, pkg));
                if !touches {
                    allowed_gitlinks.push(rel.to_path_buf());
                }
                touches
            },
        )
        .is_err()
        {
            return Some(false);
        }
        allowed_gitlinks.sort();
        allowed_gitlinks.dedup();
        let mut rev_cmd = crate::trusted_tools::git(&canon).ok()?;
        let rev_out = rev_cmd
            .args([
                "--no-optional-locks",
                "-C",
                &canon.to_string_lossy(),
                "rev-parse",
                "HEAD",
            ])
            .output()
            .ok()?;
        if !rev_out.status.success() {
            return Some(false);
        }
        let head_rev = String::from_utf8_lossy(&rev_out.stdout);
        if !head_rev.trim().eq_ignore_ascii_case(expected) {
            return Some(false);
        }
        let mut st_cmd = crate::trusted_tools::git(&canon).ok()?;
        let st_out = st_cmd
            .args([
                "--no-optional-locks",
                "-C",
                &canon.to_string_lossy(),
                "status",
                "--porcelain",
                "-z",
                "-uall",
                crate::trusted_tools::NO_SUBMODULES,
            ])
            .output()
            .ok()?;
        if !st_out.status.success() {
            return Some(false);
        }
        let entries = st_out.stdout.split(|&b| b == 0).filter(|s| !s.is_empty());
        for rec in entries {
            if rec.len() < 4 {
                return Some(false);
            }
            let xy = &rec[..2];
            let Ok(rel_str) = std::str::from_utf8(&rec[3..]) else {
                return Some(false);
            };
            let rel = Path::new(rel_str);
            if xy.contains(&b'R') || xy.contains(&b'C') {
                return Some(false);
            }
            if !allowed_gitlinks.iter().any(|gl| gl == rel) {
                return Some(false);
            }
        }
        Some(true)
    })()
    .unwrap_or(false);
    if let Ok(mut guard) = memo.lock() {
        if current_memo_window() == window {
            guard.insert(key, (window, computed));
        }
    }
    computed
}

pub(super) fn spec_in_clean_git_pinned_manifest_package(
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
    cache: &mut LakeClosureCache,
) -> bool {
    if spec.is_root_pkg {
        return false;
    }
    let spec_canon = spec
        .pkg_root
        .canonicalize()
        .unwrap_or_else(|_| spec.pkg_root.clone());
    let Some(expected_rev) =
        manifest_pinned_git_rev_for_pkg(cfg, &spec.pkg_name, &spec.pkg_base_name, &spec.pkg_root)
    else {
        return false;
    };
    let pkg_opt = package_by_root(cfg, &spec.pkg_root);
    *cache
        .clean_git_pin_memo
        .entry(spec_canon.clone())
        .or_insert_with(|| is_clean_pinned_git_checkout(&spec_canon, expected_rev, pkg_opt))
}

pub(super) fn prebuilt_artifact_traces(
    olean_path: &Path,
) -> Option<(LakeModuleExportInfo, bool, serde_json::Value)> {
    let srv_path = PathBuf::from(format!("{}.server", olean_path.display()));
    let is_mod = srv_path.is_file();
    let tv = verify_trace_outputs_against_artifacts_with_existing_c_ext(olean_path, is_mod, true)
        .ok()?;
    let (arts_trace, meta_arts_trace, all_arts_trace) =
        compute_module_arts_traces(olean_path, is_mod, false).ok()?;
    Some((
        LakeModuleExportInfo {
            arts_trace,
            meta_arts_trace,
            all_arts_trace,
            trans_trace: 0,
            meta_trans_trace: 0,
            all_trans_trace: 0,
            legacy_trans_trace: 0,
        },
        is_mod,
        tv,
    ))
}

pub(super) fn recorded_trace_imports_hash(tv: &serde_json::Value) -> Option<u64> {
    lake_input_hash(trace_recorded_imports_array(tv)?).ok()
}

pub(super) fn prebuilt_import_specs(olean_path: &Path) -> Option<Vec<ParsedImport>> {
    let bytes = fs::read(olean_path).ok()?;
    let (specs, is_mod) = parse_olean_binary_imports(&bytes)?;
    if PathBuf::from(format!("{}.server", olean_path.display())).is_file() != is_mod {
        return None;
    }
    Some(specs)
}

pub(crate) fn resolve_source_spec_for_prebuilt_olean(
    cfg: &ProjectConfig,
    olean_path: &Path,
) -> Option<DiscoveredModuleSpec> {
    let canon = fs::canonicalize(olean_path).unwrap_or_else(|_| olean_path.to_path_buf());
    for (pkg, is_root) in
        std::iter::once((&cfg.root_pkg, true)).chain(cfg.dep_pkgs.iter().map(|dp| (dp, false)))
    {
        let lib_dir = pkg.pkg_root.join(&pkg.build_dir).join(&pkg.lean_lib_dir);
        let lib_canon = fs::canonicalize(&lib_dir).unwrap_or(lib_dir);
        if let Ok(rel) = canon.strip_prefix(&lib_canon) {
            if rel.extension().and_then(|e| e.to_str()) == Some("olean") {
                let stem = rel.with_extension("");
                let mod_name = stem
                    .to_string_lossy()
                    .replace('\\', "/")
                    .trim_matches('/')
                    .replace('/', ".");
                if !mod_name.is_empty() {
                    if let Some(spec) = resolve_module_in_package(pkg, is_root, &mod_name) {
                        return Some(spec);
                    }
                }
            }
        }
    }
    None
}

pub(super) fn module_includes_all_covered_by_lake_inputs(
    pkg: &PackageConfig,
    mod_name: &str,
    src_path: &Path,
    src_raw: &str,
) -> bool {
    if !source_uses_include_str(src_raw) {
        return true;
    }
    let Some(rel_paths) = crate::splitter::extract_include_relative_paths(src_raw) else {
        return false;
    };
    if rel_paths.is_empty() {
        return false;
    }
    let needed: BTreeSet<&str> = pkg
        .libs
        .iter()
        .filter(|lib| lib_can_build_module(lib, mod_name))
        .flat_map(|lib| lib.needs.iter().map(String::as_str))
        .chain(
            pkg.exes
                .iter()
                .filter(|exe| exe.root == mod_name)
                .flat_map(|exe| exe.needs.iter().map(String::as_str)),
        )
        .collect();
    if needed.is_empty() {
        return false;
    }
    let Ok(canon_pkg_root) = fs::canonicalize(&pkg.pkg_root) else {
        return false;
    };
    let Some(src_dir) = src_path.parent() else {
        return false;
    };
    for rel in &rel_paths {
        let candidate = src_dir.join(rel);
        let Ok(canon_target) = fs::canonicalize(&candidate) else {
            return false;
        };
        if !canon_target.starts_with(&canon_pkg_root)
            || check_input_file_is_contained_regular_file(&canon_pkg_root, &canon_target).is_err()
        {
            return false;
        }
        let covered = pkg.inputs.iter().any(|inp| {
            if !needed.contains(inp.name.as_str()) || inp.unsupported.is_some() {
                return false;
            }
            let Ok(checked) = checked_input_path(&inp.path) else {
                return false;
            };
            let Ok(canon_inp) = fs::canonicalize(pkg.pkg_root.join(checked)) else {
                return false;
            };
            if inp.is_dir {
                canon_target.starts_with(&canon_inp)
                    && canon_target != canon_inp
                    && inp.matches_extension(canon_target.extension())
            } else {
                canon_target == canon_inp
            }
        });
        if !covered {
            return false;
        }
    }
    true
}

pub(super) fn prebuilt_closure_export_info(
    cfg: &ProjectConfig,
    strict_policy: bool,
    olean_path: &Path,
    cache: &mut LakeClosureCache,
    mod_visiting: &mut HashSet<(PathBuf, String)>,
    pb_visiting: &mut HashSet<PathBuf>,
    pb_closure_opt: Option<&mut Vec<(String, PathBuf)>>,
) -> Option<LakeModuleExportInfo> {
    let canon = fs::canonicalize(olean_path).unwrap_or_else(|_| olean_path.to_path_buf());
    let memo_key = (
        canon.clone(),
        strict_policy,
        cache.allow_stale_manifest_hydration,
    );
    if pb_closure_opt.is_none() {
        if let Some(cached) = cache.pb_exp_memo.get(&memo_key) {
            return *cached;
        }
    }
    if !pb_visiting.insert(canon.clone()) {
        return None;
    }
    let had_cycle_ancestor = !mod_visiting.is_empty() || pb_visiting.len() > 1;
    let mut local_pairs: Vec<(String, PathBuf)> = Vec::new();
    let collect_pairs = pb_closure_opt.is_some();
    let res = (|| -> Option<LakeModuleExportInfo> {
        let mapped_spec_opt = resolve_source_spec_for_prebuilt_olean(cfg, olean_path);
        if let Some(ref mapped_spec) = mapped_spec_opt {
            let mapped_src = fs::read_to_string(&mapped_spec.src_path).ok()?;
            if spec_source_has_disallowed_elab_host_effects(cfg, mapped_spec, &mapped_src) {
                return None;
            }
        }
        let (mut info, is_mod, tv) = prebuilt_artifact_traces(olean_path)?;
        if tv.get("inputs").is_none() {
            let mapped_spec = mapped_spec_opt?;
            return lake_closure_export_info_inner(
                cfg,
                &mapped_spec,
                strict_policy,
                cache,
                mod_visiting,
                pb_visiting,
                if collect_pairs {
                    Some(&mut local_pairs)
                } else {
                    None
                },
            );
        }
        let actual_imports_h = recorded_trace_imports_hash(&tv)?;
        if !cfg.lean_githash.is_empty() && cfg.lean_githash != "lean-not-installed" {
            let expected_bgh = cfg.lean_githash.trim();
            let (_, actual_bgh) = read_olean_header_version_and_githash(olean_path)?;
            if !actual_bgh.eq_ignore_ascii_case(expected_bgh) {
                return None;
            }
            let expected_gh = format!("{:016x}", lake_hash_bytes(expected_bgh.as_bytes()));
            let nested = tv
                .pointer("/inputs/0/0")
                .and_then(|v| v.as_str())
                .is_some_and(|s| s.ends_with(":deps"));
            let gh_ptrs: &[&str] = if nested {
                &["/inputs/1/1"]
            } else {
                &["/inputs/2/1", "/inputs/3/1"]
            };
            let gh_ok = gh_ptrs.iter().any(|ptr| {
                tv.pointer(ptr)
                    .and_then(|v| v.as_str())
                    .is_some_and(|s| s == expected_gh)
            });
            if !gh_ok {
                return None;
            }
        } else if cfg.lean_bin.as_os_str().is_empty() || cfg.lean_githash == "lean-not-installed" {
            return None;
        }
        let specs = prebuilt_import_specs(olean_path)?;
        let mut import_entries = Vec::new();
        let mut trans_trace = 1723u64;
        let mut meta_trans_trace = 1723u64;
        let mut all_trans_trace = 1723u64;
        let mut legacy_trans_trace = 1723u64;
        for sub_imp in &specs {
            let site = match resolve_module_in_package(&cfg.root_pkg, true, &sub_imp.module) {
                Some(root_spec) => ImportSite::Module(Box::new(root_spec)),
                None => resolve_import_site(cfg, &sub_imp.module),
            };
            let sub_exp = match site {
                ImportSite::Toolchain => continue,
                ImportSite::Prebuilt(sub_olean) => {
                    if collect_pairs {
                        local_pairs.push((sub_imp.module.clone(), sub_olean.clone()));
                    }
                    prebuilt_closure_export_info(
                        cfg,
                        strict_policy,
                        &sub_olean,
                        cache,
                        mod_visiting,
                        pb_visiting,
                        if collect_pairs {
                            Some(&mut local_pairs)
                        } else {
                            None
                        },
                    )?
                }
                ImportSite::Module(sub_spec) => {
                    if cache.allows_cutoff_parsed_import(
                        &sub_spec.pkg_root,
                        &sub_spec.module_name,
                        is_mod,
                        sub_imp,
                    ) == Some(false)
                    {
                        return None;
                    }
                    if collect_pairs {
                        local_pairs.push((sub_imp.module.clone(), spec_olean_path(&sub_spec)));
                    }
                    lake_closure_export_info_inner(
                        cfg,
                        &sub_spec,
                        strict_policy,
                        cache,
                        mod_visiting,
                        pb_visiting,
                        if collect_pairs {
                            Some(&mut local_pairs)
                        } else {
                            None
                        },
                    )?
                }
                ImportSite::Unresolved => return None,
            };
            for e in lake_import_trace_entries(is_mod, sub_imp, &sub_exp) {
                import_entries.push(e);
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
        let expected_imports_h = if import_entries.is_empty() {
            1723u64
        } else {
            lake_input_hash(&serde_json::Value::Array(import_entries)).ok()?
        };
        if actual_imports_h != expected_imports_h {
            return None;
        }
        info.trans_trace = trans_trace;
        info.meta_trans_trace = meta_trans_trace;
        info.all_trans_trace = all_trans_trace;
        info.legacy_trans_trace = legacy_trans_trace;
        Some(info)
    })();
    pb_visiting.remove(&canon);
    if let Some(info) = res {
        cache.pb_exp_memo.insert(memo_key, Some(info));
        if let Some(out_pairs) = pb_closure_opt {
            out_pairs.extend(local_pairs);
        }
    } else if pb_closure_opt.is_none() && !had_cycle_ancestor {
        cache.pb_exp_memo.insert(memo_key, None);
    }
    res
}

pub(crate) fn prebuilt_olean_export_info(
    cfg: &ProjectConfig,
    strict_policy: bool,
    olean_path: &Path,
    cache: &mut LakeClosureCache,
) -> Option<LakeModuleExportInfo> {
    let mut mod_visiting = HashSet::new();
    let mut pb_visiting = HashSet::new();
    prebuilt_closure_export_info(
        cfg,
        strict_policy,
        olean_path,
        cache,
        &mut mod_visiting,
        &mut pb_visiting,
        None,
    )
}

/// Fail-closed Lake/turbo closure verifier for `spec`, returning its `LakeModuleExportInfo` only
/// when `spec` and every transitive import are proven current against sources, toolchain/options,
/// sidecars, and import export hashes (or turbo manifest pins).
pub(crate) fn lake_closure_export_info(
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
    strict_policy: bool,
    cache: &mut LakeClosureCache,
    visiting: &mut HashSet<(PathBuf, String)>,
) -> Option<LakeModuleExportInfo> {
    let mut pb_visiting = HashSet::new();
    lake_closure_export_info_inner(
        cfg,
        spec,
        strict_policy,
        cache,
        visiting,
        &mut pb_visiting,
        None,
    )
}

pub(super) fn lake_closure_export_info_inner(
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
    strict_policy: bool,
    cache: &mut LakeClosureCache,
    visiting: &mut HashSet<(PathBuf, String)>,
    pb_visiting: &mut HashSet<PathBuf>,
    out_closure_opt: Option<&mut Vec<(String, PathBuf)>>,
) -> Option<LakeModuleExportInfo> {
    let visit_key = (spec.pkg_root.clone(), spec.module_name.clone());
    let memo_key = (
        spec.pkg_root.clone(),
        spec.module_name.clone(),
        strict_policy,
        cache.allow_stale_manifest_hydration,
    );
    if out_closure_opt.is_none() {
        if let Some(cached) = cache.exp_memo.get(&memo_key) {
            return *cached;
        }
    }
    if !visiting.insert(visit_key.clone()) {
        return None;
    }
    let had_cycle_ancestor = visiting.len() > 1 || !pb_visiting.is_empty();
    let mut local_pairs: Vec<(String, PathBuf)> = Vec::new();
    let collect_pairs = out_closure_opt.is_some();
    let res = (|| -> Option<LakeModuleExportInfo> {
        let olean_path = spec_olean_path(spec);
        if !cfg.lean_githash.is_empty() && cfg.lean_githash != "lean-not-installed" {
            let (_, actual_bgh) = read_olean_header_version_and_githash(&olean_path)?;
            if !actual_bgh.eq_ignore_ascii_case(cfg.lean_githash.trim()) {
                return None;
            }
        } else if cfg.lean_bin.as_os_str().is_empty() || cfg.lean_githash == "lean-not-installed" {
            return None;
        }
        let src_raw = fs::read_to_string(&spec.src_path).ok()?;
        let hdr = parse_header_info(&src_raw);
        if hdr.header_error.is_some() {
            return None;
        }
        let is_mod = hdr.is_module;
        let rel_slash = module_name_to_rel_slash(&spec.module_name);
        let expected_lake_inputs = workspace_lake_inputs_digest(cfg).ok()?;
        let rel_src = spec_rel_src(spec);
        let allow_stale_hydration = cache.allow_stale_manifest_hydration && !strict_policy;
        let (raw_has_entry, raw_is_some, raw_pkg_matched_entry, mut manifest_entry) = {
            let cached_manifest =
                load_cached_pkg_manifest(&mut cache.manifests, cfg, spec, strict_policy)?;
            let raw_has = matches!(
                cached_manifest.raw.as_ref(),
                Some(Ok(m)) if m.modules.contains_key(&rel_src)
            );
            let raw_some = cached_manifest.raw.is_some();
            let raw_matched = if allow_stale_hydration {
                match cached_manifest.raw.as_ref() {
                    Some(Ok(m))
                        if m.pkg_name == spec.pkg_name
                            && m.toolchain == cfg.toolchain
                            && m.lean_githash == cfg.lean_githash
                            && m.pkg_config_digest == spec.pkg_config_digest =>
                    {
                        m.modules.get(&rel_src).cloned()
                    }
                    _ => None,
                }
            } else {
                None
            };
            let validated_entry = cached_manifest
                .validated
                .as_ref()
                .and_then(|m| m.modules.get(&rel_src))
                .cloned();
            (raw_has, raw_some, raw_matched, validated_entry)
        };
        if allow_stale_hydration && manifest_entry.is_none() {
            if let Some(raw_entry) = raw_pkg_matched_entry {
                if !cache.module_closure_depends_on_lake_inputs(cfg, spec) {
                    manifest_entry = Some(raw_entry);
                }
            }
        }
        let needs_c = spec.precompile_modules || spec.is_exe_target;
        verify_module_lake_sidecars_inner_opts_ext(
            &olean_path,
            Some(&spec.build_ir_dir),
            &rel_slash,
            &src_raw,
            is_mod,
            needs_c,
            false,
            true,
            !needs_c,
        )
        .ok()?;
        let (arts_trace, meta_arts_trace, all_arts_trace) =
            compute_module_arts_traces(&olean_path, is_mod, false).ok()?;
        if raw_has_entry && manifest_entry.is_none() && !allow_stale_hydration {
            return None;
        }
        if manifest_entry.is_none()
            && !cache.post_lake_refresh
            && !allow_stale_hydration
            && !expected_lake_inputs.is_empty()
            && ((spec.is_root_pkg && raw_is_some)
                || (!is_git_pinned_manifest_package(cfg, spec)
                    && package_by_root(cfg, &spec.pkg_root).is_some_and(|p| !p.inputs.is_empty())))
        {
            return None;
        }

        let has_valid_turbo_entry = if let Some(ref entry) = manifest_entry {
            let entry_inputs_ok = entry.lake_inputs_digest == expected_lake_inputs
                || (allow_stale_hydration
                    && !cache.module_closure_depends_on_lake_inputs(cfg, spec));
            if (strict_policy && spec.is_root_pkg && !entry.kernel_audited)
                || !entry_inputs_ok
                || blake3::hash(src_raw.as_bytes()).to_hex().as_str() != entry.src_blake3
                || !entry_artifacts_current(cfg, &olean_path, entry)
            {
                if allow_stale_hydration {
                    manifest_entry = None;
                    false
                } else {
                    return None;
                }
            } else {
                true
            }
        } else {
            false
        };

        // One taint classification feeds both checks: stamp eligibility keeps its
        // narrower host-read meaning, and the gated clause below is what polices pure
        // elaborator / `@[extern]` shapes.
        let host_taint = spec_source_host_effect_taint(cfg, spec, &src_raw);
        if ((!cache.post_lake_refresh || has_valid_turbo_entry)
            && spec_source_stamp_ineligible_given_taint(cfg, spec, &src_raw, host_taint))
            || (!cache.post_lake_refresh
                && host_taint.is_tainted()
                && (strict_policy
                    || !has_valid_turbo_entry
                    || crate::lake_build::worktree_auto_link_disabled(&cfg.root_pkg.pkg_root)))
        {
            return None;
        }

        if !has_valid_turbo_entry {
            if strict_policy && spec.is_root_pkg {
                return None;
            }
            if allow_stale_hydration
                && !expected_lake_inputs.is_empty()
                && !is_git_pinned_manifest_package(cfg, spec)
                && package_by_root(cfg, &spec.pkg_root).is_some_and(|p| !p.inputs.is_empty())
                && source_uses_include_str(&src_raw)
                && input_bearing_libs_for_module(cfg, &spec.module_name).is_empty()
                && input_bearing_exes_for_module(cfg, &spec.module_name).is_empty()
            {
                return None;
            }
            if spec.native_unsupported.is_some()
                || spec.link_unsupported.is_some()
                || (spec.precompile_modules && !spec.extern_lib_digests.is_empty())
            {
                return None;
            }
            if !cache.ignore_mtime_skew {
                let ot = fs::metadata(&olean_path).ok()?.modified().ok()?;
                let st = fs::metadata(&spec.src_path).ok()?.modified().ok()?;
                if ot < st {
                    return None;
                }
                for root in [&spec.pkg_root, &cfg.root_pkg.pkg_root] {
                    for name in [
                        "lakefile.lean",
                        "lakefile.toml",
                        "lake-manifest.json",
                        "lean-toolchain",
                    ] {
                        if let Ok(cm) = fs::metadata(root.join(name)) {
                            if cm.modified().map_or(true, |ct| ot < ct) {
                                return None;
                            }
                        }
                    }
                }
            }
        }

        let mut import_entries = Vec::new();
        let mut trans_trace = 1723u64;
        let mut meta_trans_trace = 1723u64;
        let mut all_trans_trace = 1723u64;
        let mut legacy_trans_trace = 1723u64;
        let hdr_vis_map = header_direct_import_visibilities(&hdr);
        for sub_imp in &hdr.import_specs {
            let site = match resolve_module_in_package(&cfg.root_pkg, true, &sub_imp.module) {
                Some(root_spec) => ImportSite::Module(Box::new(root_spec)),
                None => resolve_import_site(cfg, &sub_imp.module),
            };
            let recorded_pin_spec = manifest_entry
                .as_ref()
                .and_then(|e| entry_import_pin_spec(e, &hdr, &hdr_vis_map, &sub_imp.module));
            match site {
                ImportSite::Toolchain => {
                    if manifest_entry.is_some() && recorded_pin_spec.is_some() {
                        return None;
                    }
                }
                ImportSite::Prebuilt(pb_olean) => {
                    if let Some(pin_spec) = recorded_pin_spec {
                        if !olean_digest_is(cfg, &pb_olean, pin_spec.full_pin) {
                            return None;
                        }
                    } else if manifest_entry.is_some() {
                        return None;
                    }
                    if collect_pairs {
                        local_pairs.push((sub_imp.module.clone(), pb_olean.clone()));
                    }
                    let sub_exp = prebuilt_closure_export_info(
                        cfg,
                        strict_policy,
                        &pb_olean,
                        cache,
                        visiting,
                        pb_visiting,
                        if collect_pairs {
                            Some(&mut local_pairs)
                        } else {
                            None
                        },
                    )?;
                    for e in lake_import_trace_entries(is_mod, sub_imp, &sub_exp) {
                        import_entries.push(e);
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
                ImportSite::Module(sub_spec) => {
                    let sub_olean = spec_olean_path(&sub_spec);
                    if let Some(pin_spec) = recorded_pin_spec {
                        let pin_matches = if let Some(cutoff_ok) = cache.matches_cutoff_pin(
                            &sub_spec.pkg_root,
                            &sub_spec.module_name,
                            &pin_spec,
                        ) {
                            cutoff_ok
                        } else {
                            olean_digest_is(cfg, &sub_olean, pin_spec.full_pin)
                                || fs::read_to_string(&sub_spec.src_path)
                                    .ok()
                                    .map(|s| parse_header_info(&s))
                                    .filter(|sh| sh.header_error.is_none() && sh.is_module)
                                    .is_some_and(|_| match pin_spec.tier_pin {
                                        Some((DepImportVisibility::PublicExport, exp)) => {
                                            !exp.is_empty()
                                                && compute_dep_export_olean_digest_with_policy(
                                                    &sub_olean, true,
                                                )
                                                .is_ok_and(|d| d == exp)
                                        }
                                        Some((DepImportVisibility::MetaExport, meta)) => {
                                            !meta.is_empty()
                                                && compute_dep_meta_olean_digest_with_policy(
                                                    &sub_olean, true,
                                                )
                                                .is_ok_and(|d| d == meta)
                                        }
                                        _ => false,
                                    })
                        };
                        if !pin_matches {
                            return None;
                        }
                    } else if manifest_entry.is_some()
                        || cache.allows_cutoff_parsed_import(
                            &sub_spec.pkg_root,
                            &sub_spec.module_name,
                            is_mod,
                            sub_imp,
                        ) == Some(false)
                    {
                        return None;
                    }
                    if collect_pairs {
                        local_pairs.push((sub_imp.module.clone(), sub_olean));
                    }
                    let sub_exp = lake_closure_export_info_inner(
                        cfg,
                        &sub_spec,
                        strict_policy,
                        cache,
                        visiting,
                        pb_visiting,
                        if collect_pairs {
                            Some(&mut local_pairs)
                        } else {
                            None
                        },
                    )?;
                    for e in lake_import_trace_entries(is_mod, sub_imp, &sub_exp) {
                        import_entries.push(e);
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
                ImportSite::Unresolved => return None,
            }
        }
        if let Some(ref entry) = manifest_entry {
            if !entry
                .import_olean_digests
                .keys()
                .all(|k| hdr.imports.contains(k))
                || !entry
                    .import_export_digests
                    .keys()
                    .all(|k| hdr.imports.contains(k))
                || !entry
                    .import_meta_digests
                    .keys()
                    .all(|k| hdr.imports.contains(k))
            {
                return None;
            }
        } else {
            let tv: serde_json::Value =
                serde_json::from_slice(&fs::read(olean_path.with_extension("trace")).ok()?).ok()?;
            let src_h = lake_hash_text(&src_raw);
            if tv.get("inputs").is_none() {
                let actual_dep_h = tv
                    .get("depHash")
                    .and_then(|v| v.as_str())
                    .filter(|s| is_valid_16hex_hash(s))
                    .and_then(|s| u64::from_str_radix(s, 16).ok())?;
                if !spec.custom_target_needs.is_empty() {
                    if !spec_in_clean_git_pinned_manifest_package(cfg, spec, cache) {
                        return None;
                    }
                } else {
                    let expected_dep_h = compute_expected_lake_module_dep_hash(
                        cfg,
                        &spec.pkg_root,
                        &spec.pkg_name,
                        &spec.pkg_base_name,
                        &spec.target_name,
                        spec.is_exe_target,
                        &spec.module_name,
                        is_mod,
                        spec.platform_independent,
                        &spec.lean_options,
                        &spec.strong_args,
                        &spec.src_path,
                        src_h,
                        import_entries,
                        &[],
                    )?;
                    if actual_dep_h != expected_dep_h {
                        return None;
                    }
                }
            } else {
                let expected_gh = format!(
                    "{:016x}",
                    lake_hash_bytes(cfg.lean_githash.trim().as_bytes())
                );
                let expected_src = format!("{:016x}", src_h);
                let expected_is_mod =
                    format!("{:016x}", lake_mix_hash(1723, if is_mod { 11 } else { 13 }));
                let expected_mod_name = format!("{:016x}", lake_hash_name(&spec.module_name));
                let expected_pkg_id = format!("{:016x}", lake_hash_pkg_id(&spec.pkg_name));
                let expected_imports_h = if import_entries.is_empty() {
                    1723u64
                } else {
                    lake_input_hash(&serde_json::Value::Array(import_entries)).ok()?
                };
                let nested = lake_trace_uses_nested_mod_deps(&cfg.toolchain);
                let expected_first_tag = format!("{}:deps", spec.module_name);
                if tv.pointer("/inputs/0/0").and_then(|v| v.as_str())
                    != Some(if nested {
                        expected_first_tag.as_str()
                    } else {
                        "deps"
                    })
                {
                    return None;
                }
                let actual_imports_h = recorded_trace_imports_hash(&tv)?;
                let actual_extra_dep_h = tv
                    .pointer(if nested {
                        "/inputs/0/1/0/1/0/1"
                    } else {
                        "/inputs/0/1/0/1"
                    })
                    .and_then(|v| lake_input_hash(v).ok())?;
                let empty_libs = (0..4).fold(1723u64, |acc, _| lake_mix_hash(acc, 1723));
                let has_plat_entry = spec.platform_independent == Some(false);
                let actual_libs_h = if nested && spec.platform_independent == Some(true) {
                    empty_libs
                } else {
                    let libs_pair =
                        tv.pointer(if nested { "/inputs/0/1/1" } else { "/inputs/1" })?;
                    if libs_pair.get(0).and_then(|v| v.as_str()) != Some("libs") {
                        return None;
                    }
                    lake_input_hash(libs_pair.get(1)?).ok()?
                };
                let base_pkg_name = if spec.pkg_base_name.is_empty() {
                    &spec.pkg_name
                } else {
                    &spec.pkg_base_name
                };
                let pkg_base_ident = if base_pkg_name.contains('-') {
                    format!("«{}»", base_pkg_name)
                } else {
                    base_pkg_name.clone()
                };
                let mut extra_dep_entries = vec![serde_json::json!([
                    format!("@{}:extraDep", pkg_base_ident),
                    format!("{LAKE_NIL_HASH:016x}")
                ])];
                if let Some(pkg) = package_by_root(cfg, &spec.pkg_root) {
                    let needs: &[String] = if spec.is_exe_target {
                        pkg.exes
                            .iter()
                            .find(|e| e.name == spec.target_name && e.root == spec.module_name)
                            .map_or(&[], |e| e.needs.as_slice())
                    } else {
                        pkg.libs
                            .iter()
                            .find(|l| {
                                l.name == spec.target_name
                                    && lib_can_build_module(l, &spec.module_name)
                            })
                            .map_or(&[], |l| l.needs.as_slice())
                    };
                    extra_dep_entries.extend(
                        needs
                            .iter()
                            .filter_map(|n| pkg.inputs.iter().find(|i| &i.name == n))
                            .map(|i| {
                                serde_json::json!([
                                    pkg.pkg_root.join(&i.path).to_string_lossy(),
                                    i.lake_hash
                                ])
                            }),
                    );
                }
                let expected_extra_dep_h =
                    lake_input_hash(&serde_json::Value::Array(extra_dep_entries)).ok()?;
                let base_idx = if nested {
                    1usize
                } else if has_plat_entry {
                    3usize
                } else {
                    2usize
                };
                if nested {
                    let expected_nested_len = match spec.platform_independent {
                        Some(true) => 1usize,
                        Some(false) => 3usize,
                        None => 2usize,
                    };
                    if tv
                        .pointer("/inputs/0/1")
                        .and_then(|v| v.as_array())
                        .is_none_or(|a| a.len() != expected_nested_len)
                    {
                        return None;
                    }
                }
                if has_plat_entry {
                    let tc_spec = query_toolchain_native_spec(&cfg.lean_bin).ok()?;
                    if tc_spec.target.is_empty() {
                        return None;
                    }
                    let expected_plat_h =
                        format!("{:016x}", lake_hash_bytes(tc_spec.target.as_bytes()));
                    let plat_pair =
                        tv.pointer(if nested { "/inputs/0/1/2" } else { "/inputs/2" })?;
                    if plat_pair.get(0).and_then(|v| v.as_str()) != Some(tc_spec.target.as_str())
                        || plat_pair.get(1).and_then(|v| v.as_str())
                            != Some(expected_plat_h.as_str())
                    {
                        return None;
                    }
                }
                let expected_len = base_idx + 7;
                let inputs_arr = tv.get("inputs").and_then(|v| v.as_array())?;
                let expected_opts_and_args_ok =
                    verify_lake_trace_options_and_args(spec, &tv, base_idx + 2);
                let extra_dep_ok = if !spec.custom_target_needs.is_empty() {
                    spec_in_clean_git_pinned_manifest_package(cfg, spec, cache)
                } else {
                    actual_extra_dep_h == expected_extra_dep_h
                };
                if actual_imports_h != expected_imports_h
                    || !extra_dep_ok
                    || actual_libs_h != empty_libs
                    || inputs_arr
                        .get(base_idx)
                        .and_then(|v| v.get(1))
                        .and_then(|v| v.as_str())
                        != Some(expected_gh.as_str())
                    || inputs_arr
                        .get(base_idx + 1)
                        .and_then(|v| v.get(1))
                        .and_then(|v| v.as_str())
                        != Some(expected_src.as_str())
                    || !expected_opts_and_args_ok
                    || inputs_arr
                        .get(base_idx + 3)
                        .and_then(|v| v.get(1))
                        .and_then(|v| v.as_str())
                        != Some(expected_is_mod.as_str())
                    || inputs_arr
                        .get(base_idx + 4)
                        .and_then(|v| v.get(1))
                        .and_then(|v| v.as_str())
                        != Some(expected_mod_name.as_str())
                    || inputs_arr
                        .get(base_idx + 5)
                        .and_then(|v| v.get(1))
                        .and_then(|v| v.as_str())
                        != Some(expected_pkg_id.as_str())
                    || inputs_arr.len() != expected_len
                {
                    return None;
                }
            }
        }
        Some(LakeModuleExportInfo {
            arts_trace,
            meta_arts_trace,
            all_arts_trace,
            trans_trace,
            meta_trans_trace,
            all_trans_trace,
            legacy_trans_trace,
        })
    })();
    visiting.remove(&visit_key);
    if let Some(info) = res {
        cache.exp_memo.insert(memo_key, Some(info));
        if let Some(out_pairs) = out_closure_opt {
            out_pairs.extend(local_pairs);
        }
    } else if out_closure_opt.is_none() && !had_cycle_ancestor {
        cache.exp_memo.insert(memo_key, None);
    }
    res
}

/// Check-time counterpart of `collect_fresh_dep_pkg_closure` for a dependency-package module
/// pinned at `pin` (memoizing verified nodes in `memo`): every visited module's artifacts must
/// match its manifest entry (by stat fingerprint, else by re-hashing), its source must match the
/// entry, and every import of that source must be pinned to the current artifacts (root- and
/// dependency-package modules recursively, root ones kernel-audited under `strict_policy`;
/// prebuilt imports re-digested).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OwnedImportPinSpec {
    pub(crate) full_pin: String,
    pub(crate) tier_pin: Option<(DepImportVisibility, String)>,
}

impl OwnedImportPinSpec {
    pub(crate) fn from_spec(spec: ImportPinSpec<'_>) -> Self {
        Self {
            full_pin: spec.full_pin.to_string(),
            tier_pin: spec.tier_pin.map(|(v, d)| (v, d.to_string())),
        }
    }

    pub(crate) fn as_spec(&self) -> ImportPinSpec<'_> {
        ImportPinSpec {
            full_pin: &self.full_pin,
            tier_pin: self.tier_pin.as_ref().map(|(v, d)| (*v, d.as_str())),
        }
    }
}

pub(crate) fn dep_pkg_import_pins_consistent(
    cfg: &ProjectConfig,
    memo: &DepImportMemo,
    cache: &mut LakeClosureCache,
    spec: DiscoveredModuleSpec,
    pin_spec: ImportPinSpec<'_>,
    strict_policy: bool,
) -> bool {
    let Ok(expected_lake_inputs) = workspace_lake_inputs_digest(cfg) else {
        return false;
    };
    let mut seen: HashMap<(PathBuf, String), String> = HashMap::new();
    let mut stack = vec![(spec, OwnedImportPinSpec::from_spec(pin_spec))];
    let use_global_memo = cache.cutoff_pins.is_empty()
        && !cache.post_lake_refresh
        && !cache.allow_stale_manifest_hydration;
    while let Some((cur, req)) = stack.pop() {
        let key = (cur.pkg_root.clone(), cur.module_name.clone());
        let req_spec = req.as_spec();
        if let Some(cutoff_ok) = cache.matches_cutoff_pin(&key.0, &key.1, &req_spec) {
            if !cutoff_ok {
                return false;
            }
            continue;
        }
        let rel_src = spec_rel_src(&cur);
        let (raw_has_entry, raw_is_some, raw_pkg_matched_entry, validated_entry) = {
            let Some(cached_manifest) =
                load_cached_pkg_manifest(&mut cache.manifests, cfg, &cur, strict_policy)
            else {
                return false;
            };
            let raw_has = matches!(
                cached_manifest.raw.as_ref(),
                Some(Ok(m)) if m.modules.contains_key(&rel_src)
            );
            let raw_some = cached_manifest.raw.is_some();
            let raw_matched = if !strict_policy && cache.allow_stale_manifest_hydration {
                match (
                    cached_manifest.raw.as_ref(),
                    package_by_root(cfg, &cur.pkg_root),
                ) {
                    (Some(Ok(m)), Some(pkg))
                        if m.pkg_name == pkg.name
                            && m.toolchain == cfg.toolchain
                            && m.lean_githash == cfg.lean_githash
                            && m.pkg_config_digest == pkg.config_digest =>
                    {
                        m.modules.get(&rel_src).cloned()
                    }
                    _ => None,
                }
            } else {
                None
            };
            let val = cached_manifest
                .validated
                .as_ref()
                .and_then(|m| m.modules.get(&rel_src))
                .cloned();
            (raw_has, raw_some, raw_matched, val)
        };
        let entry_opt = match validated_entry {
            Some(e) => Some(e),
            None => match raw_pkg_matched_entry {
                Some(raw_e) if !cache.module_closure_depends_on_lake_inputs(cfg, &cur) => {
                    Some(raw_e)
                }
                _ => None,
            },
        };
        let Some(entry) = entry_opt else {
            let olean_path = spec_olean_path(&cur);
            let pin_matches_lake = olean_digest_is(cfg, &olean_path, &req.full_pin)
                || fs::read_to_string(&cur.src_path)
                    .ok()
                    .map(|s| parse_header_info(&s))
                    .filter(|sh| sh.header_error.is_none() && sh.is_module)
                    .is_some_and(|_| match req.tier_pin.as_ref() {
                        Some((DepImportVisibility::PublicExport, exp)) => {
                            !exp.is_empty()
                                && compute_dep_export_olean_digest_with_policy(&olean_path, true)
                                    .is_ok_and(|d| d == *exp)
                        }
                        Some((DepImportVisibility::MetaExport, meta)) => {
                            !meta.is_empty()
                                && compute_dep_meta_olean_digest_with_policy(&olean_path, true)
                                    .is_ok_and(|d| d == *meta)
                        }
                        _ => false,
                    });
            if (strict_policy && (cur.is_root_pkg || !is_git_pinned_manifest_package(cfg, &cur)))
                || (raw_has_entry && !cache.allow_stale_manifest_hydration)
                || (!cache.post_lake_refresh
                    && !cache.allow_stale_manifest_hydration
                    && !expected_lake_inputs.is_empty()
                    && ((cur.is_root_pkg && raw_is_some)
                        || (!is_git_pinned_manifest_package(cfg, &cur)
                            && package_by_root(cfg, &cur.pkg_root)
                                .is_some_and(|p| !p.inputs.is_empty()))))
                || !pin_matches_lake
            {
                return false;
            }
            let mut visiting = HashSet::new();
            if lake_closure_export_info(cfg, &cur, strict_policy, cache, &mut visiting).is_none() {
                return false;
            }
            if let Ok(actual_full) =
                compute_olean_artifact_set_digest_with_policy(&olean_path, true)
            {
                seen.insert(key, actual_full);
            }
            continue;
        };
        let olean_path = spec_olean_path(&cur);
        let Ok(src) = fs::read_to_string(&cur.src_path) else {
            return false;
        };
        // One classification per module; see the matching caller above.
        let host_taint = spec_source_host_effect_taint(cfg, &cur, &src);
        if spec_source_stamp_ineligible_given_taint(cfg, &cur, &src, host_taint)
            || (!cache.post_lake_refresh
                && (strict_policy
                    || crate::lake_build::worktree_auto_link_disabled(&cfg.root_pkg.pkg_root))
                && host_taint.is_tainted())
        {
            return false;
        }
        let hdr = parse_header_info(&src);
        if hdr.header_error.is_some()
            || !entry_matches_import_pin_spec(&olean_path, &entry, hdr.is_module, &req.as_spec())
        {
            return false;
        }
        let actual_pin = entry.olean_artifact_digest.clone();
        let memo_key = (key.0.clone(), key.1.clone(), actual_pin.clone());
        let cache_pin_key = (
            key.0.clone(),
            key.1.clone(),
            actual_pin.clone(),
            strict_policy,
            cache.allow_stale_manifest_hydration,
        );
        if cache.pinned_memo.contains(&cache_pin_key)
            || (strict_policy
                && use_global_memo
                && memo.0.lock().is_ok_and(|m| m.contains(&memo_key)))
        {
            continue;
        }
        if let Some(prev) = seen.get(&key) {
            if *prev != actual_pin {
                return false;
            }
            continue;
        }
        let entry_inputs_ok = entry.lake_inputs_digest == expected_lake_inputs
            || (!strict_policy
                && cache.allow_stale_manifest_hydration
                && !cache.module_closure_depends_on_lake_inputs(cfg, &cur));
        let artifacts_ok = (!strict_policy || !cur.is_root_pkg || entry.kernel_audited)
            && entry_inputs_ok
            && entry_artifacts_current(cfg, &olean_path, &entry);
        let src_ok = blake3::hash(src.as_bytes()).to_hex().as_str() == entry.src_blake3;
        let sidecars_ok = verify_module_lake_sidecars(
            &olean_path,
            Some(&cur.build_ir_dir),
            &module_name_to_rel_slash(&cur.module_name),
            &src,
            hdr.is_module,
            cur.precompile_modules || cur.emit_c_default || cur.is_exe_target || hdr.has_c_export,
        )
        .is_ok();
        let pins_ok = sidecars_ok
            && verified_entry_imports_current_for_header(&entry, &hdr, |imp, sub_pin| {
                let site = match resolve_module_in_package(&cfg.root_pkg, true, imp) {
                    Some(root_spec) => ImportSite::Module(Box::new(root_spec)),
                    None => resolve_import_site(cfg, imp),
                };
                match (site, sub_pin) {
                    (ImportSite::Toolchain, None) => true,
                    (ImportSite::Prebuilt(o), Some(p)) => {
                        olean_digest_is(cfg, &o, p.full_pin)
                            && prebuilt_olean_export_info(cfg, strict_policy, &o, cache).is_some()
                    }
                    (ImportSite::Module(sub), Some(p)) => {
                        stack.push((*sub, OwnedImportPinSpec::from_spec(p)));
                        true
                    }
                    _ => false,
                }
            });
        if !c_abi::verify_module_cache_key(true, true, src_ok, artifacts_ok && pins_ok, true) {
            return false;
        }
        seen.insert(key, actual_pin);
    }
    for ((pkg, module), pin) in &seen {
        cache.pinned_memo.insert((
            pkg.clone(),
            module.clone(),
            pin.clone(),
            strict_policy,
            cache.allow_stale_manifest_hydration,
        ));
    }
    if strict_policy && use_global_memo {
        if let Ok(mut m) = memo.0.lock() {
            m.extend(
                seen.into_iter()
                    .map(|((pkg, module), pin)| (pkg, module, pin)),
            );
        }
    }
    true
}

pub(super) fn lean_version_requires_ir_sig(version: &str) -> bool {
    let mut parts = version.trim_start_matches('v').split('.');
    match (
        parts.next().and_then(|s| s.parse::<u32>().ok()),
        parts.next().and_then(|s| s.parse::<u32>().ok()),
    ) {
        (Some(major), Some(minor)) => (major, minor) >= (4, 33),
        _ => true,
    }
}

pub(crate) fn olean_requires_ir_sig(olean_path: &Path) -> bool {
    read_olean_header_version_and_githash(olean_path)
        .is_none_or(|(version, _)| lean_version_requires_ir_sig(&version))
}

pub(super) fn module_ir_sig_hash(olean_path: &Path, require_sidecars: bool) -> Result<Option<u64>> {
    if !olean_requires_ir_sig(olean_path) {
        return Ok(None);
    }
    verify_and_hash_artifact_bytes(
        &olean_path.with_extension("ir.sig"),
        require_sidecars,
        require_sidecars,
    )
    .map(Some)
}

pub(super) fn compute_module_arts_traces(
    olean_path: &Path,
    is_mod: bool,
    require_sidecars: bool,
) -> Result<(u64, u64, u64)> {
    let olean_h = verify_and_hash_artifact_bytes(olean_path, require_sidecars, require_sidecars)?;
    let arts_trace = lake_mix_hash(1723, olean_h);
    if !is_mod {
        return Ok((arts_trace, arts_trace, arts_trace));
    }
    let srv_path = PathBuf::from(format!("{}.server", olean_path.display()));
    let priv_path = PathBuf::from(format!("{}.private", olean_path.display()));
    let ir_path = olean_path.with_extension("ir");
    let srv_h = verify_and_hash_artifact_bytes(&srv_path, require_sidecars, require_sidecars)?;
    let priv_h = verify_and_hash_artifact_bytes(&priv_path, require_sidecars, require_sidecars)?;
    let ir_sig_h = module_ir_sig_hash(olean_path, require_sidecars)?;
    let ir_h = verify_and_hash_artifact_bytes(&ir_path, require_sidecars, require_sidecars)?;
    let Some(ir_sig_h) = ir_sig_h else {
        let meta_t = lake_mix_hash(arts_trace, ir_h);
        return Ok((
            arts_trace,
            meta_t,
            lake_mix_hash(lake_mix_hash(meta_t, srv_h), priv_h),
        ));
    };
    let meta_t = lake_mix_hash(lake_mix_hash(lake_mix_hash(1723, olean_h), ir_sig_h), ir_h);
    let all_t = lake_mix_hash(
        lake_mix_hash(
            lake_mix_hash(lake_mix_hash(lake_mix_hash(1723, olean_h), srv_h), priv_h),
            ir_sig_h,
        ),
        ir_h,
    );
    Ok((arts_trace, meta_t, all_t))
}

pub(super) fn verify_trace_outputs_against_artifacts_ext(
    olean_path: &Path,
    is_module: bool,
    c_req: Option<(&Path, bool)>,
    allow_stock_missing_c_outputs: bool,
) -> Result<serde_json::Value> {
    let olean_h = verify_and_hash_artifact_bytes(olean_path, true, true)?;
    let ilean_h = verify_and_hash_artifact_bytes(&olean_path.with_extension("ilean"), true, true)?;
    let srv_path = PathBuf::from(format!("{}.server", olean_path.display()));
    let priv_path = PathBuf::from(format!("{}.private", olean_path.display()));
    let ir_path = olean_path.with_extension("ir");
    let mod_comp_hashes = if is_module {
        Some((
            verify_and_hash_artifact_bytes(&srv_path, true, true)?,
            verify_and_hash_artifact_bytes(&priv_path, true, true)?,
            module_ir_sig_hash(olean_path, true)?,
            verify_and_hash_artifact_bytes(&ir_path, true, true)?,
        ))
    } else {
        None
    };
    let c_h_opt = match c_req {
        Some((cp, needs_c)) if cp.exists() || needs_c => {
            Some(verify_and_hash_artifact_bytes(cp, true, true)?)
        }
        _ => None,
    };
    let trace_path = olean_path.with_extension("trace");
    if !trace_path.is_file() {
        anyhow::bail!(
            "Required Lake module trace `{}` is missing",
            trace_path.display()
        );
    }
    let tb = fs::read(&trace_path)?;
    let tv: serde_json::Value = serde_json::from_slice(&tb).map_err(|_| {
        anyhow::anyhow!(
            "Malformed JSON in Lake module trace `{}`",
            trace_path.display()
        )
    })?;
    let expected_o = format!("{:016x}.olean", olean_h);
    let expected_i = format!("{:016x}.ilean", ilean_h);
    let dep_hash_ok = if let Some(inputs_val) = tv.get("inputs") {
        let expected_dep_h = format!("{:016x}", lake_input_hash(inputs_val)?);
        tv.get("depHash").and_then(|v| v.as_str()) == Some(expected_dep_h.as_str())
    } else {
        tv.get("depHash")
            .and_then(|v| v.as_str())
            .is_some_and(is_valid_16hex_hash)
    };
    if tv.get("schemaVersion").and_then(|v| v.as_str()) != Some("2025-09-10") || !dep_hash_ok {
        anyhow::bail!(
            "Lake module trace `{}` failed integrity verification against artifacts",
            trace_path.display()
        );
    }
    if let Some(c_h) = c_h_opt {
        let expected_c = format!("{:016x}.c", c_h);
        let nil_c = format!("{LAKE_NIL_HASH:016x}.c");
        let c_out_ok = match tv.pointer("/outputs/c").and_then(|v| v.as_str()) {
            Some(s) => s == expected_c || (allow_stock_missing_c_outputs && s == nil_c),
            None => allow_stock_missing_c_outputs && tv.pointer("/outputs/o/0").is_some(),
        };
        if tv.pointer("/outputs/m").and_then(|v| v.as_bool()) != Some(is_module)
            || tv.pointer("/outputs/o/0").and_then(|v| v.as_str()) != Some(expected_o.as_str())
            || tv.pointer("/outputs/i").and_then(|v| v.as_str()) != Some(expected_i.as_str())
            || !c_out_ok
        {
            anyhow::bail!(
                "Lake module trace `{}` failed integrity verification against artifacts",
                trace_path.display()
            );
        }
        if let Some((srv_h, priv_h, ir_sig_h_opt, ir_h)) = mod_comp_hashes {
            let rs_ok = match (ir_sig_h_opt, tv.pointer("/outputs/rs")) {
                (Some(ir_sig_h), Some(rs_val)) => {
                    rs_val.as_str() == Some(format!("{:016x}.ir.sig", ir_sig_h).as_str())
                }
                (None, None) => true,
                _ => false,
            };
            if tv.pointer("/outputs/o/1").and_then(|v| v.as_str())
                != Some(format!("{:016x}.olean.server", srv_h).as_str())
                || tv.pointer("/outputs/o/2").and_then(|v| v.as_str())
                    != Some(format!("{:016x}.olean.private", priv_h).as_str())
                || !rs_ok
                || tv.pointer("/outputs/r").and_then(|v| v.as_str())
                    != Some(format!("{:016x}.ir", ir_h).as_str())
            {
                anyhow::bail!(
                    "Lake module trace `{}` module companion outputs do not match artifacts",
                    trace_path.display()
                );
            }
        }
    } else if allow_stock_missing_c_outputs && tv.get("outputs") != Some(&serde_json::Value::Null) {
        if tv.pointer("/outputs/m").and_then(|v| v.as_bool()) != Some(is_module)
            || tv.pointer("/outputs/o/0").and_then(|v| v.as_str()) != Some(expected_o.as_str())
            || tv.pointer("/outputs/i").and_then(|v| v.as_str()) != Some(expected_i.as_str())
        {
            anyhow::bail!(
                "Lake module trace `{}` failed integrity verification against artifacts",
                trace_path.display()
            );
        }
        if let Some((srv_h, priv_h, ir_sig_h_opt, ir_h)) = mod_comp_hashes {
            let rs_ok = match (ir_sig_h_opt, tv.pointer("/outputs/rs")) {
                (Some(ir_sig_h), Some(rs_val)) => {
                    rs_val.as_str() == Some(format!("{:016x}.ir.sig", ir_sig_h).as_str())
                }
                (None, None) => true,
                _ => false,
            };
            if tv.pointer("/outputs/o/1").and_then(|v| v.as_str())
                != Some(format!("{:016x}.olean.server", srv_h).as_str())
                || tv.pointer("/outputs/o/2").and_then(|v| v.as_str())
                    != Some(format!("{:016x}.olean.private", priv_h).as_str())
                || !rs_ok
                || tv.pointer("/outputs/r").and_then(|v| v.as_str())
                    != Some(format!("{:016x}.ir", ir_h).as_str())
            {
                anyhow::bail!(
                    "Lake module trace `{}` module companion outputs do not match artifacts",
                    trace_path.display()
                );
            }
        }
        if let Some((cp, _)) = c_req {
            if PathBuf::from(format!("{}.hash", cp.display())).exists() {
                anyhow::bail!(
                    "Stale `.c.hash` present without `.c` artifact alongside `{}`",
                    trace_path.display()
                );
            }
        }
    } else {
        if tv.get("outputs") != Some(&serde_json::Value::Null) {
            anyhow::bail!(
                "Lake module trace `{}` must record `\"outputs\": null` when `.c` is absent",
                trace_path.display()
            );
        }
        if let Some((cp, _)) = c_req {
            if PathBuf::from(format!("{}.hash", cp.display())).exists() {
                anyhow::bail!(
                    "Stale `.c.hash` present without `.c` artifact alongside `{}`",
                    trace_path.display()
                );
            }
        }
    }
    Ok(tv)
}

pub(super) fn verify_trace_outputs_against_artifacts_with_existing_c_ext(
    olean_path: &Path,
    is_module: bool,
    allow_stock_missing_c_outputs: bool,
) -> Result<serde_json::Value> {
    let olean_str = olean_path.to_string_lossy();
    let inferred_c = olean_str
        .rfind("/lib/lean/")
        .or_else(|| olean_str.rfind("\\lib\\lean\\"))
        .and_then(|idx| {
            let prefix = &olean_str[..idx];
            let sep = &olean_str[idx..idx + 1];
            let rest = &olean_str[idx + "/lib/lean/".len()..];
            let rel_no_ext = rest.strip_suffix(".olean")?;
            Some(PathBuf::from(format!("{prefix}{sep}ir{sep}{rel_no_ext}.c")))
        });
    verify_trace_outputs_against_artifacts_ext(
        olean_path,
        is_module,
        inferred_c.as_deref().map(|p| (p, false)),
        allow_stock_missing_c_outputs,
    )
}

pub(crate) fn custom_cc_env_digest_tag() -> String {
    let mut out = String::new();
    for var in ["LEAN_CC", "CC"] {
        if let Ok(val) = std::env::var(var) {
            let trimmed = val.trim();
            if !trimmed.is_empty() {
                let p = Path::new(trimmed);
                let canon = p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
                let meta_tag = fs::metadata(&canon)
                    .map(|m| {
                        let mtime = m
                            .modified()
                            .ok()
                            .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                            .map(|d| format!("{}.{}", d.as_secs(), d.subsec_nanos()))
                            .unwrap_or_else(|| "0".to_string());
                        format!("len={}:mtime={}", m.len(), mtime)
                    })
                    .unwrap_or_else(|_| "missing".to_string());
                out.push_str(&format!("{var}={}:{meta_tag};", canon.to_string_lossy()));
            }
        }
    }
    out
}

pub(crate) fn verify_project_native_and_c_sidecars_up_to_date(
    cfg: &ProjectConfig,
    targets: &[String],
) -> bool {
    let Ok(dag) = build_module_dag_with_trust(cfg, targets, false) else {
        return false;
    };
    for node in dag.nodes.values() {
        if node.needs_c {
            if !is_regular_nonempty_file(&node.c_path) {
                return false;
            }
            let Ok(src_raw) = fs::read_to_string(&node.src_path) else {
                return false;
            };
            let rel_slash = module_name_to_rel_slash(&node.module_name);
            let ir_dir = node
                .c_path
                .to_string_lossy()
                .strip_suffix(&format!("{rel_slash}.c"))
                .map(|s| PathBuf::from(s.trim_end_matches('/')));
            if verify_module_lake_sidecars(
                &node.olean_path,
                ir_dir.as_deref(),
                &rel_slash,
                &src_raw,
                node.is_module,
                true,
            )
            .is_err()
            {
                return false;
            }
        }
        if node.needs_co_export {
            let co_p = module_co_export_path(node);
            if verify_native_facet_sidecar(&co_p).is_err() {
                return false;
            }
            let c_mtime = fs::metadata(&node.c_path).and_then(|m| m.modified()).ok();
            let co_mtime = fs::metadata(&co_p).and_then(|m| m.modified()).ok();
            if !matches!((c_mtime, co_mtime), (Some(cm), Some(om)) if om >= cm) {
                return false;
            }
        }
        if node.needs_dynlib || node.precompile_modules {
            let setup_p = module_setup_json_path(node);
            if !is_regular_nonempty_file(&setup_p) {
                return false;
            }
        }
        if node.needs_dynlib {
            let Some(so_p) = module_dynlib_so_path(node) else {
                return false;
            };
            if verify_native_facet_sidecar(&so_p).is_err() {
                return false;
            }
            let rsp_p = PathBuf::from(format!("{}.rsp", so_p.display()));
            if !is_regular_nonempty_file(&rsp_p) {
                return false;
            }
            let co_p = module_co_export_path(node);
            let co_mtime = fs::metadata(&co_p).and_then(|m| m.modified()).ok();
            let so_mtime = fs::metadata(&so_p).and_then(|m| m.modified()).ok();
            if !matches!((co_mtime, so_mtime), (Some(cm), Some(sm)) if sm >= cm) {
                return false;
            }
        }
    }
    for sl in &dag.shared_libs {
        if verify_native_facet_sidecar(&sl.path).is_err() {
            return false;
        }
        let rsp_p = PathBuf::from(format!("{}.rsp", sl.path.display()));
        if !is_regular_nonempty_file(&rsp_p) {
            return false;
        }
        let Some(sl_mtime) = fs::metadata(&sl.path).and_then(|m| m.modified()).ok() else {
            return false;
        };
        for m in &sl.local_modules {
            if let Some(ln) = dag.nodes.get(m) {
                let co_p = module_co_export_path(ln);
                if fs::metadata(&co_p)
                    .and_then(|md| md.modified())
                    .map_or(true, |cm| sl_mtime < cm)
                {
                    return false;
                }
            }
        }
    }
    if !crate::lake_build::worktree_auto_link_disabled(&cfg.root_pkg.pkg_root) {
        let (exe_targets, _) = resolve_requested_exe_link_targets(cfg, targets);
        for exe_t in &exe_targets {
            if !is_regular_nonempty_file(&exe_t.binary_path) {
                return false;
            }
            let Some(bin_mtime) = fs::metadata(&exe_t.binary_path)
                .and_then(|m| m.modified())
                .ok()
            else {
                return false;
            };
            for node in dag.nodes.values() {
                if node.needs_c
                    && fs::metadata(&node.c_path)
                        .and_then(|m| m.modified())
                        .map_or(true, |cm| bin_mtime < cm)
                {
                    return false;
                }
            }
        }
    }
    true
}

pub(crate) fn verify_native_facet_sidecar(path: &Path) -> Result<()> {
    let h = verify_and_hash_artifact_bytes(path, true, true)?;
    let trace_path = PathBuf::from(format!("{}.trace", path.display()));
    if !is_regular_nonempty_file(&trace_path) {
        anyhow::bail!("Missing native facet trace `{}`", trace_path.display());
    }
    let tb = fs::read(&trace_path)?;
    let tv: serde_json::Value = serde_json::from_slice(&tb).with_context(|| {
        format!(
            "Malformed JSON in native facet trace `{}`",
            trace_path.display()
        )
    })?;
    let expected_dep_h = format!("{:016x}", lake_input_hash(&tv["inputs"])?);
    if tv.get("schemaVersion").and_then(|v| v.as_str()) != Some("2025-09-10")
        || tv.get("depHash").and_then(|v| v.as_str()) != Some(expected_dep_h.as_str())
    {
        anyhow::bail!(
            "Native facet trace `{}` failed depHash verification",
            trace_path.display()
        );
    }
    let expected_prefix = format!("{:016x}.", h);
    if !tv
        .get("outputs")
        .and_then(|v| v.as_str())
        .is_some_and(|s| s.starts_with(&expected_prefix))
    {
        anyhow::bail!(
            "Native facet trace `{}` outputs do not match `{}`",
            trace_path.display(),
            path.display()
        );
    }
    Ok(())
}

pub(crate) fn verify_module_lake_sidecars(
    olean_path: &Path,
    ir_dir_opt: Option<&Path>,
    rel_slash: &str,
    src_raw: &str,
    is_module: bool,
    needs_c: bool,
) -> Result<()> {
    verify_module_lake_sidecars_inner_opts(
        olean_path, ir_dir_opt, rel_slash, src_raw, is_module, needs_c, false, true,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn verify_module_lake_sidecars_inner_opts(
    olean_path: &Path,
    ir_dir_opt: Option<&Path>,
    rel_slash: &str,
    src_raw: &str,
    is_module: bool,
    needs_c: bool,
    require_inputs: bool,
    check_src_hash: bool,
) -> Result<()> {
    verify_module_lake_sidecars_inner_opts_ext(
        olean_path,
        ir_dir_opt,
        rel_slash,
        src_raw,
        is_module,
        needs_c,
        require_inputs,
        check_src_hash,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_module_lake_sidecars_inner_opts_ext(
    olean_path: &Path,
    ir_dir_opt: Option<&Path>,
    rel_slash: &str,
    src_raw: &str,
    is_module: bool,
    needs_c: bool,
    require_inputs: bool,
    check_src_hash: bool,
    allow_stock_missing_c_outputs: bool,
) -> Result<()> {
    let c_path = ir_dir_opt.map(|d| d.join(format!("{}.c", rel_slash)));
    let tv = verify_trace_outputs_against_artifacts_ext(
        olean_path,
        is_module,
        c_path.as_deref().map(|p| (p, needs_c)),
        allow_stock_missing_c_outputs,
    )?;
    if require_inputs && tv.get("inputs").is_none() {
        anyhow::bail!(
            "Lake module trace `{}` lacks full `inputs` array",
            olean_path.with_extension("trace").display()
        );
    }
    if check_src_hash && tv.get("inputs").is_some() {
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
                "Lake module trace `{}` recorded source hash does not match source",
                olean_path.with_extension("trace").display()
            );
        }
    }
    Ok(())
}
/// Verify whether every module in `dag` already has up-to-date, Lake-trace-coherent artifacts
/// on disk (matching `cfg.lean_githash`, exact source hash, exact strong Lean options/args,
/// exact `needs` Lake input hashes, and exact transitive `LakeModuleExportInfo` import trace
/// hashes). Used by trusted `pr-verify` statement builds on a checkout already populated by
/// `lake build` or `turbo-lean build`; callers still enforce full source hygiene and Zygote
/// in-kernel replay/soundness audit afterward.
pub(crate) fn are_dag_modules_fresh_by_lake_trace(cfg: &ProjectConfig, dag: &ModuleDag) -> bool {
    let empty_proof_only = HashSet::new();
    find_dirty_modules_in_otherwise_fresh_dag(cfg, dag, 0, &empty_proof_only)
        .map(|dirty| dirty.is_empty())
        .unwrap_or(false)
}

/// Returns `Some(dirty_modules)` (in topological wave order) when at most `max_dirty` modules in
/// `dag` need recompilation, and **every** other module in `dag` has intact, Lake-trace-coherent
/// artifacts against the existing `.lake/build` tree.
///
/// Modules in `proof_only_src_hashes` map `mod_name -> expected_base_lake_src_hash_hex`: if a
/// module's on-disk `.trace` matches `expected_base_lake_src_hash_hex` and only theorem proof
/// bodies changed relative to that base source (verified by caller via splitter), the module itself
/// is added to `dirty_mods` so its new `.olean` is compiled into the overlay, while downstream
/// importers whose `.trace` still matches the pre-edit `.lake/build` exports do NOT need to be
/// recompiled (they are still kernel-replayed against the new overlay `.olean`).
pub(crate) fn find_dirty_modules_in_otherwise_fresh_dag(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    max_dirty: usize,
    proof_only_base_trace_src_hashes: &HashSet<(String, String)>,
) -> Option<Vec<String>> {
    let mut exp_memo: HashMap<(String, bool), LakeModuleExportInfo> = HashMap::new();
    let nil_hex = format!("{LAKE_NIL_HASH:016x}");
    let expected_lean_gh_h = format!("{:016x}", lake_hash_bytes(cfg.lean_githash.as_bytes()));
    let nested = lake_trace_uses_nested_mod_deps(&cfg.toolchain);
    let allow_dirty = max_dirty > 0;
    let mut dirty_mods: Vec<String> = Vec::new();
    let mut cascading_dirty_mods: HashSet<String> = HashSet::new();
    for wave in &dag.waves {
        for mod_name in wave {
            let node = dag.nodes.get(mod_name)?;
            let src_raw = fs::read_to_string(&node.src_path).ok()?;
            if blake3::hash(src_raw.as_bytes()).to_hex().as_str() != node.src_blake3 {
                return None;
            }
            let src_has_elab_host_effects =
                node_source_has_disallowed_elab_host_effects(cfg, node, &src_raw);
            let header = parse_header_info(&src_raw);
            if header.header_error.is_some() || header.is_module != node.is_module {
                return None;
            }
            let rel_slash = module_name_to_rel_slash(mod_name);
            let ir_dir = node
                .pkg_root
                .join(&cfg.root_pkg.build_dir)
                .join(&cfg.root_pkg.ir_dir);
            let sidecars_ok = verify_module_lake_sidecars_inner_opts_ext(
                &node.olean_path,
                node.needs_c.then_some(ir_dir.as_path()),
                &rel_slash,
                &src_raw,
                node.is_module,
                node.needs_c,
                false,
                false,
                !node.needs_c,
            );
            let mark_dirty = |dirty_mods: &mut Vec<String>,
                              cascading: &mut HashSet<String>,
                              cascades: bool|
             -> Option<()> {
                if !allow_dirty || dirty_mods.len() >= max_dirty {
                    return None;
                }
                if !dirty_mods.iter().any(|m| m == mod_name) {
                    dirty_mods.push(mod_name.clone());
                }
                if cascades {
                    cascading.insert(mod_name.clone());
                }
                Some(())
            };
            if src_has_elab_host_effects || sidecars_ok.is_err() {
                mark_dirty(&mut dirty_mods, &mut cascading_dirty_mods, true)?;
                continue;
            }
            let Ok(tb) = fs::read(node.olean_path.with_extension("trace")) else {
                mark_dirty(&mut dirty_mods, &mut cascading_dirty_mods, true)?;
                continue;
            };
            let Ok(tv) = serde_json::from_slice::<serde_json::Value>(&tb) else {
                mark_dirty(&mut dirty_mods, &mut cascading_dirty_mods, true)?;
                continue;
            };
            let mut import_entries = Vec::new();
            let mut visiting = HashSet::new();
            let mut imp_dirty = false;
            for imp in &header.import_specs {
                if cascading_dirty_mods.contains(&imp.module) {
                    imp_dirty = true;
                    break;
                }
                let is_ws_or_pkg = dag.nodes.contains_key(&imp.module)
                    || node
                        .external_olean_deps
                        .iter()
                        .any(|(m, _)| m == &imp.module)
                    || resolve_module_in_package(&cfg.root_pkg, true, &imp.module).is_some()
                    || cfg
                        .dep_pkgs
                        .iter()
                        .any(|dp| resolve_module_in_package(dp, false, &imp.module).is_some());
                if !is_ws_or_pkg {
                    if is_builtin_toolchain_module(
                        &cfg.toolchain_lib_lean,
                        Some(&cfg.lean_githash),
                        &imp.module,
                    ) {
                        continue;
                    }
                    return None;
                }
                let exp_res = compute_lake_export_info_opts(
                    cfg,
                    dag,
                    node,
                    &imp.module,
                    &mut exp_memo,
                    &mut visiting,
                    allow_dirty,
                );
                let Ok(exp_info) = exp_res else {
                    imp_dirty = true;
                    break;
                };
                import_entries.extend(lake_import_trace_entries(node.is_module, imp, &exp_info));
            }
            if imp_dirty {
                mark_dirty(&mut dirty_mods, &mut cascading_dirty_mods, true)?;
                continue;
            }
            let src_h = lake_hash_text(&src_raw);
            if tv.get("inputs").is_none() {
                let raw_imp_dynlibs = compute_module_raw_import_dynlibs(dag, node);
                let actual_dep_h = tv
                    .get("depHash")
                    .and_then(|v| v.as_str())
                    .filter(|s| is_valid_16hex_hash(s))
                    .and_then(|s| u64::from_str_radix(s, 16).ok());
                let expected_dep_h = compute_expected_lake_module_dep_hash(
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
                if actual_dep_h.is_none() || actual_dep_h != expected_dep_h {
                    mark_dirty(&mut dirty_mods, &mut cascading_dirty_mods, true)?;
                }
                continue;
            }
            let expected_src_h = format!("{:016x}", src_h);
            let recorded_src_h = trace_recorded_src_hash(&tv);
            let mut src_is_proof_only_dirty = false;
            if recorded_src_h != Some(expected_src_h.as_str()) {
                let matches_proof_only_base = recorded_src_h.is_some_and(|rec| {
                    proof_only_base_trace_src_hashes.contains(&(mod_name.clone(), rec.to_string()))
                });
                if !matches_proof_only_base {
                    mark_dirty(&mut dirty_mods, &mut cascading_dirty_mods, true)?;
                    continue;
                }
                src_is_proof_only_dirty = true;
            }
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
                return None;
            }
            if tv
                .pointer(&format!("/inputs/{}/0", base_idx + 2))
                .and_then(|v| v.as_str())
                != Some("options")
                || tv
                    .pointer(&format!("/inputs/{}/1", base_idx + 2))
                    .is_none_or(|v| !verify_trace_options_value(&node.lean_options, v))
            {
                return None;
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
                return None;
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
                return None;
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
            extra_dep_entries.extend(lake_needs_trace_entries(cfg, node));
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
                return None;
            }
            let expected_imps_val = if import_entries.is_empty() {
                serde_json::json!("00000000000006bb")
            } else {
                serde_json::Value::Array(import_entries)
            };
            let expected_imps_h = lake_input_hash(&expected_imps_val).ok();
            let actual_imps_h = recorded_trace_imports_hash(&tv);
            if expected_imps_h.is_none() || expected_imps_h != actual_imps_h {
                mark_dirty(&mut dirty_mods, &mut cascading_dirty_mods, true)?;
                continue;
            }
            if src_is_proof_only_dirty {
                mark_dirty(&mut dirty_mods, &mut cascading_dirty_mods, false)?;
                continue;
            }
        }
    }
    Some(dirty_mods)
}

pub(super) fn is_clean_git_pinned_pkg(
    cfg: &ProjectConfig,
    is_root_pkg: bool,
    pkg_name: &str,
    pkg_base_name: &str,
    pkg_root: &Path,
) -> bool {
    !is_root_pkg
        && manifest_pinned_git_rev_for_pkg(cfg, pkg_name, pkg_base_name, pkg_root).is_some_and(
            |rev| is_clean_pinned_git_checkout(pkg_root, rev, package_by_root(cfg, pkg_root)),
        )
}

pub(super) fn is_git_pinned_manifest_package(cfg: &ProjectConfig, spec: &DiscoveredModuleSpec) -> bool {
    is_clean_git_pinned_pkg(
        cfg,
        spec.is_root_pkg,
        &spec.pkg_name,
        &spec.pkg_base_name,
        &spec.pkg_root,
    )
}

#[allow(clippy::type_complexity)]
pub(super) struct DepClosureMemo {
    pub(super) expected_lake_inputs: Option<String>,
    pub(super) manifests: HashMap<(PathBuf, bool), CachedPkgManifest>,
    pub(super) lake_closure_cache: LakeClosureCache,
    pub(super) search_dirs: Vec<PathBuf>,
    pub(super) fresh_closure: HashMap<(PathBuf, String, bool), Result<Option<Vec<(String, PathBuf)>>, String>>,
    pub(super) prebuilt_closure:
        HashMap<(PathBuf, String, bool, bool), Result<Option<Vec<(String, PathBuf)>>, String>>,
    pub(super) pb_olean_closure: HashMap<(String, PathBuf), Option<Vec<(String, PathBuf)>>>,
    pub(super) unshadowed_tc: HashMap<String, bool>,
    pub(super) dep_mod_memo: HashMap<String, Vec<DiscoveredModuleSpec>>,
    pub(super) root_mod_memo: HashMap<String, Option<DiscoveredModuleSpec>>,
    pub(super) prebuilt_unit_memo:
        HashMap<(PathBuf, String, bool, bool), Result<Option<(PathBuf, Vec<String>)>, String>>,
}

impl DepClosureMemo {
    pub(super) fn new(cfg: &ProjectConfig) -> Self {
        let (eff_lp, _) = build_lean_search_path(cfg, false);
        Self {
            expected_lake_inputs: workspace_lake_inputs_digest(cfg).ok(),
            manifests: HashMap::new(),
            lake_closure_cache: LakeClosureCache {
                ignore_mtime_skew: true,
                ..Default::default()
            },
            search_dirs: std::env::split_paths(&eff_lp).collect(),
            fresh_closure: HashMap::new(),
            prebuilt_closure: HashMap::new(),
            pb_olean_closure: HashMap::new(),
            unshadowed_tc: HashMap::new(),
            dep_mod_memo: HashMap::new(),
            root_mod_memo: HashMap::new(),
            prebuilt_unit_memo: HashMap::new(),
        }
    }

    pub(super) fn resolve_dep_pkg_matches(
        &mut self,
        cfg: &ProjectConfig,
        imp: &str,
    ) -> &[DiscoveredModuleSpec] {
        if !self.dep_mod_memo.contains_key(imp) {
            let matches: Vec<DiscoveredModuleSpec> = cfg
                .dep_pkgs
                .iter()
                .filter_map(|dp| resolve_importable_module_in_package(dp, false, imp))
                .collect();
            self.dep_mod_memo.insert(imp.to_string(), matches);
        }
        self.dep_mod_memo.get(imp).map(Vec::as_slice).unwrap_or(&[])
    }

    pub(super) fn resolve_root_pkg_importable(
        &mut self,
        cfg: &ProjectConfig,
        imp: &str,
    ) -> Option<DiscoveredModuleSpec> {
        if let Some(cached) = self.root_mod_memo.get(imp) {
            return cached.clone();
        }
        let spec = resolve_importable_module_in_package(&cfg.root_pkg, true, imp);
        self.root_mod_memo.insert(imp.to_string(), spec.clone());
        spec
    }

    pub(super) fn is_unshadowed_toolchain(&mut self, cfg: &ProjectConfig, imp: &str) -> bool {
        if let Some(&v) = self.unshadowed_tc.get(imp) {
            return v;
        }
        let v = is_unshadowed_toolchain_olean_import(cfg, &self.search_dirs, imp, false);
        self.unshadowed_tc.insert(imp.to_string(), v);
        v
    }

    pub(super) fn collect_prebuilt_olean_closure(
        &mut self,
        cfg: &ProjectConfig,
        imp: &str,
        pb_path: &Path,
    ) -> Option<Vec<(String, PathBuf)>> {
        let key = (imp.to_string(), pb_path.to_path_buf());
        if let Some(res) = self.pb_olean_closure.get(&key) {
            return res.clone();
        }
        let mut mod_visiting = HashSet::new();
        let mut pb_visiting = HashSet::new();
        let mut pairs = vec![(imp.to_string(), pb_path.to_path_buf())];
        let res = prebuilt_closure_export_info(
            cfg,
            false,
            pb_path,
            &mut self.lake_closure_cache,
            &mut mod_visiting,
            &mut pb_visiting,
            Some(&mut pairs),
        )
        .map(|_| {
            pairs.sort_by(|a, b| a.0.cmp(&b.0));
            pairs.dedup_by(|a, b| a.0 == b.0);
            pairs
        });
        self.pb_olean_closure.insert(key, res.clone());
        res
    }
}

pub(super) fn is_dep_olean_fresh(
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
    src_content: &str,
    is_module: bool,
    imports: &[String],
    olean_path: &Path,
    memo: &mut DepClosureMemo,
) -> Option<std::time::SystemTime> {
    let pkg_root = &spec.pkg_root;
    let src_path = &spec.src_path;
    if !is_regular_nonempty_file(olean_path) {
        return None;
    }
    if !cfg.lean_githash.is_empty() && cfg.lean_githash != "lean-not-installed" {
        let (_, actual_bgh) = read_olean_header_version_and_githash(olean_path)?;
        if !actual_bgh.eq_ignore_ascii_case(cfg.lean_githash.trim()) {
            return None;
        }
    } else if cfg.lean_bin.as_os_str().is_empty() || cfg.lean_githash == "lean-not-installed" {
        return None;
    }
    let om = fs::metadata(olean_path).ok()?;
    if is_module {
        let srv_path = PathBuf::from(format!("{}.server", olean_path.display()));
        let priv_path = PathBuf::from(format!("{}.private", olean_path.display()));
        if !is_regular_nonempty_file(&srv_path) || !is_regular_nonempty_file(&priv_path) {
            return None;
        }
    }
    let ot = om.modified().ok()?;
    // Under `--frozen-cone` the raw mtime gates stand down: the manifest checks below verify the
    // source bytes, the artifact set, and every import edge by content hash, which is exactly
    // what a hardlinked / CAS-restored cone with skewed mtimes still satisfies (#339).
    let opt_out = crate::lake_build::worktree_auto_link_disabled(&cfg.root_pkg.pkg_root)
        && !frozen_cone_enabled();
    if opt_out {
        if let Ok(sm) = fs::metadata(src_path) {
            if let Ok(st) = sm.modified() {
                if ot < st {
                    return None;
                }
            }
        }
        for cfg_file in ["lakefile.toml", "lakefile.lean", "lean-toolchain"] {
            if let Ok(cm) = fs::metadata(pkg_root.join(cfg_file)) {
                if let Ok(ct) = cm.modified() {
                    if ot < ct {
                        return None;
                    }
                }
            }
        }
    }
    // Local coherence manifest verification via `.lake/build/.turbo_verified_sources.json`
    // (trusted mode only; untrusted builds never call `collect_fresh_dep_pkg_closure` and never
    // accept pre-existing checkout `.olean` files without host `TurboStore` CAS verification).
    // Fail closed (`None`) when the manifest or audited module entry is absent or stale.
    let expected_lake_inputs = memo.expected_lake_inputs.as_deref()?;
    let manifest = load_cached_pkg_manifest(&mut memo.manifests, cfg, spec, true)?
        .validated
        .as_ref()?;
    let rel_src = src_path
        .strip_prefix(pkg_root)
        .unwrap_or(src_path)
        .to_string_lossy()
        .replace('\\', "/");
    let entry = manifest.modules.get(&rel_src)?;
    // The entry answers for itself, so re-stamping the header above cannot promote an entry
    // recorded against older input bytes (an entry written before this field existed reads as the
    // empty string and is only accepted for a workspace that declares no inputs).
    if entry.lake_inputs_digest != expected_lake_inputs {
        return None;
    }
    let actual_src_hash = blake3::hash(src_content.as_bytes()).to_hex().to_string();
    if entry.src_blake3 != actual_src_hash {
        return None;
    }
    let preserve = crate::lake_build::worktree_auto_link_disabled(&cfg.root_pkg.pkg_root);
    let actual_olean_digest =
        compute_olean_artifact_set_digest_with_policy(olean_path, preserve).ok()?;
    if entry.olean_artifact_digest != actual_olean_digest {
        return None;
    }
    // Same-package pins compare against `manifest`; other packages' against their on-disk
    // artifacts. `collect_fresh_dep_pkg_closure` verifies every visited module the same way.
    let lake_closure_cache = &mut memo.lake_closure_cache;
    let pins_ok = verified_entry_imports_current(entry, imports, |imp, pin| {
        if resolve_module_in_package(&cfg.root_pkg, true, imp).is_some() {
            return false;
        }
        match (resolve_import_site(cfg, imp), pin) {
            (ImportSite::Toolchain, None) => true,
            (ImportSite::Module(d), Some(pin)) if d.pkg_root == spec.pkg_root => manifest
                .modules
                .get(&spec_rel_src(&d))
                .is_some_and(|e| e.olean_artifact_digest == pin),
            (ImportSite::Module(d), Some(pin)) => {
                compute_olean_artifact_set_digest_with_policy(&spec_olean_path(&d), preserve)
                    .is_ok_and(|dig| dig == pin)
            }
            (ImportSite::Prebuilt(olean), Some(pin)) => {
                compute_olean_artifact_set_digest_with_policy(&olean, preserve)
                    .is_ok_and(|dig| dig == pin)
                    && prebuilt_olean_export_info(cfg, false, &olean, lake_closure_cache).is_some()
            }
            _ => false,
        }
    });
    // Toolchain, configuration, and source were matched above.
    if !c_abi::verify_module_cache_key(true, true, true, pins_ok, true) {
        return None;
    }
    let rel_slash = module_name_to_rel_slash(&spec.module_name);
    let hdr = parse_header_info(src_content);
    if verify_module_lake_sidecars(
        olean_path,
        Some(&spec.build_ir_dir),
        &rel_slash,
        src_content,
        is_module,
        spec.precompile_modules || spec.emit_c_default || spec.is_exe_target || hdr.has_c_export,
    )
    .is_err()
    {
        return None;
    }
    Some(ot)
}

/// Inspect a dependency package module and its transitive imports across `dep_pkgs` in trusted mode.
/// Returns `Ok(Some(transitive_olean_pairs))` only if every module in the dependency closure
/// has a fresh `.olean` verified against the local coherence manifest `.turbo_verified_sources.json`
/// and `olean_mtime(parent) >= olean_mtime(child)` holds along every import edge.
/// Returns `Ok(None)` if any module in the closure is missing or unverified.
/// Returns `Err` if a module import resolves ambiguously across multiple dependency packages.
pub(super) fn collect_fresh_dep_pkg_closure(
    cfg: &ProjectConfig,
    initial_spec: &DiscoveredModuleSpec,
    importer_needs_import_dynlibs: bool,
    importer_needs_c: bool,
    memo: &mut DepClosureMemo,
) -> Result<Option<Vec<(String, PathBuf)>>> {
    if initial_spec.precompile_modules || importer_needs_import_dynlibs {
        return Ok(None);
    }
    let memo_key = (
        initial_spec.pkg_root.clone(),
        initial_spec.module_name.clone(),
        importer_needs_c,
    );
    if let Some(cached) = memo.fresh_closure.get(&memo_key) {
        return match cached {
            Ok(v) => Ok(v.clone()),
            Err(msg) => anyhow::bail!("{msg}"),
        };
    }
    let res: Result<Option<Vec<(String, PathBuf)>>> = (|| {
        let mut visited: HashSet<(PathBuf, String)> = HashSet::new();
        let mut queue: VecDeque<(DiscoveredModuleSpec, Option<std::time::SystemTime>)> =
            VecDeque::new();
        let mut olean_pairs = Vec::new();
        visited.insert((
            initial_spec.pkg_root.clone(),
            initial_spec.module_name.clone(),
        ));
        queue.push_back((initial_spec.clone(), None));
        while let Some((cur, parent_olean_mtime)) = queue.pop_front() {
            let Ok(src) = fs::read_to_string(&cur.src_path) else {
                return Ok(None);
            };
            if !cur.is_root_pkg && is_git_pinned_manifest_package(cfg, &cur) {
                splitter::reject_git_pinned_dep_checking_weakening(&src).with_context(|| {
                    format!("Module {} ({})", cur.module_name, cur.src_path.display())
                })?;
            } else {
                splitter::reject_checking_weakening(&src).with_context(|| {
                    format!("Module {} ({})", cur.module_name, cur.src_path.display())
                })?;
            }
            if spec_source_has_disallowed_elab_host_effects(cfg, &cur, &src) {
                return Ok(None);
            }
            let hdr = parse_header_info(&src);
            if hdr.header_error.is_some() {
                return Ok(None);
            }
            let rel_slash = module_name_to_rel_slash(&cur.module_name);
            let olean_path = cur.build_lib_lean_dir.join(format!("{}.olean", rel_slash));
            let Some(cur_olean_mtime) = is_dep_olean_fresh(
                cfg,
                &cur,
                &src,
                hdr.is_module,
                &hdr.imports,
                &olean_path,
                memo,
            ) else {
                return Ok(None);
            };
            if importer_needs_c
                && verify_module_lake_sidecars(
                    &olean_path,
                    Some(&cur.build_ir_dir),
                    &rel_slash,
                    &src,
                    hdr.is_module,
                    true,
                )
                .is_err()
            {
                return Ok(None);
            }
            // Verify parent `.olean` is at least as new as child `.olean` when opt-out requires raw mtime parity;
            // otherwise `is_dep_olean_fresh` already cryptographically verified `import_olean_digests` pins across every edge.
            // A `--frozen-cone` pack's hardlinks carry arbitrary relative mtimes, so the parity
            // gate also stands down there in favor of those per-edge content pins (#339).
            if crate::lake_build::worktree_auto_link_disabled(&cfg.root_pkg.pkg_root)
                && !frozen_cone_enabled()
            {
                if let Some(parent_mt) = parent_olean_mtime {
                    if parent_mt < cur_olean_mtime {
                        return Ok(None);
                    }
                }
            }
            if cur.pkg_root != initial_spec.pkg_root || cur.module_name != initial_spec.module_name
            {
                let sub_key = (
                    cur.pkg_root.clone(),
                    cur.module_name.clone(),
                    importer_needs_c,
                );
                if let Some(sub_cached) = memo.fresh_closure.get(&sub_key) {
                    match sub_cached {
                        Ok(Some(sub_pairs)) => {
                            olean_pairs.extend(sub_pairs.iter().cloned());
                            continue;
                        }
                        Ok(None) => return Ok(None),
                        Err(msg) => anyhow::bail!("{msg}"),
                    }
                }
            }
            olean_pairs.push((cur.module_name.clone(), olean_path));
            for imp in hdr.imports {
                let matches = memo.resolve_dep_pkg_matches(cfg, &imp);
                if matches.len() > 1 {
                    let pkg_names: Vec<String> =
                        matches.iter().map(|m| m.pkg_name.clone()).collect();
                    anyhow::bail!(
                        "Ambiguous module import `{}` (imported by `{}`) resolved in multiple dependency packages: {:?}",
                        imp,
                        cur.module_name,
                        pkg_names
                    );
                }
                if let Some(sub_spec) = matches.first().cloned() {
                    if sub_spec.precompile_modules {
                        return Ok(None);
                    }
                    let key = (sub_spec.pkg_root.clone(), sub_spec.module_name.clone());
                    if visited.insert(key) {
                        queue.push_back((sub_spec, Some(cur_olean_mtime)));
                    }
                    continue;
                }
                if memo.resolve_root_pkg_importable(cfg, &imp).is_some() {
                    return Ok(None);
                }
                match resolve_import_site(cfg, &imp) {
                    ImportSite::Toolchain if memo.is_unshadowed_toolchain(cfg, &imp) => {
                        continue;
                    }
                    ImportSite::Prebuilt(pb_path) => {
                        if let Some(pb_closure) =
                            memo.collect_prebuilt_olean_closure(cfg, &imp, &pb_path)
                        {
                            olean_pairs.extend(pb_closure);
                            continue;
                        }
                    }
                    _ => {}
                }
                // Unresolved or shadowed import inside dependency closure: force native DAG traversal so
                // root-package/LEAN_PATH imports or missing-module errors are handled deterministically.
                return Ok(None);
            }
        }
        olean_pairs.sort_by(|a, b| a.0.cmp(&b.0));
        olean_pairs.dedup_by(|a, b| a.0 == b.0);
        Ok(Some(olean_pairs))
    })();
    memo.fresh_closure.insert(
        memo_key,
        match &res {
            Ok(v) => Ok(v.clone()),
            Err(e) => Err(format!("{e:#}")),
        },
    );
    res
}

pub(super) fn update_lp(h: &mut blake3::Hasher, tag: &[u8], data: &[u8]) {
    h.update(&(tag.len() as u64).to_le_bytes());
    h.update(tag);
    h.update(&(data.len() as u64).to_le_bytes());
    h.update(data);
}

pub(super) fn infer_pkg_root_from_artifact_path(artifact_path: &Path) -> Option<PathBuf> {
    let mut cur = artifact_path.parent();
    while let Some(dir) = cur {
        if dir.file_name().and_then(|s| s.to_str()) == Some("build") {
            if let Some(lake_dir) = dir.parent() {
                if lake_dir.file_name().and_then(|s| s.to_str()) == Some(".lake") {
                    return lake_dir.parent().map(|p| p.to_path_buf());
                }
            }
        }
        cur = dir.parent();
    }
    None
}

/// Compute combined BLAKE3 artifact digest for an `.olean` and any companion `.olean.server`,
/// `.olean.private`, `.ilean`, `.ir`, and `.ir.sig`, encoding explicit presence/absence markers,
/// acquiring the shared package publication flock (`LOCK_SH`) so readers never observe a mid-commit
/// state, and propagating I/O errors if an existing companion file cannot be read.
pub fn compute_olean_artifact_set_digest(olean_path: &Path) -> Result<String> {
    compute_olean_artifact_set_digest_with_policy(olean_path, false)
}

pub(crate) fn compute_olean_artifact_set_digest_preserve_lake(olean_path: &Path) -> Result<String> {
    compute_olean_artifact_set_digest_with_policy(olean_path, true)
}

pub(crate) fn compute_olean_artifact_set_digest_with_policy(
    olean_path: &Path,
    preserve_caller: bool,
) -> Result<String> {
    let window = current_memo_window();
    let art_paths = olean_artifact_paths(olean_path);
    let cur_stats = [
        path_olean_stat_sig(&art_paths[0].1),
        path_olean_stat_sig(&art_paths[1].1),
        path_olean_stat_sig(&art_paths[2].1),
        path_olean_stat_sig(&art_paths[3].1),
        path_olean_stat_sig(&art_paths[4].1),
        path_olean_stat_sig(&art_paths[5].1),
    ];
    let memo = OLEAN_ARTIFACT_SET_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
    if olean_stat_bundle6_trusted_for_reuse(&cur_stats) {
        if let Ok(g) = memo.lock() {
            if let Some((w, cached_stats, hit)) = g.get(olean_path) {
                if *w == window && *cached_stats == cur_stats {
                    return Ok(hit.clone());
                }
            }
        }
    }
    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock
        .lock()
        .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
    let _flock_guard = if let Some(pkg_root) = infer_pkg_root_from_artifact_path(olean_path) {
        Some(acquire_publish_flock_mode(
            &pkg_root,
            false,
            preserve_caller || crate::lake_build::worktree_auto_link_disabled(&pkg_root),
        )?)
    } else {
        None
    };
    let read_started_ns = crate::zygote::wall_clock_ns();
    let (res, bound_stats) =
        compute_olean_artifact_set_digest_bound(olean_path, _flock_guard.as_ref())?;
    let post_stats = [
        path_olean_stat_sig(&art_paths[0].1),
        path_olean_stat_sig(&art_paths[1].1),
        path_olean_stat_sig(&art_paths[2].1),
        path_olean_stat_sig(&art_paths[3].1),
        path_olean_stat_sig(&art_paths[4].1),
        path_olean_stat_sig(&art_paths[5].1),
    ];
    if let Some(fd_stats) = bound_stats {
        if post_stats == fd_stats && olean_stat_bundle6_trusted_to_store(&fd_stats, read_started_ns)
        {
            if let Ok(mut g) = memo.lock() {
                if current_memo_window() == window {
                    if g.len() >= 65536 {
                        g.clear();
                    }
                    g.insert(olean_path.to_path_buf(), (window, fd_stats, res.clone()));
                }
            }
        }
    }
    Ok(res)
}

pub(crate) fn olean_artifact_paths(olean_path: &Path) -> [(&'static str, PathBuf); 6] {
    let suffixed = |p: &Path, sfx: &str| PathBuf::from(format!("{}{}", p.display(), sfx));
    let ir = olean_path.with_extension("ir");
    [
        ("olean", olean_path.to_path_buf()),
        ("srv", suffixed(olean_path, ".server")),
        ("priv", suffixed(olean_path, ".private")),
        ("ilean", olean_path.with_extension("ilean")),
        ("ir", ir.clone()),
        ("ir_sig", suffixed(&ir, ".sig")),
    ]
}

pub(super) fn dep_export_olean_artifact_paths(olean_path: &Path) -> [(&'static str, PathBuf); 3] {
    let ir_path = olean_path.with_extension("ir");
    let ir_sig_path = PathBuf::from(format!("{}.sig", ir_path.display()));
    [
        ("olean", olean_path.to_path_buf()),
        ("ir", ir_path),
        ("ir_sig", ir_sig_path),
    ]
}

pub(super) fn dep_meta_olean_artifact_paths(olean_path: &Path) -> [(&'static str, PathBuf); 3] {
    let ir_path = olean_path.with_extension("ir");
    let ir_sig_path = PathBuf::from(format!("{}.sig", ir_path.display()));
    [
        ("olean", olean_path.to_path_buf()),
        ("ir", ir_path),
        ("ir_sig", ir_sig_path),
    ]
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum DepImportVisibility {
    PublicExport,
    MetaExport,
    All,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ModuleArtifactTierDigests {
    pub(crate) full: String,
    pub(crate) dep_export: String,
    pub(crate) dep_meta: String,
}

impl ModuleArtifactTierDigests {
    pub(crate) fn for_visibility(&self, vis: DepImportVisibility, dep_is_module: bool) -> String {
        if !dep_is_module {
            return self.full.clone();
        }
        match vis {
            DepImportVisibility::PublicExport => self.dep_export.clone(),
            DepImportVisibility::MetaExport => self.dep_meta.clone(),
            DepImportVisibility::All => self.full.clone(),
        }
    }
}

pub fn compute_dep_export_olean_digest(olean_path: &Path) -> Result<String> {
    compute_dep_export_olean_digest_with_policy(olean_path, false)
}

pub fn compute_dep_meta_olean_digest(olean_path: &Path) -> Result<String> {
    compute_dep_meta_olean_digest_with_policy(olean_path, false)
}

pub(crate) fn compute_dep_export_olean_digest_with_policy(
    olean_path: &Path,
    preserve_caller: bool,
) -> Result<String> {
    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock
        .lock()
        .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
    let _flock_guard = if let Some(pkg_root) = infer_pkg_root_from_artifact_path(olean_path) {
        Some(acquire_publish_flock_mode(
            &pkg_root,
            false,
            preserve_caller || crate::lake_build::worktree_auto_link_disabled(&pkg_root),
        )?)
    } else {
        None
    };
    read_tagged_olean_artifact_digest(
        b"olean-export-v2\n",
        &dep_export_olean_artifact_paths(olean_path),
        _flock_guard.as_ref(),
        |p| Ok(fs::read(p)?),
    )
}

pub(crate) fn compute_dep_meta_olean_digest_with_policy(
    olean_path: &Path,
    preserve_caller: bool,
) -> Result<String> {
    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock
        .lock()
        .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
    let _flock_guard = if let Some(pkg_root) = infer_pkg_root_from_artifact_path(olean_path) {
        Some(acquire_publish_flock_mode(
            &pkg_root,
            false,
            preserve_caller || crate::lake_build::worktree_auto_link_disabled(&pkg_root),
        )?)
    } else {
        None
    };
    read_tagged_olean_artifact_digest(
        b"olean-meta-v1\n",
        &dep_meta_olean_artifact_paths(olean_path),
        _flock_guard.as_ref(),
        |p| Ok(fs::read(p)?),
    )
}

pub(crate) fn compute_module_artifact_tier_digests_with_policy(
    olean_path: &Path,
    preserve_caller: bool,
) -> Result<ModuleArtifactTierDigests> {
    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock
        .lock()
        .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
    let _flock_guard = if let Some(pkg_root) = infer_pkg_root_from_artifact_path(olean_path) {
        Some(acquire_publish_flock_mode(
            &pkg_root,
            false,
            preserve_caller || crate::lake_build::worktree_auto_link_disabled(&pkg_root),
        )?)
    } else {
        None
    };
    compute_module_artifact_tier_digests_locked(olean_path, _flock_guard.as_ref())
}

pub(crate) fn compute_module_artifact_tier_digests_parallel_safe(
    olean_path: &Path,
    preserve_caller: bool,
) -> Result<ModuleArtifactTierDigests> {
    let _flock_guard = if let Some(pkg_root) = infer_pkg_root_from_artifact_path(olean_path) {
        Some(acquire_publish_flock_mode(
            &pkg_root,
            false,
            preserve_caller || crate::lake_build::worktree_auto_link_disabled(&pkg_root),
        )?)
    } else {
        None
    };
    compute_module_artifact_tier_digests_locked(olean_path, _flock_guard.as_ref())
}

pub(super) fn compute_module_artifact_tier_digests_locked(
    olean_path: &Path,
    guard: Option<&crate::shm_cache::PublishFlockGuard>,
) -> Result<ModuleArtifactTierDigests> {
    let artifacts = olean_artifact_paths(olean_path);
    let paths: Vec<_> = artifacts.iter().map(|(_, p)| p.clone()).collect();
    let compute = || {
        let mut present_hashes: [Option<[u8; 32]>; 6] = [None; 6];
        for (idx, (tag, path)) in artifacts.iter().enumerate() {
            let present = match fs::metadata(path) {
                Ok(meta) => {
                    anyhow::ensure!(
                        meta.is_file(),
                        "Artifact path `{}` is not a regular file",
                        path.display()
                    );
                    true
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound && *tag != "olean" => false,
                Err(e) => {
                    return Err(e)
                        .with_context(|| format!("Failed to stat artifact {}", path.display()))
                }
            };
            if present {
                let bytes = fs::read(path)
                    .with_context(|| format!("Failed to read artifact {}", path.display()))?;
                present_hashes[idx] = Some(*blake3::hash(&bytes).as_bytes());
            }
        }
        let fold_subset = |domain: &[u8], indices: &[usize]| -> String {
            let mut h = blake3::Hasher::new();
            h.update(domain);
            for &idx in indices {
                let tag = artifacts[idx].0;
                let hash_opt = present_hashes[idx].as_ref();
                if tag != "olean" {
                    h.update(&[u8::from(hash_opt.is_some())]);
                }
                if let Some(raw_hash) = hash_opt {
                    update_lp(&mut h, tag.as_bytes(), raw_hash);
                } else {
                    update_lp(&mut h, tag.as_bytes(), b"");
                }
            }
            h.finalize().to_hex().to_string()
        };
        Ok(ModuleArtifactTierDigests {
            full: fold_subset(b"olean-art-v2\n", &[0, 1, 2, 3, 4, 5]),
            dep_export: fold_subset(b"olean-export-v2\n", &[0, 4, 5]),
            dep_meta: fold_subset(b"olean-meta-v1\n", &[0, 4, 5]),
        })
    };
    match guard {
        Some(guard) => guard.read_consistent(&paths, compute),
        None => compute(),
    }
}

pub(super) fn compute_olean_artifact_set_digest_locked(
    olean_path: &Path,
    guard: Option<&crate::shm_cache::PublishFlockGuard>,
) -> Result<String> {
    compute_olean_artifact_set_digest_bound(olean_path, guard).map(|(dig, _)| dig)
}

pub(super) fn read_tagged_olean_artifact_digest(
    domain: &[u8],
    artifacts: &[(&'static str, PathBuf)],
    guard: Option<&crate::shm_cache::PublishFlockGuard>,
    mut read: impl FnMut(&Path) -> Result<Vec<u8>>,
) -> Result<String> {
    let paths: Vec<_> = artifacts.iter().map(|(_, p)| p.clone()).collect();
    let mut digest = || {
        let mut h = blake3::Hasher::new();
        h.update(domain);
        for (tag, path) in artifacts {
            let present = match fs::metadata(path) {
                Ok(meta) => {
                    anyhow::ensure!(
                        meta.is_file(),
                        "Artifact path `{}` is not a regular file",
                        path.display()
                    );
                    true
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound && *tag != "olean" => false,
                Err(e) => {
                    return Err(e)
                        .with_context(|| format!("Failed to stat artifact {}", path.display()))
                }
            };
            if *tag != "olean" {
                h.update(&[u8::from(present)]);
            }
            if present {
                let bytes = read(path)
                    .with_context(|| format!("Failed to read artifact {}", path.display()))?;
                update_lp(&mut h, tag.as_bytes(), blake3::hash(&bytes).as_bytes());
            } else {
                update_lp(&mut h, tag.as_bytes(), b"");
            }
        }
        Ok(h.finalize().to_hex().to_string())
    };
    match guard {
        Some(guard) => guard.read_consistent(&paths, digest),
        None => digest(),
    }
}

#[allow(clippy::type_complexity)]
pub(super) fn compute_olean_artifact_set_digest_bound(
    olean_path: &Path,
    guard: Option<&crate::shm_cache::PublishFlockGuard>,
) -> Result<(String, Option<[Option<crate::zygote::OleanFileStatSig>; 6]>)> {
    read_olean_artifact_set_digest_bound_with(olean_path, guard, |p| {
        read_regular_file_bound_stat(p)
    })
}

#[allow(clippy::type_complexity)]
pub(super) fn read_olean_artifact_set_digest_bound_with(
    olean_path: &Path,
    guard: Option<&crate::shm_cache::PublishFlockGuard>,
    mut read_bound: impl FnMut(
        &Path,
    ) -> std::io::Result<(
        crate::zygote::OleanFileStatSig,
        Vec<u8>,
        crate::zygote::OleanFileStatSig,
    )>,
) -> Result<(String, Option<[Option<crate::zygote::OleanFileStatSig>; 6]>)> {
    let artifacts = olean_artifact_paths(olean_path);
    let paths: Vec<_> = artifacts.iter().map(|(_, p)| p.clone()).collect();
    let mut digest = || {
        let mut h = blake3::Hasher::new();
        h.update(b"olean-art-v2\n");
        let mut stats: [Option<crate::zygote::OleanFileStatSig>; 6] = [None; 6];
        let mut all_fd_stable = true;
        for (idx, (tag, path)) in artifacts.iter().enumerate() {
            match read_bound(path) {
                Ok((pre, bytes, post)) => {
                    if pre == post {
                        stats[idx] = Some(post);
                    } else {
                        all_fd_stable = false;
                    }
                    if *tag != "olean" {
                        h.update(&[1u8]);
                    }
                    update_lp(&mut h, tag.as_bytes(), blake3::hash(&bytes).as_bytes());
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound && *tag != "olean" => {
                    h.update(&[0u8]);
                    update_lp(&mut h, tag.as_bytes(), b"");
                }
                Err(e) => {
                    return Err(e)
                        .with_context(|| format!("Failed to read artifact {}", path.display()))
                }
            }
        }
        Ok((
            h.finalize().to_hex().to_string(),
            all_fd_stable.then_some(stats),
        ))
    };
    match guard {
        Some(guard) => guard.read_consistent(&paths, digest),
        None => digest(),
    }
}


/// Wrap a [`workspace_lake_inputs_digest`] into the synthetic dependency-interface-hash entry.
/// The `NUL` prefix cannot collide with a `"<Module>:<hex>"` entry and sorts the tag first.
pub(crate) fn lake_inputs_tag_from_digest(digest: &str) -> Option<String> {
    (!digest.is_empty()).then(|| format!("\u{0}lake-inputs:{}", blake3::hash(digest.as_bytes())))
}

/// The workspace's Lake file inputs as a synthetic *dependency interface hash* entry, to be mixed
/// into the per-file dependency list that seeds [`crate::splitter::split_lean_source`] and
/// [`crate::lake_build::compute_file_split_key_with_deps`].
///
/// This is the single place that makes the content-derived caches input-aware. Those caches key a
/// file's splits, its theorem shards (through `prefix_env_hash`) and its proof-fission entries on
/// the `.lean` bytes plus the digests of what it imports -- none of which move when an `input_dir`
/// file is edited, so `check` on a module whose `rfl` reads that file reported `all_shards_cached`
/// and exited 0 against the old bytes. Adding one entry here moves `prefix_env_hash`, and with it
/// every key derived from it, for every reader and writer at once; threading a separate argument
/// through the ~20 call sites would have left any site that was missed silently serving the stale
/// result rather than merely missing the cache.
///
/// Deliberately workspace-wide rather than per-module. [`module_lake_input_digest`] is the precise
/// answer, but it needs a resolved [`ModuleNode`] that these paths do not have, and the cost of
/// being coarse is re-splitting and re-checking files that could not have read the input -- which
/// the project-wide rule ("a changed input never yields a cache hit") explicitly prefers to the
/// alternative.
///
/// `None` for a workspace that declares no inputs, so those keys are untouched.
///
/// Memoized per top-level command / request, keyed on the project directory *and the memo window
/// it was computed in*. This runs once per `.lean` file, and resolving the workspace re-reads every
/// declared input byte: measured at 33 ms per call for a 200-file `input_dir`, i.e. ~16 s on a
/// 500-module project, down to 0.4 ms amortized with the memo (and 104 µs → 3.5 µs for a project
/// that declares no inputs, where only the config scan runs). The memo is the form the reverted
/// `hash_input_target` memo's docstring identified as the safe one, and it is safe for the reason
/// that one was not: there is no `(len, mtime)` in the key, so a same-length write with a restored
/// mtime cannot be served a stale digest -- the only thing the memo asserts is that the inputs are
/// read once per window, which is already how every other config resolution behaves.
///
/// The window id is what makes the memo safe in a process that serves *concurrent* requests.
/// `serve` runs up to 64 handlers at once and `reset_lake_inputs_tag_memo` is called by each; a
/// handler that is still mid-request when the next one resets would otherwise publish the digest it
/// read before the reset into the new request's window, which is a hit against bytes that may no
/// longer exist. Every entry therefore records the window it was computed in,
/// [`project_lake_inputs_tag`] reads only entries from the window it entered, and
/// [`publish_lake_inputs_tag`] refuses to store one whose window has been superseded.
///
/// The price is that a superseded in-flight request stops memoizing and recomputes per `.lean`
/// file. That is the over-invalidating side of the trade the project-wide rule asks for, and it is
/// bounded to the overlap between two concurrent requests on the same project; the one-shot CLI
/// path, where the figures above were measured, has a single window and is unaffected.
pub(super) type LakeInputsTagMemoEntry = (u64, Option<String>);

pub(super) static LAKE_INPUTS_TAG_MEMO: OnceLock<Mutex<HashMap<PathBuf, LakeInputsTagMemoEntry>>> =
    OnceLock::new();

/// Counter for unique per-call nonces emitted when a non-`Result` caller asks for a Lake inputs
/// tag on a workspace whose Lake inputs are unsupported or unresolvable, guaranteeing zero cross-run
/// or cross-edit cache key collisions.
pub(super) static LAKE_INPUTS_UNRESOLVED_NONCE: AtomicU64 = AtomicU64::new(1);

pub(crate) fn fresh_unresolved_lake_inputs_tag(err: &str) -> String {
    let seq = LAKE_INPUTS_UNRESOLVED_NONCE.fetch_add(1, Ordering::Relaxed);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-unresolved-lake-inputs-nonce-v1:");
    h.update(&std::process::id().to_le_bytes());
    h.update(&seq.to_le_bytes());
    h.update(&nanos.to_le_bytes());
    h.update(err.as_bytes());
    format!("\u{0}lake-inputs-uncacheable:{}", h.finalize().to_hex())
}

/// Current memo window. Bumped by [`reset_lake_inputs_tag_memo`] before it takes the memo lock, so
/// a publication that observes the old value under that lock is necessarily one that started before
/// the reset.
pub(super) static LAKE_INPUTS_TAG_MEMO_WINDOW: AtomicU64 = AtomicU64::new(0);

pub(crate) fn current_memo_window() -> u64 {
    LAKE_INPUTS_TAG_MEMO_WINDOW.load(Ordering::SeqCst)
}

pub(crate) type FileStatFingerprint = Option<(i64, i64, i64)>;

#[inline]
pub(crate) fn path_stat_fingerprint(path: &Path) -> FileStatFingerprint {
    let meta = fs::metadata(path).ok()?;
    if !meta.is_file() {
        return None;
    }
    Some(TurboStore::extract_file_stat_tuple(&meta))
}

#[inline]
pub(crate) fn path_olean_stat_sig(path: &Path) -> Option<crate::zygote::OleanFileStatSig> {
    let meta = fs::metadata(path).ok()?;
    if !meta.is_file() {
        return None;
    }
    Some(crate::zygote::OleanFileStatSig::from_meta(&meta))
}

#[inline]
pub(crate) fn read_regular_file_bound_stat(
    path: &Path,
) -> std::io::Result<(
    crate::zygote::OleanFileStatSig,
    Vec<u8>,
    crate::zygote::OleanFileStatSig,
)> {
    use std::io::Read;
    let mut opts = fs::OpenOptions::new();
    opts.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.custom_flags(libc::O_NOFOLLOW);
    }
    let mut f = opts.open(path)?;
    let pre_meta = f.metadata()?;
    if !pre_meta.is_file() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("`{}` is not a regular file", path.display()),
        ));
    }
    let pre = crate::zygote::OleanFileStatSig::from_meta(&pre_meta);
    let mut bytes = Vec::with_capacity(pre.size as usize);
    f.read_to_end(&mut bytes)?;
    let post = crate::zygote::OleanFileStatSig::from_meta(&f.metadata()?);
    Ok((pre, bytes, post))
}

#[inline]
pub(crate) fn olean_stat_sig_trusted_at(
    sig: &crate::zygote::OleanFileStatSig,
    read_started_ns: i128,
) -> bool {
    crate::zygote::dev_records_subsecond_timestamps(sig)
        && read_started_ns > 0
        && sig.ctime_ns() < read_started_ns - crate::zygote::STAT_TRUST_WINDOW_NS
}

#[inline]
pub(crate) fn olean_stat_bundle_trusted_for_reuse(
    sigs: &[Option<crate::zygote::OleanFileStatSig>; 4],
) -> bool {
    sigs[0].is_some_and(|s| s.size > 0)
        && sigs
            .iter()
            .flatten()
            .all(crate::zygote::dev_records_subsecond_timestamps)
}

#[inline]
pub(crate) fn olean_stat_bundle_trusted_to_store(
    sigs: &[Option<crate::zygote::OleanFileStatSig>; 4],
    read_started_ns: i128,
) -> bool {
    sigs[0].is_some_and(|s| s.size > 0)
        && sigs
            .iter()
            .flatten()
            .all(|s| olean_stat_sig_trusted_at(s, read_started_ns))
}

#[inline]
pub(crate) fn olean_stat_bundle6_trusted_for_reuse(
    sigs: &[Option<crate::zygote::OleanFileStatSig>; 6],
) -> bool {
    sigs[0].is_some_and(|s| s.size > 0)
        && sigs
            .iter()
            .flatten()
            .all(crate::zygote::dev_records_subsecond_timestamps)
}

#[inline]
pub(crate) fn olean_stat_bundle6_trusted_to_store(
    sigs: &[Option<crate::zygote::OleanFileStatSig>; 6],
    read_started_ns: i128,
) -> bool {
    sigs[0].is_some_and(|s| s.size > 0)
        && sigs
            .iter()
            .flatten()
            .all(|s| olean_stat_sig_trusted_at(s, read_started_ns))
}

#[allow(clippy::type_complexity)]
pub(super) static REPLAYED_OLEAN_DIGEST_MEMO: OnceLock<
    Mutex<HashMap<PathBuf, (u64, [Option<crate::zygote::OleanFileStatSig>; 4], String)>>,
> = OnceLock::new();

#[allow(clippy::type_complexity)]
pub(super) static OLEAN_BINARY_IMPORTS_MEMO: OnceLock<
    Mutex<
        HashMap<
            PathBuf,
            (
                u64,
                crate::zygote::OleanFileStatSig,
                Vec<ParsedImport>,
                bool,
            ),
        >,
    >,
> = OnceLock::new();

#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(super) struct OleanImportClosureEntry {
    pub(super) window: u64,
    pub(super) tracked_stats: Arc<Vec<(PathBuf, FileStatFingerprint)>>,
    pub(super) resolved_tc: Arc<BTreeSet<String>>,
    pub(super) resolved_non_tc: Arc<BTreeMap<String, String>>,
}

#[cfg(test)]
pub(super) fn closure_entry_stats_valid(
    entry: &OleanImportClosureEntry,
    window: u64,
    stat_memo: &mut HashMap<PathBuf, FileStatFingerprint>,
) -> bool {
    if entry.window != window {
        return false;
    }
    entry.tracked_stats.iter().all(|(p, expected_st)| {
        let cur = *stat_memo
            .entry(p.clone())
            .or_insert_with(|| path_stat_fingerprint(p));
        cur == *expected_st
    })
}

#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(super) static OLEAN_IMPORT_CLOSURE_MEMO: OnceLock<
    Mutex<HashMap<(String, String, PathBuf), OleanImportClosureEntry>>,
> = OnceLock::new();

#[allow(clippy::type_complexity)]
pub(super) static ARTIFACT_LAKE_HASH_MEMO: OnceLock<
    Mutex<
        HashMap<
            PathBuf,
            (
                u64,
                crate::zygote::OleanFileStatSig,
                Option<crate::zygote::OleanFileStatSig>,
                u64,
            ),
        >,
    >,
> = OnceLock::new();

#[allow(clippy::type_complexity)]
pub(super) static OLEAN_ARTIFACT_SET_MEMO: OnceLock<
    Mutex<HashMap<PathBuf, (u64, [Option<crate::zygote::OleanFileStatSig>; 6], String)>>,
> = OnceLock::new();

#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(super) static OLEAN_TRANSITIVE_ENV_MEMO: OnceLock<
    Mutex<
        HashMap<(String, String, PathBuf), (u64, Arc<Vec<(PathBuf, FileStatFingerprint)>>, String)>,
    >,
> = OnceLock::new();

/// End the memo window above and open the next one. Called once per CLI command and once per
/// `serve` / MCP request, so a process that outlives a single command never answers from a previous
/// request's input bytes.
pub fn reset_lake_inputs_tag_memo() {
    // Bump first: a concurrent `publish_lake_inputs_tag` either already holds the lock (and this
    // clear removes its entry) or takes it after this store and sees its own window superseded.
    LAKE_INPUTS_TAG_MEMO_WINDOW.fetch_add(1, Ordering::SeqCst);
    if let Some(m) = LAKE_INPUTS_TAG_MEMO.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
    if let Some(m) = REPLAYED_OLEAN_DIGEST_MEMO.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
    if let Some(m) = OLEAN_BINARY_IMPORTS_MEMO.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
    #[cfg(test)]
    if let Some(m) = OLEAN_IMPORT_CLOSURE_MEMO.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
    if let Some(m) = OLEAN_ARTIFACT_SET_MEMO.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
    if let Some(m) = ARTIFACT_LAKE_HASH_MEMO.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
    if let Some(m) = CLEAN_GIT_PIN_MEMO.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
    if let Some(m) = super::host_effects::TRACKED_INCLUDE_MEMO.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
    if let Some(m) = super::host_effects::SPREAD_TRANSITIVE_VERDICTS.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
    #[cfg(test)]
    if let Some(m) = OLEAN_TRANSITIVE_ENV_MEMO.get() {
        if let Ok(mut g) = m.lock() {
            g.clear();
        }
    }
    crate::lake_build::clear_worktree_auto_link_memo();
    crate::lake_build::clear_olean_interface_memo();
}

/// Store positive `tag` for `project_dir` as a caller that entered in `window` computed it.
/// Errors are never memoized (positive-only memoization). Returns `false` when the window has been
/// superseded, i.e. another command or request reset the memo while this caller was reading input bytes.
pub(super) fn publish_lake_inputs_tag(project_dir: &Path, window: u64, tag: &Option<String>) -> bool {
    let memo = LAKE_INPUTS_TAG_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
    let Ok(mut g) = memo.lock() else {
        return false;
    };
    if LAKE_INPUTS_TAG_MEMO_WINDOW.load(Ordering::SeqCst) != window {
        return false;
    }
    // Bounded: one entry per project directory seen, cleared at every window boundary.
    if g.len() >= 256 {
        g.clear();
    }
    g.insert(project_dir.to_path_buf(), (window, tag.clone()));
    true
}

/// Fallible version of [`project_lake_inputs_tag`]: returns `Err` when the workspace may declare
/// Lake file inputs (`input_dir` / `input_file`) or has an unparseable manifest/config, and either
/// [`resolve_project_config`] or [`workspace_lake_inputs_digest`] fails (for instance on an
/// unreadable input path, escaping symlink, non-regular file, or unsupported `filter` / field in a
/// root or dependency package). Top-level commands call this to fail closed before consulting any
/// content-addressed or `/dev/shm` cache.
pub(crate) fn try_project_lake_inputs_tag(project_dir: &Path) -> Result<Option<String>> {
    if project_dir.as_os_str().is_empty() {
        return Ok(None);
    }
    let memo = LAKE_INPUTS_TAG_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
    // Read *before* any input byte is, and re-checked by `publish_lake_inputs_tag` afterwards.
    let window = LAKE_INPUTS_TAG_MEMO_WINDOW.load(Ordering::SeqCst);
    if let Ok(g) = memo.lock() {
        if let Some((w, hit)) = g.get(project_dir) {
            if *w == window {
                return Ok(hit.clone());
            }
        }
    }
    let tag = if workspace_may_declare_lake_inputs(project_dir) {
        let cfg = resolve_project_config(project_dir)?;
        let digest = workspace_lake_inputs_digest(&cfg)?;
        lake_inputs_tag_from_digest(&digest)
    } else {
        None
    };
    let _ = publish_lake_inputs_tag(project_dir, window, &tag);
    Ok(tag)
}

pub(crate) fn project_lake_inputs_tag(project_dir: &Path) -> Option<String> {
    match try_project_lake_inputs_tag(project_dir) {
        Ok(tag) => tag,
        // Never emit a deterministic tag for an unresolvable or unsupported workspace: two runs
        // with different underlying input bytes would produce the same error string and collide on
        // every shard, split, and zygote cache key. Each call gets a fresh unrepeatable nonce.
        Err(e) => Some(fresh_unresolved_lake_inputs_tag(&e.to_string())),
    }
}

/// Lake's `LeanLib.recBuildExtraDepTargets` mixes one trace entry per `needs` target into the
/// library's `extraDep` job, in declaration order, captioned with the input's resolved path.
/// Unlike the cache key above this follows a single attribution (`node.target_name`), because the
/// `.trace` file has to reproduce one specific Lake computation bit-for-bit.
///
/// That attribution is `build_module_dag`'s -- the **first** library whose globs select the module,
/// because it expands them in declaration order -- while `lake build <Mod>` would use Lake's
/// `findModule?`, the **last** one. Deliberately left divergent, because for a module two libraries
/// select, both choices are sound and neither is "right":
///
/// - Lake has no single answer to reproduce. `lake build <Mod>` uses the last library, `lake build
///   <Lib>` uses `<Lib>`, and a bare `lake build` walks each default target separately -- so the
///   same module legitimately has different `extraDep` traces depending on what was asked for.
/// - Every mismatch fails safe. Writing *fewer* input entries than Lake expects, or *more*, both
///   make Lake's recomputed trace differ from the file and rebuild the module. The only way to get
///   a "nothing to do" out of Lake is to match exactly, which is correct at the moment this is
///   written: the module was just elaborated natively against the bytes being recorded.
/// - What is *not* safe is a later input edit that Lake's own attribution cannot see, and that is
///   not a trace-writing problem. `lake_build::lake_refresh_targets` handles it by asking Lake for
///   the input-bearing library instead of the module.
///
/// Changing it would also risk the `lake build --no-build` parity this was verified against, for no
/// soundness gain. `test_lake_input_dir_needs_trace_differential_against_lake` pins the bytes, and
/// `test_lake_input_digest_reaches_module_and_project_keys` pins both attributions explicitly.
pub(super) fn lake_needs_trace_entries(cfg: &ProjectConfig, node: &ModuleNode) -> Vec<serde_json::Value> {
    let Some(pkg) = package_by_root(cfg, &node.pkg_root) else {
        return Vec::new();
    };
    let needs: &[String] = if node.is_exe_target {
        let Some(exe) = pkg
            .exes
            .iter()
            .find(|e| e.name == node.target_name && e.root == node.module_name)
        else {
            return Vec::new();
        };
        &exe.needs
    } else {
        let Some(lib) = pkg
            .libs
            .iter()
            .find(|l| l.name == node.target_name && lib_can_build_module(l, &node.module_name))
        else {
            return Vec::new();
        };
        &lib.needs
    };
    needs
        .iter()
        .filter_map(|n| pkg.inputs.iter().find(|i| &i.name == n))
        .map(|i| serde_json::json!([pkg.pkg_root.join(&i.path).to_string_lossy(), i.lake_hash]))
        .collect()
}

#[allow(clippy::type_complexity)]
#[derive(serde::Serialize, serde::Deserialize)]
pub(super) struct ShmReplayedOleanDigestEntry {
    pub(super) stats: [Option<crate::zygote::OleanFileStatSig>; 4],
    pub(super) digest: String,
    #[serde(default)]
    pub(super) imports: Option<(Vec<ParsedImport>, bool)>,
    #[serde(default)]
    pub(super) epoch: String,
}

pub(super) fn shm_replayed_olean_cache_file_name(olean_path: &Path) -> String {
    let key = blake3::hash(olean_path.to_string_lossy().as_bytes())
        .to_hex()
        .to_string();
    format!("om_{}.json", &key[..28])
}

#[derive(serde::Serialize, serde::Deserialize)]
pub(super) struct ShmSourceHygieneEntry {
    pub(super) stat: crate::zygote::OleanFileStatSig,
    pub(super) hygiene: splitter::HygieneReport,
    #[serde(default)]
    pub(super) epoch: String,
}

pub(crate) fn load_source_hygiene_cached(src_path: &Path) -> Result<splitter::HygieneReport> {
    let cur_stat = path_olean_stat_sig(src_path);
    let cache_file_name = if let Some(st) = cur_stat {
        let key = blake3::hash(src_path.to_string_lossy().as_bytes())
            .to_hex()
            .to_string();
        let file_name = format!("sh_{}.json", &key[..28]);
        if crate::zygote::dev_records_subsecond_timestamps(&st) {
            if let Some(bytes) =
                crate::shm_cache::read_verified_private_shm_file("src_hygiene_v2", &file_name)
            {
                if let Ok(entry) = serde_json::from_slice::<ShmSourceHygieneEntry>(&bytes) {
                    if entry.epoch == crate::TURBO_LEAN_BUILD_EPOCH && entry.stat == st {
                        return Ok(entry.hygiene);
                    }
                }
            }
        }
        Some(file_name)
    } else {
        None
    };
    let read_started_ns = crate::zygote::wall_clock_ns();
    let (fd_pre, raw_bytes, fd_post) = read_regular_file_bound_stat(src_path)?;
    let src = String::from_utf8(raw_bytes)
        .map_err(|e| anyhow::anyhow!("Invalid UTF-8 in `{}`: {e}", src_path.display()))?;
    let hygiene = splitter::audit_hygiene(&splitter::strip_lean_comments(&src));
    if let (Some(file_name), Some(post_st)) = (cache_file_name, path_olean_stat_sig(src_path)) {
        if fd_pre == fd_post
            && Some(fd_pre) == cur_stat
            && post_st == fd_post
            && olean_stat_sig_trusted_at(&post_st, read_started_ns)
        {
            let entry = ShmSourceHygieneEntry {
                stat: post_st,
                hygiene: hygiene.clone(),
                epoch: crate::TURBO_LEAN_BUILD_EPOCH.to_string(),
            };
            if let Ok(bytes) = serde_json::to_vec(&entry) {
                let _ = crate::shm_cache::write_verified_private_shm_file(
                    "src_hygiene_v2",
                    &file_name,
                    &bytes,
                );
            }
        }
    }
    Ok(hygiene)
}

/// Compute BLAKE3 digest of on-disk `.olean` + `.ilean` bytes (plus `module` companion `.olean.server`
/// / `.olean.private` when present) under a read-only shared package publication flock (never creating
/// `.lake/build/.turbo_publish.lock` inside external/opted-out worktrees), failing closed if
/// `.olean` is missing, unreadable, or non-regular, and binding `.ilean` presence + bytes (`1` + hash
/// when present, `0` when absent).
#[allow(clippy::type_complexity)]
pub(crate) fn compute_replayed_olean_ilean_digest(olean_path: &Path) -> Result<String> {
    let window = current_memo_window();
    let ilean_path = olean_path.with_extension("ilean");
    let srv_path = olean_path.with_extension("olean.server");
    let priv_path = olean_path.with_extension("olean.private");
    let cur_stats = [
        path_olean_stat_sig(olean_path),
        path_olean_stat_sig(&ilean_path),
        path_olean_stat_sig(&srv_path),
        path_olean_stat_sig(&priv_path),
    ];
    let memo = REPLAYED_OLEAN_DIGEST_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
    if olean_stat_bundle_trusted_for_reuse(&cur_stats) {
        if let Ok(g) = memo.lock() {
            if let Some((w, cached_stats, hit)) = g.get(olean_path) {
                if *w == window && *cached_stats == cur_stats {
                    return Ok(hit.clone());
                }
            }
        }
        let shm_file_name = shm_replayed_olean_cache_file_name(olean_path);
        if let Some(bytes) =
            crate::shm_cache::read_verified_private_shm_file("olean_meta_v2", &shm_file_name)
        {
            if let Ok(entry) = serde_json::from_slice::<ShmReplayedOleanDigestEntry>(&bytes) {
                if entry.epoch == crate::TURBO_LEAN_BUILD_EPOCH
                    && entry.stats == cur_stats
                    && !entry.digest.is_empty()
                {
                    if let Ok(mut g) = memo.lock() {
                        if current_memo_window() == window {
                            if g.len() >= 65536 {
                                g.clear();
                            }
                            g.insert(
                                olean_path.to_path_buf(),
                                (window, cur_stats, entry.digest.clone()),
                            );
                        }
                    }
                    if let (Some(st0), Some((imps, is_mod))) = (cur_stats[0], entry.imports) {
                        let imemo =
                            OLEAN_BINARY_IMPORTS_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
                        if let Ok(mut ig) = imemo.lock() {
                            if current_memo_window() == window && ig.len() < 65536 {
                                ig.insert(olean_path.to_path_buf(), (window, st0, imps, is_mod));
                            }
                        }
                    }
                    return Ok(entry.digest);
                }
            }
        }
    }
    let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
    let _guard = lock
        .lock()
        .map_err(|_| anyhow::anyhow!("Module artifact publication mutex poisoned"))?;
    let _flock_guard = if let Some(pkg_root) = infer_pkg_root_from_artifact_path(olean_path) {
        Some(acquire_publish_flock_mode(&pkg_root, false, true)?)
    } else {
        None
    };
    let pre_stats = [
        path_olean_stat_sig(olean_path),
        path_olean_stat_sig(&ilean_path),
        path_olean_stat_sig(&srv_path),
        path_olean_stat_sig(&priv_path),
    ];
    let read_started_ns = crate::zygote::wall_clock_ns();
    let paths = vec![
        olean_path.to_path_buf(),
        ilean_path.clone(),
        srv_path.clone(),
        priv_path.clone(),
    ];
    let digest = || -> Result<(
        String,
        Option<(Vec<ParsedImport>, bool)>,
        [Option<crate::zygote::OleanFileStatSig>; 4],
        bool,
    )> {
        let mut h = blake3::Hasher::new();
        h.update(b"turbo-lean-replayed-olean-ilean-v1\n");
        let mut parsed_imps = None;
        let mut fd_stats = [None; 4];
        let mut fd_stable = true;
        for (idx, (tag, p, required)) in [
            ("olean", olean_path, true),
            ("ilean", ilean_path.as_path(), false),
            ("srv", srv_path.as_path(), false),
            ("priv", priv_path.as_path(), false),
        ]
        .into_iter()
        .enumerate()
        {
            match read_regular_file_bound_stat(p) {
                Ok((fpre, bytes, fpost)) => {
                    anyhow::ensure!(
                        !required || !bytes.is_empty(),
                        "Replay-verified artifact `{}` is not a non-empty regular file",
                        p.display()
                    );
                    if fpre != fpost {
                        fd_stable = false;
                    }
                    fd_stats[idx] = Some(fpost);
                    h.update(&[1u8]);
                    if tag == "olean" {
                        parsed_imps = parse_olean_binary_imports(&bytes);
                    }
                    update_lp(&mut h, tag.as_bytes(), blake3::hash(&bytes).as_bytes());
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound && !required => {
                    h.update(&[0u8]);
                    update_lp(&mut h, tag.as_bytes(), b"");
                }
                Err(e) if e.kind() == std::io::ErrorKind::InvalidInput => {
                    anyhow::bail!(
                        "Replay-verified artifact `{}` is not a non-empty regular file",
                        p.display()
                    );
                }
                Err(e) => {
                    return Err(e).with_context(|| {
                        format!("Failed to read replay-verified artifact `{}`", p.display())
                    })
                }
            }
        }
        Ok((h.finalize().to_hex().to_string(), parsed_imps, fd_stats, fd_stable))
    };
    let (res, parsed_imps, fd_stats, fd_stable) = match _flock_guard.as_ref() {
        Some(g) => g.read_consistent(&paths, digest),
        None => digest(),
    }?;
    let post_stats = [
        path_olean_stat_sig(olean_path),
        path_olean_stat_sig(&ilean_path),
        path_olean_stat_sig(&srv_path),
        path_olean_stat_sig(&priv_path),
    ];
    if fd_stable
        && fd_stats == pre_stats
        && post_stats == pre_stats
        && olean_stat_bundle_trusted_to_store(&post_stats, read_started_ns)
    {
        if let Ok(mut g) = memo.lock() {
            if current_memo_window() == window {
                if g.len() >= 65536 {
                    g.clear();
                }
                g.insert(olean_path.to_path_buf(), (window, post_stats, res.clone()));
            }
        }
        if let (Some(st0), Some((ref imps, is_mod))) = (post_stats[0], &parsed_imps) {
            let imemo = OLEAN_BINARY_IMPORTS_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
            if let Ok(mut ig) = imemo.lock() {
                if current_memo_window() == window && ig.len() < 65536 {
                    ig.insert(
                        olean_path.to_path_buf(),
                        (window, st0, imps.clone(), *is_mod),
                    );
                }
            }
        }
        let shm_file_name = shm_replayed_olean_cache_file_name(olean_path);
        let shm_entry = ShmReplayedOleanDigestEntry {
            stats: post_stats,
            digest: res.clone(),
            imports: parsed_imps,
            epoch: crate::TURBO_LEAN_BUILD_EPOCH.to_string(),
        };
        if let Ok(bytes) = serde_json::to_vec(&shm_entry) {
            let _ = crate::shm_cache::write_verified_private_shm_file(
                "olean_meta_v2",
                &shm_file_name,
                &bytes,
            );
        }
    }
    Ok(res)
}

pub(crate) fn read_olean_binary_imports_cached(
    olean_path: &Path,
) -> Result<(Vec<ParsedImport>, bool)> {
    let window = current_memo_window();
    let cur_stat = path_olean_stat_sig(olean_path);
    let memo = OLEAN_BINARY_IMPORTS_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
    if let Some(st) = cur_stat {
        if crate::zygote::dev_records_subsecond_timestamps(&st) {
            if let Ok(g) = memo.lock() {
                if let Some((w, cached_st, imps, is_mod)) = g.get(olean_path) {
                    if *w == window && *cached_st == st {
                        return Ok((imps.clone(), *is_mod));
                    }
                }
            }
            let shm_file_name = shm_replayed_olean_cache_file_name(olean_path);
            if let Some(bytes) =
                crate::shm_cache::read_verified_private_shm_file("olean_meta_v2", &shm_file_name)
            {
                if let Ok(entry) = serde_json::from_slice::<ShmReplayedOleanDigestEntry>(&bytes) {
                    if entry.epoch == crate::TURBO_LEAN_BUILD_EPOCH && entry.stats[0] == Some(st) {
                        if let Some((imps, is_mod)) = entry.imports {
                            if let Ok(mut g) = memo.lock() {
                                if current_memo_window() == window {
                                    if g.len() >= 65536 {
                                        g.clear();
                                    }
                                    g.insert(
                                        olean_path.to_path_buf(),
                                        (window, st, imps.clone(), is_mod),
                                    );
                                }
                            }
                            return Ok((imps, is_mod));
                        }
                    }
                }
            }
        }
    }
    let read_started_ns = crate::zygote::wall_clock_ns();
    let (fd_pre, bytes, fd_post) = read_regular_file_bound_stat(olean_path).with_context(|| {
        format!(
            "Failed to read `.olean` `{}` for binary import header",
            olean_path.display()
        )
    })?;
    let (imps, is_mod) = parse_olean_binary_imports(&bytes).ok_or_else(|| {
        anyhow::anyhow!(
            "Failed to parse binary `.olean` header of `{}`: fail-closed",
            olean_path.display()
        )
    })?;
    if let Some(post_st) = path_olean_stat_sig(olean_path) {
        if fd_pre == fd_post
            && Some(fd_pre) == cur_stat
            && post_st == fd_post
            && olean_stat_sig_trusted_at(&post_st, read_started_ns)
        {
            if let Ok(mut g) = memo.lock() {
                if current_memo_window() == window {
                    if g.len() >= 65536 {
                        g.clear();
                    }
                    g.insert(
                        olean_path.to_path_buf(),
                        (window, post_st, imps.clone(), is_mod),
                    );
                }
            }
        }
    }
    Ok((imps, is_mod))
}

pub(crate) fn project_disallowed_replay_store_roots(cfg: &ProjectConfig) -> Vec<PathBuf> {
    let mut roots = Vec::with_capacity(1 + cfg.dep_pkgs.len() + cfg.manifest_packages.len());
    roots.push(cfg.root_pkg.pkg_root.clone());
    for dp in &cfg.dep_pkgs {
        roots.push(dp.pkg_root.clone());
    }
    for mp in &cfg.manifest_packages {
        roots.push(mp.dir.clone());
    }
    roots
}

/// Compute the deterministic transitive binary import environment digest for `olean_path` along
/// `lean_path_env` (plus `cfg.toolchain_lib_lean`), binding every reachable non-toolchain `.olean`
/// (with `.ilean`/companion files via `compute_replayed_olean_ilean_digest`) and marking verified
/// toolchain modules by `(module_name, cfg.lean_githash)` while failing closed (`Err`) if any
/// binary import is unresolvable or unreadable. Because every imported non-toolchain artifact's
/// full content digest is folded into `environment_digest`, modifying a child module's interface
/// immediately invalidates the parent module's replay authority even when the parent `.olean` bytes
/// were left untouched on disk.
pub(crate) fn is_root_project_olean_path(cfg: &ProjectConfig, olean_path: &Path) -> bool {
    let canon_olean = olean_path
        .canonicalize()
        .unwrap_or_else(|_| olean_path.to_path_buf());
    let canon_root_lib = cfg
        .root_pkg
        .pkg_root
        .join(&cfg.root_pkg.build_dir)
        .join(&cfg.root_pkg.lean_lib_dir)
        .canonicalize()
        .unwrap_or_else(|_| {
            cfg.root_pkg
                .pkg_root
                .join(&cfg.root_pkg.build_dir)
                .join(&cfg.root_pkg.lean_lib_dir)
        });
    let canon_root_pkg = cfg
        .root_pkg
        .pkg_root
        .canonicalize()
        .unwrap_or_else(|_| cfg.root_pkg.pkg_root.clone());
    let canon_packages = cfg
        .root_pkg
        .pkg_root
        .join(&cfg.root_pkg.packages_dir)
        .canonicalize()
        .unwrap_or_else(|_| cfg.root_pkg.pkg_root.join(&cfg.root_pkg.packages_dir));
    canon_olean.starts_with(&canon_root_lib)
        || (canon_olean.starts_with(&canon_root_pkg) && !canon_olean.starts_with(&canon_packages))
}

#[cfg(test)]
#[allow(clippy::type_complexity)]
pub(super) fn resolve_olean_import_closure_cached_with_stat_memo(
    cfg: &ProjectConfig,
    dirs: &[PathBuf],
    lean_path_env: &str,
    olean_path: &Path,
    stat_memo: &mut HashMap<PathBuf, FileStatFingerprint>,
    path_memo: &mut HashMap<String, PathBuf>,
    valid_closures: &mut HashSet<PathBuf>,
) -> Result<(
    Arc<Vec<(PathBuf, FileStatFingerprint)>>,
    Arc<BTreeSet<String>>,
    Arc<BTreeMap<String, String>>,
)> {
    let window = current_memo_window();
    let closure_memo = OLEAN_IMPORT_CLOSURE_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
    let ckey = (
        cfg.lean_githash.clone(),
        lean_path_env.to_string(),
        olean_path.to_path_buf(),
    );
    if let Ok(g) = closure_memo.lock() {
        if let Some(entry) = g.get(&ckey) {
            if entry.window == window
                && (valid_closures.contains(olean_path)
                    || closure_entry_stats_valid(entry, window, stat_memo))
            {
                valid_closures.insert(olean_path.to_path_buf());
                return Ok((
                    entry.tracked_stats.clone(),
                    entry.resolved_tc.clone(),
                    entry.resolved_non_tc.clone(),
                ));
            }
        }
    }
    enum ClosureFrame {
        Enter(PathBuf),
        Exit(PathBuf, Vec<(String, PathBuf, Option<String>)>),
    }
    let mut stack = vec![ClosureFrame::Enter(olean_path.to_path_buf())];
    let mut visiting: HashSet<PathBuf> = HashSet::new();
    while let Some(frame) = stack.pop() {
        match frame {
            ClosureFrame::Enter(cur_path) => {
                let cur_ckey = (
                    cfg.lean_githash.clone(),
                    lean_path_env.to_string(),
                    cur_path.clone(),
                );
                if let Ok(g) = closure_memo.lock() {
                    if let Some(entry) = g.get(&cur_ckey) {
                        if entry.window == window
                            && (valid_closures.contains(&cur_path)
                                || closure_entry_stats_valid(entry, window, stat_memo))
                        {
                            valid_closures.insert(cur_path);
                            continue;
                        }
                    }
                }
                if !visiting.insert(cur_path.clone()) {
                    continue;
                }
                let (imps, _) = read_olean_binary_imports_cached(&cur_path).with_context(|| {
                    format!(
                        "Failed to parse binary `.olean` header of `{}`: fail-closed",
                        cur_path.display()
                    )
                })?;
                let mut direct: Vec<(String, PathBuf, Option<String>)> =
                    Vec::with_capacity(imps.len());
                let mut children_to_visit: Vec<PathBuf> = Vec::new();
                for imp in imps {
                    let m = imp.module;
                    let path = if let Some(cached_p) = path_memo.get(&m) {
                        cached_p.clone()
                    } else {
                        let resolved = resolve_olean_along_search_dirs(dirs, &m).ok_or_else(
                            || {
                                anyhow::anyhow!(
                                    "Unresolvable binary import `{}` required by `{}` along LEAN_PATH: fail-closed",
                                    m,
                                    cur_path.display()
                                )
                            },
                        )?;
                        path_memo.insert(m.clone(), resolved.clone());
                        resolved
                    };
                    if is_verified_toolchain_olean_file(
                        &cfg.toolchain_lib_lean,
                        Some(&cfg.lean_githash),
                        &path,
                    ) {
                        direct.push((m, path, None));
                        continue;
                    }
                    let dep_dig = compute_replayed_olean_ilean_digest(&path)?;
                    children_to_visit.push(path.clone());
                    direct.push((m, path, Some(dep_dig)));
                }
                stack.push(ClosureFrame::Exit(cur_path, direct));
                for ch in children_to_visit.into_iter().rev() {
                    stack.push(ClosureFrame::Enter(ch));
                }
            }
            ClosureFrame::Exit(cur_path, direct) => {
                visiting.remove(&cur_path);
                let mut stats_map: BTreeMap<PathBuf, FileStatFingerprint> = BTreeMap::new();
                let cur_st = *stat_memo
                    .entry(cur_path.clone())
                    .or_insert_with(|| path_stat_fingerprint(&cur_path));
                stats_map.insert(cur_path.clone(), cur_st);
                let mut tc_set: BTreeSet<String> = BTreeSet::new();
                let mut non_tc_map: BTreeMap<String, String> = BTreeMap::new();
                for (m, path, dep_dig_opt) in direct {
                    match dep_dig_opt {
                        None => {
                            tc_set.insert(m);
                        }
                        Some(dep_dig) => {
                            for comp in [
                                path.clone(),
                                path.with_extension("ilean"),
                                path.with_extension("olean.server"),
                                path.with_extension("olean.private"),
                            ] {
                                let st = *stat_memo
                                    .entry(comp.clone())
                                    .or_insert_with(|| path_stat_fingerprint(&comp));
                                stats_map.insert(comp, st);
                            }
                            non_tc_map.insert(m, dep_dig);
                            let ch_ckey =
                                (cfg.lean_githash.clone(), lean_path_env.to_string(), path);
                            if let Ok(g) = closure_memo.lock() {
                                if let Some(ch_entry) = g.get(&ch_ckey) {
                                    if ch_entry.window == window {
                                        for (p, st) in ch_entry.tracked_stats.iter() {
                                            stats_map.entry(p.clone()).or_insert(*st);
                                        }
                                        for tm in ch_entry.resolved_tc.iter() {
                                            tc_set.insert(tm.clone());
                                        }
                                        for (dm, dd) in ch_entry.resolved_non_tc.iter() {
                                            non_tc_map
                                                .entry(dm.clone())
                                                .or_insert_with(|| dd.clone());
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                let tracked_vec: Vec<(PathBuf, FileStatFingerprint)> =
                    stats_map.into_iter().collect();
                let entry = OleanImportClosureEntry {
                    window,
                    tracked_stats: Arc::new(tracked_vec),
                    resolved_tc: Arc::new(tc_set),
                    resolved_non_tc: Arc::new(non_tc_map),
                };
                if let Ok(mut g) = closure_memo.lock() {
                    if current_memo_window() == window {
                        if g.len() >= 16384 {
                            g.clear();
                            valid_closures.clear();
                        }
                        let cur_ckey = (
                            cfg.lean_githash.clone(),
                            lean_path_env.to_string(),
                            cur_path.clone(),
                        );
                        g.insert(cur_ckey, entry);
                        valid_closures.insert(cur_path);
                    }
                }
            }
        }
    }
    if let Ok(g) = closure_memo.lock() {
        if let Some(entry) = g.get(&ckey) {
            if entry.window == window {
                return Ok((
                    entry.tracked_stats.clone(),
                    entry.resolved_tc.clone(),
                    entry.resolved_non_tc.clone(),
                ));
            }
        }
    }
    anyhow::bail!(
        "Failed to memoize binary import closure for `{}`: fail-closed",
        olean_path.display()
    )
}

#[allow(clippy::type_complexity)]
#[derive(Clone)]
pub(super) struct ReplayClosureMemoEntry {
    pub(super) generation: u64,
    pub(super) reach: Vec<usize>,
    pub(super) resolved_mods: Vec<(String, PathBuf)>,
    pub(super) tc_mods: Vec<String>,
    pub(super) non_tc_mods: Vec<(String, PathBuf, String)>,
}

#[derive(Clone)]
pub(crate) struct VerifiedFastStoreAuthority {
    pub(crate) artifact_digest: String,
    pub(super) reach_sigs: Vec<(PathBuf, crate::zygote::OleanFileStatSig)>,
    pub(super) resolved_mods: Vec<(String, PathBuf)>,
    pub(super) non_tc_mods: Vec<(PathBuf, String)>,
}

#[allow(clippy::type_complexity)]
pub(crate) struct ReplayLookupBatchCache {
    pub(super) path_memo: HashMap<String, PathBuf>,
    pub(super) env_memo: HashMap<(bool, PathBuf), (u64, String)>,
    pub(super) next_closure_gen: u64,
    pub(super) node_pool: Vec<PathBuf>,
    pub(super) node_ids: HashMap<PathBuf, usize>,
    pub(super) node_closures: Vec<Option<ReplayClosureMemoEntry>>,
    pub(super) node_header_sigs: Vec<Option<crate::zygote::OleanFileStatSig>>,
    pub(super) dirs: Vec<PathBuf>,
    pub(super) disallowed_roots: Vec<PathBuf>,
    pub(super) store_outside_disallowed: bool,
    pub(super) replay_hmac_key: Option<[u8; 32]>,
    pub(super) policy_dig: String,
    pub(super) canon_root_lib: PathBuf,
    pub(super) canon_extra_root_lib: Option<PathBuf>,
    pub(super) canon_root_pkg: PathBuf,
    pub(super) canon_packages: PathBuf,
}

impl ReplayLookupBatchCache {
    pub(crate) fn new(store: &TurboStore, cfg: &ProjectConfig, lean_path_env: &str) -> Self {
        Self::new_with_extra_root_lib(store, cfg, lean_path_env, None)
    }

    pub(crate) fn new_with_extra_root_lib(
        store: &TurboStore,
        cfg: &ProjectConfig,
        lean_path_env: &str,
        extra_root_lib: Option<&Path>,
    ) -> Self {
        let mut dirs: Vec<PathBuf> = std::env::split_paths(lean_path_env).collect();
        if !cfg.toolchain_lib_lean.as_os_str().is_empty() && !dirs.contains(&cfg.toolchain_lib_lean)
        {
            dirs.push(cfg.toolchain_lib_lean.clone());
        }
        let disallowed_roots = project_disallowed_replay_store_roots(cfg);
        let store_outside_disallowed = store.is_store_outside_disallowed_roots(&disallowed_roots);
        let replay_hmac_key = if store_outside_disallowed {
            store.load_verified_replay_hmac_key(&disallowed_roots)
        } else {
            None
        };
        let policy_dig = crate::splitter::current_kernel_policy_digest();
        let canon_root_lib = cfg
            .root_pkg
            .pkg_root
            .join(&cfg.root_pkg.build_dir)
            .join(&cfg.root_pkg.lean_lib_dir)
            .canonicalize()
            .unwrap_or_else(|_| {
                cfg.root_pkg
                    .pkg_root
                    .join(&cfg.root_pkg.build_dir)
                    .join(&cfg.root_pkg.lean_lib_dir)
            });
        let canon_root_pkg = cfg
            .root_pkg
            .pkg_root
            .canonicalize()
            .unwrap_or_else(|_| cfg.root_pkg.pkg_root.clone());
        let canon_packages = cfg
            .root_pkg
            .pkg_root
            .join(&cfg.root_pkg.packages_dir)
            .canonicalize()
            .unwrap_or_else(|_| cfg.root_pkg.pkg_root.join(&cfg.root_pkg.packages_dir));
        let canon_extra_root_lib =
            extra_root_lib.map(|p| p.canonicalize().unwrap_or_else(|_| p.to_path_buf()));
        Self {
            path_memo: HashMap::new(),
            env_memo: HashMap::new(),
            next_closure_gen: 1,
            node_pool: Vec::new(),
            node_ids: HashMap::new(),
            node_closures: Vec::new(),
            node_header_sigs: Vec::new(),
            dirs,
            disallowed_roots,
            store_outside_disallowed,
            replay_hmac_key,
            policy_dig,
            canon_root_lib,
            canon_extra_root_lib,
            canon_root_pkg,
            canon_packages,
        }
    }

    pub(super) fn resolve_module_along_dirs(&self, m: &str) -> Option<PathBuf> {
        resolve_olean_along_search_dirs(&self.dirs, m)
    }

    pub(super) fn intern_node(&mut self, path: &Path) -> usize {
        if let Some(&id) = self.node_ids.get(path) {
            return id;
        }
        let id = self.node_pool.len();
        let owned = path.to_path_buf();
        self.node_pool.push(owned.clone());
        self.node_ids.insert(owned, id);
        self.node_closures.push(None);
        self.node_header_sigs.push(None);
        id
    }

    pub(super) fn closure_memo_is_fresh(&self, entry: &ReplayClosureMemoEntry) -> bool {
        for &nid in &entry.reach {
            let Some(expected_sig) = self.node_header_sigs[nid] else {
                return false;
            };
            if !crate::zygote::dev_records_subsecond_timestamps(&expected_sig)
                || path_olean_stat_sig(&self.node_pool[nid]) != Some(expected_sig)
            {
                return false;
            }
        }
        for (m, cached_p) in &entry.resolved_mods {
            if self.resolve_module_along_dirs(m).as_ref() != Some(cached_p) {
                return false;
            }
        }
        for (_, dep_p, expected_dig) in &entry.non_tc_mods {
            let Ok(cur_dig) = compute_replayed_olean_ilean_digest(dep_p) else {
                return false;
            };
            if &cur_dig != expected_dig {
                return false;
            }
        }
        true
    }

    pub(super) fn ensure_node_closure(&mut self, cfg: &ProjectConfig, olean_path: &Path) -> Result<usize> {
        let mut root_id = self.intern_node(olean_path);
        if let Some(ref entry) = self.node_closures[root_id] {
            if self.closure_memo_is_fresh(entry) {
                return Ok(root_id);
            }
            self.invalidate_memo();
            root_id = self.intern_node(olean_path);
        }
        enum Frame {
            Enter(usize),
            Exit(
                usize,
                Vec<usize>,
                Vec<(String, PathBuf)>,
                Vec<String>,
                Vec<(String, PathBuf, String)>,
            ),
        }
        let mut stack = vec![Frame::Enter(root_id)];
        let mut visiting: HashSet<usize> = HashSet::new();
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Enter(uid) => {
                    if let Some(ref existing) = self.node_closures[uid] {
                        if self.closure_memo_is_fresh(existing) {
                            continue;
                        }
                        self.node_closures[uid] = None;
                        self.node_header_sigs[uid] = None;
                    }
                    if !visiting.insert(uid) {
                        continue;
                    }
                    let cur_path = self.node_pool[uid].clone();
                    let pre_sig = path_olean_stat_sig(&cur_path);
                    let (imps, _) =
                        read_olean_binary_imports_cached(&cur_path).with_context(|| {
                            format!(
                                "Failed to parse binary `.olean` header of `{}`: fail-closed",
                                cur_path.display()
                            )
                        })?;
                    let post_sig = path_olean_stat_sig(&cur_path);
                    self.node_header_sigs[uid] = if pre_sig.is_some() && pre_sig == post_sig {
                        post_sig
                    } else {
                        None
                    };
                    let mut direct_resolved = Vec::with_capacity(imps.len());
                    let mut direct_tc = Vec::new();
                    let mut direct_non_tc = Vec::new();
                    let mut child_ids = Vec::new();
                    for imp in imps {
                        let m = imp.module;
                        let path = self.resolve_module_along_dirs(&m).ok_or_else(|| {
                            anyhow::anyhow!(
                                "Unresolvable binary import `{}` required by `{}` along LEAN_PATH: fail-closed",
                                m,
                                cur_path.display()
                            )
                        })?;
                        self.path_memo.insert(m.clone(), path.clone());
                        direct_resolved.push((m.clone(), path.clone()));
                        if is_verified_toolchain_olean_file(
                            &cfg.toolchain_lib_lean,
                            Some(&cfg.lean_githash),
                            &path,
                        ) {
                            direct_tc.push(m);
                            continue;
                        }
                        let dep_dig = compute_replayed_olean_ilean_digest(&path)?;
                        let cid = self.intern_node(&path);
                        child_ids.push(cid);
                        direct_non_tc.push((m, path, dep_dig));
                    }
                    let to_visit: Vec<usize> = child_ids
                        .iter()
                        .copied()
                        .filter(|&cid| {
                            self.node_closures[cid]
                                .as_ref()
                                .is_none_or(|e| !self.closure_memo_is_fresh(e))
                        })
                        .collect();
                    stack.push(Frame::Exit(
                        uid,
                        child_ids,
                        direct_resolved,
                        direct_tc,
                        direct_non_tc,
                    ));
                    for cid in to_visit.into_iter().rev() {
                        stack.push(Frame::Enter(cid));
                    }
                }
                Frame::Exit(uid, child_ids, mut resolved_vec, mut tc_vec, mut non_tc_vec) => {
                    visiting.remove(&uid);
                    let mut reach: Vec<usize> = Vec::with_capacity(1 + child_ids.len() * 8);
                    reach.push(uid);
                    for cid in child_ids {
                        if let Some(ch_entry) = &self.node_closures[cid] {
                            reach.extend_from_slice(&ch_entry.reach);
                            resolved_vec.extend(ch_entry.resolved_mods.iter().cloned());
                            tc_vec.extend(ch_entry.tc_mods.iter().cloned());
                            non_tc_vec.extend(ch_entry.non_tc_mods.iter().cloned());
                        }
                    }
                    reach.sort_unstable();
                    reach.dedup();
                    resolved_vec.sort_unstable_by(|a, b| a.0.cmp(&b.0));
                    resolved_vec.dedup_by(|a, b| a.0 == b.0);
                    tc_vec.sort_unstable();
                    tc_vec.dedup();
                    non_tc_vec.sort_unstable_by(|a, b| a.0.cmp(&b.0));
                    non_tc_vec.dedup_by(|a, b| a.0 == b.0);
                    let generation = self.next_closure_gen;
                    self.next_closure_gen += 1;
                    self.node_closures[uid] = Some(ReplayClosureMemoEntry {
                        generation,
                        reach,
                        resolved_mods: resolved_vec,
                        tc_mods: tc_vec,
                        non_tc_mods: non_tc_vec,
                    });
                }
            }
        }
        Ok(root_id)
    }

    pub(super) fn is_root_olean(&self, olean_path: &Path) -> bool {
        if olean_path.starts_with(&self.canon_packages) {
            return false;
        }
        if olean_path.starts_with(&self.canon_root_lib) {
            return true;
        }
        if let Some(ref extra) = self.canon_extra_root_lib {
            if olean_path.starts_with(extra) {
                return true;
            }
        }
        let canon_olean = olean_path
            .canonicalize()
            .unwrap_or_else(|_| olean_path.to_path_buf());
        canon_olean.starts_with(&self.canon_root_lib)
            || self
                .canon_extra_root_lib
                .as_ref()
                .is_some_and(|extra| canon_olean.starts_with(extra))
            || (canon_olean.starts_with(&self.canon_root_pkg)
                && !canon_olean.starts_with(&self.canon_packages))
    }

    pub(crate) fn compute_env_digest_with_binds_policy(
        &mut self,
        cfg: &ProjectConfig,
        olean_path: &Path,
        binds_policy: bool,
    ) -> Result<String> {
        let (_, res) = self.compute_env_digest_and_root(cfg, olean_path, binds_policy)?;
        Ok(res)
    }

    pub(super) fn compute_env_digest_and_root(
        &mut self,
        cfg: &ProjectConfig,
        olean_path: &Path,
        binds_policy: bool,
    ) -> Result<(usize, String)> {
        let root_id = self.ensure_node_closure(cfg, olean_path)?;
        let Some(entry) = &self.node_closures[root_id] else {
            anyhow::bail!(
                "Failed to memoize binary import closure for `{}`: fail-closed",
                olean_path.display()
            );
        };
        let cur_gen = entry.generation;
        if let Some((hit_gen, hit)) = self.env_memo.get(&(binds_policy, olean_path.to_path_buf())) {
            if *hit_gen == cur_gen {
                return Ok((root_id, hit.clone()));
            }
        }
        let policy_dig_ref = if binds_policy {
            self.policy_dig.as_str()
        } else {
            ""
        };
        let mut h = blake3::Hasher::new();
        h.update(b"turbo-lean-olean-transitive-env-v1\n");
        update_lp(&mut h, b"githash", cfg.lean_githash.as_bytes());
        if binds_policy && !policy_dig_ref.is_empty() {
            update_lp(&mut h, b"kernel_policy", policy_dig_ref.as_bytes());
        }
        h.update(&(entry.tc_mods.len() as u64).to_le_bytes());
        for tc_m in entry.tc_mods.iter() {
            update_lp(&mut h, b"tc", tc_m.as_bytes());
        }
        h.update(&(entry.non_tc_mods.len() as u64).to_le_bytes());
        for (dep_m, _, dep_dig) in entry.non_tc_mods.iter() {
            update_lp(&mut h, b"dep_mod", dep_m.as_bytes());
            update_lp(&mut h, b"dep_dig", dep_dig.as_bytes());
        }
        let res = h.finalize().to_hex().to_string();
        self.env_memo.insert(
            (binds_policy, olean_path.to_path_buf()),
            (cur_gen, res.clone()),
        );
        Ok((root_id, res))
    }

    pub(super) fn capture_verified_closure_authority(
        &self,
        root_id: usize,
        artifact_digest: String,
    ) -> Option<VerifiedFastStoreAuthority> {
        let entry = self.node_closures.get(root_id)?.as_ref()?;
        if !self.closure_memo_is_fresh(entry) {
            return None;
        }
        let mut reach_sigs = Vec::with_capacity(entry.reach.len());
        for &nid in &entry.reach {
            let sig = self.node_header_sigs.get(nid).copied().flatten()?;
            reach_sigs.push((self.node_pool.get(nid)?.clone(), sig));
        }
        Some(VerifiedFastStoreAuthority {
            artifact_digest,
            reach_sigs,
            resolved_mods: entry.resolved_mods.clone(),
            non_tc_mods: entry
                .non_tc_mods
                .iter()
                .map(|(_, p, d)| (p.clone(), d.clone()))
                .collect(),
        })
    }

    pub(crate) fn verify_fast_store_authority(&self, auth: &VerifiedFastStoreAuthority) -> bool {
        for (p, expected_sig) in &auth.reach_sigs {
            if !crate::zygote::dev_records_subsecond_timestamps(expected_sig)
                || path_olean_stat_sig(p).as_ref() != Some(expected_sig)
            {
                return false;
            }
        }
        for (m, expected_p) in &auth.resolved_mods {
            if self.resolve_module_along_dirs(m).as_ref() != Some(expected_p) {
                return false;
            }
        }
        for (dep_p, expected_dig) in &auth.non_tc_mods {
            let Ok(cur_dig) = compute_replayed_olean_ilean_digest(dep_p) else {
                return false;
            };
            if &cur_dig != expected_dig {
                return false;
            }
        }
        true
    }

    pub(crate) fn is_root_module_olean(&self, olean_path: &Path) -> bool {
        self.is_root_olean(olean_path)
    }

    pub(crate) fn refresh_replay_hmac_key(&mut self, store: &TurboStore) {
        if self.replay_hmac_key.is_none() && self.store_outside_disallowed {
            self.replay_hmac_key = store.load_verified_replay_hmac_key(&self.disallowed_roots);
        }
    }

    pub(crate) fn invalidate_memo(&mut self) {
        self.path_memo.clear();
        self.env_memo.clear();
        self.node_pool.clear();
        self.node_ids.clear();
        self.node_closures.clear();
        self.node_header_sigs.clear();
    }

    pub(crate) fn is_replayed_in_store_with_binds_policy(
        &mut self,
        store: &TurboStore,
        cfg: &ProjectConfig,
        olean_path: &Path,
        binds_policy: bool,
    ) -> bool {
        self.verify_replayed_in_store_authority(store, cfg, olean_path, binds_policy, String::new())
            .is_some()
    }

    pub(crate) fn verify_replayed_in_store_authority(
        &mut self,
        store: &TurboStore,
        cfg: &ProjectConfig,
        olean_path: &Path,
        binds_policy: bool,
        artifact_digest: String,
    ) -> Option<VerifiedFastStoreAuthority> {
        if cfg.lean_githash.is_empty() || !self.store_outside_disallowed {
            return None;
        }
        self.refresh_replay_hmac_key(store);
        let key = self.replay_hmac_key?;
        let dig = compute_replayed_olean_ilean_digest(olean_path).ok()?;
        let (root_id, env_dig) = self
            .compute_env_digest_and_root(cfg, olean_path, binds_policy)
            .ok()?;
        if !store.has_kernel_replayed_olean_with_key(
            &key,
            &dig,
            &env_dig,
            crate::zygote::ZYGOTE_REPLAY_VERSION,
            &cfg.lean_githash,
        ) {
            return None;
        }
        if compute_replayed_olean_ilean_digest(olean_path)
            .ok()
            .as_deref()
            != Some(dig.as_str())
        {
            return None;
        }
        self.capture_verified_closure_authority(root_id, artifact_digest)
    }

    pub(crate) fn is_replayed_in_store(
        &mut self,
        store: &TurboStore,
        cfg: &ProjectConfig,
        lean_path_env: &str,
        olean_path: &Path,
    ) -> bool {
        let _ = lean_path_env;
        let binds_policy = self.is_root_olean(olean_path);
        self.is_replayed_in_store_with_binds_policy(store, cfg, olean_path, binds_policy)
    }

    pub(crate) fn is_audited_in_store_with_binds_policy(
        &mut self,
        store: &TurboStore,
        cfg: &ProjectConfig,
        mod_name: &str,
        olean_path: &Path,
        binds_policy: bool,
    ) -> bool {
        self.verify_audited_in_store_authority(
            store,
            cfg,
            mod_name,
            olean_path,
            binds_policy,
            String::new(),
        )
        .is_some()
    }

    pub(crate) fn verify_audited_in_store_authority(
        &mut self,
        store: &TurboStore,
        cfg: &ProjectConfig,
        mod_name: &str,
        olean_path: &Path,
        binds_policy: bool,
        artifact_digest: String,
    ) -> Option<VerifiedFastStoreAuthority> {
        if cfg.lean_githash.is_empty() || !self.store_outside_disallowed {
            return None;
        }
        self.refresh_replay_hmac_key(store);
        let key = self.replay_hmac_key?;
        let dig = compute_replayed_olean_ilean_digest(olean_path).ok()?;
        let (root_id, env_dig) = self
            .compute_env_digest_and_root(cfg, olean_path, binds_policy)
            .ok()?;
        let policy_dig = crate::zygote::compute_module_audit_policy_digest(cfg, mod_name);
        if !store.has_kernel_audited_olean_with_key(
            &key,
            &dig,
            &env_dig,
            crate::zygote::ZYGOTE_REPLAY_VERSION,
            &cfg.lean_githash,
            &policy_dig,
        ) {
            return None;
        }
        if compute_replayed_olean_ilean_digest(olean_path)
            .ok()
            .as_deref()
            != Some(dig.as_str())
        {
            return None;
        }
        self.capture_verified_closure_authority(root_id, artifact_digest)
    }

    pub(crate) fn is_audited_in_store(
        &mut self,
        store: &TurboStore,
        cfg: &ProjectConfig,
        lean_path_env: &str,
        mod_name: &str,
        olean_path: &Path,
    ) -> bool {
        let _ = lean_path_env;
        let binds_policy = self.is_root_olean(olean_path);
        self.is_audited_in_store_with_binds_policy(store, cfg, mod_name, olean_path, binds_policy)
    }

    pub(crate) fn disallowed_roots(&self) -> &[PathBuf] {
        &self.disallowed_roots
    }

    pub(crate) fn resolve_module_olean(&mut self, m: &str) -> Option<PathBuf> {
        let found = self.resolve_module_along_dirs(m)?;
        self.path_memo.insert(m.to_string(), found.clone());
        Some(found)
    }
}

#[cfg(test)]
pub(crate) fn compute_olean_transitive_env_digest(
    cfg: &ProjectConfig,
    lean_path_env: &str,
    olean_path: &Path,
) -> Result<String> {
    let window = current_memo_window();
    let memo = OLEAN_TRANSITIVE_ENV_MEMO.get_or_init(|| Mutex::new(HashMap::new()));
    let binds_policy = is_root_project_olean_path(cfg, olean_path);
    let policy_dig = if binds_policy {
        crate::splitter::current_kernel_policy_digest()
    } else {
        String::new()
    };
    let policy_key = format!(
        "{}\u{0}{}\u{0}{}",
        cfg.lean_githash,
        u8::from(binds_policy),
        policy_dig
    );
    let key = (
        policy_key,
        lean_path_env.to_string(),
        olean_path.to_path_buf(),
    );
    let mut stat_memo: HashMap<PathBuf, FileStatFingerprint> = HashMap::new();
    if let Ok(g) = memo.lock() {
        if let Some((w, dep_stats, hit)) = g.get(&key) {
            if *w == window
                && dep_stats.iter().all(|(p, expected_st)| {
                    let cur = *stat_memo
                        .entry(p.clone())
                        .or_insert_with(|| path_stat_fingerprint(p));
                    cur == *expected_st
                })
            {
                return Ok(hit.clone());
            }
        }
    }
    let mut dirs: Vec<PathBuf> = std::env::split_paths(lean_path_env).collect();
    if !cfg.toolchain_lib_lean.as_os_str().is_empty() && !dirs.contains(&cfg.toolchain_lib_lean) {
        dirs.push(cfg.toolchain_lib_lean.clone());
    }
    let mut path_memo: HashMap<String, PathBuf> = HashMap::new();
    let mut valid_closures: HashSet<PathBuf> = HashSet::new();
    let (tracked_stats, resolved_tc, resolved_non_tc) =
        resolve_olean_import_closure_cached_with_stat_memo(
            cfg,
            &dirs,
            lean_path_env,
            olean_path,
            &mut stat_memo,
            &mut path_memo,
            &mut valid_closures,
        )?;
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-olean-transitive-env-v1\n");
    update_lp(&mut h, b"githash", cfg.lean_githash.as_bytes());
    if binds_policy && !policy_dig.is_empty() {
        update_lp(&mut h, b"kernel_policy", policy_dig.as_bytes());
    }
    h.update(&(resolved_tc.len() as u64).to_le_bytes());
    for tc_m in resolved_tc.iter() {
        update_lp(&mut h, b"tc", tc_m.as_bytes());
    }
    h.update(&(resolved_non_tc.len() as u64).to_le_bytes());
    for (dep_m, dep_dig) in resolved_non_tc.iter() {
        update_lp(&mut h, b"dep_mod", dep_m.as_bytes());
        update_lp(&mut h, b"dep_dig", dep_dig.as_bytes());
    }
    let res = h.finalize().to_hex().to_string();
    if let Ok(mut g) = memo.lock() {
        if current_memo_window() == window {
            if g.len() >= 16384 {
                g.clear();
            }
            g.insert(key, (window, tracked_stats, res.clone()));
        }
    }
    Ok(res)
}

#[cfg(test)]
pub(crate) fn is_olean_replayed_in_store(
    store: &TurboStore,
    cfg: &ProjectConfig,
    lean_path_env: &str,
    olean_path: &Path,
) -> bool {
    if cfg.lean_githash.is_empty() {
        return false;
    }
    let disallowed_roots = project_disallowed_replay_store_roots(cfg);
    if !store.is_store_outside_disallowed_roots(&disallowed_roots) {
        return false;
    }
    let Ok(dig) = compute_replayed_olean_ilean_digest(olean_path) else {
        return false;
    };
    let Ok(env_dig) = compute_olean_transitive_env_digest(cfg, lean_path_env, olean_path) else {
        return false;
    };
    store.has_kernel_replayed_olean(
        &dig,
        &env_dig,
        crate::zygote::ZYGOTE_REPLAY_VERSION,
        &cfg.lean_githash,
        &disallowed_roots,
    )
}

/// Compute the per-module CAS action key (`module_unit`), incorporating:
/// - toolchain string & `lean --githash`
/// - OS & architecture
/// - package configuration digest
/// - normalized strong & weak Lean arguments
/// - `is_module`, `has_prelude`, `precompile_modules`, `needs_c`
/// - module name & source BLAKE3 digest
/// - the digests of the declarative Lake file inputs the module may read (`needs`)
/// - exact dependency `.olean` (+ `.olean.server` / `.olean.private`) digests
/// - `extern_lib` static archive digests
pub fn compute_module_cas_key(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    dep_olean_digests: &[(String, String)],
    needs_c_override: bool,
) -> Result<String> {
    compute_module_cas_key_with_dynlibs(cfg, node, dep_olean_digests, needs_c_override, &[])
}

pub fn compute_module_cas_key_with_dynlibs(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    dep_olean_digests: &[(String, String)],
    needs_c_override: bool,
    import_dynlib_digests: &[(String, String)],
) -> Result<String> {
    let toolchain_valid =
        !cfg.toolchain.is_empty() && !cfg.lean_githash.is_empty() && cfg.lean_bin.is_file();
    let args_valid = node
        .strong_args
        .iter()
        .chain(node.weak_args.iter())
        .all(|a| is_allowed_lean_arg(verification_lake_arg(a)))
        && node
            .lean_options
            .iter()
            .all(|(k, v)| is_allowed_lean_option(k, &verification_lake_option(k, v)));
    let src_valid = node.src_blake3.len() == 64;
    let cfg_valid = node.pkg_config_digest.len() == 64;
    let deps_sorted_unique = dep_olean_digests.windows(2).all(|w| w[0].0 < w[1].0)
        && dep_olean_digests
            .iter()
            .all(|(m, d)| !m.is_empty() && !d.is_empty());
    let provided_dep_names: HashSet<&str> =
        dep_olean_digests.iter().map(|(m, _)| m.as_str()).collect();
    let all_direct_and_ext_present = node
        .direct_dag_deps
        .iter()
        .all(|d| provided_dep_names.contains(d.as_str()))
        && node
            .external_olean_deps
            .iter()
            .all(|(d, _)| provided_dep_names.contains(d.as_str()));
    let deps_exact_match = all_direct_and_ext_present
        && dep_olean_digests.len() == node.expected_all_deps.len()
        && dep_olean_digests
            .iter()
            .zip(node.expected_all_deps.iter())
            .all(|((m, _), exp_m)| m == exp_m);
    let deps_valid = deps_sorted_unique && deps_exact_match;

    let gate_ok = c_abi::verify_module_cache_key(
        toolchain_valid,
        args_valid,
        src_valid,
        deps_valid,
        cfg_valid,
    );
    if !gate_ok {
        if !deps_sorted_unique {
            anyhow::bail!(
                "C-ABI gate `turbo_spec_verify_module_cache_key` rejected unsorted or duplicate dependency digests for module `{}`",
                node.module_name
            );
        }
        if !all_direct_and_ext_present {
            anyhow::bail!(
                "C-ABI gate `turbo_spec_verify_module_cache_key` rejected incomplete dependency digests for module `{}` (missing required dependency)",
                node.module_name
            );
        }
        if !deps_exact_match {
            anyhow::bail!(
                "C-ABI gate `turbo_spec_verify_module_cache_key` rejected dependency digests for module `{}` (unexpected extra dependency outside resolved DAG)",
                node.module_name
            );
        }
        anyhow::bail!(
            "C-ABI gate `turbo_spec_verify_module_cache_key` rejected cache key inputs for module `{}` (toolchain={}, args={}, src={}, deps={}, cfg={})",
            node.module_name,
            toolchain_valid,
            args_valid,
            src_valid,
            deps_valid,
            cfg_valid
        );
    }
    validate_materialized_artifacts(cfg)?;
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-module-cas-v8\n");
    update_lp(
        &mut h,
        b"build_epoch",
        crate::TURBO_LEAN_BUILD_EPOCH.as_bytes(),
    );
    update_lp(&mut h, b"toolchain", cfg.toolchain.as_bytes());
    update_lp(&mut h, b"githash", cfg.lean_githash.as_bytes());
    update_lp(
        &mut h,
        b"lean_bin_digest",
        blake3::hash(&fs::read(&cfg.lean_bin).context("Cannot hash Lean compiler")?).as_bytes(),
    );
    update_lp(&mut h, b"os", std::env::consts::OS.as_bytes());
    update_lp(&mut h, b"arch", std::env::consts::ARCH.as_bytes());
    update_lp(&mut h, b"pkg_cfg", node.pkg_config_digest.as_bytes());
    update_lp(&mut h, b"pkg_name", node.pkg_name.as_bytes());
    update_lp(&mut h, b"pkg_base_name", node.pkg_base_name.as_bytes());
    update_lp(&mut h, b"target", node.target_name.as_bytes());
    update_lp(&mut h, b"module", node.module_name.as_bytes());
    let pi_byte = match node.platform_independent {
        None => b'n',
        Some(false) => b'f',
        Some(true) => b't',
    };
    let flags_bytes = [
        if node.is_module { b'M' } else { b'm' },
        if node.has_prelude { b'P' } else { b'p' },
        if node.precompile_modules { b'C' } else { b'c' },
        if needs_c_override { b'E' } else { b'e' },
        pi_byte,
    ];
    update_lp(&mut h, b"flags", &flags_bytes);
    update_hasher_lean_options(&mut h, &node.lean_options);
    h.update(&(node.strong_args.len() as u64).to_le_bytes());
    for a in &node.strong_args {
        update_lp(&mut h, b"sarg", a.as_bytes());
    }
    h.update(&(node.weak_args.len() as u64).to_le_bytes());
    for a in &node.weak_args {
        update_lp(&mut h, b"warg", a.as_bytes());
    }
    update_lp(&mut h, b"src", node.src_blake3.as_bytes());
    // Declarative Lake file inputs the module may read during elaboration (`needs`).
    let lake_inputs = module_lake_input_digest(cfg, node)?;
    if !lake_inputs.is_empty() {
        update_lp(&mut h, b"lake_inputs", lake_inputs.as_bytes());
    }
    h.update(&(dep_olean_digests.len() as u64).to_le_bytes());
    for (dep_mod, dep_hash) in dep_olean_digests {
        update_lp(&mut h, b"dep_mod", dep_mod.as_bytes());
        update_lp(&mut h, b"dep_hash", dep_hash.as_bytes());
    }
    h.update(&(node.extern_lib_digests.len() as u64).to_le_bytes());
    for ext in &node.extern_lib_digests {
        update_lp(&mut h, b"ext_lib", ext.as_bytes());
    }
    if !import_dynlib_digests.is_empty() {
        h.update(&(import_dynlib_digests.len() as u64).to_le_bytes());
        for (dyn_tag, dyn_hash) in import_dynlib_digests {
            update_lp(&mut h, b"imp_dynlib_tag", dyn_tag.as_bytes());
            update_lp(&mut h, b"imp_dynlib_hash", dyn_hash.as_bytes());
        }
    }
    let allowed = crate::splitter::allowed_axioms();
    if allowed.len() > crate::splitter::STANDARD_AXIOMS.len() {
        update_lp(&mut h, b"axioms", allowed.join(",").as_bytes());
    }
    Ok(h.finalize().to_hex().to_string())
}
pub(crate) fn record_verified_dep_source(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    node: &ModuleNode,
    olean_artifact_digest: &str,
    kernel_audited: bool,
    olean_digests: &HashMap<String, String>,
    tier_digests: &HashMap<String, ModuleArtifactTierDigests>,
) {
    let tainted = compute_tainted_elab_host_effect_modules(cfg, dag);
    let mut one_shot_cache: HashMap<PathBuf, (VerifiedDepManifest, bool)> = HashMap::new();
    let ws_inputs = workspace_lake_inputs_digest(cfg).ok();
    record_verified_dep_source_cached(
        cfg,
        dag,
        node,
        tainted.contains(&node.module_name),
        olean_artifact_digest,
        kernel_audited,
        olean_digests,
        tier_digests,
        &mut one_shot_cache,
        false,
        ws_inputs.as_deref(),
    );
}

pub(crate) fn record_locally_rebuilt_sources(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    modules: &[String],
) -> Result<()> {
    let mut full = HashMap::new();
    let mut tiers = HashMap::new();
    for node in dag.nodes.values() {
        for (name, path) in std::iter::once((&node.module_name, &node.olean_path))
            .chain(node.external_olean_deps.iter().map(|(m, p)| (m, p)))
        {
            let td = compute_module_artifact_tier_digests_with_policy(path, true)?;
            full.insert(name.clone(), td.full.clone());
            tiers.insert(name.clone(), td);
        }
    }
    let inputs = workspace_lake_inputs_digest(cfg)?;
    let mut manifests = HashMap::new();
    for name in modules {
        if let Some(node) = dag.nodes.get(name) {
            record_verified_dep_source_cached(
                cfg,
                dag,
                node,
                false,
                &full[name],
                false,
                &full,
                &tiers,
                &mut manifests,
                false,
                Some(&inputs),
            );
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn record_verified_dep_source_cached(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    node: &ModuleNode,
    closure_has_elab_host_effects: bool,
    olean_artifact_digest: &str,
    kernel_audited: bool,
    olean_digests: &HashMap<String, String>,
    tier_digests: &HashMap<String, ModuleArtifactTierDigests>,
    manifest_cache: &mut HashMap<PathBuf, (VerifiedDepManifest, bool)>,
    defer_disk_flush: bool,
    precomputed_ws_inputs: Option<&str>,
) {
    let src_raw = fs::read_to_string(&node.src_path).ok();
    if closure_has_elab_host_effects
        || src_raw.as_ref().is_none_or(|src| {
            source_ineligible_for_stamp_reuse(
                cfg,
                &node.pkg_root,
                &node.module_name,
                &node.src_path,
                src,
            )
        })
    {
        let pkg_root = &node.pkg_root;
        let rel_src = node
            .src_path
            .strip_prefix(pkg_root)
            .unwrap_or(&node.src_path)
            .to_string_lossy()
            .replace('\\', "/");
        if let Some((manifest, dirty)) = manifest_cache.get_mut(pkg_root) {
            if manifest.modules.remove(&rel_src).is_some() {
                *dirty = true;
                if !defer_disk_flush && flush_verified_dep_manifest_atomic(pkg_root, manifest) {
                    *dirty = false;
                }
            }
        } else {
            let manifest_path = pkg_root.join(".lake/build/.turbo_verified_sources.json");
            if let Ok(bytes) = fs::read(&manifest_path) {
                if let Ok(mut m) = serde_json::from_slice::<VerifiedDepManifest>(&bytes) {
                    if m.modules.remove(&rel_src).is_some() {
                        let _ = flush_verified_dep_manifest_atomic(pkg_root, &m);
                    }
                }
            }
        }
        return;
    }
    // Pin the direct imports the `.olean` was elaborated against; skip recording if the
    // source moved on mid-build or a dependency digest is unknown.
    let Some(header) = src_raw
        .filter(|src| blake3::hash(src.as_bytes()).to_hex().as_str() == node.src_blake3)
        .map(|src| parse_header_info(&src))
    else {
        return;
    };
    let direct_import_names: Vec<&String> = node
        .direct_dag_deps
        .iter()
        .chain(
            node.external_olean_deps
                .iter()
                .map(|(m, _)| m)
                .filter(|m| header.imports.contains(m)),
        )
        .collect();
    let Some(import_olean_digests) = direct_import_names
        .iter()
        .map(|&m| Some((m.clone(), olean_digests.get(m)?.clone())))
        .collect::<Option<BTreeMap<_, _>>>()
    else {
        return;
    };
    let mut import_export_digests = BTreeMap::new();
    let mut import_meta_digests = BTreeMap::new();
    if header.is_module {
        for &m in &direct_import_names {
            let dep_is_mod = dag
                .nodes
                .get(m)
                .map(|n| n.is_module)
                .unwrap_or_else(|| resolve_dep_module_visibility_spec(cfg, dag, node, m).0);
            if dep_is_mod {
                if let Some(td) = tier_digests.get(m) {
                    import_export_digests.insert(m.clone(), td.dep_export.clone());
                    import_meta_digests.insert(m.clone(), td.dep_meta.clone());
                }
            }
        }
    }
    let preserve = crate::lake_build::worktree_auto_link_disabled(&cfg.root_pkg.pkg_root);
    let (olean_export_digest, olean_meta_digest) = if header.is_module {
        compute_module_artifact_tier_digests_with_policy(&node.olean_path, preserve)
            .ok()
            .filter(|td| td.full == olean_artifact_digest)
            .map(|td| (td.dep_export, td.dep_meta))
            .unwrap_or_default()
    } else {
        (String::new(), String::new())
    };
    // Fingerprint only a stable dependency-package artifact set that is already past the
    // sub-tick trust window (`STAT_TRUST_WINDOW_NS`) and still digests to the recorded value;
    // root `.turbo_verified_sources.json` stays purely content-addressed across CAS restores.
    let fp = (!node.is_root_pkg)
        .then(|| olean_artifact_stat_fingerprint_for_store(&node.olean_path))
        .flatten();
    let artifact_stat_fingerprint = fp
        .filter(|fp| {
            compute_olean_artifact_set_digest_with_policy(
                &node.olean_path,
                crate::lake_build::worktree_auto_link_disabled(&cfg.root_pkg.pkg_root),
            )
            .is_ok_and(|d| d == olean_artifact_digest)
                && olean_artifact_stat_fingerprint_for_store(&node.olean_path).as_ref() == Some(fp)
        })
        .unwrap_or_default();
    let pkg_root = &node.pkg_root;
    let build_dir = pkg_root.join(".lake/build");
    let _ = fs::create_dir_all(&build_dir);
    let manifest_path = build_dir.join(".turbo_verified_sources.json");
    let allowed_axioms = crate::splitter::allowed_axioms();
    let kernel_policy_digest = crate::splitter::current_kernel_policy_digest();
    // Recorded alongside the entries so every reader can tell whether these `.olean` files were
    // elaborated against the Lake file inputs currently on disk. Workspace-wide, matching
    // `lake_build::load_verified_project_manifest`: a module of this package imports dependency
    // modules whose own elaboration reads the dependency's inputs.
    let Some(lake_inputs_digest) = precomputed_ws_inputs.map(str::to_string) else {
        // Never stamp a verified-sources manifest when any workspace Lake input is unsupported.
        manifest_cache.remove(pkg_root);
        let _ = fs::remove_file(&manifest_path);
        return;
    };
    let (manifest, dirty) = manifest_cache.entry(pkg_root.clone()).or_insert_with(|| {
        let mut header_changed = false;
        let loaded = fs::read(&manifest_path)
            .ok()
            .and_then(|b| serde_json::from_slice::<VerifiedDepManifest>(&b).ok())
            .filter(|m| {
                m.pkg_name == node.pkg_name
                    && m.toolchain == cfg.toolchain
                    && m.lean_githash == cfg.lean_githash
                    && m.pkg_config_digest == node.pkg_config_digest
            })
            .map(|mut m| {
                // Retain untouched sibling entries across workspace-digest, Lake-input, or axiom-policy
                // shifts (`turbo-lean build` rooted inside a dependency package vs. from its consumer,
                // partial library rebuilds, or under a narrower allowlist) so `dep_pkg_module_stale`
                // never misclassifies a previously native-built sibling as Lake-managed. Each entry
                // carries its own `lake_inputs_digest`, so updating the header digest never promotes
                // un-rebuilt siblings; when `allowed_axioms` changed, drop `kernel_audited` on
                // retained entries so stale audit bits never carry over.
                if m.allowed_axioms != allowed_axioms
                    || m.kernel_policy_digest != kernel_policy_digest
                {
                    for e in m.modules.values_mut() {
                        e.kernel_audited = false;
                    }
                    m.allowed_axioms = allowed_axioms.clone();
                    m.kernel_policy_digest = kernel_policy_digest.clone();
                    header_changed = true;
                }
                if m.lake_inputs_digest != lake_inputs_digest {
                    m.lake_inputs_digest = lake_inputs_digest.clone();
                    header_changed = true;
                }
                if m.workspace_config_digest != cfg.canonical_config_digest {
                    m.workspace_config_digest = cfg.canonical_config_digest.clone();
                    header_changed = true;
                }
                m
            });
        match loaded {
            Some(m) => (m, header_changed),
            None => (
                VerifiedDepManifest {
                    pkg_name: node.pkg_name.clone(),
                    toolchain: cfg.toolchain.clone(),
                    lean_githash: cfg.lean_githash.clone(),
                    pkg_config_digest: node.pkg_config_digest.clone(),
                    lake_inputs_digest: lake_inputs_digest.clone(),
                    workspace_config_digest: cfg.canonical_config_digest.clone(),
                    allowed_axioms,
                    kernel_policy_digest,
                    modules: BTreeMap::new(),
                    cfg: None,
                    dep_import_memo: DepImportMemo::default(),
                },
                true,
            ),
        }
    });
    let rel_src = node
        .src_path
        .strip_prefix(pkg_root)
        .unwrap_or(&node.src_path)
        .to_string_lossy()
        .replace('\\', "/");
    let new_entry = VerifiedDepModuleEntry {
        src_blake3: node.src_blake3.clone(),
        olean_artifact_digest: olean_artifact_digest.to_string(),
        lake_inputs_digest,
        kernel_audited,
        import_olean_digests,
        import_export_digests,
        import_meta_digests,
        olean_export_digest,
        olean_meta_digest,
        artifact_stat_fingerprint,
    };
    if manifest.modules.get(&rel_src) != Some(&new_entry) {
        manifest.modules.insert(rel_src, new_entry);
        *dirty = true;
    }
    if !defer_disk_flush && *dirty && flush_verified_dep_manifest_atomic(pkg_root, manifest) {
        *dirty = false;
    }
}

pub(super) fn flush_verified_dep_manifest_atomic(pkg_root: &Path, manifest: &VerifiedDepManifest) -> bool {
    let build_dir = pkg_root.join(".lake/build");
    let _ = fs::create_dir_all(&build_dir);
    let manifest_path = build_dir.join(".turbo_verified_sources.json");
    let Ok(json_bytes) = serde_json::to_vec(manifest) else {
        return false;
    };
    let tmp_path = build_dir.join(format!(
        ".turbo_verified_sources.json.tmp.{}.{}",
        std::process::id(),
        crate::pack::next_tmp_id()
    ));
    let write_ok = (|| -> std::io::Result<()> {
        use std::io::Write;
        let mut f = create_fresh_file(&tmp_path)?;
        f.write_all(&json_bytes)?;
        f.sync_all()?;
        Ok(())
    })()
    .is_ok();
    if write_ok && fs::rename(&tmp_path, &manifest_path).is_ok() {
        true
    } else {
        let _ = fs::remove_file(&tmp_path);
        false
    }
}

pub(super) fn flush_all_verified_dep_manifests(
    manifest_cache: &mut HashMap<PathBuf, (VerifiedDepManifest, bool)>,
) {
    for (pkg_root, (manifest, dirty)) in manifest_cache.iter_mut() {
        if *dirty && flush_verified_dep_manifest_atomic(pkg_root, manifest) {
            *dirty = false;
        }
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn probe_warm_on_disk_module_candidate(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    node: &ModuleNode,
    preserve_lake: bool,
    olean_digests: &HashMap<String, String>,
    tier_digests: &HashMap<String, ModuleArtifactTierDigests>,
    raw_imp_dynlibs: &[PathBuf],
    exp_memo: &mut HashMap<(String, bool), LakeModuleExportInfo>,
    probe_manifest_cache: &mut HashMap<PathBuf, Option<Result<VerifiedDepManifest, ()>>>,
    precomputed_ws_inputs: Option<&str>,
) -> Option<String> {
    if cfg.lean_githash.is_empty()
        || cfg.lean_githash == "lean-not-installed"
        || cfg.lean_githash.len() != 40
    {
        return None;
    }
    let src_raw = fs::read_to_string(&node.src_path).ok()?;
    if blake3::hash(src_raw.as_bytes()).to_hex().as_str() != node.src_blake3 {
        return None;
    }
    if node_source_has_disallowed_elab_host_effects(cfg, node, &src_raw) {
        return None;
    }
    let header = parse_header_info(&src_raw);
    if header.header_error.is_some() || header.is_module != node.is_module {
        return None;
    }
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
    if !sorry_ok
        || !axiom_ok
        || (node.is_root_pkg && hygiene.native_violation())
        || (node.is_root_pkg && hygiene.has_trust_compiler)
        || !checking_weakening_ok
    {
        return None;
    }
    if node.is_module {
        let ir_path = node.olean_path.with_extension("ir");
        let ir_sig_path = PathBuf::from(format!("{}.sig", ir_path.display()));
        let needs_ir_sig = !lake_trace_uses_nested_mod_deps(&cfg.toolchain)
            || olean_requires_ir_sig(&node.olean_path);
        if !is_regular_nonempty_file(&ir_path)
            || (needs_ir_sig && !is_regular_nonempty_file(&ir_sig_path))
        {
            return None;
        }
    }
    let actual_olean_digest = {
        let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
        let _guard = lock.lock().ok()?;
        let _flock_guard = acquire_publish_flock_mode(&node.pkg_root, false, true).ok()?;
        let mut paths: Vec<_> = olean_artifact_paths(&node.olean_path)
            .into_iter()
            .map(|(_, p)| p)
            .collect();
        if node.needs_c || node.c_path.exists() {
            paths.push(node.c_path.clone());
        }
        _flock_guard
            .read_consistent(&paths, || {
                if !validate_materialized_module_artifacts(node, true) {
                    return Ok(None);
                }
                let Some((_, hdr_gh)) = read_olean_header_version_and_githash(&node.olean_path)
                else {
                    return Ok(None);
                };
                if !hdr_gh.eq_ignore_ascii_case(cfg.lean_githash.trim()) {
                    return Ok(None);
                }
                compute_olean_artifact_set_digest_locked(&node.olean_path, Some(&_flock_guard))
                    .map(Some)
            })
            .ok()
            .flatten()?
    };

    let expected_ws_inputs = precomputed_ws_inputs?;
    let rel_src = node
        .src_path
        .strip_prefix(&node.pkg_root)
        .unwrap_or(&node.src_path)
        .to_string_lossy()
        .replace('\\', "/");
    let manifest_entry = probe_manifest_cache
        .entry(node.pkg_root.clone())
        .or_insert_with(|| {
            let manifest_path = node
                .pkg_root
                .join(".lake/build/.turbo_verified_sources.json");
            match fs::read(&manifest_path) {
                Ok(bytes) => {
                    Some(serde_json::from_slice::<VerifiedDepManifest>(&bytes).map_err(|_| ()))
                }
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
                Err(_) => Some(Err(())),
            }
        });
    let raw_manifest_opt: Option<&VerifiedDepManifest> = match manifest_entry.as_ref() {
        Some(Ok(m)) => Some(m),
        Some(Err(())) => return None,
        None => None,
    };
    let raw_has_entry = raw_manifest_opt.is_some_and(|m| m.modules.contains_key(&rel_src));
    let validated_entry = raw_manifest_opt.and_then(|m| {
        if m.pkg_name == node.pkg_name
            && m.toolchain == cfg.toolchain
            && m.lean_githash == cfg.lean_githash
            && m.pkg_config_digest == node.pkg_config_digest
            && m.lake_inputs_digest == expected_ws_inputs
            && (!node.is_root_pkg
                || (m.workspace_config_digest == cfg.canonical_config_digest
                    && m.allowed_axioms == crate::splitter::allowed_axioms()
                    && m.kernel_policy_digest == crate::splitter::current_kernel_policy_digest()))
        {
            m.modules.get(&rel_src)
        } else {
            None
        }
    });
    let manifest_matched = if let Some(entry) = validated_entry {
        if raw_imp_dynlibs.is_empty()
            && entry.lake_inputs_digest == expected_ws_inputs
            && entry.src_blake3 == node.src_blake3
            && entry.olean_artifact_digest == actual_olean_digest
        {
            verified_entry_imports_current_for_header(entry, &header, |imp, pin_spec| {
                if let Some(expected_dig) = olean_digests.get(imp) {
                    let Some(ps) = pin_spec else {
                        return false;
                    };
                    if ps.full_pin == expected_dig {
                        return true;
                    }
                    let dep_is_mod = dag.nodes.get(imp).map(|n| n.is_module).unwrap_or_else(|| {
                        resolve_dep_module_visibility_spec(cfg, dag, node, imp).0
                    });
                    if !dep_is_mod {
                        return false;
                    }
                    match (ps.tier_pin, tier_digests.get(imp)) {
                        (Some((DepImportVisibility::PublicExport, exp)), Some(td)) => {
                            !exp.is_empty() && exp == td.dep_export
                        }
                        (Some((DepImportVisibility::MetaExport, meta)), Some(td)) => {
                            !meta.is_empty() && meta == td.dep_meta
                        }
                        _ => false,
                    }
                } else {
                    pin_spec.is_none()
                        && is_builtin_toolchain_module(
                            &cfg.toolchain_lib_lean,
                            Some(&cfg.lean_githash),
                            imp,
                        )
                }
            })
        } else {
            false
        }
    } else {
        false
    };
    if !manifest_matched {
        let uses_include_str = source_uses_include_str(&src_raw);
        let inputs_may_be_unverified_in_trace = !expected_ws_inputs.is_empty()
            && uses_include_str
            && input_bearing_libs_for_module(cfg, &node.module_name).is_empty()
            && input_bearing_exes_for_module(cfg, &node.module_name).is_empty();
        if raw_has_entry || inputs_may_be_unverified_in_trace {
            return None;
        }
    }

    let clean_stale_ltar_bc = || -> bool {
        if preserve_lake {
            return true;
        }
        let ltar_path = node.c_path.with_extension("ltar");
        let bc_path = node.c_path.with_extension("bc");
        let ltar_hash_path = PathBuf::from(format!("{}.hash", ltar_path.display()));
        let bc_hash_path = PathBuf::from(format!("{}.hash", bc_path.display()));
        let exists_any = |p: &Path| fs::symlink_metadata(p).is_ok();
        if !exists_any(&ltar_path)
            && !exists_any(&bc_path)
            && !exists_any(&ltar_hash_path)
            && !exists_any(&bc_hash_path)
        {
            return true;
        }
        let lock = PUBLISH_LOCK.get_or_init(|| Mutex::new(()));
        let Ok(_guard) = lock.lock() else {
            return false;
        };
        let Ok(_flock) = acquire_publish_flock(&node.pkg_root, false) else {
            return false;
        };
        for p in [&ltar_path, &bc_path, &ltar_hash_path, &bc_hash_path] {
            let _ = fs::remove_file(p);
        }
        validate_materialized_module_artifacts(node, false)
    };

    if manifest_matched {
        if preserve_lake {
            let rel_slash = module_name_to_rel_slash(&node.module_name);
            let ir_dir = node
                .c_path
                .to_string_lossy()
                .strip_suffix(&format!("{rel_slash}.c"))
                .map(|s| PathBuf::from(s.trim_end_matches('/')));
            if verify_module_lake_sidecars(
                &node.olean_path,
                ir_dir.as_deref(),
                &rel_slash,
                &src_raw,
                node.is_module,
                node.needs_c,
            )
            .is_err()
            {
                return None;
            }
        }
        if !clean_stale_ltar_bc() {
            return None;
        }
        return Some(actual_olean_digest);
    }

    if node.native_unsupported.is_some()
        || node.link_unsupported.is_some()
        || (node.precompile_modules && !node.extern_lib_digests.is_empty())
        || !node.weak_args.is_empty()
    {
        return None;
    }
    let rel_slash = module_name_to_rel_slash(&node.module_name);
    let ir_dir = node
        .c_path
        .to_string_lossy()
        .strip_suffix(&format!("{rel_slash}.c"))
        .map(|s| PathBuf::from(s.trim_end_matches('/')));
    verify_module_lake_sidecars_inner_opts_ext(
        &node.olean_path,
        ir_dir.as_deref(),
        &rel_slash,
        &src_raw,
        node.is_module,
        node.needs_c,
        false,
        true,
        !node.needs_c,
    )
    .ok()?;
    let tv: serde_json::Value =
        serde_json::from_slice(&fs::read(node.olean_path.with_extension("trace")).ok()?).ok()?;

    let mut import_entries = Vec::new();
    let mut visiting = HashSet::new();
    for imp in &header.import_specs {
        let is_ws_or_pkg = olean_digests.contains_key(&imp.module)
            || dag.nodes.contains_key(&imp.module)
            || node
                .external_olean_deps
                .iter()
                .any(|(m, _)| m == &imp.module)
            || resolve_importable_module_in_package(&cfg.root_pkg, true, &imp.module).is_some()
            || cfg
                .dep_pkgs
                .iter()
                .any(|dp| resolve_importable_module_in_package(dp, false, &imp.module).is_some())
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
            return None;
        }
        let exp_info =
            compute_lake_export_info(cfg, dag, node, &imp.module, exp_memo, &mut visiting).ok()?;
        import_entries.extend(lake_import_trace_entries(node.is_module, imp, &exp_info));
    }

    if tv.get("inputs").is_none() {
        let actual_dep_h = tv
            .get("depHash")
            .and_then(|v| v.as_str())
            .filter(|s| is_valid_16hex_hash(s))
            .and_then(|s| u64::from_str_radix(s, 16).ok())?;
        let expected_dep_h = compute_expected_lake_module_dep_hash(
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
            lake_hash_text(&src_raw),
            import_entries,
            raw_imp_dynlibs,
        )?;
        if actual_dep_h != expected_dep_h {
            return None;
        }
        if !clean_stale_ltar_bc() {
            return None;
        }
        return Some(actual_olean_digest);
    }

    let expected_imports_h = if import_entries.is_empty() {
        LAKE_NIL_HASH
    } else {
        lake_input_hash(&serde_json::Value::Array(import_entries)).ok()?
    };
    let nested = lake_trace_uses_nested_mod_deps(&cfg.toolchain);
    let expected_first_tag = format!("{}:deps", node.module_name);
    if tv.pointer("/inputs/0/0").and_then(|v| v.as_str())
        != Some(if nested {
            expected_first_tag.as_str()
        } else {
            "deps"
        })
    {
        return None;
    }
    let actual_imports_h = recorded_trace_imports_hash(&tv)?;
    let actual_extra_dep_h = tv
        .pointer(if nested {
            "/inputs/0/1/0/1/0/1"
        } else {
            "/inputs/0/1/0/1"
        })
        .and_then(|v| lake_input_hash(v).ok())?;

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
        format!("{LAKE_NIL_HASH:016x}")
    ])];
    extra_dep_entries.extend(lake_needs_trace_entries(cfg, node));
    let expected_extra_dep_h =
        lake_input_hash(&serde_json::Value::Array(extra_dep_entries)).ok()?;

    let expected_libs_json = if node.platform_independent == Some(true) {
        serde_json::json!([
            ["import dynlibs", "00000000000006bb"],
            ["package external libraries", "00000000000006bb"],
            ["module dynlibs", "00000000000006bb"],
            ["module plugins", "00000000000006bb"]
        ])
    } else {
        let mut import_dynlib_entries = Vec::with_capacity(raw_imp_dynlibs.len());
        for p in raw_imp_dynlibs {
            let h = verify_and_hash_artifact_bytes(p, false, false).ok()?;
            import_dynlib_entries.push(serde_json::json!([
                p.to_string_lossy(),
                format!("{:016x}", h)
            ]));
        }
        let import_dynlibs_json = if import_dynlib_entries.is_empty() {
            serde_json::Value::String("00000000000006bb".to_string())
        } else {
            serde_json::Value::Array(import_dynlib_entries)
        };
        serde_json::json!([
            ["import dynlibs", import_dynlibs_json],
            ["package external libraries", "00000000000006bb"],
            ["module dynlibs", "00000000000006bb"],
            ["module plugins", "00000000000006bb"]
        ])
    };
    let expected_libs_h = lake_input_hash(&expected_libs_json).ok()?;
    let actual_libs_h = if nested && node.platform_independent == Some(true) {
        expected_libs_h
    } else {
        let libs_pair = tv.pointer(if nested { "/inputs/0/1/1" } else { "/inputs/1" })?;
        if libs_pair.get(0).and_then(|v| v.as_str()) != Some("libs") {
            return None;
        }
        lake_input_hash(libs_pair.get(1)?).ok()?
    };

    let has_plat_entry = node.platform_independent == Some(false);
    let base_idx = if nested {
        1usize
    } else if has_plat_entry {
        3usize
    } else {
        2usize
    };
    if nested {
        let expected_nested_len = match node.platform_independent {
            Some(true) => 1usize,
            Some(false) => 3usize,
            None => 2usize,
        };
        if tv
            .pointer("/inputs/0/1")
            .and_then(|v| v.as_array())
            .is_none_or(|a| a.len() != expected_nested_len)
        {
            return None;
        }
    }
    if has_plat_entry {
        let tc_spec = query_toolchain_native_spec(&cfg.lean_bin).ok()?;
        if tc_spec.target.is_empty() {
            return None;
        }
        let expected_plat_h = format!("{:016x}", lake_hash_bytes(tc_spec.target.as_bytes()));
        let plat_pair = tv.pointer(if nested { "/inputs/0/1/2" } else { "/inputs/2" })?;
        if plat_pair.get(0).and_then(|v| v.as_str()) != Some(tc_spec.target.as_str())
            || plat_pair.get(1).and_then(|v| v.as_str()) != Some(expected_plat_h.as_str())
        {
            return None;
        }
    }

    let inputs_arr = tv.get("inputs").and_then(|v| v.as_array())?;
    let expected_len = base_idx + 7;
    if inputs_arr.len() != expected_len {
        return None;
    }

    let opt_idx = base_idx + 2;
    let opt_pair = inputs_arr.get(opt_idx).and_then(|v| v.as_array())?;
    if opt_pair.len() != 2
        || opt_pair[0].as_str() != Some("options")
        || !verify_trace_options_value(&node.lean_options, &opt_pair[1])
    {
        return None;
    }

    let args_pair = inputs_arr.get(opt_idx + 4).and_then(|v| v.as_array())?;
    if args_pair.len() != 2 {
        return None;
    }
    let expected_args_cap = if node.strong_args.is_empty() {
        "Module.leanArgs: #[]".to_string()
    } else {
        format!("Module.leanArgs: #[{}]", node.strong_args.join(", "))
    };
    let expected_args_h = format!(
        "{:016x}",
        node.strong_args
            .iter()
            .fold(LAKE_NIL_HASH, |acc, a| lake_mix_hash(
                acc,
                lake_hash_bytes(a.as_bytes())
            ))
    );
    if args_pair[0].as_str() != Some(expected_args_cap.as_str())
        || args_pair[1].as_str() != Some(expected_args_h.as_str())
    {
        return None;
    }

    let expected_gh = format!(
        "{:016x}",
        lake_hash_bytes(cfg.lean_githash.trim().as_bytes())
    );
    let expected_src = format!("{:016x}", lake_hash_text(&src_raw));
    let expected_is_mod = format!(
        "{:016x}",
        lake_mix_hash(LAKE_NIL_HASH, if node.is_module { 11 } else { 13 })
    );
    let expected_mod_name = format!("{:016x}", lake_hash_name(&node.module_name));
    let expected_pkg_id = format!("{:016x}", lake_hash_pkg_id(&node.pkg_name));

    if actual_imports_h != expected_imports_h
        || actual_extra_dep_h != expected_extra_dep_h
        || actual_libs_h != expected_libs_h
        || inputs_arr
            .get(base_idx)
            .and_then(|v| v.get(1))
            .and_then(|v| v.as_str())
            != Some(expected_gh.as_str())
        || inputs_arr
            .get(base_idx + 1)
            .and_then(|v| v.get(1))
            .and_then(|v| v.as_str())
            != Some(expected_src.as_str())
        || inputs_arr
            .get(base_idx + 3)
            .and_then(|v| v.get(1))
            .and_then(|v| v.as_str())
            != Some(expected_is_mod.as_str())
        || inputs_arr
            .get(base_idx + 4)
            .and_then(|v| v.get(1))
            .and_then(|v| v.as_str())
            != Some(expected_mod_name.as_str())
        || inputs_arr
            .get(base_idx + 5)
            .and_then(|v| v.get(1))
            .and_then(|v| v.as_str())
            != Some(expected_pkg_id.as_str())
    {
        return None;
    }

    if !clean_stale_ltar_bc() {
        return None;
    }
    Some(actual_olean_digest)
}

#[cfg(test)]
mod frozen_cone_tests {
    use super::*;

    fn env_test_guard() -> std::sync::MutexGuard<'static, ()> {
        crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner())
    }

    struct ScopedEnvVar {
        key: &'static str,
        prev: Option<std::ffi::OsString>,
    }

    impl ScopedEnvVar {
        fn set(key: &'static str, val: &str) -> Self {
            let prev = std::env::var_os(key);
            std::env::set_var(key, val);
            Self { key, prev }
        }
    }

    impl Drop for ScopedEnvVar {
        fn drop(&mut self) {
            match self.prev.take() {
                Some(p) => std::env::set_var(self.key, p),
                None => std::env::remove_var(self.key),
            }
        }
    }

    /// Re-materialize `build_dir` as a hardlinked pack: move it aside to `cas_dir` (the CAS
    /// `state.db` stand-in) and hardlink every artifact back, backdated to `artifact_mtime`.
    /// This is the cone shape `import` + `worktree-dedup` mint (#339): byte-identical artifacts
    /// whose mtimes predate the freshly stamped checkout sources.
    fn rematerialize_as_hardlinked_pack(
        build_dir: &Path,
        cas_dir: &Path,
        artifact_mtime: std::time::SystemTime,
    ) -> Result<()> {
        fs::rename(build_dir, cas_dir)?;
        for entry in WalkDir::new(cas_dir) {
            let entry = entry?;
            let rel = entry.path().strip_prefix(cas_dir)?;
            let dst = build_dir.join(rel);
            if entry.file_type().is_dir() {
                fs::create_dir_all(&dst)?;
            } else {
                fs::hard_link(entry.path(), &dst)?;
                fs::File::options()
                    .write(true)
                    .open(&dst)?
                    .set_modified(artifact_mtime)?;
            }
        }
        Ok(())
    }

    /// Rewrite `path` with identical bytes and stamp it strictly newer than any artifact, the way
    /// a fresh checkout / `git` operation stamps sources newer than a frozen pack's artifacts.
    fn restamp_checkout_file(path: &Path) -> Result<()> {
        let bytes = fs::read(path)?;
        fs::write(path, &bytes)?;
        fs::File::options()
            .write(true)
            .open(path)?
            .set_modified(std::time::SystemTime::now() + std::time::Duration::from_secs(2))?;
        Ok(())
    }

    #[test]
    fn test_frozen_cone_content_hash_freshness_hardlinked_cone_zero_rebuilds() -> Result<()> {
        let _env_guard = env_test_guard();
        let dir = std::env::temp_dir().join(format!(
            "turbo_lean_frozen_cone_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let proj_dir = dir.join("proj");
        let dep_dir = proj_dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("Dep"))?;
        fs::create_dir_all(proj_dir.join("App"))?;
        let run = (|| -> Result<()> {
            for d in [&proj_dir, &dep_dir] {
                fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
            }
            fs::write(
                dep_dir.join("lakefile.toml"),
                "name = \"dep_pkg\"\ndefaultTargets = [\"Dep\"]\n[[lean_lib]]\nname = \"Dep\"\nglobs = [\"Dep.+\"]\n",
            )?;
            fs::write(dep_dir.join("Dep/Base.lean"), "def baseVal : Nat := 7\n")?;
            fs::write(
                dep_dir.join("Dep/Value.lean"),
                "import Dep.Base\ndef depVal : Nat := baseVal\n",
            )?;
            fs::write(
                proj_dir.join("lake-manifest.json"),
                r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep_pkg", "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml", "inherited": false}], "name": "app_pkg", "lakeDir": ".lake", "fixedToolchain": false}"#,
            )?;
            fs::write(
                proj_dir.join("lakefile.toml"),
                "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
            )?;
            fs::write(
                proj_dir.join("App/Use.lean"),
                "import Dep.Value\ntheorem use_ok : depVal = 7 := rfl\n",
            )?;

            let mut store = TurboStore::open(Some(&dir.join(".turbo_store")))?;
            let rep0 = crate::module_builder::build_project_modules_native(
                &mut store,
                &proj_dir,
                &[],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )?;
            assert_eq!(rep0.modules_compiled, 3);
            assert!(dep_dir
                .join(".lake/build/.turbo_verified_sources.json")
                .is_file());

            // Freeze the dependency cone: hardlink its artifacts out of a CAS stand-in with the
            // pack's original (old) mtimes, then stamp sources and lakefiles newer, as a fresh
            // checkout does. Content stays byte-identical throughout.
            let backdate = std::time::SystemTime::now() - std::time::Duration::from_secs(3600);
            rematerialize_as_hardlinked_pack(
                &dep_dir.join(".lake/build"),
                &dir.join("cas_pack"),
                backdate,
            )?;
            for rel in [
                "Dep/Base.lean",
                "Dep/Value.lean",
                "lakefile.toml",
                "lean-toolchain",
            ] {
                restamp_checkout_file(&dep_dir.join(rel))?;
            }
            for rel in ["lakefile.toml", "lean-toolchain", "lake-manifest.json"] {
                restamp_checkout_file(&proj_dir.join(rel))?;
            }
            // Hand-materialized cones run with worktree auto-linking opted out (#339's flow).
            let _no_link = ScopedEnvVar::set("TURBO_LEAN_NO_WORKTREE_LINK", "1");

            // Control, the preserved default: raw mtime skew classifies the byte-identical
            // hardlinked cone stale, so its modules are scheduled for rebuild.
            reset_lake_inputs_tag_memo();
            let cfg = resolve_project_config(&proj_dir)?;
            let dag_mtime = build_module_dag_with_trust(&cfg, &["App.Use".to_string()], false)?;
            assert!(
                dag_mtime.nodes.contains_key("Dep.Base")
                    && dag_mtime.nodes.contains_key("Dep.Value"),
                "without --frozen-cone, mtime-skewed dep cone modules stay scheduled, got {:?}",
                dag_mtime.nodes.keys().collect::<Vec<_>>()
            );

            // `--frozen-cone`: freshness is decided by the verified-sources content hashes
            // (`src_blake3`, `olean_artifact_digest`, per-edge import pins), so the hardlinked
            // cone is adopted as external `.olean` deps with zero rebuild nodes.
            let _frozen = ScopedEnvVar::set("TURBO_LEAN_FROZEN_CONE", "1");
            reset_lake_inputs_tag_memo();
            let cfg = resolve_project_config(&proj_dir)?;
            let dag = build_module_dag_with_trust(&cfg, &["App.Use".to_string()], false)?;
            assert_eq!(
                dag.nodes.keys().map(|s| s.as_str()).collect::<Vec<_>>(),
                vec!["App.Use"],
                "frozen cone must contribute 0 rebuild nodes"
            );
            let use_node = dag.nodes.get("App.Use").unwrap();
            let mut ext: Vec<&str> = use_node
                .external_olean_deps
                .iter()
                .map(|(m, _)| m.as_str())
                .collect();
            ext.sort_unstable();
            assert_eq!(ext, vec!["Dep.Base", "Dep.Value"]);

            let rep = crate::module_builder::build_project_modules_native(
                &mut store,
                &proj_dir,
                &["App.Use".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )?;
            assert_eq!(
                rep.modules_compiled, 0,
                "hardlinked cone with equal content must trigger 0 rebuilds"
            );
            Ok(())
        })();
        let _ = fs::remove_dir_all(&dir);
        run
    }
}

