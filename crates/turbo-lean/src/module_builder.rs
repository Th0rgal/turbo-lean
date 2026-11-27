//! Native Lean 4 Project Configuration Resolver, Deterministic Module DAG Builder,
//! Direct `lean` Module Compiler, and Per-Module CAS (`module_unit`).
//!
//! Replaces runtime `lake build` invocations in `turbo-lean build` and `turbo-lean ci-verify`
//! with a Rust-owned module DAG orchestrator verified by C-ABI gates in `TurboLean.Kernel`:
//! - `turbo_spec_verify_static_lake_config`
//! - `turbo_spec_verify_dag_schedule_step`
//! - `turbo_spec_verify_module_cache_key`
//! - `turbo_spec_verify_module_artifact_set`
use crate::c_abi;
use crate::db::{BlobEntry, SingleflightOutcome, TurboStore};
use crate::lake_build;
use crate::splitter;
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
#[cfg(test)]
use std::sync::Arc;
use std::sync::{Mutex, OnceLock};
use std::time::Instant;
use walkdir::WalkDir;
mod dag;
pub use self::dag::*;
mod freshness;
pub use self::freshness::*;
mod host_effects;
pub(crate) use self::host_effects::*;
mod publish;
pub use self::publish::*;
#[cfg(test)]
#[path = "../tests/support/lean_options.rs"]
pub(crate) mod option_cases;

#[cfg(test)]
mod tests {
    use super::*;
    /// Serialize native builds with tests that toggle `TURBO_LEAN_NO_WORKTREE_LINK`.
    fn native_build_env_guard() -> std::sync::MutexGuard<'static, ()> {
        crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner())
    }
    fn make_temp_test_dir(tag: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "turbo_lean_mod_builder_{}_{}_{}",
            tag,
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create temp test dir");
        dir
    }
    #[cfg(unix)]
    #[test]
    fn test_stamp_eligibility_canonical_package_root() -> Result<()> {
        let dir = make_temp_test_dir("stamp_canonical_root");
        let root = dir.join("project");
        fs::create_dir_all(&root)?;
        fs::write(
            root.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )?;
        fs::write(
            root.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage p\ninput_file data where\n  path := \"data.txt\"\nlean_lib P where\n  needs := #[data]\n",
        )?;
        fs::write(root.join("data.txt"), "tracked")?;
        fs::write(root.join("other.txt"), "untracked")?;
        let cfg = resolve_project_config(&root)?;
        let alias = dir.join("alias");
        std::os::unix::fs::symlink(&root, &alias)?;
        let mut alias_cfg = cfg.clone();
        alias_cfg.root_pkg.pkg_root = alias.clone();
        for cfg in [&cfg, &alias_cfg] {
            for pkg_root in [&root, &alias, &root.join("../project")] {
                assert!(
                    package_by_root(cfg, pkg_root).is_some(),
                    "{}",
                    pkg_root.display()
                );
                for (source, ineligible) in [
                    ("def value : Nat := 1\n", false),
                    ("def value := include_str \"data.txt\"\n", false),
                    ("def value := include_str \"other.txt\"\n", true),
                    ("#eval (IO.FS.readFile \"P/data.txt\")\n", true),
                ] {
                    assert_eq!(
                        source_ineligible_for_stamp_reuse(
                            cfg,
                            pkg_root,
                            "P",
                            &pkg_root.join("P.lean"),
                            source,
                        ),
                        ineligible,
                        "{}: {source}",
                        pkg_root.display(),
                    );
                }
            }
        }
        assert!(source_ineligible_for_stamp_reuse(
            &cfg,
            &dir,
            "P",
            &dir.join("P.lean"),
            "def value : Nat := 1\n",
        ));
        assert!(source_ineligible_for_stamp_reuse(
            &cfg,
            &dir.join("missing"),
            "P",
            &root.join("P.lean"),
            "def value : Nat := 1\n",
        ));
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_post_lake_refresh_rejects_untracked_stamp_inputs() -> Result<()> {
        let _guard = native_build_env_guard();
        let tree = crate::worktree_test_support::LakeTree::new(
            "post_refresh_stamp_inputs",
            &[
                ("P/Pure.lean", "def value : Nat := 1\n"),
                (
                    "P/Include.lean",
                    "def embedded := include_str \"data.txt\"\n",
                ),
                ("P/Host.lean", "#eval (IO.FS.readFile \"P/data.txt\")\n"),
                ("P/data.txt", "first"),
            ],
        )?;
        let cfg = resolve_project_config(&tree.project)?;
        for module in ["P.Pure", "P.Include", "P.Host"] {
            let spec = resolve_module_in_package(&cfg.root_pkg, true, module).unwrap();
            let pin = compute_olean_artifact_set_digest(&spec_olean_path(&spec))?;
            let entry = VerifiedDepModuleEntry {
                src_blake3: blake3::hash(&fs::read(&spec.src_path)?)
                    .to_hex()
                    .to_string(),
                olean_artifact_digest: pin.clone(),
                lake_inputs_digest: workspace_lake_inputs_digest(&cfg)?,
                kernel_audited: true,
                ..Default::default()
            };
            let manifest = VerifiedDepManifest {
                modules: BTreeMap::from([(spec_rel_src(&spec), entry)]),
                ..Default::default()
            };
            let mut fresh_cache = LakeClosureCache {
                post_lake_refresh: true,
                ..Default::default()
            };
            assert!(lake_closure_export_info(
                &cfg, &spec, false, &mut fresh_cache, &mut HashSet::new(),
            ).is_some(), "fresh unstamped {module}");
            assert!(
                dep_pkg_import_pins_consistent(
                    &cfg,
                    &DepImportMemo::default(),
                    &mut fresh_cache,
                    spec.clone(),
                    ImportPinSpec {
                        full_pin: &pin,
                        tier_pin: None
                    },
                    false,
                ),
                "fresh unstamped pins {module}"
            );
            for strict in [false, true] {
                for post_lake_refresh in [false, true] {
                    let mut cache = LakeClosureCache {
                        post_lake_refresh,
                        ..Default::default()
                    };
                    cache.insert_pre_pkg_manifest(
                        spec.pkg_root.clone(),
                        strict,
                        Some(Ok(manifest.clone())),
                        Some(manifest.clone()),
                    );
                    assert_eq!(
                        lake_closure_export_info(
                            &cfg,
                            &spec,
                            strict,
                            &mut cache,
                            &mut HashSet::new(),
                        )
                        .is_some(),
                        module == "P.Pure",
                        "closure {module}, strict={strict}, refreshed={post_lake_refresh}",
                    );
                    assert_eq!(
                        dep_pkg_import_pins_consistent(
                            &cfg,
                            &DepImportMemo::default(),
                            &mut cache,
                            spec.clone(),
                            ImportPinSpec {
                                full_pin: &pin,
                                tier_pin: None
                            },
                            strict,
                        ),
                        module == "P.Pure",
                        "pins {module}, strict={strict}, refreshed={post_lake_refresh}",
                    );
                }
            }
        }
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_publication_process_child() -> Result<()> {
        let Some(root) = std::env::var_os("TURBO_TEST_PUBLISH_ROOT").map(PathBuf::from) else {
            return Ok(());
        };
        let mode = std::env::var("TURBO_TEST_PUBLISH_MODE")?;
        let node: ModuleNode = serde_json::from_slice(&fs::read(root.join("node.json"))?)?;
        fs::write(root.join("starting"), b"")?;
        if mode == "legacy" {
            let _legacy = crate::shm_cache::acquire_flock(
                &node.pkg_root.join(".lake/build/.turbo_publish.lock"),
                true,
                false,
            )?;
            fs::write(&node.olean_path, b"new olean")?;
            fs::write(&node.ilean_path, b"new ilean")?;
        } else if mode == "reader" {
            let digest = compute_olean_artifact_set_digest(&node.olean_path)?;
            assert_eq!(digest, fs::read_to_string(root.join("expected"))?);
        } else {
            let tmp = root.join("staged");
            publish_module_artifacts_atomic(
                &tmp,
                &node,
                &tmp.join("P.olean"),
                &tmp.join("P.ilean"),
                &tmp.join("P.olean.server"),
                &tmp.join("P.olean.private"),
                &tmp.join("P.ir"),
                &tmp.join("P.ir.sig"),
                &tmp.join("P.c"),
            )?;
        }
        fs::write(root.join("done"), b"")?;
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_reader_rejects_legacy_first_publication_mid_digest() -> Result<()> {
        use crate::worktree_test_support::{LakeTree, TestChild};
        let tree = LakeTree::new("legacy_race", &[("P/A.lean", "def value : Nat := 1\n")])?;
        let cfg = resolve_project_config(&tree.project)?;
        let dag = build_module_dag(&cfg, &[])?;
        let node = &dag.nodes["P.A"];
        tree.opt_out()?;
        let legacy = tree.project.join(".lake/build/.turbo_publish.lock");
        if legacy.exists() {
            fs::remove_file(&legacy)?;
        }
        fs::write(tree.root.join("node.json"), serde_json::to_vec(node)?)?;
        // Reader starts first and consumes the old .olean. An old binary then
        // creates only the legacy lock and replaces both outputs before .ilean.
        let guard = acquire_publish_flock_mode(&tree.project, false, true)?;
        let err =
            read_olean_artifact_set_digest_bound_with(&node.olean_path, Some(&guard), |path| {
                let res = read_regular_file_bound_stat(path)?;
                if path == node.olean_path {
                    let mut command =
                        TestChild::command("module_builder::tests::test_publication_process_child")
                            .map_err(std::io::Error::other)?;
                    command
                        .env("TURBO_TEST_PUBLISH_ROOT", &tree.root)
                        .env("TURBO_TEST_PUBLISH_MODE", "legacy");
                    let mut child =
                        TestChild::spawn(&mut command).map_err(std::io::Error::other)?;
                    child
                        .finish(&tree.root.join("done"))
                        .map_err(std::io::Error::other)?;
                }
                Ok(res)
            })
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("changed during") || err.contains("appeared or changed"),
            "{err}"
        );
        assert_eq!(fs::read(&node.olean_path)?, b"new olean");
        drop(guard);
        // A fresh reader locks the now-existing legacy inode and succeeds.
        compute_olean_artifact_set_digest(&node.olean_path)?;
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_publication_process_contention_across_cache_homes_and_legacy() -> Result<()> {
        use crate::worktree_test_support::{LakeTree, TestChild};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::new(
            "publish_contention",
            &[("P/A.lean", "def value : Nat := 1\n")],
        )?;
        let cfg = resolve_project_config(&tree.project)?;
        let dag = build_module_dag(&cfg, &[])?;
        let node = &dag.nodes["P.A"];
        fs::write(tree.root.join("node.json"), serde_json::to_vec(node)?)?;
        fs::create_dir_all(tree.root.join("staged"))?;
        // The parent and child use different HOME and TURBO_LEAN_HOME values. Exercise
        // both lock directions, first publication without a legacy file, and old holders.
        for (mode, legacy_holder, optout, missing_legacy) in [
            ("publisher", false, true, true),
            ("publisher", false, false, false),
            ("reader", false, false, false),
            ("reader", false, true, false),
            ("publisher", true, false, false),
            ("reader", true, true, false),
        ] {
            for name in ["starting", "done"] {
                let _ = fs::remove_file(tree.root.join(name));
            }
            if missing_legacy {
                let _ = fs::remove_file(tree.project.join(".lake/build/.turbo_publish.lock"));
            }
            if optout {
                tree.opt_out()?;
            } else {
                let _ = fs::remove_file(tree.project.join("turbo-lean.toml"));
            }
            let legacy = if legacy_holder {
                crate::shm_cache::acquire_flock(
                    &tree.project.join(".lake/build/.turbo_publish.lock"),
                    true,
                    false,
                )?
            } else {
                None
            };
            let current = if legacy_holder {
                None
            } else {
                Some(acquire_publish_flock_mode(
                    &tree.project,
                    mode == "reader",
                    optout,
                )?)
            };
            let mut command =
                TestChild::command("module_builder::tests::test_publication_process_child")?;
            command
                .env("TURBO_TEST_PUBLISH_ROOT", &tree.root)
                .env("TURBO_TEST_PUBLISH_MODE", mode)
                .env("TURBO_LEAN_HOME", tree.root.join("other-cache"))
                .env("HOME", tree.root.join("other-home"))
                // Only the reader opts out; its competing publisher must still create the
                // legacy lock once the directory reader has released it.
                .env("TURBO_LEAN_NO_WORKTREE_LINK", "0");
            if mode == "publisher" && optout {
                fs::remove_file(tree.project.join("turbo-lean.toml"))?;
            }
            if mode == "publisher" {
                fs::write(tree.root.join("staged/P.olean"), b"new olean generation")?;
                fs::write(tree.root.join("staged/P.ilean"), b"new ilean generation")?;
            }
            let mut child = TestChild::spawn(&mut command)?;
            child.wait_for(&tree.root.join("starting"))?;
            child.assert_blocked(&tree.root.join("done"))?;
            if mode == "reader" {
                // Finish a multi-file transaction while the real digest reader is blocked.
                fs::write(&node.olean_path, b"committed olean")?;
                fs::write(&node.ilean_path, b"committed ilean")?;
                fs::write(
                    tree.root.join("expected"),
                    compute_olean_artifact_set_digest_locked(&node.olean_path, current.as_ref())?,
                )?;
            }
            drop((legacy, current));
            child.finish(&tree.root.join("done"))?;
            if mode == "publisher" {
                assert_eq!(fs::read(&node.olean_path)?, b"new olean generation");
                assert_eq!(fs::read(&node.ilean_path)?, b"new ilean generation");
            }
        }
        Ok(())
    }

    #[test]
    fn test_weakening_options_all_sources_fail_closed() {
        use option_cases::*;
        let dir = make_temp_test_dir("weakening_options");
        for (cases, allowed) in [
            (ORIGINAL_OPTIONS, false),
            (RESTRICTED_OPTIONS, false),
            (GOOD_OPTIONS, true),
        ] {
            for &(name, value) in cases {
                for prefix in PREFIXES {
                    let key = format!("{prefix}{name}");
                    let arg = format!("-D{key}={value}");
                    let allowed = if allowed {
                        matches!(*prefix, "" | "weak.")
                    } else {
                        original_case_allowed(name, value, prefix)
                    };
                    assert_eq!(is_allowed_lean_arg(&arg), allowed, "{arg}");
                    assert_eq!(validate_lean_args([&arg]).is_ok(), allowed, "{arg}");
                    for format in ["lean", "toml"] {
                        for scope in SCOPES {
                            for field in FIELDS {
                                let path = dir.join(format!("lakefile.{format}"));
                                fs::write(&path, lakefile(format, scope, field, &key, value))
                                    .unwrap();
                                for root in [false, true] {
                                    let result = if format == "lean" {
                                        parse_lakefile_lean(&dir, &path, root)
                                    } else {
                                        parse_lakefile_toml(&dir, &path, root)
                                    };
                                    if allowed
                                        || (matches!(
                                            key.as_str(),
                                            "warn.sorry" | "weak.warn.sorry"
                                        ) && value == "false")
                                    {
                                        result.unwrap_or_else(|e| {
                                            panic!("{format}/{scope}/{field}/{arg}: {e:#}")
                                        });
                                    } else {
                                        let error = format!("{:#}", result.unwrap_err());
                                        assert!(
                                            error.contains(&key),
                                            "{format}/{scope}/{field}/{arg}: {error}"
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn test_parse_lakefile_lean_namespaced_static_facet() {
        let dir = make_temp_test_dir("namespaced_static_facet");
        let path = dir.join("lakefile.lean");
        fs::write(
            &path,
            r#"import Lake
open Lake DSL
package demo
lean_lib spec_cabi where
  roots := #[`Demo]
  defaultFacets := #[LeanLib.staticFacet]
"#,
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &path, true).unwrap();
        assert_eq!(pkg.libs.len(), 1);
        assert_eq!(pkg.libs[0].default_facets, vec!["LeanLib.staticFacet"]);
        fs::remove_dir_all(dir).unwrap();
    }
    const INPUT_DIR_LAKEFILE: &str = r#"import Lake
open Lake DSL
package demo
/-- Solidity read by `solidity_import`. -/
input_dir smokeSources where
  path := "Smoke"
  filter := .extension "sol"
  text := true
lean_lib Early where
  globs := #[.one `Smoke.Both]
lean_lib «Smoke» where
  globs := #[.one `Smoke.A, .one `Smoke.Shared, .one `Smoke.Both]
  needs := #[smokeSources]
lean_lib Other where
  roots := #[`Other]
lean_lib Later where
  globs := #[.one `Smoke.Shared]
"#;
    #[test]
    fn test_issue355_dependency_configuration_syntax_and_security() {
        let dir = make_temp_test_dir("issue355_config");
        let lf = dir.join("lakefile.lean");
        fs::create_dir_all(dir.join("widget/src")).unwrap();
        fs::write(dir.join("widget/package.json"), "{}").unwrap();
        fs::write(dir.join("widget/src/main.ts"), "export {}").unwrap();
        let evmyul = "import Lake\nopen Lake DSL System\npackage «evmyul» {\n  moreLeanArgs := #[\"-DautoImplicit=false\"]\n  moreServerOptions := #[⟨`autoImplicit, false⟩]\n}\ndef cloneWithCache (url : String) := do\n  if true then dbg_trace s!\"Cloning: {url}\"; pure ()\ntarget ffi.o pkg : FilePath := do\n  pure (pkg.buildDir / \"ffi.o\")\nextern_lib libleanffi pkg := do\n  discard <| IO.Process.run {cmd := \"git\", args := #[\"status\"]}\nlean_lib «EvmYul»\n";
        let widgets = "import Lake\nopen Lake DSL System\npackage proofwidgets where\ndef widgetDir : FilePath := \"widget\"\nnonrec def Lake.Package.widgetDir (pkg : Package) : FilePath :=\n  pkg.dir / widgetDir\ndef Lake.Package.runNpmCommand (pkg : Package) := do\n  pure ()\ninput_file widgetPackageJson where\n  path := widgetDir / \"package.json\"\ninput_dir widgetJsSrcs where\n  path := widgetDir / \"src\"\n  filter := .extension <| .mem #[\"ts\", \"tsx\", \"js\", \"jsx\"]\n  text := true\ntarget widgetJsAll pkg : Unit :=\n  pure ()\nlean_lib ProofWidgets where\n  needs := #[widgetJsAll]\n".to_string();
        for src in [evmyul, widgets.as_str()] {
            fs::write(&lf, src).unwrap();
            let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
            assert_eq!(pkg.libs.len(), 1);
            assert!(parse_lakefile_lean(&dir, &lf, true).is_err());
        }
        fs::write(&lf, &widgets).unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
        assert_eq!(pkg.inputs[0].path, Path::new("widget/package.json"));
        assert_eq!(pkg.inputs[1].path, Path::new("widget/src"));
        assert!(pkg.libs[0].needs.is_empty());
        assert!(pkg.libs[0].unsupported.is_some());
        assert!(pkg.unsupported.is_none());
        for bad in [
            evmyul.replace("-DautoImplicit=false", "-Ddebug.skipKernelTC=true"),
            evmyul.replace(
                "moreServerOptions := #[⟨`autoImplicit, false⟩]",
                "srcDir := \"../escape\"",
            ),
            evmyul.replace(
                "moreServerOptions := #[⟨`autoImplicit, false⟩]",
                "libName := \"x\"; moreLeanArgs := #[\"-Dwarn.sorry=false\"]",
            ),
            evmyul.replace("  if true then", "  lean_lib Hidden\n  if true then"),
            evmyul.replace("}\ndef clone", "def clone"),
            widgets.replace("needs := #[widgetJsAll]", "needs := #[missing]"),
            widgets.replace("\"widget\"", "\"../escape\""),
            widgets.replace("def widgetDir", "def LeanOption.mk := 0\ndef widgetDir"),
        ] {
            fs::write(&lf, &bad).unwrap();
            assert!(parse_lakefile_lean(&dir, &lf, false).is_err(), "{bad}");
        }
        for field in [
            "plugins := #[`evil]",
            "dynlibs := #[\"evil\"]",
            "backend := .llvm",
            "moreLeancArgs := #[\"-DEVIL\"]",
        ] {
            fs::write(
                &lf,
                evmyul.replace("moreServerOptions := #[⟨`autoImplicit, false⟩]", field),
            )
            .unwrap();
            let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
            assert!(
                pkg.unsupported.is_some() || pkg.native_unsupported.is_some(),
                "{field}"
            );
        }
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn test_parse_lakefile_lean_input_targets_and_needs() {
        let dir = make_temp_test_dir("input_targets");
        let lf = dir.join("lakefile.lean");
        fs::create_dir_all(dir.join("Smoke/sub")).unwrap();
        fs::write(dir.join("Smoke/a.sol"), "contract A {}").unwrap();
        fs::write(dir.join("Smoke/sub/b.sol"), "contract B {}").unwrap();
        fs::write(dir.join("Smoke/notes.txt"), "notes").unwrap();
        fs::write(dir.join("spec.json"), "{}").unwrap();
        // 1. `input_dir` + `.extension` filter + `needs` parse; the library records the input.
        fs::write(&lf, INPUT_DIR_LAKEFILE).unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, true).unwrap();
        let lib = |n: &str| pkg.libs.iter().find(|l| l.name == n).unwrap();
        assert_eq!(lib("Smoke").needs, vec!["smokeSources"]);
        assert!(lib("Other").needs.is_empty() && lib("Later").needs.is_empty());
        let input = &pkg.inputs[0];
        assert_eq!(
            (input.name.as_str(), input.path.as_path(), input.is_dir),
            ("smokeSources", Path::new("Smoke"), true)
        );
        assert_eq!(
            (input.extension.as_deref(), input.text),
            (Some("sol"), true)
        );
        assert_eq!(input.blake3.len(), 64);
        // Lake's own file hash of the input, for the `.trace` files written for Lake.
        assert_eq!(input.lake_hash.len(), 16);
        // 5. `input_file` with `path` (and `needs` on `lean_lib` + `lean_exe`) works too, and tracks the file.
        let file_lf = "import Lake\nopen Lake DSL\npackage demo\ninput_file spec where\n  path := \"spec.json\"\nlean_lib A where\n  needs := #[spec]\nlean_exe «my-driver» where\n  root := `Main\n  needs := #[spec]\n";
        fs::write(&lf, file_lf).unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, true).unwrap();
        assert_eq!(pkg.inputs[0].path, PathBuf::from("spec.json"));
        assert!(!pkg.inputs[0].is_dir && pkg.libs[0].needs == vec!["spec"]);
        assert_eq!(pkg.exes[0].name, "my-driver");
        assert_eq!(pkg.exes[0].needs, vec!["spec"]);
        fs::write(dir.join("spec.json"), "{\"v\":1}").unwrap();
        let edited = parse_lakefile_lean(&dir, &lf, true).unwrap();
        assert_ne!(pkg.inputs[0].blake3, edited.inputs[0].blake3);
        assert_ne!(pkg.inputs[0].lake_hash, edited.inputs[0].lake_hash);
        // The package digest deliberately does not move: it would invalidate every module of the
        // package, while only the targets that `needs` the input read it (see
        // `module_lake_input_digest`, exercised by the next test).
        assert_eq!(pkg.config_digest, edited.config_digest);
        // Non-empty `needs` on `[[lean_exe]]` in `lakefile.toml` fails closed even for dependencies.
        let toml_path = dir.join("lakefile.toml");
        fs::write(
            &toml_path,
            "name = \"demo\"\n[[lean_exe]]\nname = \"drv\"\nroot = \"Main\"\nneeds = [\"spec\"]\n",
        )
        .unwrap();
        let toml_err = parse_lakefile_toml(&dir, &toml_path, false)
            .unwrap_err()
            .to_string();
        assert!(
            toml_err.contains("Unsupported `needs` on executable `drv`")
                && toml_err.contains("fail-closed"),
            "{toml_err}"
        );
        let _ = fs::remove_file(&toml_path);
        // 4. Everything beyond declarative file inputs still fails closed.
        let base = INPUT_DIR_LAKEFILE;
        let filter = "  filter := .extension \"sol\"\n";
        for (bad, needle) in [
            (
                base.replace(filter, "  filter := .not (.extension \"sol\")\n"),
                "filter",
            ),
            (
                base.replace(filter, "  filter := fun p => p.extension == some \"sol\"\n"),
                "filter",
            ),
            (
                base.replace(
                    filter,
                    "  filter := .extension \"sol\" ||| .extension \"lean\"\n",
                ),
                "filter",
            ),
            (
                base.replace(filter, "  filter := .fileName \"a.sol\"\n"),
                "filter",
            ),
            (
                base.replace(filter, "  filter := .extension #[\"sol\", \"lean\"]\n"),
                "filter",
            ),
            (base.replace("  text := true\n", "  kind := 1\n"), "kind"),
            (
                base.replace("needs := #[smokeSources]", "needs := #[Other]"),
                "`Other`",
            ),
            (
                base.replace("needs := #[smokeSources]", "needs := #[`+Other]"),
                "needs",
            ),
            (
                base.replace("needs := #[smokeSources]", "needs := #[demo/smokeSources]"),
                "needs",
            ),
            (
                base.replace(
                    "needs := #[smokeSources]",
                    "needs := #[smokeSources:default]",
                ),
                "needs",
            ),
            (
                base.replace(
                    "  roots := #[`Other]\n",
                    "  roots := #[`Other]\n  needs := #[nope]\n",
                ),
                "`nope`",
            ),
            (
                base.replace(
                    "input_dir smokeSources where",
                    "input_dir smokeSources := {}",
                ),
                "input_dir",
            ),
            (base.replace("\"Smoke\"", "\"Missing\""), "smokeSources"),
            // A file input may not read outside its own package.
            (base.replace("\"Smoke\"", "\"/etc\""), "/etc"),
            (base.replace("\"Smoke\"", "\"../Smoke\""), "../Smoke"),
            // `needs` resolves input targets by name, so duplicates are ambiguous.
            (
                base.replace(
                    "lean_lib «Smoke» where",
                    "input_dir smokeSources where\n  path := \"Smoke\"\nlean_lib «Smoke» where",
                ),
                "Duplicate Lake input target `smokeSources`",
            ),
            (
                file_lf.replace(
                    "  path := \"spec.json\"\n",
                    "  path := \"spec.json\"\n  filter := .extension \"json\"\n",
                ),
                "filter",
            ),
            (
                file_lf.replace("needs := #[spec]", "needs := #[spec, other]"),
                "`other`",
            ),
            (
                file_lf.replace(
                    "  root := `Main\n  needs := #[spec]\n",
                    "  root := `Main\n  needs := #[spec, missingExeInput]\n",
                ),
                "executable `my-driver`",
            ),
        ] {
            fs::write(&lf, &bad).unwrap();
            let err = parse_lakefile_lean(&dir, &lf, true)
                .unwrap_err()
                .to_string();
            assert!(
                err.contains(needle) && err.contains("fail-closed"),
                "{bad}\n=> {err}"
            );
        }
        fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn test_lake_input_digest_reaches_module_and_project_keys() {
        // `compute_module_cas_key` and `compute_shard_key_with_args` fold in
        // `splitter::allowed_axioms()`, which several tests set and restore process-wide -- some
        // under `env_test_lock` (`pack::test_check_shard_http_offload_and_cache_hit`) and some
        // under `BWRAP_TEST_ENV_LOCK` (`check`, `mcp`, `zygote`). A key read between two such
        // mutations moves for a reason that has nothing to do with the inputs under test, so both
        // locks are held, `env_test_lock` first as everywhere else.
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = make_temp_test_dir("input_keys");
        fs::create_dir_all(dir.join("Smoke/sub")).unwrap();
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(dir.join("lakefile.lean"), INPUT_DIR_LAKEFILE).unwrap();
        fs::write(dir.join("Smoke/A.lean"), "def a : Nat := 1\n").unwrap();
        fs::write(dir.join("Smoke/Shared.lean"), "def s : Nat := 1\n").unwrap();
        fs::write(dir.join("Smoke/Both.lean"), "def b : Nat := 1\n").unwrap();
        fs::write(dir.join("Other.lean"), "def o : Nat := 1\n").unwrap();
        fs::write(dir.join("Smoke/a.sol"), "contract A {}").unwrap();
        fs::write(dir.join("Smoke/sub/b.sol"), "contract B {}").unwrap();
        fs::write(dir.join("Smoke/notes.txt"), "notes").unwrap();
        fs::write(dir.join("outside.sol"), "contract O {}").unwrap();
        // (module CAS keys of `Smoke.A` / `Smoke.Shared` / `Smoke.Both` / `Other`, project fold)
        let keys = || {
            let cfg = resolve_project_config(&dir).unwrap();
            let dag = build_module_dag(&cfg, &[]).unwrap();
            let key = |m: &str| compute_module_cas_key(&cfg, &dag.nodes[m], &[], false).unwrap();
            // Attribution of a module two libraries can build differs between Lake and the DAG:
            // Lake v4.31 takes the LAST such library (`Package.findModule?` =
            // `leanLibs.findSomeRev?`, which `resolve_module_in_package` mirrors) while the build
            // DAG expands globs in declaration order and so keeps the FIRST. The digest folds the
            // union over every library that can build the module, so either attribution
            // invalidates.
            let lake_target = |m: &str| {
                resolve_module_in_package(&cfg.root_pkg, true, m)
                    .unwrap()
                    .target_name
            };
            assert_eq!(dag.nodes["Smoke.A"].target_name, "Smoke");
            assert_eq!(
                (
                    dag.nodes["Smoke.Shared"].target_name.as_str(),
                    lake_target("Smoke.Shared").as_str()
                ),
                ("Smoke", "Later")
            );
            assert_eq!(
                (
                    dag.nodes["Smoke.Both"].target_name.as_str(),
                    lake_target("Smoke.Both").as_str()
                ),
                ("Early", "Smoke")
            );
            let mut h = blake3::Hasher::new();
            lake_build::update_with_lake_input_digests(&mut h, &dir).unwrap();
            (
                key("Smoke.A"),
                key("Smoke.Shared"),
                key("Smoke.Both"),
                key("Other"),
                h.finalize().to_hex().to_string(),
            )
        };
        let k0 = keys();
        // 3. Non-matching extension inside `path`, or a `.sol` outside `path`: keys unchanged.
        fs::write(dir.join("Smoke/notes.txt"), "edited notes").unwrap();
        fs::write(dir.join("outside.sol"), "contract O2 {}").unwrap();
        assert_eq!(keys(), k0);
        // 2. A matched `.sol` (nested too) changes the key of every module a `needs`-ing library
        //    can build, but not of a library that needs no input.
        fs::write(dir.join("Smoke/sub/b.sol"), "contract B2 {}").unwrap();
        let k1 = keys();
        assert!(k1.0 != k0.0 && k1.4 != k0.4);
        // Conservative on both attributions: `Smoke.Shared` is attributed to `Later` by Lake and
        // `Smoke.Both` to `Early` by the DAG, yet `Smoke` can build both, so both keys move.
        assert!(k1.1 != k0.1 && k1.2 != k0.2);
        assert_eq!(k1.3, k0.3, "`Other` needs no input, so its key is stable");
        fs::write(dir.join("Smoke/c.sol"), "contract C {}").unwrap();
        let k2 = keys();
        assert!(k2.0 != k1.0 && k2.1 != k1.1 && k2.2 != k1.2 && k2.4 != k1.4);
        assert_eq!(k2.3, k0.3);
        // A root config that declares inputs but does not resolve statically fails closed
        // instead of yielding a project key that silently drops them.
        let bad = INPUT_DIR_LAKEFILE.replace(".extension \"sol\"", ".fileName \"a.sol\"");
        fs::write(dir.join("lakefile.lean"), bad).unwrap();
        let err = lake_build::update_with_lake_input_digests(&mut blake3::Hasher::new(), &dir)
            .unwrap_err()
            .to_string();
        assert!(err.contains("declares file inputs"), "{err}");
        fs::remove_dir_all(dir).unwrap();
    }

    /// Every content-derived cache key a `check` consults must move when a matched input is edited.
    ///
    /// The per-module CAS key already did, but `check` does not always compute one: it splits the
    /// file, looks the split up by `compute_file_split_key_with_deps`, and looks each theorem up by
    /// `compute_shard_key_with_args` / `compute_fission_store_key_with_args`, all of which are
    /// derived from the `.lean` bytes and the digests of what the file *imports*. An `input_dir`
    /// file is neither, so all four were blind to it. `compute_imported_olean_interface_hashes`
    /// carries the inputs as one extra dependency entry, which is what moves all four at once --
    /// including for a file with no imports at all, where that function used to return early with
    /// an empty list.
    ///
    /// Asserted at the level of the keys rather than end to end on purpose. A theorem *shard* is
    /// elaborated from a relocated input context, where `include_str` -- the only way a proof can
    /// read a declared input -- fails outright with "cannot compute parent directory", so no shard
    /// that reads an input can be elaborated, let alone cached, and the "edit the `.sol`, get a
    /// green cached shard" shape is not reachable through this path today. What is reachable is a
    /// stale `.olean` (covered end to end by
    /// `pr_verify::tests::test_warm_build_dir_rejects_oleans_stale_against_edited_lake_input`),
    /// whose digest these same keys already depend on. Folding the inputs in here keeps that
    /// independent of the `.olean` freshness logic being right.
    #[test]
    fn test_lake_input_digest_reaches_shard_split_and_fission_keys() {
        // Drives the process-global Lake-input memo window, and the shard key below folds in
        // `splitter::allowed_axioms()`, which other tests mutate under either lock.
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let _bwrap_guard = BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = make_temp_test_dir("input_shard_keys");
        fs::create_dir_all(dir.join("Smoke")).unwrap();
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(dir.join("lakefile.lean"), INPUT_DIR_LAKEFILE).unwrap();
        fs::write(dir.join("Smoke/Shared.lean"), "def s : Nat := 1\n").unwrap();
        fs::write(dir.join("Smoke/Both.lean"), "def b : Nat := 1\n").unwrap();
        fs::write(dir.join("Other.lean"), "def o : Nat := 1\n").unwrap();
        fs::write(dir.join("Smoke/a.sol"), "contract A {}").unwrap();
        fs::write(dir.join("Smoke/notes.txt"), "notes").unwrap();
        fs::write(dir.join("outside.sol"), "contract O {}").unwrap();
        // Two sources: one with an import (the old non-empty path) and one without (the path that
        // returned an empty dependency list and so could not carry anything).
        let imports_src = "import Smoke.Shared\ntheorem t : s = 1 := by rfl\n";
        let no_imports_src = "theorem u : (1 : Nat) = 1 := by rfl\n";
        fs::write(dir.join("Smoke/A.lean"), imports_src).unwrap();

        // (dep hashes, file-split key, prefix_env_hash, shard key, fission key) for both sources.
        // Each call stands for a fresh command, so it must see the inputs on disk.
        let keys = || {
            reset_lake_inputs_tag_memo();
            [imports_src, no_imports_src].map(|src| {
                let deps = lake_build::compute_imported_olean_interface_hashes(src, &dir, None);
                let sb = blake3::hash(src.as_bytes()).to_hex().to_string();
                let split = crate::splitter::split_lean_source(src, &deps);
                let shard = split
                    .shards
                    .first()
                    .expect("both sources declare one theorem")
                    .clone();
                let shard_key = lake_build::compute_shard_key_with_args("tc", &shard, &[]);
                (
                    deps.clone(),
                    lake_build::compute_file_split_key_with_deps(&sb, &deps),
                    shard.prefix_env_hash.clone(),
                    shard_key.clone(),
                    crate::check::compute_fission_store_key_with_args(
                        "tc",
                        &shard.prefix_env_hash,
                        &shard_key,
                        &[],
                    ),
                )
            })
        };
        let k0 = keys();
        assert!(
            k0.iter()
                .all(|k| k.0.iter().any(|d| d.starts_with('\u{0}'))),
            "a workspace with inputs must carry the synthetic input entry even with no imports"
        );

        // An edit the filter excludes, or a `.sol` outside `path`, must change nothing.
        fs::write(dir.join("Smoke/notes.txt"), "edited notes").unwrap();
        fs::write(dir.join("outside.sol"), "contract O2 {}").unwrap();
        assert_eq!(keys(), k0, "an unmatched file must not move any key");

        // A matched edit must move all five, for the importing and the import-free source alike.
        fs::write(dir.join("Smoke/a.sol"), "contract AMuchLongerName {}").unwrap();
        let k1 = keys();
        for (i, (a, b)) in k0.iter().zip(k1.iter()).enumerate() {
            assert_ne!(a.0, b.0, "source {i}: dependency digests");
            assert_ne!(a.1, b.1, "source {i}: file split key");
            assert_ne!(a.2, b.2, "source {i}: prefix_env_hash");
            assert_ne!(a.3, b.3, "source {i}: theorem shard key");
            assert_ne!(a.4, b.4, "source {i}: proof fission store key");
        }
        // Restoring the bytes restores the keys: the invalidation is content-driven, not a blanket
        // "this project declares inputs, so never hit".
        fs::write(dir.join("Smoke/a.sol"), "contract A {}").unwrap();
        assert_eq!(keys(), k0);

        // A workspace that declares no inputs keeps byte-identical keys and pays nothing.
        let plain = make_temp_test_dir("no_input_shard_keys");
        fs::write(plain.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            plain.join("lakefile.toml"),
            "name = \"plain\"\n[[lean_lib]]\nname = \"P\"\nroots = [\"P\"]\n",
        )
        .unwrap();
        assert!(!workspace_may_declare_lake_inputs(&plain));
        assert_eq!(project_lake_inputs_tag(&plain), None);
        assert_eq!(
            lake_build::compute_imported_olean_interface_hashes(no_imports_src, &plain, None),
            Vec::<String>::new()
        );
        fs::remove_dir_all(plain).unwrap();
        fs::remove_dir_all(dir).unwrap();
    }

    /// A dependency package's declared inputs are read while *its* modules elaborate, so they have
    /// to reach the same guards the root package's do, and a dependency whose declared input cannot
    /// be read must fail the resolve instead of hashing to a constant.
    #[test]
    fn test_dependency_package_lake_inputs_are_folded_and_fail_closed() {
        // Drives the process-global Lake-input memo window.
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = make_temp_test_dir("dep_inputs");
        let dep_dir = dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("DepPkg")).unwrap();
        fs::create_dir_all(dep_dir.join("Data")).unwrap();
        fs::create_dir_all(dir.join("App")).unwrap();
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        fs::write(
            dir.join("lake-manifest.json"),
            r#"{"version":"1.2.0","packagesDir":".lake/packages","packages":[{"type":"path","name":"dep_pkg","dir":".lake/packages/dep_pkg","configFile":"lakefile.lean","inherited":false}],"name":"app_pkg","lakeDir":".lake","fixedToolchain":false}"#,
        )
        .unwrap();
        fs::write(dir.join("App/A.lean"), "def a : Nat := 1\n").unwrap();
        fs::write(
            dep_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage dep_pkg\ninput_dir depSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\nlean_lib DepPkg where\n  globs := #[.submodules `DepPkg]\n  needs := #[depSources]\n",
        )
        .unwrap();
        fs::write(dep_dir.join("DepPkg/Base.lean"), "def d : Nat := 1\n").unwrap();
        fs::write(dep_dir.join("Data/d.sol"), "contract D {}").unwrap();

        // (workspace digest, `build` / `ci-verify` project fold, dependency-hash tag)
        let folds = || {
            reset_lake_inputs_tag_memo();
            let cfg = resolve_project_config(&dir).unwrap();
            let mut h = blake3::Hasher::new();
            lake_build::update_with_lake_input_digests(&mut h, &dir).unwrap();
            (
                workspace_lake_inputs_digest(&cfg).unwrap(),
                h.finalize().to_hex().to_string(),
                project_lake_inputs_tag(&dir),
            )
        };
        let f0 = folds();
        assert!(
            f0.0.contains("dep_pkg/depSources") && f0.2.is_some(),
            "a dependency's inputs must appear in the workspace digest: {:?}",
            f0
        );
        fs::write(dep_dir.join("Data/d.sol"), "contract DLonger {}").unwrap();
        let f1 = folds();
        assert!(
            f1.0 != f0.0 && f1.1 != f0.1 && f1.2 != f0.2,
            "editing a dependency's input must move every workspace-wide fold"
        );

        // An unreadable dependency input is an error. It used to hash to the constant
        // `"unreadable"`, which compares equal across two different sets of bytes -- so a later
        // readable edit would have matched the recorded digest and reused the stale `.olean`.
        fs::remove_dir_all(dep_dir.join("Data")).unwrap();
        let err = resolve_project_config(&dir).unwrap_err().to_string();
        assert!(err.contains("Unreadable Lake input `depSources`"), "{err}");
        // And that unresolvable workspace fails closed rather than emitting a deterministic tag.
        reset_lake_inputs_tag_memo();
        assert!(
            try_project_lake_inputs_tag(&dir).is_err(),
            "an unresolvable workspace that declares inputs must fail closed"
        );
        let t_a = project_lake_inputs_tag(&dir);
        let t_b = project_lake_inputs_tag(&dir);
        assert!(
            t_a.is_some() && t_b.is_some() && t_a != t_b,
            "fallback tags on unresolved workspaces must be fresh nonces, never colliding: {t_a:?} vs {t_b:?}"
        );
        assert!(
            lake_build::update_with_lake_input_digests(&mut blake3::Hasher::new(), &dir).is_err(),
            "a project key must not silently drop inputs it cannot read"
        );

        // `needs` in a dependency's `lakefile.toml` is refused rather than dropped: this parser
        // reads no input declarations out of TOML, so a kept `needs` would name an input that
        // nothing hashes.
        fs::create_dir_all(dep_dir.join("Data")).unwrap();
        fs::write(dep_dir.join("Data/d.sol"), "contract D {}").unwrap();
        fs::remove_file(dep_dir.join("lakefile.lean")).unwrap();
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepPkg\"\nglobs = [\"DepPkg.+\"]\nneeds = [\"depSources\"]\n",
        )
        .unwrap();
        let err = resolve_package_config(&dep_dir, false)
            .unwrap_err()
            .to_string();
        assert!(err.contains("needs"), "{err}");
        fs::remove_dir_all(dir).unwrap();
    }

    /// A dependency's declared inputs must reach the cache keys wherever the manifest puts that
    /// dependency, not only in `.lake/packages/<name>/lakefile.{lean,toml}`.
    ///
    /// `resolve_project_config` honours four fields that relocate a package: `packagesDir`, a
    /// package's `subDir`, a `type: path` dependency's `dir`, and a `configFile` that is not
    /// `lakefile`. The cheap pre-scan that decides whether a workspace declares inputs at all is
    /// what every key path consults first, so a layout it does not know about is a dependency
    /// whose `input_dir` edit moves *nothing*: `update_with_lake_input_digests` returns before it
    /// hashes anything and `project_lake_inputs_tag` answers `None`, which is indistinguishable
    /// from "this workspace declares no inputs". `build` / `ci-verify` then hit their old action
    /// key and every content-derived shard cache answers from the old bytes.
    #[test]
    fn test_lake_inputs_follow_relocated_dependency_packages() {
        // Drives the process-global Lake-input memo window.
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        const DEP_CFG: &str = "import Lake\nopen Lake DSL\npackage dep_pkg\ninput_dir depSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\nlean_lib DepPkg where\n  globs := #[.submodules `DepPkg]\n  needs := #[depSources]\n";
        // Deliberately mentions neither `input_dir` nor `input_file`: the scan must find the
        // dependency's declaration, not the root's.
        const ROOT_CFG: &str = "import Lake\nopen Lake DSL\npackage app_pkg\n@[default_target]\nlean_lib App where\n  globs := #[.submodules `App]\n";

        let build_workspace = |tag: &str,
                               root_cfg: &str,
                               manifest: Option<&str>,
                               dep_rel: &str,
                               dep_cfg_name: &str|
         -> (PathBuf, PathBuf) {
            let dir = make_temp_test_dir(tag);
            let dep_dir = dir.join(dep_rel);
            fs::create_dir_all(dep_dir.join("DepPkg")).unwrap();
            fs::create_dir_all(dep_dir.join("Data")).unwrap();
            fs::create_dir_all(dir.join("App")).unwrap();
            fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
            fs::write(dir.join("lakefile.lean"), root_cfg).unwrap();
            if let Some(m) = manifest {
                fs::write(dir.join("lake-manifest.json"), m).unwrap();
            }
            fs::write(dir.join("App/A.lean"), "def a : Nat := 1\n").unwrap();
            fs::write(dep_dir.join(dep_cfg_name), DEP_CFG).unwrap();
            fs::write(dep_dir.join("DepPkg/Base.lean"), "def d : Nat := 1\n").unwrap();
            fs::write(dep_dir.join("Data/d.sol"), "contract D {}").unwrap();
            (dir, dep_dir)
        };
        // (project action-key fold, shard dependency-hash tag) -- the two folds a relocated
        // dependency was invisible to.
        let folds = |dir: &Path| -> (String, Option<String>) {
            reset_lake_inputs_tag_memo();
            let mut h = blake3::Hasher::new();
            lake_build::update_with_lake_input_digests(&mut h, dir).unwrap();
            (
                h.finalize().to_hex().to_string(),
                project_lake_inputs_tag(dir),
            )
        };

        for (tag, root_cfg, manifest, dep_rel, dep_cfg_name) in [
            // A `type: path` dependency pointed outside `.lake/packages` entirely, and reading a
            // `configFile` that is not `lakefile.lean`: two misses in one layout.
            (
                "reloc_path_dep",
                ROOT_CFG,
                Some(
                    r#"{"version":"1.2.0","packagesDir":".lake/packages","packages":[{"type":"path","name":"dep_pkg","dir":"vendor/dep_pkg","configFile":"dep_lakefile.lean","inherited":false}],"name":"app_pkg","lakeDir":".lake","fixedToolchain":false}"#,
                ),
                "vendor/dep_pkg",
                "dep_lakefile.lean",
            ),
            // A manifest `packagesDir` plus the package's own `subDir`.
            (
                "reloc_pkgs_dir",
                ROOT_CFG,
                Some(
                    r#"{"version":"1.2.0","packagesDir":"deps","packages":[{"type":"git","name":"dep_pkg","subDir":"sub","inherited":false}],"name":"app_pkg","lakeDir":".lake","fixedToolchain":false}"#,
                ),
                "deps/dep_pkg/sub",
                "lakefile.lean",
            ),
            // No manifest at all: the resolver enumerates the root package's `packagesDir`, which
            // only the root config knows.
            (
                "reloc_root_pkgs_dir",
                "import Lake\nopen Lake DSL\npackage app_pkg where\n  packagesDir := \"deps\"\n@[default_target]\nlean_lib App where\n  globs := #[.submodules `App]\n",
                None,
                "deps/dep_pkg",
                "lakefile.lean",
            ),
        ] {
            let (dir, dep_dir) = build_workspace(tag, root_cfg, manifest, dep_rel, dep_cfg_name);
            assert!(
                workspace_may_declare_lake_inputs(&dir),
                "{tag}: the pre-scan must find the relocated dependency's declaration"
            );
            let cfg = resolve_project_config(&dir).unwrap();
            assert!(
                workspace_lake_inputs_digest(&cfg)
                    .unwrap()
                    .contains("dep_pkg/depSources"),
                "{tag}: the relocated dependency must be adopted and its input digested"
            );
            let f0 = folds(&dir);
            assert!(
                f0.1.is_some(),
                "{tag}: a workspace with inputs must carry a shard tag"
            );
            fs::write(dep_dir.join("Data/d.sol"), "contract DMuchLongerName {}").unwrap();
            let f1 = folds(&dir);
            assert_ne!(
                f1.0, f0.0,
                "{tag}: editing the dependency's input must move the project action key"
            );
            assert_ne!(
                f1.1, f0.1,
                "{tag}: editing the dependency's input must move the shard tag"
            );
            fs::remove_dir_all(dir).unwrap();
        }

        // Negative control: widening the candidate list must not make every workspace answer
        // "may declare inputs", or the fast path this scan protects is gone.
        let (plain, _) = build_workspace(
            "reloc_no_inputs",
            ROOT_CFG,
            Some(
                r#"{"version":"1.2.0","packagesDir":"deps","packages":[],"name":"app_pkg","lakeDir":".lake","fixedToolchain":false}"#,
            ),
            "deps/unused",
            "ignored.txt",
        );
        assert!(
            !workspace_may_declare_lake_inputs(&plain),
            "a workspace whose configs name no input must still take the fast path"
        );
        reset_lake_inputs_tag_memo();
        assert_eq!(project_lake_inputs_tag(&plain), None);
        // And a manifest nobody can parse is the fail-closed answer, not the default layout.
        fs::write(plain.join("lake-manifest.json"), "{not json").unwrap();
        assert!(
            workspace_may_declare_lake_inputs(&plain),
            "an unparseable manifest leaves the dependency set unknown, so it may declare inputs"
        );
        fs::remove_dir_all(plain).unwrap();
    }

    /// The Lake-input memo must not let one request publish into another's window.
    ///
    /// `serve` runs up to 64 handler threads and each calls `reset_lake_inputs_tag_memo`. A
    /// handler that read its input bytes *before* the next handler's reset used to insert them
    /// afterwards, keyed on the project directory alone -- so the next request, whose whole reason
    /// for resetting was that the inputs may have changed, was served the previous request's
    /// digest and hit the cache against bytes that no longer existed.
    ///
    /// Exercised deterministically rather than with threads: `publish_lake_inputs_tag` is the
    /// publication half of `project_lake_inputs_tag`, so calling it with a stale window is exactly
    /// the interleaving a race would produce, without depending on one happening.
    #[test]
    fn test_lake_inputs_tag_memo_rejects_cross_request_publication() {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = make_temp_test_dir("input_tag_memo_race");
        fs::create_dir_all(dir.join("Data")).unwrap();
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\ninput_dir d where\n  path := \"Data\"\n  filter := .extension \"sol\"\n@[default_target]\nlean_lib Smoke where\n  globs := #[.submodules `Smoke]\n  needs := #[d]\n",
        )
        .unwrap();
        fs::write(dir.join("Data/a.sol"), "contract A {}").unwrap();

        // Request 1 enters, reads the inputs, and is still running.
        reset_lake_inputs_tag_memo();
        let window_1 = LAKE_INPUTS_TAG_MEMO_WINDOW.load(std::sync::atomic::Ordering::SeqCst);
        let tag_1 = project_lake_inputs_tag(&dir).expect("declared inputs produce a tag");
        // The input changes and request 2 opens its own window.
        fs::write(dir.join("Data/a.sol"), "contract AMuchLongerName {}").unwrap();
        reset_lake_inputs_tag_memo();
        // Request 1 now tries to publish what it read before that reset.
        assert!(
            !publish_lake_inputs_tag(&dir, window_1, &Some(tag_1.clone())),
            "a superseded window must not be able to publish into the current one"
        );
        let tag_2 = project_lake_inputs_tag(&dir).expect("still declares inputs");
        assert_ne!(
            tag_1, tag_2,
            "request 2 must read the new bytes, not request 1's digest"
        );

        // The memo is still a memo: a publication from the *current* window is accepted and read
        // back, so the test above is not just observing a disabled cache.
        let window_2 = LAKE_INPUTS_TAG_MEMO_WINDOW.load(std::sync::atomic::Ordering::SeqCst);
        let sentinel = Some("\u{0}lake-inputs:sentinel".to_string());
        assert!(
            publish_lake_inputs_tag(&dir, window_2, &sentinel),
            "the current window must be able to publish"
        );
        assert_eq!(
            project_lake_inputs_tag(&dir),
            sentinel,
            "a same-window entry must be served from the memo"
        );

        // Concurrent handlers resetting and reading at once must stay consistent: every tag any
        // thread observes has to be one of the two digests the two file contents can produce,
        // never a mix and never a value from a window that had already ended.
        reset_lake_inputs_tag_memo();
        fs::write(dir.join("Data/a.sol"), "contract A {}").unwrap();
        let legal = {
            reset_lake_inputs_tag_memo();
            let a = project_lake_inputs_tag(&dir).unwrap();
            fs::write(dir.join("Data/a.sol"), "contract AMuchLongerName {}").unwrap();
            reset_lake_inputs_tag_memo();
            let b = project_lake_inputs_tag(&dir).unwrap();
            [a, b]
        };
        let shared_dir = dir.clone();
        let handles: Vec<_> = (0..8)
            .map(|_| {
                let d = shared_dir.clone();
                let legal = legal.clone();
                std::thread::spawn(move || {
                    for _ in 0..8 {
                        reset_lake_inputs_tag_memo();
                        let t = project_lake_inputs_tag(&d).expect("declared inputs");
                        assert!(legal.contains(&t), "observed an impossible tag: {t}");
                    }
                })
            })
            .collect();
        for (i, h) in handles.into_iter().enumerate() {
            h.join()
                .unwrap_or_else(|_| panic!("handler thread {i} panicked"));
        }
        fs::remove_dir_all(dir).unwrap();
    }

    /// An unknown field, or a `filter` this parser does not recognise, on a *dependency's*
    /// `input_dir` must fail closed instead of being silently dropped.
    ///
    /// The root package has always failed closed here. A dependency's fell through a bare
    /// `_ => {}`, so the resolve reported a clean config and a digest derived from whatever set of
    /// files *this* parser happened to select -- while the field that was ignored is precisely the
    /// one that decides which files Lake reads. Routing it through `unsupported_lake_field` puts it
    /// on the same footing as every other dependency field: recorded, promoted onto the package so
    /// `build_module_dag` refuses to publish a Lake trace for any of its modules, and spelled into
    /// the input digests so no key can collide with one from a declaration turbo-lean understood.
    #[test]
    fn test_dependency_input_unsupported_field_fails_closed() {
        // Drives the process-global Lake-input memo window.
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = make_temp_test_dir("dep_input_unsupported");
        let dep_dir = dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("Data")).unwrap();
        fs::create_dir_all(dep_dir.join("DepPkg")).unwrap();
        fs::create_dir_all(dir.join("App")).unwrap();
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        fs::write(
            dir.join("lake-manifest.json"),
            r#"{"version":"1.2.0","packagesDir":".lake/packages","packages":[{"type":"path","name":"dep_pkg","dir":".lake/packages/dep_pkg","configFile":"lakefile.lean","inherited":false}],"name":"app_pkg","lakeDir":".lake","fixedToolchain":false}"#,
        )
        .unwrap();
        fs::write(dir.join("App/A.lean"), "def a : Nat := 1\n").unwrap();
        fs::write(dep_dir.join("DepPkg/Base.lean"), "def d : Nat := 1\n").unwrap();
        fs::write(dep_dir.join("Data/d.sol"), "contract D {}").unwrap();
        let write_cfg = |extra: &str| {
            fs::write(
                dep_dir.join("lakefile.lean"),
                format!(
                    "import Lake\nopen Lake DSL\npackage dep_pkg\ninput_dir depSources where\n  path := \"Data\"\n{extra}lean_lib DepPkg where\n  globs := #[.submodules `DepPkg]\n  needs := #[depSources]\n"
                ),
            )
            .unwrap();
        };
        let workspace_digest = || {
            workspace_lake_inputs_digest(&resolve_project_config(&dir).expect("workspace resolves"))
        };

        // The understood baseline: a recognised filter leaves nothing unsupported, and the digest
        // is the input's content hash.
        write_cfg("  filter := .extension \"sol\"\n");
        let ok = resolve_package_config(&dep_dir, false).unwrap();
        assert!(
            ok.inputs[0].unsupported.is_none() && ok.unsupported.is_none(),
            "a recognised `filter` must stay supported"
        );
        let ok_digest = workspace_digest().expect("supported input digests cleanly");
        assert!(
            ok_digest.contains(&ok.inputs[0].blake3) && !ok_digest.contains("unsupported:"),
            "{ok_digest}"
        );

        for extra in [
            // An unknown field.
            "  followSymlinks := true\n",
            // A `filter` that is not `.extension "<ext>"`. Keeping every file of the directory is a
            // superset of what Lake selects, but it is not the same set, and the next filter form
            // Lake grows may just as easily be a narrower one that reads files this parser skips.
            "  filter := .name \"d.sol\"\n",
        ] {
            write_cfg(extra);
            // The root package still fails the parse outright.
            let err = resolve_package_config(&dep_dir, true)
                .unwrap_err()
                .to_string();
            assert!(
                err.contains("Unsupported `input_dir` field")
                    && err.contains("fail-closed static Lake config gate"),
                "{extra}: {err}"
            );
            // A dependency records it, and it is promoted onto the package, which is the slot
            // `build_module_dag` checks before it builds any of the package's modules.
            let dep = resolve_package_config(&dep_dir, false).unwrap();
            let why = dep.inputs[0]
                .unsupported
                .clone()
                .unwrap_or_else(|| panic!("{extra}: a dependency's input field must be recorded"));
            assert!(
                why.contains("Unsupported `input_dir` field"),
                "{extra}: {why}"
            );
            assert_eq!(
                dep.unsupported.as_deref(),
                Some(why.as_str()),
                "{extra}: an unread input must make every module of the package fail closed"
            );
            // Both `workspace_lake_inputs_digest` and `try_project_lake_inputs_tag` must fail
            // closed (`Err`) rather than emitting a constant placeholder string that would compare
            // equal across edits to the underlying input bytes.
            let digest_err = workspace_digest()
                .expect_err("unsupported dependency input must fail closed")
                .to_string();
            assert!(
                digest_err.contains("Unsupported Lake input `dep_pkg/depSources`"),
                "{extra}: {digest_err}"
            );
            reset_lake_inputs_tag_memo();
            let tag_err = try_project_lake_inputs_tag(&dir)
                .expect_err("try_project_lake_inputs_tag must fail closed on unsupported dep input")
                .to_string();
            assert!(
                tag_err.contains("Unsupported Lake input `dep_pkg/depSources`"),
                "{extra}: {tag_err}"
            );
            let fallback_1 = project_lake_inputs_tag(&dir);
            fs::write(dep_dir.join("Data/other.txt"), "edited bytes").unwrap();
            reset_lake_inputs_tag_memo();
            let fallback_2 = project_lake_inputs_tag(&dir);
            assert!(
                fallback_1.is_some() && fallback_2.is_some() && fallback_1 != fallback_2,
                "{extra}: non-Result fallback tags must never collide across edits: {fallback_1:?} vs {fallback_2:?}"
            );
            let _ = fs::remove_file(dep_dir.join("Data/other.txt"));
        }
        fs::remove_dir_all(dir).unwrap();
    }

    /// An input path may only name plain files inside the package.
    ///
    /// Lake follows a symlink out of the checkout and quietly skips a FIFO. Both would let a
    /// declared "input" stand for bytes that no diff of the repository reports and that no digest
    /// can reproduce -- and `fs::read` on a FIFO blocks the build forever. Both are refused here,
    /// on the host, before any sandbox is entered.
    #[test]
    #[cfg(unix)]
    fn test_lake_input_rejects_escaping_symlinks_and_non_regular_files() {
        let dir = make_temp_test_dir("input_symlink");
        let proj = dir.join("proj");
        fs::create_dir_all(proj.join("Data/sub")).unwrap();
        fs::write(dir.join("outside.sol"), "contract Outside {}").unwrap();
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            proj.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[smokeSources]\n",
        )
        .unwrap();
        fs::write(proj.join("Data/a.sol"), "contract A {}").unwrap();
        let resolve = || resolve_package_config(&proj, true);
        let digest = || resolve().unwrap().inputs[0].blake3.clone();
        let base = digest();

        // 1. A symlink to a file inside the package stays allowed, and its bytes are hashed.
        fs::write(proj.join("Data/sub/real.sol"), "contract Real {}").unwrap();
        std::os::unix::fs::symlink("sub/real.sol", proj.join("Data/link_in.sol")).unwrap();
        let with_inside_link = digest();
        assert_ne!(
            with_inside_link, base,
            "a contained symlink must still contribute its bytes"
        );

        // 2. A symlink out of the package root fails closed. Lake would follow it and hash bytes
        // that `git diff` cannot report, so pr-verify would call a changed input unchanged.
        std::os::unix::fs::symlink(dir.join("outside.sol"), proj.join("Data/escape.sol")).unwrap();
        let err = resolve().unwrap_err().to_string();
        assert!(
            err.contains("outside the package root") && err.contains("escape.sol"),
            "{err}"
        );
        fs::remove_file(proj.join("Data/escape.sol")).unwrap();
        assert_eq!(
            digest(),
            with_inside_link,
            "removing it restores the digest"
        );

        // 3. A dangling symlink fails closed too, rather than being skipped.
        std::os::unix::fs::symlink("nowhere.sol", proj.join("Data/dangling.sol")).unwrap();
        assert!(resolve().is_err(), "a dangling input symlink must fail");
        fs::remove_file(proj.join("Data/dangling.sol")).unwrap();

        // 3b. A symlinked *directory* escapes just as effectively, and this is the case a
        // leaf-only check misses: `follow_links` descends through it, so the entry it yields is an
        // ordinary file and its own metadata says nothing about the escape.
        fs::create_dir_all(dir.join("outside_dir")).unwrap();
        fs::write(dir.join("outside_dir/x.sol"), "contract X {}").unwrap();
        std::os::unix::fs::symlink(dir.join("outside_dir"), proj.join("Data/linked_dir")).unwrap();
        let err = resolve().unwrap_err().to_string();
        assert!(
            err.contains("outside the package root") && err.contains("x.sol"),
            "{err}"
        );
        fs::remove_file(proj.join("Data/linked_dir")).unwrap();
        assert_eq!(digest(), with_inside_link);

        // 4. A non-regular file matching the filter fails closed. Reading it would block forever.
        let fifo = proj.join("Data/pipe.sol");
        assert!(
            std::process::Command::new("mkfifo")
                .arg(&fifo)
                .status()
                .is_ok_and(|s| s.success()),
            "mkfifo must be available to exercise the non-regular-file gate"
        );
        let err = resolve().unwrap_err().to_string();
        assert!(
            err.contains("is not a regular file") && err.contains("pipe.sol"),
            "{err}"
        );
        // A non-regular file the filter excludes is irrelevant and must not break the resolve.
        fs::rename(&fifo, proj.join("Data/pipe.txt")).unwrap();
        assert_eq!(digest(), with_inside_link);

        // 5. The same two gates apply to an `input_file` naming the path directly.
        fs::write(
            proj.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\ninput_file specFile where\n  path := \"spec.json\"\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[specFile]\n",
        )
        .unwrap();
        std::os::unix::fs::symlink(dir.join("outside.sol"), proj.join("spec.json")).unwrap();
        let err = resolve().unwrap_err().to_string();
        assert!(err.contains("outside the package root"), "{err}");
        fs::remove_file(proj.join("spec.json")).unwrap();
        assert!(std::process::Command::new("mkfifo")
            .arg(proj.join("spec.json"))
            .status()
            .is_ok_and(|s| s.success()));
        let err = resolve().unwrap_err().to_string();
        assert!(err.contains("is not a regular file"), "{err}");
        fs::remove_dir_all(dir).unwrap();
    }

    /// The per-command memo must not outlive its command: the whole point of folding the inputs
    /// into the keys is that an edit is seen, and a `serve` / MCP process handles many edits.
    #[test]
    fn test_lake_inputs_tag_memo_is_reset_between_commands() {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = make_temp_test_dir("input_tag_memo");
        fs::create_dir_all(dir.join("Data")).unwrap();
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\ninput_dir d where\n  path := \"Data\"\n  filter := .extension \"sol\"\n@[default_target]\nlean_lib Smoke where\n  globs := #[.submodules `Smoke]\n  needs := #[d]\n",
        )
        .unwrap();
        fs::write(dir.join("Data/a.sol"), "contract A {}").unwrap();
        reset_lake_inputs_tag_memo();
        let t0 = project_lake_inputs_tag(&dir).expect("declared inputs produce a tag");
        // Within one command the digest is stable even though the bytes moved: that is the memo,
        // and it is exactly the window `reset_lake_inputs_tag_memo` exists to close.
        fs::write(dir.join("Data/a.sol"), "contract AMuchLongerName {}").unwrap();
        assert_eq!(project_lake_inputs_tag(&dir).as_deref(), Some(t0.as_str()));
        // Across the boundary the edit must be visible.
        reset_lake_inputs_tag_memo();
        let t1 = project_lake_inputs_tag(&dir).expect("still declares inputs");
        assert_ne!(t0, t1, "a reset command window must re-read the inputs");
        reset_lake_inputs_tag_memo();
        fs::write(dir.join("Data/a.sol"), "contract A {}").unwrap();
        assert_eq!(project_lake_inputs_tag(&dir).as_deref(), Some(t0.as_str()));
        fs::remove_dir_all(dir).unwrap();
    }

    /// Sorting the selected files by raw bytes agrees with Lake's `String` order on valid UTF-8 and,
    /// unlike `to_string_lossy`, cannot collapse two distinct paths onto one sort key.
    #[test]
    fn test_lake_input_dir_file_order_is_byte_sorted() {
        let dir = make_temp_test_dir("input_order");
        fs::create_dir_all(dir.join("Data")).unwrap();
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\ninput_dir d where\n  path := \"Data\"\n  filter := .extension \"sol\"\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[d]\n",
        )
        .unwrap();
        // `Z` (0x5A) sorts before `a` (0x61) by byte, as it does by Lean `Char` code point.
        for (name, body) in [("Z.sol", "z"), ("a.sol", "a")] {
            fs::write(dir.join("Data").join(name), body).unwrap();
        }
        let forward = resolve_package_config(&dir, true).unwrap().inputs[0]
            .blake3
            .clone();
        // Rewriting the files in the opposite creation order must not change the digest: the order
        // comes from the paths, not from the directory iteration order.
        for (name, body) in [("a.sol", "a"), ("Z.sol", "z")] {
            fs::write(dir.join("Data").join(name), body).unwrap();
        }
        assert_eq!(
            resolve_package_config(&dir, true).unwrap().inputs[0].blake3,
            forward
        );
        // Swapping the two bodies must change it, which is what proves the order is load-bearing.
        for (name, body) in [("Z.sol", "a"), ("a.sol", "z")] {
            fs::write(dir.join("Data").join(name), body).unwrap();
        }
        assert_ne!(
            resolve_package_config(&dir, true).unwrap().inputs[0].blake3,
            forward
        );
        fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn test_lake_input_dir_needs_trace_differential_against_lake() {
        let dir = make_temp_test_dir("input_trace");
        let proj = dir.join("proj");
        fs::create_dir_all(proj.join("Smoke")).unwrap();
        fs::create_dir_all(proj.join("Data/sub")).unwrap();
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            proj.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n  text := true\ninput_file specFile where\n  path := \"spec.json\"\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[smokeSources, specFile]\nlean_exe drv where\n  root := `Driver\n  needs := #[smokeSources, specFile]\n",
        )
        .unwrap();
        fs::write(proj.join("Smoke/A.lean"), "def a : Nat := 1\n").unwrap();
        fs::write(
            proj.join("Driver.lean"),
            "def main : IO Unit := IO.println \"ok\"\n",
        )
        .unwrap();
        fs::write(proj.join("Data/a.sol"), "contract A {}\n").unwrap();
        fs::write(proj.join("Data/sub/b.sol"), "contract B {}\n").unwrap();
        fs::write(proj.join("Data/notes.txt"), "ignored\n").unwrap();
        fs::write(proj.join("spec.json"), "{\"v\":1}\n").unwrap();
        let lake_bin = match resolve_project_config(&proj) {
            Ok(cfg) => cfg.lean_bin.with_file_name("lake"),
            Err(_) => return,
        };
        if !lake_bin.is_file() {
            return;
        }
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        let trace_path = proj.join(".lake/build/lib/lean/Smoke/A.trace");
        let exe_trace_path = proj.join(".lake/build/lib/lean/Driver.trace");
        let dep_hash = |p: &Path| -> serde_json::Value {
            serde_json::from_slice::<serde_json::Value>(&fs::read(p).unwrap()).unwrap()["depHash"]
                .clone()
        };
        build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke:c".to_string(), "@demo/drv:default".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        let native_dep_hash = dep_hash(&trace_path);
        let native_exe_dep_hash = dep_hash(&exe_trace_path);
        assert!(
            Command::new(&lake_bin)
                .args(["build", "--no-build", "Smoke", "+Driver:olean"])
                .current_dir(&proj)
                .status()
                .unwrap()
                .success(),
            "`lake build --no-build` must accept artifacts of both `lean_lib` and `lean_exe` with `needs` inputs"
        );
        fs::remove_dir_all(proj.join(".lake/build")).unwrap();
        assert!(Command::new(&lake_bin)
            .args(["build", "Smoke", "@demo/drv:exe"])
            .current_dir(&proj)
            .status()
            .unwrap()
            .success());
        assert_eq!(
            native_dep_hash,
            dep_hash(&trace_path),
            "native vs lake Smoke.A.trace depHash must match with `input_dir` / `input_file` needs"
        );
        assert_eq!(
            native_exe_dep_hash,
            dep_hash(&exe_trace_path),
            "native vs lake Driver.trace depHash must match for `lean_exe` with `needs`"
        );
        // A changed matched input moves Lake's dep hash too, so the two stay in step.
        fs::write(proj.join("Data/sub/b.sol"), "contract B2 {}\n").unwrap();
        fs::remove_dir_all(proj.join(".lake/build")).unwrap();
        build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke:c".to_string(), "@demo/drv:default".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        let edited_dep_hash = dep_hash(&trace_path);
        let edited_exe_dep_hash = dep_hash(&exe_trace_path);
        assert_ne!(native_dep_hash, edited_dep_hash);
        assert_ne!(native_exe_dep_hash, edited_exe_dep_hash);
        assert!(Command::new(&lake_bin)
            .args(["build", "--no-build", "Smoke", "+Driver:olean"])
            .current_dir(&proj)
            .status()
            .unwrap()
            .success());
        fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn test_parse_header_imports_comments_prelude_and_module_flags() {
        let src = "\
/-
  Multi-line block comment with fake import:
  import Fake.Blocked
  /- nested comment import Fake.Nested -/
-/
module
prelude
-- inline comment import Fake.Inline
public import Mathlib.Logic.Basic
import all Demo.Internal -- space-separated
meta
import
Demo.MetaMod
public import Demo.Shared
import all Demo.Shared
import Demo.A
import «Demo».«B»
@[expose] public section
namespace Demo
@[inline, export demo_c_symbol]
public def f (x : Nat) : Nat := x
";
        let info = parse_header_info(src);
        assert!(info.header_error.is_none());
        assert!(info.is_module);
        assert!(info.has_prelude);
        assert!(info.has_c_export);
        assert_eq!(
            info.imports,
            vec![
                "Mathlib.Logic.Basic".to_string(),
                "Demo.Internal".to_string(),
                "Demo.MetaMod".to_string(),
                "Demo.Shared".to_string(),
                "Demo.A".to_string(),
                "Demo.B".to_string()
            ]
        );
        let shared_specs: Vec<&ParsedImport> = info
            .import_specs
            .iter()
            .filter(|s| s.module == "Demo.Shared")
            .collect();
        assert_eq!(shared_specs.len(), 2);
        assert!(shared_specs[0].is_exported && !shared_specs[0].import_all);
        assert!(!shared_specs[1].is_exported && shared_specs[1].import_all);
    }

    #[test]
    fn test_parse_header_info_differential_against_lean_deps_json() {
        let dir = make_temp_test_dir("diff_header_deps_json");
        let (lean_bin, _, _, _) = resolve_toolchain_compiler(&dir, "leanprover/lean4:v4.35.0")
            .expect("resolve Lean v4.35.0 binary");
        let cases: &[(&str, &str)] = &[
            ("plain_default", "import Std.Data.HashMap\ndef x : Nat := 1\n"),
            ("module_no_prelude", "module\npublic import Std\nmeta import Lean.Elab\nimport all Init.Data.Array\npublic section\n"),
            ("module_prelude_dup_flags", "module\nprelude\npublic import Foo.Bar\nimport all Foo.Bar\nmeta import Foo.Bar\n"),
            ("guillemets_and_multiline", "module\n  /- nested /- block -/ -/\n  prelude\n  public\n  meta\n  import «Foo».«Bar Baz».Qux'!\n"),
            ("stops_at_doc_comment", "/-- module doc stops header -/\nimport IgnoredAfterDoc\n"),
            ("stops_at_semicolon", "import Foo.A; import IgnoredAfterSemi\n"),
            ("concat_module_prefix", "moduleFoo\n"),
            ("char_quote_in_body", "import Foo.A\ndef quoteChar : Char := '\"' -- import Fake.InComment\n"),
            ("stops_at_tab_after_import_kw", "import\tFoo.A\n"),
            ("err_tab_after_all", "module\nprelude\nimport all\tFoo.A\n"),
            ("err_modifier_without_module", "public import Foo.A\n"),
            ("err_unterminated_comment", "/- unterminated\nimport Foo.A\n"),
            ("err_missing_ident", "import -- nothing\n"),
            ("err_public_import_all", "module\nprelude\npublic import all Foo.A\n"),
        ];

        for (name, content) in cases {
            let file_path = dir.join(format!("{}.lean", name));
            fs::write(&file_path, content).unwrap();
            let info = parse_header_info(content);
            let out = Command::new(&lean_bin)
                .arg("--deps-json")
                .arg(&file_path)
                .output()
                .unwrap();
            assert!(out.status.success(), "lean --deps-json failed for {}", name);
            let parsed_json: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
            let entry = &parsed_json["imports"][0];
            let lean_errs = entry["errors"].as_array().cloned().unwrap_or_default();
            if *name == "err_public_import_all" {
                // `ParseImportsFast` defers `public import all` rejection to `Lean.Parser.Module.parseHeader`
                assert!(
                    info.header_error.is_some(),
                    "expected header_error for {}",
                    name
                );
                continue;
            }
            if !lean_errs.is_empty() {
                assert!(
                    info.header_error.is_some(),
                    "expected header_error for {} matching lean --deps-json errors {:?}",
                    name,
                    lean_errs
                );
            } else {
                assert!(
                    info.header_error.is_none(),
                    "unexpected header_error {:?} for {}",
                    info.header_error,
                    name
                );
                let res = &entry["result"];
                assert_eq!(
                    info.is_module,
                    res["isModule"].as_bool().unwrap(),
                    "isModule mismatch for {}",
                    name
                );
                let expected_specs: Vec<ParsedImport> = res["imports"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|imp| ParsedImport {
                        module: imp["module"].as_str().unwrap().to_string(),
                        is_exported: imp["isExported"].as_bool().unwrap(),
                        is_meta: imp["isMeta"].as_bool().unwrap(),
                        import_all: imp["importAll"].as_bool().unwrap(),
                    })
                    .collect();
                assert_eq!(
                    info.import_specs, expected_specs,
                    "import_specs mismatch vs lean --deps-json for {}",
                    name
                );
            }
        }
        let _ = fs::remove_dir_all(dir);
    }
    #[test]
    fn test_parse_lakefile_toml_and_lakefile_lean_static_configs() {
        let dir = make_temp_test_dir("cfg_parse");
        let toml_content = r#"
name = "demo-toml-pkg"
version = "0.1.0"
srcDir = "src"
defaultTargets = ["DemoLib"]
moreLeanArgs = ["-DwarningAsError=false"]
weakLeanArgs = ["-Dpp.unicode.fun=true"]
precompileModules = false
[leanOptions]
autoImplicit = false
"relaxedAutoImplicit" = false
[[require]]
name = "dep-a"
path = "../dep-a"
[[lean_lib]]
name = "DemoLib"
roots = ["Demo"]
globs = ["Demo.*", "Extra.+"]
moreLeanArgs = ["-j1"]
[[lean_exe]]
name = "demo-runner"
root = "Demo.Main"
supportInterpreter = true
"#;
        let toml_path = dir.join("lakefile.toml");
        fs::write(&toml_path, toml_content).unwrap();
        let pkg_toml = parse_lakefile_toml(&dir, &toml_path, true).unwrap();
        assert_eq!(pkg_toml.name, "demo-toml-pkg");
        assert_eq!(pkg_toml.src_dir, PathBuf::from("src"));
        assert_eq!(pkg_toml.default_targets, vec!["DemoLib".to_string()]);
        assert_eq!(
            pkg_toml
                .lean_options
                .get(&LeanName::from_str_to_name("autoImplicit").unwrap()),
            Some(&LeanOptionValue::Bool(false))
        );
        assert_eq!(pkg_toml.libs.len(), 1);
        assert_eq!(
            pkg_toml.libs[0].globs,
            vec![
                GlobSpec::AndSubmodules("Demo".to_string()),
                GlobSpec::Submodules("Extra".to_string()),
            ]
        );
        assert_eq!(pkg_toml.exes.len(), 1);
        assert_eq!(pkg_toml.exes[0].root, "Demo.Main");
        assert!(pkg_toml.exes[0].support_interpreter);
        let lean_content = r#"
import Lake
open Lake DSL
package «demo-lean-pkg» where
  srcDir := "lean_src"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  moreLeanArgs := #["-DwarningAsError=false"]
@[default_target]
lean_lib «DemoLean» where
  roots := #[`DemoLean]
  globs := #[.submodules `DemoLean, .one `DemoLeanRoot]
lean_exe «demo-exe» where
  root := `DemoLean.Main
  supportInterpreter := true
"#;
        let lean_path = dir.join("lakefile.lean");
        fs::write(&lean_path, lean_content).unwrap();
        let pkg_lean = parse_lakefile_lean(&dir, &lean_path, true).unwrap();
        assert_eq!(pkg_lean.name, "demo-lean-pkg");
        assert_eq!(pkg_lean.src_dir, PathBuf::from("lean_src"));
        assert_eq!(pkg_lean.default_targets, vec!["DemoLean".to_string()]);
        assert_eq!(
            pkg_lean
                .lean_options
                .get(&LeanName::from_str_to_name("autoImplicit").unwrap()),
            Some(&LeanOptionValue::Bool(false))
        );
        assert_eq!(
            pkg_lean.libs[0].globs,
            vec![
                GlobSpec::Submodules("DemoLean".to_string()),
                GlobSpec::One("DemoLeanRoot".to_string()),
            ]
        );
        let _ = fs::remove_dir_all(&dir);
    }
    #[test]
    fn test_computed_lean_options_mathlib_lakefile() {
        // Mathlib @ 0df444a3 binds `leanOptions` through `abbrev`s built with `++` and a
        // `weak.`-prefix `map`, which the literal-only parser used to reject.
        let dir = make_temp_test_dir("mathlib_opts");
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            include_str!("../tests/fixtures/mathlib-0df444a3-lakefile.lean"),
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
        let lib = |name: &str| {
            pkg.libs
                .iter()
                .find(|l| l.name == name)
                .unwrap_or_else(|| panic!("missing lean_lib {name}"))
                .lean_options
                .clone()
        };
        let expected: LeanOptionsMap = [
            ("pp.unicode.fun", LeanOptionValue::Bool(true)),
            ("autoImplicit", LeanOptionValue::Bool(false)),
            ("maxSynthPendingDepth", LeanOptionValue::Nat(3)),
            (
                "weak.linter.mathlibStandardSet",
                LeanOptionValue::Bool(true),
            ),
            ("weak.linter.style.header", LeanOptionValue::Bool(true)),
            ("weak.linter.checkInitImports", LeanOptionValue::Bool(true)),
            (
                "weak.linter.allScriptsDocumented",
                LeanOptionValue::Bool(true),
            ),
            ("weak.linter.pythonStyle", LeanOptionValue::Bool(true)),
            ("weak.linter.style.longFile", LeanOptionValue::Nat(1500)),
        ]
        .into_iter()
        .map(|(k, v)| (LeanName::from_str_to_name(k).unwrap(), v))
        .collect();
        assert_eq!(lib("Mathlib"), expected);
        assert_eq!(lib("Archive"), expected);
        assert_eq!(lib("Counterexamples"), expected);
        assert_eq!(
            lib("MathlibTest"),
            BTreeMap::from([(
                LeanName::from_str_to_name("pp.mvars.anonymous").unwrap(),
                LeanOptionValue::Bool(false)
            )])
        );
        // turbo-lean's own proofs package (CI builds it) uses `«»` names, including on
        // `require`; it must keep parsing.
        let own = dir.join("own-lakefile.lean");
        fs::write(&own, include_str!("../../../lean/lakefile.lean")).unwrap();
        let own_pkg = parse_lakefile_lean(&dir, &own, true).unwrap();
        let own_src = include_str!("../../../lean/lakefile.lean");
        let count = |kw: &str| own_src.lines().filter(|l| l.starts_with(kw)).count();
        assert_eq!(
            (own_pkg.libs.len(), own_pkg.exes.len()),
            (count("lean_lib "), count("lean_exe "))
        );
        // `Cache.+` / `MathlibTest.+` are submodule globs, not modules named `+`.
        let globs = |name: &str| {
            pkg.libs
                .iter()
                .find(|l| l.name == name)
                .unwrap()
                .globs
                .clone()
        };
        assert_eq!(
            globs("Cache"),
            vec![GlobSpec::Submodules("Cache".to_string())]
        );
        assert_eq!(
            globs("MathlibTest"),
            vec![GlobSpec::Submodules("MathlibTest".to_string())]
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_computed_lean_options_fail_closed() {
        let defs = collect_lakefile_abbrevs(
            "abbrev a := b\nabbrev b := a\nabbrev xs : Array LeanOption := #[⟨`x, true⟩]\n",
        );
        // Cyclic identifiers are detected instead of looping.
        let err = resolve_lean_options_expr("a", &defs, usize::MAX)
            .unwrap_err()
            .to_string();
        // Under sequential elaboration a cycle is a forward reference.
        assert!(
            err.contains("Cyclic") || err.contains("before its declaration"),
            "{err}"
        );
        // Self-referential appends and wide diamonds resolve in linear time (memoised).
        let selfref = collect_lakefile_abbrevs(
            "abbrev a := a ++ a ++ a ++ a
",
        );
        assert!(resolve_lean_options_expr("a", &selfref, usize::MAX).is_err());
        let wide = |n: usize| {
            (0..32)
                .map(|_| format!("a{n}"))
                .collect::<Vec<_>>()
                .join(" ++ ")
        };
        let mut src = "abbrev a0 : Array LeanOption := #[⟨`x, true⟩]
"
        .to_string();
        for n in 1..=8 {
            src.push_str(&format!(
                "abbrev a{n} : Array LeanOption := {}
",
                wide(n - 1)
            ));
        }
        let diamond = collect_lakefile_abbrevs(&src);
        let start = std::time::Instant::now();
        assert_eq!(
            resolve_lean_options_expr("a8", &diamond, usize::MAX).unwrap(),
            BTreeMap::from([(
                LeanName::from_str_to_name("x").unwrap(),
                LeanOptionValue::Bool(true)
            )])
        );
        assert!(start.elapsed() < std::time::Duration::from_secs(2));
        // Unknown identifiers and other computations are still rejected.
        for expr in [
            "missing",
            "xs.filter fun s ↦ true",
            "xs.map fun s ↦ { s with name := `strong ++ s.name }",
            "xs.map fun s ↦ { s with value := true }",
            "if cond then xs else #[]",
            // Values must be literals, not identifiers passed through as `-Dk=ident`.
            "#[⟨`maxHeartbeats, someIdent⟩]",
            "#[⟨`x, .ofBool 3⟩]",
            "#[⟨`x, .ofString bare⟩]",
            "#[LeanOption.mk `x someIdent]",
        ] {
            let err = resolve_lean_options_expr(expr, &defs, usize::MAX)
                .unwrap_err()
                .to_string();
            assert!(err.contains("Unsupported"), "{expr}: {err}");
        }
        // Literal, append, parenthesised and weak-prefix forms resolve; later entries win.
        let got = resolve_lean_options_expr(
            "(xs) ++ #[⟨`x, false⟩, ⟨`n, .ofNat 7⟩, ⟨`s, .ofString \"hi\"⟩] ++ xs.map fun s => { s with name := `weak ++ s.name }",
            &defs,
            usize::MAX,
        )
        .unwrap();
        assert_eq!(
            got,
            BTreeMap::from([
                (
                    LeanName::from_str_to_name("x").unwrap(),
                    LeanOptionValue::Bool(false)
                ),
                (
                    LeanName::from_str_to_name("n").unwrap(),
                    LeanOptionValue::Nat(7)
                ),
                (
                    LeanName::from_str_to_name("s").unwrap(),
                    LeanOptionValue::Str("hi".to_string())
                ),
                (
                    LeanName::from_str_to_name("weak.x").unwrap(),
                    LeanOptionValue::Bool(true)
                ),
            ])
        );
    }

    #[test]
    fn test_lakefile_toml_lean_options_fail_closed() {
        // Multi-line TOML strings, string values that setup.json / CLI would re-read as a
        // bool or a number, and quoted dotted keys (`"weak.linter.myStr"` -> single Str segment `«weak.linter.myStr»`).
        let dir = make_temp_test_dir("toml_opts");
        let tf = dir.join("lakefile.toml");
        let parse = |src: &str| {
            fs::write(&tf, src).unwrap();
            parse_lakefile_toml(&dir, &tf, false)
        };
        for bad in [
            "name = \"demo\"\nleanOptions = { autoImplicit = false }\ndescription = \"\"\"\nleanOptions = { autoImplicit = true }\n# \"\"\"\n[[lean_lib]]\nname = \"Demo\"\n",
            "name = \"demo\"\n[leanOptions]\nweak.linter.myStr = \"true\"\n",
            "name = \"demo\"\n[leanOptions]\nweak.linter.myStr = \"1500\"\n",
            "name = \"demo\"\n[leanOptions]\n\"weak.linter.myStr\" = \"x\"\n",
        ] {
            assert!(parse(bad).is_err(), "{bad}");
        }
        let quoted_seg = parse(
            "name = \"demo\"\n[leanOptions]\nweak.linter.\"unused-vars\" = false\nweak.linter.\"0\" = true\nweak.linter.\"has.dot\" = \"x\"\n",
        )
        .unwrap();
        assert_eq!(
            quoted_seg.lean_options,
            BTreeMap::from([
                (
                    LeanName(vec![
                        LeanNamePart::Str("weak".to_string()),
                        LeanNamePart::Str("linter".to_string()),
                        LeanNamePart::Str("unused-vars".to_string()),
                    ]),
                    LeanOptionValue::Bool(false),
                ),
                (
                    LeanName(vec![
                        LeanNamePart::Str("weak".to_string()),
                        LeanNamePart::Str("linter".to_string()),
                        LeanNamePart::Str("0".to_string()),
                    ]),
                    LeanOptionValue::Bool(true),
                ),
                (
                    LeanName(vec![
                        LeanNamePart::Str("weak".to_string()),
                        LeanNamePart::Str("linter".to_string()),
                        LeanNamePart::Str("has.dot".to_string()),
                    ]),
                    LeanOptionValue::Str("x".to_string()),
                ),
            ])
        );
        let ok = parse("name = \"demo\"\n[leanOptions]\nweak.linter.style.longFile = 1500\n\"autoImplicit\" = false\n").unwrap();
        // Astra r10: TOML escapes decode (`α`) or fail; explicit empty selections fail.
        let esc = parse("name = \"demo\"\nsrcDir = \"src/\\u03b1\"\n").unwrap();
        assert_eq!(esc.src_dir, PathBuf::from("src/α"));
        assert!(parse("name = \"demo\"\nsrcDir = \"src/\\q\"\n").is_err());
        assert!(parse("name = \"demo\"\n[[lean_lib]]\nname = \"Demo\"\nglobs = []\n").is_err());
        assert!(parse("name = \"demo\"\n[[lean_lib]]\nname = \"Demo\"\nroots = []\n").is_err());
        let tools = parse(
            "name = \"demo\"\n[[lean_lib]]\nname = \"Tools\"\nroots = []\nglobs = [\"Tools.+\"]\n",
        )
        .unwrap();
        assert_eq!(
            tools.libs[0].globs,
            vec![GlobSpec::Submodules("Tools".to_string())]
        );
        assert_eq!(
            ok.lean_options,
            BTreeMap::from([
                (
                    LeanName::from_str_to_name("autoImplicit").unwrap(),
                    LeanOptionValue::Bool(false)
                ),
                (
                    LeanName::from_str_to_name("weak.linter.style.longFile").unwrap(),
                    LeanOptionValue::Nat(1500)
                ),
            ])
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_lake_init_templates_and_module_resolution_follow_lake() {
        // Gemini r9: `lake init demo std.lean` output, `«»` in name literals.
        let dir = make_temp_test_dir("lake_init_resolution");
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\n\npackage \"demo\" where\n  version := v!\"0.1.0\"\n\nlean_lib «Demo» where\n  -- add library configuration options here\n\n@[default_target]\nlean_exe \"demo\" where\n  root := `Main\n",
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, true).unwrap();
        assert_eq!(pkg.name, "demo");
        assert_eq!(pkg.libs[0].name, "Demo");
        assert_eq!(pkg.exes[0].name, "demo");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage «p» where\n  defaultTargets := #[`«demo-exe»]\nlean_exe «demo-exe» where\n  root := `Main\n",
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, true).unwrap();
        assert_eq!(pkg.default_targets, vec!["demo-exe".to_string()]);
        let _ = fs::remove_dir_all(&dir);

        // Module-to-target resolution follows Lake's `findTargetModule?`.
        let dir = make_temp_test_dir("lake_resolution");
        let tf = dir.join("lakefile.toml");
        let touch = |rel: &str| {
            let f = dir.join(rel);
            fs::create_dir_all(f.parent().unwrap()).unwrap();
            fs::write(f, "").unwrap();
        };
        for f in [
            "Demo.lean",
            "Main.lean",
            "Guest.lean",
            "Tools.lean",
            "Tools/Helper.lean",
            "Parent.lean",
            "Parent/Child/Leaf.lean",
        ] {
            touch(f);
        }
        let target = |toml: &str, module: &str| {
            fs::write(&tf, toml).unwrap();
            let pkg = parse_lakefile_toml(&dir, &tf, true).unwrap();
            resolve_module_in_package(&pkg, true, module).map(|m| m.target_name)
        };
        // An executable's root belongs to the executable, not to a library sharing srcDir.
        let std_toml = "name = \"demo\"\ndefaultTargets = [\"demo\"]\n[[lean_lib]]\nname = \"Demo\"\n[[lean_exe]]\nname = \"demo\"\nroot = \"Main\"\n";
        assert_eq!(target(std_toml, "Main").as_deref(), Some("demo"));
        assert_eq!(target(std_toml, "Demo").as_deref(), Some("Demo"));
        // `roots = []` + `globs = ["Tools.+"]`: submodules belong to that library, and
        // `Tools` itself is no library's module.
        let tools = "name = \"Guest\"\n[[lean_lib]]\nname = \"Guest\"\n[[lean_lib]]\nname = \"HelperLib\"\nroots = []\nglobs = [\"Tools.+\"]\n";
        assert_eq!(target(tools, "Tools.Helper").as_deref(), Some("HelperLib"));
        assert_eq!(target(tools, "Tools"), None);
        // Later libraries win (`findSomeRev?`).
        let nested = "name = \"P\"\n[[lean_lib]]\nname = \"Parent\"\n[[lean_lib]]\nname = \"Parent.Child\"\n";
        assert_eq!(
            target(nested, "Parent.Child.Leaf").as_deref(),
            Some("Parent.Child")
        );
        assert_eq!(target(nested, "Parent").as_deref(), Some("Parent"));
        // Astra r12: a root claims its subtree only if a glob selects the root itself.
        touch("Parent/Other.lean");
        touch("Parent/Child.lean");
        let selective = "name = \"P\"\n[[lean_lib]]\nname = \"Parent\"\n[[lean_lib]]\nname = \"Selected\"\nroots = [\"Parent\"]\nglobs = [\"Parent.Child\"]\n";
        assert_eq!(target(selective, "Parent.Other").as_deref(), Some("Parent"));
        assert_eq!(
            target(selective, "Parent.Child").as_deref(),
            Some("Selected")
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_lakefile_lexical_guard_rejects_desync_syntax() {
        let dir = make_temp_test_dir("lakefile_lexical_guard");
        let lf = dir.join("lakefile.lean");
        let parse = |src: &str, root: bool| {
            fs::write(&lf, src).unwrap();
            parse_lakefile_lean(&dir, &lf, root)
        };
        let lib = "@[default_target]\nlean_lib Demo where\n  leanOptions := opts\n";
        let opts = "abbrev opts : Array LeanOption := #[⟨`autoImplicit, false⟩]\n";
        // Gemini r5, each verified against real Lake: guillemets that open a fake comment or
        // string, raw strings, interpolation braces holding comments, brace configs, `;`,
        // guillemet field names, `buildType`, duplicate fields, `run_io`.
        let cases = [
            "import Lake\nopen Lake DSL\n\npackage «demo/-»\n\n#eval IO.println \"PWNED\"\nmacro_rules | `(#[⟨`autoImplicit, false⟩]) => `(#[⟨`warn.sorry, false⟩])\n\n-- -/\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n".to_string(),
            format!("import Lake\nopen Lake DSL\n{opts}def n1 : Lean.Name := `«\"» #eval IO.println \"EXEC\" def n2 : Lean.Name := `«\"»\npackage demo\n{lib}"),
            format!("import Lake\nopen Lake DSL\n{opts}def s1 : String := r#\"\\\"# #eval IO.println r#\"RAW\"# def s2 : String := r#\"\"\"#\npackage demo\n{lib}"),
            format!("import Lake\nopen Lake DSL\n{opts}def s1 : String := s!\"{{ /- \"{{ -/ 0 }}\" #eval IO.println \"INTERP\" def s2 : String := s!\"{{ /- \" -/ 0 }}\"\npackage demo\n{lib}"),
            "import Lake\nopen Lake DSL\n\npackage demo { leanOptions := #[⟨`autoImplicit, false⟩] }\n\n@[default_target]\nlean_lib Demo { leanOptions := #[⟨`warn.sorry, false⟩] }\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  libName := \"a\"; moreLeanArgs := #[\"-Dwarn.sorry=false\"]\n".to_string(),
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  «leanOptions» := #[⟨`warn.sorry, false⟩]\n".to_string(),
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  buildType := .debug\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n  leanOptions := #[]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo where\n  description := run_io do\n    IO.println \"RUN_IO\"\n    return \"desc\"\n  leanOptions := #[⟨`autoImplicit, false⟩]\n\n@[default_target]\nlean_lib Demo\n".to_string(),
            format!("import Lake\nopen Lake DSL\n{opts}def c : Char := '\"' #eval IO.println \"CHAR\"\npackage demo\n{lib}"),
            format!("import Lake\nopen Lake DSL\n{opts}def inλ : Nat := 1\npackage demo\n{lib}"),
        ];
        for src in &cases {
            for root in [false, true] {
                assert!(parse(src, root).is_err(), "root={root}: {src}");
            }
        }
        // Gemini r6: `<--` and `/--/` comment desyncs, `!run_io` / `!r#"` after a non-word char,
        // `run_io` inside string braces, header braces without a space, `toLeanConfig`,
        // indented metaprogramming, `#[..] ++ #[..]` argument arrays.
        let r6 = [
            "import Lake\nopen Lake DSL\n\npackage demo where\n  description := (fun _ => \"ok\") (`(tactic| rw [<-- h]) : Lean.MacroM _) #eval IO.println \"x\" /-\n  ])) -/\n\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n".to_string(),
            "import Lake\nopen Lake DSL\n\n/--/\n-- -/ def hidden : Unit := () #eval IO.println \"x\"\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo where\n  preferReleaseBuild := !run_io do\n    IO.println \"x\"\n    return false\n\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n".to_string(),
            format!("import Lake\nopen Lake DSL\n{opts}def b1 : Bool := !r#\"\\\"#.isEmpty #eval IO.println \"x\" def b2 : Bool := !r#\"\"\"#.isEmpty\npackage demo\n{lib}"),
            format!("import Lake\nopen Lake DSL\n{opts}def payload : IO String := pure \"h\"\npackage demo where\n  description := s!\"{{run_io payload}}\"\n{lib}"),
            "import Lake\nopen Lake DSL\n\npackage demo{leanOptions:=#[⟨`warn.sorry,false⟩]}\n\n@[default_target]\nlean_lib Demo\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  toLeanConfig := { leanOptions := #[⟨`autoImplicit, false⟩] }\n".to_string(),
            "import Lake\nopen Lake DSL\n\n  local notation \"#[]\" => #[\"-DautoImplicit=true\"]\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  moreLeanArgs := #[]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  moreLeanArgs := #[\"-DautoImplicit=false\"] ++ #[\"-DautoImplicit=true\"]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  moreLeanArgs := #[\"-DautoImplicit=\\x66alse\"]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target] lean_lib«Demo» where\n  moreLeanArgs := #[]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib\n  Demo where\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`sat.solver, \"./evil.sh\"⟩]\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo\n\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`maxHeartbeats, 18446744073709551616⟩]\n".to_string(),
        ];
        for src in &r6 {
            for root in [false, true] {
                assert!(parse(src, root).is_err(), "root={root}: {src}");
            }
        }
        for bad in [
            "-Dsat.solver=./evil.sh",
            "-Dtrace.profiler.output=/tmp/x.json",
            "-Ddebug.byAsSorry=true",
            "-Dweak.debug.proofAsSorry=true",
        ] {
            assert!(!is_allowed_lean_arg(bad), "{bad}");
        }
        for ok in [
            "-Dweak.linter.style.longFile=1500",
            "-Dexperimental.module=true",
            "-DwarningAsError=false",
        ] {
            assert!(is_allowed_lean_arg(ok), "{ok}");
        }
        // Gemini r7 / Astra r9: `\/-` and `//-` openers, `lo...r#"` dotted words, indented and
        // inline-driver targets, whitespace-only multi-line values, shadowable `FilePath.mk`,
        // bare names and `++` in name arrays.
        let r9 = [
            "import Lake\nopen Lake DSL\n\npackage demo where\n  preferReleaseBuild := (fun _ => false) (True \\/- -1 < (0 : Int))\n  leanOptions := #[⟨`autoImplicit, false⟩]\n  buildArchive := (fun _ => \"x\") (True -- -/\n  )\n\n@[default_target]\nlean_lib Demo\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo where\n  preferReleaseBuild := (fun lo => (lo...r#\"\\\"#.length).lower == 99) 0\n  leanOptions := #[⟨`autoImplicit, false⟩]\n  buildArchive := (fun lo => (lo...r#\"\"\"#.length).lower.repr) 0\n\n@[default_target]\nlean_lib Demo\n".to_string(),
            "import Lake\nopen Lake DSL\n\npackage demo where\n  defaultTargets := #[`Demo]\nopen Lake\n\n@[default_target]\n  lean_lib Demo where\n    moreLeanArgs := #[\"-DautoImplicit=false\"]\n".to_string(),
            "import Lake\nopen Lake DSL\npackage demo where\n  srcDir := \"\n  \"\n@[default_target]\nlean_lib Demo\n".to_string(),
            "import Lake\nopen System Lake DSL\ndef FilePath.mk (_ : String) : System.FilePath := \"actual\"\npackage demo where\n  srcDir := FilePath.mk \"wrong\"\n@[default_target]\nlean_lib Demo\n".to_string(),
            "import Lake\nopen Lake DSL\nabbrev entry : Lean.Name := `Actual\npackage demo\n@[default_target]\nlean_lib Demo where\n  roots := #[entry]\n".to_string(),
            "import Lake\nopen Lake DSL\npackage demo\n@[default_target]\nlean_lib Demo where\n  roots := #[`A]++#[`B]\n".to_string(),
        ];
        for src in &r9 {
            for root in [false, true] {
                assert!(parse(src, root).is_err(), "root={root}: {src}");
            }
        }
        // `@[test_driver]` marks the next target without dropping its fields; #299: Lake also
        // accepts it inline on the header line, where the fields attach to the target the same
        // way (the plain gate used to refuse the inline `where` form).
        let driver = "import Lake\nopen Lake DSL\npackage demo\n@[test_driver]\nlean_lib Demo where\n  moreLeanArgs := #[\"-DautoImplicit=false\"]\n";
        let inline_pkg = parse(&driver.replace("]\nlean_lib", "] lean_lib"), false).unwrap();
        assert_eq!(
            inline_pkg.libs[0].more_lean_args,
            vec!["-DautoImplicit=false".to_string()]
        );
        let pkg = parse(driver, false).unwrap();
        assert_eq!(pkg.libs.len(), 1);
        assert_eq!(
            pkg.libs[0].more_lean_args,
            vec!["-DautoImplicit=false".to_string()]
        );
        assert!(!pkg.libs[0].is_default_target);
        // Args are checked exactly as passed on; `pp.*` beyond Mathlib's two keys is refused
        // (`pp.maxSteps`, `pp.all`, ... reprint the sorry warning).
        for bad in [
            " --quiet",
            "\n-DautoImplicit=false",
            "-Dweak.linter.s=foo\n",
            "-Dweak.warn.sorry=true ",
            "-Dpp.maxSteps=0",
            "-Dpp.all=true",
            "-Dweak.pp.raw=true",
            "-Dweak.weak.linter.x=true",
        ] {
            assert!(!is_allowed_lean_arg(bad), "{bad:?}");
        }
        // Fable r9: a column-0 `++` continuing a target field; Astra r10: explicit empty
        // module selections.
        for src in [
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n++ #[⟨`linter.x, true⟩]\n",
            "import Lake\nopen Lake DSL\npackage demo\n@[default_target]\nlean_lib Demo where\n  globs := #[]\n",
            "import Lake\nopen Lake DSL\npackage demo\n@[default_target]\nlean_lib Demo where\n  roots := #[]\n",
        ] {
            for root in [false, true] {
                assert!(parse(src, root).is_err(), "root={root}: {src}");
            }
        }
        // Signed or zero-padded digit strings and Nats would be re-read as other numbers.
        for v in ["\"+0\"", "\"+42\"", "007", ".ofNat 01"] {
            let src = format!(
                "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`maxHeartbeats, {v}⟩]\n"
            );
            assert!(parse(&src, false).is_err(), "{v}");
        }
        assert!(!is_allowed_lean_arg("-Ddebug.skipKernelTC=true"));
        assert!(!is_allowed_lean_arg("-Dweak.debug.skipKernelTC=true"));
        // What Mathlib needs still passes: `«»` target names, `s!` with a dotted name in
        // braces, structure-instance braces in code.
        let ok = "import Lake\nopen Lake DSL\nabbrev xs : Array LeanOption := #[⟨`a, true⟩].map fun s ↦ { s with name := `weak ++ s.name }\npackage demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\nlean_exe «cache-test» where\n  root := `Main\npost_update pkg do\n  IO.println s!\"x ({pkg.baseName}) \\\n    y\"\n";
        assert_eq!(
            lakefile_lexical_guard(ok, true).unwrap().0,
            splitter::strip_lean_comments(ok)
        );
        assert!(parse(ok, false).is_ok());
        // Astra r7: a target written inside a multi-line string is not a target.
        let phantom = "import Lake\nopen Lake DSL\ndef msg : String := \"\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, true⟩]\n  \"\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n";
        let pkg = parse(phantom, false).unwrap();
        assert_eq!(pkg.libs.len(), 1);
        assert_eq!(
            pkg.libs[0].lean_options,
            BTreeMap::from([(
                LeanName::from_str_to_name("autoImplicit").unwrap(),
                LeanOptionValue::Bool(false)
            )])
        );
        // Astra r8: shadowing a constructor spelling the resolver reads, and a field value
        // written with a string gap, both fail closed.
        let shadow = "import Lake\nopen Lake DSL\ndef LeanOption.mk (_ : Lean.Name) (_ : LeanOptionValue) : Lake.LeanOption := ⟨`autoImplicit, false⟩\npackage demo\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[LeanOption.mk `autoImplicit true]\n";
        assert!(parse(shadow, false).is_err());
        let gap = "import Lake\nopen Lake DSL\npackage demo where\n  srcDir := \"s\\\n    rc\"\n@[default_target]\nlean_lib Demo\n";
        assert!(parse(gap, false)
            .unwrap_err()
            .to_string()
            .contains("multi-line string"));
        // Astra r7: `leanOptions` reach Lean through setup.json (or last in flat CLI helpers), which beats `-D` flags,
        // while staying separate from `strong_args` (`Module.leanArgs`).
        let precedence = "import Lake\nopen Lake DSL\npackage demo\n@[default_target]\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n  moreLeanArgs := #[\"-DautoImplicit=true\"]\n";
        let pkg = parse(precedence, false).unwrap();
        let lib = &pkg.libs[0];
        let (eff_opts, strong, weak) = compose_effective_args(
            &pkg,
            &lib.lean_options,
            &lib.more_lean_args,
            &lib.weak_lean_args,
        );
        assert_eq!(strong, vec!["-DautoImplicit=true".to_string()]);
        assert_eq!(
            eff_opts.get(&LeanName::from_str_to_name("autoImplicit").unwrap()),
            Some(&LeanOptionValue::Bool(false))
        );
        let flat = compose_flat_filtered_args_with_options(&weak, &strong, &eff_opts);
        let last_auto = flat.iter().rfind(|a| a.starts_with("-DautoImplicit="));
        assert_eq!(last_auto.map(String::as_str), Some("-DautoImplicit=false"));
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_static_sorry_options_are_forced_on() {
        let dir = make_temp_test_dir("static_sorry");
        for key in ["warn.sorry", "weak.warn.sorry"] {
            for (file, source) in [
                ("lakefile.toml", format!("name = \"demo\"\nmoreLeanArgs = [\"-D{key}=false\"]\nweakLeanArgs = [\"-D{key}=false\"]\n[leanOptions]\n{key} = false\n[[lean_lib]]\nname = \"Demo\"\n")),
                ("lakefile.lean", format!("import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`{key}, false⟩]\n  moreLeanArgs := #[\"-D{key}=false\"]\n  weakLeanArgs := #[\"-D{key}=false\"]\n")),
            ] {
                let path = dir.join(file);
                fs::write(&path, &source).unwrap();
                let cfg = resolve_project_config(&dir).unwrap();
                let pkg = &cfg.root_pkg;
                let lib = &pkg.libs[0];
                let (opts, strong, weak) = compose_effective_args(pkg, &lib.lean_options, &lib.more_lean_args, &lib.weak_lean_args);
                let args = compose_flat_filtered_args_with_options(&weak, &strong, &opts);
                assert!(strong.contains(&format!("-D{key}=false")));
                let raw_options = serde_json::json!([[format!("-D{key}=false"), format!("{:016x}", lake_hash_text(&format!("-D{key}=false")))]]);
                assert!(verify_trace_options_value(&opts, &raw_options));
                assert!(args.contains(&format!("-D{key}=true")), "{args:?}");
                assert!(!args.iter().any(|a| a.ends_with("sorry=false")));
                for bad in ["debug.skipKernelTC", "pp.all"] {
                    fs::write(&path, source.replace(key, bad).replace("false", "true")).unwrap();
                    assert!(resolve_project_config(&dir).is_err());
                }
                fs::remove_file(path).unwrap();
            }
        }
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    #[ignore = "requires warm PFR and Mathlib fixtures via TURBO_LEAN_WARM_ROOT"]
    fn test_warm_pfr_static_configs() {
        let root = PathBuf::from(std::env::var_os("TURBO_LEAN_WARM_ROOT").unwrap());
        resolve_project_config(&root.join("pfr")).unwrap();
        for entry in fs::read_dir(root.join("pfr/.lake/packages")).unwrap() {
            resolve_package_config(&entry.unwrap().path(), false).unwrap();
        }
        let fixture = root.join("fixtures/mathlib-v4.35.0-lakefile.lean");
        parse_lakefile_lean(fixture.parent().unwrap(), &fixture, false).unwrap();
    }

    #[test]
    fn test_computed_lean_options_scopes_continuations_and_lexing() {
        let dir = make_temp_test_dir("lean_opts_regress");
        let lf = dir.join("lakefile.lean");
        let parse = |src: &str| {
            fs::write(&lf, src).unwrap();
            parse_lakefile_lean(&dir, &lf, false)
        };
        let opts = |pkg: &PackageConfig| pkg.libs[0].lean_options.clone();
        let piped_binding = "import Lake\nopen Lake DSL\nabbrev xs : Array LeanOption := #[]\n|>.push ⟨`autoImplicit, false⟩\npackage demo\nlean_lib Demo where\n  leanOptions := xs\n";
        assert_eq!(
            opts(&parse(piped_binding).unwrap()).values().next(),
            Some(&LeanOptionValue::Bool(false))
        );
        for target in ["lean_lib", "lean_exe"] {
            for close in ["}", "  }"] {
                let src = format!("import Lake\nopen Lake DSL\npackage demo\n@[default_target] {target} Demo {{\n  leanOptions := #[⟨`autoImplicit, false⟩]\n{close}\n");
                assert!(parse(&src).is_ok(), "{src}");
                assert!(parse(src.rsplit_once(close).unwrap().0).is_err());
            }
        }
        for field in ["roots := #[`Demo]", "leanOptions := #[]"] {
            let src = format!("import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  {field}\n|>.push arbitraryCode\n");
            assert!(parse(&src).is_err(), "{src}");
        }
        for expr in [
            "xs.push ⟨`linter.a, false⟩ |>.push ⟨`linter.b, true⟩",
            "xs.push (⟨`linter.a, false⟩)\n  |>.push (⟨`linter.b, true⟩)",
            "Array.push (Array.push xs (⟨`linter.a, false⟩)) (⟨`linter.b, true⟩)",
            "Array.push\t(Array.push xs (⟨`linter.a, false⟩)) (⟨`linter.b, true⟩)",
            "(xs.push ⟨`linter.a, false⟩).push ⟨`linter.b, true⟩",
        ] {
            let src = format!("import Lake\nopen Lake DSL\nabbrev xs : Array LeanOption := #[⟨`linter.a, true⟩]\npackage demo\nlean_lib Demo where\n  leanOptions := {expr}\n");
            let pkg = parse(&src).unwrap();
            assert_eq!(
                opts(&pkg),
                parse_lean_options_expr("#[⟨`linter.a, false⟩, ⟨`linter.b, true⟩]").unwrap()
            );
            for bad in ["debug.skipKernelTC", "pp.all"] {
                assert!(parse(&src.replace("linter.b", bad)).is_err());
            }
            assert!(parse(&src.replace("⟨`linter.b, true⟩", "arbitraryCode")).is_err());
        }
        let deep = format!(
            "#[]{}",
            ".push ⟨`linter.a, true⟩".repeat(LEAN_OPTIONS_MAX_DEPTH + 1)
        );
        assert!(
            resolve_lean_options_expr(&deep, &LakefileBindings::default(), usize::MAX).is_err()
        );
        // A same-named binding inside a namespace makes the reference ambiguous: fail closed
        // rather than pick a body (Lake would resolve the global one).
        let scoped = "import Lake\nopen Lake DSL\nabbrev opts : Array LeanOption := #[⟨`autoImplicit, false⟩]\nnamespace Other\nabbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\nend Other\npackage demo\nlean_lib Demo where\n  leanOptions := opts\n";
        assert!(parse(scoped).unwrap_err().to_string().contains("not plain"));
        // Indented declarations and declarations inside an indented namespace also block
        // resolution (Lean would pick `N.opts` here).
        let indented = "import Lake\nopen Lake DSL\nabbrev opts : Array LeanOption := #[⟨`autoImplicit, false⟩]\nnamespace N\n  abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\nlean_lib Demo where\n  leanOptions := opts\nend N\npackage demo\n";
        assert!(parse(indented).is_err());
        // A value must be one string token, not an expression that starts and ends with quotes.
        for v in [
            "\"a\" ++ \"b\"",
            ".ofString \"a\" ++ \"b\"",
            "\"a\" \"b\"",
            "\"a\\\"",
        ] {
            let src = format!(
                "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`linter.s, {v}⟩]\n"
            );
            assert!(parse(&src).is_err(), "{v}");
        }
        // Parameterised declarations are not bindings.
        let param = "import Lake\nopen Lake DSL\nabbrev opts (b : Bool) : Array LeanOption := #[⟨`autoImplicit, b⟩]\npackage demo\nlean_lib Demo where\n  leanOptions := opts\n";
        assert!(parse(param)
            .unwrap_err()
            .to_string()
            .contains("parameterised"));
        // A field's expression continues on deeper-indented lines; later entries win.
        let cont = "import Lake\nopen Lake DSL\nabbrev xs : Array LeanOption := #[⟨`linter.a, true⟩]\nabbrev ys : Array LeanOption := #[⟨`linter.a, false⟩]\npackage demo\nlean_lib Demo where\n  leanOptions := xs\n\n    ++ ys\n  srcDir := \"src\"\n";
        assert_eq!(
            opts(&parse(cont).unwrap()),
            BTreeMap::from([(
                LeanName::from_str_to_name("linter.a").unwrap(),
                LeanOptionValue::Bool(false)
            )])
        );
        let bad_cont = cont.replace("++ ys", "++ ys.filter fun _ => true");
        assert!(parse(&bad_cont).is_err());
        // Delimiters inside strings do not change nesting, so the following column-0
        // declaration is not swallowed into the binding body.
        let strs = "import Lake\nopen Lake DSL\nabbrev xs : Array LeanOption := #[⟨`linter.s, \"[\"⟩, ⟨`linter.t, \"a,b\"⟩]\npackage demo\nlean_lib Demo where\n  leanOptions := xs\n";
        assert_eq!(
            opts(&parse(strs).unwrap()),
            BTreeMap::from([
                (
                    LeanName::from_str_to_name("linter.s").unwrap(),
                    LeanOptionValue::Str("[".to_string())
                ),
                (
                    LeanName::from_str_to_name("linter.t").unwrap(),
                    LeanOptionValue::Str("a,b".to_string())
                ),
            ])
        );
        // `'` is an identifier character in Lean names, not a string delimiter: lexing splits
        // correctly, and the resulting primed key is then refused by the `-D` key gate.
        let (parts, open) = lean_scan("⟨`custom.flag', true⟩, ⟨`linter.x, false⟩", ",").unwrap();
        assert_eq!((parts.len(), open), (2, 0));
        let prime = "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`custom.flag', true⟩, ⟨`linter.x, false⟩]\n";
        assert!(parse(prime)
            .unwrap_err()
            .to_string()
            .contains("leanOptions"));
        // `leanOptions` pass the same flag gate as `moreLeanArgs`.
        let sorry_off = "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`warn.sorry, false⟩]\n";
        let pkg = parse(sorry_off).unwrap();
        assert_eq!(
            opts(&pkg).values().next(),
            Some(&LeanOptionValue::Bool(false))
        );
        // Modified or attributed declarations are not bindings (same line or previous line).
        for decl in [
            "private abbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]",
            "@[reducible] abbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]",
            "@[reducible]\nabbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]",
        ] {
            let src = format!(
                "import Lake\nopen Lake DSL\n{decl}\npackage demo\nlean_lib Demo where\n  leanOptions := opts\n"
            );
            assert!(parse(&src).is_err(), "{decl}");
        }
        // String values may contain spaces and escapes.
        let spaced = "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`linter.s, .ofString \"a b\\\"c\"⟩]\n";
        assert_eq!(
            opts(&parse(spaced).unwrap()),
            BTreeMap::from([(
                LeanName::from_str_to_name("linter.s").unwrap(),
                LeanOptionValue::Str("a b\"c".to_string())
            )])
        );
        // Mismatched delimiters fail.
        assert!(lean_scan("#[⟨`linter.a, true)]", ",").is_err());
        assert!(lean_scan("#[\"unclosed]", ",").is_err());
        let lib = |opts_expr: &str, prelude: &str| {
            format!("import Lake\nopen Lake DSL\n{prelude}package demo\nlean_lib Demo where\n  leanOptions := {opts_expr}\n")
        };
        // Static weak options retain Lake's raw values, including the weak-prefix map.
        assert_eq!(
            opts(&parse(&lib("#[⟨`weak.warn.sorry, false⟩]", "")).unwrap())
                .values()
                .next(),
            Some(&LeanOptionValue::Bool(false))
        );
        let ws = "abbrev ws : Array LeanOption := #[⟨`warn.sorry, false⟩]\n";
        assert_eq!(
            opts(
                &parse(&lib(
                    "ws.map fun s ↦ { s with name := `weak ++ s.name }",
                    ws
                ))
                .unwrap()
            )
            .values()
            .next(),
            Some(&LeanOptionValue::Bool(false))
        );
        // Option names must be name literals. #299: Lake 4.35 rejects explicit `LeanOption.mk`
        // applications and plain `(k, v)` tuples (unknown constants under the module system):
        // the root fails closed at parse time, a dependency records `unsupported` so only its
        // own modules fail, never the whole workspace configuration.
        for e in ["#[⟨optKey, false⟩]", "#[⟨``linter.x, false⟩]"] {
            assert!(parse(&lib(e, "")).is_err(), "{e}");
        }
        for e in [
            "#[LeanOption.mk optKey false]",
            "#[LeanOption.mk ` true]",
            "#[LeanOption.mk `linter.n (.ofNat 1500), LeanOption.mk `linter.s \"a b\"]",
            "#[(`linter.a, false)]",
        ] {
            let dep = parse(&lib(e, "")).unwrap();
            assert!(dep.libs[0].unsupported.is_some(), "{e}");
        }
        // Every scope form disables resolution; binders, dotted and universe names are rejected.
        for prelude in [
            "abbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]\nnoncomputable section\nend\n",
            "abbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]\nmutual\nend\n",
            "abbrev opts(b : Bool) : Array LeanOption := #[⟨`linter.a, true⟩]\n",
            "abbrev opts.{u} : Array LeanOption := #[⟨`linter.a, true⟩]\n",
            "abbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]\nabbrev Foo.opts : Array LeanOption := #[⟨`linter.a, false⟩]\n",
            "set_option autoImplicit true in\nabbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]\n",
        ] {
            assert!(parse(&lib("opts", prelude)).is_err(), "{prelude}");
        }
        // Same-column `++` continues a field, and a column-0 `++` continues a binding body.
        let xs = "abbrev xs : Array LeanOption := #[⟨`linter.a, true⟩]\nabbrev ys : Array LeanOption := #[⟨`linter.a, false⟩]\n";
        assert_eq!(
            opts(&parse(&lib("xs\n  ++ ys", xs)).unwrap()),
            BTreeMap::from([(
                LeanName::from_str_to_name("linter.a").unwrap(),
                LeanOptionValue::Bool(false)
            )])
        );
        let body =
            "abbrev zs : Array LeanOption := #[⟨`linter.a, true⟩]\n++ #[⟨`linter.a, false⟩]\n";
        assert_eq!(
            opts(&parse(&lib("zs", body)).unwrap()),
            BTreeMap::from([(
                LeanName::from_str_to_name("linter.a").unwrap(),
                LeanOptionValue::Bool(false)
            )])
        );
        // Char literals such as '[' or '"' are outside the lexical subset: fail closed.
        let chars = "def openBr : Char := '['\ndef dq : Char := '\"'\nabbrev xs : Array LeanOption := #[⟨`linter.a, true⟩]\n";
        assert!(parse(&lib("xs", chars))
            .unwrap_err()
            .to_string()
            .contains("char literal"));
        // Root packages keep rejecting top-level declarations (stricter root gate).
        fs::write(&lf, lib("xs", xs)).unwrap();
        assert!(parse_lakefile_lean(&dir, &lf, true).is_err());
        // Non-plain lakefiles disable identifier resolution: scopes hidden inside an unrelated
        // binding's body, `where` clauses, notation/macros and `open ... in` can all shadow `opts`.
        let opts_g = "abbrev opts : Array LeanOption := #[⟨`autoImplicit, false⟩]\n";
        for extra in [
            "def unrelated : Nat := 0\n  namespace N\n  abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n",
            "abbrev other : Array LeanOption := opts\nwhere\n  opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n",
            "macro \"opts\" : term => `(#[⟨`autoImplicit, true⟩])\n",
            "def Other.opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\nopen Other in\n",
        ] {
            let prelude = format!("{opts_g}{extra}");
            assert!(parse(&lib("opts", &prelude)).is_err(), "{extra}");
        }
        // Commands may share a line: a namespace and a shadowing declaration after an unrelated
        // body on the same line are still detected.
        let same_line = format!(
            "{opts_g}def unrelated : Nat := 0 namespace N abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n"
        );
        assert!(parse(&lib("opts", &same_line)).is_err());
        assert!(!lakefile_is_plain(
            "abbrev opts : Array LeanOption := #[] end N\npackage demo\n"
        ));
        assert!(lakefile_is_plain(
            "import Lake\nopen Lake DSL\nlean_lib Demo where\n  leanOptions := #[⟨`linter.s, \"namespace end\"⟩]\n"
        ));
        // Metaprogramming anywhere (incl. inside a post_update do-block or as `#command`s), `;`
        // field separators and a second target command mid-line make the file non-plain; then
        // even literal arrays fail closed, since notation/macro_rules can rewrite literals.
        for extra in [
            "post_update _pkg do\n  pure ()\n  macro:max (priority := high) \"opts\" : term => `(#[])\n",
            "post_update _pkg do\n  pure ()\n  #eval pure ()\n",
            "run_cmd pure ()\n",
            "notation:max \"false\" => true\n",
            "macro_rules | `(false) => `(true)\n",
            "@[default_target] lean_lib Dummy namespace N\n",
        ] {
            let prelude = format!("{opts_g}{extra}");
            assert!(parse(&lib("opts", &prelude)).is_err(), "{extra}");
            assert!(parse(&lib("#[⟨`autoImplicit, false⟩]", &prelude)).is_err(), "{extra}");
        }
        // Fable r4: keywords after an allowed start, after a `++` continuation, or later on an
        // indented continuation line; and a command hidden after a multi-line string closes.
        for extra in [
            "abbrev junk : Nat := 7 namespace Other abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n",
            "abbrev junk : Array Nat := #[1]\n++ #[2] namespace Other abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n",
            "def junk : Nat :=\n  7 namespace Other abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n",
            "def junk : Nat := 7\n  macro_rules | `(opts) => `((#[] : Array LeanOption))\n",
            "def s : String := \"abc\\\n  foo\" namespace N abbrev opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n",
        ] {
            let prelude = format!("{opts_g}{extra}");
            assert!(parse(&lib("opts", &prelude)).is_err(), "{extra}");
        }
        // A multi-line string mentioning keywords is still just a string.
        assert!(lakefile_is_plain(
            "abbrev xs : Array LeanOption := #[]\ndef msg : String := \"open in \\\n  namespace end\"\npackage demo\n"
        ));
        let semi =
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  moreLinkArgs := #[]; leanOptions := #[⟨`autoImplicit, true⟩]\n";
        assert!(parse(semi).is_err());
        // Lean elaborates in order: a binding declared after its use is not in scope.
        let forward = "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := opts\nabbrev opts : Array LeanOption := #[⟨`linter.a, true⟩]\n";
        assert!(parse(forward)
            .unwrap_err()
            .to_string()
            .contains("before its declaration"));
        let fwd_binding =
            "abbrev a : Array LeanOption := b\nabbrev b : Array LeanOption := #[⟨`linter.x, true⟩]\n";
        assert!(parse(&lib("a", fwd_binding)).is_err());
        let where_field = format!(
            "import Lake\nopen Lake DSL\n{opts_g}package demo\nlean_lib Demo where\n  leanOptions := opts\n  where\n    opts : Array LeanOption := #[⟨`autoImplicit, true⟩]\n"
        );
        assert!(parse(&where_field).is_err());
        // Option names are plain dotted identifiers only.
        for e in [
            "#[⟨`«a.b», true⟩]",
            "#[⟨`\"warn.sorry\", true⟩]",
            "#[⟨`x++y, true⟩]",
            "#[⟨`a..b, true⟩]",
            "#[⟨`«warn.sorry», false⟩]",
            "#[⟨`weak.linter.0, true⟩]",
        ] {
            assert!(parse(&lib(e, "")).is_err(), "{e}");
        }
        assert_eq!(
            opts(
                &parse(&lib(
                    "#[⟨`weak.linter.«unused-vars», false⟩, ⟨`weak.linter.«0», true⟩, ⟨`weak.linter.«has.dot», \"x\"⟩]",
                    ""
                ))
                .unwrap()
            ),
            BTreeMap::from([
                (
                    LeanName(vec![
                        LeanNamePart::Str("weak".to_string()),
                        LeanNamePart::Str("linter".to_string()),
                        LeanNamePart::Str("unused-vars".to_string()),
                    ]),
                    LeanOptionValue::Bool(false),
                ),
                (
                    LeanName(vec![
                        LeanNamePart::Str("weak".to_string()),
                        LeanNamePart::Str("linter".to_string()),
                        LeanNamePart::Str("0".to_string()),
                    ]),
                    LeanOptionValue::Bool(true),
                ),
                (
                    LeanName(vec![
                        LeanNamePart::Str("weak".to_string()),
                        LeanNamePart::Str("linter".to_string()),
                        LeanNamePart::Str("has.dot".to_string()),
                    ]),
                    LeanOptionValue::Str("x".to_string()),
                ),
            ])
        );
        // String values: only escapes Lean and the decoder agree on, no bool/number lookalikes.
        for e in [
            "#[⟨`linter.s, \"\\x41\"⟩]",
            "#[⟨`linter.s, \"\\u0041\"⟩]",
            "#[⟨`linter.s, \"\\'\"⟩]",
            "#[⟨`linter.s, .ofString \"true\"⟩]",
            "#[⟨`linter.s, \"42\"⟩]",
        ] {
            assert!(parse(&lib(e, "")).is_err(), "{e}");
        }
        assert_eq!(
            opts(&parse(&lib("#[⟨`linter.s, \"a\\\\b \\\"c\\\"\"⟩]", "")).unwrap()),
            BTreeMap::from([(
                LeanName::from_str_to_name("linter.s").unwrap(),
                LeanOptionValue::Str("a\\b \"c\"".to_string())
            )])
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_lake_trace_dep_hash_and_precompile_goldens() {
        assert_eq!(
            format!(
                "{:016x}",
                LeanName::from_str_to_name("weak.linter.«unused-vars»")
                    .unwrap()
                    .lean_hash()
            ),
            "002e710fcaedc2e4"
        );
        assert_eq!(
            format!(
                "{:016x}",
                LeanName::from_str_to_name("weak.linter.«0»")
                    .unwrap()
                    .lean_hash()
            ),
            "603252224c2aeb40"
        );
        assert_eq!(
            format!(
                "{:016x}",
                LeanName::from_str_to_name("weak.linter.0")
                    .unwrap()
                    .lean_hash()
            ),
            "61440faf51aadfb7"
        );
        assert_eq!(
            format!(
                "{:016x}",
                LeanName::from_str_to_name("autoImplicit")
                    .unwrap()
                    .lean_hash()
            ),
            "dd5e5669cec58574"
        );
        assert_eq!(
            format!(
                "{:016x}",
                LeanName::from_str_to_name("TurboLean.Assembler")
                    .unwrap()
                    .lean_hash()
            ),
            "f3ff02d4b89e0162"
        );
        assert_eq!(
            format!(
                "{:016x}",
                LeanName(vec![LeanNamePart::Str("weak.linter.myStr".to_string())]).lean_hash()
            ),
            "2332246c88276666"
        );
        assert_eq!(
            format!("{:016x}", lake_hash_name("TurboLean.Assembler")),
            "6f4e7ca5f8ee9bd1"
        );
        assert!(
            LeanName::from_str_to_name("weak.linter.«0»").unwrap()
                < LeanName::from_str_to_name("weak.linter.0").unwrap()
        );
        assert!(LeanName::quick_cmp_aux(
            &LeanName::from_str_to_name("weak.linter.0").unwrap().0,
            &LeanName::from_str_to_name("weak.linter.«0»").unwrap().0
        )
        .is_lt());
        assert_eq!(
            format!(
                "{:016x}",
                lake_hash_text(&format!(
                    "-Dweak.linter.«0»={}",
                    LeanOptionValue::Bool(false).as_cli_flag_value()
                ))
            ),
            "d567b2b483628b87"
        );
        assert_eq!(
            format!(
                "{:016x}",
                lake_hash_text(&format!(
                    "-Dweak.linter.0={}",
                    LeanOptionValue::Bool(true).as_cli_flag_value()
                ))
            ),
            "94bec158fd2f30c2"
        );
        assert_eq!(
            format!(
                "{:016x}",
                lake_hash_text(&format!(
                    "-Dweak.linter.«unused-vars»={}",
                    LeanOptionValue::Bool(false).as_cli_flag_value()
                ))
            ),
            "5abb2fa15f85b98a"
        );
        assert_eq!(
            LeanOptionValue::Str("he\"l\\lo\n".to_string()).as_cli_flag_value(),
            "\"he\"l\\lo\n\""
        );
        assert_eq!(
            format!(
                "{:016x}",
                lake_hash_text(
                    &LeanOptionValue::Str("he\"l\\lo\n".to_string()).as_cli_flag_value()
                )
            ),
            "e3d65d0f38a3bdf3"
        );
        assert_eq!(
            format!(
                "{:016x}",
                lake_hash_text(&format!(
                    "-Dweak.linter.myStr={}",
                    LeanOptionValue::Str("he\"l\\lo\n".to_string()).as_cli_flag_value()
                ))
            ),
            "152abd8af517775f"
        );
        assert_eq!(
            format!(
                "{:016x}",
                lake_mix_hash(
                    1723,
                    lake_hash_text(&format!(
                        "-DmaxHeartbeats={}",
                        LeanOptionValue::Nat(200000).as_cli_flag_value()
                    ))
                )
            ),
            "c9c9a05b5120f965"
        );
        let mut opts = LeanOptionsMap::new();
        opts.insert(
            LeanName::from_str_to_name("weak.linter.0").unwrap(),
            LeanOptionValue::Bool(true),
        );
        opts.insert(
            LeanName::from_str_to_name("weak.linter.«0»").unwrap(),
            LeanOptionValue::Bool(false),
        );
        let mut hasher = blake3::Hasher::new();
        update_hasher_lean_options(&mut hasher, &opts);
        let ordered = hasher.finalize();
        let mut reversed = LeanOptionsMap::new();
        reversed.insert(
            LeanName::from_str_to_name("weak.linter.«0»").unwrap(),
            LeanOptionValue::Bool(false),
        );
        reversed.insert(
            LeanName::from_str_to_name("weak.linter.0").unwrap(),
            LeanOptionValue::Bool(true),
        );
        let mut hasher = blake3::Hasher::new();
        update_hasher_lean_options(&mut hasher, &reversed);
        assert_eq!(ordered, hasher.finalize());
        let dir = make_temp_test_dir("precompile_or");
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"pre\"\nprecompileModules = true\n[[lean_lib]]\nname = \"Pre\"\nprecompileModules = false\nglobs = [\"Pre.+\"]\n",
        )
        .unwrap();
        fs::create_dir_all(dir.join("Pre")).unwrap();
        fs::write(dir.join("Pre/A.lean"), "def a : Nat := 1\n").unwrap();
        fs::write(dir.join("Pre/B.lean"), "import Pre.A\ndef b : Nat := a\n").unwrap();
        fs::write(dir.join("Pre/C.lean"), "import Pre.A\ndef c : Nat := a\n").unwrap();
        fs::write(
            dir.join("Pre/D.lean"),
            "import Pre.B\nimport Pre.C\ndef d : Nat := b + c\n",
        )
        .unwrap();
        let cfg = resolve_project_config(&dir).unwrap();
        assert!(cfg.root_pkg.precompile_modules);
        assert!(!cfg.root_pkg.libs[0].precompile_modules.unwrap());
        let dag = build_module_dag(&cfg, &[]).unwrap();
        for name in ["Pre.A", "Pre.B", "Pre.C", "Pre.D"] {
            assert!(
                dag.nodes
                    .values()
                    .any(|n| n.module_name == name && n.needs_c),
                "{name} must need .c"
            );
        }
        // Also verify precompiled-lib -> non-precompiled-lib diamond propagation (`PreLib.D` -> `Plain.B`/`Plain.C` -> `Plain.A`).
        let exe_dir = make_temp_test_dir("ws9_exe_prop");
        fs::write(exe_dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            exe_dir.join("lakefile.toml"),
            "name = \"exeprop\"\n[[lean_lib]]\nname = \"Plain\"\nglobs = [\"Plain.+\"]\n[[lean_lib]]\nname = \"PreLib\"\nprecompileModules = true\nglobs = [\"PreLib.+\"]\n",
        )
        .unwrap();
        fs::create_dir_all(exe_dir.join("Plain")).unwrap();
        fs::create_dir_all(exe_dir.join("PreLib")).unwrap();
        fs::write(exe_dir.join("Plain/A.lean"), "def a : Nat := 1\n").unwrap();
        fs::write(
            exe_dir.join("Plain/B.lean"),
            "import Plain.A\ndef b : Nat := a + 1\n",
        )
        .unwrap();
        fs::write(
            exe_dir.join("Plain/C.lean"),
            "import Plain.A\ndef c : Nat := a + 2\n",
        )
        .unwrap();
        fs::write(
            exe_dir.join("PreLib/D.lean"),
            "import Plain.B\nimport Plain.C\ndef d : Nat := b + c\n",
        )
        .unwrap();
        let exe_cfg = resolve_project_config(&exe_dir).unwrap();
        let exe_dag = build_module_dag(&exe_cfg, &["PreLib".to_string()]).unwrap();
        for name in ["Plain.A", "Plain.B", "Plain.C", "PreLib.D"] {
            assert!(
                exe_dag
                    .nodes
                    .values()
                    .any(|n| n.module_name == name && n.needs_c),
                "precompiled transitive dependency {name} must need .c"
            );
        }
        let _ = fs::remove_dir_all(&exe_dir);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_plain_lakefile_supports_input_dir_and_input_file_with_lean_options() {
        let dir = make_temp_test_dir("plain_input_targets_with_options");
        fs::create_dir_all(dir.join("Data")).unwrap();
        fs::create_dir_all(dir.join("Smoke")).unwrap();
        fs::write(dir.join("Data/a.sol"), "contract A {}\n").unwrap();
        fs::write(dir.join("spec.json"), "{}\n").unwrap();
        fs::write(dir.join("Smoke/A.lean"), "def a : Nat := 1\n").unwrap();
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        let lf = dir.join("lakefile.lean");

        // 1. Root package combining `leanOptions`, `moreLeanArgs`, `weakLeanArgs` AND
        //    `input_dir` / `input_file` / `needs` (including guillemet and inline `@[default_target]`).
        let root_src = "\
import Lake
open Lake DSL

package demo where
  leanOptions := #[⟨`autoImplicit, false⟩]
  moreLeanArgs := #[\"-DrelaxedAutoImplicit=false\"]
  weakLeanArgs := #[\"-Dweak.linter.unusedVariables=false\"]

input_dir smokeSources where
  path := \"Data\"
  filter := .extension \"sol\"

@[default_target]
input_file specFile where
  path := \"spec.json\"
  text := true

@[default_target]
lean_lib Smoke where
  globs := #[.one `Smoke.A]
  leanOptions := #[⟨`pp.unicode.fun, true⟩]
  needs := #[smokeSources, specFile]
";
        assert!(lakefile_is_plain(root_src));
        fs::write(&lf, root_src).unwrap();
        for is_root in [true, false] {
            let pkg = parse_lakefile_lean(&dir, &lf, is_root).unwrap();
            assert!(pkg.unsupported.is_none());
            assert_eq!(
                pkg.lean_options,
                BTreeMap::from([(
                    LeanName::from_str_to_name("autoImplicit").unwrap(),
                    LeanOptionValue::Bool(false)
                )])
            );
            assert_eq!(pkg.more_lean_args, vec!["-DrelaxedAutoImplicit=false"]);
            assert_eq!(
                pkg.weak_lean_args,
                vec!["-Dweak.linter.unusedVariables=false"]
            );
            assert_eq!(pkg.inputs.len(), 2);
            assert_eq!(pkg.inputs[0].name, "smokeSources");
            assert_eq!(pkg.inputs[1].name, "specFile");
            assert_eq!(pkg.libs[0].needs, vec!["smokeSources", "specFile"]);
            assert_eq!(
                pkg.libs[0].lean_options,
                BTreeMap::from([(
                    LeanName::from_str_to_name("pp.unicode.fun").unwrap(),
                    LeanOptionValue::Bool(true)
                )])
            );
        }
        let cfg = resolve_project_config(&dir).unwrap();
        let dag = build_module_dag(&cfg, &[]).unwrap();
        assert!(dag.nodes.contains_key("Smoke.A"));

        // 2. Dependency package combining `abbrev` option bindings with `input_dir` / `input_file` / `needs`.
        let dep_src = "\
import Lake
open Lake DSL

abbrev sharedOpts : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`pp.unicode.fun, true⟩
]

package dep where
  leanOptions := sharedOpts

input_dir smokeSources where
  path := \"Data\"
  filter := .extension \"sol\"

lean_lib Smoke where
  globs := #[.one `Smoke.A]
  leanOptions := sharedOpts.map fun s ↦ { s with name := `weak ++ s.name }
  needs := #[smokeSources]
";
        assert!(lakefile_is_plain(dep_src));
        fs::write(&lf, dep_src).unwrap();
        let dep_pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
        assert!(dep_pkg.unsupported.is_none());
        assert_eq!(
            dep_pkg.lean_options,
            BTreeMap::from([
                (
                    LeanName::from_str_to_name("autoImplicit").unwrap(),
                    LeanOptionValue::Bool(false)
                ),
                (
                    LeanName::from_str_to_name("pp.unicode.fun").unwrap(),
                    LeanOptionValue::Bool(true)
                ),
            ])
        );
        assert_eq!(
            dep_pkg.libs[0].lean_options,
            BTreeMap::from([
                (
                    LeanName::from_str_to_name("weak.autoImplicit").unwrap(),
                    LeanOptionValue::Bool(false)
                ),
                (
                    LeanName::from_str_to_name("weak.pp.unicode.fun").unwrap(),
                    LeanOptionValue::Bool(true)
                ),
            ])
        );
        assert_eq!(dep_pkg.libs[0].needs, vec!["smokeSources"]);

        // 3. Mid-line, indented, or inline-attributed `input_dir` / `input_file` smuggling remains non-plain & rejected.
        for smuggled in [
            "import Lake\nopen Lake DSL\nabbrev opts : Array LeanOption := #[] input_dir hid where\npackage demo\nlean_lib Smoke where\n  leanOptions := opts\n",
            "import Lake\nopen Lake DSL\npackage demo\ndef junk : Nat := 0\n  input_file hid where\nlean_lib Smoke where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n",
            "import Lake\nopen Lake DSL\npackage demo\n@[default_target] input_file hid where\n  path := \"spec.json\"\nlean_lib Smoke where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n",
            "import Lake\nopen Lake DSL\npackage demo\n@[default_target] abbrev opts : Array LeanOption := #[⟨`autoImplicit, false⟩]\nlean_lib Smoke where\n  leanOptions := opts\n",
        ] {
            assert!(!lakefile_is_plain(smuggled), "{smuggled}");
            fs::write(&lf, smuggled).unwrap();
            assert!(parse_lakefile_lean(&dir, &lf, true).is_err(), "{smuggled}");
            assert!(parse_lakefile_lean(&dir, &lf, false).is_err(), "{smuggled}");
        }

        // 4. Shadowing / duplicate identifier collisions between `abbrev`/`def` and `input_dir`,
        //    `input_file`, or `lean_lib` (in either order), as well as scoped `needs` shadowing or
        //    forward `needs` references, fail closed.
        for shadowed in [
            "import Lake\nopen Lake DSL\nabbrev opts : Array LeanOption := #[⟨`autoImplicit, false⟩]\npackage demo\ninput_dir opts where\n  path := \"Data\"\nlean_lib Smoke where\n  leanOptions := opts\n",
            "import Lake\nopen Lake DSL\npackage demo\ninput_file opts where\n  path := \"spec.json\"\nabbrev opts : Array LeanOption := #[⟨`autoImplicit, false⟩]\nlean_lib Smoke where\n  leanOptions := opts\n",
            "import Lake\nopen Lake DSL\nabbrev Smoke : Array LeanOption := #[⟨`autoImplicit, false⟩]\npackage demo\nlean_lib Smoke where\n  leanOptions := Smoke\n",
            "import Lake\nopen Lake DSL\npackage demo\nabbrev smokeSources : Nat := 1\ninput_dir smokeSources where\n  path := \"Data\"\nlean_lib Smoke where\n  needs := #[smokeSources]\n",
            "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\ninput_dir otherSources where\n  path := \"Data\"\nnamespace N\nabbrev smokeSources := otherSources\nlean_lib Smoke where\n  needs := #[smokeSources]\nend N\n",
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib Smoke where\n  needs := #[smokeSources]\ninput_dir smokeSources where\n  path := \"Data\"\n",
        ] {
            fs::write(&lf, shadowed).unwrap();
            for is_root in [true, false] {
                assert!(
                    parse_lakefile_lean(&dir, &lf, is_root).is_err(),
                    "is_root={is_root}: {shadowed}"
                );
            }
        }

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_portable_compiler_and_hybrid_lake_keys() -> Result<()> {
        let _guard = native_build_env_guard();
        let dir = make_temp_test_dir("hybrid_lake");
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(dir.join("A.lean"), "def answer : Nat := 42\n")?;
        fs::write(dir.join("payload"), "first")?;
        fs::write(dir.join("native.a"), "!<arch>\n")?;
        fs::write(dir.join("lakefile.lean"), "import Lake\nopen Lake DSL\nopen System (FilePath)\npackage hybrid\ntarget generated pkg : FilePath := do\n  inputTextFile (pkg.dir / \"payload\")\nextern_lib libnative pkg := do\n  inputTextFile (pkg.dir / \"native.a\")\n@[default_target]\nlean_lib A\n")?;
        let cfg = resolve_project_config(&dir)?;
        assert!(cfg.root_pkg.extern_libs[0].static_artifact_blake3.is_some());
        let dag = build_module_dag(&cfg, &[])?;
        let node = &dag.nodes["A"];
        let key = compute_module_cas_key(&cfg, node, &[], false)?;
        let mut relocated = cfg.clone();
        relocated.lean_bin = dir.join("relocated-lean");
        fs::copy(&cfg.lean_bin, &relocated.lean_bin)?;
        assert_eq!(key, compute_module_cas_key(&relocated, node, &[], false)?);
        fs::write(&relocated.lean_bin, b"different compiler")?;
        assert_ne!(key, compute_module_cas_key(&relocated, node, &[], false)?);
        fs::write(dir.join("payload"), "second")?;
        let changed = resolve_project_config(&dir)?;
        let changed_dag = build_module_dag(&changed, &[])?;
        assert_ne!(
            key,
            compute_module_cas_key(&changed, &changed_dag.nodes["A"], &[], false)?
        );
        assert!(workspace_lake_inputs_digest(&cfg).is_err());
        assert!(compute_module_cas_key(&cfg, node, &[], false).is_err());
        assert!(!workspace_lake_inputs_digest(&changed)?.is_empty());
        assert!(resolve_project_config_with_trust(&dir, true).is_err());
        let changed_key = compute_module_cas_key(&changed, &changed_dag.nodes["A"], &[], false)?;
        fs::write(dir.join("native.a"), "!<arch>\nchanged")?;
        let native_changed = resolve_project_config(&dir)?;
        let native_dag = build_module_dag(&native_changed, &[])?;
        assert_ne!(
            changed_key,
            compute_module_cas_key(&native_changed, &native_dag.nodes["A"], &[], false)?
        );
        fs::write(dir.join("lakefile.lean"), "import Lake\nopen Lake DSL\npackage hybrid\nextern_lib libnative pkg := do\n  inputTextFile (pkg.dir / \"native.a\")\n")?;
        let bare_cfg = resolve_project_config(&dir)?;
        let bare_dag = build_module_dag(&bare_cfg, &[])?;
        assert_eq!(bare_dag.nodes["A"].extern_lib_digests.len(), 1);
        fs::write(dir.join("lakefile.lean"), "import Lake\nopen Lake DSL\nopen System (FilePath)\npackage hybrid\ntarget generated pkg : FilePath := do\n  pure (Job.pure (pkg.dir / \"missing\"))\nlean_lib A\n")?;
        assert!(resolve_project_config(&dir).is_err());
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_native_archive_linkage_dependency_closure() -> Result<()> {
        let _guard = native_build_env_guard();
        let dir = make_temp_test_dir("native_archive_closure");
        for (name, source) in [
            ("app", "import Dep\ndef app := dep\n"),
            ("dep", "import Leaf\ndef dep := leaf\n"),
            ("leaf", "def leaf := 1\n"),
            ("unrelated", "def unrelated := 2\n"),
        ] {
            let root = dir.join(name);
            fs::create_dir_all(&root)?;
            fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
            let module = match name {
                "app" => "App",
                "dep" => "Dep",
                "leaf" => "Leaf",
                _ => "Unrelated",
            };
            fs::write(root.join(format!("{module}.lean")), source)?;
            fs::write(root.join("native.a"), b"!<arch>\n")?;
            let requires = if name == "app" {
                "require dep from \"../dep\"\nrequire leaf from \"../leaf\"\nrequire unrelated from \"../unrelated\"\n"
            } else if name == "dep" {
                "require leaf from \"../leaf\"\n"
            } else {
                ""
            };
            fs::write(root.join("lakefile.lean"), format!("import Lake\nopen Lake DSL\npackage {name}\n{requires}extern_lib native_ext pkg := do\n  inputTextFile (pkg.dir / \"native.a\")\nlean_lib {module}\n"))?;
        }
        resolve_project_config(&dir.join("app"))?;
        let cfg = resolve_project_config(&dir.join("app"))?;
        let dag = build_module_dag(
            &cfg,
            &["+App:dynlib".into(), "@unrelated/+Unrelated:dynlib".into()],
        )?;
        let expected = BTreeSet::from([
            dir.join("app").canonicalize()?,
            dir.join("dep").canonicalize()?,
            dir.join("leaf").canonicalize()?,
        ]);
        assert_eq!(
            native_link_package_roots(&dag, &module_dynlib_so_path(&dag.nodes["App"]).unwrap())?,
            expected
        );
        let shared = build_module_dag(
            &cfg,
            &["App:shared".into(), "@unrelated/Unrelated:shared".into()],
        )?;
        let sl = shared
            .shared_libs
            .iter()
            .find(|s| s.pkg_root == cfg.root_pkg.pkg_root)
            .unwrap();
        assert_eq!(native_link_package_roots(&shared, &sl.path)?, expected);
        assert!(build_module_dag(&cfg, &["native_ext".into()])?
            .nodes
            .is_empty());
        assert!(build_module_dag(&cfg, &["native_ext:bogus".into()]).is_err());
        fs::write(dir.join("unrelated/native.a"), b"invalid unrelated archive")?;
        let mut link_cfg = cfg.clone();
        let unrelated = link_cfg
            .dep_pkgs
            .iter_mut()
            .find(|p| p.base_name == "unrelated")
            .unwrap();
        unrelated.extern_libs[0].static_artifact_blake3 = Some(
            blake3::hash(b"invalid unrelated archive")
                .to_hex()
                .to_string(),
        );
        fs::write(
            dir.join("entry.c"),
            "int native_link_entry(void) { return 42; }\n",
        )?;
        let object = dir.join("entry.o");
        let (cc, _cflags, _link_flags, _toolchain_native, _custom_cc) = lake_cc_and_flags(&cfg)?;
        let status = Command::new(&cc)
            .args(["-fPIC", "-c"])
            .arg(dir.join("entry.c"))
            .arg("-o")
            .arg(&object)
            .status()?;
        anyhow::ensure!(
            status.success(),
            "Failed to compile linkage regression object"
        );
        fs::write(
            dir.join("entry.o.hash"),
            format!("{:016x}", lake_hash_bytes(&fs::read(&object)?)),
        )?;
        build_shared_object(
            &link_cfg,
            &shared,
            &sl.path,
            std::slice::from_ref(&object),
            &[],
        )?;
        build_shared_object(
            &link_cfg,
            &dag,
            &module_dynlib_so_path(&dag.nodes["App"]).unwrap(),
            std::slice::from_ref(&object),
            &[],
        )?;
        fs::write(dir.join("leaf/native.a"), b"invalid required archive")?;
        let leaf = link_cfg
            .dep_pkgs
            .iter_mut()
            .find(|p| p.base_name == "leaf")
            .unwrap();
        leaf.extern_libs[0].static_artifact_blake3 = Some(
            blake3::hash(b"invalid required archive")
                .to_hex()
                .to_string(),
        );
        assert!(build_shared_object(&link_cfg, &shared, &sl.path, &[object], &[]).is_err());
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_lean_sys_native_recipe_materialization() -> Result<()> {
        let _guard = native_build_env_guard();
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../lean-sys");
        let dir = make_temp_test_dir("lean_sys_native_recipe");
        fs::create_dir_all(dir.join("c"))?;
        if fixture.join("lakefile.lean").is_file() {
            fs::copy(fixture.join("lakefile.lean"), dir.join("lakefile.lean"))?;
            fs::copy(fixture.join("lean-toolchain"), dir.join("lean-toolchain"))?;
            fs::copy(
                fixture.join("c/lean_sys_shim.c"),
                dir.join("c/lean_sys_shim.c"),
            )?;
            for entry in walkdir::WalkDir::new(fixture.join("LeanSys")) {
                let entry = entry?;
                let dest = dir.join(entry.path().strip_prefix(&fixture)?);
                if entry.file_type().is_dir() {
                    fs::create_dir_all(dest)?;
                } else if entry.path().extension().is_some_and(|e| e == "lean") {
                    fs::copy(entry.path(), dest)?;
                }
            }
            fs::copy(fixture.join("LeanSys.lean"), dir.join("LeanSys.lean"))?;
        } else {
            let repo_tc = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/lean-toolchain");
            fs::copy(repo_tc, dir.join("lean-toolchain"))?;
            fs::write(
                dir.join("lakefile.lean"),
                "import Lake\nopen Lake DSL\nopen System (FilePath)\n\npackage «lean-sys» where\n  version := v!\"0.1.0\"\n\ntarget lean_sys_shim_o pkg : FilePath := do\n  let oFile := pkg.buildDir / \"c\" / \"lean_sys_shim.o\"\n  let srcJob ← inputTextFile <| pkg.dir / \"c\" / \"lean_sys_shim.c\"\n  let leanIncludeDir ← getLeanIncludeDir\n  buildO oFile srcJob #[\"-I\", leanIncludeDir.toString] #[\"-O3\", \"-fPIC\"] \"cc\"\n\nextern_lib liblean_sys_shim pkg := do\n  let shimO ← lean_sys_shim_o.fetch\n  let name := nameToStaticLib \"lean_sys_shim\"\n  buildStaticLib (pkg.staticLibDir / name) #[shimO]\n\n@[default_target]\nlean_lib «LeanSys» where\n  roots := #[`LeanSys]\n  precompileModules := false\n\n@[default_target]\nlean_exe «lean-sys-core» where\n  root := `LeanSys.Core\n  supportInterpreter := false\n",
            )?;
            fs::write(
                dir.join("c/lean_sys_shim.c"),
                "#include <lean/lean.h>\nlean_obj_res leansys_ping(lean_obj_arg w) { return lean_io_result_mk_ok(lean_box(0)); }\n",
            )?;
            fs::create_dir_all(dir.join("LeanSys/Contracts"))?;
            fs::write(
                dir.join("LeanSys/Contracts/MetaGate.lean"),
                "namespace LeanSys.Contracts\ndef metaGateOk : Bool := true\nend LeanSys.Contracts\n",
            )?;
            fs::write(
                dir.join("LeanSys/Posix.lean"),
                "namespace LeanSys.Posix\n@[extern \"leansys_ping\"] opaque rawPing : IO Unit\nend LeanSys.Posix\n",
            )?;
            fs::write(
                dir.join("LeanSys/Core.lean"),
                "import LeanSys.Posix\ndef main : IO Unit := LeanSys.Posix.rawPing\n",
            )?;
            fs::write(
                dir.join("LeanSys.lean"),
                "import LeanSys.Contracts.MetaGate\nimport LeanSys.Posix\n",
            )?;
        }
        let cfg = resolve_project_config(&dir)?;
        let ext = &cfg.root_pkg.extern_libs[0];
        assert!(ext.static_artifact_path.as_ref().unwrap().is_file());
        assert!(ext.static_artifact_blake3.is_some());
        assert!(cfg
            .root_pkg
            .inputs
            .iter()
            .any(|i| i.name == "lean_sys_shim_o"));
        validate_materialized_artifacts(&cfg)?;
        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        let report = build_project_modules_native(
            &mut store,
            &dir,
            &["+LeanSys.Contracts.MetaGate".into()],
            "trusted",
            0,
            false,
            false,
            None,
        )?;
        assert!(report.modules_compiled > 0);
        assert!(dir
            .join(".lake/build/lib/lean/LeanSys/Contracts/MetaGate.olean")
            .is_file());
        let error = build_project_modules_native(
            &mut store,
            &dir,
            &["LeanSys".into()],
            "trusted",
            0,
            false,
            false,
            None,
        )
        .unwrap_err()
        .to_string();
        assert!(
            error.contains("LeanSys.Posix") && error.contains("forbidden"),
            "{error}"
        );
        assert!(
            !resolve_requested_exe_link_targets(&cfg, &["lean-sys-core".into()])
                .0
                .is_empty()
        );
        let exe_error = build_project_modules_native(
            &mut store,
            &dir,
            &["lean-sys-core".into()],
            "trusted",
            0,
            false,
            false,
            None,
        )
        .unwrap_err()
        .to_string();
        assert!(
            exe_error.contains("LeanSys.Posix") && exe_error.contains("forbidden"),
            "{exe_error}"
        );
        assert!(!dir.join(".lake/build/bin/lean-sys-core").exists());
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_lean_project_untrusted_accepts_prebuilt_extern_lib() {
        let lean_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean");
        let archive = lean_dir.join(".lake/packages/lean-sys/.lake/build/lib/liblean_sys_shim.a");
        if archive.is_file() {
            let cfg = resolve_project_config_with_trust(&lean_dir, true).unwrap();
            let dag = build_module_dag_with_trust(&cfg, &[], true).unwrap();
            assert!(!workspace_lake_inputs_digest(&cfg).unwrap().is_empty());
            let leaf = dag
                .nodes
                .values()
                .find(|n| n.direct_dag_deps.is_empty() && n.external_olean_deps.is_empty())
                .unwrap();
            assert!(!compute_module_cas_key(&cfg, leaf, &[], false)
                .unwrap()
                .is_empty());
        }
    }

    #[test]
    fn test_dynamic_lakefile_fails_closed_with_precise_diagnostics() {
        let dir = make_temp_test_dir("fail_closed");
        // 1. Dynamic `meta if` in lakefile.lean
        let dyn_if = "import Lake\nopen Lake DSL\npackage p\nmeta if true then\n  lean_lib A\n";
        let lf = dir.join("lakefile.lean");
        fs::write(&lf, dyn_if).unwrap();
        let err1 = parse_lakefile_lean(&dir, &lf, true)
            .unwrap_err()
            .to_string();
        assert!(err1.contains("meta if") && err1.contains("fail-closed"));
        // 2. Dynamic `run_cmd` in lakefile.lean
        let dyn_cmd = "import Lake\nopen Lake DSL\npackage p\nrun_cmd IO.println \"hi\"\n";
        fs::write(&lf, dyn_cmd).unwrap();
        let err2 = parse_lakefile_lean(&dir, &lf, true)
            .unwrap_err()
            .to_string();
        assert!(err2.contains("run_cmd") && err2.contains("fail-closed"));
        // 3. Unbuilt dynamic `extern_lib` in root lakefile.lean
        let dyn_ext = "import Lake\nopen Lake DSL\npackage p\nextern_lib libfoo pkg := do\n  pure ()\nlean_lib A\n";
        fs::write(&lf, dyn_ext).unwrap();
        assert_eq!(
            parse_lakefile_lean(&dir, &lf, true).unwrap().extern_libs[0].name,
            "libfoo"
        );
        // 4. Custom `target ... := do` in root lakefile.lean
        let dyn_tgt = "import Lake\nopen Lake DSL\npackage p\ntarget custom_c pkg : FilePath := do\n  pure ()\nlean_lib A\n";
        fs::write(&lf, dyn_tgt).unwrap();
        assert_eq!(
            parse_lakefile_lean(&dir, &lf, true).unwrap().custom_targets,
            ["custom_c"]
        );
        // 5. Unsafe `--load-dynlib` in `moreLeanArgs` in lakefile.toml
        let dyn_toml = "name = \"p\"\nmoreLeanArgs = [\"--load-dynlib=evil.so\"]\n[[lean_lib]]\nname = \"A\"\n";
        let tf = dir.join("lakefile.toml");
        fs::write(&tf, dyn_toml).unwrap();
        let err5 = parse_lakefile_toml(&dir, &tf, true)
            .unwrap_err()
            .to_string();
        assert!(err5.contains("--load-dynlib") && err5.contains("fail-closed"));
        let _ = fs::remove_dir_all(&dir);
    }
    #[test]
    fn test_dag_cycle_and_missing_module_detection() {
        let dir = make_temp_test_dir("dag_cycle_missing");
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"cyc\"\n[[lean_lib]]\nname = \"Cyc\"\nglobs = [\"Cyc.*\"]\n",
        )
        .unwrap();
        fs::create_dir_all(dir.join("Cyc")).unwrap();
        fs::write(dir.join("Cyc/A.lean"), "import Cyc.B\ndef a : Nat := 1\n").unwrap();
        fs::write(dir.join("Cyc/B.lean"), "import Cyc.C\ndef b : Nat := 2\n").unwrap();
        fs::write(dir.join("Cyc/C.lean"), "import Cyc.A\ndef c : Nat := 3\n").unwrap();
        let cfg = resolve_project_config(&dir).unwrap();
        let cyc_err = build_module_dag(&cfg, &[]).unwrap_err().to_string();
        assert!(
            cyc_err.contains("Module import cycle detected:")
                && cyc_err.contains("Cyc.A")
                && cyc_err.contains("Cyc.B")
                && cyc_err.contains("Cyc.C"),
            "unexpected cycle error: {}",
            cyc_err
        );
        // Replace cycle with missing import
        fs::write(
            dir.join("Cyc/C.lean"),
            "import NonExistent.GhostMod\ndef c : Nat := 3\n",
        )
        .unwrap();
        let miss_err = build_module_dag(&cfg, &[]).unwrap_err().to_string();
        assert!(
            miss_err.contains("Missing module `NonExistent.GhostMod`")
                && miss_err.contains("Cyc.C"),
            "unexpected missing error: {}",
            miss_err
        );
        // Unsupported facet check
        fs::write(dir.join("Cyc/C.lean"), "def c : Nat := 3\n").unwrap();
        let facet_err = build_module_dag(&cfg, &["Cyc:unknown_facet".to_string()])
            .unwrap_err()
            .to_string();
        assert!(facet_err.contains("Unsupported target facet `:unknown_facet`"));
        let _ = fs::remove_dir_all(&dir);
    }

    /// P7 (#436): `turbo-lean build <Lib>` must not schedule a native compile of a git-pinned
    /// dependency whose checkout lies outside the project root (a symlinked `.lake/packages`
    /// entry into another checkout): publishing would rewrite `.olean`/`.trace` files and take
    /// `.turbo_publish.lock` in that foreign checkout. Such a dependency is adopted read-only or
    /// the DAG build fails naming the `lake build` command that refreshes it. A pinned clone
    /// under the project root keeps building, like Lake builds it.
    #[cfg(unix)]
    #[test]
    fn test_dag_build_scope_refuses_stale_git_pinned_dep_outside_project_root() -> Result<()> {
        let dir = make_temp_test_dir("dag_build_scope_pinned_dep");
        let origin = dir.join("other_checkout/dep_pin");
        let proj = dir.join("proj");
        fs::create_dir_all(&origin)?;
        fs::create_dir_all(&proj)?;
        let tc = "leanprover/lean4:v4.35.0\n";
        fs::write(origin.join("lean-toolchain"), tc)?;
        fs::write(proj.join("lean-toolchain"), tc)?;
        fs::write(
            origin.join("lakefile.toml"),
            "name = \"dep_pin\"\ndefaultTargets = [\"DepPin\"]\n[[lean_lib]]\nname = \"DepPin\"\n",
        )?;
        fs::write(origin.join("DepPin.lean"), "def depPinVal : Nat := 7\n")?;
        let git_bin = std::env::var_os("TURBO_LEAN_GIT")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("git"));
        for args in [
            vec!["init"],
            vec!["config", "user.email", "t@e.com"],
            vec!["config", "user.name", "T"],
            vec!["add", "."],
            vec!["commit", "-m", "init"],
        ] {
            let st = Command::new(&git_bin)
                .args(&args)
                .current_dir(&origin)
                .status()?;
            anyhow::ensure!(st.success(), "git {args:?} failed in dep origin");
        }
        let rev_out = Command::new(&git_bin)
            .args(["rev-parse", "HEAD"])
            .current_dir(&origin)
            .output()?;
        anyhow::ensure!(rev_out.status.success());
        let rev = String::from_utf8(rev_out.stdout)?.trim().to_string();
        fs::write(
            proj.join("lakefile.toml"),
            format!(
                "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"dep_pin\"\ngit = {:?}\nrev = {:?}\n[[lean_lib]]\nname = \"App\"\n",
                origin.to_string_lossy(),
                rev
            ),
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            serde_json::json!({
                "version": "1.1.0",
                "packagesDir": ".lake/packages",
                "packages": [{
                    "type": "git",
                    "scope": "",
                    "name": "dep_pin",
                    "manifestFile": "lake-manifest.json",
                    "rev": rev,
                    "inherited": false,
                    "configFile": "lakefile.toml",
                    "inputRev": rev,
                    "url": origin.to_string_lossy()
                }]
            })
            .to_string(),
        )?;
        fs::write(
            proj.join("App.lean"),
            "import DepPin\ntheorem app_ok : depPinVal = 7 := rfl\n",
        )?;
        fs::create_dir_all(proj.join(".lake/packages"))?;
        std::os::unix::fs::symlink(&origin, proj.join(".lake/packages/dep_pin"))?;

        let cfg = resolve_project_config(&proj)?;
        // 1. `build <Lib>` (trusted, no prebuilt adoption) fails closed instead of scheduling a
        //    native compile that would publish into the other checkout. The remedy named by the
        //    refusal is decided on CANONICAL paths (after the #436 follow-up
        //    canonicalized the gate's compare): this entry is a SYMLINK to the other checkout, so
        //    running `lake build +DepPin` from the project root would write through the symlink —
        //    the very publish this gate stops — and the message must instead point at the
        //    checkout's own workspace. No marker hint is suggested for THIS shape (an in-tree
        //    packages dir with one symlinked entry): per `non_owned_dep_refresh_remedy`'s
        //    contract, no owner marker clears the gate here, and the packages-dir marker hint
        //    belongs to the relocated-packages-dir shape that case 4 below pins.
        let err = build_module_dag(&cfg, &["App".to_string()])
            .expect_err("stale pinned out-of-tree dep must not become a DAG build node")
            .to_string();
        assert!(
            err.contains("outside the project root")
                && err.contains("own workspace (`lake build` in ")
                && !err.contains(".turbo-lean-packages-owner")
                && !err.contains("`lake build +DepPin` from the project root")
                && !err.contains("adopted read-only"),
            "unexpected error: {err}"
        );
        // 2. The statement path (`allow_prebuilt_dep_pkgs = true`, `check`) keeps today's shape.
        let stmt_dag = build_module_dag_for_trusted_statement(&cfg, &["App".to_string()])?;
        assert!(stmt_dag.nodes.contains_key("DepPin"));
        // 3. Control: the same pinned clone under the project root keeps building like Lake.
        fs::remove_file(proj.join(".lake/packages/dep_pin"))?;
        let clone_st = Command::new(&git_bin)
            .args(["clone", "--quiet"])
            .arg(&origin)
            .arg(proj.join(".lake/packages/dep_pin"))
            .status()?;
        anyhow::ensure!(clone_st.success(), "git clone into packages dir failed");
        let cfg_in = resolve_project_config(&proj)?;
        let dag_in = build_module_dag(&cfg_in, &["App".to_string()])?;
        assert!(dag_in.nodes.contains_key("DepPin"));
        // 4. A packages dir that is ITSELF a symlink to another volume is exempt only with
        //    PROOF of ownership: turbo-lean cannot tell a private RAM-disk relocation from a
        //    packages dir several worktrees share, and the shared case is the #436 publish
        //    race. Without the owner marker (or with another project's) the gate fires; with a
        //    marker recording THIS project's canonical root, the relocation counts as its own.
        let ext_pkgs = dir.join("ext_pkgs");
        fs::rename(proj.join(".lake/packages"), &ext_pkgs)?;
        std::os::unix::fs::symlink(&ext_pkgs, proj.join(".lake/packages"))?;
        let cfg_ext = resolve_project_config(&proj)?;
        let err = build_module_dag(&cfg_ext, &["App".to_string()])
            .expect_err("an unproven shared packages dir must not be exempt from the gate")
            .to_string();
        assert!(err.contains("outside the project root"), "{err}");
        fs::write(
            ext_pkgs.join(".turbo-lean-packages-owner"),
            format!("{}\n", dir.join("elsewhere").display()),
        )?;
        let cfg_foreign = resolve_project_config(&proj)?;
        assert!(build_module_dag(&cfg_foreign, &["App".to_string()]).is_err());
        fs::write(
            ext_pkgs.join(".turbo-lean-packages-owner"),
            format!("{}\n", proj.canonicalize()?.display()),
        )?;
        let cfg_owned = resolve_project_config(&proj)?;
        let dag_ext = build_module_dag(&cfg_owned, &["App".to_string()])?;
        assert!(dag_ext.nodes.contains_key("DepPin"));
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    /// L299 (#299, module resolution): import edges resolve like Lake's `Package.findModule?`
    /// (libraries only), never like `findTargetModule?` (executables first), so a module that is
    /// solely a `lean_exe` root is not importable and the DAG fails where Lake fails.
    #[test]
    fn test_l299_import_lookup_skips_exe_roots_like_find_module() -> Result<()> {
        let dir = make_temp_test_dir("l299_find_module");
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"app\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\n[[lean_exe]]\nname = \"runner\"\nroot = \"Main\"\n",
        )?;
        fs::write(dir.join("Main.lean"), "def main : IO Unit := pure ()\n")?;
        fs::write(dir.join("App.lean"), "import Main\ndef app : Nat := 1\n")?;
        let cfg = resolve_project_config(&dir)?;
        let pkg = &cfg.root_pkg;
        assert_eq!(
            resolve_module_in_package(pkg, true, "Main").map(|s| s.target_name),
            Some("runner".to_string())
        );
        assert!(resolve_importable_module_in_package(pkg, true, "Main").is_none());
        let err = build_module_dag(&cfg, &["App".to_string()])
            .expect_err("a module that is only an exe root must not be importable")
            .to_string();
        assert!(err.contains("Missing module `Main`"), "{err}");
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    /// L299 (#299, module resolution): glob-expanded modules take their `leanOptions` from the
    /// library module resolution picks (Lake's `findModule?`, the LAST library that can build
    /// the module), not from whichever library's glob expanded them.
    #[test]
    fn test_l299_glob_expansion_routes_options_through_module_resolution() -> Result<()> {
        let dir = make_temp_test_dir("l299_glob_options");
        fs::create_dir_all(dir.join("Shared"))?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage overl\nlean_lib First where\n  globs := #[`Shared.+]\n  leanOptions := #[⟨`linter.first, true⟩]\nlean_lib Second where\n  globs := #[`Shared.+]\n  leanOptions := #[⟨`linter.second, true⟩]\n",
        )?;
        fs::write(dir.join("Shared/M.lean"), "def m : Nat := 1\n")?;
        let cfg = resolve_project_config(&dir)?;
        let dag = build_module_dag(&cfg, &["First".to_string()])?;
        let node = &dag.nodes["Shared.M"];
        // The needs-trace attribution stays the requested library's...
        assert_eq!(node.target_name, "First");
        // ...while the options are the owning (last) library's, like Lake compiles it.
        let second = LeanName::from_str_to_name("linter.second")?;
        let first = LeanName::from_str_to_name("linter.first")?;
        assert_eq!(
            node.lean_options.get(&second),
            Some(&LeanOptionValue::Bool(true))
        );
        assert!(!node.lean_options.contains_key(&first));
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    /// L299 fix-forward (#299): a glob-expanded module inherits the fail-closed `unsupported`
    /// flags of the library module resolution assigns it to, not only its options: an owning
    /// library turbo-lean cannot build like Lake must stop the build even when the expanding
    /// library is clean.
    #[test]
    fn test_l299_glob_expansion_inherits_owner_unsupported_gate() -> Result<()> {
        let dir = make_temp_test_dir("l299_owner_unsupported");
        let proj = dir.join("proj");
        let dep = proj.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep.join("Shared"))?;
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(dep.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dep.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage dep_pkg\ntarget helperT pkg : Unit := do\n  return .nil\nlean_lib First where\n  globs := #[`Shared.+]\nlean_lib Second where\n  globs := #[`Shared.+]\n  needs := #[helperT]\n",
        )?;
        fs::write(dep.join("Shared/M.lean"), "def m : Nat := 1\n")?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"dep_pkg\"\npath = \".lake/packages/dep_pkg\"\n[[lean_lib]]\nname = \"App\"\n",
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            r#"{"version": "1.1.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "scope": "", "name": "dep_pkg", "inherited": false, "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.lean"}]}"#,
        )?;
        fs::write(proj.join("App.lean"), "def app : Nat := 2\n")?;
        let cfg = resolve_project_config(&proj)?;
        // `Second` (the owner by `findModule?`) carries `unsupported` (a custom-target `needs`);
        // expanding `First`'s glob must not launder `Shared.M` past the fail-closed gate.
        let err = build_module_dag(&cfg, &["@dep_pkg/First".to_string()])
            .expect_err("owner-unsupported module must not build through a clean expander")
            .to_string();
        assert!(err.contains("like Lake"), "{err}");
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    /// L299 fix-forward (#299): a module the root package OWNS (a library's globs select it)
    /// whose source file is missing must fail like Lake, never resolve to a same-named module
    /// in a dependency package one lookup level further out.
    #[test]
    fn test_l299_owned_module_with_missing_source_never_resolves_in_dep_packages() -> Result<()> {
        let dir = make_temp_test_dir("l299_owned_missing_dep");
        let proj = dir.join("proj");
        let dep = proj.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep.join("Shared"))?;
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(dep.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dep.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepShared\"\nroots = []\nglobs = [\"Shared.+\"]\n",
        )?;
        fs::write(dep.join("Shared/M.lean"), "def m : Nat := 1\n")?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"dep_pkg\"\npath = \".lake/packages/dep_pkg\"\n[[lean_lib]]\nname = \"App\"\n[[lean_lib]]\nname = \"Owner\"\nroots = []\nglobs = [\"Shared.+\"]\n",
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            r#"{"version": "1.1.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "scope": "", "name": "dep_pkg", "inherited": false, "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml"}]}"#,
        )?;
        fs::write(proj.join("App.lean"), "import Shared.M\ndef app : Nat := m\n")?;
        let cfg = resolve_project_config(&proj)?;
        // Root `Owner` owns `Shared.M`, but `Shared/M.lean` is missing in the root package.
        let err = build_module_dag(&cfg, &["App".to_string()])
            .expect_err("an owned module with a missing source must not resolve in a dependency")
            .to_string();
        assert!(err.contains("Shared.M") && err.contains("missing"), "{err}");
        // Control: once the root file exists, the root library owns and builds it.
        fs::create_dir_all(proj.join("Shared"))?;
        fs::write(proj.join("Shared/M.lean"), "def m : Nat := 3\n")?;
        let cfg2 = resolve_project_config(&proj)?;
        let dag = build_module_dag(&cfg2, &["App".to_string()])?;
        assert!(dag.nodes["Shared.M"].is_root_pkg);
        // #299: a dependency that OWNS the module with a MISSING source counts toward
        // the ambiguity check. Lake's `findSomeRev?` may pick it and fail, so one Found sibling
        // must not resolve silently when another dependency owns the name without its source.
        fs::remove_file(proj.join("Shared/M.lean"))?;
        fs::remove_file(dep.join("Shared/M.lean"))?;
        let dep2 = proj.join(".lake/packages/dep2_pkg");
        fs::create_dir_all(dep2.join("Shared"))?;
        fs::write(dep2.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dep2.join("lakefile.toml"),
            "name = \"dep2_pkg\"\n[[lean_lib]]\nname = \"Dep2Shared\"\nroots = []\nglobs = [\"Shared.+\"]\n",
        )?;
        fs::write(dep2.join("Shared/M.lean"), "def m : Nat := 1\n")?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"dep_pkg\"\npath = \".lake/packages/dep_pkg\"\n[[require]]\nname = \"dep2_pkg\"\npath = \".lake/packages/dep2_pkg\"\n[[lean_lib]]\nname = \"App\"\n",
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            r#"{"version": "1.1.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "scope": "", "name": "dep_pkg", "inherited": false, "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml"}, {"type": "path", "scope": "", "name": "dep2_pkg", "inherited": false, "dir": ".lake/packages/dep2_pkg", "configFile": "lakefile.toml"}]}"#,
        )?;
        let cfg3 = resolve_project_config(&proj)?;
        let err = build_module_dag(&cfg3, &["App".to_string()])
            .expect_err("an owned-but-missing dependency must count toward the ambiguity check")
            .to_string();
        assert!(err.contains("Ambiguous"), "{err}");
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    /// L299 (#299, module resolution): a matching target whose source file is missing resolves
    /// to nothing (and the build fails like Lake fails), instead of silently trying an earlier
    /// candidate Lake would never build.
    #[test]
    fn test_l299_missing_source_file_fails_instead_of_trying_earlier_candidate() {
        let dir = make_temp_test_dir("l299_missing_source");
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage miss\nlean_lib Early where\n  roots := #[`M]\nlean_lib Late where\n  srcDir := \"late\"\n  roots := #[`M]\n",
        )
        .unwrap();
        fs::write(dir.join("M.lean"), "").unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, true).unwrap();
        // `Late` (the last declaration) owns `M` like Lake's `findModule?`; its missing
        // `late/M.lean` is Lake's build-time error, never a fallback to `Early`.
        assert!(resolve_module_in_package(&pkg, true, "M").is_none());
        fs::create_dir_all(dir.join("late")).unwrap();
        fs::write(dir.join("late/M.lean"), "").unwrap();
        assert_eq!(
            resolve_module_in_package(&pkg, true, "M").map(|s| s.target_name),
            Some("Late".to_string())
        );
        let _ = fs::remove_dir_all(&dir);
    }

    /// L299 (#299, header syntax): `lake init foo.bar std.lean` emits per-segment guillemets
    /// (`lean_lib «Foo».«Bar» where`), which parse to the dotted Lake name.
    #[test]
    fn test_l299_per_segment_guillemets_in_target_header() {
        let dir = make_temp_test_dir("l299_guillemets");
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib «Foo».«Bar» where\n",
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, true).unwrap();
        assert_eq!(pkg.libs[0].name, "Foo.Bar");
        let _ = fs::remove_dir_all(&dir);
    }

    /// L299 (#299, header syntax): a dot inside a quoted target name is one atomic segment to
    /// Lake (`Name.mkSimple`), which this parser cannot represent: fail closed instead of
    /// splitting it into `Foo/Bar.lean`.
    #[test]
    fn test_l299_dots_in_quoted_target_names_fail_closed() {
        let dir = make_temp_test_dir("l299_quoted_dots");
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib \"Foo.Bar\" where\n",
        )
        .unwrap();
        assert!(parse_lakefile_lean(&dir, &lf, true).is_err());
        // The unquoted `lake init` form stays accepted.
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage \"demo\" where\nlean_lib Demo where\n",
        )
        .unwrap();
        assert_eq!(
            parse_lakefile_lean(&dir, &lf, true).unwrap().libs[0].name,
            "Demo"
        );
        // A quoted PACKAGE name with a dot stays accepted (`lake init foo.bar` emits it): a
        // package name never becomes a source path.
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage \"foo.bar\" where\nlean_lib Demo where\n",
        )
        .unwrap();
        assert_eq!(parse_lakefile_lean(&dir, &lf, true).unwrap().name, "foo.bar");
        // A quoted dotted INPUT name stays rejected: `Name.mkSimple "widget.tar"` is one
        // component to Lake, so a dotted `needs := #[widget.tar]` entry (two components, which
        // Lake would never resolve to the input) must not match it here by string equality.
        fs::write(dir.join("widget.tar"), "x").unwrap();
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage demo\ninput_file \"widget.tar\" where\n  path := \"widget.tar\"\nlean_lib Demo where\n  needs := #[widget.tar]\n",
        )
        .unwrap();
        assert!(parse_lakefile_lean(&dir, &lf, true).is_err());
        let _ = fs::remove_dir_all(&dir);
    }

    /// L299 (#299, header syntax): inline `@[default_target] lean_lib X where` and the
    /// `open Lake DSL System` word order keep a lakefile plain, so `leanOptions` elsewhere in
    /// the file still resolve (Lake accepts both).
    #[test]
    fn test_l299_inline_default_target_attribute_and_open_word_order_stay_plain() {
        let dir = make_temp_test_dir("l299_inline_attr");
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL System\npackage demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n@[default_target] lean_lib Demo where\n",
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, true).unwrap();
        assert_eq!(pkg.default_targets, vec!["Demo".to_string()]);
        assert_eq!(
            pkg.lean_options
                .get(&LeanName::from_str_to_name("autoImplicit").unwrap()),
            Some(&LeanOptionValue::Bool(false))
        );
        let _ = fs::remove_dir_all(&dir);
    }

    /// L299 (#299, header syntax): stacked target attributes on separate lines apply together;
    /// `@[test_driver]` does not clear a pending `@[default_target]`.
    #[test]
    fn test_l299_stacked_target_attributes_keep_pending_default_target() {
        let dir = make_temp_test_dir("l299_stacked_attrs");
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage demo\n@[default_target]\n@[test_driver]\nlean_lib A where\nlean_lib B where\n",
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, true).unwrap();
        assert_eq!(pkg.default_targets, vec!["A".to_string()]);
        let _ = fs::remove_dir_all(&dir);
    }

    /// L299 (#299, dependency shadowing): a dependency lakefile that declares a dotted helper
    /// (which could shadow `Glob` constructor spellings) fails closed for constructor-named
    /// globs instead of reading them literally; backtick-literal globs cannot be shadowed.
    #[test]
    fn test_l299_shadowable_glob_constructors_fail_closed_in_dep_packages() {
        let dir = make_temp_test_dir("l299_glob_shadow");
        let lf = dir.join("lakefile.lean");
        let shadowed = "import Lake\nopen Lake DSL\npackage dep\ndef Glob.submodules (n : Lake.Glob) : Lake.Glob := n\nlean_lib Dep where\n  globs := #[Glob.submodules `Wrong]\n";
        fs::write(&lf, shadowed).unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
        assert!(
            pkg.libs[0].unsupported.is_some() || pkg.unsupported.is_some(),
            "shadowable Glob constructor accepted literally"
        );
        // A plain dependency lakefile keeps constructor globs...
        let plain = "import Lake\nopen Lake DSL\npackage dep\nlean_lib Dep where\n  globs := #[Glob.submodules `Right]\n";
        fs::write(&lf, plain).unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
        assert!(pkg.libs[0].unsupported.is_none() && pkg.unsupported.is_none());
        assert_eq!(
            pkg.libs[0].globs,
            vec![GlobSpec::Submodules("Right".to_string())]
        );
        // ...and backtick-literal globs survive beside a dotted helper, even when the literal
        // NAME contains "Glob." as a segment (a name literal is not a constructor reference).
        for globs in ["#[`Dep.+]", "#[`Dep.Glob.+]"] {
            let literal = format!("import Lake\nopen Lake DSL\npackage dep\ndef Glob.submodules (n : Lake.Glob) : Lake.Glob := n\nlean_lib Dep where\n  globs := {globs}\n");
            fs::write(&lf, &literal).unwrap();
            let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
            assert!(pkg.libs[0].unsupported.is_none(), "{globs}");
        }
        let _ = fs::remove_dir_all(&dir);
    }

    /// L299 (#299, accepted-but-invalid forms): Lake 4.35 rejects plain `(k, v)` tuples and
    /// explicit `LeanOption.mk` applications in `leanOptions`: the root package fails closed at
    /// parse time, a dependency records `unsupported` so only its own modules fail (a dependency
    /// must not refuse the whole workspace configuration). The `⟨k, v⟩` form stays. The
    /// bullet's third form, an untyped `abbrev xs := #[⟨...⟩]`, stays accepted: Mathlib's real
    /// lakefile binds `mathlibLeanOptions` that way on its pinned toolchain
    /// (`test_computed_lean_options_mathlib_lakefile`), and refusing valid input is the failure
    /// mode #299 asks to avoid.
    #[test]
    fn test_l299_prod_tuple_and_lean_option_mk_fail_closed_untyped_abbrev_accepted() {
        let dir = make_temp_test_dir("l299_invalid_forms");
        let lf = dir.join("lakefile.lean");
        let parse = |src: &str| {
            fs::write(&lf, src).unwrap();
            parse_lakefile_lean(&dir, &lf, false)
        };
        let lib = |expr: &str, prelude: &str| {
            format!("import Lake\nopen Lake DSL\n{prelude}package demo\nlean_lib Demo where\n  leanOptions := {expr}\n")
        };
        for e in [
            "#[(`autoImplicit, false)]",
            "#[LeanOption.mk `autoImplicit false]",
            // Qualified spellings are the same rejected form.
            "#[Lake.LeanOption.mk `autoImplicit false]",
            "#[Lean.LeanOption.mk `autoImplicit false]",
        ] {
            let dep = parse(&lib(e, "")).unwrap();
            assert!(dep.libs[0].unsupported.is_some(), "{e}");
            fs::write(&lf, lib(e, "")).unwrap();
            assert!(parse_lakefile_lean(&dir, &lf, true).is_err(), "{e}");
        }
        // A parenthesized ascription is not a `(k, v)` tuple: it takes the generic fail-closed
        // error for every package (Lake would elaborate it; a named limit), never the
        // Lake-rejected class a dependency downgrades.
        assert!(parse(&lib("#[(⟨`autoImplicit, false⟩ : LeanOption)]", "")).is_err());
        // The untyped Mathlib-shaped binding keeps resolving.
        let untyped = parse(&lib("xs", "abbrev xs := #[⟨`autoImplicit, false⟩]\n")).unwrap();
        assert_eq!(
            untyped.libs[0].lean_options,
            parse_lean_options_expr("#[⟨`autoImplicit, false⟩]").unwrap()
        );
        // The forms Lake elaborates stay accepted: `⟨k, v⟩` and a typed abbrev.
        let ok = parse(&lib(
            "xs ++ #[⟨`linter.b, true⟩]",
            "abbrev xs : Array LeanOption := #[⟨`linter.a, false⟩]\n",
        ))
        .unwrap();
        assert_eq!(
            ok.libs[0].lean_options,
            parse_lean_options_expr("#[⟨`linter.a, false⟩, ⟨`linter.b, true⟩]").unwrap()
        );
        let _ = fs::remove_dir_all(&dir);
    }

    /// L299 (#299, pre-existing non-root behaviour): duplicate `lean_lib` names fail closed
    /// (Lake rejects the duplicate declaration), `meta if` fails closed instead of keeping the
    /// first branch, and TOML `buildType = "debug"` fails closed instead of silently dropping
    /// Lake's `debugAssertions`.
    #[test]
    fn test_l299_duplicate_libs_meta_if_and_toml_build_type_fail_closed() {
        let dir = make_temp_test_dir("l299_dup_metaif_buildtype");
        let lf = dir.join("lakefile.lean");
        let dup =
            "import Lake\nopen Lake DSL\npackage dep\nlean_lib Demo where\nlean_lib Demo where\n";
        fs::write(&lf, dup).unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
        assert!(pkg.unsupported.is_some(), "duplicate lean_lib accepted");
        assert!(parse_lakefile_lean(&dir, &lf, true).is_err());
        // Cross-kind collisions are duplicate Lean declarations to Lake too.
        let dup_kinds =
            "import Lake\nopen Lake DSL\npackage dep\nlean_lib Demo where\nlean_exe Demo where\n";
        fs::write(&lf, dup_kinds).unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
        assert!(
            pkg.unsupported.is_some(),
            "lib-vs-exe name collision accepted"
        );
        assert!(parse_lakefile_lean(&dir, &lf, true).is_err());
        let meta_if = "import Lake\nopen Lake DSL\npackage dep\nmeta if true then\nlean_lib A where\nlean_lib B where\n";
        fs::write(&lf, meta_if).unwrap();
        let dep = parse_lakefile_lean(&dir, &lf, false);
        assert!(
            dep.is_err() || dep.unwrap().unsupported.is_some(),
            "`meta if` accepted"
        );
        let tf = dir.join("lakefile.toml");
        fs::write(
            &tf,
            "name = \"demo\"\nbuildType = \"debug\"\n[[lean_lib]]\nname = \"Demo\"\n",
        )
        .unwrap();
        assert!(parse_lakefile_toml(&dir, &tf, true).is_err());
        fs::write(
            &tf,
            "name = \"demo\"\nbuildType = \"release\"\n[[lean_lib]]\nname = \"Demo\"\n",
        )
        .unwrap();
        assert!(parse_lakefile_toml(&dir, &tf, true).is_ok());
        let _ = fs::remove_dir_all(&dir);
    }

    /// L299 (#299, arguments and options): TOML option values stay typed `LeanOptionValue`s end
    /// to end (a Nat is a Nat on the CLI, not a quoted string), and quoted keys parse.
    #[test]
    fn test_l299_toml_lean_option_values_stay_typed() {
        let dir = make_temp_test_dir("l299_toml_typed_options");
        let tf = dir.join("lakefile.toml");
        fs::write(
            &tf,
            "name = \"demo\"\n[leanOptions]\nmaxHeartbeats = 400000\nautoImplicit = false\nlinter.style.longFile = 1500\n[[lean_lib]]\nname = \"Demo\"\n",
        )
        .unwrap();
        let pkg = parse_lakefile_toml(&dir, &tf, true).unwrap();
        let get = |k: &str| {
            pkg.lean_options
                .get(&LeanName::from_str_to_name(k).unwrap())
                .cloned()
        };
        assert_eq!(get("maxHeartbeats"), Some(LeanOptionValue::Nat(400000)));
        assert_eq!(get("maxHeartbeats").unwrap().as_cli_flag_value(), "400000");
        assert_eq!(get("autoImplicit"), Some(LeanOptionValue::Bool(false)));
        assert_eq!(
            get("linter.style.longFile"),
            Some(LeanOptionValue::Nat(1500))
        );
        // A quoted TOML key is one atomic segment (`«linter.style»`), which the option
        // allowlist then refuses: strict, like the quoted-header rule.
        fs::write(
            &tf,
            "name = \"demo\"\n[leanOptions]\n\"linter.style\" = \"all\"\n[[lean_lib]]\nname = \"Demo\"\n",
        )
        .unwrap();
        assert!(parse_lakefile_toml(&dir, &tf, true).is_err());
        let _ = fs::remove_dir_all(&dir);
    }

    /// L299 (#299): root directories are also parsed with `is_root_pkg = false`
    /// (pr-verify's working-tree resolve, `try_resolve_lean_args_for_path`), so the dependency
    /// downgrade for Lake-rejected `leanOptions` entry forms must not let those paths hand out
    /// args with entries silently dropped: `optional_package_config` fails like the root parse.
    #[test]
    fn test_l299_root_as_dep_paths_reject_lake_rejected_option_entries() {
        let dir = make_temp_test_dir("l299_root_as_dep_options");
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[LeanOption.mk `autoImplicit false]\n",
        )
        .unwrap();
        fs::write(dir.join("Demo.lean"), "").unwrap();
        assert!(try_resolve_lean_args_for_path(&dir, Some(Path::new("Demo.lean"))).is_err());
        assert!(optional_package_config(&dir).is_err());
        // A clean lakefile keeps resolving through the same path.
        fs::write(
            &dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n",
        )
        .unwrap();
        assert!(try_resolve_lean_args_for_path(&dir, Some(Path::new("Demo.lean"))).is_ok());
        let _ = fs::remove_dir_all(&dir);
    }

    /// The Lake-rejected `leanOptions` downgrade is recorded in its
    /// own right, not found by scanning the shared `unsupported` reason slot afterwards. An
    /// earlier unsupported construct in the same target occupies that slot first
    /// (`unsupported_lake_field` keeps the first reason), and the refusal must still fire.
    #[test]
    fn test_l299_earlier_unsupported_reason_does_not_mask_rejected_options() {
        let dir = make_temp_test_dir("l299_masked_rejected_options");
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\nlean_lib Demo where\n  bogusUnknownField := true\n  leanOptions := #[LeanOption.mk `autoImplicit false]\n",
        )
        .unwrap();
        fs::write(dir.join("Demo.lean"), "").unwrap();
        // The earlier construct really is recorded first in the shared slot.
        let dep = resolve_package_config(&dir, false).unwrap();
        assert!(
            dep.libs[0]
                .unsupported
                .as_deref()
                .is_some_and(|w| w.contains("bogusUnknownField")),
            "fixture must occupy the shared reason slot first, or it proves nothing: {:?}",
            dep.libs[0].unsupported
        );
        assert!(
            optional_package_config(&dir).is_err(),
            "a dropped `leanOptions` entry must refuse even when an earlier reason \
             occupies the `unsupported` slot"
        );
        assert!(try_resolve_lean_args_for_path(&dir, Some(Path::new("Demo.lean"))).is_err());
        let _ = fs::remove_dir_all(&dir);
    }

    /// L299 (#299, arguments and options): the sorry-adjacent debug keys stay outside the
    /// option allowlist, whatever value they carry.
    #[test]
    fn test_l299_sorry_adjacent_option_keys_stay_outside_allowlist() {
        for key in [
            "debug.proofAsSorry",
            "debug.byAsSorry",
            "debug.terminalTacticsAsSorry",
            "weak.debug.proofAsSorry",
            "weak.debug.byAsSorry",
            "weak.debug.terminalTacticsAsSorry",
        ] {
            for val in [LeanOptionValue::Bool(true), LeanOptionValue::Bool(false)] {
                assert!(
                    !is_allowed_lean_option(&LeanName::from_str_to_name(key).unwrap(), &val),
                    "{key}"
                );
            }
        }
    }

    #[cfg(unix)]
    #[test]
    fn test_optout_module_cache_hits_preserve_existing_lake_tree() -> Result<()> {
        use crate::worktree_test_support::{snapshot, LakeTree};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = LakeTree::new("module_cas", &[("P/Fixture.lean",
            "module\n@[expose] public def value : Nat := 7\npublic theorem value_eq : value = 7 := rfl\n")])?;
        let project = &tree.project;
        let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
        // Seed the module action from Lake's actual output bytes, without a turbo build.
        let cfg = resolve_project_config(project)?;
        let dag = build_module_dag_with_trust(&cfg, &[], false)?;
        let node = &dag.nodes["P.Fixture"];
        let key = compute_module_cas_key(&cfg, node, &[], node.needs_c)?;
        store_module_artifacts_in_cas(
            &mut store,
            project,
            node,
            &key,
            &cfg.toolchain,
            "trusted-internal",
            1,
            0,
        )?;
        tree.opt_out()?;
        tree.prepare_snapshot(".lake/build/lib/lean/P/Fixture.olean")?;
        let artifact = project.join(".lake/build/lib/lean/P/Fixture.olean");
        let build = |store: &mut TurboStore| {
            build_project_modules_native(
                store,
                project,
                &[],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
        };
        let before = snapshot(project)?;
        let report = build(&mut store)?;
        assert_eq!(report.modules_compiled, 0);
        assert_eq!(report.modules_cached, 1);
        assert_eq!(
            snapshot(project)?,
            before,
            "module CAS hit changed Lake artifacts/entries"
        );
        // A missing companion must fail without wiping the remaining output set.
        fs::remove_file(artifact.with_extension("olean.server"))?;
        let before = snapshot(project)?;
        let err = build(&mut store).unwrap_err().to_string();
        assert!(err.contains("Worktree opt-out prevents restoring"), "{err}");
        assert_eq!(snapshot(project)?, before);
        drop(store);
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_caller_optout_preserves_external_path_dependency() -> Result<()> {
        use crate::worktree_test_support::{snapshot, LakeTree};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for prebuilt in [false, true] {
            let tree = LakeTree::new("external_dep", &[("P/A.lean", "def depValue : Nat := 7\n")])?;
            let caller = tree.root.join("caller");
            fs::create_dir_all(&caller)?;
            fs::write(
                caller.join("lean-toolchain"),
                include_str!("../../../lean/lean-toolchain"),
            )?;
            fs::write(caller.join("lakefile.toml"),
                "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"fixture\"\npath = \"../project\"\n[[lean_lib]]\nname = \"App\"\n")?;
            fs::write(
                caller.join("App.lean"),
                "import P.A\ntheorem app : depValue = 7 := rfl\n",
            )?;
            let out = Command::new("lake")
                .args(["build", "App"])
                .current_dir(&caller)
                .output()?;
            anyhow::ensure!(
                out.status.success(),
                "{}",
                String::from_utf8_lossy(&out.stderr)
            );
            let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
            let targets = vec!["App".to_string()];
            // Seed both module actions before opting out. Keep the dependency's
            // manifest only in the case exercising external-prebuilt digest reads.
            let seed = build_project_modules_native(
                &mut store,
                &caller,
                &targets,
                "trusted-internal",
                1,
                false,
                true,
                None,
            )?;
            assert_eq!(seed.modules_compiled, 0);
            assert_eq!(seed.modules_up_to_date_reused, 2);
            if !prebuilt {
                fs::remove_file(
                    tree.project
                        .join(".lake/build/.turbo_verified_sources.json"),
                )?;
            }
            fs::write(
                caller.join("turbo-lean.toml"),
                "[worktree]\nauto_link = false\n",
            )?;
            assert!(!tree.project.join("turbo-lean.toml").exists());
            tree.prepare_snapshot(".lake/build/lib/lean/P/A.olean")?;
            fs::remove_file(caller.join(".lake/build/.turbo_publish.lock"))?;
            let dep_before = snapshot(&tree.project)?;
            let caller_before = snapshot(&caller)?;
            let cfg = resolve_project_config(&caller)?;
            let dag = build_module_dag(&cfg, &targets)?;
            assert_eq!(dag.nodes.contains_key("P.A"), !prebuilt);
            let report = build_project_modules_native(
                &mut store,
                &caller,
                &targets,
                "trusted-internal",
                1,
                false,
                true,
                None,
            )?;
            assert_eq!(report.modules_compiled, 0);
            assert_eq!(report.modules_cached, if prebuilt { 1 } else { 2 });
            crate::lake_build::run_build_command(
                &mut store,
                true,
                targets,
                caller.clone(),
                "trusted-internal".to_string(),
                1,
                false,
            )?;
            assert_eq!(
                snapshot(&tree.project)?,
                dep_before,
                "external dependency changed (prebuilt={prebuilt})"
            );
            assert_eq!(
                snapshot(&caller)?,
                caller_before,
                "caller changed (prebuilt={prebuilt})"
            );
        }
        Ok(())
    }

    /// P0-4: rebuilding only an imported module (`build App.A`) must invalidate the manifest
    /// entry of its reverse dependent `App.B`, whose `.olean` was elaborated against the old `A`.
    #[test]
    fn test_dependent_manifest_entry_stale_after_import_only_rebuild() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("stale_dependent");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let a_src = |v: u32| format!("namespace App\ndef g : Nat := {v}\nend App\n");
        fs::write(proj_dir.join("App/A.lean"), a_src(3)).unwrap();
        let b_file = proj_dir.join("App/B.lean");
        let b_src = "import App.A\nnamespace App\ntheorem g_eq : g = 3 := rfl\nend App\n";
        fs::write(&b_file, b_src).unwrap();
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        let mut build = |targets: &[String]| {
            build_project_modules_native(
                &mut store,
                &proj_dir,
                targets,
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap()
        };
        assert_eq!(build(&[]).modules_compiled, 2);
        let canon = proj_dir.canonicalize().unwrap();
        let canon_b = b_file.canonicalize().unwrap();
        assert!(crate::lake_build::is_file_verified_in_lake_build(
            &canon, &canon_b, b_src
        ));
        assert!(crate::lake_build::resolve_prebuilt_module_import(&canon, &canon_b).is_some());
        // Edit `A` so `B`'s theorem no longer holds, then rebuild only `App.A`.
        fs::write(proj_dir.join("App/A.lean"), a_src(4)).unwrap();
        let rep = build(&["App.A".to_string()]);
        assert_eq!(rep.compiled_modules, vec!["App.A".to_string()]);
        assert!(
            !crate::lake_build::is_file_verified_in_lake_build(&canon, &canon_b, b_src),
            "`App.B` reported verified from an `.olean` built against the old `App.A`"
        );
        assert!(crate::lake_build::resolve_prebuilt_module_import(&canon, &canon_b).is_none());
        // Restoring the original `A` (CAS hit) makes `B`'s recorded inputs current again.
        fs::write(proj_dir.join("App/A.lean"), a_src(3)).unwrap();
        let rep = build(&["App.A".to_string()]);
        assert_eq!(rep.cached_modules, vec!["App.A".to_string()]);
        assert!(crate::lake_build::is_file_verified_in_lake_build(
            &canon, &canon_b, b_src
        ));
        // Legacy entries without pinned import digests fail closed.
        let manifest_path = crate::lake_build::verified_sources_manifest_path(&canon);
        let mut legacy: serde_json::Value =
            serde_json::from_slice(&fs::read(&manifest_path).unwrap()).unwrap();
        for entry in legacy["modules"].as_object_mut().unwrap().values_mut() {
            entry
                .as_object_mut()
                .unwrap()
                .remove("import_olean_digests");
        }
        fs::write(&manifest_path, serde_json::to_vec(&legacy).unwrap()).unwrap();
        assert!(!crate::lake_build::is_file_verified_in_lake_build(
            &canon, &canon_b, b_src
        ));
        // ...and gives no freshness evidence before elaboration: every built import is refreshed.
        let c_file = canon.join("App/C.lean");
        fs::write(&c_file, "import App.B\n").unwrap();
        let res = crate::lake_build::ensure_project_imports_fresh_for_check(&canon, &[c_file]);
        assert!(
            !matches!(res, Ok(0)),
            "legacy manifest fell back to timestamps"
        );
        assert!(!manifest_path.exists());
        let _ = fs::remove_dir_all(&dir);
    }

    /// P0-4 across packages: rebuilding only a transitive dependency-package import must
    /// invalidate the root module, and an entry missing an external pin fails closed.
    #[test]
    fn test_root_entry_stale_after_transitive_dep_pkg_rebuild() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("stale_dep_pkg");
        let proj_dir = dir.join("proj");
        let dep_dir = proj_dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("DepPkg")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        for d in [&proj_dir, &dep_dir] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepPkg\"\nglobs = [\"DepPkg.+\"]\n",
        )
        .unwrap();
        let a_src = |v: u32| format!("namespace DepPkg\ndef g : Nat := {v}\nend DepPkg\n");
        fs::write(dep_dir.join("DepPkg/A.lean"), a_src(3)).unwrap();
        fs::write(
            dep_dir.join("DepPkg/B.lean"),
            "import DepPkg.A\nnamespace DepPkg\ndef h : Nat := g\nend DepPkg\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lake-manifest.json"),
            r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep_pkg", "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml", "inherited": false}], "name": "app_pkg", "lakeDir": ".lake", "fixedToolchain": false}"#,
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let c_file = proj_dir.join("App/C.lean");
        let c_src = "import DepPkg.B\nnamespace App\ntheorem h_eq : DepPkg.h = 3 := rfl\nend App\n";
        fs::write(&c_file, c_src).unwrap();
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        let mut build = |root: &Path, targets: &[String]| {
            build_project_modules_native(
                &mut store,
                root,
                targets,
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap()
        };
        assert_eq!(build(&proj_dir, &[]).modules_compiled, 3);
        let canon = proj_dir.canonicalize().unwrap();
        let canon_c = c_file.canonicalize().unwrap();
        let verified =
            || crate::lake_build::is_file_verified_in_lake_build(&canon, &canon_c, c_src);
        assert!(verified());
        // An entry missing its external pin fails closed.
        let manifest_path = crate::lake_build::verified_sources_manifest_path(&canon);
        let good = fs::read(&manifest_path).unwrap();
        let mut partial: serde_json::Value = serde_json::from_slice(&good).unwrap();
        partial["modules"]["App/C.lean"]["import_olean_digests"] = serde_json::json!({});
        fs::write(&manifest_path, serde_json::to_vec(&partial).unwrap()).unwrap();
        assert!(!verified(), "unpinned dependency-package import accepted");
        fs::write(&manifest_path, &good).unwrap();
        assert!(verified());
        // ...and so does a dependency-package entry missing a pin (stat fingerprints are omitted
        // while artifacts are younger than `STAT_TRUST_WINDOW_NS`, forcing re-digest on young
        // artifacts, and populated by `hydrate_project_traces` once aged past the cooldown).
        let dep_manifest_path = dep_dir.join(".lake/build/.turbo_verified_sources.json");
        let dep_good = fs::read(&dep_manifest_path).unwrap();
        let mut dep_partial: serde_json::Value = serde_json::from_slice(&dep_good).unwrap();
        assert!(
            dep_partial["modules"]["DepPkg/A.lean"]["artifact_stat_fingerprint"]
                .as_str()
                .is_some_and(str::is_empty)
        );
        std::thread::sleep(std::time::Duration::from_millis(2100));
        hydrate_project_traces(&canon).unwrap();
        let dep_good = fs::read(&dep_manifest_path).unwrap();
        dep_partial = serde_json::from_slice(&dep_good).unwrap();
        assert!(
            dep_partial["modules"]["DepPkg/A.lean"]["artifact_stat_fingerprint"]
                .as_str()
                .is_some_and(|fp| !fp.is_empty())
        );
        dep_partial["modules"]["DepPkg/B.lean"]["import_olean_digests"] = serde_json::json!({});
        fs::write(
            &dep_manifest_path,
            serde_json::to_vec(&dep_partial).unwrap(),
        )
        .unwrap();
        assert!(!verified(), "unpinned transitive import accepted");
        fs::write(&dep_manifest_path, &dep_good).unwrap();
        assert!(verified());
        // A foreign rewrite of a transitive `.olean` with an old mtime is detected, and putting
        // the original bytes back (new ctime, same digest) is accepted again.
        let a_olean = dep_dir.join(".lake/build/lib/lean/DepPkg/A.olean");
        let a_bytes = fs::read(&a_olean).unwrap();
        let _ = fs::remove_file(&a_olean);
        fs::write(&a_olean, b"foreign olean").unwrap();
        assert!(Command::new("touch")
            .args(["-d", "@1000000000"])
            .arg(&a_olean)
            .status()
            .unwrap()
            .success());
        assert!(!verified(), "rewritten transitive `.olean` accepted");
        let _ = fs::remove_file(&a_olean);
        fs::write(&a_olean, &a_bytes).unwrap();
        assert!(verified());
        // Rebuild only the transitive import `DepPkg.A` (inside the dependency package).
        std::thread::sleep(std::time::Duration::from_millis(20));
        fs::write(dep_dir.join("DepPkg/A.lean"), a_src(4)).unwrap();
        let rep = build(&dep_dir, &["DepPkg.A".to_string()]);
        assert_eq!(rep.compiled_modules, vec!["DepPkg.A".to_string()]);
        assert!(
            !verified(),
            "`App.C` reported verified against a dependency closure rebuilt underneath it"
        );
        assert!(crate::lake_build::resolve_prebuilt_module_import(&canon, &canon_c).is_none());
        // `check` must not elaborate `App.C` against the stale `DepPkg.B` either.
        let res = crate::lake_build::ensure_project_imports_fresh_for_check(
            &canon,
            std::slice::from_ref(&canon_c),
        );
        assert!(
            !matches!(res, Ok(0)),
            "stale `DepPkg.B` left in place for elaboration"
        );
        // The dependency's own manifest is the evidence: it counts without a root manifest too.
        let _ = fs::remove_file(&manifest_path);
        let res = crate::lake_build::ensure_project_imports_fresh_for_check(
            &canon,
            std::slice::from_ref(&canon_c),
        );
        assert!(
            !matches!(res, Ok(0)),
            "dependency evidence ignored without a root manifest"
        );
        // Rebuilding the root must not reuse the stale `DepPkg.B` as a fresh external closure:
        // its pin for `DepPkg.A` no longer matches, so `B` is rebuilt and `App.C` (`h = 3`) fails.
        let rebuilt = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        );
        assert!(rebuilt.is_err(), "stale `DepPkg.B` reused: {rebuilt:?}");
        assert!(!verified());
        // An unreadable dependency manifest establishes nothing: refresh rather than trust it.
        fs::write(&dep_manifest_path, b"{").unwrap();
        let res = crate::lake_build::ensure_project_imports_fresh_for_check(
            &canon,
            std::slice::from_ref(&canon_c),
        );
        assert!(
            !matches!(res, Ok(0)),
            "corrupt dependency manifest treated as Lake-managed"
        );
        let _ = fs::remove_dir_all(&dir);
    }

    /// P0-4 on the elaboration path: a CAS restore of an import (old blob mtime) must still make
    /// `ensure_project_imports_fresh_for_check` treat dependents built against the newer import
    /// as stale, so `check` never elaborates against a stale intermediate `.olean`.
    #[test]
    fn test_check_refreshes_dependent_after_import_cas_restore() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("stale_dependent_restore");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let a_src = |v: u32| format!("namespace App\ndef g : Nat := {v}\nend App\n");
        let b_src = |v: u32| {
            format!("import App.A\nnamespace App\ntheorem g_eq : g = {v} := rfl\nend App\n")
        };
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        let mut build = |targets: &[String]| {
            build_project_modules_native(
                &mut store,
                &proj_dir,
                targets,
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap()
        };
        fs::write(proj_dir.join("App/A.lean"), a_src(3)).unwrap();
        fs::write(proj_dir.join("App/B.lean"), b_src(3)).unwrap();
        build(&[]);
        std::thread::sleep(std::time::Duration::from_millis(20));
        fs::write(proj_dir.join("App/A.lean"), a_src(4)).unwrap();
        fs::write(proj_dir.join("App/B.lean"), b_src(4)).unwrap();
        build(&[]);
        // Restore `A` v3 from CAS; `B` (built against `A` v4) is now stale.
        fs::write(proj_dir.join("App/A.lean"), a_src(3)).unwrap();
        let rep = build(&["App.A".to_string()]);
        assert_eq!(rep.cached_modules, vec!["App.A".to_string()]);
        let canon = proj_dir.canonicalize().unwrap();
        let c_file = canon.join("App/C.lean");
        fs::write(&c_file, "import App.B\n").unwrap();
        // Lake must be asked to refresh `App.B` (which then fails: `g = 4` no longer holds).
        let res = crate::lake_build::ensure_project_imports_fresh_for_check(&canon, &[c_file]);
        assert!(
            !matches!(res, Ok(0)),
            "stale `App.B` left in place for elaboration"
        );
        let _ = fs::remove_dir_all(&dir);
    }

    /// P0-4 on the elaboration path: an import whose artifacts were replaced behind turbo-lean's
    /// back (old mtimes, unchanged source and manifest) must be refreshed before elaboration.
    #[test]
    fn test_check_refreshes_after_foreign_import_artifact_restore() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("foreign_import_restore");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let a_src = |v: u32| format!("namespace App\ndef g : Nat := {v}\nend App\n");
        let b_src = |v: u32| {
            format!("import App.A\nnamespace App\ntheorem g_eq : g = {v} := rfl\nend App\n")
        };
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        let mut build = || {
            build_project_modules_native(
                &mut store,
                &proj_dir,
                &[],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap()
        };
        fs::write(proj_dir.join("App/A.lean"), a_src(3)).unwrap();
        fs::write(proj_dir.join("App/B.lean"), b_src(3)).unwrap();
        build();
        let a_olean = proj_dir.join(".lake/build/lib/lean/App/A.olean");
        let old_a = fs::read(&a_olean).unwrap();
        fs::write(proj_dir.join("App/A.lean"), a_src(4)).unwrap();
        fs::write(proj_dir.join("App/B.lean"), b_src(4)).unwrap();
        build();
        // Put the `A` v3 `.olean` back with ordered, old timestamps; source and manifest say v4.
        let _ = fs::remove_file(&a_olean);
        fs::write(&a_olean, &old_a).unwrap();
        for (path, stamp) in [
            (proj_dir.join("App/A.lean"), "@1000000000"),
            (a_olean.clone(), "@1000000001"),
        ] {
            assert!(Command::new("touch")
                .args(["-d", stamp])
                .arg(&path)
                .status()
                .unwrap()
                .success());
        }
        let canon = proj_dir.canonicalize().unwrap();
        let c_file = canon.join("App/C.lean");
        fs::write(&c_file, "import App.B\n").unwrap();
        let res = crate::lake_build::ensure_project_imports_fresh_for_check(&canon, &[c_file]);
        assert!(
            !matches!(res, Ok(0)),
            "foreign `App.A` artifact left in place under `App.B`"
        );
        let _ = fs::remove_dir_all(&dir);
    }

    /// P0-4: a dependency module named `Lean.*` is not a toolchain module. With no root manifest,
    /// a stale pin still forces a refresh (or a fail-closed error) instead of `Ok(0)`.
    #[test]
    fn test_dep_owned_lean_namespace_stale_without_root_manifest() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("stale_lean_ns");
        let proj_dir = dir.join("proj");
        let dep_dir = proj_dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("Lean")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        for d in [&proj_dir, &dep_dir] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"Lean\"\nglobs = [\"Lean.+\"]\n",
        )
        .unwrap();
        fs::write(dep_dir.join("Lean/Base.lean"), "def base : Nat := 1\n").unwrap();
        fs::write(
            dep_dir.join("Lean/Extra.lean"),
            "import Lean.Base\ndef extra : Nat := base\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lake-manifest.json"),
            r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep_pkg", "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml", "inherited": false}], "name": "app_pkg", "lakeDir": ".lake", "fixedToolchain": false}"#,
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let c_file = proj_dir.join("App/C.lean");
        fs::write(&c_file, "import Lean.Extra\n#check extra\n").unwrap();
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        assert_eq!(
            build_project_modules_native(
                &mut store,
                &proj_dir,
                &[],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap()
            .modules_compiled,
            3
        );
        let dep_manifest_path = dep_dir.join(".lake/build/.turbo_verified_sources.json");
        let mut dep_partial: serde_json::Value =
            serde_json::from_slice(&fs::read(&dep_manifest_path).unwrap()).unwrap();
        dep_partial["modules"]["Lean/Extra.lean"]["import_olean_digests"]
            .as_object_mut()
            .unwrap()
            .insert(
                "Lean.Base".into(),
                serde_json::json!("not-the-recorded-digest"),
            );
        fs::write(
            &dep_manifest_path,
            serde_json::to_vec(&dep_partial).unwrap(),
        )
        .unwrap();
        let canon = proj_dir.canonicalize().unwrap();
        let _ = fs::remove_file(crate::lake_build::verified_sources_manifest_path(&canon));
        let res = crate::lake_build::ensure_project_imports_fresh_for_check(
            &canon,
            std::slice::from_ref(&c_file.canonicalize().unwrap()),
        );
        assert!(
            !matches!(res, Ok(0)),
            "`Lean.Extra` skipped as a toolchain name: {res:?}"
        );
        let _ = fs::remove_dir_all(&dir);
    }

    /// P0-4: a root entry recorded for a different toolchain or Lean githash is stale before
    /// elaboration, even when its only imports are genuine toolchain modules (unpinned).
    #[test]
    fn test_root_entry_stale_on_toolchain_identity_mismatch() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("stale_tc_identity");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let b_src = "import Init\ntheorem t : True := trivial\n";
        fs::write(proj_dir.join("App/B.lean"), b_src).unwrap();
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        let canon = proj_dir.canonicalize().unwrap();
        let manifest_path = crate::lake_build::verified_sources_manifest_path(&canon);
        let good = fs::read(&manifest_path).unwrap();
        let c_file = canon.join("App/C.lean");
        fs::write(&c_file, "import App.B\n").unwrap();
        let fresh = |bytes: &[u8]| {
            fs::write(&manifest_path, bytes).unwrap();
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&c_file),
            )
        };
        assert!(
            matches!(fresh(&good), Ok(0)),
            "matching toolchain identity must stay fresh"
        );
        for (field, value) in [
            ("pkg_name", "other_pkg"),
            ("toolchain", "leanprover/lean4:v4.24.0"),
            ("lean_githash", "0000000000000000000000000000000000000000"),
            (
                "pkg_config_digest",
                "0000000000000000000000000000000000000000000000000000000000000000",
            ),
        ] {
            let mut stale: serde_json::Value = serde_json::from_slice(&good).unwrap();
            stale[field] = serde_json::json!(value);
            let res = fresh(&serde_json::to_vec(&stale).unwrap());
            assert!(
                !matches!(res, Ok(0)),
                "mismatched `{field}` left `App.B` in place: {res:?}"
            );
            fs::write(&manifest_path, &good).unwrap();
        }
        let lakefile = canon.join("lakefile.toml");
        let saved_lakefile = fs::read(&lakefile).unwrap();
        let saved_lf_mtime = fs::metadata(&lakefile).unwrap().modified().unwrap();
        for extra_cfg in [
            "leanOptions = { autoImplicit = false }\n",
            "moreLeanArgs = [\"-DwarningAsError=true\"]\n",
            "weakLeanArgs = [\"-DmaxSynthPendingDepth=4\"]\n",
        ] {
            let mut shifted = String::from_utf8(saved_lakefile.clone()).unwrap();
            let lib_idx = shifted.find("[[lean_lib]]").unwrap();
            shifted.insert_str(lib_idx, extra_cfg);
            fs::write(&lakefile, shifted).unwrap();
            fs::File::open(&lakefile)
                .unwrap()
                .set_times(std::fs::FileTimes::new().set_modified(saved_lf_mtime))
                .unwrap();
            fs::write(
                canon.join("turbo-lean.toml"),
                "[worktree]\nauto_link = false\n",
            )
            .unwrap();
            #[cfg(unix)]
            let before_opt = crate::worktree_test_support::snapshot(&canon).unwrap();
            let opt_err = crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&c_file),
            )
            .unwrap_err()
            .to_string();
            assert!(
                opt_err.contains("Worktree opt-out prevents refreshing stale imports: App.B"),
                "opt-out missed `{extra_cfg}` root config drift: {opt_err}"
            );
            #[cfg(unix)]
            assert_eq!(
                crate::worktree_test_support::snapshot(&canon).unwrap(),
                before_opt,
                "opt-out mutated `.lake` on `{extra_cfg}`"
            );
            fs::remove_file(canon.join("turbo-lean.toml")).unwrap();
            assert_eq!(
                crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon,
                    std::slice::from_ref(&c_file),
                )
                .unwrap(),
                1
            );
            let post: serde_json::Value =
                serde_json::from_slice(&fs::read(&manifest_path).unwrap()).unwrap();
            assert!(post["modules"].get("App/B.lean").is_none());
            assert_eq!(
                crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon,
                    std::slice::from_ref(&c_file),
                )
                .unwrap(),
                0
            );
            fs::write(&lakefile, &saved_lakefile).unwrap();
            fs::File::open(&lakefile)
                .unwrap()
                .set_times(std::fs::FileTimes::new().set_modified(saved_lf_mtime))
                .unwrap();
        }
        build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        let good = fs::read(&manifest_path).unwrap();
        fs::remove_file(&lakefile).unwrap();
        let mut stale: serde_json::Value = serde_json::from_slice(&good).unwrap();
        stale["lean_githash"] = serde_json::json!("0000000000000000000000000000000000000000");
        let res = fresh(&serde_json::to_vec(&stale).unwrap());
        assert!(
            !matches!(res, Ok(0)),
            "missing lakefile bypassed `lean_githash` check: {res:?}"
        );
        fs::write(&lakefile, saved_lakefile).unwrap();
        let _ = fs::remove_dir_all(&dir);
    }

    /// P0-4 across a dependency-to-root edge: `App.C → DepPkg.B → App.A → App.X`; rebuilding only
    /// `App.X` must invalidate `App.C`.
    #[test]
    fn test_root_entry_stale_through_dep_to_root_import() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("stale_dep_to_root");
        let proj_dir = dir.join("proj");
        let dep_dir = proj_dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("DepPkg")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        for d in [&proj_dir, &dep_dir] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepPkg\"\nglobs = [\"DepPkg.+\"]\n",
        )
        .unwrap();
        fs::write(
            dep_dir.join("DepPkg/B.lean"),
            "import App.A\nnamespace DepPkg\ndef h : Nat := App.k\nend DepPkg\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lake-manifest.json"),
            r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep_pkg", "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml", "inherited": false}], "name": "app_pkg", "lakeDir": ".lake", "fixedToolchain": false}"#,
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let x_src = |v: u32| format!("namespace App\ndef x : Nat := {v}\nend App\n");
        fs::write(proj_dir.join("App/X.lean"), x_src(3)).unwrap();
        fs::write(
            proj_dir.join("App/A.lean"),
            "import App.X\nnamespace App\ndef k : Nat := x\nend App\n",
        )
        .unwrap();
        let c_file = proj_dir.join("App/C.lean");
        let c_src = "import DepPkg.B\nnamespace App\ntheorem h_eq : DepPkg.h = 3 := rfl\nend App\n";
        fs::write(&c_file, c_src).unwrap();
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        let mut build = |targets: &[String]| {
            build_project_modules_native(
                &mut store,
                &proj_dir,
                targets,
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap()
        };
        assert_eq!(build(&[]).modules_compiled, 4);
        let canon = proj_dir.canonicalize().unwrap();
        let canon_c = c_file.canonicalize().unwrap();
        let verified =
            || crate::lake_build::is_file_verified_in_lake_build(&canon, &canon_c, c_src);
        assert!(verified());
        fs::write(proj_dir.join("App/X.lean"), x_src(4)).unwrap();
        assert_eq!(
            build(&["App.X".to_string()]).compiled_modules,
            vec!["App.X".to_string()]
        );
        assert!(
            !verified(),
            "`App.C` accepted through a dependency-to-root edge onto a rebuilt `App.X`"
        );
        fs::write(
            canon.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )
        .unwrap();
        let err_rebuilt = crate::lake_build::ensure_project_imports_fresh_for_check(
            &canon,
            std::slice::from_ref(&canon_c),
        )
        .unwrap_err()
        .to_string();
        assert!(
            err_rebuilt.contains("Worktree opt-out prevents refreshing stale imports: DepPkg.B"),
            "opt-out missed dep-to-root staleness after rebuilding `App.X`: {err_rebuilt}"
        );
        fs::remove_file(canon.join("turbo-lean.toml")).unwrap();
        fs::write(proj_dir.join("App/X.lean"), x_src(3)).unwrap();
        build(&[]);
        assert!(verified());
        let root_lf = canon.join("lakefile.toml");
        let orig_lf = fs::read_to_string(&root_lf).unwrap();
        let orig_lf_mtime = fs::metadata(&root_lf).unwrap().modified().unwrap();
        let shifted_lf = orig_lf.replace(
            "[[lean_lib]]",
            "weakLeanArgs = [\"-DmaxSynthPendingDepth=4\"]\n[[lean_lib]]",
        );
        fs::write(&root_lf, shifted_lf).unwrap();
        fs::File::open(&root_lf)
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(orig_lf_mtime))
            .unwrap();
        fs::write(
            canon.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )
        .unwrap();
        #[cfg(unix)]
        let before_opt = crate::worktree_test_support::snapshot(&canon).unwrap();
        let err_cfg = crate::lake_build::ensure_project_imports_fresh_for_check(
            &canon,
            std::slice::from_ref(&canon_c),
        )
        .unwrap_err()
        .to_string();
        assert!(
            err_cfg.contains("Worktree opt-out prevents refreshing stale imports: DepPkg.B"),
            "opt-out missed dep-to-root `weakLeanArgs` drift with preserved lakefile mtime: {err_cfg}"
        );
        #[cfg(unix)]
        assert_eq!(
            crate::worktree_test_support::snapshot(&canon).unwrap(),
            before_opt,
            "opt-out mutated `.lake` across dep-to-root config drift"
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_config_resolution_failure_fails_closed_for_stale_dep_and_preserves_optout_lake_tree() {
        use crate::worktree_test_support::snapshot;
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("cfg_fail_stale_dep");
        let proj_dir = dir.join("proj");
        let dep_dir = proj_dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("DepPkg")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        for d in [&proj_dir, &dep_dir] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }
        let dep_lakefile = dep_dir.join("lakefile.toml");
        let valid_dep_lf =
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepPkg\"\nglobs = [\"DepPkg.+\"]\n";
        fs::write(&dep_lakefile, valid_dep_lf).unwrap();
        let a_src = |v: u32| format!("namespace DepPkg\ndef g : Nat := {v}\nend DepPkg\n");
        fs::write(dep_dir.join("DepPkg/A.lean"), a_src(3)).unwrap();
        fs::write(
            dep_dir.join("DepPkg/B.lean"),
            "import DepPkg.A\nnamespace DepPkg\ndef h : Nat := g\nend DepPkg\n",
        )
        .unwrap();
        let manifest_path_json = proj_dir.join("lake-manifest.json");
        let valid_manifest_json = r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep_pkg", "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml", "inherited": false}], "name": "app_pkg", "lakeDir": ".lake", "fixedToolchain": false}"#;
        fs::write(&manifest_path_json, valid_manifest_json).unwrap();
        let root_lakefile = proj_dir.join("lakefile.toml");
        let valid_root_lf = "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n";
        fs::write(&root_lakefile, valid_root_lf).unwrap();
        let c_file = proj_dir.join("App/C.lean");
        fs::write(
            &c_file,
            "import DepPkg.B\nnamespace App\ntheorem h_eq : DepPkg.h = 3 := rfl\nend App\n",
        )
        .unwrap();
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        assert_eq!(
            build_project_modules_native(
                &mut store,
                &proj_dir,
                &[],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap()
            .modules_compiled,
            3
        );
        std::thread::sleep(std::time::Duration::from_millis(20));
        fs::write(dep_dir.join("DepPkg/A.lean"), a_src(4)).unwrap();
        assert_eq!(
            build_project_modules_native(
                &mut store,
                &dep_dir,
                &["DepPkg.A".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap()
            .compiled_modules,
            vec!["DepPkg.A".to_string()]
        );
        let canon = proj_dir.canonicalize().unwrap();
        let canon_c = c_file.canonicalize().unwrap();
        let root_manifest_path = crate::lake_build::verified_sources_manifest_path(&canon);
        let saved_root_manifest = fs::read(&root_manifest_path).unwrap();
        for with_root_manifest in [true, false] {
            for opt_out in [false, true] {
                if with_root_manifest {
                    fs::write(&root_manifest_path, &saved_root_manifest).unwrap();
                } else {
                    let _ = fs::remove_file(&root_manifest_path);
                }
                if opt_out {
                    fs::write(
                        canon.join("turbo-lean.toml"),
                        "[worktree]\nauto_link = false\n",
                    )
                    .unwrap();
                } else {
                    let _ = fs::remove_file(canon.join("turbo-lean.toml"));
                }
                for kind in ["dep_lakefile", "lake_manifest", "missing_root_lakefile"] {
                    match kind {
                        "dep_lakefile" => fs::write(&dep_lakefile, "name = [\n").unwrap(),
                        "lake_manifest" => fs::write(&manifest_path_json, "{corrupt").unwrap(),
                        _ => fs::remove_file(&root_lakefile).unwrap(),
                    }
                    let before = opt_out.then(|| snapshot(&canon).unwrap());
                    let err = crate::lake_build::ensure_project_imports_fresh_for_check(
                        &canon,
                        std::slice::from_ref(&canon_c),
                    )
                    .unwrap_err();
                    assert!(
                        format!("{err:#}").contains("Failed to resolve Lean options"),
                        "unexpected error ({kind}, manifest={with_root_manifest}, opt_out={opt_out}): {err:#}"
                    );
                    if let Some(before) = before {
                        assert_eq!(
                            snapshot(&canon).unwrap(),
                            before,
                            ".lake mutated ({kind}, manifest={with_root_manifest})"
                        );
                    }
                    fs::write(&dep_lakefile, valid_dep_lf).unwrap();
                    fs::write(&manifest_path_json, valid_manifest_json).unwrap();
                    fs::write(&root_lakefile, valid_root_lf).unwrap();
                }
            }
        }
        // Even a genuinely Lake-less directory (no lakefile, no manifest, no `.lake/packages`)
        // must fail closed on non-root/non-toolchain imports (including under `Lean.*`).
        let lakeless = dir.join("lakeless");
        fs::create_dir_all(&lakeless).unwrap();
        fs::write(
            lakeless.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        let canon_ll = lakeless.canonicalize().unwrap();
        for imp in ["DepPkg.B", "Lean.NonexistentUserShadowMod"] {
            let f = canon_ll.join("Main.lean");
            fs::write(&f, format!("import {imp}\n")).unwrap();
            let err = crate::lake_build::ensure_project_imports_fresh_for_check(&canon_ll, &[f])
                .unwrap_err();
            assert!(
                format!("{err:#}").contains("Unresolved non-root import"),
                "Lake-less import `{imp}` did not fail closed: {err:#}"
            );
        }
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_allowed_axioms_shift_retains_siblings_without_kernel_audit_and_strict_memo_separates() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("axiom_shift_memo");
        let proj_dir = dir.join("proj");
        let dep_dir = proj_dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("DepPkg")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        for d in [&proj_dir, &dep_dir] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepPkg\"\nglobs = [\"DepPkg.+\"]\n",
        )
        .unwrap();
        fs::write(dep_dir.join("DepPkg/A.lean"), "def depA : Nat := 1\n").unwrap();
        fs::write(
            dep_dir.join("DepPkg/B.lean"),
            "import App.R\ndef depB : Nat := rootR\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lake-manifest.json"),
            r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep_pkg", "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml", "inherited": false}], "name": "app_pkg", "lakeDir": ".lake", "fixedToolchain": false}"#,
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        fs::write(proj_dir.join("App/R.lean"), "def rootR : Nat := 1\n").unwrap();
        fs::write(proj_dir.join("App/S.lean"), "def rootS : Nat := 2\n").unwrap();
        fs::write(
            proj_dir.join("App/T.lean"),
            "import DepPkg.B\ndef rootT : Nat := depB\n",
        )
        .unwrap();
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, "Custom.Ax");
        build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        std::env::remove_var(crate::splitter::ALLOWED_AXIOMS_ENV);
        // Rebuild only `App.S` under strict default axioms: `App/R.lean` must stay in the
        // manifest with `kernel_audited == false` rather than retaining the lax audit bit or
        // being dropped as Lake-managed.
        fs::write(proj_dir.join("App/S.lean"), "def rootS : Nat := 3\n").unwrap();
        build_project_modules_native(
            &mut store,
            &proj_dir,
            &["App.S".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        let canon = proj_dir.canonicalize().unwrap();
        let root_manifest_bytes =
            fs::read(crate::lake_build::verified_sources_manifest_path(&canon)).unwrap();
        let root_manifest: VerifiedDepManifest =
            serde_json::from_slice(&root_manifest_bytes).unwrap();
        assert_eq!(
            root_manifest.allowed_axioms,
            crate::splitter::allowed_axioms()
        );
        assert!(
            !root_manifest.modules["App/R.lean"].kernel_audited,
            "retained sibling kept `kernel_audited` across `allowed_axioms` shift"
        );
        assert!(root_manifest.modules["App/S.lean"].kernel_audited);
        // `strict_policy = false` (`dep_pkg_module_stale`) accepts `DepPkg.B -> App.R` because
        // `App.R`'s artifact bytes are current, and must NOT insert into `memo` so a subsequent
        // `strict_policy = true` (`import_pin_current`) rejects the unaudited `App.R`.
        let cfg = resolve_project_config(&canon).unwrap();
        let memo = DepImportMemo::default();
        let mut cache = LakeClosureCache::default();
        assert!(!dep_pkg_module_stale(&cfg, &memo, &mut cache, "DepPkg.B"));
        assert!(
            memo.0.lock().unwrap().is_empty(),
            "non-strict staleness check polluted `DepImportMemo`"
        );
        let dep_manifest: VerifiedDepManifest = serde_json::from_slice(
            &fs::read(dep_dir.join(".lake/build/.turbo_verified_sources.json")).unwrap(),
        )
        .unwrap();
        let dep_b_pin = &dep_manifest.modules["DepPkg/B.lean"].olean_artifact_digest;
        assert!(
            !import_pin_current(
                &cfg,
                &memo,
                "DepPkg.B",
                Some(ImportPinSpec {
                    full_pin: dep_b_pin,
                    tier_pin: None,
                }),
            ),
            "`import_pin_current` accepted unaudited `App.R` via non-strict memo"
        );

        // Repeat for `kernel_policy_digest` shifts (`TURBO_LEAN_ALLOWED_UNSAFE` without changing
        // `allowed_axioms`): `load_cached_pkg_manifest` (`strict_policy`), warm adoption, and
        // `hydrate_project_traces` must all reject/clear stale `kernel_audited` bits.
        std::env::set_var("TURBO_LEAN_ALLOWED_UNSAFE", "rootU");
        fs::write(proj_dir.join("App/U.lean"), "unsafe def rootU : Nat := 1\n").unwrap();
        build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        std::env::remove_var("TURBO_LEAN_ALLOWED_UNSAFE");
        // Before rewriting the manifest, `import_pin_current` (`strict_policy = true` via
        // `load_cached_pkg_manifest`) must reject `DepPkg.B -> App.R` because `App`'s manifest has
        // a stale `kernel_policy_digest`.
        let cfg_post = resolve_project_config(&canon).unwrap();
        let memo_post = DepImportMemo::default();
        let dep_manifest_post: VerifiedDepManifest = serde_json::from_slice(
            &fs::read(dep_dir.join(".lake/build/.turbo_verified_sources.json")).unwrap(),
        )
        .unwrap();
        let dep_b_pin_post = &dep_manifest_post.modules["DepPkg/B.lean"].olean_artifact_digest;
        assert!(
            !import_pin_current(
                &cfg_post,
                &memo_post,
                "DepPkg.B",
                Some(ImportPinSpec {
                    full_pin: dep_b_pin_post,
                    tier_pin: None,
                }),
            ),
            "`import_pin_current` accepted stale `kernel_policy_digest` in `load_cached_pkg_manifest`"
        );
        hydrate_project_traces(&canon).unwrap();
        let hydrated_manifest: VerifiedDepManifest = serde_json::from_slice(
            &fs::read(crate::lake_build::verified_sources_manifest_path(&canon)).unwrap(),
        )
        .unwrap();
        assert_eq!(
            hydrated_manifest.kernel_policy_digest,
            crate::splitter::current_kernel_policy_digest()
        );
        assert!(
            !hydrated_manifest.modules["App/U.lean"].kernel_audited,
            "`hydrate_project_traces` preserved stale `kernel_audited` across `kernel_policy_digest` shift"
        );
        let u_chk = crate::check::evaluate_check_command_value(
            &mut store,
            proj_dir.join("App/U.lean"),
            None,
            proj_dir.clone(),
        );
        assert!(
            u_chk.is_err(),
            "`check` accepted `unsafe def` after `TURBO_LEAN_ALLOWED_UNSAFE` was cleared"
        );
        let _ = fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_lake_managed_dep_and_root_closures_detect_staleness_and_preserve_optout() {
        use crate::worktree_test_support::snapshot;

        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("lake_managed_dep_stale");
        let proj_dir = dir.join("proj");
        let dep_dir = dir.join("dep_pkg");
        fs::create_dir_all(dep_dir.join("DepPkg")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        for d in [&proj_dir, &dep_dir] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }
        let dep_lf_base = "name = \"dep_pkg\"\n[leanOptions]\nautoImplicit = false\npp.unicode.fun = true\nmaxSynthPendingDepth = 3\n[[lean_lib]]\nname = \"DepPkg\"\nglobs = [\"DepPkg.+\"]\nmoreLeanArgs = [\"-DwarningAsError=false\"]\n";
        fs::write(dep_dir.join("lakefile.toml"), dep_lf_base).unwrap();
        let a_src = |v: u32| format!("namespace DepPkg\ndef g : Nat := {v}\nend DepPkg\n");
        fs::write(dep_dir.join("DepPkg/A.lean"), a_src(3)).unwrap();
        fs::write(
            dep_dir.join("DepPkg/B.lean"),
            "import DepPkg.A\nnamespace DepPkg\ndef h : Nat := g\nend DepPkg\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            format!(
                "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[leanOptions]\nautoImplicit = false\n[[require]]\nname = \"dep_pkg\"\npath = \"{}\"\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
                dep_dir.display()
            ),
        )
        .unwrap();
        fs::write(
            proj_dir.join("App/Mid.lean"),
            "import DepPkg.B\nnamespace App\ndef mid : Nat := DepPkg.h\nend App\n",
        )
        .unwrap();
        let c_file = proj_dir.join("App/C.lean");
        let c_src = "import App.Mid\nnamespace App\ntheorem mid_eq : mid = 3 := rfl\nend App\n";
        fs::write(&c_file, c_src).unwrap();

        let run_lake = |cwd: &Path, args: &[&str]| {
            let st = std::process::Command::new("lake")
                .args(args)
                .current_dir(cwd)
                .status()
                .unwrap();
            assert!(st.success(), "`lake {args:?}` failed in {}", cwd.display());
        };
        run_lake(&proj_dir, &["build", "App.Mid"]);
        let canon = proj_dir.canonicalize().unwrap();
        let canon_c = c_file.canonicalize().unwrap();
        let dep_turbo_manifest = dep_dir.join(".lake/build/.turbo_verified_sources.json");
        let root_turbo_manifest = crate::lake_build::verified_sources_manifest_path(&canon);
        assert!(
            !dep_turbo_manifest.exists() && !root_turbo_manifest.exists(),
            "raw `lake build` must not create `.turbo_verified_sources.json`"
        );

        // Fresh Lake-built dependency + root `App.Mid` without any turbo manifest: `Ok(0)` and
        // zero `.lake` mutations under worktree opt-out (no `.turbo_publish.lock` or `.hash`).
        fs::write(
            canon.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )
        .unwrap();
        let snap_fresh_proj = snapshot(&canon).unwrap();
        let snap_fresh_dep = snapshot(&dep_dir.canonicalize().unwrap()).unwrap();
        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&canon_c),
            )
            .unwrap(),
            0
        );
        assert_eq!(
            snapshot(&canon).unwrap(),
            snap_fresh_proj,
            "fresh check mutated root `.lake` under worktree opt-out"
        );
        assert_eq!(
            snapshot(&dep_dir.canonicalize().unwrap()).unwrap(),
            snap_fresh_dep,
            "fresh check mutated dependency `.lake` under worktree opt-out"
        );

        // Unmanifested Lake `.olean`s must NOT count as kernel-audited for `is_file_verified_in_lake_build`.
        run_lake(&proj_dir, &["build", "App.C"]);
        assert!(
            !crate::lake_build::is_file_verified_in_lake_build(&canon, &canon_c, c_src),
            "unaudited Lake `.olean` accepted by `is_file_verified_in_lake_build`"
        );

        // Case 1: `DepPkg/A.lean` edited & rebuilt in `dep_dir` via Lake (leaving `DepPkg/B.olean`
        // and `App/Mid.olean` built against old `DepPkg/A.olean` with no turbo manifest anywhere).
        std::thread::sleep(std::time::Duration::from_millis(20));
        fs::write(dep_dir.join("DepPkg/A.lean"), a_src(4)).unwrap();
        run_lake(&dep_dir, &["build", "DepPkg.A"]);
        assert!(!dep_turbo_manifest.exists());
        let snap_stale_proj = snapshot(&canon).unwrap();
        let snap_stale_dep = snapshot(&dep_dir.canonicalize().unwrap()).unwrap();
        let err = crate::lake_build::ensure_project_imports_fresh_for_check(
            &canon,
            std::slice::from_ref(&canon_c),
        )
        .unwrap_err();
        assert!(
            format!("{err:#}").contains("Worktree opt-out prevents refreshing stale imports"),
            "stale Lake-built `DepPkg.B` / `App.Mid` escaped opt-out gate: {err:#}"
        );
        assert_eq!(
            snapshot(&canon).unwrap(),
            snap_stale_proj,
            "stale opt-out check mutated root `.lake`"
        );
        assert_eq!(
            snapshot(&dep_dir.canonicalize().unwrap()).unwrap(),
            snap_stale_dep,
            "stale opt-out check mutated dependency `.lake`"
        );

        // Without opt-out, `ensure_project_imports_fresh_for_check` refreshes `App.Mid` (and
        // transitively `DepPkg.B`) via Lake, after which a repeat check returns `Ok(0)`.
        fs::remove_file(canon.join("turbo-lean.toml")).unwrap();
        let refreshed = crate::lake_build::ensure_project_imports_fresh_for_check(
            &canon,
            std::slice::from_ref(&canon_c),
        )
        .unwrap();
        assert!(refreshed >= 1, "expected stale Lake closure refresh");
        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&canon_c),
            )
            .unwrap(),
            0
        );

        // Case 2: turbo-built root `App.Mid` (with root turbo manifest) importing Lake-managed
        // `DepPkg.B` (no dep turbo manifest); editing `DepPkg/A.lean` (even with backdated mtime)
        // or shifting `dep_pkg` `leanOptions`/`moreLeanArgs` must invalidate `App.Mid`.
        fs::write(dep_dir.join("DepPkg/A.lean"), a_src(3)).unwrap();
        run_lake(&proj_dir, &["build", "DepPkg.B"]);
        assert!(!dep_turbo_manifest.exists());
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
        build_project_modules_native(
            &mut store,
            &proj_dir,
            &["App.Mid".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert!(root_turbo_manifest.is_file());
        // Drop `dep_pkg` turbo manifest if native build populated it so `DepPkg` is purely Lake-managed.
        let _ = fs::remove_file(&dep_turbo_manifest);
        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&canon_c),
            )
            .unwrap(),
            0
        );
        let old_a_mtime = fs::metadata(dep_dir.join("DepPkg/A.lean"))
            .unwrap()
            .modified()
            .unwrap();
        fs::write(dep_dir.join("DepPkg/A.lean"), a_src(5)).unwrap();
        fs::File::open(dep_dir.join("DepPkg/A.lean"))
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(old_a_mtime))
            .unwrap();
        fs::write(
            canon.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )
        .unwrap();
        let err = crate::lake_build::ensure_project_imports_fresh_for_check(
            &canon,
            std::slice::from_ref(&canon_c),
        )
        .unwrap_err();
        assert!(
            format!("{err:#}").contains("App.Mid"),
            "root turbo manifest entry `App.Mid` did not go stale when Lake dep `DepPkg.A` changed with preserved mtime: {err:#}"
        );

        // Restore `DepPkg/A.lean` to `3`, then mutate `dep_pkg`'s `leanOptions` with preserved mtime:
        // `verify_lake_trace_options_and_args` must detect the option drift.
        fs::write(dep_dir.join("DepPkg/A.lean"), a_src(3)).unwrap();
        fs::File::open(dep_dir.join("DepPkg/A.lean"))
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(old_a_mtime))
            .unwrap();
        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&canon_c),
            )
            .unwrap(),
            0
        );
        let old_lf_mtime = fs::metadata(dep_dir.join("lakefile.toml"))
            .unwrap()
            .modified()
            .unwrap();
        let dep_lf_shifted =
            dep_lf_base.replace("maxSynthPendingDepth = 3", "maxSynthPendingDepth = 4");
        fs::write(dep_dir.join("lakefile.toml"), dep_lf_shifted).unwrap();
        fs::File::open(dep_dir.join("lakefile.toml"))
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(old_lf_mtime))
            .unwrap();
        let err_opt = crate::lake_build::ensure_project_imports_fresh_for_check(
            &canon,
            std::slice::from_ref(&canon_c),
        )
        .unwrap_err();
        assert!(
            format!("{err_opt:#}").contains("App.Mid"),
            "`dep_pkg` `leanOptions` drift with preserved lakefile mtime escaped freshness gate: {err_opt:#}"
        );

        // Case 3: direct dependency import (`App/Direct.lean` importing `DepPkg.B`) without any
        // intermediate root module or turbo manifest, plus missing `.olean` non-stale behavior.
        fs::write(dep_dir.join("lakefile.toml"), dep_lf_base).unwrap();
        fs::File::open(dep_dir.join("lakefile.toml"))
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(old_lf_mtime))
            .unwrap();
        let direct_file = canon.join("App/Direct.lean");
        fs::write(&direct_file, "import DepPkg.B\n#check DepPkg.h\n").unwrap();
        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&direct_file),
            )
            .unwrap(),
            0
        );
        // Missing `.olean` when `build_missing == false` and no manifest entry exists is NOT marked stale.
        fs::write(
            dep_dir.join("DepPkg/Unbuilt.lean"),
            "def unbuilt : Nat := 7\n",
        )
        .unwrap();
        let unbuilt_user = canon.join("App/UseUnbuilt.lean");
        fs::write(&unbuilt_user, "import DepPkg.Unbuilt\n").unwrap();
        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&unbuilt_user),
            )
            .unwrap(),
            0
        );
        fs::remove_file(dep_dir.join("DepPkg/Unbuilt.lean")).unwrap();
        fs::remove_file(&unbuilt_user).unwrap();
        fs::remove_file(canon.join("turbo-lean.toml")).unwrap();
        build_project_modules_native(
            &mut store,
            &dep_dir,
            &["DepPkg.B".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert!(dep_turbo_manifest.is_file());
        fs::write(
            canon.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )
        .unwrap();
        let dep_lf_weak = dep_lf_base.replace(
            "[leanOptions]",
            "weakLeanArgs = [\"-DwarningAsError=true\"]\n[leanOptions]",
        );
        fs::write(dep_dir.join("lakefile.toml"), dep_lf_weak).unwrap();
        fs::File::open(dep_dir.join("lakefile.toml"))
            .unwrap()
            .set_times(std::fs::FileTimes::new().set_modified(old_lf_mtime))
            .unwrap();
        let err_dep_weak = crate::lake_build::ensure_project_imports_fresh_for_check(
            &canon,
            std::slice::from_ref(&direct_file),
        )
        .unwrap_err()
        .to_string();
        assert!(
            err_dep_weak.contains("Worktree opt-out prevents refreshing stale imports: DepPkg.B"),
            "retained dep turbo manifest missed `weakLeanArgs` drift with preserved mtime: {err_dep_weak}"
        );
        fs::remove_file(canon.join("turbo-lean.toml")).unwrap();
        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&direct_file),
            )
            .unwrap(),
            1
        );
        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&direct_file),
            )
            .unwrap(),
            0
        );

        let canon_dep = dep_dir.canonicalize().unwrap();
        let mid_trace = canon.join(".lake/build/lib/lean/App/Mid.trace");
        let mid_hash = canon.join(".lake/build/lib/lean/App/Mid.olean.hash");
        let dep_b_trace = canon_dep.join(".lake/build/lib/lean/DepPkg/B.trace");
        let dep_a_trace = canon_dep.join(".lake/build/lib/lean/DepPkg/A.trace");
        let assert_optout_stale_preserves_trees =
            |target: &PathBuf, expected_mod: &str, label: &str| {
                fs::write(
                    canon.join("turbo-lean.toml"),
                    "[worktree]\nauto_link = false\n",
                )
                .unwrap();
                let sp = snapshot(&canon).unwrap();
                let sd = snapshot(&canon_dep).unwrap();
                let err = crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon,
                    std::slice::from_ref(target),
                )
                .unwrap_err()
                .to_string();
                assert!(
                    err.contains("Worktree opt-out prevents refreshing stale imports")
                        && err.contains(expected_mod),
                    "{label}: unexpected opt-out result: {err}"
                );
                assert_eq!(
                    snapshot(&canon).unwrap(),
                    sp,
                    "{label}: mutated root `.lake`"
                );
                assert_eq!(
                    snapshot(&canon_dep).unwrap(),
                    sd,
                    "{label}: mutated dep `.lake`"
                );
                fs::remove_file(canon.join("turbo-lean.toml")).unwrap();
            };

        let _ = fs::remove_file(&root_turbo_manifest);
        let _ = fs::remove_file(&dep_turbo_manifest);
        run_lake(&proj_dir, &["build", "App.Mid"]);
        assert!(!root_turbo_manifest.exists() && !dep_turbo_manifest.exists());
        fs::remove_file(&mid_trace).unwrap();
        assert_optout_stale_preserves_trees(&canon_c, "App.Mid", "missing Lake root trace");
        assert!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&canon_c),
            )
            .unwrap()
                >= 1
        );
        assert!(mid_trace.is_file());
        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&canon_c),
            )
            .unwrap(),
            0
        );
        fs::remove_file(&dep_a_trace).unwrap();
        assert_optout_stale_preserves_trees(&direct_file, "DepPkg.B", "missing Lake dep trace");
        run_lake(&dep_dir, &["build", "DepPkg.B"]);
        run_lake(&proj_dir, &["build", "App.Mid"]);
        assert!(dep_a_trace.is_file());

        build_project_modules_native(
            &mut store,
            &dep_dir,
            &["DepPkg.B".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        build_project_modules_native(
            &mut store,
            &proj_dir,
            &["App.Mid".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert!(root_turbo_manifest.is_file() && dep_turbo_manifest.is_file());
        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&canon_c),
            )
            .unwrap(),
            0
        );

        let saved_mid_trace = fs::read(&mid_trace).unwrap();
        fs::remove_file(&mid_trace).unwrap();
        assert_optout_stale_preserves_trees(&canon_c, "App.Mid", "missing manifest root trace");
        fs::write(&mid_trace, &saved_mid_trace).unwrap();

        let saved_mid_hash = fs::read(&mid_hash).unwrap();
        fs::remove_file(&mid_hash).unwrap();
        assert_optout_stale_preserves_trees(
            &canon_c,
            "App.Mid",
            "missing manifest root hash sidecar",
        );
        fs::write(&mid_hash, &saved_mid_hash).unwrap();

        let saved_dep_b_trace = fs::read(&dep_b_trace).unwrap();
        fs::remove_file(&dep_b_trace).unwrap();
        assert_optout_stale_preserves_trees(
            &direct_file,
            "DepPkg.B",
            "missing manifest dep trace (direct)",
        );
        assert_optout_stale_preserves_trees(
            &canon_c,
            "App.Mid",
            "missing manifest dep trace (via root)",
        );
        fs::write(&dep_b_trace, &saved_dep_b_trace).unwrap();

        let saved_dep_a_trace = fs::read(&dep_a_trace).unwrap();
        fs::remove_file(&dep_a_trace).unwrap();
        assert_optout_stale_preserves_trees(
            &direct_file,
            "DepPkg.B",
            "missing transitive manifest dep trace",
        );
        fs::write(&dep_a_trace, &saved_dep_a_trace).unwrap();

        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&canon_c),
            )
            .unwrap(),
            0
        );
        fs::remove_file(&mid_trace).unwrap();
        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&canon_c),
            )
            .unwrap(),
            1
        );
        assert!(mid_trace.is_file());
        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&canon_c),
            )
            .unwrap(),
            0
        );

        let _ = fs::remove_dir_all(&dir);
    }

    /// Astra r4: a trusted dependency module forging a theorem with `debug.skipKernelTC` must
    /// not be importable on the fresh-build, CAS-restore, or stale-manifest paths.
    #[cfg(unix)]
    #[test]
    fn test_trusted_dependency_modules_are_kernel_replayed_before_import() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = make_temp_test_dir("dep_replay");
        let (proj, dep) = (dir.join("app"), dir.join("app/.lake/packages/dep"));
        fs::create_dir_all(dep.join("Dep"))?;
        fs::create_dir_all(dep.join("Forge"))?;
        let toolchain = include_str!("../../../lean/lean-toolchain");
        fs::write(proj.join("lean-toolchain"), toolchain)?;
        fs::write(dep.join("lean-toolchain"), toolchain)?;
        fs::write(
            dep.join("lakefile.toml"),
            "name = \"dep\"\n[[lean_lib]]\nname = \"Dep\"\n[[lean_lib]]\nname = \"Forge\"\n",
        )?;
        fs::write(dep.join("Forge/Bad.lean"), "import Lean\nopen Lean Elab Command Term\nelab \"forge_bad\" : command => liftTermElabM do\n  withOptions (fun o => o.setBool `debug.skipKernelTC true) do\n    Lean.addDecl <| .thmDecl {name := `bad, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro}\nforge_bad\n")?;
        fs::write(
            dep.join("Dep/Bad.lean"),
            "theorem bad : False := True.intro\n",
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep", "dir": ".lake/packages/dep", "configFile": "lakefile.toml", "inherited": false}], "name": "app", "lakeDir": ".lake", "fixedToolchain": false}"#,
        )?;
        fs::write(proj.join("lakefile.toml"), "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"dep\"\npath = \".lake/packages/dep\"\n[[lean_lib]]\nname = \"App\"\n")?;
        fs::write(
            proj.join("App.lean"),
            "import Dep.Bad\ntheorem uses_bad : False := bad\n",
        )?;
        let mut store = TurboStore::open(Some(&dir.join("cache")))?;
        let dep_olean = dep.join(".lake/build/lib/lean/Dep/Bad.olean");
        let manifest_path = dep.join(".lake/build/.turbo_verified_sources.json");
        let build = |store: &mut TurboStore| {
            format!(
                "{:#}",
                build_project_modules_native(
                    store,
                    &proj,
                    &[],
                    "trusted-internal",
                    1,
                    false,
                    true,
                    None,
                )
                .map(|_| ())
                .unwrap_err()
            )
        };
        let assert_rejected = |store: &TurboStore, err: &str, path: &str| {
            assert!(err.contains("Dep.Bad"), "{path}: {err}");
            assert!(
                !proj.join(".lake/build/lib/lean/App.olean").exists(),
                "{path}"
            );
            let cfg = resolve_project_config(&proj).unwrap();
            let (lp_env, _) = build_lean_search_path(&cfg, false);
            assert!(
                !is_olean_replayed_in_store(store, &cfg, &lp_env, &dep_olean),
                "{path}: forged `.olean` must never gain store DB replay authority"
            );
        };
        // 1. Fresh build: a dependency with an elaborator forging a theorem is replayed (and rejected) before App imports it.
        fs::write(dep.join("Dep/Bad.lean"), "import Lean\nopen Lean Elab Command Term\nelab \"forge_bad\" : command => liftTermElabM do\n  withOptions (fun o => o.setBool `debug.skipKernelTC true) do\n    Lean.addDecl <| .thmDecl {name := `bad, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro}\nforge_bad\n")?;
        let err = build(&mut store);
        assert!(err.contains("KernelReplay"), "{err}");
        assert_rejected(&store, &err, "fresh");
        // For steps 2–4, `Dep/Bad.lean` has pure source (`theorem bad : False := True.intro`) while its `.olean`
        // is swapped from `Forge.Bad` so CAS lookup and `external_olean_deps` / manifest freshness paths are exercised
        // without triggering the host-effect elaborator bypass.
        let pure_dep_src = "theorem bad : False := True.intro\n";
        fs::write(dep.join("Dep/Bad.lean"), pure_dep_src)?;
        let forge_sidecars = |olean_p: &Path, c_opt: Option<&Path>, src_text: &str| -> Result<()> {
            let ob = fs::read(olean_p)?;
            let ib = fs::read(olean_p.with_extension("ilean"))?;
            let (oh, ih) = (lake_hash_bytes(&ob), lake_hash_bytes(&ib));
            fs::write(format!("{}.hash", olean_p.display()), format!("{oh:016x}"))?;
            fs::write(
                format!("{}.hash", olean_p.with_extension("ilean").display()),
                format!("{ih:016x}"),
            )?;
            let outputs = if let Some(cp) = c_opt.filter(|p| p.is_file()) {
                let ch = lake_hash_bytes(&fs::read(cp)?);
                fs::write(format!("{}.hash", cp.display()), format!("{ch:016x}"))?;
                serde_json::json!({
                    "o": [format!("{oh:016x}.olean")],
                    "m": false,
                    "i": format!("{ih:016x}.ilean"),
                    "c": format!("{ch:016x}.c"),
                })
            } else {
                serde_json::Value::Null
            };
            let sh = lake_hash_text(src_text);
            let z = 0u64;
            let dh = lake_mix_hash(
                lake_mix_hash(lake_mix_hash(lake_mix_hash(LAKE_NIL_HASH, z), z), z),
                sh,
            );
            let tj = serde_json::json!({
                "schemaVersion": "2025-09-10",
                "depHash": format!("{dh:016x}"),
                "inputs": [["a", format!("{z:016x}")], ["b", format!("{z:016x}")], ["c", format!("{z:016x}")], ["src", format!("{sh:016x}")]],
                "outputs": outputs,
            });
            fs::write(olean_p.with_extension("trace"), serde_json::to_vec(&tj)?)?;
            Ok(())
        };
        let forge_build = |dep_olean: &Path| -> Result<()> {
            let lake = Command::new("lake")
                .args(["build", "Forge.Bad"])
                .current_dir(&proj)
                .output()?;
            anyhow::ensure!(
                lake.status.success(),
                "{}",
                String::from_utf8_lossy(&lake.stderr)
            );
            let forge_dir = dep.join(".lake/build/lib/lean/Forge");
            let dst_dir = dep_olean.parent().unwrap();
            fs::create_dir_all(dst_dir)?;
            fs::copy(forge_dir.join("Bad.olean"), dep_olean)?;
            fs::copy(forge_dir.join("Bad.ilean"), dst_dir.join("Bad.ilean"))?;
            let ir_src = dep.join(".lake/build/ir/Forge");
            let ir_dst = dep.join(".lake/build/ir/Dep");
            fs::create_dir_all(&ir_dst)?;
            let dep_c = ir_dst.join("Bad.c");
            if ir_src.join("Bad.c").is_file() {
                fs::copy(ir_src.join("Bad.c"), &dep_c)?;
            }
            if ir_src.join("Bad.setup.json").is_file() {
                fs::copy(ir_src.join("Bad.setup.json"), ir_dst.join("Bad.setup.json"))?;
            }
            forge_sidecars(dep_olean, Some(&dep_c), pure_dep_src)
        };
        // 2. CAS restore of the unreplayed Lake artifacts (as stored before this fix).
        forge_build(&dep_olean)?;
        let cfg = resolve_project_config(&proj)?;
        let dag = build_module_dag_with_trust(&cfg, &[], false)?;
        let node = &dag.nodes["Dep.Bad"];
        let key = compute_module_cas_key(&cfg, node, &[], node.needs_c)?;
        store_module_artifacts_in_cas(
            &mut store,
            &proj,
            node,
            &key,
            &cfg.toolchain,
            "trusted-internal",
            1,
            0,
        )?;
        fs::remove_dir_all(dep.join(".lake/build"))?;
        let err = build(&mut store);
        assert!(err.contains("materialized CAS hit"), "{err}");
        assert_rejected(&store, &err, "restore");
        // 3. A forged current-version `.turbo_verified_sources.json` manifest makes the `.olean`
        // appear fresh, yet `TurboStore` DB holds no replay row, so `build`, `ci-verify`, `check`,
        // and `pr-verify` all kernel-replay and reject `Dep.Bad`!
        forge_build(&dep_olean)?;
        let dep_olean_digest = compute_olean_artifact_set_digest(&dep_olean)?;
        let ws_inputs = workspace_lake_inputs_digest(&cfg)?;
        let policy_dig = crate::splitter::current_kernel_policy_digest();
        let forged_dep_manifest = serde_json::json!({
            "pkg_name": node.pkg_name,
            "toolchain": cfg.toolchain,
            "lean_githash": cfg.lean_githash,
            "pkg_config_digest": node.pkg_config_digest,
            "lake_inputs_digest": &ws_inputs,
            "workspace_config_digest": cfg.canonical_config_digest,
            "allowed_axioms": crate::splitter::allowed_axioms(),
            "kernel_policy_digest": &policy_dig,
            "modules": {
                "Dep/Bad.lean": {
                    "src_blake3": node.src_blake3,
                    "olean_artifact_digest": &dep_olean_digest,
                    "lake_inputs_digest": &ws_inputs,
                    "kernel_audited": true,
                    "import_olean_digests": {},
                    "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION,
                }
            }
        });
        fs::write(&manifest_path, serde_json::to_vec(&forged_dep_manifest)?)?;
        let fresh_dag = build_module_dag_with_trust(&cfg, &[], false)?;
        assert!(
            !fresh_dag.nodes.contains_key("Dep.Bad"),
            "forged manifest exercises external_olean_deps path"
        );
        let err = build(&mut store);
        assert!(err.contains("KernelReplay"), "forged manifest build: {err}");
        assert_rejected(&store, &err, "forged manifest build");
        // 4. `check` and `ci-verify` with forged manifest on disk also reject `Dep.Bad` via store DB authority.
        fs::write(&manifest_path, serde_json::to_vec(&forged_dep_manifest)?)?;
        let err = crate::check::evaluate_check_command_value(
            &mut store,
            proj.join("App.lean"),
            None,
            proj.clone(),
        )
        .unwrap_err();
        assert!(
            format!("{err:#}").contains("KernelReplay"),
            "check: {err:#}"
        );
        fs::write(&manifest_path, serde_json::to_vec(&forged_dep_manifest)?)?;
        let ci_err = crate::pr_verify::run_ci_verify_command(
            &mut store,
            true,
            "trusted".to_string(),
            proj.clone(),
            None,
            None,
            false,
            None,
        )
        .unwrap_err();
        assert!(
            format!("{ci_err:#}").contains("KernelReplay"),
            "ci-verify: {ci_err:#}"
        );
        // 5. Even if `App` itself is built with `Dep.Bad`'s forged `.olean` and a forged root
        // `.turbo_verified_sources.json`, `build`, `ci-verify`, `check`, and `pr-verify` reject it
        // because `TurboStore` DB lacks replay authority.
        forge_build(&dep_olean)?;
        let (lp_env_app, _) = build_lean_search_path(&cfg, false);
        let app_lib_dir = proj.join(".lake/build/lib/lean");
        let app_ir_dir = proj.join(".lake/build/ir");
        fs::create_dir_all(&app_lib_dir)?;
        fs::create_dir_all(&app_ir_dir)?;
        let lean_app = Command::new(&cfg.lean_bin)
            .env("LEAN_PATH", &lp_env_app)
            .arg(proj.join("App.lean"))
            .arg("-R")
            .arg(&proj)
            .arg("-o")
            .arg(app_lib_dir.join("App.olean"))
            .arg("-i")
            .arg(app_lib_dir.join("App.ilean"))
            .arg("-c")
            .arg(app_ir_dir.join("App.c"))
            .current_dir(&proj)
            .output()?;
        anyhow::ensure!(
            lean_app.status.success(),
            "{}",
            String::from_utf8_lossy(&lean_app.stderr)
        );
        fs::write(&manifest_path, serde_json::to_vec(&forged_dep_manifest)?)?;
        let app_olean = proj.join(".lake/build/lib/lean/App.olean");
        let app_src_raw = fs::read_to_string(proj.join("App.lean"))?;
        forge_sidecars(&app_olean, Some(&app_ir_dir.join("App.c")), &app_src_raw)?;
        let forged_root_manifest = serde_json::json!({
            "pkg_name": cfg.root_pkg.name,
            "toolchain": cfg.toolchain,
            "lean_githash": cfg.lean_githash,
            "pkg_config_digest": cfg.root_pkg.config_digest,
            "lake_inputs_digest": &ws_inputs,
            "workspace_config_digest": cfg.canonical_config_digest,
            "allowed_axioms": crate::splitter::allowed_axioms(),
            "kernel_policy_digest": &policy_dig,
            "modules": {
                "App.lean": {
                    "src_blake3": blake3::hash(app_src_raw.as_bytes()).to_hex().to_string(),
                    "olean_artifact_digest": compute_olean_artifact_set_digest(&app_olean)?,
                    "lake_inputs_digest": &ws_inputs,
                    "kernel_audited": true,
                    "import_olean_digests": { "Dep.Bad": &dep_olean_digest },
                    "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION,
                }
            }
        });
        fs::write(
            proj.join(".lake/build/.turbo_verified_sources.json"),
            serde_json::to_vec(&forged_root_manifest)?,
        )?;
        let build_cmd_err = crate::lake_build::run_build_command(
            &mut store,
            true,
            vec![],
            proj.clone(),
            "trusted".to_string(),
            1,
            false,
        )
        .unwrap_err();
        assert!(
            format!("{build_cmd_err:#}").contains("KernelReplay"),
            "run_build_command forged root manifest: {build_cmd_err:#}"
        );
        let ci_root_err = crate::pr_verify::run_ci_verify_command(
            &mut store,
            true,
            "trusted".to_string(),
            proj.clone(),
            None,
            None,
            false,
            None,
        )
        .unwrap_err();
        assert!(
            format!("{ci_root_err:#}").contains("KernelReplay"),
            "ci-verify forged root manifest: {ci_root_err:#}"
        );
        let check_decl_err = crate::check::evaluate_check_command_value(
            &mut store,
            proj.join("App.lean"),
            Some("uses_bad".to_string()),
            proj.clone(),
        )
        .unwrap_err();
        assert!(
            format!("{check_decl_err:#}").contains("KernelReplay"),
            "check --decl forged root manifest: {check_decl_err:#}"
        );
        // 6. Initialize a git base commit and edit `App.lean`'s proof body so `pr-verify` runs in
        // trusted mode with forged `.turbo_verified_sources.json` manifests on disk: `TurboStore` DB
        // still has no replay row, so `pr-verify` rejects `Dep.Bad` via independent kernel replay.
        for args in [
            vec!["init"],
            vec!["config", "user.email", "test@example.com"],
            vec!["config", "user.name", "Test"],
            vec![
                "add",
                "lean-toolchain",
                "lakefile.toml",
                "lake-manifest.json",
                "App.lean",
            ],
            vec!["commit", "-m", "base"],
        ] {
            let g = Command::new("git")
                .args(&args)
                .current_dir(&proj)
                .output()?;
            anyhow::ensure!(
                g.status.success(),
                "git {:?}: {}",
                args,
                String::from_utf8_lossy(&g.stderr)
            );
        }
        let edited_app = "import Dep.Bad\ntheorem uses_bad : False := by exact bad\n";
        fs::write(proj.join("App.lean"), edited_app)?;
        forge_build(&dep_olean)?;
        let lean_app2 = Command::new(&cfg.lean_bin)
            .env("LEAN_PATH", &lp_env_app)
            .arg(proj.join("App.lean"))
            .arg("-R")
            .arg(&proj)
            .arg("-o")
            .arg(app_lib_dir.join("App.olean"))
            .arg("-i")
            .arg(app_lib_dir.join("App.ilean"))
            .arg("-c")
            .arg(app_ir_dir.join("App.c"))
            .current_dir(&proj)
            .output()?;
        anyhow::ensure!(
            lean_app2.status.success(),
            "{}",
            String::from_utf8_lossy(&lean_app2.stderr)
        );
        forge_sidecars(&app_olean, Some(&app_ir_dir.join("App.c")), edited_app)?;
        let ws_inputs2 = workspace_lake_inputs_digest(&resolve_project_config(&proj)?)?;
        let forged_dep_manifest2 = serde_json::json!({
            "pkg_name": node.pkg_name,
            "toolchain": cfg.toolchain,
            "lean_githash": cfg.lean_githash,
            "pkg_config_digest": node.pkg_config_digest,
            "lake_inputs_digest": &ws_inputs2,
            "workspace_config_digest": cfg.canonical_config_digest,
            "allowed_axioms": crate::splitter::allowed_axioms(),
            "kernel_policy_digest": &policy_dig,
            "modules": {
                "Dep/Bad.lean": {
                    "src_blake3": node.src_blake3,
                    "olean_artifact_digest": &dep_olean_digest,
                    "lake_inputs_digest": &ws_inputs2,
                    "kernel_audited": true,
                    "import_olean_digests": {},
                    "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION,
                }
            }
        });
        fs::write(&manifest_path, serde_json::to_vec(&forged_dep_manifest2)?)?;
        let forged_root_manifest2 = serde_json::json!({
            "pkg_name": cfg.root_pkg.name,
            "toolchain": cfg.toolchain,
            "lean_githash": cfg.lean_githash,
            "pkg_config_digest": cfg.root_pkg.config_digest,
            "lake_inputs_digest": &ws_inputs2,
            "workspace_config_digest": cfg.canonical_config_digest,
            "allowed_axioms": crate::splitter::allowed_axioms(),
            "kernel_policy_digest": &policy_dig,
            "modules": {
                "App.lean": {
                    "src_blake3": blake3::hash(edited_app.as_bytes()).to_hex().to_string(),
                    "olean_artifact_digest": compute_olean_artifact_set_digest(&app_olean)?,
                    "lake_inputs_digest": &ws_inputs2,
                    "kernel_audited": true,
                    "import_olean_digests": { "Dep.Bad": &dep_olean_digest },
                    "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION,
                }
            }
        });
        fs::write(
            proj.join(".lake/build/.turbo_verified_sources.json"),
            serde_json::to_vec(&forged_root_manifest2)?,
        )?;
        let pr_err = crate::pr_verify::run_pr_verify_command(
            &mut store,
            true,
            proj.clone(),
            "HEAD".to_string(),
            "trusted".to_string(),
            false,
            None,
            None,
            None,
            None,
            false,
            1,
            None,
        )
        .unwrap_err();
        assert!(
            format!("{pr_err:#}").contains("KernelReplay"),
            "pr-verify forged manifest: {pr_err:#}"
        );
        drop(store);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    /// Regression test: a module under `Std.*` (`Std.Forge`) that is NOT in the installed
    /// toolchain `lib/lean` (or shadows it on `LEAN_PATH` / package search order) must never be
    /// exempted as a builtin toolchain module, and must be kernel-replayed and rejected across
    /// `build`, `check`, `ci-verify`, and `pr-verify`.
    #[cfg(unix)]
    #[test]
    fn test_std_prefix_module_is_not_exempted_as_builtin_toolchain_module() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = make_temp_test_dir("std_forge_replay");
        let proj = dir.join("app");
        let ext_pkg = dir.join("ext_std");
        fs::create_dir_all(&proj)?;
        fs::create_dir_all(ext_pkg.join("Std"))?;
        let toolchain = include_str!("../../../lean/lean-toolchain");
        fs::write(proj.join("lean-toolchain"), toolchain)?;
        fs::write(ext_pkg.join("lean-toolchain"), toolchain)?;
        let forge_src = "import Init\n";
        fs::write(ext_pkg.join("Std/Forge.lean"), forge_src)?;
        fs::write(
            ext_pkg.join("lakefile.toml"),
            "name = \"ext_std\"\n[[lean_lib]]\nname = \"ExtStd\"\nroots = [\"Std.Forge\"]\n",
        )?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"app\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\n",
        )?;
        fs::write(
            proj.join("App.lean"),
            "import Std.Forge\ntheorem bad_from_std : False := std_forged_false\n",
        )?;
        let cfg = resolve_project_config(&proj)?;
        let lake_bin = cfg.lean_bin.parent().expect("lean bin parent").join("lake");
        let lake_ext = Command::new(&lake_bin)
            .args(["build", "Std.Forge"])
            .current_dir(&ext_pkg)
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .output()?;
        anyhow::ensure!(
            lake_ext.status.success(),
            "lake build ext Std.Forge: {} {}",
            String::from_utf8_lossy(&lake_ext.stdout),
            String::from_utf8_lossy(&lake_ext.stderr)
        );
        let ext_lib_lean = ext_pkg.join(".lake/build/lib/lean");
        let ext_olean = ext_lib_lean.join("Std/Forge.olean");
        let forged_olean = dir.join("Forged.olean");
        let maker_path = dir.join("Maker.lean");
        fs::write(
            &maker_path,
            "import Lean\nopen Lean\ndef main (args : List String) : IO Unit := do\n  searchPathRef.set [System.FilePath.mk args[1]!]\n  let env ← importModules #[{ module := `Init }] {} 0\n  let env := env.setMainModule `Std.Forge\n  let decl : Declaration := .thmDecl {\n    name := `std_forged_false,\n    levelParams := [],\n    type := mkConst ``False,\n    value := mkConst ``True.intro\n  }\n  match env.addDeclCore 0 0 decl none false with\n  | Except.ok env2 => writeModule env2 args[0]! false\n  | Except.error _ => throw <| IO.userError \"addDecl failed\"\n",
        )?;
        let compile_ext = Command::new(&cfg.lean_bin)
            .arg("--run")
            .arg(&maker_path)
            .arg(&forged_olean)
            .arg(&cfg.toolchain_lib_lean)
            .env("LEAN_PATH", &cfg.toolchain_lib_lean)
            .output()?;
        anyhow::ensure!(
            compile_ext.status.success(),
            "stdout: {} stderr: {}",
            String::from_utf8_lossy(&compile_ext.stdout),
            String::from_utf8_lossy(&compile_ext.stderr)
        );
        let _ = fs::remove_file(ext_lib_lean.join("Std/Forge.olean.server"));
        let _ = fs::remove_file(ext_lib_lean.join("Std/Forge.olean.server.hash"));
        let _ = fs::remove_file(ext_lib_lean.join("Std/Forge.olean.private"));
        let _ = fs::remove_file(ext_lib_lean.join("Std/Forge.olean.private.hash"));
        let _ = fs::remove_file(ext_lib_lean.join("Std/Forge.ir"));
        let _ = fs::remove_file(ext_lib_lean.join("Std/Forge.ir.hash"));
        let _ = fs::remove_file(ext_lib_lean.join("Std/Forge.ir.sig"));
        let _ = fs::remove_file(ext_lib_lean.join("Std/Forge.ir.sig.hash"));
        fs::copy(&forged_olean, &ext_olean)?;
        let ext_olean_h = lake_hash_bytes(&fs::read(&ext_olean)?);
        fs::write(
            ext_lib_lean.join("Std/Forge.olean.hash"),
            format!("{:016x}\n", ext_olean_h),
        )?;
        let ext_trace_path = ext_lib_lean.join("Std/Forge.trace");
        let mut ext_tv: serde_json::Value = serde_json::from_slice(&fs::read(&ext_trace_path)?)?;
        ext_tv["outputs"]["m"] = serde_json::Value::Bool(false);
        ext_tv["outputs"]["o"] = serde_json::json!([format!("{:016x}.olean", ext_olean_h)]);
        if let Some(obj) = ext_tv["outputs"].as_object_mut() {
            obj.remove("r");
            obj.remove("rs");
        }
        fs::write(&ext_trace_path, serde_json::to_vec(&ext_tv)?)?;
        assert!(ext_olean.is_file(), "lean must emit Std/Forge.olean");
        assert!(
            !is_builtin_toolchain_module(
                &cfg.toolchain_lib_lean,
                Some(&cfg.lean_githash),
                "Std.Forge"
            ),
            "Std.Forge does not exist in toolchain_lib_lean and must not be exempted by prefix"
        );
        assert!(
            is_builtin_toolchain_module(&cfg.toolchain_lib_lean, Some(&cfg.lean_githash), "Init"),
            "real toolchain Init.olean with matching githash must be recognized"
        );
        assert!(
            !is_verified_toolchain_olean_file(
                &cfg.toolchain_lib_lean,
                Some(&cfg.lean_githash),
                &ext_olean
            ),
            "external Std/Forge.olean outside toolchain_lib_lean must not pass toolchain verification"
        );

        // Part A: Prebuilt `Std.Forge` supplied via `LEAN_PATH` (earlier in search order than toolchain).
        let prev_lp = std::env::var_os("LEAN_PATH");
        std::env::set_var("LEAN_PATH", &ext_lib_lean);
        let res_a = (|| -> Result<()> {
            let mut store = TurboStore::open(Some(&dir.join("cache_lp")))?;
            let dag = build_module_dag_with_trust(&cfg, &[], false)?;
            assert!(
                dag.nodes["App"]
                    .external_olean_deps
                    .iter()
                    .any(|(m, _)| m == "Std.Forge"),
                "LEAN_PATH Std.Forge must be tracked in external_olean_deps, not skipped as toolchain"
            );
            let build_err = build_project_modules_native(
                &mut store,
                &proj,
                &[],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap_err();
            assert!(
                format!("{build_err:#}").contains("KernelReplay"),
                "native build with LEAN_PATH Std.Forge: {build_err:#}"
            );
            let check_err = crate::check::evaluate_check_command_value(
                &mut store,
                proj.join("App.lean"),
                None,
                proj.clone(),
            )
            .unwrap_err();
            assert!(
                format!("{check_err:#}").contains("KernelReplay"),
                "check with LEAN_PATH Std.Forge: {check_err:#}"
            );
            Ok(())
        })();
        match prev_lp {
            Some(v) => std::env::set_var("LEAN_PATH", v),
            None => std::env::remove_var("LEAN_PATH"),
        }
        res_a?;

        // Part B: Dependency-package `Std/Forge.lean` (`dep_std`): `Std.Forge` is a prebuilt
        // dependency `.olean` in `.lake/packages/dep_std` (whose source only imports `Init`, so
        // `Std.Forge.olean` has zero `Std.*` transitive imports). Before our fix, `Std.Forge` was
        // skipped by prefix across `build_module_dag_with_trust`, `are_all_project_oleans_replayed_in_store`,
        // `ensure_imported_oleans_replayed`, and `stateless_imports_replayed_in_store`; now all four
        // entrypoints (`build`, `ci-verify`, `check`, and `pr-verify`) kernel-replay `Std/Forge.olean`
        // and reject it.
        let dep_std = proj.join(".lake/packages/dep_std");
        fs::create_dir_all(dep_std.join("Std"))?;
        fs::write(dep_std.join("lean-toolchain"), toolchain)?;
        fs::write(dep_std.join("Std/Forge.lean"), forge_src)?;
        fs::write(
            dep_std.join("lakefile.toml"),
            "name = \"dep_std\"\n[[lean_lib]]\nname = \"DepStd\"\nroots = [\"Std.Forge\"]\n",
        )?;
        let dep_lib_lean = dep_std.join(".lake/build/lib/lean");
        let lake_bin = cfg.lean_bin.parent().expect("lean bin parent").join("lake");
        let lake_dep = Command::new(&lake_bin)
            .args(["build", "Std.Forge"])
            .current_dir(&dep_std)
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .output()?;
        anyhow::ensure!(
            lake_dep.status.success(),
            "lake build Std.Forge: {} {}",
            String::from_utf8_lossy(&lake_dep.stdout),
            String::from_utf8_lossy(&lake_dep.stderr)
        );
        // Replace `Std/Forge.olean` with the forged `.olean` containing `std_forged_false : False`
        // and update `Std/Forge.trace`'s `outputs.o[0]` hash so `verify_module_lake_sidecars`
        // accepts `Std.Forge` as a fresh Lake-built dependency artifact!
        let _ = fs::remove_file(dep_lib_lean.join("Std/Forge.olean.server"));
        let _ = fs::remove_file(dep_lib_lean.join("Std/Forge.olean.server.hash"));
        let _ = fs::remove_file(dep_lib_lean.join("Std/Forge.olean.private"));
        let _ = fs::remove_file(dep_lib_lean.join("Std/Forge.olean.private.hash"));
        let _ = fs::remove_file(dep_lib_lean.join("Std/Forge.ir"));
        let _ = fs::remove_file(dep_lib_lean.join("Std/Forge.ir.hash"));
        let _ = fs::remove_file(dep_lib_lean.join("Std/Forge.ir.sig"));
        let _ = fs::remove_file(dep_lib_lean.join("Std/Forge.ir.sig.hash"));
        fs::copy(&ext_olean, dep_lib_lean.join("Std/Forge.olean"))?;
        let new_olean_h = lake_hash_bytes(&fs::read(dep_lib_lean.join("Std/Forge.olean"))?);
        fs::write(
            dep_lib_lean.join("Std/Forge.olean.hash"),
            format!("{:016x}\n", new_olean_h),
        )?;
        let dep_trace_path = dep_lib_lean.join("Std/Forge.trace");
        let mut dep_tv: serde_json::Value = serde_json::from_slice(&fs::read(&dep_trace_path)?)?;
        dep_tv["outputs"]["m"] = serde_json::Value::Bool(false);
        dep_tv["outputs"]["o"] = serde_json::json!([format!("{:016x}.olean", new_olean_h)]);
        if let Some(obj) = dep_tv["outputs"].as_object_mut() {
            obj.remove("r");
            obj.remove("rs");
        }
        fs::write(&dep_trace_path, serde_json::to_vec(&dep_tv)?)?;
        fs::write(
            proj.join("lake-manifest.json"),
            r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep_std", "dir": ".lake/packages/dep_std", "configFile": "lakefile.toml", "inherited": false}], "name": "app", "lakeDir": ".lake", "fixedToolchain": false}"#,
        )?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"dep_std\"\npath = \".lake/packages/dep_std\"\n[[lean_lib]]\nname = \"App\"\n",
        )?;
        let cfg_b = resolve_project_config(&proj)?;
        let dep_pkg_cfg = &cfg_b.dep_pkgs[0];
        let dep_std_olean_digest =
            compute_olean_artifact_set_digest(&dep_lib_lean.join("Std/Forge.olean"))?;
        let forged_dep_std_manifest = serde_json::json!({
            "pkg_name": dep_pkg_cfg.name,
            "toolchain": cfg_b.toolchain,
            "lean_githash": cfg_b.lean_githash,
            "pkg_config_digest": dep_pkg_cfg.config_digest,
            "workspace_config_digest": cfg_b.canonical_config_digest,
            "allowed_axioms": crate::splitter::allowed_axioms(),
            "modules": {
                "Std/Forge.lean": {
                    "src_blake3": blake3::hash(forge_src.as_bytes()).to_hex().to_string(),
                    "olean_artifact_digest": &dep_std_olean_digest,
                    "kernel_audited": true,
                    "import_olean_digests": {},
                }
            }
        });
        fs::write(
            dep_std.join(".lake/build/.turbo_verified_sources.json"),
            serde_json::to_vec(&forged_dep_std_manifest)?,
        )?;
        let dag_b = build_module_dag_with_trust(&cfg_b, &[], false)?;
        assert!(
            dag_b.nodes["App"]
                .external_olean_deps
                .iter()
                .any(|(m, _)| m == "Std.Forge"),
            "dep_std Std.Forge must be in App's external_olean_deps (not skipped as builtin toolchain)"
        );
        let lake_app = Command::new(&lake_bin)
            .args(["build", "App"])
            .current_dir(&proj)
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .output()?;
        anyhow::ensure!(
            lake_app.status.success(),
            "lake build App: {} {}",
            String::from_utf8_lossy(&lake_app.stdout),
            String::from_utf8_lossy(&lake_app.stderr)
        );
        let proj_lib_lean = proj.join(".lake/build/lib/lean");
        let app_src_b = fs::read_to_string(proj.join("App.lean"))?;
        let forged_root_b = serde_json::json!({
            "pkg_name": cfg_b.root_pkg.name,
            "toolchain": cfg_b.toolchain,
            "lean_githash": cfg_b.lean_githash,
            "pkg_config_digest": cfg_b.root_pkg.config_digest,
            "workspace_config_digest": cfg_b.canonical_config_digest,
            "allowed_axioms": crate::splitter::allowed_axioms(),
            "modules": {
                "App.lean": {
                    "src_blake3": blake3::hash(app_src_b.as_bytes()).to_hex().to_string(),
                    "olean_artifact_digest": compute_olean_artifact_set_digest(&proj_lib_lean.join("App.olean"))?,
                    "kernel_audited": true,
                    "import_olean_digests": { "Std.Forge": &dep_std_olean_digest },
                }
            }
        });
        fs::write(
            proj.join(".lake/build/.turbo_verified_sources.json"),
            serde_json::to_vec(&forged_root_b)?,
        )?;
        let mut store_b = TurboStore::open(Some(&dir.join("cache_proj")))?;
        let build_cmd_err = crate::lake_build::run_build_command(
            &mut store_b,
            true,
            vec![],
            proj.clone(),
            "trusted".to_string(),
            1,
            false,
        )
        .unwrap_err();
        assert!(
            format!("{build_cmd_err:#}").contains("KernelReplay"),
            "run_build_command project Std.Forge: {build_cmd_err:#}"
        );
        let ci_err = crate::pr_verify::run_ci_verify_command(
            &mut store_b,
            true,
            "trusted".to_string(),
            proj.clone(),
            None,
            None,
            false,
            None,
        )
        .unwrap_err();
        assert!(
            format!("{ci_err:#}").contains("KernelReplay"),
            "ci-verify project Std.Forge: {ci_err:#}"
        );
        let check_proj_err = crate::check::evaluate_check_command_value(
            &mut store_b,
            proj.join("App.lean"),
            Some("bad_from_std".to_string()),
            proj.clone(),
        )
        .unwrap_err();
        assert!(
            format!("{check_proj_err:#}").contains("KernelReplay"),
            "check --decl project Std.Forge: {check_proj_err:#}"
        );

        for args in [
            vec!["init"],
            vec!["config", "user.email", "test@example.com"],
            vec!["config", "user.name", "Test"],
            vec![
                "add",
                "lean-toolchain",
                "lakefile.toml",
                "lake-manifest.json",
                "App.lean",
            ],
            vec!["commit", "-m", "base"],
        ] {
            let g = Command::new("git")
                .args(&args)
                .current_dir(&proj)
                .output()?;
            anyhow::ensure!(
                g.status.success(),
                "git {:?}: {}",
                args,
                String::from_utf8_lossy(&g.stderr)
            );
        }
        let edited_app_b =
            "import Std.Forge\ntheorem bad_from_std : False := by exact std_forged_false\n";
        fs::write(proj.join("App.lean"), edited_app_b)?;
        let lake_app2 = Command::new(&lake_bin)
            .args(["build", "App"])
            .current_dir(&proj)
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .output()?;
        anyhow::ensure!(
            lake_app2.status.success(),
            "lake build App (2): {} {}",
            String::from_utf8_lossy(&lake_app2.stdout),
            String::from_utf8_lossy(&lake_app2.stderr)
        );
        let forged_root_b2 = serde_json::json!({
            "pkg_name": cfg_b.root_pkg.name,
            "toolchain": cfg_b.toolchain,
            "lean_githash": cfg_b.lean_githash,
            "pkg_config_digest": cfg_b.root_pkg.config_digest,
            "workspace_config_digest": cfg_b.canonical_config_digest,
            "allowed_axioms": crate::splitter::allowed_axioms(),
            "modules": {
                "App.lean": {
                    "src_blake3": blake3::hash(edited_app_b.as_bytes()).to_hex().to_string(),
                    "olean_artifact_digest": compute_olean_artifact_set_digest(&proj_lib_lean.join("App.olean"))?,
                    "kernel_audited": true,
                    "import_olean_digests": { "Std.Forge": &dep_std_olean_digest },
                }
            }
        });
        fs::write(
            proj.join(".lake/build/.turbo_verified_sources.json"),
            serde_json::to_vec(&forged_root_b2)?,
        )?;
        let pr_err = crate::pr_verify::run_pr_verify_command(
            &mut store_b,
            true,
            proj.clone(),
            "HEAD".to_string(),
            "trusted".to_string(),
            false,
            None,
            None,
            None,
            None,
            false,
            1,
            None,
        )
        .unwrap_err();
        assert!(
            format!("{pr_err:#}").contains("KernelReplay"),
            "pr-verify project Std.Forge: {pr_err:#}"
        );
        drop(store_b);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_native_module_builder_cas_partial_invalidation_lazy_c_and_lake_differential() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("native_e2e");
        let store_dir = dir.join(".turbo_store");
        let proj_dir = dir.join("proj");
        let dep_dir = proj_dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("DepPkg")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepPkg\"\nroots = [\"DepPkg.Base\"]\n",
        )
        .unwrap();
        fs::write(
            dep_dir.join("DepPkg/Base.lean"),
            "namespace DepPkg\ndef baseVal : Nat := 10\nend DepPkg\n",
        )
        .unwrap();
        let manifest_json = r#"{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {
      "type": "path",
      "name": "dep_pkg",
      "dir": ".lake/packages/dep_pkg",
      "configFile": "lakefile.toml",
      "inherited": false
    }
  ],
  "name": "app_pkg",
  "lakeDir": ".lake",
  "fixedToolchain": false
}"#;
        fs::write(proj_dir.join("lake-manifest.json"), manifest_json).unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[leanOptions]\nautoImplicit = false\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        // App.A imports DepPkg.Base
        fs::write(
            proj_dir.join("App/A.lean"),
            "import DepPkg.Base\nnamespace App\ndef aVal : Nat := DepPkg.baseVal + 5\ntheorem a_eq : aVal = 15 := rfl\nend App\n",
        )
        .unwrap();
        // App.B imports App.A
        fs::write(
            proj_dir.join("App/B.lean"),
            "import App.A\nnamespace App\ntheorem b_thm : aVal + 1 = 16 := rfl\nend App\n",
        )
        .unwrap();
        // App.Indep is a Lean 4.35 `module` completely independent of App.A and App.B
        fs::write(
            proj_dir.join("App/Indep.lean"),
            "module\n@[expose] public def indepVal : Nat := 99\npublic theorem indep_thm : indepVal = 99 := rfl\n",
        )
        .unwrap();
        let mut store = TurboStore::open(Some(&store_dir)).unwrap();
        // 1. Cold build: compiles DepPkg.Base, App.A, App.Indep, App.B
        let rep1 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep1.modules_total, 4);
        assert_eq!(rep1.modules_compiled, 4);
        assert_eq!(rep1.modules_cached, 0);
        let build_lib = proj_dir.join(".lake/build/lib/lean/App");
        assert!(build_lib.join("A.olean").is_file());
        assert!(build_lib.join("A.ilean").is_file());
        assert!(build_lib.join("B.olean").is_file());
        assert!(build_lib.join("Indep.olean").is_file());
        // Verify Lean 4.35 `module` companion artifacts (.olean.server, .olean.private)
        assert!(build_lib.join("Indep.olean.server").is_file());
        assert!(build_lib.join("Indep.olean.private").is_file());
        // Verify lazy `.c` policy: pure library modules without `precompileModules` or `@[export]` do not emit `.c`
        assert!(!proj_dir.join(".lake/build/ir/App/A.c").is_file());
        // 2. Warm build with clean `.lake/build` (both root and dep): all 4 modules hit per-module CAS!
        fs::remove_dir_all(proj_dir.join(".lake/build")).unwrap();
        fs::remove_dir_all(dep_dir.join(".lake/build")).unwrap();
        let rep2 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep2.modules_total, 4);
        assert_eq!(rep2.modules_compiled, 0);
        assert_eq!(rep2.modules_cached, 4);
        assert!(build_lib.join("Indep.olean.server").is_file());
        assert!(build_lib.join("Indep.olean.private").is_file());
        // 3. Partial invalidation: modify leaf `App/B.lean`; `App.A` and `App.Indep` MUST hit CAS
        // (and `DepPkg.Base` is already fresh in `.lake/packages/dep_pkg/.lake/build`)!
        fs::write(
            proj_dir.join("App/B.lean"),
            "import App.A\nnamespace App\ntheorem b_thm : aVal + 2 = 17 := rfl\nend App\n",
        )
        .unwrap();
        let rep3 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep3.modules_compiled, 1);
        assert_eq!(rep3.compiled_modules, vec!["App.B".to_string()]);
        assert_eq!(rep3.modules_cached, 2);
        assert!(rep3.cached_modules.contains(&"App.A".to_string()));
        assert!(rep3.cached_modules.contains(&"App.Indep".to_string()));
        // 4. Upstream dependency invalidation: modify `App/A.lean`; `App.A` and `App.B` recompile, while `App.Indep` hits CAS!
        fs::write(
            proj_dir.join("App/A.lean"),
            "import DepPkg.Base\nnamespace App\ndef aVal : Nat := DepPkg.baseVal + 20\ntheorem a_eq : aVal = 30 := rfl\nend App\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("App/B.lean"),
            "import App.A\nnamespace App\ntheorem b_thm : aVal + 2 = 32 := rfl\nend App\n",
        )
        .unwrap();
        let rep4 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep4.modules_compiled, 2);
        assert_eq!(
            rep4.compiled_modules,
            vec!["App.A".to_string(), "App.B".to_string()]
        );
        assert_eq!(rep4.modules_cached, 1);
        assert!(rep4.cached_modules.contains(&"App.Indep".to_string()));
        // 5. Explicit `:c` facet materializes `.c` codegen
        let rep5 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &["App.A:c".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep5.modules_total, 1); // App.A (DepPkg.Base is fresh external .olean)
        assert!(proj_dir.join(".lake/build/ir/App/A.c").is_file());
        // 6. Differential test against `lake build` on an isolated single-package project
        let diff_dir = dir.join("diff_proj");
        fs::create_dir_all(diff_dir.join("Diff")).unwrap();
        fs::write(
            diff_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            diff_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage «diff» where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n@[default_target]\nlean_lib «Diff» where\n  globs := #[.submodules `Diff]\n",
        )
        .unwrap();
        fs::write(
            diff_dir.join("Diff/Core.lean"),
            "namespace Diff\ndef sq (n : Nat) : Nat := n * n\ntheorem sq_two : sq 2 = 4 := rfl\nend Diff\n",
        )
        .unwrap();
        fs::write(
            diff_dir.join("Diff/Use.lean"),
            "import Diff.Core\nnamespace Diff\ntheorem sq_three : sq 3 = 9 := rfl\nend Diff\n",
        )
        .unwrap();
        fs::write(
            diff_dir.join("Diff/ModBase.lean"),
            "module\nnamespace Diff\npublic def mbase : Nat := 5\nend Diff\n",
        )
        .unwrap();
        fs::write(
            diff_dir.join("Diff/ModSys.lean"),
            "module\npublic import Diff.ModBase\nnamespace Diff\npublic def cube (n : Nat) : Nat := n * mbase\nend Diff\n",
        )
        .unwrap();
        build_project_modules_native(
            &mut store,
            &diff_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        let native_core_olean =
            fs::read(diff_dir.join(".lake/build/lib/lean/Diff/Core.olean")).unwrap();
        let native_use_olean =
            fs::read(diff_dir.join(".lake/build/lib/lean/Diff/Use.olean")).unwrap();
        assert!(!native_core_olean.is_empty() && !native_use_olean.is_empty());
        let lake_bin = resolve_project_config(&diff_dir)
            .unwrap()
            .lean_bin
            .with_file_name("lake");
        if lake_bin.is_file() {
            // Re-run with `:c` facet so `.c`, `.c.hash`, `.olean.hash`, `.ilean.hash`, companion `.hash`, and `.trace` are materialized,
            // then verify `lake build --no-build` succeeds with 0 rebuilds!
            build_project_modules_native(
                &mut store,
                &diff_dir,
                &["Diff:c".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            let native_use_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(diff_dir.join(".lake/build/lib/lean/Diff/Use.trace")).unwrap(),
            )
            .unwrap();
            let native_modsys_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(diff_dir.join(".lake/build/lib/lean/Diff/ModSys.trace")).unwrap(),
            )
            .unwrap();
            let no_build_st = Command::new(&lake_bin)
                .args(["build", "--no-build"])
                .current_dir(&diff_dir)
                .status()
                .unwrap();
            assert!(
                no_build_st.success(),
                "`lake build --no-build` must succeed directly on turbo-lean materialized artifacts"
            );
            fs::remove_dir_all(diff_dir.join(".lake/build")).unwrap();
            let st = Command::new(&lake_bin)
                .arg("build")
                .current_dir(&diff_dir)
                .status()
                .unwrap();
            assert!(st.success());
            let lake_use_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(diff_dir.join(".lake/build/lib/lean/Diff/Use.trace")).unwrap(),
            )
            .unwrap();
            let lake_modsys_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(diff_dir.join(".lake/build/lib/lean/Diff/ModSys.trace")).unwrap(),
            )
            .unwrap();
            assert_eq!(
                native_use_trace["depHash"], lake_use_trace["depHash"],
                "native vs lake Diff.Use.trace depHash must match bit-for-bit"
            );
            assert_eq!(
                native_use_trace["outputs"], lake_use_trace["outputs"],
                "native vs lake Diff.Use.trace outputs must match bit-for-bit"
            );
            assert_eq!(
                native_modsys_trace["depHash"], lake_modsys_trace["depHash"],
                "native vs lake module-system Diff.ModSys.trace depHash must match bit-for-bit"
            );
            assert_eq!(
                native_modsys_trace["outputs"], lake_modsys_trace["outputs"],
                "native vs lake module-system Diff.ModSys.trace outputs must match bit-for-bit"
            );
            let lake_core_olean =
                fs::read(diff_dir.join(".lake/build/lib/lean/Diff/Core.olean")).unwrap();
            let lake_use_olean =
                fs::read(diff_dir.join(".lake/build/lib/lean/Diff/Use.olean")).unwrap();
            assert_eq!(
                blake3::hash(&native_core_olean),
                blake3::hash(&lake_core_olean),
                "native vs lake Diff.Core.olean bytes must match"
            );
            assert_eq!(
                blake3::hash(&native_use_olean),
                blake3::hash(&lake_use_olean),
                "native vs lake Diff.Use.olean bytes must match"
            );

            // 7. Differential parity for WS9 bugs:
            //    (a) `leanOptions` (`Name.quickCmp`, `Str("0")` vs `Num(0)`, `asCliFlagValue`) vs `moreLeanArgs` (`-D`)
            //    (b) missing `.c` emits `"outputs": null`, cleans stale `.ltar`/`.bc` (+ `.hash`), and `lake build --no-build` succeeds
            //    (c) `pkg.precompileModules = true` + `lib.precompileModules = false` builds `.c` across diamond DAG so `lake build --no-build` succeeds
            let lake_cache = dir.join("lake_cache_ws9");
            fs::create_dir_all(&lake_cache).unwrap();

            let opt_proj = dir.join("ws9_opts_proj");
            fs::create_dir_all(opt_proj.join("Opt")).unwrap();
            fs::write(
                opt_proj.join("lean-toolchain"),
                "leanprover/lean4:v4.35.0\n",
            )
            .unwrap();
            fs::write(
                opt_proj.join("lakefile.toml"),
                r#"name = "ws9_opts"
defaultTargets = ["Opt"]
moreLeanArgs = ["-DmaxHeartbeats=200000"]
leanOptions = [
  { name = "weak.linter.0", value = true },
  { name = "weak.linter.«0»", value = false },
  { name = "weak.linter.«unused-vars»", value = false },
  { name = "weak.linter.myStr", value = "hello \"world\"" },
  { name = "autoImplicit", value = false }
]
[[lean_lib]]
name = "Opt"
globs = ["Opt.+"]
"#,
            )
            .unwrap();
            fs::write(
                opt_proj.join("Opt/A.lean"),
                "namespace Opt\ndef x : Nat := 42\nend Opt\n",
            )
            .unwrap();
            fs::create_dir_all(opt_proj.join(".lake/build/ir/Opt")).unwrap();
            fs::write(opt_proj.join(".lake/build/ir/Opt/A.ltar"), b"stale_ltar").unwrap();
            fs::write(
                opt_proj.join(".lake/build/ir/Opt/A.ltar.hash"),
                b"0000000000000000",
            )
            .unwrap();
            fs::write(opt_proj.join(".lake/build/ir/Opt/A.bc"), b"stale_bc").unwrap();
            fs::write(
                opt_proj.join(".lake/build/ir/Opt/A.bc.hash"),
                b"0000000000000000",
            )
            .unwrap();

            // Build without `:c`: `.c` is absent, `.trace` must have `"outputs": null`, stale `.ltar`/`.bc` removed.
            build_project_modules_native(
                &mut store,
                &opt_proj,
                &[],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            assert!(!opt_proj.join(".lake/build/ir/Opt/A.c").exists());
            assert!(!opt_proj.join(".lake/build/ir/Opt/A.ltar").exists());
            assert!(!opt_proj.join(".lake/build/ir/Opt/A.ltar.hash").exists());
            assert!(!opt_proj.join(".lake/build/ir/Opt/A.bc").exists());
            assert!(!opt_proj.join(".lake/build/ir/Opt/A.bc.hash").exists());
            let no_c_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(opt_proj.join(".lake/build/lib/lean/Opt/A.trace")).unwrap(),
            )
            .unwrap();
            assert!(
                no_c_trace["outputs"].is_null(),
                "expected null outputs when .c is absent, got: {}",
                no_c_trace["outputs"]
            );
            let native_opt_dep_hash = no_c_trace["depHash"].clone();
            // When `.c` is absent, `"outputs": null` forces Lake out of a corrupt cache lookup (`resolveModuleOutputs`
            // does not see a bogus `"c": "0000000000000000.c"`), and `Module.checkExists` correctly observes `.c` is missing.
            let no_build_missing_c = Command::new(&lake_bin)
                .args(["build", "Opt.A:olean", "--no-build"])
                .env("LAKE_CACHE_DIR", &lake_cache)
                .current_dir(&opt_proj)
                .output()
                .unwrap();
            assert!(
                !no_build_missing_c.status.success()
                    && !String::from_utf8_lossy(&no_build_missing_c.stderr).contains("ill-formed"),
                "expected clean out-of-date exit when .c is absent and outputs is null"
            );
            // Also verify that if Lake's local artifact cache holds a valid `.olean`/`.ilean`/`.c` entry for `depHash`
            // while `.lake/build` has no `.c` and `"outputs": null` (and stale `.ltar` was cleaned), `lake build --no-build`
            // restores cleanly without unpack errors from stale `.ltar`.
            fs::remove_file(opt_proj.join(".lake/build/lib/lean/Opt/A.trace.nobuild")).ok();

            // Re-seed stale `.ltar`/`.bc` before CAS-hit / `:c` build to verify they are cleaned and `lake build --no-build` succeeds.
            fs::create_dir_all(opt_proj.join(".lake/build/ir/Opt")).unwrap();
            fs::write(opt_proj.join(".lake/build/ir/Opt/A.ltar"), b"stale_ltar2").unwrap();
            fs::write(opt_proj.join(".lake/build/ir/Opt/A.bc"), b"stale_bc2").unwrap();
            let rep_cas = build_project_modules_native(
                &mut store,
                &opt_proj,
                &["Opt:c".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            let _ = rep_cas;
            assert!(!opt_proj.join(".lake/build/ir/Opt/A.ltar").exists());
            assert!(!opt_proj.join(".lake/build/ir/Opt/A.bc").exists());
            let with_c_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(opt_proj.join(".lake/build/lib/lean/Opt/A.trace")).unwrap(),
            )
            .unwrap();
            assert!(with_c_trace["outputs"].is_object());
            assert_eq!(with_c_trace["depHash"], native_opt_dep_hash);
            let no_build_full = Command::new(&lake_bin)
                .args(["build", "--no-build"])
                .env("LAKE_CACHE_DIR", &lake_cache)
                .current_dir(&opt_proj)
                .status()
                .unwrap();
            assert!(
                no_build_full.success(),
                "`lake build --no-build` must succeed with complex leanOptions + moreLeanArgs"
            );
            // Compare bit-for-bit against clean `lake build` (with `LAKE_ARTIFACT_CACHE=true` to also populate `LAKE_CACHE_DIR`).
            fs::remove_dir_all(opt_proj.join(".lake/build")).unwrap();
            let clean_lake = Command::new(&lake_bin)
                .arg("build")
                .env("LAKE_CACHE_DIR", &lake_cache)
                .env("LAKE_ARTIFACT_CACHE", "true")
                .current_dir(&opt_proj)
                .status()
                .unwrap();
            assert!(clean_lake.success());
            let lake_opt_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(opt_proj.join(".lake/build/lib/lean/Opt/A.trace")).unwrap(),
            )
            .unwrap();
            assert_eq!(native_opt_dep_hash, lake_opt_trace["depHash"]);
            assert_eq!(with_c_trace["outputs"], lake_opt_trace["outputs"]);

            // Re-run without `:c` (hits `c_key` CAS fallback and removes `.c` while emitting `"outputs": null` and cleaning stale `.ltar`/`.bc`):
            // with `LAKE_CACHE_DIR` populated by `lake build`, `lake build Opt.A:olean --no-build` restores from `LAKE_CACHE_DIR` with 0 rebuilds!
            fs::write(opt_proj.join(".lake/build/ir/Opt/A.ltar"), b"corrupt_ltar").unwrap();
            build_project_modules_native(
                &mut store,
                &opt_proj,
                &[],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            assert!(!opt_proj.join(".lake/build/ir/Opt/A.c").exists());
            assert!(!opt_proj.join(".lake/build/ir/Opt/A.ltar").exists());
            let no_c_trace2: serde_json::Value = serde_json::from_slice(
                &fs::read(opt_proj.join(".lake/build/lib/lean/Opt/A.trace")).unwrap(),
            )
            .unwrap();
            assert!(no_c_trace2["outputs"].is_null());
            let no_build_from_lake_cache = Command::new(&lake_bin)
                .args(["build", "Opt.A:olean", "--no-build"])
                .env("LAKE_CACHE_DIR", &lake_cache)
                .current_dir(&opt_proj)
                .status()
                .unwrap();
            assert!(
                no_build_from_lake_cache.success(),
                "`lake build Opt.A:olean --no-build` must succeed from Lake cache when .c is absent, outputs is null, and stale .ltar is cleaned"
            );

            // (c) `pkg.precompileModules = true` + `lib.precompileModules = false` -> Lake's `LeanLib.precompileModules` is `self.pkg.precompileModules || self.config.precompileModules` (`true`),
            // propagating `needs_c`, `.c.o.export`, module `.so` dynlibs, and library shared object `libws9__pre_Pre.so` across a diamond DAG (`Pre.Base` <- `Pre.Left`/`Pre.Right` <- `Pre.Top`)
            // and downstream library `Down` (`Down.Use`), so full `lake build --no-build` exits 0!
            let pre_proj = dir.join("ws9_pre,proj");
            fs::create_dir_all(pre_proj.join("Pre")).unwrap();
            fs::create_dir_all(pre_proj.join("Down")).unwrap();
            fs::write(
                pre_proj.join("lean-toolchain"),
                "leanprover/lean4:v4.35.0\n",
            )
            .unwrap();
            fs::write(
                pre_proj.join("lakefile.toml"),
                r#"name = "ws9_pre"
precompileModules = true
defaultTargets = ["Pre", "Down"]
[leanOptions]
autoImplicit = false
weak.linter."unused-vars" = false
weak.linter."0" = true
[[lean_lib]]
name = "Pre"
precompileModules = false
roots = ["Pre.Top"]
globs = ["Pre.+"]
[[lean_lib]]
name = "Down"
roots = ["Down.Use"]
globs = ["Down.+"]
"#,
            )
            .unwrap();
            fs::write(pre_proj.join("Pre/Base.lean"), "def base : Nat := 3\n").unwrap();
            fs::write(
                pre_proj.join("Pre/Left.lean"),
                "import Pre.Base\ndef left : Nat := base + 1\n",
            )
            .unwrap();
            fs::write(
                pre_proj.join("Pre/Right.lean"),
                "import Pre.Base\ndef right : Nat := base + 2\n",
            )
            .unwrap();
            fs::write(
                pre_proj.join("Pre/Top.lean"),
                "import Pre.Left\nimport Pre.Right\ndef top : Nat := left + right\n",
            )
            .unwrap();
            fs::write(
                pre_proj.join("Down/Use.lean"),
                "import Pre.Top\ndef useTop : Nat := top + 10\n",
            )
            .unwrap();
            // Untrusted mode must fail closed before running clang or loading native dynlibs.
            let err_untrusted_pre = build_project_modules_native(
                &mut store,
                &pre_proj,
                &[],
                "untrusted:pr",
                1,
                true,
                true,
                None,
            )
            .unwrap_err()
            .to_string();
            assert!(
                err_untrusted_pre.contains("fail-closed"),
                "expected untrusted rejection for precompileModules, got: {err_untrusted_pre}"
            );
            build_project_modules_native(
                &mut store,
                &pre_proj,
                &[],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            for m in ["Base", "Left", "Right", "Top"] {
                assert!(
                    pre_proj.join(format!(".lake/build/ir/Pre/{m}.c")).is_file(),
                    "Pre/{m}.c must be materialized when pkg.precompileModules = true even if lib.precompileModules = false"
                );
                assert!(
                    pre_proj
                        .join(format!(".lake/build/ir/Pre/{m}.c.o.export"))
                        .is_file(),
                    "Pre/{m}.c.o.export must be materialized"
                );
            }
            let pre_cfg = resolve_project_config(&pre_proj).unwrap();
            let tc_spec = query_toolchain_native_spec(&pre_cfg.lean_bin).unwrap();
            assert!(!tc_spec.target.is_empty());
            assert!(tc_spec
                .c_flags
                .iter()
                .any(|f| f == "-Wno-unused-command-line-argument"));
            let sh_ext = tc_spec.shared_lib_ext();
            let native_facet_paths = [
                ".lake/build/ir/Pre/Base.c.o.export".to_string(),
                format!(".lake/build/lib/lean/ws9__pre_Pre_Base.{sh_ext}"),
                format!(".lake/build/lib/libws9__pre_Pre.{sh_ext}"),
            ];
            for rel in &native_facet_paths[1..] {
                let bytes = fs::read(pre_proj.join(rel)).unwrap();
                assert!(
                    !bytes
                        .windows(b".turbo_tmp_".len())
                        .any(|w| w == b".turbo_tmp_"),
                    "shared library `{rel}` must be linked with its final basename without embedding temporary staging paths"
                );
            }
            let ours_native_traces: Vec<serde_json::Value> = native_facet_paths
                .iter()
                .map(|rel| {
                    serde_json::from_slice(
                        &fs::read(pre_proj.join(format!("{rel}.trace"))).unwrap(),
                    )
                    .unwrap()
                })
                .collect();
            let ours_native_rsps: Vec<String> = native_facet_paths[1..]
                .iter()
                .map(|rel| fs::read_to_string(pre_proj.join(format!("{rel}.rsp"))).unwrap())
                .collect();
            let pre_base_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(pre_proj.join(".lake/build/lib/lean/Pre/Base.trace")).unwrap(),
            )
            .unwrap();
            let pre_top_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(pre_proj.join(".lake/build/lib/lean/Pre/Top.trace")).unwrap(),
            )
            .unwrap();
            let down_use_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(pre_proj.join(".lake/build/lib/lean/Down/Use.trace")).unwrap(),
            )
            .unwrap();
            // Full `lake build --no-build` across all default targets (`Pre`, `Pre:shared`, `Down`, `Down:shared`, module dynlibs, and module oleans) must exit 0!
            let full_pre_no_build = Command::new(&lake_bin)
                .args(["build", "--no-build"])
                .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
                .env("LAKE_CACHE_DIR", &lake_cache)
                .current_dir(&pre_proj)
                .status()
                .unwrap();
            assert!(
                full_pre_no_build.success(),
                "`lake build --no-build` must exit 0 on precompileModules diamond + downstream library"
            );
            fs::remove_dir_all(pre_proj.join(".lake/build")).unwrap();
            let clean_pre_lake = Command::new(&lake_bin)
                .arg("build")
                .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
                .env("LAKE_CACHE_DIR", &lake_cache)
                .current_dir(&pre_proj)
                .status()
                .unwrap();
            assert!(clean_pre_lake.success());
            let lake_pre_base_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(pre_proj.join(".lake/build/lib/lean/Pre/Base.trace")).unwrap(),
            )
            .unwrap();
            let lake_pre_top_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(pre_proj.join(".lake/build/lib/lean/Pre/Top.trace")).unwrap(),
            )
            .unwrap();
            let lake_down_use_trace: serde_json::Value = serde_json::from_slice(
                &fs::read(pre_proj.join(".lake/build/lib/lean/Down/Use.trace")).unwrap(),
            )
            .unwrap();
            assert_eq!(pre_base_trace["depHash"], lake_pre_base_trace["depHash"]);
            assert_eq!(pre_base_trace["outputs"], lake_pre_base_trace["outputs"]);
            assert_eq!(pre_top_trace["outputs"], lake_pre_top_trace["outputs"]);
            assert_eq!(down_use_trace["outputs"], lake_down_use_trace["outputs"]);
            for (idx, rel) in native_facet_paths.iter().enumerate() {
                let lake_trace: serde_json::Value = serde_json::from_slice(
                    &fs::read(pre_proj.join(format!("{rel}.trace"))).unwrap(),
                )
                .unwrap();
                assert_eq!(
                    ours_native_traces[idx]["depHash"], lake_trace["depHash"],
                    "native facet depHash mismatch on {rel}"
                );
                assert_eq!(
                    ours_native_traces[idx]["inputs"], lake_trace["inputs"],
                    "native facet inputs mismatch on {rel}"
                );
            }
            for (idx, rel) in native_facet_paths[1..].iter().enumerate() {
                let lake_rsp = fs::read_to_string(pre_proj.join(format!("{rel}.rsp"))).unwrap();
                assert_eq!(
                    ours_native_rsps[idx], lake_rsp,
                    "native shared-lib .rsp mismatch vs Lake on {rel}"
                );
            }

            let dyn_proj = dir.join("ws9_explicit_dynlib");
            fs::create_dir_all(dyn_proj.join("Supp")).unwrap();
            fs::create_dir_all(dyn_proj.join("Demo")).unwrap();
            fs::write(
                dyn_proj.join("lean-toolchain"),
                "leanprover/lean4:v4.35.0\n",
            )
            .unwrap();
            fs::write(
                dyn_proj.join("lakefile.toml"),
                r#"name = "ws9_dyn"
precompileModules = false
defaultTargets = ["Demo"]
[[lean_lib]]
name = "Supp"
roots = ["Supp.Core", "Supp.Extra"]
globs = ["Supp.+"]
[[lean_lib]]
name = "Demo"
roots = ["Demo.Top"]
globs = ["Demo.+"]
"#,
            )
            .unwrap();
            fs::write(dyn_proj.join("Supp/Core.lean"), "def suppCore : Nat := 5\n").unwrap();
            fs::write(
                dyn_proj.join("Supp/Extra.lean"),
                "import Supp.Core\ndef suppExtra : Nat := suppCore + 1\n",
            )
            .unwrap();
            fs::write(
                dyn_proj.join("Demo/Base.lean"),
                "def demoBase : Nat := 11\n",
            )
            .unwrap();
            fs::write(
                dyn_proj.join("Demo/Top.lean"),
                "import Supp.Core\nimport Demo.Base\ndef demoTop : Nat := suppCore + demoBase\n",
            )
            .unwrap();
            build_project_modules_native(
                &mut store,
                &dyn_proj,
                &["+Demo.Top:dynlib".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            let sh_prefix = if tc_spec.is_windows { "" } else { "lib" };
            let dyn_facet_paths = [
                format!(".lake/build/lib/{sh_prefix}ws9__dyn_Supp.{sh_ext}"),
                format!(".lake/build/lib/lean/ws9__dyn_Demo_Base.{sh_ext}"),
                format!(".lake/build/lib/lean/ws9__dyn_Demo_Top.{sh_ext}"),
            ];
            let ours_dyn_traces: Vec<serde_json::Value> = dyn_facet_paths
                .iter()
                .map(|rel| {
                    serde_json::from_slice(
                        &fs::read(dyn_proj.join(format!("{rel}.trace"))).unwrap(),
                    )
                    .unwrap()
                })
                .collect();
            let ours_dyn_rsps: Vec<String> = dyn_facet_paths
                .iter()
                .map(|rel| fs::read_to_string(dyn_proj.join(format!("{rel}.rsp"))).unwrap())
                .collect();
            let dyn_no_build = Command::new(&lake_bin)
                .args(["build", "+Demo.Top:dynlib", "--no-build"])
                .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
                .env("LAKE_CACHE_DIR", &lake_cache)
                .current_dir(&dyn_proj)
                .status()
                .unwrap();
            assert!(
                dyn_no_build.success(),
                "`lake build +Demo.Top:dynlib --no-build` must exit 0 on clean build with precompileModules = false"
            );
            fs::remove_dir_all(dyn_proj.join(".lake/build")).unwrap();
            let clean_dyn_lake = Command::new(&lake_bin)
                .args(["build", "+Demo.Top:dynlib"])
                .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
                .env("LAKE_CACHE_DIR", &lake_cache)
                .current_dir(&dyn_proj)
                .status()
                .unwrap();
            assert!(clean_dyn_lake.success());
            for (idx, rel) in dyn_facet_paths.iter().enumerate() {
                let lake_trace: serde_json::Value = serde_json::from_slice(
                    &fs::read(dyn_proj.join(format!("{rel}.trace"))).unwrap(),
                )
                .unwrap();
                assert_eq!(
                    ours_dyn_traces[idx]["depHash"], lake_trace["depHash"],
                    "explicit :dynlib depHash mismatch on {rel}"
                );
                assert_eq!(
                    ours_dyn_traces[idx]["inputs"], lake_trace["inputs"],
                    "explicit :dynlib inputs mismatch on {rel}"
                );
                let lake_rsp = fs::read_to_string(dyn_proj.join(format!("{rel}.rsp"))).unwrap();
                assert_eq!(
                    ours_dyn_rsps[idx], lake_rsp,
                    "explicit :dynlib .rsp mismatch vs Lake on {rel}"
                );
            }
            let bad_exe = dir.join("ws9_exe_facet");
            fs::create_dir_all(&bad_exe).unwrap();
            fs::write(bad_exe.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
            fs::write(
                bad_exe.join("lakefile.toml"),
                "name = \"ws9_exe\"\n[[lean_exe]]\nname = \"main\"\nroot = \"Main\"\n",
            )
            .unwrap();
            fs::write(bad_exe.join("Main.lean"), "def main : IO Unit := pure ()\n").unwrap();
            let err_exe = build_project_modules_native(
                &mut store,
                &bad_exe,
                &["main:dynlib".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap_err()
            .to_string();
            assert!(
                err_exe.contains("lean_exe") && err_exe.contains("fail-closed"),
                "expected lean_exe facet rejection, got: {err_exe}"
            );
            let err_exe_bin = build_project_modules_native(
                &mut store,
                &bad_exe,
                &["main:exe".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap_err()
            .to_string();
            assert!(
                err_exe_bin.contains("fail-closed"),
                "expected `main:exe` rejection, got: {err_exe_bin}"
            );

            // 5. Package-qualified `+` module syntax (`ws9_chain/+App.Top:dynlib`) + 3-package
            // pre-existing fresh external `.olean` chain (`App.Top -> DepB.Mid -> DepC.Leaf`) with `precompileModules = false`:
            let chain_proj = dir.join("ws9_chain");
            let dep_b = chain_proj.join(".lake/packages/depb");
            let dep_c = chain_proj.join(".lake/packages/depc");
            fs::create_dir_all(chain_proj.join("App")).unwrap();
            fs::create_dir_all(dep_b.join("DepB")).unwrap();
            fs::create_dir_all(dep_c.join("DepC")).unwrap();
            fs::write(
                chain_proj.join("lean-toolchain"),
                "leanprover/lean4:v4.35.0\n",
            )
            .unwrap();
            fs::write(
                dep_c.join("lakefile.toml"),
                "name = \"depc\"\n[[lean_lib]]\nname = \"DepC\"\nglobs = [\"DepC.+\"]\n",
            )
            .unwrap();
            fs::write(dep_c.join("DepC/Leaf.lean"), "def leafVal : Nat := 13\n").unwrap();
            fs::write(
                dep_b.join("lakefile.toml"),
                "name = \"depb\"\n[[require]]\nname = \"depc\"\npath = \"../depc\"\n[[lean_lib]]\nname = \"DepB\"\nglobs = [\"DepB.+\"]\n",
            )
            .unwrap();
            fs::write(
                dep_b.join("DepB/Mid.lean"),
                "import DepC.Leaf\ndef midVal : Nat := leafVal + 5\n",
            )
            .unwrap();
            fs::write(
                chain_proj.join("lakefile.toml"),
                "name = \"ws9_chain\"\n[[require]]\nname = \"depb\"\npath = \".lake/packages/depb\"\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
            )
            .unwrap();
            fs::write(
                chain_proj.join("App/Top.lean"),
                "import DepB.Mid\ndef topVal : Nat := midVal * 2\n",
            )
            .unwrap();
            // Pre-populate fresh `.olean`s ONLY (no `:shared` libs yet) in `depb` and `depc` via Lake:
            let pre_olean_status = Command::new(&lake_bin)
                .args(["build", "depc/+DepC.Leaf:olean", "depb/+DepB.Mid:olean"])
                .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
                .env("LAKE_CACHE_DIR", &lake_cache)
                .current_dir(&chain_proj)
                .status()
                .unwrap();
            assert!(pre_olean_status.success());
            assert!(!dep_c
                .join(format!(".lake/build/lib/{sh_prefix}depc_DepC.{sh_ext}"))
                .exists());
            assert!(!dep_b
                .join(format!(".lake/build/lib/{sh_prefix}depb_DepB.{sh_ext}"))
                .exists());
            // Build `ws9_chain/+App.Top:dynlib` via turbo-lean; both `depb_DepB` and transitive `depc_DepC` `:shared` must be materialized!
            build_project_modules_native(
                &mut store,
                &chain_proj,
                &["ws9_chain/+App.Top:dynlib".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            assert!(dep_c
                .join(format!(".lake/build/lib/{sh_prefix}depc_DepC.{sh_ext}"))
                .is_file());
            assert!(dep_b
                .join(format!(".lake/build/lib/{sh_prefix}depb_DepB.{sh_ext}"))
                .is_file());
            let chain_no_build = Command::new(&lake_bin)
                .args(["build", "ws9_chain/+App.Top:dynlib", "--no-build"])
                .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
                .env("LAKE_CACHE_DIR", &lake_cache)
                .current_dir(&chain_proj)
                .status()
                .unwrap();
            assert!(
                chain_no_build.success(),
                "`lake build ws9_chain/+App.Top:dynlib --no-build` must exit 0 after 3-package fresh external olean promotion"
            );

            // 6. Compiler vs linker native config gate split:
            let gate_proj = dir.join("ws9_gate_split");
            fs::create_dir_all(gate_proj.join("G")).unwrap();
            fs::write(
                gate_proj.join("lean-toolchain"),
                "leanprover/lean4:v4.35.0\n",
            )
            .unwrap();
            fs::write(gate_proj.join("G/Mod.lean"), "def gMod : Nat := 7\n").unwrap();
            // Linker/libName flags allow `:c` and `:c.o.export` (`leanc -c`), but reject `:dynlib` and `:shared`:
            fs::write(
                gate_proj.join("lakefile.toml"),
                "name = \"ws9_gate\"\nmoreLinkArgs = [\"-lm\"]\n[[lean_lib]]\nname = \"G\"\nlibName = \"custom_g\"\nglobs = [\"G.+\"]\n",
            )
            .unwrap();
            build_project_modules_native(
                &mut store,
                &gate_proj,
                &["+G.Mod:c".to_string(), "+G.Mod:c.o.export".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            for bad_link_tgt in ["+G.Mod:dynlib", "G:shared"] {
                let err = build_project_modules_native(
                    &mut store,
                    &gate_proj,
                    &[bad_link_tgt.to_string()],
                    "trusted-internal",
                    1,
                    false,
                    true,
                    None,
                )
                .unwrap_err()
                .to_string();
                assert!(
                    err.contains("fail-closed"),
                    "expected `{bad_link_tgt}` to fail closed on custom linker/libName settings, got: {err}"
                );
            }
            // C-compiler flags (`moreLeancArgs`) still allow `:c` (`lean --c`), while rejecting `:c.o.export`, `:dynlib`, and `:shared`:
            fs::write(
                gate_proj.join("lakefile.toml"),
                "name = \"ws9_gate\"\nmoreLeancArgs = [\"-DFOO=1\"]\n[[lean_lib]]\nname = \"G\"\nglobs = [\"G.+\"]\n",
            )
            .unwrap();
            build_project_modules_native(
                &mut store,
                &gate_proj,
                &["+G.Mod:c".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            for bad_c_tgt in ["+G.Mod:c.o.export", "+G.Mod:dynlib", "G:shared"] {
                let err = build_project_modules_native(
                    &mut store,
                    &gate_proj,
                    &[bad_c_tgt.to_string()],
                    "trusted-internal",
                    1,
                    false,
                    true,
                    None,
                )
                .unwrap_err()
                .to_string();
                assert!(
                    err.contains("fail-closed"),
                    "expected `{bad_c_tgt}` to fail closed on custom leanc settings, got: {err}"
                );
            }

            // 7. Reverse-lexical precompiled import declaration order (`import Ord.Z` before `import Ord.A`)
            // + explicit `Lib:default` spelling with `defaultFacets = ["shared"]`:
            let ord_proj = dir.join("ws9_ord_default");
            fs::create_dir_all(ord_proj.join("Ord")).unwrap();
            fs::create_dir_all(ord_proj.join("DefSh")).unwrap();
            fs::write(
                ord_proj.join("lean-toolchain"),
                "leanprover/lean4:v4.35.0\n",
            )
            .unwrap();
            fs::write(ord_proj.join("Ord/Z.lean"), "def zVal : Nat := 100\n").unwrap();
            fs::write(ord_proj.join("Ord/A.lean"), "def aVal : Nat := 23\n").unwrap();
            fs::write(
                ord_proj.join("Ord/Top.lean"),
                "import Ord.Z\nimport Ord.A\ndef topOrd : Nat := zVal + aVal\n",
            )
            .unwrap();
            fs::write(ord_proj.join("DefSh/One.lean"), "def defShVal : Nat := 9\n").unwrap();
            fs::write(
                ord_proj.join("lakefile.toml"),
                "name = \"ws9_ord\"\n[[lean_lib]]\nname = \"Ord\"\nprecompileModules = true\nglobs = [\"Ord.+\"]\n[[lean_lib]]\nname = \"DefSh\"\ndefaultFacets = [\"shared\"]\nglobs = [\"DefSh.+\"]\n",
            )
            .unwrap();
            // Explicit `DefSh:default` and `Ord:default` must materialize both shared libs and match Lake traces bit-for-bit
            // even though `Ord.Top` imports `Ord.Z` before `Ord.A` (reverse-lexical):
            build_project_modules_native(
                &mut store,
                &ord_proj,
                &["Ord:default".to_string(), "DefSh:default".to_string()],
                "trusted-internal",
                2,
                false,
                true,
                None,
            )
            .unwrap();
            assert!(ord_proj
                .join(format!(
                    ".lake/build/lib/{sh_prefix}ws9__ord_DefSh.{sh_ext}"
                ))
                .is_file());
            assert!(ord_proj
                .join(format!(".lake/build/lib/{sh_prefix}ws9__ord_Ord.{sh_ext}"))
                .is_file());
            let ord_top_trace_path = ord_proj.join(".lake/build/lib/lean/Ord/Top.trace");
            let ours_ord_top_trace: serde_json::Value =
                serde_json::from_slice(&fs::read(&ord_top_trace_path).unwrap()).unwrap();
            let ord_no_build = Command::new(&lake_bin)
                .args(["build", "Ord:default", "DefSh:default", "--no-build"])
                .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
                .env("LAKE_CACHE_DIR", &lake_cache)
                .current_dir(&ord_proj)
                .status()
                .unwrap();
            assert!(
                ord_no_build.success(),
                "`lake build Ord:default DefSh:default --no-build` must exit 0 with reverse-lexical precompiled imports and explicit :default shared facet"
            );
            fs::remove_dir_all(ord_proj.join(".lake/build")).unwrap();
            let clean_ord_lake = Command::new(&lake_bin)
                .args(["build", "Ord:default", "DefSh:default"])
                .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
                .env("LAKE_CACHE_DIR", &lake_cache)
                .current_dir(&ord_proj)
                .status()
                .unwrap();
            assert!(clean_ord_lake.success());
            let lake_ord_top_trace: serde_json::Value =
                serde_json::from_slice(&fs::read(&ord_top_trace_path).unwrap()).unwrap();
            assert_eq!(
                ours_ord_top_trace["depHash"], lake_ord_top_trace["depHash"],
                "reverse-lexical precompiled import depHash mismatch on Ord.Top"
            );
            assert_eq!(
                ours_ord_top_trace["outputs"], lake_ord_top_trace["outputs"],
                "reverse-lexical precompiled import outputs mismatch on Ord.Top"
            );
            assert_eq!(
                ours_ord_top_trace["inputs"][0], lake_ord_top_trace["inputs"][0],
                "reverse-lexical precompiled import deps order mismatch on Ord.Top"
            );
            assert_eq!(
                ours_ord_top_trace["inputs"][1], lake_ord_top_trace["inputs"][1],
                "reverse-lexical precompiled import dynlibs order mismatch on Ord.Top"
            );
            // Also verify bare `DefSh` (omitted facet) and fail-closed `DefSh:default` under custom linker flags:
            let _ = fs::remove_dir_all(ord_proj.join(".lake/build"));
            build_project_modules_native(
                &mut store,
                &ord_proj,
                &["DefSh".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            assert!(ord_proj
                .join(format!(
                    ".lake/build/lib/{sh_prefix}ws9__ord_DefSh.{sh_ext}"
                ))
                .is_file());
            let bare_defsh_no_build = Command::new(&lake_bin)
                .args(["build", "DefSh", "--no-build"])
                .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
                .env("LAKE_CACHE_DIR", &lake_cache)
                .current_dir(&ord_proj)
                .status()
                .unwrap();
            assert!(bare_defsh_no_build.success());
            fs::write(
                ord_proj.join("lakefile.toml"),
                "name = \"ws9_ord\"\n[[lean_lib]]\nname = \"DefSh\"\ndefaultFacets = [\"shared\"]\nmoreLinkArgs = [\"-lm\"]\nglobs = [\"DefSh.+\"]\n",
            )
            .unwrap();
            for sh_def_tgt in ["DefSh", "DefSh:default"] {
                let err_def = build_project_modules_native(
                    &mut store,
                    &ord_proj,
                    &[sh_def_tgt.to_string()],
                    "trusted-internal",
                    1,
                    false,
                    true,
                    None,
                )
                .unwrap_err()
                .to_string();
                assert!(
                    err_def.contains("fail-closed"),
                    "expected `{sh_def_tgt}` with `defaultFacets = [\"shared\"]` and `moreLinkArgs` to fail closed, got: {err_def}"
                );
            }
        }
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_parallel_diamond_dag_and_ci_verify_native_builder() {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = make_temp_test_dir("diamond");
        let proj_dir = dir.join("diamond_proj");
        let store_dir = dir.join("store");
        fs::create_dir_all(proj_dir.join("Diamond")).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"diamond_proj\"\ndefaultTargets = [\"Diamond\"]\n[[lean_lib]]\nname = \"Diamond\"\nglobs = [\"Diamond.+\"]\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("Diamond/Root.lean"),
            "namespace Diamond\ndef r : Nat := 3\nend Diamond\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("Diamond/Left.lean"),
            "import Diamond.Root\nnamespace Diamond\ndef l : Nat := r + 4\nend Diamond\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("Diamond/Right.lean"),
            "import Diamond.Root\nnamespace Diamond\ndef rg : Nat := r * 4\nend Diamond\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("Diamond/Top.lean"),
            "import Diamond.Left\nimport Diamond.Right\nnamespace Diamond\ntheorem top_eq : l + rg = 19 := rfl\nend Diamond\n",
        )
        .unwrap();

        let cfg = resolve_project_config(&proj_dir).unwrap();
        let dag = build_module_dag(&cfg, &[]).unwrap();
        assert_eq!(dag.waves.len(), 3);
        assert_eq!(dag.waves[0], vec!["Diamond.Root".to_string()]);
        assert_eq!(
            dag.waves[1],
            vec!["Diamond.Left".to_string(), "Diamond.Right".to_string()]
        );
        assert_eq!(dag.waves[2], vec!["Diamond.Top".to_string()]);

        let mut store = TurboStore::open(Some(&store_dir)).unwrap();
        // Run across the diamond DAG (Wave 0: Root, Wave 1: Left + Right in parallel, Wave 2: Top)
        let rep = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep.modules_total, 4);
        assert_eq!(rep.modules_compiled, 4);
        assert_eq!(rep.waves_count, 3);

        // Verify `lake_build::run_build_command` and `pr_verify::run_ci_verify_command` succeed using native builder
        crate::lake_build::run_build_command(
            &mut store,
            false,
            Vec::new(),
            proj_dir.clone(),
            "trusted-internal".to_string(),
            1,
            false,
        )
        .unwrap();

        crate::pr_verify::run_ci_verify_command(
            &mut store,
            false,
            "full".to_string(),
            proj_dir.clone(),
            None,
            None,
            false,
            None,
        )
        .unwrap();

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_adversarial_compiler_arg_allowlist_and_custom_target_parsing() {
        // 1. Strict allowlist accepts safe Lean compiler flags
        for ok_arg in [
            "-DautoImplicit=false",
            "-Dpp.unicode.fun=true",
            "-DmaxHeartbeats=400000",
            "-j4",
            "--threads=4",
            "--tstack=16384",
            "--json",
            "-q",
            "--quiet",
        ] {
            assert!(
                is_allowed_lean_arg(ok_arg),
                "expected safe arg `{}` to be allowed",
                ok_arg
            );
        }

        // 2. Strict allowlist rejects attached short flags, abbreviated long options, and positional args
        for bad_arg in [
            "-ofoo.olean",
            "-c/tmp/evil.c",
            "-ibaz.ilean",
            "-R/tmp",
            "--load-dyn=evil.so",
            "--plug=evil.so",
            "--setup=fake.json",
            "--run",
            "-v",
            "--version",
            "positional.lean",
            "-D=true",
            "-Dfoo=",
            "-Dfoo=bar\nbaz",
            "-j0",
            "--threads=0",
        ] {
            assert!(
                !is_allowed_lean_arg(bad_arg),
                "expected unsafe/unknown arg `{}` to be rejected",
                bad_arg
            );
        }

        let dir = make_temp_test_dir("adv_custom_target_with_ext");
        fs::create_dir_all(dir.join(".lake/build/lib")).unwrap();
        fs::write(dir.join(".lake/build/lib/libfoo.a"), b"!<arch>\n").unwrap();
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage p\nextern_lib libfoo pkg := do\n  pure ()\ntarget custom_gen pkg : FilePath := do\n  pure ()\nlean_lib A\n",
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, true).unwrap();
        assert_eq!(pkg.custom_targets, ["custom_gen"]);
        assert_eq!(pkg.extern_libs[0].name, "libfoo");
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_adversarial_toolchain_resolution_and_untrusted_env_isolation() {
        let dir = make_temp_test_dir("adv_toolchain");
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"adv_tc\"\n[[lean_lib]]\nname = \"Adv\"\n",
        )
        .unwrap();

        // 1. Specific non-existent toolchain MUST fail closed without falling back to PATH `lean` or `spawn_lake_env`
        let err_missing =
            resolve_toolchain_compiler_with_trust(&dir, "leanprover/lean4:v99.99.99", false)
                .unwrap_err()
                .to_string();
        assert!(
            err_missing.contains("v99.99.99") && err_missing.contains("fail-closed"),
            "unexpected error for missing toolchain: {}",
            err_missing
        );

        // 2. Substring prefix directory (`v4.35.0-rc1`) is NOT matched for `v4.35.0`
        let fake_elan = dir.join("fake_elan");
        let rc_bin = fake_elan.join("toolchains/leanprover--lean4---v4.35.0-rc1/bin/lean");
        assert!(
            !path_has_toolchain_component(&rc_bin, "leanprover--lean4---v4.35.0"),
            "substring prefix directory must not match exact path component"
        );
        let exact_bin = fake_elan.join("toolchains/leanprover--lean4---v4.35.0/bin/lean");
        assert!(
            path_has_toolchain_component(&exact_bin, "leanprover--lean4---v4.35.0"),
            "exact path component must match"
        );

        // 3. Symlink to `.elan/bin/lean` (where `lean` is a hardlink or regular file, not a symlink to `elan`)
        // MUST be detected by `path_is_elan_proxy_bin` via canonicalized component check.
        let fake_dot_elan_bin = dir.join(".elan/bin");
        fs::create_dir_all(&fake_dot_elan_bin).unwrap();
        let fake_proxy = fake_dot_elan_bin.join("lean");
        fs::write(&fake_proxy, b"#!/bin/sh\n").unwrap();
        assert!(path_is_elan_proxy_bin(&fake_proxy));
        #[cfg(unix)]
        {
            let usr_local_bin = dir.join("usr_local_bin");
            fs::create_dir_all(&usr_local_bin).unwrap();
            let sym_lean = usr_local_bin.join("lean");
            std::os::unix::fs::symlink(&fake_proxy, &sym_lean).unwrap();
            assert!(
                path_is_elan_proxy_bin(&sym_lean),
                "symlink pointing into .elan/bin/lean must be detected as elan proxy"
            );
        }

        // 4. `v4.31.0` with only `v4.35.0` installed fails closed unless `TURBO_LEAN_ALLOW_TOOLCHAIN_FALLBACK=1`
        {
            let _env_guard = native_build_env_guard();
            let _bwrap_guard = BWRAP_TEST_ENV_LOCK
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            let prev_fallback = std::env::var_os("TURBO_LEAN_ALLOW_TOOLCHAIN_FALLBACK");
            let prev_strict = std::env::var_os("TURBO_LEAN_STRICT_TOOLCHAIN");
            let prev_elan = std::env::var_os("ELAN_HOME");
            let prev_extra = std::env::var_os("TURBO_LEAN_ELAN_ROOTS");

            let (_, _, real_lib_lean, _) =
                resolve_toolchain_compiler_with_trust(&dir, "leanprover/lean4:v4.35.0", false)
                    .expect("resolve installed v4.35.0 toolchain");
            let real_elan_root = real_lib_lean
                .ancestors()
                .nth(4)
                .expect("elan root from lib/lean")
                .to_path_buf();

            let isolated_elan = dir.join("only_v435_elan");
            fs::create_dir_all(isolated_elan.join("toolchains")).unwrap();
            #[cfg(unix)]
            std::os::unix::fs::symlink(
                real_elan_root.join("toolchains/leanprover--lean4---v4.35.0"),
                isolated_elan.join("toolchains/leanprover--lean4---v4.35.0"),
            )
            .unwrap();
            let isolated_home = dir.join("isolated/a/b/home");
            fs::create_dir_all(&isolated_home).unwrap();
            let prev_home = std::env::var_os("HOME");
            let prev_path = std::env::var_os("PATH");

            unsafe {
                std::env::remove_var("TURBO_LEAN_ALLOW_TOOLCHAIN_FALLBACK");
                std::env::remove_var("TURBO_LEAN_STRICT_TOOLCHAIN");
                std::env::set_var("ELAN_HOME", &isolated_elan);
                std::env::set_var("HOME", &isolated_home);
                std::env::set_var("PATH", "/usr/bin:/bin");
                std::env::remove_var("TURBO_LEAN_ELAN_ROOTS");
            }

            let isolated_roots = vec![isolated_elan.clone()];
            let err_v431 = resolve_toolchain_compiler_with_roots(
                &dir,
                "leanprover/lean4:v4.31.0",
                false,
                Some(&isolated_roots),
            )
            .unwrap_err()
            .to_string();
            assert!(
                err_v431.contains(
                    "Could not locate installed `lean` compiler binary matching toolchain"
                ) && err_v431.contains("v4.31.0")
                    && err_v431.contains("fail-closed"),
                "expected v4.31.0 without fallback opt-in to fail closed, got: {err_v431}"
            );

            unsafe {
                std::env::set_var("TURBO_LEAN_ALLOW_TOOLCHAIN_FALLBACK", "1");
            }
            let (fb_bin, fb_gh, _, _) = resolve_toolchain_compiler_with_roots(
                &dir,
                "leanprover/lean4:v4.31.0",
                false,
                Some(&isolated_roots),
            )
            .expect("TURBO_LEAN_ALLOW_TOOLCHAIN_FALLBACK=1 restores fleet fallback");
            assert!(
                fb_bin
                    .to_string_lossy()
                    .contains("leanprover--lean4---v4.35.0"),
                "expected v4.35.0 fallback binary, got: {}",
                fb_bin.display()
            );

            // 5. Hard-block `.olean` v2 githash skew and missing/sentinel githashes
            let init_olean = real_lib_lean.join("Init.olean");
            assert!(
                is_verified_toolchain_olean_file(&real_lib_lean, Some(&fb_gh), &init_olean),
                "matching real githash must verify toolchain Init.olean"
            );
            assert!(
                !is_verified_toolchain_olean_file(&real_lib_lean, None, &init_olean),
                "None githash must fail closed"
            );
            assert!(
                !is_verified_toolchain_olean_file(
                    &real_lib_lean,
                    Some("lean-not-installed"),
                    &init_olean
                ),
                "sentinel githash must fail closed"
            );
            assert!(
                !is_verified_toolchain_olean_file(
                    &real_lib_lean,
                    Some("0000000000000000000000000000000000000000"),
                    &init_olean
                ),
                "mismatched githash must fail closed"
            );

            unsafe {
                match prev_fallback {
                    Some(v) => std::env::set_var("TURBO_LEAN_ALLOW_TOOLCHAIN_FALLBACK", v),
                    None => std::env::remove_var("TURBO_LEAN_ALLOW_TOOLCHAIN_FALLBACK"),
                }
                match prev_strict {
                    Some(v) => std::env::set_var("TURBO_LEAN_STRICT_TOOLCHAIN", v),
                    None => std::env::remove_var("TURBO_LEAN_STRICT_TOOLCHAIN"),
                }
                match prev_elan {
                    Some(v) => std::env::set_var("ELAN_HOME", v),
                    None => std::env::remove_var("ELAN_HOME"),
                }
                match prev_extra {
                    Some(v) => std::env::set_var("TURBO_LEAN_ELAN_ROOTS", v),
                    None => std::env::remove_var("TURBO_LEAN_ELAN_ROOTS"),
                }
                match prev_home {
                    Some(v) => std::env::set_var("HOME", v),
                    None => std::env::remove_var("HOME"),
                }
                match prev_path {
                    Some(v) => std::env::set_var("PATH", v),
                    None => std::env::remove_var("PATH"),
                }
            }
        }

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_adversarial_cas_key_dep_digest_validation_and_ambiguous_or_same_mtime_deps() {
        let _env_guard = native_build_env_guard();
        let _bwrap_guard = BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = make_temp_test_dir("adv_cas_and_deps");
        let store_dir = dir.join("store");
        let proj_dir = dir.join("proj");
        let dep1_dir = proj_dir.join(".lake/packages/dep_one");
        let dep2_dir = proj_dir.join(".lake/packages/dep_two");
        fs::create_dir_all(dep1_dir.join("Shared")).unwrap();
        fs::create_dir_all(dep2_dir.join("Shared")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            dep1_dir.join("lakefile.toml"),
            "name = \"dep_one\"\n[[lean_lib]]\nname = \"SharedOne\"\nroots = [\"Shared.Util\"]\n",
        )
        .unwrap();
        fs::write(
            dep2_dir.join("lakefile.toml"),
            "name = \"dep_two\"\n[[lean_lib]]\nname = \"SharedTwo\"\nroots = [\"Shared.Util\"]\n",
        )
        .unwrap();
        fs::write(
            dep1_dir.join("Shared/Util.lean"),
            "namespace Shared\ndef v : Nat := 1\nend Shared\n",
        )
        .unwrap();
        fs::write(
            dep2_dir.join("Shared/Util.lean"),
            "namespace Shared\ndef v : Nat := 2\nend Shared\n",
        )
        .unwrap();
        let manifest_ambig = r#"{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [
    { "type": "path", "name": "dep_one", "dir": ".lake/packages/dep_one", "configFile": "lakefile.toml", "inherited": false },
    { "type": "path", "name": "dep_two", "dir": ".lake/packages/dep_two", "configFile": "lakefile.toml", "inherited": false }
  ],
  "name": "app_pkg",
  "lakeDir": ".lake",
  "fixedToolchain": false
}"#;
        fs::write(proj_dir.join("lake-manifest.json"), manifest_ambig).unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nroots = [\"App.Main\"]\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("App/Main.lean"),
            "import Shared.Util\ndef m : Nat := Shared.v\n",
        )
        .unwrap();

        // 1. Ambiguous module import across two dependency packages MUST fail closed
        let cfg_ambig = resolve_project_config(&proj_dir).unwrap();
        let ambig_err = build_module_dag(&cfg_ambig, &[]).unwrap_err().to_string();
        assert!(
            ambig_err.contains("Ambiguous module import `Shared.Util`"),
            "expected ambiguous import error, got: {}",
            ambig_err
        );

        // 2. Remove `dep_two` so `Shared.Util` is unambiguous in `dep_one`
        let manifest_single = r#"{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [
    { "type": "path", "name": "dep_one", "dir": ".lake/packages/dep_one", "configFile": "lakefile.toml", "inherited": false }
  ],
  "name": "app_pkg",
  "lakeDir": ".lake",
  "fixedToolchain": false
}"#;
        fs::write(proj_dir.join("lake-manifest.json"), manifest_single).unwrap();
        let cfg = resolve_project_config(&proj_dir).unwrap();
        let dag = build_module_dag(&cfg, &[]).unwrap();
        let main_node = dag.nodes.get("App.Main").unwrap();

        // 3. `compute_module_cas_key` rejects duplicate, unsorted, incomplete, or extra dependency digest vectors
        let err_dup = compute_module_cas_key(
            &cfg,
            main_node,
            &[
                ("Shared.Util".to_string(), "h1".to_string()),
                ("Shared.Util".to_string(), "h1".to_string()),
            ],
            false,
        )
        .unwrap_err()
        .to_string();
        assert!(err_dup.contains("unsorted or duplicate"));

        let err_unsorted = compute_module_cas_key(
            &cfg,
            main_node,
            &[
                ("Z.Mod".to_string(), "h2".to_string()),
                ("Shared.Util".to_string(), "h1".to_string()),
            ],
            false,
        )
        .unwrap_err()
        .to_string();
        assert!(err_unsorted.contains("unsorted or duplicate"));

        let err_missing_dep = compute_module_cas_key(&cfg, main_node, &[], false)
            .unwrap_err()
            .to_string();
        assert!(err_missing_dep.contains("missing required dependency"));

        let err_extra_dep = compute_module_cas_key(
            &cfg,
            main_node,
            &[
                ("Shared.Util".to_string(), "h1".to_string()),
                ("Z.UnrelatedExtraDep".to_string(), "h2".to_string()),
            ],
            false,
        )
        .unwrap_err()
        .to_string();
        assert!(
            err_extra_dep.contains("unexpected extra dependency"),
            "expected extra dependency to be rejected, got: {}",
            err_extra_dep
        );

        // 4. Same-mtime source replacement in `dep_one` (`Shared/Util.lean`) is detected by `.turbo_verified_sources.json` content hash
        let mut store = TurboStore::open(Some(&store_dir)).unwrap();
        let rep1 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(rep1.modules_compiled, 2);

        let util_src = dep1_dir.join("Shared/Util.lean");
        let orig_mtime = fs::metadata(&util_src).unwrap().modified().unwrap();
        fs::write(
            &util_src,
            "namespace Shared\ndef v : Nat := 42\nend Shared\n",
        )
        .unwrap();
        // Force `Shared/Util.lean` back to its exact previous modification timestamp
        if let Ok(f) = fs::File::options().write(true).open(&util_src) {
            let _ = f.set_modified(orig_mtime);
        }
        let rep2 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(
            rep2.modules_compiled, 2,
            "same-mtime source change in dep_one must invalidate Shared.Util and App.Main"
        );

        // 5. H5: When `is_untrusted = true`, pre-existing `.olean` and `.turbo_verified_sources.json` in `dep_one`
        // are NEVER trusted from the checkout; `Shared.Util` is added to `dag.nodes` instead of `external_olean_deps`.
        let dag_untrusted = build_module_dag_with_trust(&cfg, &[], true).unwrap();
        assert!(
            dag_untrusted.nodes.contains_key("Shared.Util"),
            "untrusted DAG must include dependency package module Shared.Util as a DAG node"
        );
        let main_untrusted = dag_untrusted.nodes.get("App.Main").unwrap();
        assert!(
            main_untrusted.external_olean_deps.is_empty(),
            "untrusted DAG must not trust checkout external_olean_deps"
        );

        // 6. H6 & HIGH 1: Verify `build_module_compile_command` places `--setenv LEAN_PATH ...` before `cfg.lean_bin`
        // and `-M 4096` after `cfg.lean_bin`.
        let dummy_tmp = proj_dir.join(".lake/build/.turbo_test_tmp");
        fs::create_dir_all(&dummy_tmp).unwrap();
        let (lp_env, ld_env) = build_lean_search_path(&cfg, true);
        let cmd_bwrap = build_module_compile_command(
            &cfg,
            main_untrusted,
            &dummy_tmp,
            &dummy_tmp.join("App/Main.olean"),
            &dummy_tmp.join("App/Main.ilean"),
            &dummy_tmp.join("App/Main.c"),
            &dummy_tmp.join("App/Main.setup.json"),
            &lp_env,
            &ld_env,
            true,
            Some(Path::new("/usr/bin/bwrap")),
            1,
        )
        .unwrap();
        assert_eq!(
            cmd_bwrap.get_program(),
            std::ffi::OsStr::new("/usr/bin/bwrap")
        );
        let args: Vec<String> = cmd_bwrap
            .get_args()
            .map(|a| a.to_string_lossy().to_string())
            .collect();
        let pos_clearenv = args.iter().position(|a| a == "--clearenv").unwrap();
        let pos_setenv_lp = args
            .windows(3)
            .position(|w| w[0] == "--setenv" && w[1] == "LEAN_PATH" && w[2] == lp_env)
            .expect("bwrap command must contain `--setenv LEAN_PATH <lp_env>`");
        let pos_lean_bin = args
            .iter()
            .position(|a| a == &cfg.lean_bin.to_string_lossy())
            .expect("bwrap command must contain lean_bin");
        let pos_mem = args
            .windows(2)
            .position(|w| w[0] == "-M" && w[1] == "4096")
            .expect("lean args must contain `-M 4096`");
        assert!(
            pos_clearenv < pos_setenv_lp && pos_setenv_lp < pos_lean_bin && pos_lean_bin < pos_mem,
            "expected --clearenv < --setenv LEAN_PATH < lean_bin < -M 4096, got args: {:?}",
            args
        );

        // 7. M7: When `is_untrusted = true` and `bwrap_bin` is `None`, `build_module_compile_command`
        // unconditionally fails closed even if `TURBO_LEAN_ALLOW_NO_BWRAP_IN_CONTAINER=1` is set in env.
        std::env::set_var("TURBO_LEAN_ALLOW_NO_BWRAP_IN_CONTAINER", "1");
        let err_no_bwrap = build_module_compile_command(
            &cfg,
            main_untrusted,
            &dummy_tmp,
            &dummy_tmp.join("App/Main.olean"),
            &dummy_tmp.join("App/Main.ilean"),
            &dummy_tmp.join("App/Main.c"),
            &dummy_tmp.join("App/Main.setup.json"),
            &lp_env,
            &ld_env,
            true,
            None,
            1,
        )
        .unwrap_err()
        .to_string();
        std::env::remove_var("TURBO_LEAN_ALLOW_NO_BWRAP_IN_CONTAINER");
        assert!(
            err_no_bwrap.contains("requires a working bubblewrap"),
            "expected fail-closed error when bwrap is missing, got: {}",
            err_no_bwrap
        );
        // Also verify untrusted search path validation rejects `..` or unbound paths in `lean_path_env`.
        let err_bad_lp = build_module_compile_command(
            &cfg,
            main_untrusted,
            &dummy_tmp,
            &dummy_tmp.join("App/Main.olean"),
            &dummy_tmp.join("App/Main.ilean"),
            &dummy_tmp.join("App/Main.c"),
            &dummy_tmp.join("App/Main.setup.json"),
            "/tmp/unbound_evil_lean_path",
            &ld_env,
            true,
            Some(Path::new("/usr/bin/bwrap")),
            1,
        )
        .unwrap_err()
        .to_string();
        assert!(
            err_bad_lp.contains("Invalid or unbound search path entry"),
            "expected unbound search path rejection, got: {}",
            err_bad_lp
        );

        // 8. Execute a real 2-module untrusted build (`Shared.Util` + `App.Main`) through an executable `bwrap` shim.
        let fake_bwrap = ScopedTestBwrapOverride::write_fake_bwrap_script(&dir).unwrap();
        let mut untrusted_store = TurboStore::open(Some(&dir.join("untrusted_store"))).unwrap();
        let rep_untrusted = {
            let _bwrap_guard =
                ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy().into_owned());
            build_project_modules_native(
                &mut untrusted_store,
                &proj_dir,
                &["App:c".to_string()],
                "untrusted:pr",
                1,
                true,
                true,
                None,
            )
            .unwrap()
        };
        assert!(
            rep_untrusted.bwrap_used
                && rep_untrusted.modules_compiled == 2
                && main_untrusted.c_path.is_file()
        );

        // 9. When rebuilding with `needs_c = false`, stale `Main.c` is removed, and failed staging leaves destination untouched.
        {
            let _bwrap_guard =
                ScopedTestBwrapOverride::set(fake_bwrap.to_string_lossy().into_owned());
            build_project_modules_native(
                &mut untrusted_store,
                &proj_dir,
                &[],
                "untrusted:pr",
                1,
                true,
                true,
                None,
            )
            .unwrap();
        }
        assert!(!main_untrusted.c_path.exists());
        let orig_olean_bytes = fs::read(&main_untrusted.olean_path).unwrap();
        let orig_ilean_bytes = fs::read(&main_untrusted.ilean_path).unwrap();
        let bad_tmp = proj_dir.join(".lake/build/.turbo_bad_pub_tmp");
        fs::create_dir_all(bad_tmp.join("App")).unwrap();
        fs::write(bad_tmp.join("App/Main.olean"), b"corrupt_olean").unwrap();
        #[cfg(unix)]
        std::os::unix::fs::symlink("/etc/passwd", bad_tmp.join("App/Main.ilean")).unwrap();
        let pub_from_tmp = |tmp_root: &Path| {
            publish_module_artifacts_atomic(
                tmp_root,
                main_untrusted,
                &tmp_root.join("App/Main.olean"),
                &tmp_root.join("App/Main.ilean"),
                &tmp_root.join("App/Main.olean.server"),
                &tmp_root.join("App/Main.olean.private"),
                &tmp_root.join("App/Main.ir"),
                &tmp_root.join("App/Main.ir.sig"),
                &tmp_root.join("App/Main.c"),
            )
        };
        assert!(pub_from_tmp(&bad_tmp).is_err());
        assert_eq!(
            fs::read(&main_untrusted.olean_path).unwrap(),
            orig_olean_bytes
        );

        // 10. Phase 2 second-rename failure rollback + stale artifact restoration + inconsistent state reporting.
        let bad_tmp2 = proj_dir.join(".lake/build/.turbo_bad_pub_tmp2");
        fs::create_dir_all(bad_tmp2.join("App")).unwrap();
        fs::write(bad_tmp2.join("App/Main.olean"), b"corrupt_phase2_olean").unwrap();
        fs::write(bad_tmp2.join("App/Main.ilean"), b"corrupt_phase2_ilean").unwrap();
        fs::create_dir_all(main_untrusted.c_path.parent().unwrap()).unwrap();
        fs::write(&main_untrusted.c_path, b"pre_existing_c_bytes").unwrap();
        fs::remove_file(&main_untrusted.ilean_path).unwrap();
        fs::create_dir_all(main_untrusted.ilean_path.join("blocker_subfile")).unwrap();
        assert!(pub_from_tmp(&bad_tmp2).is_err());
        assert_eq!(
            fs::read(&main_untrusted.olean_path).unwrap(),
            orig_olean_bytes
        );
        assert_eq!(
            fs::read(&main_untrusted.c_path).unwrap(),
            b"pre_existing_c_bytes"
        );
        let _ = fs::remove_file(&main_untrusted.c_path);
        let fake_backup = main_untrusted
            .ilean_path
            .parent()
            .unwrap()
            .join(".turbo_test_unrestorable_backup");
        fs::write(&fake_backup, &orig_ilean_bytes).unwrap();
        let rb_err = rollback_publish_state(
            main_untrusted,
            true,
            &[],
            &[BackupRecord {
                dst_path: main_untrusted.ilean_path.clone(),
                backup_file: Some((
                    fake_backup.clone(),
                    blake3::hash(&orig_ilean_bytes),
                    orig_ilean_bytes.len() as u64,
                )),
            }],
        )
        .unwrap_err()
        .to_string();
        let _ = fs::remove_file(&fake_backup);
        assert!(
            rb_err.contains("publication state potentially inconsistent")
                && !main_untrusted.olean_path.exists()
        );
        let _ = fs::remove_dir_all(&main_untrusted.ilean_path);
        fs::write(&main_untrusted.olean_path, &orig_olean_bytes).unwrap();
        fs::write(&main_untrusted.ilean_path, &orig_ilean_bytes).unwrap();

        // 10b. Stale `.ltar`, `.ltar.hash`, `.bc`, and `.bc.hash` cleanup is transactional inside
        // `publish_module_artifacts_atomic`: when all are regular files, publication removes all four;
        // when Phase 2b fails (e.g. a non-empty directory at `Main.bc.hash`), publication fails and
        // rolls back pre-existing `.olean`, `.ilean`, `.ltar`, and `.ltar.hash` cleanly.
        let dst_ltar = main_untrusted.c_path.with_extension("ltar");
        let dst_ltar_hash = PathBuf::from(format!("{}.hash", dst_ltar.display()));
        let dst_bc = main_untrusted.c_path.with_extension("bc");
        let dst_bc_hash = PathBuf::from(format!("{}.hash", dst_bc.display()));
        fs::create_dir_all(dst_ltar.parent().unwrap()).unwrap();
        fs::write(&dst_ltar, b"stale_ltar_bytes").unwrap();
        fs::write(&dst_ltar_hash, b"0123456789abcdef").unwrap();
        fs::create_dir_all(dst_bc_hash.join("blocker_subfile")).unwrap();
        let bad_tmp3 = proj_dir.join(".lake/build/.turbo_bad_pub_tmp3");
        fs::create_dir_all(bad_tmp3.join("App")).unwrap();
        fs::write(bad_tmp3.join("App/Main.olean"), b"corrupt_phase2b_olean").unwrap();
        fs::write(bad_tmp3.join("App/Main.ilean"), b"corrupt_phase2b_ilean").unwrap();
        let phase2b_err = pub_from_tmp(&bad_tmp3).unwrap_err();
        let phase2b_msg = format!("{:#}", phase2b_err);
        assert!(
            phase2b_msg.contains("Failed to remove stale companion artifact"),
            "unexpected error: {}",
            phase2b_msg
        );
        assert_eq!(
            fs::read(&main_untrusted.olean_path).unwrap(),
            orig_olean_bytes
        );
        assert_eq!(
            fs::read(&main_untrusted.ilean_path).unwrap(),
            orig_ilean_bytes
        );
        assert_eq!(fs::read(&dst_ltar).unwrap(), b"stale_ltar_bytes");
        assert_eq!(fs::read(&dst_ltar_hash).unwrap(), b"0123456789abcdef");
        assert!(!validate_materialized_module_artifacts(
            main_untrusted,
            false
        ));
        let _ = fs::remove_dir_all(&dst_bc_hash);
        fs::write(&dst_bc, b"stale_bc_bytes").unwrap();
        fs::write(&dst_bc_hash, b"fedcba9876543210").unwrap();
        let good_tmp3 = proj_dir.join(".lake/build/.turbo_good_pub_tmp3");
        fs::create_dir_all(good_tmp3.join("App")).unwrap();
        fs::write(good_tmp3.join("App/Main.olean"), &orig_olean_bytes).unwrap();
        fs::write(good_tmp3.join("App/Main.ilean"), &orig_ilean_bytes).unwrap();
        pub_from_tmp(&good_tmp3).unwrap();
        assert!(!dst_ltar.exists());
        assert!(!dst_ltar_hash.exists());
        assert!(!dst_bc.exists());
        assert!(!dst_bc_hash.exists());
        assert!(validate_materialized_module_artifacts(
            main_untrusted,
            false
        ));

        // 11. Verify Lake `.hash` and `.trace` sidecars + bit-exact Lake MurmurHash64A parity
        assert_eq!(
            format!("{:016x}", lake_hash_text("-DautoImplicit=false")),
            "4a85acb881fd49d0"
        );
        assert_eq!(
            format!("{:016x}", lake_hash_name("TurboLean.Assembler")),
            "6f4e7ca5f8ee9bd1"
        );
        assert_eq!(
            format!("{:016x}", lake_hash_pkg_id("turbo-lean-proofs")),
            "537b25143adc2c3f"
        );
        assert_eq!(
            format!(
                "{:016x}",
                lake_hash_bytes(b"eb6cafb7290e8bd5f2937522d8d804f58f02bafc")
            ),
            "407ce514b71d5a10"
        );
        let expected_main_dig =
            compute_olean_artifact_set_digest(&main_untrusted.olean_path).unwrap();
        let write_hashes = |art: &str, aud: Option<&str>, clean: bool| {
            write_lake_module_hashes_and_trace(
                &cfg,
                &dag_untrusted,
                main_untrusted,
                art,
                aud,
                clean,
            )
        };
        write_hashes(&expected_main_dig, Some(&expected_main_dig), true).unwrap();
        let olean_hash_p = PathBuf::from(format!("{}.hash", main_untrusted.olean_path.display()));
        let ilean_hash_p = PathBuf::from(format!("{}.hash", main_untrusted.ilean_path.display()));
        let trace_p = main_untrusted.olean_path.with_extension("trace");
        assert!(olean_hash_p.is_file() && fs::read_to_string(&olean_hash_p).unwrap().len() == 16);
        assert!(ilean_hash_p.is_file() && fs::read_to_string(&ilean_hash_p).unwrap().len() == 16);
        let trace_val: serde_json::Value =
            serde_json::from_slice(&fs::read(&trace_p).unwrap()).unwrap();
        assert!(
            trace_val["schemaVersion"] == "2025-09-10"
                && trace_val["depHash"].as_str().unwrap_or_default().len() == 16
        );
        assert!(write_hashes("mismatch_digest", Some(&expected_main_dig), true).is_err());
        assert!(!olean_hash_p.exists() && !ilean_hash_p.exists() && !trace_p.exists());
        assert!(write_hashes(&expected_main_dig, Some(&expected_main_dig), false).is_err());
        assert!(write_hashes(&expected_main_dig, Some("tampered_audit_digest"), true).is_err());
        assert!(write_hashes(&expected_main_dig, None, true).is_err());
        let shared_node = dag_untrusted.nodes.get("Shared.Util").unwrap();
        let shared_hash_p = PathBuf::from(format!("{}.hash", shared_node.olean_path.display()));
        let orig_shared_hash = fs::read_to_string(&shared_hash_p).unwrap();
        fs::write(&shared_hash_p, "0000000000000000").unwrap();
        assert!(write_hashes(&expected_main_dig, Some(&expected_main_dig), true).is_err());
        fs::write(&shared_hash_p, &orig_shared_hash).unwrap();
        let orig_main_src = fs::read_to_string(&main_untrusted.src_path).unwrap();
        fs::write(
            &main_untrusted.src_path,
            "import Shared.Util\ntheorem bad : False := sorry\n",
        )
        .unwrap();
        assert!(write_hashes(&expected_main_dig, Some(&expected_main_dig), true).is_err());
        fs::write(&main_untrusted.src_path, &orig_main_src).unwrap();
        fs::remove_file(&main_untrusted.olean_path).unwrap();
        assert!(write_hashes(&expected_main_dig, Some(&expected_main_dig), true).is_err());

        fs::write(proj_dir.join("App/Empty.lean"), b"").unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nroots = [\"App.Main\", \"App.Empty\"]\n",
        )
        .unwrap();
        let rep_empty = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert!(rep_empty.modules_compiled >= 1);
        let cfg_empty = resolve_project_config(&proj_dir).unwrap();
        let dag_empty = build_module_dag(&cfg_empty, &[]).unwrap();
        let empty_node = dag_empty.nodes.get("App.Empty").unwrap();
        assert!(
            empty_node.olean_path.is_file()
                && empty_node.olean_path.with_extension("trace").is_file()
        );

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_lean_args_allowlist_and_per_target_resolution() {
        assert!(is_allowed_lean_arg("-DmaxHeartbeats=4000000"));
        assert!(!is_allowed_lean_arg(" -DautoImplicit=false "));
        assert!(is_allowed_lean_arg("-j8"));
        assert!(is_allowed_lean_arg("--threads=16"));
        assert!(is_allowed_lean_arg("--tstack=262144"));
        assert!(is_allowed_lean_arg("--json"));
        assert!(is_allowed_lean_arg("-q"));
        assert!(is_allowed_lean_arg("--quiet"));

        assert!(!is_allowed_lean_arg(""));
        assert!(!is_allowed_lean_arg("Foo.lean"));
        assert!(!is_allowed_lean_arg("-Dwarn.sorry=false"));
        assert!(!is_allowed_lean_arg("-D"));
        assert!(!is_allowed_lean_arg("-D=1"));
        assert!(!is_allowed_lean_arg("-Dfoo="));
        assert!(!is_allowed_lean_arg("-Dbad$key=1"));
        assert!(!is_allowed_lean_arg("-Dfoo=bar\nbaz"));
        assert!(!is_allowed_lean_arg("-ofoo.olean"));
        assert!(!is_allowed_lean_arg("--plugin=evil.so"));
        assert!(!is_allowed_lean_arg("--load-dynlib=evil.so"));
        assert!(!is_allowed_lean_arg("--run"));
        assert!(!is_allowed_lean_arg("-j0"));
        assert!(!is_allowed_lean_arg("-j65"));

        assert_eq!(
            filter_allowed_lean_args(["--json", " -q ", "--quiet", "-DautoImplicit=false"]),
            vec!["-DautoImplicit=false".to_string()]
        );
        assert!(compute_lean_args_digest(&["--json".to_string()]).is_err());
        assert!(compute_lean_args_digest(&[" -DautoImplicit=false ".to_string()]).is_err());
        assert_eq!(compute_lean_args_digest(&[]).unwrap(), None);
        assert!(compute_lean_args_digest(&[
            "--plugin=evil.so".to_string(),
            "pos.lean".to_string()
        ])
        .is_err());
        let d_hb_4m = compute_lean_args_digest(&["-DmaxHeartbeats=4000000".to_string()]).unwrap();
        let d_hb_200k = compute_lean_args_digest(&["-DmaxHeartbeats=200000".to_string()]).unwrap();
        assert_ne!(d_hb_4m, d_hb_200k);

        let dir = make_temp_test_dir("per_target_lean_args");
        fs::create_dir_all(dir.join("Fast")).unwrap();
        fs::create_dir_all(dir.join("Heavy")).unwrap();
        let fast_file = dir.join("Fast/Basic.lean");
        let heavy_file = dir.join("Heavy/Big.lean");
        fs::write(&fast_file, "def x : Nat := 1\n").unwrap();
        fs::write(&heavy_file, "def y : Nat := 2\n").unwrap();

        fs::write(
            dir.join("lakefile.toml"),
            r#"name = "unsafe_opts"
moreLeanArgs = ["--plugin=evil.so"]
[[lean_lib]]
name = "Fast"
roots = ["Fast"]
"#,
        )
        .unwrap();
        assert!(resolve_package_config(&dir, false).is_err());
        assert!(try_resolve_lean_args_for_path(&dir, Some(&fast_file)).is_err());
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"dropped\"\nmoreLeanArgs = [\"--json\", \"-q\"]\n",
        )
        .unwrap();
        assert!(try_resolve_lean_args_for_path(&dir, None).is_err());
        fs::write(
            dir.join("lakefile.toml"),
            r#"name = "padded"
moreLeanArgs = [" -DautoImplicit=false "]
"#,
        )
        .unwrap();
        assert!(try_resolve_lean_args_for_path(&dir, None).is_err());

        fs::write(
            dir.join("lakefile.toml"),
            r#"name = "demo_opts"
weakLeanArgs = ["-DmaxHeartbeats=300000"]
[leanOptions]
autoImplicit = false

[[lean_lib]]
name = "Heavy"
roots = ["Heavy"]
globs = ["Heavy.+", "Extra.+"]
moreLeanArgs = ["-DmaxHeartbeats=4000000"]

[[lean_lib]]
name = "Fast"
roots = ["Fast"]
"#,
        )
        .unwrap();

        let fast_args = try_resolve_lean_args_for_path(&dir, Some(&fast_file)).unwrap();
        assert_eq!(
            fast_args,
            vec![
                "-DmaxHeartbeats=300000".to_string(),
                "-DautoImplicit=false".to_string()
            ]
        );
        let heavy_args = try_resolve_lean_args_for_path(&dir, Some(&heavy_file)).unwrap();
        assert_eq!(
            heavy_args,
            vec![
                "-DmaxHeartbeats=300000".to_string(),
                "-DmaxHeartbeats=4000000".to_string(),
                "-DautoImplicit=false".to_string(),
            ]
        );
        // Lake ownership: globs select modules outside the roots, and a file no target owns
        // gets package-level flags rather than those of the first lib sharing its src dir.
        fs::create_dir_all(dir.join("Extra")).unwrap();
        let extra_file = dir.join("Extra/Glob.lean");
        let scratch_file = dir.join("Scratch.lean");
        fs::write(&extra_file, "def z : Nat := 3\n").unwrap();
        fs::write(&scratch_file, "def w : Nat := 4\n").unwrap();
        assert_eq!(
            try_resolve_lean_args_for_path(&dir, Some(&extra_file)).unwrap(),
            heavy_args
        );
        assert_eq!(
            try_resolve_lean_args_for_path(&dir, Some(&scratch_file)).unwrap(),
            try_resolve_lean_args_for_path(&dir, None).unwrap()
        );
        assert_eq!(
            try_resolve_lean_args_for_path(&dir, None).unwrap(),
            fast_args
        );
        fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn test_lakefile_and_manifest_path_fields_reject_escapes() {
        // P0-5: `irDir = "/abs"` (or `..`) in any package used to send `.c` writes and stale
        // deletes anywhere on the host.
        let dir = make_temp_test_dir("path_escape");
        let tf = dir.join("lakefile.toml");
        let lf = dir.join("lakefile.lean");
        for (field, lean_block) in [
            ("srcDir", "package p where\n  srcDir := {v}\n"),
            ("buildDir", "package p where\n  buildDir := {v}\n"),
            ("leanLibDir", "package p where\n  leanLibDir := {v}\n"),
            ("irDir", "package p where\n  irDir := {v}\n"),
            ("packagesDir", "package p where\n  packagesDir := {v}\n"),
            ("nativeLibDir", "package p where\n  nativeLibDir := {v}\n"),
            ("srcDir", "package p\nlean_lib A where\n  srcDir := {v}\n"),
        ] {
            for bad in ["/tmp/turbo-evil", "../sibling", "src/../../up"] {
                for is_root in [true, false] {
                    let toml = if lean_block.contains("lean_lib") {
                        format!("name = \"p\"\n[[lean_lib]]\nname = \"A\"\n{field} = \"{bad}\"\n")
                    } else {
                        format!("name = \"p\"\n{field} = \"{bad}\"\n")
                    };
                    fs::write(&tf, toml).unwrap();
                    let err = parse_lakefile_toml(&dir, &tf, is_root)
                        .unwrap_err()
                        .to_string();
                    assert!(
                        err.contains(field) && err.contains("relative"),
                        "{field}={bad}: {err}"
                    );
                    let lean = format!(
                        "import Lake\nopen Lake DSL\n{}",
                        lean_block.replace("{v}", &format!("\"{bad}\""))
                    );
                    fs::write(&lf, lean).unwrap();
                    let err = parse_lakefile_lean(&dir, &lf, is_root)
                        .unwrap_err()
                        .to_string();
                    assert!(
                        err.contains(field) && err.contains("relative"),
                        "{field}={bad}: {err}"
                    );
                }
            }
        }
        // Package-relative paths keep working.
        fs::write(
            &tf,
            "name = \"p\"\nsrcDir = \"./src\"\nbuildDir = \"out/build\"\n",
        )
        .unwrap();
        let pkg = parse_lakefile_toml(&dir, &tf, true).unwrap();
        assert_eq!(pkg.build_dir, PathBuf::from("out/build"));
        fs::remove_file(&tf).unwrap();
        fs::remove_file(&lf).unwrap();

        let manifest = |pkgs_dir: &str, pkg: serde_json::Value| {
            let m = serde_json::json!({"version": "1.1.0", "packagesDir": pkgs_dir,
                "packages": [pkg]});
            fs::write(dir.join("lake-manifest.json"), m.to_string()).unwrap();
        };
        let git = |name: &str| serde_json::json!({"type": "git", "name": name, "rev": "0"});
        manifest("/tmp/turbo-evil", git("dep"));
        assert!(parse_lake_manifest(&dir, false).is_err());
        manifest("../up", git("dep"));
        assert!(parse_lake_manifest(&dir, false).is_err());
        manifest(".lake/packages", git("../../escape"));
        assert!(parse_lake_manifest(&dir, false).is_err());
        let mut sub = git("dep");
        sub["subDir"] = "../../escape".into();
        manifest(".lake/packages", sub);
        assert!(parse_lake_manifest(&dir, false).is_err());
        // A `path` dependency on another host project: untrusted builds would publish into it.
        for d in ["../other-project", "/home/victim/project"] {
            manifest(
                ".lake/packages",
                serde_json::json!({"type": "path", "name": "dep", "dir": d}),
            );
            let err = parse_lake_manifest(&dir, true).unwrap_err().to_string();
            assert!(err.contains("`dir`"), "{err}");
            // A trusted workspace may still use a sibling checkout, as Lake does.
            let (_, entries, _) = parse_lake_manifest(&dir, false).unwrap();
            assert_eq!(entries[0].dir, dir.join(d));
        }
        manifest(".lake/packages", git("dep"));
        let (pkgs_dir, entries, _) = parse_lake_manifest(&dir, true).unwrap();
        assert_eq!(pkgs_dir, PathBuf::from(".lake/packages"));
        assert_eq!(entries[0].dir, dir.join(".lake/packages/dep"));
        let _ = fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_untrusted_build_never_writes_outside_the_checkout() {
        // P0-5: a symlinked build directory or a dependency that resolves elsewhere on the host
        // must fail before the first filesystem write.
        let root = make_temp_test_dir("write_escape");
        let proj = root.join("proj");
        let outside = root.join("outside");
        fs::create_dir_all(proj.join("P")).unwrap();
        fs::create_dir_all(&outside).unwrap();
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"p\"\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n",
        )
        .unwrap();
        fs::write(proj.join("P/A.lean"), "def a : Nat := 1\n").unwrap();
        // Skip only when the host lacks the toolchain; any other resolution error is a failure.
        let tc = "leanprover/lean4:v4.35.0";
        if resolve_toolchain_compiler_with_trust(&proj, tc, true).is_err() {
            eprintln!("skipping: no Lean v4.35.0 toolchain on this host");
            return;
        }
        resolve_project_config_with_trust(&proj, true).unwrap();
        std::os::unix::fs::symlink(&outside, proj.join(".lake")).unwrap();
        let mut store = TurboStore::open(Some(&root.join("store"))).unwrap();
        let err = build_project_modules_native(
            &mut store,
            &proj,
            &[],
            "untrusted:pr",
            1,
            true,
            true,
            None,
        )
        .unwrap_err()
        .to_string();
        assert!(err.contains("fail-closed build path gate"), "{err}");
        assert_eq!(fs::read_dir(&outside).unwrap().count(), 0, "wrote outside");
        // A trusted build keeps following the user's own symlinks.
        let cfg = resolve_project_config(&proj).unwrap();
        let dag = build_module_dag(&cfg, &[]).unwrap();
        let canon = proj.canonicalize().unwrap();
        validate_build_write_dirs(&cfg, &dag, &canon, false).unwrap();
        assert!(validate_build_write_dirs(&cfg, &dag, &canon, true).is_err());
        fs::remove_file(proj.join(".lake")).unwrap();

        // A dependency symlinked to another project on the host.
        let other = root.join("other");
        fs::create_dir_all(other.join("Q")).unwrap();
        fs::write(
            other.join("lakefile.toml"),
            "name = \"q\"\n[[lean_lib]]\nname = \"Q\"\n",
        )
        .unwrap();
        fs::write(other.join("Q.lean"), "def q : Nat := 1\n").unwrap();
        fs::create_dir_all(proj.join(".lake/packages")).unwrap();
        std::os::unix::fs::symlink(&other, proj.join(".lake/packages/q")).unwrap();
        let err = resolve_project_config_with_trust(&proj, true)
            .unwrap_err()
            .to_string();
        assert!(err.contains("outside the workspace"), "{err}");
        resolve_project_config_with_trust(&proj, false).unwrap();
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn test_dependency_lakefile_compile_affecting_config_fails_closed() {
        // P0-6: a dependency's compile-affecting settings used to be skipped silently, so its
        // modules were built differently from Lake yet published with a Lake trace.
        let dir = make_temp_test_dir("dep_fail_closed");
        let tf = dir.join("lakefile.toml");
        let lib = "[[lean_lib]]\nname = \"A\"\n";
        for (top, lib_extra) in [
            ("buildType = \"debug\"\n", ""),
            ("buildType = \"Debug\"\n", ""),
            ("plugins = [\"evil\"]\n", ""),
            ("dynlibs = [\"evil\"]\n", ""),
            ("precompileImports = true\n", ""),
            ("backend = \"llvm\"\n", ""),
            ("extraDepTargets = [\"gen\"]\n", ""),
            ("someFutureKey = 1\n", ""),
            ("\"buildType\" = \"debug\"\n", ""),
            ("", "buildType = \"debug\"\n"),
            ("", "defaultFacets = [\"customFacet\"]\n"),
            ("", "extraDepTargets = [\"gen\"]\n"),
            ("", "someFutureKey = 1\n"),
        ] {
            let src = format!("name = \"d\"\n{top}{lib}{lib_extra}");
            fs::write(&tf, &src).unwrap();
            let err = parse_lakefile_toml(&dir, &tf, true)
                .unwrap_err()
                .to_string();
            assert!(err.contains("fail-closed"), "{src}: {err}");
            let pkg = parse_lakefile_toml(&dir, &tf, false).unwrap();
            let why = pkg.unsupported.clone().or(pkg.libs[0].unsupported.clone());
            assert!(why.is_some(), "dependency accepted `{src}`");
        }
        // A `needs` naming a target is stricter than `unsupported`: it fails closed for a
        // dependency too. This parser reads no `input_file` / `input_dir` declarations out of
        // TOML, so the named input is one nothing hashes, and recording it would leave the
        // digest and staleness callers -- which only resolve the config -- vouching for a stale
        // `.olean`. An empty `needs` still passes for every package (checked below).
        fs::write(&tf, format!("name = \"d\"\n{lib}needs = [\"gen\"]\n")).unwrap();
        for is_root in [true, false] {
            let err = parse_lakefile_toml(&dir, &tf, is_root)
                .unwrap_err()
                .to_string();
            assert!(
                err.contains("fail-closed") && err.contains("needs"),
                "{err}"
            );
        }
        // Lake reads a quoted key as the bare key, so a quoted `moreLeanArgs` applies.
        fs::write(
            &tf,
            format!("name = \"d\"\n\"moreLeanArgs\" = [\"-DautoImplicit=false\"]\n{lib}"),
        )
        .unwrap();
        for is_root in [true, false] {
            let pkg = parse_lakefile_toml(&dir, &tf, is_root).unwrap();
            assert_eq!(pkg.more_lean_args, vec!["-DautoImplicit=false".to_string()]);
        }
        fs::write(
            &tf,
            format!("name = \"d\"\n'moreLeanArgs' = [\"--plugin=x.so\"]\n{lib}"),
        )
        .unwrap();
        assert!(parse_lakefile_toml(&dir, &tf, false).is_err());
        // Settings Lake builds identically with (and metadata) pass for every package.
        fs::write(
            &tf,
            format!(
                "name = \"d\"\nplatformIndependent = false\nbuildType = \"release\"\n\
                 precompileImports = false\ntestRunner = \"T\"\nfixedToolchain = true\n\
                 moreLinkArgs = [\"-lfoo\"]\n{lib}platformIndependent = true\nneeds = []\nlibName = \"a\"\n"
            ),
        )
        .unwrap();
        for is_root in [true, false] {
            let pkg = parse_lakefile_toml(&dir, &tf, is_root).unwrap();
            assert_eq!(pkg.platform_independent, Some(false));
            assert_eq!(pkg.libs[0].platform_independent, Some(true));
            assert!(pkg.unsupported.is_none() && pkg.libs[0].unsupported.is_none());
        }
        fs::remove_file(&tf).unwrap();

        let lf = dir.join("lakefile.lean");
        let head = "import Lake\nopen Lake DSL\n";
        for body in [
            "package d where\n  buildType := .debug\nlean_lib A\n",
            "package d where\n  buildType := BuildType.debug\nlean_lib A\n",
            "package d where\n  precompileImports := true\nlean_lib A\n",
            "package d where\n  bootstrap := true\nlean_lib A\n",
            "package d where\n  someFutureKey := 1\nlean_lib A\n",
            "package d\nlean_lib A where\n  needs := #[gen]\n",
            "package d\nlean_lib A where\n  extraDepTargets := #[`gen]\n",
            "package d\nlean_lib A where\n  defaultFacets := #[LeanLib.customFacet]\n",
            "package d\nlean_lib A where\n  someFutureKey := 1\n",
            "package d\nmeta if true then\n  lean_lib B\nlean_lib A\n",
            "package d\n#eval IO.println \"x\"\nlean_lib A\n",
            "package d\nset_option autoImplicit false\nlean_lib A\n",
            "package d\ninput_file gen where\n  path := \"x\"\nlean_lib A\n",
        ] {
            let src = format!("{head}{body}");
            fs::write(&lf, &src).unwrap();
            let err = parse_lakefile_lean(&dir, &lf, true)
                .unwrap_err()
                .to_string();
            assert!(err.contains("fail-closed"), "{src}: {err}");
            // Syntax the reader cannot follow (e.g. `.debug`) fails to parse for any package.
            match parse_lakefile_lean(&dir, &lf, false) {
                Ok(pkg) => {
                    let why = pkg.unsupported.clone().or(pkg.libs[0].unsupported.clone());
                    assert!(why.is_some(), "dependency accepted `{src}`");
                }
                Err(e) => eprintln!("dependency rejected `{src}`: {e}"),
            }
        }
        // A dependency's update hook may spawn processes; it never runs during a build.
        fs::write(
            &lf,
            format!(
                "{head}package d where\n  platformIndependent := false\n  fixedToolchain := true\n\
                 lean_lib A where\n  platformIndependent := true\npost_update pkg do\n  let _ ← IO.Process.getCurrentDir\n"
            ),
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
        assert_eq!(pkg.platform_independent, Some(false));
        assert_eq!(pkg.libs[0].platform_independent, Some(true));
        assert!(pkg.unsupported.is_none() && pkg.libs[0].unsupported.is_none());
        assert!(parse_lakefile_lean(&dir, &lf, true).is_err());
        // Mathlib as a dependency stays buildable.
        fs::write(
            &lf,
            include_str!("../tests/fixtures/mathlib-0df444a3-lakefile.lean"),
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
        assert_eq!(pkg.unsupported, None);
        assert!(pkg.libs.iter().all(|l| l.unsupported.is_none()));
        assert!(pkg.exes.iter().all(|e| e.unsupported.is_none()));
        let _ = fs::remove_dir_all(&dir);

        // Building (not reusing) a module of such a dependency fails closed.
        let proj = make_temp_test_dir("dep_fail_closed_dag");
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"app\"\n[[lean_lib]]\nname = \"App\"\n",
        )
        .unwrap();
        fs::write(proj.join("App.lean"), "import Dep\ndef app : Nat := 1\n").unwrap();
        let dep = proj.join(".lake/packages/dep");
        fs::create_dir_all(&dep).unwrap();
        fs::write(
            dep.join("lakefile.toml"),
            "name = \"dep\"\nbuildType = \"debug\"\n[[lean_lib]]\nname = \"Dep\"\n",
        )
        .unwrap();
        fs::write(dep.join("Dep.lean"), "def dep : Nat := 1\n").unwrap();
        let cfg = resolve_project_config(&proj).unwrap();
        let err = build_module_dag_with_trust(&cfg, &[], true)
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("`Dep`") && err.contains("buildType") && err.contains("fail-closed"),
            "{err}"
        );
        fs::write(
            dep.join("lakefile.toml"),
            "name = \"dep\"\nbuildType = \"release\"\n[[lean_lib]]\nname = \"Dep\"\n",
        )
        .unwrap();
        let cfg = resolve_project_config(&proj).unwrap();
        build_module_dag_with_trust(&cfg, &[], true).unwrap();
        // `precompileModules = true` on a dependency is supported in trusted mode, and rejected in untrusted mode.
        fs::write(
            dep.join("lakefile.toml"),
            "name = \"dep\"\n[[lean_lib]]\nname = \"Dep\"\nprecompileModules = true\n",
        )
        .unwrap();
        let cfg = resolve_project_config(&proj).unwrap();
        build_module_dag_with_trust(&cfg, &[], false).unwrap();
        let err_sh = build_module_dag_with_trust(&cfg, &[], true)
            .unwrap_err()
            .to_string();
        assert!(err_sh.contains("fail-closed"), "{err_sh}");
        // `defaultFacets = ["shared"]` on the root library is supported in trusted mode, and rejected in untrusted mode.
        fs::write(
            dep.join("lakefile.toml"),
            "name = \"dep\"\n[[lean_lib]]\nname = \"Dep\"\n",
        )
        .unwrap();
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"app\"\n[[lean_lib]]\nname = \"App\"\ndefaultFacets = [\"shared\"]\n",
        )
        .unwrap();
        let cfg = resolve_project_config(&proj).unwrap();
        build_module_dag_with_trust(&cfg, &[], false).unwrap();
        let err_root_sh = build_module_dag_with_trust(&cfg, &[], true)
            .unwrap_err()
            .to_string();
        assert!(err_root_sh.contains("fail-closed"), "{err_root_sh}");
        let _ = fs::remove_dir_all(&proj);
    }

    #[test]
    fn test_lake_config_file_choice_precompile_and_enum_literals_follow_lake() {
        let dir = make_temp_test_dir("lake_config_choice");
        let toml = "name = \"t\"\n[[lean_lib]]\nname = \"FromToml\"\n";
        let lean = "import Lake\nopen Lake DSL\npackage t\nlean_lib FromLean\n";
        // Lake loads `lakefile.lean` when both are present.
        fs::write(dir.join("lakefile.toml"), toml).unwrap();
        fs::write(dir.join("lakefile.lean"), lean).unwrap();
        let pkg = resolve_package_config(&dir, false).unwrap();
        assert_eq!(pkg.libs[0].name, "FromLean");
        // ... and a manifest `configFile`, with or without an extension.
        fs::create_dir_all(dir.join("cfg")).unwrap();
        fs::write(dir.join("cfg/custom.toml"), toml).unwrap();
        for cfg in ["cfg/custom", "cfg/custom.toml"] {
            let pkg = resolve_package_config_file(&dir, false, Some(cfg)).unwrap();
            assert_eq!(pkg.libs[0].name, "FromToml", "{cfg}");
        }
        assert!(resolve_package_config_file(&dir, false, Some("../x")).is_err());
        assert!(resolve_package_config_file(&dir, false, Some("missing")).is_err());

        // `precompileModules = true` parses cleanly in static Lake configs for trusted native
        // builds, and is rejected at the untrusted DAG gate (`build_module_dag_with_trust`).
        for (file, src, pkg_flag, lib_flag) in [
            ("lakefile.toml", "name = \"t\"\nprecompileModules = true\n", true, None),
            (
                "lakefile.toml",
                "name = \"t\"\n[[lean_lib]]\nname = \"A\"\nprecompileModules = true\n",
                false,
                Some(true),
            ),
            (
                "lakefile.lean",
                "import Lake\nopen Lake DSL\npackage t where\n  precompileModules := true\n",
                true,
                None,
            ),
            (
                "lakefile.lean",
                "import Lake\nopen Lake DSL\npackage t\nlean_lib A where\n  precompileModules := true\n",
                false,
                Some(true),
            ),
        ] {
            let f = dir.join(file);
            fs::write(&f, src).unwrap();
            for is_root in [true, false] {
                let pkg = if file.ends_with("toml") {
                    parse_lakefile_toml(&dir, &f, is_root)
                } else {
                    parse_lakefile_lean(&dir, &f, is_root)
                }
                .unwrap();
                assert_eq!(pkg.precompile_modules, pkg_flag, "{src}");
                assert_eq!(
                    pkg.libs.first().and_then(|l| l.precompile_modules),
                    lib_flag,
                    "{src}"
                );
            }
        }
        // Only a plain enum literal can pass: Lake evaluates any other expression.
        for v in [
            "if true then .llvm else .default",
            "match x with | _ => .c",
            "(.c)",
            "\"llvm\"",
            "Backend.default",
            "Lake.Backend.c",
            ".C",
            ".Default",
            "\"C\"",
        ] {
            assert!(
                matches!(
                    classify_lake_field(LakeScope::Package, "backend", v),
                    LakeField::Unsupported
                ),
                "{v}"
            );
        }
        for v in [".c", ".default", "\"c\""] {
            assert!(matches!(
                classify_lake_field(LakeScope::Lib, "backend", v),
                LakeField::Passive
            ));
        }
        for (v, ok) in [
            ("\"Release\"", true),
            ("\"minSizeRel\"", true),
            (".relWithDebInfo", true),
            (".Release", false),
            (".debug", false),
            ("\"debug\"", false),
        ] {
            assert_eq!(
                matches!(
                    classify_lake_field(LakeScope::Package, "buildType", v),
                    LakeField::Passive
                ),
                ok,
                "{v}"
            );
        }
        // A dependency's own helper can shadow a non-constructor enum name.
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\ndef Lake.Backend.C : Lake.Backend := .llvm\npackage t where\n  backend := .C\nlean_lib A\n",
        )
        .unwrap();
        assert!(parse_lakefile_lean(&dir, &lf, false)
            .unwrap()
            .unsupported
            .is_some());
        // ... or a qualified enum name.
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\ndef Backend.default : Lake.Backend := .llvm\npackage t where\n  backend := Backend.default\nlean_lib A\n",
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
        assert!(pkg.unsupported.is_some());
        // A command hidden after a helper on the same line, or indented inside a body the reader
        // skips, still configures Lake.
        for body in [
            "def helper := 0 package t where\n  precompileModules := true\nlean_lib A\n",
            "package t\ndef helper := 0\n  lean_lib Hidden where\n    moreLeanArgs := #[\"-DautoImplicit=false\"]\nlean_lib A\n",
            "package t\npost_update pkg do\n  pure ()\n  set_option maxHeartbeats 1\nlean_lib A\n",
            "package t\nrequire foo from git\n  \"https://x\" @ \"main\" lean_lib Hidden\nlean_lib A\n",
            "package t where\n  moreLinkArgs := #[]\n    lean_exe Hidden\nlean_lib A\n",
            "package t\nlean_lib A\ndef helper := #[0\n] lean_lib Hidden where\n  roots := #[`A]\n  precompileModules := true\n",
            "package t\nlean_lib A\nabbrev x := 1\nfoo lean_exe Hidden\n",
        ] {
            fs::write(&lf, format!("import Lake\nopen Lake DSL\n{body}")).unwrap();
            assert!(parse_lakefile_lean(&dir, &lf, true).is_err(), "{body}");
            // Otherwise rejected outright by another guard.
            if let Ok(pkg) = parse_lakefile_lean(&dir, &lf, false) {
                assert!(pkg.unsupported.is_some(), "{body}");
            }
        }
        // Empty `plugins`/`dynlibs` change nothing; non-empty ones fail closed.
        for (field, ok) in [
            ("plugins := #[]", true),
            ("dynlibs := #[]", true),
            ("plugins := #[p]", false),
        ] {
            fs::write(
                &lf,
                format!("import Lake\nopen Lake DSL\npackage t\nlean_lib A where\n  {field}\n"),
            )
            .unwrap();
            assert_eq!(parse_lakefile_lean(&dir, &lf, true).is_ok(), ok, "{field}");
            let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
            assert_eq!(pkg.libs[0].unsupported.is_none(), ok, "{field}");
        }
        // Lake's TOML decoder ignores `nativeFacets`.
        let tf = dir.join("lakefile.toml");
        fs::write(
            &tf,
            "name = \"t\"\n[[lean_lib]]\nname = \"A\"\nnativeFacets = []\n[[lean_exe]]\nname = \"e\"\nnativeFacets = []\n",
        )
        .unwrap();
        let pkg = parse_lakefile_toml(&dir, &tf, false).unwrap();
        assert!(pkg.libs[0].unsupported.is_none() && pkg.exes[0].unsupported.is_none());
        // Empty arrays pass however they are spelled.
        fs::write(
            &tf,
            "name = \"t\"\n[[lean_lib]]\nname = \"A\"\nplugins = [ ]\ndynlibs = [\n]\n",
        )
        .unwrap();
        assert!(parse_lakefile_toml(&dir, &tf, true).is_ok());
        assert!(parse_lakefile_toml(&dir, &tf, true).is_ok());
        fs::remove_file(&tf).unwrap();
        // Imports beyond `Lake` could change how the lakefile elaborates.
        for imp in ["import Lake Foo", "import Mathlib"] {
            fs::write(
                &lf,
                format!("{imp}\nopen Lake DSL\npackage t\nlean_lib A\n"),
            )
            .unwrap();
            assert!(parse_lakefile_lean(&dir, &lf, true).is_err(), "{imp}");
            assert!(
                parse_lakefile_lean(&dir, &lf, false)
                    .unwrap()
                    .unsupported
                    .is_some(),
                "{imp}"
            );
        }
        // An unsupported field only marks the target that sets it, for a dependency.
        let lf = dir.join("lakefile.lean");
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage t\nlean_lib A where\n  someFutureKey := 1\nlean_lib B where\n  needs := #[]\n",
        )
        .unwrap();
        let pkg = parse_lakefile_lean(&dir, &lf, false).unwrap();
        assert!(pkg.unsupported.is_none() && pkg.libs[1].unsupported.is_none());
        assert!(pkg.libs[0].unsupported.is_some());
        assert!(parse_lakefile_lean(&dir, &lf, true).is_err());
        // `needs` is no longer one of those fields: it is read (into `lib.needs`) and folded into
        // every cache key, so a `needs` naming a declared input is simply supported, while one
        // naming nothing fails closed for *every* package rather than marking its target. The
        // declaration is what the digests key on, so a dependency resolve that silently kept a
        // `needs` pointing at no input would hand "unchanged" to code deciding staleness.
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage t\nlean_lib A where\n  needs := #[gen]\n",
        )
        .unwrap();
        for is_root in [true, false] {
            let err = parse_lakefile_lean(&dir, &lf, is_root)
                .unwrap_err()
                .to_string();
            assert!(
                err.contains("fail-closed") && err.contains("`gen`"),
                "{err}"
            );
        }
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage t\ninput_file gen where\n  path := \"g.txt\"\nlean_lib A where\n  needs := #[gen]\n",
        )
        .unwrap();
        fs::write(dir.join("g.txt"), "g\n").unwrap();
        for is_root in [true, false] {
            let pkg = parse_lakefile_lean(&dir, &lf, is_root).unwrap();
            assert!(pkg.unsupported.is_none() && pkg.libs[0].unsupported.is_none());
            assert_eq!(pkg.libs[0].needs, vec!["gen".to_string()]);
        }
        let _ = fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_planted_lock_symlink_and_foreign_cas_paths_never_write_outside() {
        let root = make_temp_test_dir("lock_cas_escape");
        let proj = root.join("proj");
        let outside = root.join("outside");
        fs::create_dir_all(proj.join(".lake/build")).unwrap();
        fs::create_dir_all(&outside).unwrap();
        // A checked-in `.turbo_publish.lock` symlink must not create a file elsewhere.
        let lock = proj.join(".lake/build/.turbo_publish.lock");
        std::os::unix::fs::symlink(outside.join("created"), &lock).unwrap();
        assert!(crate::shm_cache::acquire_flock(&lock, true, false).is_err());
        assert!(acquire_publish_flock_mode(&proj, true, false).is_err());
        assert!(!outside.join("created").exists());
        // Predictable staging names (`.turbo_stage_sidecar_*`, backups, manifest tmp files)
        // replace a planted symlink instead of writing through it.
        let stage = proj.join(".lake/build/.turbo_stage_sidecar_1_1_P.olean.hash");
        std::os::unix::fs::symlink(outside.join("staged"), &stage).unwrap();
        fs::write(outside.join("victim"), b"keep").unwrap();
        let stage2 = proj.join(".lake/build/.turbo_backup_1_1_P.olean");
        std::os::unix::fs::symlink(outside.join("victim"), &stage2).unwrap();
        for p in [&stage, &stage2] {
            use std::io::Write;
            create_fresh_file(p).unwrap().write_all(b"x").unwrap();
            assert!(!fs::symlink_metadata(p).unwrap().file_type().is_symlink());
        }
        assert!(!outside.join("staged").exists());
        assert_eq!(fs::read(outside.join("victim")).unwrap(), b"keep");

        // A cache entry restores only onto the node's own artifact paths.
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"p\"\n[[lean_lib]]\nname = \"P\"\n",
        )
        .unwrap();
        fs::write(proj.join("P.lean"), "def p : Nat := 1\n").unwrap();
        fs::remove_file(&lock).unwrap();
        let cfg = resolve_project_config(&proj).unwrap();
        let dag = build_module_dag(&cfg, &[]).unwrap();
        let node = &dag.nodes["P"];
        let canon = proj.canonicalize().unwrap();
        let entry = |rel: &str| BlobEntry {
            blob_hash: "00".into(),
            kind: "olean".into(),
            size_bytes: 1,
            rel_path: rel.into(),
        };
        let own = node
            .olean_path
            .strip_prefix(&canon)
            .unwrap()
            .to_string_lossy()
            .to_string();
        let ilean = node
            .ilean_path
            .strip_prefix(&canon)
            .unwrap()
            .to_string_lossy()
            .to_string();
        assert!(cas_outputs_bound_to_node(
            &[entry(&own), entry(&ilean), entry("thm:x")],
            &canon,
            node
        ));
        for foreign in [
            "vendor/old/.lake/build/lib/lean/P.olean",
            ".lake/build/lib/lean/../../../../outside/P.olean",
            outside.join("P.olean").to_str().unwrap(),
        ] {
            assert!(
                !cas_outputs_bound_to_node(&[entry(&own), entry(foreign)], &canon, node),
                "{foreign}"
            );
        }
        let _ = fs::remove_dir_all(&root);
    }
    #[test]
    fn test_precompile_library_fails_closed_everywhere() {
        // Lake's `LeanLib.shouldPrecompile` also covers `precompileLibrary`: importers load it.
        let dir = make_temp_test_dir("precompile_library");
        let tf = dir.join("lakefile.toml");
        let lf = dir.join("lakefile.lean");
        fs::write(
            &tf,
            "name = \"t\"\n[[lean_lib]]\nname = \"A\"\nprecompileLibrary = true\n",
        )
        .unwrap();
        fs::write(
            &lf,
            "import Lake\nopen Lake DSL\npackage t\nlean_lib A where\n  precompileLibrary := true\n",
        )
        .unwrap();
        for is_root in [true, false] {
            let e = parse_lakefile_toml(&dir, &tf, is_root)
                .unwrap_err()
                .to_string();
            assert!(e.contains("precompileLibrary"), "{e}");
            let e = parse_lakefile_lean(&dir, &lf, is_root)
                .unwrap_err()
                .to_string();
            assert!(e.contains("precompileLibrary"), "{e}");
        }
        fs::write(
            &tf,
            "name = \"t\"\n[[lean_lib]]\nname = \"A\"\nprecompileLibrary = false\n",
        )
        .unwrap();
        parse_lakefile_toml(&dir, &tf, false).unwrap();
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_toml_key_ty_redefinition_and_prefix_conflicts_fail_closed() {
        let dir = make_temp_test_dir("toml_key_ty");
        let tf = dir.join("lakefile.toml");
        for bad in [
            "name = \"t\"\nname = \"t2\"\n",
            "name = \"t\"\n[leanOptions]\nautoImplicit = false\nautoImplicit = true\n",
            "name = \"t\"\nleanOptions.autoImplicit = false\n[leanOptions]\npp.all = true\n",
            "name = \"t\"\n[leanOptions]\npp = true\npp.all = false\n",
            "name = \"t\"\n[leanOptions]\npp.all = false\npp = true\n",
            "name = \"t\"\nleanOptions = {}\n[[leanOptions]]\nautoImplicit = false\n",
            "name = \"t\"\n[[lean_lib]]\nname = \"A\"\n[lean_lib]\nname = \"B\"\n",
            "name = \"t\"\n[[lean_lib]]\nname = \"A\"\nname = \"B\"\n",
        ] {
            fs::write(&tf, bad).unwrap();
            for is_root in [true, false] {
                let err = parse_lakefile_toml(&dir, &tf, is_root)
                    .unwrap_err()
                    .to_string();
                assert!(err.contains("cannot redefine"), "{bad}: {err}");
            }
        }
        // Valid nested array-of-tables + subtable (`[[lean_lib]]` followed by `[lean_lib.leanOptions]`)
        // and multiple `[[lean_lib]]` elements with independent keys must elaborate cleanly.
        let valid = r#"name = "t"
[leanOptions.pp.unicode]
fun = true
[leanOptions]
autoImplicit = false
[[lean_lib]]
name = "A"
[lean_lib.leanOptions]
autoImplicit = true
[[lean_lib]]
name = "B"
[lean_lib.leanOptions]
autoImplicit = false
"#;
        fs::write(&tf, valid).unwrap();
        let pkg = parse_lakefile_toml(&dir, &tf, true).unwrap();
        assert_eq!(pkg.libs.len(), 2);
        assert_eq!(pkg.libs[0].name, "A");
        assert_eq!(pkg.libs[1].name, "B");
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_ws9_lake_parity_differential_all_five_findings() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("ws9_lake_parity_5");
        let store_dir = dir.join("store");
        let lake_cache = dir.join("lake_cache");
        fs::create_dir_all(&lake_cache).unwrap();
        let mut store = TurboStore::open(Some(&store_dir)).unwrap();

        // ------------------------------------------------------------------
        // Subcase A: `platformIndependent` (None / false / true), `baseName` vs
        // `origName` (`orig-dep` aliased to `dep-alias`), duplicate `origName`
        // deps (`dup_orig` at two `pkg_root`s), unqualified `lib.name` dedup,
        // `build_setup_json` `import all` through non-module -> module, and
        // `+Main:dynlib` on an executable root module.
        // ------------------------------------------------------------------
        let ws = dir.join("ws");
        let dep_alias_dir = ws.join("deps/dep_alias_dir");
        let dup1_dir = ws.join("deps/dup1_dir");
        let dup2_dir = ws.join("deps/dup2_dir");
        fs::create_dir_all(dep_alias_dir.join("OrigLib")).unwrap();
        fs::create_dir_all(dup1_dir.join("DupOne")).unwrap();
        fs::create_dir_all(dup2_dir.join("DupTwo")).unwrap();
        fs::create_dir_all(ws.join("PiNone")).unwrap();
        fs::create_dir_all(ws.join("PiFalse")).unwrap();
        fs::create_dir_all(ws.join("PiTrue")).unwrap();
        fs::create_dir_all(ws.join("ModChain")).unwrap();

        for p in [&ws, &dep_alias_dir, &dup1_dir, &dup2_dir] {
            fs::write(p.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }

        // Dep 1: origName = `orig-dep`, manifest baseName = `dep-alias`, precompileModules = true
        fs::write(
            dep_alias_dir.join("lakefile.toml"),
            "name = \"orig-dep\"\ndefaultTargets = [\"OrigLib\"]\n[[lean_lib]]\nname = \"OrigLib\"\nprecompileModules = true\n",
        )
        .unwrap();
        fs::write(
            dep_alias_dir.join("OrigLib.lean"),
            "import OrigLib.Sub\ndef origVal : Nat := origSub + 1\n",
        )
        .unwrap();
        fs::write(
            dep_alias_dir.join("OrigLib/Sub.lean"),
            "def origSub : Nat := 10\n",
        )
        .unwrap();

        // Dep 2 & Dep 3: SAME `origName` (`dup_orig`), distinct `pkg_root` & manifest `base_name` (`dup_one`, `dup_two`).
        // Dep 2 also declares library `SameLib` (`precompileModules = true`) to test unqualified `lib.name` dedup
        // when root also declares `SameLib` or another dep declares `SameLib`.
        fs::write(
            dup1_dir.join("lakefile.toml"),
            "name = \"dup_orig\"\ndefaultTargets = [\"DupOne\"]\n[[lean_lib]]\nname = \"DupOne\"\nprecompileModules = true\n[[lean_lib]]\nname = \"SameLib\"\nprecompileModules = true\n",
        )
        .unwrap();
        fs::write(dup1_dir.join("DupOne.lean"), "def dupOne : Nat := 101\n").unwrap();
        fs::write(
            dup1_dir.join("SameLib.lean"),
            "def sameFromOne : Nat := 201\n",
        )
        .unwrap();

        fs::write(
            dup2_dir.join("lakefile.toml"),
            "name = \"dup_orig\"\ndefaultTargets = [\"DupTwo\"]\n[[lean_lib]]\nname = \"DupTwo\"\nprecompileModules = true\n[[lean_lib]]\nname = \"SameLib\"\nprecompileModules = true\n",
        )
        .unwrap();
        fs::write(dup2_dir.join("DupTwo.lean"), "def dupTwo : Nat := 102\n").unwrap();
        fs::write(
            dup2_dir.join("SameLib2.lean"),
            "def sameFromTwo : Nat := 202\n",
        )
        .unwrap();
        fs::write(
            dup2_dir.join("lakefile.toml"),
            "name = \"dup_orig\"\ndefaultTargets = [\"DupTwo\"]\n[[lean_lib]]\nname = \"DupTwo\"\nprecompileModules = true\n[[lean_lib]]\nname = \"SameLib\"\nroots = [\"SameLib2\"]\nprecompileModules = true\n",
        )
        .unwrap();

        // Root workspace manifest assigning `«dep-alias»`, `«dup-one»`, `«dup-two»` (serialized via Lean `Name` JSON)
        fs::write(
            ws.join("lake-manifest.json"),
            r#"{
  "version": "1.1.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {"type": "path", "scope": "", "name": "«dep-alias»", "inherited": false, "dir": "deps/dep_alias_dir", "configFile": "lakefile.toml"},
    {"type": "path", "scope": "", "name": "«dup-one»", "inherited": false, "dir": "deps/dup1_dir", "configFile": "lakefile.toml"},
    {"type": "path", "scope": "", "name": "«dup-two»", "inherited": false, "dir": "deps/dup2_dir", "configFile": "lakefile.toml"}
  ]
}
"#,
        )
        .unwrap();

        fs::write(
            ws.join("lakefile.toml"),
            r#"name = "ws-root"
defaultTargets = ["PiNone", "PiFalse", "PiTrue", "ModChain"]

[[require]]
name = "dep-alias"
path = "deps/dep_alias_dir"

[[require]]
name = "dup-one"
path = "deps/dup1_dir"

[[require]]
name = "dup-two"
path = "deps/dup2_dir"

[[lean_lib]]
name = "PiNone"

[[lean_lib]]
name = "PiFalse"
platformIndependent = false

[[lean_lib]]
name = "PiTrue"
platformIndependent = true

[[lean_lib]]
name = "ModChain"
globs = ["ModChain.+"]

[[lean_exe]]
name = "runner"
root = "Main"
"#,
        )
        .unwrap();

        fs::write(
            ws.join("PiNone.lean"),
            "import OrigLib\nimport DupOne\nimport DupTwo\nimport SameLib\nimport SameLib2\ndef piNone : Nat := origVal + dupOne + dupTwo + sameFromOne + sameFromTwo\n",
        )
        .unwrap();
        fs::write(
            ws.join("PiFalse.lean"),
            "import OrigLib\ndef piFalse : Nat := origVal + 2\n",
        )
        .unwrap();
        fs::write(
            ws.join("PiTrue.lean"),
            "import OrigLib\ndef piTrue : Nat := origVal + 3\n",
        )
        .unwrap();

        // Module system chain:
        // ModChain.Leaf is a `module` with a private def;
        // ModChain.Mid is a `module` (`public import ModChain.Leaf`, NOT `import all`);
        // ModChain.Top is a `module` with `import all ModChain.Mid` (`ModChain.Leaf` must NOT get `.olean.private`);
        // ModChain.Plain is a non-`module` importing `ModChain.Mid` (`nonModule := true` promotes both `Mid` and `Leaf` to `.olean.private`).
        fs::write(
            ws.join("ModChain/Leaf.lean"),
            "module\npublic def leafPub : Nat := 7\nprivate def leafPriv : Nat := 9\n",
        )
        .unwrap();
        fs::write(
            ws.join("ModChain/Mid.lean"),
            "module\npublic import ModChain.Leaf\npublic def midVal : Nat := leafPub\n",
        )
        .unwrap();
        fs::write(
            ws.join("ModChain/Top.lean"),
            "module\nimport all ModChain.Mid\npublic def topVal : Nat := midVal\n",
        )
        .unwrap();
        fs::write(
            ws.join("ModChain/Plain.lean"),
            "import ModChain.Mid\ndef plainVal : Nat := midVal\n",
        )
        .unwrap();
        fs::write(
            ws.join("Main.lean"),
            "import OrigLib\ndef main : IO Unit := IO.println s!\"{origVal}\"\n",
        )
        .unwrap();

        let cfg = resolve_project_config(&ws).unwrap();
        let lake_bin = cfg.lean_bin.with_file_name("lake");
        assert!(lake_bin.is_file(), "expected lake binary next to lean");

        // Verify CAS key distinguishes `platformIndependent` None vs Some(false) vs Some(true)
        let dag0 =
            build_module_dag(&cfg, &["PiNone".into(), "PiFalse".into(), "PiTrue".into()]).unwrap();
        assert_eq!(dag0.nodes["PiNone"].platform_independent, None);
        assert_eq!(dag0.nodes["PiFalse"].platform_independent, Some(false));
        assert_eq!(dag0.nodes["PiTrue"].platform_independent, Some(true));
        let mut fake_node = dag0.nodes["PiFalse"].clone();
        fake_node.expected_all_deps.clear();
        fake_node.direct_dag_deps.clear();
        fake_node.external_olean_deps.clear();
        let k_false = compute_module_cas_key(&cfg, &fake_node, &[], false).unwrap();
        fake_node.platform_independent = None;
        let k_none = compute_module_cas_key(&cfg, &fake_node, &[], false).unwrap();
        fake_node.platform_independent = Some(true);
        let k_true = compute_module_cas_key(&cfg, &fake_node, &[], false).unwrap();
        assert_ne!(k_none, k_false);
        assert_ne!(k_none, k_true);
        assert_ne!(k_false, k_true);

        // Verify CLI target resolution edge cases on `cfg`:
        // 1) `@`, `@/`, `@dep-alias`, `@dep-alias/`, `dep-alias/`, `@dep-alias/OrigLib`, `@dep-alias/+OrigLib.Sub`
        for ok_spec in [
            "@",
            "@/",
            "@dep-alias",
            "@dep-alias/",
            "dep-alias/",
            "@dep-alias/OrigLib",
            "@dep-alias/+OrigLib.Sub",
        ] {
            build_module_dag(&cfg, &[ok_spec.to_string()])
                .unwrap_or_else(|e| panic!("expected `{ok_spec}` to resolve cleanly: {e}"));
        }
        // 2) Rejections: `@+PiNone`, `@dep-alias:olean`, `dep-alias/:olean`, `+PiNone:olean:c`, `@dep-alias/OrigLib:olean:c`
        for bad_spec in [
            "@+PiNone",
            "@dep-alias:olean",
            "dep-alias/:olean",
            "ws-root:olean",
            "+PiNone:olean:c",
            "@dep-alias/OrigLib:olean:c",
        ] {
            assert!(
                build_module_dag(&cfg, &[bad_spec.to_string()]).is_err(),
                "expected `{bad_spec}` to be rejected like Lake"
            );
        }

        // Build default targets (`@`) + `:c` + `+Main:dynlib` via turbo-lean native module builder
        build_project_modules_native(
            &mut store,
            &ws,
            &[
                "PiNone:c".to_string(),
                "PiFalse:c".to_string(),
                "PiTrue:c".to_string(),
                "ModChain:c".to_string(),
                "+Main:dynlib".to_string(),
            ],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();

        // Capture turbo-lean outputs before running Lake
        let read_json = |p: &Path| -> serde_json::Value {
            serde_json::from_slice(
                &fs::read(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display())),
            )
            .unwrap()
        };
        let ours_pi_none_trace = read_json(&ws.join(".lake/build/lib/lean/PiNone.trace"));
        let ours_pi_false_trace = read_json(&ws.join(".lake/build/lib/lean/PiFalse.trace"));
        let ours_pi_true_trace = read_json(&ws.join(".lake/build/lib/lean/PiTrue.trace"));
        let ours_pi_true_setup = read_json(&ws.join(".lake/build/ir/PiTrue.setup.json"));
        let ours_orig_trace = read_json(&dep_alias_dir.join(".lake/build/lib/lean/OrigLib.trace"));
        let ours_top_setup = read_json(&ws.join(".lake/build/ir/ModChain/Top.setup.json"));
        let ours_top_trace = read_json(&ws.join(".lake/build/lib/lean/ModChain/Top.trace"));
        let ours_plain_setup = read_json(&ws.join(".lake/build/ir/ModChain/Plain.setup.json"));

        // Verify `PiTrue.setup.json` still includes precompiled `OrigLib` plugin/dynlib even though `PiTrue.trace` uses `nilLibTrace`
        assert!(
            !ours_pi_true_setup["plugins"].as_array().unwrap().is_empty()
                || !ours_pi_true_setup["dynlibs"].as_array().unwrap().is_empty(),
            "platformIndependent=true must still pass precompiled dynlibs/plugins in setup.json"
        );

        // Verify `lake build --no-build` succeeds across default targets, `@dep-alias`, and `+Main:dynlib`!
        let st_no_build = Command::new(&lake_bin)
            .args([
                "build",
                "@",
                "@dep-alias",
                "@dup-one",
                "@dup-two",
                "+Main:dynlib",
                "--no-build",
            ])
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .env("LAKE_CACHE_DIR", &lake_cache)
            .current_dir(&ws)
            .status()
            .unwrap();
        assert!(
            st_no_build.success(),
            "`lake build @ @dep-alias @dup-one @dup-two +Main:dynlib --no-build` must exit 0 on turbo-lean artifacts"
        );

        // Clean `.lake/build` in root and all deps, run real `lake build`, and compare `.trace` and `setup.json` bit-for-bit!
        for p in [&ws, &dep_alias_dir, &dup1_dir, &dup2_dir] {
            let _ = fs::remove_dir_all(p.join(".lake/build"));
        }
        let st_clean_lake = Command::new(&lake_bin)
            .args([
                "build",
                "@",
                "@dep-alias",
                "@dup-one",
                "@dup-two",
                "+Main:dynlib",
            ])
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .env("LAKE_CACHE_DIR", &lake_cache)
            .current_dir(&ws)
            .status()
            .unwrap();
        assert!(st_clean_lake.success(), "clean `lake build` must succeed");

        let lake_pi_none_trace = read_json(&ws.join(".lake/build/lib/lean/PiNone.trace"));
        let lake_pi_false_trace = read_json(&ws.join(".lake/build/lib/lean/PiFalse.trace"));
        let lake_pi_true_trace = read_json(&ws.join(".lake/build/lib/lean/PiTrue.trace"));
        let lake_orig_trace = read_json(&dep_alias_dir.join(".lake/build/lib/lean/OrigLib.trace"));
        let lake_top_setup = read_json(&ws.join(".lake/build/ir/ModChain/Top.setup.json"));
        let lake_top_trace = read_json(&ws.join(".lake/build/lib/lean/ModChain/Top.trace"));
        let lake_plain_setup = read_json(&ws.join(".lake/build/ir/ModChain/Plain.setup.json"));

        assert_eq!(
            ours_orig_trace["depHash"], lake_orig_trace["depHash"],
            "aliased package OrigLib depHash mismatch (baseName vs origName): ours={ours_orig_trace} lake={lake_orig_trace}"
        );
        assert_eq!(
            ours_pi_none_trace["depHash"], lake_pi_none_trace["depHash"],
            "PiNone depHash mismatch (unqualified lib.name dedup + dup origName deps): ours={ours_pi_none_trace} lake={lake_pi_none_trace}"
        );
        assert_eq!(
            ours_pi_false_trace["depHash"], lake_pi_false_trace["depHash"],
            "PiFalse (platformIndependent=false) depHash mismatch: ours={ours_pi_false_trace} lake={lake_pi_false_trace}"
        );
        assert_eq!(
            ours_pi_true_trace["depHash"], lake_pi_true_trace["depHash"],
            "PiTrue (platformIndependent=true) depHash mismatch: ours={ours_pi_true_trace} lake={lake_pi_true_trace}"
        );
        assert_eq!(
            ours_top_trace["depHash"], lake_top_trace["depHash"],
            "ModChain.Top depHash mismatch"
        );
        assert_eq!(
            ours_top_setup["importArts"], lake_top_setup["importArts"],
            "ModChain.Top setup.json importArts mismatch vs Lake fetchTransImportArts"
        );
        assert_eq!(
            ours_plain_setup["importArts"], lake_plain_setup["importArts"],
            "ModChain.Plain setup.json importArts mismatch vs Lake fetchTransImportArts"
        );

        // ------------------------------------------------------------------
        // Subcase B: CAS `:olean` (no `.c`) -> `:c` promotion and root-first
        // workspace target priority + empty `defaultTargets = []` on explicit `@pkg`.
        // ------------------------------------------------------------------
        let cas_proj = dir.join("cas_proj");
        let shadow_dep = cas_proj.join("deps/shadow_dep");
        fs::create_dir_all(&shadow_dep).unwrap();
        fs::write(
            cas_proj.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            shadow_dep.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )
        .unwrap();
        fs::write(
            shadow_dep.join("lakefile.toml"),
            "name = \"shadow_dep\"\ndefaultTargets = []\n[[lean_lib]]\nname = \"SharedTarget\"\nroots = [\"DepMod\"]\n",
        )
        .unwrap();
        fs::write(shadow_dep.join("DepMod.lean"), "def depOnly : Nat := 1\n").unwrap();
        fs::write(
            cas_proj.join("lake-manifest.json"),
            r#"{
  "version": "1.1.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {"type": "path", "scope": "", "name": "shadow_dep", "inherited": false, "dir": "deps/shadow_dep", "configFile": "lakefile.toml"}
  ]
}
"#,
        )
        .unwrap();
        fs::write(
            cas_proj.join("lakefile.toml"),
            "name = \"cas_proj\"\ndefaultTargets = [\"SharedTarget\"]\n[[require]]\nname = \"shadow_dep\"\npath = \"deps/shadow_dep\"\n[[lean_lib]]\nname = \"SharedTarget\"\nroots = [\"RootMod\"]\n",
        )
        .unwrap();
        fs::write(cas_proj.join("RootMod.lean"), "def rootOnly : Nat := 2\n").unwrap();

        let cas_cfg = resolve_project_config(&cas_proj).unwrap();
        // Bare `SharedTarget` must pick root package first (`RootMod`), matching `ws.packages` order!
        let st_dag = build_module_dag(&cas_cfg, &["SharedTarget".to_string()]).unwrap();
        assert!(st_dag.nodes.contains_key("RootMod"));
        assert!(!st_dag.nodes.contains_key("DepMod"));
        // Explicit `@shadow_dep` with `defaultTargets = []` builds 0 modules!
        let empty_pkg_dag = build_module_dag(&cas_cfg, &["@shadow_dep".to_string()]).unwrap();
        assert!(empty_pkg_dag.nodes.is_empty());

        // Build `RootMod:olean` first (populates CAS without `.c`), wipe `.lake/build`, then build `RootMod:c`
        build_project_modules_native(
            &mut store,
            &cas_proj,
            &["RootMod:olean".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert!(!cas_proj.join(".lake/build/ir/RootMod.c").exists());
        fs::remove_dir_all(cas_proj.join(".lake/build")).unwrap();
        build_project_modules_native(
            &mut store,
            &cas_proj,
            &["RootMod:c".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap();
        assert!(cas_proj.join(".lake/build/ir/RootMod.c").is_file());
        let st_cas_c = Command::new(&lake_bin)
            .args(["build", "+RootMod:c", "--no-build"])
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .env("LAKE_CACHE_DIR", &lake_cache)
            .current_dir(&cas_proj)
            .status()
            .unwrap();
        assert!(
            st_cas_c.success(),
            "`lake build +RootMod:c --no-build` must succeed"
        );

        // Worklist re-hit propagation: `RootMod` first enqueued via `+RootMod:olean` (`needs_c = false`),
        // then re-hit via `+RootMod:c` (`needs_c = true`), plus `native_unsupported` fail-closed on re-hit `:c.o.export`!
        let rehit_dag =
            build_module_dag(&cas_cfg, &["+RootMod:olean".into(), "+RootMod:c".into()]).unwrap();
        assert!(rehit_dag.nodes["RootMod"].needs_c);
        fs::write(
            cas_proj.join("lakefile.toml"),
            "name = \"cas_proj\"\nmoreLeancArgs = [\"-O3\"]\n[[lean_lib]]\nname = \"SharedTarget\"\nroots = [\"RootMod\"]\n",
        )
        .unwrap();
        let cas_cfg_unsup = resolve_project_config(&cas_proj).unwrap();
        assert!(
            build_module_dag(
                &cas_cfg_unsup,
                &["+RootMod:olean".into(), "+RootMod:c.o.export".into()]
            )
            .is_err(),
            "worklist re-hit promoting `needs_co_export` must enforce `native_unsupported` gate"
        );

        fs::write(
            cas_proj.join("lakefile.toml"),
            "name = \"cas_proj\"\n[[require]]\nname = \"shadow_dep\"\npath = \"deps/shadow_dep\"\n[[lean_lib]]\nname = \"SharedTarget\"\nroots = [\"RootMod\"]\n",
        )
        .unwrap();
        fs::write(
            shadow_dep.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage cas_proj\nextern_lib native_ext pkg := do\n  inputTextFile (pkg.dir / \"native.a\")\nlean_lib SharedTarget where\n  roots := #[`DepMod]\n",
        )
        .unwrap();
        fs::write(shadow_dep.join("native.a"), b"!<arch>\n").unwrap();
        let _ = fs::remove_file(shadow_dep.join("lakefile.toml"));
        fs::write(
            cas_proj.join("lake-manifest.json"),
            r#"{
  "version": "1.1.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {"type": "path", "scope": "", "name": "shadow_dep", "inherited": false, "dir": "deps/shadow_dep", "configFile": "lakefile.lean"}
  ]
}
"#,
        )
        .unwrap();
        let dup_ext_cfg = resolve_project_config(&cas_proj).unwrap();
        let dep_dag =
            build_module_dag(&dup_ext_cfg, &["@shadow_dep/+DepMod:dynlib".into()]).unwrap();
        let dep_node = &dep_dag.nodes["DepMod"];
        assert_eq!(dep_node.pkg_root, shadow_dep.canonicalize().unwrap());
        assert_eq!(
            native_link_package_roots(&dep_dag, &module_dynlib_so_path(dep_node).unwrap()).unwrap(),
            BTreeSet::from([dep_node.pkg_root.clone()])
        );
        let root_dag = build_module_dag(&dup_ext_cfg, &["+RootMod:dynlib".into()]).unwrap();
        let root_node = &root_dag.nodes["RootMod"];
        assert_eq!(
            native_link_package_roots(&root_dag, &module_dynlib_so_path(root_node).unwrap())
                .unwrap(),
            BTreeSet::from([root_node.pkg_root.clone()])
        );
        assert!(
            build_module_dag(&dup_ext_cfg, &["@shadow_dep/native_ext".into()])
                .unwrap()
                .nodes
                .is_empty()
        );

        let samelib_base = dir.join("samelib_proj");
        let samelib_dep = samelib_base.join("dep");
        let samelib_root = samelib_base.join("root");
        fs::create_dir_all(samelib_dep.join("Dep")).unwrap();
        fs::create_dir_all(samelib_root.join("App")).unwrap();
        for p in [&samelib_dep, &samelib_root] {
            fs::write(p.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }
        fs::write(
            samelib_dep.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"Foo\"\nprecompileModules = true\nroots = [\"Dep.Base\", \"Dep.Mid\"]\n",
        )
        .unwrap();
        fs::write(
            samelib_dep.join("Dep/Base.lean"),
            "def depVal : Nat := 41\n",
        )
        .unwrap();
        fs::write(
            samelib_dep.join("Dep/Mid.lean"),
            "import Dep.Base\ndef midVal : Nat := depVal + 1\n",
        )
        .unwrap();
        fs::write(
            samelib_root.join("lakefile.toml"),
            "name = \"root_pkg\"\n[[require]]\nname = \"dep_pkg\"\npath = \"../dep\"\n[[lean_lib]]\nname = \"Foo\"\nprecompileModules = true\nroots = [\"App.Main\"]\n",
        )
        .unwrap();
        fs::write(
            samelib_root.join("lake-manifest.json"),
            r#"{
  "version": "1.1.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {"type": "path", "scope": "", "name": "dep_pkg", "inherited": false, "dir": "../dep", "configFile": "lakefile.toml"}
  ]
}
"#,
        )
        .unwrap();
        fs::write(
            samelib_root.join("App/Main.lean"),
            "import Dep.Mid\ndef appVal : Nat := midVal + 1\n",
        )
        .unwrap();
        let samelib_summary = build_project_modules_native(
            &mut store,
            &samelib_root,
            &["Foo".into(), "Foo:shared".into()],
            "trusted-internal",
            2,
            false,
            true,
            None,
        )
        .unwrap();
        assert_eq!(samelib_summary.modules_total, 3);
        let samelib_no_build = Command::new(&lake_bin)
            .args(["build", "--no-build", "Foo", "Foo:shared"])
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .env("LAKE_CACHE_DIR", &lake_cache)
            .current_dir(&samelib_root)
            .output()
            .unwrap();
        assert!(
            samelib_no_build.status.success(),
            "`lake build --no-build Foo Foo:shared` failed on cross-package same-name `lean_lib`:\nstdout: {}\nstderr: {}",
            String::from_utf8_lossy(&samelib_no_build.stdout),
            String::from_utf8_lossy(&samelib_no_build.stderr)
        );
        let ours_samelib_main_trace: serde_json::Value = serde_json::from_slice(
            &fs::read(samelib_root.join(".lake/build/lib/lean/App/Main.trace")).unwrap(),
        )
        .unwrap();
        let ours_samelib_shared_trace: serde_json::Value = serde_json::from_slice(
            &fs::read(samelib_root.join(".lake/build/lib/libroot__pkg_Foo.so.trace")).unwrap(),
        )
        .unwrap();
        let _ = fs::remove_dir_all(samelib_dep.join(".lake/build"));
        let _ = fs::remove_dir_all(samelib_root.join(".lake/build"));
        let clean_samelib = Command::new(&lake_bin)
            .args(["build", "Foo", "Foo:shared"])
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .env("LAKE_CACHE_DIR", &lake_cache)
            .current_dir(&samelib_root)
            .status()
            .unwrap();
        assert!(clean_samelib.success());
        let lake_samelib_main_trace: serde_json::Value = serde_json::from_slice(
            &fs::read(samelib_root.join(".lake/build/lib/lean/App/Main.trace")).unwrap(),
        )
        .unwrap();
        let lake_samelib_shared_trace: serde_json::Value = serde_json::from_slice(
            &fs::read(samelib_root.join(".lake/build/lib/libroot__pkg_Foo.so.trace")).unwrap(),
        )
        .unwrap();
        assert_eq!(
            ours_samelib_main_trace["depHash"],
            lake_samelib_main_trace["depHash"]
        );
        assert_eq!(
            ours_samelib_shared_trace["depHash"],
            lake_samelib_shared_trace["depHash"]
        );

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_minimum_lean_toolchain_guidance() {
        for toolchain in [
            "leanprover/lean4:v4.24.0",
            "leanprover/lean4:v4.30.9",
            "v3.99.0",
        ] {
            let err =
                resolve_toolchain_compiler_with_roots(Path::new("/"), toolchain, true, Some(&[]))
                    .unwrap_err()
                    .to_string();
            assert!(err.contains(toolchain), "{err}");
            assert!(err.contains("requires Lean >= 4.31.0"), "{err}");
            assert!(err.contains("update lean-toolchain"), "{err}");
        }
    }

    #[test]
    fn test_lake_trace_toolchain_compatibility() -> Result<()> {
        let _env_guard = native_build_env_guard();
        for version in ["4.31.0", "4.33.1", "4.35.0"] {
            let toolchain = PathBuf::from(format!(
                "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v{version}"
            ));
            if !toolchain.join("bin/lake").is_file() {
                continue;
            }
            for platform in [
                "",
                "platformIndependent = true\n",
                "platformIndependent = false\n",
            ] {
                let dir = make_temp_test_dir("trace_toolchain_compatibility");
                fs::write(
                    dir.join("lean-toolchain"),
                    format!("leanprover/lean4:v{version}\n"),
                )?;
                fs::write(
                    dir.join("lakefile.toml"),
                    format!("name = \"probe\"\n[[lean_lib]]\nname = \"Probe\"\n{platform}"),
                )?;
                fs::create_dir_all(dir.join("Probe"))?;
                fs::write(
                    dir.join("Probe/Dep.lean"),
                    "module\npublic def dep : Nat := 1\n",
                )?;
                let src = "module\npublic import Probe.Dep\npublic def probe : Nat := dep\n";
                fs::write(dir.join("Probe.lean"), src)?;
                let output = Command::new(toolchain.join("bin/lake"))
                    .args(["build", "Probe"])
                    .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
                    .current_dir(&dir)
                    .output()?;
                anyhow::ensure!(
                    output.status.success(),
                    "{version}: {}{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
                let olean = dir.join(".lake/build/lib/lean/Probe.olean");
                let ir_dir = dir.join(".lake/build/ir");
                assert_eq!(olean_requires_ir_sig(&olean), version != "4.31.0");
                let mut raw: serde_json::Value =
                    serde_json::from_slice(&fs::read(olean.with_extension("trace"))?)?;
                assert_eq!(
                    raw["inputs"].as_array().unwrap().len(),
                    if version == "4.31.0" {
                        8
                    } else if platform.contains("false") {
                        10
                    } else {
                        9
                    }
                );
                verify_module_lake_sidecars(&olean, Some(&ir_dir), "Probe", src, true, true)?;
                assert!(verify_module_lake_sidecars(
                    &olean,
                    Some(&ir_dir),
                    "Probe",
                    "changed",
                    true,
                    true
                )
                .is_err());
                let (arts, meta, all) = compute_module_arts_traces(&olean, true, true)?;
                let hash = |p: &Path| verify_and_hash_artifact_bytes(p, true, true).unwrap();
                assert_eq!(arts, lake_mix_hash(1723, hash(&olean)));
                if version == "4.31.0" {
                    assert_eq!(meta, lake_mix_hash(arts, hash(&olean.with_extension("ir"))));
                    assert_eq!(
                        all,
                        lake_mix_hash(
                            lake_mix_hash(meta, hash(&olean.with_extension("olean.server"))),
                            hash(&olean.with_extension("olean.private"))
                        )
                    );
                }
                let cfg = resolve_project_config(&dir)?;
                if platform.contains("false") {
                    query_toolchain_native_spec(&cfg.lean_bin)?;
                }
                let spec = resolve_module_in_package(&cfg.root_pkg, true, "Probe").unwrap();
                assert!(lake_closure_export_info(
                    &cfg,
                    &spec,
                    false,
                    &mut LakeClosureCache::default(),
                    &mut HashSet::new()
                )
                .is_some());
                let dag = build_module_dag(&cfg, &["Probe".into()])?;
                let node = &dag.nodes["Probe"];
                let digest = compute_olean_artifact_set_digest(&olean)?;
                write_lake_module_hashes_and_trace(&cfg, &dag, node, &digest, Some(&digest), true)?;
                let written: serde_json::Value =
                    serde_json::from_slice(&fs::read(olean.with_extension("trace"))?)?;
                let src_idx = if version == "4.31.0" {
                    2
                } else if platform.contains("false") {
                    4
                } else {
                    3
                };
                raw["inputs"][src_idx][0] = written["inputs"][src_idx][0].clone();
                assert_eq!(written["inputs"], raw["inputs"]);
                assert_eq!(written["depHash"], raw["depHash"]);
                assert_eq!(written["outputs"], raw["outputs"]);
                verify_module_lake_sidecars(&olean, Some(&ir_dir), "Probe", src, true, true)?;
                if version != "4.31.0" {
                    fs::remove_file(olean.with_extension("ir.sig"))?;
                    assert!(compute_module_arts_traces(&olean, true, true).is_err());
                    assert!(verify_module_lake_sidecars(
                        &olean,
                        Some(&ir_dir),
                        "Probe",
                        src,
                        true,
                        true
                    )
                    .is_err());
                }
                fs::remove_dir_all(dir)?;
            }
        }
        Ok(())
    }

    #[test]
    fn test_direct_prebuilt_import_requires_valid_trace_and_hash_sidecars() {
        use crate::worktree_test_support::snapshot;

        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("direct_prebuilt_sidecars");
        let ext_dir = dir.join("ext_pkg");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(ext_dir.join("ExtLib")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        for d in [&ext_dir, &proj_dir] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }
        fs::write(
            ext_dir.join("lakefile.toml"),
            "name = \"ext_pkg\"\ndefaultTargets = [\"ExtLib\"]\n[[lean_lib]]\nname = \"ExtLib\"\nglobs = [\"ExtLib.+\"]\n",
        )
        .unwrap();
        fs::write(ext_dir.join("ExtLib/Base.lean"), "def extVal : Nat := 7\n").unwrap();
        let st = std::process::Command::new("lake")
            .args(["build", "ExtLib.Base"])
            .current_dir(&ext_dir)
            .status()
            .unwrap();
        assert!(st.success(), "`lake build ExtLib.Base` failed");

        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let use_file = proj_dir.join("App/Use.lean");
        let use_src = "import ExtLib.Base\ntheorem use_ok : extVal = 7 := rfl\n";
        fs::write(&use_file, use_src).unwrap();

        let ext_lib_lean = ext_dir.canonicalize().unwrap().join(".lake/build/lib/lean");
        let prev_lp = std::env::var_os("LEAN_PATH");
        std::env::set_var("LEAN_PATH", &ext_lib_lean);

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
            build_project_modules_native(
                &mut store,
                &proj_dir,
                &["App.Use".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();

            let canon = proj_dir.canonicalize().unwrap();
            let canon_use = use_file.canonicalize().unwrap();
            assert!(crate::lake_build::is_file_verified_in_lake_build(
                &canon, &canon_use, use_src
            ));
            assert_eq!(
                crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon,
                    std::slice::from_ref(&canon_use),
                )
                .unwrap(),
                0
            );

            let ext_trace = ext_lib_lean.join("ExtLib/Base.trace");
            let ext_hash = ext_lib_lean.join("ExtLib/Base.olean.hash");
            for (sidecar, label) in [
                (&ext_trace, "missing prebuilt .trace"),
                (&ext_hash, "missing prebuilt .olean.hash"),
            ] {
                let saved = fs::read(sidecar).unwrap();
                fs::remove_file(sidecar).unwrap();

                assert!(
                    !crate::lake_build::is_file_verified_in_lake_build(
                        &canon, &canon_use, use_src
                    ),
                    "{label}: `is_file_verified_in_lake_build` accepted prebuilt import without sidecar"
                );

                fs::write(
                    canon.join("turbo-lean.toml"),
                    "[worktree]\nauto_link = false\n",
                )
                .unwrap();
                let snap_proj = snapshot(&canon).unwrap();
                let snap_ext = snapshot(&ext_dir.canonicalize().unwrap()).unwrap();
                let opt_err = crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon,
                    std::slice::from_ref(&canon_use),
                )
                .unwrap_err()
                .to_string();
                assert!(
                    opt_err.contains("Worktree opt-out prevents refreshing stale imports")
                        && opt_err.contains("ExtLib.Base"),
                    "{label}: opt-out check missed stale direct prebuilt import: {opt_err}"
                );
                assert_eq!(
                    snapshot(&canon).unwrap(),
                    snap_proj,
                    "{label}: opt-out mutated root `.lake`"
                );
                assert_eq!(
                    snapshot(&ext_dir.canonicalize().unwrap()).unwrap(),
                    snap_ext,
                    "{label}: opt-out mutated external prebuilt `.lake`"
                );
                fs::remove_file(canon.join("turbo-lean.toml")).unwrap();

                assert!(
                    crate::lake_build::ensure_project_imports_fresh_for_check(
                        &canon,
                        std::slice::from_ref(&canon_use),
                    )
                    .is_err(),
                    "{label}: non-opt-out check accepted unbuildable prebuilt import without sidecar"
                );
                assert!(
                    build_project_modules_native(
                        &mut store,
                        &proj_dir,
                        &["App.Use".to_string()],
                        "trusted-internal",
                        1,
                        false,
                        true,
                        None,
                    )
                    .is_err(),
                    "{label}: `build_project_modules_native` accepted prebuilt import without sidecar"
                );

                fs::write(sidecar, saved).unwrap();
            }

            assert_eq!(
                crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon,
                    std::slice::from_ref(&canon_use),
                )
                .unwrap(),
                0
            );
            build_project_modules_native(
                &mut store,
                &proj_dir,
                &["App.Use".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            assert!(crate::lake_build::is_file_verified_in_lake_build(
                &canon, &canon_use, use_src
            ));
        }));

        match prev_lp {
            Some(v) => std::env::set_var("LEAN_PATH", v),
            None => std::env::remove_var("LEAN_PATH"),
        }
        let _ = fs::remove_dir_all(&dir);
        if let Err(e) = result {
            std::panic::resume_unwind(e);
        }
    }

    #[test]
    fn test_prebuilt_import_with_intact_sidecars_rejects_rebuilt_transitive_import() {
        use crate::worktree_test_support::snapshot;

        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("prebuilt_transitive_stale");
        let ext_dir = dir.join("ext_pkg");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(ext_dir.join("Ext")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        for d in [&ext_dir, &proj_dir] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }
        fs::write(
            ext_dir.join("lakefile.toml"),
            "name = \"ext_pkg\"\ndefaultTargets = [\"Ext\"]\n[[lean_lib]]\nname = \"Ext\"\nglobs = [\"Ext.+\"]\n",
        )
        .unwrap();
        fs::write(ext_dir.join("Ext/A.lean"), "def n : Nat := 1\n").unwrap();
        fs::write(
            ext_dir.join("Ext/B.lean"),
            "import Ext.A\ntheorem old : n = 1 := rfl\n",
        )
        .unwrap();
        let st = std::process::Command::new("lake")
            .args(["build", "Ext.B"])
            .current_dir(&ext_dir)
            .status()
            .unwrap();
        assert!(st.success(), "`lake build Ext.B` failed");

        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        let use_file = proj_dir.join("App/Use.lean");
        let use_src = "import Ext.B\ntheorem check_old : n = 1 := old\n";
        fs::write(&use_file, use_src).unwrap();

        let ext_lib_lean = ext_dir.canonicalize().unwrap().join(".lake/build/lib/lean");
        let prev_lp = std::env::var_os("LEAN_PATH");
        std::env::set_var("LEAN_PATH", &ext_lib_lean);

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
            build_project_modules_native(
                &mut store,
                &proj_dir,
                &["App.Use".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();

            let canon = proj_dir.canonicalize().unwrap();
            let canon_use = use_file.canonicalize().unwrap();
            assert!(crate::lake_build::is_file_verified_in_lake_build(
                &canon, &canon_use, use_src
            ));
            assert_eq!(
                crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon,
                    std::slice::from_ref(&canon_use),
                )
                .unwrap(),
                0
            );

            fs::write(ext_dir.join("Ext/A.lean"), "def n : Nat := 2\n").unwrap();
            let st_a = std::process::Command::new("lake")
                .args(["build", "Ext.A"])
                .current_dir(&ext_dir)
                .status()
                .unwrap();
            assert!(st_a.success(), "`lake build Ext.A` failed");
            assert!(ext_lib_lean.join("Ext/B.trace").is_file());
            assert!(ext_lib_lean.join("Ext/B.olean.hash").is_file());

            assert!(
                !crate::lake_build::is_file_verified_in_lake_build(&canon, &canon_use, use_src),
                "`is_file_verified_in_lake_build` accepted prebuilt `Ext.B` after `Ext.A` was rebuilt alone"
            );

            fs::write(
                canon.join("turbo-lean.toml"),
                "[worktree]\nauto_link = false\n",
            )
            .unwrap();
            let snap_proj = snapshot(&canon).unwrap();
            let snap_ext = snapshot(&ext_dir.canonicalize().unwrap()).unwrap();
            let opt_err = crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&canon_use),
            )
            .unwrap_err()
            .to_string();
            assert!(
                opt_err.contains("Worktree opt-out prevents refreshing stale imports")
                    && opt_err.contains("Ext.B"),
                "opt-out check missed stale transitive prebuilt import: {opt_err}"
            );
            assert_eq!(
                snapshot(&canon).unwrap(),
                snap_proj,
                "opt-out mutated root `.lake`"
            );
            assert_eq!(
                snapshot(&ext_dir.canonicalize().unwrap()).unwrap(),
                snap_ext,
                "opt-out mutated external prebuilt `.lake`"
            );
            fs::remove_file(canon.join("turbo-lean.toml")).unwrap();

            assert!(
                crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon,
                    std::slice::from_ref(&canon_use),
                )
                .is_err(),
                "non-opt-out check accepted prebuilt `Ext.B` against incompatible rebuilt `Ext.A`"
            );
            assert!(
                build_project_modules_native(
                    &mut store,
                    &proj_dir,
                    &["App.Use".to_string()],
                    "trusted-internal",
                    1,
                    false,
                    true,
                    None,
                )
                .is_err(),
                "`build_project_modules_native` accepted prebuilt `Ext.B` against incompatible rebuilt `Ext.A`"
            );

            fs::write(
                ext_dir.join("Ext/B.lean"),
                "import Ext.A\ntheorem old : n = 2 := rfl\n",
            )
            .unwrap();
            let st_b = std::process::Command::new("lake")
                .args(["build", "Ext.B"])
                .current_dir(&ext_dir)
                .status()
                .unwrap();
            assert!(
                st_b.success(),
                "`lake build Ext.B` after `Ext.A` update failed"
            );

            let updated_use_src = "import Ext.B\ntheorem check_old : n = 2 := old\n";
            fs::write(&use_file, updated_use_src).unwrap();
            assert_eq!(
                crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon,
                    std::slice::from_ref(&canon_use),
                )
                .unwrap(),
                0
            );
            build_project_modules_native(
                &mut store,
                &proj_dir,
                &["App.Use".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            assert!(crate::lake_build::is_file_verified_in_lake_build(
                &canon,
                &canon_use,
                updated_use_src
            ));

            fs::write(
                ext_dir.join("Ext/Z.lean"),
                "module\n@[expose] public def z : Nat := 1\n",
            )
            .unwrap();
            fs::write(
                ext_dir.join("Ext/Mid.lean"),
                "module\nimport Ext.Z\npublic theorem mid_ok : True := True.intro\nprivate theorem uses_z : z = 1 := rfl\n",
            )
            .unwrap();
            fs::write(
                ext_dir.join("Ext/Top.lean"),
                "module\npublic import Ext.Mid\npublic def top : Nat := 1\n",
            )
            .unwrap();
            let st_top = std::process::Command::new("lake")
                .args(["build", "Ext.Top"])
                .current_dir(&ext_dir)
                .status()
                .unwrap();
            assert!(st_top.success(), "`lake build Ext.Top` failed");

            let mod_use_src = "module\nimport Ext.Top\ndef useTop : Nat := top\n";
            fs::write(&use_file, mod_use_src).unwrap();
            assert_eq!(
                crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon,
                    std::slice::from_ref(&canon_use),
                )
                .unwrap(),
                0
            );
            build_project_modules_native(
                &mut store,
                &proj_dir,
                &["App.Use".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            assert!(crate::lake_build::is_file_verified_in_lake_build(
                &canon,
                &canon_use,
                mod_use_src
            ));

            fs::write(
                ext_dir.join("Ext/Z.lean"),
                "module\n@[expose] public def z : Nat := 9\n",
            )
            .unwrap();
            let st_z = std::process::Command::new("lake")
                .args(["build", "Ext.Z"])
                .current_dir(&ext_dir)
                .status()
                .unwrap();
            assert!(st_z.success(), "`lake build Ext.Z` failed");
            assert!(ext_lib_lean.join("Ext/Mid.trace").is_file());
            assert!(ext_lib_lean.join("Ext/Top.trace").is_file());

            assert!(
                !crate::lake_build::is_file_verified_in_lake_build(&canon, &canon_use, mod_use_src),
                "module-mode private transitive import `Ext.Z` rebuild must invalidate `Ext.Top`"
            );
            assert!(crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&canon_use),
            )
            .is_err());
            assert!(build_project_modules_native(
                &mut store,
                &proj_dir,
                &["App.Use".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .is_err());

            let lean_ns_dir = dir.join("lean_ns_pkg");
            fs::create_dir_all(lean_ns_dir.join("Lean")).unwrap();
            fs::write(
                lean_ns_dir.join("lean-toolchain"),
                "leanprover/lean4:v4.35.0\n",
            )
            .unwrap();
            fs::write(
                lean_ns_dir.join("lakefile.toml"),
                "name = \"lean_ns_pkg\"\ndefaultTargets = [\"LeanExternal\"]\n[[lean_lib]]\nname = \"LeanExternal\"\nroots = [\"Lean.ExternalA\", \"Lean.ExternalB\"]\n",
            )
            .unwrap();
            fs::write(
                lean_ns_dir.join("Lean/ExternalA.lean"),
                "def n : Nat := 1\n",
            )
            .unwrap();
            fs::write(
                lean_ns_dir.join("Lean/ExternalB.lean"),
                "import Lean.ExternalA\ntheorem old : n = 1 := rfl\n",
            )
            .unwrap();
            let st_lns = std::process::Command::new("lake")
                .args(["build", "Lean.ExternalB"])
                .current_dir(&lean_ns_dir)
                .status()
                .unwrap();
            assert!(st_lns.success(), "`lake build Lean.ExternalB` failed");

            let lean_ns_lib_lean = lean_ns_dir
                .canonicalize()
                .unwrap()
                .join(".lake/build/lib/lean");
            std::env::set_var("LEAN_PATH", &lean_ns_lib_lean);

            let lean_use_src = "import Lean.ExternalB\ntheorem accepted : n = 1 := old\n";
            fs::write(&use_file, lean_use_src).unwrap();
            build_project_modules_native(
                &mut store,
                &proj_dir,
                &["App.Use".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            let helper_file = proj_dir.join("App/Helper.lean");
            let helper_src = "import App.Use\ntheorem helper_ok : n = 1 := accepted\n";
            fs::write(&helper_file, helper_src).unwrap();
            build_project_modules_native(
                &mut store,
                &proj_dir,
                &["App.Helper".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            let canon_helper = helper_file.canonicalize().unwrap();
            assert!(crate::lake_build::is_file_verified_in_lake_build(
                &canon,
                &canon_helper,
                helper_src
            ));
            assert!(crate::lake_build::is_file_verified_in_lake_build(
                &canon,
                &canon_use,
                lean_use_src
            ));
            let _ = fs::remove_file(proj_dir.join(".lake/build/.turbo_verified_sources.json"));
            assert_eq!(
                crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon,
                    std::slice::from_ref(&canon_helper),
                )
                .unwrap(),
                0
            );
            let iface_before = crate::lake_build::compute_imported_olean_interface_hashes(
                lean_use_src,
                &canon,
                None,
            );
            assert!(
                iface_before
                    .iter()
                    .any(|e| e.starts_with("Lean.ExternalA:")),
                "expected `Lean.ExternalA` in imported interface hashes: {iface_before:?}"
            );

            fs::write(
                lean_ns_dir.join("Lean/ExternalA.lean"),
                "def n : Nat := 2\n",
            )
            .unwrap();
            let st_lns_a = std::process::Command::new("lake")
                .args(["build", "Lean.ExternalA"])
                .current_dir(&lean_ns_dir)
                .status()
                .unwrap();
            assert!(st_lns_a.success(), "`lake build Lean.ExternalA` failed");
            assert!(lean_ns_lib_lean.join("Lean/ExternalB.trace").is_file());
            assert!(lean_ns_lib_lean.join("Lean/ExternalB.olean.hash").is_file());

            let iface_after = crate::lake_build::compute_imported_olean_interface_hashes(
                lean_use_src,
                &canon,
                None,
            );
            assert_ne!(iface_before, iface_after);

            assert!(
                !crate::lake_build::is_file_verified_in_lake_build(&canon, &canon_use, lean_use_src),
                "`is_file_verified_in_lake_build` accepted stale `Lean.ExternalB` after `Lean.ExternalA` rebuild"
            );
            assert!(
                !crate::lake_build::is_file_verified_in_lake_build(
                    &canon,
                    &canon_helper,
                    helper_src
                ),
                "`is_file_verified_in_lake_build` accepted `App.Helper` over stale `Lean.ExternalB`"
            );
            assert!(
                crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon,
                    std::slice::from_ref(&canon_use),
                )
                .is_err(),
                "`ensure_project_imports_fresh_for_check` accepted stale `Lean.ExternalB`"
            );
            let _ = fs::remove_dir_all(proj_dir.join(".lake"));
            assert!(
                build_project_modules_native(
                    &mut store,
                    &proj_dir,
                    &["App.Use".to_string()],
                    "trusted-internal",
                    1,
                    false,
                    true,
                    None,
                )
                .is_err(),
                "`build_project_modules_native` treated `Lean.ExternalB` as built-in and accepted stale artifact"
            );
        }));

        match prev_lp {
            Some(v) => std::env::set_var("LEAN_PATH", v),
            None => std::env::remove_var("LEAN_PATH"),
        }
        let _ = fs::remove_dir_all(&dir);
        if let Err(e) = result {
            std::panic::resume_unwind(e);
        }
    }

    #[test]
    fn test_prebuilt_import_over_source_backed_dependency_closure_fresh_and_stale() {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("prebuilt_over_source_dep");
        let ext_dir = dir.join("toolchains").join("ext_pkg");
        let proj_dir = dir.join("proj");
        let dep_dir = proj_dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(ext_dir.join("Ext")).unwrap();
        fs::create_dir_all(dep_dir.join("Dep")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        for d in [&ext_dir, &dep_dir, &proj_dir] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\ndefaultTargets = [\"Dep\"]\n[[lean_lib]]\nname = \"Dep\"\nglobs = [\"Dep.+\"]\n",
        )
        .unwrap();
        fs::write(dep_dir.join("Dep/Base.lean"), "def baseVal : Nat := 7\n").unwrap();
        fs::write(
            dep_dir.join("Dep/Value.lean"),
            "import Dep.Base\ndef depVal : Nat := baseVal\n",
        )
        .unwrap();

        fs::write(
            ext_dir.join("lakefile.toml"),
            format!(
                "name = \"ext_pkg\"\ndefaultTargets = [\"Ext\"]\n[[require]]\nname = \"dep_pkg\"\npath = {:?}\n[[lean_lib]]\nname = \"Ext\"\nglobs = [\"Ext.+\"]\n",
                dep_dir.canonicalize().unwrap().to_string_lossy()
            ),
        )
        .unwrap();
        fs::write(
            ext_dir.join("Ext/Wrap.lean"),
            "import Dep.Value\ndef wrapVal : Nat := depVal\n",
        )
        .unwrap();

        let dep_lib_lean = dep_dir.canonicalize().unwrap().join(".lake/build/lib/lean");
        fs::write(
            ext_dir.join("lake-manifest.json"),
            format!(
                r#"{{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{{"type": "path", "name": "dep_pkg", "dir": {:?}, "configFile": "lakefile.toml", "inherited": false}}], "name": "ext_pkg", "lakeDir": ".lake", "fixedToolchain": false}}"#,
                dep_dir.canonicalize().unwrap().to_string_lossy()
            ),
        )
        .unwrap();
        let prev_lp = std::env::var_os("LEAN_PATH");

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            fs::write(
                proj_dir.join("lake-manifest.json"),
                r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep_pkg", "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml", "inherited": false}], "name": "app_pkg", "lakeDir": ".lake", "fixedToolchain": false}"#,
            )
            .unwrap();
            fs::write(
                proj_dir.join("lakefile.toml"),
                "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
            )
            .unwrap();
            let use_file = proj_dir.join("App/Use.lean");
            let use_src = "import Ext.Wrap\ntheorem wrap_ok : wrapVal = 7 := rfl\n";
            fs::write(&use_file, use_src).unwrap();

            let st_dep = std::process::Command::new("lake")
                .args(["build", "Dep.Value"])
                .current_dir(&dep_dir)
                .status()
                .unwrap();
            assert!(st_dep.success(), "`lake build Dep.Value` failed");
            let st_ext = std::process::Command::new("lake")
                .args(["build", "Ext.Wrap"])
                .current_dir(&ext_dir)
                .status()
                .unwrap();
            assert!(st_ext.success(), "`lake build Ext.Wrap` failed");

            let ext_lib_lean = ext_dir.canonicalize().unwrap().join(".lake/build/lib/lean");
            std::env::set_var("LEAN_PATH", &ext_lib_lean);

            let cfg = resolve_project_config_with_trust(&proj_dir, false).unwrap();
            let dag = build_module_dag_with_trust(&cfg, &["App.Use".to_string()], false).unwrap();
            let use_node = dag.nodes.get("App.Use").unwrap();
            let ext_names: Vec<&str> = use_node
                .external_olean_deps
                .iter()
                .map(|(m, _)| m.as_str())
                .collect();
            assert_eq!(ext_names, vec!["Dep.Base", "Dep.Value", "Ext.Wrap"]);

            let mut store = TurboStore::open(Some(&dir.join(".turbo_store"))).unwrap();
            let rep = build_project_modules_native(
                &mut store,
                &proj_dir,
                &["App.Use".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .unwrap();
            assert_eq!(rep.modules_compiled, 1);

            let canon = proj_dir.canonicalize().unwrap();
            let canon_use = use_file.canonicalize().unwrap();
            assert!(crate::lake_build::is_file_verified_in_lake_build(
                &canon, &canon_use, use_src
            ));
            assert_eq!(
                crate::lake_build::ensure_project_imports_fresh_for_check(
                    &canon,
                    std::slice::from_ref(&canon_use),
                )
                .unwrap(),
                0
            );
            let iface_before =
                crate::lake_build::compute_imported_olean_interface_hashes(use_src, &canon, None);
            assert!(iface_before.iter().any(|e| e.starts_with("Ext.Wrap:")));
            assert!(iface_before.iter().any(|e| e.starts_with("Dep.Value:")));
            assert!(iface_before.iter().any(|e| e.starts_with("Dep.Base:")));

            fs::write(dep_dir.join("Dep/Base.lean"), "def baseVal : Nat := 99\n").unwrap();
            let st_base = std::process::Command::new("lake")
                .args(["build", "Dep.Base"])
                .current_dir(&dep_dir)
                .status()
                .unwrap();
            assert!(st_base.success(), "`lake build Dep.Base` failed");
            assert!(ext_lib_lean.join("Ext/Wrap.trace").is_file());
            assert!(dep_lib_lean.join("Dep/Value.trace").is_file());

            let iface_after =
                crate::lake_build::compute_imported_olean_interface_hashes(use_src, &canon, None);
            assert_ne!(iface_before, iface_after);
            assert!(!crate::lake_build::is_file_verified_in_lake_build(
                &canon, &canon_use, use_src
            ));
            assert!(crate::lake_build::ensure_project_imports_fresh_for_check(
                &canon,
                std::slice::from_ref(&canon_use),
            )
            .is_err());
            assert!(build_project_modules_native(
                &mut store,
                &proj_dir,
                &["App.Use".to_string()],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )
            .is_err());
        }));

        match prev_lp {
            Some(v) => std::env::set_var("LEAN_PATH", v),
            None => std::env::remove_var("LEAN_PATH"),
        }
        let _ = fs::remove_dir_all(&dir);
        if let Err(e) = result {
            std::panic::resume_unwind(e);
        }
    }

    #[test]
    fn test_raw_sqlite_replay_row_and_checkout_local_store_never_suppress_kernel_replay(
    ) -> Result<()> {
        let _env_lock_guard = native_build_env_guard();
        let _env_guard = BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = make_temp_test_dir("replay_sqlite_mac_and_local_store");
        let toolchain = "leanprover/lean4:v4.35.0\n";
        let Ok((lean_bin, _, _, _)) = resolve_toolchain_compiler(&dir, toolchain.trim()) else {
            let _ = fs::remove_dir_all(&dir);
            return Ok(());
        };
        if !lean_bin.is_file() {
            let _ = fs::remove_dir_all(&dir);
            return Ok(());
        }
        let proj = dir.join("proj");
        let dep = proj.join(".lake/packages/dep");
        fs::create_dir_all(dep.join("Dep"))?;
        fs::create_dir_all(dep.join("Forge"))?;
        fs::write(proj.join("lean-toolchain"), toolchain)?;
        fs::write(dep.join("lean-toolchain"), toolchain)?;
        let forge_src = "import Lean\nopen Lean Elab Command\nelab \"forge_bad\" : command => do\n  let k := Name.mkStr (Name.mkStr .anonymous \"debug\") (\"skip\" ++ \"KernelTC\")\n  withScope (fun sc => { sc with opts := sc.opts.setBool k true }) do\n    liftCoreM <| addDecl <| .thmDecl {\n      name := `bad, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }\nforge_bad\n";
        fs::write(dep.join("Forge/Bad.lean"), forge_src)?;
        let bad_src = "theorem bad : False := True.intro\n";
        fs::write(dep.join("Dep/Bad.lean"), bad_src)?;
        fs::write(
            dep.join("lakefile.toml"),
            "name = \"dep\"\n[[lean_lib]]\nname = \"Dep\"\n[[lean_lib]]\nname = \"Forge\"\n",
        )?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"dep\"\npath = \".lake/packages/dep\"\n[[lean_lib]]\nname = \"App\"\n",
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep", "dir": ".lake/packages/dep", "configFile": "lakefile.toml", "inherited": false}], "name": "app", "lakeDir": ".lake", "fixedToolchain": false}"#,
        )?;
        fs::write(
            proj.join("App.lean"),
            "import Dep.Bad\ntheorem uses_bad : False := bad\n",
        )?;
        let lake_bin = lean_bin.parent().expect("lean bin parent").join("lake");
        let lake_out = Command::new(&lake_bin)
            .args(["build", "Forge.Bad"])
            .current_dir(&proj)
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .output()?;
        anyhow::ensure!(
            lake_out.status.success(),
            "lake build Forge.Bad: {}",
            String::from_utf8_lossy(&lake_out.stderr)
        );
        let forge_lib = dep.join(".lake/build/lib/lean/Forge");
        let dep_lib = dep.join(".lake/build/lib/lean/Dep");
        fs::create_dir_all(&dep_lib)?;
        fs::copy(forge_lib.join("Bad.olean"), dep_lib.join("Bad.olean"))?;
        fs::copy(forge_lib.join("Bad.ilean"), dep_lib.join("Bad.ilean"))?;
        let cfg = resolve_project_config(&proj)?;
        let dep_cfg = &cfg.dep_pkgs[0];
        let dep_olean = dep.join(".lake/build/lib/lean/Dep/Bad.olean");
        let ob = fs::read(&dep_olean)?;
        let ib = fs::read(dep_olean.with_extension("ilean"))?;
        let (oh, ih, sh) = (
            lake_hash_bytes(&ob),
            lake_hash_bytes(&ib),
            lake_hash_text(bad_src),
        );
        fs::write(
            format!("{}.hash", dep_olean.display()),
            format!("{oh:016x}"),
        )?;
        fs::write(
            format!("{}.hash", dep_olean.with_extension("ilean").display()),
            format!("{ih:016x}"),
        )?;
        let z = 0u64;
        let dh = lake_mix_hash(
            lake_mix_hash(lake_mix_hash(lake_mix_hash(LAKE_NIL_HASH, z), z), z),
            sh,
        );
        let tj = serde_json::json!({
            "schemaVersion": "2025-09-10",
            "depHash": format!("{dh:016x}"),
            "inputs": [["a", format!("{z:016x}")], ["b", format!("{z:016x}")], ["c", format!("{z:016x}")], ["src", format!("{sh:016x}")]],
            "outputs": serde_json::Value::Null,
        });
        fs::write(dep_olean.with_extension("trace"), serde_json::to_vec(&tj)?)?;
        let ws_inputs = workspace_lake_inputs_digest(&cfg)?;
        let forged_manifest = serde_json::json!({
            "pkg_name": dep_cfg.name,
            "toolchain": cfg.toolchain,
            "lean_githash": cfg.lean_githash,
            "pkg_config_digest": dep_cfg.config_digest,
            "lake_inputs_digest": &ws_inputs,
            "workspace_config_digest": cfg.canonical_config_digest,
            "allowed_axioms": crate::splitter::allowed_axioms(),
            "kernel_policy_digest": crate::splitter::current_kernel_policy_digest(),
            "modules": {
                "Dep/Bad.lean": {
                    "src_blake3": blake3::hash(bad_src.as_bytes()).to_hex().to_string(),
                    "olean_artifact_digest": compute_olean_artifact_set_digest(&dep_olean)?,
                    "lake_inputs_digest": &ws_inputs,
                    "kernel_audited": true,
                    "import_olean_digests": {},
                }
            }
        });
        fs::write(
            dep.join(".lake/build/.turbo_verified_sources.json"),
            serde_json::to_vec(&forged_manifest)?,
        )?;
        let (lp_env, _) = build_lean_search_path(&cfg, false);
        let art_dig = compute_replayed_olean_ilean_digest(&dep_olean)?;
        let env_dig = compute_olean_transitive_env_digest(&cfg, &lp_env, &dep_olean)?;

        // 1. External verifier store with raw SQLite row insertion into both `kernel_replayed_oleans`
        // and `kernel_replayed_oleans_auth` (forged MAC): `check` and `build` MUST still run
        // independent kernel replay and reject `Dep.Bad` (`KernelReplay`)!
        let mut ext_store = TurboStore::open(Some(&dir.join("external_cache")))?;
        ext_store.conn.execute(
            "INSERT INTO kernel_replayed_oleans (artifact_digest, replay_version, toolchain_hash, module_name, verified_at)
             VALUES (?1, ?2, ?3, 'Dep.Bad', 1)",
            rusqlite::params![
                &art_dig,
                i64::from(crate::zygote::ZYGOTE_REPLAY_VERSION),
                &cfg.lean_githash
            ],
        )?;
        ext_store.conn.execute(
            "INSERT INTO kernel_replayed_oleans_auth (artifact_digest, environment_digest, replay_version, toolchain_hash, module_name, replay_mac, verified_at)
             VALUES (?1, ?2, ?3, ?4, 'Dep.Bad', 'ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff', 1)",
            rusqlite::params![
                &art_dig,
                &env_dig,
                i64::from(crate::zygote::ZYGOTE_REPLAY_VERSION),
                &cfg.lean_githash
            ],
        )?;
        assert!(
            !is_olean_replayed_in_store(&ext_store, &cfg, &lp_env, &dep_olean),
            "unauthenticated SQLite row must never grant replay authority"
        );
        let check_err = crate::check::evaluate_check_command_value(
            &mut ext_store,
            proj.join("App.lean"),
            None,
            proj.clone(),
        )
        .unwrap_err();
        assert!(
            format!("{check_err:#}").contains("KernelReplay"),
            "raw SQLite row suppressed check kernel replay: {check_err:#}"
        );
        let build_err = build_project_modules_native(
            &mut ext_store,
            &proj,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )
        .unwrap_err();
        assert!(
            format!("{build_err:#}").contains("KernelReplay"),
            "raw SQLite row suppressed native build kernel replay: {build_err:#}"
        );

        // 2. Checkout-local store (`proj/.turbo-cache`): even if an attacker writes a valid 0600
        // `.verifier_replay_hmac_key` AND valid keyed MAC inside the checkout, checkout-local stores
        // are rejected as replay authority and kernel replay still executes and rejects `Dep.Bad`!
        let local_cache = proj.join(".turbo-cache");
        let mut local_store = TurboStore::open(Some(&local_cache))?;
        let attacker_key = [0x42u8; 32];
        let key_path = local_cache.join(".verifier_replay_hmac_key");
        fs::write(&key_path, attacker_key)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&key_path, fs::Permissions::from_mode(0o600))?;
        }
        let mut mac_msg = Vec::new();
        mac_msg.extend_from_slice(b"turbo-lean-verifier-replay-mac-v1\n");
        mac_msg.extend_from_slice(&(art_dig.len() as u64).to_le_bytes());
        mac_msg.extend_from_slice(art_dig.as_bytes());
        mac_msg.extend_from_slice(&(env_dig.len() as u64).to_le_bytes());
        mac_msg.extend_from_slice(env_dig.as_bytes());
        mac_msg.extend_from_slice(&crate::zygote::ZYGOTE_REPLAY_VERSION.to_le_bytes());
        mac_msg.extend_from_slice(&(cfg.lean_githash.len() as u64).to_le_bytes());
        mac_msg.extend_from_slice(cfg.lean_githash.as_bytes());
        let attacker_mac = blake3::keyed_hash(&attacker_key, &mac_msg)
            .to_hex()
            .to_string();
        local_store.conn.execute(
            "INSERT INTO kernel_replayed_oleans_auth (artifact_digest, environment_digest, replay_version, toolchain_hash, module_name, replay_mac, verified_at)
             VALUES (?1, ?2, ?3, ?4, 'Dep.Bad', ?5, 1)",
            rusqlite::params![
                &art_dig,
                &env_dig,
                i64::from(crate::zygote::ZYGOTE_REPLAY_VERSION),
                &cfg.lean_githash,
                &attacker_mac
            ],
        )?;
        assert!(
            !is_olean_replayed_in_store(&local_store, &cfg, &lp_env, &dep_olean),
            "checkout-local store must never be accepted as replay authority"
        );
        let local_check_err = crate::check::evaluate_check_command_value(
            &mut local_store,
            proj.join("App.lean"),
            None,
            proj.clone(),
        )
        .unwrap_err();
        assert!(
            format!("{local_check_err:#}").contains("KernelReplay"),
            "checkout-local store suppressed kernel replay: {local_check_err:#}"
        );

        // 3. Transitive import environment binding: if `Mid` imports `Base` (`def k : Nat := 1`)
        // and `Mid` is genuinely replayed & MAC-authenticated in `ext_store`, modifying `Base`'s
        // `.olean` on disk immediately invalidates `Mid`'s replay authority (`env_dig` changes)
        // even when `Mid.olean` bytes themselves are untouched!
        let env_proj = dir.join("env_proj");
        fs::create_dir_all(env_proj.join("Pkg"))?;
        fs::write(env_proj.join("lean-toolchain"), toolchain)?;
        fs::write(
            env_proj.join("lakefile.toml"),
            "name = \"env_proj\"\ndefaultTargets = [\"Pkg\"]\n[[lean_lib]]\nname = \"Pkg\"\nroots = [\"Pkg.Base\", \"Pkg.Mid\"]\n",
        )?;
        fs::write(env_proj.join("Pkg/Base.lean"), "def k : Nat := 1\n")?;
        fs::write(
            env_proj.join("Pkg/Mid.lean"),
            "import Pkg.Base\ntheorem mid_ok : k = 1 := rfl\n",
        )?;
        build_project_modules_native(
            &mut ext_store,
            &env_proj,
            &[],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )?;
        let env_cfg = resolve_project_config(&env_proj)?;
        let (env_lp, _) = build_lean_search_path(&env_cfg, false);
        let mid_olean = env_proj.join(".lake/build/lib/lean/Pkg/Mid.olean");
        let base_olean = env_proj.join(".lake/build/lib/lean/Pkg/Base.olean");
        assert!(
            is_olean_replayed_in_store(&ext_store, &env_cfg, &env_lp, &mid_olean),
            "freshly audited Mid.olean must hold authenticated replay authority under Base v1"
        );
        fs::write(env_proj.join("Pkg/Base.lean"), "def k : Nat := 2\n")?;
        let recompile_base = Command::new(&env_cfg.lean_bin)
            .arg("-R")
            .arg(&env_proj)
            .arg(env_proj.join("Pkg/Base.lean"))
            .arg("-o")
            .arg(&base_olean)
            .arg("-i")
            .arg(base_olean.with_extension("ilean"))
            .current_dir(&env_proj)
            .env("LEAN_PATH", &env_lp)
            .output()?;
        anyhow::ensure!(
            recompile_base.status.success(),
            "lean Base.lean v2: {}",
            String::from_utf8_lossy(&recompile_base.stderr)
        );
        assert!(
            !is_olean_replayed_in_store(&ext_store, &env_cfg, &env_lp, &mid_olean),
            "editing child Base.olean must invalidate parent Mid.olean replay authority"
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_prebuilt_dependency_checking_weakening_directive_and_missing_source_rejected(
    ) -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = make_temp_test_dir("dep_source_hygiene");
        let (proj, dep) = (dir.join("app"), dir.join("app/.lake/packages/dep"));
        fs::create_dir_all(dep.join("Dep"))?;
        let toolchain = include_str!("../../../lean/lean-toolchain");
        fs::write(proj.join("lean-toolchain"), toolchain)?;
        fs::write(dep.join("lean-toolchain"), toolchain)?;
        fs::write(
            dep.join("lakefile.toml"),
            "name = \"dep\"\n[[lean_lib]]\nname = \"Dep\"\n",
        )?;
        let dep_src = "set_option debug.skipKernelTC true\ntheorem ok : True := True.intro\n";
        fs::write(dep.join("Dep/Weak.lean"), dep_src)?;
        fs::write(
            proj.join("lake-manifest.json"),
            r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep", "dir": ".lake/packages/dep", "configFile": "lakefile.toml", "inherited": false}], "name": "app", "lakeDir": ".lake", "fixedToolchain": false}"#,
        )?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"dep\"\npath = \".lake/packages/dep\"\n[[lean_lib]]\nname = \"App\"\n",
        )?;
        fs::write(
            proj.join("App.lean"),
            "import Dep.Weak\ntheorem uses_ok : True := ok\n",
        )?;

        let cfg = resolve_project_config(&proj)?;
        let lake_bin = cfg.lean_bin.parent().expect("lean bin parent").join("lake");
        let lake_out = Command::new(&lake_bin)
            .args(["build", "App"])
            .current_dir(&proj)
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .output()?;
        anyhow::ensure!(
            lake_out.status.success(),
            "lake build App: {} {}",
            String::from_utf8_lossy(&lake_out.stdout),
            String::from_utf8_lossy(&lake_out.stderr)
        );

        let mut store = TurboStore::open(Some(&dir.join("cache")))?;

        // 1. `check` rejects importing a prebuilt dependency whose `.lean` source contains
        // `set_option debug.skipKernelTC true`, even though `ok : True := True.intro` kernel-replays cleanly.
        let check_err = crate::check::evaluate_check_command_value(
            &mut store,
            proj.join("App.lean"),
            None,
            proj.clone(),
        )
        .unwrap_err();
        let check_msg = format!("{check_err:#}");
        assert!(
            check_msg.contains("checking-weakening")
                || check_msg.contains("Soundness hygiene violation"),
            "check must reject prebuilt dependency checking-weakening directive: {check_msg}"
        );

        // 2. `ci-verify` rejects the prebuilt dependency as well.
        let ci_err = crate::pr_verify::run_ci_verify_command(
            &mut store,
            true,
            "trusted".to_string(),
            proj.clone(),
            None,
            None,
            false,
            None,
        )
        .unwrap_err();
        let ci_msg = format!("{ci_err:#}");
        assert!(
            ci_msg.contains("checking-weakening") || ci_msg.contains("Soundness hygiene violation"),
            "ci-verify must reject prebuilt dependency checking-weakening directive: {ci_msg}"
        );

        // 3. `pr-verify` rejects a PR whose dependency has `set_option debug.skipKernelTC true`.
        for args in [
            vec!["init"],
            vec!["config", "user.email", "test@example.com"],
            vec!["config", "user.name", "Test"],
            vec![
                "add",
                "lean-toolchain",
                "lakefile.toml",
                "lake-manifest.json",
                "App.lean",
            ],
            vec!["commit", "-m", "base"],
        ] {
            let g = Command::new("git")
                .args(&args)
                .current_dir(&proj)
                .output()?;
            anyhow::ensure!(
                g.status.success(),
                "git {:?}: {}",
                args,
                String::from_utf8_lossy(&g.stderr)
            );
        }
        fs::write(
            proj.join("App.lean"),
            "import Dep.Weak\ntheorem uses_ok : True := by exact ok\n",
        )?;
        let receipt_path = dir.join("pr_receipt.json");
        let pr_err = crate::pr_verify::run_pr_verify_command(
            &mut store,
            true,
            proj.clone(),
            "HEAD".to_string(),
            "trusted".to_string(),
            true,
            Some(receipt_path.clone()),
            None,
            None,
            None,
            false,
            2,
            None,
        )
        .unwrap_err();
        let pr_msg = format!("{pr_err:#}");
        assert!(
            pr_msg.contains("checking-weakening") || pr_msg.contains("Soundness hygiene violation"),
            "pr-verify must reject prebuilt dependency checking-weakening directive: {pr_msg}"
        );
        assert!(
            !receipt_path.exists(),
            "rejected pr-verify must emit no receipt"
        );

        // 4. Deleting `Dep/Weak.lean` while leaving `Dep/Weak.olean` in `.lake/packages/dep/.lake/build/lib/lean`
        // must also fail closed on both `check` and `pr-verify` due to missing package `.lean` source.
        fs::remove_file(dep.join("Dep/Weak.lean"))?;
        let missing_src_check = crate::check::evaluate_check_command_value(
            &mut store,
            proj.join("App.lean"),
            None,
            proj.clone(),
        )
        .unwrap_err();
        let missing_check_msg = format!("{missing_src_check:#}");
        assert!(
            missing_check_msg.contains("no resolvable `.lean` source"),
            "check must reject package `.olean` without `.lean` source: {missing_check_msg}"
        );
        let missing_src_pr = crate::pr_verify::run_pr_verify_command(
            &mut store,
            true,
            proj.clone(),
            "HEAD".to_string(),
            "trusted".to_string(),
            true,
            Some(receipt_path.clone()),
            None,
            None,
            None,
            false,
            2,
            None,
        )
        .unwrap_err();
        let missing_pr_msg = format!("{missing_src_pr:#}");
        assert!(
            missing_pr_msg.contains("no resolvable `.lean` source"),
            "pr-verify must reject package `.olean` without `.lean` source: {missing_pr_msg}"
        );
        assert!(!receipt_path.exists());

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_round9_external_dep_pruning_and_cross_pkg_same_lib_shared_local_modules() -> Result<()>
    {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("round9_ext_dep_and_cross_pkg_shared");

        // Subtest A (§1.B.1): Multi-hop prebuilt dependency (`App.Main -> Dep.Mid -> Dep.Base`)
        // with `root` `precompileModules = false`, `dep` `precompileModules = false`, promoted via
        // `App.Main:dynlib` (`explicit_dynlib_mods`), must NOT leave `Dep.Base` in both
        // `dag.nodes` and `App.Main.external_olean_deps`.
        let proj_a = dir.join("proj_a");
        let dep_a = proj_a.join(".lake/packages/dep_a");
        fs::create_dir_all(proj_a.join("App"))?;
        fs::create_dir_all(dep_a.join("Dep"))?;
        for d in [&proj_a, &dep_a] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        }
        fs::write(
            dep_a.join("lakefile.toml"),
            "name = \"dep_a\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"Dep.+\"]\n",
        )?;
        fs::write(dep_a.join("Dep/Base.lean"), "def baseVal : Nat := 10\n")?;
        fs::write(
            dep_a.join("Dep/Mid.lean"),
            "import Dep.Base\ndef midVal : Nat := baseVal + 1\n",
        )?;
        let st = Command::new("lake")
            .args(["build", "Dep.Mid"])
            .current_dir(&dep_a)
            .status()?;
        assert!(st.success(), "`lake build Dep.Mid` failed in dep_a");

        fs::write(
            proj_a.join("lakefile.toml"),
            "name = \"root_a\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )?;
        fs::write(
            proj_a.join("lake-manifest.json"),
            r#"{"version":"1.1.0","packagesDir":".lake/packages","packages":[{"type":"path","name":"dep_a","dir":".lake/packages/dep_a"}]}"#,
        )?;
        fs::write(
            proj_a.join("App/Helper.lean"),
            "import Dep.Mid\ndef helperVal : Nat := midVal\n",
        )?;
        fs::write(
            proj_a.join("App/Main.lean"),
            "import App.Helper\ndef mainVal : Nat := helperVal + 1\n",
        )?;

        let cfg_a = resolve_project_config(&proj_a)?;
        let dag_a = build_module_dag_with_trust(
            &cfg_a,
            &["App.Helper".to_string(), "App.Main:dynlib".to_string()],
            false,
        )?;
        assert!(
            dag_a.nodes.contains_key("Dep.Mid") && dag_a.nodes.contains_key("Dep.Base"),
            "Dep.Mid and Dep.Base must be promoted into dag.nodes for same-lib-name :dynlib"
        );
        for (mod_name, node) in &dag_a.nodes {
            for (ext_m, _) in &node.external_olean_deps {
                assert!(
                    !dag_a.nodes.contains_key(ext_m),
                    "node `{mod_name}` kept `{ext_m}` in external_olean_deps while `{ext_m}` is in dag.nodes"
                );
            }
        }

        // Subtest B (§1.B.2): `root_pkg` and `dep_pkg` both define non-precompiled `lean_lib Foo`.
        // `App.A` (`root_pkg` `Foo`) imports `Dep.Mid -> Dep.Base` (`dep_pkg` `Foo`, with fresh `.olean`s),
        // and `Bar` (`precompileModules = true`) imports `App.B` (`root_pkg` `Foo`), triggering `Foo:shared`
        // AFTER `App.A` is processed. Both `Dep.Mid` and `Dep.Base` must be promoted into `dag.nodes`
        // and included in `Foo:shared`'s `local_modules` (matching Lake's `LeanLib.recCollectLocalModules`).
        let proj_b = dir.join("proj_b");
        let dep_b = proj_b.join(".lake/packages/dep_b");
        fs::create_dir_all(proj_b.join("App"))?;
        fs::create_dir_all(proj_b.join("Bar"))?;
        fs::create_dir_all(dep_b.join("Dep"))?;
        for d in [&proj_b, &dep_b] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        }
        fs::write(
            dep_b.join("lakefile.toml"),
            "name = \"dep_b\"\ndefaultTargets = [\"Foo\"]\n[[lean_lib]]\nname = \"Foo\"\nglobs = [\"Dep.+\"]\n",
        )?;
        fs::write(dep_b.join("Dep/Base.lean"), "def depBase : Nat := 3\n")?;
        fs::write(
            dep_b.join("Dep/Mid.lean"),
            "import Dep.Base\ndef depMid : Nat := depBase + 4\n",
        )?;
        let st_b = Command::new("lake")
            .args(["build", "Dep.Mid"])
            .current_dir(&dep_b)
            .status()?;
        assert!(st_b.success(), "`lake build Dep.Mid` failed in dep_b");

        fs::write(
            proj_b.join("lakefile.toml"),
            concat!(
                "name = \"root_b\"\n",
                "defaultTargets = [\"Foo\", \"Bar\"]\n",
                "[[lean_lib]]\nname = \"Foo\"\nglobs = [\"App.+\"]\n",
                "[[lean_lib]]\nname = \"Bar\"\nglobs = [\"Bar.+\"]\nprecompileModules = true\n",
            ),
        )?;
        fs::write(
            proj_b.join("lake-manifest.json"),
            r#"{"version":"1.1.0","packagesDir":".lake/packages","packages":[{"type":"path","name":"dep_b","dir":".lake/packages/dep_b"}]}"#,
        )?;
        fs::write(
            proj_b.join("App/A.lean"),
            "import Dep.Mid\ndef appA : Nat := depMid\n",
        )?;
        fs::write(proj_b.join("App/B.lean"), "def appB : Nat := 1\n")?;
        fs::write(
            proj_b.join("Bar/Entry.lean"),
            "import App.B\ndef barEntry : Nat := appB\n",
        )?;

        let cfg_b = resolve_project_config(&proj_b)?;
        let dag_b = build_module_dag_with_trust(
            &cfg_b,
            &["App.A".to_string(), "Bar.Entry".to_string()],
            false,
        )?;
        assert!(
            dag_b.nodes.contains_key("Dep.Mid") && dag_b.nodes.contains_key("Dep.Base"),
            "Dep.Mid and Dep.Base must be promoted into dag.nodes when same-name Foo:shared is requested"
        );
        let foo_shared = dag_b
            .shared_libs
            .iter()
            .find(|sl| sl.lib_name == "Foo" && sl.pkg_root == cfg_b.root_pkg.pkg_root)
            .expect("root Foo:shared must be scheduled");
        assert!(
            foo_shared.local_modules.contains(&"Dep.Mid".to_string())
                && foo_shared.local_modules.contains(&"Dep.Base".to_string()),
            "root Foo:shared local_modules {:?} must include same-lib-name Dep.Mid and Dep.Base",
            foo_shared.local_modules
        );
        for (mod_name, node) in &dag_b.nodes {
            for (ext_m, _) in &node.external_olean_deps {
                assert!(
                    !dag_b.nodes.contains_key(ext_m),
                    "node `{mod_name}` kept `{ext_m}` in external_olean_deps while `{ext_m}` is in dag.nodes"
                );
            }
        }

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_round9_lake_cc_and_flags_rejects_in_checkout_compiler_and_accepts_system_cc(
    ) -> Result<()> {
        use std::os::unix::fs::PermissionsExt;

        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("round9_trusted_cc");
        let proj = dir.join("proj");
        let dep = proj.join(".lake/packages/dep");
        fs::create_dir_all(proj.join("App"))?;
        fs::create_dir_all(dep.join("Dep"))?;
        for d in [&proj, &dep] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        }
        fs::write(
            dep.join("lakefile.toml"),
            "name = \"dep\"\ndefaultTargets = [\"Dep\"]\n[[lean_lib]]\nname = \"Dep\"\nglobs = [\"Dep.+\"]\n",
        )?;
        fs::write(dep.join("Dep/A.lean"), "def d : Nat := 1\n")?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"proj\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            r#"{"version":"1.1.0","packagesDir":".lake/packages","packages":[{"type":"path","name":"dep","dir":".lake/packages/dep"}]}"#,
        )?;
        fs::write(
            proj.join("App/Main.lean"),
            "@[export turbo_r9_fn]\ndef r9Fn (x : UInt32) : UInt32 := x + 1\n",
        )?;

        let evil_root_cc = proj.join("evil_cc.sh");
        fs::write(&evil_root_cc, "#!/bin/sh\nexit 0\n")?;
        fs::set_permissions(&evil_root_cc, fs::Permissions::from_mode(0o755))?;
        let evil_dep_cc = dep.join("evil_dep_cc.sh");
        fs::write(&evil_dep_cc, "#!/bin/sh\nexit 0\n")?;
        fs::set_permissions(&evil_dep_cc, fs::Permissions::from_mode(0o755))?;

        let cfg = resolve_project_config(&proj)?;
        let prev_lean_cc = std::env::var_os("LEAN_CC");
        let prev_cc = std::env::var_os("CC");
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> Result<()> {
            std::env::set_var("LEAN_CC", &evil_root_cc);
            let err_root = lake_cc_and_flags(&cfg).unwrap_err();
            assert!(
                format!("{err_root:#}").contains("inside a project/checkout"),
                "in-root LEAN_CC must be rejected: {err_root:#}"
            );

            std::env::set_var("LEAN_CC", &evil_dep_cc);
            let err_dep = lake_cc_and_flags(&cfg).unwrap_err();
            assert!(
                format!("{err_dep:#}").contains("inside a project/checkout"),
                "in-dep LEAN_CC must be rejected: {err_dep:#}"
            );

            std::env::set_var("LEAN_CC", "cc");
            let err_rel = lake_cc_and_flags(&cfg).unwrap_err();
            assert!(
                format!("{err_rel:#}").contains("must be absolute"),
                "bare relative LEAN_CC must be rejected: {err_rel:#}"
            );

            if Path::new("/usr/bin/cc").is_file() {
                std::env::set_var("LEAN_CC", "/usr/bin/cc");
                let (resolved_cc, _, _, _, custom_cc) = lake_cc_and_flags(&cfg)?;
                assert!(custom_cc);
                assert!(resolved_cc.is_absolute());
                let tag_usr = custom_cc_env_digest_tag();
                std::env::remove_var("LEAN_CC");
                std::env::remove_var("CC");
                let tag_default = custom_cc_env_digest_tag();
                assert_ne!(
                    tag_usr, tag_default,
                    "custom_cc_env_digest_tag must distinguish LEAN_CC override from default"
                );
            }
            Ok(())
        }));
        match prev_lean_cc {
            Some(v) => std::env::set_var("LEAN_CC", v),
            None => std::env::remove_var("LEAN_CC"),
        }
        match prev_cc {
            Some(v) => std::env::set_var("CC", v),
            None => std::env::remove_var("CC"),
        }
        let _ = fs::remove_dir_all(&dir);
        match res {
            Ok(inner) => inner,
            Err(p) => std::panic::resume_unwind(p),
        }
    }

    #[cfg(unix)]
    #[test]
    fn test_round9_module_full_cas_stages_native_artifacts_and_detects_missing_c_and_co_export(
    ) -> Result<()> {
        let _env_guard = native_build_env_guard();
        if !Path::new("/usr/bin/cc").is_file() {
            return Ok(());
        }
        let dir = make_temp_test_dir("round9_module_full_native");
        let store_dir = dir.join("store");
        let proj1 = dir.join("proj1");
        let dep1 = proj1.join(".lake/packages/dep");
        fs::create_dir_all(proj1.join("App"))?;
        fs::create_dir_all(dep1.join("Dep"))?;
        for d in [&proj1, &dep1] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        }
        fs::write(
            dep1.join("lakefile.toml"),
            "name = \"dep\"\ndefaultTargets = [\"Dep\"]\n[[lean_lib]]\nname = \"Dep\"\nglobs = [\"Dep.+\"]\n",
        )?;
        fs::write(
            dep1.join("Dep/Exported.lean"),
            "@[export turbo_dep_r9_add]\ndef depAdd (x : UInt32) : UInt32 := x + 2\n",
        )?;
        fs::write(
            proj1.join("lakefile.toml"),
            "name = \"app\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )?;
        fs::write(
            proj1.join("lake-manifest.json"),
            r#"{"version":"1.1.0","packagesDir":".lake/packages","packages":[{"type":"path","name":"dep","dir":".lake/packages/dep"}]}"#,
        )?;
        fs::write(
            proj1.join("App/Main.lean"),
            "import Dep.Exported\n@[export turbo_app_r9_use]\ndef appUse (x : UInt32) : UInt32 := depAdd x\n",
        )?;

        let prev_lean_cc = std::env::var_os("LEAN_CC");
        let prev_emit_c = std::env::var_os("TURBO_LEAN_EMIT_C");
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> Result<()> {
            std::env::set_var("LEAN_CC", "/usr/bin/cc");
            std::env::remove_var("TURBO_LEAN_EMIT_C");

            let target_facets = vec![
                "App.Main:c.o.export".to_string(),
                "Dep.Exported:c.o.export".to_string(),
            ];
            let mut store = TurboStore::open(Some(&store_dir))?;
            crate::lake_build::run_build_command(
                &mut store,
                true,
                target_facets.clone(),
                proj1.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;

            let app_co = proj1.join(".lake/build/ir/App/Main.c.o.export");
            let app_co_trace = proj1.join(".lake/build/ir/App/Main.c.o.export.trace");
            let dep_co = dep1.join(".lake/build/ir/Dep/Exported.c.o.export");
            let dep_co_trace = dep1.join(".lake/build/ir/Dep/Exported.c.o.export.trace");
            assert!(
                app_co.is_file() && app_co_trace.is_file(),
                "root :c.o.export module must build .c.o.export + .trace"
            );
            assert!(
                dep_co.is_file() && dep_co_trace.is_file(),
                "in-tree dep :c.o.export module must build .c.o.export + .trace"
            );

            // Clone sources into a clean worktree `proj2` and hit `module_full` CAS:
            // both root `.lake/build` and `.lake/packages/dep/.lake/build` native `.c.o.export`
            // artifacts must be restored!
            let proj2 = dir.join("proj2");
            let dep2 = proj2.join(".lake/packages/dep");
            fs::create_dir_all(proj2.join("App"))?;
            fs::create_dir_all(dep2.join("Dep"))?;
            for (src_d, dst_d) in [(&proj1, &proj2), (&dep1, &dep2)] {
                for rel in ["lean-toolchain", "lakefile.toml"] {
                    fs::copy(src_d.join(rel), dst_d.join(rel))?;
                }
            }
            fs::copy(
                proj1.join("lake-manifest.json"),
                proj2.join("lake-manifest.json"),
            )?;
            fs::copy(proj1.join("App/Main.lean"), proj2.join("App/Main.lean"))?;
            fs::copy(
                dep1.join("Dep/Exported.lean"),
                dep2.join("Dep/Exported.lean"),
            )?;

            crate::lake_build::run_build_command(
                &mut store,
                true,
                target_facets.clone(),
                proj2.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;
            let proj2_co = proj2.join(".lake/build/ir/App/Main.c.o.export");
            let dep2_co = dep2.join(".lake/build/ir/Dep/Exported.c.o.export");
            assert!(
                proj2_co.is_file() && verify_native_facet_sidecar(&proj2_co).is_ok(),
                "module_full CacheHit must restore root .c.o.export and valid sidecars"
            );
            assert!(
                dep2_co.is_file() && verify_native_facet_sidecar(&dep2_co).is_ok(),
                "module_full CacheHit must restore in-tree dep .c.o.export and valid sidecars"
            );

            // Also verify `are_all_project_oleans_up_to_date` on a default-target `precompileModules`
            // / `:c.o.export` check: deleting `.c.o.export` when `defaultFacets = ["leanArts", "oExport"]`
            // or rebuilding `target_facets` on a fresh store must NOT skip rebuilding `.c.o.export`!
            fs::remove_file(&proj2_co)?;
            let mut fresh_store = TurboStore::open(Some(&dir.join("store2")))?;
            crate::lake_build::run_build_command(
                &mut fresh_store,
                true,
                target_facets,
                proj2.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;
            assert!(
                proj2_co.is_file() && verify_native_facet_sidecar(&proj2_co).is_ok(),
                "build must not skip native rebuild when .c.o.export is missing"
            );

            // Toggling `TURBO_LEAN_EMIT_C=1` on a non-export module must change `module_full` key
            // AND invalidate `are_all_project_oleans_up_to_date` when `.c` was not previously emitted.
            let proj3 = dir.join("proj3");
            fs::create_dir_all(proj3.join("Plain"))?;
            fs::write(proj3.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
            fs::write(
                proj3.join("lakefile.toml"),
                "name = \"plain\"\ndefaultTargets = [\"Plain\"]\n[[lean_lib]]\nname = \"Plain\"\nglobs = [\"Plain.+\"]\n",
            )?;
            fs::write(
                proj3.join("Plain/Basic.lean"),
                "theorem t : True := trivial\n",
            )?;

            std::env::remove_var("TURBO_LEAN_EMIT_C");
            crate::lake_build::run_build_command(
                &mut store,
                true,
                vec![],
                proj3.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;
            let plain_c = proj3.join(".lake/build/ir/Plain/Basic.c");
            assert!(
                !plain_c.exists(),
                "Plain/Basic.c should not exist when EMIT_C is unset"
            );

            std::env::set_var("TURBO_LEAN_EMIT_C", "1");
            crate::lake_build::run_build_command(
                &mut store,
                true,
                vec![],
                proj3.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;
            assert!(
                plain_c.is_file(),
                "setting TURBO_LEAN_EMIT_C=1 must miss prior module_full entry and emit Plain/Basic.c"
            );

            // Deleting `Plain/Basic.c` while `TURBO_LEAN_EMIT_C=1` and running `run_build_command`
            // with `targets = []` on a fresh store must NOT treat `.olean`s as up-to-date:
            // `are_all_project_oleans_up_to_date` must detect missing `.c` and rebuild!
            fs::remove_file(&plain_c)?;
            let mut store3 = TurboStore::open(Some(&dir.join("store3")))?;
            crate::lake_build::run_build_command(
                &mut store3,
                true,
                vec![],
                proj3.clone(),
                "trusted".to_string(),
                0,
                false,
            )?;
            assert!(
                plain_c.is_file(),
                "are_all_project_oleans_up_to_date must reject missing .c when TURBO_LEAN_EMIT_C=1"
            );

            // And when `precompileModules = true` on `Plain`, `are_all_project_oleans_up_to_date`
            // (`verify_project_native_and_c_sidecars_up_to_date`) must return false if `.c.o.export`
            // or module dynlib `.so` is missing!
            fs::write(
                proj3.join("lakefile.toml"),
                "name = \"plain\"\ndefaultTargets = [\"Plain\"]\n[[lean_lib]]\nname = \"Plain\"\nglobs = [\"Plain.+\"]\nprecompileModules = true\n",
            )?;
            let cfg3 = resolve_project_config(&proj3)?;
            assert!(
                !verify_project_native_and_c_sidecars_up_to_date(&cfg3, &[]),
                "verify_project_native_and_c_sidecars_up_to_date must be false when precompileModules artifacts are missing"
            );

            Ok(())
        }));
        match prev_lean_cc {
            Some(v) => std::env::set_var("LEAN_CC", v),
            None => std::env::remove_var("LEAN_CC"),
        }
        match prev_emit_c {
            Some(v) => std::env::set_var("TURBO_LEAN_EMIT_C", v),
            None => std::env::remove_var("TURBO_LEAN_EMIT_C"),
        }
        let _ = fs::remove_dir_all(&dir);
        match res {
            Ok(inner) => inner,
            Err(p) => std::panic::resume_unwind(p),
        }
    }

    #[test]
    fn test_warm_on_disk_olean_reuse_and_githash_gate() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("warm_olean_reuse");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("Warm"))?;
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"warm_pkg\"\ndefaultTargets = [\"Warm\"]\n[[lean_lib]]\nname = \"Warm\"\nglobs = [\"Warm.+\"]\n",
        )?;
        fs::write(
            proj_dir.join("Warm/Base.lean"),
            "namespace Warm\ndef baseVal : Nat := 11\nend Warm\n",
        )?;
        fs::write(
            proj_dir.join("Warm/Top.lean"),
            "import Warm.Base\nnamespace Warm\ntheorem top_eq : baseVal + 4 = 15 := rfl\nend Warm\n",
        )?;

        let out = Command::new("lake")
            .arg("build")
            .env("LEAN_NUM_THREADS", "2")
            .current_dir(&proj_dir)
            .output()?;
        anyhow::ensure!(
            out.status.success(),
            "lake build failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        let base_olean = proj_dir.join(".lake/build/lib/lean/Warm/Base.olean");
        let top_olean = proj_dir.join(".lake/build/lib/lean/Warm/Top.olean");
        assert!(base_olean.is_file() && top_olean.is_file());

        // 1. Positive test: fresh TurboStore adopts Lake-built `.olean`s without recompiling
        //    and ingests them into per-module CAS.
        let mut store1 = TurboStore::open(Some(&dir.join("store1")))?;
        let rep1 = build_project_modules_native(
            &mut store1,
            &proj_dir,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        assert_eq!(rep1.modules_total, 2);
        assert_eq!(rep1.modules_compiled, 0);
        assert_eq!(rep1.modules_cached, 0);
        assert_eq!(rep1.modules_up_to_date_reused, 2);

        // Verify CAS ingestion: deleting `.lake/build` and rebuilding hits per-module CAS!
        fs::remove_dir_all(proj_dir.join(".lake/build"))?;
        let rep_cas = build_project_modules_native(
            &mut store1,
            &proj_dir,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        assert_eq!(rep_cas.modules_compiled, 0);
        assert_eq!(rep_cas.modules_cached, 2);
        assert_eq!(rep_cas.modules_up_to_date_reused, 0);

        // 2. CLI `run_seed_oleans_command` smoke test on a fresh store with warm `.olean`s:
        let mut store_seed = TurboStore::open(Some(&dir.join("store_seed")))?;
        run_seed_oleans_command(
            &mut store_seed,
            true,
            proj_dir.clone(),
            vec!["Warm".to_string()],
            1,
        )?;
        fs::remove_dir_all(proj_dir.join(".lake/build"))?;
        let rep_after_seed = build_project_modules_native(
            &mut store_seed,
            &proj_dir,
            &["Warm".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        assert_eq!(rep_after_seed.modules_compiled, 0);
        assert_eq!(rep_after_seed.modules_cached, 2);

        // 3. Negative test: mutating the `.olean` v2 header githash (`hdr[40..80]`) to a
        //    mismatched 40-char githash forces recompilation on a fresh TurboStore.
        let out2 = Command::new("lake")
            .arg("build")
            .env("LEAN_NUM_THREADS", "2")
            .current_dir(&proj_dir)
            .output()?;
        anyhow::ensure!(
            out2.status.success(),
            "second lake build failed: {}",
            String::from_utf8_lossy(&out2.stderr)
        );
        let mut tampered_base = fs::read(&base_olean)?;
        assert!(
            tampered_base.len() >= 80 && &tampered_base[0..5] == b"olean" && tampered_base[5] == 2
        );
        tampered_base[40..80].copy_from_slice(b"0000000000000000000000000000000000000000");
        fs::write(&base_olean, &tampered_base)?;
        let _ = fs::remove_file(proj_dir.join(".lake/build/.turbo_verified_sources.json"));

        let mut store2 = TurboStore::open(Some(&dir.join("store2")))?;
        let rep_bad_hdr = build_project_modules_native(
            &mut store2,
            &proj_dir,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        assert!(
            rep_bad_hdr.modules_compiled >= 1,
            "mismatched olean header githash must force recompilation, got {:?}",
            rep_bad_hdr
        );
        assert!(
            rep_bad_hdr
                .compiled_modules
                .contains(&"Warm.Base".to_string()),
            "Warm.Base with tampered githash must recompile: {:?}",
            rep_bad_hdr.compiled_modules
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_target_cone_scoping_skips_unrelated_libs_and_module_full_cas() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("target_cone_scoping");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("LibA"))?;
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        // Declare two libraries: `LibA` (present) and `LibB` whose `LibB.+` directory does not
        // exist unless walked, plus later a broken `LibB/Broken.lean` that would fail `split_lean_source`
        // or compilation if `LibB` were eagerly walked or compiled.
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"two_libs\"\ndefaultTargets = [\"LibA\", \"LibB\"]\n[[lean_lib]]\nname = \"LibA\"\nglobs = [\"LibA.+\"]\n[[lean_lib]]\nname = \"LibB\"\nglobs = [\"LibB.+\"]\n",
        )?;
        fs::write(
            proj_dir.join("LibA/Core.lean"),
            "namespace LibA\ndef val : Nat := 42\ntheorem val_eq : val = 42 := rfl\nend LibA\n",
        )?;

        // 1. Even before `LibB/` exists on disk (which would fail `expand_lib_configured_modules`
        //    if `LibB.+` were walked), `build_module_dag_with_trust(..., &["LibA"], ...)` and
        //    `run_build_command(..., vec!["LibA"])` succeed and build only `LibA.Core`.
        let cfg = resolve_project_config(&proj_dir)?;
        let dag_a = build_module_dag_with_trust(&cfg, &["LibA".to_string()], false)?;
        assert_eq!(
            dag_a.nodes.keys().cloned().collect::<Vec<_>>(),
            vec!["LibA.Core".to_string()]
        );

        // Now populate `LibB/Broken.lean` with an invalid Lean proof/header that must never be
        // compiled or walked when building target `LibA`.
        fs::create_dir_all(proj_dir.join("LibB"))?;
        fs::write(
            proj_dir.join("LibB/Broken.lean"),
            "import NonExistent.Module\ndef broken : Nat := \"type_mismatch\"\n",
        )?;

        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        crate::lake_build::run_build_command(
            &mut store,
            true,
            vec!["LibA".to_string()],
            proj_dir.clone(),
            "trusted".to_string(),
            1,
            true,
        )?;
        assert!(
            proj_dir
                .join(".lake/build/lib/lean/LibA/Core.olean")
                .is_file(),
            "LibA.Core.olean must be built"
        );
        assert!(
            !proj_dir
                .join(".lake/build/lib/lean/LibB/Broken.olean")
                .exists(),
            "LibB.Broken.olean must never be built when targeting LibA"
        );
        let module_full_count: i64 = store.conn.query_row(
            "SELECT COUNT(*) FROM actions WHERE kind = 'module_full'",
            [],
            |r| r.get(0),
        )?;
        assert_eq!(
            module_full_count, 0,
            "target-scoped build must publish zero `module_full` actions"
        );
        let module_unit_count: i64 = store.conn.query_row(
            "SELECT COUNT(*) FROM actions WHERE kind = 'module_unit'",
            [],
            |r| r.get(0),
        )?;
        assert_eq!(
            module_unit_count, 1,
            "target-scoped build must populate `module_unit` CAS for LibA.Core"
        );

        // 2. Clean `.lake/build` into a fresh worktree `proj2` (still keeping broken `LibB/Broken.lean`)
        //    and verify `run_build_command(..., vec!["LibA"])` restores `LibA.Core` from `module_unit` CAS
        //    without touching `LibB` or publishing `module_full`.
        let proj2 = dir.join("proj2");
        fs::create_dir_all(proj2.join("LibA"))?;
        fs::create_dir_all(proj2.join("LibB"))?;
        for rel in [
            "lean-toolchain",
            "lakefile.toml",
            "LibA/Core.lean",
            "LibB/Broken.lean",
        ] {
            fs::copy(proj_dir.join(rel), proj2.join(rel))?;
        }
        crate::lake_build::run_build_command(
            &mut store,
            true,
            vec!["LibA".to_string()],
            proj2.clone(),
            "trusted".to_string(),
            1,
            false,
        )?;
        assert!(
            proj2.join(".lake/build/lib/lean/LibA/Core.olean").is_file(),
            "proj2 LibA.Core.olean must be restored from module_unit CAS"
        );
        let module_full_count_after: i64 = store.conn.query_row(
            "SELECT COUNT(*) FROM actions WHERE kind = 'module_full'",
            [],
            |r| r.get(0),
        )?;
        assert_eq!(module_full_count_after, 0);

        // 3. Whole-repo build (`targets = []`) once `LibB/Broken.lean` is fixed still publishes `module_full`.
        fs::write(
            proj_dir.join("LibB/Broken.lean"),
            "namespace LibB\ndef okVal : Nat := 7\nend LibB\n",
        )?;
        crate::lake_build::run_build_command(
            &mut store,
            true,
            Vec::new(),
            proj_dir.clone(),
            "trusted".to_string(),
            1,
            false,
        )?;
        let module_full_whole: i64 = store.conn.query_row(
            "SELECT COUNT(*) FROM actions WHERE kind = 'module_full'",
            [],
            |r| r.get(0),
        )?;
        assert_eq!(
            module_full_whole, 1,
            "whole-repo build (`targets = []`) must still publish `module_full`"
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_seed_verified_fresh_modules_handles_stock_lake_nil_c_trace_and_prebuilt_deps(
    ) -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_seed_nil_c_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos()
        ));
        let dep_dir = dir.join("dep_pkg");
        let src_proj = dir.join("src_proj");
        let dst_proj = dir.join("dst_proj");
        fs::create_dir_all(dep_dir.join("Dep"))?;
        fs::create_dir_all(src_proj.join("Root"))?;
        fs::create_dir_all(dst_proj.join("Root"))?;

        let tc_str = fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .and_then(|p| p.parent())
                .unwrap_or_else(|| Path::new("."))
                .join("lean/lean-toolchain"),
        )
        .unwrap_or_else(|_| "leanprover/lean4:v4.24.0\n".to_string());

        fs::write(dep_dir.join("lean-toolchain"), &tc_str)?;
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\ndefaultTargets = [\"Dep\"]\n[[lean_lib]]\nname = \"Dep\"\nglobs = [\"Dep.+\"]\n",
        )?;
        fs::write(dep_dir.join("Dep/Val.lean"), "def depBase : Nat := 10\n")?;

        let lake_status = std::process::Command::new("lake")
            .arg("build")
            .current_dir(&dep_dir)
            .status()?;
        assert!(lake_status.success(), "stock lake build of dep_pkg failed");
        let _ = fs::remove_file(dep_dir.join(".lake/build/.turbo_verified_sources.json"));

        for p in [&src_proj, &dst_proj] {
            fs::write(p.join("lean-toolchain"), &tc_str)?;
            fs::write(
                p.join("lakefile.toml"),
                "name = \"root_pkg\"\ndefaultTargets = [\"Root\"]\n[[require]]\nname = \"dep_pkg\"\npath = \"../dep_pkg\"\n[[lean_lib]]\nname = \"Root\"\nglobs = [\"Root.+\"]\n",
            )?;
            fs::create_dir_all(p.join(".lake"))?;
            #[cfg(unix)]
            {
                let _ = std::os::unix::fs::symlink(&dep_dir, p.join(".lake/packages_dep"));
            }
            fs::write(
                p.join("lake-manifest.json"),
                serde_json::json!({
                    "version": "1.1.0",
                    "packagesDir": ".lake",
                    "packages": [{
                        "type": "path",
                        "scope": "",
                        "name": "dep_pkg",
                        "manifestFile": "lake-manifest.json",
                        "inherited": false,
                        "dir": "../dep_pkg",
                        "configFile": "lakefile.toml"
                    }]
                })
                .to_string(),
            )?;
            fs::write(
                p.join("Root/Base.lean"),
                "import Dep.Val\ndef rootBase : Nat := depBase + 1\n",
            )?;
            fs::write(
                p.join("Root/Top.lean"),
                "import Root.Base\ntheorem top_eq : rootBase = 11 := rfl\n",
            )?;
        }

        let root_status = std::process::Command::new("lake")
            .arg("build")
            .current_dir(&src_proj)
            .status()?;
        assert!(root_status.success(), "stock lake build of src_proj failed");

        let base_trace_path = src_proj.join(".lake/build/lib/lean/Root/Base.trace");
        let base_c_path = src_proj.join(".lake/build/ir/Root/Base.c");
        if base_c_path.is_file() && base_trace_path.is_file() {
            let mut tv: serde_json::Value = serde_json::from_slice(&fs::read(&base_trace_path)?)?;
            if let Some(outs) = tv.get_mut("outputs").and_then(|v| v.as_object_mut()) {
                outs.insert(
                    "c".to_string(),
                    serde_json::Value::String(format!("{LAKE_NIL_HASH:016x}.c")),
                );
                fs::write(&base_trace_path, serde_json::to_vec_pretty(&tv)?)?;
            }
        }
        let unverified_base_c = src_proj.join(".lake/build/ir/Root/Base.c");
        if let Some(p) = unverified_base_c.parent() {
            fs::create_dir_all(p)?;
        }
        fs::write(&unverified_base_c, "// unverified stale C artifact\n")?;

        // Edit only `Root/Top.lean` in `dst_proj`; `Root/Base` must still verify and seed cleanly!
        fs::write(
            dst_proj.join("Root/Top.lean"),
            "import Root.Base\ntheorem top_eq : rootBase = 11 := by\n  have _h : True := trivial\n  exact rfl\n",
        )?;

        let src_cfg = resolve_project_config_with_trust(&src_proj, false)?;
        let targets = vec!["Root".to_string()];
        let trusted_dag = build_module_dag_for_trusted_statement(&src_cfg, &targets)?;
        assert!(
            !trusted_dag.nodes.contains_key("Dep.Val"),
            "prebuilt dep_pkg without .turbo_verified_sources.json must stay in external_olean_deps for trusted statement DAG"
        );
        let strict_dag = build_module_dag_with_trust(&src_cfg, &targets, false)?;
        assert!(
            strict_dag.nodes.contains_key("Dep.Val"),
            "strict build_module_dag_with_trust must still include unmanifested dep_pkg in DAG"
        );

        let before_src_base_nlink = {
            #[cfg(unix)]
            {
                use std::os::unix::fs::MetadataExt;
                fs::metadata(src_proj.join(".lake/build/lib/lean/Root/Base.olean"))?.nlink()
            }
            #[cfg(not(unix))]
            {
                1u64
            }
        };

        seed_verified_fresh_modules_into_disposable_snapshot(&src_cfg, &dst_proj, &targets)?;

        assert!(
            dst_proj
                .join(".lake/build/lib/lean/Root/Base.olean")
                .is_file(),
            "fresh upstream Root.Base must be seeded into dst_proj even with Lake NIL_HASH outputs.c"
        );
        assert!(
            !dst_proj.join(".lake/build/ir/Root/Base.c").exists(),
            "unverified .c sidecar must NOT be copied when !node.needs_c"
        );
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            assert_eq!(
                fs::metadata(src_proj.join(".lake/build/lib/lean/Root/Base.olean"))?.nlink(),
                before_src_base_nlink,
                "seeding disposable snapshot must copy regular files without mutating src st_nlink/ctime"
            );
        }

        let dst_cfg = resolve_project_config_with_trust(&dst_proj, false)?;
        let dst_dag = build_module_dag_for_trusted_statement(&dst_cfg, &targets)?;
        let dirty =
            find_dirty_modules_in_otherwise_fresh_dag(&dst_cfg, &dst_dag, 16, &HashSet::new())
                .expect("find_dirty_modules_in_otherwise_fresh_dag should return dirty set");
        assert_eq!(
            dirty,
            vec!["Root.Top".to_string()],
            "only edited Root.Top should be dirty after seeding"
        );
        compile_disposable_snapshot_dirty_modules_direct(&dst_cfg, &dst_dag, &dirty)?;
        assert!(dst_proj
            .join(".lake/build/lib/lean/Root/Top.olean")
            .is_file());

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_prebuilt_dep_pkg_closure_rejects_stale_transitive_macro_import() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_prebuilt_dep_stale_trans_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos()
        ));
        let dep_dir = dir.join("dep_pkg");
        let root_dir = dir.join("root_pkg");
        fs::create_dir_all(dep_dir.join("Dep"))?;
        fs::create_dir_all(root_dir.join("Root"))?;

        let tc_str = fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .and_then(|p| p.parent())
                .unwrap_or_else(|| Path::new("."))
                .join("lean/lean-toolchain"),
        )
        .unwrap_or_else(|_| "leanprover/lean4:v4.24.0\n".to_string());

        fs::write(dep_dir.join("lean-toolchain"), &tc_str)?;
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\ndefaultTargets = [\"Dep\"]\n[[lean_lib]]\nname = \"Dep\"\nglobs = [\"Dep.+\"]\n",
        )?;
        fs::write(
            dep_dir.join("Dep/A.lean"),
            "macro \"depMacroTy\" : term => `(Nat)\n",
        )?;
        fs::write(
            dep_dir.join("Dep/B.lean"),
            "import Dep.A\ntheorem dep_witness : Nonempty depMacroTy := ⟨default⟩\n",
        )?;

        let dep_status = std::process::Command::new("lake")
            .arg("build")
            .current_dir(&dep_dir)
            .status()?;
        assert!(dep_status.success(), "initial lake build of dep_pkg failed");
        let _ = fs::remove_file(dep_dir.join(".lake/build/.turbo_verified_sources.json"));

        fs::write(root_dir.join("lean-toolchain"), &tc_str)?;
        fs::write(
            root_dir.join("lakefile.toml"),
            "name = \"root_pkg\"\ndefaultTargets = [\"Root\"]\n[[require]]\nname = \"dep_pkg\"\npath = \"../dep_pkg\"\n[[lean_lib]]\nname = \"Root\"\nglobs = [\"Root.+\"]\n",
        )?;
        fs::create_dir_all(root_dir.join(".lake"))?;
        fs::write(
            root_dir.join("lake-manifest.json"),
            serde_json::json!({
                "version": "1.1.0",
                "packagesDir": ".lake",
                "packages": [{
                    "type": "path",
                    "scope": "",
                    "name": "dep_pkg",
                    "manifestFile": "lake-manifest.json",
                    "inherited": false,
                    "dir": "../dep_pkg",
                    "configFile": "lakefile.toml"
                }]
            })
            .to_string(),
        )?;
        fs::write(
            root_dir.join("Root/Main.lean"),
            "import Dep.B\ntheorem root_ok : Nonempty Nat := dep_witness\n",
        )?;

        let targets = vec!["Root".to_string()];
        let fresh_cfg = resolve_project_config_with_trust(&root_dir, false)?;
        let fresh_dag = build_module_dag_for_trusted_statement(&fresh_cfg, &targets)?;
        assert!(
            !fresh_dag.nodes.contains_key("Dep.B") && !fresh_dag.nodes.contains_key("Dep.A"),
            "fresh unmanifested dep_pkg closure should stay in external_olean_deps"
        );

        fs::write(
            dep_dir.join("Dep/A.lean"),
            "macro \"depMacroTy\" : term => `(Bool)\n",
        )?;
        let dep_a_status = std::process::Command::new("lake")
            .args(["build", "Dep.A"])
            .current_dir(&dep_dir)
            .status()?;
        assert!(dep_a_status.success(), "selective lake build Dep.A failed");
        let _ = fs::remove_file(dep_dir.join(".lake/build/.turbo_verified_sources.json"));

        let stale_cfg = resolve_project_config_with_trust(&root_dir, false)?;
        let stale_dag = build_module_dag_for_trusted_statement(&stale_cfg, &targets)?;
        assert!(
            stale_dag.nodes.contains_key("Dep.B"),
            "stale Dep.B whose recorded import hash no longer matches rebuilt Dep.A must not be accepted as prebuilt external_olean_deps"
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
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
            if let Some(ref p) = self.prev {
                std::env::set_var(self.key, p);
            } else {
                std::env::remove_var(self.key);
            }
        }
    }

    struct ScopedSchedulerTrace {
        _active: (),
    }

    impl ScopedSchedulerTrace {
        fn start(hook: Option<std::sync::Arc<NativeSchedulerTestHook>>) -> Self {
            let ev_lock = TEST_NATIVE_SCHEDULER_EVENTS.get_or_init(|| Mutex::new(None));
            if let Ok(mut g) = ev_lock.lock() {
                *g = Some(Vec::new());
            }
            let hk_lock = TEST_NATIVE_SCHEDULER_HOOK.get_or_init(|| Mutex::new(None));
            if let Ok(mut g) = hk_lock.lock() {
                *g = hook;
            }
            Self { _active: () }
        }

        fn take_events(&self) -> Vec<NativeSchedulerTestEvent> {
            let mut out = Vec::new();
            if let Some(lock) = TEST_NATIVE_SCHEDULER_EVENTS.get() {
                if let Ok(mut g) = lock.lock() {
                    if let Some(ref mut v) = *g {
                        std::mem::swap(&mut out, v);
                    }
                }
            }
            out
        }
    }

    impl Drop for ScopedSchedulerTrace {
        fn drop(&mut self) {
            if let Some(lock) = TEST_NATIVE_SCHEDULER_HOOK.get() {
                if let Ok(mut g) = lock.lock() {
                    *g = None;
                }
            }
            if let Some(lock) = TEST_NATIVE_SCHEDULER_EVENTS.get() {
                if let Ok(mut g) = lock.lock() {
                    *g = None;
                }
            }
        }
    }

    /// Speed-2 (1): Ready-queue prioritizes higher `b_level` critical-path modules over
    /// lexicographically earlier leaf modules in the same initial wave, using cached
    /// `actions.duration_ms` when present and source-byte fallback otherwise.
    #[test]
    fn test_speed2_critical_path_priority_over_wave_ready_set() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let _jobs = ScopedEnvVar::set("TURBO_LEAN_JOBS", "1");
        let dir = make_temp_test_dir("speed2_b_level_prio");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("App"))?;
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"prio\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )?;
        // Wave 0 has `App.ALeaf` (lexicographically first, short leaf) and `App.ZRoot`
        // (lexicographically last, root of chain `App.ZRoot -> App.ZMid -> App.ZTop`).
        fs::write(proj_dir.join("App/ALeaf.lean"), "def aLeaf : Nat := 1\n")?;
        fs::write(proj_dir.join("App/ZRoot.lean"), "def zRoot : Nat := 2\n")?;
        fs::write(
            proj_dir.join("App/ZMid.lean"),
            "import App.ZRoot\ndef zMid : Nat := zRoot + 1\n",
        )?;
        fs::write(
            proj_dir.join("App/ZTop.lean"),
            "import App.ZMid\ndef zTop : Nat := zMid + 1\n",
        )?;

        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        let trace = ScopedSchedulerTrace::start(None);
        let rep = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let events = trace.take_events();
        assert_eq!(rep.modules_compiled, 4);
        assert_eq!(rep.waves_count, 3);
        let dispatches: Vec<String> = events
            .iter()
            .filter(|e| e.kind == "compile_dispatch")
            .flat_map(|e| e.modules.clone())
            .collect();
        // Source-byte fallback gives `App.ZRoot` (`w(ZRoot)+w(ZMid)+w(ZTop)`) higher `b_level`
        // than leaf `App.ALeaf`, so `App.ZRoot` dispatches before `App.ALeaf` despite `A < Z`.
        assert_eq!(
            dispatches.first().map(String::as_str),
            Some("App.ZRoot"),
            "critical-path root App.ZRoot must dispatch before wave-0 leaf App.ALeaf: {dispatches:?}"
        );

        // Now boost `App.ALeaf`'s cached `duration_ms` in `actions` (then delete its cached action
        // row? No: keep `duration_ms` on `App.ALeaf`? Wait: if `App.ALeaf` is in CAS it hits CAS!
        // Instead, test `compute_module_b_levels` directly with cached `duration_ms`, AND test
        // rebuilding when `App.ZTop` has a huge cached `duration_ms` vs a second 2-node chain).
        store.conn.execute(
            "UPDATE actions SET duration_ms = 500000 WHERE kind = 'module_unit'",
            [],
        )?;
        let cfg = resolve_project_config(&proj_dir)?;
        let dag = build_module_dag_with_trust(&cfg, &[], false)?;
        let (_, dependents) = compute_dag_schedule_edges(&dag.nodes, &dag.shared_libs);
        let b_levels = compute_module_b_levels(
            &store,
            &cfg,
            &dag,
            &HashSet::new(),
            &dependents,
            "trusted",
            false,
            &HashMap::new(),
        );
        assert!(
            b_levels["App.ZRoot"] >= 1_500_000 && b_levels["App.ALeaf"] >= 500_000,
            "cached duration_ms must feed b_level weights: {b_levels:?}"
        );
        assert!(b_levels["App.ZRoot"] > b_levels["App.ZMid"]);
        assert!(b_levels["App.ZMid"] > b_levels["App.ZTop"]);

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    /// Speed-2 (2): A downstream module starts compiling as soon as its own dependencies are
    /// accepted, without waiting for an unrelated slow module in its dependency's old wave.
    #[test]
    fn test_speed2_dependent_starts_before_unrelated_wave_peer_finishes() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let _jobs = ScopedEnvVar::set("TURBO_LEAN_JOBS", "2");
        let dir = make_temp_test_dir("speed2_no_wave_barrier");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("Fast"))?;
        fs::create_dir_all(proj_dir.join("Slow"))?;
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"nobarrier\"\ndefaultTargets = [\"Fast\", \"Slow\"]\n[[lean_lib]]\nname = \"Fast\"\nglobs = [\"Fast.+\"]\n[[lean_lib]]\nname = \"Slow\"\nglobs = [\"Slow.+\"]\n",
        )?;
        fs::write(
            proj_dir.join("Fast/Base.lean"),
            "def fastBase : Nat := 10\n",
        )?;
        fs::write(
            proj_dir.join("Fast/Child.lean"),
            "import Fast.Base\ndef fastChild : Nat := fastBase + 1\n",
        )?;
        // Pad Slow/Peer.lean with comments so its initial b_level keeps both roots active on 2 workers,
        // and use the scheduler test hook to hold `Slow.Peer`'s compile until `Fast.Child` starts!
        let slow_src = format!("-- {}\ndef slowPeer : Nat := 99\n", "x".repeat(512));
        fs::write(proj_dir.join("Slow/Peer.lean"), slow_src)?;

        let pair = std::sync::Arc::new((Mutex::new(false), std::sync::Condvar::new()));
        let pair_hook = std::sync::Arc::clone(&pair);
        let hook: std::sync::Arc<NativeSchedulerTestHook> =
            std::sync::Arc::new(move |kind: &str, mods: &[String]| {
                if kind == "compile_subprocess_start" && mods.iter().any(|m| m == "Fast.Child") {
                    let (lk, cv) = &*pair_hook;
                    if let Ok(mut started) = lk.lock() {
                        *started = true;
                        cv.notify_all();
                    }
                }
                if kind == "compile_subprocess_end" && mods.iter().any(|m| m == "Slow.Peer") {
                    let (lk, cv) = &*pair_hook;
                    if let Ok(guard) = lk.lock() {
                        let _ = cv.wait_timeout_while(
                            guard,
                            std::time::Duration::from_secs(30),
                            |started| !*started,
                        );
                    }
                }
            });

        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        let trace = ScopedSchedulerTrace::start(Some(hook));
        let rep = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let events = trace.take_events();
        assert_eq!(rep.modules_compiled, 3);
        let fast_child_start = events
            .iter()
            .find(|e| e.kind == "compile_subprocess_start" && e.modules == ["Fast.Child"])
            .expect("Fast.Child compile_subprocess_start")
            .at_ns;
        let slow_peer_end = events
            .iter()
            .find(|e| e.kind == "compile_subprocess_end" && e.modules == ["Slow.Peer"])
            .expect("Slow.Peer compile_subprocess_end")
            .at_ns;
        assert!(
            fast_child_start <= slow_peer_end,
            "Fast.Child (wave 1) must start compiling before wave-0 peer Slow.Peer finishes ({fast_child_start} vs {slow_peer_end})"
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    /// Speed-2 (3): `precompileModules` module dynlibs and library shared objects are built
    /// incrementally and exist on disk before any downstream dependent starts compiling.
    #[test]
    fn test_speed2_dynlib_and_shared_lib_ready_before_dependents_compile() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let _jobs = ScopedEnvVar::set("TURBO_LEAN_JOBS", "2");
        let dir = make_temp_test_dir("speed2_dynlib_ready");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("Pre"))?;
        fs::create_dir_all(proj_dir.join("Down"))?;
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            proj_dir.join("lakefile.toml"),
            r#"name = "dynready"
defaultTargets = ["Pre", "Down"]
[[lean_lib]]
name = "Pre"
precompileModules = true
roots = ["Pre.Top"]
globs = ["Pre.+"]
[[lean_lib]]
name = "Down"
roots = ["Down.Use"]
globs = ["Down.+"]
"#,
        )?;
        fs::write(proj_dir.join("Pre/A.lean"), "def preA : Nat := 11\n")?;
        fs::write(proj_dir.join("Pre/B.lean"), "def preB : Nat := 22\n")?;
        fs::write(
            proj_dir.join("Pre/Top.lean"),
            "import Pre.A\ndef preTop : Nat := preA + 1\n",
        )?;
        fs::write(
            proj_dir.join("Down/Use.lean"),
            "import Pre.Top\ndef usePre : Nat := preTop + 1\n",
        )?;

        let cfg = resolve_project_config(&proj_dir)?;
        let tc_spec = query_toolchain_native_spec(&cfg.lean_bin)?;
        let sh_ext = tc_spec.shared_lib_ext().to_string();
        let mod_dynlib_a = proj_dir.join(format!(".lake/build/lib/lean/dynready_Pre_A.{sh_ext}"));
        let co_export_b = proj_dir.join(".lake/build/ir/Pre/B.c.o.export");
        let shared_lib_pre = proj_dir.join(format!(".lake/build/lib/libdynready_Pre.{sh_ext}"));

        let saw_ready = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let saw_ready_hook = std::sync::Arc::clone(&saw_ready);
        let mod_a_chk = mod_dynlib_a.clone();
        let co_b_chk = co_export_b.clone();
        let sh_pre_chk = shared_lib_pre.clone();
        let hook: std::sync::Arc<NativeSchedulerTestHook> =
            std::sync::Arc::new(move |kind: &str, mods: &[String]| {
                if kind == "compile_subprocess_start"
                    && mods.iter().any(|m| m == "Down.Use")
                    && mod_a_chk.is_file()
                    && co_b_chk.is_file()
                    && sh_pre_chk.is_file()
                {
                    saw_ready_hook.store(true, Ordering::SeqCst);
                }
            });

        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        let _trace = ScopedSchedulerTrace::start(Some(hook));
        let rep = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        assert_eq!(rep.modules_compiled, 4);
        assert!(
            saw_ready.load(Ordering::SeqCst),
            "Pre module dynlibs and shared library must already exist on disk when Down.Use starts compiling"
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    /// Speed-2 (4): Zygote audit runs in micro-batches (not 1 subprocess per module when multiple
    /// candidates are ready) and overlaps with ongoing compilation / CAS blob hashing.
    #[test]
    fn test_speed2_microbatched_audit_and_cas_overlap() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let _jobs = ScopedEnvVar::set("TURBO_LEAN_JOBS", "2");
        let _batch = ScopedEnvVar::set("TURBO_LEAN_AUDIT_BATCH_SIZE", "4");
        let dir = make_temp_test_dir("speed2_batch_overlap");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("Batch"))?;
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"batchproj\"\ndefaultTargets = [\"Batch\"]\n[[lean_lib]]\nname = \"Batch\"\nglobs = [\"Batch.+\"]\n",
        )?;
        for name in ["M1", "M2", "M3", "M4"] {
            fs::write(
                proj_dir.join(format!("Batch/{name}.lean")),
                format!("def val{name} : Nat := 1\n"),
            )?;
        }

        // First build populates per-module CAS and exercises concurrent compile + audit + CAS hashing.
        let overlapped_compile_and_bg =
            std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let overlap_flag = std::sync::Arc::clone(&overlapped_compile_and_bg);
        let in_audit_or_cas = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let bg_counter = std::sync::Arc::clone(&in_audit_or_cas);
        let hook1: std::sync::Arc<NativeSchedulerTestHook> =
            std::sync::Arc::new(move |kind: &str, _mods: &[String]| match kind {
                "audit_subprocess_start" | "cas_hash_start" => {
                    bg_counter.fetch_add(1, Ordering::SeqCst);
                    std::thread::sleep(std::time::Duration::from_millis(40));
                }
                "audit_subprocess_end" | "cas_hash_end" => {
                    bg_counter.fetch_sub(1, Ordering::SeqCst);
                }
                "compile_subprocess_start" => {
                    let deadline =
                        std::time::Instant::now() + std::time::Duration::from_millis(120);
                    while std::time::Instant::now() < deadline {
                        if bg_counter.load(Ordering::SeqCst) > 0 {
                            overlap_flag.store(true, Ordering::SeqCst);
                            break;
                        }
                        std::thread::sleep(std::time::Duration::from_millis(2));
                    }
                }
                _ => {}
            });

        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        let trace1 = ScopedSchedulerTrace::start(Some(hook1));
        let rep1 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let ev1 = trace1.take_events();
        assert_eq!(rep1.modules_compiled, 4);
        assert_eq!(
            ev1.iter().filter(|e| e.kind == "cas_hash_start").count(),
            4,
            "all 4 compiled modules must stream through the background CAS hashing worker"
        );
        assert!(
            overlapped_compile_and_bg.load(Ordering::SeqCst),
            "compilation of remaining ready modules must overlap with background Zygote audit / CAS hashing"
        );

        // Second build after wiping `.lake/build`: all 4 CAS hits materialize and are audited in a
        // single micro-batched Zygote subprocess (`batch_size == 4`), NOT 4 separate subprocesses!
        fs::remove_dir_all(proj_dir.join(".lake/build"))?;
        let trace2 = ScopedSchedulerTrace::start(None);
        let rep2 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let ev2 = trace2.take_events();
        assert_eq!(rep2.modules_cached, 4);
        let audit_batches: Vec<&Vec<String>> = ev2
            .iter()
            .filter(|e| e.kind == "audit_subprocess_start")
            .map(|e| &e.modules)
            .collect();
        assert_eq!(
            audit_batches.len(),
            1,
            "4 ready CAS hits with batch_size=4 must run in 1 micro-batched Zygote audit subprocess, got: {audit_batches:?}"
        );
        assert_eq!(audit_batches[0].len(), 4);

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    /// Speed-2 (5): `CasRestored` audit failure fails closed, wipes the unverified materialized
    /// outputs on disk, and never accepts or schedules downstream dependents.
    #[test]
    fn test_speed2_cas_restored_audit_failure_fails_closed_and_cleans_up() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("speed2_cas_fail_closed");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("CasFail"))?;
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"casfail\"\ndefaultTargets = [\"CasFail\"]\n[[lean_lib]]\nname = \"CasFail\"\nglobs = [\"CasFail.+\"]\n",
        )?;
        fs::write(
            proj_dir.join("CasFail/Base.lean"),
            "theorem bad_thm : True := by sorry\n",
        )?;
        fs::write(
            proj_dir.join("CasFail/Child.lean"),
            "import CasFail.Base\ndef useBase : Nat := 1\n",
        )?;

        // Build `CasFail.Base` with `lake build` so we get real `.olean` artifacts containing `sorryAx`,
        // then inject them into `TurboStore` under `CasFail.Base`'s `module_unit` key.
        let out = Command::new("lake")
            .args(["build", "CasFail.Base"])
            .env("LEAN_NUM_THREADS", "2")
            .current_dir(&proj_dir)
            .output()?;
        anyhow::ensure!(
            out.status.success(),
            "lake build CasFail.Base failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        let cfg = resolve_project_config(&proj_dir)?;
        let dag = build_module_dag_with_trust(&cfg, &[], false)?;
        let base_node = dag.nodes.get("CasFail.Base").expect("CasFail.Base in dag");
        let canon_proj = proj_dir.canonicalize()?;
        let base_key = compute_module_cas_key(&cfg, base_node, &[], base_node.needs_c)?;

        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        store_module_artifacts_in_cas(
            &mut store,
            &canon_proj,
            base_node,
            &base_key,
            &cfg.toolchain,
            "trusted",
            1,
            10,
        )?;
        fs::remove_dir_all(proj_dir.join(".lake/build"))?;

        let trace = ScopedSchedulerTrace::start(None);
        let err = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )
        .unwrap_err()
        .to_string();
        let events = trace.take_events();
        assert!(
            err.contains(
                "In-kernel `.olean` audit rejected materialized CAS hit for module `CasFail.Base`"
            ),
            "unexpected error: {err}"
        );
        assert!(
            !base_node.olean_path.exists(),
            "rejected CasRestored `.olean` must be wiped from `.lake/build`"
        );
        assert!(
            !events
                .iter()
                .any(|e| e.modules.iter().any(|m| m == "CasFail.Child")),
            "dependent CasFail.Child must never be scheduled or compiled when CasFail.Base fails audit: {events:?}"
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    /// Speed-2 (6): When a `WarmAdopted` on-disk candidate fails Zygote audit (even inside a
    /// mixed batch with a valid `WarmAdopted` peer), only the rejected candidate is wiped and
    /// recompiled from clean source before any of its dependents is accepted or compiled.
    #[test]
    fn test_speed2_warm_adopted_audit_failure_falls_back_before_dependent_starts() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let _jobs = ScopedEnvVar::set("TURBO_LEAN_JOBS", "2");
        let dir = make_temp_test_dir("speed2_warm_fallback");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("WarmFb"))?;
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"warmfb\"\ndefaultTargets = [\"WarmFb\"]\n[[lean_lib]]\nname = \"WarmFb\"\nglobs = [\"WarmFb.+\"]\n",
        )?;
        // First build with `sorry` in `WarmFb.Bad` via Lake so `.olean` has `sorryAx`.
        fs::write(
            proj_dir.join("WarmFb/Good.lean"),
            "def goodVal : Nat := 7\n",
        )?;
        let sorry_src = "theorem warm_thm : True := by sorry\n";
        let clean_src = "theorem warm_thm : True := trivial\n";
        fs::write(proj_dir.join("WarmFb/Bad.lean"), sorry_src)?;
        fs::write(
            proj_dir.join("WarmFb/Child.lean"),
            "import WarmFb.Bad\ntheorem child_thm : True := warm_thm\n",
        )?;
        let out = Command::new("lake")
            .args(["build", "WarmFb.Good", "WarmFb.Bad"])
            .env("LEAN_NUM_THREADS", "2")
            .current_dir(&proj_dir)
            .output()?;
        anyhow::ensure!(
            out.status.success(),
            "lake build failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );

        // Now fix `WarmFb/Bad.lean` to clean `trivial` AND rewrite `Bad.trace`'s source hash AND
        // recompute `depHash = lake_input_hash(&tv["inputs"])` so `probe_warm_on_disk_module_candidate`
        // treats the stale `sorryAx`-tainted `.olean` as a `WarmAdopted` candidate; Zygote's in-kernel
        // audit must catch `sorryAx`, wipe `WarmFb.Bad`, fall back to clean compilation of
        // `WarmFb/Bad.lean`, and only THEN compile `WarmFb.Child`!
        fs::write(proj_dir.join("WarmFb/Bad.lean"), clean_src)?;
        let trace_path = proj_dir.join(".lake/build/lib/lean/WarmFb/Bad.trace");
        let old_src_hash = format!("{:016x}", lake_hash_text(sorry_src));
        let new_src_hash = format!("{:016x}", lake_hash_text(clean_src));
        let patched_raw = fs::read_to_string(&trace_path)?.replace(&old_src_hash, &new_src_hash);
        let mut tv: serde_json::Value = serde_json::from_str(&patched_raw)?;
        let new_dep_h = format!("{:016x}", lake_input_hash(&tv["inputs"])?);
        tv["depHash"] = serde_json::Value::String(new_dep_h);
        fs::write(&trace_path, serde_json::to_vec(&tv)?)?;

        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        let trace = ScopedSchedulerTrace::start(None);
        let rep = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let events = trace.take_events();
        assert_eq!(
            rep.modules_up_to_date_reused, 1,
            "WarmFb.Good must still be WarmAdopted without recompiling"
        );
        assert_eq!(
            rep.compiled_modules,
            vec!["WarmFb.Bad".to_string(), "WarmFb.Child".to_string()],
            "WarmFb.Bad must fall back to source compilation and then unlock WarmFb.Child"
        );
        let fb_idx = events
            .iter()
            .position(|e| e.kind == "warm_fallback_to_compile" && e.modules == ["WarmFb.Bad"])
            .expect("warm_fallback_to_compile for WarmFb.Bad");
        let bad_accept_idx = events
            .iter()
            .position(|e| e.kind == "module_accepted" && e.modules == ["WarmFb.Bad"])
            .expect("module_accepted for WarmFb.Bad");
        let child_dispatch_idx = events
            .iter()
            .position(|e| e.kind == "compile_dispatch" && e.modules == ["WarmFb.Child"])
            .expect("compile_dispatch for WarmFb.Child");
        assert!(
            fb_idx < bad_accept_idx && bad_accept_idx < child_dispatch_idx,
            "WarmFb.Child must not dispatch until WarmFb.Bad falls back, recompiles, and passes audit (fb={fb_idx}, accept={bad_accept_idx}, child={child_dispatch_idx})"
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_speed3_attested_replay_transfer_and_cone_export_skip_dep_replay() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("speed3_replay_and_cone");
        let sk_hex = "7777777777777777777777777777777777777777777777777777777777777777";
        let pk_hex = crate::receipt::ed25519_verifying_key_hex(&[0x77u8; 32]);

        let build_workspace = |root: &Path| -> Result<()> {
            let dep_dir = root.join(".lake/packages/dep_pkg");
            fs::create_dir_all(dep_dir.join("Dep"))?;
            fs::create_dir_all(root.join("ConeA"))?;
            fs::create_dir_all(root.join("ConeB"))?;
            fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
            fs::write(dep_dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
            fs::write(
                dep_dir.join("lakefile.toml"),
                "name = \"dep_pkg\"\ndefaultTargets = [\"Dep\"]\n[[lean_lib]]\nname = \"Dep\"\nglobs = [\"Dep.+\"]\n",
            )?;
            fs::write(dep_dir.join("Dep/Base.lean"), "def depBase : Nat := 42\n")?;
            fs::write(
                root.join("lake-manifest.json"),
                r#"{"version":"1.1.0","packagesDir":".lake/packages","packages":[{"type":"path","name":"dep_pkg","dir":".lake/packages/dep_pkg"}]}"#,
            )?;
            fs::write(
                root.join("lakefile.toml"),
                "name = \"cone_root\"\ndefaultTargets = [\"ConeA\", \"ConeB\"]\n[[lean_lib]]\nname = \"ConeA\"\nglobs = [\"ConeA.+\"]\n[[lean_lib]]\nname = \"ConeB\"\nglobs = [\"ConeB.+\"]\n",
            )?;
            fs::write(
                root.join("ConeA/Main.lean"),
                "import Dep.Base\ndef coneAVal : Nat := depBase + 1\n",
            )?;
            fs::write(
                root.join("ConeB/Unrelated.lean"),
                "def coneBVal : Nat := 999\n",
            )?;
            Ok(())
        };

        let proj_src = dir.join("proj_src");
        build_workspace(&proj_src)?;
        let mut store_src = TurboStore::open(Some(&dir.join("store_src")))?;
        let rep_src = build_project_modules_native(
            &mut store_src,
            &proj_src,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        assert_eq!(rep_src.modules_compiled, 3);

        // Export `--cone ConeA.Main` signed with `sk_hex`; verify `ConeB.Unrelated` is excluded
        // from both `actions` and `replayed_oleans`, while `Dep.Base` + `ConeA.Main` are included.
        let cone_pack = dir.join("cone_a.tlpack");
        crate::pack::run_export_command(
            &store_src,
            true,
            cone_pack.clone(),
            true,
            Some(sk_hex.to_string()),
            Some("ConeA.Main".to_string()),
            Some(proj_src.clone()),
        )?;
        let raw_cone = fs::read(&cone_pack)?;
        assert_eq!(&raw_cone[..8], b"TLPK\x00\x00\x00\x02");
        let hlen = u64::from_le_bytes(raw_cone[8..16].try_into()?) as usize;
        let cone_manifest: crate::pack::PackManifest =
            serde_json::from_slice(&raw_cone[16..16 + hlen])?;
        assert_eq!(
            cone_manifest.actions.len(),
            2,
            "cone pack must contain only Dep.Base and ConeA.Main actions"
        );
        let replay_mods: BTreeSet<&str> = cone_manifest
            .replayed_oleans
            .iter()
            .map(|r| r.module_name.as_str())
            .collect();
        assert!(
            replay_mods.contains("Dep.Base") && !replay_mods.contains("ConeB.Unrelated"),
            "cone replayed_oleans must include Dep.Base and exclude ConeB.Unrelated: {replay_mods:?}"
        );

        // Import into a cold destination store (`store_dst`) with a separate `.verifier_replay_hmac_key`
        // and verify `ConeA.Main` restores from CAS WITHOUT spawning `--kernel-replay-module` for `Dep.Base`.
        let proj_dst = dir.join("proj_dst");
        build_workspace(&proj_dst)?;
        let mut store_dst = TurboStore::open(Some(&dir.join("store_dst")))?;
        crate::pack::import_pack_with_policy(
            &mut store_dst,
            &cone_pack,
            Some("trusted"),
            Some(&pk_hex),
            false,
        )?;
        let trace = ScopedSchedulerTrace::start(None);
        let rep_dst = build_project_modules_native(
            &mut store_dst,
            &proj_dst,
            &["ConeA.Main".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let events = trace.take_events();
        assert_eq!(rep_dst.modules_compiled, 0);
        assert_eq!(rep_dst.modules_cached, 2);
        assert!(
            !events.iter().any(|e| e.kind == "replay_subprocess_start"),
            "attested non-root Dep.Base must skip --kernel-replay-module subprocess: {events:?}"
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_build_setup_json_and_lake_trace_toolchain_compat() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_setup_compat_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(dir.join("T"))?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.31.0\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"t\"\ndefaultTargets = [\"T\"]\n[[lean_lib]]\nname = \"T\"\nglobs = [\"T.+\", \"T\"]\n",
        )?;
        fs::write(dir.join("T/Leg.lean"), "def leg := 1\n")?;
        fs::write(dir.join("T/ModA.lean"), "module\npublic def modA := 1\n")?;
        fs::write(
            dir.join("T/ModB.lean"),
            "module\nimport T.ModA\nimport all T.Leg\npublic def modB := modA\n",
        )?;
        fs::write(dir.join("T.lean"), "import T.Leg\nimport T.ModA\n")?;

        let mut cfg = resolve_project_config_with_trust(&dir, false)?;
        let dag = build_module_dag_with_trust(&cfg, &["T".to_string()], false)?;
        let node_t = dag.nodes.get("T").expect("T node");
        let node_b = dag.nodes.get("T.ModB").expect("T.ModB node");
        let leg_olean = dag.nodes["T.Leg"].olean_path.to_string_lossy().to_string();
        let moda_olean_p = &dag.nodes["T.ModA"].olean_path;
        let moda_olean = moda_olean_p.to_string_lossy().to_string();
        let moda_ir = moda_olean_p
            .with_extension("ir")
            .to_string_lossy()
            .to_string();
        let moda_srv = format!("{}.server", moda_olean_p.display());
        let moda_priv = format!("{}.private", moda_olean_p.display());
        let moda_sig = format!("{}.sig", moda_ir);
        let dummy_plug = dir.join("plug.so");

        // 1. Lean 4.30: 1D `importArts` + plain string `plugins`.
        cfg.toolchain = "leanprover/lean4:v4.30.0".to_string();
        let s430 = build_setup_json(
            &cfg,
            &dag,
            node_t,
            None,
            Some(std::slice::from_ref(&dummy_plug)),
        )?;
        assert_eq!(s430["importArts"]["T.Leg"], serde_json::json!([leg_olean]));
        assert_eq!(
            s430["importArts"]["T.ModA"],
            serde_json::json!([moda_olean, moda_ir, moda_srv, moda_priv])
        );
        assert!(s430["plugins"]
            .as_array()
            .unwrap()
            .iter()
            .all(|v| v.is_string()));
        assert!(s430["plugins"]
            .as_array()
            .unwrap()
            .contains(&serde_json::json!(dummy_plug.to_string_lossy())));

        // 2. Lean 4.31: 1D `importArts` (`[olean, ir, server]` for module-to-module, `[olean, ir, server, private]` for legacy) + `{path}` `plugins`.
        cfg.toolchain = "leanprover/lean4:v4.31.0".to_string();
        let s431_b = build_setup_json(
            &cfg,
            &dag,
            node_b,
            None,
            Some(std::slice::from_ref(&dummy_plug)),
        )?;
        assert_eq!(
            s431_b["importArts"]["T.ModA"],
            serde_json::json!([moda_olean, moda_ir, moda_srv])
        );
        assert!(s431_b["plugins"]
            .as_array()
            .unwrap()
            .iter()
            .all(|v| v.is_object()));
        assert!(s431_b["plugins"]
            .as_array()
            .unwrap()
            .contains(&serde_json::json!({"path": dummy_plug.to_string_lossy()})));

        // 3. Lean 4.33+: 2D `importArts` (`[[olean, server], [ir.sig, ir]]`).
        cfg.toolchain = "leanprover/lean4:v4.33.0".to_string();
        let s433_b = build_setup_json(&cfg, &dag, node_b, None, None)?;
        assert_eq!(
            s433_b["importArts"]["T.ModA"],
            serde_json::json!([[moda_olean, moda_srv], [moda_sig, moda_ir]])
        );
        let s433_t = build_setup_json(&cfg, &dag, node_t, None, None)?;
        assert_eq!(
            s433_t["importArts"]["T.Leg"],
            serde_json::json!([[leg_olean]])
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_speed3_remote_cache_pull_push_tamper_fail_closed_and_untrusted_no_push() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let _bwrap_guard = BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = make_temp_test_dir("speed3_remote_cache");
        let sk_hex = "8888888888888888888888888888888888888888888888888888888888888888";
        let pk_hex = crate::receipt::ed25519_verifying_key_hex(&[0x88u8; 32]);
        let _sk = ScopedEnvVar::set("TURBO_LEAN_PACK_SIGNING_KEY", sk_hex);
        let _pk = ScopedEnvVar::set("TURBO_LEAN_PACK_TRUSTED_PUBKEY", &pk_hex);

        let srv_dir = dir.join("srv_store");
        let _ = TurboStore::open(Some(&srv_dir))?;
        let srv_url = format!(
            "http://{}",
            crate::pack::tests::spawn_test_server(&srv_dir)?
        );

        let write_proj = |p: &Path, val: u32| -> Result<()> {
            fs::create_dir_all(p.join("Rem"))?;
            fs::write(p.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
            fs::write(
                p.join("lakefile.toml"),
                "name = \"rem_proj\"\ndefaultTargets = [\"Rem\"]\n[[lean_lib]]\nname = \"Rem\"\nglobs = [\"Rem.+\"]\n",
            )?;
            fs::write(
                p.join("Rem/Mod.lean"),
                format!("def remVal : Nat := {val}\n"),
            )?;
            Ok(())
        };

        // 1. Trusted build with `TURBO_LEAN_REMOTE_CACHE` pushes `module_unit` to remote coordinator.
        {
            let _rc = ScopedEnvVar::set("TURBO_LEAN_REMOTE_CACHE", &srv_url);
            let proj1 = dir.join("proj1");
            write_proj(&proj1, 101)?;
            let mut store1 = TurboStore::open(Some(&dir.join("store1")))?;
            let rep1 = build_project_modules_native(
                &mut store1,
                &proj1,
                &[],
                "trusted",
                1,
                false,
                true,
                None,
            )?;
            assert_eq!(rep1.modules_compiled, 1);

            let dm = crate::pack::fetch_remote_cache_manifest(&srv_url, None)?;
            assert_eq!(
                dm.action_keys.len(),
                1,
                "trusted compile must push module_unit to remote cache"
            );

            // 2. Cold store pulls `module_unit` on demand and skips local compilation.
            let proj2 = dir.join("proj2");
            write_proj(&proj2, 101)?;
            let mut store2 = TurboStore::open(Some(&dir.join("store2")))?;
            let rep2 = build_project_modules_native(
                &mut store2,
                &proj2,
                &[],
                "trusted",
                1,
                false,
                true,
                None,
            )?;
            assert_eq!(
                rep2.modules_compiled, 0,
                "cold local store must satisfy module_unit from remote cache"
            );
            assert_eq!(rep2.modules_cached, 1);
        }

        // 3. Untrusted build (`is_untrusted = true`) MUST NEVER push to `TURBO_LEAN_REMOTE_CACHE`.
        if probe_bwrap_sandbox(&dir).is_some() {
            let srv_ut_dir = dir.join("srv_ut_store");
            let _ = TurboStore::open(Some(&srv_ut_dir))?;
            let srv_ut_url = format!(
                "http://{}",
                crate::pack::tests::spawn_test_server(&srv_ut_dir)?
            );
            let _rc = ScopedEnvVar::set("TURBO_LEAN_REMOTE_CACHE", &srv_ut_url);
            let proj_ut = dir.join("proj_ut");
            write_proj(&proj_ut, 202)?;
            let mut store_ut = TurboStore::open(Some(&dir.join("store_ut")))?;
            let rep_ut = build_project_modules_native(
                &mut store_ut,
                &proj_ut,
                &[],
                "untrusted",
                0,
                true,
                true,
                None,
            )?;
            assert_eq!(rep_ut.modules_compiled, 1);
            let dm_ut = crate::pack::fetch_remote_cache_manifest(&srv_ut_url, None)?;
            assert!(
                dm_ut.action_keys.is_empty() && dm_ut.blob_hashes.is_empty(),
                "untrusted mode must never push actions or blobs to remote cache"
            );
        }

        // 4. Remote cache serving a corrupted blob digest fails closed (populates zero CAS entries)
        //    and falls back cleanly to local compilation.
        {
            let dm_good = crate::pack::fetch_remote_cache_manifest(&srv_url, None)?;
            let target_key = dm_good.action_keys[0].clone();
            let bad_listener = std::net::TcpListener::bind("127.0.0.1:0")?;
            let bad_addr = bad_listener.local_addr()?;
            let sk_owned = sk_hex.to_string();
            let bad_handle = std::thread::spawn(move || {
                use std::io::{Read, Write};
                for _ in 0..2 {
                    let Ok((mut stream, _)) = bad_listener.accept() else {
                        break;
                    };
                    let mut buf = [0u8; 4096];
                    let n = stream.read(&mut buf).unwrap_or(0);
                    let req_str = String::from_utf8_lossy(&buf[..n]);
                    if req_str.starts_with("GET /manifest") {
                        let body = serde_json::to_vec(&crate::pack::DeltaManifest {
                            action_keys: vec![target_key.clone()],
                            blob_hashes: vec!["aa".repeat(32)],
                        })
                        .unwrap();
                        let hdr = format!(
                            "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                            body.len()
                        );
                        let _ = stream.write_all(hdr.as_bytes());
                        let _ = stream.write_all(&body);
                    } else {
                        let claimed_hash = "aa".repeat(32);
                        let corrupt_bytes = b"corrupted-remote-olean-payload";
                        let mut m = crate::pack::PackManifest {
                            format_version: 2,
                            host_arch: std::env::consts::ARCH.into(),
                            created_at: 1,
                            ed25519_pubkey: None,
                            ed25519_signature: None,
                            actions: vec![crate::db::ActionRecord {
                                action_key: target_key.clone(),
                                toolchain_githash: "v4.35.0".into(),
                                kind: "module_unit".into(),
                                status: "done".into(),
                                fencing_token: 1,
                                output_manifest_hash: "00".repeat(32),
                                duration_ms: 1,
                                peak_pss_bytes: 0,
                                heartbeats: 1,
                                trust_domain: "trusted".into(),
                                outputs: vec![BlobEntry {
                                    blob_hash: claimed_hash.clone(),
                                    kind: "olean".into(),
                                    size_bytes: corrupt_bytes.len() as u64,
                                    rel_path: ".lake/build/lib/lean/Rem/Mod.olean".into(),
                                }],
                            }],
                            blobs: vec![crate::pack::PackedBlob {
                                blob_hash: claimed_hash,
                                kind: "olean".into(),
                                size_bytes: corrupt_bytes.len() as u64,
                                portable: true,
                                data_hex_or_base64: Vec::new(),
                            }],
                            replayed_oleans: Vec::new(),
                        };
                        crate::pack::sign_pack_manifest_ed25519(&mut m, &sk_owned).unwrap();
                        let mbytes = serde_json::to_vec(&m).unwrap();
                        let mut raw_tlpk = Vec::new();
                        raw_tlpk.extend_from_slice(b"TLPK\x00\x00\x00\x02");
                        raw_tlpk.extend_from_slice(&(mbytes.len() as u64).to_le_bytes());
                        raw_tlpk.extend_from_slice(&mbytes);
                        raw_tlpk.extend_from_slice(corrupt_bytes);
                        let hdr = format!(
                            "HTTP/1.1 200 OK\r\nContent-Type: application/octet-stream\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                            raw_tlpk.len()
                        );
                        let _ = stream.write_all(hdr.as_bytes());
                        let _ = stream.write_all(&raw_tlpk);
                    }
                }
            });

            let bad_url = format!("http://{bad_addr}");
            let mut store_bad_only = TurboStore::open(Some(&dir.join("store_bad_only")))?;
            let mut rem_man = None;
            assert!(
                crate::pack::try_pull_remote_module_action(
                    &mut store_bad_only,
                    &bad_url,
                    None,
                    &mut rem_man,
                    std::slice::from_ref(&dm_good.action_keys[0]),
                    "trusted",
                    false,
                )
                .is_err(),
                "BLAKE3 digest mismatch from remote cache must fail closed"
            );
            assert!(
                store_bad_only
                    .get_cached_action(&dm_good.action_keys[0], "trusted")?
                    .is_none(),
                "corrupted remote pack must never populate local CAS"
            );
            let _ = bad_handle.join();
        }

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_speed4_module_public_export_digest_skips_downstream_on_private_edit() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("speed4_mod_pub_export_cas");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("App"))?;
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )?;
        fs::write(
            proj_dir.join("App/A.lean"),
            "module\nprivate def secretHelper : Nat := 1\nprivate theorem secretThm (x : Nat) : x + 0 = x := Nat.add_zero x\n@[noinline] public def pubFn (x : Nat) : Nat := secretHelper + x\npublic def polyFn (f : Nat → Nat) (x : Nat) : Nat := f x + 1\n@[inline] public def inlineFn (x : Nat) : Nat := x + 10\n",
        )?;
        fs::write(
            proj_dir.join("App/B.lean"),
            "module\npublic import App.A\npublic def useA : Nat := pubFn 5 + inlineFn 2 + polyFn (fun z => z + 3) 4\n",
        )?;
        fs::write(
            proj_dir.join("App/AllConsumer.lean"),
            "module\nimport all App.A\npublic def peekSecret : Nat := secretHelper\npublic theorem useSecretThm (x : Nat) : x + 0 = x := secretThm x\n",
        )?;
        fs::write(
            proj_dir.join("App/MetaConsumer.lean"),
            "module\nmeta import App.A\nmeta def metaVal : Nat := pubFn 3\n",
        )?;

        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        let rep1 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            0,
            false,
            true,
            None,
        )?;
        assert_eq!(rep1.modules_compiled, 4);

        let a_olean = proj_dir.join(".lake/build/lib/lean/App/A.olean");
        let export1 = compute_dep_export_olean_digest(&a_olean)?;
        let meta1 = compute_dep_meta_olean_digest(&a_olean)?;
        let full1 = compute_olean_artifact_set_digest(&a_olean)?;

        // 1. Edit private theorem/proof in App/A.lean:
        //    A.olean + A.ir + A.ir.sig stay byte-identical -> App.B and App.MetaConsumer hit Module CAS!
        //    Meanwhile A.olean.private & A.ilean mutate -> AllConsumer (`import all`) recompiles.
        fs::write(
            proj_dir.join("App/A.lean"),
            "module\nprivate def secretHelper : Nat := 1\nprivate theorem secretThm (x : Nat) : x + 0 = x := by exact Nat.add_zero x\nprivate theorem extraSecretThm : True := trivial\n@[noinline] public def pubFn (x : Nat) : Nat := secretHelper + x\npublic def polyFn (f : Nat → Nat) (x : Nat) : Nat := f x + 1\n@[inline] public def inlineFn (x : Nat) : Nat := x + 10\n",
        )?;
        // Wipe B's and MetaConsumer's on-disk artifacts to prove they are satisfied purely from Module CAS.
        for mod_rel in ["App/B", "App/MetaConsumer"] {
            for ext in [
                "olean",
                "olean.server",
                "olean.private",
                "ilean",
                "ir",
                "ir.sig",
                "trace",
            ] {
                let _ =
                    fs::remove_file(proj_dir.join(format!(".lake/build/lib/lean/{mod_rel}.{ext}")));
            }
        }
        let rep2 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            0,
            false,
            true,
            None,
        )?;
        let export2 = compute_dep_export_olean_digest(&a_olean)?;
        let meta2 = compute_dep_meta_olean_digest(&a_olean)?;
        let full2 = compute_olean_artifact_set_digest(&a_olean)?;
        assert_eq!(
            export1, export2,
            "private theorem edit in `module` must keep dep_export_olean_digest identical"
        );
        assert_eq!(
            meta1, meta2,
            "private theorem edit in `module` must keep dep_meta_olean_digest identical"
        );
        assert_ne!(
            full1, full2,
            "private theorem edit must change full 6-artifact digest"
        );
        assert!(
            rep2.cached_modules.contains(&"App.B".to_string())
                && !rep2.compiled_modules.contains(&"App.B".to_string())
                && rep2.cached_modules.contains(&"App.MetaConsumer".to_string())
                && !rep2.compiled_modules.contains(&"App.MetaConsumer".to_string()),
            "App.B (`public import App.A`) and App.MetaConsumer (`meta import App.A`) must hit Module CAS after private theorem edit in App.A: {rep2:?}"
        );
        assert!(
            rep2.compiled_modules.contains(&"App.A".to_string())
                && rep2
                    .compiled_modules
                    .contains(&"App.AllConsumer".to_string()),
            "App.A and App.AllConsumer (`import all`) must recompile: {rep2:?}"
        );

        // 2. Edit higher-order `public def polyFn` body in App/A.lean:
        //    A.olean and A.ir.sig stay byte-identical, while A.ir mutates (specializable IR exported in `.ir`)
        //    -> `dep_export_olean_digest` MUST change and App.B MUST miss CAS and recompile its C codegen!
        fs::write(
            proj_dir.join("App/A.lean"),
            "module\nprivate def secretHelper : Nat := 1\nprivate theorem secretThm (x : Nat) : x + 0 = x := by exact Nat.add_zero x\nprivate theorem extraSecretThm : True := trivial\n@[noinline] public def pubFn (x : Nat) : Nat := secretHelper + x\npublic def polyFn (f : Nat → Nat) (x : Nat) : Nat := f x + 999\n@[inline] public def inlineFn (x : Nat) : Nat := x + 10\n",
        )?;
        let rep2_ir = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            0,
            false,
            true,
            None,
        )?;
        let export2_ir = compute_dep_export_olean_digest(&a_olean)?;
        assert_ne!(
            export2, export2_ir,
            "higher-order `public def` body edit mutating `.ir` must change dep_export_olean_digest"
        );
        assert!(
            rep2_ir.compiled_modules.contains(&"App.B".to_string())
                && rep2_ir
                    .compiled_modules
                    .contains(&"App.MetaConsumer".to_string()),
            "App.B and App.MetaConsumer must recompile when App.A `.ir` changes: {rep2_ir:?}"
        );

        // 3. Edit `@[inline] public def inlineFn` body in App/A.lean:
        //    A.olean changes -> App.B MUST miss CAS and recompile!
        fs::write(
            proj_dir.join("App/A.lean"),
            "module\nprivate def secretHelper : Nat := 1\nprivate theorem secretThm (x : Nat) : x + 0 = x := by exact Nat.add_zero x\nprivate theorem extraSecretThm : True := trivial\n@[noinline] public def pubFn (x : Nat) : Nat := secretHelper + x\npublic def polyFn (f : Nat → Nat) (x : Nat) : Nat := f x + 999\n@[inline] public def inlineFn (x : Nat) : Nat := x + 42\n",
        )?;
        let rep3 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            0,
            false,
            true,
            None,
        )?;
        let export3 = compute_dep_export_olean_digest(&a_olean)?;
        assert_ne!(
            export2_ir, export3,
            "`@[inline] public def` body edit must change dep_export_olean_digest"
        );
        assert!(
            rep3.compiled_modules.contains(&"App.B".to_string()),
            "App.B must recompile when `@[inline] public def` body changes in App.A: {rep3:?}"
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_wave8_olean_githash_skew_gate_and_header_parser() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo-w8-skew-{}-{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        fs::create_dir_all(dir.join(".lake/build/lib/lean"))?;
        // Fake a valid Lean v2 `.olean` header (80 bytes):
        // [0..5] "olean", [5] = 2 (version), [6] = 1 (flags), [7..40] Lean version, [40..80] 40-hex githash
        let mut hdr = vec![0u8; 80];
        hdr[..5].copy_from_slice(b"olean");
        hdr[5] = 2;
        hdr[6] = 1;
        let ver = b"4.30.0";
        hdr[7..7 + ver.len()].copy_from_slice(ver);
        let fake_hash = "deadbeefdeadbeefdeadbeefdeadbeefdeadbeef";
        hdr[40..80].copy_from_slice(fake_hash.as_bytes());
        let olean_p = dir.join(".lake/build/lib/lean/Foo.olean");
        fs::write(&olean_p, &hdr)?;

        let parsed = parse_olean_header_version_and_githash(&hdr)
            .expect("valid v2 .olean header must parse");
        assert_eq!(parsed.0, "4.30.0");
        assert_eq!(parsed.1, fake_hash);

        let err = enforce_project_olean_githash_gate(
            &dir,
            "leanprover/lean4:v4.35.0",
            Path::new("/fake/lean"),
            "0123456789abcdef0123456789abcdef01234567",
            &[PathBuf::from("/var/lib/orb-node/caches/elan")],
        )
        .expect_err("skewed .olean githash must fail closed");
        let msg = format!("{:#}", err);
        assert!(msg.contains("Prebuilt `.olean` toolchain/githash skew detected"));
        assert!(msg.contains("fail-closed toolchain gate"));
        assert!(msg.contains(fake_hash));

        // Matching githash passes immediately.
        enforce_project_olean_githash_gate(
            &dir,
            "leanprover/lean4:v4.30.0",
            Path::new("/fake/lean"),
            fake_hash,
            &[],
        )?;

        // Scan-cap regression: place 40 matching `.olean` files (`A00.olean`..`A39.olean`) ahead of
        // a skewed `Z99.olean` so any 32-file scan cap would miss `Z99.olean`.
        fs::remove_file(&olean_p)?;
        let good_hash = "0123456789abcdef0123456789abcdef01234567";
        let mut good_hdr = hdr.clone();
        good_hdr[40..80].copy_from_slice(good_hash.as_bytes());
        for i in 0..40 {
            fs::write(
                dir.join(format!(".lake/build/lib/lean/A{:02}.olean", i)),
                &good_hdr,
            )?;
        }
        let z99 = dir.join(".lake/build/lib/lean/Z99.olean");
        fs::write(&z99, &hdr)?;
        let err_late = enforce_project_olean_githash_gate(
            &dir,
            "leanprover/lean4:v4.35.0",
            Path::new("/fake/lean"),
            good_hash,
            &[],
        )
        .expect_err("skewed .olean past 32 files must still fail closed");
        assert!(format!("{:#}", err_late).contains("Z99.olean"));
        fs::remove_file(&z99)?;

        // Symlink leaf regression (`O_NOFOLLOW`): a symlink `.olean` pointing at a skewed external file
        // must NOT be followed by `read_olean_header_version_and_githash` or poison the scan.
        #[cfg(unix)]
        {
            let ext_skew = dir.join("outside_skew.olean");
            fs::write(&ext_skew, &hdr)?;
            let sym_olean = dir.join(".lake/build/lib/lean/Sym.olean");
            std::os::unix::fs::symlink(&ext_skew, &sym_olean)?;
            assert!(
                read_olean_header_version_and_githash(&sym_olean).is_none(),
                "O_NOFOLLOW must reject symlink .olean leaf"
            );
            enforce_project_olean_githash_gate(
                &dir,
                "leanprover/lean4:v4.35.0",
                Path::new("/fake/lean"),
                good_hash,
                &[],
            )?;
        }

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_wave8_file_path_build_check_emit_olean_and_mtime_immune_hydrate() -> Result<()> {
        let _env_lock_guard = native_build_env_guard();
        let _bwrap_guard = BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo-w8-e2e-{}-{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let proj = dir.join("proj");
        fs::create_dir_all(proj.join("W8"))?;
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"w8\"\ndefaultTargets = [\"W8\"]\n[[lean_lib]]\nname = \"W8\"\nglobs = [\"W8.+\"]\n",
        )?;
        let base_lean = proj.join("W8/Base.lean");
        let leaf_lean = proj.join("W8/Leaf.lean");
        fs::write(
            &base_lean,
            "def baseVal : Nat := 41\ntheorem base_eq : baseVal = 41 := rfl\n",
        )?;
        fs::write(
            &leaf_lean,
            "import W8.Base\ntheorem leaf_eq : baseVal + 1 = 42 := rfl\n",
        )?;

        let mut store = TurboStore::open(Some(&dir.join("store")))?;

        // 1) `turbo-lean build <path/to/File.lean>` builds by file path instead of failing target resolution.
        crate::lake_build::run_build_command(
            &mut store,
            true,
            vec!["W8/Base.lean".to_string()],
            proj.clone(),
            "trusted".to_string(),
            0,
            false,
        )?;
        let base_olean = proj.join(".lake/build/lib/lean/W8/Base.olean");
        assert!(
            base_olean.is_file(),
            "file-path build must materialize W8/Base.olean"
        );

        // 2) `turbo-lean check <file> --emit-olean` verifies & emits `.olean` + `.trace` for Leaf.lean.
        crate::check::run_check_command_with_opts(
            &mut store,
            true,
            true,
            PathBuf::from("W8/Leaf.lean"),
            None,
            proj.clone(),
            Some(2),
            true,
            None,
            true,
        )?;
        let leaf_olean = proj.join(".lake/build/lib/lean/W8/Leaf.olean");
        let leaf_trace = proj.join(".lake/build/lib/lean/W8/Leaf.trace");
        assert!(
            leaf_olean.is_file(),
            "check --emit-olean must materialize W8/Leaf.olean"
        );
        assert!(
            leaf_trace.is_file(),
            "check --emit-olean must materialize W8/Leaf.trace"
        );

        // 3) Simulate `git checkout` / `rebase` mtime skew AND missing `.turbo_verified_sources.json`:
        // bump source mtimes into the future without modifying bytes, delete `.turbo_verified_sources.json`,
        // run `hydrate_project_traces`, and assert `<200ms` hydration + zero-rebuild freshness.
        let manifest_path = proj.join(".lake/build/.turbo_verified_sources.json");
        assert!(
            manifest_path.is_file(),
            "turbo-lean build / check --emit-olean must populate .turbo_verified_sources.json"
        );
        // Re-write identical bytes so source mtime > olean mtime (simulating `git checkout` / `rebase`).
        std::thread::sleep(std::time::Duration::from_millis(25));
        fs::write(&base_lean, fs::read(&base_lean)?)?;
        fs::write(&leaf_lean, fs::read(&leaf_lean)?)?;

        let canon_proj = proj.canonicalize().unwrap_or_else(|_| proj.clone());
        let canon_leaf = leaf_lean
            .canonicalize()
            .unwrap_or_else(|_| leaf_lean.clone());

        // 3a) `are_all_project_oleans_up_to_date` must remain true in <200ms despite source mtime > olean mtime!
        let mut fhashes = BTreeMap::new();
        fhashes.insert(
            "W8/Base.lean".to_string(),
            blake3::hash(&fs::read(&base_lean)?).to_hex().to_string(),
        );
        fhashes.insert(
            "W8/Leaf.lean".to_string(),
            blake3::hash(&fs::read(&leaf_lean)?).to_hex().to_string(),
        );
        let t_fresh = std::time::Instant::now();
        assert!(
            crate::lake_build::are_all_project_oleans_up_to_date(&canon_proj, &fhashes),
            "mtime-skewed sources with identical BLAKE3 content must stay cryptographically fresh"
        );
        assert!(t_fresh.elapsed().as_millis() < 200);

        // 3b) Delete `.turbo_verified_sources.json` (simulating a warm Lake worktree without turbo manifest),
        // run `hydrate_project_traces`, and assert `<200ms` hydration + zero-rebuild import freshness
        // WITHOUT forging `kernel_audited = true`!
        fs::remove_file(&manifest_path)?;
        let hyd = hydrate_project_traces(&proj)?;
        assert_eq!(hyd.modules_verified, 2);
        assert_eq!(hyd.entries_written, 2);
        assert!(
            hyd.elapsed_ms < 200,
            "hydrate-traces on small workspace took {} ms (budget <200ms)",
            hyd.elapsed_ms
        );
        assert!(
            manifest_path.is_file(),
            "hydrate-traces must write .turbo_verified_sources.json"
        );
        let hydrated_manifest: VerifiedDepManifest =
            serde_json::from_slice(&fs::read(&manifest_path)?)?;
        for entry in hydrated_manifest.modules.values() {
            assert!(
                !entry.kernel_audited,
                "hydrate-traces must not forge kernel_audited=true without kernel replay"
            );
        }
        let t_imp = std::time::Instant::now();
        let refreshed = crate::lake_build::ensure_project_imports_fresh_for_check(
            &canon_proj,
            std::slice::from_ref(&canon_leaf),
        )?;
        assert_eq!(
            refreshed, 0,
            "hydrated mtime-skewed imports must require 0 Lake refreshes"
        );
        assert!(t_imp.elapsed().as_millis() < 200);

        // 4) Toolchain-upgrade rebuild regression vs hydrate fail-closed skew gate:
        // overwrite `W8/Base.olean` with a valid v2 header carrying an old toolchain githash while
        // the exact requested toolchain (`v4.35.0`) is installed.
        // - `hydrate_project_traces` MUST fail closed on the githash skew.
        // - `turbo-lean build` MUST treat the skewed `.olean` as stale and rebuild it cleanly!
        let mut skewed_bytes = fs::read(&base_olean)?;
        assert!(skewed_bytes.len() >= 80);
        skewed_bytes[40..80].copy_from_slice(b"deadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
        fs::write(&base_olean, &skewed_bytes)?;
        let hyd_err = hydrate_project_traces(&proj)
            .expect_err("hydrate-traces must fail closed on skewed .olean githash");
        assert!(format!("{:#}", hyd_err).contains("Prebuilt `.olean` toolchain/githash skew"));

        crate::lake_build::run_build_command(
            &mut store,
            true,
            vec!["W8/Leaf.lean".to_string()],
            proj.clone(),
            "trusted".to_string(),
            0,
            false,
        )?;
        let (_, rebuilt_gh) = read_olean_header_version_and_githash(&base_olean)
            .expect("rebuilt Base.olean must have valid v2 header");
        assert_ne!(
            rebuilt_gh, "deadbeefdeadbeefdeadbeefdeadbeefdeadbeef",
            "turbo-lean build must rebuild skewed .olean on toolchain upgrade instead of failing closed"
        );

        #[cfg(unix)]
        {
            let fake_tc = dir.join("fake_tc_lib_lean");
            fs::create_dir_all(fake_tc.join("Init"))?;
            fs::copy(&base_olean, fake_tc.join("RealBase.olean"))?;
            assert!(is_verified_toolchain_olean_file(
                &fake_tc,
                Some(&rebuilt_gh),
                &fake_tc.join("RealBase.olean")
            ));
            std::os::unix::fs::symlink(&base_olean, fake_tc.join("Init/SymlinkLeaf.olean"))?;
            assert!(
                !is_verified_toolchain_olean_file(
                    &fake_tc,
                    Some(&rebuilt_gh),
                    &fake_tc.join("Init/SymlinkLeaf.olean")
                ),
                "is_verified_toolchain_olean_file must reject symlinked .olean leaf"
            );
            std::os::unix::fs::symlink(
                proj.join(".lake/build/lib/lean/W8"),
                fake_tc.join("SymlinkDir"),
            )?;
            assert!(
                !is_verified_toolchain_olean_file(
                    &fake_tc,
                    Some(&rebuilt_gh),
                    &fake_tc.join("SymlinkDir/Base.olean")
                ),
                "is_verified_toolchain_olean_file must reject symlinked directory inside toolchain_lib_lean"
            );
            let canon_fake = fake_tc.canonicalize()?;
            assert!(read_olean_header_version_and_githash_confined(
                &canon_fake,
                &canon_fake.join("RealBase.olean")
            )
            .is_some());
            assert!(
                read_olean_header_version_and_githash_confined(
                    &canon_fake,
                    &canon_fake.join("SymlinkDir/Base.olean")
                )
                .is_none(),
                "read_olean_header_version_and_githash_confined must reject intermediate directory symlinks"
            );
            assert!(
                read_olean_header_version_and_githash_confined(
                    &canon_fake,
                    &canon_fake.join("Init/SymlinkLeaf.olean")
                )
                .is_none(),
                "read_olean_header_version_and_githash_confined must reject symlinked leaf .olean"
            );
        }

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_lean_diagnostics_persisted_in_lake_trace_and_cas_restore() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("trace_diagnostics_cas");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("WarnLib"))?;
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"warn_proj\"\ndefaultTargets = [\"WarnLib\"]\n[[lean_lib]]\nname = \"WarnLib\"\nglobs = [\"WarnLib.+\"]\n",
        )?;
        fs::write(
            proj_dir.join("WarnLib/Mod.lean"),
            "namespace WarnLib\ntheorem unused_var_thm (x y : Nat) : x = x := rfl\nend WarnLib\n",
        )?;

        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        crate::lake_build::run_build_command(
            &mut store,
            false,
            vec!["WarnLib".to_string()],
            proj_dir.clone(),
            "trusted".to_string(),
            1,
            true,
        )?;

        let trace_path = proj_dir.join(".lake/build/lib/lean/WarnLib/Mod.trace");
        let trace_val: serde_json::Value = serde_json::from_slice(&fs::read(&trace_path)?)?;
        let log_arr = trace_val["log"].as_array().expect("trace log array");
        assert!(
            log_arr.iter().any(|entry| {
                entry["level"] == "warning"
                    && entry["message"]
                        .as_str()
                        .is_some_and(|m| m.starts_with("WarnLib/Mod.lean:") && m.contains("`y`"))
            }),
            "cold build must populate Lake .trace log with workspace-relative warning: {:?}",
            log_arr
        );
        let rendered = format_lake_trace_log_stdout(log_arr);
        assert!(
            rendered.starts_with("warning: WarnLib/Mod.lean:"),
            "formatted stdout must match Lake warning prefix: {rendered:?}"
        );

        fs::remove_dir_all(proj_dir.join(".lake/build"))?;
        let rep_cas = build_project_modules_native(
            &mut store,
            &proj_dir,
            &["WarnLib".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        assert_eq!(rep_cas.modules_cached, 1);
        let trace_val_cas: serde_json::Value = serde_json::from_slice(&fs::read(&trace_path)?)?;
        assert_eq!(
            trace_val_cas["log"], trace_val["log"],
            "CAS restore must preserve .trace log warnings"
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_lean_exe_target_links_binary_and_restores_from_module_full_cas() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("lean_exe_link_cas");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("App"))?;
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_proj\"\nbinDir = \"custom_bin\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n[[lean_exe]]\nname = \"my-cli\"\nexeName = \"my-cli-bin\"\nroot = \"App.Main\"\n",
        )?;
        fs::write(
            proj_dir.join("App/Helper.lean"),
            "namespace App\ndef msg : String := \"hello-exe-cas\"\nend App\n",
        )?;
        fs::write(
            proj_dir.join("App/Main.lean"),
            "import App.Helper\ndef main : IO Unit := IO.println App.msg\n",
        )?;

        let cfg = resolve_project_config_with_trust(&proj_dir, false)?;
        let dag_exe = build_module_dag_with_trust(&cfg, &["my-cli".to_string()], false)?;
        assert!(
            dag_exe.nodes.get("App.Helper").expect("App.Helper").needs_c,
            "transitive dependency of lean_exe must set needs_c = true"
        );

        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        let untrusted_err = crate::lake_build::run_build_command(
            &mut store,
            false,
            vec!["my-cli:exe".to_string()],
            proj_dir.clone(),
            "untrusted".to_string(),
            1,
            true,
        )
        .expect_err("untrusted :exe target must fail closed");
        assert!(untrusted_err
            .to_string()
            .contains("Unsupported target facet `:exe`"));

        crate::lake_build::run_build_command(
            &mut store,
            false,
            vec!["my-cli".to_string()],
            proj_dir.clone(),
            "trusted".to_string(),
            1,
            true,
        )?;
        let bin_path = proj_dir.join(".lake/build/custom_bin/my-cli-bin");
        assert!(
            bin_path.is_file(),
            "linked executable must exist at custom binDir/exeName: {}",
            bin_path.display()
        );
        let out1 = std::process::Command::new(&bin_path).output()?;
        assert!(out1.status.success());
        assert_eq!(
            String::from_utf8_lossy(&out1.stdout).trim(),
            "hello-exe-cas"
        );

        fs::remove_dir_all(proj_dir.join(".lake/build"))?;
        assert!(!bin_path.exists());
        crate::lake_build::run_build_command(
            &mut store,
            false,
            vec!["my-cli".to_string()],
            proj_dir.clone(),
            "trusted".to_string(),
            1,
            true,
        )?;
        assert!(
            bin_path.is_file(),
            "module_full CAS hit must materialize executable at {}",
            bin_path.display()
        );
        let out2 = std::process::Command::new(&bin_path).output()?;
        assert!(out2.status.success());
        assert_eq!(
            String::from_utf8_lossy(&out2.stdout).trim(),
            "hello-exe-cas"
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_audited_store_shortcut_skips_redundant_audit_and_invalidates_on_policy_change(
    ) -> Result<()> {
        let _env_guard = native_build_env_guard();
        let _jobs = ScopedEnvVar::set("TURBO_LEAN_JOBS", "2");
        let dir = make_temp_test_dir("audited_store_shortcut");
        let proj_dir = dir.join("proj");
        fs::create_dir_all(proj_dir.join("FastAud"))?;
        fs::write(
            proj_dir.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"fastaud\"\ndefaultTargets = [\"FastAud\"]\n[[lean_lib]]\nname = \"FastAud\"\nglobs = [\"FastAud.+\"]\n",
        )?;
        fs::write(
            proj_dir.join("FastAud/A.lean"),
            "theorem thm_a : True := trivial\n",
        )?;
        fs::write(
            proj_dir.join("FastAud/B.lean"),
            "import FastAud.A\ntheorem thm_b : True := thm_a\n",
        )?;

        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        // Cold build: compiles A and B, runs `--audit-modules`, and records HMAC-authenticated
        // `kernel_audited_oleans_auth` rows in `store`.
        let trace1 = ScopedSchedulerTrace::start(None);
        let rep1 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let ev1 = trace1.take_events();
        assert_eq!(rep1.modules_compiled, 2);
        assert!(
            ev1.iter().any(|e| e.kind == "audit_subprocess_start"),
            "cold build must execute Zygote `--audit-modules` subprocess"
        );

        // Second build after wiping `.lake/build`: CAS restores A and B, and the authenticated
        // `kernel_audited_oleans_auth` fast path skips spawning `--audit-modules` subprocesses.
        fs::remove_dir_all(proj_dir.join(".lake/build"))?;
        let trace2 = ScopedSchedulerTrace::start(None);
        let rep2 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let ev2 = trace2.take_events();
        assert_eq!(rep2.modules_cached, 2);
        assert!(
            !ev2.iter().any(|e| e.kind == "audit_subprocess_start"),
            "CAS restore with valid `kernel_audited_oleans_auth` MAC must skip `--audit-modules` subprocess, got: {ev2:?}"
        );

        // Changing `TURBO_LEAN_ALLOWED_CSIMP` mutates `policy_digest` without changing the module
        // CAS key, invalidating `kernel_audited_oleans_auth` and forcing `--audit-modules` to run.
        fs::remove_dir_all(proj_dir.join(".lake/build"))?;
        let _csimp = ScopedEnvVar::set("TURBO_LEAN_ALLOWED_CSIMP", "FastAud.custom_csimp");
        let trace3 = ScopedSchedulerTrace::start(None);
        let rep3 = build_project_modules_native(
            &mut store,
            &proj_dir,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let ev3 = trace3.take_events();
        assert_eq!(rep3.modules_cached, 2);
        assert!(
            ev3.iter().any(|e| e.kind == "audit_subprocess_start"),
            "policy_digest change must invalidate `kernel_audited_oleans_auth` shortcut and re-audit"
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_git_pinned_extern_lib_dep_mixed_manifest_stays_fresh_for_check() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("git_extern_lib_mixed_manifest");
        let dep_origin = dir.join("dep_origin");
        let proj = dir.join("proj");
        let dep = proj.join(".lake/packages/dep_sys");
        fs::create_dir_all(dep_origin.join("DepSys"))?;
        fs::create_dir_all(dep_origin.join("c"))?;
        fs::create_dir_all(proj.join("App"))?;
        let tc = "leanprover/lean4:v4.35.0\n";
        fs::write(dep_origin.join("lean-toolchain"), tc)?;
        fs::write(proj.join("lean-toolchain"), tc)?;
        fs::write(
            dep_origin.join("c/shim.c"),
            "int dep_sys_shim_val(void) { return 42; }\n",
        )?;
        fs::write(
            dep_origin.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\nopen System (FilePath)\npackage «dep_sys»\ntarget shim_o pkg : FilePath := do\n  let oFile := pkg.buildDir / \"c\" / \"shim.o\"\n  let srcJob ← inputTextFile <| pkg.dir / \"c\" / \"shim.c\"\n  buildO oFile srcJob #[] #[\"-O2\", \"-fPIC\"] \"cc\"\nextern_lib libdep_sys_shim pkg := do\n  let o ← shim_o.fetch\n  buildStaticLib (pkg.staticLibDir / nameToStaticLib \"dep_sys_shim\") #[o]\n@[default_target]\nlean_lib «DepSys» where\n  roots := #[`DepSys]\n  precompileModules := false\n",
        )?;
        fs::write(
            dep_origin.join("DepSys/Pure.lean"),
            "def pureVal : Nat := 7\n",
        )?;
        fs::write(
            dep_origin.join("DepSys/Ffi.lean"),
            "import DepSys.Pure\ndef ffiHelper : Nat := pureVal + 1\n",
        )?;
        fs::write(
            dep_origin.join("DepSys.lean"),
            "import DepSys.Pure\nimport DepSys.Ffi\n",
        )?;
        let git_bin = std::env::var_os("TURBO_LEAN_GIT")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("git"));
        for args in [
            vec!["init"],
            vec!["config", "user.email", "t@e.com"],
            vec!["config", "user.name", "T"],
            vec!["add", "."],
            vec!["commit", "-m", "init"],
        ] {
            let st = Command::new(&git_bin)
                .args(&args)
                .current_dir(&dep_origin)
                .status()?;
            anyhow::ensure!(st.success(), "git init dep_origin failed on {args:?}");
        }
        let rev_out = Command::new(&git_bin)
            .args(["rev-parse", "HEAD"])
            .current_dir(&dep_origin)
            .output()?;
        anyhow::ensure!(rev_out.status.success());
        let rev = String::from_utf8(rev_out.stdout)?.trim().to_string();
        fs::create_dir_all(dep.parent().unwrap())?;
        let clone_st = Command::new(&git_bin)
            .args(["clone", "--quiet"])
            .arg(&dep_origin)
            .arg(&dep)
            .status()?;
        anyhow::ensure!(clone_st.success(), "git clone dep_origin failed");
        fs::write(
            proj.join("lakefile.lean"),
            format!(
                "import Lake\nopen Lake DSL\npackage «app»\nrequire «dep_sys» from git {:?} @ {:?}\n@[default_target]\nlean_lib «App» where\n  globs := #[.submodules `App]\n@[default_target]\nlean_exe «app-exe» where\n  root := `App.Exe\n  supportInterpreter := false\n",
                dep_origin.to_string_lossy(),
                rev
            ),
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            serde_json::json!({
                "version": "1.1.0",
                "packagesDir": ".lake/packages",
                "packages": [{
                    "type": "git",
                    "scope": "",
                    "name": "dep_sys",
                    "manifestFile": "lake-manifest.json",
                    "rev": rev,
                    "inherited": false,
                    "configFile": "lakefile.lean",
                    "inputRev": rev,
                    "url": dep_origin.to_string_lossy()
                }]
            })
            .to_string(),
        )?;
        fs::write(
            proj.join("App/SpecMod.lean"),
            "import DepSys.Pure\ntheorem spec_ok : pureVal = 7 := rfl\n",
        )?;
        fs::write(
            proj.join("App/Exe.lean"),
            "import DepSys.Ffi\ndef main : IO Unit := IO.println s!\"{ffiHelper}\"\n",
        )?;

        fs::write(
            proj.join("App/TopMod.lean"),
            "import App.SpecMod\ntheorem top_ok : pureVal = 7 := spec_ok\n",
        )?;

        let cfg = resolve_project_config(&proj)?;
        let lake_bin = cfg.lean_bin.parent().expect("lean bin parent").join("lake");
        let lake_st = Command::new(&lake_bin)
            .arg("build")
            .current_dir(&proj)
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .status()?;
        anyhow::ensure!(lake_st.success(), "initial stock lake build failed");

        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        // Force `DepSys.Ffi` (needed for C link by `app-exe`) to be compiled into `dep_sys`'s
        // `.turbo_verified_sources.json` while `DepSys.Pure` remains a stock Lake prebuilt artifact,
        // and leave a `.c` file on disk for `App.SpecMod` before stock `lake build +App.SpecMod`.
        let _ = fs::remove_file(dep.join(".lake/build/ir/DepSys/Ffi.c"));
        build_project_modules_native(&mut store, &proj, &[], "trusted", 2, false, true, None)?;
        assert!(dep
            .join(".lake/build/.turbo_verified_sources.json")
            .is_file());

        // Stage and publish the no-`:c` action outputs (`App.SpecMod.trace` has `"outputs": null`),
        // then emit `:c` so `.lake/build/ir/App/SpecMod.c` (+ `.c.hash`) exist on disk, then
        // materialize the cached no-`:c` outputs back into the worktree and verify directory `check`.
        let (staged_no_c, staged_reg_blobs) =
            crate::lake_build::stage_lake_build_outputs(&store, &proj)?;
        store.publish_ingested_worktree_action(
            None,
            "test_no_c_action_key",
            &cfg.lean_githash,
            "module_full",
            &proj,
            "app",
            &staged_reg_blobs,
            &staged_no_c,
            1,
            "trusted",
            2,
            None,
            None,
        )?;
        build_project_modules_native(
            &mut store,
            &proj,
            &["App:c".to_string()],
            "trusted",
            2,
            false,
            true,
            None,
        )?;
        assert!(proj.join(".lake/build/ir/App/SpecMod.c").is_file());
        store.materialize_into_worktree(&proj, "app", &staged_no_c)?;
        assert!(!proj.join(".lake/build/ir/App/SpecMod.c").exists());
        assert!(!proj.join(".lake/build/ir/App/SpecMod.c.hash").exists());

        let chk = crate::check::evaluate_check_command_value(
            &mut store,
            proj.join("App/SpecMod.lean"),
            Some("spec_ok".to_string()),
            proj.clone(),
        )?;
        assert_eq!(chk["status"], "theorem_verified");
        let dir_chk = crate::check::evaluate_check_command_value(
            &mut store,
            proj.join("App"),
            None,
            proj.clone(),
        )?;
        assert_eq!(dir_chk["status"], "file_verified");

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_dep_manifest_stat_fingerprint_is_age_gated_against_subsecond_rewrite() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("dep_stat_fp_age_gate");
        let proj_dir = dir.join("proj");
        let dep_dir = proj_dir.join(".lake/packages/dep_pkg");
        fs::create_dir_all(dep_dir.join("DepPkg")).unwrap();
        fs::create_dir_all(proj_dir.join("App")).unwrap();
        for d in [&proj_dir, &dep_dir] {
            fs::write(d.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
        }
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepPkg\"\nglobs = [\"DepPkg.+\"]\n",
        )
        .unwrap();
        fs::write(dep_dir.join("DepPkg/A.lean"), "def depA : Nat := 11\n").unwrap();
        fs::write(
            proj_dir.join("lake-manifest.json"),
            r#"{"version": "1.2.0", "packagesDir": ".lake/packages", "packages": [{"type": "path", "name": "dep_pkg", "dir": ".lake/packages/dep_pkg", "configFile": "lakefile.toml", "inherited": false}], "name": "app_pkg", "lakeDir": ".lake", "fixedToolchain": false}"#,
        )
        .unwrap();
        fs::write(
            proj_dir.join("lakefile.toml"),
            "name = \"app_pkg\"\ndefaultTargets = [\"App\"]\n[[lean_lib]]\nname = \"App\"\nglobs = [\"App.+\"]\n",
        )
        .unwrap();
        fs::write(
            proj_dir.join("App/Main.lean"),
            "import DepPkg.A\ndef appMain : Nat := depA\n",
        )
        .unwrap();
        let mut store = TurboStore::open(Some(&dir.join(".turbo_store")))?;
        crate::zygote::digest_test_hooks::set_forced_ts_granularity_shared_ns(Some(100_000_000));
        let run = (|| -> Result<()> {
            build_project_modules_native(
                &mut store,
                &proj_dir,
                &[],
                "trusted-internal",
                1,
                false,
                true,
                None,
            )?;
            let dep_manifest_path = dep_dir.join(".lake/build/.turbo_verified_sources.json");
            let m0: VerifiedDepManifest = serde_json::from_slice(&fs::read(&dep_manifest_path)?)?;
            let e0 = &m0.modules["DepPkg/A.lean"];
            assert!(
                e0.artifact_stat_fingerprint.is_empty(),
                "freshly written dep `.olean` inside STAT_TRUST_WINDOW_NS must not persist stat fingerprint, got `{}`",
                e0.artifact_stat_fingerprint
            );
            let orig_dig = e0.olean_artifact_digest.clone();
            let dep_olean = dep_dir.join(".lake/build/lib/lean/DepPkg/A.olean");
            let clean_bytes = fs::read(&dep_olean)?;
            let mut tampered = clean_bytes.clone();
            let last = tampered.len() - 1;
            tampered[last] ^= 0x5a;
            {
                let mut f = fs::OpenOptions::new().write(true).open(&dep_olean)?;
                use std::io::Write;
                f.write_all(&tampered)?;
                f.flush()?;
            }
            let canon = proj_dir.canonicalize()?;
            let cfg = resolve_project_config(&canon)?;
            let memo = DepImportMemo::default();
            assert!(
                !import_pin_current(
                    &cfg,
                    &memo,
                    "DepPkg.A",
                    Some(ImportPinSpec {
                        full_pin: &orig_dig,
                        tier_pin: None,
                    }),
                ),
                "in-place sub-window dep `.olean` mutation must invalidate `import_pin_current`"
            );
            {
                let mut f = fs::OpenOptions::new().write(true).open(&dep_olean)?;
                use std::io::Write;
                f.write_all(&clean_bytes)?;
                f.flush()?;
            }
            hydrate_project_traces(&canon)?;
            let m_young: VerifiedDepManifest =
                serde_json::from_slice(&fs::read(&dep_manifest_path)?)?;
            assert!(
                m_young.modules["DepPkg/A.lean"]
                    .artifact_stat_fingerprint
                    .is_empty(),
                "`hydrate_project_traces` must also omit stat fingerprint while artifact is younger than STAT_TRUST_WINDOW_NS"
            );
            std::thread::sleep(std::time::Duration::from_millis(2200));
            hydrate_project_traces(&canon)?;
            let m_aged: VerifiedDepManifest =
                serde_json::from_slice(&fs::read(&dep_manifest_path)?)?;
            assert!(
                !m_aged.modules["DepPkg/A.lean"]
                    .artifact_stat_fingerprint
                    .is_empty(),
                "once dep `.olean` is older than STAT_TRUST_WINDOW_NS, `hydrate_project_traces` must record trusted stat fingerprint"
            );
            Ok(())
        })();
        crate::zygote::digest_test_hooks::clear();
        let _ = fs::remove_dir_all(&dir);
        run
    }

    #[test]
    fn test_native_scheduler_audit_authority_gated_on_ancestor_and_live_digest_acceptance(
    ) -> Result<()> {
        let _env_guard = native_build_env_guard();
        let _jobs = ScopedEnvVar::set("TURBO_LEAN_JOBS", "2");
        let _batch = ScopedEnvVar::set("TURBO_LEAN_AUDIT_BATCH_SIZE", "4");
        let dir = make_temp_test_dir("sched_audit_authority_gate");

        // Case 1: `Base` has a stale `sorryAx` `.olean` matching a tampered `.trace`, while `Child`
        // has a clean `.olean` whose `.trace` matches that `sorryAx` `Base`. Both enter the warm
        // audit batch together; `Base` fails `sorryAx` audit while `Child` passes its own slice,
        // `Base` falls back to clean compilation, and `Child` is invalidated & recompiled against
        // the new `Base`. The rejected `Child` warm candidate (`in_degree > 0`) MUST NEVER be
        // recorded in `TurboStore` as audited or replayed!
        let proj1 = dir.join("proj_anc");
        fs::create_dir_all(proj1.join("Anc"))?;
        fs::write(proj1.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            proj1.join("lakefile.toml"),
            "name = \"ancgate\"\ndefaultTargets = [\"Anc\"]\n[[lean_lib]]\nname = \"Anc\"\nglobs = [\"Anc.+\"]\n",
        )?;
        let sorry_base = "theorem anc_thm : True := by sorry\n";
        let clean_base = "theorem anc_thm : True := trivial\n";
        fs::write(proj1.join("Anc/Base.lean"), sorry_base)?;
        fs::write(
            proj1.join("Anc/Child.lean"),
            "import Anc.Base\ntheorem child_thm : True := anc_thm\n",
        )?;
        let out = Command::new("lake")
            .args(["build", "Anc.Base", "Anc.Child"])
            .env("LEAN_NUM_THREADS", "2")
            .current_dir(&proj1)
            .output()?;
        anyhow::ensure!(
            out.status.success(),
            "lake build failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        let stale_base_bytes = fs::read(proj1.join(".lake/build/lib/lean/Anc/Base.olean"))?;
        let stale_child_bytes = fs::read(proj1.join(".lake/build/lib/lean/Anc/Child.olean"))?;

        fs::write(proj1.join("Anc/Base.lean"), clean_base)?;
        let base_trace = proj1.join(".lake/build/lib/lean/Anc/Base.trace");
        let old_h = format!("{:016x}", lake_hash_text(sorry_base));
        let new_h = format!("{:016x}", lake_hash_text(clean_base));
        let patched = fs::read_to_string(&base_trace)?.replace(&old_h, &new_h);
        let mut tv: serde_json::Value = serde_json::from_str(&patched)?;
        tv["depHash"] =
            serde_json::Value::String(format!("{:016x}", lake_input_hash(&tv["inputs"])?));
        fs::write(&base_trace, serde_json::to_vec(&tv)?)?;

        let mut store1 = TurboStore::open(Some(&dir.join("store_anc")))?;
        let rep1 = build_project_modules_native(
            &mut store1,
            &proj1,
            &[],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        assert_eq!(
            rep1.compiled_modules,
            vec!["Anc.Base".to_string(), "Anc.Child".to_string()],
            "both Anc.Base and Anc.Child must be compiled cleanly after warm Base fails audit"
        );
        let cfg1 = resolve_project_config(&proj1)?;
        let (lp1, _) = build_lean_search_path(&cfg1, true);
        // Restore the stale `Base` + `Child` `.olean`s into an inspection copy and verify neither
        // holds audited or replayed authority in `store1`.
        fs::write(
            proj1.join(".lake/build/lib/lean/Anc/Base.olean"),
            &stale_base_bytes,
        )?;
        fs::write(
            proj1.join(".lake/build/lib/lean/Anc/Child.olean"),
            &stale_child_bytes,
        )?;
        let mut lookup1 = ReplayLookupBatchCache::new(&store1, &cfg1, &lp1);
        assert!(
            !lookup1.is_audited_in_store(
                &store1,
                &cfg1,
                &lp1,
                "Anc.Child",
                &proj1.join(".lake/build/lib/lean/Anc/Child.olean")
            ),
            "unaccepted warm Child (`in_degree > 0` whose ancestor failed audit) must NEVER receive audited authority"
        );
        assert!(
            !lookup1.is_replayed_in_store(
                &store1,
                &cfg1,
                &lp1,
                &proj1.join(".lake/build/lib/lean/Anc/Child.olean")
            ),
            "unaccepted warm Child (`in_degree > 0` whose ancestor failed audit) must NEVER receive replayed authority"
        );

        // Case 2: Swap live `.olean` on disk to `sorryAx` during `sched_audit_after_chunk` in
        // `build_project_modules_native`. The build MUST fail closed (`post_audit_dig != dig`) and
        // MUST NOT record authority in `TurboStore`.
        let proj2 = dir.join("proj_swap");
        fs::create_dir_all(proj2.join("Sw"))?;
        fs::write(proj2.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            proj2.join("lakefile.toml"),
            "name = \"swsched\"\ndefaultTargets = [\"Sw\"]\n[[lean_lib]]\nname = \"Sw\"\nroots = [\"Sw.Leaf\"]\n",
        )?;
        fs::write(
            proj2.join("Sw/Leaf.lean"),
            "theorem sw_thm : 1 = 2 := by sorry\n",
        )?;
        let out_bad = Command::new("lake")
            .args(["build", "Sw.Leaf"])
            .env("LEAN_NUM_THREADS", "2")
            .current_dir(&proj2)
            .output()?;
        anyhow::ensure!(out_bad.status.success(), "lake build sorry Sw.Leaf failed");
        let sorry_leaf_bytes = fs::read(proj2.join(".lake/build/lib/lean/Sw/Leaf.olean"))?;
        let _ = fs::remove_dir_all(proj2.join(".lake/build"));
        fs::write(
            proj2.join("Sw/Leaf.lean"),
            "theorem sw_thm : True := trivial\n",
        )?;

        let swap_target = proj2.join(".lake/build/lib/lean/Sw/Leaf.olean");
        let bad_copy = sorry_leaf_bytes.clone();
        let swap_hook: std::sync::Arc<NativeSchedulerTestHook> =
            std::sync::Arc::new(move |kind: &str, mods: &[String]| {
                if kind == "audit_subprocess_end"
                    && mods.iter().any(|m| m == "Sw.Leaf")
                    && swap_target.is_file()
                {
                    let _ = fs::write(&swap_target, &bad_copy);
                }
            });
        let mut store2 = TurboStore::open(Some(&dir.join("store_swap")))?;
        let _trace2 = ScopedSchedulerTrace::start(Some(swap_hook));
        let build_res =
            build_project_modules_native(&mut store2, &proj2, &[], "trusted", 1, false, true, None);
        let err2 = build_res
            .expect_err("live `.olean` swap during native scheduler audit must fail closed");
        assert!(
            err2.to_string()
                .contains("mutated during `.olean` kernel audit"),
            "expected artifact mutation error, got: {err2:#}"
        );
        let cfg2 = resolve_project_config(&proj2)?;
        let (lp2, _) = build_lean_search_path(&cfg2, true);
        fs::create_dir_all(proj2.join(".lake/build/lib/lean/Sw"))?;
        fs::write(
            proj2.join(".lake/build/lib/lean/Sw/Leaf.olean"),
            &sorry_leaf_bytes,
        )?;
        let mut lookup2 = ReplayLookupBatchCache::new(&store2, &cfg2, &lp2);
        assert!(
            !lookup2.is_audited_in_store(
                &store2,
                &cfg2,
                &lp2,
                "Sw.Leaf",
                &proj2.join(".lake/build/lib/lean/Sw/Leaf.olean")
            ),
            "swapped sorryAx Leaf.olean must never receive audited authority"
        );

        crate::zygote::purge_snapshot_dir(&dir);
        Ok(())
    }

    #[test]
    fn test_record_verified_dep_source_preserves_manifest_when_workspace_lake_inputs_present(
    ) -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_rec_ver_src_ws_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let proj = dir.join("proj");
        fs::create_dir_all(proj.join("Pkg"))?;
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(proj.join("spec.json"), "{\"v\":1}\n")?;
        fs::write(
            proj.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage recws\ninput_file specFile where\n  path := \"spec.json\"\n@[default_target]\nlean_lib Pkg where\n  roots := #[`Pkg.Mod]\n  needs := #[specFile]\n",
        )?;
        fs::write(
            proj.join("Pkg/Mod.lean"),
            "def pkgVal : Nat := 42\ntheorem pkg_thm : pkgVal = 42 := rfl\n",
        )?;
        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        build_project_modules_native(&mut store, &proj, &[], "trusted", 1, false, true, None)?;
        let manifest_path = proj.join(".lake/build/.turbo_verified_sources.json");
        assert!(
            manifest_path.is_file(),
            "native build must write .turbo_verified_sources.json"
        );
        let cfg = resolve_project_config(&proj)?;
        let expected_ws_inputs = workspace_lake_inputs_digest(&cfg)?;
        assert!(
            !expected_ws_inputs.is_empty(),
            "workspace_lake_inputs_digest must be non-empty when input_file is declared"
        );
        let dag = build_module_dag(&cfg, &[])?;
        let node = dag.nodes.get("Pkg.Mod").expect("Pkg.Mod node");
        let art_dig = compute_olean_artifact_set_digest(&node.olean_path)?;
        let mut olean_digs = HashMap::new();
        olean_digs.insert("Pkg.Mod".to_string(), art_dig.clone());
        let mut tier_digs = HashMap::new();
        tier_digs.insert(
            "Pkg.Mod".to_string(),
            compute_module_artifact_tier_digests_with_policy(&node.olean_path, false)?,
        );
        record_verified_dep_source(&cfg, &dag, node, &art_dig, true, &olean_digs, &tier_digs);
        assert!(
            manifest_path.is_file(),
            "record_verified_dep_source must preserve .turbo_verified_sources.json rather than deleting it"
        );
        let parsed: serde_json::Value = serde_json::from_slice(&fs::read(&manifest_path)?)?;
        assert_eq!(
            parsed["lake_inputs_digest"].as_str(),
            Some(expected_ws_inputs.as_str()),
            "manifest must retain non-empty lake_inputs_digest: {parsed}"
        );
        assert_eq!(
            parsed["modules"]["Pkg/Mod.lean"]["lake_inputs_digest"].as_str(),
            Some(expected_ws_inputs.as_str()),
            "module entry must retain non-empty lake_inputs_digest: {parsed}"
        );
        crate::zygote::purge_snapshot_dir(&dir);
        Ok(())
    }

    #[test]
    fn test_scheduler_fast_store_hit_rejects_live_olean_swap_and_recompiles() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_sched_fast_store_swap_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let proj = dir.join("proj");
        fs::create_dir_all(proj.join("Fs"))?;
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"fsstore\"\ndefaultTargets = [\"Fs\"]\n[[lean_lib]]\nname = \"Fs\"\nroots = [\"Fs.Mod\"]\n",
        )?;
        fs::write(
            proj.join("Fs/Mod.lean"),
            "theorem fs_ok : 1 = 2 := by sorry\n",
        )?;
        let bad_out = Command::new("lake")
            .args(["build", "Fs.Mod"])
            .env("LEAN_NUM_THREADS", "2")
            .current_dir(&proj)
            .output()?;
        anyhow::ensure!(bad_out.status.success(), "lake build sorry Fs.Mod failed");
        let sorry_bytes = fs::read(proj.join(".lake/build/lib/lean/Fs/Mod.olean"))?;

        let _ = fs::remove_dir_all(proj.join(".lake/build"));
        fs::write(proj.join("Fs/Mod.lean"), "theorem fs_ok : 1 = 1 := rfl\n")?;
        let clean_out = Command::new("lake")
            .args(["build", "Fs.Mod"])
            .env("LEAN_NUM_THREADS", "2")
            .current_dir(&proj)
            .output()?;
        anyhow::ensure!(clean_out.status.success(), "lake build clean Fs.Mod failed");
        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        {
            // Seed audited authority for the clean Lake-built `.olean` in `store` WITHOUT
            // writing a `build_module` CAS action entry, so `build_project_modules_native` takes
            // the `WarmAdopted` + `audit_fast_store_hit` path!
            let cfg0 = resolve_project_config(&proj)?;
            let (lp0, _) = build_lean_search_path(&cfg0, true);
            crate::zygote::audit_compiled_modules_with_zygote(
                &store,
                &cfg0,
                &["Fs.Mod".to_string()],
                &lp0,
                &[],
                false,
            )?;
        }

        // Overwrite `Mod.olean` with `sorry_bytes` AFTER `WarmAdopted` records the clean digest
        // (`warm_adopted` scheduler trace event) — before `audit_fast_store_hit` inspects `store`.
        // The scheduler must reject the swapped `.olean`, fall back to clean compilation, and
        // never grant authority to `sorry_bytes`!
        let target_olean = proj.join(".lake/build/lib/lean/Fs/Mod.olean");
        let bad_copy = sorry_bytes.clone();
        let hook: std::sync::Arc<NativeSchedulerTestHook> =
            std::sync::Arc::new(move |kind: &str, mods: &[String]| {
                if kind == "warm_adopted" && mods.iter().any(|m| m == "Fs.Mod") {
                    let _ = fs::write(&target_olean, &bad_copy);
                }
            });
        let _trace = ScopedSchedulerTrace::start(Some(hook));
        let rep2 =
            build_project_modules_native(&mut store, &proj, &[], "trusted", 1, false, true, None)?;
        assert_eq!(
            rep2.compiled_modules,
            vec!["Fs.Mod".to_string()],
            "swapped warm .olean must fail audit/fast-store check and recompile cleanly"
        );
        let cfg = resolve_project_config(&proj)?;
        let (lp, _) = build_lean_search_path(&cfg, true);
        fs::write(proj.join(".lake/build/lib/lean/Fs/Mod.olean"), &sorry_bytes)?;
        let mut lookup = ReplayLookupBatchCache::new(&store, &cfg, &lp);
        assert!(
            !lookup.is_audited_in_store(
                &store,
                &cfg,
                &lp,
                "Fs.Mod",
                &proj.join(".lake/build/lib/lean/Fs/Mod.olean")
            ),
            "swapped sorry Fs/Mod.olean must never receive audited authority"
        );
        crate::zygote::purge_snapshot_dir(&dir);
        Ok(())
    }

    #[test]
    fn replay_lookup_batch_cache_revalidates_mutated_transitive_dependency_and_shadowing(
    ) -> Result<()> {
        if Command::new("lean").arg("--version").output().is_err()
            || Command::new("lake").arg("--version").output().is_err()
        {
            return Ok(());
        }
        let _env_guard = native_build_env_guard();
        let _bwrap_guard = BWRAP_TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_replay_batch_dep_reval_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let proj = dir.join("proj");
        let extra = dir.join("extra_lib");
        fs::create_dir_all(proj.join("Rb"))?;
        fs::create_dir_all(&extra)?;
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"rbbatch\"\ndefaultTargets = [\"Rb\"]\n[[lean_lib]]\nname = \"Rb\"\nroots = [\"Leaf\", \"Rb.Mid\", \"Rb.Top\", \"Rb.Parent\"]\n",
        )?;
        fs::write(proj.join("Leaf.lean"), "def leafVal : Nat := 1\n")?;
        fs::write(
            proj.join("Rb/Mid.lean"),
            "import Leaf\ndef midVal : Nat := leafVal\n",
        )?;
        fs::write(
            proj.join("Rb/Top.lean"),
            "import Rb.Mid\ntheorem top_ok : midVal = 1 := rfl\n",
        )?;
        fs::write(
            proj.join("Rb/Parent.lean"),
            "import Rb.Mid\ntheorem parent_ok : midVal = 1 := rfl\n",
        )?;
        let out1 = Command::new("lake")
            .args(["build", "Rb"])
            .env("LEAN_NUM_THREADS", "2")
            .current_dir(&proj)
            .output()?;
        anyhow::ensure!(out1.status.success(), "lake build Rb v1 failed");

        let store = TurboStore::open(Some(&dir.join("store")))?;
        let cfg = resolve_project_config(&proj)?;
        let (base_lp, _) = build_lean_search_path(&cfg, true);
        let lp = format!("{}:{base_lp}", extra.display());
        crate::zygote::audit_compiled_modules_with_zygote(
            &store,
            &cfg,
            &[
                "Leaf".to_string(),
                "Rb.Mid".to_string(),
                "Rb.Top".to_string(),
                "Rb.Parent".to_string(),
            ],
            &lp,
            &[],
            false,
        )?;
        let leaf_olean = proj.join(".lake/build/lib/lean/Leaf.olean");
        let mid_olean = proj.join(".lake/build/lib/lean/Rb/Mid.olean");
        let top_olean = proj.join(".lake/build/lib/lean/Rb/Top.olean");
        let parent_olean = proj.join(".lake/build/lib/lean/Rb/Parent.olean");
        let leaf_v1 = fs::read(&leaf_olean)?;
        let top_v1 = fs::read(&top_olean)?;
        let mid_v1 = fs::read(&mid_olean)?;
        let parent_v1 = fs::read(&parent_olean)?;

        // Seed `lookup` with `Mid` and `Top` (leaving `Parent` unseen so traversing `Parent`
        // enters DFS without top-level `invalidate_memo()`!).
        let mut lookup = ReplayLookupBatchCache::new(&store, &cfg, &lp);
        assert!(lookup.is_audited_in_store(&store, &cfg, &lp, "Rb.Mid", &mid_olean));
        assert!(lookup.is_audited_in_store(&store, &cfg, &lp, "Rb.Top", &top_olean));
        let fast_auth = lookup
            .verify_audited_in_store_authority(
                &store,
                &cfg,
                "Rb.Top",
                &top_olean,
                true,
                "dig-v1".to_string(),
            )
            .expect("fast-store authority snapshot");
        assert!(lookup.verify_fast_store_authority(&fast_auth));

        // Rebuild `Leaf` with a changed definition while restoring `Mid`, `Top`, and `Parent`
        // `.olean` bytes untouched on disk.
        fs::write(proj.join("Leaf.lean"), "def leafVal : Nat := 2\n")?;
        let out2 = Command::new("lake")
            .args(["build", "Leaf"])
            .env("LEAN_NUM_THREADS", "2")
            .current_dir(&proj)
            .output()?;
        anyhow::ensure!(out2.status.success(), "lake build Leaf v2 failed");
        let leaf_v2 = fs::read(&leaf_olean)?;
        fs::write(&mid_olean, &mid_v1)?;
        fs::write(&top_olean, &top_v1)?;
        fs::write(&parent_olean, &parent_v1)?;

        // First query previously-unseen `Rb.Parent`: DFS refreshes `Rb.Mid`'s closure internally
        // without calling `invalidate_memo()`. A subsequent query on `Rb.Mid` MUST NOT reuse
        // `Rb.Mid`'s stale pre-refresh `env_memo` generation!
        assert!(
            !lookup.is_audited_in_store(&store, &cfg, &lp, "Rb.Parent", &parent_olean),
            "unseen parent Rb.Parent must reject stale transitive Leaf"
        );
        assert!(
            !lookup.is_audited_in_store(&store, &cfg, &lp, "Rb.Mid", &mid_olean),
            "child Rb.Mid refreshed during unseen parent DFS must not reuse stale env_memo"
        );
        assert!(
            !lookup.is_audited_in_store(&store, &cfg, &lp, "Rb.Top", &top_olean),
            "mutated transitive dependency Leaf must invalidate memoized Rb.Top audit lookup"
        );
        assert!(
            !lookup.verify_fast_store_authority(&fast_auth),
            "mutated transitive dependency Leaf must invalidate FastStore authority"
        );

        // Restore v1 `Leaf.olean`, re-populate memo, then place v2 `Leaf.olean` in higher-precedence
        // search-path directory `extra` without touching `proj/.lake/build/lib/lean/Leaf.olean`.
        fs::write(&leaf_olean, &leaf_v1)?;
        assert!(lookup.is_audited_in_store(&store, &cfg, &lp, "Rb.Top", &top_olean));
        let fast_auth_v1 = lookup
            .verify_audited_in_store_authority(
                &store,
                &cfg,
                "Rb.Top",
                &top_olean,
                true,
                "dig-v1".to_string(),
            )
            .expect("fast-store authority v1");
        fs::write(extra.join("Leaf.olean"), &leaf_v2)?;
        assert_eq!(
            lookup.resolve_module_olean("Leaf"),
            Some(extra.join("Leaf.olean")),
            "resolve_module_olean must observe newly created shadowing file along LEAN_PATH"
        );
        assert!(
            !lookup.is_audited_in_store(&store, &cfg, &lp, "Rb.Top", &top_olean),
            "shadowing transitive dependency along LEAN_PATH must invalidate memoized audit lookup"
        );
        assert!(
            !lookup.verify_fast_store_authority(&fast_auth_v1),
            "shadowing transitive dependency along LEAN_PATH must invalidate FastStore authority"
        );

        // Remove `extra/Leaf.olean`, re-populate memo & authority for `Rb.Top` (which imports `Rb.Mid`),
        // then create an empty higher-precedence package directory `extra/Rb/` (without `Mid.olean`).
        // Lean's `findOLean` selects `extra` as the package root for `Rb.*` and fails to resolve `Rb.Mid`,
        // so both `resolve_module_olean("Rb.Mid")`, `is_audited_in_store`, and `verify_fast_store_authority`
        // MUST reject the cached authority!
        fs::remove_file(extra.join("Leaf.olean"))?;
        assert!(lookup.is_audited_in_store(&store, &cfg, &lp, "Rb.Top", &top_olean));
        let fast_auth_pkg = lookup
            .verify_audited_in_store_authority(
                &store,
                &cfg,
                "Rb.Top",
                &top_olean,
                true,
                "dig-v1".to_string(),
            )
            .expect("fast-store authority before package-directory shadowing");
        fs::create_dir_all(extra.join("Rb"))?;
        assert_eq!(
            lookup.resolve_module_olean("Rb.Mid"),
            None,
            "empty higher-precedence package directory `extra/Rb/` must shadow `Rb.Mid` per Lean findOLean"
        );
        assert!(
            !lookup.is_audited_in_store(&store, &cfg, &lp, "Rb.Top", &top_olean),
            "package-directory shadowing of `Rb/` without `Mid.olean` must invalidate memoized audit lookup"
        );
        assert!(
            !lookup.verify_fast_store_authority(&fast_auth_pkg),
            "package-directory shadowing of `Rb/` without `Mid.olean` must invalidate FastStore authority"
        );

        crate::zygote::purge_snapshot_dir(&dir);
        Ok(())
    }

    #[test]
    fn test_proofwidgets_style_dep_lakefile_and_inputless_leantar_trace_verified() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_pw_leantar_trace_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir)?;
        let root = dir.as_path();
        fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.31.0\n")?;
        fs::write(
            root.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage app where\n@[default_target]\nlean_lib App where\n",
        )?;
        fs::write(
            root.join("App.lean"),
            "prelude\nimport PwDep\nimport ProofWidgets\ndef x : Nat := pwVal + pwHelper\n",
        )?;

        let pw_dir = root.join(".lake/packages/proofwidgets");
        fs::create_dir_all(pw_dir.join("widget/js"))?;
        fs::write(pw_dir.join("widget/js/hello.tsx"), "export default {}\n")?;
        fs::write(
            pw_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL System\npackage ProofWidgets where\n  preferReleaseBuild := true\ndef widgetDir : FilePath := \"widget\"\ninput_dir widgetJsAllTs where\n  path := widgetDir / \"js\"\n  filter := .extension <| .mem #[\"ts\", \"tsx\"]\ntarget widgetJsAll pkg : Unit := do\n  return .nil\ntarget widgetJsAllDev pkg : Unit := do\n  return .nil\n@[default_target]\nlean_lib ProofWidgets where\n  needs := #[widgetJsAll]\n",
        )?;
        fs::write(
            pw_dir.join("ProofWidgets.lean"),
            "prelude\nunsafe def pwFast : Nat := 1\n@[implemented_by pwFast]\ndef pwHelper : Nat := 1\n",
        )?;

        let dep_dir = root.join(".lake/packages/pwdep");
        fs::create_dir_all(&dep_dir)?;
        fs::write(dep_dir.join(".gitignore"), "/.lake/\n")?;
        fs::write(
            dep_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage PwDep where\n@[default_target]\nlean_lib PwDep where\n",
        )?;
        let dep_src = "prelude\ndef pwVal : Nat := 42\n";
        fs::write(dep_dir.join("PwDep.lean"), dep_src)?;

        let mut git_init_dep = crate::trusted_tools::git(root)?;
        assert!(git_init_dep
            .args(["init", "-q"])
            .arg(&dep_dir)
            .status()?
            .success());
        let mut git_add_dep = crate::trusted_tools::git(&dep_dir)?;
        assert!(git_add_dep
            .args(["-C"])
            .arg(&dep_dir)
            .args(["add", "."])
            .status()?
            .success());
        let mut git_commit_dep = crate::trusted_tools::git(&dep_dir)?;
        assert!(git_commit_dep
            .args([
                "-C",
                &dep_dir.to_string_lossy(),
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@e",
                "-c",
                "commit.gpgsign=false",
                "commit",
                "-qm",
                "init",
            ])
            .status()?
            .success());
        let mut git_rev_dep = crate::trusted_tools::git(&dep_dir)?;
        let pwdep_rev = String::from_utf8(
            git_rev_dep
                .args(["-C"])
                .arg(&dep_dir)
                .args(["rev-parse", "HEAD"])
                .output()?
                .stdout,
        )?
        .trim()
        .to_string();

        let mut git_init = crate::trusted_tools::git(root)?;
        assert!(git_init
            .args(["init", "-q"])
            .arg(&pw_dir)
            .status()?
            .success());
        let mut git_add = crate::trusted_tools::git(&pw_dir)?;
        assert!(git_add
            .args(["-C"])
            .arg(&pw_dir)
            .args(["add", "."])
            .status()?
            .success());
        let mut git_commit = crate::trusted_tools::git(&pw_dir)?;
        assert!(git_commit
            .args([
                "-C",
                &pw_dir.to_string_lossy(),
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@e",
                "-c",
                "commit.gpgsign=false",
                "commit",
                "-qm",
                "init",
            ])
            .status()?
            .success());
        let mut git_rev = crate::trusted_tools::git(&pw_dir)?;
        let pw_rev = String::from_utf8(
            git_rev
                .args(["-C"])
                .arg(&pw_dir)
                .args(["rev-parse", "HEAD"])
                .output()?
                .stdout,
        )?
        .trim()
        .to_string();

        fs::write(
            root.join("lake-manifest.json"),
            serde_json::to_string_pretty(&serde_json::json!({
                "version": "1.1.0",
                "packagesDir": ".lake/packages",
                "packages": [
                    {
                        "type": "git",
                        "name": "proofwidgets",
                        "rev": pw_rev,
                        "url": "https://example.invalid/ProofWidgets4",
                        "inherited": false,
                        "configFile": "lakefile.lean"
                    },
                    {
                        "type": "git",
                        "name": "pwdep",
                        "rev": pwdep_rev,
                        "url": "https://example.invalid/pwdep",
                        "inherited": false,
                        "configFile": "lakefile.lean"
                    }
                ]
            }))?,
        )?;

        let mut cfg = resolve_project_config_with_trust(root, false)?;
        let fake_githash = "0123456789abcdef0123456789abcdef01234567";
        cfg.lean_githash = fake_githash.to_string();
        cfg.lean_bin = PathBuf::from("/bin/true");
        cfg.toolchain_lib_lean = PathBuf::new();

        let pw_pkg = cfg
            .dep_pkgs
            .iter()
            .find(|p| p.name == "ProofWidgets")
            .expect("ProofWidgets parsed")
            .clone();
        assert_eq!(pw_pkg.base_name, "proofwidgets");
        assert_eq!(pw_pkg.inputs.len(), 1);
        assert_eq!(
            pw_pkg.custom_targets,
            vec!["widgetJsAll".to_string(), "widgetJsAllDev".to_string()]
        );
        assert_eq!(
            pw_pkg.libs[0].custom_target_needs,
            vec!["widgetJsAll".to_string()]
        );
        assert!(!workspace_lake_inputs_digest(&cfg)?.is_empty());

        let write_fake_leantar_artifacts = |olean_path: &Path, dep_h: u64| -> Result<()> {
            fs::create_dir_all(olean_path.parent().unwrap())?;
            let mut olean_bytes = vec![0u8; 88];
            olean_bytes[0..5].copy_from_slice(b"olean");
            olean_bytes[5] = 2;
            olean_bytes[6] = 1;
            olean_bytes[7..13].copy_from_slice(b"4.31.0");
            olean_bytes[40..80].copy_from_slice(fake_githash.as_bytes());
            fs::write(olean_path, &olean_bytes)?;
            let ilean_path = olean_path.with_extension("ilean");
            fs::write(&ilean_path, b"{}")?;
            let o_h = lake_hash_bytes(&olean_bytes);
            let i_h = lake_hash_bytes(b"{}");
            fs::write(
                PathBuf::from(format!("{}.hash", olean_path.display())),
                format!("{o_h:016x}"),
            )?;
            fs::write(
                PathBuf::from(format!("{}.hash", ilean_path.display())),
                format!("{i_h:016x}"),
            )?;
            let trace_json = serde_json::json!({
                "schemaVersion": "2025-09-10",
                "depHash": format!("{dep_h:016x}"),
                "outputs": {
                    "m": false,
                    "o": [format!("{o_h:016x}.olean")],
                    "i": format!("{i_h:016x}.ilean")
                }
            });
            fs::write(
                olean_path.with_extension("trace"),
                serde_json::to_vec(&trace_json)?,
            )?;
            Ok(())
        };

        let dep_spec = resolve_module_in_package(
            cfg.dep_pkgs.iter().find(|p| p.name == "PwDep").unwrap(),
            false,
            "PwDep",
        )
        .expect("PwDep spec");
        // Construct expected Lake trace inputs independently from Lake's documented schema
        // (`PwDep:deps` nested entry on v4.31.0, toolchain cap, source path hash, options, isModule, Module.name, Package.id?, Module.leanArgs)
        // rather than calling `compute_expected_lake_module_dep_hash` so parity is non-circular.
        let indep_inputs = serde_json::json!([
            [
                "PwDep:deps",
                [
                    [
                        "deps",
                        [
                            [
                                "pwdep/PwDep:extraDep",
                                [["@pwdep:extraDep", "00000000000006bb"]]
                            ],
                            ["imports", "00000000000006bb"]
                        ]
                    ],
                    [
                        "libs",
                        [
                            ["import dynlibs", "00000000000006bb"],
                            ["package external libraries", "00000000000006bb"],
                            ["module dynlibs", "00000000000006bb"],
                            ["module plugins", "00000000000006bb"]
                        ]
                    ]
                ]
            ],
            [
                format!("Lean 4.31.0, commit {fake_githash}"),
                format!("{:016x}", lake_hash_bytes(fake_githash.as_bytes()))
            ],
            [
                dep_spec.src_path.to_string_lossy(),
                format!("{:016x}", lake_hash_text(dep_src))
            ],
            ["options", "00000000000006bb"],
            [
                "isModule: false",
                format!("{:016x}", lake_mix_hash(LAKE_NIL_HASH, 13))
            ],
            [
                "Module.name: PwDep",
                format!("{:016x}", lake_hash_name("PwDep"))
            ],
            [
                "Package.id?: (some PwDep)",
                format!("{:016x}", lake_hash_pkg_id("PwDep"))
            ],
            ["Module.leanArgs: #[]", "00000000000006bb"]
        ]);
        let expected_dep_h = lake_input_hash(&indep_inputs)?;
        write_fake_leantar_artifacts(&spec_olean_path(&dep_spec), expected_dep_h)?;

        let mut cache = LakeClosureCache {
            ignore_mtime_skew: true,
            ..Default::default()
        };
        let mut visiting = HashSet::new();
        assert!(
            lake_closure_export_info(&cfg, &dep_spec, true, &mut cache, &mut visiting).is_some(),
            "inputless leantar .trace with exact depHash must verify"
        );

        // Tampering with source invalidates inputless depHash verification.
        fs::write(
            dep_dir.join("PwDep.lean"),
            "prelude\ndef pwVal : Nat := 99\n",
        )?;
        reset_lake_inputs_tag_memo();
        let mut cache2 = LakeClosureCache {
            ignore_mtime_skew: true,
            ..Default::default()
        };
        let mut visiting2 = HashSet::new();
        assert!(
            lake_closure_export_info(&cfg, &dep_spec, true, &mut cache2, &mut visiting2).is_none(),
            "tampered source must fail inputless leantar depHash check"
        );

        // ProofWidgets custom target `needs := #[widgetJsAll]` verifies at clean git rev and rejects both dirty non-.lean inputs and dirty .lean files.
        // Write artifacts into `.lake/build/` BEFORE committing would be wrong, so ensure `.lake/` is gitignored as in real ProofWidgets4.
        fs::write(pw_dir.join(".gitignore"), "/.lake/\n")?;
        let mut git_add_ig = crate::trusted_tools::git(&pw_dir)?;
        assert!(git_add_ig
            .args(["-C"])
            .arg(&pw_dir)
            .args(["add", ".gitignore"])
            .status()?
            .success());
        let mut git_commit_ig = crate::trusted_tools::git(&pw_dir)?;
        assert!(git_commit_ig
            .args([
                "-C",
                &pw_dir.to_string_lossy(),
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@e",
                "-c",
                "commit.gpgsign=false",
                "commit",
                "-qm",
                "ignore .lake",
            ])
            .status()?
            .success());
        let mut git_rev2 = crate::trusted_tools::git(&pw_dir)?;
        let pw_rev2 = String::from_utf8(
            git_rev2
                .args(["-C"])
                .arg(&pw_dir)
                .args(["rev-parse", "HEAD"])
                .output()?
                .stdout,
        )?
        .trim()
        .to_string();
        cfg.manifest_packages
            .iter_mut()
            .find(|mp| mp.name == "proofwidgets")
            .unwrap()
            .rev = Some(pw_rev2.clone());
        fs::write(
            root.join("lake-manifest.json"),
            serde_json::to_string_pretty(&serde_json::json!({
                "version": "1.1.0",
                "packagesDir": ".lake/packages",
                "packages": [
                    {
                        "type": "git",
                        "name": "proofwidgets",
                        "rev": pw_rev2,
                        "url": "https://example.invalid/ProofWidgets4",
                        "inherited": false,
                        "configFile": "lakefile.lean"
                    },
                    {
                        "type": "git",
                        "name": "pwdep",
                        "rev": pwdep_rev,
                        "url": "https://example.invalid/pwdep",
                        "inherited": false,
                        "configFile": "lakefile.lean"
                    }
                ]
            }))?,
        )?;
        reset_lake_inputs_tag_memo();
        let pw_spec = resolve_module_in_package(&pw_pkg, false, "ProofWidgets").expect("PW spec");
        let pw_src = "prelude\nunsafe def pwFast : Nat := 1\n@[implemented_by pwFast]\ndef pwHelper : Nat := 1\n";
        let pw_olean = spec_olean_path(&pw_spec);
        write_fake_leantar_artifacts(&pw_olean, 0x123456789abcdef0)?;
        let mut cache3 = LakeClosureCache {
            ignore_mtime_skew: true,
            ..Default::default()
        };
        let mut visiting3 = HashSet::new();
        assert!(
            lake_closure_export_info(&cfg, &pw_spec, true, &mut cache3, &mut visiting3).is_some(),
            "clean git-pinned custom-target-needs package must verify"
        );
        // Lake-built `.trace` WITH `inputs` (where `ProofWidgets:extraDep` embeds custom target `widgetJsAll` hash)
        // must also verify cleanly on clean git-pinned packages and reuse prebuilt `.olean` in `build_module_dag`.
        let pw_o_h = fs::read_to_string(format!("{}.hash", pw_olean.display()))?;
        let pw_i_h = fs::read_to_string(format!(
            "{}.hash",
            pw_olean.with_extension("ilean").display()
        ))?;
        let pw_inputs = serde_json::json!([
            [
                "ProofWidgets:deps",
                [
                    [
                        "deps",
                        [
                            [
                                "proofwidgets/ProofWidgets:extraDep",
                                [
                                    ["@ProofWidgets:extraDep", "00000000000006bb"],
                                    ["proofwidgets/widgetJsAll", "fedcba9876543210"]
                                ]
                            ],
                            ["imports", "00000000000006bb"]
                        ]
                    ],
                    [
                        "libs",
                        [
                            ["import dynlibs", "00000000000006bb"],
                            ["package external libraries", "00000000000006bb"],
                            ["module dynlibs", "00000000000006bb"],
                            ["module plugins", "00000000000006bb"]
                        ]
                    ]
                ]
            ],
            [
                format!("Lean 4.31.0, commit {fake_githash}"),
                format!("{:016x}", lake_hash_bytes(fake_githash.as_bytes()))
            ],
            [
                pw_spec.src_path.to_string_lossy(),
                format!("{:016x}", lake_hash_text(pw_src))
            ],
            ["options", "00000000000006bb"],
            [
                "isModule: false",
                format!("{:016x}", lake_mix_hash(LAKE_NIL_HASH, 13))
            ],
            [
                "Module.name: ProofWidgets",
                format!("{:016x}", lake_hash_name("ProofWidgets"))
            ],
            [
                "Package.id?: (some ProofWidgets)",
                format!("{:016x}", lake_hash_pkg_id("ProofWidgets"))
            ],
            ["Module.leanArgs: #[]", "00000000000006bb"]
        ]);
        let pw_dep_h = lake_input_hash(&pw_inputs)?;
        fs::write(
            pw_olean.with_extension("trace"),
            serde_json::to_vec(&serde_json::json!({
                "schemaVersion": "2025-09-10",
                "depHash": format!("{pw_dep_h:016x}"),
                "inputs": pw_inputs,
                "outputs": {
                    "m": false,
                    "o": [format!("{}.olean", pw_o_h.trim())],
                    "i": format!("{}.ilean", pw_i_h.trim())
                }
            }))?,
        )?;
        let mut cache3_inputs = LakeClosureCache {
            ignore_mtime_skew: true,
            ..Default::default()
        };
        let mut visiting3_inputs = HashSet::new();
        assert!(
            lake_closure_export_info(
                &cfg,
                &pw_spec,
                true,
                &mut cache3_inputs,
                &mut visiting3_inputs,
            )
            .is_some(),
            "Lake-built inputs-bearing .trace for clean git-pinned custom-target-needs + @[implemented_by] package must verify"
        );
        fs::write(dep_dir.join("PwDep.lean"), dep_src)?;
        reset_lake_inputs_tag_memo();
        let dag = build_module_dag(&cfg, &[])?;
        assert!(dag.nodes.contains_key("App"));
        assert!(!dag.nodes.contains_key("ProofWidgets"));
        let app_node = &dag.nodes["App"];
        let mut app_deps: Vec<(String, String)> = app_node
            .external_olean_deps
            .iter()
            .map(|(m, p)| Ok((m.clone(), compute_olean_artifact_set_digest(p)?)))
            .collect::<Result<Vec<_>>>()?;
        app_deps.sort_by(|a, b| a.0.cmp(&b.0));
        assert_eq!(app_deps.len(), 2);
        assert!(!compute_module_cas_key(&cfg, app_node, &app_deps, false)?.is_empty());
        // Dirty tracked custom-target input (`widget/js/hello.tsx`) must fail closed even when `.lean` is untouched.
        fs::write(
            pw_dir.join("widget/js/hello.tsx"),
            "export default { pwned: true }\n",
        )?;
        reset_lake_inputs_tag_memo();
        let mut cache_tsx = LakeClosureCache {
            ignore_mtime_skew: true,
            ..Default::default()
        };
        let mut visiting_tsx = HashSet::new();
        assert!(
            lake_closure_export_info(&cfg, &pw_spec, true, &mut cache_tsx, &mut visiting_tsx)
                .is_none(),
            "dirty non-.lean tracked input in git-pinned custom-target-needs package must fail closed"
        );
        fs::write(pw_dir.join("widget/js/hello.tsx"), "export default {}\n")?;
        fs::write(
            pw_dir.join("ProofWidgets.lean"),
            "prelude\ndef pwHelper : Nat := 2\n",
        )?;
        reset_lake_inputs_tag_memo();
        let mut cache4 = LakeClosureCache {
            ignore_mtime_skew: true,
            ..Default::default()
        };
        let mut visiting4 = HashSet::new();
        assert!(
            lake_closure_export_info(&cfg, &pw_spec, true, &mut cache4, &mut visiting4).is_none(),
            "dirty source in git-pinned custom-target-needs package must fail closed"
        );

        crate::zygote::purge_snapshot_dir(&dir);
        Ok(())
    }

    #[test]
    fn test_non_root_dep_pkg_sorry_reference_emits_sidecars_while_root_pkg_rejects() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_dep_sorry_sidecars_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir)?;
        let root = dir.as_path();
        fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.31.0\n")?;
        fs::write(
            root.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage app where\n@[default_target]\nlean_lib App where\n",
        )?;
        let root_sorry_src = "prelude\nimport SearchDep.Syntax\ntheorem badRoot : False := sorry\n";
        fs::write(root.join("App.lean"), root_sorry_src)?;

        let dep_dir = root.join(".lake/packages/searchdep");
        fs::create_dir_all(dep_dir.join("SearchDep"))?;
        fs::write(dep_dir.join(".gitignore"), "/.lake/\n")?;
        fs::write(
            dep_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage SearchDep where\n@[default_target]\nlean_lib SearchDep where\n  globs := #[.submodules `SearchDep]\n",
        )?;
        // Mimics `LeanSearchClient.Syntax`: non-root git-pinned dependency mentioning `IO.getEnv`
        // (forcing native DAG compilation) and referencing `sorryAx` in helper/meta code.
        let dep_src = "prelude\ndef queryUrl : IO (Option String) := IO.getEnv \"LEANSEARCHCLIENT_URL\"\ndef mkFallbackRef : String := s!\"{``sorryAx}\"\n";
        fs::write(dep_dir.join("SearchDep/Syntax.lean"), dep_src)?;

        let mut git_init = crate::trusted_tools::git(root)?;
        assert!(git_init
            .args(["init", "-q"])
            .arg(&dep_dir)
            .status()?
            .success());
        let mut git_add = crate::trusted_tools::git(&dep_dir)?;
        assert!(git_add
            .args(["-C"])
            .arg(&dep_dir)
            .args(["add", "."])
            .status()?
            .success());
        let mut git_commit = crate::trusted_tools::git(&dep_dir)?;
        assert!(git_commit
            .args([
                "-C",
                &dep_dir.to_string_lossy(),
                "-c",
                "user.name=t",
                "-c",
                "user.email=t@e",
                "-c",
                "commit.gpgsign=false",
                "commit",
                "-qm",
                "init",
            ])
            .status()?
            .success());
        let mut git_rev = crate::trusted_tools::git(&dep_dir)?;
        let searchdep_rev = String::from_utf8(
            git_rev
                .args(["-C"])
                .arg(&dep_dir)
                .args(["rev-parse", "HEAD"])
                .output()?
                .stdout,
        )?
        .trim()
        .to_string();

        fs::write(
            root.join("lake-manifest.json"),
            serde_json::to_string_pretty(&serde_json::json!({
                "version": "1.1.0",
                "packagesDir": ".lake/packages",
                "packages": [{
                    "type": "git",
                    "name": "searchdep",
                    "rev": searchdep_rev,
                    "url": "https://example.invalid/searchdep",
                    "inherited": false,
                    "configFile": "lakefile.lean"
                }]
            }))?,
        )?;

        let mut cfg = resolve_project_config_with_trust(root, false)?;
        let fake_githash = "0123456789abcdef0123456789abcdef01234567";
        cfg.lean_githash = fake_githash.to_string();
        cfg.lean_bin = PathBuf::from("/bin/true");
        cfg.toolchain_lib_lean = PathBuf::new();

        let dag = build_module_dag_with_trust(&cfg, &[], false)?;
        let dep_node = dag
            .nodes
            .get("SearchDep.Syntax")
            .expect("SearchDep.Syntax must enter DAG when IO.getEnv is referenced");
        assert!(!dep_node.is_root_pkg);
        let root_node = dag.nodes.get("App").expect("App in DAG");
        assert!(root_node.is_root_pkg);

        for node in [dep_node, root_node] {
            fs::create_dir_all(node.olean_path.parent().unwrap())?;
            let mut olean_bytes = vec![0u8; 88];
            olean_bytes[0..5].copy_from_slice(b"olean");
            olean_bytes[5] = 2;
            olean_bytes[6] = 1;
            olean_bytes[7..13].copy_from_slice(b"4.31.0");
            olean_bytes[40..80].copy_from_slice(fake_githash.as_bytes());
            fs::write(&node.olean_path, &olean_bytes)?;
            fs::write(&node.ilean_path, b"{}")?;
        }

        let dep_dig = compute_olean_artifact_set_digest(&dep_node.olean_path)?;
        write_lake_module_hashes_and_trace(&cfg, &dag, dep_node, &dep_dig, Some(&dep_dig), true)?;
        assert!(
            dep_node.olean_path.with_extension("trace").is_file(),
            "non-root dependency mentioning sorryAx in meta helper must emit Lake .trace sidecar"
        );

        let root_dig = compute_olean_artifact_set_digest(&root_node.olean_path)?;
        let root_err = write_lake_module_hashes_and_trace(
            &cfg,
            &dag,
            root_node,
            &root_dig,
            Some(&root_dig),
            true,
        )
        .expect_err("root-package module containing sorry must fail sidecar materialization gate");
        assert!(root_err
            .to_string()
            .contains("turbo_spec_verify_audit_materialize_gate"));
        assert!(!root_node.olean_path.with_extension("trace").exists());

        crate::zygote::purge_snapshot_dir(&dir);
        Ok(())
    }

    #[test]
    fn test_lake_inputs_tag_memo_never_poisons_transient_failure() -> Result<()> {
        reset_lake_inputs_tag_memo();
        let dir = make_temp_test_dir("lake_inputs_positive_only_memo");
        let proj = dir.join("proj");
        fs::create_dir_all(&proj)?;
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            proj.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage «p»\ninput_file specTxt where\n  path := \"spec.txt\"\n  text := true\n",
        )?;
        // Missing `spec.txt` causes `try_project_lake_inputs_tag` to error without poisoning `LAKE_INPUTS_TAG_MEMO`.
        assert!(try_project_lake_inputs_tag(&proj).is_err());

        fs::write(proj.join("spec.txt"), "hello\n")?;
        let populated = try_project_lake_inputs_tag(&proj)?;
        assert!(
            populated.is_some(),
            "try_project_lake_inputs_tag must recompute once transient missing input is restored"
        );
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_are_all_project_oleans_replayed_requires_policy_bound_audit() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("olean_up_to_date_csimp_policy");
        let proj = dir.join("proj");
        let store_dir = dir.join("store");
        fs::create_dir_all(&proj)?;
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"csimp-up-to-date\"\ndefaultTargets = [\"Fixture\"]\n[[lean_lib]]\nname = \"Fixture\"\n",
        )?;
        let src = "\
namespace Fixture
def slow (n : Nat) : Nat := n + 1
def fast (n : Nat) : Nat := n.succ
@[csimp] theorem fast_eq : @slow = @fast := by
  funext n
  rfl
end Fixture
";
        fs::write(proj.join("Fixture.lean"), src)?;
        let mut store = TurboStore::open(Some(&store_dir))?;
        let canon = fs::canonicalize(&proj)?;
        let mut file_hashes = std::collections::BTreeMap::new();
        file_hashes.insert(
            "Fixture.lean".to_string(),
            blake3::hash(src.as_bytes()).to_hex().to_string(),
        );

        // Build and audit under explicit csimp permission `Fixture.fast_eq`.
        {
            let _csimp = ScopedEnvVar::set("TURBO_LEAN_ALLOWED_CSIMP", "Fixture.fast_eq");
            build_project_modules_native(
                &mut store,
                &canon,
                &[],
                "trusted",
                1,
                false,
                true,
                Some(&file_hashes),
            )?;
            assert!(
                crate::lake_build::are_all_project_oleans_replayed_in_store(
                    &store,
                    &canon,
                    &file_hashes,
                ),
                "audited root `.olean` must satisfy `are_all_project_oleans_replayed_in_store` under matching csimp policy"
            );
        }

        // Without csimp permission, `are_all_project_oleans_replayed_in_store` must return false
        // and `ensure_project_and_imported_oleans_replayed_in_store` must reject the `.olean` via
        // the compiled kernel auditor.
        assert!(
            !crate::lake_build::are_all_project_oleans_replayed_in_store(
                &store,
                &canon,
                &file_hashes,
            ),
            "replay-only or different-policy `.olean` must not satisfy `are_all_project_oleans_replayed_in_store`"
        );
        let audit_err = crate::lake_build::ensure_project_and_imported_oleans_replayed_in_store(
            &store,
            &canon,
            &file_hashes,
        )
        .expect_err("unpermitted csimp `.olean` must fail compiled kernel audit");
        assert!(
            format!("{audit_err:#}").contains("audit")
                || format!("{audit_err:#}").contains("csimp"),
            "unexpected error: {audit_err:#}"
        );

        crate::zygote::purge_snapshot_dir(&dir);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_git_pinned_dep_unused_native_decide_allowed_but_used_rejected() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("git_pinned_dep_native_decide_hygiene");
        let dep_origin = dir.join("dep_origin");
        let proj = dir.join("proj");
        let dep = proj.join(".lake/packages/dep_bv");
        let store_dir = dir.join("store");
        fs::create_dir_all(dep_origin.join("DepBv"))?;
        fs::create_dir_all(proj.join("App"))?;
        let tc = "leanprover/lean4:v4.35.0\n";
        fs::write(dep_origin.join("lean-toolchain"), tc)?;
        fs::write(proj.join("lean-toolchain"), tc)?;
        fs::write(
            dep_origin.join("lakefile.toml"),
            "name = \"dep_bv\"\ndefaultTargets = [\"DepBv\"]\n[[lean_lib]]\nname = \"DepBv\"\n",
        )?;
        fs::write(
            dep_origin.join("DepBv/Bridge.lean"),
            "def safeVal : Nat := 7\ntheorem unused_native : 1 + 1 = 2 := by native_decide\n",
        )?;
        fs::write(dep_origin.join("DepBv.lean"), "import DepBv.Bridge\n")?;
        let git_bin = std::env::var_os("TURBO_LEAN_GIT")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("git"));
        for args in [
            vec!["init"],
            vec!["config", "user.email", "t@e.com"],
            vec!["config", "user.name", "T"],
            vec!["add", "."],
            vec!["commit", "-m", "init"],
        ] {
            let st = Command::new(&git_bin)
                .args(&args)
                .current_dir(&dep_origin)
                .status()?;
            anyhow::ensure!(st.success(), "git init dep_origin failed on {args:?}");
        }
        let rev_out = Command::new(&git_bin)
            .args(["rev-parse", "HEAD"])
            .current_dir(&dep_origin)
            .output()?;
        anyhow::ensure!(rev_out.status.success());
        let rev = String::from_utf8(rev_out.stdout)?.trim().to_string();
        fs::create_dir_all(dep.parent().unwrap())?;
        let clone_st = Command::new(&git_bin)
            .args(["clone", "--quiet"])
            .arg(&dep_origin)
            .arg(&dep)
            .status()?;
        anyhow::ensure!(clone_st.success(), "git clone dep_origin failed");
        fs::write(
            proj.join("lakefile.toml"),
            format!(
                "name = \"app\"\ndefaultTargets = [\"App\"]\n[[require]]\nname = \"dep_bv\"\ngit = {:?}\nrev = {:?}\n[[lean_lib]]\nname = \"App\"\n",
                dep_origin.to_string_lossy(),
                rev
            ),
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            serde_json::json!({
                "version": "1.1.0",
                "packagesDir": ".lake/packages",
                "packages": [{
                    "type": "git",
                    "scope": "",
                    "name": "dep_bv",
                    "manifestFile": "lake-manifest.json",
                    "rev": rev,
                    "inherited": false,
                    "configFile": "lakefile.toml",
                    "inputRev": rev,
                    "url": dep_origin.to_string_lossy()
                }]
            })
            .to_string(),
        )?;
        let mut ctor_lines =
            String::from("inductive BigExpr where\n  | leaf (n : Nat)\n  | rec1 (a b : BigExpr)\n");
        for idx in 0..72 {
            ctor_lines.push_str(&format!("  | op{idx} (a b : BigExpr)\n"));
        }
        let mut match_lines = String::from(
            "private def walkBig (e : BigExpr) : List Nat :=\n  match e with\n  | .leaf n => [n]\n  | .rec1 a b => walkBig a ++ walkBig b\n",
        );
        for idx in 0..72 {
            match_lines.push_str(&format!(
                "  | .op{idx} a b => {idx} :: (walkBig a ++ walkBig b)\n"
            ));
        }
        match_lines.push_str("termination_by sizeOf e\n");
        let safe_src = format!(
            "import DepBv.Bridge\n{ctor_lines}{match_lines}theorem root_safe : safeVal = 7 ∧ walkBig (.leaf 3) = walkBig (.leaf 3) := ⟨rfl, rfl⟩\n"
        );
        fs::write(proj.join("App/Safe.lean"), &safe_src)?;
        fs::write(proj.join("App.lean"), "import App.Safe\n")?;

        let mut store = TurboStore::open(Some(&store_dir))?;
        let canon = fs::canonicalize(&proj)?;
        let mut file_hashes = std::collections::BTreeMap::new();
        for (rel, body) in [
            ("App/Safe.lean", safe_src.as_str()),
            ("App.lean", "import App.Safe\n"),
        ] {
            file_hashes.insert(
                rel.to_string(),
                blake3::hash(body.as_bytes()).to_hex().to_string(),
            );
        }
        build_project_modules_native(
            &mut store,
            &canon,
            &[],
            "trusted",
            1,
            false,
            true,
            Some(&file_hashes),
        )?;
        crate::lake_build::ensure_project_and_imported_oleans_replayed_in_store(
            &store,
            &canon,
            &file_hashes,
        )?;
        ensure_imported_oleans_replayed_with_roots(
            &store,
            &canon,
            &[canon.join("App/Safe.lean")],
            &[String::from("App.Safe")],
        )?;

        let bad_src =
            "import DepBv.Bridge\ntheorem root_uses_native : 1 + 1 = 2 := unused_native\n";
        fs::write(proj.join("App/Safe.lean"), bad_src)?;
        file_hashes.insert(
            "App/Safe.lean".to_string(),
            blake3::hash(bad_src.as_bytes()).to_hex().to_string(),
        );
        let bad_err = build_project_modules_native(
            &mut store,
            &canon,
            &[],
            "trusted",
            1,
            false,
            true,
            Some(&file_hashes),
        )
        .expect_err(
            "root theorem referencing native_decide theorem in git-pinned dep must fail KernelGate",
        );
        assert!(
            format!("{bad_err:#}").contains("Lean.ofReduceBool")
                || format!("{bad_err:#}").contains("Lean.trustCompiler")
                || format!("{bad_err:#}").contains("KernelGate")
                || format!("{bad_err:#}").contains("disallowed axiom"),
            "unexpected error when referencing git-pinned native_decide theorem: {bad_err:#}"
        );

        crate::zygote::purge_snapshot_dir(&dir);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_git_pinned_dep_non_lean_gitlink_and_c_helper_target_hygiene() -> Result<()> {
        let _env_guard = native_build_env_guard();
        let dir = make_temp_test_dir("git_pinned_dep_non_lean_gitlink");
        let sub_origin = dir.join("eth_tests_sub");
        let dep_origin = dir.join("evmyul_origin");
        let proj = dir.join("proj");
        let dep = proj.join(".lake/packages/evmyul");
        let store_dir = dir.join("store");
        fs::create_dir_all(&sub_origin)?;
        fs::create_dir_all(dep_origin.join("EvmYul/Specs"))?;
        fs::create_dir_all(proj.join("Verity"))?;
        let tc = include_str!("../../../lean/lean-toolchain");
        fs::write(dep_origin.join("lean-toolchain"), tc)?;
        fs::write(proj.join("lean-toolchain"), tc)?;
        fs::write(sub_origin.join("fixture.json"), "{}\n")?;
        let git_bin = std::env::var_os("TURBO_LEAN_GIT")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("git"));
        for (repo_dir, msg) in [(&sub_origin, "sub_init")] {
            for args in [
                vec!["init"],
                vec!["config", "user.email", "t@e.com"],
                vec!["config", "user.name", "T"],
                vec!["add", "."],
                vec!["commit", "-m", msg],
            ] {
                let st = Command::new(&git_bin)
                    .args(&args)
                    .current_dir(repo_dir)
                    .status()?;
                anyhow::ensure!(st.success(), "git init {msg} failed on {args:?}");
            }
        }
        let sub_sha = String::from_utf8(
            Command::new(&git_bin)
                .args(["rev-parse", "HEAD"])
                .current_dir(&sub_origin)
                .output()?
                .stdout,
        )?
        .trim()
        .to_string();
        fs::write(dep_origin.join(".gitignore"), "/*.olean\n/.lake/\n/sha2/\n")?;
        fs::write(
            dep_origin.join(".gitmodules"),
            format!(
                "[submodule \"EthereumTests\"]\n\tpath = EthereumTests\n\turl = {}\n",
                sub_origin.display()
            ),
        )?;
        fs::write(
            dep_origin.join("lakefile.lean"),
            "import Lake\nopen Lake DSL System\n\npackage «evmyul» {\n  moreLeanArgs := #[\"-DautoImplicit=false\"]\n  moreServerOptions := #[⟨`autoImplicit, false⟩]\n}\n\ntarget cloneSha2 pkg : FilePath := do\n  inputTextFile (pkg.dir / \"lakefile.lean\")\n\n@[default_target]\nlean_lib «EvmYul»\n",
        )?;
        fs::write(
            dep_origin.join("EvmYul/Specs/Bridge.lean"),
            "def evmSafe : Nat := 42\ntheorem unused_bv : (1 : BitVec 8) + 1 = 2 := by decide\ntheorem unused_native : 1 + 1 = 2 := by native_decide\n",
        )?;
        fs::write(
            dep_origin.join("EvmYul.lean"),
            "import EvmYul.Specs.Bridge\n",
        )?;
        for args in [
            vec!["init"],
            vec!["config", "user.email", "t@e.com"],
            vec!["config", "user.name", "T"],
            vec!["add", "."],
        ] {
            let st = Command::new(&git_bin)
                .args(&args)
                .current_dir(&dep_origin)
                .status()?;
            anyhow::ensure!(st.success(), "git prep dep_origin failed on {args:?}");
        }
        let st_gl = Command::new(&git_bin)
            .current_dir(&dep_origin)
            .args([
                "update-index",
                "--add",
                "--cacheinfo",
                &format!("160000,{sub_sha},EthereumTests"),
            ])
            .status()?;
        anyhow::ensure!(st_gl.success(), "git update-index EthereumTests failed");
        let st_cm = Command::new(&git_bin)
            .current_dir(&dep_origin)
            .args(["commit", "-m", "init_evmyul"])
            .status()?;
        anyhow::ensure!(st_cm.success(), "git commit dep_origin failed");
        let rev = String::from_utf8(
            Command::new(&git_bin)
                .args(["rev-parse", "HEAD"])
                .current_dir(&dep_origin)
                .output()?
                .stdout,
        )?
        .trim()
        .to_string();
        fs::create_dir_all(dep.parent().unwrap())?;
        let clone_st = Command::new(&git_bin)
            .env("GIT_ALLOW_PROTOCOL", "file")
            .args(["clone", "--quiet"])
            .arg(&dep_origin)
            .arg(&dep)
            .status()?;
        anyhow::ensure!(clone_st.success(), "git clone dep_origin failed");
        let sub_init = Command::new(&git_bin)
            .env("GIT_ALLOW_PROTOCOL", "file")
            .current_dir(&dep)
            .args(["submodule", "update", "--init", "--quiet"])
            .status()?;
        anyhow::ensure!(sub_init.success(), "git submodule update --init failed");
        // Dirty the non-Lean submodule and populate gitignored `sha2/` just like sticky CI disks.
        fs::write(dep.join("EthereumTests/untracked.json"), "{}\n")?;
        fs::create_dir_all(dep.join("sha2"))?;
        fs::write(dep.join("sha2/sha-256.c"), "int x = 0;\n")?;

        fs::write(
            proj.join("lakefile.toml"),
            format!(
                "name = \"verity\"\ndefaultTargets = [\"Verity\"]\n[[require]]\nname = \"evmyul\"\ngit = {:?}\nrev = {:?}\n[[lean_lib]]\nname = \"Verity\"\n",
                dep_origin.to_string_lossy(),
                rev
            ),
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            serde_json::json!({
                "version": "1.1.0",
                "packagesDir": ".lake/packages",
                "packages": [{
                    "type": "git",
                    "scope": "",
                    "name": "evmyul",
                    "manifestFile": "lake-manifest.json",
                    "rev": rev,
                    "inherited": false,
                    "configFile": "lakefile.lean",
                    "inputRev": rev,
                    "url": dep_origin.to_string_lossy()
                }]
            })
            .to_string(),
        )?;
        let root_src = "import EvmYul.Specs.Bridge\ntheorem verity_ok : evmSafe = 42 := rfl\n";
        fs::write(proj.join("Verity/Core.lean"), root_src)?;
        fs::write(proj.join("Verity.lean"), "import Verity.Core\n")?;

        reset_lake_inputs_tag_memo();
        let cfg = resolve_project_config(&proj)?;
        if let Some(evmyul_lf) = std::env::var_os("TURBO_TEST_EVMYUL_LAKEFILE") {
            let real_evmyul = PathBuf::from(evmyul_lf);
            let real_pkg = parse_lakefile_lean(real_evmyul.parent().unwrap(), &real_evmyul, false)?;
            assert!(!package_gitlink_touches_lean(
                Path::new("EthereumTests"),
                &real_pkg
            ));
            assert!(package_gitlink_touches_lean(
                Path::new("EvmYul/Sub"),
                &real_pkg
            ));
            assert!(package_gitlink_touches_lean(
                Path::new("Conform/Sub"),
                &real_pkg
            ));
        }
        let dep_pkg = cfg
            .dep_pkgs
            .iter()
            .find(|p| p.name == "evmyul")
            .expect("evmyul resolved");
        assert!(!package_gitlink_touches_lean(
            Path::new("EthereumTests"),
            dep_pkg
        ));
        assert!(package_gitlink_touches_lean(
            Path::new("EvmYul/Sub"),
            dep_pkg
        ));
        assert!(is_clean_pinned_git_checkout(&dep, &rev, Some(dep_pkg)));
        assert!(
            !is_clean_pinned_git_checkout(&dep, &rev, None),
            "without resolved PackageConfig, any 160000 gitlink must fail closed"
        );

        let mut store = TurboStore::open(Some(&store_dir))?;
        let canon = fs::canonicalize(&proj)?;
        let mut file_hashes = std::collections::BTreeMap::new();
        for (rel, body) in [
            ("Verity/Core.lean", root_src),
            ("Verity.lean", "import Verity.Core\n"),
        ] {
            file_hashes.insert(
                rel.to_string(),
                blake3::hash(body.as_bytes()).to_hex().to_string(),
            );
        }
        build_project_modules_native(
            &mut store,
            &canon,
            &[],
            "trusted",
            1,
            false,
            true,
            Some(&file_hashes),
        )?;
        crate::lake_build::ensure_project_and_imported_oleans_replayed_in_store(
            &store,
            &canon,
            &file_hashes,
        )?;

        // Fail closed if a tracked file in the Lean package is modified or untracked outside gitignored/non-Lean-gitlink paths.
        fs::write(dep.join("EvmYul/Untracked.lean"), "def bad := 1\n")?;
        reset_lake_inputs_tag_memo();
        assert!(!is_clean_pinned_git_checkout(&dep, &rev, Some(dep_pkg)));

        crate::zygote::purge_snapshot_dir(&dir);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_per_worker_lean_num_threads_avoids_pool_oversubscription() {
        assert_eq!(per_worker_lean_num_threads(Some("8"), 8, 8), 1);
        assert_eq!(per_worker_lean_num_threads(None, 8, 8), 1);
        assert_eq!(per_worker_lean_num_threads(Some("8"), 8, 2), 4);
        assert_eq!(per_worker_lean_num_threads(Some("2"), 8, 2), 2);
        assert_eq!(per_worker_lean_num_threads(Some("8"), 8, 1), 8);
        assert_eq!(per_worker_lean_num_threads(None, 8, 1), 8);
    }

    #[test]
    fn test_source_uses_include_str_detects_bin_and_qualified_variants() {
        assert!(source_uses_include_str("def a := include_str \"x.txt\"\n"));
        assert!(source_uses_include_str(
            "def b := Lean.include_str \"x.txt\"\n"
        ));
        assert!(source_uses_include_str("def c := include_bin \"x.bin\"\n"));
        assert!(source_uses_include_str(
            "def d := Lean.include_bin? \"x.bin\"\n"
        ));
        assert!(!source_uses_include_str(
            "def e := \"include_str not real\"\n"
        ));
        assert!(!source_uses_include_str(
            "-- include_bin \"commented.bin\"\ndef f := 1\n"
        ));
    }

    #[test]
    fn test_root_pure_elaborator_module_caches_in_cas_and_manifest() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "tl_root_pure_elab_cas_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let proj = dir.join("proj");
        let store_dir = dir.join("store");
        fs::create_dir_all(proj.join("Verity"))?;
        let tc = std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/lean-toolchain"),
        )?;
        fs::write(proj.join("lean-toolchain"), &tc)?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"verity\"\ndefaultTargets = [\"Verity\"]\n[[lean_lib]]\nname = \"Verity\"\n",
        )?;
        let macro_src = "import Lean\nsyntax (name := checkContractCmd) \"#check_contract_nop\" : command\n@[command_elab checkContractCmd]\ndef elabCheckContract : Lean.Elab.Command.CommandElab := fun _ => pure ()\n";
        let leaf_src =
            "import Verity.Macro\n#check_contract_nop\ntheorem leaf_ok : 1 + 1 = 2 := rfl\n";
        let root_src = "import Verity.Leaf\n";
        fs::write(proj.join("Verity/Macro.lean"), macro_src)?;
        fs::write(proj.join("Verity/Leaf.lean"), leaf_src)?;
        fs::write(proj.join("Verity.lean"), root_src)?;
        let canon = fs::canonicalize(&proj)?;
        let mut store = TurboStore::open(Some(&store_dir))?;
        let r1 =
            build_project_modules_native(&mut store, &canon, &[], "trusted", 2, false, true, None)?;
        assert_eq!(r1.modules_compiled, 3);
        let manifest_path = canon.join(".lake/build/.turbo_verified_sources.json");
        let manifest_raw = fs::read_to_string(&manifest_path)?;
        assert!(
            manifest_raw.contains("Verity/Macro.lean") && manifest_raw.contains("Verity/Leaf.lean"),
            "pure root elaborator and its dependents must record verified source manifest entries: {manifest_raw}"
        );
        let mut file_hashes = BTreeMap::new();
        for rel in ["Verity/Macro.lean", "Verity/Leaf.lean", "Verity.lean"] {
            let b3 = blake3::hash(&fs::read(canon.join(rel))?)
                .to_hex()
                .to_string();
            file_hashes.insert(rel.to_string(), b3);
        }
        assert!(
            crate::lake_build::are_all_project_oleans_up_to_date(&canon, &file_hashes),
            "check fast-path must treat verified pure root elaborator closure as up-to-date"
        );
        assert_eq!(
            crate::lake_build::ensure_project_imports_fresh(
                &canon,
                &[canon.join("Verity/Leaf.lean")],
                None,
                true,
            )?,
            0,
            "ensure_project_imports_fresh must not mark verified pure root elaborator stale"
        );
        let snap = dir.join("snap");
        fs::create_dir_all(snap.join("Verity"))?;
        fs::write(snap.join("lean-toolchain"), &tc)?;
        fs::write(
            snap.join("lakefile.toml"),
            "name = \"verity\"\ndefaultTargets = [\"Verity\"]\n[[lean_lib]]\nname = \"Verity\"\n",
        )?;
        fs::write(snap.join("Verity/Macro.lean"), macro_src)?;
        fs::write(
            snap.join("Verity/Leaf.lean"),
            "import Verity.Macro\n#check_contract_nop\ntheorem leaf_ok : 1 + 1 = 2 := by decide\n",
        )?;
        fs::write(snap.join("Verity.lean"), root_src)?;
        let src_cfg = resolve_project_config(&canon)?;
        seed_verified_fresh_modules_into_disposable_snapshot(&src_cfg, &snap, &[])?;
        assert!(
            snap.join(".lake/build/lib/lean/Verity/Macro.olean").is_file(),
            "pure root elaborator Verity.Macro must seed into disposable snapshot when Leaf changes"
        );
        let snap_cfg = resolve_project_config_with_trust(&snap, false)?;
        let snap_dag = build_module_dag_for_trusted_statement(&snap_cfg, &["Verity".to_string()])?;
        let dirty =
            find_dirty_modules_in_otherwise_fresh_dag(&snap_cfg, &snap_dag, 16, &HashSet::new())
                .expect("disposable snapshot with seeded Verity.Macro must resolve dirty cone");
        assert_eq!(dirty, vec!["Verity.Leaf", "Verity"]);
        let _ = fs::remove_dir_all(canon.join(".lake/build"));
        reset_lake_inputs_tag_memo();
        let r2 =
            build_project_modules_native(&mut store, &canon, &[], "trusted", 2, false, true, None)?;
        assert_eq!(r2.modules_compiled, 0);
        assert_eq!(r2.modules_cached, 3);

        // Untracked `include_str` in a root module (no Lake `inputs`/`needs`) must NOT enter
        // Module CAS or `.turbo_verified_sources.json`, so editing the referenced file invalidates cleanly.
        fs::write(canon.join("Verity/secret.txt"), "v1")?;
        fs::write(
            canon.join("Verity/Untracked.lean"),
            "def embedded : String := include_str \"secret.txt\"\n",
        )?;
        let cfg_u = resolve_project_config(&canon)?;
        let spec_u = resolve_module_in_package(&cfg_u.root_pkg, true, "Verity.Untracked")
            .expect("Untracked module resolves");
        let src_u = fs::read_to_string(&spec_u.src_path)?;
        assert!(
            spec_source_has_disallowed_elab_host_effects(&cfg_u, &spec_u, &src_u),
            "root module with untracked include_str must be flagged as host-effecting"
        );
        let impl_by_src =
            "unsafe def fast : Nat := 0\n@[implemented_by fast]\ndef slow : Nat := 1\n";
        std::env::remove_var("TURBO_LEAN_ALLOWED_IMPLEMENTED_BY");
        assert!(
            spec_source_has_disallowed_elab_host_effects(&cfg_u, &spec_u, impl_by_src),
            "root module with @[implemented_by] must be flagged when allowlist is empty"
        );
        std::env::set_var("TURBO_LEAN_ALLOWED_IMPLEMENTED_BY", "slow");
        let allowed_ok =
            !spec_source_has_disallowed_elab_host_effects(&cfg_u, &spec_u, impl_by_src);
        let extern_still_blocked = spec_source_has_disallowed_elab_host_effects(
            &cfg_u,
            &spec_u,
            "@[extern \"c_fn\"]\nopaque extFn : Nat\n",
        );
        let unsafe_io_still_blocked = spec_source_has_disallowed_elab_host_effects(
            &cfg_u,
            &spec_u,
            "unsafe def bad (io : IO Nat) : Nat := match unsafeIO io with | .ok x => x | .error _ => 0\n",
        );
        std::env::remove_var("TURBO_LEAN_ALLOWED_IMPLEMENTED_BY");
        assert!(
            allowed_ok,
            "policy-bound @[implemented_by] must allow root module CAS caching"
        );
        assert!(
            extern_still_blocked,
            "@[extern] on root module must remain blocked"
        );
        assert!(
            unsafe_io_still_blocked,
            "unsafeIO on root module must remain blocked"
        );

        let _ = fs::remove_file(canon.join("Verity/Untracked.lean"));
        let _ = fs::remove_dir_all(canon.join(".lake/build"));
        fs::write(
            canon.join("Verity/Macro.lean"),
            "import Lean\nprivate unsafe def fastHelper : Nat := 1\n@[implemented_by fastHelper]\ndef evalSpec : Nat := 1\nsyntax (name := checkContractCmd) \"#check_contract_nop\" : command\n@[command_elab checkContractCmd]\ndef elabCheckContract : Lean.Elab.Command.CommandElab := fun _ => pure ()\n",
        )?;
        reset_lake_inputs_tag_memo();
        let _u_allow = ScopedEnvVar::set("TURBO_LEAN_ALLOWED_UNSAFE", "fastHelper");
        let r_impl1 = {
            let _i_allow = ScopedEnvVar::set("TURBO_LEAN_ALLOWED_IMPLEMENTED_BY", "evalSpec");
            build_project_modules_native(&mut store, &canon, &[], "trusted", 2, false, true, None)?
        };
        assert_eq!(r_impl1.modules_compiled, 3);
        let _ = fs::remove_dir_all(canon.join(".lake/build"));
        reset_lake_inputs_tag_memo();
        let r_impl2 = {
            let _i_allow = ScopedEnvVar::set("TURBO_LEAN_ALLOWED_IMPLEMENTED_BY", "evalSpec");
            build_project_modules_native(&mut store, &canon, &[], "trusted", 2, false, true, None)?
        };
        assert_eq!(r_impl2.modules_compiled, 0);
        assert_eq!(r_impl2.modules_cached, 3);
        let _ = fs::remove_dir_all(canon.join(".lake/build"));
        reset_lake_inputs_tag_memo();
        let wrong_policy = {
            let _i_wrong = ScopedEnvVar::set("TURBO_LEAN_ALLOWED_IMPLEMENTED_BY", "otherFn");
            build_project_modules_native(&mut store, &canon, &[], "trusted", 2, false, true, None)
        };
        assert!(
            wrong_policy.is_err(),
            "CAS hit for @[implemented_by] module must fail closed when allowlist omits declaration"
        );

        crate::zygote::purge_snapshot_dir(&dir);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_trace_options_order_independent_and_warm_on_disk_lake_trace_fallback() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let mut expected = LeanOptionsMap::new();
        expected.insert(
            LeanName::from_str_to_name("autoImplicit")?,
            LeanOptionValue::Bool(false),
        );
        expected.insert(
            LeanName::from_str_to_name("weak.linter.mathlibStandardSet")?,
            LeanOptionValue::Bool(true),
        );
        let cap_auto = "-DautoImplicit=false";
        let cap_lint = "-Dweak.linter.mathlibStandardSet=true";
        let hex_auto = format!("{:016x}", lake_hash_text(cap_auto));
        let hex_lint = format!("{:016x}", lake_hash_text(cap_lint));
        let reversed_json = serde_json::json!([[cap_lint, hex_lint], [cap_auto, hex_auto]]);
        assert!(
            verify_trace_options_value(&expected, &reversed_json),
            "verify_trace_options_value must be order-independent across Lake option serialization orders"
        );
        let mismatched_json = serde_json::json!([
            ["-Dweak.linter.mathlibStandardSet=false", hex_lint],
            [cap_auto, hex_auto]
        ]);
        assert!(!verify_trace_options_value(&expected, &mismatched_json));

        let dir = std::env::temp_dir().join(format!(
            "turbo_warm_trace_fallback_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(dir.join("Pkg"))?;
        let tc = include_str!("../../../lean/lean-toolchain");
        fs::write(dir.join("lean-toolchain"), tc)?;
        fs::write(
            dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage pkg\n@[default_target]\nlean_lib Pkg\n",
        )?;
        fs::write(dir.join("Pkg/A.lean"), "theorem a_ok : 1 + 1 = 2 := rfl\n")?;
        fs::write(
            dir.join("Pkg.lean"),
            "import Pkg.A\ntheorem root_ok : 2 + 2 = 4 := rfl\n",
        )?;
        let canon = dir.canonicalize()?;
        let cfg = resolve_project_config(&canon)?;
        let lake_bin = cfg.lean_bin.parent().expect("lean bin parent").join("lake");
        let stock_st = Command::new(&lake_bin)
            .current_dir(&canon)
            .env("SANDBOXED_ALLOW_RAW_LAKE", "1")
            .arg("build")
            .status()?;
        anyhow::ensure!(stock_st.success(), "stock lake build failed");
        // Simulate a sticky CI cache with fresh Lake `.trace`/`.hash` artifacts, skewed mtimes,
        // and no `.turbo_verified_sources.json` / empty CAS store.
        let _ = fs::remove_file(canon.join(".lake/build/.turbo_verified_sources.json"));
        let mut store = TurboStore::open(Some(&canon.join(".turbo-store")))?;
        reset_lake_inputs_tag_memo();
        let rep =
            build_project_modules_native(&mut store, &canon, &[], "trusted", 2, false, true, None)?;
        assert_eq!(
            rep.modules_compiled, 0,
            "fresh stock Lake artifacts with valid .trace/.hash must warm-adopt without recompiling"
        );
        assert!(
            canon
                .join(".lake/build/.turbo_verified_sources.json")
                .is_file(),
            "warm-adopted build must persist root .turbo_verified_sources.json"
        );
        crate::zygote::purge_snapshot_dir(&dir);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_s1_module_builder_public_api_surface_pinned() {
        use crate::module_builder as mb;
        let _: fn(&mb::ProjectConfig, &[String]) -> Result<mb::ModuleDag> = mb::build_module_dag;
        let _: fn(&mb::ProjectConfig, &[String], bool) -> Result<mb::ModuleDag> =
            mb::build_module_dag_with_trust;
        let _: fn(
            &mut TurboStore,
            &Path,
            &[String],
            &str,
            i64,
            bool,
            bool,
            Option<&BTreeMap<String, String>>,
        ) -> Result<mb::NativeBuildReport> = mb::build_project_modules_native;
        let _: fn(&TurboStore, &Path, &str) -> Result<crate::pack::ExportInclusionFilter> =
            mb::build_cone_export_filter;
        let _: fn(&str) -> String = mb::clean_lake_ident;
        let _: fn(&[String], &[String]) -> Vec<String> = mb::compose_flat_filtered_args;
        let _: fn(&Path) -> Result<String> = mb::compute_dep_export_olean_digest;
        let _: fn(&Path) -> Result<String> = mb::compute_dep_meta_olean_digest;
        let _: fn(&[String]) -> Result<Option<String>> = mb::compute_lean_args_digest;
        let _: fn(
            &mb::ProjectConfig,
            &mb::ModuleNode,
            &[(String, String)],
            bool,
        ) -> Result<String> = mb::compute_module_cas_key;
        let _: fn(
            &mb::ProjectConfig,
            &mb::ModuleNode,
            &[(String, String)],
            bool,
            &[(String, String)],
        ) -> Result<String> = mb::compute_module_cas_key_with_dynlibs;
        let _: fn(&Path) -> Result<String> = mb::compute_olean_artifact_set_digest;
        let _: fn(&Path) -> Result<mb::HydrateTracesReport> = mb::hydrate_project_traces;
        let _: fn(&str) -> bool = mb::is_allowed_lean_arg;
        let _: fn(&[u8]) -> u64 = mb::lake_hash_bytes;
        let _: fn(&str) -> u64 = mb::lake_hash_name;
        let _: fn(&str) -> u64 = mb::lake_hash_pkg_id;
        let _: fn(&str) -> u64 = mb::lake_hash_text;
        let _: fn(u64, u64) -> u64 = mb::lake_mix_hash;
        let _: fn(&[u8], u64) -> u64 = mb::lake_murmur64a;
        let _: fn(&str, Option<&str>) -> String = mb::lean_mk_module_initialization_stem;
        let _: fn(&mb::LeanName, &str) -> String = mb::lean_name_mangle;
        let _: fn(&str) -> String = mb::lean_string_mangle;
        let _: fn(&str) -> String = mb::module_name_to_rel_slash;
        let _: fn(&mb::PackageConfig) -> Vec<String> = mb::package_default_lean_args;
        let _: fn(&str) -> Vec<String> = mb::parse_header_imports;
        let _: fn(&str) -> mb::HeaderInfo = mb::parse_header_info;
        let _: fn(&Path, bool) -> Result<(PathBuf, Vec<mb::ManifestPackageEntry>, Option<String>)> =
            mb::parse_lake_manifest;
        let _: fn(&Path, &Path, bool) -> Result<mb::PackageConfig> = mb::parse_lakefile_lean;
        let _: fn(&Path, &Path, bool) -> Result<mb::PackageConfig> = mb::parse_lakefile_toml;
        let _: fn(&[u8]) -> Option<(Vec<mb::ParsedImport>, bool)> = mb::parse_olean_binary_imports;
        let _: fn() = mb::reset_lake_inputs_tag_memo;
        let _: fn(&mb::PackageConfig, &Path) -> Vec<String> = mb::resolve_file_lean_args_in_package;
        let _: fn(&Path, bool) -> Result<mb::PackageConfig> = mb::resolve_package_config;
        let _: fn(&Path) -> Result<mb::ProjectConfig> = mb::resolve_project_config;
        let _: fn(&Path, bool) -> Result<mb::ProjectConfig> = mb::resolve_project_config_with_trust;
        let _: fn(&Path, &str) -> Result<(PathBuf, String, PathBuf, PathBuf)> =
            mb::resolve_toolchain_compiler;
        let _: fn(&Path, &str, bool) -> Result<(PathBuf, String, PathBuf, PathBuf)> =
            mb::resolve_toolchain_compiler_with_trust;
        let _: fn(&mut TurboStore, bool, PathBuf, Vec<String>, usize) -> Result<()> =
            mb::run_seed_oleans_command;
        let _: fn(&Path, Option<&Path>) -> Result<Vec<String>> = mb::try_resolve_lean_args_for_path;
        let _: fn(&[String]) -> Result<Vec<String>> = mb::validate_effective_lean_args;
        let _: fn(
            &mb::ProjectConfig,
            &mb::ModuleDag,
            &mb::ModuleNode,
            &str,
            Option<&str>,
            bool,
        ) -> Result<()> = mb::write_lake_module_hashes_and_trace;
        assert_eq!(mb::LAKE_NIL_HASH, 1723);
        assert!(!mb::FLEET_SYSTEM_ELAN_ROOTS.is_empty());
        let _ = (
            std::mem::size_of::<mb::GlobSpec>(),
            std::mem::size_of::<mb::LeanNamePart>(),
            std::mem::size_of::<mb::LeanOptionValue>(),
            std::mem::size_of::<mb::LeanOptionsMap>(),
            std::mem::size_of::<mb::ExternLibConfig>(),
            std::mem::size_of::<mb::HeaderInfo>(),
            std::mem::size_of::<mb::HydrateTracesReport>(),
            std::mem::size_of::<mb::InputTargetConfig>(),
            std::mem::size_of::<mb::LeanExeConfig>(),
            std::mem::size_of::<mb::LeanLibConfig>(),
            std::mem::size_of::<mb::LeanName>(),
            std::mem::size_of::<mb::ManifestPackageEntry>(),
            std::mem::size_of::<mb::ModuleDag>(),
            std::mem::size_of::<mb::ModuleNode>(),
            std::mem::size_of::<mb::NativeBuildReport>(),
            std::mem::size_of::<mb::PackageConfig>(),
            std::mem::size_of::<mb::ParsedImport>(),
            std::mem::size_of::<mb::ProjectConfig>(),
            std::mem::size_of::<mb::SharedLibSpec>(),
            std::mem::size_of::<mb::DepImportVisibility>(),
            std::mem::size_of::<mb::ImportSite>(),
            std::mem::size_of::<mb::CachedPkgManifest>(),
            std::mem::size_of::<mb::CutoffPinBaseline>(),
            std::mem::size_of::<mb::DepImportMemo>(),
            std::mem::size_of::<mb::DiscoveredModuleSpec>(),
            std::mem::size_of::<mb::LakeClosureCache>(),
            std::mem::size_of::<mb::LakeModuleExportInfo>(),
            std::mem::size_of::<mb::ModuleArtifactTierDigests>(),
            std::mem::size_of::<mb::OwnedImportPinSpec>(),
            std::mem::size_of::<mb::ReplayLookupBatchCache>(),
            std::mem::size_of::<mb::ResolvedExeLinkTarget>(),
            std::mem::size_of::<mb::ToolchainExecutables>(),
            std::mem::size_of::<mb::TrustedAssuranceSurface>(),
            std::mem::size_of::<mb::VerifiedDepManifest>(),
            std::mem::size_of::<mb::VerifiedDepModuleEntry>(),
            std::mem::size_of::<mb::VerifiedFastStoreAuthority>(),
        );
    }
}
