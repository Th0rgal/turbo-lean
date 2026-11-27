use anyhow::Result;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use walkdir::WalkDir;

use crate::db::{BlobEntry, TurboStore};
use crate::pack;
use crate::splitter::split_lean_source;

use super::*;

    #[cfg(unix)]
    #[test]
    fn cached_lake_environments_cannot_supply_verifier_executables() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo-cached-tools-{}-{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        let store = TurboStore::open(Some(&dir.join("store")))?;
        let key = TurboStore::compute_lake_env_key(&dir);
        let poisoned = HashMap::from([
            (
                "PATH".into(),
                dir.join(".lake/build/bin").to_string_lossy().into_owned(),
            ),
            (
                "LAKE".into(),
                dir.join("lake").to_string_lossy().into_owned(),
            ),
            ("LEAN".into(), "lean".into()),
            ("LEANC".into(), "leanc".into()),
        ]);
        store.put_lake_env(&key, &poisoned)?;
        let tools =
            crate::module_builder::ToolchainExecutables::resolve(&dir, &detect_toolchain(&dir))?;
        let (cached, hit) = resolve_lake_env(&store, &dir)?;
        assert!(hit);
        let shared = resolve_or_share_lake_env(&store, &dir, &key)?.unwrap().0;
        for env in [cached, shared] {
            assert_eq!(env["PATH"], tools.path());
            for (name, path) in [
                ("LEAN", &tools.lean),
                ("LAKE", &tools.lake),
                ("LEANC", &tools.leanc),
            ] {
                assert_eq!(env[name], path.to_string_lossy());
            }
        }
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_optout_installed_toolchain_env_child() -> Result<()> {
        use crate::worktree_test_support::snapshot;
        let Some(root) = std::env::var_os("TURBO_TEST_ENV_ROOT").map(PathBuf::from) else {
            return Ok(());
        };
        let project = root.join("project");
        let before = snapshot(&project)?;
        let store = TurboStore::open(Some(&root.join("env-cache")))?;
        if std::env::var_os("TURBO_TEST_MISSING_LEAN").is_some() {
            for err in [
                resolve_lake_env(&store, &project).unwrap_err(),
                resolve_or_share_lake_env(&store, &project, "uncached-share").unwrap_err(),
            ] {
                assert!(
                    err.to_string().contains("fail-closed toolchain gate"),
                    "{err:#}"
                );
            }
        } else {
            let (env, cached) = resolve_lake_env(&store, &project)?;
            assert!(!cached, "fixture must miss both environment caches");
            let shared = resolve_or_share_lake_env(&store, &project, "uncached-share")?
                .unwrap()
                .0;
            let prefix = fs::read_to_string(root.join("prefix"))?;
            for env in [&env, &shared] {
                assert_eq!(env["LAKE"], format!("{}/bin/lake", prefix.trim()));
                let lean_paths: Vec<_> = std::env::split_paths(&env["LEAN_PATH"]).collect();
                assert!(lean_paths.contains(&project.join(".lake/build/lib/lean")));
                assert!(lean_paths.contains(&PathBuf::from(prefix.trim()).join("lib/lean")));
            }
            assert!(resolve_lake_env(&store, &project)?.1);
        }
        assert!(
            !root.join("lake-invoked").exists(),
            "environment resolution invoked Lake"
        );
        assert_eq!(
            before,
            snapshot(&project)?,
            "environment resolution changed .lake"
        );
        fs::write(root.join("done"), b"")?;
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_optout_installed_toolchain_preserves_missing_and_stale_lean_config() -> Result<()> {
        use crate::worktree_test_support::{snapshot, LakeTree, TestChild};
        use std::os::unix::fs::PermissionsExt;
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for state in ["missing", "stale", "missing-compiler"] {
            let tree = LakeTree::new("path_toolchain", &[("P/A.lean", "def value : Nat := 1\n")])?;
            fs::remove_file(tree.project.join("lakefile.toml"))?;
            let config = tree.project.join("lakefile.lean");
            fs::write(&config, "import Lake\nopen Lake DSL\npackage fixture where\nlean_lib P where\n  globs := #[.submodules `P]\n")?;
            tree.lake(&["build", "P"])?;
            let env = spawn_lake_env(&tree.project)?;
            let lean = PathBuf::from(resolve_lean_bin(&tree.project)?);
            let prefix = Command::new(&lean).arg("--print-prefix").output()?;
            anyhow::ensure!(prefix.status.success(), "fixture Lean prefix query failed");
            fs::write(tree.root.join("prefix"), prefix.stdout)?;
            let bin = tree.root.join("path/bin");
            fs::create_dir_all(&bin)?;
            if state != "missing-compiler" {
                std::os::unix::fs::symlink(&lean, bin.join("lean"))?;
            }
            // Instrument the real Lake executable: a regression must also fail if loading
            // a config happens to preserve identical artifact bytes.
            let lake = bin.join("lake");
            let quote =
                |p: &Path| format!("'{}'", p.display().to_string().replace('\'', "'\"'\"'"));
            fs::write(
                &lake,
                format!(
                    "#!/bin/sh\nprintf invoked > {}\nexec {} \"$@\"\n",
                    quote(&tree.root.join("lake-invoked")),
                    quote(Path::new(&env["LAKE"]))
                ),
            )?;
            fs::set_permissions(&lake, fs::Permissions::from_mode(0o755))?;
            if state == "stale" {
                fs::write(
                    &config,
                    format!(
                        "{}\n-- stale compiled Lake config\n",
                        fs::read_to_string(&config)?
                    ),
                )?;
                fs::File::options()
                    .write(true)
                    .open(&config)?
                    .set_modified(
                        std::time::SystemTime::now() + std::time::Duration::from_secs(2),
                    )?;
            } else {
                let compiled = WalkDir::new(tree.project.join(".lake"))
                    .into_iter()
                    .collect::<std::result::Result<Vec<_>, _>>()?
                    .into_iter()
                    .find(|e| e.file_name() == "lakefile.olean")
                    .expect("real compiled Lean Lake config");
                fs::remove_file(compiled.path())?;
            }
            tree.opt_out()?;
            if state == "missing-compiler" {
                fs::write(
                    tree.project.join("lean-toolchain"),
                    "leanprover/lean4:v99.99.99\n",
                )?;
            }
            tree.prepare_snapshot(".lake/build/lib/lean/P/A.olean")?;
            let before = snapshot(&tree.project)?;
            let mut command =
                TestChild::command("lake_build::tests::test_optout_installed_toolchain_env_child")?;
            command
                .env("TURBO_TEST_ENV_ROOT", &tree.root)
                .env("PATH", &bin)
                .env("HOME", tree.root.join("isolated/a/b/home"))
                // Register the installed toolchain explicitly; verification never trusts PATH discovery.
                .env(
                    "ELAN_HOME",
                    lean.ancestors().nth(4).expect("installed Elan toolchain"),
                )
                .env("TURBO_LEAN_HOME", tree.root.join("cache"))
                .env("TURBO_LEAN_STAGING_DIR", tree.root.join("staging"))
                .env("TURBO_LEAN_ALLOW_TOOLCHAIN_FALLBACK", "0")
                .env_remove("LEAN_PATH");
            if state == "missing-compiler" {
                command.env("TURBO_TEST_MISSING_LEAN", "1");
            }
            let mut child = TestChild::spawn(&mut command)?;
            child.finish(&tree.root.join("done"))?;
            assert_eq!(
                before,
                snapshot(&tree.project)?,
                "{state} config changed .lake"
            );
        }
        Ok(())
    }

    #[test]
    fn seeding_rejects_invalid_config_before_publishing() -> Result<()> {
        let dir =
            std::env::temp_dir().join(format!("turbo_seed_options_{}", crate::pack::next_tmp_id()));
        let project = dir.join("project");
        fs::create_dir_all(&project)?;
        let file = project.join("Demo.lean");
        let source = "theorem seed_options : True := by trivial\n";
        fs::write(&file, source)?;
        let split = split_lean_source(source, &[]);
        assert_eq!(split.shards.len(), 1);
        let key = compute_shard_key("test", &split.shards[0]);
        let splits = vec![(file, source.to_string(), split)];
        let mut store = TurboStore::open(Some(&dir.join("store")))?;
        for config in [
            "name = [",
            "name = \"bad\"\nmoreLeanArgs = [\"--plugin=bad.so\"]\n",
        ] {
            fs::write(project.join("lakefile.toml"), config)?;
            let err = seed_project_theorem_shards_from_splits(
                &mut store, &project, "test", "trusted", false, &splits,
            )
            .unwrap_err();
            assert!(format!("{err:#}").contains("Failed to resolve Lean options"));
            assert!(store
                .batch_get_theorem_shards_readonly(std::slice::from_ref(&key), "trusted")?
                .is_empty());
            let count: i64 = store
                .conn
                .query_row("SELECT COUNT(*) FROM actions", [], |r| r.get(0))?;
            assert_eq!(count, 0, "invalid configuration must publish no entries");
        }
        // Standalone projects with no Lake config still have known empty options.
        fs::remove_file(project.join("lakefile.toml"))?;
        assert_eq!(
            seed_project_theorem_shards_from_splits(
                &mut store, &project, "test", "trusted", false, &splits,
            )?,
            (1, 1)
        );
        assert!(store.has_cached_action_readonly(&key, "trusted")?);
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_imported_olean_modification_invalidates_shard_key() {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let prev_lp = std::env::var_os("LEAN_PATH");
        std::env::remove_var("LEAN_PATH");
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_test_olean_inv_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let lib_dir = tmp_dir.join("lib");
        let _ = fs::remove_dir_all(&tmp_dir);
        fs::create_dir_all(lib_dir.join("Foo")).expect("create dummy LEAN_PATH dir");

        let olean_path = lib_dir.join("Foo/Bar.olean");
        let mut olean_bytes = vec![0x42u8; 256];
        fs::write(&olean_path, &olean_bytes).expect("write initial dummy .olean");

        let src = "import Foo.Bar\n\ntheorem my_thm : 1 + 1 = 2 := by rfl\n";
        let lp_str = lib_dir.to_string_lossy().to_string();

        let dep_hashes_v1 = compute_imported_olean_interface_hashes(src, &tmp_dir, Some(&lp_str));
        assert!(dep_hashes_v1.len() == 1 && dep_hashes_v1[0].starts_with("Foo.Bar:"));

        let split_v1 = split_lean_source(src, &dep_hashes_v1);
        assert_eq!(split_v1.shards.len(), 1);
        let shard_v1 = &split_v1.shards[0];
        let key_v1 = compute_shard_key("leanprover/lean4:v4.35.0", shard_v1);

        // Modify 1 byte inside the .olean file in place (preserving length)
        olean_bytes[128] ^= 0xFF;
        fs::write(&olean_path, &olean_bytes).expect("modify dummy .olean in place");

        let dep_hashes_v2 = compute_imported_olean_interface_hashes(src, &tmp_dir, Some(&lp_str));
        assert!(dep_hashes_v2.len() == 1 && dep_hashes_v1 != dep_hashes_v2);

        let split_v2 = split_lean_source(src, &dep_hashes_v2);
        let shard_v2 = &split_v2.shards[0];
        let key_v2 = compute_shard_key("leanprover/lean4:v4.35.0", shard_v2);

        assert!(
            shard_v1.cone_env_hash != shard_v2.cone_env_hash
                && shard_v1.prefix_env_hash != shard_v2.prefix_env_hash
                && key_v1 != key_v2
        );

        let user_tc_dir = tmp_dir.join("toolchains/ext/lib/lean");
        let sysroot_root = tmp_dir.join("fake_lean_prefix");
        let sysroot_lib = sysroot_root.join("lib/lean");
        fs::create_dir_all(user_tc_dir.join("UserPkg")).unwrap();
        fs::create_dir_all(sysroot_root.join("bin")).unwrap();
        fs::create_dir_all(sysroot_lib.join("Init")).unwrap();
        fs::write(sysroot_root.join("bin/lean"), b"stub").unwrap();
        let user_olean = user_tc_dir.join("UserPkg/Mod.olean");
        fs::write(&user_olean, [0x11u8; 128]).unwrap();
        fs::write(sysroot_lib.join("Init/Core.olean"), [0x22u8; 128]).unwrap();
        let mixed_lp = format!("{}:{}", user_tc_dir.display(), sysroot_lib.display());
        let mixed_src = "import UserPkg.Mod\nimport Init.Core\ntheorem t : True := trivial\n";
        let mixed_h1 =
            compute_imported_olean_interface_hashes(mixed_src, Path::new(""), Some(&mixed_lp));
        assert!(mixed_h1.iter().any(|e| e.starts_with("UserPkg.Mod:")));
        assert!(!mixed_h1.iter().any(|e| e.starts_with("Init.Core:")));
        fs::write(&user_olean, [0x33u8; 128]).unwrap();
        let mixed_h2 =
            compute_imported_olean_interface_hashes(mixed_src, Path::new(""), Some(&mixed_lp));
        assert_ne!(mixed_h1, mixed_h2);

        let local_lean_lib = tmp_dir.join(".lake/build/lib/lean");
        fs::create_dir_all(local_lean_lib.join("UserPkg")).unwrap();
        fs::write(local_lean_lib.join("UserPkg/Mod.olean"), [0x77u8; 128]).unwrap();
        let project_first = compute_imported_olean_interface_hashes(mixed_src, &tmp_dir, None);
        assert_ne!(project_first, mixed_h2);
        let project_user_mod = project_first
            .iter()
            .find(|x| x.starts_with("UserPkg.Mod:"))
            .unwrap()
            .clone();
        assert!(!mixed_h2.contains(&project_user_mod));
        let explicit_lp_with_project =
            compute_imported_olean_interface_hashes(mixed_src, &tmp_dir, Some(&mixed_lp));
        assert!(explicit_lp_with_project.contains(&project_user_mod));

        std::env::set_var("LEAN_PATH", &mixed_lp);
        let caller_env_with_project =
            compute_imported_olean_interface_hashes(mixed_src, &tmp_dir, None);
        assert_eq!(caller_env_with_project, explicit_lp_with_project);
        let remote_lp = resolve_remote_lean_path(&tmp_dir, None);
        assert!(remote_lp.starts_with(local_lean_lib.to_string_lossy().as_ref()));
        assert!(remote_lp.contains(user_tc_dir.to_string_lossy().as_ref()));
        assert_eq!(
            compute_imported_olean_interface_hashes(mixed_src, &tmp_dir, Some(&remote_lp)),
            explicit_lp_with_project
        );
        let mut lake_ev = HashMap::new();
        lake_ev.insert(
            "LEAN".to_string(),
            sysroot_root.join("bin/lean").to_string_lossy().to_string(),
        );
        lake_ev.insert(
            "LEAN_PATH".to_string(),
            format!("{}:{}", local_lean_lib.display(), sysroot_lib.display()),
        );
        merge_caller_lean_path(&mut lake_ev);
        assert_eq!(
            lake_ev["LEAN_PATH"],
            format!(
                "{}:{}:{}",
                local_lean_lib.display(),
                user_tc_dir.display(),
                sysroot_lib.display()
            )
        );

        let second_tc_root = tmp_dir.join("second_toolchain");
        let second_tc_lib = second_tc_root.join("lib/lean");
        fs::create_dir_all(second_tc_root.join("bin")).unwrap();
        fs::create_dir_all(second_tc_lib.join("ExtraTc")).unwrap();
        fs::write(second_tc_root.join("bin/lean"), b"stub").unwrap();
        let extra_tc_olean = second_tc_lib.join("ExtraTc/Mod.olean");
        fs::write(&extra_tc_olean, [0x91u8; 128]).unwrap();
        let extra_src = "import ExtraTc.Mod\ntheorem t : True := trivial\n";
        let extra_lp = second_tc_lib.to_string_lossy().to_string();
        let extra_h1 =
            compute_imported_olean_interface_hashes(extra_src, &tmp_dir, Some(&extra_lp));
        assert!(extra_h1.iter().any(|e| e.starts_with("ExtraTc.Mod:")));
        fs::write(&extra_tc_olean, [0x92u8; 128]).unwrap();
        let extra_h2 =
            compute_imported_olean_interface_hashes(extra_src, &tmp_dir, Some(&extra_lp));
        assert_ne!(extra_h1, extra_h2);

        let pkg_root_first = tmp_dir.join("pkg_root_first");
        let pkg_root_second = tmp_dir.join("pkg_root_second");
        fs::create_dir_all(pkg_root_first.join("ShadowPkg")).unwrap();
        fs::create_dir_all(pkg_root_second.join("ShadowPkg")).unwrap();
        let shadowed_olean = pkg_root_second.join("ShadowPkg/Sub.olean");
        fs::write(&shadowed_olean, [0xA1u8; 128]).unwrap();
        let shadow_lp = format!("{}:{}", pkg_root_first.display(), pkg_root_second.display());
        let shadow_src = "import ShadowPkg.Sub\ntheorem t : True := trivial\n";
        let shadow_h1 =
            compute_imported_olean_interface_hashes(shadow_src, &tmp_dir, Some(&shadow_lp));
        assert_eq!(shadow_h1, vec!["ShadowPkg.Sub:missing".to_string()]);
        fs::write(&shadowed_olean, [0xA2u8; 128]).unwrap();
        let shadow_h2 =
            compute_imported_olean_interface_hashes(shadow_src, &tmp_dir, Some(&shadow_lp));
        assert_eq!(shadow_h1, shadow_h2);
        let first_olean = pkg_root_first.join("ShadowPkg/Sub.olean");
        fs::write(&first_olean, [0xB1u8; 128]).unwrap();
        let shadow_h3 =
            compute_imported_olean_interface_hashes(shadow_src, &tmp_dir, Some(&shadow_lp));
        assert_ne!(shadow_h3, shadow_h1);
        assert!(shadow_h3[0].starts_with("ShadowPkg.Sub:"));
        assert!(!shadow_h3[0].ends_with(":missing"));

        match prev_lp {
            Some(v) => std::env::set_var("LEAN_PATH", v),
            None => std::env::remove_var("LEAN_PATH"),
        }
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_check_freshens_stale_lake_imports_with_lake_without_deleting() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir =
            std::env::temp_dir().join(format!("turbo_lean_lake_fresh_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(dir.join("P"))?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"p\"\n[[lean_lib]]\nname = \"P\"\n",
        )?;
        fs::write(dir.join("P/A.lean"), "def a : Nat := 1\n")?;
        fs::write(
            dir.join("P/B.lean"),
            "import P.A\ntheorem b : a = 1 := rfl\n",
        )?;
        let lake = |args: &[&str]| Command::new("lake").args(args).current_dir(&dir).output();
        assert!(
            lake(&["build", "P.B"])?.status.success(),
            "Lake fixture must build"
        );
        assert!(!worktree_auto_link_disabled(&dir));
        let old_olean = fs::read(dir.join(".lake/build/lib/lean/P/A.olean"))?;
        std::thread::sleep(std::time::Duration::from_millis(1100));
        fs::write(
            dir.join("P/A.lean"),
            "def a : Nat := 1\ndef a2 : Nat := 2\n",
        )?;
        let olean = |m: &str| dir.join(format!(".lake/build/lib/lean/P/{}.olean", m));
        assert_eq!(
            ensure_project_imports_fresh_for_check(&dir, &[dir.join("P/B.lean")])?,
            1
        );
        assert_ne!(
            fs::read(olean("A"))?,
            old_olean,
            "default must actually rebuild the import"
        );
        // Lake rebuilt the stale import in place of deleting it; nothing else was removed.
        assert!(olean("A").is_file() && olean("B").is_file());
        assert!(lake(&["build", "--no-build", "P.A"])?.status.success());
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_verified_import_stamps_refreshed_target_sidecars() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tree = crate::worktree_test_support::LakeTree::new(
            "refreshed_sidecars",
            &[
                ("P/A.lean", "def a : Nat := 1\n"),
                ("P/B.lean", "import P.A\ntheorem b : a = 1 := rfl\n"),
            ],
        )?;
        let targets = [tree.project.join("P/B.lean")];
        ensure_project_imports_fresh_inner(&tree.project, &targets, None, true, true)?;
        for suffix in ["olean.hash", "ilean.hash", "trace"] {
            let sidecar = tree
                .project
                .join(format!(".lake/build/lib/lean/P/A.{suffix}"));
            let original = fs::read(&sidecar)?;
            fs::write(&sidecar, "0")?;
            assert!(
                ensure_project_imports_fresh_inner(&tree.project, &targets, None, true, true)
                    .is_err(),
                "accepted {suffix}"
            );
            fs::write(&sidecar, original)?;
        }
        Ok(())
    }

    #[test]
    fn test_local_host_reads_remain_ineligible_for_stamp_reuse() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_host_stamp_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        fs::create_dir_all(dir.join("P"))?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"p\"\n[[lean_lib]]\nname = \"P\"\n",
        )?;
        fs::write(dir.join("P/A.lean"), "initialize stampEnv : Option String ← IO.getEnv \"TURBO_STAMP_TEST\"\ndef a : Nat := 1\n")?;
        fs::write(
            dir.join("P/B.lean"),
            "import P.A\ntheorem b : a = 1 := rfl\n",
        )?;
        assert!(Command::new("lake")
            .args(["build", "P.B"])
            .current_dir(&dir)
            .output()?
            .status
            .success());
        let target = [dir.join("P/B.lean")];
        assert_eq!(ensure_project_imports_fresh_for_check(&dir, &target)?, 1);
        let artifact = dir.join(".lake/build/lib/lean/P/A.olean");
        let before = fs::metadata(&artifact)?.modified()?;
        assert!(!load_verified_project_manifest(&dir)
            .is_some_and(|m| m.modules.contains_key("P/A.lean")));
        for _ in 0..2 {
            crate::module_builder::reset_lake_inputs_tag_memo();
            assert_eq!(ensure_project_imports_fresh_for_check(&dir, &target)?, 1);
            assert!(fs::metadata(&artifact)?.modified()? >= before);
        }
        fs::write(dir.join("P/A.lean"), "initialize stampEnv : Option String ← IO.getEnv \"TURBO_STAMP_TEST_CHANGED\"\ndef a : Nat := 1\n")?;
        assert_eq!(ensure_project_imports_fresh_for_check(&dir, &target)?, 1);
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[test]
    fn test_untracked_include_str_remains_ineligible_for_stamp_reuse() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_include_stamp_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        fs::create_dir_all(dir.join("P"))?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            dir.join("lakefile.toml"),
            "name = \"p\"\n[[lean_lib]]\nname = \"P\"\n",
        )?;
        fs::write(dir.join("P/data.txt"), "before")?;
        fs::write(
            dir.join("P/A.lean"),
            "def data : String := include_str \"data.txt\"\n",
        )?;
        fs::write(dir.join("P/B.lean"), "import P.A\n")?;
        let output = Command::new("lake")
            .args(["build", "P.B"])
            .current_dir(&dir)
            .output()?;
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let target = [dir.join("P/B.lean")];
        assert_eq!(ensure_project_imports_fresh_for_check(&dir, &target)?, 1);
        let artifact = dir.join(".lake/build/lib/lean/P/A.olean");
        let before = fs::read(&artifact)?;
        fs::write(dir.join("P/data.txt"), "after")?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        assert_eq!(ensure_project_imports_fresh_for_check(&dir, &target)?, 1);
        assert_ne!(
            before,
            fs::read(&artifact)?,
            "data-only edit must rebuild the artifact"
        );
        assert!(!load_verified_project_manifest(&dir)
            .is_some_and(|m| m.modules.contains_key("P/A.lean")));
        let mut cfg = crate::module_builder::resolve_project_config(&dir)?;
        let pkg = cfg.root_pkg.clone();
        let spec = crate::module_builder::resolve_module_in_package(&pkg, false, "P.A")
            .expect("dependency module");
        cfg.root_pkg.pkg_root = dir.join("consumer");
        cfg.dep_pkgs.push(pkg);
        let src = fs::read_to_string(dir.join("P/A.lean"))?;
        assert!(
            crate::module_builder::spec_source_has_disallowed_elab_host_effects(&cfg, &spec, &src)
        );
        let mut cache = crate::module_builder::LakeClosureCache::for_project(&cfg);
        assert!(crate::module_builder::lake_closure_export_info(
            &cfg,
            &spec,
            false,
            &mut cache,
            &mut HashSet::new(),
        )
        .is_none());
        fs::remove_dir_all(dir)?;
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_optout_stale_import_check_preserves_lake_tree_with_and_without_config() -> Result<()> {
        use crate::worktree_test_support::{assert_stale_error, snapshot, LakeTree};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        for lake_config in [true, false] {
            let tree = LakeTree::imports("stale_check")?;
            tree.opt_out()?;
            tree.stale_import()?;
            // A valid manifest exercises the rewrite branch, as well as stale artifact removal.
            let cfg = crate::module_builder::resolve_project_config(&tree.project)?;
            let manifest = crate::module_builder::VerifiedDepManifest {
                pkg_name: cfg.root_pkg.name.clone(),
                toolchain: cfg.toolchain.clone(),
                lean_githash: cfg.lean_githash.clone(),
                pkg_config_digest: cfg.root_pkg.config_digest.clone(),
                lake_inputs_digest: crate::module_builder::workspace_lake_inputs_digest(&cfg)?,
                workspace_config_digest: cfg.canonical_config_digest.clone(),
                allowed_axioms: crate::splitter::allowed_axioms(),
                kernel_policy_digest: crate::splitter::current_kernel_policy_digest(),
                modules: std::collections::BTreeMap::from([(
                    "P/A.lean".into(),
                    crate::module_builder::VerifiedDepModuleEntry {
                        src_blake3: "previous source".into(),
                        olean_artifact_digest: "previous artifact".into(),
                        lake_inputs_digest: crate::module_builder::workspace_lake_inputs_digest(
                            &cfg,
                        )?,
                        kernel_audited: true,
                        import_olean_digests: Default::default(),
                        artifact_stat_fingerprint: String::new(),
                        ..Default::default()
                    },
                )]),
                ..Default::default()
            };
            fs::write(
                verified_sources_manifest_path(&tree.project),
                serde_json::to_vec(&manifest)?,
            )?;
            assert!(load_verified_project_manifest(&tree.project).is_some());
            if !lake_config {
                fs::remove_file(tree.project.join("lakefile.toml"))?;
            }
            tree.prepare_snapshot(".lake/build/lib/lean/P/A.olean")?;
            let before = snapshot(&tree.project)?;
            let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
            // Cover both the single-file and directory check callers.
            for target in [tree.project.join("P/Target.lean"), tree.project.join("P")] {
                let err = crate::check::run_check_command(
                    &mut store,
                    false,
                    true,
                    target,
                    None,
                    tree.project.clone(),
                    None,
                    false,
                    None,
                )
                .unwrap_err();
                assert_stale_error(&err);
                assert_eq!(
                    snapshot(&tree.project)?,
                    before,
                    "check mutated Lake tree (config={lake_config})"
                );
            }
        }
        for manifest_backed in [false, true] {
            let tree = LakeTree::imports("missing_trace")?;
            let mut store = TurboStore::open(Some(&tree.root.join("cache")))?;
            if manifest_backed {
                crate::module_builder::build_project_modules_native(
                    &mut store,
                    &tree.project,
                    &["P.Middle".into()],
                    "trusted-internal",
                    1,
                    false,
                    true,
                    None,
                )?;
                assert!(verified_sources_manifest_path(&tree.project).is_file());
            } else {
                assert!(!verified_sources_manifest_path(&tree.project).exists());
            }
            fs::remove_file(tree.project.join(".lake/build/lib/lean/P/A.trace"))?;
            tree.opt_out()?;
            tree.prepare_snapshot(".lake/build/lib/lean/P/A.olean")?;
            let before = snapshot(&tree.project)?;
            let err = crate::check::run_check_command(
                &mut store,
                false,
                true,
                tree.project.join("P/Target.lean"),
                None,
                tree.project.clone(),
                None,
                false,
                None,
            )
            .unwrap_err();
            assert_stale_error(&err);
            assert_eq!(
                snapshot(&tree.project)?,
                before,
                "missing-trace check mutated Lake tree (manifest={manifest_backed})"
            );
        }
        Ok(())
    }

    /// A project with Lake file inputs, laid out by hand because `LakeTree` uses a `lakefile.toml`
    /// (which cannot declare inputs). `Smoke.Shared` is deliberately buildable by two libraries.
    fn input_bearing_tree(tag: &str) -> Result<PathBuf> {
        let proj = std::env::temp_dir().join(format!(
            "turbo_lake_inputs_{tag}_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&proj);
        fs::create_dir_all(proj.join("Smoke"))?;
        fs::create_dir_all(proj.join("Data"))?;
        fs::create_dir_all(proj.join(".lake/build/lib/lean/Smoke"))?;
        fs::write(
            proj.join("lean-toolchain"),
            include_str!("../../../../lean/lean-toolchain"),
        )?;
        fs::write(
            proj.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n@[default_target]\nlean_lib «Smoke» where\n  globs := #[.one `Smoke.A, .one `Smoke.Shared]\n  needs := #[smokeSources]\nlean_lib Other where\n  roots := #[`Other]\nlean_lib Later where\n  globs := #[.one `Smoke.Shared]\n",
        )?;
        fs::write(proj.join("Smoke/A.lean"), "def a : Nat := 1\n")?;
        fs::write(proj.join("Smoke/Shared.lean"), "def s : Nat := 1\n")?;
        fs::write(proj.join("Other.lean"), "def o : Nat := 1\n")?;
        fs::write(proj.join("Data/a.sol"), "contract A {}")?;
        Ok(proj)
    }

    /// `lake build <Mod>` builds the module under Lake's own attribution -- the **last** library
    /// that can build it -- and that library's `extraDep` may carry none of the `needs` naming the
    /// input the module reads. Lake then finds the dep trace unchanged by an input edit and reports
    /// the module up to date, so the "refresh" leaves the stale `.olean` in place and the caller
    /// goes on to check against it. Deleting the artifacts first is not enough either: Lake can
    /// restore one from its artifact cache keyed on that same input-blind trace. The refresh must
    /// ask for the library instead.
    #[test]
    fn test_lake_refresh_targets_substitutes_the_input_bearing_library() -> Result<()> {
        let proj = input_bearing_tree("refresh_targets")?;
        if crate::module_builder::resolve_project_config(&proj).is_err() {
            let _ = fs::remove_dir_all(&proj);
            return Ok(());
        }
        let cfg = crate::module_builder::resolve_project_config(&proj)?;
        // The hazard is real: Lake attributes `Smoke.Shared` to `Later`, which has no `needs`.
        assert_eq!(
            crate::module_builder::resolve_module_in_package(&cfg.root_pkg, true, "Smoke.Shared")
                .expect("Smoke.Shared resolves")
                .target_name,
            "Later"
        );
        assert_eq!(
            lake_refresh_targets(&proj, &["Smoke.Shared".to_string()]),
            vec!["Smoke".to_string()],
            "a module an input-bearing library can build must be refreshed by library name"
        );
        assert_eq!(
            lake_refresh_targets(&proj, &["Smoke.A".to_string()]),
            vec!["Smoke".to_string()]
        );
        // A module no input-bearing library can build is passed through untouched, so the refresh
        // stays as narrow as it was for everything the inputs cannot reach.
        assert_eq!(
            lake_refresh_targets(&proj, &["Other".to_string()]),
            vec!["Other".to_string()]
        );
        assert_eq!(
            lake_refresh_targets(
                &proj,
                &[
                    "Smoke.A".to_string(),
                    "Smoke.Shared".to_string(),
                    "Other".to_string()
                ]
            ),
            vec!["Smoke".to_string(), "Other".to_string()]
        );
        // A project without inputs keeps the exact module list it had before.
        let plain = std::env::temp_dir().join(format!(
            "turbo_lake_plain_targets_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        fs::create_dir_all(&plain)?;
        fs::write(
            plain.join("lean-toolchain"),
            include_str!("../../../../lean/lean-toolchain"),
        )?;
        fs::write(
            plain.join("lakefile.toml"),
            "name = \"plain\"\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n[[lean_exe]]\nname = \"runner\"\nroot = \"Main\"\n",
        )?;
        let mods = vec!["P.A".to_string(), "P.B".to_string()];
        assert_eq!(lake_refresh_targets(&plain, &mods), mods);
        assert_eq!(
            lake_refresh_targets(&plain, &["P.A".to_string(), "Main".to_string()]),
            vec!["@plain/runner:exe".to_string(), "P.A".to_string()],
            "a lean_exe root module must translate to @<pkg>/<exe>:exe so Lake relinks the binary"
        );
        let dep_dir = plain.join(".lake/packages/dep");
        fs::create_dir_all(dep_dir.join("Dep"))?;
        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep\"\n[[lean_lib]]\nname = \"Dep\"\nglobs = [\"Dep.+\"]\n",
        )?;
        fs::write(dep_dir.join("Dep/D.lean"), "def dVal : Nat := 1\n")?;
        fs::write(
            plain.join("lake-manifest.json"),
            "{\"version\":\"1.1.0\",\"packagesDir\":\".lake/packages\",\"packages\":[{\"type\":\"path\",\"name\":\"dep\",\"dir\":\".lake/packages/dep\"}]}\n",
        )?;
        assert_eq!(
            lake_refresh_targets(&plain, &["Dep.D".to_string()]),
            vec!["+Dep.D".to_string()],
            "a dependency module without input-bearing libs must be qualified with `+` so Lake builds it"
        );
        let _ = fs::remove_dir_all(&plain);
        let _ = fs::remove_dir_all(&proj);
        Ok(())
    }

    /// A manifest entry has to name the input bytes it was recorded against, and a *missing* entry
    /// has to read as stale once the package declares inputs.
    ///
    /// `build <OneLib>` re-stamps the manifest header for the whole package, and the lake-delegated
    /// refresh *deletes* the entries it hands to Lake, so "header current, entry absent" is exactly
    /// the state a partial rebuild leaves behind for the library it did not touch. Every other
    /// signal `ensure_project_imports_fresh_for_check` has -- the `.lean` source hash, the `.olean`
    /// mtime -- is unmoved by a `.sol` edit, so treating an absent entry as fresh accepted an
    /// `.olean` elaborated against bytes that are gone.
    ///
    /// The worktree opt-out turns the verdict into an error naming the stale modules, which is what
    /// lets this assert "stale" without running Lake.
    #[test]
    fn test_check_treats_absent_and_input_stale_manifest_entries_as_stale() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let proj = input_bearing_tree("manifest_entries")?;
        if crate::module_builder::resolve_project_config(&proj).is_err() {
            let _ = fs::remove_dir_all(&proj);
            return Ok(());
        }
        fs::write(
            proj.join("Smoke/B.lean"),
            "import Smoke.A\ntheorem b : a = 1 := rfl\n",
        )?;
        fs::write(
            proj.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        // A plausible warm `.lake/build`: the `.olean` exists and is newer than its source, so
        // every mtime check below reports fresh and only the manifest can object.
        let olean = proj.join(".lake/build/lib/lean/Smoke/A.olean");
        let mut store = TurboStore::open(Some(&proj.join(".turbo-test-store")))?;
        fs::remove_file(proj.join("turbo-lean.toml"))?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.A".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )?;
        fs::write(
            proj.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        fs::File::options()
            .write(true)
            .open(&olean)?
            .set_modified(std::time::SystemTime::now() + std::time::Duration::from_secs(2))?;
        let olean_digest = crate::module_builder::compute_olean_artifact_set_digest(&olean)?;

        let a_src = fs::read_to_string(proj.join("Smoke/A.lean"))?;
        type Entry = crate::module_builder::VerifiedDepModuleEntry;
        let write_manifest = |entry: Option<Entry>| -> Result<()> {
            let cfg = crate::module_builder::resolve_project_config(&proj)?;
            let manifest = crate::module_builder::VerifiedDepManifest {
                pkg_name: cfg.root_pkg.name.clone(),
                toolchain: cfg.toolchain.clone(),
                lean_githash: cfg.lean_githash.clone(),
                pkg_config_digest: cfg.root_pkg.config_digest.clone(),
                // Always the *current* digest: the point is that a current header must not vouch
                // for an entry that is absent or was recorded against older bytes.
                lake_inputs_digest: crate::module_builder::workspace_lake_inputs_digest(&cfg)?,
                workspace_config_digest: cfg.canonical_config_digest.clone(),
                allowed_axioms: crate::splitter::allowed_axioms(),
                kernel_policy_digest: crate::splitter::current_kernel_policy_digest(),
                modules: entry
                    .into_iter()
                    .map(|e| ("Smoke/A.lean".to_string(), e))
                    .collect(),
                ..Default::default()
            };
            fs::write(
                verified_sources_manifest_path(&proj),
                serde_json::to_vec(&manifest)?,
            )?;
            assert!(
                load_verified_project_manifest(&proj).is_some(),
                "the fixture manifest must be accepted, or the assertions below prove nothing"
            );
            assert!(
                !lake_inputs_changed_since_manifest(&proj),
                "the header must read as current, so only the entry is under test"
            );
            Ok(())
        };
        let fresh_entry = |inputs_digest: String| Entry {
            src_blake3: blake3::hash(a_src.as_bytes()).to_hex().to_string(),
            olean_artifact_digest: olean_digest.clone(),
            lake_inputs_digest: inputs_digest,
            kernel_audited: true,
            import_olean_digests: BTreeMap::new(),
            artifact_stat_fingerprint: String::new(),
            ..Default::default()
        };
        let verdict = || {
            crate::module_builder::reset_lake_inputs_tag_memo();
            ensure_project_imports_fresh_for_check(&proj, &[proj.join("Smoke/B.lean")])
                .map_err(|e| e.to_string())
        };
        let current = crate::module_builder::workspace_lake_inputs_digest(
            &crate::module_builder::resolve_project_config(&proj)?,
        )?;
        assert!(!current.is_empty(), "the fixture must declare inputs");

        // 1. A complete, current entry is fresh: this is not a blanket refusal.
        write_manifest(Some(fresh_entry(current.clone())))?;
        assert_eq!(verdict(), Ok(0), "a current entry must stay fresh");

        // 2. Entry recorded against older input bytes while the header is current.
        write_manifest(Some(fresh_entry("stale-digest".to_string())))?;
        let err = verdict().expect_err("an entry from older input bytes must be stale");
        assert!(err.contains("Smoke.A"), "{err}");

        // 3. Entry absent entirely, which is what a partial rebuild leaves behind.
        write_manifest(None)?;
        let err =
            verdict().expect_err("an absent entry must be stale for an input-bearing package");
        assert!(err.contains("Smoke.A"), "{err}");

        // 4. The same absent entry stays *fresh* once the package declares no inputs: there the
        // source hashes, sidecars, and mtimes are a complete signal and nothing changes for existing projects.
        fs::write(
            proj.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage demo\n@[default_target]\nlean_lib «Smoke» where\n  globs := #[.submodules `Smoke]\n",
        )?;
        fs::remove_file(proj.join("turbo-lean.toml"))?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.A".to_string()],
            "trusted-internal",
            1,
            false,
            true,
            None,
        )?;
        fs::write(
            proj.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        fs::File::options()
            .write(true)
            .open(&olean)?
            .set_modified(std::time::SystemTime::now() + std::time::Duration::from_secs(2))?;
        write_manifest(None)?;
        assert_eq!(
            verdict(),
            Ok(0),
            "a project without Lake inputs must keep its previous behaviour"
        );
        let _ = fs::remove_dir_all(&proj);
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_optout_preserves_preexisting_lake_inodes_modes_and_links() -> Result<()> {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let root = std::env::temp_dir().join(format!(
            "turbo_lake_preserve_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let project = root.join("project");
        let mut store = TurboStore::open(Some(&root.join("cache")))?;
        for (rel, mode) in [
            ("build/lib/lean/Readonly.olean", 0o444),
            ("build/lib/lean/Linked.ilean", 0o640),
            ("packages/pkg/A.olean", 0o644),
            ("packages/pkg/B.olean", 0o600),
            ("packages/pkg/.git/objects/pack/keep.pack", 0o640),
            ("cache/keep.barrel", 0o640),
        ] {
            let path = project.join(".lake").join(rel);
            fs::create_dir_all(path.parent().unwrap())?;
            fs::write(&path, b"preexisting artifact")?;
            fs::set_permissions(&path, fs::Permissions::from_mode(mode))?;
        }
        fs::hard_link(
            project.join(".lake/build/lib/lean/Linked.ilean"),
            root.join("external-link"),
        )?;
        let snapshot = || -> Result<Vec<_>> {
            let mut rows = Vec::new();
            for e in WalkDir::new(project.join(".lake")) {
                let e = e?;
                let m = e.metadata()?;
                rows.push((
                    e.path().to_path_buf(),
                    m.ino(),
                    m.mode(),
                    m.nlink(),
                    if m.is_file() {
                        fs::read(e.path())?
                    } else {
                        Vec::new()
                    },
                ));
            }
            rows.sort_by(|a, b| a.0.cmp(&b.0));
            Ok(rows)
        };
        let before = snapshot()?;
        let saved = std::env::var_os("TURBO_LEAN_NO_WORKTREE_LINK");
        for source in ["toml", "env", "cli"] {
            std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
            fs::write(
                project.join("turbo-lean.toml"),
                if source == "toml" {
                    "[worktree]\nauto_link = false\n"
                } else {
                    "[worktree]\nauto_link = true\n"
                },
            )?;
            if source == "env" {
                std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", "1");
            }
            if source == "cli" {
                use clap::Parser;
                let cli =
                    crate::Cli::try_parse_from(["turbo-lean", "--no-auto-worktree-link", "build"])?;
                crate::apply_global_cli_env(&cli);
            }
            assert_eq!(auto_hardlink_worktree_oleans_from_main_repo(&project), 0);
            // Same staging function used by build and pr-verify. It still ingests CAS bytes.
            let (outputs, blobs) = stage_lake_build_outputs(&store, &project)?;
            assert_eq!(outputs.len(), 2);
            assert_eq!(blobs.len(), 1);
            // Shared CAS restore used by build, ci-verify and module builds.
            let mut restore_outputs = outputs.clone();
            restore_outputs.push(BlobEntry {
                rel_path: ".lake/packages/pkg/A.olean".to_string(),
                ..outputs[0].clone()
            });
            assert_eq!(
                store.materialize_into_worktree(&project, "project", &restore_outputs)?,
                0
            );
            for rel_path in [
                ".lake/build/lib/lean/Missing.olean",
                ".lake/build/lib/lean/Readonly.olean",
            ] {
                let mut invalid = outputs.clone();
                invalid[0].rel_path = rel_path.to_string();
                invalid[0].blob_hash = blake3::hash(b"different artifact").to_hex().to_string();
                assert!(store
                    .materialize_into_worktree(&project, "project", &invalid)
                    .is_err());
            }
            assert_eq!(
                dedup_worktree_packages(&store, &project)?["status"],
                "worktree_link_disabled"
            );
            assert_eq!(
                snapshot()?,
                before,
                "{source} opt-out changed the existing .lake tree"
            );
        }
        match &saved {
            Some(v) => std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", v),
            None => std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK"),
        }
        // CAS ingest must still detach read-only/shared build artifacts when enabled.
        fs::write(
            project.join("turbo-lean.toml"),
            "[worktree]\nauto_link = true\n",
        )?;
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
        stage_lake_build_outputs(&store, &project)?;
        for rel in ["Readonly.olean", "Linked.ilean"] {
            let m = fs::metadata(project.join(".lake/build/lib/lean").join(rel))?;
            assert_eq!(m.nlink(), 1);
            assert_eq!(m.mode() & 0o777, 0o644);
        }
        match &saved {
            Some(v) => std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", v),
            None => std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK"),
        }
        drop(store);
        fs::remove_dir_all(root)?;
        Ok(())
    }

    #[test]
    fn test_dedup_worktree_packages_hardlinks_and_purges_barrels() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let saved_wt_env = std::env::var("TURBO_LEAN_NO_WORKTREE_LINK").ok();
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
        #[cfg(unix)]
        use std::os::unix::fs::MetadataExt;
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_dedup_pkgs_test_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let (cache_dir, wt1, wt2) = (
            tmp_dir.join("cache"),
            tmp_dir.join("wt1"),
            tmp_dir.join("wt2"),
        );

        let pkg1_dir = wt1.join(".lake/packages/mathlib/.lake/build/lib/lean/Mathlib");
        let pkg2_dir = wt2.join(".lake/packages/mathlib/.lake/build/lib/lean/Mathlib");
        fs::create_dir_all(&pkg1_dir)?;
        fs::create_dir_all(&pkg2_dir)?;

        let (olean1, olean2) = (pkg1_dir.join("Basic.olean"), pkg2_dir.join("Basic.olean"));
        let barrel1 = wt1.join(".lake/packages/mathlib/mathlib.barrel");

        let payload = vec![0xABu8; 2048];
        fs::write(&olean1, &payload)?;
        fs::write(&olean2, &payload)?;
        fs::write(&barrel1, vec![0xCDu8; 1024])?;

        assert_ne!(fs::metadata(&olean1)?.ino(), fs::metadata(&olean2)?.ino());
        let store = TurboStore::open(Some(&cache_dir))?;

        let rep1 = dedup_worktree_packages(&store, &wt1)?;
        assert!(
            rep1["status"] == "worktree_packages_deduped"
                && rep1["barrels_removed"] == 1
                && !barrel1.exists()
        );

        let rep2 = dedup_worktree_packages(&store, &wt2)?;
        assert!(
            rep2["status"] == "worktree_packages_deduped"
                && rep2["files_hardlinked"] == 1
                && rep2["bytes_saved"].as_u64().unwrap_or(0) >= 2048
        );
        assert_eq!(fs::metadata(&olean1)?.ino(), fs::metadata(&olean2)?.ino());

        let main_repo = tmp_dir.join("main_repo");
        let main_git = main_repo.join(".git/worktrees/wt_auto");
        let main_olean = main_repo.join(".lake/build/lib/lean/MainMod.olean");
        fs::create_dir_all(&main_git)?;
        fs::create_dir_all(main_olean.parent().unwrap())?;
        fs::write(main_git.join("commondir"), "../..\n")?;
        fs::write(&main_olean, vec![0xEFu8; 512])?;

        let wt_auto = tmp_dir.join("wt_auto");
        fs::create_dir_all(&wt_auto)?;
        fs::write(
            wt_auto.join(".git"),
            format!("gitdir: {}\n", main_git.display()),
        )?;
        assert_eq!(auto_hardlink_worktree_oleans_from_main_repo(&wt_auto), 1);
        let wt_main_olean = wt_auto.join(".lake/build/lib/lean/MainMod.olean");
        assert_ne!(
            fs::metadata(&main_olean)?.ino(),
            fs::metadata(&wt_main_olean)?.ino(),
            "worktree `.lake/build` artifacts must be copied with distinct inode (`nlink == 1`), never hardlinked"
        );
        assert_eq!(fs::metadata(&wt_main_olean)?.nlink(), 1);
        assert_eq!(fs::read(&wt_main_olean)?, fs::read(&main_olean)?);

        // Now verify that when a module or its transitive import differs in the worktree,
        // `auto_hardlink_worktree_oleans_from_main_repo` skips copying that module's `.olean`
        // and never copies `.turbo_verified_sources.json` or `.turbo_lean_verified_sources.json`.
        let main_git2 = main_repo.join(".git/worktrees/wt_diff");
        fs::create_dir_all(&main_git2)?;
        fs::write(main_git2.join("commondir"), "../..\n")?;
        fs::create_dir_all(main_repo.join("Guest"))?;
        fs::create_dir_all(main_repo.join("submission/InitECandidate/Solver"))?;
        fs::write(
            main_repo.join("Guest/Ast.lean"),
            "namespace Guest\ndef totalCols : Nat := 928\nend Guest\n",
        )?;
        fs::write(
            main_repo.join("submission/InitECandidate/Solver/GuestStepBound.lean"),
            "import Guest.Ast\ntheorem t : Guest.totalCols = 928 := rfl\n",
        )?;
        let main_ast_olean = main_repo.join(".lake/build/lib/lean/Guest/Ast.olean");
        let main_bound_olean =
            main_repo.join(".lake/build/lib/lean/InitECandidate/Solver/GuestStepBound.olean");
        fs::create_dir_all(main_ast_olean.parent().unwrap())?;
        fs::create_dir_all(main_bound_olean.parent().unwrap())?;
        fs::write(&main_ast_olean, b"ast-928-olean")?;
        fs::write(&main_bound_olean, b"bound-928-olean")?;
        fs::write(
            main_repo.join(".lake/build/.turbo_lean_verified_sources.json"),
            b"{\"Guest/Ast.lean\":\"dummy\"}",
        )?;
        fs::write(
            main_repo.join(".lake/build/.turbo_verified_sources.json"),
            b"{\"modules\":{}}",
        )?;

        let wt_diff = tmp_dir.join("wt_diff");
        fs::create_dir_all(wt_diff.join("Guest"))?;
        fs::create_dir_all(wt_diff.join("submission/InitECandidate/Solver"))?;
        fs::write(
            wt_diff.join(".git"),
            format!("gitdir: {}\n", main_git2.display()),
        )?;
        // In wt_diff, `Guest/Ast.lean` is modified (`934`), while `GuestStepBound.lean` is identical!
        fs::write(
            wt_diff.join("Guest/Ast.lean"),
            "namespace Guest\ndef totalCols : Nat := 934\nend Guest\n",
        )?;
        fs::write(
            wt_diff.join("submission/InitECandidate/Solver/GuestStepBound.lean"),
            "import Guest.Ast\ntheorem t : Guest.totalCols = 928 := rfl\n",
        )?;
        let _ = auto_hardlink_worktree_oleans_from_main_repo(&wt_diff);
        let main_pkg = main_repo.join(".lake/packages/mathlib/Basic.olean");
        fs::create_dir_all(main_pkg.parent().unwrap())?;
        fs::write(&main_pkg, b"pkg-olean")?;
        #[cfg(unix)]
        let (main_pkg_mode, main_olean_mode) = {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&main_pkg, fs::Permissions::from_mode(0o640))?;
            fs::set_permissions(&main_olean, fs::Permissions::from_mode(0o640))?;
            (0o640u32, 0o640u32)
        };
        let mut main_lake_bytes: Vec<(PathBuf, Vec<u8>)> = Vec::new();
        for entry in WalkDir::new(main_repo.join(".lake")) {
            let entry = entry?;
            if entry.file_type().is_file() {
                main_lake_bytes.push((entry.path().to_path_buf(), fs::read(entry.path())?));
            }
        }
        let wt_opt = tmp_dir.join("wt_optout");
        fs::create_dir_all(&wt_opt)?;
        fs::write(
            wt_opt.join(".git"),
            format!("gitdir: {}\n", main_git.display()),
        )?;
        fs::write(
            wt_opt.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
        assert_eq!(auto_hardlink_worktree_oleans_from_main_repo(&wt_opt), 0);
        assert!(
            !wt_opt.join(".lake").exists(),
            "toml opt-out must not create or copy `.lake`"
        );
        let wt_env = tmp_dir.join("wt_env");
        fs::create_dir_all(&wt_env)?;
        fs::write(
            wt_env.join(".git"),
            format!("gitdir: {}\n", main_git.display()),
        )?;
        std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", "1");
        let _ = resolve_lake_env(&store, &wt_env)?;
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
        assert!(
            !wt_env.join(".lake").exists(),
            "env opt-out must not create or copy `.lake` during resolve_lake_env"
        );
        let wt_cli = tmp_dir.join("wt_cli");
        fs::create_dir_all(&wt_cli)?;
        fs::write(
            wt_cli.join(".git"),
            format!("gitdir: {}\n", main_git.display()),
        )?;
        let wt_local = wt_cli.join(".lake/local_state");
        fs::create_dir_all(wt_local.parent().unwrap())?;
        fs::write(&wt_local, b"preexisting")?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&wt_local, fs::Permissions::from_mode(0o600))?;
        }
        use clap::Parser;
        let cli = crate::Cli::try_parse_from([
            "turbo-lean",
            "check",
            "--no-auto-worktree-link",
            "MainMod.lean",
        ])
        .expect("global --no-auto-worktree-link parses after the subcommand");
        crate::apply_global_cli_env(&cli);
        let _ = resolve_lake_env(&store, &wt_cli)?;
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
        assert!(
            !wt_cli.join(".lake/build").exists() && !wt_cli.join(".lake/packages").exists(),
            "CLI opt-out must not link or copy `.lake` from the main clone"
        );
        assert_eq!(fs::read(&wt_local)?, b"preexisting");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(fs::metadata(&wt_local)?.permissions().mode() & 0o777, 0o600);
        }
        for (path, bytes) in &main_lake_bytes {
            assert_eq!(
                &fs::read(path)?,
                bytes,
                "opt-out must not copy or rewrite main `.lake`"
            );
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(
                fs::metadata(&main_pkg)?.permissions().mode() & 0o777,
                main_pkg_mode
            );
            assert_eq!(
                fs::metadata(&main_olean)?.permissions().mode() & 0o777,
                main_olean_mode
            );
        }
        assert!(
            !wt_diff
                .join(".lake/build/lib/lean/Guest/Ast.olean")
                .exists(),
            "modified Guest/Ast.olean must not be copied into worktree"
        );
        assert!(
            !wt_diff
                .join(".lake/build/lib/lean/InitECandidate/Solver/GuestStepBound.olean")
                .exists(),
            "downstream GuestStepBound.olean with modified transitive import must not be copied into worktree"
        );
        assert!(
            !wt_diff
                .join(".lake/build/.turbo_lean_verified_sources.json")
                .exists(),
            ".turbo_lean_verified_sources.json must not be copied into worktree"
        );
        assert!(
            !wt_diff
                .join(".lake/build/.turbo_verified_sources.json")
                .exists(),
            ".turbo_verified_sources.json must not be copied into worktree"
        );

        match saved_wt_env {
            Some(v) => std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", v),
            None => std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK"),
        }
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_workspace_olean_precedes_caller_lean_path_preventing_shadow_cas_poisoning() -> Result<()>
    {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let prev_lp = std::env::var_os("LEAN_PATH");
        let root = std::env::temp_dir().join(format!(
            "turbo_ws_precedes_caller_lp_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&root);
        let ws = root.join("ws");
        let shadow = root.join("shadow");
        for (dir, val) in [(&ws, 1u32), (&shadow, 2u32)] {
            fs::create_dir_all(dir.join("P"))?;
            fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
            fs::write(
                dir.join("lakefile.toml"),
                "name = \"p\"\ndefaultTargets = [\"P\"]\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n",
            )?;
            fs::write(dir.join("P/A.lean"), format!("def k : Nat := {val}\n"))?;
        }
        fs::write(
            ws.join("P/B.lean"),
            "import P.A\ntheorem b_ok : k = 1 := rfl\n",
        )?;
        assert!(Command::new("lake")
            .args(["build", "P.B"])
            .current_dir(&ws)
            .status()?
            .success());
        assert!(Command::new("lake")
            .args(["build", "P.A"])
            .current_dir(&shadow)
            .status()?
            .success());

        let canon_ws = ws.canonicalize()?;
        let shadow_lib = shadow.canonicalize()?.join(".lake/build/lib/lean");
        let shadow_lp = shadow_lib.to_string_lossy().to_string();
        let b_src = fs::read_to_string(canon_ws.join("P/B.lean"))?;

        std::env::remove_var("LEAN_PATH");
        let clean_hashes = compute_imported_olean_interface_hashes(&b_src, &canon_ws, None);
        let shadow_only_hashes =
            compute_imported_olean_interface_hashes(&b_src, Path::new(""), Some(&shadow_lp));
        assert_ne!(clean_hashes, shadow_only_hashes);

        // Caller `LEAN_PATH` carries incompatible `P/A.olean` (`k := 2`), while workspace `ws`
        // has fresh `P/A.olean` (`k := 1`) and `P/B.olean`. Workspace `P/A.olean` must win
        // everywhere (`compute_imported_olean_interface_hashes`, `resolve_remote_lean_path`,
        // `resolve_lake_env`), and fast `.olean` certification in `ws` must NOT populate CAS
        // under `shadow_only_hashes`.
        std::env::set_var("LEAN_PATH", &shadow_lp);
        assert_eq!(
            compute_imported_olean_interface_hashes(&b_src, &canon_ws, None),
            clean_hashes
        );
        assert_eq!(
            compute_imported_olean_interface_hashes(&b_src, &canon_ws, Some(&shadow_lp)),
            clean_hashes
        );
        let resolved_lp = resolve_remote_lean_path(&canon_ws, None);
        assert!(resolved_lp.starts_with(
            canon_ws
                .join(".lake/build/lib/lean")
                .to_string_lossy()
                .as_ref()
        ));

        let mut store = TurboStore::open(Some(&root.join("cache")))?;
        let (lake_ev, _) = resolve_lake_env(&store, &canon_ws)?;
        assert!(lake_ev["LEAN_PATH"].starts_with(
            canon_ws
                .join(".lake/build/lib/lean")
                .to_string_lossy()
                .as_ref()
        ));
        crate::check::run_check_command(
            &mut store,
            false,
            true,
            canon_ws.join("P/B.lean"),
            None,
            canon_ws.clone(),
            None,
            false,
            None,
        )?;
        let shadow_split = split_lean_source(&b_src, &shadow_only_hashes);
        let shadow_key = compute_shard_key("leanprover/lean4:v4.35.0", &shadow_split.shards[0]);
        assert!(
            store.get_cached_action(&shadow_key, "trusted")?.is_none(),
            "fast workspace `.olean` check poisoned CAS under shadowed caller `LEAN_PATH` digest"
        );
        let clean_split = split_lean_source(&b_src, &clean_hashes);
        let clean_key = compute_shard_key("leanprover/lean4:v4.35.0", &clean_split.shards[0]);
        assert!(store.get_cached_action(&clean_key, "trusted")?.is_some());

        // When `P.A` is only on caller `LEAN_PATH = shadow_lp` (`k = 2`) in a project without
        // workspace `P/A`, `theorem b_ok : k = 1 := rfl` must fail rather than hitting a poisoned CAS entry!
        let consumer = root.join("consumer");
        fs::create_dir_all(&consumer)?;
        fs::write(
            consumer.join("lean-toolchain"),
            "leanprover/lean4:v4.35.0\n",
        )?;
        fs::write(
            consumer.join("lakefile.toml"),
            "name = \"consumer\"\n[[lean_lib]]\nname = \"Use\"\n",
        )?;
        let consumer_b = consumer.join("Use.lean");
        fs::write(&consumer_b, &b_src)?;
        assert!(
            crate::check::run_check_command(
                &mut store, false, true, consumer_b, None, consumer, None, false, None,
            )
            .is_err(),
            "consumer check with `LEAN_PATH` = shadow (`k = 2`) falsely succeeded"
        );
        // Also test uncached elaboration inside `ws` when `b_ok` is edited (`k + 0 = 1`):
        // elaboration must resolve workspace `P/A.olean` (`k = 1`), not `shadow_lp` (`k = 2`).
        fs::write(
            canon_ws.join("P/B.lean"),
            "import P.A\ntheorem b_edited : k + 0 = 1 := rfl\n",
        )?;
        crate::check::run_check_command(
            &mut store,
            false,
            true,
            canon_ws.join("P/B.lean"),
            None,
            canon_ws,
            None,
            false,
            None,
        )?;

        match prev_lp {
            Some(v) => std::env::set_var("LEAN_PATH", v),
            None => std::env::remove_var("LEAN_PATH"),
        }
        drop(store);
        let _ = fs::remove_dir_all(&root);
        Ok(())
    }

    #[test]
    fn test_dedup_worktree_packages_verifies_cas_digest_and_stages_exact_bytes() -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let saved_wt_env = std::env::var("TURBO_LEAN_NO_WORKTREE_LINK").ok();
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");
        #[cfg(unix)]
        use std::os::unix::fs::{MetadataExt, PermissionsExt};

        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_dedup_digest_test_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let cache_dir = tmp_dir.join("cache");
        let wt = tmp_dir.join("wt");
        let pkg_dir = wt.join(".lake/packages/dep/.lake/build/lib/lean/Dep");
        fs::create_dir_all(&pkg_dir)?;

        let store = TurboStore::open(Some(&cache_dir))?;
        let good_bytes = vec![0x5Au8; 1024];
        let good_hash = blake3::hash(&good_bytes).to_hex().to_string();
        let cas_file = store
            .root
            .join("pkg_cas")
            .join(&good_hash[..2])
            .join(&good_hash);
        fs::create_dir_all(cas_file.parent().unwrap())?;
        // Pre-seed a corrupt `pkg_cas` entry with the EXACT same byte length (1024 bytes).
        fs::write(&cas_file, vec![0xFFu8; 1024])?;

        let olean_a = pkg_dir.join("A.olean");
        let olean_b = pkg_dir.join("B.olean");
        fs::write(&olean_a, &good_bytes)?;
        fs::write(&olean_b, &good_bytes)?;

        // Also place two hardlinked files sharing an inode (`C.olean` and `D.olean`), keep an
        // already-open writable descriptor on `C.olean` BEFORE setting mode `0o444`, and mutate
        // `C.olean` in-place (same byte length!) via that pre-opened writable fd. Permissions do
        // not revoke an open writable fd: `dedup_worktree_packages` must never reuse a stale hash
        // from `(dev, ino, len, 0o444)` alone, and must stage the true mutated bytes.
        let orig_shared_bytes = vec![0x3Cu8; 768];
        let olean_c = pkg_dir.join("C.olean");
        let olean_d = pkg_dir.join("D.olean");
        let mut pre_open_rw = fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .truncate(true)
            .open(&olean_c)?;
        std::io::Write::write_all(&mut pre_open_rw, &orig_shared_bytes)?;
        fs::hard_link(&olean_c, &olean_d)?;
        #[cfg(unix)]
        {
            let mut ro = fs::metadata(&olean_c)?.permissions();
            ro.set_mode(0o444);
            fs::set_permissions(&olean_c, ro)?;
        }
        // First dedup pass records `orig_shared_bytes` into `pkg_cas`.
        let rep0 = dedup_worktree_packages(&store, &wt)?;
        assert_eq!(rep0["status"], "worktree_packages_deduped");
        // Now mutate `pre_open_rw` (or re-create a hardlinked `0o444` pair with open writable fd)
        // to prove a `0o444` hardlinked pair mutated via an open writable descriptor between or
        // during dedup is hashed from live bytes rather than cached inode metadata.
        let olean_e = pkg_dir.join("E.olean");
        let olean_f = pkg_dir.join("F.olean");
        let mut rw_ef = fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .truncate(true)
            .open(&olean_e)?;
        std::io::Write::write_all(&mut rw_ef, &orig_shared_bytes)?;
        fs::hard_link(&olean_e, &olean_f)?;
        #[cfg(unix)]
        {
            let mut ro = fs::metadata(&olean_e)?.permissions();
            ro.set_mode(0o444);
            fs::set_permissions(&olean_e, ro)?;
        }
        // Mutate same-length `0o444` inode through the already-open writable descriptor!
        let mutated_shared_bytes = vec![0x99u8; 768];
        use std::io::Seek;
        rw_ef.seek(std::io::SeekFrom::Start(0))?;
        std::io::Write::write_all(&mut rw_ef, &mutated_shared_bytes)?;
        drop(rw_ef);
        drop(pre_open_rw);

        let rep = dedup_worktree_packages(&store, &wt)?;
        assert_eq!(rep["status"], "worktree_packages_deduped");
        assert_eq!(
            fs::read(&cas_file)?,
            good_bytes,
            "same-size corrupt pkg_cas entry must be replaced with digest-verified bytes, never linked over worktree files"
        );
        assert_eq!(fs::read(&olean_a)?, good_bytes);
        assert_eq!(fs::read(&olean_b)?, good_bytes);
        assert_eq!(fs::read(&olean_c)?, orig_shared_bytes);
        assert_eq!(fs::read(&olean_d)?, orig_shared_bytes);
        assert_eq!(
            fs::read(&olean_e)?,
            mutated_shared_bytes,
            "0o444 inode mutated via open writable fd must hash actual bytes, never reuse orig_shared_bytes CAS blob"
        );
        assert_eq!(fs::read(&olean_f)?, mutated_shared_bytes);
        let mutated_hash = blake3::hash(&mutated_shared_bytes).to_hex().to_string();
        let mutated_cas = store
            .root
            .join("pkg_cas")
            .join(&mutated_hash[..2])
            .join(&mutated_hash);
        assert_eq!(fs::read(&mutated_cas)?, mutated_shared_bytes);
        #[cfg(unix)]
        {
            assert_eq!(
                fs::metadata(&olean_a)?.ino(),
                fs::metadata(&cas_file)?.ino()
            );
            assert_eq!(
                fs::metadata(&olean_b)?.ino(),
                fs::metadata(&cas_file)?.ino()
            );
            assert_eq!(fs::metadata(&cas_file)?.permissions().mode() & 0o222, 0);
            assert_eq!(fs::metadata(&olean_c)?.ino(), fs::metadata(&olean_d)?.ino());
            assert_eq!(fs::metadata(&olean_c)?.permissions().mode() & 0o222, 0);
            assert_eq!(
                fs::metadata(&olean_e)?.ino(),
                fs::metadata(&mutated_cas)?.ino()
            );
            assert_eq!(
                fs::metadata(&olean_f)?.ino(),
                fs::metadata(&mutated_cas)?.ino()
            );

            // Also verify `dedup_worktree_packages` isolates against a pre-existing unstamped
            // `pkg_cas` inode that has a retained open writable descriptor: dedup must replace
            // `pkg_cas` with a fresh store-owned inode so post-dedup writes to the retained fd
            // cannot corrupt either `pkg_cas` or deduplicated package artifacts!
            let leaked_bytes = vec![0x77u8; 640];
            let leaked_hash = blake3::hash(&leaked_bytes).to_hex().to_string();
            let leaked_cas = store
                .root
                .join("pkg_cas")
                .join(&leaked_hash[..2])
                .join(&leaked_hash);
            fs::create_dir_all(leaked_cas.parent().unwrap())?;
            let mut retained_cas_rw = fs::OpenOptions::new()
                .create(true)
                .truncate(true)
                .read(true)
                .write(true)
                .open(&leaked_cas)?;
            std::io::Write::write_all(&mut retained_cas_rw, &leaked_bytes)?;
            let old_cas_ino = retained_cas_rw.metadata()?.ino();
            let olean_g = pkg_dir.join("G.olean");
            let olean_h = pkg_dir.join("H.olean");
            fs::write(&olean_g, &leaked_bytes)?;
            fs::write(&olean_h, &leaked_bytes)?;
            dedup_worktree_packages(&store, &wt)?;
            assert_ne!(fs::metadata(&leaked_cas)?.ino(), old_cas_ino);
            retained_cas_rw.seek(std::io::SeekFrom::Start(0))?;
            std::io::Write::write_all(&mut retained_cas_rw, &vec![0xEEu8; 640])?;
            drop(retained_cas_rw);
            assert_eq!(fs::read(&leaked_cas)?, leaked_bytes);
            assert_eq!(fs::read(&olean_g)?, leaked_bytes);
            assert_eq!(fs::read(&olean_h)?, leaked_bytes);
        }

        match saved_wt_env {
            Some(v) => std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", v),
            None => std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK"),
        }
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_optout_lakeless_nonroot_import_child() -> Result<()> {
        let Some(root) = std::env::var_os("TURBO_TEST_LAKELESS_OPTOUT_ROOT").map(PathBuf::from)
        else {
            return Ok(());
        };
        let dir = root.join("lakeless").canonicalize()?;
        let target = dir.join("Main.lean").canonicalize()?;
        let err = ensure_project_imports_fresh_for_check(&dir, &[target]).unwrap_err();
        let msg = format!("{err:#}");
        assert!(
            msg.contains("Cannot verify standalone import `Ext.NonRoot`")
                && msg.contains("fail-closed toolchain gate"),
            "unexpected error: {msg}"
        );
        assert!(
            !root.join("ambient-lean-invoked").exists(),
            "ensure_project_imports_fresh executed ambient PATH `lean`"
        );
        fs::write(root.join("done"), b"")?;
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn test_optout_lakeless_nonroot_import_never_executes_ambient_path_lean() -> Result<()> {
        use crate::worktree_test_support::TestChild;
        use std::os::unix::fs::PermissionsExt;
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let root = std::env::temp_dir().join(format!(
            "turbo_lakeless_optout_nopath_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&root);
        let dir = root.join("lakeless");
        let bin = root.join("path/bin");
        let fake_prefix = root.join("fake_prefix");
        fs::create_dir_all(&dir)?;
        fs::create_dir_all(&bin)?;
        fs::create_dir_all(fake_prefix.join("lib/lean/Ext"))?;
        // Fake `.olean` that would have satisfied the old `Command::new("lean") --print-prefix` fallback!
        fs::write(fake_prefix.join("lib/lean/Ext/NonRoot.olean"), [0x55u8; 64])?;
        fs::write(dir.join("lean-toolchain"), "leanprover/lean4:v99.99.99\n")?;
        fs::write(
            dir.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        fs::write(
            dir.join("Main.lean"),
            "import Ext.NonRoot\ntheorem t : True := trivial\n",
        )?;
        let shim_lean = bin.join("lean");
        fs::write(
            &shim_lean,
            format!(
                "#!/bin/sh\nprintf invoked > '{}'\nprintf '%s\\n' '{}'\n",
                root.join("ambient-lean-invoked").display(),
                fake_prefix.display()
            ),
        )?;
        fs::set_permissions(&shim_lean, fs::Permissions::from_mode(0o755))?;

        let mut command =
            TestChild::command("lake_build::tests::test_optout_lakeless_nonroot_import_child")?;
        command
            .env("TURBO_TEST_LAKELESS_OPTOUT_ROOT", &root)
            .env("PATH", format!("{}:/usr/bin:/bin", bin.display()))
            .env("HOME", root.join("isolated/a/b/home"))
            .env("ELAN_HOME", root.join("empty_elan"))
            .env("TURBO_LEAN_HOME", root.join("cache"))
            .env("TURBO_LEAN_STAGING_DIR", root.join("staging"))
            .env_remove("LEAN_PATH");
        let mut child = TestChild::spawn(&mut command)?;
        child.finish(&root.join("done"))?;
        assert!(
            !root.join("ambient-lean-invoked").exists(),
            "ambient PATH `lean` shim was executed"
        );
        crate::zygote::purge_snapshot_dir(&root);
        Ok(())
    }

    #[test]
    fn test_auto_hardlink_worktree_oleans_rejects_divergent_lake_inputs_manifest_and_config(
    ) -> Result<()> {
        let _env_guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let saved_wt_env = std::env::var("TURBO_LEAN_NO_WORKTREE_LINK").ok();
        std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK");

        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_lean_wt_lake_inputs_parity_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);

        let main_repo = tmp_dir.join("main_repo");
        fs::create_dir_all(main_repo.join("Smoke"))?;
        fs::create_dir_all(main_repo.join("Data"))?;
        fs::create_dir_all(main_repo.join(".lake/build/lib/lean/Smoke"))?;
        fs::write(
            main_repo.join("lean-toolchain"),
            include_str!("../../../../lean/lean-toolchain"),
        )?;
        let lakefile_lean = "import Lake\nopen Lake DSL\npackage demo\ninput_dir smokeSources where\n  path := \"Data\"\n  filter := .extension \"sol\"\n@[default_target]\nlean_lib Smoke where\n  globs := #[.one `Smoke.A]\n  needs := #[smokeSources]\n";
        fs::write(main_repo.join("lakefile.lean"), lakefile_lean)?;
        fs::write(main_repo.join("Smoke/A.lean"), "def a : Nat := 1\n")?;
        fs::write(main_repo.join("Data/a.sol"), "contract A {}\n")?;
        let manifest_v1 =
            "{\"version\": 7, \"packagesDir\": \".lake/packages\", \"packages\": []}\n";
        fs::write(main_repo.join("lake-manifest.json"), manifest_v1)?;
        fs::write(
            main_repo.join(".lake/build/lib/lean/Smoke/A.olean"),
            b"smoke-a-olean-v1",
        )?;

        if crate::module_builder::resolve_project_config(&main_repo).is_err() {
            match saved_wt_env {
                Some(v) => std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", v),
                None => std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK"),
            }
            let _ = fs::remove_dir_all(&tmp_dir);
            return Ok(());
        }

        let cfg = crate::module_builder::resolve_project_config(&main_repo)?;
        let cur_inputs_digest = crate::module_builder::workspace_lake_inputs_digest(&cfg)?;
        let write_main_verified_manifest = |inputs_digest: &str| -> Result<()> {
            let m = crate::module_builder::VerifiedDepManifest {
                pkg_name: cfg.root_pkg.name.clone(),
                toolchain: cfg.toolchain.clone(),
                lean_githash: cfg.lean_githash.clone(),
                pkg_config_digest: cfg.root_pkg.config_digest.clone(),
                lake_inputs_digest: inputs_digest.to_string(),
                workspace_config_digest: cfg.canonical_config_digest.clone(),
                allowed_axioms: crate::splitter::allowed_axioms(),
                kernel_policy_digest: crate::splitter::current_kernel_policy_digest(),
                modules: std::collections::BTreeMap::from([(
                    "Smoke/A.lean".to_string(),
                    crate::module_builder::VerifiedDepModuleEntry {
                        src_blake3: blake3::hash(b"def a : Nat := 1\n").to_hex().to_string(),
                        olean_artifact_digest: "art".to_string(),
                        lake_inputs_digest: inputs_digest.to_string(),
                        kernel_audited: true,
                        import_olean_digests: Default::default(),
                        artifact_stat_fingerprint: String::new(),
                        ..Default::default()
                    },
                )]),
                ..Default::default()
            };
            fs::write(
                verified_sources_manifest_path(&main_repo),
                serde_json::to_vec(&m)?,
            )?;
            Ok(())
        };
        write_main_verified_manifest(&cur_inputs_digest)?;

        let make_wt = |name: &str| -> Result<PathBuf> {
            let main_git = main_repo.join(".git/worktrees").join(name);
            fs::create_dir_all(&main_git)?;
            fs::write(main_git.join("commondir"), "../..\n")?;
            let wt = tmp_dir.join(name);
            let _ = fs::remove_dir_all(&wt);
            fs::create_dir_all(wt.join("Smoke"))?;
            fs::create_dir_all(wt.join("Data"))?;
            fs::write(wt.join(".git"), format!("gitdir: {}\n", main_git.display()))?;
            fs::write(
                wt.join("lean-toolchain"),
                include_str!("../../../../lean/lean-toolchain"),
            )?;
            fs::write(wt.join("lakefile.lean"), lakefile_lean)?;
            fs::write(wt.join("Smoke/A.lean"), "def a : Nat := 1\n")?;
            fs::write(wt.join("Data/a.sol"), "contract A {}\n")?;
            fs::write(wt.join("lake-manifest.json"), manifest_v1)?;
            Ok(wt)
        };

        // 1. Identical inputs + manifest + config + verified manifest => copies Smoke/A.olean.
        let wt_same = make_wt("wt_same")?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        assert_eq!(auto_hardlink_worktree_oleans_from_main_repo(&wt_same), 1);
        assert!(wt_same.join(".lake/build/lib/lean/Smoke/A.olean").exists());

        // 2. Divergent matched `input_dir` file => must refuse copying `.olean`s.
        let wt_input_diff = make_wt("wt_input_diff")?;
        fs::write(wt_input_diff.join("Data/a.sol"), "contract AChanged {}\n")?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        assert_eq!(
            auto_hardlink_worktree_oleans_from_main_repo(&wt_input_diff),
            0,
            "divergent matched input_dir file must block worktree .olean copy"
        );
        assert!(!wt_input_diff
            .join(".lake/build/lib/lean/Smoke/A.olean")
            .exists());

        // 3. Divergent `lake-manifest.json` => must refuse copying `.olean`s.
        let wt_manifest_diff = make_wt("wt_manifest_diff")?;
        fs::write(
            wt_manifest_diff.join("lake-manifest.json"),
            "{\"version\": 7, \"packagesDir\": \".lake/packages_alt\", \"packages\": []}\n",
        )?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        assert_eq!(
            auto_hardlink_worktree_oleans_from_main_repo(&wt_manifest_diff),
            0,
            "divergent lake-manifest.json must block worktree .olean copy"
        );

        // 4. Stale main verified manifest (`lake_inputs_digest` mismatch) => must refuse copying.
        write_main_verified_manifest("stale_digest_from_earlier_input")?;
        let wt_stale_main = make_wt("wt_stale_main")?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        assert_eq!(
            auto_hardlink_worktree_oleans_from_main_repo(&wt_stale_main),
            0,
            "main repo with stale verified manifest must not seed worktree .olean files"
        );

        match saved_wt_env {
            Some(v) => std::env::set_var("TURBO_LEAN_NO_WORKTREE_LINK", v),
            None => std::env::remove_var("TURBO_LEAN_NO_WORKTREE_LINK"),
        }
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_speed4_public_signature_early_cutoff_and_readonly_impact() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_speed4_pubsig_impact_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&tmp_dir);
        let proj = tmp_dir.join("proj");
        let cache = tmp_dir.join("cache");
        fs::create_dir_all(proj.join("Smoke"))?;
        fs::write(
            proj.join("lean-toolchain"),
            include_str!("../../../../lean/lean-toolchain"),
        )?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"smoke\"\n[[lean_lib]]\nname = \"Smoke\"\nglobs = [\"Smoke.+\"]\n",
        )?;

        let a_v1 = "\
module
private def privHelper (n : Nat) : Nat := n + 1
@[noinline] public def pubApi (n : Nat) : Nat := privHelper n
public theorem pub_thm (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n
";
        let b_src = "\
module
public import Smoke.A
public theorem downstream_b (n : Nat) : n + 0 = n := pub_thm n
";
        let c_src = "\
module
import Smoke.B
public theorem downstream_c (n : Nat) : n + 0 = n := downstream_b n
";
        fs::write(proj.join("Smoke/A.lean"), a_v1)?;
        fs::write(proj.join("Smoke/B.lean"), b_src)?;
        fs::write(proj.join("Smoke/C.lean"), c_src)?;

        let Some(git_bin) = crate::trusted_tools::discover_or_skip_trusted_git_for_test(&proj)?
        else {
            let _ = fs::remove_dir_all(&tmp_dir);
            return Ok(());
        };
        if std::env::var_os("TURBO_LEAN_GIT").is_none() {
            std::env::set_var("TURBO_LEAN_GIT", &git_bin);
        }
        let run_git = |args: &[&str]| -> Result<()> {
            let st = Command::new(&git_bin)
                .current_dir(&proj)
                .args(args)
                .env("GIT_AUTHOR_NAME", "Test")
                .env("GIT_AUTHOR_EMAIL", "test@example.com")
                .env("GIT_COMMITTER_NAME", "Test")
                .env("GIT_COMMITTER_EMAIL", "test@example.com")
                .status()?;
            anyhow::ensure!(st.success(), "git {:?} failed", args);
            Ok(())
        };
        run_git(&["init"])?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-m", "init"])?;

        // 1. `compute_impact_report` BEFORE any build or store open: strictly read-only, no `.lake` or `.turbo-lean` created.
        let rep_unchanged = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_unchanged.edit_class, "unchanged");
        assert!(!rep_unchanged.public_signature_changed);
        assert_eq!(rep_unchanged.direct_dependents, vec!["Smoke.B".to_string()]);
        assert!(rep_unchanged.transitive_dependents.is_empty());
        assert_eq!(
            rep_unchanged.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(!proj.join(".lake").exists());
        assert!(!proj.join(".turbo-lean").exists());

        // Initial native build of the DAG so `Smoke.A`, `Smoke.B`, and `Smoke.C` have verified `.olean` baselines.
        let mut store = TurboStore::open(Some(&cache))?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let canon_proj = proj.canonicalize().unwrap_or_else(|_| proj.clone());

        // 2. Private theorem + proof-only edit on `pub_thm` (preserving exported axiom footprint `[]`):
        //    - `.ir` and `.ir.sig` remain byte-identical and `dumpPublicSignatureJson` matches -> cuts off at `Smoke.A` (1 module, NOT 3!).
        let a_proof_only_edit = "\
module
private def privHelper (n : Nat) : Nat := n + 1
@[noinline] public def pubApi (n : Nat) : Nat := privHelper n
public theorem pub_thm (n : Nat) : n + 0 = n := by
  have _unused : 1 + 1 = 2 := rfl
  exact Nat.add_zero n
private theorem priv_extra_lemma : 1 + 1 = 2 := rfl
";
        fs::write(proj.join("Smoke/A.lean"), a_proof_only_edit)?;
        let rep_priv = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_priv.edit_class, "private_module_edit");
        assert!(!rep_priv.public_signature_changed);
        assert!(!rep_priv.meta_signature_changed);
        assert!(rep_priv.transitive_dependents.is_empty());
        assert_eq!(
            rep_priv.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        let (rechecked_n, _files, rechecked_mods, _) = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        )?;
        assert_eq!(
            rechecked_n, 1,
            "public-signature early cutoff must stop at Smoke.A on theorem proof / private theorem edit, got {:?}",
            rechecked_mods
        );
        assert_eq!(rechecked_mods, vec!["Smoke.A".to_string()]);

        // 2a. Blocking 2 regression: proof-only edit that introduces `propext`/`Quot.sound` via `omega`
        //     mutates `exportedAxiomsExt` in `Smoke/A.olean`, so Stage-2 cutoff MUST recheck `Smoke.B`/`Smoke.C`!
        let a_axiom_footprint_edit = "\
module
private def privHelper (n : Nat) : Nat := n + 1
@[noinline] public def pubApi (n : Nat) : Nat := privHelper n
public theorem pub_thm (n : Nat) : n + 0 = n := by
  omega
";
        fs::write(proj.join("Smoke/A.lean"), a_axiom_footprint_edit)?;
        let (rechecked_ax_n, _ax_files, mut rechecked_ax_mods, _) =
            lake_recheck_dependents_with_store(
                Some(&store),
                &canon_proj,
                &["Smoke/A.lean".to_string()],
                Some("HEAD"),
                false,
            )?;
        rechecked_ax_mods.sort();
        assert_eq!(
            rechecked_ax_n, 3,
            "proof edit changing exportedAxiomsExt footprint (`[]` -> `[propext, Quot.sound]`) must not cut off downstream modules"
        );

        // 2b. Blocking 1 regression: mutating a `private def` body alters `Smoke/A.ir` (which Lean 4.35
        //     `PublicExport` passes via `importArts`), so Stage-2 cutoff MUST NOT skip `Smoke.B`/`Smoke.C`
        //     and must recheck all 3 modules so downstream `.trace` input hashes stay synchronized!
        let a_ir_mutating_edit = "\
module
private def privHelper (n : Nat) : Nat := n + 42
@[noinline] public def pubApi (n : Nat) : Nat := privHelper n
public theorem pub_thm (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n
";
        fs::write(proj.join("Smoke/A.lean"), a_ir_mutating_edit)?;
        let (rechecked_ir_n, _ir_files, mut rechecked_ir_mods, _) =
            lake_recheck_dependents_with_store(
                Some(&store),
                &canon_proj,
                &["Smoke/A.lean".to_string()],
                Some("HEAD"),
                false,
            )?;
        rechecked_ir_mods.sort();
        assert_eq!(
            rechecked_ir_n, 3,
            "`.ir`-mutating private def edit must not unsoundly cut off downstream modules in Lean 4.35 PublicExport"
        );
        assert_eq!(
            rechecked_ir_mods,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );

        // 3. Public theorem type / attribute edit (`@[simp]` added on `pub_thm`):
        //    - `impact` classifies `public_signature_edit`, `public_signature_changed == true`, lists full downstream cone `Smoke.B` & `Smoke.C`.
        //    - `lake_recheck_dependents_with_store` does NOT cut off and rechecks all 3 modules (`Smoke.A`, `Smoke.B`, `Smoke.C`).
        let a_pub_edit = a_v1.replace("public theorem pub_thm", "@[simp] public theorem pub_thm");
        fs::write(proj.join("Smoke/A.lean"), &a_pub_edit)?;
        let rep_pub = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_pub.edit_class, "public_signature_edit");
        assert!(rep_pub.public_signature_changed);
        assert_eq!(
            rep_pub.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_pub.pruned_dependents.is_empty());

        let (rechecked_pub_n, _pub_files, mut rechecked_pub_mods, _) =
            lake_recheck_dependents_with_store(
                Some(&store),
                &canon_proj,
                &["Smoke/A.lean".to_string()],
                Some("HEAD"),
                false,
            )?;
        rechecked_pub_mods.sort();
        assert_eq!(rechecked_pub_n, 3);
        assert_eq!(
            rechecked_pub_mods,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );

        // 4. Blocking 2 regressions on `dumpPublicSignatureJson` (`olean-pubsig:v2`):
        //    (a) Instance priority change (`@[instance 100]` vs `@[instance 200]`) MUST alter `public_sig_digest`.
        //    (b) Non-whitelisted persistent extension (`register_simp_attr` custom ext) MUST set `has_opaque_ext = true`
        //        so Stage-2 cutoff fails closed instead of trusting partial metadata projection!
        let inst_v1 = "\
module
namespace SmokeA
public class MyTag (α : Type) where
  tag : Nat
public def mkTag100 : MyTag Nat := { tag := 1 }
attribute [instance 100] mkTag100
end SmokeA
";
        let inst_v2 = "\
module
namespace SmokeA
public class MyTag (α : Type) where
  tag : Nat
public def mkTag100 : MyTag Nat := { tag := 1 }
attribute [instance 200] mkTag100
end SmokeA
";
        fs::write(proj.join("Smoke/A.lean"), inst_v1)?;
        lake_build_modules(&canon_proj, &["Smoke.A".to_string()], None)?;
        let cfg = crate::module_builder::resolve_project_config(&canon_proj)?;
        let replay_lp = format!(
            "{}:{}",
            resolve_remote_lean_path(&canon_proj, None),
            cfg.toolchain_lib_lean.display()
        );
        let sig_inst_100 = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.A",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(!sig_inst_100.has_opaque_ext);
        assert!(!sig_inst_100.instance_entries.is_empty());

        fs::write(proj.join("Smoke/A.lean"), inst_v2)?;
        lake_build_modules(&canon_proj, &["Smoke.A".to_string()], None)?;
        let sig_inst_200 = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.A",
            &replay_lp,
            &[],
            false,
        )?;
        assert_ne!(
            sig_inst_100.public_sig_digest, sig_inst_200.public_sig_digest,
            "instance priority change in Meta.instanceExtension must alter olean public_sig_digest"
        );

        //    (b) Exporting an alias for an imported declaration (`export SmokeA (mkTag100)`)
        //        where `origName` is NOT in `Smoke.B`'s `md.constants` MUST alter `Smoke.B`'s
        //        `public_sig_digest` when added or removed.
        let b_no_export = "\
module
public import Smoke.A
public def bVal : Nat := 1
";
        let b_with_imported_export = "\
module
public import Smoke.A
export SmokeA (mkTag100)
public def bVal : Nat := 1
";
        fs::write(proj.join("Smoke/B.lean"), b_no_export)?;
        lake_build_modules(&canon_proj, &["Smoke.B".to_string()], None)?;
        let sig_b_no_export = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.B",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(!sig_b_no_export.has_opaque_ext);

        fs::write(proj.join("Smoke/B.lean"), b_with_imported_export)?;
        lake_build_modules(&canon_proj, &["Smoke.B".to_string()], None)?;
        let sig_b_with_export = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.B",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(!sig_b_with_export.has_opaque_ext);
        assert_ne!(
            sig_b_no_export.public_sig_digest, sig_b_with_export.public_sig_digest,
            "re-exporting an imported declaration via `export N (foo)` must alter olean public_sig_digest"
        );

        //    (c) Adding an entry to a whitelisted attribute/tag extension (`Lean.matchPatternAttr` /
        //        `Lean.Compiler.specializeAttr`) targeting an IMPORTED declaration from `Smoke.A`
        //        (so `Smoke.B`'s `md.constants` does NOT contain `SmokeA.mkTag100`) MUST alter
        //        `Smoke.B`'s `public_sig_digest` without setting `has_opaque_ext = true`.
        let b_imported_match_pat = "\
module
public import Smoke.A
meta import Lean
run_cmd Lean.Elab.Command.liftCoreM <| Lean.modifyEnv (fun env => Lean.matchPatternAttr.ext.addEntry env `SmokeA.mkTag100)
public def bVal : Nat := 1
";
        fs::write(proj.join("Smoke/B.lean"), b_imported_match_pat)?;
        lake_build_modules(&canon_proj, &["Smoke.B".to_string()], None)?;
        let sig_b_imported_match_pat = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.B",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(
            !sig_b_imported_match_pat.has_opaque_ext,
            "whitelisted matchPatternAttr entry must not set has_opaque_ext"
        );
        assert_ne!(
            sig_b_no_export.public_sig_digest, sig_b_imported_match_pat.public_sig_digest,
            "whitelisted tag/attribute extension entry targeting an imported declaration outside md.constants must alter public_sig_digest"
        );

        let b_spec_arg1 = "\
module
public def polyFn (f : Nat → Nat) (g : Nat → Nat) (x : Nat) : Nat := f (g x)
attribute [specialize 1] polyFn
";
        let b_spec_arg2 = "\
module
public def polyFn (f : Nat → Nat) (g : Nat → Nat) (x : Nat) : Nat := f (g x)
attribute [specialize 2] polyFn
";
        fs::write(proj.join("Smoke/B.lean"), b_spec_arg1)?;
        lake_build_modules(&canon_proj, &["Smoke.B".to_string()], None)?;
        let sig_b_spec_arg1 = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.B",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(
            !sig_b_spec_arg1.has_opaque_ext,
            "`@[specialize 1]` (`Lean.Compiler.specializeAttr`) must be whitelisted and decoded"
        );
        fs::write(proj.join("Smoke/B.lean"), b_spec_arg2)?;
        lake_build_modules(&canon_proj, &["Smoke.B".to_string()], None)?;
        let sig_b_spec_arg2 = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.B",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(!sig_b_spec_arg2.has_opaque_ext);
        assert_ne!(
            sig_b_spec_arg1.public_sig_digest, sig_b_spec_arg2.public_sig_digest,
            "changing `@[specialize 1]` to `@[specialize 2]` must alter public_sig_digest"
        );

        let opaque_ext_src = "\
module
public meta import Lean
public meta initialize myOpaqueExt : Lean.SimplePersistentEnvExtension Lean.Name (Array Lean.Name) ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun _ => #[]
    addEntryFn := Array.push
  }
";
        let opaque_user_src = "\
module
public meta import Smoke.A
run_cmd Lean.Elab.Command.liftCoreM <| Lean.modifyEnv (fun env => myOpaqueExt.addEntry env `hello)
public theorem trivial_ok : 1 + 1 = 2 := rfl
";
        fs::write(proj.join("Smoke/A.lean"), opaque_ext_src)?;
        fs::write(proj.join("Smoke/B.lean"), opaque_user_src)?;
        lake_build_modules(
            &canon_proj,
            &["Smoke.A".to_string(), "Smoke.B".to_string()],
            None,
        )?;
        let sig_opaque = crate::zygote::read_module_public_signature_with_zygote(
            &store.root,
            &cfg,
            "Smoke.B",
            &replay_lp,
            &[],
            false,
        )?;
        assert!(
            sig_opaque.has_opaque_ext,
            "unrecognized persistent environment extension entry must trip `has_opaque_ext = true` fail-closed guard"
        );

        //    (d) End-to-end `compute_impact_report` check for `local notation`: editing a `local notation`
        //        before a public declaration whose type uses that notation MUST mark
        //        `public_signature_changed = true` and classify as `public_signature_edit`.
        let a_local_not_v1 = "\
module
local notation \"MYTYPE\" => Nat
public def localNotVal : MYTYPE := 0
";
        let a_local_not_v2 = "\
module
local notation \"MYTYPE\" => Bool
public def localNotVal : MYTYPE := true
";
        fs::write(proj.join("Smoke/A.lean"), a_local_not_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useIt := localNotVal\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useItC := useIt\n",
        )?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-m", "local notation baseline"])?;
        fs::write(proj.join("Smoke/A.lean"), a_local_not_v2)?;
        let rep_local_not = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_local_not.edit_class, "public_signature_edit");
        assert!(
            rep_local_not.public_signature_changed,
            "`local notation` edit before a public declaration must mark `public_signature_changed = true`"
        );
        assert_eq!(
            rep_local_not.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/Provider1.lean"),
            "module\npublic def foo : Nat := 0\n",
        )?;
        fs::write(
            proj.join("Smoke/Provider2.lean"),
            "module\npublic def foo : Bool := true\n",
        )?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\nimport Smoke.Provider1\npublic def api := foo\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useApi := api\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useApiC := useApi\n",
        )?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-m", "non-exported import baseline"])?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\nimport Smoke.Provider2\npublic def api := foo\n",
        )?;
        let rep_nonexp_imp = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_nonexp_imp.edit_class, "public_signature_edit");
        assert!(
            rep_nonexp_imp.public_signature_changed,
            "non-exported import change before a public declaration must mark `public_signature_changed = true`"
        );
        assert_eq!(
            rep_nonexp_imp.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_nonexp_imp.pruned_dependents.is_empty());

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\nprivate def helper := (0 : Nat)\npublic def api := helper\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useApi := api\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useApiC := useApi\n",
        )?;
        run_git(&["add", "."])?;
        run_git(&[
            "commit",
            "-m",
            "private helper inferred public def baseline",
        ])?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\nprivate def helper := true\npublic def api := helper\n",
        )?;
        let rep_priv_helper = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_priv_helper.edit_class, "public_signature_edit");
        assert!(
            rep_priv_helper.public_signature_changed,
            "private helper edit before `public def api := helper` must mark `public_signature_changed = true`"
        );
        assert_eq!(
            rep_priv_helper.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_priv_helper.pruned_dependents.is_empty());

        for (commit_msg, base_a, edited_a) in [
            (
                "private abbrev in public theorem baseline",
                "module\nprivate abbrev MyProp := (1 = 1)\npublic theorem apiThm : MyProp := rfl\n",
                "module\nprivate abbrev MyProp := (2 = 2)\npublic theorem apiThm : MyProp := rfl\n",
            ),
            (
                "private def in public theorem baseline",
                "module\nprivate def targetVal : Nat := 1\npublic theorem apiThm : targetVal = targetVal := rfl\n",
                "module\nprivate def targetVal : Nat := 2\npublic theorem apiThm : targetVal = targetVal := rfl\n",
            ),
        ] {
            fs::write(proj.join("Smoke/A.lean"), base_a)?;
            fs::write(
                proj.join("Smoke/B.lean"),
                "module\npublic import Smoke.A\npublic theorem useThm : True := trivial\n",
            )?;
            fs::write(
                proj.join("Smoke/C.lean"),
                "module\nimport Smoke.B\npublic theorem useThmC : True := useThm\n",
            )?;
            run_git(&["add", "."])?;
            run_git(&["commit", "-m", commit_msg])?;
            fs::write(proj.join("Smoke/A.lean"), edited_a)?;
            let rep_thm_priv = compute_impact_report(
                proj.join("Smoke/A.lean"),
                Some(proj.clone()),
                Some("HEAD".to_string()),
            )?;
            assert_eq!(rep_thm_priv.edit_class, "public_signature_edit");
            assert!(rep_thm_priv.public_signature_changed);
            assert_eq!(
                rep_thm_priv.transitive_dependents,
                vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
            );
            assert!(rep_thm_priv.pruned_dependents.is_empty());
        }

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic def api : Nat := 1\nprivate def trailingHelper := (0 : Nat)\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useApi := api\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useApiC := useApi\n",
        )?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-m", "trailing private helper baseline"])?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic def api : Nat := 1\nprivate def trailingHelper := true\n",
        )?;
        let rep_trailing_priv = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_trailing_priv.edit_class, "private_module_edit");
        assert!(!rep_trailing_priv.public_signature_changed);
        assert!(rep_trailing_priv.transitive_dependents.is_empty());
        assert_eq!(
            rep_trailing_priv.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/Provider1.lean"),
            "module\npublic def p1 : Nat := 1\n",
        )?;
        fs::write(
            proj.join("Smoke/Provider2.lean"),
            "module\npublic def p2 : Nat := 2\n",
        )?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic import Smoke.Provider1\npublic import Smoke.Provider2\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useReexport : Nat := p1 + p2\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useReexportC : Nat := useReexport\n",
        )?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-m", "public import order baseline"])?;

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic import Smoke.Provider2\npublic import Smoke.Provider1\n",
        )?;
        let rep_pub_imp_swap = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_pub_imp_swap.edit_class, "public_signature_edit");
        assert!(
            rep_pub_imp_swap.public_signature_changed,
            "swapping `public import` order must mark `public_signature_changed = true`"
        );
        assert!(rep_pub_imp_swap.meta_signature_changed);
        assert_ne!(
            Some(rep_pub_imp_swap.public_signature_digest.as_str()),
            rep_pub_imp_swap.baseline_public_signature_digest.as_deref()
        );
        assert_eq!(
            rep_pub_imp_swap.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(
            rep_pub_imp_swap.pruned_dependents.is_empty(),
            "downstream importers must not be pruned when `public import` order changes"
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "-- header note\nmodule /- cmt -/\n\n  public   import   Smoke.Provider1 -- first\n  /- between -/\n  public   import   Smoke.Provider2\n",
        )?;
        let rep_pub_imp_ws_pure = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert!(!rep_pub_imp_ws_pure.public_signature_changed);
        assert!(!rep_pub_imp_ws_pure.meta_signature_changed);
        assert_eq!(
            Some(rep_pub_imp_ws_pure.public_signature_digest.as_str()),
            rep_pub_imp_ws_pure
                .baseline_public_signature_digest
                .as_deref()
        );
        assert!(rep_pub_imp_ws_pure.transitive_dependents.is_empty());
        assert_eq!(
            rep_pub_imp_ws_pure.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "-- header note\nmodule /- cmt -/\n\n  public   import   Smoke.Provider1 -- first\n  /- between -/\n  public   import   Smoke.Provider2\nprivate def trailingOnly : Nat := 9\n",
        )?;
        let rep_pub_imp_ws = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_pub_imp_ws.edit_class, "private_module_edit");
        assert!(!rep_pub_imp_ws.public_signature_changed);
        assert!(!rep_pub_imp_ws.meta_signature_changed);
        assert_eq!(
            Some(rep_pub_imp_ws.public_signature_digest.as_str()),
            rep_pub_imp_ws.baseline_public_signature_digest.as_deref()
        );
        assert_eq!(
            Some(rep_pub_imp_ws.meta_signature_digest.as_str()),
            rep_pub_imp_ws.baseline_meta_signature_digest.as_deref()
        );
        assert!(rep_pub_imp_ws.transitive_dependents.is_empty());
        assert_eq!(
            rep_pub_imp_ws.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic meta import Smoke.Provider1\npublic meta import Smoke.Provider2\npublic meta def metaConst : Nat := 1\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def usePubOnly : Nat := 1\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def usePubOnlyC : Nat := usePubOnly\n",
        )?;
        fs::write(
            proj.join("Smoke/M.lean"),
            "module\nmeta import Smoke.A\nmeta def useMeta : Nat := p1 + p2 + metaConst\n",
        )?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-m", "public meta import order baseline"])?;

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic meta import Smoke.Provider2\npublic meta import Smoke.Provider1\npublic meta def metaConst : Nat := 1\n",
        )?;
        let rep_meta_imp_swap = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_meta_imp_swap.edit_class, "meta_only_module_edit");
        assert!(!rep_meta_imp_swap.public_signature_changed);
        assert!(
            rep_meta_imp_swap.meta_signature_changed,
            "swapping `public meta import` order must mark `meta_signature_changed = true`"
        );
        assert_eq!(
            Some(rep_meta_imp_swap.public_signature_digest.as_str()),
            rep_meta_imp_swap
                .baseline_public_signature_digest
                .as_deref()
        );
        assert_ne!(
            Some(rep_meta_imp_swap.meta_signature_digest.as_str()),
            rep_meta_imp_swap.baseline_meta_signature_digest.as_deref()
        );
        assert_eq!(
            rep_meta_imp_swap.transitive_dependents,
            vec!["Smoke.M".to_string()]
        );
        assert_eq!(
            rep_meta_imp_swap.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\n  /- meta cmt -/ public  meta  import  Smoke.Provider1 -- m1\n  public  meta  import  Smoke.Provider2\npublic meta def metaConst : Nat := 1\n",
        )?;
        let rep_meta_imp_ws = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert!(!rep_meta_imp_ws.public_signature_changed);
        assert!(!rep_meta_imp_ws.meta_signature_changed);
        assert_eq!(
            Some(rep_meta_imp_ws.meta_signature_digest.as_str()),
            rep_meta_imp_ws.baseline_meta_signature_digest.as_deref()
        );
        assert!(rep_meta_imp_ws.transitive_dependents.is_empty());
        assert_eq!(
            rep_meta_imp_ws.pruned_dependents,
            vec![
                "Smoke.B".to_string(),
                "Smoke.C".to_string(),
                "Smoke.M".to_string()
            ]
        );

        fs::write(
            proj.join("Smoke/Provider1.lean"),
            "module\nsyntax \"makeVal\" : term\nmacro_rules | `(makeVal) => `((0 : Nat))\n",
        )?;
        fs::write(
            proj.join("Smoke/Provider2.lean"),
            "module\nsyntax \"makeVal\" : term\nmacro_rules | `(makeVal) => `(true)\n",
        )?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic meta import Smoke.Provider1\npublic def api := makeVal\npublic meta def helperMeta : Nat := 1\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useApi : Nat := api + 1\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useApiC : Nat := useApi\n",
        )?;
        fs::write(
            proj.join("Smoke/M.lean"),
            "module\nmeta import Smoke.A\nmeta def useMeta : Nat := helperMeta\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "public meta import macro provider baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string(), "Smoke.M".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic meta import Smoke.Provider1\npublic def api := makeVal\npublic meta def helperMeta : Nat := 2\n",
        )?;
        let rep_meta_def_only = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_meta_def_only.edit_class, "meta_only_module_edit");
        assert!(!rep_meta_def_only.public_signature_changed);
        assert!(rep_meta_def_only.meta_signature_changed);
        assert_eq!(
            rep_meta_def_only.transitive_dependents,
            vec!["Smoke.M".to_string()]
        );
        assert_eq!(
            rep_meta_def_only.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic meta import Smoke.Provider2\npublic def api := makeVal\npublic meta def helperMeta : Nat := 1\n",
        )?;
        let rep_pub_meta_macro = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_pub_meta_macro.edit_class, "public_signature_edit");
        assert!(rep_pub_meta_macro.public_signature_changed);
        assert!(rep_pub_meta_macro.meta_signature_changed);
        assert_eq!(
            rep_pub_meta_macro.transitive_dependents,
            vec![
                "Smoke.B".to_string(),
                "Smoke.C".to_string(),
                "Smoke.M".to_string()
            ]
        );
        assert!(rep_pub_meta_macro.pruned_dependents.is_empty());
        let err_pub_meta_macro = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(err_pub_meta_macro.is_err());

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic meta import all Smoke.Provider2\npublic def api := makeVal\npublic meta def helperMeta : Nat := 1\n",
        )?;
        let err_pub_meta_all = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("invalid `public meta import all` header must fail closed in impact");
        assert!(
            format!("{err_pub_meta_all:#}").contains("cannot use `all` with `public import`"),
            "unexpected header error: {err_pub_meta_all:#}"
        );

        let a_pub_meta_ctx_v1 = "\
module
public meta def useNat : Bool := true
macro \"makeVal\" : term => if useNat then `((0 : Nat)) else `(true)
public def api := makeVal
";
        let a_pub_meta_ctx_v2 = "\
module
public meta def useNat : Bool := false
macro \"makeVal\" : term => if useNat then `((0 : Nat)) else `(true)
public def api := makeVal
";
        fs::write(proj.join("Smoke/A.lean"), a_pub_meta_ctx_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useApi : Nat := api + 1\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\nimport Smoke.B\npublic def useApiC : Nat := useApi\n",
        )?;
        fs::write(
            proj.join("Smoke/M.lean"),
            "module\nmeta import Smoke.A\nmeta def useMeta : Bool := useNat\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "public meta def macro context baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string(), "Smoke.M".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_pub_meta_ctx_v2)?;
        let rep_pub_meta_ctx = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_pub_meta_ctx.edit_class, "public_signature_edit");
        assert!(
            rep_pub_meta_ctx.public_signature_changed,
            "preceding `public meta def` controlling macro before `public def` must mark `public_signature_changed = true`"
        );
        assert!(rep_pub_meta_ctx.meta_signature_changed);
        assert_eq!(
            rep_pub_meta_ctx.transitive_dependents,
            vec![
                "Smoke.B".to_string(),
                "Smoke.C".to_string(),
                "Smoke.M".to_string()
            ]
        );
        assert!(
            rep_pub_meta_ctx.pruned_dependents.is_empty(),
            "ordinary public importers must NOT be pruned when preceding `public meta def` changes `api` from `Nat` to `Bool`"
        );
        let err_pub_meta_ctx = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_pub_meta_ctx.is_err(),
            "downstream ordinary consumer Smoke.B must be rechecked and fail when `useNat` flips `api` from `Nat` to `Bool`"
        );

        let a_trail_attr_v1 = "\
module
namespace SmokeA
public class MyTag (α : Type) where
  tag : Nat
@[expose, instance_reducible] public def mkTag100 : MyTag Nat := { tag := 1 }
@[expose, instance_reducible] public def mkTag150 : MyTag Nat := { tag := 2 }
attribute [instance 150] mkTag150
attribute [instance 100] mkTag100
end SmokeA
";
        let a_trail_attr_v2 = "\
module
namespace SmokeA
public class MyTag (α : Type) where
  tag : Nat
@[expose, instance_reducible] public def mkTag100 : MyTag Nat := { tag := 1 }
@[expose, instance_reducible] public def mkTag150 : MyTag Nat := { tag := 2 }
attribute [instance 150] mkTag150
attribute [instance 200] mkTag100
end SmokeA
";
        fs::write(proj.join("Smoke/A.lean"), a_trail_attr_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic theorem useTag : (inferInstance : SmokeA.MyTag Nat).tag = 2 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic theorem useTagC : (inferInstance : SmokeA.MyTag Nat).tag = 2 := useTag\n",
        )?;
        let _ = fs::remove_file(proj.join("Smoke/M.lean"));
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "trailing non-local attribute baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;

        fs::write(proj.join("Smoke/A.lean"), a_trail_attr_v2)?;
        let rep_trail_attr = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_trail_attr.edit_class, "public_signature_edit");
        assert!(
            rep_trail_attr.public_signature_changed,
            "trailing `attribute [instance 100]` -> `200` outside `public section` must mark `public_signature_changed = true`"
        );
        assert!(rep_trail_attr.meta_signature_changed);
        assert_eq!(
            rep_trail_attr.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(
            rep_trail_attr.pruned_dependents.is_empty(),
            "downstream consumers must not be pruned on trailing non-local attribute edit"
        );
        // Consumer `Smoke.B` actually fails to elaborate when `mkTag100` priority rises from 100 to 200 (`tag = 1` != `2`),
        // proving `lake_recheck_dependents_with_store` does NOT cut off at `Smoke.A` and rechecks `Smoke.B`.
        let err_recheck = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_recheck.is_err(),
            "downstream consumer Smoke.B must be rechecked (and fail typechecking) when trailing `attribute [instance 100]` changes to `200`"
        );

        let a_trail_local_attr_v1 =
            format!("{a_trail_attr_v1}attribute [local instance 300] SmokeA.mkTag100\n");
        let a_trail_local_attr_v2 =
            format!("{a_trail_attr_v1}attribute [local instance 400] SmokeA.mkTag100\n");
        fs::write(proj.join("Smoke/A.lean"), &a_trail_local_attr_v1)?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "trailing local attribute baseline"])?;
        fs::write(proj.join("Smoke/A.lean"), &a_trail_local_attr_v2)?;
        let rep_trail_local_attr = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_trail_local_attr.edit_class, "private_module_edit");
        assert!(
            !rep_trail_local_attr.public_signature_changed,
            "trailing `attribute [local ...]` edit after all public declarations must stay `private_module_edit`"
        );
        assert!(!rep_trail_local_attr.meta_signature_changed);
        assert!(rep_trail_local_attr.transitive_dependents.is_empty());
        assert_eq!(
            rep_trail_local_attr.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        // Command-bearing diagnostic wrappers (`#time`, `#guard_msgs`, `#info_trees`, `#with_exporting`,
        // `open ... in #time`, `#eval`, `assert_not_exists`, `#exit`) must NEVER be discarded as pure
        // diagnostics in `compute_impact_report`: exported signature/body/directive edits under them
        // must mark `public_signature_changed = true` and retain downstream dependents (`Smoke.B`, `Smoke.C`).
        let a_time_v1 = "module\n#time\n@[expose] public def timedApi : Nat := 1\n";
        let a_time_v2 = "module\n#time\n@[expose] public def timedApi : Nat := 2\n";
        fs::write(proj.join("Smoke/A.lean"), a_time_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic theorem useTimed : timedApi = 1 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic theorem useTimedC : timedApi = 1 := useTimed\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "time wrapper baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;

        fs::write(proj.join("Smoke/A.lean"), a_time_v2)?;
        let rep_time = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_time.edit_class, "public_signature_edit");
        assert!(
            rep_time.public_signature_changed,
            "`#time` wrapping `@[expose] public def` edit must mark `public_signature_changed = true`"
        );
        assert!(rep_time.meta_signature_changed);
        assert_eq!(
            rep_time.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(
            rep_time.pruned_dependents.is_empty(),
            "downstream consumers must NOT be pruned when `#time`-wrapped public declaration changes"
        );
        let err_time_recheck = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_time_recheck.is_err(),
            "downstream consumer Smoke.B (`timedApi = 1`) must be rechecked and fail when `timedApi` changes to `2` under `#time`"
        );

        let a_guard_msgs_v1 = "module\n#guard_msgs (drop info) in\npublic def gmApi : Nat := 1\n";
        let a_guard_msgs_v2 =
            "module\n#guard_msgs (drop info) in\npublic def gmApi : Bool := true\n";
        fs::write(proj.join("Smoke/A.lean"), a_guard_msgs_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useGm : Nat := gmApi\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic def useGmC : Nat := useGm\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "guard_msgs wrapper baseline"])?;
        fs::write(proj.join("Smoke/A.lean"), a_guard_msgs_v2)?;
        let rep_gm = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_gm.edit_class, "public_signature_edit");
        assert!(rep_gm.public_signature_changed);
        assert_eq!(
            rep_gm.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_gm.pruned_dependents.is_empty());

        // Moving a scope boundary (`end`) before vs after a `public def` (changing whether
        // section-local `variable (x : Nat)` / `open` applies to `public def`) must mark
        // `public_signature_changed = true`, retain downstream consumers in `compute_impact_report`,
        // and refuse early cutoff in `lake_recheck_dependents_with_store` (catching real downstream breakage).
        let a_sec_v1 = "module\nsection\nvariable (x : Nat)\npublic def secApi : Nat := x\nend\n";
        let a_sec_v2 = "module\nsection\nvariable (x : Nat)\nend\npublic def secApi : Nat := 0\n";
        fs::write(proj.join("Smoke/A.lean"), a_sec_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useSec : Nat := secApi 42\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic def useSecC : Nat := useSec\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "section boundary baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_sec_v2)?;
        let rep_sec = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_sec.edit_class, "public_signature_edit");
        assert!(
            rep_sec.public_signature_changed,
            "moving `end` before `public def` must mark `public_signature_changed = true`"
        );
        assert!(rep_sec.meta_signature_changed);
        assert_eq!(
            rep_sec.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(
            rep_sec.pruned_dependents.is_empty(),
            "downstream consumers must NOT be pruned when `section ... end` boundary shifts across `public def`"
        );
        let err_sec_recheck = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_sec_recheck.is_err(),
            "downstream consumer Smoke.B (`secApi 42`) must be rechecked and fail when `end` moves before `secApi` (0-ary `Nat`)"
        );

        // Moving `end` before vs after an exported `attribute [instance ...]` directive where a
        // section-scoped `open` selects which candidate receives `[instance 200]` must mark
        // `public_signature_changed = true` and fail downstream recheck instead of falsely cutting off.
        let a_dir_sec_v1 = "\
module
public class Tag (α : Type) where val : Nat
@[expose, instance_reducible] public def instTag : Tag Nat := { val := 22 }
namespace Foo
@[expose, instance_reducible] public def instTag : Tag Nat := { val := 11 }
attribute [instance 200] instTag
end Foo
";
        let a_dir_sec_v2 = "\
module
public class Tag (α : Type) where val : Nat
@[expose, instance_reducible] public def instTag : Tag Nat := { val := 22 }
namespace Foo
@[expose, instance_reducible] public def instTag : Tag Nat := { val := 11 }
end Foo
attribute [instance 200] instTag
";
        fs::write(proj.join("Smoke/A.lean"), a_dir_sec_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\nattribute [instance 150] _root_.instTag\npublic theorem useDirSec : (inferInstance : Tag Nat).val = 11 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic theorem useDirSecC : (inferInstance : Tag Nat).val = 11 := useDirSec\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "directive section boundary baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_dir_sec_v2)?;
        let rep_dir_sec = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_dir_sec.edit_class, "public_signature_edit");
        assert!(
            rep_dir_sec.public_signature_changed,
            "moving `end` before exported `notation` must mark `public_signature_changed = true`"
        );
        assert_eq!(
            rep_dir_sec.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_dir_sec.pruned_dependents.is_empty());
        let err_dir_sec_recheck = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_dir_sec_recheck.is_err(),
            "downstream consumer Smoke.B must be rechecked and fail when `end` moves before `attribute [instance 200] instTag`"
        );

        // Moving `end` before vs after an exported `macro` directive where a section-scoped
        // `set_option hygiene false` governs macro hygiene must mark `public_signature_changed = true`
        // and fail downstream recheck instead of falsely cutting off.
        let a_sec_macro_v1 = "\
module
section
set_option hygiene false
macro \"SEC_VAL\" : term => `(macVal)
end
";
        let a_sec_macro_v2 = "\
module
section
set_option hygiene false
end
macro \"SEC_VAL\" : term => `(macVal)
";
        fs::write(proj.join("Smoke/A.lean"), a_sec_macro_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\n@[expose] public def macVal : Nat := 11\npublic theorem useSecMacro : SEC_VAL = 11 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic theorem useSecMacroC : SEC_VAL = 11 := useSecMacro\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "section macro boundary baseline"])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_sec_macro_v2)?;
        let rep_sec_macro = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_sec_macro.edit_class, "public_signature_edit");
        assert!(
            rep_sec_macro.public_signature_changed,
            "moving unnamed `section ... end` before exported `macro` must mark `public_signature_changed = true`"
        );
        assert_eq!(
            rep_sec_macro.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_sec_macro.pruned_dependents.is_empty());
        let err_sec_macro_recheck = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_sec_macro_recheck.is_err(),
            "downstream consumer Smoke.B (`SEC_VAL = 11`) must be rechecked and fail when unnamed `end` moves before `macro \"SEC_VAL\"`"
        );

        // Editing or renaming a trailing private `section ... end` containing private theorems
        // after all public declarations must classify as `private_module_edit`
        // (`public_signature_changed = false`), prune downstream dependents `Smoke.B` and `Smoke.C`
        // in `compute_impact_report`, and cut off Stage-2 native recheck after `Smoke.A` (since
        // `.ir`/`.ir.sig` and `dumpPublicSignatureJson` stay unchanged).
        let a_trail_sec_v1 =
            "module\npublic def apiStable : Nat := 7\nsection Priv1\nvariable (k : Nat)\nprivate theorem p : k = k := rfl\nend Priv1\n";
        let a_trail_sec_v2 =
            "module\npublic def apiStable : Nat := 7\nsection Priv2\nvariable (b : Bool)\nprivate theorem p2 : b = b := rfl\nend Priv2\n";
        fs::write(proj.join("Smoke/A.lean"), a_trail_sec_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useStable : Nat := apiStable\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic def useStableC : Nat := useStable\n",
        )?;
        let _ = fs::remove_file(proj.join("Smoke/Provider1.lean"));
        let _ = fs::remove_file(proj.join("Smoke/Provider2.lean"));
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "trailing private section baseline"])?;
        fs::write(proj.join("Smoke/A.lean"), a_trail_sec_v2)?;
        let rep_trail_sec = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_trail_sec.edit_class, "private_module_edit");
        assert!(
            !rep_trail_sec.public_signature_changed,
            "trailing private `section ... end` edit must NOT mark `public_signature_changed = true`"
        );
        assert!(!rep_trail_sec.meta_signature_changed);
        assert!(rep_trail_sec.transitive_dependents.is_empty());
        assert_eq!(
            rep_trail_sec.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        let (n_trail_sec, _, mods_trail_sec, _) = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        )?;
        assert_eq!(n_trail_sec, 1);
        assert_eq!(mods_trail_sec, vec!["Smoke.A".to_string()]);

        // Also verify compute_impact_report prunes downstream dependents even when the trailing
        // private section contains `private def` items.
        let a_trail_priv_def =
            "module\npublic def apiStable : Nat := 7\nsection Priv3\nvariable (m : Nat)\nprivate def pDef : Nat := m + 1\nend Priv3\n";
        fs::write(proj.join("Smoke/A.lean"), a_trail_priv_def)?;
        let rep_trail_priv_def = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_trail_priv_def.edit_class, "private_module_edit");
        assert!(!rep_trail_priv_def.public_signature_changed);
        assert!(!rep_trail_priv_def.meta_signature_changed);
        assert!(rep_trail_priv_def.transitive_dependents.is_empty());
        assert_eq!(
            rep_trail_priv_def.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        // Placeholder return-type / binder-type / unannotated-binder declarations MUST classify
        // body edits as `public_signature_edit` (NOT `private_module_edit` or `proof_body_only`)
        // and retain downstream dependents (`Smoke.B`, `Smoke.C`), while fully annotated public
        // definitions and theorems preserve `private_module_edit` / `proof_body_only` cutoff.
        for (commit_msg, base_a, edited_a) in [
            (
                "placeholder return type `_` baseline",
                "module\npublic def api : _ := (0 : Nat)\n",
                "module\npublic def api : _ := true\n",
            ),
            (
                "partial placeholder return type `List _` baseline",
                "module\npublic def api : List _ := [0]\n",
                "module\npublic def api : List _ := [true]\n",
            ),
            (
                "named hole return type `?_` baseline",
                "module\npublic def api : ?_ := 0\n",
                "module\npublic def api : ?_ := true\n",
            ),
            (
                "placeholder theorem statement `: _` baseline",
                "module\npublic theorem thm : _ := True.intro\n",
                "module\npublic theorem thm : _ := (rfl : 0 = 0)\n",
            ),
            (
                "placeholder binder `(x : _)` baseline",
                "module\npublic def api (x : _) : Nat := x + 1\n",
                "module\npublic def api (x : _) : Nat := if x then 1 else 0\n",
            ),
            (
                "unannotated binder `(x)` baseline",
                "module\npublic def api (x) : Nat := x + 1\n",
                "module\npublic def api (x) : Nat := if x then 1 else 0\n",
            ),
            (
                "bare binder `x` baseline",
                "module\npublic def api x : Nat := x + 1\n",
                "module\npublic def api x : Nat := if x then 1 else 0\n",
            ),
            (
                "unannotated implicit binder `{x}` baseline",
                "module\npublic def api {x} : Nat := x + 1\n",
                "module\npublic def api {x} : Nat := if x then 1 else 0\n",
            ),
            (
                "placeholder strict-implicit binder `⦃x : _⦄` baseline",
                "module\npublic def api ⦃x : _⦄ : Nat := x + 1\n",
                "module\npublic def api ⦃x : _⦄ : Nat := if x then 1 else 0\n",
            ),
            (
                "strict-implicit binder `⦃x : Nat⦄` without top-level return type baseline",
                "module\npublic def api ⦃x : Nat⦄ := x + 1\n",
                "module\npublic def api ⦃x : Nat⦄ := true\n",
            ),
        ] {
            fs::write(proj.join("Smoke/A.lean"), base_a)?;
            fs::write(
                proj.join("Smoke/B.lean"),
                "module\npublic import Smoke.A\npublic def useB : Nat := 1\n",
            )?;
            fs::write(
                proj.join("Smoke/C.lean"),
                "module\npublic import Smoke.B\npublic def useC : Nat := useB\n",
            )?;
            run_git(&["add", "-A"])?;
            run_git(&["commit", "-m", commit_msg])?;
            fs::write(proj.join("Smoke/A.lean"), edited_a)?;
            let rep_hole = compute_impact_report(
                proj.join("Smoke/A.lean"),
                Some(proj.clone()),
                Some("HEAD".to_string()),
            )?;
            assert_eq!(
                rep_hole.edit_class, "public_signature_edit",
                "{commit_msg}: body edit on placeholder/unannotated-binder decl must be public_signature_edit"
            );
            assert!(
                rep_hole.public_signature_changed,
                "{commit_msg}: public_signature_changed must be true"
            );
            assert_eq!(
                rep_hole.transitive_dependents,
                vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
            );
            assert!(rep_hole.pruned_dependents.is_empty());
        }

        // Fully annotated `public theorem thm (x_1 : Nat) : x_1 = x_1` BEFORE `public def api.{u} (x_1 : _root_.Nat) : Nat`
        // keeps `proof_body_only` (theorem proof edit before public def) and `private_module_edit`
        // (trailing unexposed public def body edit) cutoff intact.
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic theorem thm (x_1 : Nat) : x_1 = x_1 := rfl\npublic def api.{u} (x_1 : _root_.Nat) : Nat := x_1 + 1\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&["commit", "-m", "fully annotated thm before def baseline"])?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic theorem thm (x_1 : Nat) : x_1 = x_1 := rfl\npublic def api.{u} (x_1 : _root_.Nat) : Nat := 1 + x_1\n",
        )?;
        let rep_annot_def = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_annot_def.edit_class, "private_module_edit");
        assert!(!rep_annot_def.public_signature_changed);
        assert!(rep_annot_def.transitive_dependents.is_empty());
        assert_eq!(
            rep_annot_def.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic theorem thm (x_1 : Nat) : x_1 = x_1 := Eq.refl x_1\npublic def api.{u} (x_1 : _root_.Nat) : Nat := x_1 + 1\n",
        )?;
        let rep_annot_thm = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_annot_thm.edit_class, "proof_body_only");
        assert!(!rep_annot_thm.public_signature_changed);
        assert!(rep_annot_thm.transitive_dependents.is_empty());
        assert_eq!(
            rep_annot_thm.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        // P2 4481733184 regression: within a `module`, an unexposed `public def flag : Bool := true`
        // is reducible to subsequent declarations inside the same module! Flipping `flag` from `true`
        // to `false` changes `api`'s elaborated type from `Nat` to `Bool`, so `compute_impact_report`
        // MUST classify as `public_signature_edit` (`public_signature_changed == true`) and retain
        // `Smoke.B` and `Smoke.C` (and Stage-2 native recheck must fail on broken `Smoke.B`).
        let a_p2_intra_v1 = "\
module
public def flag : Bool := true
public def api := by
  first
  | have h : flag = true := rfl
    exact (0 : Nat)
  | exact false
";
        let a_p2_intra_v2 = "\
module
public def flag : Bool := false
public def api := by
  first
  | have h : flag = true := rfl
    exact (0 : Nat)
  | exact false
";
        fs::write(proj.join("Smoke/A.lean"), a_p2_intra_v1)?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useB : Nat := api + 1\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic def useC : Nat := useB\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&[
            "commit",
            "-m",
            "intra-module public def reducibility baseline",
        ])?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_p2_intra_v2)?;
        let rep_p2_intra = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_p2_intra.edit_class, "public_signature_edit");
        assert!(
            rep_p2_intra.public_signature_changed,
            "preceding unexposed `public def flag : Bool` edit before `public def api := ...` must mark `public_signature_changed = true`"
        );
        assert!(rep_p2_intra.meta_signature_changed);
        assert_eq!(
            rep_p2_intra.transitive_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );
        assert!(rep_p2_intra.pruned_dependents.is_empty());
        let err_p2_intra_recheck = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            Some("HEAD"),
            false,
        );
        assert!(
            err_p2_intra_recheck.is_err(),
            "downstream consumer Smoke.B (`api + 1`) must be rechecked and fail when `flag` flips `api` from `Nat` to `Bool`"
        );

        for (commit_msg, base_a, edited_a) in [
            (
                "preceding public def type alias baseline",
                "module\npublic def ty : Type := Nat\npublic def useTy (x : ty) : ty := x\n",
                "module\npublic def ty : Type := Bool\npublic def useTy (x : ty) : ty := x\n",
            ),
            (
                "preceding public section def baseline",
                "module\npublic section\ndef flag : Bool := true\ndef api := flag\nend\n",
                "module\npublic section\ndef flag : Bool := false\ndef api := flag\nend\n",
            ),
            (
                "mutual public def sibling baseline",
                "module\nmutual\n  public def a := b\n  public def b : Bool := true\nend\n",
                "module\nmutual\n  public def a := b\n  public def b : Bool := false\nend\n",
            ),
            (
                "preceding public def before exported notation baseline",
                "module\npublic def flag : Bool := true\nnotation \"PUB_FLAG\" => flag\n",
                "module\npublic def flag : Bool := false\nnotation \"PUB_FLAG\" => flag\n",
            ),
        ] {
            fs::write(proj.join("Smoke/A.lean"), base_a)?;
            fs::write(
                proj.join("Smoke/B.lean"),
                "module\npublic import Smoke.A\npublic def useB : Nat := 1\n",
            )?;
            fs::write(
                proj.join("Smoke/C.lean"),
                "module\npublic import Smoke.B\npublic def useC : Nat := useB\n",
            )?;
            run_git(&["add", "-A"])?;
            run_git(&["commit", "-m", commit_msg])?;
            fs::write(proj.join("Smoke/A.lean"), edited_a)?;
            let rep_sub = compute_impact_report(
                proj.join("Smoke/A.lean"),
                Some(proj.clone()),
                Some("HEAD".to_string()),
            )?;
            assert_eq!(
                rep_sub.edit_class, "public_signature_edit",
                "{commit_msg}: preceding public def body edit must be public_signature_edit"
            );
            assert!(rep_sub.public_signature_changed);
            assert_eq!(
                rep_sub.transitive_dependents,
                vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
            );
            assert!(rep_sub.pruned_dependents.is_empty());
        }

        // Preceding unexposed `public def` edit followed ONLY by `public meta def` classifies as
        // `meta_only_module_edit`, retaining `Smoke.M` (`meta import Smoke.A`) while pruning
        // ordinary importers `Smoke.B` and `Smoke.C`!
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic def flag : Bool := true\npublic meta def metaApi : Bool := flag\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic def useB : Bool := flag\n",
        )?;
        fs::write(
            proj.join("Smoke/C.lean"),
            "module\npublic import Smoke.B\npublic def useC : Bool := useB\n",
        )?;
        fs::write(
            proj.join("Smoke/M.lean"),
            "module\nmeta import Smoke.A\nmeta def useMeta : Bool := metaApi\n",
        )?;
        run_git(&["add", "-A"])?;
        run_git(&[
            "commit",
            "-m",
            "preceding public def before public meta def baseline",
        ])?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic def flag : Bool := false\npublic meta def metaApi : Bool := flag\n",
        )?;
        let rep_pub_before_meta = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(rep_pub_before_meta.edit_class, "meta_only_module_edit");
        assert!(!rep_pub_before_meta.public_signature_changed);
        assert!(rep_pub_before_meta.meta_signature_changed);
        assert_eq!(
            rep_pub_before_meta.transitive_dependents,
            vec!["Smoke.M".to_string()]
        );
        assert_eq!(
            rep_pub_before_meta.pruned_dependents,
            vec!["Smoke.B".to_string(), "Smoke.C".to_string()]
        );

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_speed4_cutoff_shielded_fails_closed_on_stale_non_cutoff_dependencies() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_speed4_cutoff_non_cutoff_deps_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let proj = tmp_dir.join("proj");
        let dep_dir = proj.join(".lake/packages/dep_pkg");
        let pb_pkg = tmp_dir.join("pb_pkg");
        let cache = tmp_dir.join("cache");
        fs::create_dir_all(proj.join("Smoke"))?;
        fs::create_dir_all(dep_dir.join("DepPkg"))?;
        fs::create_dir_all(pb_pkg.join("Prebuilt"))?;
        fs::create_dir_all(&cache)?;

        let tc = "leanprover/lean4:v4.35.0\n";
        fs::write(proj.join("lean-toolchain"), tc)?;
        fs::write(dep_dir.join("lean-toolchain"), tc)?;
        fs::write(pb_pkg.join("lean-toolchain"), tc)?;

        fs::write(
            pb_pkg.join("lakefile.toml"),
            "name = \"pb_pkg\"\ndefaultTargets = [\"Prebuilt\"]\n[[lean_lib]]\nname = \"Prebuilt\"\nglobs = [\"Prebuilt.+\"]\n",
        )?;
        let pb_v1 = "module\n@[expose] public def pbVal : Nat := 100\n";
        let pb_v2 = "module\n@[expose] public def pbVal : Nat := 200\n";
        fs::write(pb_pkg.join("Prebuilt/Ext.lean"), pb_v1)?;

        let mut store = TurboStore::open(Some(&cache))?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &pb_pkg,
            &["Prebuilt.Ext".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let pb_lib_dir = pb_pkg
            .join(".lake/build/lib/lean")
            .canonicalize()
            .unwrap_or_else(|_| pb_pkg.join(".lake/build/lib/lean"));

        struct LeanPathEnvGuard(Option<std::ffi::OsString>);
        impl Drop for LeanPathEnvGuard {
            fn drop(&mut self) {
                match &self.0 {
                    Some(v) => std::env::set_var("LEAN_PATH", v),
                    None => std::env::remove_var("LEAN_PATH"),
                }
            }
        }
        let _lp_guard = LeanPathEnvGuard(std::env::var_os("LEAN_PATH"));
        std::env::set_var("LEAN_PATH", &pb_lib_dir);

        fs::write(
            dep_dir.join("lakefile.toml"),
            "name = \"dep_pkg\"\n[[lean_lib]]\nname = \"DepPkg\"\nroots = [\"DepPkg.Base\"]\n",
        )?;
        let dep_v1 = "module\n@[expose] public def depVal : Nat := 10\n";
        let dep_v2 = "module\n@[expose] public def depVal : Nat := 20\n";
        fs::write(dep_dir.join("DepPkg/Base.lean"), dep_v1)?;

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
  "name": "cutoff_pin_smoke",
  "lakeDir": ".lake",
  "fixedToolchain": false
}"#;
        fs::write(proj.join("lake-manifest.json"), manifest_json)?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"cutoff_pin_smoke\"\ndefaultTargets = [\"Smoke\"]\n[[lean_lib]]\nname = \"Smoke\"\nroots = [\"Smoke.A\", \"Smoke.U\", \"Smoke.B\", \"Smoke.C\"]\n",
        )?;

        let a_base = "module\n@[expose] public def pubA : Nat := 1\npublic theorem a_thm (n : Nat) : n + 0 = n := by\n  exact Nat.add_zero n\n";
        let a_priv_v1 = "module\n@[expose] public def pubA : Nat := 1\npublic theorem a_thm (n : Nat) : n + 0 = n := by\n  have _h1 : 1 + 1 = 2 := rfl\n  exact Nat.add_zero n\nprivate theorem extra_priv_1 : 2 + 2 = 4 := rfl\n";
        let a_priv_v2 = "module\n@[expose] public def pubA : Nat := 1\npublic theorem a_thm (n : Nat) : n + 0 = n := by\n  have _h2 : 3 + 3 = 6 := rfl\n  exact Nat.add_zero n\nprivate theorem extra_priv_2 : 4 + 4 = 8 := rfl\n";
        let a_priv_v3 = "module\n@[expose] public def pubA : Nat := 1\npublic theorem a_thm (n : Nat) : n + 0 = n := by\n  have _h3 : 5 + 5 = 10 := rfl\n  exact Nat.add_zero n\nprivate theorem extra_priv_3 : 6 + 6 = 12 := rfl\n";
        let a_priv_v4 = "module\n@[expose] public def pubA : Nat := 1\npublic theorem a_thm (n : Nat) : n + 0 = n := by\n  have _h4 : 7 + 7 = 14 := rfl\n  exact Nat.add_zero n\nprivate theorem extra_priv_4 : 8 + 8 = 16 := rfl\n";
        let a_priv_v5 = "module\n@[expose] public def pubA : Nat := 1\npublic theorem a_thm (n : Nat) : n + 0 = n := by\n  have _h5 : 9 + 9 = 18 := rfl\n  exact Nat.add_zero n\nprivate theorem extra_priv_5 : 10 + 10 = 20 := rfl\n";

        let u_v1 = "module\n@[expose] public def uVal : Nat := 5\n";
        let u_v2 = "module\n@[expose] public def uVal : Nat := 6\n";
        let b_src = "module\npublic import Smoke.A\npublic import Smoke.U\npublic import DepPkg.Base\npublic import Prebuilt.Ext\n@[expose] public def bVal : Nat := pubA + uVal + depVal + pbVal\n";
        let c_src = "module\npublic import Smoke.B\n@[expose] public def cVal : Nat := bVal + 1\n";
        let s_ok = "module\nimport Smoke.B\nimport Smoke.U\ntheorem s_thm : bVal = 116 := rfl\n";

        fs::write(proj.join("Smoke/A.lean"), a_base)?;
        fs::write(proj.join("Smoke/U.lean"), u_v1)?;
        fs::write(proj.join("Smoke/B.lean"), b_src)?;
        fs::write(proj.join("Smoke/C.lean"), c_src)?;
        fs::write(proj.join("Smoke/StandaloneCheck.lean"), s_ok)?;

        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        let canon_proj = proj.canonicalize().unwrap_or_else(|_| proj.clone());

        fs::write(proj.join("Smoke/A.lean"), a_priv_v1)?;
        let (n_clean, _, mods_clean, _) = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            None,
            false,
        )?;
        assert_eq!(n_clean, 1);
        assert_eq!(mods_clean, vec!["Smoke.A".to_string()]);

        fs::write(proj.join("Smoke/U.lean"), u_v2)?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.U".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(
            proj.join("Smoke/StandaloneCheck.lean"),
            "module\nimport Smoke.B\nimport Smoke.U\ntheorem s_thm : bVal = 117 := rfl\n",
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_priv_v2)?;
        let (n_stale_local, _, mut mods_stale_local, _) = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            None,
            false,
        )?;
        mods_stale_local.sort();
        assert_eq!(
            mods_stale_local,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(n_stale_local, 4);
        assert!(load_verified_project_manifest(&canon_proj)
            .is_some_and(|m| m.modules.contains_key("Smoke/B.lean")
                && m.modules.contains_key("Smoke/C.lean")));

        fs::write(dep_dir.join("DepPkg/Base.lean"), dep_v2)?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &dep_dir,
            &["DepPkg.Base".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(
            proj.join("Smoke/StandaloneCheck.lean"),
            "module\nimport Smoke.B\nimport Smoke.U\ntheorem s_thm : bVal = 127 := rfl\n",
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_priv_v3)?;
        let (n_stale_dep_pkg, _, mut mods_stale_dep_pkg, _) = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            None,
            false,
        )?;
        mods_stale_dep_pkg.sort();
        assert_eq!(
            mods_stale_dep_pkg,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(n_stale_dep_pkg, 4);

        fs::write(pb_pkg.join("Prebuilt/Ext.lean"), pb_v2)?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &pb_pkg,
            &["Prebuilt.Ext".to_string()],
            "trusted",
            1,
            false,
            true,
            None,
        )?;
        fs::write(
            proj.join("Smoke/StandaloneCheck.lean"),
            "module\nimport Smoke.B\nimport Smoke.U\ntheorem s_thm : bVal = 227 := rfl\n",
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_priv_v4)?;
        let (n_stale_prebuilt, _, mut mods_stale_prebuilt, _) = lake_recheck_dependents_with_store(
            Some(&store),
            &canon_proj,
            &["Smoke/A.lean".to_string()],
            None,
            false,
        )?;
        mods_stale_prebuilt.sort();
        assert_eq!(
            mods_stale_prebuilt,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(n_stale_prebuilt, 4);

        let manifest_path = verified_sources_manifest_path(&canon_proj);
        fs::remove_file(&manifest_path)?;
        fs::remove_file(canon_proj.join(".lake/build/lib/lean/Smoke/U.olean"))?;
        fs::write(
            proj.join("Smoke/StandaloneCheck.lean"),
            "module\nimport Smoke.A\nimport Smoke.U\ntheorem s_thm : pubA + uVal = 7 := rfl\n",
        )?;
        fs::write(proj.join("Smoke/A.lean"), a_priv_v5)?;
        let (n_lake_only_stale, _, mut mods_lake_only_stale, _) =
            lake_recheck_dependents_with_store(
                Some(&store),
                &canon_proj,
                &["Smoke/A.lean".to_string()],
                None,
                false,
            )?;
        mods_lake_only_stale.sort();
        assert_eq!(
            mods_lake_only_stale,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(n_lake_only_stale, 4);
        assert!(canon_proj
            .join(".lake/build/lib/lean/Smoke/U.olean")
            .is_file());

        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic import Smoke.U\npublic import DepPkg.Base\n@[expose] public def bVal : Nat := pubA + uVal + depVal\n",
        )?;
        fs::write(
            proj.join("Smoke/StandaloneCheck.lean"),
            "module\nimport Smoke.B\nimport Smoke.U\ntheorem s_thm : bVal = 27 := rfl\n",
        )?;
        crate::module_builder::build_project_modules_native(
            &mut store,
            &proj,
            &["Smoke.C".to_string()],
            "untrusted",
            1,
            false,
            true,
            None,
        )?;
        let closure_strict =
            compute_project_dependent_closure(&canon_proj, &["Smoke/A.lean".to_string()], true)?;
        let dag_strict = closure_strict.dag.as_ref().unwrap();
        let baselines_strict = capture_pre_rebuild_module_baselines(
            &store.root,
            &closure_strict.cfg,
            dag_strict,
            &closure_strict.edited_dag_modules,
            None,
            false,
        )
        .unwrap();
        let (pre_raw_strict, pre_man_strict) = load_pre_rebuild_root_manifest(&canon_proj);
        let mut verdicts_strict = HashMap::new();
        verdicts_strict.insert(
            "Smoke.A".to_string(),
            ModuleCutoffVerdict {
                cuts_off_public: true,
                cuts_off_meta: true,
            },
        );
        let edited_standalone_empty = std::collections::BTreeSet::new();
        let (rechecked_strict_clean, _, standalone_strict_clean, memo_strict_clean) =
            compute_stage2_dependent_closure_after_cutoff(
                &canon_proj,
                &closure_strict,
                dag_strict,
                &edited_standalone_empty,
                &baselines_strict,
                &verdicts_strict,
                &pre_raw_strict,
                pre_man_strict.as_ref(),
                Some(&store),
            )?;
        assert_eq!(rechecked_strict_clean, vec!["Smoke.A".to_string()]);
        assert!(standalone_strict_clean.is_empty());
        assert_eq!(memo_strict_clean.get("Smoke.B"), Some(&true));

        let mut tampered_man = pre_man_strict.clone().unwrap();
        if let Some(ent_b) = tampered_man.modules.get_mut("Smoke/B.lean") {
            ent_b.import_olean_digests.insert(
                "Smoke.U".to_string(),
                "0000000000000000000000000000000000000000000000000000000000000000".to_string(),
            );
            ent_b.import_export_digests.insert(
                "Smoke.U".to_string(),
                "0000000000000000000000000000000000000000000000000000000000000000".to_string(),
            );
            ent_b.import_meta_digests.insert(
                "Smoke.U".to_string(),
                "0000000000000000000000000000000000000000000000000000000000000000".to_string(),
            );
        }
        let (mut rechecked_strict_tampered, _, standalone_strict_tampered, memo_strict_tampered) =
            compute_stage2_dependent_closure_after_cutoff(
                &canon_proj,
                &closure_strict,
                dag_strict,
                &edited_standalone_empty,
                &baselines_strict,
                &verdicts_strict,
                &pre_raw_strict,
                Some(&tampered_man),
                Some(&store),
            )?;
        rechecked_strict_tampered.sort();
        assert_eq!(
            rechecked_strict_tampered,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(memo_strict_tampered.get("Smoke.B"), Some(&false));
        assert_eq!(standalone_strict_tampered.len(), 1);

        let mut tampered_man_standalone = pre_man_strict.clone().unwrap();
        fs::write(
            proj.join("Smoke/StandaloneCheck.lean"),
            "module\nimport Smoke.A\nimport Smoke.U\ntheorem s_thm : pubA + uVal = 7 := rfl\n",
        )?;
        let closure_strict_sa =
            compute_project_dependent_closure(&canon_proj, &["Smoke/A.lean".to_string()], true)?;
        let dag_strict_sa = closure_strict_sa.dag.as_ref().unwrap();
        let (rechecked_sa_clean, _, standalone_sa_clean, _) =
            compute_stage2_dependent_closure_after_cutoff(
                &canon_proj,
                &closure_strict_sa,
                dag_strict_sa,
                &edited_standalone_empty,
                &baselines_strict,
                &verdicts_strict,
                &pre_raw_strict,
                Some(&tampered_man_standalone),
                Some(&store),
            )?;
        assert_eq!(rechecked_sa_clean, vec!["Smoke.A".to_string()]);
        assert!(standalone_sa_clean.is_empty());

        tampered_man_standalone.modules.remove("Smoke/U.lean");
        let (_, _, standalone_sa_u_unverified, _) = compute_stage2_dependent_closure_after_cutoff(
            &canon_proj,
            &closure_strict_sa,
            dag_strict_sa,
            &edited_standalone_empty,
            &baselines_strict,
            &verdicts_strict,
            &pre_raw_strict,
            Some(&tampered_man_standalone),
            Some(&store),
        )?;
        assert_eq!(standalone_sa_u_unverified.len(), 1);

        let (mut rechecked_strict_no_man, _, _, memo_strict_no_man) =
            compute_stage2_dependent_closure_after_cutoff(
                &canon_proj,
                &closure_strict,
                dag_strict,
                &edited_standalone_empty,
                &baselines_strict,
                &verdicts_strict,
                &None,
                None,
                Some(&store),
            )?;
        rechecked_strict_no_man.sort();
        assert_eq!(
            rechecked_strict_no_man,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(memo_strict_no_man.get("Smoke.B"), Some(&false));

        let canon_dep = dep_dir.canonicalize().unwrap_or_else(|_| dep_dir.clone());
        fs::remove_file(verified_sources_manifest_path(&canon_dep))?;
        let (mut rechecked_strict_dep_unverified, _, _, memo_strict_dep_unverified) =
            compute_stage2_dependent_closure_after_cutoff(
                &canon_proj,
                &closure_strict,
                dag_strict,
                &edited_standalone_empty,
                &baselines_strict,
                &verdicts_strict,
                &pre_raw_strict,
                pre_man_strict.as_ref(),
                Some(&store),
            )?;
        rechecked_strict_dep_unverified.sort();
        assert_eq!(
            rechecked_strict_dep_unverified,
            vec![
                "Smoke.A".to_string(),
                "Smoke.B".to_string(),
                "Smoke.C".to_string()
            ]
        );
        assert_eq!(memo_strict_dep_unverified.get("Smoke.B"), Some(&false));

        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_speed4_impact_report_fails_closed_on_invalid_config_dag_and_rev() -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_speed4_impact_fail_closed_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let proj = tmp_dir.join("proj");
        let solo_dir = tmp_dir.join("solo");
        fs::create_dir_all(proj.join("Smoke"))?;
        fs::create_dir_all(&solo_dir)?;

        let tc = include_str!("../../../../lean/lean-toolchain");
        fs::write(proj.join("lean-toolchain"), tc)?;
        let valid_lakefile =
            "name = \"smoke\"\n[[lean_lib]]\nname = \"Smoke\"\nglobs = [\"Smoke.+\"]\n";
        fs::write(proj.join("lakefile.toml"), valid_lakefile)?;
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic theorem a_thm : 1 + 1 = 2 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic theorem b_thm : 1 + 1 = 2 := a_thm\n",
        )?;

        let Some(git_bin) = crate::trusted_tools::discover_or_skip_trusted_git_for_test(&proj)?
        else {
            let _ = fs::remove_dir_all(&tmp_dir);
            return Ok(());
        };
        if std::env::var_os("TURBO_LEAN_GIT").is_none() {
            std::env::set_var("TURBO_LEAN_GIT", &git_bin);
        }
        let run_git = |args: &[&str]| -> Result<()> {
            let st = Command::new(&git_bin)
                .current_dir(&proj)
                .args(args)
                .env("GIT_AUTHOR_NAME", "Test")
                .env("GIT_AUTHOR_EMAIL", "test@example.com")
                .env("GIT_COMMITTER_NAME", "Test")
                .env("GIT_COMMITTER_EMAIL", "test@example.com")
                .status()?;
            anyhow::ensure!(st.success(), "git {:?} failed", args);
            Ok(())
        };
        run_git(&["init", "-q"])?;
        run_git(&["add", "."])?;
        run_git(&["commit", "-qm", "init"])?;

        // 0. Sanity: valid project succeeds and reports `Smoke.B` as dependent;
        //    newly added untracked file at valid `HEAD` and valid explicit `--rev HEAD` succeeds as unbaselined;
        //    non-Lake standalone file succeeds.
        let ok_rep = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(ok_rep.direct_dependents, vec!["Smoke.B".to_string()]);

        let new_file = proj.join("Smoke/NewMod.lean");
        fs::write(&new_file, "module\npublic def newVal : Nat := 42\n")?;
        let new_rep_default = compute_impact_report(new_file.clone(), Some(proj.clone()), None)?;
        assert_eq!(new_rep_default.edit_class, "unbaselined_module");
        assert_eq!(new_rep_default.module_name.as_deref(), Some("Smoke.NewMod"));
        let new_rep_explicit = compute_impact_report(
            new_file.clone(),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )?;
        assert_eq!(new_rep_explicit.edit_class, "unbaselined_module");
        fs::remove_file(&new_file)?;

        let solo_file = solo_dir.join("Solo.lean");
        fs::write(&solo_file, "module\npublic def soloVal : Nat := 7\n")?;
        let solo_rep = compute_impact_report(solo_file.clone(), None, None)?;
        assert_eq!(solo_rep.edit_class, "unbaselined_module");
        assert!(solo_rep.module_name.is_none());

        // 1. Corrupt `lake-manifest.json` must fail closed (`Err`), never silently return empty dependents.
        fs::write(proj.join("lake-manifest.json"), "{ invalid json ")?;
        let err_manifest = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("corrupt lake-manifest.json must fail closed");
        assert!(
            format!("{err_manifest:#}").contains("lake-manifest.json"),
            "unexpected manifest error: {err_manifest:#}"
        );
        fs::remove_file(proj.join("lake-manifest.json"))?;

        // 2. Corrupt `lakefile.toml` must fail closed (`Err`).
        fs::write(proj.join("lakefile.toml"), "name = [unterminated\n")?;
        let err_lakefile = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("corrupt lakefile.toml must fail closed");
        assert!(
            format!("{err_lakefile:#}").contains("lakefile.toml"),
            "unexpected lakefile error: {err_lakefile:#}"
        );
        fs::write(proj.join("lakefile.toml"), valid_lakefile)?;

        // 3. Missing toolchain with `TURBO_LEAN_STRICT_TOOLCHAIN=1` must fail closed (`Err`).
        struct StrictToolchainGuard(Option<std::ffi::OsString>);
        impl Drop for StrictToolchainGuard {
            fn drop(&mut self) {
                match &self.0 {
                    Some(v) => std::env::set_var("TURBO_LEAN_STRICT_TOOLCHAIN", v),
                    None => std::env::remove_var("TURBO_LEAN_STRICT_TOOLCHAIN"),
                }
            }
        }
        let _strict_tc_guard =
            StrictToolchainGuard(std::env::var_os("TURBO_LEAN_STRICT_TOOLCHAIN"));
        std::env::set_var("TURBO_LEAN_STRICT_TOOLCHAIN", "1");
        fs::write(
            proj.join("lean-toolchain"),
            "leanprover/lean4:v4.99.0-nonexistent-impact-test\n",
        )?;
        let err_tc = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("strict missing toolchain must fail closed");
        assert!(
            format!("{err_tc:#}").contains("fail-closed toolchain gate"),
            "unexpected strict toolchain error: {err_tc:#}"
        );
        drop(_strict_tc_guard);
        fs::write(proj.join("lean-toolchain"), tc)?;

        // 4. DAG construction errors (missing imported module & import cycle) must fail closed (`Err`).
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\nimport Smoke.DoesNotExistAnywhere\npublic theorem b_thm : 1 + 1 = 2 := a_thm\n",
        )?;
        let err_missing_imp = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("missing DAG import must fail closed");
        assert!(
            format!("{err_missing_imp:#}").contains("DoesNotExistAnywhere"),
            "unexpected missing import error: {err_missing_imp:#}"
        );

        fs::write(
            proj.join("Smoke/A.lean"),
            "module\nimport Smoke.B\npublic theorem a_thm : 1 + 1 = 2 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\nimport Smoke.A\npublic theorem b_thm : 1 + 1 = 2 := rfl\n",
        )?;
        let err_cycle = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("DAG import cycle must fail closed");
        assert!(
            format!("{err_cycle:#}").contains("cycle"),
            "unexpected cycle error: {err_cycle:#}"
        );
        fs::write(
            proj.join("Smoke/A.lean"),
            "module\npublic theorem a_thm : 1 + 1 = 2 := rfl\n",
        )?;
        fs::write(
            proj.join("Smoke/B.lean"),
            "module\npublic import Smoke.A\npublic theorem b_thm : 1 + 1 = 2 := a_thm\n",
        )?;

        // 5. Invalid standalone module header in project must fail closed (`Err`).
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"smoke\"\n[[lean_lib]]\nname = \"Smoke\"\nroots = [\"Smoke.A\", \"Smoke.B\"]\n",
        )?;
        let bad_standalone = proj.join("StandaloneBad.lean");
        fs::write(&bad_standalone, "public import Smoke.A\n")?;
        let err_standalone = compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("HEAD".to_string()),
        )
        .expect_err("invalid standalone header must fail closed");
        assert!(
            format!("{err_standalone:#}").contains("StandaloneBad.lean"),
            "unexpected standalone error: {err_standalone:#}"
        );
        fs::remove_file(&bad_standalone)?;
        fs::write(proj.join("lakefile.toml"), valid_lakefile)?;

        // 6. Invalid explicit `--rev` (nonexistent ref, flag-like ref, or outside a git repo) must fail closed (`Err`).
        compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("refs/heads/definitely-does-not-exist-impact".to_string()),
        )
        .expect_err("nonexistent explicit --rev must fail closed");
        compute_impact_report(
            proj.join("Smoke/A.lean"),
            Some(proj.clone()),
            Some("--invalid-flag-rev".to_string()),
        )
        .expect_err("flag-like explicit --rev must fail closed");
        compute_impact_report(solo_file, None, Some("HEAD".to_string()))
            .expect_err("explicit --rev outside git repo must fail closed");
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_worktree_auto_link_disabled_invalidates_negative_memo_when_toml_created() -> Result<()>
    {
        let tmp_dir = std::env::temp_dir().join(format!(
            "turbo_wt_neg_memo_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos()
        ));
        let proj = tmp_dir.join("sub/proj");
        fs::create_dir_all(&proj)?;
        assert!(
            !worktree_auto_link_disabled(&proj),
            "default without turbo-lean.toml must allow worktree auto-link"
        );
        fs::write(
            tmp_dir.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        assert!(
            worktree_auto_link_disabled(&proj),
            "creating ancestor turbo-lean.toml within same memo window must invalidate negative lookup"
        );
        fs::write(
            tmp_dir.join("turbo-lean.toml"),
            "[worktree]\nauto_link = true\n",
        )?;
        assert!(
            !worktree_auto_link_disabled(&proj),
            "updating ancestor turbo-lean.toml to auto_link = true must re-enable auto-link"
        );
        fs::write(
            tmp_dir.join("sub/turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        assert!(
            worktree_auto_link_disabled(&proj),
            "creating closer intermediate sub/turbo-lean.toml must override outer turbo-lean.toml within same memo window"
        );
        let _ = fs::remove_file(tmp_dir.join("sub/turbo-lean.toml"));
        assert!(
            !worktree_auto_link_disabled(&proj),
            "removing closer sub/turbo-lean.toml must fall back to outer turbo-lean.toml immediately"
        );
        let _ = fs::remove_dir_all(&tmp_dir);
        Ok(())
    }

    #[test]
    fn test_ensure_project_imports_fresh_accepts_git_pinned_implemented_by_and_custom_target_dep(
    ) -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "tl_fresh_git_pinned_dep_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let proj = dir.join("proj");
        let ext_pkgs = dir.join("shared_pkgs");
        let bat_dir = ext_pkgs.join("batteries");
        let pw_dir = ext_pkgs.join("proofwidgets");
        fs::create_dir_all(proj.join("Verity"))?;
        fs::create_dir_all(proj.join(".lake"))?;
        fs::create_dir_all(bat_dir.join("Batteries"))?;
        fs::create_dir_all(pw_dir.join("ProofWidgets"))?;
        fs::create_dir_all(pw_dir.join("widget/js"))?;

        let tc = std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean/lean-toolchain"),
        )?;
        fs::write(proj.join("lean-toolchain"), &tc)?;
        fs::write(bat_dir.join("lean-toolchain"), &tc)?;
        fs::write(pw_dir.join("lean-toolchain"), &tc)?;

        fs::write(bat_dir.join(".gitignore"), "/.lake/\n")?;
        fs::write(
            bat_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage batteries where\n@[default_target]\nlean_lib Batteries where\n",
        )?;
        fs::write(
            bat_dir.join("Batteries/Fast.lean"),
            "unsafe def scanFast (n : Nat) : Nat := n\n@[implemented_by scanFast]\ndef scanSpec (n : Nat) : Nat := n\n@[csimp]\ntheorem scan_eq : @scanSpec = @scanSpec := rfl\n",
        )?;
        fs::write(bat_dir.join("Batteries.lean"), "import Batteries.Fast\n")?;

        fs::write(pw_dir.join(".gitignore"), "/.lake/\n")?;
        fs::write(
            pw_dir.join("widget/js/ofRpcMethod.js"),
            "export default {}\n",
        )?;
        fs::write(
            pw_dir.join("lakefile.lean"),
            "import Lake\nopen Lake DSL System\npackage proofwidgets where\ndef widgetDir : FilePath := \"widget\"\ninput_dir widgetJsAllTs where\n  path := widgetDir / \"js\"\n  filter := .extension <| .mem #[\"ts\", \"tsx\", \"js\"]\ntarget widgetJsAll pkg : Unit := do\n  return .nil\n@[default_target]\nlean_lib ProofWidgets where\n  needs := #[widgetJsAll, widgetJsAllTs]\n",
        )?;
        fs::write(
            pw_dir.join("ProofWidgets/OfRpc.lean"),
            "def rpcJs : String := include_str \"..\" / \"widget\" / \"js\" / \"ofRpcMethod.js\"\n",
        )?;
        fs::write(
            pw_dir.join("ProofWidgets.lean"),
            "import ProofWidgets.OfRpc\n",
        )?;

        let init_commit = |repo: &Path| -> Result<String> {
            assert!(crate::trusted_tools::git(repo)?
                .args(["init", "-q"])
                .arg(repo)
                .status()?
                .success());
            assert!(crate::trusted_tools::git(repo)?
                .arg("-C")
                .arg(repo)
                .args(["add", "."])
                .status()?
                .success());
            assert!(crate::trusted_tools::git(repo)?
                .arg("-C")
                .arg(repo)
                .args([
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
            Ok(String::from_utf8(
                crate::trusted_tools::git(repo)?
                    .arg("-C")
                    .arg(repo)
                    .args(["rev-parse", "HEAD"])
                    .output()?
                    .stdout,
            )?
            .trim()
            .to_string())
        };
        let bat_rev = init_commit(&bat_dir)?;
        let pw_rev = init_commit(&pw_dir)?;

        #[cfg(unix)]
        std::os::unix::fs::symlink(&ext_pkgs, proj.join(".lake/packages"))?;

        fs::write(
            proj.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\npackage verity where\nrequire batteries from \".lake/packages/batteries\"\nrequire proofwidgets from \".lake/packages/proofwidgets\"\n@[default_target]\nlean_lib Verity where\n",
        )?;
        fs::write(
            proj.join("lake-manifest.json"),
            serde_json::to_string_pretty(&serde_json::json!({
                "version": "1.1.0",
                "packagesDir": ".lake/packages",
                "packages": [
                    {
                        "type": "git",
                        "name": "batteries",
                        "rev": bat_rev,
                        "url": "https://example.invalid/batteries",
                        "inherited": false,
                        "configFile": "lakefile.lean"
                    },
                    {
                        "type": "git",
                        "name": "proofwidgets",
                        "rev": pw_rev,
                        "url": "https://example.invalid/proofwidgets",
                        "inherited": false,
                        "configFile": "lakefile.lean"
                    }
                ]
            }))?,
        )?;
        let target_file = proj.join("Verity/Target.lean");
        fs::write(
            &target_file,
            "import Batteries\nimport ProofWidgets\ntheorem ok : scanSpec 3 = 3 := rfl\n",
        )?;
        fs::write(proj.join("Verity.lean"), "import Verity.Target\n")?;

        let canon = fs::canonicalize(&proj)?;
        crate::module_builder::reset_lake_inputs_tag_memo();
        let rebuilt = ensure_project_imports_fresh(
            &canon,
            std::slice::from_ref(&target_file),
            Some(tc.trim()),
            true,
        )?;
        assert!(
            rebuilt >= 1,
            "first call must Lake-build missing dep imports"
        );
        // Second call must hit 0 stale imports without re-invoking Lake!
        let rebuilt2 = ensure_project_imports_fresh(
            &canon,
            std::slice::from_ref(&target_file),
            Some(tc.trim()),
            true,
        )?;
        assert_eq!(
            rebuilt2, 0,
            "Lake-built git-pinned @[implemented_by]/@[csimp] + custom-target-needs deps must verify fresh"
        );
        let mut store = crate::TurboStore::open(Some(&dir.join("store")))?;
        let build_rep = crate::module_builder::build_project_modules_native(
            &mut store,
            &canon,
            &[],
            "trusted",
            2,
            false,
            true,
            None,
        )?;
        assert_eq!(
            build_rep.modules_compiled, 2,
            "turbo-lean build must reuse prebuilt ProofWidgets & Batteries oleans and compile only Verity.Target + Verity"
        );

        crate::zygote::purge_snapshot_dir(&dir);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_s2_lake_build_public_api_surface_pinned() {
        let _ = std::mem::size_of::<crate::lake_build::StandaloneOleanOverlay>();
        let _ = std::mem::size_of::<crate::lake_build::ImpactReport>();
        let _ = std::mem::size_of::<crate::lake_build::OleanInterfaceBatchSession>();
        let _ = std::mem::size_of::<crate::lake_build::ShmCachedFileSplit>();
        let _ = std::mem::size_of::<crate::lake_build::ShmProjectStatSummary>();
        let _ = std::mem::size_of::<crate::StandaloneOleanOverlay>();
        let _ = std::mem::size_of::<crate::ImpactReport>();

        let _ = crate::lake_build::compute_imported_olean_interface_hashes
            as fn(&str, &Path, Option<&str>) -> Vec<String>;
        let _ = crate::lake_build::compute_impact_report
            as fn(PathBuf, Option<PathBuf>, Option<String>) -> Result<ImpactReport>;
        let _ = crate::lake_build::run_impact_command
            as fn(bool, PathBuf, Option<PathBuf>, Option<String>) -> Result<()>;
        let _ = crate::lake_build::dedup_worktree_packages
            as fn(&TurboStore, &Path) -> Result<serde_json::Value>;
        let _ = crate::lake_build::run_build_command
            as fn(&mut TurboStore, bool, Vec<String>, PathBuf, String, i64, bool) -> Result<()>;
        let _ = crate::lake_build::validate_lnir_expr_v1_blob as fn(&[u8]) -> bool;
        let _ = crate::lake_build::replay_project_cas_expr_shards
            as fn(&mut TurboStore, &Path, &str, &str, Option<&[PathBuf]>) -> Result<usize>;
        let _ = crate::lake_build::run_build_command_with_cas_replay
            as fn(&mut TurboStore, bool, Vec<String>, PathBuf, String, i64, bool, bool) -> Result<()>;
        let _ = crate::lake_build::run_hydrate_traces_command as fn(bool, PathBuf) -> Result<()>;
        assert!(!crate::validate_lnir_expr_v1_blob(b""));
    }

    #[test]
    fn test_p9_freshness_preflight_fails_closed_on_uncovered_project_owned_csimp(
    ) -> Result<()> {
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        struct RestoreEnv(&'static str, Option<std::ffi::OsString>);
        impl Drop for RestoreEnv {
            fn drop(&mut self) {
                match self.1 {
                    Some(ref v) => std::env::set_var(self.0, v),
                    None => std::env::remove_var(self.0),
                }
            }
        }
        let key = "TURBO_LEAN_ALLOWED_CSIMP";
        let restore = RestoreEnv(key, std::env::var_os(key));

        let dir = std::env::temp_dir().join(format!(
            "tl_p9_fail_closed_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let proj = dir.join("proj");
        fs::create_dir_all(&proj)?;
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"p9-fixture\"\ndefaultTargets = [\"Main\"]\n[[lean_lib]]\nname = \"Main\"\n",
        )?;
        fs::write(
            proj.join("Main.lean"),
            "def slow (n : Nat) : Nat := n + 1\ndef fast (n : Nat) : Nat := n.succ\n@[csimp] theorem slow_eq_fast : @slow = @fast := rfl\n",
        )?;
        let canon = fs::canonicalize(&proj)?;
        let target = canon.join("Main.lean");
        crate::module_builder::reset_lake_inputs_tag_memo();

        // Empty policy: the project-owned `@[csimp]` theorem fails closed before expensive work
        // (before any Lake invocation or olean manifest read), with the actionable fix named.
        std::env::remove_var(key);
        let err = ensure_project_imports_fresh(
            &canon,
            std::slice::from_ref(&target),
            Some("leanprover/lean4:v4.35.0"),
            true,
        )
        .expect_err("uncovered project-owned csimp entry must fail closed before expensive work");
        let msg = format!("{err:#}");
        assert!(
            msg.contains("slow_eq_fast") && msg.contains("[csimp] allow"),
            "actionable error must name the theorem and the fix: {msg}"
        );
        assert!(
            !proj.join(".lake/build").exists(),
            "preflight must decide before any Lake build work"
        );

        // Covered policy: the same gate passes and the no-import gate short-circuits cleanly.
        std::env::set_var(key, "slow_eq_fast");
        crate::module_builder::reset_lake_inputs_tag_memo();
        ensure_project_imports_fresh(
            &canon,
            std::slice::from_ref(&target),
            Some("leanprover/lean4:v4.35.0"),
            true,
        )?;

        // Wildcard policy also covers the owned entry.
        std::env::set_var(key, "*");
        crate::module_builder::reset_lake_inputs_tag_memo();
        ensure_project_imports_fresh(
            &canon,
            std::slice::from_ref(&target),
            Some("leanprover/lean4:v4.35.0"),
            true,
        )?;

        drop(restore);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_p9_preflight_zero_config_autoallows_dependency_package_csimp() -> Result<()> {
        // The CLI-side preflight (`AllDependencyPackages`, `apply_env = true`) must extend the
        // effective allowlist with `@[csimp]` theorems scraped from dependency sources, while a
        // project without dependency csimp leaves the env untouched.
        let _guard = crate::pack::tests::env_test_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        struct RestoreEnv(&'static str, Option<std::ffi::OsString>);
        impl Drop for RestoreEnv {
            fn drop(&mut self) {
                match self.1 {
                    Some(ref v) => std::env::set_var(self.0, v),
                    None => std::env::remove_var(self.0),
                }
            }
        }
        let key = "TURBO_LEAN_ALLOWED_CSIMP";
        let restore = RestoreEnv(key, std::env::var_os(key));

        let dir = std::env::temp_dir().join(format!(
            "tl_p9_autoallow_{}_{}",
            std::process::id(),
            pack::next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let proj = dir.join("proj");
        let bat_dir = proj.join(".lake/packages/batteries");
        fs::create_dir_all(bat_dir.join("Batteries"))?;
        fs::write(proj.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(bat_dir.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
        fs::write(
            proj.join("lakefile.toml"),
            "name = \"p9-auto\"\ndefaultTargets = [\"Main\"]\n[[lean_lib]]\nname = \"Main\"\n",
        )?;
        fs::write(
            bat_dir.join("lakefile.toml"),
            "name = \"batteries\"\ndefaultTargets = [\"Batteries\"]\n[[lean_lib]]\nname = \"Batteries\"\n",
        )?;
        fs::write(
            bat_dir.join("Batteries/Fast.lean"),
            "@[csimp] theorem scan_eq : @slowSpec = @fastSpec := rfl\n",
        )?;
        fs::write(bat_dir.join("Batteries.lean"), "import Batteries.Fast\n")?;
        // Manual lake-manifest-style dep wiring via symlinked packages dir is what
        // `resolve_project_config` reads; a plain manifest entry suffices here.
        fs::write(
            proj.join("lake-manifest.json"),
            serde_json::to_string(&serde_json::json!({
                "version": "1.1.0",
                "packagesDir": ".lake/packages",
                "packages": [
                    {
                        "type": "path",
                        "name": "batteries",
                        "inherited": false,
                        "configFile": "lakefile.toml"
                    }
                ]
            }))?,
        )?;
        let canon = fs::canonicalize(&proj)?;
        crate::module_builder::reset_lake_inputs_tag_memo();

        std::env::set_var(key, "from_config");
        crate::lake_build::preflight_zero_config_csimp_import_policy(
            &canon,
            crate::lake_build::CsimpPreflightScope::AllDependencyPackages,
            true,
        )?;
        let extended = std::env::var(key).unwrap_or_default();
        assert!(
            extended.contains("scan_eq") && extended.contains("from_config"),
            "preflight must merge configured policy with scraped dependency csimp entries: {extended}"
        );
        let parts: Vec<&str> = extended.split(',').collect();
        assert_eq!(
            parts,
            ["from_config", "scan_eq"],
            "effective allowlist must be sorted and de-duplicated: {extended}"
        );

        // Read-only mode never mutates the env.
        std::env::set_var(key, "from_config");
        crate::lake_build::preflight_zero_config_csimp_import_policy(
            &canon,
            crate::lake_build::CsimpPreflightScope::AllDependencyPackages,
            false,
        )?;
        assert_eq!(
            std::env::var(key).unwrap_or_default(),
            "from_config",
            "apply_env = false must leave the environment untouched"
        );

        drop(restore);
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }
