#![cfg(unix)]

use serde_json::Value;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static TEST_SEQ: AtomicU64 = AtomicU64::new(1);

fn temp_test_dir(label: &str) -> PathBuf {
    let seq = TEST_SEQ.fetch_add(1, Ordering::Relaxed);
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "turbo_superopt_evolve_cli_{}_{}_{}_{}",
        label,
        std::process::id(),
        nanos,
        seq
    ));
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn write_executable(path: &Path, content: &str) {
    fs::write(
        path,
        content.replacen(
            "#!/bin/sh\n",
            "#!/bin/sh\nif [ \"$2\" = \"--verify-bundle\" ]; then exit 0; fi\n",
            1,
        ),
    )
    .unwrap();
    let mut perms = fs::metadata(path).unwrap().permissions();
    perms.set_mode(0o755);
    fs::set_permissions(path, perms).unwrap();
}

fn run_turbo(cache_dir: &Path, helper_bin: &Path, args: &[&str]) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
    cmd.env("TURBO_LEAN_TELEMETRY", "off")
        .env("TURBO_LEAN_NO_DAEMON", "1")
        .env("LEAN_NATIVE_CORE_BIN", helper_bin)
        .arg("--no-daemon")
        .arg("--no-telemetry")
        .arg("--cache-dir")
        .arg(cache_dir)
        .args(args);
    cmd.output().unwrap()
}

#[test]
fn cli_superopt_evolve_forwards_flags_and_exports_importable_tlpack() {
    let root = temp_test_dir("pack_import");
    let cache_src = root.join("cache_src");
    let cache_dst = root.join("cache_dst");
    let args_log = root.join("helper_args.txt");
    let helper = root.join("mock-lean-native-core");

    let script = format!(
        "#!/bin/sh\nprintf '%s\\n' \"$@\" > \"{}\"\nbundle=\"\"\nprev=\"\"\nfor a in \"$@\"; do\n  if [ \"$prev\" = \"--bundle-out\" ]; then bundle=\"$a\"; fi\n  prev=\"$a\"\ndone\nif [ -n \"$bundle\" ]; then\n  printf '{{\"schema\":\"lean-native.superopt-evolve.v1\",\"target\":\"cuda_ptx\",\"certificates\":[{{\"rule\":\"shl_zero\",\"sound\":true}}]}}' > \"$bundle\"\nfi\nprintf '{{\"status\":\"evolved\",\"target\":\"cuda_ptx\",\"generations\":6,\"seed\":99,\"acceptedRules\":1}}\\n'\n",
        args_log.display()
    );
    write_executable(
        &helper,
        &script.replace(
            r#"{"schema":"lean-native.superopt-evolve.v1","target":"cuda_ptx","certificates":[{"rule":"shl_zero","sound":true}]}"#,
            include_str!("fixtures/empty_stochastic_bundle.json").trim(),
        ),
    );

    let bundle_out = root.join("out").join("cert_bundle.json");
    let pack_out = root.join("out").join("cert_bundle.tlpack");

    let out = run_turbo(
        &cache_src,
        &helper,
        &[
            "--json",
            "superopt-evolve",
            "--target",
            "cuda_ptx",
            "--generations",
            "6",
            "--seed",
            "99",
            "--bundle-out",
            bundle_out.to_str().unwrap(),
            "--pack-out",
            pack_out.to_str().unwrap(),
        ],
    );
    assert!(
        out.status.success(),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let parsed: Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(parsed["status"], "evolved");
    assert_eq!(parsed["acceptedRules"], 1);
    assert_eq!(parsed["bundle_out"], bundle_out.display().to_string());
    assert_eq!(parsed["pack_out"], pack_out.display().to_string());
    assert_eq!(parsed["pack_export"]["exported_actions"], 1);
    assert_eq!(parsed["pack_export"]["exported_blobs"], 1);

    let forwarded: Vec<String> = fs::read_to_string(&args_log)
        .unwrap()
        .lines()
        .map(ToOwned::to_owned)
        .collect();
    assert_eq!(
        forwarded,
        vec![
            "superopt-evolve",
            "--target",
            "cuda_ptx",
            "--generations",
            "6",
            "--seed",
            "99",
            "--bundle-out",
            bundle_out.to_str().unwrap(),
            "--input",
            "canonical",
            "--json",
        ]
    );

    assert!(bundle_out.is_file());
    assert!(pack_out.is_file());

    let import_out = run_turbo(
        &cache_dst,
        &helper,
        &[
            "--json",
            "import",
            pack_out.to_str().unwrap(),
            "--trust-domain",
            "trusted",
            "--allow-unattested-trusted",
        ],
    );
    assert!(
        import_out.status.success(),
        "import stdout: {}\nimport stderr: {}",
        String::from_utf8_lossy(&import_out.stdout),
        String::from_utf8_lossy(&import_out.stderr)
    );
    let import_json: Value = serde_json::from_slice(&import_out.stdout).unwrap();
    assert_eq!(import_json["imported_actions"], 1);
    assert_eq!(import_json["imported_blobs"], 1);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn cli_superopt_evolve_rejects_invalid_target_and_propagates_helper_failure() {
    let root = temp_test_dir("errors");
    let cache_dir = root.join("cache");
    let helper = root.join("mock-lean-native-core");
    write_executable(
        &helper,
        "#!/bin/sh\nprintf 'simulated evolution failure\\n' >&2\nexit 7\n",
    );

    let bad_target = run_turbo(
        &cache_dir,
        &helper,
        &["superopt-evolve", "--target", "sparc64"],
    );
    assert!(!bad_target.status.success());
    let bad_stderr = String::from_utf8_lossy(&bad_target.stderr);
    assert!(bad_stderr.contains("Unsupported superopt-evolve target"));

    let helper_fail = run_turbo(
        &cache_dir,
        &helper,
        &[
            "superopt-evolve",
            "--target",
            "apple_metal",
            "--input",
            "custom.lnir",
        ],
    );
    assert!(!helper_fail.status.success());
    let fail_stderr = String::from_utf8_lossy(&helper_fail.stderr);
    assert!(fail_stderr.contains("simulated evolution failure"));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn pack_export_rejects_missing_bundle_and_report_schema() {
    let root = temp_test_dir("missing_bundle");
    let helper = root.join("helper");
    let bundle = root.join("bundle.json");
    let pack = root.join("bundle.tlpack");
    write_executable(&helper, "#!/bin/sh\nprintf '{\"status\":\"evolved\"}'\n");
    let good: Value =
        serde_json::from_str(include_str!("fixtures/empty_stochastic_bundle.json")).unwrap();
    let mut malformed = good.clone();
    malformed["certificates"] = serde_json::json!([{}]);
    let mut corrupt_wire = good.clone();
    corrupt_wire["certificates"] = serde_json::json!([{
        "theoremRef": "test", "costBefore": 2, "costAfter": 1,
        "candidate": {"lhs": "LNIR_WIRE_V1|malformed", "rhs": "LNIR_WIRE_V1|garbage"}
    }]);
    let mut non_improving = good;
    non_improving["certificates"] = serde_json::json!([{
        "theoremRef": "test", "costBefore": 1, "costAfter": 1,
        "candidate": {"lhs": "LNIR_WIRE_V1|", "rhs": "LNIR_WIRE_V1|"}
    }]);
    for payload in [
        None,
        Some(serde_json::json!({"schema":"lean-native.superopt-evolve-receipt.v1"})),
        Some(serde_json::json!({"schema":"lean-native.stochastic-cert.v1"})),
        Some(malformed),
        Some(non_improving),
        Some(corrupt_wire),
    ] {
        if let Some(payload) = payload {
            fs::write(&bundle, serde_json::to_vec(&payload).unwrap()).unwrap();
        }
        let out = run_turbo(
            &root.join("cache"),
            &helper,
            &[
                "superopt-evolve",
                "--bundle-out",
                bundle.to_str().unwrap(),
                "--pack-out",
                pack.to_str().unwrap(),
            ],
        );
        assert!(!out.status.success());
        assert!(!pack.exists());
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn real_bundle_json_raw_and_zstd_pack_consumption_and_rejection() {
    let root = temp_test_dir("real_bundle");
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let core = repo.join("lean/.lake/build/bin/lean-native-core");
    assert!(
        core.is_file(),
        "Build lean-native-core before running integration tests"
    );
    let bundle = root.join("bundle.json");
    let pack = root.join("bundle.tlpack");
    let out = run_turbo(
        &root.join("cache"),
        &core,
        &[
            "--json",
            "superopt-evolve",
            "--bundle-out",
            bundle.to_str().unwrap(),
            "--pack-out",
            pack.to_str().unwrap(),
        ],
    );
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let compressed = root.join("bundle.tlpack.zst");
    assert!(Command::new("zstd")
        .args(["-q", "-o"])
        .arg(&compressed)
        .arg(&pack)
        .status()
        .unwrap()
        .success());
    for path in [&bundle, &pack, &compressed] {
        for command in ["compile-llvm", "verify-certs"] {
            let mut cmd = Command::new(&core);
            cmd.args([command, "--canonical", "--stochastic-bundle"])
                .arg(path);
            if command == "verify-certs" {
                cmd.args(["--verified-kernel-only", "--json"]);
            }
            let out = cmd.output().unwrap();
            assert!(
                out.status.success(),
                "{}: {}",
                path.display(),
                String::from_utf8_lossy(&out.stderr)
            );
            if command == "verify-certs" {
                let report: Value = serde_json::from_slice(&out.stdout).unwrap();
                assert_eq!(report["verified"], true);
                assert_eq!(report["overallAssurance"], "VerifiedKernelProof");
            }
        }
    }
    let good: Value = serde_json::from_slice(&fs::read(&bundle).unwrap()).unwrap();
    // Same-size valid JSON mutation: only the manifest digest changes.
    let mut corrupted = fs::read(&pack).unwrap();
    let header_len = u64::from_le_bytes(corrupted[8..16].try_into().unwrap()) as usize;
    let mut manifest: Value = serde_json::from_slice(&corrupted[16..16 + header_len]).unwrap();
    let hash = manifest["blobs"][0]["blob_hash"].as_str().unwrap();
    manifest["blobs"][0]["blob_hash"] = serde_json::json!(format!(
        "{}{}",
        if hash.starts_with('0') { "1" } else { "0" },
        &hash[1..]
    ));
    let header = serde_json::to_vec(&manifest).unwrap();
    assert_eq!(header.len(), header_len);
    corrupted[16..16 + header_len].copy_from_slice(&header);
    let corrupt_pack = root.join("corrupt.tlpack");
    let corrupt_zst = root.join("corrupt.tlpack.zst");
    fs::write(&corrupt_pack, &corrupted).unwrap();
    assert!(Command::new("zstd")
        .args(["-q", "-o"])
        .arg(&corrupt_zst)
        .arg(&corrupt_pack)
        .status()
        .unwrap()
        .success());
    for path in [&corrupt_pack, &corrupt_zst] {
        let out = Command::new(&core)
            .args(["verify-certs", "--canonical", "--stochastic-bundle"])
            .arg(path)
            .output()
            .unwrap();
        assert!(
            !out.status.success(),
            "accepted tampered pack {}",
            path.display()
        );
    }
    assert!(!good["certificates"].as_array().unwrap().is_empty());
    let mut bad_cost = good.clone();
    bad_cost["certificates"][0]["costAfter"] = serde_json::json!(999999);
    let mut bad_theorem = good.clone();
    bad_theorem["certificates"][0]["theoremRef"] = serde_json::json!("forged");
    let mut unsound = good.clone();
    unsound["certificates"][0]["candidate"]["rhs"] =
        good["certificates"][0]["candidate"]["lhs"].clone();
    let mut add_one = good.clone();
    let mut malformed_wire = good.clone();
    malformed_wire["certificates"][0]["candidate"]["lhs"] =
        serde_json::json!("LNIR_WIRE_V1|malformed");
    let scalar_wire = good["certificates"][0]["candidate"]["lhs"]
        .as_str()
        .unwrap();
    let scalar_start = scalar_wire.find("S_").unwrap();
    let scalar_end = scalar_wire.rfind("|C_ret").unwrap();
    let wire = |expr: &str| {
        format!(
            "{}{}{}",
            &scalar_wire[..scalar_start],
            expr,
            &scalar_wire[scalar_end..]
        )
    };
    add_one["certificates"][0]["candidate"]["lhs"] =
        serde_json::json!(wire("S_bin|B_add|S_var|0|S_u64|1"));
    add_one["certificates"][0]["candidate"]["rhs"] = serde_json::json!(wire("S_var|0"));
    add_one["certificates"][0]["costBefore"] = serde_json::json!(1);
    add_one["certificates"][0]["costAfter"] = serde_json::json!(0);
    let cases = [
        b"not JSON".to_vec(),
        b"TLPK\0\0\0\x02".to_vec(),
        br#"{"schema":"lean-native.superopt-evolve-receipt.v1"}"#.to_vec(),
        serde_json::to_vec(&bad_cost).unwrap(),
        serde_json::to_vec(&bad_theorem).unwrap(),
        serde_json::to_vec(&unsound).unwrap(),
        serde_json::to_vec(&add_one).unwrap(),
        serde_json::to_vec(&malformed_wire).unwrap(),
    ];
    let invalid = root.join("invalid");
    for data in std::iter::once(None).chain(cases.iter().map(Some)) {
        if let Some(data) = data {
            fs::write(&invalid, data).unwrap();
        }
        let verified = Command::new(&core)
            .args(["superopt-evolve", "--verify-bundle"])
            .arg(&invalid)
            .output()
            .unwrap();
        assert!(
            !verified.status.success(),
            "verifier accepted invalid bundle"
        );
        for command in ["compile-llvm", "verify-certs"] {
            let out = Command::new(&core)
                .args([command, "--canonical", "--stochastic-bundle"])
                .arg(&invalid)
                .output()
                .unwrap();
            assert!(!out.status.success(), "accepted invalid bundle");
        }
    }
    // A producer may report success while leaving a forged bundle. Delegate
    // verification to the real Lean core and ensure publication never occurs.
    let producer = root.join("forged-producer");
    fs::write(&producer, format!(
        "#!/bin/sh\nif [ \"$2\" = \"--verify-bundle\" ]; then exec '{}' \"$@\"; fi\nprintf '{{}}'\n",
        core.display()
    )).unwrap();
    fs::set_permissions(&producer, fs::Permissions::from_mode(0o755)).unwrap();
    let rejected_pack = root.join("rejected.tlpack");
    for payload in [&add_one, &malformed_wire] {
        fs::write(&invalid, serde_json::to_vec(payload).unwrap()).unwrap();
        let out = run_turbo(
            &root.join("rejected-cache"),
            &producer,
            &[
                "superopt-evolve",
                "--bundle-out",
                invalid.to_str().unwrap(),
                "--pack-out",
                rejected_pack.to_str().unwrap(),
            ],
        );
        assert!(!out.status.success());
        assert!(!rejected_pack.exists());
    }
    fs::remove_dir_all(root).unwrap();
}
