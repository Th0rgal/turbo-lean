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
    fs::write(path, content).unwrap();
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
    write_executable(&helper, &script);

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
