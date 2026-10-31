use std::{
    fs,
    path::Path,
    process::{Command, Output},
};
#[path = "support/lean_options.rs"]
mod cases;
use cases::*;

fn turbo(project: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_turbo-lean"))
        .args(["--json", "--cache-dir"])
        .arg(project.join("cache"))
        .args(args)
        .args(["--project-dir"])
        .arg(project)
        .env("TURBO_LEAN_NO_DAEMON", "1")
        .env("LEAN_NUM_THREADS", "4")
        .output()
        .unwrap()
}
fn output(out: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}
fn rejected(out: Output, key: &str) {
    let text = output(&out);
    assert!(!out.status.success(), "accepted {key}: {text}");
    assert!(text.contains(key), "missing option {key}: {text}");
    assert!(
        !text.contains("PR-VERIFY PASSED") && !text.contains("\"verified\":true"),
        "{text}"
    );
}

#[test]
fn real_binary_rejects_weakening_options_and_kernel_bypass_fixture() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/weakening-options");
    let project = std::env::temp_dir().join(format!("turbo_option_policy_{}", std::process::id()));
    fs::create_dir_all(&project).unwrap();
    for name in ["lean-toolchain", "Bad.lean", "lakefile.lean"] {
        fs::copy(fixture.join(name), project.join(name)).unwrap();
    }
    fs::write(project.join("Main.lean"), "def main : IO Unit := pure ()\n").unwrap();

    // Prove the fixture hits the actual kernel-check bypass, with no sorry/axiom escape.
    let source = fs::read_to_string(project.join("Bad.lean")).unwrap();
    assert!(!source.contains("sorry") && !source.contains("axiom "));
    let lean = |args: &[&str]| {
        Command::new("lean")
            .args(args)
            .arg("Bad.lean")
            .current_dir(&project)
            .env("LEAN_NUM_THREADS", "4")
            .output()
            .unwrap()
    };
    let checked = lean(&[]);
    assert!(!checked.status.success(), "{}", output(&checked));
    assert!(output(&checked).contains("kernel"), "{}", output(&checked));
    let skipped = lean(&["-Ddebug.skipKernelTC=true"]);
    assert!(skipped.status.success(), "{}", output(&skipped));
    assert!(
        output(&skipped).contains("does not depend on any axioms"),
        "{}",
        output(&skipped)
    );

    rejected(turbo(&project, &["build"]), "debug.skipKernelTC");
    fs::write(
        project.join("Bad.lean"),
        "theorem good : True := True.intro\n",
    )
    .unwrap();
    let mut accepted = 0;
    let mut denied = 0;
    // Every original option case and the old pp/async cases reach the binary.
    for format in ["lean", "toml"] {
        let _ = fs::remove_file(project.join("lakefile.lean"));
        let _ = fs::remove_file(project.join("lakefile.toml"));
        for &(name, value) in ORIGINAL_OPTIONS.iter().chain(RESTRICTED_OPTIONS) {
            for prefix in PREFIXES {
                let key = format!("{prefix}{name}");
                for scope in SCOPES {
                    for field in FIELDS {
                        fs::write(
                            project.join(format!("lakefile.{format}")),
                            lakefile(format, scope, field, &key, value),
                        )
                        .unwrap();
                        let out = turbo(&project, &["build"]);
                        if original_case_allowed(name, value, prefix) {
                            assert!(out.status.success(), "{}", output(&out));
                            accepted += 1;
                        } else {
                            rejected(out, &key);
                            denied += 1;
                        }
                    }
                }
                // The CLI has no Lean flag passthrough: unsupported -D arguments fail closed.
                assert!(!turbo(&project, &["build", &format!("-D{key}={value}")])
                    .status
                    .success());
            }
        }
    }

    assert_eq!((accepted, denied), (36, 1044));
    println!("Lake/CLI matrix: 864 original configurations + 216 pp/async regressions; 36 safe accepted, 1044 denied");

    // A valid project with real options must still build through the same binary.
    fs::remove_file(project.join("lakefile.toml")).unwrap();
    fs::write(
        project.join("Bad.lean"),
        "theorem good : True := True.intro\n",
    )
    .unwrap();
    let options: String = GOOD_OPTIONS
        .iter()
        .map(|(k, v)| format!("⟨`{k}, {v}⟩"))
        .collect::<Vec<_>>()
        .join(", ");
    fs::write(project.join("lakefile.lean"), format!("import Lake\nopen Lake DSL\npackage fixture where\n  leanOptions := #[{options}]\n@[default_target]\nlean_lib Bad\n")).unwrap();
    let built = turbo(&project, &["build"]);
    assert!(built.status.success(), "{}", output(&built));
    fs::remove_dir_all(project).unwrap();
}

#[test]
fn verification_entrypoints_reject_options_on_unchanged_projects() {
    let project = std::env::temp_dir().join(format!("turbo_option_verify_{}", std::process::id()));
    fs::create_dir_all(&project).unwrap();
    fs::write(project.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n").unwrap();
    fs::write(
        project.join("Bad.lean"),
        "theorem good : True := True.intro\n",
    )
    .unwrap();
    fs::write(
        project.join("lakefile.lean"),
        lakefile(
            "lean",
            "package",
            "leanOptions",
            "debug.skipKernelTC",
            "true",
        ),
    )
    .unwrap();
    assert!(Command::new("git")
        .args(["init", "-q"])
        .current_dir(&project)
        .status()
        .unwrap()
        .success());
    assert!(Command::new("git")
        .args(["add", "."])
        .current_dir(&project)
        .status()
        .unwrap()
        .success());
    assert!(Command::new("git")
        .args([
            "-c",
            "user.name=Option Policy Fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-qm",
            "fixture"
        ])
        .current_dir(&project)
        .status()
        .unwrap()
        .success());
    // Both verification entrypoints must reject the option before sandbox/kernel execution.
    for mode in ["trusted", "untrusted"] {
        for args in [
            vec!["ci-verify", "--mode", mode],
            vec!["pr-verify", "--mode", mode, "--base", "HEAD"],
        ] {
            let out = turbo(&project, &args);
            if mode == "untrusted" && output(&out).contains("working bubblewrap") {
                assert!(!out.status.success(), "{}", output(&out));
            } else {
                rejected(out, "debug.skipKernelTC");
            }
        }
    }

    fs::remove_dir_all(project).unwrap();
}

struct Server(std::process::Child);
impl Drop for Server {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

#[test]
fn http_lean_args_fail_closed_on_every_endpoint() {
    use std::{
        net::TcpListener,
        time::{Duration, Instant},
    };
    let dir = std::env::temp_dir().join(format!("turbo_option_http_{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();
    drop(listener);
    let server = Server(
        Command::new(env!("CARGO_BIN_EXE_turbo-lean"))
            .arg("--cache-dir")
            .arg(&dir)
            .args([
                "serve",
                "--listen",
                &addr.to_string(),
                "--api-token",
                "option-test",
            ])
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .unwrap(),
    );
    let agent = ureq::AgentBuilder::new()
        .timeout(Duration::from_secs(180))
        .build();
    let started = Instant::now();
    while std::net::TcpStream::connect(addr).is_err() {
        assert!(
            started.elapsed() < Duration::from_secs(10),
            "server did not start"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    for endpoint in ["check-shard", "check-shards-batch", "eval"] {
        let request = serde_json::json!({
            "source": "theorem good : True := True.intro", "shard_source": "theorem good : True := True.intro",
            "coalesced_shard_source": "theorem good : True := True.intro", "decl": "good", "shard_key": "option-test",
            "items": [{"decl_name": "good", "shard_key": "option-test"}], "lean_args": ["-DmaxHeartbeats=400000"]
        });
        let response = agent
            .post(&format!("http://{addr}/{endpoint}"))
            .set("X-Turbo-Token", "option-test")
            .set("Content-Type", "application/json")
            .send_string(&request.to_string())
            .unwrap()
            .into_string()
            .unwrap();
        let reply: serde_json::Value = serde_json::from_str(&response).unwrap();
        assert!(
            reply["ok"] == true || reply["status"] == "remote_theorem_verified",
            "{endpoint}: {response}"
        );
        if endpoint == "check-shards-batch" {
            assert_eq!(reply["cache_hits"], 1, "{response}");
        }
    }
    let mut failures = Vec::new();
    for &(name, value) in ORIGINAL_OPTIONS.iter().chain(RESTRICTED_OPTIONS) {
        for prefix in PREFIXES {
            if original_case_allowed(name, value, prefix) {
                continue;
            }
            let arg = format!("-D{prefix}{name}={value}");
            for endpoint in ["eval", "check-shard", "check-shards-batch"] {
                let request = serde_json::json!({
                    "source": "theorem good : True := True.intro", "shard_source": "theorem good : True := True.intro",
                    "coalesced_shard_source": "theorem good : True := True.intro", "decl": "good", "shard_key": "option-test",
                    "items": [{"decl_name": "good", "shard_key": "option-test"}], "lean_args": [arg], "timeout_ms": 30000
                });
                let result = agent
                    .post(&format!("http://{addr}/{endpoint}"))
                    .set("X-Turbo-Token", "option-test")
                    .set("Content-Type", "application/json")
                    .send_string(&request.to_string());
                let response = match result {
                    Ok(r) | Err(ureq::Error::Status(_, r)) => r,
                    Err(e) => panic!("{endpoint}: {e}"),
                };
                let text = response.into_string().unwrap();
                let reply: serde_json::Value = serde_json::from_str(&text).unwrap();
                if reply["ok"] == true
                    || reply["status"] == "remote_theorem_cache_hit"
                    || reply["status"] == "remote_theorem_verified"
                    || !text.contains(&arg)
                    || (reply["error"].is_null()
                        && reply["errors"].as_array().is_none_or(|e| e.is_empty()))
                {
                    failures.push(format!("{endpoint}/{arg}: {text}"));
                }
            }
        }
    }
    drop(server);
    fs::remove_dir_all(dir).unwrap();
    assert!(
        failures.is_empty(),
        "options were silently dropped: {}",
        failures.join("\n")
    );
}
