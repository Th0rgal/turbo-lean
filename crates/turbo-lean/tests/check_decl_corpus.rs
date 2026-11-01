#[path = "support/corpus.rs"]
mod corpus;
use std::{collections::BTreeSet, fs, process::Command};

/// Heavy A0d integration test, intentionally not #[ignore]: the existing cargo test --release
/// CI step runs every baseline and every mutant. No clifv checkout/build or network is needed.
#[test]
fn heavy_check_decl_corpus_stock_lean_verdict_parity() {
    let tmp = corpus::Temp::new("verdict");
    fs::write(
        tmp.0.join("lean-toolchain"),
        include_str!("../../../lean/lean-toolchain"),
    )
    .unwrap();
    fs::copy(
        corpus::fixtures().join("turbo-lean.toml"),
        tmp.0.join("turbo-lean.toml"),
    )
    .unwrap();
    fs::write(
        tmp.0.join("lakefile.toml"),
        "name = \"check-decl-corpus\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let mut declarations = 0;
    let mut comparisons = 0;
    for module in corpus::MODULES {
        let original =
            fs::read_to_string(corpus::fixtures().join(format!("{module}.lean"))).unwrap();
        let expected = corpus::oracle(&tmp.0, module, &original);
        let mut cases = Vec::new();
        let mut rest = original.as_str();
        while let Some((_, after)) = rest.split_once("-- CORPUS-PROOF ") {
            let (name, body) = after.split_once('\n').unwrap();
            let (proof, tail) = body.split_once("-- CORPUS-END").unwrap();
            let offset = original.len() - body.len();
            cases.push((name.to_string(), offset, offset + proof.len()));
            rest = tail;
        }
        let marked: BTreeSet<_> = cases.iter().map(|c| c.0.clone()).collect();
        assert_eq!(
            marked, expected,
            "mutation inventory must cover every oracle theorem in {module}"
        );
        declarations += expected.len();
        let file = tmp.0.join(format!("{module}.lean"));
        fs::write(&file, &original).unwrap();
        let baseline = corpus::run(Command::new("lean").arg(&file).current_dir(&tmp.0));
        assert!(
            baseline.status.success(),
            "stock baseline {module}: {}",
            corpus::diagnostic(&baseline)
        );
        let check = |name: &str, source: &str, valid: bool| {
            fs::write(&file, source).unwrap();
            // Original/restored bytes are identical: compile that stock baseline once per
            // module, then compile every distinct mutant. Every CLI invocation still runs.
            let mutant =
                (!valid).then(|| corpus::run(Command::new("lean").arg(&file).current_dir(&tmp.0)));
            let lean = mutant.as_ref().unwrap_or(&baseline);
            assert_eq!(
                lean.status.success(),
                valid,
                "stock Lean {module}/{name} valid={valid}: {}",
                corpus::diagnostic(&lean)
            );
            let turbo = corpus::run(
                Command::new(env!("CARGO_BIN_EXE_turbo-lean"))
                    .env("TURBO_LEAN_NO_DAEMON", "1")
                    .env_remove("TURBO_LEAN_ALLOWED_AXIOMS")
                    .env_remove("TURBO_LEAN_ALLOWED_AXIOMS_FROM_CONFIG")
                    .args(["--cache-dir"])
                    .arg(tmp.0.join("cache"))
                    .args(["--json", "check"])
                    .arg(&file)
                    .args(["--decl", name, "--project-dir"])
                    .arg(&tmp.0)
                    .args(["--timeout", "120"])
                    .current_dir(&tmp.0),
            );
            assert_eq!(
                turbo.status.success(),
                lean.status.success(),
                "verdict mismatch {module}/{name} valid={valid}\nstock: {}\nturbo: {}",
                corpus::diagnostic(&lean),
                corpus::diagnostic(&turbo)
            );
            if !valid {
                let stock_errors = corpus::diagnostic(lean).to_lowercase();
                assert_eq!(
                    lean.status.code(),
                    Some(1),
                    "stock mutant must be rejected normally: {stock_errors}"
                );
                assert!(
                    stock_errors.contains("type mismatch"),
                    "stock mutant failed without a proof-type diagnostic: {stock_errors}"
                );
                let errors = corpus::diagnostic(&turbo).to_lowercase();
                assert_eq!(
                    turbo.status.code(),
                    Some(1),
                    "mutant must be rejected normally: {errors}"
                );
                assert!(
                    errors.contains("type mismatch"),
                    "mutant failed without a proof-type diagnostic: {errors}"
                );
            }
            if valid {
                let value: serde_json::Value = serde_json::from_slice(&turbo.stdout)
                    .unwrap_or_else(|_| {
                        panic!("CLI did not return JSON: {}", corpus::diagnostic(&turbo))
                    });
                assert!(
                    matches!(
                        value["status"].as_str(),
                        Some("theorem_verified" | "cache_hit" | "theorem_cache_hit")
                    ),
                    "unexpected success: {value}"
                );
            }
        };
        for (name, start, end) in cases {
            // Same path and persistent cache: detect stale positive hits on edits and restored proofs.
            check(&name, &original, true);
            let broken = format!(
                "{}:= by exact (0 : Nat)\n{}",
                &original[..start],
                &original[end..]
            );
            check(&name, &broken, false);
            check(&name, &original, true);
            comparisons += 3;
            eprintln!("A0d verdict: {name}: baseline/pass, mutant/fail, restored/pass");
        }
    }
    eprintln!(
        "A0d verdict parity: {declarations} declarations, {comparisons} comparisons, 0 mismatches"
    );
}
