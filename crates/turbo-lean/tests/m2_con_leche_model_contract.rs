use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

struct M2ModelContractFixture {
    root: PathBuf,
}

impl M2ModelContractFixture {
    fn new(name: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "turbo_m2_model_contract_{}_{}_{}",
            name,
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir_all(&root).unwrap();
        Self { root }
    }

    fn cli(&self, cache_tag: &str) -> Command {
        let cache_dir = self.root.join(format!("cache-{cache_tag}"));
        let staging_dir = self.root.join(format!("staging-{cache_tag}"));
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_turbo-lean"));
        cmd.current_dir(&self.root)
            .env("TURBO_LEAN_HOME", &cache_dir)
            .env("TURBO_LEAN_STAGING_DIR", &staging_dir)
            .env("TURBO_LEAN_NO_DAEMON", "1")
            .env("TURBO_LEAN_TELEMETRY", "off")
            .env("TURBO_LEAN_NO_REMOTE_TELEMETRY", "1")
            .env_remove("TURBO_LEAN_AUDIT_CACHE_DIR")
            .env_remove("TURBO_LEAN_NO_AUDIT_CACHE");
        cmd
    }
}

impl Drop for M2ModelContractFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

/// G1b real-`.olean` theorems that must exist, kernel-check and pass `audit-spec` as tight.
const REAL_OLEAN_THEOREMS: [&str; 4] = [
    "TurboLean.Kernel.ConLeche.parseRealOleanHeader_iff",
    "TurboLean.Kernel.ConLeche.olen_shard_not_real_olean",
    "TurboLean.Kernel.ConLeche.real_olean_bridge_sound",
    "TurboLean.Kernel.ConLeche.real_olean_checkDecl_sound",
];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

/// Return the string literal following `marker` in `src` (e.g. `asciiBytes "<lit>"`).
fn literal_after<'a>(src: &'a str, marker: &str) -> &'a str {
    let start = src
        .find(marker)
        .unwrap_or_else(|| panic!("missing `{marker}`"));
    let rest = &src[start..];
    let open = rest.find('"').unwrap() + 1;
    let close = open + rest[open..].find('"').unwrap();
    &rest[open..close]
}

fn assert_ok(out: &Output, ctx: &str) {
    assert!(
        out.status.success(),
        "{ctx} failed (status {:?}):\nstdout:\n{}\nstderr:\n{}",
        out.status.code(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn milestone_m2_g1b_con_leche_contract_v4_and_olen_v1_model_disclosure() {
    let f = M2ModelContractFixture::new("g1b_contract_v4");
    let repo_root = repo_root();

    let con_leche_lean = repo_root.join("lean/TurboLean/ConLeche.lean");
    let src = fs::read_to_string(&con_leche_lean).expect("read lean/TurboLean/ConLeche.lean");
    assert!(
        src.contains("namespace TurboLean.Kernel.ConLeche"),
        "lean/TurboLean/ConLeche.lean must declare `namespace TurboLean.Kernel.ConLeche`"
    );
    assert!(
        src.contains("OLEN")
            && src.contains("0x4F4C454E")
            && src.contains("model")
            && src.contains("leanprover/con-leche")
            && src.contains("H1"),
        "lean/TurboLean/ConLeche.lean must explicitly disclose the self-contained `OLEN` v1 (`0x4F4C454E`) model parser scope and preserve the real `leanprover/con-leche` H1/H3 goal distinction"
    );

    let kernel_elab_lean = repo_root.join("lean/LeanNative/Proofs/KernelElabProofs.lean");
    let kernel_elab_src = fs::read_to_string(&kernel_elab_lean)
        .expect("read lean/LeanNative/Proofs/KernelElabProofs.lean");
    for bridge_decl in [
        "kernel_conLeche_olean_mmap_bridge_sound_bridge",
        "kernel_conLeche_verify_decl_sound_bridge",
    ] {
        assert!(
            kernel_elab_src.contains(bridge_decl),
            "lean/LeanNative/Proofs/KernelElabProofs.lean must export `{bridge_decl}`"
        );
    }

    let axiom_audit_lean = repo_root.join("lean/LeanNative/Proofs/AxiomAudit.lean");
    let axiom_audit_src =
        fs::read_to_string(&axiom_audit_lean).expect("read lean/LeanNative/Proofs/AxiomAudit.lean");
    for audited_thm in [
        "``TurboLean.Kernel.ConLeche.verifyDeclsPrefix_append_singleton",
        "``TurboLean.Kernel.ConLeche.olean_mmap_bridge_sound",
        "``TurboLean.Kernel.ConLeche.con_leche_verify_decl_sound",
        "``TurboLean.Kernel.ConLeche.typecheck_rejects_ill_typed_app",
    ] {
        assert!(
            axiom_audit_src.contains(audited_thm),
            "lean/LeanNative/Proofs/AxiomAudit.lean must register `{audited_thm}` in `auditedTheoremNames`"
        );
    }

    let audit_out = f
        .cli("m2_g1b_audit")
        .args([
            "--json",
            "audit-spec",
            "--policy",
            "strict-proofs",
            con_leche_lean.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_ok(&audit_out, "audit-spec lean/TurboLean/ConLeche.lean");
    let audit: Value = serde_json::from_slice(&audit_out.stdout).unwrap();
    assert_eq!(
        audit["ok"].as_bool(),
        Some(true),
        "audit-spec failed: {audit}"
    );
    assert_eq!(audit["vacuous_specs"].as_u64(), Some(0), "{audit}");
    assert_eq!(audit["trivial_specs"].as_u64(), Some(0), "{audit}");
    assert_eq!(
        audit["droppable_hypotheses"].as_array().map(|a| a.len()),
        Some(0),
        "{audit}"
    );
    assert_eq!(
        audit["horizontal_packing_warnings"]
            .as_array()
            .map(|a| a.len()),
        Some(0),
        "expected 0 horizontal_packing_warnings in ConLeche.lean: {audit}"
    );
    let specs = audit["specs"].as_array().expect("specs array");
    for required_decl in [
        "TurboLean.Kernel.ConLeche.verifyDeclsPrefix_append_singleton",
        "TurboLean.Kernel.ConLeche.olean_mmap_bridge_sound",
        "TurboLean.Kernel.ConLeche.con_leche_verify_decl_sound",
        "TurboLean.Kernel.ConLeche.typecheck_rejects_ill_typed_app",
    ]
    .into_iter()
    .chain(REAL_OLEAN_THEOREMS)
    {
        assert!(
            specs.iter().any(|s| {
                s["decl"].as_str() == Some(required_decl)
                    && s["tight"].as_bool() == Some(true)
                    && s["vacuous"].as_bool() == Some(false)
            }),
            "missing or non-tight required M2 G1b theorem `{required_decl}` in {audit}"
        );
    }
}

#[test]
fn milestone_m2_g1b_real_olean_header_theorems_and_trusted_boundary() {
    let root = repo_root();
    let src = fs::read_to_string(root.join("lean/TurboLean/ConLeche.lean"))
        .expect("read lean/TurboLean/ConLeche.lean");

    for thm in REAL_OLEAN_THEOREMS {
        let short = thm.rsplit('.').next().unwrap();
        assert!(
            src.contains(&format!("theorem {short} ")),
            "ConLeche.lean must declare `theorem {short}`"
        );
    }
    assert_eq!(
        src.matches("sorry").count(),
        src.matches("sorryAx").count(),
        "ConLeche.lean must not use `sorry` (only `0 sorryAx` mentions allowed)"
    );
    assert!(
        !src.lines().any(|l| l.trim_start().starts_with("axiom ")),
        "ConLeche.lean must not declare axioms"
    );
    for def in [
        "def parseRealOleanHeader",
        "def RealOleanHeaderSpec",
        "def parseRealOlean",
        "def checkRealOleanDecl",
        "def realOleanHeaderSize : Nat := 96",
    ] {
        assert!(src.contains(def), "ConLeche.lean must define `{def}`");
    }
    // Mutant-kill guards for the real header must be present (one per mutant class).
    for mutant in [
        "Mutant R1",
        "Mutant R2",
        "Mutant R3",
        "Mutant R4",
        "Mutant R5",
        "Mutant R6",
    ] {
        assert!(
            src.contains(mutant),
            "ConLeche.lean must keep `#guard` block `{mutant}`"
        );
    }
    assert!(
        src.matches("#guard (parseRealOleanHeader").count() >= 12,
        "expected >= 12 `parseRealOleanHeader` #guard checks"
    );
    // The trusted boundary must be disclosed in-file and in the trusted base.
    assert!(
        src.contains("lean_compacted_region_read"),
        "ConLeche.lean must name the trusted C reader `lean_compacted_region_read`"
    );
    let trusted = fs::read_to_string(root.join("docs/TRUSTED_BASE.md")).unwrap();
    let item4 = &trusted[trusted.find("\n4. ").expect("TRUSTED_BASE.md item 4")..];
    for needle in ["lean_compacted_region_read", "Trusted, not proved"]
        .into_iter()
        .chain(REAL_OLEAN_THEOREMS.map(|t| t.rsplit('.').next().unwrap()))
    {
        assert!(
            item4.contains(needle),
            "TRUSTED_BASE.md item 4 must mention `{needle}`"
        );
    }

    // Cross-check the pinned constants against the real toolchain `.olean` when available.
    let lean_version = literal_after(&src, "def realOleanLeanVersion");
    let githash = literal_after(&src, "def realOleanGithash");
    assert_eq!(lean_version, "4.35.0");
    assert_eq!(githash.len(), 40, "githash field is 40 bytes");
    let toolchain = fs::read_to_string(root.join("lean/lean-toolchain")).unwrap();
    assert!(
        toolchain.trim().ends_with(&format!("v{lean_version}")),
        "pinned .olean version must match lean/lean-toolchain ({})",
        toolchain.trim()
    );
    let prefix = Command::new("lean")
        .arg("--print-prefix")
        .current_dir(root.join("lean"))
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| PathBuf::from(String::from_utf8_lossy(&o.stdout).trim()));
    let Some(prefix) = prefix else {
        eprintln!("skipping real .olean cross-check: `lean --print-prefix` unavailable");
        return;
    };
    let prelude = prefix.join("lib/lean/Init/Prelude.olean");
    let bytes = fs::read(&prelude).unwrap_or_else(|e| panic!("read {}: {e}", prelude.display()));
    assert!(
        bytes.len() >= 96,
        "real .olean shorter than the 96-byte header"
    );
    assert_eq!(&bytes[0..5], b"olean");
    assert!(matches!(bytes[5], 2 | 3), "version byte {}", bytes[5]);
    let mut version_field = lean_version.as_bytes().to_vec();
    version_field.resize(33, 0);
    assert_eq!(
        &bytes[7..40],
        &version_field[..],
        "bytes 7..40 must be NUL-padded version"
    );
    assert_eq!(
        &bytes[40..80],
        githash.as_bytes(),
        "bytes 40..80 must be the pinned githash"
    );
    let le = |off: usize| u64::from_le_bytes(bytes[off..off + 8].try_into().unwrap()) as u128;
    let (base, root_ptr, size) = (le(80), le(88), bytes.len() as u128);
    assert!(base + 96 <= root_ptr, "root pointer inside header");
    assert!(root_ptr + 8 <= base + size, "root pointer past region end");
    assert_eq!((root_ptr - base) % 8, 0, "root pointer misaligned");
}
