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
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();

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
    assert_eq!(audit["ok"].as_bool(), Some(true), "audit-spec failed: {audit}");
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
    ] {
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
