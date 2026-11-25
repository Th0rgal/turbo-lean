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

/// G1b real-`.olean` leg: a real artifact compiled by the PINNED toolchain is structurally
/// disjoint from the in-repo `"OLEN"` v1 model shard format, so the Contract V4 M2 theorems
/// (stated over `parseOleanShard`) demonstrably say nothing about real `.olean` files, and
/// `ConLeche.lean` carries kernel-evaluated guards pinning that rejection.
#[cfg(unix)]
#[test]
fn milestone_m2_g1b_real_olean_artifact_disjoint_from_olen_model_shards() {
    let f = M2ModelContractFixture::new("g1b_real_olean");
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();

    // Real compiled artifact from the pinned toolchain — never synthesized `.olean` bytes.
    let toolchain = fs::read_to_string(repo_root.join("lean/lean-toolchain"))
        .expect("read lean/lean-toolchain")
        .trim()
        .to_string();
    let dir = f.root.join("olean");
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("lean-toolchain"), format!("{toolchain}\n")).unwrap();
    let lean_bin = Command::new("elan")
        .current_dir(&dir)
        .args(["which", "lean"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| PathBuf::from(String::from_utf8_lossy(&o.stdout).trim()))
        .unwrap_or_else(|| PathBuf::from("lean"));
    let ver = Command::new(&lean_bin)
        .current_dir(&dir)
        .arg("--version")
        .output()
        .unwrap();
    assert_ok(&ver, "pinned `lean --version`");
    let ver_txt = String::from_utf8_lossy(&ver.stdout).into_owned();
    let githash8: String = ver_txt
        .split("commit ")
        .nth(1)
        .expect("`lean --version` names its commit")
        .chars()
        .take(8)
        .collect();

    fs::write(
        dir.join("ValidPrelude.lean"),
        "module\nprelude\npublic section\ninductive Yes : Prop where\n  | intro\ntheorem yes : Yes := Yes.intro\nend\n",
    )
    .unwrap();
    let olean_path = dir.join("ValidPrelude.olean");
    let comp = Command::new(&lean_bin)
        .current_dir(&dir)
        .args([
            "-R",
            dir.to_str().unwrap(),
            "-o",
            olean_path.to_str().unwrap(),
            dir.join("ValidPrelude.lean").to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_ok(&comp, "compile ValidPrelude.lean with the pinned toolchain");

    let bytes = fs::read(&olean_path).expect("read real ValidPrelude.olean");

    // Real `.olean` header facts under the pinned toolchain: ASCII `olean` magic, the ASCII
    // compiler version at byte offset 7, the emitting compiler githash at byte offset 40.
    const OLEN_MODEL_MAGIC: [u8; 4] = [0x4F, 0x4C, 0x45, 0x4E];
    assert!(
        bytes.len() > 48,
        "real .olean larger than its 48-byte header prefix (got {})",
        bytes.len()
    );
    assert_eq!(&bytes[..5], &b"olean"[..], "real Lean 4 `.olean` magic");
    let version = toolchain
        .rsplit(":v")
        .next()
        .expect("toolchain pins a version");
    assert_eq!(
        &bytes[7..7 + version.len()],
        version.as_bytes(),
        "artifact embeds the pinned compiler version"
    );
    assert_eq!(
        &bytes[40..48],
        githash8.as_bytes(),
        "artifact embeds the pinned compiler githash"
    );
    // The disjointness the G1b guards pin in Lean: a real `.olean` never carries the model magic.
    assert_ne!(
        &bytes[..4],
        &OLEN_MODEL_MAGIC[..],
        "a real `.olean` is not an OLEN v1 model shard"
    );

    // Planted control: a synthesized OLEN v1 model shard must NOT read as a real artifact.
    let synthesized_olen_model_shard: [u8; 5] = [0x4F, 0x4C, 0x45, 0x4E, 0x00];
    assert_eq!(&synthesized_olen_model_shard[..4], &OLEN_MODEL_MAGIC[..]);
    assert_ne!(&synthesized_olen_model_shard[..5], &b"olean"[..]);

    // ConLeche.lean carries the executable discriminator guards (G1b honesty, kernel-evaluated).
    let src = fs::read_to_string(repo_root.join("lean/TurboLean/ConLeche.lean"))
        .expect("read lean/TurboLean/ConLeche.lean");
    assert!(src.contains("def realLeanOleanHeaderPrefix : ByteArray"));
    assert!(src.contains("#guard (parseOleanShard realLeanOleanHeaderPrefix).isOk == false"));
    assert!(src.contains("#guard realLeanOleanHeaderPrefix.get! 0 != 0x4F"));
}
