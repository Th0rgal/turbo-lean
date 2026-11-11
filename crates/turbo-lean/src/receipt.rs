//! Cryptographic Verification Receipts (`schema_version = 2` provenance-bound + legacy `schema_version = 1` verification).
//!
//! Provides sub-millisecond offline verification of `ci-verify` and `pr-verify` receipts
//! without opening SQLite (`state.db`), including BLAKE3 content addressing, keyed HMAC-BLAKE3
//! / Ed25519-domain-separated attestation helpers, and per-file `InterfaceHash` drift pinpointing.
//!
//! Declarative Lake file inputs (`input_dir` / `input_file`) are deliberately **not** mixed into
//! `interface_hash` or `per_file_interfaces`. Those are projections of the Lean sources alone --
//! the proof-irrelevant signature of each file -- and their one job is to be compared between two
//! revisions to pinpoint interface drift. Both sides of that comparison are read with the same
//! inputs on disk, so folding the input bytes in would move both and report nothing new, while
//! making an unchanged Lean interface look changed whenever a `.sol` file was touched.
//!
//! The receipt is still bound to the input bytes, through `action_key`:
//! `lake_build::update_with_lake_input_digests` folds the whole workspace's input digests into the
//! `build` and `ci-verify` action keys, and `compute_receipt_blake3` covers `action_key`. So a
//! receipt issued against one set of inputs cannot be presented for another.

use anyhow::{Context, Result};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

pub const CURRENT_RECEIPT_SCHEMA_VERSION: u32 = 2;

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct VerificationReceipt {
    pub schema_version: u32,
    pub mode: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kernel_engine: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lean_toolchain: Option<String>,
    #[serde(default)]
    pub con_leche_rev: Option<String>,
    pub interface_hash: String,
    pub action_key: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub active_csimp_digest: Option<String>,
    pub files_audited: usize,
    pub theorem_shards: usize,
    pub forbidden_constructs_found: usize,
    pub per_file_interfaces: BTreeMap<String, String>,
    pub receipt_blake3: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub signature_alg: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ed25519_pubkey: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ed25519_signature: Option<String>,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ReceiptVerificationReport {
    pub status: String,
    pub schema_version: u32,
    pub mode: String,
    pub kernel_engine: Option<String>,
    pub lean_toolchain: Option<String>,
    pub con_leche_rev: Option<String>,
    pub interface_hash: String,
    pub action_key: String,
    pub receipt_blake3: String,
    pub files_audited: usize,
    pub theorem_shards: usize,
    pub forbidden_constructs_found: usize,
    pub altered_files: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub signature_verified: Option<bool>,
}

#[inline(always)]
fn classify_receipt_str_field(val: Option<&str>) -> u8 {
    match val {
        None => 0,
        Some(s) if s.trim().is_empty() => 1,
        Some(_) => 2,
    }
}

#[inline(always)]
fn classify_receipt_engine_kind(
    raw: Option<&str>,
) -> (Option<crate::kernel::ResolvedKernelEngine>, u8) {
    match raw.and_then(|s| crate::kernel::ResolvedKernelEngine::parse_resolved(s).ok()) {
        Some(resolved @ crate::kernel::ResolvedKernelEngine::Standard) => (Some(resolved), 1),
        Some(resolved @ crate::kernel::ResolvedKernelEngine::ConLeche) => (Some(resolved), 2),
        Some(resolved @ crate::kernel::ResolvedKernelEngine::Both) => (Some(resolved), 3),
        None => (None, 0),
    }
}

fn validate_receipt_kernel_provenance(
    kernel_engine: &str,
    lean_toolchain: &str,
    con_leche_rev: Option<&str>,
) -> Result<()> {
    let (resolved_opt, engine_kind) = classify_receipt_engine_kind(Some(kernel_engine));
    let toolchain_state = classify_receipt_str_field(Some(lean_toolchain));
    let rev_state = classify_receipt_str_field(con_leche_rev);
    if crate::c_abi::verify_receipt_provenance(
        CURRENT_RECEIPT_SCHEMA_VERSION,
        true,
        engine_kind,
        toolchain_state,
        rev_state,
        true,
    ) {
        return Ok(());
    }
    let Some(resolved) = resolved_opt else {
        anyhow::bail!(
            "Receipt kernel provenance check FAILED: invalid `kernel_engine` `{}` (expected `standard`, `con-leche`, or `both`)",
            kernel_engine
        );
    };
    if toolchain_state != 2 {
        anyhow::bail!("Receipt kernel provenance check FAILED: `lean_toolchain` must be non-empty");
    }
    if engine_kind == 1 {
        anyhow::bail!(
            "Receipt kernel provenance check FAILED: `kernel_engine` is `standard` but `con_leche_rev` is set (`{}`)",
            con_leche_rev.unwrap_or_default()
        );
    }
    anyhow::bail!(
        "Receipt kernel provenance check FAILED: `kernel_engine` `{}` requires a non-empty `con_leche_rev`",
        resolved.as_str()
    )
}

#[allow(clippy::too_many_arguments)]
pub fn compute_receipt_blake3_v1(
    schema_version: u32,
    mode: &str,
    interface_hash: &str,
    action_key: &str,
    files_audited: usize,
    theorem_shards: usize,
    forbidden_constructs_found: usize,
    per_file_interfaces: &BTreeMap<String, String>,
) -> String {
    use std::fmt::Write;
    let mut hasher = blake3::Hasher::new();
    let mut header = String::with_capacity(256);
    let _ = writeln!(
        header,
        "turbo-lean-verification-receipt-v1\nschema_version:{}\nmode:{}\ninterface_hash:{}\naction_key:{}\nfiles_audited:{}\ntheorem_shards:{}\nforbidden_constructs_found:{}",
        schema_version,
        mode,
        interface_hash,
        action_key,
        files_audited,
        theorem_shards,
        forbidden_constructs_found
    );
    hasher.update(header.as_bytes());
    for (rel_path, file_ih) in per_file_interfaces {
        hasher.update(b"file:");
        hasher.update(rel_path.as_bytes());
        hasher.update(b"=");
        hasher.update(file_ih.as_bytes());
        hasher.update(b"\n");
    }
    hasher.finalize().to_hex().to_string()
}

#[allow(clippy::too_many_arguments)]
pub fn compute_receipt_blake3(
    schema_version: u32,
    mode: &str,
    kernel_engine: &str,
    lean_toolchain: &str,
    con_leche_rev: Option<&str>,
    active_csimp_digest: Option<&str>,
    interface_hash: &str,
    action_key: &str,
    files_audited: usize,
    theorem_shards: usize,
    forbidden_constructs_found: usize,
    per_file_interfaces: &BTreeMap<String, String>,
) -> String {
    use std::fmt::Write;
    let mut hasher = blake3::Hasher::new();
    let mut header = String::with_capacity(384);
    let _ = writeln!(
        header,
        "turbo-lean-verification-receipt-v2\nschema_version:{}\nmode:{}\nkernel_engine:{}:{}\nlean_toolchain:{}:{}\ninterface_hash:{}\naction_key:{}\nfiles_audited:{}\ntheorem_shards:{}\nforbidden_constructs_found:{}",
        schema_version,
        mode,
        kernel_engine.len(),
        kernel_engine,
        lean_toolchain.len(),
        lean_toolchain,
        interface_hash,
        action_key,
        files_audited,
        theorem_shards,
        forbidden_constructs_found
    );
    match con_leche_rev {
        None => {
            let _ = writeln!(header, "con_leche_rev:none");
        }
        Some(rev) => {
            let _ = writeln!(header, "con_leche_rev:some:{}:{}", rev.len(), rev);
        }
    }
    hasher.update(header.as_bytes());
    for (rel_path, file_ih) in per_file_interfaces {
        hasher.update(b"file:");
        hasher.update(rel_path.as_bytes());
        hasher.update(b"=");
        hasher.update(file_ih.as_bytes());
        hasher.update(b"\n");
    }
    bind_active_csimp_digest(&hasher.finalize().to_hex().to_string(), active_csimp_digest)
}

/// Canonical active compiler-simplification policy and entries. Entries include the
/// theorem, source, and replacement identities (prefer content-bound identities).
/// Ordering and duplicate policy/entry observations do not affect the digest.
pub fn compute_active_csimp_digest(
    policy: &[String],
    entries: &[(String, String, String)],
) -> String {
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-active-csimp-v1\n");
    let mut field = |s: &str| {
        h.update(&(s.len() as u64).to_le_bytes());
        h.update(s.as_bytes());
    };
    for pattern in policy
        .iter()
        .map(|p| p.trim())
        .filter(|p| !p.is_empty())
        .collect::<BTreeSet<_>>()
    {
        field("policy");
        field(pattern);
    }
    for (theorem, from, to) in entries.iter().collect::<BTreeSet<_>>() {
        field("entry");
        field(theorem);
        field(from);
        field(to);
    }
    h.finalize().to_hex().to_string()
}

fn bind_active_csimp_digest(legacy_hash: &str, digest: Option<&str>) -> String {
    let Some(digest) = digest else {
        return legacy_hash.to_owned();
    };
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean-receipt-active-csimp-v1\n");
    for value in [legacy_hash, digest] {
        h.update(&(value.len() as u64).to_le_bytes());
        h.update(value.as_bytes());
    }
    h.finalize().to_hex().to_string()
}

impl VerificationReceipt {
    /// Bind observed entries before signing. A changed digest invalidates any old
    /// signature, so the caller must sign the updated receipt again.
    pub fn bind_active_csimp(
        &mut self,
        policy: &[String],
        entries: &[(String, String, String)],
    ) -> Result<()> {
        verify_single_receipt_integrity_and_provenance(self, "Cryptographic")?;
        let digest = compute_active_csimp_digest(policy, entries);
        let legacy_hash = match self.schema_version {
            1 => compute_receipt_blake3_v1(
                self.schema_version,
                &self.mode,
                &self.interface_hash,
                &self.action_key,
                self.files_audited,
                self.theorem_shards,
                self.forbidden_constructs_found,
                &self.per_file_interfaces,
            ),
            _ => compute_receipt_blake3(
                self.schema_version,
                &self.mode,
                self.kernel_engine.as_deref().unwrap_or_default(),
                self.lean_toolchain.as_deref().unwrap_or_default(),
                self.con_leche_rev.as_deref(),
                None,
                &self.interface_hash,
                &self.action_key,
                self.files_audited,
                self.theorem_shards,
                self.forbidden_constructs_found,
                &self.per_file_interfaces,
            ),
        };
        self.receipt_blake3 = bind_active_csimp_digest(&legacy_hash, Some(&digest));
        self.active_csimp_digest = Some(digest);
        self.signature_alg = None;
        self.ed25519_pubkey = None;
        self.ed25519_signature = None;
        Ok(())
    }
}

/// Compute a keyed HMAC-BLAKE3 authentication tag over `receipt_blake3`.
pub fn compute_receipt_hmac_blake3(key: &[u8; 32], receipt_blake3: &str) -> String {
    blake3::keyed_hash(key, receipt_blake3.as_bytes())
        .to_hex()
        .to_string()
}

use crate::pack::{decode_hex_fixed, encode_hex_bytes};

fn receipt_ed25519_signing_message(receipt_blake3: &str) -> Vec<u8> {
    let mut msg = Vec::with_capacity(32 + receipt_blake3.len());
    msg.extend_from_slice(b"turbo-lean-receipt-ed25519-v1\n");
    msg.extend_from_slice(receipt_blake3.as_bytes());
    msg
}

/// Resolve an optional 32-byte Ed25519 signing key from CLI flag or `TURBO_LEAN_RECEIPT_SIGNING_KEY`.
pub fn resolve_ed25519_signing_key_with_override(
    explicit_hex: Option<&str>,
) -> Result<Option<[u8; 32]>> {
    let env_val = std::env::var("TURBO_LEAN_RECEIPT_SIGNING_KEY").ok();
    let raw = match explicit_hex.or(env_val.as_deref()) {
        Some(v) if !v.trim().is_empty() => v.trim(),
        _ => return Ok(None),
    };
    let key = decode_hex_fixed::<32>(raw)
        .context("Invalid Ed25519 signing key: expected 64-character hex seed")?;
    Ok(Some(key))
}

pub fn resolve_ed25519_signing_key() -> Option<[u8; 32]> {
    resolve_ed25519_signing_key_with_override(None)
        .ok()
        .flatten()
}

pub fn ed25519_verifying_key_hex(signing_key_seed: &[u8; 32]) -> String {
    use ed25519_dalek::SigningKey;
    let sk = SigningKey::from_bytes(signing_key_seed);
    encode_hex_bytes(sk.verifying_key().as_bytes())
}

/// Produce a real Ed25519 (`ed25519-dalek`) attestation signature over `receipt_blake3`.
pub fn sign_receipt_ed25519(signing_key_seed: &[u8; 32], receipt_blake3: &str) -> String {
    use ed25519_dalek::{Signer, SigningKey};
    let sk = SigningKey::from_bytes(signing_key_seed);
    let msg = receipt_ed25519_signing_message(receipt_blake3);
    let sig = sk.sign(&msg);
    encode_hex_bytes(&sig.to_bytes())
}

/// Verify a real Ed25519 (`ed25519-dalek`) attestation signature over `receipt_blake3` using a 32-byte public key.
pub fn verify_receipt_ed25519_pubkey(
    pubkey_bytes: &[u8; 32],
    receipt_blake3: &str,
    signature_hex: &str,
) -> bool {
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};
    let Ok(vk) = VerifyingKey::from_bytes(pubkey_bytes) else {
        return false;
    };
    let Ok(sig_bytes) = decode_hex_fixed::<64>(signature_hex) else {
        return false;
    };
    let sig = Signature::from_bytes(&sig_bytes);
    let msg = receipt_ed25519_signing_message(receipt_blake3);
    vk.verify(&msg, &sig).is_ok()
}

/// Verify an Ed25519 signature given the 32-byte signing seed (derives the public key and verifies).
pub fn verify_receipt_ed25519(
    signing_key_seed: &[u8; 32],
    receipt_blake3: &str,
    signature_hex: &str,
) -> bool {
    use ed25519_dalek::SigningKey;
    let vk = SigningKey::from_bytes(signing_key_seed).verifying_key();
    verify_receipt_ed25519_pubkey(vk.as_bytes(), receipt_blake3, signature_hex)
}

pub fn attach_ed25519_signature(receipt: &mut VerificationReceipt, signing_key_seed: &[u8; 32]) {
    let pub_hex = ed25519_verifying_key_hex(signing_key_seed);
    let sig_hex = sign_receipt_ed25519(signing_key_seed, &receipt.receipt_blake3);
    receipt.signature_alg = Some("ed25519-v1".to_string());
    receipt.ed25519_pubkey = Some(pub_hex);
    receipt.ed25519_signature = Some(sig_hex);
}

#[allow(clippy::too_many_arguments)]
pub fn build_verification_receipt_with_provenance(
    mode: &str,
    kernel_engine: &str,
    lean_toolchain: &str,
    con_leche_rev: Option<&str>,
    interface_hash: &str,
    action_key: &str,
    files_audited: usize,
    theorem_shards: usize,
    forbidden_constructs_found: usize,
    per_file_interfaces: BTreeMap<String, String>,
) -> VerificationReceipt {
    let schema_version = CURRENT_RECEIPT_SCHEMA_VERSION;
    let normalized_tc = crate::kernel::normalize_lean_toolchain(lean_toolchain);
    let receipt_blake3 = compute_receipt_blake3(
        schema_version,
        mode,
        kernel_engine,
        &normalized_tc,
        con_leche_rev,
        None,
        interface_hash,
        action_key,
        files_audited,
        theorem_shards,
        forbidden_constructs_found,
        &per_file_interfaces,
    );
    let mut rec = VerificationReceipt {
        schema_version,
        mode: mode.to_string(),
        kernel_engine: Some(kernel_engine.to_string()),
        lean_toolchain: Some(normalized_tc),
        con_leche_rev: con_leche_rev.map(String::from),
        interface_hash: interface_hash.to_string(),
        action_key: action_key.to_string(),
        active_csimp_digest: None,
        files_audited,
        theorem_shards,
        forbidden_constructs_found,
        per_file_interfaces,
        receipt_blake3,
        signature_alg: None,
        ed25519_pubkey: None,
        ed25519_signature: None,
    };
    if let Some(sk) = resolve_ed25519_signing_key() {
        attach_ed25519_signature(&mut rec, &sk);
    }
    rec
}

pub fn build_verification_receipt(
    mode: &str,
    interface_hash: &str,
    action_key: &str,
    files_audited: usize,
    theorem_shards: usize,
    forbidden_constructs_found: usize,
    per_file_interfaces: BTreeMap<String, String>,
) -> VerificationReceipt {
    build_verification_receipt_with_provenance(
        mode,
        "standard",
        "unknown",
        None,
        interface_hash,
        action_key,
        files_audited,
        theorem_shards,
        forbidden_constructs_found,
        per_file_interfaces,
    )
}

/// Write a [`VerificationReceipt`] to `receipt_path` if requested, optionally signing with `signing_key_hex`.
pub fn emit_verification_receipt_with_signing_key(
    receipt_path: Option<&Path>,
    receipt: &mut VerificationReceipt,
    signing_key_hex: Option<&str>,
) -> Result<()> {
    if let Some(sk) = resolve_ed25519_signing_key_with_override(signing_key_hex)? {
        attach_ed25519_signature(receipt, &sk);
    }
    if let Some(path) = receipt_path {
        if let Some(parent) = path.parent() {
            if !parent.as_os_str().is_empty() {
                fs::create_dir_all(parent)?;
            }
        }
        fs::write(path, serde_json::to_vec_pretty(receipt)?)?;
    }
    Ok(())
}

/// Write a [`VerificationReceipt`] to `receipt_path` if requested.
pub fn emit_verification_receipt_if_requested(
    receipt_path: Option<&Path>,
    receipt: &VerificationReceipt,
) -> Result<()> {
    let mut cloned = receipt.clone();
    emit_verification_receipt_with_signing_key(receipt_path, &mut cloned, None)
}

pub fn verify_receipt_signature_policy(
    receipt: &VerificationReceipt,
    verify_pubkey_hex: Option<&str>,
    require_signature: bool,
) -> Result<Option<bool>> {
    let env_pk = std::env::var("TURBO_LEAN_RECEIPT_VERIFY_PUBKEY")
        .ok()
        .filter(|s| !s.trim().is_empty());
    let env_req = std::env::var("TURBO_LEAN_RECEIPT_REQUIRE_SIGNATURE")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false);
    let eff_pk_hex = verify_pubkey_hex
        .filter(|s| !s.trim().is_empty())
        .or(env_pk.as_deref());
    let eff_require = require_signature || env_req || eff_pk_hex.is_some();

    let has_any_sig_field = receipt.signature_alg.is_some()
        || receipt.ed25519_pubkey.is_some()
        || receipt.ed25519_signature.is_some();

    if !has_any_sig_field {
        if eff_require {
            anyhow::bail!("Receipt Ed25519 signature required, but receipt is unsigned");
        }
        return Ok(None);
    }

    let alg = receipt.signature_alg.as_deref().unwrap_or("");
    if alg != "ed25519-v1" {
        anyhow::bail!(
            "Unsupported or mislabeled receipt signature_alg `{}` (expected `ed25519-v1`)",
            alg
        );
    }
    let sig_hex = receipt
        .ed25519_signature
        .as_deref()
        .ok_or_else(|| anyhow::anyhow!("Receipt missing ed25519_signature field"))?;
    let embedded_pk_opt = match receipt.ed25519_pubkey.as_deref() {
        Some(pk) => Some(
            decode_hex_fixed::<32>(pk).context("Invalid embedded ed25519_pubkey hex in receipt")?,
        ),
        None => None,
    };
    let pubkey_bytes = if let Some(exp_hex) = eff_pk_hex {
        let exp_bytes = decode_hex_fixed::<32>(exp_hex)
            .context("Invalid expected Ed25519 verify public key hex")?;
        if let Some(emb) = embedded_pk_opt {
            if emb != exp_bytes {
                anyhow::bail!("Receipt ed25519_pubkey does not match expected verify pubkey");
            }
        }
        exp_bytes
    } else if let Some(emb) = embedded_pk_opt {
        emb
    } else {
        anyhow::bail!("Receipt has signature but no ed25519_pubkey or --verify-pubkey");
    };

    if !verify_receipt_ed25519_pubkey(&pubkey_bytes, &receipt.receipt_blake3, sig_hex) {
        anyhow::bail!("Receipt Ed25519 signature verification FAILED");
    }
    Ok(Some(true))
}

pub fn verify_receipt_data(
    receipt: &VerificationReceipt,
    expected_interface_hash: Option<&str>,
    baseline: Option<&VerificationReceipt>,
) -> Result<Vec<String>> {
    verify_receipt_data_with_policy(receipt, expected_interface_hash, baseline, None, false)
        .map(|(altered, _)| altered)
}

fn verify_single_receipt_integrity_and_provenance(
    receipt: &VerificationReceipt,
    label: &str,
) -> Result<()> {
    let has_kernel_engine = receipt.kernel_engine.is_some();
    let (_, engine_kind) = classify_receipt_engine_kind(receipt.kernel_engine.as_deref());
    let toolchain_state = classify_receipt_str_field(receipt.lean_toolchain.as_deref());
    let rev_state = classify_receipt_str_field(receipt.con_leche_rev.as_deref());
    let expected_blake3_opt = match receipt.schema_version {
        1 => Some(bind_active_csimp_digest(
            &compute_receipt_blake3_v1(
                receipt.schema_version,
                &receipt.mode,
                &receipt.interface_hash,
                &receipt.action_key,
                receipt.files_audited,
                receipt.theorem_shards,
                receipt.forbidden_constructs_found,
                &receipt.per_file_interfaces,
            ),
            receipt.active_csimp_digest.as_deref(),
        )),
        CURRENT_RECEIPT_SCHEMA_VERSION => receipt
            .kernel_engine
            .as_deref()
            .zip(receipt.lean_toolchain.as_deref())
            .map(|(ke, tc)| {
                compute_receipt_blake3(
                    receipt.schema_version,
                    &receipt.mode,
                    ke,
                    tc,
                    receipt.con_leche_rev.as_deref(),
                    receipt.active_csimp_digest.as_deref(),
                    &receipt.interface_hash,
                    &receipt.action_key,
                    receipt.files_audited,
                    receipt.theorem_shards,
                    receipt.forbidden_constructs_found,
                    &receipt.per_file_interfaces,
                )
            }),
        _ => None,
    };
    let blake3_matches = expected_blake3_opt
        .as_deref()
        .is_some_and(|exp| receipt.receipt_blake3 == exp);

    if crate::c_abi::verify_receipt_provenance(
        receipt.schema_version,
        has_kernel_engine,
        engine_kind,
        toolchain_state,
        rev_state,
        blake3_matches,
    ) {
        return Ok(());
    }

    match receipt.schema_version {
        1 => {
            if has_kernel_engine || toolchain_state != 0 || rev_state != 0 {
                anyhow::bail!(
                    "{label} receipt schema_version 1 cannot carry unauthenticated kernel provenance fields (`kernel_engine`, `lean_toolchain`, or `con_leche_rev`); use schema_version 2"
                );
            }
            let expected_blake3 = expected_blake3_opt.unwrap_or_default();
            anyhow::bail!(
                "{label} receipt BLAKE3 integrity check FAILED: expected {}, got {}",
                expected_blake3,
                receipt.receipt_blake3
            )
        }
        CURRENT_RECEIPT_SCHEMA_VERSION => {
            let kernel_engine = receipt.kernel_engine.as_deref().ok_or_else(|| {
                anyhow::anyhow!(
                    "{label} receipt schema_version 2 missing required `kernel_engine` field"
                )
            })?;
            let lean_toolchain = receipt.lean_toolchain.as_deref().ok_or_else(|| {
                anyhow::anyhow!(
                    "{label} receipt schema_version 2 missing required `lean_toolchain` field"
                )
            })?;
            if !blake3_matches {
                let expected_blake3 = expected_blake3_opt.unwrap_or_default();
                anyhow::bail!(
                    "{label} receipt BLAKE3 integrity check FAILED: expected {}, got {}",
                    expected_blake3,
                    receipt.receipt_blake3
                );
            }
            validate_receipt_kernel_provenance(
                kernel_engine,
                lean_toolchain,
                receipt.con_leche_rev.as_deref(),
            )?;
            anyhow::bail!("{label} receipt kernel provenance admission rejected by Lean C-ABI gate")
        }
        other => {
            anyhow::bail!(
                "Unsupported {} receipt schema_version {} (expected 1 or 2)",
                label.to_ascii_lowercase(),
                other
            )
        }
    }
}

pub fn verify_receipt_data_with_policy(
    receipt: &VerificationReceipt,
    expected_interface_hash: Option<&str>,
    baseline: Option<&VerificationReceipt>,
    verify_pubkey_hex: Option<&str>,
    require_signature: bool,
) -> Result<(Vec<String>, Option<bool>)> {
    verify_single_receipt_integrity_and_provenance(receipt, "Cryptographic")?;
    let sig_verified =
        verify_receipt_signature_policy(receipt, verify_pubkey_hex, require_signature)?;
    if receipt.forbidden_constructs_found != 0 {
        anyhow::bail!(
            "Receipt certification gate FAILED: forbidden_constructs_found = {} (must be 0)",
            receipt.forbidden_constructs_found
        );
    }
    if let Some(exp_ih) = expected_interface_hash {
        if receipt.interface_hash != exp_ih {
            anyhow::bail!(
                "Project InterfaceHash mismatch: expected {}, got {}",
                exp_ih,
                receipt.interface_hash
            );
        }
    }
    let mut altered_files = Vec::new();
    if let Some(base) = baseline {
        verify_single_receipt_integrity_and_provenance(base, "Baseline")?;
        if base.forbidden_constructs_found != 0 {
            anyhow::bail!(
                "Baseline receipt certification gate FAILED: forbidden_constructs_found = {} (must be 0)",
                base.forbidden_constructs_found
            );
        }
        let mut all_paths: BTreeSet<&String> = receipt.per_file_interfaces.keys().collect();
        all_paths.extend(base.per_file_interfaces.keys());
        for path in all_paths {
            match (
                base.per_file_interfaces.get(path),
                receipt.per_file_interfaces.get(path),
            ) {
                (Some(b_ih), Some(r_ih)) if b_ih == r_ih => {}
                _ => altered_files.push(path.clone()),
            }
        }
        if !altered_files.is_empty() || receipt.interface_hash != base.interface_hash {
            anyhow::bail!(
                "Theorem interface drift detected against baseline receipt (altered files: {:?}, baseline interface_hash={}, current interface_hash={})",
                altered_files,
                base.interface_hash,
                receipt.interface_hash
            );
        }
    }
    Ok((altered_files, sig_verified))
}

/// Verify a receipt JSON file on disk and return a structured [`ReceiptVerificationReport`].
pub fn verify_receipt_file(
    receipt_path: &Path,
    expected_interface_hash: Option<&str>,
    baseline_receipt_path: Option<&Path>,
) -> Result<ReceiptVerificationReport> {
    verify_receipt_file_with_policy(
        receipt_path,
        expected_interface_hash,
        baseline_receipt_path,
        None,
        false,
    )
}

pub fn verify_receipt_file_with_policy(
    receipt_path: &Path,
    expected_interface_hash: Option<&str>,
    baseline_receipt_path: Option<&Path>,
    verify_pubkey_hex: Option<&str>,
    require_signature: bool,
) -> Result<ReceiptVerificationReport> {
    let raw = fs::read_to_string(receipt_path)
        .with_context(|| format!("Failed to read receipt {}", receipt_path.display()))?;
    let parsed: VerificationReceipt = serde_json::from_str(&raw)
        .with_context(|| format!("Invalid receipt JSON in {}", receipt_path.display()))?;

    let baseline_parsed: Option<VerificationReceipt> =
        if let Some(bp) = baseline_receipt_path {
            if bp == receipt_path {
                Some(parsed.clone())
            } else {
                let braw = fs::read_to_string(bp)
                    .with_context(|| format!("Failed to read baseline receipt {}", bp.display()))?;
                Some(serde_json::from_str(&braw).with_context(|| {
                    format!("Invalid baseline receipt JSON in {}", bp.display())
                })?)
            }
        } else {
            None
        };

    let (altered_files, signature_verified) = verify_receipt_data_with_policy(
        &parsed,
        expected_interface_hash,
        baseline_parsed.as_ref(),
        verify_pubkey_hex,
        require_signature,
    )?;

    Ok(ReceiptVerificationReport {
        status: "receipt_verified".to_string(),
        schema_version: parsed.schema_version,
        mode: parsed.mode,
        kernel_engine: parsed.kernel_engine,
        lean_toolchain: parsed.lean_toolchain,
        con_leche_rev: parsed.con_leche_rev,
        interface_hash: parsed.interface_hash,
        action_key: parsed.action_key,
        receipt_blake3: parsed.receipt_blake3,
        files_audited: parsed.files_audited,
        theorem_shards: parsed.theorem_shards,
        forbidden_constructs_found: parsed.forbidden_constructs_found,
        altered_files,
        signature_verified,
    })
}

/// Execute `turbo-lean verify-receipt` without opening SQLite.
pub fn run_verify_receipt_command(
    json: bool,
    receipt: Option<PathBuf>,
    receipt_flag: Option<PathBuf>,
    expected_interface_hash: Option<String>,
    baseline_receipt: Option<PathBuf>,
    verify_pubkey: Option<String>,
    require_signature: bool,
) -> Result<()> {
    let receipt = receipt
        .or(receipt_flag)
        .context("Missing receipt file path (pass `<RECEIPT>` or `--receipt <RECEIPT>`)")?;
    let t0 = Instant::now();
    let report = verify_receipt_file_with_policy(
        &receipt,
        expected_interface_hash.as_deref(),
        baseline_receipt.as_deref(),
        verify_pubkey.as_deref(),
        require_signature,
    )?;

    let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
    if json {
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
                "status": report.status,
                "schema_version": report.schema_version,
                "mode": report.mode,
                "kernel_engine": report.kernel_engine,
                "lean_toolchain": report.lean_toolchain,
                "con_leche_rev": report.con_leche_rev,
                "interface_hash": report.interface_hash,
                "action_key": report.action_key,
                "receipt_blake3": report.receipt_blake3,
                "files_audited": report.files_audited,
                "theorem_shards": report.theorem_shards,
                "forbidden_constructs_found": report.forbidden_constructs_found,
                "altered_files": report.altered_files,
                "signature_verified": report.signature_verified,
                "elapsed_ms": (elapsed_ms * 1000.0).round() / 1000.0
            }))?
        );
    } else {
        println!(
            "[turbo-lean] RECEIPT VERIFIED (schema=v{}, kernel={}, toolchain={}, receipt_blake3={}.., interface_hash={}.., {} files, {:.3} ms)",
            report.schema_version,
            report.kernel_engine.as_deref().unwrap_or("legacy-v1"),
            report.lean_toolchain.as_deref().unwrap_or("legacy-v1"),
            &report.receipt_blake3[..12.min(report.receipt_blake3.len())],
            &report.interface_hash[..12.min(report.interface_hash.len())],
            report.files_audited,
            elapsed_ms
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn active_csimp_digest_is_canonical_and_content_sensitive() {
        let policy = vec![" B.* ".into(), "A.eq".into(), "B.*".into()];
        let entries = vec![("A.eq".into(), "A.slow".into(), "A.fast".into())];
        let digest = compute_active_csimp_digest(&policy, &entries);
        assert_eq!(
            digest,
            compute_active_csimp_digest(
                &["A.eq".into(), "B.*".into()],
                &[entries[0].clone(), entries[0].clone()]
            )
        );
        assert_ne!(digest, compute_active_csimp_digest(&[], &entries));
        for column in 0..3 {
            let mut changed = entries.clone();
            match column {
                0 => changed[0].0.push('x'),
                1 => changed[0].1.push('x'),
                _ => changed[0].2.push('x'),
            }
            assert_ne!(digest, compute_active_csimp_digest(&policy, &changed));
        }
        assert_ne!(
            compute_active_csimp_digest(&["a".into(), "bc".into()], &[]),
            compute_active_csimp_digest(&["ab".into(), "c".into()], &[])
        );
    }

    #[test]
    fn active_csimp_receipt_binding_preserves_legacy_and_rejects_tampering() {
        let receipt = build_verification_receipt("trusted", "ih", "act", 1, 1, 0, BTreeMap::new());
        for schema in [1, 2] {
            let mut rec = receipt.clone();
            if schema == 1 {
                rec.schema_version = 1;
                rec.kernel_engine = None;
                rec.lean_toolchain = None;
                rec.receipt_blake3 = compute_receipt_blake3_v1(
                    1,
                    "trusted",
                    "ih",
                    "act",
                    1,
                    1,
                    0,
                    &rec.per_file_interfaces,
                );
            }
            let legacy_hash = rec.receipt_blake3.clone();
            let json = serde_json::to_value(&rec).unwrap();
            assert!(json.get("active_csimp_digest").is_none());
            let decoded: VerificationReceipt = serde_json::from_value(json).unwrap();
            assert!(verify_receipt_data(&decoded, None, None).is_ok());
            rec.active_csimp_digest = Some(compute_active_csimp_digest(&[], &[]));
            assert!(verify_receipt_data(&rec, None, None).is_err());
            rec.receipt_blake3 =
                bind_active_csimp_digest(&legacy_hash, rec.active_csimp_digest.as_deref());
            assert!(verify_receipt_data(&rec, None, None).is_ok());
            let key = [0x42; 32];
            rec.bind_active_csimp(&[], &[]).unwrap();
            assert!(verify_receipt_data(&rec, None, None).is_ok());
            attach_ed25519_signature(&mut rec, &key);
            let decoded: VerificationReceipt =
                serde_json::from_value(serde_json::to_value(&rec).unwrap()).unwrap();
            assert!(verify_receipt_data_with_policy(&decoded, None, None, None, true).is_ok());
            for digest in [None, Some(String::new()), Some("forged".into())] {
                let mut tampered = rec.clone();
                tampered.active_csimp_digest = digest;
                assert!(verify_receipt_data(&tampered, None, None).is_err());
            }
            rec.bind_active_csimp(&["A.*".into()], &[]).unwrap();
            assert!(rec.ed25519_signature.is_none());
            assert!(verify_receipt_data(&rec, None, None).is_ok());
        }
    }

    #[test]
    fn test_verification_receipt_integrity_and_altered_file_pinpointing() {
        let mut files_v1 = BTreeMap::new();
        files_v1.insert(
            "TurboLean/Reflection.lean".to_string(),
            "hash_refl_v1".to_string(),
        );
        files_v1.insert(
            "TurboLean/Inspector.lean".to_string(),
            "hash_insp_v1".to_string(),
        );

        let rec_v1 = build_verification_receipt(
            "untrusted",
            "proj_ih_v1",
            "act_key_1",
            2,
            15,
            0,
            files_v1.clone(),
        );

        let res_ok = verify_receipt_data(&rec_v1, Some("proj_ih_v1"), Some(&rec_v1));
        assert!(res_ok.is_ok());

        let key = [0x42u8; 32];
        let hmac = compute_receipt_hmac_blake3(&key, &rec_v1.receipt_blake3);
        assert_eq!(hmac.len(), 64);
        let sig = sign_receipt_ed25519(&key, &rec_v1.receipt_blake3);
        assert_eq!(sig.len(), 128);
        assert!(verify_receipt_ed25519(&key, &rec_v1.receipt_blake3, &sig));
        assert!(!verify_receipt_ed25519(
            &key,
            "0000000000000000000000000000000000000000000000000000000000000000",
            &sig
        ));
        let wrong_key = [0x43u8; 32];
        assert!(!verify_receipt_ed25519(
            &wrong_key,
            &rec_v1.receipt_blake3,
            &sig
        ));

        let mut tampered = rec_v1.clone();
        tampered.interface_hash = "forged_hash".to_string();
        let res_tampered = verify_receipt_data(&tampered, None, None);
        assert!(res_tampered.is_err());
        assert!(res_tampered
            .unwrap_err()
            .to_string()
            .contains("BLAKE3 integrity check FAILED"));

        let mut files_v2 = files_v1.clone();
        files_v2.insert(
            "TurboLean/Reflection.lean".to_string(),
            "hash_refl_weakened_spec".to_string(),
        );
        let rec_v2 =
            build_verification_receipt("untrusted", "proj_ih_v2", "act_key_2", 2, 15, 0, files_v2);
        let err_drift = verify_receipt_data(&rec_v2, None, Some(&rec_v1)).unwrap_err();
        let msg = err_drift.to_string();
        assert!(msg.contains("Theorem interface drift detected"));
        assert!(msg.contains("TurboLean/Reflection.lean"));
        assert!(!msg.contains("TurboLean/Inspector.lean"));

        // Ed25519 receipt signing & policy enforcement (`require_signature` + `verify_pubkey`)
        let tmp_rec_path = std::env::temp_dir().join(format!(
            "turbo_lean_signed_receipt_{}.json",
            std::process::id()
        ));
        let mut rec_signed = rec_v1.clone();
        let sk_hex = "4242424242424242424242424242424242424242424242424242424242424242";
        let pk_hex = ed25519_verifying_key_hex(&key);
        let wrong_pk_hex = ed25519_verifying_key_hex(&wrong_key);
        emit_verification_receipt_with_signing_key(
            Some(&tmp_rec_path),
            &mut rec_signed,
            Some(sk_hex),
        )
        .unwrap();
        assert_eq!(rec_signed.signature_alg.as_deref(), Some("ed25519-v1"));
        assert_eq!(rec_signed.ed25519_pubkey.as_deref(), Some(pk_hex.as_str()));

        let rep = verify_receipt_file_with_policy(
            &tmp_rec_path,
            Some("proj_ih_v1"),
            None,
            Some(&pk_hex),
            true,
        )
        .unwrap();
        assert_eq!(rep.signature_verified, Some(true));

        // Wrong pubkey or unsigned receipt with `require_signature=true` must fail closed
        assert!(verify_receipt_file_with_policy(
            &tmp_rec_path,
            None,
            None,
            Some(&wrong_pk_hex),
            true,
        )
        .is_err());
        assert!(verify_receipt_data_with_policy(&rec_v1, None, None, None, true).is_err());
        let _ = fs::remove_file(&tmp_rec_path);
    }

    #[test]
    fn test_receipt_kernel_provenance_domain_separation_and_fail_closed_validation() {
        let mut files = BTreeMap::new();
        files.insert("A.lean".to_string(), "ih_a".to_string());

        let h_none = compute_receipt_blake3(
            CURRENT_RECEIPT_SCHEMA_VERSION,
            "trusted",
            "standard",
            "leanprover/lean4:v4.35.0",
            None,
            None,
            "ih",
            "act",
            1,
            1,
            0,
            &files,
        );
        let h_some_none = compute_receipt_blake3(
            CURRENT_RECEIPT_SCHEMA_VERSION,
            "trusted",
            "standard",
            "leanprover/lean4:v4.35.0",
            Some("none"),
            None,
            "ih",
            "act",
            1,
            1,
            0,
            &files,
        );
        let h_some_empty = compute_receipt_blake3(
            CURRENT_RECEIPT_SCHEMA_VERSION,
            "trusted",
            "standard",
            "leanprover/lean4:v4.35.0",
            Some(""),
            None,
            "ih",
            "act",
            1,
            1,
            0,
            &files,
        );
        assert_ne!(h_none, h_some_none);
        assert_ne!(h_none, h_some_empty);
        assert_ne!(h_some_none, h_some_empty);

        let rec = build_verification_receipt_with_provenance(
            "trusted",
            "standard",
            "leanprover/lean4:v4.35.0",
            None,
            "ih",
            "act",
            1,
            1,
            0,
            files.clone(),
        );
        assert_eq!(rec.schema_version, CURRENT_RECEIPT_SCHEMA_VERSION);
        assert!(verify_receipt_data(&rec, None, None).is_ok());

        for mut tampered in [
            {
                let mut r = rec.clone();
                r.kernel_engine = Some("con-leche".to_string());
                r
            },
            {
                let mut r = rec.clone();
                r.lean_toolchain = Some("leanprover/lean4:v4.36.0".to_string());
                r
            },
            {
                let mut r = rec.clone();
                r.con_leche_rev = Some("deadbeef".to_string());
                r
            },
        ] {
            let err = verify_receipt_data(&tampered, None, None).unwrap_err();
            assert!(
                err.to_string().contains("BLAKE3 integrity check FAILED"),
                "tampered provenance must fail BLAKE3 check: {err}"
            );
            let sk = [0x55u8; 32];
            attach_ed25519_signature(&mut tampered, &sk);
            let err_sig = verify_receipt_data(&tampered, None, None).unwrap_err();
            assert!(err_sig
                .to_string()
                .contains("BLAKE3 integrity check FAILED"));
        }

        let missing_engine = VerificationReceipt {
            kernel_engine: None,
            ..rec.clone()
        };
        assert!(verify_receipt_data(&missing_engine, None, None)
            .unwrap_err()
            .to_string()
            .contains("missing required `kernel_engine`"));

        let missing_tc = VerificationReceipt {
            lean_toolchain: None,
            ..rec.clone()
        };
        assert!(verify_receipt_data(&missing_tc, None, None)
            .unwrap_err()
            .to_string()
            .contains("missing required `lean_toolchain`"));

        let recompute = |mut r: VerificationReceipt| -> VerificationReceipt {
            r.receipt_blake3 = compute_receipt_blake3(
                r.schema_version,
                &r.mode,
                r.kernel_engine.as_deref().unwrap(),
                r.lean_toolchain.as_deref().unwrap(),
                r.con_leche_rev.as_deref(),
                r.active_csimp_digest.as_deref(),
                &r.interface_hash,
                &r.action_key,
                r.files_audited,
                r.theorem_shards,
                r.forbidden_constructs_found,
                &r.per_file_interfaces,
            );
            r
        };

        let invalid_engine = recompute(VerificationReceipt {
            kernel_engine: Some("auto".to_string()),
            ..rec.clone()
        });
        assert!(verify_receipt_data(&invalid_engine, None, None)
            .unwrap_err()
            .to_string()
            .contains("invalid `kernel_engine`"));

        let empty_tc = recompute(VerificationReceipt {
            lean_toolchain: Some("   ".to_string()),
            ..rec.clone()
        });
        assert!(verify_receipt_data(&empty_tc, None, None)
            .unwrap_err()
            .to_string()
            .contains("`lean_toolchain` must be non-empty"));

        let std_with_rev = recompute(VerificationReceipt {
            con_leche_rev: Some("rev123".to_string()),
            ..rec.clone()
        });
        assert!(verify_receipt_data(&std_with_rev, None, None)
            .unwrap_err()
            .to_string()
            .contains("`kernel_engine` is `standard` but `con_leche_rev` is set"));

        let std_with_blank_rev = recompute(VerificationReceipt {
            con_leche_rev: Some("   ".to_string()),
            ..rec.clone()
        });
        assert!(verify_receipt_data(&std_with_blank_rev, None, None)
            .unwrap_err()
            .to_string()
            .contains("`kernel_engine` is `standard` but `con_leche_rev` is set"));

        for eng in ["con-leche", "both"] {
            let missing_rev = recompute(VerificationReceipt {
                kernel_engine: Some(eng.to_string()),
                con_leche_rev: None,
                ..rec.clone()
            });
            assert!(verify_receipt_data(&missing_rev, None, None)
                .unwrap_err()
                .to_string()
                .contains("requires a non-empty `con_leche_rev`"));

            let blank_rev = recompute(VerificationReceipt {
                kernel_engine: Some(eng.to_string()),
                con_leche_rev: Some("   ".to_string()),
                ..rec.clone()
            });
            assert!(verify_receipt_data(&blank_rev, None, None)
                .unwrap_err()
                .to_string()
                .contains("requires a non-empty `con_leche_rev`"));

            let valid_cl = recompute(VerificationReceipt {
                kernel_engine: Some(eng.to_string()),
                con_leche_rev: Some("0123456789abcdef".to_string()),
                ..rec.clone()
            });
            assert!(verify_receipt_data(&valid_cl, None, None).is_ok());
        }
    }

    #[test]
    fn test_legacy_v1_receipt_backward_compatibility_and_cross_version_baseline() {
        let mut files = BTreeMap::new();
        files.insert("TurboLean/Spec.lean".to_string(), "ih_spec_v1".to_string());
        let v1_blake3 =
            compute_receipt_blake3_v1(1, "trusted", "proj_ih", "act_v1", 1, 8, 0, &files);
        let sk = [0x77u8; 32];
        let pk_hex = ed25519_verifying_key_hex(&sk);
        let sig_hex = sign_receipt_ed25519(&sk, &v1_blake3);

        // Exact JSON shape emitted by pre-G1 `schema_version = 1` releases (no provenance keys).
        let legacy_json = serde_json::json!({
            "schema_version": 1,
            "mode": "trusted",
            "interface_hash": "proj_ih",
            "action_key": "act_v1",
            "files_audited": 1,
            "theorem_shards": 8,
            "forbidden_constructs_found": 0,
            "per_file_interfaces": {
                "TurboLean/Spec.lean": "ih_spec_v1"
            },
            "receipt_blake3": v1_blake3,
            "signature_alg": "ed25519-v1",
            "ed25519_pubkey": pk_hex,
            "ed25519_signature": sig_hex
        });
        let legacy_rec: VerificationReceipt = serde_json::from_value(legacy_json).unwrap();
        assert_eq!(legacy_rec.schema_version, 1);
        assert!(legacy_rec.kernel_engine.is_none());
        assert!(legacy_rec.lean_toolchain.is_none());
        assert!(legacy_rec.con_leche_rev.is_none());

        let (altered, sig_ok) = verify_receipt_data_with_policy(
            &legacy_rec,
            Some("proj_ih"),
            Some(&legacy_rec),
            Some(&pk_hex),
            true,
        )
        .unwrap();
        assert!(altered.is_empty());
        assert_eq!(sig_ok, Some(true));

        // Cross-version baseline: new v2 receipt verified against a legacy v1 `--baseline-receipt`.
        let v2_rec = build_verification_receipt_with_provenance(
            "trusted",
            "standard",
            "leanprover/lean4:v4.35.0",
            None,
            "proj_ih",
            "act_v2",
            1,
            8,
            0,
            files.clone(),
        );
        assert!(verify_receipt_data(&v2_rec, Some("proj_ih"), Some(&legacy_rec)).is_ok());
        assert!(verify_receipt_data(&legacy_rec, Some("proj_ih"), Some(&v2_rec)).is_ok());

        // Injecting unauthenticated provenance (even empty strings) into a v1 receipt fails closed.
        for forged_v1 in [
            VerificationReceipt {
                kernel_engine: Some("con-leche".to_string()),
                ..legacy_rec.clone()
            },
            VerificationReceipt {
                kernel_engine: Some(String::new()),
                ..legacy_rec.clone()
            },
            VerificationReceipt {
                lean_toolchain: Some(String::new()),
                ..legacy_rec.clone()
            },
            VerificationReceipt {
                con_leche_rev: Some(String::new()),
                ..legacy_rec.clone()
            },
        ] {
            assert!(verify_receipt_data(&forged_v1, None, None)
                .unwrap_err()
                .to_string()
                .contains("cannot carry unauthenticated kernel provenance"));
        }

        // Unsupported schema_version (e.g. 0 or 3) fails closed.
        let mut bad_ver = v2_rec.clone();
        bad_ver.schema_version = 3;
        assert!(verify_receipt_data(&bad_ver, None, None)
            .unwrap_err()
            .to_string()
            .contains("expected 1 or 2"));
    }
}
