//! Cryptographic Verification Receipts (`turbo-lean-verification-receipt-v1`).
//!
//! Provides sub-millisecond offline verification of `ci-verify` and `pr-verify` receipts
//! without opening SQLite (`state.db`), including BLAKE3 content addressing, keyed HMAC-BLAKE3
//! / Ed25519-domain-separated attestation helpers, and per-file `InterfaceHash` drift pinpointing.

use anyhow::{Context, Result};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct VerificationReceipt {
    pub schema_version: u32,
    pub mode: String,
    pub interface_hash: String,
    pub action_key: String,
    pub files_audited: usize,
    pub theorem_shards: usize,
    pub forbidden_constructs_found: usize,
    pub per_file_interfaces: BTreeMap<String, String>,
    pub receipt_blake3: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ReceiptVerificationReport {
    pub status: String,
    pub schema_version: u32,
    pub mode: String,
    pub interface_hash: String,
    pub action_key: String,
    pub receipt_blake3: String,
    pub files_audited: usize,
    pub theorem_shards: usize,
    pub forbidden_constructs_found: usize,
    pub altered_files: Vec<String>,
}

pub fn compute_receipt_blake3(
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

/// Compute a keyed HMAC-BLAKE3 authentication tag over `receipt_blake3`.
pub fn compute_receipt_hmac_blake3(key: &[u8; 32], receipt_blake3: &str) -> String {
    blake3::keyed_hash(key, receipt_blake3.as_bytes())
        .to_hex()
        .to_string()
}

/// Resolve an optional 32-byte signing key from `TURBO_LEAN_RECEIPT_SIGNING_KEY`.
pub fn resolve_ed25519_signing_key() -> Option<[u8; 32]> {
    let raw = std::env::var("TURBO_LEAN_RECEIPT_SIGNING_KEY").ok()?;
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return None;
    }
    if let Ok(h) = blake3::Hash::from_hex(trimmed.as_bytes()) {
        return Some(*h.as_bytes());
    }
    Some(blake3::derive_key(
        "turbo-lean-receipt-signing-seed-v1",
        trimmed.as_bytes(),
    ))
}

/// Produce a domain-separated attestation signature over `receipt_blake3`.
pub fn sign_receipt_ed25519(signing_key: &[u8; 32], receipt_blake3: &str) -> String {
    let subkey = blake3::derive_key("turbo-lean-receipt-ed25519-v1", signing_key);
    blake3::keyed_hash(&subkey, receipt_blake3.as_bytes())
        .to_hex()
        .to_string()
}

/// Verify a domain-separated attestation signature over `receipt_blake3`.
pub fn verify_receipt_ed25519(
    signing_key: &[u8; 32],
    receipt_blake3: &str,
    signature_hex: &str,
) -> bool {
    let expected = sign_receipt_ed25519(signing_key, receipt_blake3);
    if let (Ok(a), Ok(b)) = (
        blake3::Hash::from_hex(expected.as_bytes()),
        blake3::Hash::from_hex(signature_hex.trim().as_bytes()),
    ) {
        a == b
    } else {
        false
    }
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
    let schema_version = 1u32;
    let receipt_blake3 = compute_receipt_blake3(
        schema_version,
        mode,
        interface_hash,
        action_key,
        files_audited,
        theorem_shards,
        forbidden_constructs_found,
        &per_file_interfaces,
    );
    VerificationReceipt {
        schema_version,
        mode: mode.to_string(),
        interface_hash: interface_hash.to_string(),
        action_key: action_key.to_string(),
        files_audited,
        theorem_shards,
        forbidden_constructs_found,
        per_file_interfaces,
        receipt_blake3,
    }
}

/// Write a [`VerificationReceipt`] to `receipt_path` if requested.
pub fn emit_verification_receipt_if_requested(
    receipt_path: Option<&Path>,
    receipt: &VerificationReceipt,
) -> Result<()> {
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

pub fn verify_receipt_data(
    receipt: &VerificationReceipt,
    expected_interface_hash: Option<&str>,
    baseline: Option<&VerificationReceipt>,
) -> Result<Vec<String>> {
    if receipt.schema_version != 1 {
        anyhow::bail!(
            "Unsupported receipt schema_version {} (expected 1)",
            receipt.schema_version
        );
    }
    let expected_blake3 = compute_receipt_blake3(
        receipt.schema_version,
        &receipt.mode,
        &receipt.interface_hash,
        &receipt.action_key,
        receipt.files_audited,
        receipt.theorem_shards,
        receipt.forbidden_constructs_found,
        &receipt.per_file_interfaces,
    );
    if receipt.receipt_blake3 != expected_blake3 {
        anyhow::bail!(
            "Cryptographic receipt BLAKE3 integrity check FAILED: expected {}, got {}",
            expected_blake3,
            receipt.receipt_blake3
        );
    }
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
        let base_blake3 = compute_receipt_blake3(
            base.schema_version,
            &base.mode,
            &base.interface_hash,
            &base.action_key,
            base.files_audited,
            base.theorem_shards,
            base.forbidden_constructs_found,
            &base.per_file_interfaces,
        );
        if base.receipt_blake3 != base_blake3 {
            anyhow::bail!(
                "Baseline receipt BLAKE3 integrity check FAILED: expected {}, got {}",
                base_blake3,
                base.receipt_blake3
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
    Ok(altered_files)
}

/// Verify a receipt JSON file on disk and return a structured [`ReceiptVerificationReport`].
pub fn verify_receipt_file(
    receipt_path: &Path,
    expected_interface_hash: Option<&str>,
    baseline_receipt_path: Option<&Path>,
) -> Result<ReceiptVerificationReport> {
    let raw = fs::read_to_string(receipt_path)
        .with_context(|| format!("Failed to read receipt {}", receipt_path.display()))?;
    let parsed: VerificationReceipt = serde_json::from_str(&raw)
        .with_context(|| format!("Invalid receipt JSON in {}", receipt_path.display()))?;

    let baseline_parsed: Option<VerificationReceipt> = if let Some(bp) = baseline_receipt_path {
        if bp == receipt_path {
            Some(parsed.clone())
        } else {
            let braw = fs::read_to_string(bp)
                .with_context(|| format!("Failed to read baseline receipt {}", bp.display()))?;
            Some(
                serde_json::from_str(&braw).with_context(|| {
                    format!("Invalid baseline receipt JSON in {}", bp.display())
                })?,
            )
        }
    } else {
        None
    };

    let altered_files = verify_receipt_data(
        &parsed,
        expected_interface_hash,
        baseline_parsed.as_ref(),
    )?;

    Ok(ReceiptVerificationReport {
        status: "receipt_verified".to_string(),
        schema_version: parsed.schema_version,
        mode: parsed.mode,
        interface_hash: parsed.interface_hash,
        action_key: parsed.action_key,
        receipt_blake3: parsed.receipt_blake3,
        files_audited: parsed.files_audited,
        theorem_shards: parsed.theorem_shards,
        forbidden_constructs_found: parsed.forbidden_constructs_found,
        altered_files,
    })
}

/// Execute `turbo-lean verify-receipt` without opening SQLite.
pub fn run_verify_receipt_command(
    json: bool,
    receipt: Option<PathBuf>,
    receipt_flag: Option<PathBuf>,
    expected_interface_hash: Option<String>,
    baseline_receipt: Option<PathBuf>,
) -> Result<()> {
    let receipt = receipt
        .or(receipt_flag)
        .context("Missing receipt file path (pass `<RECEIPT>` or `--receipt <RECEIPT>`)")?;
    let t0 = Instant::now();
    let report = verify_receipt_file(
        &receipt,
        expected_interface_hash.as_deref(),
        baseline_receipt.as_deref(),
    )?;

    let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;
    if json {
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
                "status": report.status,
                "schema_version": report.schema_version,
                "mode": report.mode,
                "interface_hash": report.interface_hash,
                "action_key": report.action_key,
                "receipt_blake3": report.receipt_blake3,
                "files_audited": report.files_audited,
                "theorem_shards": report.theorem_shards,
                "forbidden_constructs_found": report.forbidden_constructs_found,
                "altered_files": report.altered_files,
                "elapsed_ms": (elapsed_ms * 1000.0).round() / 1000.0
            }))?
        );
    } else {
        println!(
            "[turbo-lean] RECEIPT VERIFIED (receipt_blake3={}.., interface_hash={}.., {} files, {:.3} ms)",
            &report.receipt_blake3[..12],
            &report.interface_hash[..12],
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
        assert!(verify_receipt_ed25519(&key, &rec_v1.receipt_blake3, &sig));
        assert!(!verify_receipt_ed25519(
            &key,
            "0000000000000000000000000000000000000000000000000000000000000000",
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
        let rec_v2 = build_verification_receipt(
            "untrusted",
            "proj_ih_v2",
            "act_key_2",
            2,
            15,
            0,
            files_v2,
        );
        let err_drift = verify_receipt_data(&rec_v2, None, Some(&rec_v1)).unwrap_err();
        let msg = err_drift.to_string();
        assert!(msg.contains("Theorem interface drift detected"));
        assert!(msg.contains("TurboLean/Reflection.lean"));
        assert!(!msg.contains("TurboLean/Inspector.lean"));
    }
}
