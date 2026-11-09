use crate::db::{ActionRecord, BlobEntry, TurboStore};
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs;
use std::io::Read;
use std::path::Path;

use super::deferred::write_cached_portable_manifest_with_epoch;

pub(super) fn blob_hash_prefix(hash: &str) -> &str {
    hash.get(..2).unwrap_or("00")
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttestedOleanReplay {
    pub artifact_digest: String,
    pub environment_digest: String,
    pub replay_version: u32,
    pub toolchain_hash: String,
    pub module_name: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackManifest {
    pub format_version: u32,
    pub host_arch: String,
    pub created_at: i64,
    pub actions: Vec<ActionRecord>,
    pub blobs: Vec<PackedBlob>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ed25519_pubkey: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ed25519_signature: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub replayed_oleans: Vec<AttestedOleanReplay>,
}

pub fn decode_hex_fixed<const N: usize>(hex: &str) -> Result<[u8; N]> {
    let s = hex.trim();
    if s.len() != N * 2 {
        anyhow::bail!(
            "Expected {}-hex-char key/signature, got {} chars",
            N * 2,
            s.len()
        );
    }
    let mut out = [0u8; N];
    for (i, chunk) in s.as_bytes().as_chunks::<2>().0.iter().enumerate() {
        let pair = std::str::from_utf8(chunk).context("Invalid UTF-8 in hex")?;
        out[i] = u8::from_str_radix(pair, 16).context("Invalid hex byte")?;
    }
    Ok(out)
}

pub fn encode_hex_bytes(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        use std::fmt::Write as _;
        let _ = write!(&mut s, "{:02x}", b);
    }
    s
}

fn compute_pack_attestation_digest_with_version(
    manifest: &PackManifest,
    include_replayed_oleans_v2: bool,
) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    if include_replayed_oleans_v2 {
        h.update(b"turbo-lean:pack-attestation:v2\n");
    } else {
        h.update(b"turbo-lean:pack-attestation:v1\n");
    }
    h.update(&manifest.format_version.to_le_bytes());
    h.update(manifest.host_arch.as_bytes());
    h.update(b"\n");
    h.update(&manifest.created_at.to_le_bytes());
    let mut acts: Vec<&ActionRecord> = manifest.actions.iter().collect();
    acts.sort_by(|a, b| a.action_key.cmp(&b.action_key));
    for a in acts {
        h.update(b"act:");
        h.update(a.action_key.as_bytes());
        h.update(b"|");
        h.update(a.toolchain_githash.as_bytes());
        h.update(b"|");
        h.update(a.kind.as_bytes());
        h.update(b"|");
        h.update(a.output_manifest_hash.as_bytes());
        h.update(b"\n");
        let mut outs: Vec<&BlobEntry> = a.outputs.iter().collect();
        outs.sort_by(|x, y| x.rel_path.cmp(&y.rel_path));
        for o in outs {
            h.update(b"out:");
            h.update(o.rel_path.as_bytes());
            h.update(b"=");
            h.update(o.blob_hash.as_bytes());
            h.update(b":");
            h.update(&o.size_bytes.to_le_bytes());
            h.update(b"\n");
        }
    }
    let mut blobs: Vec<&PackedBlob> = manifest.blobs.iter().collect();
    blobs.sort_by(|a, b| a.blob_hash.cmp(&b.blob_hash));
    for b in blobs {
        h.update(b"blob:");
        h.update(b.blob_hash.as_bytes());
        h.update(b":");
        h.update(b.kind.as_bytes());
        h.update(b":");
        h.update(&b.size_bytes.to_le_bytes());
        h.update(b"\n");
    }
    if include_replayed_oleans_v2 {
        let mut replayed: Vec<&AttestedOleanReplay> = manifest.replayed_oleans.iter().collect();
        replayed.sort_by(|a, b| {
            a.artifact_digest
                .cmp(&b.artifact_digest)
                .then_with(|| a.environment_digest.cmp(&b.environment_digest))
                .then_with(|| a.replay_version.cmp(&b.replay_version))
                .then_with(|| a.toolchain_hash.cmp(&b.toolchain_hash))
                .then_with(|| a.module_name.cmp(&b.module_name))
        });
        h.update(b"replayed_count:");
        h.update(&(replayed.len() as u64).to_le_bytes());
        h.update(b"\n");
        for r in replayed {
            h.update(b"replayed:");
            for field in [
                r.artifact_digest.as_bytes(),
                r.environment_digest.as_bytes(),
                r.toolchain_hash.as_bytes(),
                r.module_name.as_bytes(),
            ] {
                h.update(&(field.len() as u64).to_le_bytes());
                h.update(field);
            }
            h.update(&r.replay_version.to_le_bytes());
            h.update(b"\n");
        }
    }
    *h.finalize().as_bytes()
}

pub fn compute_pack_attestation_digest(manifest: &PackManifest) -> [u8; 32] {
    compute_pack_attestation_digest_with_version(manifest, true)
}

#[cfg(test)]
#[cfg(test)]
pub(crate) fn compute_pack_attestation_digest_v1_legacy(manifest: &PackManifest) -> [u8; 32] {
    compute_pack_attestation_digest_with_version(manifest, false)
}

pub fn sign_pack_manifest_ed25519(
    manifest: &mut PackManifest,
    signing_key_hex: &str,
) -> Result<()> {
    use ed25519_dalek::{Signer, SigningKey};
    let sk_bytes = decode_hex_fixed::<32>(signing_key_hex)?;
    let signing_key = SigningKey::from_bytes(&sk_bytes);
    let digest = compute_pack_attestation_digest(manifest);
    let sig = signing_key.sign(&digest);
    manifest.ed25519_pubkey = Some(encode_hex_bytes(signing_key.verifying_key().as_bytes()));
    manifest.ed25519_signature = Some(encode_hex_bytes(&sig.to_bytes()));
    Ok(())
}

pub fn verify_pack_manifest_ed25519(
    manifest: &PackManifest,
    trusted_pubkey_hex: &str,
) -> Result<()> {
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};
    let expected_pk_bytes = decode_hex_fixed::<32>(trusted_pubkey_hex)?;
    let vk = VerifyingKey::from_bytes(&expected_pk_bytes)
        .map_err(|_| anyhow::anyhow!("Invalid Ed25519 trusted public key"))?;
    if let Some(ref embedded_pk) = manifest.ed25519_pubkey {
        let emb_bytes = decode_hex_fixed::<32>(embedded_pk)?;
        if emb_bytes != expected_pk_bytes {
            anyhow::bail!("Pack Ed25519 public key mismatch against trusted pubkey");
        }
    }
    let sig_hex = manifest
        .ed25519_signature
        .as_deref()
        .ok_or_else(|| anyhow::anyhow!("Pack manifest is missing Ed25519 attestation signature"))?;
    let sig_bytes = decode_hex_fixed::<64>(sig_hex)?;
    let sig = Signature::from_bytes(&sig_bytes);
    let digest_v2 = compute_pack_attestation_digest_with_version(manifest, true);
    if vk.verify(&digest_v2, &sig).is_ok() {
        return Ok(());
    }
    if manifest.replayed_oleans.is_empty() {
        let digest_v1 = compute_pack_attestation_digest_with_version(manifest, false);
        if vk.verify(&digest_v1, &sig).is_ok() {
            return Ok(());
        }
    }
    anyhow::bail!("Pack Ed25519 attestation signature verification failed")
}

pub fn pack_manifest_has_verified_ed25519(
    manifest: &PackManifest,
    trusted_pubkey: Option<&str>,
) -> bool {
    let env_pk = std::env::var("TURBO_LEAN_PACK_TRUSTED_PUBKEY")
        .ok()
        .filter(|s| !s.trim().is_empty());
    let Some(pk) = trusted_pubkey
        .filter(|s| !s.trim().is_empty())
        .or(env_pk.as_deref())
    else {
        return false;
    };
    verify_pack_manifest_ed25519(manifest, pk).is_ok()
}

pub fn resolve_pack_import_trust_domain(
    manifest: &PackManifest,
    requested_domain: Option<&str>,
    trusted_pubkey: Option<&str>,
    allow_unattested_trusted: bool,
) -> Result<&'static str> {
    let env_pk = std::env::var("TURBO_LEAN_PACK_TRUSTED_PUBKEY")
        .ok()
        .filter(|s| !s.trim().is_empty());
    let pk_opt = trusted_pubkey
        .filter(|s| !s.trim().is_empty())
        .or(env_pk.as_deref());
    let req = requested_domain.map(|s| s.trim()).filter(|s| !s.is_empty());
    let requested_untrusted = match req {
        Some("untrusted") => true,
        Some("trusted") | None => false,
        Some(other) => anyhow::bail!(
            "Unsupported pack import trust_domain `{}` (expected 'trusted' or 'untrusted')",
            other
        ),
    };
    let has_trusted_pubkey = pk_opt.is_some();
    let has_attestation_fields =
        manifest.ed25519_signature.is_some() || manifest.ed25519_pubkey.is_some();
    let mut sig_valid = false;
    let mut sig_err: Option<anyhow::Error> = None;
    if !requested_untrusted {
        if let Some(pk) = pk_opt {
            if req == Some("trusted") || has_attestation_fields {
                match verify_pack_manifest_ed25519(manifest, pk) {
                    Ok(()) => sig_valid = true,
                    Err(e) => sig_err = Some(e),
                }
            }
        }
    }
    let admit_trusted = crate::c_abi::verify_pack_trust_admission(
        requested_untrusted,
        has_trusted_pubkey,
        has_attestation_fields,
        sig_valid,
        allow_unattested_trusted,
    );
    if admit_trusted {
        return Ok("trusted");
    }
    if let Some(e) = sig_err {
        return Err(e);
    }
    if req == Some("trusted") {
        anyhow::bail!(
            "Refusing unattested trusted pack import: pass --trusted-pubkey / TURBO_LEAN_PACK_TRUSTED_PUBKEY or --allow-unattested-trusted"
        );
    }
    Ok("untrusted")
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackedBlob {
    pub blob_hash: String,
    pub kind: String,
    pub size_bytes: u64,
    pub portable: bool,
    pub data_hex_or_base64: Vec<u8>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct DeltaManifest {
    pub action_keys: Vec<String>,
    pub blob_hashes: Vec<String>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ExportDeltaRequest {
    #[serde(default)]
    pub exclude_actions: Vec<String>,
    #[serde(default)]
    pub exclude_blobs: Vec<String>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FastCheckHttpRequest {
    #[serde(default)]
    pub filename: String,
    #[serde(default)]
    pub source: String,
    #[serde(default)]
    pub gpu: bool,
    #[serde(default)]
    pub precomputed_bin_key: String,
    #[serde(default)]
    pub has_main: Option<bool>,
    #[serde(default)]
    pub local_path: String,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CheckShardHttpRequest {
    #[serde(default)]
    pub decl: String,
    #[serde(default)]
    pub shard_key: String,
    #[serde(default)]
    pub shard_source: String,
    #[serde(default)]
    pub interface_hash: String,
    #[serde(default)]
    pub prefix_env_hash: String,
    #[serde(default)]
    pub stmt_hash: String,
    #[serde(default)]
    pub proof_hash: String,
    #[serde(default)]
    pub toolchain: String,
    #[serde(default)]
    pub lean_path: String,
    #[serde(default)]
    pub skip_cas_lock: bool,
    #[serde(default)]
    pub allowed_axioms: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub lean_args: Vec<String>,
    /// Batch requests: the declarations under check (never `sorry`-stub exempt). When empty, every
    /// declaration of `shard_source` is treated as a target.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub targets: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expected_kernel_type_hash: Option<String>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CheckShardBatchItem {
    #[serde(default)]
    pub shard_key: String,
    #[serde(default)]
    pub decl_name: String,
    #[serde(default)]
    pub prefix_env_hash: String,
    #[serde(default)]
    pub stmt_hash: String,
    #[serde(default)]
    pub proof_hash: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expected_kernel_type_hash: Option<String>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CheckShardsBatchRequest {
    #[serde(default)]
    pub items: Vec<CheckShardBatchItem>,
    #[serde(default)]
    pub coalesced_shard_source: String,
    #[serde(default)]
    pub trust_domain: String,
    #[serde(default)]
    pub toolchain: String,
    #[serde(default)]
    pub lean_path: String,
    #[serde(default)]
    pub allowed_axioms: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub lean_args: Vec<String>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CheckShardsBatchResponse {
    pub ok: bool,
    pub verified_count: usize,
    pub cache_hits: usize,
    pub elapsed_ms: f64,
    pub exit_code: i32,
    pub stdout: String,
    pub stderr: String,
    pub error: Option<String>,
    #[serde(default, skip_serializing_if = "std::collections::BTreeMap::is_empty")]
    pub verified_decl_types: std::collections::BTreeMap<String, String>,
}

pub fn is_portable_artifact(kind: &str, rel_path: &str) -> bool {
    // .olean, .ilean, .c, .lean4export, and theorem expr shards are portable across 64-bit x86_64 and aarch64
    // whereas native compiled .o / .so / binaries are architecture-specific.
    if rel_path.ends_with(".o") || rel_path.ends_with(".so") || rel_path.ends_with(".dylib") {
        return false;
    }
    matches!(
        kind,
        "olean" | "ilean" | "c" | "expr_shard" | "lean4export" | "receipt"
    )
}

pub fn get_store_manifest(store: &TurboStore, only_portable: bool) -> Result<DeltaManifest> {
    let mut stmt = store.conn.prepare_cached(
        "SELECT a.action_key, b.blob_hash, b.kind, ao.rel_path
         FROM actions a
         JOIN action_outputs ao ON ao.action_key = a.action_key
         JOIN blobs b ON b.blob_hash = ao.blob_hash
         WHERE a.status = 'completed' AND a.trust_domain = 'trusted' AND b.trust_domain = 'trusted'
         ORDER BY a.action_key ASC",
    )?;
    let rows = stmt.query_map([], |r| {
        Ok((
            r.get::<_, String>(0)?,
            r.get::<_, String>(1)?,
            r.get::<_, String>(2)?,
            r.get::<_, String>(3)?,
        ))
    })?;

    let mut action_keys = Vec::new();
    let mut blob_set = HashSet::new();

    let mut cur_ak: Option<String> = None;
    let mut cur_outputs: Vec<(String, String, String)> = Vec::new();

    let mut flush_action = |ak: String, outputs: &[(String, String, String)]| {
        if outputs.is_empty() {
            return;
        }
        if only_portable
            && outputs
                .iter()
                .any(|(_, kind, rel)| !is_portable_artifact(kind, rel))
        {
            return;
        }
        for (bh, _, _) in outputs {
            if !blob_set.contains(bh) {
                blob_set.insert(bh.clone());
            }
        }
        action_keys.push(ak);
    };

    for row in rows {
        let (ak, bh, kind, rel) = row?;
        if cur_ak.as_deref() != Some(ak.as_str()) {
            if let Some(prev_ak) = cur_ak.take() {
                flush_action(prev_ak, &cur_outputs);
                cur_outputs.clear();
            }
            cur_ak = Some(ak);
        }
        cur_outputs.push((bh, kind, rel));
    }
    if let Some(last_ak) = cur_ak.take() {
        flush_action(last_ak, &cur_outputs);
    }

    let mut blob_hashes: Vec<String> = blob_set.into_iter().collect();
    blob_hashes.sort();
    let dm = DeltaManifest {
        action_keys,
        blob_hashes,
    };
    if only_portable {
        write_cached_portable_manifest_with_epoch(&store.root, &dm, crate::TURBO_LEAN_BUILD_EPOCH);
    }
    Ok(dm)
}

pub(crate) fn is_loopback_http_url(base_url: &str) -> bool {
    let Some(rest) = base_url.strip_prefix("http://") else {
        return false;
    };
    let authority = rest.split('/').next().unwrap_or("");
    let host = match authority.rsplit_once(':') {
        Some((h, port)) if !port.is_empty() && port.bytes().all(|b| b.is_ascii_digit()) => h,
        _ => authority,
    };
    host == "localhost"
        || host == "[::1]"
        || host
            .parse::<std::net::Ipv4Addr>()
            .map(|ip| ip.is_loopback())
            .unwrap_or(false)
}

pub(crate) fn read_u64_le_at(buf: &[u8], offset: usize) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&buf[offset..offset + 8]);
    u64::from_le_bytes(b)
}

pub(crate) fn read_pack_header_from_file(input_path: &Path) -> Option<(u64, [u8; 8], Vec<u8>)> {
    let mut f = fs::File::open(input_path).ok()?;
    let file_len = f.metadata().ok()?.len();
    if file_len < 16 {
        return None;
    }
    let mut prefix = [0u8; 16];
    f.read_exact(&mut prefix).ok()?;
    if &prefix[0..8] != b"TLPK\x00\x00\x00\x02" && &prefix[0..8] != b"TLPK\x00\x00\x00\x03" {
        return None;
    }
    let header_len = read_u64_le_at(&prefix, 8) as usize;
    if 16 + (header_len as u64) > file_len {
        return None;
    }
    let mut header_buf = vec![0u8; header_len];
    f.read_exact(&mut header_buf).ok()?;
    let mut magic = [0u8; 8];
    magic.copy_from_slice(&prefix[0..8]);
    Some((file_len, magic, header_buf))
}

pub(crate) fn set_file_mode_unix(path: &Path, mode: u32) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if let Ok(m) = fs::metadata(path) {
            let mut p = m.permissions();
            p.set_mode(mode);
            let _ = fs::set_permissions(path, p);
        }
    }
    #[cfg(not(unix))]
    let _ = (path, mode);
}
