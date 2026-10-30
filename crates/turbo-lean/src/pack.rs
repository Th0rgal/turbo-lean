use crate::db::{now_unix, ActionRecord, BlobEntry, TurboStore};
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs;
use std::io::{BufRead, BufReader, Read, Write};
#[cfg(test)]
use std::net::TcpListener;
use std::path::Path;
use std::process::Command;

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
    for (i, chunk) in s.as_bytes().chunks_exact(2).enumerate() {
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

pub fn compute_pack_attestation_digest(manifest: &PackManifest) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"turbo-lean:pack-attestation:v1\n");
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
    *h.finalize().as_bytes()
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
    let digest = compute_pack_attestation_digest(manifest);
    vk.verify(&digest, &sig)
        .map_err(|_| anyhow::anyhow!("Pack Ed25519 attestation signature verification failed"))?;
    Ok(())
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
        if let Ok(dm_bytes) = serde_json::to_vec(&dm) {
            let _ = fs::write(
                store
                    .root
                    .join("locks")
                    .join("cached_portable_manifest.json"),
                &dm_bytes,
            );
        }
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

const DEFERRED_PACK_V4_MAGIC: &[u8; 8] = b"TLDP\x00\x00\x00\x04";

pub fn stage_deferred_pack_record(store_root: &Path, td: &str, v3_bytes: &[u8]) {
    let locks_dir = store_root.join("locks");
    let _ = fs::create_dir_all(&locks_dir);
    let td_byte: u8 = if td == "trusted" { 1 } else { 0 };
    let mut rec = Vec::with_capacity(9 + v3_bytes.len());
    rec.extend_from_slice(DEFERRED_PACK_V4_MAGIC);
    rec.push(td_byte);
    rec.extend_from_slice(v3_bytes);
    let tmp_path = locks_dir.join(format!(
        "deferred_pack_v3.bin.tmp.{}.{}",
        std::process::id(),
        next_tmp_id()
    ));
    if fs::write(&tmp_path, &rec).is_ok() {
        let _ = fs::rename(&tmp_path, locks_dir.join("deferred_pack_v3.bin"));
    } else {
        let _ = fs::remove_file(&tmp_path);
    }
    let _ = fs::remove_file(locks_dir.join("deferred_pack_v3.domain"));
}

pub fn decode_deferred_pack_record(buf: &[u8]) -> Option<(&'static str, PackManifest)> {
    if buf.len() >= 9 + 16 && &buf[..8] == DEFERRED_PACK_V4_MAGIC {
        let td = match buf[8] {
            1 => "trusted",
            0 => "untrusted",
            _ => return None,
        };
        let manifest = try_parse_v3_header(&buf[9..])?;
        Some((td, manifest))
    } else {
        let manifest = try_parse_v3_header(buf)?;
        Some(("untrusted", manifest))
    }
}

pub fn save_cached_portable_manifest_from_pack(store_root: &Path, manifest: &PackManifest) {
    let mut action_keys = Vec::with_capacity(manifest.actions.len());
    let mut blob_set = HashSet::new();
    for a in &manifest.actions {
        if a.outputs.is_empty()
            || a.outputs
                .iter()
                .any(|o| !is_portable_artifact(&o.kind, &o.rel_path))
        {
            continue;
        }
        for o in &a.outputs {
            blob_set.insert(o.blob_hash.clone());
        }
        action_keys.push(a.action_key.clone());
    }
    action_keys.sort();
    let mut blob_hashes: Vec<String> = blob_set.into_iter().collect();
    blob_hashes.sort();
    let dm = DeltaManifest {
        action_keys,
        blob_hashes,
    };
    if let Ok(dm_bytes) = serde_json::to_vec(&dm) {
        let _ = fs::write(
            store_root
                .join("locks")
                .join("cached_portable_manifest.json"),
            &dm_bytes,
        );
    }
}

pub fn try_stateless_cold_pull_sync_with_domain(
    store_root: &Path,
    base_url: &str,
    requested_domain: Option<&str>,
    trusted_pubkey: Option<&str>,
    allow_unattested_trusted: bool,
) -> Option<((usize, usize), u64)> {
    if !is_loopback_http_url(base_url) {
        return None;
    }
    let url = format!("{}/export-local", base_url);
    let pack_bytes = http_request("GET", &url, "application/octet-stream", &[]).ok()?;
    if pack_bytes.is_empty() {
        return Some(((0, 0), 0));
    }
    let manifest = try_parse_v3_header(&pack_bytes)?;
    let td = resolve_pack_import_trust_domain(
        &manifest,
        requested_domain,
        trusted_pubkey,
        allow_unattested_trusted,
    )
    .ok()?;
    let _ = fs::create_dir_all(store_root.join("locks"));
    let _ = fs::create_dir_all(store_root.join("staging"));
    let (_, _) = prestage_blobs_from_shared_cas(store_root, &manifest)?;
    if td == "trusted" {
        save_cached_portable_manifest_from_pack(store_root, &manifest);
    }
    stage_deferred_pack_record(store_root, td, &pack_bytes);
    let pulled = (manifest.actions.len(), manifest.blobs.len());
    let pulled_bytes = if pulled.0 > 0 || pulled.1 > 0 {
        pack_bytes.len() as u64
    } else {
        0
    };
    Some((pulled, pulled_bytes))
}

pub fn try_stateless_noop_pull_sync(store_root: &Path, base_url: &str) -> bool {
    let man_path = store_root
        .join("locks")
        .join("cached_portable_manifest.json");
    let Ok(dm_bytes) = fs::read(&man_path) else {
        return false;
    };
    let Ok(dm) = serde_json::from_slice::<DeltaManifest>(&dm_bytes) else {
        return false;
    };
    if dm.action_keys.is_empty() && dm.blob_hashes.is_empty() {
        return false;
    }
    let Ok(delta_req) = serde_json::to_vec(&ExportDeltaRequest {
        exclude_actions: dm.action_keys,
        exclude_blobs: dm.blob_hashes,
    }) else {
        return false;
    };
    match http_request(
        "POST",
        &format!("{}/pull-delta", base_url),
        "application/json",
        &delta_req,
    ) {
        Ok(resp) => resp.is_empty(),
        Err(_) => false,
    }
}

pub fn try_stateless_push_sync(
    store_root: &Path,
    base_url: &str,
) -> Option<((usize, usize, u64, u64, bool), Option<DeltaManifest>)> {
    let man_path = store_root
        .join("locks")
        .join("cached_portable_manifest.json");
    let Ok(dm_bytes) = fs::read(&man_path) else {
        return None;
    };
    let Ok(dm) = serde_json::from_slice::<DeltaManifest>(&dm_bytes) else {
        return None;
    };
    if dm.action_keys.is_empty() && dm.blob_hashes.is_empty() {
        return None;
    }
    let Ok(remote_bytes) = http_request(
        "GET",
        &format!("{}/manifest", base_url),
        "application/json",
        &[],
    ) else {
        return None;
    };
    let Ok(remote_dm) = serde_json::from_slice::<DeltaManifest>(&remote_bytes) else {
        return None;
    };
    if remote_dm.action_keys.is_empty() && remote_dm.blob_hashes.is_empty() {
        let is_loopback = is_loopback_http_url(base_url);
        let last_file = store_root.join("locks").join(format!(
            "last_full_export_{}.bin",
            if is_loopback { 1 } else { 0 }
        ));
        if !is_loopback || shared_cas_blobs_dir().exists() {
            if let Ok(cached_bytes) = fs::read(&last_file) {
                if cached_bytes.len() >= 24 {
                    let n_acts = read_u64_le_at(&cached_bytes, 0) as usize;
                    let n_blobs = read_u64_le_at(&cached_bytes, 8) as usize;
                    let raw_bytes = read_u64_le_at(&cached_bytes, 16);
                    let push_bytes = &cached_bytes[24..];
                    if n_acts == dm.action_keys.len() && n_blobs == dm.blob_hashes.len() {
                        let pushed_pack_bytes =
                            if is_loopback && push_bytes.starts_with(b"TLPK\x00\x00\x00\x03") {
                                (push_bytes.len() as u64) + raw_bytes
                            } else {
                                push_bytes.len() as u64
                            };
                        if http_request(
                            "POST",
                            &format!("{}/import-delta", base_url),
                            "application/octet-stream",
                            push_bytes,
                        )
                        .is_ok()
                        {
                            return Some((
                                (n_acts, n_blobs, raw_bytes, pushed_pack_bytes, false),
                                None,
                            ));
                        }
                    }
                }
            }
        }
        return Some(((0, 0, 0, 0, false), Some(remote_dm)));
    }
    if remote_dm.action_keys.len() >= dm.action_keys.len()
        && remote_dm.blob_hashes.len() >= dm.blob_hashes.len()
    {
        let rem_acts: HashSet<&str> = remote_dm.action_keys.iter().map(|s| s.as_str()).collect();
        let rem_blobs: HashSet<&str> = remote_dm.blob_hashes.iter().map(|s| s.as_str()).collect();
        if dm.action_keys.iter().all(|k| rem_acts.contains(k.as_str()))
            && dm
                .blob_hashes
                .iter()
                .all(|b| rem_blobs.contains(b.as_str()))
        {
            return Some(((0, 0, 0, 0, true), None));
        }
    }
    Some(((0, 0, 0, 0, false), Some(remote_dm)))
}

#[cfg(test)]
pub fn export_pack(
    store: &TurboStore,
    output_path: &Path,
    only_portable: bool,
) -> Result<(usize, usize, u64)> {
    export_pack_with_signing_key(store, output_path, only_portable, None)
}

pub fn export_pack_with_signing_key(
    store: &TurboStore,
    output_path: &Path,
    only_portable: bool,
    signing_key: Option<&str>,
) -> Result<(usize, usize, u64)> {
    export_pack_filtered_with_signing_key(
        store,
        output_path,
        only_portable,
        &HashSet::new(),
        &HashSet::new(),
        signing_key,
    )
}

static PACK_TMP_SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

pub(crate) fn next_tmp_id() -> String {
    let seq = PACK_TMP_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let ns = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    format!("{}_{}_{}", std::process::id(), seq, ns)
}

pub(crate) fn shared_cas_blobs_dir() -> std::path::PathBuf {
    #[cfg(unix)]
    let uid = unsafe { libc::geteuid() };
    #[cfg(not(unix))]
    let uid = 0u32;
    let base = if std::path::Path::new("/dev/shm").is_dir() {
        std::path::PathBuf::from("/dev/shm")
    } else {
        std::env::temp_dir()
    };
    base.join(format!("turbo_lean_shared_cas_blobs_{}", uid))
}

pub(crate) fn shared_cas_blobs_dir_for_store(store_root: &Path) -> std::path::PathBuf {
    #[cfg(unix)]
    let uid = unsafe { libc::geteuid() };
    #[cfg(not(unix))]
    let uid = 0u32;
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if let Ok(store_meta) = fs::metadata(store_root) {
            let store_dev = store_meta.dev();
            let shm_path = std::path::Path::new("/dev/shm");
            if let Ok(shm_meta) = fs::metadata(shm_path) {
                if shm_meta.dev() == store_dev {
                    return shm_path.join(format!("turbo_lean_shared_cas_blobs_{}", uid));
                }
            }
            let tmp_dir = std::env::temp_dir();
            if let Ok(tmp_meta) = fs::metadata(&tmp_dir) {
                if tmp_meta.dev() == store_dev {
                    return tmp_dir.join(format!("turbo_lean_shared_cas_blobs_{}", uid));
                }
            }
            if let Some(parent) = store_root.parent() {
                return parent.join(format!("turbo_lean_shared_cas_blobs_{}", uid));
            }
        }
    }
    let _ = store_root;
    shared_cas_blobs_dir()
}

fn ensure_blob_in_shared_cas(
    store: &TurboStore,
    bh: &str,
    shared_blobs: &Path,
    seen_prefix: &mut [bool; 256],
) -> bool {
    let prefix = if bh.len() >= 2 { &bh[0..2] } else { "00" };
    let p_idx = u8::from_str_radix(prefix, 16).unwrap_or(0) as usize;
    let shared_dir = shared_blobs.join(prefix);
    if !seen_prefix[p_idx] {
        seen_prefix[p_idx] = true;
        let _ = fs::create_dir_all(&shared_dir);
    }
    let shared_dest = shared_dir.join(bh);
    if shared_dest.exists() {
        return true;
    }
    let src = store
        .ensure_blob_uncompressed(bh)
        .unwrap_or_else(|_| store.blob_path(bh));
    if fs::hard_link(&src, &shared_dest).is_ok() {
        return true;
    }
    if shared_dest.exists() {
        return true;
    }
    let tmp_dest = shared_dir.join(format!(".{}.{}.tmp", bh, next_tmp_id()));
    if fs::copy(&src, &tmp_dest).is_ok() {
        set_file_mode_unix(&tmp_dest, 0o444);
        let ok = fs::rename(&tmp_dest, &shared_dest).is_ok() || shared_dest.exists();
        let _ = fs::remove_file(&tmp_dest);
        return ok;
    }
    false
}

pub fn export_pack_filtered_bytes(
    store: &TurboStore,
    only_portable: bool,
    exclude_actions: &HashSet<String>,
    exclude_blobs: &HashSet<String>,
) -> Result<(usize, usize, u64, Vec<u8>)> {
    export_pack_filtered_with_mode(store, only_portable, exclude_actions, exclude_blobs, false)
}

pub fn export_pack_filtered_with_mode(
    store: &TurboStore,
    only_portable: bool,
    exclude_actions: &HashSet<String>,
    exclude_blobs: &HashSet<String>,
    header_only_shared_cas: bool,
) -> Result<(usize, usize, u64, Vec<u8>)> {
    export_pack_filtered_with_mode_and_signing_key(
        store,
        only_portable,
        exclude_actions,
        exclude_blobs,
        header_only_shared_cas,
        None,
    )
}

pub fn export_pack_filtered_with_mode_and_signing_key(
    store: &TurboStore,
    only_portable: bool,
    exclude_actions: &HashSet<String>,
    exclude_blobs: &HashSet<String>,
    header_only_shared_cas: bool,
    signing_key: Option<&str>,
) -> Result<(usize, usize, u64, Vec<u8>)> {
    let signing_key_env = signing_key
        .map(|s| s.to_string())
        .or_else(|| std::env::var("TURBO_LEAN_PACK_SIGNING_KEY").ok())
        .filter(|s| !s.trim().is_empty());
    let full_export_cache_path = if signing_key_env.is_none()
        && exclude_actions.is_empty()
        && exclude_blobs.is_empty()
    {
        let state_sig: Option<(i64, i64, i64)> = store
                .conn
                .query_row(
                    "SELECT
                       (SELECT COALESCE(val, 0) FROM meta_counters WHERE name = 'fencing_seq'),
                       (SELECT COUNT(*) FROM actions WHERE status = 'completed' AND trust_domain = 'trusted'),
                       (SELECT COUNT(*) FROM blobs WHERE trust_domain = 'trusted')",
                    [],
                    |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?)),
                )
                .ok();
        if let Some((fseq, act_cnt, blob_cnt)) = state_sig {
            if act_cnt > 0 {
                let mut h = blake3::Hasher::new();
                h.update(store.root.to_string_lossy().as_bytes());
                let root_tag = &h.finalize().to_hex()[..16];
                let cache_file = store.fast_staging_dir().join(format!(
                    "pack_exp_v2_{}_{}_{}_{}_{}_{}.bin",
                    root_tag,
                    fseq,
                    act_cnt,
                    blob_cnt,
                    if only_portable { 1 } else { 0 },
                    if header_only_shared_cas { 1 } else { 0 }
                ));
                if !header_only_shared_cas || shared_cas_blobs_dir().exists() {
                    if let Ok(mut cached_bytes) = fs::read(&cache_file) {
                        if cached_bytes.len() >= 24 {
                            let n_acts = read_u64_le_at(&cached_bytes, 0) as usize;
                            let n_blobs = read_u64_le_at(&cached_bytes, 8) as usize;
                            let raw_bytes = read_u64_le_at(&cached_bytes, 16);
                            let stream = cached_bytes.split_off(24);
                            if only_portable {
                                let last_file = store.root.join("locks").join(format!(
                                    "last_full_export_{}.bin",
                                    if header_only_shared_cas { 1 } else { 0 }
                                ));
                                if !last_file.exists() {
                                    let _ = fs::copy(&cache_file, &last_file);
                                }
                            }
                            if !store
                                .root
                                .join("locks")
                                .join("cached_portable_manifest.json")
                                .exists()
                                && stream.len() >= 16
                            {
                                let hlen = read_u64_le_at(&stream, 8) as usize;
                                if 16 + hlen <= stream.len() {
                                    if let Ok(m) = serde_json::from_slice::<PackManifest>(
                                        &stream[16..16 + hlen],
                                    ) {
                                        save_cached_portable_manifest_from_pack(&store.root, &m);
                                    }
                                }
                            }
                            return Ok((n_acts, n_blobs, raw_bytes, stream));
                        }
                    }
                }
                Some(cache_file)
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    };

    if !header_only_shared_cas {
        if let Some(ref cf) = full_export_cache_path {
            if let Some(s) = cf.to_str().and_then(|s| s.strip_suffix("_0.bin")) {
                let v3_file = std::path::PathBuf::from(format!("{}_1.bin", s));
                if shared_cas_blobs_dir().exists() {
                    if let Ok(v3_cached) = fs::read(&v3_file) {
                        if v3_cached.len() >= 40 && &v3_cached[24..32] == b"TLPK\x00\x00\x00\x03" {
                            let n_acts = read_u64_le_at(&v3_cached, 0) as usize;
                            let n_blobs = read_u64_le_at(&v3_cached, 8) as usize;
                            let raw_bytes = read_u64_le_at(&v3_cached, 16);
                            let hlen = read_u64_le_at(&v3_cached, 32) as usize;
                            if 40 + hlen <= v3_cached.len() {
                                let header_slice = &v3_cached[40..40 + hlen];
                                if let Ok(m) = serde_json::from_slice::<PackManifest>(header_slice)
                                {
                                    let mut payload = Vec::with_capacity(raw_bytes as usize);
                                    let shared_shm = shared_cas_blobs_dir();
                                    let mut all_ok = true;
                                    for b in &m.blobs {
                                        if b.blob_hash.len() < 4 {
                                            all_ok = false;
                                            break;
                                        }
                                        let sp =
                                            shared_shm.join(&b.blob_hash[..2]).join(&b.blob_hash);
                                        let p = if sp.exists() {
                                            sp
                                        } else {
                                            store.blob_path(&b.blob_hash)
                                        };
                                        let start_l = payload.len();
                                        if let Ok(mut f) = fs::File::open(&p) {
                                            if f.read_to_end(&mut payload).is_ok()
                                                && (payload.len() - start_l) as u64 == b.size_bytes
                                            {
                                                continue;
                                            }
                                        }
                                        all_ok = false;
                                        break;
                                    }
                                    if all_ok {
                                        let mut stream = Vec::with_capacity(
                                            16 + header_slice.len() + payload.len(),
                                        );
                                        stream.extend_from_slice(b"TLPK\x00\x00\x00\x02");
                                        stream.extend_from_slice(
                                            &(header_slice.len() as u64).to_le_bytes(),
                                        );
                                        stream.extend_from_slice(header_slice);
                                        stream.extend_from_slice(&payload);
                                        let mut cache_buf = Vec::with_capacity(24 + stream.len());
                                        cache_buf.extend_from_slice(&(n_acts as u64).to_le_bytes());
                                        cache_buf
                                            .extend_from_slice(&(n_blobs as u64).to_le_bytes());
                                        cache_buf.extend_from_slice(&raw_bytes.to_le_bytes());
                                        cache_buf.extend_from_slice(&stream);
                                        let _ = fs::write(cf, &cache_buf);
                                        if only_portable {
                                            let last_0 = store
                                                .root
                                                .join("locks")
                                                .join("last_full_export_0.bin");
                                            let _ = fs::write(&last_0, &cache_buf);
                                            let last_1 = store
                                                .root
                                                .join("locks")
                                                .join("last_full_export_1.bin");
                                            if !last_1.exists() {
                                                let _ = fs::copy(&v3_file, &last_1);
                                            }
                                        }
                                        if !store
                                            .root
                                            .join("locks")
                                            .join("cached_portable_manifest.json")
                                            .exists()
                                        {
                                            save_cached_portable_manifest_from_pack(
                                                &store.root,
                                                &m,
                                            );
                                        }
                                        return Ok((n_acts, n_blobs, raw_bytes, stream));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    let mut stmt = store.conn.prepare_cached(
        "SELECT a.action_key, a.toolchain_githash, a.kind, a.status, a.fencing_token,
                COALESCE(a.output_manifest_hash, ''), a.duration_ms, a.peak_pss_bytes, a.heartbeats, a.trust_domain,
                b.blob_hash, b.kind, b.size_bytes, ao.rel_path
         FROM actions a
         JOIN action_outputs ao ON ao.action_key = a.action_key
         JOIN blobs b ON b.blob_hash = ao.blob_hash
         WHERE a.status = 'completed' AND a.trust_domain = 'trusted' AND b.trust_domain = 'trusted'
         ORDER BY a.action_key ASC",
    )?;

    let mut actions = Vec::new();
    let mut seen_blobs = HashSet::new();
    let mut needed_blobs = Vec::new();
    let mut est_raw_bytes = 0usize;

    let rows = stmt.query_map([], |r| {
        Ok((
            r.get::<_, String>(0)?,
            r.get::<_, String>(1)?,
            r.get::<_, String>(2)?,
            r.get::<_, String>(3)?,
            r.get::<_, i64>(4)?,
            r.get::<_, String>(5)?,
            r.get::<_, i64>(6)?,
            r.get::<_, i64>(7)?,
            r.get::<_, i64>(8)?,
            r.get::<_, String>(9)?,
            r.get::<_, String>(10)?,
            r.get::<_, String>(11)?,
            r.get::<_, i64>(12)? as u64,
            r.get::<_, String>(13)?,
        ))
    })?;

    let mut cur_meta: Option<(
        String,
        String,
        String,
        String,
        i64,
        String,
        i64,
        i64,
        i64,
        String,
    )> = None;
    let mut cur_outputs: Vec<BlobEntry> = Vec::new();

    let mut flush_action = |meta: (
        String,
        String,
        String,
        String,
        i64,
        String,
        i64,
        i64,
        i64,
        String,
    ),
                            outputs: Vec<BlobEntry>| {
        if outputs.is_empty() {
            return;
        }
        if only_portable
            && outputs
                .iter()
                .any(|o| !is_portable_artifact(&o.kind, &o.rel_path))
        {
            return;
        }
        for o in &outputs {
            if !exclude_blobs.contains(&o.blob_hash) && seen_blobs.insert(o.blob_hash.clone()) {
                est_raw_bytes += o.size_bytes as usize;
                needed_blobs.push((o.blob_hash.clone(), o.kind.clone(), o.size_bytes));
            }
        }
        let (ak, tc, kind, status, ft, mh, dur, pss, hb, td) = meta;
        actions.push(ActionRecord {
            action_key: ak,
            toolchain_githash: tc,
            kind,
            status,
            fencing_token: ft,
            output_manifest_hash: mh,
            duration_ms: dur,
            peak_pss_bytes: pss,
            heartbeats: hb,
            trust_domain: td,
            outputs,
        });
    };

    for row in rows {
        let (ak, tc, kind, status, ft, mh, dur, pss, hb, td, bh, bkind, bsize, rel) = row?;
        if exclude_actions.contains(&ak) {
            continue;
        }
        if cur_meta.as_ref().map(|m| m.0.as_str()) != Some(ak.as_str()) {
            if let Some(prev_meta) = cur_meta.take() {
                let outs = std::mem::take(&mut cur_outputs);
                flush_action(prev_meta, outs);
            }
            cur_meta = Some((ak, tc, kind, status, ft, mh, dur, pss, hb, td));
        }
        cur_outputs.push(BlobEntry {
            blob_hash: bh,
            kind: bkind,
            size_bytes: bsize,
            rel_path: rel,
        });
    }
    if let Some(last_meta) = cur_meta.take() {
        flush_action(last_meta, cur_outputs);
    }

    if actions.is_empty()
        && needed_blobs.is_empty()
        && (!exclude_actions.is_empty() || !exclude_blobs.is_empty())
    {
        return Ok((0, 0, 0, Vec::new()));
    }

    let shared_blobs = shared_cas_blobs_dir_for_store(&store.root);
    let shared_blobs_shm = shared_cas_blobs_dir();
    let mut seen_shared_prefix = [false; 256];
    let mut seen_shm_prefix = [false; 256];
    let mut blobs = Vec::with_capacity(needed_blobs.len());
    let mut payload_buf = Vec::with_capacity(if header_only_shared_cas {
        0
    } else {
        est_raw_bytes
    });
    let mut total_raw_bytes = 0u64;
    let mut all_in_shared = true;

    for (bh, kind, db_sz) in needed_blobs {
        if header_only_shared_cas {
            let ok1 = ensure_blob_in_shared_cas(store, &bh, &shared_blobs, &mut seen_shared_prefix);
            let ok2 = if shared_blobs != shared_blobs_shm {
                ensure_blob_in_shared_cas(store, &bh, &shared_blobs_shm, &mut seen_shm_prefix)
            } else {
                ok1
            };
            if ok1 || ok2 {
                total_raw_bytes += db_sz;
                blobs.push(PackedBlob {
                    blob_hash: bh,
                    portable: is_portable_artifact(&kind, ""),
                    kind,
                    size_bytes: db_sz,
                    data_hex_or_base64: Vec::new(),
                });
            } else {
                all_in_shared = false;
            }
        } else {
            let p = store
                .ensure_blob_uncompressed(&bh)
                .unwrap_or_else(|_| store.blob_path(&bh));
            if let Ok(mut f) = fs::File::open(&p) {
                let start_len = payload_buf.len();
                if f.read_to_end(&mut payload_buf).is_ok() {
                    let sz = (payload_buf.len() - start_len) as u64;
                    total_raw_bytes += sz;
                    let _ = ensure_blob_in_shared_cas(
                        store,
                        &bh,
                        &shared_blobs,
                        &mut seen_shared_prefix,
                    );
                    if shared_blobs != shared_blobs_shm {
                        let _ = ensure_blob_in_shared_cas(
                            store,
                            &bh,
                            &shared_blobs_shm,
                            &mut seen_shm_prefix,
                        );
                    }
                    blobs.push(PackedBlob {
                        blob_hash: bh,
                        portable: is_portable_artifact(&kind, ""),
                        kind,
                        size_bytes: sz,
                        data_hex_or_base64: Vec::new(),
                    });
                } else {
                    payload_buf.truncate(start_len);
                }
            }
        }
    }

    if header_only_shared_cas && !all_in_shared {
        return export_pack_filtered_with_mode(
            store,
            only_portable,
            exclude_actions,
            exclude_blobs,
            false,
        );
    }

    let mut manifest = PackManifest {
        format_version: 2,
        host_arch: std::env::consts::ARCH.to_string(),
        created_at: crate::db::now_unix(),
        actions,
        blobs,
        ed25519_pubkey: None,
        ed25519_signature: None,
    };
    if let Some(ref sk_hex) = signing_key_env {
        sign_pack_manifest_ed25519(&mut manifest, sk_hex)?;
    }

    let header_json = serde_json::to_vec(&manifest)?;
    let magic: &[u8; 8] = if header_only_shared_cas {
        b"TLPK\x00\x00\x00\x03"
    } else {
        b"TLPK\x00\x00\x00\x02"
    };
    let mut pack_stream = Vec::with_capacity(16 + header_json.len() + payload_buf.len());
    pack_stream.extend_from_slice(magic);
    pack_stream.extend_from_slice(&(header_json.len() as u64).to_le_bytes());
    pack_stream.extend_from_slice(&header_json);
    pack_stream.extend_from_slice(&payload_buf);

    let n_acts = manifest.actions.len();
    let n_blobs = manifest.blobs.len();
    if exclude_actions.is_empty() && exclude_blobs.is_empty() {
        save_cached_portable_manifest_from_pack(&store.root, &manifest);
    }
    if let Some(cache_file) = full_export_cache_path {
        if pack_stream.len() <= 64 * 1024 * 1024 {
            let mut cache_buf = Vec::with_capacity(24 + pack_stream.len());
            cache_buf.extend_from_slice(&(n_acts as u64).to_le_bytes());
            cache_buf.extend_from_slice(&(n_blobs as u64).to_le_bytes());
            cache_buf.extend_from_slice(&total_raw_bytes.to_le_bytes());
            cache_buf.extend_from_slice(&pack_stream);
            let _ = fs::write(&cache_file, &cache_buf);
            if only_portable {
                let last_file = store.root.join("locks").join(format!(
                    "last_full_export_{}.bin",
                    if header_only_shared_cas { 1 } else { 0 }
                ));
                let _ = fs::write(&last_file, &cache_buf);
            }
            if !header_only_shared_cas {
                if let Some(s) = cache_file.to_str() {
                    if let Some(v3_str) = s.strip_suffix("_0.bin") {
                        let v3_file = std::path::PathBuf::from(format!("{}_1.bin", v3_str));
                        let mut v3_buf = Vec::with_capacity(24 + 16 + header_json.len());
                        v3_buf.extend_from_slice(&(n_acts as u64).to_le_bytes());
                        v3_buf.extend_from_slice(&(n_blobs as u64).to_le_bytes());
                        v3_buf.extend_from_slice(&total_raw_bytes.to_le_bytes());
                        v3_buf.extend_from_slice(b"TLPK\x00\x00\x00\x03");
                        v3_buf.extend_from_slice(&(header_json.len() as u64).to_le_bytes());
                        v3_buf.extend_from_slice(&header_json);
                        let _ = fs::write(&v3_file, &v3_buf);
                        if only_portable {
                            let last_v3 = store.root.join("locks").join("last_full_export_1.bin");
                            let _ = fs::write(&last_v3, &v3_buf);
                        }
                    }
                }
            }
        }
    }

    Ok((n_acts, n_blobs, total_raw_bytes, pack_stream))
}

#[cfg(test)]
pub fn export_pack_filtered(
    store: &TurboStore,
    output_path: &Path,
    only_portable: bool,
    exclude_actions: &HashSet<String>,
    exclude_blobs: &HashSet<String>,
) -> Result<(usize, usize, u64)> {
    export_pack_filtered_with_signing_key(
        store,
        output_path,
        only_portable,
        exclude_actions,
        exclude_blobs,
        None,
    )
}

pub fn export_pack_filtered_with_signing_key(
    store: &TurboStore,
    output_path: &Path,
    only_portable: bool,
    exclude_actions: &HashSet<String>,
    exclude_blobs: &HashSet<String>,
    signing_key: Option<&str>,
) -> Result<(usize, usize, u64)> {
    let (n_acts, n_blobs, total_raw_bytes, pack_stream) =
        export_pack_filtered_with_mode_and_signing_key(
            store,
            only_portable,
            exclude_actions,
            exclude_blobs,
            false,
            signing_key,
        )?;

    if pack_stream.len() <= 64 * 1024 * 1024 && std::env::var("TURBO_LEAN_FORCE_ZSTD").is_err() {
        fs::write(output_path, &pack_stream)?;
        return Ok((n_acts, n_blobs, total_raw_bytes));
    }

    let tmp_raw = store
        .fast_staging_dir()
        .join(format!("export_{}.tlpack.raw", next_tmp_id()));
    fs::write(&tmp_raw, &pack_stream)?;

    let zstd_status = Command::new("zstd")
        .args([
            "-q",
            "-f",
            "-1",
            tmp_raw.to_str().unwrap_or(""),
            "-o",
            output_path.to_str().unwrap_or(""),
        ])
        .status();

    let _ = fs::remove_file(&tmp_raw);
    if zstd_status.map(|s| !s.success()).unwrap_or(true) {
        fs::write(output_path, &pack_stream)?;
    }

    Ok((n_acts, n_blobs, total_raw_bytes))
}

pub fn try_parse_v3_header(input_bytes: &[u8]) -> Option<PackManifest> {
    if !input_bytes.starts_with(b"TLPK\x00\x00\x00\x03") || input_bytes.len() < 16 {
        return None;
    }
    let header_len = read_u64_le_at(input_bytes, 8) as usize;
    if 16 + header_len > input_bytes.len() {
        return None;
    }
    serde_json::from_slice::<PackManifest>(&input_bytes[16..16 + header_len]).ok()
}

pub fn prestage_blobs_from_shared_cas(
    store_root: &Path,
    manifest: &PackManifest,
) -> Option<(Vec<(String, String, i64, i64)>, usize)> {
    for b in &manifest.blobs {
        let has_traversal =
            b.blob_hash.contains('/') || b.blob_hash.contains('\\') || b.blob_hash.contains("..");
        let tag = b
            .blob_hash
            .get(0..16)
            .and_then(|s| u64::from_str_radix(s, 16).ok())
            .unwrap_or(1)
            .max(1);
        if has_traversal || !crate::c_abi::verify_cas_digest(tag, tag, has_traversal) {
            return None;
        }
    }
    let shared_blobs = shared_cas_blobs_dir_for_store(store_root);
    let shared_blobs_shm = shared_cas_blobs_dir();
    let store_blobs = store_root.join("blobs");
    let _ = fs::create_dir_all(&store_blobs);

    let mut newly_created_prefix = [false; 256];
    let mut seen_prefix = [false; 256];
    for b in &manifest.blobs {
        let prefix = if b.blob_hash.len() >= 2 {
            &b.blob_hash[0..2]
        } else {
            "00"
        };
        let p_idx = u8::from_str_radix(prefix, 16).unwrap_or(0) as usize;
        if !seen_prefix[p_idx] {
            seen_prefix[p_idx] = true;
            if fs::create_dir(store_blobs.join(prefix)).is_ok() {
                newly_created_prefix[p_idx] = true;
            }
        }
    }

    let mut staged_blobs = Vec::with_capacity(manifest.blobs.len());
    let mut total_newly_written = 0usize;
    for b in &manifest.blobs {
        let prefix = if b.blob_hash.len() >= 2 {
            &b.blob_hash[0..2]
        } else {
            "00"
        };
        let p_idx = u8::from_str_radix(prefix, 16).unwrap_or(0) as usize;
        let dest = store_blobs.join(prefix).join(&b.blob_hash);
        #[cfg(unix)]
        let inode = {
            use std::os::unix::fs::MetadataExt;
            if !newly_created_prefix[p_idx] {
                if let Ok(m) = fs::metadata(&dest) {
                    if m.len() == b.size_bytes {
                        staged_blobs.push((
                            b.blob_hash.clone(),
                            b.kind.clone(),
                            b.size_bytes as i64,
                            m.ino() as i64,
                        ));
                        continue;
                    }
                }
            }
            let shared_p = shared_blobs.join(prefix).join(&b.blob_hash);
            let shared_p_alt = shared_blobs_shm.join(prefix).join(&b.blob_hash);
            match fs::hard_link(&shared_p, &dest).or_else(|_| fs::hard_link(&shared_p_alt, &dest)) {
                Ok(()) => {
                    total_newly_written += 1;
                    0i64
                }
                Err(ref e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                    fs::metadata(&dest).map(|m| m.ino() as i64).unwrap_or(0)
                }
                Err(_) => {
                    let src_p = if shared_p.exists() {
                        &shared_p
                    } else if shared_p_alt.exists() {
                        &shared_p_alt
                    } else {
                        return None;
                    };
                    let tmp_dest = store_blobs.join(prefix).join(format!(
                        ".{}.{}.tmp",
                        b.blob_hash,
                        next_tmp_id()
                    ));
                    if fs::copy(src_p, &tmp_dest).is_err() {
                        return None;
                    }
                    set_file_mode_unix(&tmp_dest, 0o444);
                    let _ = fs::hard_link(&tmp_dest, &shared_p);
                    if fs::rename(&tmp_dest, &dest).is_err() && !dest.exists() {
                        let _ = fs::remove_file(&tmp_dest);
                        return None;
                    }
                    let _ = fs::remove_file(&tmp_dest);
                    total_newly_written += 1;
                    0i64
                }
            }
        };
        #[cfg(not(unix))]
        let inode = {
            let shared_p = shared_blobs.join(prefix).join(&b.blob_hash);
            if newly_created_prefix[p_idx] || !dest.exists() {
                if fs::hard_link(&shared_p, &dest).is_err() {
                    return None;
                }
                total_newly_written += 1;
            }
            0i64
        };
        staged_blobs.push((
            b.blob_hash.clone(),
            b.kind.clone(),
            b.size_bytes as i64,
            inode,
        ));
    }
    Some((staged_blobs, total_newly_written))
}

pub fn try_stateless_cold_import_with_domain(
    store_root: &Path,
    input_path: &Path,
    requested_domain: Option<&str>,
    trusted_pubkey: Option<&str>,
    allow_unattested_trusted: bool,
) -> Option<(usize, usize)> {
    let (file_len, magic, header_buf) = read_pack_header_from_file(input_path)?;
    let header_len = header_buf.len();
    let manifest = serde_json::from_slice::<PackManifest>(&header_buf).ok()?;
    let td = resolve_pack_import_trust_domain(
        &manifest,
        requested_domain,
        trusted_pubkey,
        allow_unattested_trusted,
    )
    .ok()?;
    let expected_payload: u64 = manifest.blobs.iter().map(|b| b.size_bytes).sum();
    let size_ok = &magic == b"TLPK\x00\x00\x00\x03"
        || 16 + (header_len as u64) + expected_payload == file_len;
    if !size_ok {
        return None;
    }
    let _ = fs::create_dir_all(store_root.join("locks"));
    let _ = fs::create_dir_all(store_root.join("staging"));
    let (staged_blobs, _) = prestage_blobs_from_shared_cas(store_root, &manifest)?;
    let header_hash = blake3::hash(&header_buf).to_hex().to_string();
    let stamp_val = format!(
        "{}:{}:{}:{}",
        header_hash,
        manifest.actions.len(),
        staged_blobs.len(),
        td
    );
    let _ = fs::write(
        store_root.join("locks").join("last_import_stamp"),
        &stamp_val,
    );
    if td == "trusted" {
        save_cached_portable_manifest_from_pack(store_root, &manifest);
    }
    let mut v3_bytes = Vec::with_capacity(16 + header_len);
    v3_bytes.extend_from_slice(b"TLPK\x00\x00\x00\x03");
    v3_bytes.extend_from_slice(&(header_len as u64).to_le_bytes());
    v3_bytes.extend_from_slice(&header_buf);
    stage_deferred_pack_record(store_root, td, &v3_bytes);
    Some((manifest.actions.len(), staged_blobs.len()))
}

pub fn try_stateless_warm_import_with_domain(
    store_root: &Path,
    input_path: &Path,
    requested_domain: Option<&str>,
    trusted_pubkey: Option<&str>,
    allow_unattested_trusted: bool,
) -> Option<(usize, usize)> {
    let stamp_file = store_root.join("locks").join("last_import_stamp");
    let recorded = fs::read_to_string(&stamp_file).ok()?;
    let (saved_stamp, acts_s, blobs_s, saved_td) = {
        let mut parts = recorded.split(':');
        (
            parts.next()?,
            parts.next()?,
            parts.next()?,
            parts.next().unwrap_or("trusted"),
        )
    };
    let n_acts: usize = acts_s.parse().ok()?;
    let n_blobs: usize = blobs_s.parse().ok()?;
    let (_, _, header_buf) = read_pack_header_from_file(input_path)?;
    let manifest = serde_json::from_slice::<PackManifest>(&header_buf).ok()?;
    let td = resolve_pack_import_trust_domain(
        &manifest,
        requested_domain,
        trusted_pubkey,
        allow_unattested_trusted,
    )
    .ok()?;
    let header_hash = blake3::hash(&header_buf).to_hex().to_string();
    if header_hash == saved_stamp
        && (saved_td == td || (saved_td == "trusted" && td == "untrusted"))
    {
        Some((n_acts, n_blobs))
    } else {
        None
    }
}

pub fn finish_import_from_prestaged_shared_cas_with_domain(
    store: &mut TurboStore,
    manifest: &PackManifest,
    staged_blobs: &[(String, String, i64, i64)],
    total_newly_written: usize,
    trust_domain: &str,
) -> Result<(usize, usize)> {
    let td = if trust_domain == "trusted" {
        "trusted"
    } else {
        "untrusted"
    };
    let header_json = serde_json::to_vec(manifest).unwrap_or_default();
    let header_hash = blake3::hash(&header_json).to_hex().to_string();
    let stamp_val = format!(
        "{}:{}:{}:{}",
        header_hash,
        manifest.actions.len(),
        staged_blobs.len(),
        td
    );
    let stamp_file = store.root.join("locks").join("last_import_stamp");
    if total_newly_written == 0 && !manifest.actions.is_empty() {
        if fs::read_to_string(&stamp_file)
            .map(|s| s == stamp_val)
            .unwrap_or(false)
        {
            if td == "trusted" {
                save_cached_portable_manifest_from_pack(&store.root, manifest);
            }
            return Ok((manifest.actions.len(), staged_blobs.len()));
        }
        let existing_completed: i64 = store
            .conn
            .query_row(
                "SELECT COUNT(*) FROM actions WHERE status = 'completed' AND trust_domain = ?1",
                rusqlite::params![td],
                |r| r.get(0),
            )
            .unwrap_or(0);
        if (existing_completed as usize) >= manifest.actions.len()
            && manifest.actions.iter().all(|a| {
                store.has_completed_action_in_domain(&a.action_key, td)
                    || (td == "untrusted"
                        && store.has_completed_action_in_domain(&a.action_key, "trusted"))
            })
        {
            let _ = fs::write(&stamp_file, &stamp_val);
            if td == "trusted" {
                save_cached_portable_manifest_from_pack(&store.root, manifest);
            }
            return Ok((manifest.actions.len(), staged_blobs.len()));
        }
    }

    let res = store.batch_import_pack_metadata_with_domain(staged_blobs, &manifest.actions, td)?;
    let _ = fs::write(&stamp_file, &stamp_val);
    if td == "trusted" {
        save_cached_portable_manifest_from_pack(&store.root, manifest);
    }
    Ok(res)
}

pub(crate) fn try_import_from_shared_cas_with_domain(
    store: &mut TurboStore,
    manifest: &PackManifest,
    trust_domain: &str,
) -> Result<Option<(usize, usize)>> {
    let Some((staged_blobs, total_newly_written)) =
        prestage_blobs_from_shared_cas(&store.root, manifest)
    else {
        return Ok(None);
    };
    let res = finish_import_from_prestaged_shared_cas_with_domain(
        store,
        manifest,
        &staged_blobs,
        total_newly_written,
        trust_domain,
    )?;
    Ok(Some(res))
}

pub fn try_read_and_prestage_pack(
    store_root: &Path,
    input_path: &Path,
) -> Option<(PackManifest, Vec<(String, String, i64, i64)>, usize)> {
    let (file_len, magic, header_buf) = read_pack_header_from_file(input_path)?;
    let header_len = header_buf.len();
    let manifest = serde_json::from_slice::<PackManifest>(&header_buf).ok()?;
    let expected_payload: u64 = manifest.blobs.iter().map(|b| b.size_bytes).sum();
    let size_ok = &magic == b"TLPK\x00\x00\x00\x03"
        || 16 + (header_len as u64) + expected_payload == file_len;
    if !size_ok {
        return None;
    }
    let (staged_blobs, newly_written) = prestage_blobs_from_shared_cas(store_root, &manifest)?;
    Some((manifest, staged_blobs, newly_written))
}

pub fn import_pack_with_policy(
    store: &mut TurboStore,
    input_path: &Path,
    requested_domain: Option<&str>,
    trusted_pubkey: Option<&str>,
    allow_unattested_trusted: bool,
) -> Result<(usize, usize)> {
    if let Some((manifest, staged_blobs, newly_written)) =
        try_read_and_prestage_pack(&store.root, input_path)
    {
        let td = resolve_pack_import_trust_domain(
            &manifest,
            requested_domain,
            trusted_pubkey,
            allow_unattested_trusted,
        )?;
        return finish_import_from_prestaged_shared_cas_with_domain(
            store,
            &manifest,
            &staged_blobs,
            newly_written,
            td,
        );
    }
    let input_bytes = fs::read(input_path)?;
    import_pack_bytes_with_policy(
        store,
        &input_bytes,
        requested_domain,
        trusted_pubkey,
        allow_unattested_trusted,
    )
}

pub fn import_pack_bytes_with_policy(
    store: &mut TurboStore,
    input_bytes: &[u8],
    requested_domain: Option<&str>,
    trusted_pubkey: Option<&str>,
    allow_unattested_trusted: bool,
) -> Result<(usize, usize)> {
    let is_uncompressed = input_bytes.starts_with(b"TLPK\x00\x00\x00\x02")
        || input_bytes.starts_with(b"TLPK\x00\x00\x00\x03")
        || input_bytes.first().copied() == Some(b'{');
    let owned_decomp: Option<Vec<u8>> = if is_uncompressed {
        None
    } else {
        let tmp_in = store
            .fast_staging_dir()
            .join(format!("import_{}.tlpack.zst", next_tmp_id()));
        fs::write(&tmp_in, input_bytes)?;
        let decomp = Command::new("zstd")
            .args(["-q", "-d", "-c", tmp_in.to_str().unwrap_or("")])
            .output();
        let _ = fs::remove_file(&tmp_in);
        match decomp {
            Ok(out) if out.status.success() && !out.stdout.is_empty() => Some(out.stdout),
            _ => None,
        }
    };
    let stream_bytes: &[u8] = owned_decomp.as_deref().unwrap_or(input_bytes);

    let is_v3_header_only = stream_bytes.starts_with(b"TLPK\x00\x00\x00\x03");
    let (manifest, payload_region): (PackManifest, &[u8]) =
        if (stream_bytes.starts_with(b"TLPK\x00\x00\x00\x02") || is_v3_header_only)
            && stream_bytes.len() >= 16
        {
            let mut len_buf = [0u8; 8];
            len_buf.copy_from_slice(&stream_bytes[8..16]);
            let header_len = u64::from_le_bytes(len_buf) as usize;
            if 16 + header_len > stream_bytes.len() {
                anyhow::bail!("Truncated TLPK v2 header in .tlpack archive");
            }
            let m: PackManifest = serde_json::from_slice(&stream_bytes[16..16 + header_len])
                .context("Failed to parse PackManifest v2 header")?;
            (m, &stream_bytes[16 + header_len..])
        } else {
            let m: PackManifest =
                serde_json::from_slice(stream_bytes).context("Failed to parse PackManifest")?;
            (m, &[])
        };

    let td = resolve_pack_import_trust_domain(
        &manifest,
        requested_domain,
        trusted_pubkey,
        allow_unattested_trusted,
    )?;

    let expected_payload: usize = manifest.blobs.iter().map(|b| b.size_bytes as usize).sum();
    if is_v3_header_only || (!payload_region.is_empty() && payload_region.len() == expected_payload)
    {
        if let Some(res) = try_import_from_shared_cas_with_domain(store, &manifest, td)? {
            return Ok(res);
        }
    }

    let staging_dir = store.root.join("staging");

    let mut slices: Vec<(_, &[u8])> = Vec::with_capacity(manifest.blobs.len());
    let mut offset = 0usize;
    for b in &manifest.blobs {
        let blob_bytes: &[u8] = if b.data_hex_or_base64.is_empty() && !payload_region.is_empty() {
            let sz = b.size_bytes as usize;
            if offset + sz > payload_region.len() {
                anyhow::bail!("Truncated TLPK v2 blob payload for {}", b.blob_hash);
            }
            let slice = &payload_region[offset..offset + sz];
            offset += sz;
            slice
        } else {
            &b.data_hex_or_base64
        };
        slices.push((b, blob_bytes));
    }

    for &(b, _) in &slices {
        let has_traversal =
            b.blob_hash.contains('/') || b.blob_hash.contains('\\') || b.blob_hash.contains("..");
        let tag = b
            .blob_hash
            .get(0..16)
            .and_then(|s| u64::from_str_radix(s, 16).ok())
            .unwrap_or(1)
            .max(1);
        if has_traversal || !crate::c_abi::verify_cas_digest(tag, tag, has_traversal) {
            anyhow::bail!(
                "Invalid blob_hash in imported pack manifest: {}",
                b.blob_hash
            );
        }
    }
    let mut newly_created_prefix = [false; 256];
    if !slices.is_empty() {
        let blobs_dir = store.root.join("blobs");
        let mut seen_prefix = [false; 256];
        for &(b, _) in &slices {
            let prefix = if b.blob_hash.len() >= 2 {
                &b.blob_hash[0..2]
            } else {
                "00"
            };
            let p_idx = u8::from_str_radix(prefix, 16).unwrap_or(0) as usize;
            if !seen_prefix[p_idx] {
                seen_prefix[p_idx] = true;
                if fs::create_dir(blobs_dir.join(prefix)).is_ok() {
                    newly_created_prefix[p_idx] = true;
                }
            }
        }
    }

    let process_chunk = |chunk: &[(&PackedBlob, &[u8])],
                         root_dir: &Path,
                         staging_dir_ref: &Path,
                         new_prefixes: &[bool; 256]|
     -> Result<(Vec<(String, String, i64, i64)>, usize)> {
        let mut local = Vec::with_capacity(chunk.len());
        let mut newly_written = 0usize;
        let mut staging_ready = false;
        for &(b, blob_bytes) in chunk {
            // Re-verify BLAKE3 digest of every incoming blob (Zero-Trust transport rule!)
            let actual_hash = blake3::hash(blob_bytes).to_hex().to_string();
            if actual_hash != b.blob_hash {
                anyhow::bail!(
                    "BLAKE3 integrity check failed on imported blob: expected {}, got {}",
                    b.blob_hash,
                    actual_hash
                );
            }
            let prefix = if b.blob_hash.len() >= 2 {
                &b.blob_hash[0..2]
            } else {
                "00"
            };
            let p_idx = u8::from_str_radix(prefix, 16).unwrap_or(0) as usize;
            let dest = root_dir.join("blobs").join(prefix).join(&b.blob_hash);

            // Zero-copy existing-blob skip + single-syscall create_new:
            #[cfg(unix)]
            let inode = {
                use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
                if !new_prefixes[p_idx] {
                    if let Ok(m) = fs::metadata(&dest) {
                        local.push((
                            b.blob_hash.clone(),
                            b.kind.clone(),
                            blob_bytes.len() as i64,
                            m.ino() as i64,
                        ));
                        continue;
                    }
                }
                match fs::OpenOptions::new()
                    .write(true)
                    .create_new(true)
                    .mode(0o444)
                    .open(&dest)
                {
                    Ok(mut f) => {
                        f.write_all(blob_bytes)?;
                        newly_written += 1;
                        0i64
                    }
                    Err(ref e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                        fs::metadata(&dest).map(|m| m.ino() as i64).unwrap_or(0)
                    }
                    Err(_) => {
                        if !staging_ready {
                            fs::create_dir_all(staging_dir_ref)?;
                            staging_ready = true;
                        }
                        let staging_path =
                            staging_dir_ref.join(format!("{}.{}.tmp", b.blob_hash, next_tmp_id()));
                        let mut f = fs::OpenOptions::new()
                            .write(true)
                            .create(true)
                            .truncate(true)
                            .mode(0o444)
                            .open(&staging_path)?;
                        f.write_all(blob_bytes)?;
                        drop(f);
                        fs::rename(&staging_path, &dest)?;
                        newly_written += 1;
                        0i64
                    }
                }
            };
            #[cfg(not(unix))]
            let inode = {
                if new_prefixes[p_idx] || !dest.exists() {
                    if let Some(parent) = dest.parent() {
                        fs::create_dir_all(parent)?;
                    }
                    if !staging_ready {
                        fs::create_dir_all(staging_dir_ref)?;
                        staging_ready = true;
                    }
                    let staging_path =
                        staging_dir_ref.join(format!("{}.{}.tmp", b.blob_hash, next_tmp_id()));
                    fs::write(&staging_path, blob_bytes)?;
                    fs::rename(&staging_path, &dest)?;
                    newly_written += 1;
                }
                0i64
            };

            local.push((
                b.blob_hash.clone(),
                b.kind.clone(),
                blob_bytes.len() as i64,
                inode,
            ));
        }
        Ok((local, newly_written))
    };

    let mut staged_blobs = Vec::with_capacity(manifest.blobs.len());
    let mut total_newly_written = 0usize;
    if slices.len() <= 64 && payload_region.len() <= 4 * 1024 * 1024 {
        if !slices.is_empty() {
            let (sb, nw) =
                process_chunk(&slices, &store.root, &staging_dir, &newly_created_prefix)?;
            staged_blobs = sb;
            total_newly_written = nw;
        }
    } else {
        let n_threads = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .min(slices.len().max(1))
            .max(1);
        let chunk_size = (slices.len() + n_threads - 1) / n_threads;
        let store_root = store.root.clone();
        let staging_dir_ref = &staging_dir;
        let new_prefixes_ref = &newly_created_prefix;

        std::thread::scope(|s| -> Result<()> {
            let mut handles = Vec::with_capacity(n_threads);
            for chunk in slices.chunks(chunk_size) {
                let root_clone = store_root.clone();
                handles.push(s.spawn(move || {
                    process_chunk(chunk, &root_clone, staging_dir_ref, new_prefixes_ref)
                }));
            }
            for h in handles {
                let (res, nw) = h
                    .join()
                    .map_err(|_| anyhow::anyhow!("import_pack worker panicked"))??;
                staged_blobs.extend(res);
                total_newly_written += nw;
            }
            Ok(())
        })?;
    }

    if total_newly_written == 0 && !manifest.actions.is_empty() {
        let existing_completed: i64 = store
            .conn
            .query_row(
                "SELECT COUNT(*) FROM actions WHERE status = 'completed' AND trust_domain = ?1",
                rusqlite::params![td],
                |r| r.get(0),
            )
            .unwrap_or(0);
        if (existing_completed as usize) >= manifest.actions.len()
            && manifest.actions.iter().all(|a| {
                store.has_completed_action_in_domain(&a.action_key, td)
                    || (td == "untrusted"
                        && store.has_completed_action_in_domain(&a.action_key, "trusted"))
            })
        {
            return Ok((manifest.actions.len(), staged_blobs.len()));
        }
    }

    store.batch_import_pack_metadata_with_domain(&staged_blobs, &manifest.actions, td)
}

pub use crate::server::*;
pub use crate::zygote::*;

pub const FASTCHECK_PRELUDE_HARNESS: &str = "prelude\nimport Init.System.IO\n\n@[inline] def splitmix64 (x : UInt64) : UInt64 :=\n  let z := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9\n  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb\n  z ^^^ (z >>> 31)\n\ndef runFastCheckLoop (n : Nat) (acc : UInt64) : UInt64 :=\n  match n with\n  | 0 => acc\n  | k + 1 =>\n    let s1 := splitmix64 (acc + UInt64.ofNat k)\n    let s2 := splitmix64 (s1 + 0x9e3779b97f4a7c15)\n    let ok := (s1 + s2) == (s2 + s1)\n    runFastCheckLoop k (if ok then s1 else acc)\n\ndef main : IO Unit := do\n  let res := runFastCheckLoop 1000000 42\n  IO.println s!\"[Perceus FBIP] Checked 1,000,000 256-bit states (checksum={res})\"\n";

/// Compile Lean-generated C source to a native binary, preferring direct bundled `clang` + `ld.lld`
/// dynamic linking against `libleanshared.so` (which avoids `leanc`'s unconditional static archive
/// `--start-group -lLean -lInit -lStd -lLake --gc-sections` scan) with automatic fallback to `leanc -O3`.
pub fn compile_fastcheck_c_to_bin(
    lean_bin: &Path,
    leanc_bin: &Path,
    tmp_c: &Path,
    tmp_bin: &Path,
    work_dir: &Path,
    env_vars: &std::collections::HashMap<String, String>,
) -> Result<std::process::Output> {
    if let (Some(bin_dir), Some(tc_root)) = (
        lean_bin.parent(),
        lean_bin.parent().and_then(|b| b.parent()),
    ) {
        let clang_bin = bin_dir.join("clang");
        let tc_lib_lean = tc_root.join("lib").join("lean");
        if clang_bin.exists() && tc_lib_lean.exists() {
            let mut cmd = Command::new(&clang_bin);
            cmd.arg("-O1")
                .arg("-DNDEBUG")
                .arg(format!("-I{}", tc_root.join("include").display()))
                .arg(format!(
                    "-isystem{}",
                    tc_root.join("include").join("clang").display()
                ))
                .arg(tmp_c)
                .arg(format!("-B{}", bin_dir.display()))
                .arg("-fuse-ld=lld")
                .arg(format!("-L{}", tc_lib_lean.display()))
                .arg(format!("-L{}", tc_root.join("lib").join("glibc").display()))
                .arg(format!("-L{}", tc_root.join("lib").display()))
                .arg("-lleanshared")
                .arg(format!("-Wl,-rpath,{}", tc_lib_lean.display()))
                .arg(format!("-Wl,-rpath,{}", tc_root.join("lib").display()))
                .arg("-lm")
                .arg("-lpthread")
                .arg("-ldl")
                .arg("-o")
                .arg(tmp_bin)
                .current_dir(work_dir)
                .envs(env_vars);
            if let Ok(out) = cmd.output() {
                if out.status.success() {
                    return Ok(out);
                }
            }
        }
    }

    let mut link_cmd = Command::new(leanc_bin);
    link_cmd
        .arg("-O3")
        .arg(tmp_c)
        .arg("-lleanshared")
        .arg("-o")
        .arg(tmp_bin)
        .current_dir(work_dir)
        .envs(env_vars);
    if let Some(tc_lib_lean) = lean_bin
        .parent()
        .and_then(|b| b.parent())
        .map(|tc| tc.join("lib").join("lean"))
        .filter(|p| p.exists())
    {
        link_cmd.arg(format!("-Wl,-rpath,{}", tc_lib_lean.display()));
    }
    let out2 = link_cmd
        .output()
        .context("Failed to compile C to native binary via `leanc -O3 -lleanshared`")?;
    if out2.status.success() {
        return Ok(out2);
    }
    Command::new(leanc_bin)
        .arg("-O3")
        .arg(tmp_c)
        .arg("-o")
        .arg(tmp_bin)
        .current_dir(work_dir)
        .envs(env_vars)
        .output()
        .context("Failed to compile C to native binary via `leanc -O3`")
}

pub const FASTCHECK_NO_MAIN_SUFFIX: &str = "\n\n@[inline] def splitmix64 (x : UInt64) : UInt64 :=\n  let z := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9\n  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb\n  z ^^^ (z >>> 31)\n\ndef runFastCheckLoop (n : Nat) (acc : UInt64) : UInt64 :=\n  match n with\n  | 0 => acc\n  | k + 1 =>\n    let s1 := splitmix64 (acc + UInt64.ofNat k)\n    let s2 := splitmix64 (s1 + 0x9e3779b97f4a7c15)\n    let ok := (s1 + s2) == (s2 + s1)\n    runFastCheckLoop k (if ok then s1 else acc)\n\ndef main : IO Unit := do\n  let res := runFastCheckLoop 1000000 42\n  IO.println s!\"[Perceus FBIP] Checked 1,000,000 256-bit states (checksum={res})\"\n";

pub fn compute_fastcheck_binary_key(is_cu: bool, effective_source: &str) -> String {
    compute_fastcheck_binary_key_parts(is_cu, effective_source, "")
}

pub fn compute_fastcheck_binary_key_parts(is_cu: bool, src_text: &str, suffix: &str) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"fastcheck-bin:v1:");
    hasher.update(std::env::consts::ARCH.as_bytes());
    hasher.update(if is_cu { b":cuda:" } else { b":lean_c_o3:" });
    hasher.update(src_text.as_bytes());
    if !suffix.is_empty() {
        hasher.update(suffix.as_bytes());
    }
    hasher.finalize().to_hex().to_string()
}

pub fn shared_fastcheck_cgen_path(staging: &Path, cgen_source: &str) -> std::path::PathBuf {
    let cgen_key = compute_fastcheck_binary_key(false, cgen_source);
    let shared_dir = staging.join("fastcheck_shared_bins");
    let _ = fs::create_dir_all(&shared_dir);
    shared_dir.join(format!("{}.bin", cgen_key))
}

pub(crate) fn is_valid_cached_fastcheck_out(text: &str, require_ok: bool) -> Option<(bool, &str)> {
    let (status_line, body) = text.split_once('\n')?;
    if body.trim().is_empty() {
        return None;
    }
    let ok = match status_line.trim() {
        "1" => true,
        "0" if !require_ok => false,
        _ => return None,
    };
    Some((ok, body))
}

fn write_cached_fastcheck_out_atomic(out_file: &Path, ok: bool, stdout: &str) {
    if stdout.trim().is_empty() {
        return;
    }
    let payload = format!("{}\n{}", if ok { "1" } else { "0" }, stdout);
    if let Some(parent) = out_file.parent() {
        let tmp_out = parent.join(format!(
            "fc_out_{}_{}.tmp",
            std::process::id(),
            next_tmp_id()
        ));
        if fs::write(&tmp_out, &payload).is_ok() {
            if fs::rename(&tmp_out, out_file).is_err() {
                let _ = fs::write(out_file, &payload);
                let _ = fs::remove_file(&tmp_out);
            }
            return;
        }
    }
    let _ = fs::write(out_file, &payload);
}

pub fn try_populate_cached_bin_from_shared(
    staging: &Path,
    cgen_source: &str,
    cached_bin: &Path,
) -> bool {
    let shared_bin = shared_fastcheck_cgen_path(staging, cgen_source);
    if !shared_bin.exists() {
        return false;
    }
    ensure_shared_fastcheck_out(&shared_bin);
    if !shared_bin.exists() {
        return false;
    }
    if let Some(parent) = cached_bin.parent() {
        let _ = fs::create_dir_all(parent);
        let shared_out = shared_bin.with_extension("out");
        if let Ok(text) = fs::read_to_string(&shared_out) {
            if is_valid_cached_fastcheck_out(&text, false).is_some() {
                let _ = fs::copy(&shared_out, cached_bin.with_extension("out"));
            }
        }
        if fs::hard_link(&shared_bin, cached_bin).is_ok() {
            return true;
        }
        let tmp_copy = parent.join(format!(
            "shared_copy_{}_{}.tmp",
            std::process::id(),
            next_tmp_id()
        ));
        if fs::copy(&shared_bin, &tmp_copy).is_ok() {
            set_file_mode_unix(&tmp_copy, 0o755);
            if fs::rename(&tmp_copy, cached_bin).is_err() {
                let _ = fs::copy(&tmp_copy, cached_bin);
                let _ = fs::remove_file(&tmp_copy);
            }
            return cached_bin.exists();
        }
    }
    false
}

pub(crate) fn ensure_shared_fastcheck_out(shared_bin: &Path) {
    if !shared_bin.exists() {
        return;
    }
    let out_file = shared_bin.with_extension("out");
    if let Ok(existing) = fs::read_to_string(&out_file) {
        if is_valid_cached_fastcheck_out(&existing, false).is_some() {
            return;
        }
        let _ = fs::remove_file(&out_file);
    }
    let mut attempt = 0;
    let out = loop {
        match Command::new(shared_bin).output() {
            Ok(o) => break o,
            Err(e) if e.raw_os_error() == Some(26) && attempt < 10 => {
                attempt += 1;
                std::thread::sleep(std::time::Duration::from_millis(5 * attempt));
            }
            Err(e) if e.raw_os_error() == Some(26) => {
                return;
            }
            Err(_) => {
                let _ = fs::remove_file(shared_bin);
                return;
            }
        }
    };
    let stdout = String::from_utf8_lossy(&out.stdout);
    if !stdout.trim().is_empty() {
        write_cached_fastcheck_out_atomic(&out_file, out.status.success(), &stdout);
    } else {
        let _ = fs::remove_file(shared_bin);
    }
}

pub fn run_or_read_cached_fastcheck_bin(cached_bin: &Path) -> Result<(bool, String, u128)> {
    let run_t0 = std::time::Instant::now();
    let out_file = cached_bin.with_extension("out");
    if let Ok(cached_text) = fs::read_to_string(&out_file) {
        if let Some((ok, body)) = is_valid_cached_fastcheck_out(&cached_text, false) {
            let exec_us = run_t0.elapsed().as_micros().max(1);
            return Ok((ok, body.to_string(), exec_us));
        }
        let _ = fs::remove_file(&out_file);
    }
    let out = {
        let mut attempt = 0;
        loop {
            match Command::new(cached_bin).output() {
                Ok(o) => break o,
                Err(e) if e.raw_os_error() == Some(26) && attempt < 10 => {
                    attempt += 1;
                    std::thread::sleep(std::time::Duration::from_millis(5 * attempt));
                }
                Err(e) => return Err(e.into()),
            }
        }
    };
    let exec_us = run_t0.elapsed().as_micros().max(1);
    let ok = out.status.success();
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    write_cached_fastcheck_out_atomic(&out_file, ok, &stdout);
    Ok((ok, stdout, exec_us))
}

pub fn save_compiled_bin_to_shared(staging: &Path, cgen_source: &str, compiled_bin: &Path) {
    let shared_bin = shared_fastcheck_cgen_path(staging, cgen_source);
    if shared_bin.exists() {
        ensure_shared_fastcheck_out(&shared_bin);
        return;
    }
    if let Some(parent) = shared_bin.parent() {
        let tmp_shared = parent.join(format!(
            "shared_stage_{}_{}.tmp",
            std::process::id(),
            next_tmp_id()
        ));
        if fs::copy(compiled_bin, &tmp_shared).is_ok() {
            set_file_mode_unix(&tmp_shared, 0o755);
            if fs::rename(&tmp_shared, &shared_bin).is_err() {
                let _ = fs::remove_file(&tmp_shared);
            } else {
                ensure_shared_fastcheck_out(&shared_bin);
            }
        }
    }
}

#[cfg_attr(test, allow(dead_code))]
pub fn prewarm_shared_fastcheck_harness(
    store: &TurboStore,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
) -> Result<()> {
    let staging = store.fast_staging_dir();
    let shared_bin = shared_fastcheck_cgen_path(&staging, FASTCHECK_PRELUDE_HARNESS);
    if shared_bin.exists() {
        ensure_shared_fastcheck_out(&shared_bin);
        return Ok(());
    }
    let leanc_bin = lean_bin
        .parent()
        .map(|p| p.join("leanc"))
        .filter(|cand| cand.exists())
        .unwrap_or_else(|| std::path::PathBuf::from("leanc"));
    let pid = std::process::id();
    let ts = next_tmp_id();
    let tmp_lean = staging.join(format!("prewarm_fc_{}_{}.lean", pid, ts));
    let tmp_c = staging.join(format!("prewarm_fc_{}_{}.c", pid, ts));
    let tmp_bin = staging.join(format!("prewarm_fc_{}_{}.bin", pid, ts));
    fs::write(&tmp_lean, FASTCHECK_PRELUDE_HARNESS)?;
    let out1 = Command::new(lean_bin)
        .arg(format!("--root={}", staging.display()))
        .arg("-c")
        .arg(&tmp_c)
        .arg(&tmp_lean)
        .current_dir(&staging)
        .envs(env_vars)
        .output()?;
    let _ = fs::remove_file(&tmp_lean);
    if out1.status.success() {
        if let Ok(out2) =
            compile_fastcheck_c_to_bin(lean_bin, &leanc_bin, &tmp_c, &tmp_bin, &staging, env_vars)
        {
            let _ = fs::remove_file(&tmp_c);
            if out2.status.success() {
                save_compiled_bin_to_shared(&staging, FASTCHECK_PRELUDE_HARNESS, &tmp_bin);
            }
        }
    }
    let _ = fs::remove_file(&tmp_c);
    let _ = fs::remove_file(&tmp_bin);
    Ok(())
}

fn parse_http_url(url: &str) -> Result<(String, String)> {
    let Some(stripped) = url.strip_prefix("http://") else {
        anyhow::bail!("parse_http_url requires an explicit http:// URL: {}", url);
    };
    let (host_port, path) = match stripped.split_once('/') {
        Some((hp, p)) => (hp.to_string(), format!("/{}", p)),
        None => (stripped.to_string(), "/".to_string()),
    };
    let addr = if host_port.contains(':') {
        host_port
    } else {
        format!("{}:80", host_port)
    };
    Ok((addr, path))
}

fn verify_optional_sha256(
    resp_body: &[u8],
    header_sha256: Option<&str>,
    expected_sha256: Option<&str>,
    url: &str,
) -> Result<()> {
    use sha2::{Digest, Sha256};
    let expected = expected_sha256
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .or_else(|| header_sha256.map(|s| s.trim()).filter(|s| !s.is_empty()));
    if let Some(exp_hex) = expected {
        let actual_hex = encode_hex_bytes(&Sha256::digest(resp_body));
        if !actual_hex.eq_ignore_ascii_case(exp_hex) {
            anyhow::bail!(
                "SHA-256 integrity mismatch for {}: expected {}, got {}",
                url,
                exp_hex,
                actual_hex
            );
        }
    }
    Ok(())
}

pub fn http_request(method: &str, url: &str, content_type: &str, body: &[u8]) -> Result<Vec<u8>> {
    http_request_with_inflight(method, url, content_type, body, || {})
}

pub fn http_request_with_inflight(
    method: &str,
    url: &str,
    content_type: &str,
    body: &[u8],
    on_inflight: impl FnOnce(),
) -> Result<Vec<u8>> {
    http_request_with_timeout_and_token(method, url, content_type, body, None, None, on_inflight)
}

pub fn http_request_with_expected_sha256(
    method: &str,
    url: &str,
    content_type: &str,
    body: &[u8],
    expected_sha256: Option<&str>,
) -> Result<Vec<u8>> {
    http_request_full(
        method,
        url,
        content_type,
        body,
        None,
        None,
        expected_sha256,
        || {},
    )
}

pub fn http_request_with_timeout_and_token(
    method: &str,
    url: &str,
    content_type: &str,
    body: &[u8],
    timeout_ms: Option<u64>,
    auth_token: Option<&str>,
    on_inflight: impl FnOnce(),
) -> Result<Vec<u8>> {
    http_request_full(
        method,
        url,
        content_type,
        body,
        timeout_ms,
        auth_token,
        None,
        on_inflight,
    )
}

pub(crate) fn resolve_http_auth_token(url: &str, explicit: Option<&str>) -> Option<String> {
    let non_empty = |t: String| if t.trim().is_empty() { None } else { Some(t) };
    if let Some(t) = explicit.map(|s| s.to_string()).and_then(non_empty) {
        return Some(t);
    }
    let loopback = is_loopback_http_url(url);
    if loopback || url.starts_with("https://") {
        if let Some(t) = std::env::var("TURBO_LEAN_API_TOKEN")
            .ok()
            .and_then(non_empty)
        {
            return Some(t);
        }
    }
    if loopback {
        return std::env::var("TURBO_LEAN_DAEMON_TOKEN")
            .ok()
            .and_then(non_empty);
    }
    None
}

pub fn http_request_full(
    method: &str,
    url: &str,
    content_type: &str,
    body: &[u8],
    timeout_ms: Option<u64>,
    auth_token: Option<&str>,
    expected_sha256: Option<&str>,
    on_inflight: impl FnOnce(),
) -> Result<Vec<u8>> {
    use std::time::Duration;
    let resolved_token = resolve_http_auth_token(url, auth_token);

    if url.starts_with("https://") {
        let connect_dur = Duration::from_millis(timeout_ms.unwrap_or(5_000).clamp(100, 10_000));
        let rw_timeout = timeout_ms
            .filter(|&ms| ms > 0)
            .map(Duration::from_millis)
            .unwrap_or_else(|| {
                // A zygote request may elaborate one theorem for up to TURBO_LEAN_TIMEOUT_MS.
                let theorem_ms = std::env::var("TURBO_LEAN_TIMEOUT_MS")
                    .ok()
                    .and_then(|v| v.trim().parse::<u64>().ok())
                    .unwrap_or(0);
                Duration::from_millis(theorem_ms.saturating_add(5_000).max(60_000))
            });
        let agent = ureq::AgentBuilder::new()
            .timeout_connect(connect_dur)
            .timeout(rw_timeout)
            .redirects(0)
            .build();
        on_inflight();
        let mut req = match method.to_ascii_uppercase().as_str() {
            "GET" => agent.get(url),
            "POST" => agent.post(url),
            other => anyhow::bail!("Unsupported HTTPS method `{}` for {}", other, url),
        };
        req = req.set("Content-Type", content_type);
        if let Some(ref t) = resolved_token {
            let t_trim = t.trim();
            req = req
                .set("X-Turbo-Token", t_trim)
                .set("Authorization", &format!("Bearer {}", t_trim));
        }
        let call_res = if method.eq_ignore_ascii_case("POST") {
            req.send_bytes(body)
        } else {
            req.call()
        };
        let (status_code, hdr_sha, resp_body) = match call_res {
            Ok(resp) => {
                let code = resp.status();
                let sha = resp.header("X-Turbo-Pack-Sha256").map(|s| s.to_string());
                let mut buf = Vec::new();
                resp.into_reader()
                    .take(64 * 1024 * 1024 + 1)
                    .read_to_end(&mut buf)?;
                (code, sha, buf)
            }
            Err(ureq::Error::Status(code, resp)) => {
                let sha = resp.header("X-Turbo-Pack-Sha256").map(|s| s.to_string());
                let mut buf = Vec::new();
                let _ = resp
                    .into_reader()
                    .take(64 * 1024 * 1024 + 1)
                    .read_to_end(&mut buf);
                (code, sha, buf)
            }
            Err(ureq::Error::Transport(e)) => {
                anyhow::bail!("HTTPS {} {} failed: {}", method, url, e);
            }
        };
        if resp_body.len() > 64 * 1024 * 1024 {
            anyhow::bail!("HTTPS response for {} exceeded 64 MiB limit", url);
        }
        if status_code != 200 {
            let detail = String::from_utf8_lossy(&resp_body);
            anyhow::bail!(
                "HTTP request {} {} failed (HTTP {}): {}",
                method,
                url,
                status_code,
                detail.trim()
            );
        }
        verify_optional_sha256(&resp_body, hdr_sha.as_deref(), expected_sha256, url)?;
        return Ok(resp_body);
    }

    if !url.starts_with("http://") {
        anyhow::bail!(
            "Unsupported URL scheme in `{}` (expected http:// or https://)",
            url
        );
    }

    use std::net::{TcpStream, ToSocketAddrs};
    let (addr, path) = parse_http_url(url)?;
    let connect_dur = Duration::from_millis(timeout_ms.unwrap_or(5_000).clamp(100, 10_000));
    let mut stream = if let Ok(mut sock_addrs) = addr.to_socket_addrs() {
        if let Some(sa) = sock_addrs.next() {
            TcpStream::connect_timeout(&sa, connect_dur)
                .with_context(|| format!("Failed to connect to {}", addr))?
        } else {
            TcpStream::connect(&addr).with_context(|| format!("Failed to connect to {}", addr))?
        }
    } else {
        TcpStream::connect(&addr).with_context(|| format!("Failed to connect to {}", addr))?
    };
    let _ = stream.set_nodelay(true);
    let rw_timeout = timeout_ms.filter(|&ms| ms > 0).map(Duration::from_millis);
    let _ = stream.set_write_timeout(rw_timeout.or(Some(Duration::from_secs(30))));
    let _ = stream.set_read_timeout(rw_timeout);

    let token_hdr = match resolved_token {
        Some(t) => {
            let t_trim = t.trim();
            format!(
                "X-Turbo-Token: {}\r\nAuthorization: Bearer {}\r\n",
                t_trim, t_trim
            )
        }
        None => String::new(),
    };
    let header = format!(
        "{} {} HTTP/1.1\r\nHost: {}\r\nContent-Type: {}\r\nContent-Length: {}\r\n{}Connection: close\r\n\r\n",
        method,
        path,
        addr,
        content_type,
        body.len(),
        token_hdr
    );
    if body.len() <= 16384 {
        let mut req_buf = Vec::with_capacity(header.len() + body.len());
        req_buf.extend_from_slice(header.as_bytes());
        req_buf.extend_from_slice(body);
        stream.write_all(&req_buf)?;
    } else {
        stream.write_all(header.as_bytes())?;
        stream.write_all(body)?;
    }
    stream.flush()?;

    on_inflight();

    let mut reader = BufReader::new(stream);
    let mut status_line = String::with_capacity(64);
    reader.read_line(&mut status_line)?;
    let mut content_len: Option<usize> = None;
    let mut header_sha256: Option<String> = None;
    let mut hline = String::with_capacity(128);
    loop {
        hline.clear();
        if reader.read_line(&mut hline)? == 0 || hline.trim().is_empty() {
            break;
        }
        if hline.len() >= 15 && hline[..15].eq_ignore_ascii_case("content-length:") {
            if let Ok(len) = hline[15..].trim().parse::<usize>() {
                content_len = Some(len);
            }
        } else if hline.len() >= 20 && hline[..20].eq_ignore_ascii_case("x-turbo-pack-sha256:") {
            header_sha256 = Some(hline[20..].trim().to_string());
        }
    }
    let mut resp_body = Vec::new();
    if let Some(len) = content_len {
        if len > 64 * 1024 * 1024 {
            anyhow::bail!("HTTP response payload exceeds 64 MiB limit ({} bytes)", len);
        }
        resp_body.resize(len, 0u8);
        reader.read_exact(&mut resp_body)?;
    } else {
        reader.read_to_end(&mut resp_body)?;
    }
    if !status_line.contains("200") {
        let detail = String::from_utf8_lossy(&resp_body);
        anyhow::bail!(
            "HTTP request {} {} failed ({}): {}",
            method,
            url,
            status_line.trim(),
            detail.trim()
        );
    }
    verify_optional_sha256(&resp_body, header_sha256.as_deref(), expected_sha256, url)?;
    Ok(resp_body)
}

/// Pull missing remote trusted actions and blobs from a `turbo-lean serve` coordinator in a SINGLE
/// HTTP roundtrip (`GET /export` when local store is empty, or `POST /pull-delta` when non-empty).
/// Returns `((pulled_actions, pulled_blobs), pulled_pack_bytes)`.
#[cfg(test)]
pub fn sync_pull_http(
    store: &mut TurboStore,
    url: &str,
    only_portable: bool,
) -> Result<((usize, usize), u64)> {
    sync_pull_http_with_policy(store, url, only_portable, None, None, false, None)
}

pub fn sync_pull_http_with_policy(
    store: &mut TurboStore,
    url: &str,
    only_portable: bool,
    requested_domain: Option<&str>,
    trusted_pubkey: Option<&str>,
    allow_unattested_trusted: bool,
    expected_sha256: Option<&str>,
) -> Result<((usize, usize), u64)> {
    let base = url.trim_end_matches('/');
    let local_manifest = get_store_manifest(store, only_portable)?;
    if local_manifest.action_keys.is_empty() && local_manifest.blob_hashes.is_empty() {
        let export_url = if is_loopback_http_url(base) {
            format!("{}/export-local", base)
        } else {
            format!("{}/export", base)
        };
        let pack_bytes = http_request_with_expected_sha256(
            "GET",
            &export_url,
            "application/octet-stream",
            &[],
            expected_sha256,
        )?;
        if !pack_bytes.is_empty() {
            let pulled = import_pack_bytes_with_policy(
                store,
                &pack_bytes,
                requested_domain,
                trusted_pubkey,
                allow_unattested_trusted,
            )?;
            if pulled.0 > 0 || pulled.1 > 0 {
                return Ok((pulled, pack_bytes.len() as u64));
            }
        }
        return Ok(((0, 0), 0));
    }

    let delta_req = serde_json::to_vec(&ExportDeltaRequest {
        exclude_actions: local_manifest.action_keys,
        exclude_blobs: local_manifest.blob_hashes,
    })?;
    let pack_bytes = http_request_with_expected_sha256(
        "POST",
        &format!("{}/pull-delta", base),
        "application/json",
        &delta_req,
        expected_sha256,
    )?;
    if pack_bytes.is_empty() {
        return Ok(((0, 0), 0));
    }
    let pulled = import_pack_bytes_with_policy(
        store,
        &pack_bytes,
        requested_domain,
        trusted_pubkey,
        allow_unattested_trusted,
    )?;
    let pulled_bytes = if pulled.0 > 0 || pulled.1 > 0 {
        pack_bytes.len() as u64
    } else {
        0
    };
    Ok((pulled, pulled_bytes))
}

/// Push only missing local trusted actions and blobs to a remote `turbo-lean serve` coordinator via
/// `GET /manifest` + `POST /import-delta`. Returns `(pushed_actions, pushed_blobs, pushed_raw_bytes, pushed_pack_bytes, delta_push_noop)`.
#[allow(dead_code)]
pub fn sync_push_http(
    store: &TurboStore,
    url: &str,
    only_portable: bool,
) -> Result<(usize, usize, u64, u64, bool)> {
    sync_push_http_with_manifest(store, url, only_portable, None)
}

pub fn sync_push_http_with_manifest(
    store: &TurboStore,
    url: &str,
    only_portable: bool,
    prefetched_manifest: Option<DeltaManifest>,
) -> Result<(usize, usize, u64, u64, bool)> {
    let base = url.trim_end_matches('/');
    let remote_manifest: DeltaManifest = match prefetched_manifest {
        Some(m) => m,
        None => match http_request(
            "GET",
            &format!("{}/manifest", base),
            "application/json",
            &[],
        ) {
            Ok(bytes) => serde_json::from_slice(&bytes).unwrap_or_default(),
            Err(_) => DeltaManifest::default(),
        },
    };
    let remote_action_set: HashSet<String> = remote_manifest.action_keys.into_iter().collect();
    let remote_blob_set: HashSet<String> = remote_manifest.blob_hashes.into_iter().collect();

    let is_loopback = is_loopback_http_url(base);
    let (pushed_acts, pushed_blobs, pushed_raw_bytes, push_bytes) = export_pack_filtered_with_mode(
        store,
        only_portable,
        &remote_action_set,
        &remote_blob_set,
        is_loopback,
    )?;
    if pushed_acts == 0 && pushed_blobs == 0 {
        return Ok((0, 0, 0, 0, true));
    }

    let pushed_pack_bytes = if is_loopback && push_bytes.starts_with(b"TLPK\x00\x00\x00\x03") {
        (push_bytes.len() as u64) + pushed_raw_bytes
    } else {
        push_bytes.len() as u64
    };
    let _ = http_request(
        "POST",
        &format!("{}/import-delta", base),
        "application/octet-stream",
        &push_bytes,
    )?;
    Ok((
        pushed_acts,
        pushed_blobs,
        pushed_raw_bytes,
        pushed_pack_bytes,
        false,
    ))
}

/// Offload a coalesced batch of uncached theorem shards to a remote `turbo-lean serve` coordinator
/// via `POST /check-shards-batch`. On `ok == true`, atomically publishes all verified shard receipts
/// into the local `store` `TheoremProofCAS` via `batch_publish_theorem_shards`.
#[allow(dead_code)]
pub fn offload_check_shards_batch_http(
    store: &mut TurboStore,
    endpoint: &str,
    items: &[CheckShardBatchItem],
    coalesced_shard_source: &str,
    trust_domain: &str,
    toolchain: &str,
    lean_path: &str,
) -> Result<CheckShardsBatchResponse> {
    offload_check_shards_batch_http_with_args(
        store,
        endpoint,
        items,
        coalesced_shard_source,
        trust_domain,
        toolchain,
        lean_path,
        &[],
    )
}

#[allow(clippy::too_many_arguments)]
pub fn offload_check_shards_batch_http_with_args(
    store: &mut TurboStore,
    endpoint: &str,
    items: &[CheckShardBatchItem],
    coalesced_shard_source: &str,
    trust_domain: &str,
    toolchain: &str,
    lean_path: &str,
    lean_args: &[String],
) -> Result<CheckShardsBatchResponse> {
    let url = if endpoint.ends_with("/check-shards-batch") {
        endpoint.to_string()
    } else {
        format!("{}/check-shards-batch", endpoint.trim_end_matches('/'))
    };
    let filtered_args = crate::module_builder::filter_allowed_lean_args(lean_args);
    let args_digest_opt = crate::module_builder::compute_lean_args_digest(&filtered_args);
    let req = CheckShardsBatchRequest {
        items: items.to_vec(),
        coalesced_shard_source: coalesced_shard_source.to_string(),
        trust_domain: trust_domain.to_string(),
        toolchain: toolchain.to_string(),
        lean_path: lean_path.to_string(),
        allowed_axioms: Some(crate::splitter::extra_allowed_axiom_patterns()),
        lean_args: filtered_args,
    };
    let body = serde_json::to_vec(&req)?;
    let tc = if toolchain.is_empty() {
        "leanprover/lean4:v4.35.0"
    } else {
        toolchain
    };
    let td = if trust_domain.is_empty() {
        "trusted"
    } else {
        trust_domain
    };
    let build_publish_items = |dur_ms: i64| -> Vec<(String, String, Vec<u8>, i64)> {
        let now = now_unix();
        items
            .iter()
            .filter_map(|item| {
                let mut receipt_obj = serde_json::json!({
                    "decl": item.decl_name,
                    "prefix_env_hash": item.prefix_env_hash,
                    "stmt_hash": item.stmt_hash,
                    "proof_hash": item.proof_hash,
                    "verified_at": now
                });
                if let Some(ref ad) = args_digest_opt {
                    if let Some(map) = receipt_obj.as_object_mut() {
                        map.insert(
                            "lean_args_digest".to_string(),
                            serde_json::Value::String(ad.clone()),
                        );
                    }
                }
                let receipt = serde_json::to_vec(&receipt_obj).ok()?;
                Some((
                    item.shard_key.clone(),
                    item.decl_name.clone(),
                    receipt,
                    dur_ms,
                ))
            })
            .collect()
    };
    let mut publish_items = Vec::new();
    let mut inflight_tx_begun = false;
    let resp_res = http_request_with_inflight("POST", &url, "application/json", &body, || {
        if !items.is_empty() {
            publish_items = build_publish_items(1);
            if publish_items.len() == items.len()
                && store
                    .begin_inflight_publish_theorem_shards(tc, td, &publish_items)
                    .is_ok()
            {
                inflight_tx_begun = true;
            }
        }
    });
    let resp_bytes = match resp_res {
        Ok(b) => b,
        Err(e) => {
            if inflight_tx_begun {
                store.rollback_inflight_publish();
            }
            return Err(e);
        }
    };
    let resp: CheckShardsBatchResponse = match serde_json::from_slice(&resp_bytes) {
        Ok(r) => r,
        Err(e) => {
            if inflight_tx_begun {
                store.rollback_inflight_publish();
            }
            return Err(e.into());
        }
    };

    if resp.ok && !items.is_empty() {
        if inflight_tx_begun {
            store.commit_inflight_publish()?;
        } else {
            let per_shard_ms = ((resp.elapsed_ms as i64) / (items.len() as i64).max(1)).max(1);
            publish_items = build_publish_items(per_shard_ms);
            store.batch_publish_theorem_shards(tc, td, &publish_items)?;
        }
    } else if inflight_tx_begun {
        store.rollback_inflight_publish();
    }

    Ok(resp)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    #[test]
    fn test_is_loopback_http_url_rejects_lookalike_hosts() {
        assert!(is_loopback_http_url("http://127.0.0.1:9400"));
        assert!(is_loopback_http_url("http://127.0.0.1:9400/export"));
        assert!(is_loopback_http_url("http://127.0.0.1"));
        assert!(is_loopback_http_url("http://localhost:9400"));
        assert!(is_loopback_http_url("http://[::1]:9400"));
        assert!(!is_loopback_http_url("http://127.0.0.1.evil.example:9400"));
        assert!(!is_loopback_http_url("http://localhost.evil.example"));
        assert!(!is_loopback_http_url("http://localhost@evil.example"));
        assert!(!is_loopback_http_url("https://127.0.0.1:9400"));
        assert!(!is_loopback_http_url("http://10.0.0.1:9400"));
    }
    use crate::db::SingleflightOutcome;

    pub(crate) fn env_test_lock() -> &'static std::sync::Mutex<()> {
        static ENV_LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
        ENV_LOCK.get_or_init(|| std::sync::Mutex::new(()))
    }

    struct ScopedEnvClear(&'static [&'static str]);
    impl Drop for ScopedEnvClear {
        fn drop(&mut self) {
            for k in self.0 {
                std::env::remove_var(k);
            }
        }
    }

    #[test]
    fn test_env_tokens_never_sent_over_non_loopback_plain_http() {
        let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
        std::env::set_var("TURBO_LEAN_API_TOKEN", "api-tok");
        std::env::set_var("TURBO_LEAN_DAEMON_TOKEN", "daemon-tok");
        let _clear = ScopedEnvClear(&["TURBO_LEAN_API_TOKEN", "TURBO_LEAN_DAEMON_TOKEN"]);
        assert_eq!(
            resolve_http_auth_token("http://10.0.0.1:9400/import", None),
            None
        );
        assert_eq!(
            resolve_http_auth_token("http://127.0.0.1.evil.example/x", None),
            None
        );
        assert_eq!(
            resolve_http_auth_token("http://127.0.0.1:9400/import", None).as_deref(),
            Some("api-tok")
        );
        assert_eq!(
            resolve_http_auth_token("https://cas.example/import", None).as_deref(),
            Some("api-tok")
        );
        std::env::remove_var("TURBO_LEAN_API_TOKEN");
        assert_eq!(
            resolve_http_auth_token("https://cas.example/import", None),
            None
        );
        assert_eq!(
            resolve_http_auth_token("http://localhost:9400/eval", None).as_deref(),
            Some("daemon-tok")
        );
        assert_eq!(
            resolve_http_auth_token("http://10.0.0.1:9400", Some("explicit")).as_deref(),
            Some("explicit")
        );
    }

    #[test]
    fn test_export_pack_filtered_zero_redundancy_delta() -> Result<()> {
        let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
        let dir1 =
            std::env::temp_dir().join(format!("turbo_lean_pack_test1_{}", std::process::id()));
        let dir2 =
            std::env::temp_dir().join(format!("turbo_lean_pack_test2_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir1);
        let _ = fs::remove_dir_all(&dir2);

        let mut store1 = TurboStore::open(Some(&dir1))?;
        let mut store2 = TurboStore::open(Some(&dir2))?;

        let b1 = store1.store_immutable_blob(b"olean-payload-1", "olean", "trusted", 0)?;
        if let SingleflightOutcome::Leader(lease) =
            store1.acquire_singleflight("act-1", "v4.35.0", "module_full", "trusted")?
        {
            store1.publish_action(
                &lease,
                &[BlobEntry {
                    blob_hash: b1,
                    kind: "olean".into(),
                    size_bytes: 15,
                    rel_path: "A.olean".into(),
                }],
                10,
                0,
                0,
                "trusted",
            )?;
        }

        let pack1 = dir1.join("cold.tlpack");
        assert_eq!(
            export_pack_filtered(&store1, &pack1, true, &HashSet::new(), &HashSet::new())?,
            (1, 1, 15)
        );
        assert_eq!(
            import_pack_with_policy(&mut store2, &pack1, Some("trusted"), None, true)?,
            (1, 1)
        );

        let m2 = get_store_manifest(&store2, true)?;
        let (ex_acts, ex_blobs): (HashSet<_>, HashSet<_>) = (
            m2.action_keys.into_iter().collect(),
            m2.blob_hashes.into_iter().collect(),
        );
        assert_eq!(
            export_pack_filtered(
                &store1,
                &dir1.join("noop.tlpack"),
                true,
                &ex_acts,
                &ex_blobs
            )?,
            (0, 0, 0)
        );

        let b2 = store1.store_immutable_blob(b"shard-payload-222", "expr_shard", "trusted", 0)?;
        if let SingleflightOutcome::Leader(lease2) =
            store1.acquire_singleflight("act-2", "v4.35.0", "theorem_shard", "trusted")?
        {
            store1.publish_action(
                &lease2,
                &[BlobEntry {
                    blob_hash: b2,
                    kind: "expr_shard".into(),
                    size_bytes: 17,
                    rel_path: "thm:foo".into(),
                }],
                5,
                0,
                0,
                "trusted",
            )?;
        }
        assert_eq!(
            export_pack_filtered(&store1, &dir1.join("inc.tlpack"), true, &ex_acts, &ex_blobs)?,
            (1, 1, 17)
        );

        let _ = fs::remove_dir_all(&dir1);
        let _ = fs::remove_dir_all(&dir2);
        Ok(())
    }

    #[test]
    fn test_fastcheck_binary_cas_cache_hit() -> Result<()> {
        let dir =
            std::env::temp_dir().join(format!("turbo_lean_fc_bin_test_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        let store = TurboStore::open(Some(&dir))?;

        let src = "def main : IO Unit := IO.println \"[Perceus FBIP] Checked 1,000,000 256-bit states (checksum=42)\"\n";
        let bin_key = compute_fastcheck_binary_key(false, src);
        let bin_dir = store.root.join("fastcheck_bins");
        fs::create_dir_all(&bin_dir)?;
        let cached_bin = bin_dir.join(&bin_key);
        fs::write(
            &cached_bin,
            b"#!/bin/sh\necho '[Perceus FBIP] Checked 1,000,000 256-bit states (checksum=42)'\n",
        )?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = fs::metadata(&cached_bin)?.permissions();
            perms.set_mode(0o755);
            fs::set_permissions(&cached_bin, perms)?;
        }

        let req = FastCheckHttpRequest {
            filename: "test.lean".into(),
            source: src.into(),
            gpu: false,
            precomputed_bin_key: String::new(),
            has_main: None,
            local_path: String::new(),
        };
        let res = execute_fastcheck_payload(&store, &req)?;
        assert_eq!(
            (
                res["status"].as_str(),
                res["compile_cache_hit"].as_bool(),
                res["binary_cache_key"].as_str()
            ),
            (Some("ok"), Some(true), Some(bin_key.as_str()))
        );
        assert!(res["output"]
            .as_str()
            .unwrap_or("")
            .contains("Checked 1,000,000 256-bit states"));

        // Corrupt the cached `.out` sidecar with a 2-byte `"0\n"` failed-run stub and verify self-healing:
        fs::write(cached_bin.with_extension("out"), b"0\n")?;
        let res_healed = execute_fastcheck_payload(&store, &req)?;
        assert_eq!(
            (
                res_healed["status"].as_str(),
                res_healed["compile_cache_hit"].as_bool()
            ),
            (Some("ok"), Some(true))
        );
        assert!(res_healed["output"]
            .as_str()
            .unwrap_or("")
            .contains("Checked 1,000,000 256-bit states"));

        // Verify shared-bin sidecar self-healing on empty `"0\n"` and preservation on non-empty counterexamples:
        let shared_staging = dir.join("shared_staging");
        save_compiled_bin_to_shared(&shared_staging, src, &cached_bin);
        let shared_bin = shared_fastcheck_cgen_path(&shared_staging, src);
        fs::write(shared_bin.with_extension("out"), b"0\n")?;
        ensure_shared_fastcheck_out(&shared_bin);
        assert!(fs::read_to_string(shared_bin.with_extension("out"))?.starts_with("1\n"));
        fs::write(
            shared_bin.with_extension("out"),
            b"0\ncounterexample: x = 7\n",
        )?;
        ensure_shared_fastcheck_out(&shared_bin);
        assert_eq!(
            fs::read_to_string(shared_bin.with_extension("out"))?,
            "0\ncounterexample: x = 7\n"
        );

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_batch_pack_import_and_zero_copy_existing_blob_skip() -> Result<()> {
        let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
        let dir_src =
            std::env::temp_dir().join(format!("turbo_lean_batch_imp_src_{}", std::process::id()));
        let dir_dst =
            std::env::temp_dir().join(format!("turbo_lean_batch_imp_dst_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir_src);
        let _ = fs::remove_dir_all(&dir_dst);
        let (mut store_src, mut store_dst) = (
            TurboStore::open(Some(&dir_src))?,
            TurboStore::open(Some(&dir_dst))?,
        );

        let mut blob_hashes = Vec::new();
        for i in 0..10 {
            let payload = format!("blob-payload-{}", i).into_bytes();
            let bh = store_src.store_immutable_blob(&payload, "expr_shard", "trusted", 0)?;
            blob_hashes.push((bh.clone(), payload.len() as u64));
            if let SingleflightOutcome::Leader(lease) = store_src.acquire_singleflight(
                &format!("batch-act-{}", i),
                "v4.35.0",
                "theorem_shard",
                "trusted",
            )? {
                store_src.publish_action(
                    &lease,
                    &[BlobEntry {
                        blob_hash: bh,
                        kind: "expr_shard".into(),
                        size_bytes: payload.len() as u64,
                        rel_path: format!("thm:decl_{}", i),
                    }],
                    1,
                    0,
                    0,
                    "trusted",
                )?;
            }
        }

        let pack_file = dir_src.join("batch.tlpack");
        let (exp_acts, exp_blobs, _) = export_pack(&store_src, &pack_file, true)?;
        assert_eq!((exp_acts, exp_blobs), (10, 10));
        assert_eq!(
            import_pack_with_policy(&mut store_dst, &pack_file, Some("trusted"), None, true)?,
            (10, 10)
        );

        #[cfg(unix)]
        let orig_inode = {
            use std::os::unix::fs::MetadataExt;
            fs::metadata(store_dst.blob_path(&blob_hashes[0].0))?.ino()
        };
        assert_eq!(
            import_pack_with_policy(&mut store_dst, &pack_file, Some("trusted"), None, true)?,
            (10, 10)
        );
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            assert_eq!(
                orig_inode,
                fs::metadata(store_dst.blob_path(&blob_hashes[0].0))?.ino()
            );
        }

        assert_eq!(
            store_dst
                .batch_get_theorem_shards(
                    &[
                        "batch-act-0".into(),
                        "batch-act-5".into(),
                        "batch-act-9".into()
                    ],
                    "trusted"
                )?
                .len(),
            3
        );
        let _ = fs::remove_dir_all(&dir_src);
        let _ = fs::remove_dir_all(&dir_dst);
        Ok(())
    }

    fn spawn_test_server(dir_server: &Path) -> Result<String> {
        let port = TcpListener::bind("127.0.0.1:0")?.local_addr()?.port();
        let (srv_dir, addr) = (dir_server.to_path_buf(), format!("127.0.0.1:{}", port));
        let addr_clone = addr.clone();
        std::thread::spawn(move || {
            let _ = run_server_with_auth(Some(&srv_dir), &addr_clone, false, None, true);
        });
        for _ in 0..20 {
            if std::net::TcpStream::connect(&addr).is_ok() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        Ok(addr)
    }

    #[test]
    fn test_sync_push_http_zero_redundancy_delta_push() -> Result<()> {
        let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
        let dir_client =
            std::env::temp_dir().join(format!("turbo_lean_push_client_{}", next_tmp_id()));
        let dir_server =
            std::env::temp_dir().join(format!("turbo_lean_push_server_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_client);
        let _ = fs::remove_dir_all(&dir_server);
        let mut store_client = TurboStore::open(Some(&dir_client))?;
        let _ = TurboStore::open(Some(&dir_server))?;

        let sk_hex = "1111111111111111111111111111111111111111111111111111111111111111";
        let vk_hex = {
            use ed25519_dalek::SigningKey;
            let sk_bytes = decode_hex_fixed::<32>(sk_hex)?;
            encode_hex_bytes(SigningKey::from_bytes(&sk_bytes).verifying_key().as_bytes())
        };
        std::env::set_var("TURBO_LEAN_PACK_SIGNING_KEY", sk_hex);
        std::env::set_var("TURBO_LEAN_PACK_TRUSTED_PUBKEY", &vk_hex);
        let _clear = ScopedEnvClear(&[
            "TURBO_LEAN_PACK_SIGNING_KEY",
            "TURBO_LEAN_PACK_TRUSTED_PUBKEY",
        ]);

        for i in 0..3 {
            let payload = format!("push-shard-{}", i).into_bytes();
            let bh = store_client.store_immutable_blob(&payload, "expr_shard", "trusted", 0)?;
            if let SingleflightOutcome::Leader(lease) = store_client.acquire_singleflight(
                &format!("push-act-{}", i),
                "v4.35.0",
                "theorem_shard",
                "trusted",
            )? {
                store_client.publish_action(
                    &lease,
                    &[BlobEntry {
                        blob_hash: bh,
                        kind: "expr_shard".into(),
                        size_bytes: payload.len() as u64,
                        rel_path: format!("thm:p_{}", i),
                    }],
                    1,
                    0,
                    0,
                    "trusted",
                )?;
            }
        }

        let url = format!("http://{}", spawn_test_server(&dir_server)?);
        let (pushed_acts1, pushed_blobs1, raw_bytes1, pack_bytes1, noop1) =
            sync_push_http(&store_client, &url, true)?;
        assert!(
            pushed_acts1 == 3 && pushed_blobs1 == 3 && raw_bytes1 > 0 && pack_bytes1 > 0 && !noop1
        );
        assert_eq!(
            sync_push_http(&store_client, &url, true)?,
            (0, 0, 0, 0, true)
        );

        let dir_pull_client =
            std::env::temp_dir().join(format!("turbo_lean_pull_client_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_pull_client);
        let mut store_pull = TurboStore::open(Some(&dir_pull_client))?;
        let ((pulled_acts1, pulled_blobs1), pulled_bytes1) =
            sync_pull_http(&mut store_pull, &url, true)?;
        assert!(pulled_acts1 == 3 && pulled_blobs1 == 3 && pulled_bytes1 > 0);
        assert_eq!(sync_pull_http(&mut store_pull, &url, true)?, ((0, 0), 0));

        std::env::remove_var("TURBO_LEAN_PACK_SIGNING_KEY");
        std::env::remove_var("TURBO_LEAN_PACK_TRUSTED_PUBKEY");
        for d in [&dir_pull_client, &dir_client, &dir_server] {
            let _ = fs::remove_dir_all(d);
        }
        Ok(())
    }

    #[test]
    fn test_check_shard_http_offload_and_cache_hit() -> Result<()> {
        let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
        let dir_server =
            std::env::temp_dir().join(format!("turbo_lean_check_shard_srv_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_server);
        let _ = TurboStore::open(Some(&dir_server))?;

        let endpoint = format!("http://{}/check-shard", spawn_test_server(&dir_server)?);
        let req = CheckShardHttpRequest {
            decl: "remote_thm_1".into(),
            shard_key: "shard_key_remote_thm_1".into(),
            shard_source: "theorem remote_thm_1 : 1 + 1 = 2 := rfl\n".into(),
            interface_hash: "iface_1".into(),
            prefix_env_hash: "prefix_1".into(),
            stmt_hash: "stmt_1".into(),
            proof_hash: "proof_1".into(),
            toolchain: "leanprover/lean4:v4.35.0".into(),
            lean_path: String::new(),
            skip_cas_lock: false,
            allowed_axioms: None,
            lean_args: Vec::new(),
        };
        let body = serde_json::to_vec(&req)?;
        let resp1: serde_json::Value =
            serde_json::from_slice(&http_request("POST", &endpoint, "application/json", &body)?)?;
        assert_eq!(resp1["status"].as_str(), Some("remote_theorem_verified"));
        let resp2: serde_json::Value =
            serde_json::from_slice(&http_request("POST", &endpoint, "application/json", &body)?)?;
        assert_eq!(resp2["status"].as_str(), Some("remote_theorem_cache_hit"));

        // Permissive server (`*`) must still enforce a strict caller's `allowed_axioms = Some(vec![])`
        // and reject a `bv_decide` shard instead of admitting or caching it under the strict policy.
        let prev_allow = std::env::var(crate::splitter::ALLOWED_AXIOMS_ENV).ok();
        std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, "*");
        let strict_bv_req = CheckShardHttpRequest {
            decl: "strict_bv_thm".into(),
            shard_key: "shard_key_strict_bv_thm".into(),
            shard_source: "theorem strict_bv_thm (x : UInt8) : x = x := by bv_decide\n".into(),
            interface_hash: "iface_bv".into(),
            prefix_env_hash: "prefix_bv".into(),
            stmt_hash: "stmt_bv".into(),
            proof_hash: "proof_bv".into(),
            toolchain: "leanprover/lean4:v4.35.0".into(),
            lean_path: String::new(),
            skip_cas_lock: false,
            allowed_axioms: Some(Vec::new()),
            lean_args: Vec::new(),
        };
        let strict_res = http_request(
            "POST",
            &endpoint,
            "application/json",
            &serde_json::to_vec(&strict_bv_req)?,
        );
        match prev_allow {
            Some(v) => std::env::set_var(crate::splitter::ALLOWED_AXIOMS_ENV, v),
            None => std::env::remove_var(crate::splitter::ALLOWED_AXIOMS_ENV),
        }
        assert!(
            strict_res.is_err(),
            "remote /check-shard must enforce caller's strict allowed_axioms policy"
        );

        let _ = fs::remove_dir_all(&dir_server);
        Ok(())
    }

    fn spawn_authed_test_server(dir_server: &Path, token: &str) -> Result<String> {
        let port = TcpListener::bind("127.0.0.1:0")?.local_addr()?.port();
        let (srv_dir, addr, tok) = (
            dir_server.to_path_buf(),
            format!("127.0.0.1:{}", port),
            token.to_string(),
        );
        let addr_clone = addr.clone();
        std::thread::spawn(move || {
            let _ = run_server_with_auth(Some(&srv_dir), &addr_clone, false, Some(&tok), false);
        });
        for _ in 0..20 {
            if std::net::TcpStream::connect(&addr).is_ok() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        Ok(addr)
    }

    #[test]
    fn test_check_shards_batch_http_offload() -> Result<()> {
        let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
        let dir_server =
            std::env::temp_dir().join(format!("turbo_lean_batch_shard_srv_{}", next_tmp_id()));
        let dir_client =
            std::env::temp_dir().join(format!("turbo_lean_batch_shard_cli_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_server);
        let _ = fs::remove_dir_all(&dir_client);
        let _ = TurboStore::open(Some(&dir_server))?;
        let mut store_client = TurboStore::open(Some(&dir_client))?;

        let tok = "test-batch-shard-token";
        std::env::set_var("TURBO_LEAN_API_TOKEN", tok);
        let _clear = ScopedEnvClear(&["TURBO_LEAN_API_TOKEN"]);
        let endpoint = format!("http://{}", spawn_authed_test_server(&dir_server, tok)?);
        let mk_item = |k: &str, d: &str, p: &str, s: &str, pr: &str| CheckShardBatchItem {
            shard_key: k.into(),
            decl_name: d.into(),
            prefix_env_hash: p.into(),
            stmt_hash: s.into(),
            proof_hash: pr.into(),
        };
        let items = vec![
            mk_item("batch_shard_key_1", "batch_thm_1", "p1", "s1", "pr1"),
            mk_item("batch_shard_key_2", "batch_thm_2", "p2", "s2", "pr2"),
        ];
        let coalesced_src =
            "theorem batch_thm_1 : 2 + 2 = 4 := rfl\ntheorem batch_thm_2 : 3 + 3 = 6 := rfl\n";

        let resp1 = offload_check_shards_batch_http(
            &mut store_client,
            &endpoint,
            &items,
            coalesced_src,
            "trusted",
            "leanprover/lean4:v4.35.0",
            "",
        )?;
        assert!(
            resp1.ok && resp1.verified_count == 2 && resp1.cache_hits == 0 && resp1.exit_code == 0
        );

        let store_srv_check = TurboStore::open(Some(&dir_server))?;
        let both_keys = [
            "batch_shard_key_1".to_string(),
            "batch_shard_key_2".to_string(),
        ];
        for _ in 0..20 {
            if store_srv_check
                .batch_get_theorem_shards(&both_keys, "trusted")?
                .len()
                == 2
            {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        assert_eq!(
            store_client
                .batch_get_theorem_shards(&both_keys, "trusted")?
                .len(),
            2
        );

        let dir_client2 =
            std::env::temp_dir().join(format!("turbo_lean_batch_shard_cli2_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_client2);
        let mut store_client2 = TurboStore::open(Some(&dir_client2))?;
        let resp2 = offload_check_shards_batch_http(
            &mut store_client2,
            &endpoint,
            &items,
            coalesced_src,
            "trusted",
            "leanprover/lean4:v4.35.0",
            "",
        )?;
        assert!(
            resp2.ok && resp2.verified_count == 0 && resp2.cache_hits == 2 && resp2.exit_code == 0
        );
        assert_eq!(
            store_client2
                .batch_get_theorem_shards(&both_keys, "trusted")?
                .len(),
            2
        );

        let dir_client3 =
            std::env::temp_dir().join(format!("turbo_lean_batch_shard_cli3_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_client3);
        let mut store_client3 = TurboStore::open(Some(&dir_client3))?;
        let partial_items = vec![
            mk_item("batch_shard_key_1", "batch_thm_1", "p1", "s1", "pr1"),
            mk_item("batch_shard_key_3", "batch_thm_3", "p3", "s3", "pr3"),
        ];
        let partial_fast_src = "theorem _turbo_verify_1_batch_thm_1 : 2 + 2 = 4 := rfl\ntheorem _turbo_verify_2_batch_thm_3 : 4 + 4 = 8 := rfl\n";
        let resp3 = offload_check_shards_batch_http(
            &mut store_client3,
            &endpoint,
            &partial_items,
            partial_fast_src,
            "trusted",
            "leanprover/lean4:v4.35.0",
            "",
        )?;
        assert!(resp3.ok && resp3.cache_hits == 1 && resp3.verified_count == 1);

        std::env::remove_var("TURBO_LEAN_API_TOKEN");
        for d in [&dir_server, &dir_client, &dir_client2, &dir_client3] {
            let _ = fs::remove_dir_all(d);
        }
        Ok(())
    }

    #[test]
    fn test_zygote_worker_in_memory_env_reuse() -> Result<()> {
        let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
        let dir_server =
            std::env::temp_dir().join(format!("turbo_lean_zygote_srv_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_server);
        let iso_lp = dir_server.join("isolated_lean_path");
        fs::create_dir_all(&iso_lp)?;
        let iso_lp_str = iso_lp.to_string_lossy().to_string();
        let _ = TurboStore::open(Some(&dir_server))?;

        let endpoint = format!("http://{}/check-shard", spawn_test_server(&dir_server)?);
        let mk_req = |decl: &str, src: &str, stmt: &str, proof: &str| CheckShardHttpRequest {
            decl: decl.into(),
            shard_key: format!("shard_key_{}", decl),
            shard_source: src.into(),
            interface_hash: "iface_z".into(),
            prefix_env_hash: "prefix_z".into(),
            stmt_hash: stmt.into(),
            proof_hash: proof.into(),
            toolchain: "leanprover/lean4:v4.35.0".into(),
            lean_path: iso_lp_str.clone(),
            skip_cas_lock: false,
            allowed_axioms: None,
            lean_args: Vec::new(),
        };
        let post = |req: &CheckShardHttpRequest| -> Result<serde_json::Value> {
            Ok(serde_json::from_slice(&http_request(
                "POST",
                &endpoint,
                "application/json",
                &serde_json::to_vec(req)?,
            )?)?)
        };

        let resp1 = post(&mk_req(
            "zygote_thm_a",
            "import Init\ntheorem zygote_thm_a (a b : Nat) : a + b = b + a := by omega\n",
            "stmt_za",
            "proof_za",
        ))?;
        assert_eq!(
            (resp1["status"].as_str(), resp1["zygote_used"].as_bool()),
            (Some("remote_theorem_verified"), Some(true))
        );

        let resp2 = post(&mk_req(
            "zygote_thm_b",
            "import Init\ntheorem zygote_thm_b (x : Nat) : x + 0 = x := by omega\n",
            "stmt_zb",
            "proof_zb",
        ))?;
        assert_eq!(
            (
                resp2["status"].as_str(),
                resp2["zygote_used"].as_bool(),
                resp2["zygote_env_cache_hit"].as_bool(),
                resp2["zygote_import_us"].as_u64()
            ),
            (
                Some("remote_theorem_verified"),
                Some(true),
                Some(true),
                Some(0)
            )
        );

        assert!(http_request(
            "POST",
            &endpoint,
            "application/json",
            &serde_json::to_vec(&mk_req(
                "zygote_thm_bad",
                "import Init\ntheorem zygote_thm_bad : 1 = 2 := rfl\n",
                "stmt_zbad",
                "proof_zbad"
            ))?
        )
        .is_err());
        let _ = fs::remove_dir_all(&dir_server);
        Ok(())
    }

    #[test]
    fn test_fastcheck_cold_dynamic_link_and_warm_cache_hit() -> Result<()> {
        let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
        let dir = std::env::temp_dir().join(format!(
            "turbo_lean_fc_cold_dyn_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let store = TurboStore::open(Some(&dir))?;
        let req = FastCheckHttpRequest {
            filename: "FastCheck.lean".into(),
            source: "def dummyVal : UInt64 := 42\n".into(),
            gpu: false,
            precomputed_bin_key: String::new(),
            has_main: None,
            local_path: String::new(),
        };
        let res_cold = execute_fastcheck_payload(&store, &req)?;
        assert_eq!(
            (
                res_cold["status"].as_str(),
                res_cold["compile_cache_hit"].as_bool()
            ),
            (Some("ok"), Some(false))
        );
        assert!(res_cold["output"]
            .as_str()
            .unwrap_or("")
            .contains("Checked 1,000,000 256-bit states"));
        let res_warm = execute_fastcheck_payload(&store, &req)?;
        assert_eq!(
            (
                res_warm["status"].as_str(),
                res_warm["compile_cache_hit"].as_bool(),
                res_warm["binary_cache_key"].as_str()
            ),
            (
                Some("ok"),
                Some(true),
                res_cold["binary_cache_key"].as_str()
            )
        );
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_zygote_parallel_cross_file_shard_eval() -> Result<()> {
        let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
        let dir =
            std::env::temp_dir().join(format!("turbo_lean_zygote_par_cross_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir);
        let iso_lp = dir.join("isolated_lean_path");
        fs::create_dir_all(&iso_lp)?;
        let mut store = TurboStore::open(Some(&dir))?;
        let req = CheckShardHttpRequest {
            decl: "__batch__".into(),
            shard_key: "shard_key_par_cross_1".into(),
            shard_source: "import Init\n-- namespace _TurboCrossFileShard_0\n-- end _TurboCrossFileShard_0\ntheorem _turbo_verify_10000_par1 (a b : Nat) : a + b = b + a := Nat.add_comm a b\n-- namespace _TurboCrossFileShard_1\n-- end _TurboCrossFileShard_1\ntheorem _turbo_verify_20000_par2 (x : Nat) : x + 0 = x := rfl\n".into(),
            interface_hash: String::new(),
            prefix_env_hash: String::new(),
            stmt_hash: String::new(),
            proof_hash: String::new(),
            toolchain: "leanprover/lean4:v4.35.0".into(),
            lean_path: iso_lp.to_string_lossy().to_string(),
            skip_cas_lock: true,
            allowed_axioms: None,
            lean_args: Vec::new(),
        };
        let res1 = execute_check_shard_payload(&mut store, &req)?;
        assert_eq!(
            (res1["status"].as_str(), res1["zygote_used"].as_bool()),
            (Some("remote_theorem_verified"), Some(true))
        );
        let res2 = execute_check_shard_payload(&mut store, &req)?;
        assert_eq!(res2["zygote_env_cache_hit"].as_bool(), Some(true));
        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_server_auth_local_path_traversal_and_eval_env_hardening() -> Result<()> {
        let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
        let dir_server = std::env::temp_dir().join(format!("turbo_lean_sec_srv_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_server);
        let _ = TurboStore::open(Some(&dir_server))?;
        let tok = "sec-test-token-20261029";
        let addr = spawn_authed_test_server(&dir_server, tok)?;
        let base = format!("http://{}", addr);

        // 1. Unauthenticated access to protected routes is rejected with HTTP 401
        let unauth_err = http_request_with_timeout_and_token(
            "POST",
            &format!("{}/eval", base),
            "application/json",
            b"{\"code\":\"#eval 1\"}",
            Some(2_000),
            None,
            || {},
        )
        .unwrap_err()
        .to_string();
        assert!(
            unauth_err.contains("401"),
            "expected 401, got: {}",
            unauth_err
        );

        // 2. Non-loopback bind without token fails closed before binding
        let non_loopback_res =
            run_server_with_auth(Some(&dir_server), "0.0.0.0:0", false, None, false);
        assert!(non_loopback_res.is_err());

        // 3. `/fast-check` rejects `local_path` (no arbitrary server file read) and `precomputed_bin_key` traversal
        let fc_local_err = http_request_with_timeout_and_token(
            "POST",
            &format!("{}/fast-check", base),
            "application/json",
            b"{\"local_path\":\"/etc/passwd\"}",
            Some(2_000),
            Some(tok),
            || {},
        )
        .unwrap_err()
        .to_string();
        assert!(
            fc_local_err.contains("400") && fc_local_err.contains("local_path"),
            "expected 400 on local_path, got: {}",
            fc_local_err
        );

        let fc_trav_err = http_request_with_timeout_and_token(
            "POST",
            &format!("{}/fast-check", base),
            "application/json",
            b"{\"source\":\"def x := 1\",\"precomputed_bin_key\":\"../../../../bin/sh\"}",
            Some(2_000),
            Some(tok),
            || {},
        )
        .unwrap_err()
        .to_string();
        assert!(
            fc_trav_err.contains("400"),
            "expected 400 on precomputed_bin_key traversal, got: {}",
            fc_trav_err
        );

        // 4. `/eval` rejects disallowed environment variables (`LD_PRELOAD`, `PATH`, `LAKE`)
        let eval_env_err = http_request_with_timeout_and_token(
            "POST",
            &format!("{}/eval", base),
            "application/json",
            b"{\"code\":\"#eval 1\",\"env_vars\":{\"LD_PRELOAD\":\"/tmp/evil.so\"}}",
            Some(2_000),
            Some(tok),
            || {},
        )
        .unwrap_err()
        .to_string();
        assert!(
            eval_env_err.contains("400") && eval_env_err.contains("LD_PRELOAD"),
            "expected 400 on disallowed env_vars, got: {}",
            eval_env_err
        );

        // 5. SHA-256 verification fails closed on mismatch
        let sha_err = http_request_full(
            "GET",
            &format!("{}/export", base),
            "application/octet-stream",
            &[],
            Some(2_000),
            Some(tok),
            Some("0000000000000000000000000000000000000000000000000000000000000000"),
            || {},
        )
        .unwrap_err()
        .to_string();
        assert!(
            sha_err.contains("SHA-256 integrity mismatch"),
            "got: {}",
            sha_err
        );

        let dir_empty_pull =
            std::env::temp_dir().join(format!("turbo_lean_empty_pull_sha_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_empty_pull);
        let mut store_empty_pull = TurboStore::open(Some(&dir_empty_pull))?;
        std::env::set_var("TURBO_LEAN_API_TOKEN", tok);
        let _tok_clear = ScopedEnvClear(&["TURBO_LEAN_API_TOKEN"]);
        let init_pull_err = sync_pull_http_with_policy(
            &mut store_empty_pull,
            &base,
            true,
            None,
            None,
            false,
            Some("0000000000000000000000000000000000000000000000000000000000000000"),
        )
        .unwrap_err()
        .to_string();
        assert!(
            init_pull_err.contains("SHA-256 integrity mismatch"),
            "initial empty-store pull must propagate SHA-256 mismatch, got: {}",
            init_pull_err
        );

        let _ = fs::remove_dir_all(&dir_empty_pull);
        let _ = fs::remove_dir_all(&dir_server);
        Ok(())
    }

    #[test]
    fn test_ed25519_signed_pack_trust_domain_isolation_and_non_downgrade() -> Result<()> {
        let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
        let dir_src =
            std::env::temp_dir().join(format!("turbo_lean_pack_sig_src_{}", next_tmp_id()));
        let dir_dst =
            std::env::temp_dir().join(format!("turbo_lean_pack_sig_dst_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_src);
        let _ = fs::remove_dir_all(&dir_dst);
        let mut store_src = TurboStore::open(Some(&dir_src))?;
        let mut store_dst = TurboStore::open(Some(&dir_dst))?;

        let payload = b"verified-shard-payload";
        let bh = store_src.store_immutable_blob(payload, "expr_shard", "trusted", 0)?;
        if let SingleflightOutcome::Leader(lease) =
            store_src.acquire_singleflight("sig-act-1", "v4.35.0", "theorem_shard", "trusted")?
        {
            store_src.publish_action(
                &lease,
                &[BlobEntry {
                    blob_hash: bh.clone(),
                    kind: "expr_shard".into(),
                    size_bytes: payload.len() as u64,
                    rel_path: "thm:sig_decl".into(),
                }],
                1,
                0,
                0,
                "trusted",
            )?;
        }

        // Unattested pack defaults to `untrusted` and is refused when `trusted` is requested without override
        let unsigned_pack = dir_src.join("unsigned.tlpack");
        export_pack_with_signing_key(&store_src, &unsigned_pack, true, None)?;
        assert!(import_pack_with_policy(
            &mut store_dst,
            &unsigned_pack,
            Some("trusted"),
            None,
            false
        )
        .is_err());
        import_pack_with_policy(&mut store_dst, &unsigned_pack, None, None, false)?;
        assert!(store_dst
            .batch_get_theorem_shards(&["sig-act-1".into()], "trusted")?
            .is_empty());
        assert_eq!(
            store_dst
                .batch_get_theorem_shards(&["sig-act-1".into()], "untrusted")?
                .len(),
            1
        );

        // Signed pack with Ed25519 key promotes to `trusted`, and subsequent untrusted import cannot downgrade it
        let sk_hex = "1111111111111111111111111111111111111111111111111111111111111111";
        let pk_hex = crate::receipt::ed25519_verifying_key_hex(&[0x11u8; 32]);
        let wrong_pk_hex = crate::receipt::ed25519_verifying_key_hex(&[0x22u8; 32]);
        let signed_pack = dir_src.join("signed.tlpack");
        export_pack_with_signing_key(&store_src, &signed_pack, true, Some(sk_hex))?;

        assert!(import_pack_with_policy(
            &mut store_dst,
            &signed_pack,
            Some("trusted"),
            Some(&wrong_pk_hex),
            false
        )
        .is_err());
        import_pack_with_policy(
            &mut store_dst,
            &signed_pack,
            Some("trusted"),
            Some(&pk_hex),
            false,
        )?;
        assert_eq!(
            store_dst
                .batch_get_theorem_shards(&["sig-act-1".into()], "trusted")?
                .len(),
            1
        );
        // Re-importing unsigned pack into `untrusted` must NOT downgrade existing `trusted` action/blob
        import_pack_with_policy(
            &mut store_dst,
            &unsigned_pack,
            Some("untrusted"),
            None,
            false,
        )?;
        assert_eq!(
            store_dst
                .batch_get_theorem_shards(&["sig-act-1".into()], "trusted")?
                .len(),
            1
        );

        let _ = fs::remove_dir_all(&dir_src);
        let _ = fs::remove_dir_all(&dir_dst);
        Ok(())
    }

    #[test]
    fn test_configured_pubkey_honored_over_allow_unattested_and_trusted_promotion_replaces_outputs(
    ) -> Result<()> {
        let _env_guard = env_test_lock().lock().unwrap_or_else(|e| e.into_inner());
        let dir_untrusted_src =
            std::env::temp_dir().join(format!("turbo_lean_pack_ut_src_{}", next_tmp_id()));
        let dir_trusted_src =
            std::env::temp_dir().join(format!("turbo_lean_pack_tr_src_{}", next_tmp_id()));
        let dir_dst =
            std::env::temp_dir().join(format!("turbo_lean_pack_promo_dst_{}", next_tmp_id()));
        let dir_wt =
            std::env::temp_dir().join(format!("turbo_lean_pack_promo_wt_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_untrusted_src);
        let _ = fs::remove_dir_all(&dir_trusted_src);
        let _ = fs::remove_dir_all(&dir_dst);
        let _ = fs::remove_dir_all(&dir_wt);
        fs::create_dir_all(&dir_wt)?;

        let mut store_ut = TurboStore::open(Some(&dir_untrusted_src))?;
        let mut store_tr = TurboStore::open(Some(&dir_trusted_src))?;
        let mut store_dst = TurboStore::open(Some(&dir_dst))?;

        let good_payload = b"legit-olean-bytes";
        let evil_payload = b"injected-untrusted-extra-olean";
        let good_bh = store_ut.store_immutable_blob(good_payload, "olean", "trusted", 0)?;
        let evil_bh = store_ut.store_immutable_blob(evil_payload, "olean", "trusted", 0)?;
        if let SingleflightOutcome::Leader(lease) =
            store_ut.acquire_singleflight("mod-act-promo", "v4.35.0", "module_unit", "trusted")?
        {
            store_ut.publish_action(
                &lease,
                &[
                    BlobEntry {
                        blob_hash: good_bh.clone(),
                        kind: "olean".into(),
                        size_bytes: good_payload.len() as u64,
                        rel_path: "build/lib/lean/Good.olean".into(),
                    },
                    BlobEntry {
                        blob_hash: evil_bh.clone(),
                        kind: "olean".into(),
                        size_bytes: evil_payload.len() as u64,
                        rel_path: "build/lib/lean/EvilInjected.olean".into(),
                    },
                ],
                1,
                0,
                0,
                "trusted",
            )?;
        }
        let unsigned_extra_pack = dir_untrusted_src.join("unsigned_extra.tlpack");
        export_pack_with_signing_key(&store_ut, &unsigned_extra_pack, true, None)?;

        let good_bh_tr = store_tr.store_immutable_blob(good_payload, "olean", "trusted", 0)?;
        assert_eq!(good_bh, good_bh_tr);
        if let SingleflightOutcome::Leader(lease) =
            store_tr.acquire_singleflight("mod-act-promo", "v4.35.0", "module_unit", "trusted")?
        {
            store_tr.publish_action(
                &lease,
                &[BlobEntry {
                    blob_hash: good_bh_tr.clone(),
                    kind: "olean".into(),
                    size_bytes: good_payload.len() as u64,
                    rel_path: "build/lib/lean/Good.olean".into(),
                }],
                1,
                0,
                0,
                "trusted",
            )?;
        }
        let sk_hex = "3333333333333333333333333333333333333333333333333333333333333333";
        let pk_hex = crate::receipt::ed25519_verifying_key_hex(&[0x33u8; 32]);
        let wrong_pk_hex = crate::receipt::ed25519_verifying_key_hex(&[0x44u8; 32]);
        let signed_clean_pack = dir_trusted_src.join("signed_clean.tlpack");
        export_pack_with_signing_key(&store_tr, &signed_clean_pack, true, Some(sk_hex))?;

        // 1. When a trusted pubkey is configured, `--allow-unattested-trusted` with `requested_domain = None`
        //    MUST NOT admit an unsigned pack into `trusted` (quarantines to `untrusted`), and MUST fail closed
        //    when `requested_domain = Some("trusted")` or when signature verification fails.
        assert!(import_pack_with_policy(
            &mut store_dst,
            &unsigned_extra_pack,
            Some("trusted"),
            Some(&pk_hex),
            true,
        )
        .is_err());
        assert!(import_pack_with_policy(
            &mut store_dst,
            &signed_clean_pack,
            None,
            Some(&wrong_pk_hex),
            true,
        )
        .is_err());
        import_pack_with_policy(
            &mut store_dst,
            &unsigned_extra_pack,
            None,
            Some(&pk_hex),
            true,
        )?;
        assert!(store_dst
            .get_cached_action("mod-act-promo", "trusted")?
            .is_none());
        let untrusted_outs = store_dst
            .get_cached_action("mod-act-promo", "untrusted")?
            .expect("quarantined in untrusted");
        assert_eq!(untrusted_outs.len(), 2);

        // 2. Importing a legitimately signed pack for `mod-act-promo` promotes it to `trusted` AND atomically
        //    replaces `action_outputs`, purging `EvilInjected.olean` so it is never returned or materialized.
        import_pack_with_policy(
            &mut store_dst,
            &signed_clean_pack,
            None,
            Some(&pk_hex),
            true,
        )?;
        let trusted_outs = store_dst
            .get_cached_action("mod-act-promo", "trusted")?
            .expect("promoted to trusted");
        assert_eq!(trusted_outs.len(), 1);
        assert_eq!(trusted_outs[0].rel_path, "build/lib/lean/Good.olean");
        assert_eq!(trusted_outs[0].blob_hash, good_bh);

        store_dst.materialize_into_worktree(&dir_wt, "promo-test", &trusted_outs)?;
        assert!(dir_wt.join("build/lib/lean/Good.olean").exists());
        assert!(!dir_wt.join("build/lib/lean/EvilInjected.olean").exists());

        // 3. Atomic single-file deferred pack record (`TLDP\x00\x00\x00\x04` + domain byte + V3 header)
        //    preserves `untrusted` across concurrent `TurboStore::open` calls and legacy header-only fallback.
        let dir_cold =
            std::env::temp_dir().join(format!("turbo_lean_pack_cold_def_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_cold);
        fs::create_dir_all(&dir_cold)?;
        let (_, _, raw_hdr) = read_pack_header_from_file(&unsigned_extra_pack).unwrap();
        let mut raw_v3 = Vec::with_capacity(16 + raw_hdr.len());
        raw_v3.extend_from_slice(b"TLPK\x00\x00\x00\x03");
        raw_v3.extend_from_slice(&(raw_hdr.len() as u64).to_le_bytes());
        raw_v3.extend_from_slice(&raw_hdr);
        assert_eq!(
            decode_deferred_pack_record(&raw_v3).map(|(td, _)| td),
            Some("untrusted")
        );
        assert!(try_stateless_cold_import_with_domain(
            &dir_cold,
            &unsigned_extra_pack,
            None,
            Some(&pk_hex),
            true,
        )
        .is_some());
        let c1 = dir_cold.clone();
        let c2 = dir_cold.clone();
        let h1 = std::thread::spawn(move || TurboStore::open(Some(&c1)));
        let h2 = std::thread::spawn(move || TurboStore::open(Some(&c2)));
        let s1 = h1.join().unwrap()?;
        let s2 = h2.join().unwrap()?;
        assert!(s1.get_cached_action("mod-act-promo", "trusted")?.is_none());
        assert!(s2.get_cached_action("mod-act-promo", "trusted")?.is_none());
        assert!(s1
            .get_cached_action("mod-act-promo", "untrusted")?
            .is_some());
        assert!(s2
            .get_cached_action("mod-act-promo", "untrusted")?
            .is_some());

        // 4. Plain HTTP `X-Turbo-Pack-Sha256` response header mismatch fails closed even with `expected_sha256 = None`
        let bad_sha_listener = TcpListener::bind("127.0.0.1:0")?;
        let bad_sha_addr = bad_sha_listener.local_addr()?;
        std::thread::spawn(move || {
            if let Ok((mut sock, _)) = bad_sha_listener.accept() {
                let mut rbuf = [0u8; 512];
                let _ = sock.read(&mut rbuf);
                let resp = b"HTTP/1.1 200 OK\r\nContent-Length: 4\r\nX-Turbo-Pack-Sha256: ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\r\n\r\ntest";
                let _ = sock.write_all(resp);
            }
        });
        let hdr_sha_err = http_request_full(
            "GET",
            &format!("http://{}/export", bad_sha_addr),
            "application/octet-stream",
            &[],
            Some(2_000),
            None,
            None,
            || {},
        )
        .unwrap_err()
        .to_string();
        assert!(
            hdr_sha_err.contains("SHA-256 integrity mismatch"),
            "expected header SHA-256 mismatch error, got: {}",
            hdr_sha_err
        );

        // 5. Daemon mode (`TURBO_LEAN_DAEMON=1`) honors `TURBO_LEAN_DAEMON_TOKEN` ahead of inherited `TURBO_LEAN_API_TOKEN`
        assert_eq!(
            crate::server::resolve_server_auth_token(
                None,
                true,
                Some("remote-coordinator-token"),
                Some("local-daemon-token-xyz"),
            ),
            Some("local-daemon-token-xyz".to_string())
        );
        assert_eq!(
            crate::server::resolve_server_auth_token(
                None,
                false,
                Some("remote-coordinator-token"),
                Some("local-daemon-token-xyz"),
            ),
            Some("remote-coordinator-token".to_string())
        );
        assert_eq!(
            crate::server::resolve_server_auth_token(
                Some("explicit-cli-token"),
                true,
                Some("remote-coordinator-token"),
                Some("local-daemon-token-xyz"),
            ),
            Some("explicit-cli-token".to_string())
        );

        let _ = fs::remove_dir_all(&dir_cold);
        let _ = fs::remove_dir_all(&dir_untrusted_src);
        let _ = fs::remove_dir_all(&dir_trusted_src);
        let _ = fs::remove_dir_all(&dir_dst);
        let _ = fs::remove_dir_all(&dir_wt);
        Ok(())
    }
}

pub type PrefetchedExportItem = (
    Vec<u8>,
    Option<(PackManifest, Vec<(String, String, i64, i64)>, usize)>,
);

/// Execute `turbo-lean export`.
pub fn run_export_command(
    store: &TurboStore,
    json: bool,
    output: std::path::PathBuf,
    portable_only: bool,
    signing_key: Option<String>,
) -> Result<()> {
    let (acts, blobs, bytes) =
        export_pack_with_signing_key(store, &output, portable_only, signing_key.as_deref())?;
    if json {
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
                "exported_actions": acts, "exported_blobs": blobs,
                "raw_bytes": bytes, "archive": output.display().to_string()
            }))?
        );
    } else {
        println!(
            "[turbo-lean] Exported {} actions and {} portable blobs ({:.2} MiB raw) to {}",
            acts,
            blobs,
            bytes as f64 / (1024.0 * 1024.0),
            output.display()
        );
    }
    Ok(())
}

/// Execute `turbo-lean import`.
pub fn run_import_command(
    store: &mut TurboStore,
    json: bool,
    input: std::path::PathBuf,
    trust_domain: Option<String>,
    trusted_pubkey: Option<String>,
    allow_unattested_trusted: bool,
    expected_sha256: Option<String>,
    prefetched: Option<
        std::thread::JoinHandle<Option<(PackManifest, Vec<(String, String, i64, i64)>, usize)>>,
    >,
) -> Result<()> {
    let req_td = trust_domain.as_deref();
    let pk_opt = trusted_pubkey.as_deref();
    let env_sha = std::env::var("TURBO_LEAN_PACK_EXPECTED_SHA256")
        .ok()
        .filter(|s| !s.trim().is_empty());
    let sha_opt = expected_sha256.as_deref().or(env_sha.as_deref());
    let (acts, blobs) = if let Some(exp_sha) = sha_opt {
        if let Some(h) = prefetched {
            let _ = h.join();
        }
        let raw_bytes = fs::read(&input)
            .with_context(|| format!("Failed to read pack file {}", input.display()))?;
        verify_optional_sha256(
            &raw_bytes,
            None,
            Some(exp_sha),
            &input.display().to_string(),
        )?;
        import_pack_bytes_with_policy(store, &raw_bytes, req_td, pk_opt, allow_unattested_trusted)?
    } else if let Some((manifest, staged_blobs, newly_written)) =
        prefetched.and_then(|h| h.join().ok().flatten())
    {
        let td =
            resolve_pack_import_trust_domain(&manifest, req_td, pk_opt, allow_unattested_trusted)?;
        finish_import_from_prestaged_shared_cas_with_domain(
            store,
            &manifest,
            &staged_blobs,
            newly_written,
            td,
        )?
    } else {
        import_pack_with_policy(store, &input, req_td, pk_opt, allow_unattested_trusted)?
    };
    if json {
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
                "imported_actions": acts, "imported_blobs": blobs, "archive": input.display().to_string()
            }))?
        );
    } else {
        println!(
            "[turbo-lean] Imported & BLAKE3-verified {} actions and {} blobs from {}",
            acts,
            blobs,
            input.display()
        );
    }
    Ok(())
}

/// Execute `turbo-lean sync`.
pub fn run_sync_command(
    store: &mut TurboStore,
    json: bool,
    remote: String,
    push: bool,
    bidirectional: bool,
    trust_domain: Option<String>,
    trusted_pubkey: Option<String>,
    allow_unattested_trusted: bool,
    expected_sha256: Option<String>,
    mut prefetched_export: Option<std::thread::JoinHandle<Result<PrefetchedExportItem>>>,
    mut prefetched_manifest: Option<std::thread::JoinHandle<Option<DeltaManifest>>>,
) -> Result<()> {
    let t0 = std::time::Instant::now();
    if !remote.starts_with("http://") && !remote.starts_with("https://") {
        anyhow::bail!(
            "Unsupported remote scheme `{}` (use http://host:port or export/import)",
            remote
        );
    }
    let req_td = trust_domain.as_deref();
    let pk_opt = trusted_pubkey.as_deref();
    let sha_opt = expected_sha256.as_deref();
    let print_sync_report = |mode: &str,
                             pulled: (usize, usize),
                             pulled_bytes: u64,
                             pushed: (usize, usize, u64),
                             pushed_pack_bytes: u64,
                             delta_push_noop: bool|
     -> Result<()> {
        let elapsed_ms = t0.elapsed().as_millis();
        if json {
            println!(
                "{}",
                serde_json::to_string_pretty(&serde_json::json!({
                    "status": "synced", "mode": mode, "remote": remote,
                    "pulled_actions": pulled.0, "pulled_blobs": pulled.1, "pulled_pack_bytes": pulled_bytes,
                    "pushed_actions": pushed.0, "pushed_blobs": pushed.1, "pushed_raw_bytes": pushed.2,
                    "pushed_pack_bytes": pushed_pack_bytes, "delta_push_noop": delta_push_noop, "elapsed_ms": elapsed_ms
                }))?
            );
        } else if mode == "push_only" {
            println!(
                "[turbo-lean] Delta-pushed to {} in {} ms: {} actions ({} blobs, {} bytes)",
                remote, elapsed_ms, pushed.0, pushed.1, pushed_pack_bytes
            );
        } else {
            println!("[turbo-lean] Synced with {} in {} ms: pulled {} actions ({} blobs), pushed {} actions ({} blobs)", remote, elapsed_ms, pulled.0, pulled.1, pushed.0, pushed.1);
        }
        Ok(())
    };

    if push && !bidirectional {
        let pre_man = prefetched_manifest
            .take()
            .and_then(|h| h.join().ok().flatten());
        let (pushed_acts, pushed_blobs, pushed_raw, pushed_pack, delta_push_noop) =
            sync_push_http_with_manifest(store, &remote, true, pre_man)?;
        return print_sync_report(
            "push_only",
            (0, 0),
            0,
            (pushed_acts, pushed_blobs, pushed_raw),
            pushed_pack,
            delta_push_noop,
        );
    }
    if !bidirectional {
        let mut pulled = (0usize, 0usize);
        let mut pulled_bytes = 0u64;
        if let Some(handle) = prefetched_export.take() {
            match handle.join() {
                Ok(Ok((pack_bytes, prestaged_opt))) => {
                    verify_optional_sha256(&pack_bytes, None, sha_opt, &remote)?;
                    if !pack_bytes.is_empty() {
                        pulled =
                            if let Some((manifest, staged_blobs, newly_written)) = prestaged_opt {
                                let td = resolve_pack_import_trust_domain(
                                    &manifest,
                                    req_td,
                                    pk_opt,
                                    allow_unattested_trusted,
                                )?;
                                finish_import_from_prestaged_shared_cas_with_domain(
                                    store,
                                    &manifest,
                                    &staged_blobs,
                                    newly_written,
                                    td,
                                )?
                            } else {
                                import_pack_bytes_with_policy(
                                    store,
                                    &pack_bytes,
                                    req_td,
                                    pk_opt,
                                    allow_unattested_trusted,
                                )?
                            };
                        if pulled.0 > 0 || pulled.1 > 0 {
                            pulled_bytes = pack_bytes.len() as u64;
                        }
                    }
                }
                Ok(Err(e)) => return Err(e),
                Err(_) => {
                    (pulled, pulled_bytes) = sync_pull_http_with_policy(
                        store,
                        &remote,
                        true,
                        req_td,
                        pk_opt,
                        allow_unattested_trusted,
                        sha_opt,
                    )?
                }
            }
        } else {
            (pulled, pulled_bytes) = sync_pull_http_with_policy(
                store,
                &remote,
                true,
                req_td,
                pk_opt,
                allow_unattested_trusted,
                sha_opt,
            )?;
        }
        return print_sync_report("bidirectional", pulled, pulled_bytes, (0, 0, 0), 0, true);
    }

    let base = remote.trim_end_matches('/');
    let local_manifest = get_store_manifest(store, true)?;
    let mut pulled = (0usize, 0usize);
    let mut pulled_bytes = 0u64;
    let mut pushed = (0usize, 0usize, 0u64);
    let mut pushed_pack_bytes = 0u64;

    if local_manifest.action_keys.is_empty() && local_manifest.blob_hashes.is_empty() {
        let pack_bytes = http_request_with_expected_sha256(
            "GET",
            &format!("{}/export", base),
            "application/octet-stream",
            &[],
            sha_opt,
        )?;
        if !pack_bytes.is_empty() {
            pulled = import_pack_bytes_with_policy(
                store,
                &pack_bytes,
                req_td,
                pk_opt,
                allow_unattested_trusted,
            )?;
            if pulled.0 > 0 || pulled.1 > 0 {
                pulled_bytes = pack_bytes.len() as u64;
            }
        }
    } else {
        let local_action_set: std::collections::HashSet<String> =
            local_manifest.action_keys.iter().cloned().collect();
        let local_blob_set: std::collections::HashSet<String> =
            local_manifest.blob_hashes.iter().cloned().collect();
        let remote_manifest: DeltaManifest = http_request(
            "GET",
            &format!("{}/manifest", base),
            "application/json",
            &[],
        )
        .ok()
        .and_then(|bytes| serde_json::from_slice(&bytes).ok())
        .unwrap_or_default();
        let remote_action_set: std::collections::HashSet<String> =
            remote_manifest.action_keys.iter().cloned().collect();
        let remote_blob_set: std::collections::HashSet<String> =
            remote_manifest.blob_hashes.iter().cloned().collect();

        let need_pull = remote_manifest
            .action_keys
            .iter()
            .any(|k| !local_action_set.contains(k))
            || remote_manifest
                .blob_hashes
                .iter()
                .any(|b| !local_blob_set.contains(b));
        if need_pull {
            let delta_req = serde_json::to_vec(&ExportDeltaRequest {
                exclude_actions: local_manifest.action_keys.clone(),
                exclude_blobs: local_manifest.blob_hashes.clone(),
            })?;
            let pack_bytes = http_request_with_expected_sha256(
                "POST",
                &format!("{}/export-delta", base),
                "application/json",
                &delta_req,
                sha_opt,
            )?;
            if !pack_bytes.is_empty() {
                pulled_bytes = pack_bytes.len() as u64;
                pulled = import_pack_bytes_with_policy(
                    store,
                    &pack_bytes,
                    req_td,
                    pk_opt,
                    allow_unattested_trusted,
                )?;
            }
        }

        let need_push = local_manifest
            .action_keys
            .iter()
            .any(|k| !remote_action_set.contains(k))
            || local_manifest
                .blob_hashes
                .iter()
                .any(|b| !remote_blob_set.contains(b));
        if need_push {
            let (p_acts, p_blobs, p_raw, push_bytes) =
                export_pack_filtered_bytes(store, true, &remote_action_set, &remote_blob_set)?;
            pushed = (p_acts, p_blobs, p_raw);
            if pushed.0 > 0 || pushed.1 > 0 {
                pushed_pack_bytes = push_bytes.len() as u64;
                let _ = http_request(
                    "POST",
                    &format!("{}/import-delta", base),
                    "application/octet-stream",
                    &push_bytes,
                )?;
            }
        }
    }
    print_sync_report(
        "bidirectional",
        pulled,
        pulled_bytes,
        pushed,
        pushed_pack_bytes,
        pushed.0 == 0 && pushed.1 == 0,
    )
}
