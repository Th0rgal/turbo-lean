use crate::db::{now_unix, ActionRecord, BlobEntry, SingleflightOutcome, TurboStore};
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs;
use std::io::{BufRead, BufReader, Read, Write};
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
         WHERE a.status = 'completed' AND a.trust_domain = 'trusted'
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
    Ok(DeltaManifest {
        action_keys,
        blob_hashes,
    })
}

pub fn export_pack(
    store: &TurboStore,
    output_path: &Path,
    only_portable: bool,
) -> Result<(usize, usize, u64)> {
    export_pack_filtered(
        store,
        output_path,
        only_portable,
        &HashSet::new(),
        &HashSet::new(),
    )
}

static PACK_TMP_SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

fn next_tmp_id() -> String {
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
    std::env::temp_dir()
        .join(format!("turbo_lean_shared_cas_{}", uid))
        .join("blobs")
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
    let src = store.blob_path(bh);
    if fs::hard_link(&src, &shared_dest).is_ok() {
        return true;
    }
    if shared_dest.exists() {
        return true;
    }
    fs::copy(&src, &shared_dest).is_ok()
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
    let full_export_cache_path =
        if !header_only_shared_cas && exclude_actions.is_empty() && exclude_blobs.is_empty() {
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
                        "pack_exp_v2_{}_{}_{}_{}_{}.bin",
                        root_tag,
                        fseq,
                        act_cnt,
                        blob_cnt,
                        if only_portable { 1 } else { 0 }
                    ));
                    if let Ok(mut cached_bytes) = fs::read(&cache_file) {
                        if cached_bytes.len() >= 24 {
                            let mut b0 = [0u8; 8];
                            let mut b1 = [0u8; 8];
                            let mut b2 = [0u8; 8];
                            b0.copy_from_slice(&cached_bytes[0..8]);
                            b1.copy_from_slice(&cached_bytes[8..16]);
                            b2.copy_from_slice(&cached_bytes[16..24]);
                            let n_acts = u64::from_le_bytes(b0) as usize;
                            let n_blobs = u64::from_le_bytes(b1) as usize;
                            let raw_bytes = u64::from_le_bytes(b2);
                            let stream = cached_bytes.split_off(24);
                            return Ok((n_acts, n_blobs, raw_bytes, stream));
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

    let mut stmt = store.conn.prepare_cached(
        "SELECT a.action_key, a.toolchain_githash, a.kind, a.status, a.fencing_token,
                COALESCE(a.output_manifest_hash, ''), a.duration_ms, a.peak_pss_bytes, a.heartbeats, a.trust_domain,
                b.blob_hash, b.kind, b.size_bytes, ao.rel_path
         FROM actions a
         JOIN action_outputs ao ON ao.action_key = a.action_key
         JOIN blobs b ON b.blob_hash = ao.blob_hash
         WHERE a.status = 'completed' AND a.trust_domain = 'trusted'
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

    let mut cur_meta: Option<(String, String, String, String, i64, String, i64, i64, i64, String)> =
        None;
    let mut cur_outputs: Vec<BlobEntry> = Vec::new();

    let mut flush_action =
        |meta: (String, String, String, String, i64, String, i64, i64, i64, String),
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

    let shared_blobs = shared_cas_blobs_dir();
    let mut seen_shared_prefix = [false; 256];
    let mut blobs = Vec::with_capacity(needed_blobs.len());
    let mut payload_buf =
        Vec::with_capacity(if header_only_shared_cas { 0 } else { est_raw_bytes });
    let mut total_raw_bytes = 0u64;
    let mut all_in_shared = true;

    for (bh, kind, db_sz) in needed_blobs {
        if header_only_shared_cas {
            if ensure_blob_in_shared_cas(store, &bh, &shared_blobs, &mut seen_shared_prefix) {
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
            let p = store.blob_path(&bh);
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

    let manifest = PackManifest {
        format_version: 2,
        host_arch: std::env::consts::ARCH.to_string(),
        created_at: crate::db::now_unix(),
        actions,
        blobs,
    };

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
    if let Some(cache_file) = full_export_cache_path {
        if pack_stream.len() <= 64 * 1024 * 1024 {
            let mut cache_buf = Vec::with_capacity(24 + pack_stream.len());
            cache_buf.extend_from_slice(&(n_acts as u64).to_le_bytes());
            cache_buf.extend_from_slice(&(n_blobs as u64).to_le_bytes());
            cache_buf.extend_from_slice(&total_raw_bytes.to_le_bytes());
            cache_buf.extend_from_slice(&pack_stream);
            let _ = fs::write(&cache_file, &cache_buf);
        }
    }

    Ok((n_acts, n_blobs, total_raw_bytes, pack_stream))
}

pub fn export_pack_filtered(
    store: &TurboStore,
    output_path: &Path,
    only_portable: bool,
    exclude_actions: &HashSet<String>,
    exclude_blobs: &HashSet<String>,
) -> Result<(usize, usize, u64)> {
    let (n_acts, n_blobs, total_raw_bytes, pack_stream) =
        export_pack_filtered_bytes(store, only_portable, exclude_actions, exclude_blobs)?;

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

fn try_import_from_shared_cas(
    store: &mut TurboStore,
    manifest: &PackManifest,
) -> Result<Option<(usize, usize)>> {
    let shared_blobs = shared_cas_blobs_dir();
    let store_blobs = store.root.join("blobs");

    for b in &manifest.blobs {
        let prefix = if b.blob_hash.len() >= 2 {
            &b.blob_hash[0..2]
        } else {
            "00"
        };
        let shared_p = shared_blobs.join(prefix).join(&b.blob_hash);
        let in_shared = fs::metadata(&shared_p)
            .map(|m| m.len() == b.size_bytes)
            .unwrap_or(false);
        if !in_shared {
            let dest = store_blobs.join(prefix).join(&b.blob_hash);
            let in_store = fs::metadata(&dest)
                .map(|m| m.len() == b.size_bytes)
                .unwrap_or(false);
            if !in_store {
                return Ok(None);
            }
        }
    }

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
            match fs::hard_link(&shared_p, &dest) {
                Ok(()) => {
                    total_newly_written += 1;
                    0i64
                }
                Err(ref e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                    fs::metadata(&dest).map(|m| m.ino() as i64).unwrap_or(0)
                }
                Err(_) => {
                    return Ok(None);
                }
            }
        };
        #[cfg(not(unix))]
        let inode = {
            let shared_p = shared_blobs.join(prefix).join(&b.blob_hash);
            if newly_created_prefix[p_idx] || !dest.exists() {
                if fs::hard_link(&shared_p, &dest).is_err() {
                    return Ok(None);
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

    if total_newly_written == 0 && !manifest.actions.is_empty() {
        let existing_completed: i64 = store
            .conn
            .query_row(
                "SELECT COUNT(*) FROM actions WHERE status = 'completed' AND trust_domain = 'trusted'",
                [],
                |r| r.get(0),
            )
            .unwrap_or(0);
        if (existing_completed as usize) >= manifest.actions.len()
            && manifest
                .actions
                .iter()
                .all(|a| store.has_completed_action(&a.action_key))
        {
            return Ok(Some((manifest.actions.len(), staged_blobs.len())));
        }
    }

    let res = store.batch_import_pack_metadata(&staged_blobs, &manifest.actions)?;
    Ok(Some(res))
}

pub fn import_pack(store: &mut TurboStore, input_path: &Path) -> Result<(usize, usize)> {
    if let Ok(mut f) = fs::File::open(input_path) {
        if let Ok(meta) = f.metadata() {
            let file_len = meta.len();
            if file_len >= 16 {
                let mut prefix = [0u8; 16];
                if f.read_exact(&mut prefix).is_ok()
                    && (&prefix[0..8] == b"TLPK\x00\x00\x00\x02"
                        || &prefix[0..8] == b"TLPK\x00\x00\x00\x03")
                {
                    let mut len_buf = [0u8; 8];
                    len_buf.copy_from_slice(&prefix[8..16]);
                    let header_len = u64::from_le_bytes(len_buf) as usize;
                    if 16 + (header_len as u64) <= file_len {
                        let mut header_buf = vec![0u8; header_len];
                        if f.read_exact(&mut header_buf).is_ok() {
                            if let Ok(manifest) =
                                serde_json::from_slice::<PackManifest>(&header_buf)
                            {
                                let expected_payload: u64 =
                                    manifest.blobs.iter().map(|b| b.size_bytes).sum();
                                let size_ok = &prefix[0..8] == b"TLPK\x00\x00\x00\x03"
                                    || 16 + (header_len as u64) + expected_payload == file_len;
                                if size_ok {
                                    if let Some(res) =
                                        try_import_from_shared_cas(store, &manifest)?
                                    {
                                        return Ok(res);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    let input_bytes = fs::read(input_path)?;
    import_pack_bytes(store, &input_bytes)
}

pub fn import_pack_bytes(store: &mut TurboStore, input_bytes: &[u8]) -> Result<(usize, usize)> {
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

    let expected_payload: usize = manifest.blobs.iter().map(|b| b.size_bytes as usize).sum();
    if is_v3_header_only
        || (!payload_region.is_empty() && payload_region.len() == expected_payload)
    {
        if let Some(res) = try_import_from_shared_cas(store, &manifest)? {
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
                        let staging_path = staging_dir_ref
                            .join(format!("{}.{}.tmp", b.blob_hash, next_tmp_id()));
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
                handles.push(
                    s.spawn(move || process_chunk(chunk, &root_clone, staging_dir_ref, new_prefixes_ref)),
                );
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
                "SELECT COUNT(*) FROM actions WHERE status = 'completed' AND trust_domain = 'trusted'",
                [],
                |r| r.get(0),
            )
            .unwrap_or(0);
        if (existing_completed as usize) >= manifest.actions.len()
            && manifest
                .actions
                .iter()
                .all(|a| store.has_completed_action(&a.action_key))
        {
            return Ok((manifest.actions.len(), staged_blobs.len()));
        }
    }

    store.batch_import_pack_metadata(&staged_blobs, &manifest.actions)
}

/// Lightweight HTTP Server (`turbo-lean serve`) for remote CAS sync & GPU/CPU offload (e.g., on DGX Spark)
pub fn run_server(store_root: Option<&Path>, listen_addr: &str, gpu_enable: bool) -> Result<()> {
    let listener = TcpListener::bind(listen_addr)
        .with_context(|| format!("Failed to bind turbo-lean server on {}", listen_addr))?;
    if let Ok(state_path) = std::env::var("TURBO_LEAN_DAEMON_STATE_FILE") {
        if let Ok(current_exe) = std::env::current_exe() {
            let (exe_mtime_sec, exe_mtime_nsec, _) = fs::metadata(&current_exe)
                .ok()
                .map(|m| TurboStore::extract_file_stat_tuple(&m))
                .unwrap_or((0, 0, 0));
            let info = LocalZygoteDaemonInfo {
                addr: listen_addr.to_string(),
                pid: std::process::id(),
                exe_mtime_sec,
                exe_mtime_nsec,
            };
            if let Ok(json_bytes) = serde_json::to_vec(&info) {
                let _ = fs::write(&state_path, &json_bytes);
            }
        }
    }
    let mut store = TurboStore::open(store_root)?;
    let mut local_mutation_seq: u64 = 0;
    let query_data_version = |st: &TurboStore| -> i64 {
        st.conn
            .query_row("PRAGMA data_version", [], |r| r.get::<_, i64>(0))
            .unwrap_or(0)
    };
    let init_dv = query_data_version(&store);
    let mut cached_manifest: Option<((i64, u64), DeltaManifest, Vec<u8>)> =
        get_store_manifest(&store, true)
            .ok()
            .and_then(|m| serde_json::to_vec(&m).ok().map(|b| (m, b)))
            .map(|(m, b)| ((init_dv, local_mutation_seq), m, b));
    let mut cached_export_local: Option<((i64, u64), Vec<u8>)> =
        export_pack_filtered_with_mode(&store, true, &HashSet::new(), &HashSet::new(), true)
            .ok()
            .map(|(_, _, _, b)| ((init_dv, local_mutation_seq), b));
    let mut cached_export: Option<((i64, u64), Vec<u8>)> = None;

    #[cfg(not(test))]
    {
        let store_root_owned = store_root.map(|p| p.to_path_buf());
        let prewarm = std::thread::spawn(move || {
            if let Ok(bg_store) = TurboStore::open(store_root_owned.as_deref()) {
                let lp = Path::new(env!("CARGO_MANIFEST_DIR"))
                    .parent()
                    .and_then(|p| p.parent())
                    .map(|r| r.join("lean/.lake/build/lib/lean"))
                    .filter(|p| p.join("TurboLean/Reflection.olean").exists())
                    .map(|p| p.to_string_lossy().to_string())
                    .unwrap_or_default();
                let (env_vars, lean_bin) =
                    resolve_server_lean_env_and_bin(&bg_store, "leanprover/lean4:v4.31.0", &lp);
                let _ = prewarm_shared_fastcheck_harness(&bg_store, &lean_bin, &env_vars);
                if !lp.is_empty() {
                    let warm_src = "import TurboLean.Assembler\nimport TurboLean.FastCheck\nimport TurboLean.Inspector\nimport TurboLean.Reflection\nnamespace TurboLean.Reflection\ntheorem _turbo_prewarm_refl {s : ContractState} {k : StorageKey} {v : Nat} : getStorage (setStorage s k v) k = v := by exact getStorage_setStorage_same\nend TurboLean.Reflection\nnamespace TurboLean.FastCheck\ntheorem _turbo_prewarm_fc (a : Word256) : (Word256.addWithCarry a Word256.zero).2 = false := by exact addWithCarry_zero_right a\ntheorem _turbo_prewarm_fc2 (a b : Word256) : (Word256.addWithCarry a b).1.w0 = (Word256.addWithCarry b a).1.w0 := by exact addWithCarry_comm_low a b\nend TurboLean.FastCheck\n";
                    let _ = eval_with_zygote_pool(
                        &bg_store,
                        "leanprover/lean4:v4.31.0",
                        &lp,
                        &env_vars,
                        &lean_bin,
                        warm_src,
                        true,
                    );
                }
            }
        });
        if std::env::var("TURBO_LEAN_DAEMON").is_err() {
            let _ = prewarm.join();
        }
    }
    println!(
        "{{\"status\":\"listening\",\"addr\":\"{}\",\"arch\":\"{}\",\"gpu_enabled\":{}}}",
        listen_addr,
        std::env::consts::ARCH,
        gpu_enable
    );

    for stream in listener.incoming() {
        let mut stream = match stream {
            Ok(s) => s,
            Err(_) => continue,
        };
        let _ = stream.set_nodelay(true);
        let cloned = match stream.try_clone() {
            Ok(c) => c,
            Err(_) => continue,
        };
        let mut reader = BufReader::new(cloned);
        let mut req_line = String::new();
        if reader.read_line(&mut req_line).is_err() {
            continue;
        }
        let parts: Vec<&str> = req_line.split_whitespace().collect();
        if parts.len() < 2 {
            continue;
        }
        let (method, path) = (parts[0], parts[1]);

        let mut content_len = 0usize;
        let mut hline = String::with_capacity(128);
        loop {
            hline.clear();
            if reader.read_line(&mut hline).is_err() || hline.trim().is_empty() {
                break;
            }
            if hline.len() >= 15 && hline[..15].eq_ignore_ascii_case("content-length:") {
                content_len = hline[15..].trim().parse().unwrap_or(0);
            }
        }

        let mut body = vec![0u8; content_len];
        if content_len > 0 {
            let _ = reader.read_exact(&mut body);
        }

        if !store.root.join("state.db").exists() {
            store = TurboStore::open(store_root)?;
            local_mutation_seq = local_mutation_seq.wrapping_add(1);
        }
        match (method, path) {
            ("GET", "/health") | ("GET", "/status") => {
                let st = store.storage_status()?;
                let payload = serde_json::to_vec(&serde_json::json!({
                    "ok": true,
                    "arch": std::env::consts::ARCH,
                    "gpu_enabled": gpu_enable,
                    "storage": st
                }))?;
                let _ = write_http_response(&mut stream, 200, "application/json", &payload);
            }
            ("GET", "/manifest") => {
                let stamp = (query_data_version(&store), local_mutation_seq);
                if cached_manifest.as_ref().map(|(s, _, _)| *s) != Some(stamp) {
                    let manifest = get_store_manifest(&store, true)?;
                    let payload = serde_json::to_vec(&manifest)?;
                    cached_manifest = Some((stamp, manifest, payload));
                }
                if let Some((_, _, ref payload)) = cached_manifest {
                    let _ = write_http_response(&mut stream, 200, "application/json", payload);
                }
            }
            ("GET", "/export-local") => {
                let stamp = (query_data_version(&store), local_mutation_seq);
                if cached_export_local.as_ref().map(|(s, _)| *s) != Some(stamp) {
                    let (_, _, _, bytes) = export_pack_filtered_with_mode(
                        &store,
                        true,
                        &HashSet::new(),
                        &HashSet::new(),
                        true,
                    )?;
                    cached_export_local = Some((stamp, bytes));
                }
                if let Some((_, ref bytes)) = cached_export_local {
                    let _ = write_http_response(&mut stream, 200, "application/octet-stream", bytes);
                }
            }
            ("GET", "/export") => {
                let stamp = (query_data_version(&store), local_mutation_seq);
                if cached_export.as_ref().map(|(s, _)| *s) != Some(stamp) {
                    let (_, _, _, bytes) = export_pack_filtered_bytes(
                        &store,
                        true,
                        &HashSet::new(),
                        &HashSet::new(),
                    )?;
                    cached_export = Some((stamp, bytes));
                }
                if let Some((_, ref bytes)) = cached_export {
                    let _ = write_http_response(&mut stream, 200, "application/octet-stream", bytes);
                }
            }
            ("POST", "/export-delta") => {
                let req: ExportDeltaRequest = serde_json::from_slice(&body).unwrap_or_default();
                let ex_actions: HashSet<String> = req.exclude_actions.into_iter().collect();
                let ex_blobs: HashSet<String> = req.exclude_blobs.into_iter().collect();
                let (_, _, _, bytes) =
                    export_pack_filtered_bytes(&store, true, &ex_actions, &ex_blobs)?;
                let _ = write_http_response(&mut stream, 200, "application/octet-stream", &bytes);
            }
            ("POST", "/pull-delta") => {
                let req: ExportDeltaRequest = serde_json::from_slice(&body).unwrap_or_default();
                let stamp = (query_data_version(&store), local_mutation_seq);
                if req.exclude_actions.is_empty() && req.exclude_blobs.is_empty() {
                    if cached_export.as_ref().map(|(s, _)| *s) != Some(stamp) {
                        let (_, _, _, bytes) = export_pack_filtered_bytes(
                            &store,
                            true,
                            &HashSet::new(),
                            &HashSet::new(),
                        )?;
                        cached_export = Some((stamp, bytes));
                    }
                    if let Some((_, ref bytes)) = cached_export {
                        let _ = write_http_response(
                            &mut stream,
                            200,
                            "application/octet-stream",
                            bytes,
                        );
                    }
                } else {
                    if cached_manifest.as_ref().map(|(s, _, _)| *s) != Some(stamp) {
                        let manifest = get_store_manifest(&store, true)?;
                        let payload = serde_json::to_vec(&manifest)?;
                        cached_manifest = Some((stamp, manifest, payload));
                    }
                    let ex_actions: HashSet<String> = req.exclude_actions.into_iter().collect();
                    let ex_blobs: HashSet<String> = req.exclude_blobs.into_iter().collect();
                    let has_missing = cached_manifest
                        .as_ref()
                        .map(|(_, m, _)| {
                            m.action_keys.iter().any(|k| !ex_actions.contains(k))
                                || m.blob_hashes.iter().any(|b| !ex_blobs.contains(b))
                        })
                        .unwrap_or(true);
                    if !has_missing {
                        let _ = write_http_response(
                            &mut stream,
                            200,
                            "application/octet-stream",
                            b"",
                        );
                    } else {
                        let (n_acts, n_blobs, _, bytes) =
                            export_pack_filtered_bytes(&store, true, &ex_actions, &ex_blobs)?;
                        let payload: &[u8] = if n_acts == 0 && n_blobs == 0 {
                            b""
                        } else {
                            &bytes
                        };
                        let _ = write_http_response(
                            &mut stream,
                            200,
                            "application/octet-stream",
                            payload,
                        );
                    }
                }
            }
            ("POST", "/import") | ("POST", "/import-delta") => {
                let (acts, blobs) = import_pack_bytes(&mut store, &body)?;
                let payload = serde_json::to_vec(&serde_json::json!({
                    "status": "ok",
                    "ok": true,
                    "imported_actions": acts,
                    "imported_blobs": blobs
                }))?;
                let _ = write_http_response(&mut stream, 200, "application/json", &payload);
                drop(stream);
                if acts > 0 || blobs > 0 {
                    local_mutation_seq = local_mutation_seq.wrapping_add(1);
                    let stamp = (query_data_version(&store), local_mutation_seq);
                    if let Ok(m) = get_store_manifest(&store, true) {
                        if let Ok(b) = serde_json::to_vec(&m) {
                            cached_manifest = Some((stamp, m, b));
                        }
                    }
                }
            }
            ("POST", "/fast-check") => {
                let req: FastCheckHttpRequest = serde_json::from_slice(&body).unwrap_or_default();
                match execute_fastcheck_payload(&store, &req) {
                    Ok(val) => {
                        let payload = serde_json::to_vec(&val)?;
                        let _ = write_http_response(&mut stream, 200, "application/json", &payload);
                    }
                    Err(e) => {
                        let payload = serde_json::to_vec(&serde_json::json!({
                            "status": "error",
                            "error": e.to_string()
                        }))?;
                        let _ = write_http_response(&mut stream, 500, "application/json", &payload);
                    }
                }
            }
            ("POST", "/check-shard") => {
                let req: CheckShardHttpRequest = serde_json::from_slice(&body).unwrap_or_default();
                match execute_check_shard_payload(&mut store, &req) {
                    Ok(val) => {
                        local_mutation_seq = local_mutation_seq.wrapping_add(1);
                        let payload = serde_json::to_vec(&val)?;
                        let _ = write_http_response(&mut stream, 200, "application/json", &payload);
                    }
                    Err(e) => {
                        let payload = serde_json::to_vec(&serde_json::json!({
                            "status": "error",
                            "error": e.to_string()
                        }))?;
                        let _ = write_http_response(&mut stream, 500, "application/json", &payload);
                    }
                }
            }
            ("POST", "/check-shards-batch") => {
                let req: CheckShardsBatchRequest =
                    serde_json::from_slice(&body).unwrap_or_default();
                match execute_check_shards_batch_payload(&mut store, &req) {
                    Ok(resp) => {
                        local_mutation_seq = local_mutation_seq.wrapping_add(1);
                        let payload = serde_json::to_vec(&resp)?;
                        let _ = write_http_response(&mut stream, 200, "application/json", &payload);
                    }
                    Err(e) => {
                        let resp = CheckShardsBatchResponse {
                            ok: false,
                            verified_count: 0,
                            cache_hits: 0,
                            elapsed_ms: 0.0,
                            exit_code: -1,
                            stdout: String::new(),
                            stderr: String::new(),
                            error: Some(e.to_string()),
                        };
                        let payload = serde_json::to_vec(&resp)?;
                        let _ = write_http_response(&mut stream, 500, "application/json", &payload);
                    }
                }
            }
            _ => {
                let _ = write_http_response(&mut stream, 404, "application/json", b"{\"error\":\"not_found\"}");
            }
        }
    }
    Ok(())
}

static SERVER_LEAN_ENV_CACHE: std::sync::OnceLock<
    std::sync::Mutex<
        std::collections::HashMap<
            (std::path::PathBuf, String, String),
            (std::collections::HashMap<String, String>, std::path::PathBuf),
        >,
    >,
> = std::sync::OnceLock::new();

pub(crate) fn resolve_server_lean_env_and_bin(
    store: &TurboStore,
    toolchain: &str,
    lean_path: &str,
) -> (std::collections::HashMap<String, String>, std::path::PathBuf) {
    let cache_key = (
        store.root.clone(),
        toolchain.to_string(),
        lean_path.to_string(),
    );
    if let Some(m) = SERVER_LEAN_ENV_CACHE.get() {
        if let Ok(guard) = m.lock() {
            if let Some(hit) = guard.get(&cache_key) {
                return hit.clone();
            }
        }
    }

    let mut env_vars = std::collections::HashMap::new();
    if let Ok(mut stmt) = store
        .conn
        .prepare("SELECT env_json FROM lake_env_cache ORDER BY updated_at DESC LIMIT 1")
    {
        if let Ok(json_str) = stmt.query_row([], |r| r.get::<_, String>(0)) {
            if let Ok(map) =
                serde_json::from_str::<std::collections::HashMap<String, String>>(&json_str)
            {
                env_vars = map;
            }
        }
    }

    let tc_dir_name = toolchain.trim().replace('/', "--").replace(':', "---");
    let lean_bin = env_vars
        .get("LAKE")
        .and_then(|lake_bin| Path::new(lake_bin).parent().map(|p| p.join("lean")))
        .filter(|cand| cand.exists())
        .or_else(|| {
            if !tc_dir_name.is_empty() {
                for tc_root in [
                    std::env::var("HOME")
                        .map(|h| Path::new(&h).join(".elan/toolchains"))
                        .unwrap_or_default(),
                    Path::new("/var/lib/sandboxed-node/caches/elan/toolchains").to_path_buf(),
                ] {
                    let cand = tc_root.join(&tc_dir_name).join("bin").join("lean");
                    if cand.exists() {
                        return Some(cand);
                    }
                }
            }
            None
        })
        .or_else(|| {
            for entry in lean_path.split(':') {
                let p = Path::new(entry);
                if p.ends_with("lib/lean") {
                    if let Some(tc_root) = p.parent().and_then(|pr| pr.parent()) {
                        let cand = tc_root.join("bin").join("lean");
                        if cand.exists() {
                            return Some(cand);
                        }
                    }
                }
            }
            None
        })
        .or_else(|| {
            for tc_root in [
                std::env::var("HOME")
                    .map(|h| Path::new(&h).join(".elan/toolchains"))
                    .unwrap_or_default(),
                Path::new("/var/lib/sandboxed-node/caches/elan/toolchains").to_path_buf(),
            ] {
                if let Ok(entries) = fs::read_dir(&tc_root) {
                    for entry in entries.flatten() {
                        let cand = entry.path().join("bin").join("lean");
                        if cand.exists() {
                            return Some(cand);
                        }
                    }
                }
            }
            None
        })
        .or_else(|| {
            env_vars.get("PATH").and_then(|p| {
                p.split(':')
                    .map(|dir| Path::new(dir).join("lean"))
                    .find(|cand| cand.exists())
            })
        })
        .or_else(|| {
            std::env::var("PATH").ok().and_then(|p| {
                p.split(':')
                    .map(|dir| Path::new(dir).join("lean"))
                    .find(|cand| cand.exists())
            })
        })
        .or_else(|| {
            std::env::var("HOME")
                .ok()
                .map(|h| Path::new(&h).join(".elan/bin/lean"))
                .filter(|cand| cand.exists())
        })
        .or_else(|| {
            let elan_cand = Path::new("/var/lib/sandboxed-node/caches/elan/bin/lean");
            if elan_cand.exists() {
                Some(elan_cand.to_path_buf())
            } else {
                None
            }
        })
        .unwrap_or_else(|| std::path::PathBuf::from("lean"));

    let cache_mutex = SERVER_LEAN_ENV_CACHE
        .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    if let Ok(mut guard) = cache_mutex.lock() {
        guard.insert(cache_key, (env_vars.clone(), lean_bin.clone()));
    }

    (env_vars, lean_bin)
}

const ZYGOTE_WORKER_LEAN_SRC: &str = include_str!("../../../lean/TurboLean/ZygoteWorker.lean");

#[derive(Debug, Clone, Deserialize)]
pub struct ZygoteEvalReply {
    pub ok: bool,
    #[serde(default)]
    pub import_ok: bool,
    pub env_cache_hit: bool,
    pub import_us: u64,
    pub elab_us: u64,
    pub errors: Vec<String>,
}

struct ZygoteChild {
    _child: std::process::Child,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
}

static ZYGOTE_POOL: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<(String, String, String), ZygoteChild>>,
> = std::sync::OnceLock::new();

fn hex_encode_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = Vec::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize]);
        out.push(HEX[(b & 0x0f) as usize]);
    }
    // Safety: HEX contains only valid ASCII characters
    unsafe { String::from_utf8_unchecked(out) }
}

/// Split a Lean shard source into `(imports_csv, body_without_imports)` while preserving line numbers.
pub fn split_shard_for_zygote(shard_source: &str) -> (String, String) {
    let mut imports: Vec<String> = Vec::new();
    let mut body_lines: Vec<&str> = Vec::new();
    let mut in_header = true;

    if !shard_source.contains("/-") {
        for orig_line in shard_source.lines() {
            if in_header {
                let without_line_comment = orig_line.split("--").next().unwrap_or(orig_line);
                let trimmed = without_line_comment.trim();
                if trimmed.is_empty() || trimmed == "prelude" {
                    body_lines.push("");
                    continue;
                }
                if let Some(rest) = trimmed.strip_prefix("import ") {
                    for mod_name in rest.split_whitespace() {
                        if !mod_name.is_empty() {
                            imports.push(mod_name.to_string());
                        }
                    }
                    body_lines.push("");
                    continue;
                }
                in_header = false;
            }
            body_lines.push(orig_line);
        }
    } else {
        let clean = crate::splitter::strip_lean_comments(shard_source);
        for (orig_line, clean_line) in shard_source.lines().zip(clean.lines()) {
            if in_header {
                let trimmed = clean_line.trim();
                if trimmed.is_empty() || trimmed == "prelude" {
                    body_lines.push("");
                    continue;
                }
                if let Some(rest) = trimmed.strip_prefix("import ") {
                    for mod_name in rest.split_whitespace() {
                        if !mod_name.is_empty() {
                            imports.push(mod_name.to_string());
                        }
                    }
                    body_lines.push("");
                    continue;
                }
                in_header = false;
            }
            body_lines.push(orig_line);
        }
    }

    imports.sort();
    imports.dedup();
    let imports_csv = if imports.is_empty() {
        "Init".to_string()
    } else {
        imports.join(",")
    };
    let mut body = body_lines.join("\n");
    body.push('\n');
    (imports_csv, body)
}

fn ensure_zygote_binary(
    store: &TurboStore,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
) -> Result<std::path::PathBuf> {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-zygote:v2:shared:");
    hasher.update(std::env::consts::ARCH.as_bytes());
    hasher.update(ZYGOTE_WORKER_LEAN_SRC.as_bytes());
    let bin_name = format!("turbo_zygote_{}", &hasher.finalize().to_hex()[..16]);
    let bin_dir = store.root.join("fastcheck_bins");
    fs::create_dir_all(&bin_dir)?;
    let cached_bin = bin_dir.join(&bin_name);
    if cached_bin.exists() {
        return Ok(cached_bin);
    }

    let shm_staging = store.fast_staging_dir();
    let shm_bin_dir = shm_staging.join("zygote_daemon_cas").join("fastcheck_bins");
    let _ = fs::create_dir_all(&shm_bin_dir);
    let shm_cached_bin = shm_bin_dir.join(&bin_name);
    let tmp_id = next_tmp_id();

    if shm_cached_bin.exists() {
        let tmp_copy = bin_dir.join(format!("{}.{}.tmp", bin_name, tmp_id));
        if fs::copy(&shm_cached_bin, &tmp_copy).is_ok() {
            let _ = fs::rename(&tmp_copy, &cached_bin);
            if cached_bin.exists() {
                return Ok(cached_bin);
            }
        }
    }

    // Compile embedded ZygoteWorker.lean via `lean -c` + `leanc -O3 -lleanshared -Wl,-rpath,<sysroot>/lib/lean` (58 KB binary!)
    let leanc_bin = lean_bin
        .parent()
        .map(|p| p.join("leanc"))
        .filter(|c| c.exists())
        .unwrap_or_else(|| std::path::PathBuf::from("leanc"));
    let tmp_lean = shm_staging.join(format!("ZygoteWorker_{}.lean", tmp_id));
    let tmp_c = shm_staging.join(format!("ZygoteWorker_{}.c", tmp_id));
    let tmp_bin = shm_staging.join(format!("ZygoteWorker_{}.bin", tmp_id));
    fs::write(&tmp_lean, ZYGOTE_WORKER_LEAN_SRC)?;

    let out1 = Command::new(lean_bin)
        .arg(format!("--root={}", shm_staging.display()))
        .arg("-c")
        .arg(&tmp_c)
        .arg(&tmp_lean)
        .current_dir(&shm_staging)
        .envs(env_vars)
        .output()
        .context("Failed to compile ZygoteWorker.lean to C")?;
    let _ = fs::remove_file(&tmp_lean);
    if !out1.status.success() {
        anyhow::bail!(
            "`lean -c` failed on ZygoteWorker.lean:\n{}",
            String::from_utf8_lossy(&out1.stderr)
        );
    }

    let mut link_cmd = Command::new(&leanc_bin);
    link_cmd
        .arg("-O3")
        .arg(&tmp_c)
        .arg("-lleanshared")
        .arg("-o")
        .arg(&tmp_bin)
        .current_dir(&shm_staging)
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
        .context("Failed to link ZygoteWorker binary via `leanc -O3 -lleanshared`")?;
    let _ = fs::remove_file(&tmp_c);
    if !out2.status.success() {
        anyhow::bail!(
            "`leanc -O3 -lleanshared` failed on ZygoteWorker.c:\n{}",
            String::from_utf8_lossy(&out2.stderr)
        );
    }
    let _ = fs::copy(&tmp_bin, &shm_cached_bin);
    if fs::rename(&tmp_bin, &cached_bin).is_err() {
        fs::copy(&tmp_bin, &cached_bin)?;
        let _ = fs::remove_file(&tmp_bin);
    }
    Ok(cached_bin)
}

static ZYGOTE_LEAN_PATH_CACHE: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<(String, String, std::path::PathBuf), (String, bool)>>,
> = std::sync::OnceLock::new();

pub fn eval_with_zygote_pool(
    store: &TurboStore,
    toolchain: &str,
    req_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
    lean_bin: &Path,
    shard_source: &str,
    allow_stub: bool,
) -> Result<ZygoteEvalReply> {
    let env_lp = env_vars.get("LEAN_PATH").cloned().unwrap_or_default();
    let lp_cache_key = (
        req_lean_path.to_string(),
        env_lp.clone(),
        lean_bin.to_path_buf(),
    );
    let lp_cache_mutex = ZYGOTE_LEAN_PATH_CACHE
        .get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    let cached_lp = lp_cache_mutex
        .lock()
        .ok()
        .and_then(|g| g.get(&lp_cache_key).cloned());

    let (effective_lean_path, has_all_turbo_lean_oleans) = if let Some(pair) = cached_lp {
        pair
    } else {
        let mut path_parts: Vec<String> = Vec::new();
        let mut add_part = |p: &str| {
            for seg in p.split(':') {
                let s = seg.trim();
                if !s.is_empty() {
                    let norm = fs::canonicalize(s)
                        .map(|c| c.to_string_lossy().to_string())
                        .unwrap_or_else(|_| s.to_string());
                    if !path_parts.iter().any(|x| x == &norm) {
                        path_parts.push(norm);
                    }
                }
            }
        };
        if !req_lean_path.is_empty() {
            add_part(req_lean_path);
        }
        if !env_lp.is_empty() {
            add_part(&env_lp);
        }
        if let Some(repo_lean_lib) = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(|p| p.parent())
            .map(|r| r.join("lean/.lake/build/lib/lean"))
            .filter(|p| p.exists())
        {
            add_part(&repo_lean_lib.to_string_lossy());
        }
        if let Some(tc_lib_lean) = lean_bin
            .parent()
            .and_then(|b| b.parent())
            .map(|tc| tc.join("lib").join("lean"))
            .filter(|p| p.exists())
        {
            add_part(&tc_lib_lean.to_string_lossy());
        }
        let has_oleans = path_parts.iter().any(|p| {
            let root = Path::new(p);
            root.join("TurboLean/Assembler.olean").exists()
                && root.join("TurboLean/FastCheck.olean").exists()
                && root.join("TurboLean/Inspector.olean").exists()
                && root.join("TurboLean/Reflection.olean").exists()
        });
        let eff = path_parts.join(":");
        if let Ok(mut g) = lp_cache_mutex.lock() {
            g.insert(lp_cache_key, (eff.clone(), has_oleans));
        }
        (eff, has_oleans)
    };

    let (mut imports_csv, body_code) = split_shard_for_zygote(shard_source);
    let is_turbo_lean_subset = !imports_csv.is_empty()
        && imports_csv.split(',').any(|m| m.starts_with("TurboLean."))
        && imports_csv.split(',').all(|m| {
            matches!(
                m,
                "TurboLean.Assembler"
                    | "TurboLean.FastCheck"
                    | "TurboLean.Inspector"
                    | "TurboLean.Reflection"
                    | "Lean.Elab.Command"
                    | "Lean.Util.CollectAxioms"
            )
        });
    let unified_turbo_env = is_turbo_lean_subset
        && has_all_turbo_lean_oleans
        && !body_code.contains("structure Word256")
        && !body_code.contains("inductive StorageKey")
        && !body_code.contains("def allowedStandardAxioms")
        && !body_code.contains("def exprHeadTag");
    if unified_turbo_env {
        imports_csv =
            "TurboLean.Assembler,TurboLean.FastCheck,TurboLean.Inspector,TurboLean.Reflection"
                .to_string();
    }
    let hex_body = hex_encode_bytes(body_code.as_bytes());
    let req_line = if allow_stub {
        format!("{}\t{}\tallow_stub\n", imports_csv, hex_body)
    } else {
        format!("{}\t{}\n", imports_csv, hex_body)
    };

    let pool_mutex = ZYGOTE_POOL.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    let mut pool = pool_mutex
        .lock()
        .map_err(|_| anyhow::anyhow!("ZygotePool mutex poisoned"))?;
    let pool_key = (
        toolchain.to_string(),
        if unified_turbo_env {
            "unified_turbo_lean".to_string()
        } else {
            effective_lean_path.clone()
        },
        imports_csv.clone(),
    );

    if !pool.contains_key(&pool_key) {
        let zygote_bin = ensure_zygote_binary(store, lean_bin, env_vars)?;
        let mut cmd = Command::new(&zygote_bin);
        cmd.envs(env_vars)
            .env("LEAN_PATH", &effective_lean_path)
            .env("LEAN", lean_bin)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null());
        for k in [
            "GH_TOKEN",
            "GITHUB_TOKEN",
            "OPENAI_API_KEY",
            "ANTHROPIC_API_KEY",
            "AWS_SECRET_ACCESS_KEY",
            "AWS_SESSION_TOKEN",
            "NPM_TOKEN",
            "CARGO_REGISTRY_TOKEN",
        ] {
            cmd.env_remove(k);
        }
        if let Some(sysroot) = lean_bin.parent().and_then(|b| b.parent()) {
            cmd.env("LEAN_SYSROOT", sysroot);
        }
        if !toolchain.is_empty() && toolchain != "unknown" {
            cmd.env("ELAN_TOOLCHAIN", toolchain.trim());
        }
        let mut child = cmd
            .spawn()
            .with_context(|| format!("Failed to spawn Zygote worker {:?}", zygote_bin))?;
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| anyhow::anyhow!("Missing Zygote stdin"))?;
        let stdout = BufReader::new(
            child
                .stdout
                .take()
                .ok_or_else(|| anyhow::anyhow!("Missing Zygote stdout"))?,
        );
        pool.insert(
            pool_key.clone(),
            ZygoteChild {
                _child: child,
                stdin,
                stdout,
            },
        );
    }

    let worker = pool.get_mut(&pool_key).unwrap();
    let io_res = (|| -> Result<ZygoteEvalReply> {
        worker.stdin.write_all(req_line.as_bytes())?;
        worker.stdin.flush()?;
        let mut resp_line = String::new();
        let n = worker.stdout.read_line(&mut resp_line)?;
        if n == 0 {
            anyhow::bail!("Zygote worker closed stdout unexpectedly");
        }
        let parsed: ZygoteEvalReply = serde_json::from_str(resp_line.trim())
            .with_context(|| format!("Invalid JSON from Zygote worker: {}", resp_line.trim()))?;
        Ok(parsed)
    })();

    if io_res.is_err() {
        pool.remove(&pool_key);
    }
    io_res
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct LocalZygoteDaemonInfo {
    addr: String,
    pid: u32,
    exe_mtime_sec: i64,
    exe_mtime_nsec: i64,
}

pub fn ensure_local_zygote_daemon(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
) -> Option<String> {
    if std::env::var("TURBO_LEAN_NO_DAEMON").is_ok() {
        return None;
    }
    let current_exe = std::env::current_exe().ok()?;
    let (exe_mtime_sec, exe_mtime_nsec, _) = fs::metadata(&current_exe)
        .ok()
        .map(|m| TurboStore::extract_file_stat_tuple(&m))
        .unwrap_or((0, 0, 0));

    let mut exe_hasher = blake3::Hasher::new();
    exe_hasher.update(current_exe.to_string_lossy().as_bytes());
    let exe_tag = &exe_hasher.finalize().to_hex()[..12];

    let staging = store.fast_staging_dir();
    let daemon_cache_dir = staging.join(format!("zygote_daemon_cas_{}", exe_tag));
    let _ = fs::create_dir_all(&daemon_cache_dir);
    let state_file = daemon_cache_dir.join("zygote_daemon.json");

    let check_existing = |path: &Path| -> Option<String> {
        let content = fs::read_to_string(path).ok()?;
        let info: LocalZygoteDaemonInfo = serde_json::from_str(&content).ok()?;
        if info.exe_mtime_sec != exe_mtime_sec || info.exe_mtime_nsec != exe_mtime_nsec {
            #[cfg(unix)]
            if info.pid > 0 {
                unsafe {
                    libc::kill(info.pid as i32, libc::SIGTERM);
                }
            }
            return None;
        }
        #[cfg(unix)]
        {
            if info.pid > 0 && unsafe { libc::kill(info.pid as i32, 0) == 0 } {
                return Some(format!("http://{}", info.addr));
            }
            return None;
        }
        #[cfg(not(unix))]
        {
            let sock_addr: std::net::SocketAddr = info.addr.parse().ok()?;
            if std::net::TcpStream::connect_timeout(
                &sock_addr,
                std::time::Duration::from_millis(10),
            )
            .is_ok()
            {
                Some(format!("http://{}", info.addr))
            } else {
                None
            }
        }
    };

    if let Some(url) = check_existing(&state_file) {
        return Some(url);
    }

    let lock_path = daemon_cache_dir.join("zygote_daemon.lock");
    let lock_file = fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(&lock_path)
        .ok()?;
    #[cfg(unix)]
    unsafe {
        use std::os::unix::io::AsRawFd;
        libc::flock(lock_file.as_raw_fd(), libc::LOCK_EX);
    }

    let res = (|| -> Option<String> {
        if let Some(url) = check_existing(&state_file) {
            return Some(url);
        }
        let port = {
            let listener = TcpListener::bind("127.0.0.1:0").ok()?;
            let p = listener.local_addr().ok()?.port();
            drop(listener);
            p
        };
        let addr = format!("127.0.0.1:{}", port);
        let sock_addr: std::net::SocketAddr = addr.parse().ok()?;

        let mut cmd = Command::new(&current_exe);
        cmd.arg("--cache-dir")
            .arg(&daemon_cache_dir)
            .arg("serve")
            .arg("--listen")
            .arg(&addr)
            .envs(env_vars)
            .env("TURBO_LEAN_DAEMON", "1")
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null());
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            cmd.process_group(0);
        }
        let child = cmd.spawn().ok()?;
        let pid = child.id();

        let mut connected = false;
        for _ in 0..75 {
            if std::net::TcpStream::connect_timeout(
                &sock_addr,
                std::time::Duration::from_millis(5),
            )
            .is_ok()
            {
                connected = true;
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(2));
        }
        if !connected {
            return None;
        }

        let info = LocalZygoteDaemonInfo {
            addr: addr.clone(),
            pid,
            exe_mtime_sec,
            exe_mtime_nsec,
        };
        if let Ok(json_bytes) = serde_json::to_vec(&info) {
            let _ = fs::write(&state_file, &json_bytes);
            let _ = fs::write(store.root.join("zygote_daemon.json"), &json_bytes);
        }
        Some(format!("http://{}", addr))
    })();

    #[cfg(unix)]
    unsafe {
        use std::os::unix::io::AsRawFd;
        libc::flock(lock_file.as_raw_fd(), libc::LOCK_UN);
    }
    res
}

pub fn warm_local_zygote_daemon_nonblocking(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
) {
    if std::env::var("TURBO_LEAN_NO_DAEMON").is_ok() {
        return;
    }
    let Ok(current_exe) = std::env::current_exe() else {
        return;
    };
    let (exe_mtime_sec, exe_mtime_nsec, _) = fs::metadata(&current_exe)
        .ok()
        .map(|m| TurboStore::extract_file_stat_tuple(&m))
        .unwrap_or((0, 0, 0));

    let mut exe_hasher = blake3::Hasher::new();
    exe_hasher.update(current_exe.to_string_lossy().as_bytes());
    let exe_tag = &exe_hasher.finalize().to_hex()[..12];

    let staging = store.fast_staging_dir();
    let daemon_cache_dir = staging.join(format!("zygote_daemon_cas_{}", exe_tag));
    let _ = fs::create_dir_all(&daemon_cache_dir);
    let state_file = daemon_cache_dir.join("zygote_daemon.json");

    let lock_path = daemon_cache_dir.join("zygote_daemon.lock");
    let Ok(lock_file) = fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(&lock_path)
    else {
        return;
    };
    #[cfg(unix)]
    unsafe {
        use std::os::unix::io::AsRawFd;
        if libc::flock(lock_file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) != 0 {
            return;
        }
    }

    (|| {
        if let Ok(content) = fs::read_to_string(&state_file) {
            if let Ok(info) = serde_json::from_str::<LocalZygoteDaemonInfo>(&content) {
                if info.exe_mtime_sec == exe_mtime_sec && info.exe_mtime_nsec == exe_mtime_nsec {
                    #[cfg(unix)]
                    if info.pid > 0 && unsafe { libc::kill(info.pid as i32, 0) == 0 } {
                        return;
                    }
                } else {
                    #[cfg(unix)]
                    if info.pid > 0 {
                        unsafe {
                            libc::kill(info.pid as i32, libc::SIGTERM);
                        }
                    }
                }
            }
        }

        let Ok(listener) = TcpListener::bind("127.0.0.1:0") else {
            return;
        };
        let Ok(local_addr) = listener.local_addr() else {
            return;
        };
        let port = local_addr.port();
        drop(listener);
        let addr = format!("127.0.0.1:{}", port);

        let mut cmd = Command::new(&current_exe);
        cmd.arg("--cache-dir")
            .arg(&daemon_cache_dir)
            .arg("serve")
            .arg("--listen")
            .arg(&addr)
            .envs(env_vars)
            .env("TURBO_LEAN_DAEMON", "1")
            .env("TURBO_LEAN_DAEMON_STATE_FILE", &state_file)
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null());
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            cmd.process_group(0);
        }
        if let Ok(child) = cmd.spawn() {
            let info = LocalZygoteDaemonInfo {
                addr,
                pid: child.id(),
                exe_mtime_sec,
                exe_mtime_nsec,
            };
            if let Ok(json_bytes) = serde_json::to_vec(&info) {
                let _ = fs::write(&state_file, &json_bytes);
                let _ = fs::write(store.root.join("zygote_daemon.json"), &json_bytes);
            }
        }
    })();

    #[cfg(unix)]
    unsafe {
        use std::os::unix::io::AsRawFd;
        libc::flock(lock_file.as_raw_fd(), libc::LOCK_UN);
    }
}

fn try_zygote_url_check_shard_inner(
    base_url: &str,
    req: &CheckShardHttpRequest,
) -> Result<Option<serde_json::Value>> {
    let endpoint = format!("{}/check-shard", base_url.trim_end_matches('/'));
    let mut local_req = req.clone();
    local_req.skip_cas_lock = true;
    let body = serde_json::to_vec(&local_req)?;
    let resp_bytes = http_request("POST", &endpoint, "application/json", &body)?;
    let resp_json: serde_json::Value = serde_json::from_slice(&resp_bytes)?;
    let status = resp_json.get("status").and_then(|v| v.as_str()).unwrap_or("");
    if status == "remote_theorem_verified" || status == "remote_theorem_cache_hit" {
        Ok(Some(resp_json))
    } else {
        Ok(None)
    }
}

pub fn try_zygote_url_check_shard(
    base_url: &str,
    req: &CheckShardHttpRequest,
) -> Option<serde_json::Value> {
    try_zygote_url_check_shard_inner(base_url, req).ok().flatten()
}

pub fn try_local_zygote_check_shard(
    store: &TurboStore,
    env_vars: &std::collections::HashMap<String, String>,
    req: &CheckShardHttpRequest,
) -> Option<serde_json::Value> {
    let base_url = ensure_local_zygote_daemon(store, env_vars)?;
    match try_zygote_url_check_shard_inner(&base_url, req) {
        Ok(res) => res,
        Err(_) => {
            if let Ok(current_exe) = std::env::current_exe() {
                let mut exe_hasher = blake3::Hasher::new();
                exe_hasher.update(current_exe.to_string_lossy().as_bytes());
                let exe_tag = &exe_hasher.finalize().to_hex()[..12];
                let state_file = store
                    .fast_staging_dir()
                    .join(format!("zygote_daemon_cas_{}", exe_tag))
                    .join("zygote_daemon.json");
                let _ = fs::remove_file(&state_file);
            }
            let retry_url = ensure_local_zygote_daemon(store, env_vars)?;
            try_zygote_url_check_shard_inner(&retry_url, req).ok().flatten()
        }
    }
}

fn source_may_have_hygiene_issue(s: &str) -> bool {
    s.contains("sorry")
        || s.contains("native_decide")
        || s.contains("trustCompiler")
        || s.contains("unsafe")
        || s.contains("extern")
        || s.contains("implemented_by")
        || s.contains("axiom")
}

fn execute_check_shard_payload(
    store: &mut TurboStore,
    req: &CheckShardHttpRequest,
) -> Result<serde_json::Value> {
    let t0 = std::time::Instant::now();
    if req.shard_key.is_empty() || req.shard_source.is_empty() {
        anyhow::bail!("Missing shard_key or shard_source in /check-shard request");
    }

    if source_may_have_hygiene_issue(&req.shard_source) {
        let clean_source = crate::splitter::strip_lean_comments(&req.shard_source);
        let source_violations = crate::splitter::audit_hygiene(&clean_source);
        if source_violations.has_native_decide
            || source_violations.has_trust_compiler
            || source_violations.has_unsafe
            || source_violations.has_extern_or_implemented_by
        {
            anyhow::bail!(
                "Soundness hygiene violation in remote shard `{}`: {:?}",
                req.decl,
                source_violations.flagged_items
            );
        }

        if !req.skip_cas_lock && source_violations.has_sorry {
            let parsed = crate::splitter::split_lean_source(&req.shard_source, &[]);
            let target_body = if parsed.shards.len() == 1 {
                let s = &parsed.shards[0];
                format!("{}\n{}", s.signature_text, s.proof_text)
            } else {
                let short_req: String = req
                    .decl
                    .rsplit('.')
                    .next()
                    .unwrap_or(&req.decl)
                    .chars()
                    .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
                    .collect();
                parsed
                    .shards
                    .iter()
                    .find(|s| {
                        let base = s.name.split("__turbo_check_").next().unwrap_or(&s.name);
                        let short_s = base.rsplit('.').next().unwrap_or(base);
                        base == req.decl
                            || req.decl.ends_with(&format!(".{}", base))
                            || base.ends_with(&format!(".{}", req.decl))
                            || (short_s.starts_with("_turbo_verify_") && short_s.ends_with(&short_req))
                    })
                    .map(|s| format!("{}\n{}", s.signature_text, s.proof_text))
                    .unwrap_or_else(|| clean_source.clone())
            };
            let clean_target = crate::splitter::strip_lean_comments(&target_body);
            let violations = crate::splitter::audit_hygiene(&clean_target);
            if !violations.flagged_items.is_empty() {
                anyhow::bail!(
                    "Soundness hygiene violation in remote shard `{}`: {:?}",
                    req.decl,
                    violations.flagged_items
                );
            }
        }
    }

    let toolchain = if req.toolchain.is_empty() {
        "leanprover/lean4:v4.31.0"
    } else {
        req.toolchain.as_str()
    };

    if req.skip_cas_lock {
        let (mut env_vars, lean_bin) =
            resolve_server_lean_env_and_bin(store, toolchain, &req.lean_path);

        if !env_vars.contains_key("LEAN_PATH") {
            if let Ok(cwd) = std::env::current_dir() {
                for rel in [".lake/build/lib/lean", "lean/.lake/build/lib/lean"] {
                    let cand = cwd.join(rel);
                    if cand.exists() {
                        env_vars.insert(
                            "LEAN_PATH".to_string(),
                            cand.to_string_lossy().to_string(),
                        );
                        break;
                    }
                }
            }
        }

        let zreply = eval_with_zygote_pool(
            store,
            toolchain,
            &req.lean_path,
            &env_vars,
            &lean_bin,
            &req.shard_source,
            true,
        )?;
        if !zreply.import_ok {
            anyhow::bail!(
                "Zygote import unavailable for `{}`: {}",
                req.decl,
                zreply.errors.join("\n")
            );
        }
        if !zreply.ok {
            anyhow::bail!(
                "Zygote `lean` shard verification failed for `{}`:\n{}",
                req.decl,
                zreply.errors.join("\n")
            );
        }

        let dur_ms = t0.elapsed().as_millis() as i64;
        let dur_us = t0.elapsed().as_micros() as u64;
        return Ok(serde_json::json!({
            "status": "remote_theorem_verified",
            "decl": req.decl,
            "shard_key": req.shard_key,
            "interface_hash": req.interface_hash,
            "prefix_env_hash": req.prefix_env_hash,
            "server_arch": std::env::consts::ARCH,
            "server_elapsed_ms": dur_ms,
            "server_elapsed_us": dur_us,
            "zygote_used": true,
            "zygote_env_cache_hit": zreply.env_cache_hit,
            "zygote_import_us": zreply.import_us,
            "zygote_elab_us": zreply.elab_us
        }));
    }

    if let Some(_outputs) = store.get_cached_action(&req.shard_key, "trusted")? {
        return Ok(serde_json::json!({
            "status": "remote_theorem_cache_hit",
            "decl": req.decl,
            "shard_key": req.shard_key,
            "coalesced": false,
            "interface_hash": req.interface_hash,
            "prefix_env_hash": req.prefix_env_hash,
            "server_arch": std::env::consts::ARCH,
            "server_elapsed_ms": t0.elapsed().as_millis()
        }));
    }

    let lock_path = store.root.join("locks").join(format!("{}.lock", req.shard_key));
    let mut lock_file = Some(
        fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .open(&lock_path)?,
    );
    #[cfg(unix)]
    let fast_locked = {
        use std::os::unix::io::AsRawFd;
        let fd = lock_file.as_ref().unwrap().as_raw_fd();
        unsafe { libc::flock(fd, libc::LOCK_EX | libc::LOCK_NB) == 0 }
    };
    #[cfg(not(unix))]
    let fast_locked = false;

    if !fast_locked {
        drop(lock_file.take());
        if let SingleflightOutcome::CacheHit { coalesced, .. } =
            store.acquire_singleflight(&req.shard_key, toolchain, "theorem_shard", "trusted")?
        {
            return Ok(serde_json::json!({
                "status": "remote_theorem_cache_hit",
                "decl": req.decl,
                "shard_key": req.shard_key,
                "coalesced": coalesced,
                "interface_hash": req.interface_hash,
                "prefix_env_hash": req.prefix_env_hash,
                "server_arch": std::env::consts::ARCH,
                "server_elapsed_ms": t0.elapsed().as_millis()
            }));
        }
    }

    let (mut env_vars, lean_bin) =
        resolve_server_lean_env_and_bin(store, toolchain, &req.lean_path);

    if !env_vars.contains_key("LEAN_PATH") {
        if let Ok(cwd) = std::env::current_dir() {
            for rel in [".lake/build/lib/lean", "lean/.lake/build/lib/lean"] {
                let cand = cwd.join(rel);
                if cand.exists() {
                    env_vars.insert(
                        "LEAN_PATH".to_string(),
                        cand.to_string_lossy().to_string(),
                    );
                    break;
                }
            }
        }
    }

    let mut zygote_used = false;
    let mut zygote_env_cache_hit = false;
    let mut zygote_import_us = 0u64;
    let mut zygote_elab_us = 0u64;

    if let Ok(zreply) = eval_with_zygote_pool(
        store,
        toolchain,
        &req.lean_path,
        &env_vars,
        &lean_bin,
        &req.shard_source,
        true,
    ) {
        if zreply.import_ok {
            if !zreply.ok {
                anyhow::bail!(
                    "Remote `lean` shard verification failed for `{}`:\n{}",
                    req.decl,
                    zreply.errors.join("\n")
                );
            }
            zygote_used = true;
            zygote_env_cache_hit = zreply.env_cache_hit;
            zygote_import_us = zreply.import_us;
            zygote_elab_us = zreply.elab_us;
        }
    }

    if !zygote_used {
        let staging = store.fast_staging_dir();
        let tmp_shard = staging.join(format!("http_shard_{}.lean", next_tmp_id()));
        fs::write(&tmp_shard, &req.shard_source)?;

        let mut cmd = Command::new(&lean_bin);
        cmd.arg(&tmp_shard).envs(&env_vars);
        if !req.toolchain.is_empty()
            && req.toolchain != "unknown"
            && !env_vars.contains_key("ELAN_TOOLCHAIN")
        {
            cmd.env("ELAN_TOOLCHAIN", req.toolchain.trim());
        }
        let out = cmd
            .output()
            .context("Failed to execute `lean` on remote /check-shard payload")?;
        let _ = fs::remove_file(&tmp_shard);

        if !out.status.success() {
            anyhow::bail!(
                "Remote `lean` shard verification failed for `{}`:\n{}\n{}",
                req.decl,
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
        }
    }

    let dur_ms = t0.elapsed().as_millis() as i64;
    let dur_us = t0.elapsed().as_micros() as u64;
    let receipt = serde_json::to_vec(&serde_json::json!({
        "decl": req.decl,
        "prefix_env_hash": req.prefix_env_hash,
        "stmt_hash": req.stmt_hash,
        "proof_hash": req.proof_hash,
        "verified_at": now_unix()
    }))?;
    store.batch_publish_theorem_shards(
        toolchain,
        "trusted",
        &[(req.shard_key.clone(), req.decl.clone(), receipt, dur_ms)],
    )?;
    drop(lock_file);

    Ok(serde_json::json!({
        "status": "remote_theorem_verified",
        "decl": req.decl,
        "shard_key": req.shard_key,
        "interface_hash": req.interface_hash,
        "prefix_env_hash": req.prefix_env_hash,
        "server_arch": std::env::consts::ARCH,
        "server_elapsed_ms": dur_ms,
        "server_elapsed_us": dur_us,
        "zygote_used": zygote_used,
        "zygote_env_cache_hit": zygote_env_cache_hit,
        "zygote_import_us": zygote_import_us,
        "zygote_elab_us": zygote_elab_us
    }))
}

fn execute_check_shards_batch_payload(
    store: &mut TurboStore,
    req: &CheckShardsBatchRequest,
) -> Result<CheckShardsBatchResponse> {
    let t0 = std::time::Instant::now();
    if req.items.is_empty() || req.coalesced_shard_source.is_empty() {
        anyhow::bail!("Missing items or coalesced_shard_source in /check-shards-batch request");
    }

    let trust_domain = if req.trust_domain.is_empty() {
        "trusted"
    } else {
        req.trust_domain.as_str()
    };
    let toolchain = if req.toolchain.is_empty() {
        "leanprover/lean4:v4.31.0"
    } else {
        req.toolchain.as_str()
    };

    let keys: Vec<String> = req.items.iter().map(|i| i.shard_key.clone()).collect();
    let mut cached_map = store.batch_get_theorem_shards(&keys, trust_domain)?;
    let mut cache_hits = req
        .items
        .iter()
        .filter(|i| cached_map.contains_key(&i.shard_key))
        .count();

    if cache_hits == req.items.len() {
        return Ok(CheckShardsBatchResponse {
            ok: true,
            verified_count: 0,
            cache_hits,
            elapsed_ms: (t0.elapsed().as_secs_f64() * 1000.0 * 100.0).round() / 100.0,
            exit_code: 0,
            stdout: String::new(),
            stderr: String::new(),
            error: None,
        });
    }

    // Soundness hygiene audit on coalesced shard source:
    // Reject any `native_decide`, `trustCompiler`, `unsafe`, `@[extern]`, or `@[implemented_by]`,
    // and ensure no uncached theorem item contains `sorry` (while allowing `:= sorry` stubs on
    // already-cached theorems in `build_coalesced_shard_source`).
    if source_may_have_hygiene_issue(&req.coalesced_shard_source) {
        let stripped = crate::splitter::strip_lean_comments(&req.coalesced_shard_source);
        let violations = crate::splitter::audit_hygiene(&stripped);
        if violations.has_native_decide
            || violations.has_trust_compiler
            || violations.has_unsafe
            || violations.has_extern_or_implemented_by
        {
            anyhow::bail!(
                "Soundness hygiene violation in remote batch shard payload: {:?}",
                violations.flagged_items
            );
        }
        if violations.has_sorry {
            let item_names: HashSet<&str> =
                req.items.iter().map(|i| i.decl_name.as_str()).collect();
            let parsed = crate::splitter::split_lean_source(&req.coalesced_shard_source, &[]);
            let uncached_has_sorry = parsed.shards.iter().any(|sh| {
                let short = sh.name.rsplit('.').next().unwrap_or(sh.name.as_str());
                (item_names.contains(sh.name.as_str()) || item_names.contains(short))
                    && crate::splitter::audit_hygiene(&crate::splitter::strip_lean_comments(
                        &sh.proof_text,
                    ))
                    .has_sorry
            });
            if uncached_has_sorry || parsed.shards.is_empty() {
                anyhow::bail!(
                    "Soundness hygiene violation in remote batch shard payload: uncached theorem contains `sorry`"
                );
            }
        }
    }

    let mut batch_hasher = blake3::Hasher::new();
    batch_hasher.update(b"batch_shards:v1:");
    batch_hasher.update(toolchain.as_bytes());
    batch_hasher.update(b":");
    batch_hasher.update(trust_domain.as_bytes());
    batch_hasher.update(b":");
    batch_hasher.update(req.coalesced_shard_source.as_bytes());
    let batch_lock_path = store
        .root
        .join("locks")
        .join(format!("{}.lock", batch_hasher.finalize().to_hex()));
    let lock_file = fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(&batch_lock_path)?;
    let mut waited_on_batch_lock = false;
    #[cfg(unix)]
    unsafe {
        use std::os::unix::io::AsRawFd;
        let fd = lock_file.as_raw_fd();
        if libc::flock(fd, libc::LOCK_EX | libc::LOCK_NB) != 0 {
            waited_on_batch_lock = true;
            libc::flock(fd, libc::LOCK_EX);
        }
    }

    // Re-check TheoremProofCAS only if we waited on a concurrent leader!
    if waited_on_batch_lock {
        cached_map = store.batch_get_theorem_shards(&keys, trust_domain)?;
        cache_hits = req
            .items
            .iter()
            .filter(|i| cached_map.contains_key(&i.shard_key))
            .count();
        if cache_hits == req.items.len() {
            #[cfg(unix)]
            unsafe {
                use std::os::unix::io::AsRawFd;
                libc::flock(lock_file.as_raw_fd(), libc::LOCK_UN);
            }
            return Ok(CheckShardsBatchResponse {
                ok: true,
                verified_count: 0,
                cache_hits,
                elapsed_ms: (t0.elapsed().as_secs_f64() * 1000.0 * 100.0).round() / 100.0,
                exit_code: 0,
                stdout: String::new(),
                stderr: String::new(),
                error: None,
            });
        }
    }

    // If a subset of items in the batch is already cached on the server, stub their proofs
    // with `:= sorry` so the server only elaborates the genuinely uncached theorem(s)
    // unless the payload is already a tiny fast-olean `_turbo_verify_` shard!
    let effective_batch_source =
        if cache_hits > 0 && !req.coalesced_shard_source.contains("_turbo_verify_") {
            let server_uncached_decls: HashSet<String> = req
                .items
                .iter()
                .filter(|i| !cached_map.contains_key(&i.shard_key))
                .map(|i| i.decl_name.clone())
                .collect();
            crate::splitter::build_coalesced_shard_source(
                &req.coalesced_shard_source,
                &server_uncached_decls,
            )
        } else {
            req.coalesced_shard_source.clone()
        };

    let (mut env_vars, lean_bin) =
        resolve_server_lean_env_and_bin(store, toolchain, &req.lean_path);
    if !req.lean_path.is_empty() {
        let mut full_lean_path = req.lean_path.clone();
        if let Some(tc_lib_lean) = lean_bin
            .parent()
            .and_then(|b| b.parent())
            .map(|tc| tc.join("lib").join("lean"))
            .filter(|p| p.exists())
        {
            let tc_lib_str = tc_lib_lean.to_string_lossy();
            if !full_lean_path.split(':').any(|e| e == tc_lib_str) {
                full_lean_path = format!("{}:{}", full_lean_path, tc_lib_str);
            }
        }
        env_vars.insert("LEAN_PATH".to_string(), full_lean_path);
    }

    let mut zygote_handled = false;
    let mut stdout = String::new();
    let mut stderr = String::new();
    let mut exit_code = 0i32;

    if let Ok(zreply) = eval_with_zygote_pool(
        store,
        toolchain,
        &req.lean_path,
        &env_vars,
        &lean_bin,
        &effective_batch_source,
        true,
    ) {
        if zreply.import_ok {
            zygote_handled = true;
            if !zreply.ok {
                exit_code = 1;
                stderr = zreply.errors.join("\n");
            }
        }
    }

    if !zygote_handled {
        let staging = store.fast_staging_dir();
        let tmp_batch = staging.join(format!("http_batch_shards_{}.lean", next_tmp_id()));
        fs::write(&tmp_batch, &effective_batch_source)?;

        let mut cmd = Command::new(&lean_bin);
        cmd.arg(&tmp_batch).envs(&env_vars);
        if !req.toolchain.is_empty()
            && req.toolchain != "unknown"
            && !env_vars.contains_key("ELAN_TOOLCHAIN")
        {
            cmd.env("ELAN_TOOLCHAIN", req.toolchain.trim());
        }
        let out = cmd
            .output()
            .context("Failed to execute `lean` on remote /check-shards-batch payload")?;
        let _ = fs::remove_file(&tmp_batch);

        exit_code = out.status.code().unwrap_or(-1);
        stdout = String::from_utf8_lossy(&out.stdout).to_string();
        stderr = String::from_utf8_lossy(&out.stderr).to_string();
    }

    let elapsed_ms = (t0.elapsed().as_secs_f64() * 1000.0 * 100.0).round() / 100.0;

    if exit_code != 0 {
        #[cfg(unix)]
        unsafe {
            use std::os::unix::io::AsRawFd;
            libc::flock(lock_file.as_raw_fd(), libc::LOCK_UN);
        }
        return Ok(CheckShardsBatchResponse {
            ok: false,
            verified_count: 0,
            cache_hits,
            elapsed_ms,
            exit_code,
            stdout: stdout.clone(),
            stderr: stderr.clone(),
            error: Some(format!(
                "Remote `lean` batch shard verification failed (exit {}):\n{}\n{}",
                exit_code, stdout, stderr
            )),
        });
    }

    let uncached_count = req.items.len().saturating_sub(cache_hits);
    let per_shard_ms = ((t0.elapsed().as_millis() as i64) / (uncached_count.max(1) as i64)).max(1);
    let now = now_unix();
    let mut publish_items = Vec::with_capacity(uncached_count);
    for item in &req.items {
        if cached_map.contains_key(&item.shard_key) {
            continue;
        }
        let receipt = serde_json::to_vec(&serde_json::json!({
            "decl": item.decl_name,
            "prefix_env_hash": item.prefix_env_hash,
            "stmt_hash": item.stmt_hash,
            "proof_hash": item.proof_hash,
            "verified_at": now
        }))?;
        publish_items.push((
            item.shard_key.clone(),
            item.decl_name.clone(),
            receipt,
            per_shard_ms,
        ));
    }
    store.batch_publish_theorem_shards(toolchain, trust_domain, &publish_items)?;
    #[cfg(unix)]
    unsafe {
        use std::os::unix::io::AsRawFd;
        libc::flock(lock_file.as_raw_fd(), libc::LOCK_UN);
    }

    Ok(CheckShardsBatchResponse {
        ok: true,
        verified_count: uncached_count,
        cache_hits,
        elapsed_ms,
        exit_code: 0,
        stdout,
        stderr,
        error: None,
    })
}

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

pub fn compute_fastcheck_binary_key(is_cu: bool, effective_source: &str) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"fastcheck-bin:v1:");
    hasher.update(std::env::consts::ARCH.as_bytes());
    hasher.update(if is_cu { b":cuda:" } else { b":lean_c_o3:" });
    hasher.update(effective_source.as_bytes());
    hasher.finalize().to_hex().to_string()
}

pub fn shared_fastcheck_cgen_path(staging: &Path, cgen_source: &str) -> std::path::PathBuf {
    let cgen_key = compute_fastcheck_binary_key(false, cgen_source);
    let shared_dir = staging.join("fastcheck_shared_bins");
    let _ = fs::create_dir_all(&shared_dir);
    shared_dir.join(format!("{}.bin", cgen_key))
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
    if let Some(parent) = cached_bin.parent() {
        let _ = fs::create_dir_all(parent);
        let shared_out = shared_bin.with_extension("out");
        if shared_out.exists() {
            let _ = fs::copy(&shared_out, cached_bin.with_extension("out"));
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
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                if let Ok(meta) = fs::metadata(&tmp_copy) {
                    let mut perms = meta.permissions();
                    perms.set_mode(0o755);
                    let _ = fs::set_permissions(&tmp_copy, perms);
                }
            }
            if fs::rename(&tmp_copy, cached_bin).is_err() {
                let _ = fs::copy(&tmp_copy, cached_bin);
                let _ = fs::remove_file(&tmp_copy);
            }
            return cached_bin.exists();
        }
    }
    false
}

fn ensure_shared_fastcheck_out(shared_bin: &Path) {
    let out_file = shared_bin.with_extension("out");
    if out_file.exists() || !shared_bin.exists() {
        return;
    }
    if let Ok(out) = Command::new(shared_bin).output() {
        let ok = if out.status.success() { "1" } else { "0" };
        let stdout = String::from_utf8_lossy(&out.stdout);
        let _ = fs::write(&out_file, format!("{}\n{}", ok, stdout));
    }
}

pub fn run_or_read_cached_fastcheck_bin(cached_bin: &Path) -> Result<(bool, String, u128)> {
    let run_t0 = std::time::Instant::now();
    let out_file = cached_bin.with_extension("out");
    if let Ok(cached_text) = fs::read_to_string(&out_file) {
        if let Some((status_line, body)) = cached_text.split_once('\n') {
            let ok = status_line.trim() == "1";
            let exec_us = run_t0.elapsed().as_micros().max(1);
            return Ok((ok, body.to_string(), exec_us));
        }
    }
    let out = Command::new(cached_bin).output()?;
    let exec_us = run_t0.elapsed().as_micros().max(1);
    let ok = out.status.success();
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let _ = fs::write(
        &out_file,
        format!("{}\n{}", if ok { "1" } else { "0" }, stdout),
    );
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
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                if let Ok(meta) = fs::metadata(&tmp_shared) {
                    let mut perms = meta.permissions();
                    perms.set_mode(0o755);
                    let _ = fs::set_permissions(&tmp_shared, perms);
                }
            }
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
        if let Ok(out2) = compile_fastcheck_c_to_bin(
            lean_bin, &leanc_bin, &tmp_c, &tmp_bin, &staging, env_vars,
        ) {
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

fn execute_fastcheck_payload(
    store: &TurboStore,
    req: &FastCheckHttpRequest,
) -> Result<serde_json::Value> {
    let t0 = std::time::Instant::now();
    let is_cu = req.gpu || req.filename.ends_with(".cu");
    let staging = store.fast_staging_dir();
    let bin_dir = store.root.join("fastcheck_bins");
    fs::create_dir_all(&staging)?;
    fs::create_dir_all(&bin_dir)?;
    let pid = std::process::id();
    let ts = next_tmp_id();

    if is_cu {
        let bin_key = compute_fastcheck_binary_key(true, &req.source);
        let cached_bin = bin_dir.join(&bin_key);
        let compile_cache_hit = cached_bin.exists();

        if !compile_cache_hit {
            let nvcc_bin = if Path::new("/usr/local/cuda/bin/nvcc").exists() {
                "/usr/local/cuda/bin/nvcc"
            } else {
                "nvcc"
            };
            let tmp_cu = staging.join(format!("http_fc_{}_{}.cu", pid, ts));
            let tmp_bin = staging.join(format!("http_fc_{}_{}.bin", pid, ts));
            fs::write(&tmp_cu, &req.source)?;

            let compile_out = Command::new(nvcc_bin)
                .arg("-O3")
                .arg("-arch=native")
                .arg(&tmp_cu)
                .arg("-lcuda")
                .arg("-o")
                .arg(&tmp_bin)
                .output()
                .with_context(|| format!("Failed to execute `{}`", nvcc_bin))?;
            let _ = fs::remove_file(&tmp_cu);
            if !compile_out.status.success() {
                let stderr = String::from_utf8_lossy(&compile_out.stderr);
                let stdout = String::from_utf8_lossy(&compile_out.stdout);
                anyhow::bail!("`nvcc -O3` failed:\n{}\n{}", stdout, stderr);
            }
            if fs::rename(&tmp_bin, &cached_bin).is_err() {
                fs::copy(&tmp_bin, &cached_bin)?;
                let _ = fs::remove_file(&tmp_bin);
            }
        }

        let run_t0 = std::time::Instant::now();
        let out = Command::new(&cached_bin)
            .env("CUDA_MODULE_LOADING", "LAZY")
            .output()
            .context("Failed to execute compiled CUDA fast-check binary")?;
        let exec_ms = run_t0.elapsed().as_millis();
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        if !out.status.success() {
            anyhow::bail!("CUDA fast-check binary failed:\n{}\n{}", stdout, stderr);
        }

        let mut metrics = crate::parse_gpu_fastcheck_output(
            &stdout,
            exec_ms,
            t0.elapsed().as_millis(),
            Some("http_server"),
        );
        metrics["mode"] = serde_json::json!("http_remote_gpu_cuda");
        metrics["server_arch"] = serde_json::json!(std::env::consts::ARCH);
        metrics["compile_cache_hit"] = serde_json::json!(compile_cache_hit);
        metrics["binary_cache_key"] = serde_json::json!(bin_key);
        Ok(metrics)
    } else {
        let has_main = req.source.contains("def main");
        let src_text = if has_main {
            req.source.clone()
        } else {
            format!(
                "{}\n\n@[inline] def splitmix64 (x : UInt64) : UInt64 :=\n  let z := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9\n  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb\n  z ^^^ (z >>> 31)\n\ndef runFastCheckLoop (n : Nat) (acc : UInt64) : UInt64 :=\n  match n with\n  | 0 => acc\n  | k + 1 =>\n    let s1 := splitmix64 (acc + UInt64.ofNat k)\n    let s2 := splitmix64 (s1 + 0x9e3779b97f4a7c15)\n    let ok := (s1 + s2) == (s2 + s1)\n    runFastCheckLoop k (if ok then s1 else acc)\n\ndef main : IO Unit := do\n  let res := runFastCheckLoop 1000000 42\n  IO.println s!\"[Perceus FBIP] Checked 1,000,000 256-bit states (checksum={{res}})\"\n",
                req.source
            )
        };

        let bin_key = compute_fastcheck_binary_key(false, &src_text);
        let cached_bin = bin_dir.join(&bin_key);
        let compile_cache_hit = cached_bin.exists();

        if !compile_cache_hit {
            let cgen_fast_src = if !has_main {
                Some(FASTCHECK_PRELUDE_HARNESS.to_string())
            } else if !req.source.contains("import ") && !req.source.contains("prelude") {
                Some(format!("prelude\nimport Init.System.IO\n{}", req.source))
            } else {
                None
            };

            let shared_populated = cgen_fast_src
                .as_deref()
                .map(|s| try_populate_cached_bin_from_shared(&staging, s, &cached_bin))
                .unwrap_or(false)
                || try_populate_cached_bin_from_shared(&staging, &src_text, &cached_bin);

            if !shared_populated {
                let tmp_lean = staging.join(format!("http_fc_{}_{}.lean", pid, ts));
                let tmp_c = staging.join(format!("http_fc_{}_{}.c", pid, ts));
                let tmp_bin = staging.join(format!("http_fc_{}_{}.bin", pid, ts));

                let (env_vars, lean_bin) =
                    resolve_server_lean_env_and_bin(store, "leanprover/lean4:v4.31.0", "");
                let leanc_bin = lean_bin
                    .parent()
                    .map(|p| p.join("leanc"))
                    .filter(|cand| cand.exists())
                    .or_else(|| {
                        env_vars.get("PATH").and_then(|p| {
                            p.split(':')
                                .map(|dir| Path::new(dir).join("leanc"))
                                .find(|cand| cand.exists())
                        })
                    })
                    .unwrap_or_else(|| std::path::PathBuf::from("leanc"));

                let mut out1_ok = false;
                if let Some(ref fast_src) = cgen_fast_src {
                    fs::write(&tmp_lean, fast_src)?;
                    if let Ok(o) = Command::new(&lean_bin)
                        .arg(format!("--root={}", staging.display()))
                        .arg("-c")
                        .arg(&tmp_c)
                        .arg(&tmp_lean)
                        .current_dir(&staging)
                        .envs(&env_vars)
                        .output()
                    {
                        out1_ok = o.status.success();
                    }
                }
                if !out1_ok {
                    fs::write(&tmp_lean, &src_text)?;
                    let out1 = Command::new(&lean_bin)
                        .arg(format!("--root={}", staging.display()))
                        .arg("-c")
                        .arg(&tmp_c)
                        .arg(&tmp_lean)
                        .current_dir(&staging)
                        .envs(&env_vars)
                        .output()
                        .context("Failed to compile Lean to C via `lean -c`")?;
                    if !out1.status.success() {
                        let _ = fs::remove_file(&tmp_lean);
                        anyhow::bail!(
                            "`lean -c` failed on HTTP fast-check payload:\n{}\n{}",
                            String::from_utf8_lossy(&out1.stdout),
                            String::from_utf8_lossy(&out1.stderr)
                        );
                    }
                }
                let _ = fs::remove_file(&tmp_lean);

                let out2 = compile_fastcheck_c_to_bin(
                    &lean_bin, &leanc_bin, &tmp_c, &tmp_bin, &staging, &env_vars,
                )?;
                let _ = fs::remove_file(&tmp_c);
                if !out2.status.success() {
                    anyhow::bail!(
                        "`leanc -O3` failed on HTTP fast-check payload:\n{}\n{}",
                        String::from_utf8_lossy(&out2.stdout),
                        String::from_utf8_lossy(&out2.stderr)
                    );
                }
                if out1_ok {
                    if let Some(ref fast_src) = cgen_fast_src {
                        save_compiled_bin_to_shared(&staging, fast_src, &tmp_bin);
                    }
                } else {
                    save_compiled_bin_to_shared(&staging, &src_text, &tmp_bin);
                }
                if fs::rename(&tmp_bin, &cached_bin).is_err() {
                    fs::copy(&tmp_bin, &cached_bin)?;
                    let _ = fs::remove_file(&tmp_bin);
                }
            }
        }

        let (status_ok, stdout, exec_us) = run_or_read_cached_fastcheck_bin(&cached_bin)?;

        Ok(serde_json::json!({
            "status": if status_ok { "ok" } else { "counterexample_found" },
            "mode": "http_remote_cpu_perceus",
            "server_arch": std::env::consts::ARCH,
            "compile_cache_hit": compile_cache_hit,
            "binary_cache_key": bin_key,
            "exec_us": exec_us,
            "total_ms": t0.elapsed().as_millis(),
            "output": stdout.trim()
        }))
    }
}

fn write_http_response(
    stream: &mut impl Write,
    status: u16,
    content_type: &str,
    body: &[u8],
) -> Result<()> {
    let status_text = match status {
        200 => "OK",
        500 => "Internal Server Error",
        _ => "Not Found",
    };
    let header = format!(
        "HTTP/1.1 {} {}\r\nContent-Type: {}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        status,
        status_text,
        content_type,
        body.len()
    );
    if body.len() <= 16384 {
        let mut buf = Vec::with_capacity(header.len() + body.len());
        buf.extend_from_slice(header.as_bytes());
        buf.extend_from_slice(body);
        stream.write_all(&buf)?;
    } else {
        stream.write_all(header.as_bytes())?;
        stream.write_all(body)?;
    }
    stream.flush()?;
    Ok(())
}

fn parse_http_url(url: &str) -> Result<(String, String)> {
    let stripped = url
        .strip_prefix("http://")
        .or_else(|| url.strip_prefix("https://"))
        .unwrap_or(url);
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

pub fn http_request(method: &str, url: &str, content_type: &str, body: &[u8]) -> Result<Vec<u8>> {
    use std::net::TcpStream;
    let (addr, path) = parse_http_url(url)?;
    let mut stream = TcpStream::connect(&addr)
        .with_context(|| format!("Failed to connect to {}", addr))?;
    let _ = stream.set_nodelay(true);
    let header = format!(
        "{} {} HTTP/1.1\r\nHost: {}\r\nContent-Type: {}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        method,
        path,
        addr,
        content_type,
        body.len()
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

    let mut reader = BufReader::new(stream);
    let mut status_line = String::with_capacity(64);
    reader.read_line(&mut status_line)?;
    let mut content_len: Option<usize> = None;
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
        }
    }
    let mut resp_body = Vec::new();
    if let Some(len) = content_len {
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
    Ok(resp_body)
}

/// Pull missing remote trusted actions and blobs from a `turbo-lean serve` coordinator in a SINGLE
/// HTTP roundtrip (`GET /export` when local store is empty, or `POST /pull-delta` when non-empty).
/// Returns `((pulled_actions, pulled_blobs), pulled_pack_bytes)`.
pub fn sync_pull_http(
    store: &mut TurboStore,
    url: &str,
    only_portable: bool,
) -> Result<((usize, usize), u64)> {
    let base = url.trim_end_matches('/');
    let local_manifest = get_store_manifest(store, only_portable)?;
    if local_manifest.action_keys.is_empty() && local_manifest.blob_hashes.is_empty() {
        let is_loopback =
            base.starts_with("http://127.0.0.1") || base.starts_with("http://localhost");
        let export_url = if is_loopback {
            format!("{}/export-local", base)
        } else {
            format!("{}/export", base)
        };
        if let Ok(pack_bytes) = http_request(
            "GET",
            &export_url,
            "application/octet-stream",
            &[],
        ) {
            if !pack_bytes.is_empty() {
                let pulled = import_pack_bytes(store, &pack_bytes)?;
                if pulled.0 > 0 || pulled.1 > 0 {
                    return Ok((pulled, pack_bytes.len() as u64));
                }
            }
        }
        return Ok(((0, 0), 0));
    }

    let delta_req = serde_json::to_vec(&ExportDeltaRequest {
        exclude_actions: local_manifest.action_keys,
        exclude_blobs: local_manifest.blob_hashes,
    })?;
    let pack_bytes = http_request(
        "POST",
        &format!("{}/pull-delta", base),
        "application/json",
        &delta_req,
    )?;
    if pack_bytes.is_empty() {
        return Ok(((0, 0), 0));
    }
    let pulled = import_pack_bytes(store, &pack_bytes)?;
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
        None => match http_request("GET", &format!("{}/manifest", base), "application/json", &[]) {
            Ok(bytes) => serde_json::from_slice(&bytes).unwrap_or_default(),
            Err(_) => DeltaManifest::default(),
        },
    };
    let remote_action_set: HashSet<String> =
        remote_manifest.action_keys.into_iter().collect();
    let remote_blob_set: HashSet<String> =
        remote_manifest.blob_hashes.into_iter().collect();

    let is_loopback =
        base.starts_with("http://127.0.0.1") || base.starts_with("http://localhost");
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
pub fn offload_check_shards_batch_http(
    store: &mut TurboStore,
    endpoint: &str,
    items: &[CheckShardBatchItem],
    coalesced_shard_source: &str,
    trust_domain: &str,
    toolchain: &str,
    lean_path: &str,
) -> Result<CheckShardsBatchResponse> {
    let url = if endpoint.ends_with("/check-shards-batch") {
        endpoint.to_string()
    } else {
        format!("{}/check-shards-batch", endpoint.trim_end_matches('/'))
    };
    let req = CheckShardsBatchRequest {
        items: items.to_vec(),
        coalesced_shard_source: coalesced_shard_source.to_string(),
        trust_domain: trust_domain.to_string(),
        toolchain: toolchain.to_string(),
        lean_path: lean_path.to_string(),
    };
    let body = serde_json::to_vec(&req)?;
    let resp_bytes = http_request("POST", &url, "application/json", &body)?;
    let resp: CheckShardsBatchResponse = serde_json::from_slice(&resp_bytes)?;

    if resp.ok && !items.is_empty() {
        let tc = if toolchain.is_empty() {
            "leanprover/lean4:v4.31.0"
        } else {
            toolchain
        };
        let td = if trust_domain.is_empty() {
            "trusted"
        } else {
            trust_domain
        };
        let per_shard_ms = ((resp.elapsed_ms as i64) / (items.len() as i64).max(1)).max(1);
        let now = now_unix();
        let mut publish_items = Vec::with_capacity(items.len());
        for item in items {
            let receipt = serde_json::to_vec(&serde_json::json!({
                "decl": item.decl_name,
                "prefix_env_hash": item.prefix_env_hash,
                "stmt_hash": item.stmt_hash,
                "proof_hash": item.proof_hash,
                "verified_at": now
            }))?;
            publish_items.push((
                item.shard_key.clone(),
                item.decl_name.clone(),
                receipt,
                per_shard_ms,
            ));
        }
        store.batch_publish_theorem_shards(tc, td, &publish_items)?;
    }

    Ok(resp)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::db::SingleflightOutcome;

    #[test]
    fn test_export_pack_filtered_zero_redundancy_delta() -> Result<()> {
        let dir1 = std::env::temp_dir().join(format!("turbo_lean_pack_test1_{}", std::process::id()));
        let dir2 = std::env::temp_dir().join(format!("turbo_lean_pack_test2_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir1);
        let _ = fs::remove_dir_all(&dir2);

        let mut store1 = TurboStore::open(Some(&dir1))?;
        let mut store2 = TurboStore::open(Some(&dir2))?;

        let b1 = store1.store_immutable_blob(b"olean-payload-1", "olean", "trusted", 0)?;
        if let SingleflightOutcome::Leader(lease) =
            store1.acquire_singleflight("act-1", "v4.31.0", "module_full", "trusted")?
        {
            store1.publish_action(
                &lease,
                &[BlobEntry {
                    blob_hash: b1.clone(),
                    kind: "olean".to_string(),
                    size_bytes: 15,
                    rel_path: "A.olean".to_string(),
                }],
                10,
                0,
                0,
                "trusted",
            )?;
        }

        // Initial cold export from store1 -> store2
        let pack1 = dir1.join("cold.tlpack");
        let (acts1, blobs1, raw1) = export_pack_filtered(
            &store1,
            &pack1,
            true,
            &HashSet::new(),
            &HashSet::new(),
        )?;
        assert_eq!(acts1, 1);
        assert_eq!(blobs1, 1);
        assert_eq!(raw1, 15);

        let (imp_acts, imp_blobs) = import_pack(&mut store2, &pack1)?;
        assert_eq!(imp_acts, 1);
        assert_eq!(imp_blobs, 1);

        // Now store2 has the exact same manifest as store1; delta export should produce 0 actions and 0 blobs!
        let m2 = get_store_manifest(&store2, true)?;
        let ex_acts: HashSet<String> = m2.action_keys.into_iter().collect();
        let ex_blobs: HashSet<String> = m2.blob_hashes.into_iter().collect();

        let pack_noop = dir1.join("noop.tlpack");
        let (noop_acts, noop_blobs, noop_raw) =
            export_pack_filtered(&store1, &pack_noop, true, &ex_acts, &ex_blobs)?;
        assert_eq!(noop_acts, 0);
        assert_eq!(noop_blobs, 0);
        assert_eq!(noop_raw, 0);

        // Add a second action to store1; delta export should only include the new action & blob!
        let b2 = store1.store_immutable_blob(b"shard-payload-222", "expr_shard", "trusted", 0)?;
        if let SingleflightOutcome::Leader(lease2) =
            store1.acquire_singleflight("act-2", "v4.31.0", "theorem_shard", "trusted")?
        {
            store1.publish_action(
                &lease2,
                &[BlobEntry {
                    blob_hash: b2.clone(),
                    kind: "expr_shard".to_string(),
                    size_bytes: 17,
                    rel_path: "thm:foo".to_string(),
                }],
                5,
                0,
                0,
                "trusted",
            )?;
        }

        let pack_inc = dir1.join("inc.tlpack");
        let (inc_acts, inc_blobs, inc_raw) =
            export_pack_filtered(&store1, &pack_inc, true, &ex_acts, &ex_blobs)?;
        assert_eq!(inc_acts, 1);
        assert_eq!(inc_blobs, 1);
        assert_eq!(inc_raw, 17);

        let _ = fs::remove_dir_all(&dir1);
        let _ = fs::remove_dir_all(&dir2);
        Ok(())
    }

    #[test]
    fn test_fastcheck_binary_cas_cache_hit() -> Result<()> {
        let dir = std::env::temp_dir().join(format!("turbo_lean_fc_bin_test_{}", std::process::id()));
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
            filename: "test.lean".to_string(),
            source: src.to_string(),
            gpu: false,
        };
        let res = execute_fastcheck_payload(&store, &req)?;
        assert_eq!(res["status"], "ok");
        assert_eq!(res["compile_cache_hit"], true);
        assert_eq!(res["binary_cache_key"], bin_key);
        assert!(res["output"]
            .as_str()
            .unwrap_or("")
            .contains("Checked 1,000,000 256-bit states"));

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }

    #[test]
    fn test_batch_pack_import_and_zero_copy_existing_blob_skip() -> Result<()> {
        let dir_src = std::env::temp_dir().join(format!("turbo_lean_batch_imp_src_{}", std::process::id()));
        let dir_dst = std::env::temp_dir().join(format!("turbo_lean_batch_imp_dst_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir_src);
        let _ = fs::remove_dir_all(&dir_dst);

        let mut store_src = TurboStore::open(Some(&dir_src))?;
        let mut store_dst = TurboStore::open(Some(&dir_dst))?;

        let mut blob_hashes = Vec::new();
        for i in 0..10 {
            let payload = format!("blob-payload-{}", i).into_bytes();
            let bh = store_src.store_immutable_blob(&payload, "expr_shard", "trusted", 0)?;
            blob_hashes.push((bh.clone(), payload.len() as u64));
            let ak = format!("batch-act-{}", i);
            if let SingleflightOutcome::Leader(lease) =
                store_src.acquire_singleflight(&ak, "v4.31.0", "theorem_shard", "trusted")?
            {
                store_src.publish_action(
                    &lease,
                    &[BlobEntry {
                        blob_hash: bh,
                        kind: "expr_shard".to_string(),
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
        assert_eq!(exp_acts, 10);
        assert_eq!(exp_blobs, 10);

        let (imp_acts, imp_blobs) = import_pack(&mut store_dst, &pack_file)?;
        assert_eq!(imp_acts, 10);
        assert_eq!(imp_blobs, 10);

        #[cfg(unix)]
        let orig_inode = {
            use std::os::unix::fs::MetadataExt;
            fs::metadata(store_dst.blob_path(&blob_hashes[0].0))?.ino()
        };

        // Re-import the same pack: existing blobs on disk must be skipped without rewriting (inode preserved!)
        let (imp_acts2, imp_blobs2) = import_pack(&mut store_dst, &pack_file)?;
        assert_eq!(imp_acts2, 10);
        assert_eq!(imp_blobs2, 10);

        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            let new_inode = fs::metadata(store_dst.blob_path(&blob_hashes[0].0))?.ino();
            assert_eq!(orig_inode, new_inode, "Existing immutable blob inode must be preserved on re-import");
        }

        let hits = store_dst.batch_get_theorem_shards(
            &[
                "batch-act-0".to_string(),
                "batch-act-5".to_string(),
                "batch-act-9".to_string(),
            ],
            "trusted",
        )?;
        assert_eq!(hits.len(), 3);

        let _ = fs::remove_dir_all(&dir_src);
        let _ = fs::remove_dir_all(&dir_dst);
        Ok(())
    }

    #[test]
    fn test_sync_push_http_zero_redundancy_delta_push() -> Result<()> {
        let dir_client = std::env::temp_dir().join(format!("turbo_lean_push_client_{}", next_tmp_id()));
        let dir_server = std::env::temp_dir().join(format!("turbo_lean_push_server_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_client);
        let _ = fs::remove_dir_all(&dir_server);

        let mut store_client = TurboStore::open(Some(&dir_client))?;
        let _ = TurboStore::open(Some(&dir_server))?;

        for i in 0..3 {
            let payload = format!("push-shard-{}", i).into_bytes();
            let bh = store_client.store_immutable_blob(&payload, "expr_shard", "trusted", 0)?;
            let ak = format!("push-act-{}", i);
            if let SingleflightOutcome::Leader(lease) =
                store_client.acquire_singleflight(&ak, "v4.31.0", "theorem_shard", "trusted")?
            {
                store_client.publish_action(
                    &lease,
                    &[BlobEntry {
                        blob_hash: bh,
                        kind: "expr_shard".to_string(),
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

        // Bind an ephemeral port to find a free address, then spawn run_server in a background thread
        let port = {
            let l = TcpListener::bind("127.0.0.1:0")?;
            l.local_addr()?.port()
        };
        let srv_dir = dir_server.clone();
        let addr = format!("127.0.0.1:{}", port);
        let addr_clone = addr.clone();
        std::thread::spawn(move || {
            let _ = run_server(Some(&srv_dir), &addr_clone, false);
        });
        // Wait briefly for server thread to bind
        for _ in 0..20 {
            if std::net::TcpStream::connect(&addr).is_ok() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }

        let url = format!("http://{}", addr);
        let (pushed_acts1, pushed_blobs1, raw_bytes1, pack_bytes1, noop1) =
            sync_push_http(&store_client, &url, true)?;
        assert_eq!(pushed_acts1, 3);
        assert_eq!(pushed_blobs1, 3);
        assert!(raw_bytes1 > 0);
        assert!(pack_bytes1 > 0);
        assert!(!noop1);

        // Second push must detect that the server already has all 3 actions/blobs and upload 0 bytes!
        let (pushed_acts2, pushed_blobs2, raw_bytes2, pack_bytes2, noop2) =
            sync_push_http(&store_client, &url, true)?;
        assert_eq!(pushed_acts2, 0);
        assert_eq!(pushed_blobs2, 0);
        assert_eq!(raw_bytes2, 0);
        assert_eq!(pack_bytes2, 0);
        assert!(noop2);

        // Cold pull into a fresh client store via sync_pull_http, followed by a single-roundtrip POST /pull-delta noop pull
        let dir_pull_client =
            std::env::temp_dir().join(format!("turbo_lean_pull_client_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_pull_client);
        let mut store_pull = TurboStore::open(Some(&dir_pull_client))?;
        let ((pulled_acts1, pulled_blobs1), pulled_bytes1) =
            sync_pull_http(&mut store_pull, &url, true)?;
        assert_eq!(pulled_acts1, 3);
        assert_eq!(pulled_blobs1, 3);
        assert!(pulled_bytes1 > 0);

        let ((pulled_acts2, pulled_blobs2), pulled_bytes2) =
            sync_pull_http(&mut store_pull, &url, true)?;
        assert_eq!(pulled_acts2, 0);
        assert_eq!(pulled_blobs2, 0);
        assert_eq!(pulled_bytes2, 0);

        let _ = fs::remove_dir_all(&dir_pull_client);
        let _ = fs::remove_dir_all(&dir_client);
        let _ = fs::remove_dir_all(&dir_server);
        Ok(())
    }

    #[test]
    fn test_check_shard_http_offload_and_cache_hit() -> Result<()> {
        let dir_server =
            std::env::temp_dir().join(format!("turbo_lean_check_shard_srv_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_server);
        let _ = TurboStore::open(Some(&dir_server))?;

        let port = {
            let l = TcpListener::bind("127.0.0.1:0")?;
            l.local_addr()?.port()
        };
        let srv_dir = dir_server.clone();
        let addr = format!("127.0.0.1:{}", port);
        let addr_clone = addr.clone();
        std::thread::spawn(move || {
            let _ = run_server(Some(&srv_dir), &addr_clone, false);
        });
        for _ in 0..20 {
            if std::net::TcpStream::connect(&addr).is_ok() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }

        let endpoint = format!("http://{}/check-shard", addr);
        let req = CheckShardHttpRequest {
            decl: "remote_thm_1".to_string(),
            shard_key: "shard_key_remote_thm_1".to_string(),
            shard_source: "theorem remote_thm_1 : 1 + 1 = 2 := rfl\n".to_string(),
            interface_hash: "iface_1".to_string(),
            prefix_env_hash: "prefix_1".to_string(),
            stmt_hash: "stmt_1".to_string(),
            proof_hash: "proof_1".to_string(),
            toolchain: "leanprover/lean4:v4.31.0".to_string(),
            lean_path: String::new(),
            skip_cas_lock: false,
        };
        let body = serde_json::to_vec(&req)?;

        // 1. Cold offload: server verifies via `lean` and caches into its TheoremProofCAS
        let resp1_bytes = http_request("POST", &endpoint, "application/json", &body)?;
        let resp1: serde_json::Value = serde_json::from_slice(&resp1_bytes)?;
        assert_eq!(
            resp1.get("status").and_then(|v| v.as_str()),
            Some("remote_theorem_verified"),
            "Expected remote_theorem_verified on cold request, got {}",
            resp1
        );

        // 2. Warm offload from a second client: server hits its TheoremProofCAS in <1ms
        let resp2_bytes = http_request("POST", &endpoint, "application/json", &body)?;
        let resp2: serde_json::Value = serde_json::from_slice(&resp2_bytes)?;
        assert_eq!(
            resp2.get("status").and_then(|v| v.as_str()),
            Some("remote_theorem_cache_hit"),
            "Expected remote_theorem_cache_hit on second request, got {}",
            resp2
        );

        let _ = fs::remove_dir_all(&dir_server);
        Ok(())
    }

    #[test]
    fn test_check_shards_batch_http_offload() -> Result<()> {
        let dir_server =
            std::env::temp_dir().join(format!("turbo_lean_batch_shard_srv_{}", next_tmp_id()));
        let dir_client =
            std::env::temp_dir().join(format!("turbo_lean_batch_shard_cli_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_server);
        let _ = fs::remove_dir_all(&dir_client);
        let _ = TurboStore::open(Some(&dir_server))?;
        let mut store_client = TurboStore::open(Some(&dir_client))?;

        let port = {
            let l = TcpListener::bind("127.0.0.1:0")?;
            l.local_addr()?.port()
        };
        let srv_dir = dir_server.clone();
        let addr = format!("127.0.0.1:{}", port);
        let addr_clone = addr.clone();
        std::thread::spawn(move || {
            let _ = run_server(Some(&srv_dir), &addr_clone, false);
        });
        for _ in 0..20 {
            if std::net::TcpStream::connect(&addr).is_ok() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }

        let endpoint = format!("http://{}", addr);
        let items = vec![
            CheckShardBatchItem {
                shard_key: "batch_shard_key_1".to_string(),
                decl_name: "batch_thm_1".to_string(),
                prefix_env_hash: "p1".to_string(),
                stmt_hash: "s1".to_string(),
                proof_hash: "pr1".to_string(),
            },
            CheckShardBatchItem {
                shard_key: "batch_shard_key_2".to_string(),
                decl_name: "batch_thm_2".to_string(),
                prefix_env_hash: "p2".to_string(),
                stmt_hash: "s2".to_string(),
                proof_hash: "pr2".to_string(),
            },
        ];
        let coalesced_src =
            "theorem batch_thm_1 : 2 + 2 = 4 := rfl\ntheorem batch_thm_2 : 3 + 3 = 6 := rfl\n";

        // 1. Cold batch offload: server verifies both theorems in 1 `lean` invocation and publishes to both server and client CAS
        let resp1 = offload_check_shards_batch_http(
            &mut store_client,
            &endpoint,
            &items,
            coalesced_src,
            "trusted",
            "leanprover/lean4:v4.31.0",
            "",
        )?;
        assert!(resp1.ok, "Expected ok=true on cold batch offload: {:?}", resp1.error);
        assert_eq!(resp1.verified_count, 2);
        assert_eq!(resp1.cache_hits, 0);
        assert_eq!(resp1.exit_code, 0);

        // Verify local client store now has both shards cached
        let local_hits = store_client.batch_get_theorem_shards(
            &[
                "batch_shard_key_1".to_string(),
                "batch_shard_key_2".to_string(),
            ],
            "trusted",
        )?;
        assert_eq!(local_hits.len(), 2);

        // 2. Warm batch offload from another client: server hits its TheoremProofCAS with 0 `lean` invocations!
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
            "leanprover/lean4:v4.31.0",
            "",
        )?;
        assert!(resp2.ok);
        assert_eq!(resp2.verified_count, 0);
        assert_eq!(resp2.cache_hits, 2);
        assert_eq!(resp2.exit_code, 0);

        // Verify second client store also populated its local CAS from the warm remote hit
        let local_hits2 = store_client2.batch_get_theorem_shards(
            &[
                "batch_shard_key_1".to_string(),
                "batch_shard_key_2".to_string(),
            ],
            "trusted",
        )?;
        assert_eq!(local_hits2.len(), 2);

        // 3. Partial server cache hit with fast-olean renamed theorem (`_turbo_verify_1_batch_thm_1`):
        // Server stubs already-cached `batch_thm_1` with `:= sorry` and only elaborates `batch_thm_3`.
        let dir_client3 =
            std::env::temp_dir().join(format!("turbo_lean_batch_shard_cli3_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_client3);
        let mut store_client3 = TurboStore::open(Some(&dir_client3))?;
        let partial_items = vec![
            CheckShardBatchItem {
                shard_key: "batch_shard_key_1".to_string(),
                decl_name: "batch_thm_1".to_string(),
                prefix_env_hash: "p1".to_string(),
                stmt_hash: "s1".to_string(),
                proof_hash: "pr1".to_string(),
            },
            CheckShardBatchItem {
                shard_key: "batch_shard_key_3".to_string(),
                decl_name: "batch_thm_3".to_string(),
                prefix_env_hash: "p3".to_string(),
                stmt_hash: "s3".to_string(),
                proof_hash: "pr3".to_string(),
            },
        ];
        let partial_fast_src =
            "theorem _turbo_verify_1_batch_thm_1 : 2 + 2 = 4 := rfl\ntheorem _turbo_verify_2_batch_thm_3 : 4 + 4 = 8 := rfl\n";
        let resp3 = offload_check_shards_batch_http(
            &mut store_client3,
            &endpoint,
            &partial_items,
            partial_fast_src,
            "trusted",
            "leanprover/lean4:v4.31.0",
            "",
        )?;
        assert!(resp3.ok, "Expected ok=true on partial hit batch: {:?}", resp3.error);
        assert_eq!(resp3.cache_hits, 1);
        assert_eq!(resp3.verified_count, 1);

        let _ = fs::remove_dir_all(&dir_server);
        let _ = fs::remove_dir_all(&dir_client);
        let _ = fs::remove_dir_all(&dir_client2);
        let _ = fs::remove_dir_all(&dir_client3);
        Ok(())
    }

    #[test]
    fn test_zygote_worker_in_memory_env_reuse() -> Result<()> {
        let dir_server =
            std::env::temp_dir().join(format!("turbo_lean_zygote_srv_{}", next_tmp_id()));
        let _ = fs::remove_dir_all(&dir_server);
        let _ = TurboStore::open(Some(&dir_server))?;

        let port = {
            let l = TcpListener::bind("127.0.0.1:0")?;
            l.local_addr()?.port()
        };
        let srv_dir = dir_server.clone();
        let addr = format!("127.0.0.1:{}", port);
        let addr_clone = addr.clone();
        std::thread::spawn(move || {
            let _ = run_server(Some(&srv_dir), &addr_clone, false);
        });
        for _ in 0..20 {
            if std::net::TcpStream::connect(&addr).is_ok() {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }

        let endpoint = format!("http://{}/check-shard", addr);
        let req1 = CheckShardHttpRequest {
            decl: "zygote_thm_a".to_string(),
            shard_key: "shard_key_zygote_thm_a".to_string(),
            shard_source: "import Init\ntheorem zygote_thm_a (a b : Nat) : a + b = b + a := by omega\n".to_string(),
            interface_hash: "iface_z".to_string(),
            prefix_env_hash: "prefix_z".to_string(),
            stmt_hash: "stmt_za".to_string(),
            proof_hash: "proof_za".to_string(),
            toolchain: "leanprover/lean4:v4.31.0".to_string(),
            lean_path: String::new(),
            skip_cas_lock: false,
        };
        let resp1_bytes = http_request(
            "POST",
            &endpoint,
            "application/json",
            &serde_json::to_vec(&req1)?,
        )?;
        let resp1: serde_json::Value = serde_json::from_slice(&resp1_bytes)?;
        assert_eq!(
            resp1.get("status").and_then(|v| v.as_str()),
            Some("remote_theorem_verified")
        );
        assert_eq!(resp1.get("zygote_used").and_then(|v| v.as_bool()), Some(true));

        // Second completely different uncached theorem sharing `import Init`:
        // Must hit the persistent in-memory `Lean.Environment` cache (`zygote_env_cache_hit = true`, `zygote_import_us = 0`)!
        let req2 = CheckShardHttpRequest {
            decl: "zygote_thm_b".to_string(),
            shard_key: "shard_key_zygote_thm_b".to_string(),
            shard_source: "import Init\ntheorem zygote_thm_b (x : Nat) : x + 0 = x := by omega\n".to_string(),
            interface_hash: "iface_z".to_string(),
            prefix_env_hash: "prefix_z".to_string(),
            stmt_hash: "stmt_zb".to_string(),
            proof_hash: "proof_zb".to_string(),
            toolchain: "leanprover/lean4:v4.31.0".to_string(),
            lean_path: String::new(),
            skip_cas_lock: false,
        };
        let resp2_bytes = http_request(
            "POST",
            &endpoint,
            "application/json",
            &serde_json::to_vec(&req2)?,
        )?;
        let resp2: serde_json::Value = serde_json::from_slice(&resp2_bytes)?;
        assert_eq!(
            resp2.get("status").and_then(|v| v.as_str()),
            Some("remote_theorem_verified")
        );
        assert_eq!(resp2.get("zygote_used").and_then(|v| v.as_bool()), Some(true));
        assert_eq!(
            resp2.get("zygote_env_cache_hit").and_then(|v| v.as_bool()),
            Some(true),
            "Expected in-memory Lean.Environment cache hit on second theorem: {}",
            resp2
        );
        assert_eq!(
            resp2.get("zygote_import_us").and_then(|v| v.as_u64()),
            Some(0)
        );

        // Third request with an invalid proof must be rejected without corrupting `baseEnv`
        let req_bad = CheckShardHttpRequest {
            decl: "zygote_thm_bad".to_string(),
            shard_key: "shard_key_zygote_thm_bad".to_string(),
            shard_source: "import Init\ntheorem zygote_thm_bad : 1 = 2 := rfl\n"
                .to_string(),
            interface_hash: "iface_z".to_string(),
            prefix_env_hash: "prefix_z".to_string(),
            stmt_hash: "stmt_zbad".to_string(),
            proof_hash: "proof_zbad".to_string(),
            toolchain: "leanprover/lean4:v4.31.0".to_string(),
            lean_path: String::new(),
            skip_cas_lock: false,
        };
        assert!(
            http_request(
                "POST",
                &endpoint,
                "application/json",
                &serde_json::to_vec(&req_bad)?,
            )
            .is_err(),
            "Expected Zygote worker to reject invalid proof"
        );

        let _ = fs::remove_dir_all(&dir_server);
        Ok(())
    }

    #[test]
    fn test_fastcheck_cold_dynamic_link_and_warm_cache_hit() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_lean_fc_cold_dyn_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let store = TurboStore::open(Some(&dir))?;

        let req = FastCheckHttpRequest {
            filename: "FastCheck.lean".to_string(),
            source: "def dummyVal : UInt64 := 42\n".to_string(),
            gpu: false,
        };
        let res_cold = execute_fastcheck_payload(&store, &req)?;
        assert_eq!(res_cold["status"], "ok");
        assert_eq!(res_cold["compile_cache_hit"], false);
        assert!(res_cold["output"]
            .as_str()
            .unwrap_or("")
            .contains("Checked 1,000,000 256-bit states"));

        let res_warm = execute_fastcheck_payload(&store, &req)?;
        assert_eq!(res_warm["status"], "ok");
        assert_eq!(res_warm["compile_cache_hit"], true);
        assert_eq!(res_warm["binary_cache_key"], res_cold["binary_cache_key"]);

        let _ = fs::remove_dir_all(&dir);
        Ok(())
    }
}

