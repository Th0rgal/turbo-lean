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
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if let Ok(m) = fs::metadata(&tmp_dest) {
                let mut p = m.permissions();
                p.set_mode(0o444);
                let _ = fs::set_permissions(&tmp_dest, p);
            }
        }
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
    let full_export_cache_path =
        if exclude_actions.is_empty() && exclude_blobs.is_empty() {
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

pub fn try_parse_v3_header(input_bytes: &[u8]) -> Option<PackManifest> {
    if !input_bytes.starts_with(b"TLPK\x00\x00\x00\x03") || input_bytes.len() < 16 {
        return None;
    }
    let mut len_buf = [0u8; 8];
    len_buf.copy_from_slice(&input_bytes[8..16]);
    let header_len = u64::from_le_bytes(len_buf) as usize;
    if 16 + header_len > input_bytes.len() {
        return None;
    }
    serde_json::from_slice::<PackManifest>(&input_bytes[16..16 + header_len]).ok()
}

pub fn prestage_blobs_from_shared_cas(
    store_root: &Path,
    manifest: &PackManifest,
) -> Option<(Vec<(String, String, i64, i64)>, usize)> {
    let shared_blobs = shared_cas_blobs_dir();
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
            match fs::hard_link(&shared_p, &dest) {
                Ok(()) => {
                    total_newly_written += 1;
                    0i64
                }
                Err(ref e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                    fs::metadata(&dest).map(|m| m.ino() as i64).unwrap_or(0)
                }
                Err(_) => {
                    if !shared_p.exists() {
                        return None;
                    }
                    let tmp_dest = store_blobs
                        .join(prefix)
                        .join(format!(".{}.{}.tmp", b.blob_hash, next_tmp_id()));
                    if fs::copy(&shared_p, &tmp_dest).is_err() {
                        return None;
                    }
                    use std::os::unix::fs::PermissionsExt;
                    if let Ok(m) = fs::metadata(&tmp_dest) {
                        let mut p = m.permissions();
                        p.set_mode(0o444);
                        let _ = fs::set_permissions(&tmp_dest, p);
                    }
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

pub fn finish_import_from_prestaged_shared_cas(
    store: &mut TurboStore,
    manifest: &PackManifest,
    staged_blobs: &[(String, String, i64, i64)],
    total_newly_written: usize,
) -> Result<(usize, usize)> {
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

    store.batch_import_pack_metadata(staged_blobs, &manifest.actions)
}

pub(crate) fn try_import_from_shared_cas(
    store: &mut TurboStore,
    manifest: &PackManifest,
) -> Result<Option<(usize, usize)>> {
    let Some((staged_blobs, total_newly_written)) =
        prestage_blobs_from_shared_cas(&store.root, manifest)
    else {
        return Ok(None);
    };
    let res = finish_import_from_prestaged_shared_cas(
        store,
        manifest,
        &staged_blobs,
        total_newly_written,
    )?;
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
    http_request_with_inflight(method, url, content_type, body, || {})
}

pub fn http_request_with_inflight(
    method: &str,
    url: &str,
    content_type: &str,
    body: &[u8],
    on_inflight: impl FnOnce(),
) -> Result<Vec<u8>> {
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

    on_inflight();

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
    let mut publish_items = Vec::new();
    let mut inflight_tx_begun = false;
    let resp_res = http_request_with_inflight("POST", &url, "application/json", &body, || {
        if !items.is_empty() {
            let now = now_unix();
            publish_items.reserve(items.len());
            for item in items {
                if let Ok(receipt) = serde_json::to_vec(&serde_json::json!({
                    "decl": item.decl_name,
                    "prefix_env_hash": item.prefix_env_hash,
                    "stmt_hash": item.stmt_hash,
                    "proof_hash": item.proof_hash,
                    "verified_at": now
                })) {
                    publish_items.push((
                        item.shard_key.clone(),
                        item.decl_name.clone(),
                        receipt,
                        1i64,
                    ));
                }
            }
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
            publish_items.clear();
            let now = now_unix();
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
    } else if inflight_tx_begun {
        store.rollback_inflight_publish();
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
            precomputed_bin_key: String::new(),
            has_main: None,
            local_path: String::new(),
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
            precomputed_bin_key: String::new(),
            has_main: None,
            local_path: String::new(),
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

    #[test]
    fn test_zygote_parallel_cross_file_shard_eval() -> Result<()> {
        let dir = std::env::temp_dir().join(format!(
            "turbo_lean_zygote_par_cross_{}",
            next_tmp_id()
        ));
        let _ = fs::remove_dir_all(&dir);
        let mut store = TurboStore::open(Some(&dir))?;

        let cross_src = "import Init\n-- namespace _TurboCrossFileShard_0\n-- end _TurboCrossFileShard_0\ntheorem _turbo_verify_10000_par1 (a b : Nat) : a + b = b + a := Nat.add_comm a b\n-- namespace _TurboCrossFileShard_1\n-- end _TurboCrossFileShard_1\ntheorem _turbo_verify_20000_par2 (x : Nat) : x + 0 = x := rfl\n";
        let req = CheckShardHttpRequest {
            decl: "__batch__".to_string(),
            shard_key: "shard_key_par_cross_1".to_string(),
            shard_source: cross_src.to_string(),
            interface_hash: String::new(),
            prefix_env_hash: String::new(),
            stmt_hash: String::new(),
            proof_hash: String::new(),
            toolchain: "leanprover/lean4:v4.31.0".to_string(),
            lean_path: String::new(),
            skip_cas_lock: true,
        };
        let res1 = execute_check_shard_payload(&mut store, &req)?;
        assert_eq!(
            res1.get("status").and_then(|v| v.as_str()),
            Some("remote_theorem_verified")
        );
        assert_eq!(res1.get("zygote_used").and_then(|v| v.as_bool()), Some(true));

        // Second cross-file batch should hit warm in-memory Environment in BOTH pooled workers!
        let res2 = execute_check_shard_payload(&mut store, &req)?;
        assert_eq!(
            res2.get("zygote_env_cache_hit").and_then(|v| v.as_bool()),
            Some(true)
        );

        let _ = fs::remove_dir_all(&dir);
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
) -> Result<()> {
    let (acts, blobs, bytes) = export_pack(store, &output, portable_only)?;
    if json {
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
                "exported_actions": acts,
                "exported_blobs": blobs,
                "raw_bytes": bytes,
                "archive": output.display().to_string()
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
) -> Result<()> {
    let (acts, blobs) = import_pack(store, &input)?;
    if json {
        println!(
            "{}",
            serde_json::to_string_pretty(&serde_json::json!({
                "imported_actions": acts,
                "imported_blobs": blobs,
                "archive": input.display().to_string()
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
    mut prefetched_export: Option<std::thread::JoinHandle<Result<PrefetchedExportItem>>>,
    mut prefetched_manifest: Option<std::thread::JoinHandle<Option<DeltaManifest>>>,
) -> Result<()> {
    let t0 = std::time::Instant::now();
    if remote.starts_with("http://") || remote.starts_with("https://") {
        if push && !bidirectional {
            let pre_man = prefetched_manifest
                .take()
                .and_then(|h| h.join().ok().flatten());
            let (pushed_acts, pushed_blobs, pushed_raw, pushed_pack, delta_push_noop) =
                sync_push_http_with_manifest(store, &remote, true, pre_man)?;
            let elapsed_ms = t0.elapsed().as_millis();
            if json {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "status": "synced",
                        "mode": "push_only",
                        "remote": remote,
                        "pulled_actions": 0,
                        "pulled_blobs": 0,
                        "pulled_pack_bytes": 0,
                        "pushed_actions": pushed_acts,
                        "pushed_blobs": pushed_blobs,
                        "pushed_raw_bytes": pushed_raw,
                        "pushed_pack_bytes": pushed_pack,
                        "delta_push_noop": delta_push_noop,
                        "elapsed_ms": elapsed_ms
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] Delta-pushed to {} in {} ms: {} actions ({} blobs, {} bytes)",
                    remote, elapsed_ms, pushed_acts, pushed_blobs, pushed_pack
                );
            }
        } else if !bidirectional {
            let mut pulled = (0usize, 0usize);
            let mut pulled_bytes = 0u64;
            if let Some(handle) = prefetched_export.take() {
                match handle.join() {
                    Ok(Ok((pack_bytes, prestaged_opt))) => {
                        if !pack_bytes.is_empty() {
                            pulled = if let Some((manifest, staged_blobs, newly_written)) =
                                prestaged_opt
                            {
                                finish_import_from_prestaged_shared_cas(
                                    store,
                                    &manifest,
                                    &staged_blobs,
                                    newly_written,
                                )?
                            } else {
                                import_pack_bytes(store, &pack_bytes)?
                            };
                            if pulled.0 > 0 || pulled.1 > 0 {
                                pulled_bytes = pack_bytes.len() as u64;
                            }
                        }
                    }
                    _ => {
                        let (p, pb) = sync_pull_http(store, &remote, true)?;
                        pulled = p;
                        pulled_bytes = pb;
                    }
                }
            } else {
                let (p, pb) = sync_pull_http(store, &remote, true)?;
                pulled = p;
                pulled_bytes = pb;
            }
            let elapsed_ms = t0.elapsed().as_millis();
            if json {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "status": "synced",
                        "mode": "bidirectional",
                        "remote": remote,
                        "pulled_actions": pulled.0,
                        "pulled_blobs": pulled.1,
                        "pulled_pack_bytes": pulled_bytes,
                        "pushed_actions": 0,
                        "pushed_blobs": 0,
                        "pushed_raw_bytes": 0,
                        "pushed_pack_bytes": 0,
                        "delta_push_noop": true,
                        "elapsed_ms": elapsed_ms
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] Synced with {} in {} ms: pulled {} actions ({} blobs), pushed 0 actions (0 blobs)",
                    remote, elapsed_ms, pulled.0, pulled.1
                );
            }
        } else {
            let base = remote.trim_end_matches('/');
            let local_manifest = get_store_manifest(store, true)?;
            let mut pulled = (0usize, 0usize);
            let mut pulled_bytes = 0u64;
            let mut pushed = (0usize, 0usize, 0u64);
            let mut pushed_pack_bytes = 0u64;

            if local_manifest.action_keys.is_empty() && local_manifest.blob_hashes.is_empty() {
                if let Ok(pack_bytes) = http_request(
                    "GET",
                    &format!("{}/export", base),
                    "application/octet-stream",
                    &[],
                ) {
                    if !pack_bytes.is_empty() {
                        pulled = import_pack_bytes(store, &pack_bytes)?;
                        if pulled.0 > 0 || pulled.1 > 0 {
                            pulled_bytes = pack_bytes.len() as u64;
                        }
                    }
                }
            } else {
                let local_action_set: std::collections::HashSet<String> =
                    local_manifest.action_keys.iter().cloned().collect();
                let local_blob_set: std::collections::HashSet<String> =
                    local_manifest.blob_hashes.iter().cloned().collect();

                let remote_manifest: DeltaManifest = match http_request(
                    "GET",
                    &format!("{}/manifest", base),
                    "application/json",
                    &[],
                ) {
                    Ok(bytes) => serde_json::from_slice(&bytes).unwrap_or_default(),
                    Err(_) => DeltaManifest::default(),
                };
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
                    let pack_bytes = http_request(
                        "POST",
                        &format!("{}/export-delta", base),
                        "application/json",
                        &delta_req,
                    )?;
                    if !pack_bytes.is_empty() {
                        pulled_bytes = pack_bytes.len() as u64;
                        pulled = import_pack_bytes(store, &pack_bytes)?;
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
                    let (p_acts, p_blobs, p_raw, push_bytes) = export_pack_filtered_bytes(
                        store,
                        true,
                        &remote_action_set,
                        &remote_blob_set,
                    )?;
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

            let elapsed_ms = t0.elapsed().as_millis();
            if json {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&serde_json::json!({
                        "status": "synced",
                        "mode": "bidirectional",
                        "remote": remote,
                        "pulled_actions": pulled.0,
                        "pulled_blobs": pulled.1,
                        "pulled_pack_bytes": pulled_bytes,
                        "pushed_actions": pushed.0,
                        "pushed_blobs": pushed.1,
                        "pushed_raw_bytes": pushed.2,
                        "pushed_pack_bytes": pushed_pack_bytes,
                        "delta_push_noop": pushed.0 == 0 && pushed.1 == 0,
                        "elapsed_ms": elapsed_ms
                    }))?
                );
            } else {
                println!(
                    "[turbo-lean] Synced with {} in {} ms: pulled {} actions ({} blobs), pushed {} actions ({} blobs)",
                    remote, elapsed_ms, pulled.0, pulled.1, pushed.0, pushed.1
                );
            }
        }
    } else {
        anyhow::bail!(
            "Unsupported remote scheme `{}` (use http://host:port or export/import)",
            remote
        );
    }
    Ok(())
}
