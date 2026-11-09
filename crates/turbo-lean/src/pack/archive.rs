use crate::db::{ActionRecord, BlobEntry, TurboStore};
use anyhow::{Context, Result};
use std::collections::HashSet;
use std::fs;
use std::io::Read;
use std::path::Path;

use super::deferred::{
    encode_last_full_export_with_epoch, format_last_import_stamp_with_epoch,
    list_pending_deferred_pack_files, load_cached_portable_manifest_with_epoch,
    read_last_full_export_with_epoch, read_last_import_stamp_with_epoch,
    save_cached_portable_manifest_from_pack, stage_deferred_pack_record_locked,
};
use super::manifest::{
    blob_hash_prefix, is_portable_artifact, pack_manifest_has_verified_ed25519,
    read_pack_header_from_file, read_u64_le_at, resolve_pack_import_trust_domain,
    sign_pack_manifest_ed25519, PackManifest, PackedBlob,
};

#[cfg(test)]
pub fn export_pack(
    store: &TurboStore,
    output_path: &Path,
    only_portable: bool,
) -> Result<(usize, usize, u64)> {
    export_pack_with_signing_key(store, output_path, only_portable, None)
}

#[cfg(test)]
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
        let probe_meta = fs::metadata(store_root).or_else(|_| {
            let mut cur = store_root.parent();
            while let Some(p) = cur {
                if !p.as_os_str().is_empty() {
                    if let Ok(m) = fs::metadata(p) {
                        return Ok(m);
                    }
                }
                cur = p.parent();
            }
            Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "no existing store_root ancestor",
            ))
        });
        if let Ok(store_meta) = probe_meta {
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

pub(super) fn ensure_blob_in_shared_cas(
    store: &TurboStore,
    bh: &str,
    expected_len: u64,
    shared_blobs: &Path,
    seen_prefix: &mut [bool; 256],
) -> bool {
    let prefix = if bh.len() >= 2 { &bh[0..2] } else { "00" };
    let p_idx = u8::from_str_radix(prefix, 16).unwrap_or(0) as usize;
    let shared_dir = shared_blobs.join(prefix);
    let stop_at = shared_blobs.parent().unwrap_or(shared_blobs);
    let created = if !seen_prefix[p_idx] {
        let Ok(dirs) = crate::db::ensure_dir_tracking(&shared_dir, stop_at) else {
            return false;
        };
        seen_prefix[p_idx] = true;
        dirs
    } else {
        Vec::new()
    };
    let shared_dest = shared_dir.join(bh);
    if let Ok((mut f, meta)) = crate::db::open_regular_nofollow(&shared_dest) {
        #[cfg(unix)]
        let owned = crate::db::is_exclusively_created_immutable_cas_inode(&meta, bh);
        #[cfg(not(unix))]
        let owned = true;
        if owned {
            let mut buf = Vec::with_capacity(meta.len().min(64 * 1024 * 1024) as usize);
            if f.read_to_end(&mut buf).is_ok()
                && buf.len() as u64 == expected_len
                && blake3::hash(&buf).to_hex().as_str() == bh
            {
                let ok = crate::db::durability_barrier(&f).is_ok()
                    && crate::db::sync_dir(&shared_dir).is_ok();
                for dir in &created {
                    if crate::db::sync_dir(dir).is_err() {
                        return false;
                    }
                }
                if ok {
                    return true;
                }
            }
        }
    }
    let Ok(src) = store.ensure_blob_uncompressed(bh) else {
        for dir in &created {
            let _ = crate::db::sync_dir(dir);
        }
        return false;
    };
    let ok =
        crate::db::publish_verified_durable_blob(&src, &shared_dest, bh, expected_len, &created)
            .is_ok();
    if !ok {
        for dir in &created {
            let _ = crate::db::sync_dir(dir);
        }
    }
    ok
}

pub(super) fn verify_cached_pack_stream_integrity_at_root(
    store_root: &Path,
    stream: &[u8],
    expected_acts: usize,
    expected_blobs: usize,
    expected_raw_bytes: u64,
) -> bool {
    if stream.len() < 16 {
        return false;
    }
    let magic = &stream[..8];
    let is_v2 = magic == b"TLPK\x00\x00\x00\x02";
    let is_v3 = magic == b"TLPK\x00\x00\x00\x03";
    if !is_v2 && !is_v3 {
        return false;
    }
    let hlen = read_u64_le_at(stream, 8) as usize;
    if 16 + hlen > stream.len() {
        return false;
    }
    let Ok(m) = serde_json::from_slice::<PackManifest>(&stream[16..16 + hlen]) else {
        return false;
    };
    if m.actions.len() != expected_acts || m.blobs.len() != expected_blobs {
        return false;
    }
    let store_blobs = store_root.join("blobs");
    let mut sum_raw = 0u64;
    if is_v2 {
        let mut cursor = 16 + hlen;
        for b in &m.blobs {
            let prefix = blob_hash_prefix(&b.blob_hash);
            let sz = b.size_bytes as usize;
            let Some(end) = cursor.checked_add(sz) else {
                return false;
            };
            if end > stream.len() {
                return false;
            }
            if blake3::hash(&stream[cursor..end]).to_hex().as_str() != b.blob_hash {
                return false;
            }
            if !matches!(
                crate::db::probe_blob_digest(
                    &store_blobs.join(prefix).join(&b.blob_hash),
                    &b.blob_hash,
                    b.size_bytes
                ),
                crate::db::BlobDisk::Intact
            ) {
                return false;
            }
            sum_raw = sum_raw.saturating_add(b.size_bytes);
            cursor = end;
        }
        cursor == stream.len() && sum_raw == expected_raw_bytes
    } else {
        if 16 + hlen != stream.len() {
            return false;
        }
        let shared_blobs = shared_cas_blobs_dir_for_store(store_root);
        let shared_shm = shared_cas_blobs_dir();
        for b in &m.blobs {
            if b.blob_hash.len() < 2 {
                return false;
            }
            let prefix = &b.blob_hash[..2];
            if !matches!(
                crate::db::probe_blob_digest(
                    &store_blobs.join(prefix).join(&b.blob_hash),
                    &b.blob_hash,
                    b.size_bytes
                ),
                crate::db::BlobDisk::Intact
            ) {
                return false;
            }
            let sp1 = shared_blobs.join(prefix).join(&b.blob_hash);
            let sp2 = shared_shm.join(prefix).join(&b.blob_hash);
            let in_shared = matches!(
                crate::db::probe_blob_digest(&sp1, &b.blob_hash, b.size_bytes),
                crate::db::BlobDisk::Intact
            ) || matches!(
                crate::db::probe_blob_digest(&sp2, &b.blob_hash, b.size_bytes),
                crate::db::BlobDisk::Intact
            );
            if !in_shared {
                return false;
            }
            sum_raw = sum_raw.saturating_add(b.size_bytes);
        }
        sum_raw == expected_raw_bytes
    }
}

fn verify_cached_pack_stream_integrity(
    store: &TurboStore,
    stream: &[u8],
    expected_acts: usize,
    expected_blobs: usize,
    expected_raw_bytes: u64,
    expected_replayed: usize,
) -> bool {
    if stream.len() < 16 {
        return false;
    }
    let hlen = read_u64_le_at(stream, 8) as usize;
    if 16 + hlen > stream.len() {
        return false;
    }
    let Ok(m) = serde_json::from_slice::<PackManifest>(&stream[16..16 + hlen]) else {
        return false;
    };
    if m.replayed_oleans.len() != expected_replayed {
        return false;
    }
    verify_cached_pack_stream_integrity_at_root(
        &store.root,
        stream,
        expected_acts,
        expected_blobs,
        expected_raw_bytes,
    )
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

#[derive(Debug, Clone)]
pub struct ExportInclusionFilter {
    pub allowed_actions: Option<HashSet<String>>,
    pub allowed_replay_modules: Option<HashSet<String>>,
    pub allowed_replay_artifact_digests: Option<HashSet<String>>,
}

pub fn export_pack_filtered_with_mode_and_signing_key(
    store: &TurboStore,
    only_portable: bool,
    exclude_actions: &HashSet<String>,
    exclude_blobs: &HashSet<String>,
    header_only_shared_cas: bool,
    signing_key: Option<&str>,
) -> Result<(usize, usize, u64, Vec<u8>)> {
    export_pack_with_filter_mode_and_signing_key(
        store,
        only_portable,
        exclude_actions,
        exclude_blobs,
        None,
        header_only_shared_cas,
        signing_key,
    )
}

pub fn export_pack_with_filter_mode_and_signing_key(
    store: &TurboStore,
    only_portable: bool,
    exclude_actions: &HashSet<String>,
    exclude_blobs: &HashSet<String>,
    inclusion_filter: Option<&ExportInclusionFilter>,
    header_only_shared_cas: bool,
    signing_key: Option<&str>,
) -> Result<(usize, usize, u64, Vec<u8>)> {
    let _pub_guard = crate::db::acquire_cas_publication_guard(&store.root)?;
    let signing_key_env = signing_key
        .map(|s| s.to_string())
        .or_else(|| std::env::var("TURBO_LEAN_PACK_SIGNING_KEY").ok())
        .filter(|s| !s.trim().is_empty());
    let full_export_cache_path = if signing_key_env.is_none()
        && exclude_actions.is_empty()
        && exclude_blobs.is_empty()
        && inclusion_filter.is_none()
    {
        let state_sig: Option<(i64, i64, i64, i64, i64)> = store
            .conn
            .query_row(
                "SELECT
                   (SELECT COALESCE(val, 0) FROM meta_counters WHERE name = 'fencing_seq'),
                   (SELECT COUNT(*) FROM actions WHERE status = 'completed' AND trust_domain = 'trusted'),
                   (SELECT COUNT(*) FROM blobs WHERE trust_domain = 'trusted'),
                   (SELECT COUNT(*) FROM kernel_replayed_oleans_auth),
                   (SELECT COALESCE(MAX(verified_at), 0) FROM kernel_replayed_oleans_auth)",
                [],
                |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?, r.get(3)?, r.get(4)?)),
            )
            .ok();
        if let Some((fseq, act_cnt, blob_cnt, replay_cnt, replay_max_ts)) = state_sig {
            if act_cnt > 0 {
                let mut h = blake3::Hasher::new();
                h.update(store.root.to_string_lossy().as_bytes());
                let root_tag = &h.finalize().to_hex()[..16];
                let cache_file = store.fast_staging_dir().join(format!(
                    "pack_exp_v2_{}_{}_{}_{}_{}_{}_{}_{}.bin",
                    root_tag,
                    fseq,
                    act_cnt,
                    blob_cnt,
                    replay_cnt,
                    replay_max_ts,
                    if only_portable { 1 } else { 0 },
                    if header_only_shared_cas { 1 } else { 0 }
                ));
                if !header_only_shared_cas || shared_cas_blobs_dir().exists() {
                    if let Some((mut cached_bytes, _)) =
                        crate::db::read_regular_nofollow(&cache_file)
                    {
                        if cached_bytes.len() >= 24 {
                            let n_acts = read_u64_le_at(&cached_bytes, 0) as usize;
                            let n_blobs = read_u64_le_at(&cached_bytes, 8) as usize;
                            let raw_bytes = read_u64_le_at(&cached_bytes, 16);
                            let stream = cached_bytes.split_off(24);
                            if verify_cached_pack_stream_integrity(
                                store,
                                &stream,
                                n_acts,
                                n_blobs,
                                raw_bytes,
                                replay_cnt as usize,
                            ) {
                                if only_portable {
                                    let locks_dir = store.root.join("locks");
                                    if let Ok(created) =
                                        crate::db::ensure_dir_tracking(&locks_dir, &store.root)
                                    {
                                        let last_file = locks_dir.join(format!(
                                            "last_full_export_{}.bin",
                                            if header_only_shared_cas { 1 } else { 0 }
                                        ));
                                        if read_last_full_export_with_epoch(
                                            &store.root,
                                            header_only_shared_cas,
                                            crate::TURBO_LEAN_BUILD_EPOCH,
                                        )
                                        .is_none()
                                        {
                                            let full_cache = encode_last_full_export_with_epoch(
                                                n_acts,
                                                n_blobs,
                                                raw_bytes,
                                                &stream,
                                                crate::TURBO_LEAN_BUILD_EPOCH,
                                            );
                                            let _ = crate::db::write_bytes_durable(
                                                &last_file,
                                                &full_cache,
                                                &created,
                                            );
                                        } else {
                                            for dir in &created {
                                                let _ = crate::db::sync_dir(dir);
                                            }
                                        }
                                    }
                                }
                                if load_cached_portable_manifest_with_epoch(
                                    &store.root,
                                    crate::TURBO_LEAN_BUILD_EPOCH,
                                )
                                .is_none()
                                    && stream.len() >= 16
                                {
                                    let hlen = read_u64_le_at(&stream, 8) as usize;
                                    if 16 + hlen <= stream.len() {
                                        if let Ok(m) = serde_json::from_slice::<PackManifest>(
                                            &stream[16..16 + hlen],
                                        ) {
                                            save_cached_portable_manifest_from_pack(
                                                &store.root,
                                                &m,
                                            );
                                        }
                                    }
                                }
                                return Ok((n_acts, n_blobs, raw_bytes, stream));
                            }
                            let _ = fs::remove_file(&cache_file);
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
                    if let Some((v3_cached, _)) = crate::db::read_regular_nofollow(&v3_file) {
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
                                        let store_p = store.blob_path(&b.blob_hash);
                                        if !matches!(
                                            crate::db::probe_blob_digest(
                                                &store_p,
                                                &b.blob_hash,
                                                b.size_bytes
                                            ),
                                            crate::db::BlobDisk::Intact
                                        ) {
                                            all_ok = false;
                                            break;
                                        }
                                        let sp =
                                            shared_shm.join(&b.blob_hash[..2]).join(&b.blob_hash);
                                        if let Some(raw) = crate::db::read_cas_blob_verified(
                                            &sp,
                                            &b.blob_hash,
                                            Some(b.size_bytes),
                                        )
                                        .or_else(|| {
                                            crate::db::read_cas_blob_verified(
                                                &store_p,
                                                &b.blob_hash,
                                                Some(b.size_bytes),
                                            )
                                        }) {
                                            payload.extend_from_slice(&raw);
                                            continue;
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
                                        let _ = crate::shm_cache::atomic_write_shm(cf, &cache_buf);
                                        if only_portable {
                                            let locks_dir = store.root.join("locks");
                                            if let Ok(created) = crate::db::ensure_dir_tracking(
                                                &locks_dir,
                                                &store.root,
                                            ) {
                                                let last_0 =
                                                    locks_dir.join("last_full_export_0.bin");
                                                let last_0_buf = encode_last_full_export_with_epoch(
                                                    n_acts,
                                                    n_blobs,
                                                    raw_bytes,
                                                    &stream,
                                                    crate::TURBO_LEAN_BUILD_EPOCH,
                                                );
                                                let _ = crate::db::write_bytes_durable(
                                                    &last_0,
                                                    &last_0_buf,
                                                    &created,
                                                );
                                                let last_1 =
                                                    locks_dir.join("last_full_export_1.bin");
                                                if read_last_full_export_with_epoch(
                                                    &store.root,
                                                    true,
                                                    crate::TURBO_LEAN_BUILD_EPOCH,
                                                )
                                                .is_none()
                                                {
                                                    let last_1_buf =
                                                        encode_last_full_export_with_epoch(
                                                            n_acts,
                                                            n_blobs,
                                                            raw_bytes,
                                                            &v3_cached[24..],
                                                            crate::TURBO_LEAN_BUILD_EPOCH,
                                                        );
                                                    let _ = crate::db::write_bytes_durable(
                                                        &last_1,
                                                        &last_1_buf,
                                                        &created,
                                                    );
                                                }
                                            }
                                        }
                                        if load_cached_portable_manifest_with_epoch(
                                            &store.root,
                                            crate::TURBO_LEAN_BUILD_EPOCH,
                                        )
                                        .is_none()
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

    #[allow(clippy::type_complexity)]
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
        if let Some(inc) = inclusion_filter {
            if let Some(ref allowed_acts) = inc.allowed_actions {
                if !allowed_acts.contains(&ak) {
                    continue;
                }
            }
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
            if !matches!(
                crate::db::probe_blob_digest(&store.blob_path(&bh), &bh, db_sz),
                crate::db::BlobDisk::Intact
            ) {
                anyhow::bail!(
                    "Refusing to export CAS blob {}: missing, symlinked, or digest-corrupted on disk",
                    bh
                );
            }
            let ok1 = ensure_blob_in_shared_cas(
                store,
                &bh,
                db_sz,
                &shared_blobs,
                &mut seen_shared_prefix,
            );
            let ok2 = if shared_blobs != shared_blobs_shm {
                ensure_blob_in_shared_cas(
                    store,
                    &bh,
                    db_sz,
                    &shared_blobs_shm,
                    &mut seen_shm_prefix,
                )
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
            let p = store.ensure_blob_uncompressed(&bh)?;
            let Some(raw) = crate::db::read_cas_blob_verified(&p, &bh, Some(db_sz)) else {
                anyhow::bail!(
                    "Refusing to export CAS blob {}: missing, symlinked, or digest-corrupted on disk",
                    bh
                );
            };
            let sz = raw.len() as u64;
            payload_buf.extend_from_slice(&raw);
            total_raw_bytes += sz;
            let _ =
                ensure_blob_in_shared_cas(store, &bh, sz, &shared_blobs, &mut seen_shared_prefix);
            if shared_blobs != shared_blobs_shm {
                let _ = ensure_blob_in_shared_cas(
                    store,
                    &bh,
                    sz,
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
        }
    }

    if header_only_shared_cas && !all_in_shared {
        drop(_pub_guard);
        return export_pack_with_filter_mode_and_signing_key(
            store,
            only_portable,
            exclude_actions,
            exclude_blobs,
            inclusion_filter,
            false,
            signing_key,
        );
    }

    let mut replayed_oleans = store.export_verified_kernel_replayed_oleans(&[])?;
    if let Some(inc) = inclusion_filter {
        replayed_oleans.retain(|r| {
            let mod_ok = inc
                .allowed_replay_modules
                .as_ref()
                .is_some_and(|mods| !r.module_name.is_empty() && mods.contains(&r.module_name));
            let dig_ok = inc
                .allowed_replay_artifact_digests
                .as_ref()
                .is_some_and(|digs| digs.contains(&r.artifact_digest));
            match (
                &inc.allowed_replay_modules,
                &inc.allowed_replay_artifact_digests,
            ) {
                (None, None) => true,
                _ => mod_ok || dig_ok,
            }
        });
    }

    let mut manifest = PackManifest {
        format_version: 2,
        host_arch: std::env::consts::ARCH.to_string(),
        created_at: crate::db::now_unix(),
        actions,
        blobs,
        ed25519_pubkey: None,
        ed25519_signature: None,
        replayed_oleans,
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
    if exclude_actions.is_empty() && exclude_blobs.is_empty() && inclusion_filter.is_none() {
        save_cached_portable_manifest_from_pack(&store.root, &manifest);
    }
    if let Some(cache_file) = full_export_cache_path {
        if pack_stream.len() <= 64 * 1024 * 1024 {
            let mut cache_buf = Vec::with_capacity(24 + pack_stream.len());
            cache_buf.extend_from_slice(&(n_acts as u64).to_le_bytes());
            cache_buf.extend_from_slice(&(n_blobs as u64).to_le_bytes());
            cache_buf.extend_from_slice(&total_raw_bytes.to_le_bytes());
            cache_buf.extend_from_slice(&pack_stream);
            let _ = crate::shm_cache::atomic_write_shm(&cache_file, &cache_buf);
            if only_portable {
                let locks_dir = store.root.join("locks");
                if let Ok(created) = crate::db::ensure_dir_tracking(&locks_dir, &store.root) {
                    let last_file = locks_dir.join(format!(
                        "last_full_export_{}.bin",
                        if header_only_shared_cas { 1 } else { 0 }
                    ));
                    let last_buf = encode_last_full_export_with_epoch(
                        n_acts,
                        n_blobs,
                        total_raw_bytes,
                        &pack_stream,
                        crate::TURBO_LEAN_BUILD_EPOCH,
                    );
                    let _ = crate::db::write_bytes_durable(&last_file, &last_buf, &created);
                }
            }
            if !header_only_shared_cas {
                if let Some(s) = cache_file.to_str() {
                    if let Some(v3_str) = s.strip_suffix("_0.bin") {
                        let v3_file = std::path::PathBuf::from(format!("{}_1.bin", v3_str));
                        let mut v3_stream = Vec::with_capacity(16 + header_json.len());
                        v3_stream.extend_from_slice(b"TLPK\x00\x00\x00\x03");
                        v3_stream.extend_from_slice(&(header_json.len() as u64).to_le_bytes());
                        v3_stream.extend_from_slice(&header_json);
                        let mut v3_buf = Vec::with_capacity(24 + v3_stream.len());
                        v3_buf.extend_from_slice(&(n_acts as u64).to_le_bytes());
                        v3_buf.extend_from_slice(&(n_blobs as u64).to_le_bytes());
                        v3_buf.extend_from_slice(&total_raw_bytes.to_le_bytes());
                        v3_buf.extend_from_slice(&v3_stream);
                        let _ = crate::shm_cache::atomic_write_shm(&v3_file, &v3_buf);
                        if only_portable {
                            let locks_dir = store.root.join("locks");
                            if let Ok(created) =
                                crate::db::ensure_dir_tracking(&locks_dir, &store.root)
                            {
                                let last_v3 = locks_dir.join("last_full_export_1.bin");
                                let last_v3_buf = encode_last_full_export_with_epoch(
                                    n_acts,
                                    n_blobs,
                                    total_raw_bytes,
                                    &v3_stream,
                                    crate::TURBO_LEAN_BUILD_EPOCH,
                                );
                                let _ = crate::db::write_bytes_durable(
                                    &last_v3,
                                    &last_v3_buf,
                                    &created,
                                );
                            }
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

#[cfg(test)]
pub fn export_pack_filtered_with_signing_key(
    store: &TurboStore,
    output_path: &Path,
    only_portable: bool,
    exclude_actions: &HashSet<String>,
    exclude_blobs: &HashSet<String>,
    signing_key: Option<&str>,
) -> Result<(usize, usize, u64)> {
    export_pack_with_filter_and_signing_key(
        store,
        output_path,
        only_portable,
        exclude_actions,
        exclude_blobs,
        None,
        signing_key,
    )
}

pub fn export_pack_with_filter_and_signing_key(
    store: &TurboStore,
    output_path: &Path,
    only_portable: bool,
    exclude_actions: &HashSet<String>,
    exclude_blobs: &HashSet<String>,
    inclusion_filter: Option<&ExportInclusionFilter>,
    signing_key: Option<&str>,
) -> Result<(usize, usize, u64)> {
    let _pub_guard = crate::db::acquire_cas_publication_guard(&store.root)?;
    let (n_acts, n_blobs, total_raw_bytes, pack_stream) =
        export_pack_with_filter_mode_and_signing_key(
            store,
            only_portable,
            exclude_actions,
            exclude_blobs,
            inclusion_filter,
            false,
            signing_key,
        )?;

    if pack_stream.len() <= 64 * 1024 * 1024 && std::env::var("TURBO_LEAN_FORCE_ZSTD").is_err() {
        fs::write(output_path, &pack_stream)?;
        return Ok((n_acts, n_blobs, total_raw_bytes));
    }

    let tmp_raw = crate::shm_cache::StagedTempFile::write(
        store
            .fast_staging_dir()
            .join(format!("export_{}.tlpack.raw", next_tmp_id())),
        &pack_stream,
    )?;

    let zstd_status = crate::trusted_tools::system_command("zstd").and_then(|mut command| {
        command
            .args([
                "-q",
                "-f",
                "-1",
                tmp_raw.to_str().unwrap_or(""),
                "-o",
                output_path.to_str().unwrap_or(""),
            ])
            .status()
            .map_err(Into::into)
    });

    drop(tmp_raw);
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

#[allow(clippy::type_complexity)]
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
    let mut created_parents: Vec<std::path::PathBuf> = Vec::new();
    let root_preexisted = store_root.exists();
    if fs::create_dir_all(store_root).is_err() {
        return None;
    }
    if !root_preexisted {
        if let Some(parent) = store_root.parent().filter(|p| !p.as_os_str().is_empty()) {
            created_parents.push(parent.to_path_buf());
        }
    }
    let shared_blobs = shared_cas_blobs_dir_for_store(store_root);
    let shared_blobs_shm = shared_cas_blobs_dir();
    let store_blobs = store_root.join("blobs");

    let mut seen_prefix = [false; 256];
    for b in &manifest.blobs {
        let prefix = blob_hash_prefix(&b.blob_hash);
        let p_idx = u8::from_str_radix(prefix, 16).unwrap_or(0) as usize;
        if !seen_prefix[p_idx] {
            seen_prefix[p_idx] = true;
            match crate::db::ensure_dir_tracking(&store_blobs.join(prefix), store_root) {
                Ok(parents) => created_parents.extend(parents),
                Err(_) => {
                    created_parents.sort_by_key(|p| std::cmp::Reverse(p.components().count()));
                    created_parents.dedup();
                    for dir in &created_parents {
                        let _ = crate::db::sync_dir(dir);
                    }
                    return None;
                }
            }
        }
    }

    let mut staged_blobs = Vec::with_capacity(manifest.blobs.len());
    let mut total_newly_written = 0usize;
    for b in &manifest.blobs {
        let prefix = blob_hash_prefix(&b.blob_hash);
        let dest = store_blobs.join(prefix).join(&b.blob_hash);
        #[cfg(unix)]
        let inode = {
            use std::os::unix::fs::MetadataExt;
            let sync_created_parents = |dirs: &mut Vec<std::path::PathBuf>| {
                dirs.sort_by_key(|p| std::cmp::Reverse(p.components().count()));
                dirs.dedup();
                for dir in dirs.iter() {
                    let _ = crate::db::sync_dir(dir);
                }
            };
            let mut existing_local_verified: Option<Vec<u8>> = None;
            if let Ok((mut f, m)) = crate::db::open_regular_nofollow(&dest) {
                let mut buf = Vec::with_capacity(m.len().min(64 * 1024 * 1024) as usize);
                if f.read_to_end(&mut buf).is_ok() {
                    if buf.len() as u64 == b.size_bytes
                        && blake3::hash(&buf).to_hex().as_str() == b.blob_hash
                    {
                        if crate::db::is_exclusively_created_immutable_cas_inode(&m, &b.blob_hash) {
                            let durable = crate::db::durability_barrier(&f).is_ok()
                                && crate::db::sync_dir(dest.parent().unwrap_or(&store_blobs))
                                    .is_ok();
                            if !durable {
                                sync_created_parents(&mut created_parents);
                                return None;
                            }
                            staged_blobs.push((
                                b.blob_hash.clone(),
                                b.kind.clone(),
                                b.size_bytes as i64,
                                m.ino() as i64,
                            ));
                            continue;
                        }
                        existing_local_verified = Some(buf);
                    } else if buf.len() >= 12 && &buf[..4] == b"TLZ1" {
                        let hdr_len = u64::from_le_bytes(buf[4..12].try_into().unwrap());
                        if hdr_len == b.size_bytes {
                            if let Some(raw) = crate::db::decompress_tlz1(&buf) {
                                if raw.len() as u64 == b.size_bytes
                                    && blake3::hash(&raw).to_hex().as_str() == b.blob_hash
                                {
                                    existing_local_verified = Some(raw);
                                }
                            }
                        }
                    }
                }
            }
            if let Some(local_raw) = existing_local_verified {
                let Ok(re_sealed_ino) =
                    crate::db::write_blob_atomic(store_root, &dest, &b.blob_hash, &local_raw, true)
                else {
                    sync_created_parents(&mut created_parents);
                    return None;
                };
                total_newly_written += 1;
                staged_blobs.push((
                    b.blob_hash.clone(),
                    b.kind.clone(),
                    b.size_bytes as i64,
                    re_sealed_ino,
                ));
                continue;
            }
            let shared_p = shared_blobs.join(prefix).join(&b.blob_hash);
            let shared_p_alt = shared_blobs_shm.join(prefix).join(&b.blob_hash);
            let mut from_alt = false;
            let published_ino = match crate::db::publish_verified_durable_blob(
                &shared_p,
                &dest,
                &b.blob_hash,
                b.size_bytes,
                &[],
            ) {
                Ok(ino) => Ok(ino),
                Err(_) if shared_p_alt != shared_p => {
                    from_alt = true;
                    crate::db::publish_verified_durable_blob(
                        &shared_p_alt,
                        &dest,
                        &b.blob_hash,
                        b.size_bytes,
                        &[],
                    )
                }
                Err(e) => Err(e),
            };
            let Ok(ino) = published_ino else {
                sync_created_parents(&mut created_parents);
                return None;
            };
            if from_alt {
                let shared_parent = shared_p.parent().unwrap_or(&shared_blobs);
                let shared_stop = shared_blobs.parent().unwrap_or(&shared_blobs);
                if let Ok(shared_created) =
                    crate::db::ensure_dir_tracking(shared_parent, shared_stop)
                {
                    let _ = crate::db::publish_verified_durable_blob(
                        &dest,
                        &shared_p,
                        &b.blob_hash,
                        b.size_bytes,
                        &shared_created,
                    );
                }
            }
            total_newly_written += 1;
            ino
        };
        #[cfg(not(unix))]
        let inode = {
            let shared_p = shared_blobs.join(prefix).join(&b.blob_hash);
            if !dest.exists() {
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
    created_parents.sort_by_key(|p| std::cmp::Reverse(p.components().count()));
    created_parents.dedup();
    for dir in created_parents {
        if crate::db::sync_dir(&dir).is_err() {
            return None;
        }
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
    if td == "trusted" && !manifest.replayed_oleans.is_empty() {
        return None;
    }
    let expected_payload: u64 = manifest.blobs.iter().map(|b| b.size_bytes).sum();
    let size_ok = &magic == b"TLPK\x00\x00\x00\x03"
        || 16 + (header_len as u64) + expected_payload == file_len;
    if !size_ok {
        return None;
    }
    let _pub_guard = crate::db::acquire_cas_publication_guard(store_root).ok()?;
    let (staged_blobs, _) = prestage_blobs_from_shared_cas(store_root, &manifest)?;
    let mut v3_bytes = Vec::with_capacity(16 + header_len);
    v3_bytes.extend_from_slice(b"TLPK\x00\x00\x00\x03");
    v3_bytes.extend_from_slice(&(header_len as u64).to_le_bytes());
    v3_bytes.extend_from_slice(&header_buf);
    if !stage_deferred_pack_record_locked(store_root, td, &v3_bytes) {
        return None;
    }
    drop(_pub_guard);
    if td == "trusted" {
        save_cached_portable_manifest_from_pack(store_root, &manifest);
    }
    Some((manifest.actions.len(), staged_blobs.len()))
}

pub fn try_stateless_warm_import_with_domain(
    store_root: &Path,
    input_path: &Path,
    requested_domain: Option<&str>,
    trusted_pubkey: Option<&str>,
    allow_unattested_trusted: bool,
) -> Option<(usize, usize)> {
    try_stateless_warm_import_with_domain_and_epoch(
        store_root,
        input_path,
        requested_domain,
        trusted_pubkey,
        allow_unattested_trusted,
        crate::TURBO_LEAN_BUILD_EPOCH,
    )
}

pub(crate) fn try_stateless_warm_import_with_domain_and_epoch(
    store_root: &Path,
    input_path: &Path,
    requested_domain: Option<&str>,
    trusted_pubkey: Option<&str>,
    allow_unattested_trusted: bool,
    expected_epoch: &str,
) -> Option<(usize, usize)> {
    let locks_dir = store_root.join("locks");
    let db_warm = fs::metadata(store_root.join("state.db"))
        .map(|m| m.len() >= 4096)
        .unwrap_or(false);
    if !db_warm {
        if fs::remove_file(locks_dir.join("last_import_stamp")).is_ok() {
            let _ = crate::db::sync_dir(&locks_dir);
        }
        return None;
    }
    if list_pending_deferred_pack_files(&locks_dir)
        .map(|v| !v.is_empty())
        .unwrap_or(false)
    {
        return None;
    }
    let (saved_stamp, n_acts, n_blobs, saved_td) =
        read_last_import_stamp_with_epoch(store_root, expected_epoch)?;
    let (_, _, header_buf) = read_pack_header_from_file(input_path)?;
    let manifest = serde_json::from_slice::<PackManifest>(&header_buf).ok()?;
    let td = resolve_pack_import_trust_domain(
        &manifest,
        requested_domain,
        trusted_pubkey,
        allow_unattested_trusted,
    )
    .ok()?;
    if td == "trusted" && !manifest.replayed_oleans.is_empty() {
        return None;
    }
    let header_hash = blake3::hash(&header_buf).to_hex().to_string();
    if header_hash == saved_stamp
        && (saved_td == td || (saved_td == "trusted" && td == "untrusted"))
    {
        Some((n_acts, n_blobs))
    } else {
        None
    }
}

pub(crate) fn finish_import_from_prestaged_shared_cas_inner(
    store: &mut TurboStore,
    manifest: &PackManifest,
    staged_blobs: &[(String, String, i64, i64)],
    total_newly_written: usize,
    trust_domain: &str,
    trusted_pubkey: Option<&str>,
    already_holds_gc_lock: bool,
) -> Result<(usize, usize)> {
    let _pub_guard = if already_holds_gc_lock {
        None
    } else {
        Some(crate::db::acquire_cas_publication_guard(&store.root)?)
    };
    let td = if trust_domain == "trusted" {
        "trusted"
    } else {
        "untrusted"
    };
    let header_json = serde_json::to_vec(manifest).unwrap_or_default();
    let header_hash = blake3::hash(&header_json).to_hex().to_string();
    let stamp_val = format_last_import_stamp_with_epoch(
        &header_hash,
        manifest.actions.len(),
        staged_blobs.len(),
        td,
        crate::TURBO_LEAN_BUILD_EPOCH,
    );
    let store_root = store.root.clone();
    let locks_dir = store_root.join("locks");
    let stamp_file = locks_dir.join("last_import_stamp");
    let write_stamp = || -> Result<()> {
        let created = crate::db::ensure_dir_tracking(&locks_dir, &store_root)?;
        crate::db::write_bytes_durable(&stamp_file, stamp_val.as_bytes(), &created)?;
        Ok(())
    };
    let mut effective_blobs: std::borrow::Cow<'_, [(String, String, i64, i64)]> =
        std::borrow::Cow::Borrowed(staged_blobs);
    let mut effective_newly_written = total_newly_written;
    let missing_on_disk = staged_blobs.iter().any(|(bh, _, sz, _)| {
        !matches!(
            crate::db::probe_blob_digest(&store.blob_path(bh), bh, (*sz).max(0) as u64),
            crate::db::BlobDisk::Intact
        )
    }) || manifest.actions.iter().any(|a| {
        a.outputs.iter().any(|o| {
            !matches!(
                crate::db::probe_blob_digest(
                    &store.blob_path(&o.blob_hash),
                    &o.blob_hash,
                    o.size_bytes
                ),
                crate::db::BlobDisk::Intact
            )
        })
    });
    if missing_on_disk {
        let Some((restaged, restaged_new)) = prestage_blobs_from_shared_cas(&store_root, manifest)
        else {
            anyhow::bail!("Refusing to publish prestaged pack import: one or more CAS blobs missing or torn on disk");
        };
        for a in &manifest.actions {
            for o in &a.outputs {
                if !matches!(
                    crate::db::probe_blob_digest(
                        &store.blob_path(&o.blob_hash),
                        &o.blob_hash,
                        o.size_bytes
                    ),
                    crate::db::BlobDisk::Intact
                ) {
                    anyhow::bail!(
                        "Refusing to publish prestaged pack import: output blob {} missing or torn on disk",
                        o.blob_hash
                    );
                }
            }
        }
        effective_blobs = std::borrow::Cow::Owned(restaged);
        effective_newly_written = effective_newly_written.max(restaged_new.max(1));
    }

    let has_pending_deferred = list_pending_deferred_pack_files(&locks_dir)
        .map(|v| !v.is_empty())
        .unwrap_or(false);
    let installed_replayed = if td == "trusted"
        && !manifest.replayed_oleans.is_empty()
        && pack_manifest_has_verified_ed25519(manifest, trusted_pubkey)
    {
        let allowed_githashes = crate::module_builder::discover_host_installed_lean_githashes();
        store.import_attested_replayed_oleans(
            &manifest.replayed_oleans,
            td,
            &allowed_githashes,
            &[],
        )?
    } else {
        0
    };
    if effective_newly_written == 0 && !has_pending_deferred && !manifest.actions.is_empty() {
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
                store
                    .has_cached_action_readonly(&a.action_key, td)
                    .unwrap_or(false)
                    || (td == "untrusted"
                        && store
                            .has_cached_action_readonly(&a.action_key, "trusted")
                            .unwrap_or(false))
            })
        {
            if fs::read_to_string(&stamp_file)
                .map(|s| s == stamp_val)
                .unwrap_or(false)
            {
                if installed_replayed > 0 {
                    store.sync_sqlite_durable()?;
                }
            } else {
                store.sync_sqlite_durable()?;
                write_stamp()?;
            }
            if td == "trusted" {
                save_cached_portable_manifest_from_pack(&store.root, manifest);
            }
            return Ok((manifest.actions.len(), effective_blobs.len()));
        }
    }

    let res =
        store.batch_import_pack_metadata_with_domain(&effective_blobs, &manifest.actions, td)?;
    if manifest.actions.is_empty() && effective_blobs.is_empty() && installed_replayed > 0 {
        store.sync_sqlite_durable()?;
    }
    write_stamp()?;
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
    try_import_from_shared_cas_with_domain_and_pubkey(store, manifest, trust_domain, None)
}

pub(crate) fn try_import_from_shared_cas_with_domain_and_pubkey(
    store: &mut TurboStore,
    manifest: &PackManifest,
    trust_domain: &str,
    trusted_pubkey: Option<&str>,
) -> Result<Option<(usize, usize)>> {
    let _pub_guard = crate::db::acquire_cas_publication_guard(&store.root)?;
    let Some((staged_blobs, total_newly_written)) =
        prestage_blobs_from_shared_cas(&store.root, manifest)
    else {
        return Ok(None);
    };
    let res = finish_import_from_prestaged_shared_cas_inner(
        store,
        manifest,
        &staged_blobs,
        total_newly_written,
        trust_domain,
        trusted_pubkey,
        true,
    )?;
    Ok(Some(res))
}

pub type PrefetchedPackPrestage = (
    PackManifest,
    Vec<(String, String, i64, i64)>,
    usize,
    crate::db::CasPublicationGuard,
);

#[allow(clippy::type_complexity)]
pub fn try_read_and_prestage_pack(
    store_root: &Path,
    input_path: &Path,
) -> Option<PrefetchedPackPrestage> {
    let (file_len, magic, header_buf) = read_pack_header_from_file(input_path)?;
    let header_len = header_buf.len();
    let manifest = serde_json::from_slice::<PackManifest>(&header_buf).ok()?;
    let expected_payload: u64 = manifest.blobs.iter().map(|b| b.size_bytes).sum();
    let size_ok = &magic == b"TLPK\x00\x00\x00\x03"
        || 16 + (header_len as u64) + expected_payload == file_len;
    if !size_ok {
        return None;
    }
    let pub_guard = crate::db::acquire_cas_publication_guard(store_root).ok()?;
    let (staged_blobs, newly_written) = prestage_blobs_from_shared_cas(store_root, &manifest)?;
    Some((manifest, staged_blobs, newly_written, pub_guard))
}

pub fn import_pack_with_policy(
    store: &mut TurboStore,
    input_path: &Path,
    requested_domain: Option<&str>,
    trusted_pubkey: Option<&str>,
    allow_unattested_trusted: bool,
) -> Result<(usize, usize)> {
    if let Some((manifest, staged_blobs, newly_written, pub_guard)) =
        try_read_and_prestage_pack(&store.root, input_path)
    {
        let td = resolve_pack_import_trust_domain(
            &manifest,
            requested_domain,
            trusted_pubkey,
            allow_unattested_trusted,
        )?;
        let res = finish_import_from_prestaged_shared_cas_inner(
            store,
            &manifest,
            &staged_blobs,
            newly_written,
            td,
            trusted_pubkey,
            false,
        );
        drop(pub_guard);
        return res;
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
    let _pub_guard = crate::db::acquire_cas_publication_guard(&store.root)?;
    let is_uncompressed = input_bytes.starts_with(b"TLPK\x00\x00\x00\x02")
        || input_bytes.starts_with(b"TLPK\x00\x00\x00\x03")
        || input_bytes.first().copied() == Some(b'{');
    let owned_decomp: Option<Vec<u8>> = if is_uncompressed {
        None
    } else {
        let tmp_in = crate::shm_cache::StagedTempFile::write(
            store
                .fast_staging_dir()
                .join(format!("import_{}.tlpack.zst", next_tmp_id())),
            input_bytes,
        )?;
        let decomp = crate::trusted_tools::system_command("zstd").and_then(|mut command| {
            command
                .args(["-q", "-d", "-c", tmp_in.to_str().unwrap_or("")])
                .output()
                .map_err(Into::into)
        });
        drop(tmp_in);
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
        if let Some(res) =
            try_import_from_shared_cas_with_domain_and_pubkey(store, &manifest, td, trusted_pubkey)?
        {
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
    let mut created_parents: Vec<std::path::PathBuf> = Vec::new();
    if !slices.is_empty() {
        let blobs_dir = store.root.join("blobs");
        let mut seen_prefix = [false; 256];
        for &(b, _) in &slices {
            let prefix = blob_hash_prefix(&b.blob_hash);
            let p_idx = u8::from_str_radix(prefix, 16).unwrap_or(0) as usize;
            if !seen_prefix[p_idx] {
                seen_prefix[p_idx] = true;
                let parents = crate::db::ensure_dir_tracking(&blobs_dir.join(prefix), &store.root)?;
                created_parents.extend(parents);
            }
        }
    }

    #[allow(clippy::type_complexity)]
    let process_chunk = |chunk: &[(&PackedBlob, &[u8])],
                         root_dir: &Path,
                         #[cfg_attr(unix, allow(unused_variables))] staging_dir_ref: &Path|
     -> Result<(Vec<(String, String, i64, i64)>, usize)> {
        let mut local = Vec::with_capacity(chunk.len());
        let mut newly_written = 0usize;
        #[cfg(not(unix))]
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
            let prefix = blob_hash_prefix(&b.blob_hash);
            let dest = root_dir.join("blobs").join(prefix).join(&b.blob_hash);

            // Existing blobs are digest-checked and torn/corrupt ones rewritten; all writes are atomic.
            #[cfg(unix)]
            let inode = {
                use crate::db::{
                    durability_barrier, is_exclusively_created_immutable_cas_inode,
                    open_regular_nofollow, sync_dir, write_blob_atomic,
                };
                use std::os::unix::fs::MetadataExt;
                let len = blob_bytes.len() as u64;
                let existing_intact = (|| -> Option<(fs::File, fs::Metadata)> {
                    let (mut f, m) = open_regular_nofollow(&dest).ok()?;
                    if m.len() != len
                        || !is_exclusively_created_immutable_cas_inode(&m, &b.blob_hash)
                    {
                        return None;
                    }
                    let mut buf = Vec::with_capacity(len.min(64 * 1024 * 1024) as usize);
                    f.read_to_end(&mut buf).ok()?;
                    if buf.len() as u64 != len
                        || blake3::hash(&buf).to_hex().as_str() != b.blob_hash
                    {
                        return None;
                    }
                    Some((f, m))
                })();
                match existing_intact {
                    Some((f, m)) => {
                        durability_barrier(&f)?;
                        if let Some(parent) = dest.parent() {
                            sync_dir(parent)?;
                        }
                        m.ino() as i64
                    }
                    None => {
                        let replace = fs::symlink_metadata(&dest).is_ok();
                        newly_written += 1;
                        write_blob_atomic(root_dir, &dest, &b.blob_hash, blob_bytes, replace)?
                    }
                }
            };
            #[cfg(not(unix))]
            let inode = {
                if !dest.exists() {
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

    let sync_created_parents = |dirs: &mut Vec<std::path::PathBuf>| -> Result<()> {
        dirs.sort_by_key(|p| std::cmp::Reverse(p.components().count()));
        dirs.dedup();
        for dir in dirs.drain(..) {
            crate::db::sync_dir(&dir)?;
        }
        Ok(())
    };
    let mut staged_blobs = Vec::with_capacity(manifest.blobs.len());
    let mut total_newly_written = 0usize;
    let import_res: Result<()> = if slices.len() <= 64 && payload_region.len() <= 4 * 1024 * 1024 {
        if !slices.is_empty() {
            match process_chunk(&slices, &store.root, &staging_dir) {
                Ok((sb, nw)) => {
                    staged_blobs = sb;
                    total_newly_written = nw;
                    Ok(())
                }
                Err(e) => Err(e),
            }
        } else {
            Ok(())
        }
    } else {
        let n_threads = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .min(slices.len().max(1))
            .max(1);
        let chunk_size = slices.len().div_ceil(n_threads);
        let store_root = store.root.clone();
        let staging_dir_ref = &staging_dir;

        std::thread::scope(|s| -> Result<()> {
            let mut handles = Vec::with_capacity(n_threads);
            for chunk in slices.chunks(chunk_size) {
                let root_clone = store_root.clone();
                handles.push(s.spawn(move || process_chunk(chunk, &root_clone, staging_dir_ref)));
            }
            for h in handles {
                let (res, nw) = h
                    .join()
                    .map_err(|_| anyhow::anyhow!("import_pack worker panicked"))??;
                staged_blobs.extend(res);
                total_newly_written += nw;
            }
            Ok(())
        })
    };
    if let Err(e) = import_res {
        let _ = sync_created_parents(&mut created_parents);
        return Err(e);
    }
    sync_created_parents(&mut created_parents)?;

    let installed_replayed = if td == "trusted"
        && !manifest.replayed_oleans.is_empty()
        && pack_manifest_has_verified_ed25519(&manifest, trusted_pubkey)
    {
        let allowed_githashes = crate::module_builder::discover_host_installed_lean_githashes();
        store.import_attested_replayed_oleans(
            &manifest.replayed_oleans,
            td,
            &allowed_githashes,
            &[],
        )?
    } else {
        0
    };

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
                store
                    .has_cached_action_readonly(&a.action_key, td)
                    .unwrap_or(false)
                    || (td == "untrusted"
                        && store
                            .has_cached_action_readonly(&a.action_key, "trusted")
                            .unwrap_or(false))
            })
        {
            if installed_replayed > 0 {
                store.sync_sqlite_durable()?;
            }
            return Ok((manifest.actions.len(), staged_blobs.len()));
        }
    }

    let res = store.batch_import_pack_metadata_with_domain(&staged_blobs, &manifest.actions, td)?;
    if manifest.actions.is_empty() && staged_blobs.is_empty() && installed_replayed > 0 {
        store.sync_sqlite_durable()?;
    }
    Ok(res)
}
