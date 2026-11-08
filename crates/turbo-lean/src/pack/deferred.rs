use crate::db::TurboStore;
use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs;
use std::path::Path;

use super::archive::{
    finish_import_from_prestaged_shared_cas_inner, prestage_blobs_from_shared_cas,
    shared_cas_blobs_dir, try_parse_v3_header, verify_cached_pack_stream_integrity_at_root,
};
use super::http_sync::http_request;
use super::manifest::{
    is_loopback_http_url, is_portable_artifact, read_u64_le_at, resolve_pack_import_trust_domain,
    DeltaManifest, ExportDeltaRequest, PackManifest,
};

const DEFERRED_PACK_V5_MAGIC: &[u8; 8] = b"TLDP\x00\x00\x00\x05";
const DEFERRED_PACK_SPOOL_PREFIX: &str = "deferred_pack_v4.";
const CACHED_MANIFEST_ENVELOPE_VERSION: u32 = 2;
const LAST_FULL_EXPORT_MAGIC: &[u8; 8] = b"TLFE\x00\x00\x00\x02";
const LAST_IMPORT_STAMP_VERSION: &str = "v2";

#[derive(Serialize, Deserialize)]
struct CachedPortableManifestEnvelope {
    version: u32,
    build_epoch: String,
    manifest: DeltaManifest,
}

pub(crate) fn write_cached_portable_manifest_with_epoch(
    store_root: &Path,
    dm: &DeltaManifest,
    expected_epoch: &str,
) {
    let env = CachedPortableManifestEnvelope {
        version: CACHED_MANIFEST_ENVELOPE_VERSION,
        build_epoch: expected_epoch.to_string(),
        manifest: dm.clone(),
    };
    if let Ok(dm_bytes) = serde_json::to_vec(&env) {
        let locks_dir = store_root.join("locks");
        if let Ok(created) = crate::db::ensure_dir_tracking(&locks_dir, store_root) {
            let _ = crate::db::write_bytes_durable(
                &locks_dir.join("cached_portable_manifest.json"),
                &dm_bytes,
                &created,
            );
        }
    }
}

pub(crate) fn load_cached_portable_manifest_with_epoch(
    store_root: &Path,
    expected_epoch: &str,
) -> Option<DeltaManifest> {
    let locks_dir = store_root.join("locks");
    let man_path = locks_dir.join("cached_portable_manifest.json");
    let (dm_bytes, _) = crate::db::read_regular_nofollow(&man_path)?;
    match serde_json::from_slice::<CachedPortableManifestEnvelope>(&dm_bytes) {
        Ok(env)
            if env.version == CACHED_MANIFEST_ENVELOPE_VERSION
                && env.build_epoch == expected_epoch =>
        {
            Some(env.manifest)
        }
        _ => {
            if fs::remove_file(&man_path).is_ok() {
                let _ = crate::db::sync_dir(&locks_dir);
            }
            None
        }
    }
}

pub(crate) fn encode_last_full_export_with_epoch(
    n_acts: usize,
    n_blobs: usize,
    raw_bytes: u64,
    stream: &[u8],
    epoch: &str,
) -> Vec<u8> {
    let epoch_bytes = epoch.as_bytes();
    let mut buf = Vec::with_capacity(8 + 2 + epoch_bytes.len() + 24 + stream.len());
    buf.extend_from_slice(LAST_FULL_EXPORT_MAGIC);
    buf.extend_from_slice(&(epoch_bytes.len() as u16).to_le_bytes());
    buf.extend_from_slice(epoch_bytes);
    buf.extend_from_slice(&(n_acts as u64).to_le_bytes());
    buf.extend_from_slice(&(n_blobs as u64).to_le_bytes());
    buf.extend_from_slice(&raw_bytes.to_le_bytes());
    buf.extend_from_slice(stream);
    buf
}

pub(crate) fn read_last_full_export_with_epoch(
    store_root: &Path,
    header_only_shared_cas: bool,
    expected_epoch: &str,
) -> Option<(usize, usize, u64, Vec<u8>)> {
    let locks_dir = store_root.join("locks");
    let last_file = locks_dir.join(format!(
        "last_full_export_{}.bin",
        if header_only_shared_cas { 1 } else { 0 }
    ));
    let (cached_bytes, _) = crate::db::read_regular_nofollow(&last_file)?;
    let parsed = (|| -> Option<(usize, usize, u64, Vec<u8>)> {
        if cached_bytes.len() < 10 + 24 || &cached_bytes[..8] != LAST_FULL_EXPORT_MAGIC {
            return None;
        }
        let ep_len = u16::from_le_bytes([cached_bytes[8], cached_bytes[9]]) as usize;
        let meta_off = 10usize.checked_add(ep_len)?;
        let stream_off = meta_off.checked_add(24)?;
        if stream_off > cached_bytes.len() {
            return None;
        }
        if &cached_bytes[10..meta_off] != expected_epoch.as_bytes() {
            return None;
        }
        let n_acts = read_u64_le_at(&cached_bytes, meta_off) as usize;
        let n_blobs = read_u64_le_at(&cached_bytes, meta_off + 8) as usize;
        let raw_bytes = read_u64_le_at(&cached_bytes, meta_off + 16);
        Some((
            n_acts,
            n_blobs,
            raw_bytes,
            cached_bytes[stream_off..].to_vec(),
        ))
    })();
    if parsed.is_none() && fs::remove_file(&last_file).is_ok() {
        let _ = crate::db::sync_dir(&locks_dir);
    }
    parsed
}

pub(crate) fn format_last_import_stamp_with_epoch(
    header_hash: &str,
    n_acts: usize,
    n_blobs: usize,
    td: &str,
    epoch: &str,
) -> String {
    format!(
        "{}:{}:{}:{}:{}:{}",
        LAST_IMPORT_STAMP_VERSION, epoch, header_hash, n_acts, n_blobs, td
    )
}

pub(crate) fn read_last_import_stamp_with_epoch(
    store_root: &Path,
    expected_epoch: &str,
) -> Option<(String, usize, usize, String)> {
    let locks_dir = store_root.join("locks");
    let stamp_file = locks_dir.join("last_import_stamp");
    let (bytes, _) = crate::db::read_regular_nofollow(&stamp_file)?;
    let parsed = (|| -> Option<(String, usize, usize, String)> {
        let recorded = std::str::from_utf8(&bytes).ok()?;
        let mut parts = recorded.split(':');
        let ver = parts.next()?;
        let saved_epoch = parts.next()?;
        let saved_stamp = parts.next()?;
        let acts_s = parts.next()?;
        let blobs_s = parts.next()?;
        let saved_td = parts.next()?;
        if parts.next().is_some()
            || ver != LAST_IMPORT_STAMP_VERSION
            || saved_epoch != expected_epoch
            || (saved_td != "trusted" && saved_td != "untrusted")
        {
            return None;
        }
        let n_acts: usize = acts_s.parse().ok()?;
        let n_blobs: usize = blobs_s.parse().ok()?;
        Some((
            saved_stamp.to_string(),
            n_acts,
            n_blobs,
            saved_td.to_string(),
        ))
    })();
    if parsed.is_none() && fs::remove_file(&stamp_file).is_ok() {
        let _ = crate::db::sync_dir(&locks_dir);
    }
    parsed
}

/// Durably purge orphan warm-DB sidecars (`last_import_stamp`, `last_full_export_{0,1}.bin`, and
/// `cached_portable_manifest.json` when no deferred-pack spool is pending) if `state.db` is missing
/// or cold (< 4096 bytes) on `TurboStore::open`.
pub(crate) fn purge_orphan_locks_sidecars_on_cold_db_durable(store_root: &Path) -> Result<()> {
    let locks_dir = store_root.join("locks");
    if !locks_dir.exists() {
        return Ok(());
    }
    let _pub_guard = crate::db::acquire_cas_publication_guard(store_root)?;
    let _def_lock = acquire_deferred_pack_lock(store_root)?;
    let has_pending_deferred = !list_pending_deferred_pack_files(&locks_dir)?.is_empty();
    let mut removed_any = false;
    for fixed in [
        "last_import_stamp",
        "last_full_export_0.bin",
        "last_full_export_1.bin",
    ] {
        match fs::remove_file(locks_dir.join(fixed)) {
            Ok(()) => removed_any = true,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(e.into()),
        }
    }
    if !has_pending_deferred {
        match fs::remove_file(locks_dir.join("cached_portable_manifest.json")) {
            Ok(()) => removed_any = true,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(e.into()),
        }
    }
    if removed_any {
        crate::db::sync_dir(&locks_dir)?;
    }
    Ok(())
}

/// Durably purge pre-epoch persistent sidecars and pending deferred-pack spool records from
/// `<store_root>/locks` during the `uver < 8` SQLite migration before `replay_pending_deferred_packs`
/// can resurrect pre-epoch actions or stateless import/sync paths can trust stale stamps/manifests.
pub(crate) fn purge_pre_epoch_locks_sidecars_durable(store_root: &Path) -> Result<()> {
    let locks_dir = store_root.join("locks");
    if !locks_dir.exists() {
        return Ok(());
    }
    // Respect global lock order `gc_publish.lock` -> `deferred_pack.lock`.
    let _pub_guard = crate::db::acquire_cas_publication_guard(store_root)?;
    let _def_lock = acquire_deferred_pack_lock(store_root)?;
    let mut removed_any = false;
    for fixed in [
        "last_import_stamp",
        "cached_portable_manifest.json",
        "last_full_export_0.bin",
        "last_full_export_1.bin",
        "deferred_pack_v3.domain",
        "deferred_pack_v3.bin",
    ] {
        match fs::remove_file(locks_dir.join(fixed)) {
            Ok(()) => removed_any = true,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(e.into()),
        }
    }
    let entries = match fs::read_dir(&locks_dir) {
        Ok(rd) => Some(rd),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
        Err(e) => return Err(e.into()),
    };
    if let Some(rd) = entries {
        for entry in rd {
            let entry = entry?;
            let fname = entry.file_name();
            let Some(name) = fname.to_str() else {
                continue;
            };
            let is_deferred_spool = (name.starts_with("deferred_pack")
                && name != "deferred_pack.lock")
                || name.starts_with(".deferred_pack")
                || name.starts_with(".last_import_stamp.")
                || name.starts_with(".cached_portable_manifest.json.")
                || name.starts_with(".last_full_export_");
            if is_deferred_spool {
                match fs::remove_file(entry.path()) {
                    Ok(()) => removed_any = true,
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                    Err(e) => return Err(e.into()),
                }
            }
        }
    }
    if removed_any {
        crate::db::sync_dir(&locks_dir)?;
    }
    Ok(())
}

pub(crate) struct DeferredPackLockGuard {
    file: fs::File,
}

#[cfg(unix)]
impl Drop for DeferredPackLockGuard {
    fn drop(&mut self) {
        unsafe {
            use std::os::unix::io::AsRawFd;
            libc::flock(self.file.as_raw_fd(), libc::LOCK_UN);
        }
    }
}

pub(crate) fn acquire_deferred_pack_lock(store_root: &Path) -> Result<DeferredPackLockGuard> {
    let locks_dir = crate::db::ensure_store_locks_dir_durable(store_root)?;
    let lock_path = locks_dir.join("deferred_pack.lock");
    let created_lock = !lock_path.exists();
    let file = fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(&lock_path)?;
    if created_lock {
        crate::db::sync_dir(&locks_dir)?;
    }
    #[cfg(unix)]
    {
        use std::os::unix::io::AsRawFd;
        if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX) } != 0 {
            return Err(std::io::Error::last_os_error())
                .context("flock(LOCK_EX) deferred_pack.lock");
        }
    }
    Ok(DeferredPackLockGuard { file })
}

pub(crate) fn list_pending_deferred_pack_files(
    locks_dir: &Path,
) -> Result<Vec<std::path::PathBuf>> {
    let entries = match fs::read_dir(locks_dir) {
        Ok(rd) => rd,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(e) => return Err(e.into()),
    };
    let mut legacy_claims = Vec::new();
    let mut legacy_v3 = Vec::new();
    let mut spool_v4 = Vec::new();
    for entry in entries {
        let entry = entry?;
        let fname = entry.file_name();
        let Some(name) = fname.to_str() else {
            continue;
        };
        if !entry.file_type().map(|ft| ft.is_file()).unwrap_or(false) {
            continue;
        }
        if name.starts_with("deferred_pack_v3.claim.") {
            legacy_claims.push(entry.path());
        } else if name == "deferred_pack_v3.bin" {
            legacy_v3.push(entry.path());
        } else if name.starts_with(DEFERRED_PACK_SPOOL_PREFIX) && name.ends_with(".bin") {
            spool_v4.push(entry.path());
        }
    }
    legacy_claims.sort();
    legacy_v3.sort();
    spool_v4.sort();
    let mut out = Vec::with_capacity(legacy_claims.len() + legacy_v3.len() + spool_v4.len());
    out.extend(legacy_claims);
    out.extend(legacy_v3);
    out.extend(spool_v4);
    Ok(out)
}

pub(crate) fn replay_pending_deferred_packs_inner(
    store: &mut TurboStore,
    already_holds_gc_or_pub_lock: bool,
) -> Result<()> {
    replay_pending_deferred_packs_inner_with_epoch(
        store,
        already_holds_gc_or_pub_lock,
        crate::TURBO_LEAN_BUILD_EPOCH,
    )
}

pub(crate) fn replay_pending_deferred_packs_inner_with_epoch(
    store: &mut TurboStore,
    already_holds_gc_or_pub_lock: bool,
    expected_epoch: &str,
) -> Result<()> {
    let locks_dir = store.root.join("locks");
    let _ = fs::remove_file(locks_dir.join("deferred_pack_v3.domain"));
    if list_pending_deferred_pack_files(&locks_dir)?.is_empty() {
        return Ok(());
    }
    // Enforce global lock order `gc_publish.lock` -> `deferred_pack.lock` across both
    // `TurboStore::open` replay (`LOCK_SH`) and `run_gc` (`LOCK_EX`), avoiding AB-BA deadlock.
    let _pub_guard = if already_holds_gc_or_pub_lock {
        None
    } else {
        Some(crate::db::acquire_cas_publication_guard(&store.root)?)
    };
    let _def_lock = acquire_deferred_pack_lock(&store.root)?;
    let pending = list_pending_deferred_pack_files(&locks_dir)?;
    if pending.is_empty() {
        return Ok(());
    }
    let mut removed_any = false;
    let mut replay_err: Option<anyhow::Error> = None;
    for spool_path in pending {
        let pack_bytes = match fs::read(&spool_path) {
            Ok(b) => b,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
            Err(e) => {
                replay_err = Some(e.into());
                break;
            }
        };
        let Some((deferred_td, manifest)) =
            decode_deferred_pack_record_with_epoch(&pack_bytes, expected_epoch)
        else {
            if fs::remove_file(&spool_path).is_ok() {
                removed_any = true;
            }
            continue;
        };
        let staged_blobs: Vec<(String, String, i64, i64)> = manifest
            .blobs
            .iter()
            .map(|b| (b.blob_hash.clone(), b.kind.clone(), b.size_bytes as i64, 0))
            .collect();
        let force_commit = staged_blobs.len().max(1);
        match finish_import_from_prestaged_shared_cas_inner(
            store,
            &manifest,
            &staged_blobs,
            force_commit,
            deferred_td,
            None,
            true,
        ) {
            Ok(_) => match fs::remove_file(&spool_path) {
                Ok(()) => removed_any = true,
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                Err(e) => {
                    replay_err = Some(e.into());
                    break;
                }
            },
            Err(e) => {
                replay_err = Some(e);
                break;
            }
        }
    }
    if removed_any {
        if let Err(e) = crate::db::sync_dir(&locks_dir) {
            if replay_err.is_none() {
                replay_err = Some(e);
            }
        }
    }
    if let Some(e) = replay_err {
        return Err(e);
    }
    Ok(())
}

pub(crate) fn replay_pending_deferred_packs(store: &mut TurboStore) -> Result<()> {
    replay_pending_deferred_packs_inner(store, false)
}

pub(crate) fn encode_deferred_pack_record_with_epoch(
    td: &str,
    v3_bytes: &[u8],
    epoch: &str,
) -> Vec<u8> {
    let td_byte: u8 = if td == "trusted" { 1 } else { 0 };
    let epoch_bytes = epoch.as_bytes();
    let mut rec = Vec::with_capacity(8 + 1 + 2 + epoch_bytes.len() + v3_bytes.len());
    rec.extend_from_slice(DEFERRED_PACK_V5_MAGIC);
    rec.push(td_byte);
    rec.extend_from_slice(&(epoch_bytes.len() as u16).to_le_bytes());
    rec.extend_from_slice(epoch_bytes);
    rec.extend_from_slice(v3_bytes);
    rec
}

fn stage_deferred_pack_record_locked_with_epoch(
    store_root: &Path,
    td: &str,
    v3_bytes: &[u8],
    epoch: &str,
) -> bool {
    let Ok(locks_dir) = crate::db::ensure_store_locks_dir_durable(store_root) else {
        return false;
    };
    let canonical_root = locks_dir.parent().unwrap_or(store_root);
    let Ok(created) = crate::db::ensure_dir_tracking(&locks_dir, canonical_root) else {
        return false;
    };
    let Ok(_def_lock) = acquire_deferred_pack_lock(canonical_root) else {
        for dir in &created {
            let _ = crate::db::sync_dir(dir);
        }
        return false;
    };
    static DEF_SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
    let seq = DEF_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let spool_name = format!(
        "{}{:020}.{:010}.{:010}.bin",
        DEFERRED_PACK_SPOOL_PREFIX,
        nanos,
        std::process::id(),
        seq
    );
    let rec = encode_deferred_pack_record_with_epoch(td, v3_bytes, epoch);
    if crate::db::write_bytes_durable(&locks_dir.join(spool_name), &rec, &created).is_err() {
        return false;
    }
    let _ = fs::remove_file(locks_dir.join("deferred_pack_v3.domain"));
    true
}

pub(super) fn stage_deferred_pack_record_locked(
    store_root: &Path,
    td: &str,
    v3_bytes: &[u8],
) -> bool {
    stage_deferred_pack_record_locked_with_epoch(
        store_root,
        td,
        v3_bytes,
        crate::TURBO_LEAN_BUILD_EPOCH,
    )
}

#[cfg(test)]
pub(crate) fn stage_deferred_pack_record_with_epoch(
    store_root: &Path,
    td: &str,
    v3_bytes: &[u8],
    epoch: &str,
) -> bool {
    // Enforce global lock order `gc_publish.lock` -> `deferred_pack.lock`.
    let Ok(_pub_guard) = crate::db::acquire_cas_publication_guard(store_root) else {
        return false;
    };
    stage_deferred_pack_record_locked_with_epoch(store_root, td, v3_bytes, epoch)
}

#[cfg(test)]
pub(crate) fn stage_deferred_pack_record(store_root: &Path, td: &str, v3_bytes: &[u8]) -> bool {
    stage_deferred_pack_record_with_epoch(store_root, td, v3_bytes, crate::TURBO_LEAN_BUILD_EPOCH)
}

pub(crate) fn decode_deferred_pack_record_with_epoch(
    buf: &[u8],
    expected_epoch: &str,
) -> Option<(&'static str, PackManifest)> {
    if buf.len() < 11 + 16 || &buf[..8] != DEFERRED_PACK_V5_MAGIC {
        return None;
    }
    let td = match buf[8] {
        1 => "trusted",
        0 => "untrusted",
        _ => return None,
    };
    let ep_len = u16::from_le_bytes([buf[9], buf[10]]) as usize;
    let hdr_off = 11usize.checked_add(ep_len)?;
    if hdr_off + 16 > buf.len() || &buf[11..hdr_off] != expected_epoch.as_bytes() {
        return None;
    }
    let manifest = try_parse_v3_header(&buf[hdr_off..])?;
    Some((td, manifest))
}

#[cfg(test)]
pub fn decode_deferred_pack_record(buf: &[u8]) -> Option<(&'static str, PackManifest)> {
    decode_deferred_pack_record_with_epoch(buf, crate::TURBO_LEAN_BUILD_EPOCH)
}

pub fn save_cached_portable_manifest_from_pack(store_root: &Path, manifest: &PackManifest) {
    save_cached_portable_manifest_from_pack_with_epoch(
        store_root,
        manifest,
        crate::TURBO_LEAN_BUILD_EPOCH,
    );
}

pub(crate) fn save_cached_portable_manifest_from_pack_with_epoch(
    store_root: &Path,
    manifest: &PackManifest,
    epoch: &str,
) {
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
    write_cached_portable_manifest_with_epoch(store_root, &dm, epoch);
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
    if td == "trusted" && !manifest.replayed_oleans.is_empty() {
        return None;
    }
    let _pub_guard = crate::db::acquire_cas_publication_guard(store_root).ok()?;
    let (_, _) = prestage_blobs_from_shared_cas(store_root, &manifest)?;
    if !stage_deferred_pack_record_locked(store_root, td, &pack_bytes) {
        return None;
    }
    drop(_pub_guard);
    if td == "trusted" {
        save_cached_portable_manifest_from_pack(store_root, &manifest);
    }
    let pulled = (manifest.actions.len(), manifest.blobs.len());
    let pulled_bytes = if pulled.0 > 0 || pulled.1 > 0 {
        pack_bytes.len() as u64
    } else {
        0
    };
    Some((pulled, pulled_bytes))
}

pub fn try_stateless_noop_pull_sync(store_root: &Path, base_url: &str) -> bool {
    try_stateless_noop_pull_sync_with_epoch(store_root, base_url, crate::TURBO_LEAN_BUILD_EPOCH)
}

pub(crate) fn try_stateless_noop_pull_sync_with_epoch(
    store_root: &Path,
    base_url: &str,
    expected_epoch: &str,
) -> bool {
    let locks_dir = store_root.join("locks");
    let db_warm = fs::metadata(store_root.join("state.db"))
        .map(|m| m.len() >= 4096)
        .unwrap_or(false);
    if !db_warm {
        if fs::remove_file(locks_dir.join("cached_portable_manifest.json")).is_ok() {
            let _ = crate::db::sync_dir(&locks_dir);
        }
        return false;
    }
    if list_pending_deferred_pack_files(&locks_dir)
        .map(|v| !v.is_empty())
        .unwrap_or(false)
    {
        return false;
    }
    let Some(dm) = load_cached_portable_manifest_with_epoch(store_root, expected_epoch) else {
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

#[allow(clippy::type_complexity)]
pub fn try_stateless_push_sync(
    store_root: &Path,
    base_url: &str,
) -> Option<((usize, usize, u64, u64, bool), Option<DeltaManifest>)> {
    try_stateless_push_sync_with_epoch(store_root, base_url, crate::TURBO_LEAN_BUILD_EPOCH)
}

#[allow(clippy::type_complexity)]
pub(crate) fn try_stateless_push_sync_with_epoch(
    store_root: &Path,
    base_url: &str,
    expected_epoch: &str,
) -> Option<((usize, usize, u64, u64, bool), Option<DeltaManifest>)> {
    let locks_dir = store_root.join("locks");
    let db_warm = fs::metadata(store_root.join("state.db"))
        .map(|m| m.len() >= 4096)
        .unwrap_or(false);
    if !db_warm {
        let mut removed = false;
        for f in [
            "cached_portable_manifest.json",
            "last_full_export_0.bin",
            "last_full_export_1.bin",
        ] {
            if fs::remove_file(locks_dir.join(f)).is_ok() {
                removed = true;
            }
        }
        if removed {
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
    let dm = load_cached_portable_manifest_with_epoch(store_root, expected_epoch)?;
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
        let last_file = locks_dir.join(format!(
            "last_full_export_{}.bin",
            if is_loopback { 1 } else { 0 }
        ));
        if !is_loopback || shared_cas_blobs_dir().exists() {
            if let Some((n_acts, n_blobs, raw_bytes, push_bytes)) =
                read_last_full_export_with_epoch(store_root, is_loopback, expected_epoch)
            {
                if n_acts == dm.action_keys.len()
                    && n_blobs == dm.blob_hashes.len()
                    && verify_cached_pack_stream_integrity_at_root(
                        store_root,
                        &push_bytes,
                        n_acts,
                        n_blobs,
                        raw_bytes,
                    )
                {
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
                        &push_bytes,
                    )
                    .is_ok()
                    {
                        return Some((
                            (n_acts, n_blobs, raw_bytes, pushed_pack_bytes, false),
                            None,
                        ));
                    }
                } else if fs::remove_file(&last_file).is_ok() {
                    let _ = crate::db::sync_dir(&locks_dir);
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
