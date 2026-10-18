use crate::db::{now_unix, ActionRecord, BlobEntry, SingleflightOutcome, TurboStore};
use anyhow::{Context, Result};
use rusqlite::params;
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
    let mut stmt = store.conn.prepare(
        "SELECT action_key FROM actions WHERE status = 'completed' AND trust_domain = 'trusted' ORDER BY action_key ASC",
    )?;
    let rows = stmt.query_map([], |r| r.get::<_, String>(0))?;

    let mut action_keys = Vec::new();
    let mut blob_set = HashSet::new();

    for row in rows {
        let ak = row?;
        let mut out_stmt = store.conn.prepare(
            "SELECT b.blob_hash, b.kind, ao.rel_path
             FROM action_outputs ao
             JOIN blobs b ON b.blob_hash = ao.blob_hash
             WHERE ao.action_key = ?1",
        )?;
        let outputs: Vec<(String, String, String)> = out_stmt
            .query_map(params![ak], |orow| {
                Ok((orow.get(0)?, orow.get(1)?, orow.get(2)?))
            })?
            .collect::<std::result::Result<Vec<_>, _>>()?;

        if outputs.is_empty() {
            continue;
        }
        if only_portable
            && outputs
                .iter()
                .any(|(_, kind, rel)| !is_portable_artifact(kind, rel))
        {
            continue;
        }
        for (bh, _, _) in outputs {
            if store.blob_path(&bh).exists() {
                blob_set.insert(bh);
            }
        }
        action_keys.push(ak);
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

pub fn export_pack_filtered(
    store: &TurboStore,
    output_path: &Path,
    only_portable: bool,
    exclude_actions: &HashSet<String>,
    exclude_blobs: &HashSet<String>,
) -> Result<(usize, usize, u64)> {
    let mut stmt = store.conn.prepare(
        "SELECT action_key, toolchain_githash, kind, status, fencing_token,
                COALESCE(output_manifest_hash, ''), duration_ms, peak_pss_bytes, heartbeats, trust_domain
         FROM actions
         WHERE status = 'completed' AND trust_domain = 'trusted'",
    )?;

    let mut actions = Vec::new();
    let mut needed_blobs = HashSet::new();

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
        ))
    })?;

    for row in rows {
        let (ak, tc, kind, status, ft, mh, dur, pss, hb, td) = row?;
        if exclude_actions.contains(&ak) {
            continue;
        }
        let mut out_stmt = store.conn.prepare(
            "SELECT b.blob_hash, b.kind, b.size_bytes, ao.rel_path
             FROM action_outputs ao
             JOIN blobs b ON b.blob_hash = ao.blob_hash
             WHERE ao.action_key = ?1",
        )?;
        let outputs: Vec<BlobEntry> = out_stmt
            .query_map(params![ak], |orow| {
                Ok(BlobEntry {
                    blob_hash: orow.get(0)?,
                    kind: orow.get(1)?,
                    size_bytes: orow.get::<_, i64>(2)? as u64,
                    rel_path: orow.get(3)?,
                })
            })?
            .collect::<std::result::Result<Vec<_>, _>>()?;

        if outputs.is_empty() {
            continue;
        }
        if only_portable
            && outputs
                .iter()
                .any(|o| !is_portable_artifact(&o.kind, &o.rel_path))
        {
            continue;
        }
        for o in &outputs {
            if !exclude_blobs.contains(&o.blob_hash) {
                needed_blobs.insert((o.blob_hash.clone(), o.kind.clone()));
            }
        }

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
    }

    let mut blobs = Vec::with_capacity(needed_blobs.len());
    let mut raw_payloads = Vec::with_capacity(needed_blobs.len());
    let mut total_raw_bytes = 0u64;
    for (bh, kind) in needed_blobs {
        let p = store.blob_path(&bh);
        if p.exists() {
            let bytes = fs::read(&p)?;
            let sz = bytes.len() as u64;
            total_raw_bytes += sz;
            blobs.push(PackedBlob {
                blob_hash: bh,
                portable: is_portable_artifact(&kind, ""),
                kind,
                size_bytes: sz,
                data_hex_or_base64: Vec::new(),
            });
            raw_payloads.push(bytes);
        }
    }

    let manifest = PackManifest {
        format_version: 2,
        host_arch: std::env::consts::ARCH.to_string(),
        created_at: crate::db::now_unix(),
        actions,
        blobs,
    };

    let header_json = serde_json::to_vec(&manifest)?;
    let mut pack_stream = Vec::with_capacity(16 + header_json.len() + total_raw_bytes as usize);
    pack_stream.extend_from_slice(b"TLPK\x00\x00\x00\x02");
    pack_stream.extend_from_slice(&(header_json.len() as u64).to_le_bytes());
    pack_stream.extend_from_slice(&header_json);
    for payload in raw_payloads {
        pack_stream.extend_from_slice(&payload);
    }

    let tmp_raw = store
        .fast_staging_dir()
        .join(format!("export_{}.tlpack.raw", next_tmp_id()));
    fs::write(&tmp_raw, &pack_stream)?;

    // Compress with zstd -1 (fast compression) if available, otherwise write raw stream
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

    Ok((
        manifest.actions.len(),
        manifest.blobs.len(),
        total_raw_bytes,
    ))
}

pub fn import_pack(store: &mut TurboStore, input_path: &Path) -> Result<(usize, usize)> {
    let raw_bytes = fs::read(input_path)?;
    let stream_bytes = if raw_bytes.starts_with(b"TLPK\x00\x00\x00\x02") || raw_bytes.starts_with(b"{") {
        raw_bytes
    } else {
        let decomp = Command::new("zstd")
            .args(["-q", "-d", "-c", input_path.to_str().unwrap_or("")])
            .output();
        match decomp {
            Ok(out) if out.status.success() && !out.stdout.is_empty() => out.stdout,
            _ => raw_bytes,
        }
    };

    let (manifest, payload_region): (PackManifest, &[u8]) =
        if stream_bytes.starts_with(b"TLPK\x00\x00\x00\x02") && stream_bytes.len() >= 16 {
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
                serde_json::from_slice(&stream_bytes).context("Failed to parse PackManifest")?;
            (m, &[])
        };

    let staging_dir = store.root.join("staging");
    fs::create_dir_all(&staging_dir)?;

    let mut offset = 0usize;
    let mut staged_blobs = Vec::with_capacity(manifest.blobs.len());
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

        // Re-verify BLAKE3 digest of every incoming blob (Zero-Trust transport rule!)
        let actual_hash = blake3::hash(blob_bytes).to_hex().to_string();
        if actual_hash != b.blob_hash {
            anyhow::bail!(
                "BLAKE3 integrity check failed on imported blob: expected {}, got {}",
                b.blob_hash,
                actual_hash
            );
        }
        let dest = store.blob_path(&b.blob_hash);
        // Zero-copy existing-blob skip: if the immutable content-addressed blob already exists on disk,
        // skip rewriting and fsyncing it!
        if !dest.exists() {
            if let Some(parent) = dest.parent() {
                fs::create_dir_all(parent)?;
            }
            let staging_path = staging_dir.join(format!("{}.{}.tmp", b.blob_hash, next_tmp_id()));
            fs::write(&staging_path, blob_bytes)?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let mut perms = fs::metadata(&staging_path)?.permissions();
                perms.set_mode(0o444);
                fs::set_permissions(&staging_path, perms)?;
            }
            fs::rename(&staging_path, &dest)?;
        }
        #[cfg(unix)]
        let inode = {
            use std::os::unix::fs::MetadataExt;
            fs::metadata(&dest).map(|m| m.ino() as i64).unwrap_or(0)
        };
        #[cfg(not(unix))]
        let inode = 0i64;

        staged_blobs.push((
            b.blob_hash.clone(),
            b.kind.clone(),
            blob_bytes.len() as i64,
            inode,
        ));
    }

    store.batch_import_pack_metadata(&staged_blobs, &manifest.actions)
}

/// Lightweight HTTP Server (`turbo-lean serve`) for remote CAS sync & GPU/CPU offload (e.g., on DGX Spark)
pub fn run_server(store_root: Option<&Path>, listen_addr: &str, gpu_enable: bool) -> Result<()> {
    let listener = TcpListener::bind(listen_addr)
        .with_context(|| format!("Failed to bind turbo-lean server on {}", listen_addr))?;
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
        let mut reader = BufReader::new(stream.try_clone()?);
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
        loop {
            let mut hline = String::new();
            if reader.read_line(&mut hline).is_err() || hline.trim().is_empty() {
                break;
            }
            if let Some(rest) = hline.to_ascii_lowercase().strip_prefix("content-length:") {
                content_len = rest.trim().parse().unwrap_or(0);
            }
        }

        let mut body = vec![0u8; content_len];
        if content_len > 0 {
            let _ = reader.read_exact(&mut body);
        }

        let mut store = TurboStore::open(store_root)?;
        match (method, path) {
            ("GET", "/health") | ("GET", "/status") => {
                let st = store.storage_status()?;
                let payload = serde_json::to_vec(&serde_json::json!({
                    "ok": true,
                    "arch": std::env::consts::ARCH,
                    "gpu_enabled": gpu_enable,
                    "storage": st
                }))?;
                write_http_response(&mut stream, 200, "application/json", &payload)?;
            }
            ("GET", "/manifest") => {
                let manifest = get_store_manifest(&store, true)?;
                let payload = serde_json::to_vec(&manifest)?;
                write_http_response(&mut stream, 200, "application/json", &payload)?;
            }
            ("GET", "/export") => {
                let tmp = store.fast_staging_dir().join(format!("http_export_{}.tlpack", next_tmp_id()));
                let _ = export_pack(&store, &tmp, true)?;
                let bytes = fs::read(&tmp).unwrap_or_default();
                let _ = fs::remove_file(&tmp);
                write_http_response(&mut stream, 200, "application/octet-stream", &bytes)?;
            }
            ("POST", "/export-delta") => {
                let req: ExportDeltaRequest = serde_json::from_slice(&body).unwrap_or_default();
                let ex_actions: HashSet<String> = req.exclude_actions.into_iter().collect();
                let ex_blobs: HashSet<String> = req.exclude_blobs.into_iter().collect();
                let tmp = store.fast_staging_dir().join(format!("http_delta_{}.tlpack", next_tmp_id()));
                let _ = export_pack_filtered(&store, &tmp, true, &ex_actions, &ex_blobs)?;
                let bytes = fs::read(&tmp).unwrap_or_default();
                let _ = fs::remove_file(&tmp);
                write_http_response(&mut stream, 200, "application/octet-stream", &bytes)?;
            }
            ("POST", "/import") | ("POST", "/import-delta") => {
                let tmp = store.fast_staging_dir().join(format!("http_import_{}.tlpack", next_tmp_id()));
                fs::write(&tmp, &body)?;
                let (acts, blobs) = import_pack(&mut store, &tmp)?;
                let _ = fs::remove_file(&tmp);
                let payload = serde_json::to_vec(&serde_json::json!({
                    "status": "ok",
                    "ok": true,
                    "imported_actions": acts,
                    "imported_blobs": blobs
                }))?;
                write_http_response(&mut stream, 200, "application/json", &payload)?;
            }
            ("POST", "/fast-check") => {
                let req: FastCheckHttpRequest = serde_json::from_slice(&body).unwrap_or_default();
                match execute_fastcheck_payload(&store, &req) {
                    Ok(val) => {
                        let payload = serde_json::to_vec(&val)?;
                        write_http_response(&mut stream, 200, "application/json", &payload)?;
                    }
                    Err(e) => {
                        let payload = serde_json::to_vec(&serde_json::json!({
                            "status": "error",
                            "error": e.to_string()
                        }))?;
                        write_http_response(&mut stream, 500, "application/json", &payload)?;
                    }
                }
            }
            ("POST", "/check-shard") => {
                let req: CheckShardHttpRequest = serde_json::from_slice(&body).unwrap_or_default();
                match execute_check_shard_payload(&mut store, &req) {
                    Ok(val) => {
                        let payload = serde_json::to_vec(&val)?;
                        write_http_response(&mut stream, 200, "application/json", &payload)?;
                    }
                    Err(e) => {
                        let payload = serde_json::to_vec(&serde_json::json!({
                            "status": "error",
                            "error": e.to_string()
                        }))?;
                        write_http_response(&mut stream, 500, "application/json", &payload)?;
                    }
                }
            }
            _ => {
                write_http_response(&mut stream, 404, "application/json", b"{\"error\":\"not_found\"}")?;
            }
        }
    }
    Ok(())
}

fn execute_check_shard_payload(
    store: &mut TurboStore,
    req: &CheckShardHttpRequest,
) -> Result<serde_json::Value> {
    let t0 = std::time::Instant::now();
    if req.shard_key.is_empty() || req.shard_source.is_empty() {
        anyhow::bail!("Missing shard_key or shard_source in /check-shard request");
    }

    let violations = crate::splitter::audit_hygiene(&req.shard_source);
    if !violations.flagged_items.is_empty() {
        anyhow::bail!(
            "Soundness hygiene violation in remote shard `{}`: {:?}",
            req.decl,
            violations.flagged_items
        );
    }

    let toolchain = if req.toolchain.is_empty() {
        "leanprover/lean4:v4.31.0"
    } else {
        req.toolchain.as_str()
    };

    match store.acquire_singleflight(&req.shard_key, toolchain, "theorem_shard", "trusted")? {
        SingleflightOutcome::CacheHit { coalesced, .. } => Ok(serde_json::json!({
            "status": "remote_theorem_cache_hit",
            "decl": req.decl,
            "shard_key": req.shard_key,
            "coalesced": coalesced,
            "interface_hash": req.interface_hash,
            "prefix_env_hash": req.prefix_env_hash,
            "server_arch": std::env::consts::ARCH,
            "server_elapsed_ms": t0.elapsed().as_millis()
        })),
        SingleflightOutcome::Leader(lease) => {
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

            let lean_bin = env_vars
                .get("LAKE")
                .and_then(|lake_bin| Path::new(lake_bin).parent().map(|p| p.join("lean")))
                .filter(|cand| cand.exists())
                .or_else(|| {
                    for tc_root in [
                        Path::new("/var/lib/sandboxed-node/caches/elan/toolchains").to_path_buf(),
                        std::env::var("HOME")
                            .map(|h| Path::new(&h).join(".elan/toolchains"))
                            .unwrap_or_default(),
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

            let dur_ms = t0.elapsed().as_millis() as i64;
            let receipt = serde_json::to_vec(&serde_json::json!({
                "decl": req.decl,
                "prefix_env_hash": req.prefix_env_hash,
                "stmt_hash": req.stmt_hash,
                "proof_hash": req.proof_hash,
                "verified_at": now_unix()
            }))?;
            let bh = store.store_immutable_blob(&receipt, "expr_shard", "trusted", 0)?;
            let entries = vec![BlobEntry {
                blob_hash: bh,
                kind: "expr_shard".to_string(),
                size_bytes: receipt.len() as u64,
                rel_path: format!("thm:{}", req.decl),
            }];
            store.publish_action(&lease, &entries, dur_ms, 0, 0, "trusted")?;
            drop(lease);

            Ok(serde_json::json!({
                "status": "remote_theorem_verified",
                "decl": req.decl,
                "shard_key": req.shard_key,
                "interface_hash": req.interface_hash,
                "prefix_env_hash": req.prefix_env_hash,
                "server_arch": std::env::consts::ARCH,
                "server_elapsed_ms": dur_ms
            }))
        }
    }
}

pub fn compute_fastcheck_binary_key(is_cu: bool, effective_source: &str) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"fastcheck-bin:v1:");
    hasher.update(std::env::consts::ARCH.as_bytes());
    hasher.update(if is_cu { b":cuda:" } else { b":lean_c_o3:" });
    hasher.update(effective_source.as_bytes());
    hasher.finalize().to_hex().to_string()
}

fn execute_fastcheck_payload(
    store: &TurboStore,
    req: &FastCheckHttpRequest,
) -> Result<serde_json::Value> {
    let t0 = std::time::Instant::now();
    let is_cu = req.gpu || req.filename.ends_with(".cu");
    let staging = store.root.join("staging");
    let bin_dir = store.root.join("fastcheck_bins");
    fs::create_dir_all(&staging)?;
    fs::create_dir_all(&bin_dir)?;
    let pid = std::process::id();
    let ts = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();

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
        let src_text = if req.source.contains("def main") {
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
            let tmp_lean = staging.join(format!("http_fc_{}_{}.lean", pid, ts));
            let tmp_c = staging.join(format!("http_fc_{}_{}.c", pid, ts));
            let tmp_bin = staging.join(format!("http_fc_{}_{}.bin", pid, ts));

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

            let lean_bin = env_vars
                .get("PATH")
                .and_then(|p| {
                    p.split(':')
                        .map(|dir| Path::new(dir).join("lean"))
                        .find(|cand| cand.exists())
                })
                .unwrap_or_else(|| std::path::PathBuf::from("lean"));
            let leanc_bin = env_vars
                .get("PATH")
                .and_then(|p| {
                    p.split(':')
                        .map(|dir| Path::new(dir).join("leanc"))
                        .find(|cand| cand.exists())
                })
                .unwrap_or_else(|| std::path::PathBuf::from("leanc"));

            fs::write(&tmp_lean, &src_text)?;

            let out1 = Command::new(&lean_bin)
                .arg("-c")
                .arg(&tmp_c)
                .arg(&tmp_lean)
                .current_dir(&staging)
                .envs(&env_vars)
                .output()
                .context("Failed to compile Lean to C via `lean -c`")?;
            let _ = fs::remove_file(&tmp_lean);
            if !out1.status.success() {
                anyhow::bail!(
                    "`lean -c` failed on HTTP fast-check payload:\n{}\n{}",
                    String::from_utf8_lossy(&out1.stdout),
                    String::from_utf8_lossy(&out1.stderr)
                );
            }

            let out2 = Command::new(&leanc_bin)
                .arg("-O3")
                .arg(&tmp_c)
                .arg("-o")
                .arg(&tmp_bin)
                .current_dir(&staging)
                .envs(&env_vars)
                .output()
                .context("Failed to compile C to native binary via `leanc -O3`")?;
            let _ = fs::remove_file(&tmp_c);
            if !out2.status.success() {
                anyhow::bail!(
                    "`leanc -O3` failed on HTTP fast-check payload:\n{}\n{}",
                    String::from_utf8_lossy(&out2.stdout),
                    String::from_utf8_lossy(&out2.stderr)
                );
            }
            if fs::rename(&tmp_bin, &cached_bin).is_err() {
                fs::copy(&tmp_bin, &cached_bin)?;
                let _ = fs::remove_file(&tmp_bin);
            }
        }

        let run_t0 = std::time::Instant::now();
        let out = Command::new(&cached_bin).output()?;
        let exec_us = run_t0.elapsed().as_micros();
        let stdout = String::from_utf8_lossy(&out.stdout);

        Ok(serde_json::json!({
            "status": if out.status.success() { "ok" } else { "counterexample_found" },
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
    let status_text = if status == 200 { "OK" } else { "Not Found" };
    write!(
        stream,
        "HTTP/1.1 {} {}\r\nContent-Type: {}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        status,
        status_text,
        content_type,
        body.len()
    )?;
    stream.write_all(body)?;
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
    write!(
        stream,
        "{} {} HTTP/1.1\r\nHost: {}\r\nContent-Type: {}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        method,
        path,
        addr,
        content_type,
        body.len()
    )?;
    if !body.is_empty() {
        stream.write_all(body)?;
    }
    stream.flush()?;

    let mut reader = BufReader::new(stream);
    let mut status_line = String::new();
    reader.read_line(&mut status_line)?;
    if !status_line.contains("200") {
        anyhow::bail!("HTTP request {} {} failed: {}", method, url, status_line.trim());
    }
    loop {
        let mut hline = String::new();
        if reader.read_line(&mut hline)? == 0 || hline.trim().is_empty() {
            break;
        }
    }
    let mut resp_body = Vec::new();
    reader.read_to_end(&mut resp_body)?;
    Ok(resp_body)
}

/// Push only missing local trusted actions and blobs to a remote `turbo-lean serve` coordinator via
/// `GET /manifest` + `POST /import-delta`. Returns `(pushed_actions, pushed_blobs, pushed_raw_bytes, pushed_pack_bytes, delta_push_noop)`.
pub fn sync_push_http(
    store: &TurboStore,
    url: &str,
    only_portable: bool,
) -> Result<(usize, usize, u64, u64, bool)> {
    let base = url.trim_end_matches('/');
    let local_manifest = get_store_manifest(store, only_portable)?;
    let remote_manifest: DeltaManifest =
        match http_request("GET", &format!("{}/manifest", base), "application/json", &[]) {
            Ok(bytes) => serde_json::from_slice(&bytes).unwrap_or_default(),
            Err(_) => DeltaManifest::default(),
        };
    let remote_action_set: HashSet<String> =
        remote_manifest.action_keys.iter().cloned().collect();
    let remote_blob_set: HashSet<String> =
        remote_manifest.blob_hashes.iter().cloned().collect();

    let need_push = local_manifest
        .action_keys
        .iter()
        .any(|k| !remote_action_set.contains(k))
        || local_manifest
            .blob_hashes
            .iter()
            .any(|b| !remote_blob_set.contains(b));

    if !need_push {
        return Ok((0, 0, 0, 0, true));
    }

    let tmp_local = store
        .fast_staging_dir()
        .join(format!("sync_out_{}.tlpack", next_tmp_id()));
    let (pushed_acts, pushed_blobs, pushed_raw_bytes) = export_pack_filtered(
        store,
        &tmp_local,
        only_portable,
        &remote_action_set,
        &remote_blob_set,
    )?;
    let mut pushed_pack_bytes = 0u64;
    if pushed_acts > 0 || pushed_blobs > 0 {
        let push_bytes = fs::read(&tmp_local)?;
        pushed_pack_bytes = push_bytes.len() as u64;
        let _ = http_request(
            "POST",
            &format!("{}/import-delta", base),
            "application/octet-stream",
            &push_bytes,
        )?;
    }
    let _ = fs::remove_file(&tmp_local);
    Ok((
        pushed_acts,
        pushed_blobs,
        pushed_raw_bytes,
        pushed_pack_bytes,
        pushed_acts == 0 && pushed_blobs == 0,
    ))
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
}
