use crate::db::{ActionRecord, BlobEntry, TurboStore};
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

pub fn export_pack(
    store: &TurboStore,
    output_path: &Path,
    only_portable: bool,
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
            needed_blobs.insert((o.blob_hash.clone(), o.kind.clone()));
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

    let mut blobs = Vec::new();
    let mut total_raw_bytes = 0u64;
    for (bh, kind) in needed_blobs {
        let p = store.blob_path(&bh);
        if p.exists() {
            let bytes = fs::read(&p)?;
            total_raw_bytes += bytes.len() as u64;
            blobs.push(PackedBlob {
                blob_hash: bh,
                portable: is_portable_artifact(&kind, ""),
                kind,
                size_bytes: bytes.len() as u64,
                data_hex_or_base64: bytes,
            });
        }
    }

    let manifest = PackManifest {
        format_version: 1,
        host_arch: std::env::consts::ARCH.to_string(),
        created_at: crate::db::now_unix(),
        actions,
        blobs,
    };

    let json_bytes = serde_json::to_vec(&manifest)?;
    let tmp_json = output_path.with_extension("json.tmp");
    fs::write(&tmp_json, &json_bytes)?;

    // Compress with zstd if available, otherwise write raw JSON
    let zstd_status = Command::new("zstd")
        .args([
            "-q",
            "-f",
            "-3",
            tmp_json.to_str().unwrap_or(""),
            "-o",
            output_path.to_str().unwrap_or(""),
        ])
        .status();

    let _ = fs::remove_file(&tmp_json);
    if zstd_status.map(|s| !s.success()).unwrap_or(true) {
        fs::write(output_path, &json_bytes)?;
    }

    Ok((
        manifest.actions.len(),
        manifest.blobs.len(),
        total_raw_bytes,
    ))
}

pub fn import_pack(store: &mut TurboStore, input_path: &Path) -> Result<(usize, usize)> {
    let tmp_json = input_path.with_extension("import.json.tmp");
    let decompressed = Command::new("zstd")
        .args([
            "-q",
            "-d",
            "-f",
            input_path.to_str().unwrap_or(""),
            "-o",
            tmp_json.to_str().unwrap_or(""),
        ])
        .status();

    let json_bytes = if decompressed.map(|s| s.success()).unwrap_or(false) && tmp_json.exists() {
        let b = fs::read(&tmp_json)?;
        let _ = fs::remove_file(&tmp_json);
        b
    } else {
        fs::read(input_path)?
    };

    let manifest: PackManifest =
        serde_json::from_slice(&json_bytes).context("Failed to parse PackManifest")?;

    let mut imported_blobs = 0usize;
    for b in &manifest.blobs {
        // Re-verify BLAKE3 digest of every incoming blob (Zero-Trust transport rule!)
        let actual_hash = blake3::hash(&b.data_hex_or_base64).to_hex().to_string();
        if actual_hash != b.blob_hash {
            anyhow::bail!(
                "BLAKE3 integrity check failed on imported blob: expected {}, got {}",
                b.blob_hash,
                actual_hash
            );
        }
        store.store_immutable_blob(&b.data_hex_or_base64, &b.kind, "trusted", 0)?;
        imported_blobs += 1;
    }

    let mut imported_actions = 0usize;
    let tx = store.conn.transaction()?;
    let now = crate::db::now_unix();
    for act in &manifest.actions {
        tx.execute(
            "INSERT INTO actions (action_key, toolchain_githash, kind, status, fencing_token,
                                  output_manifest_hash, duration_ms, peak_pss_bytes, heartbeats, trust_domain, updated_at)
             VALUES (?1, ?2, ?3, 'completed', ?4, ?5, ?6, ?7, ?8, 'trusted', ?9)
             ON CONFLICT(action_key) DO UPDATE SET
                status = 'completed',
                output_manifest_hash = excluded.output_manifest_hash,
                updated_at = excluded.updated_at",
            params![
                act.action_key,
                act.toolchain_githash,
                act.kind,
                act.fencing_token,
                act.output_manifest_hash,
                act.duration_ms,
                act.peak_pss_bytes,
                act.heartbeats,
                now
            ],
        )?;
        for out in &act.outputs {
            tx.execute(
                "INSERT OR REPLACE INTO action_outputs (action_key, rel_path, blob_hash)
                 VALUES (?1, ?2, ?3)",
                params![act.action_key, out.rel_path, out.blob_hash],
            )?;
        }
        imported_actions += 1;
    }
    tx.commit()?;

    Ok((imported_actions, imported_blobs))
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
            ("GET", "/export") => {
                let tmp = store.root.join("staging").join("http_export.tlpack");
                let _ = export_pack(&store, &tmp, true)?;
                let bytes = fs::read(&tmp).unwrap_or_default();
                let _ = fs::remove_file(&tmp);
                write_http_response(&mut stream, 200, "application/octet-stream", &bytes)?;
            }
            ("POST", "/import") => {
                let tmp = store.root.join("staging").join("http_import.tlpack");
                fs::write(&tmp, &body)?;
                let (acts, blobs) = import_pack(&mut store, &tmp)?;
                let _ = fs::remove_file(&tmp);
                let payload = serde_json::to_vec(&serde_json::json!({
                    "ok": true,
                    "imported_actions": acts,
                    "imported_blobs": blobs
                }))?;
                write_http_response(&mut stream, 200, "application/json", &payload)?;
            }
            _ => {
                write_http_response(&mut stream, 404, "application/json", b"{\"error\":\"not_found\"}")?;
            }
        }
    }
    Ok(())
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
