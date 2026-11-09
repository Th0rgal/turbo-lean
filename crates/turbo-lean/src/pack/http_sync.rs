use crate::db::{now_unix, TurboStore};
use anyhow::{Context, Result};
use std::collections::HashSet;
use std::fs;
use std::io::{BufRead, BufReader, Read, Write};

use super::archive::{
    export_pack_filtered_bytes, export_pack_filtered_with_mode,
    export_pack_with_filter_and_signing_key, export_pack_with_filter_mode_and_signing_key,
    finish_import_from_prestaged_shared_cas_inner, import_pack_bytes_with_policy,
    import_pack_with_policy, ExportInclusionFilter, PrefetchedPackPrestage,
};
use super::manifest::{
    encode_hex_bytes, get_store_manifest, is_loopback_http_url, resolve_pack_import_trust_domain,
    CheckShardBatchItem, CheckShardsBatchRequest, CheckShardsBatchResponse, DeltaManifest,
    ExportDeltaRequest,
};

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
    http_request_full(method, url, content_type, body, None, None, None, || {})
}

fn http_request_with_expected_sha256(
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

#[allow(clippy::too_many_arguments)]
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
    let resolved_token = resolve_http_auth_token(url, auth_token);
    http_request_with_resolved_token(
        method,
        url,
        content_type,
        body,
        timeout_ms,
        resolved_token,
        expected_sha256,
        on_inflight,
    )
}

/// Like [`http_request_full`] but never attaches explicit or ambient (`TURBO_LEAN_*_TOKEN`)
/// credentials; for URLs supplied by an untrusted server.
pub fn http_request_full_anonymous(
    method: &str,
    url: &str,
    content_type: &str,
    body: &[u8],
    timeout_ms: Option<u64>,
    expected_sha256: Option<&str>,
    on_inflight: impl FnOnce(),
) -> Result<Vec<u8>> {
    http_request_with_resolved_token(
        method,
        url,
        content_type,
        body,
        timeout_ms,
        None,
        expected_sha256,
        on_inflight,
    )
}

#[allow(clippy::too_many_arguments)]
fn http_request_with_resolved_token(
    method: &str,
    url: &str,
    content_type: &str,
    body: &[u8],
    timeout_ms: Option<u64>,
    resolved_token: Option<String>,
    expected_sha256: Option<&str>,
    on_inflight: impl FnOnce(),
) -> Result<Vec<u8>> {
    use std::time::Duration;

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
    if reader.read_line(&mut status_line)? == 0 {
        return Err(std::io::Error::new(
            std::io::ErrorKind::UnexpectedEof,
            "EOF before HTTP response",
        )
        .into());
    }
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
#[cfg(test)]
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

/// Local attestation-cache key prefix for `offload_check_shards_batch_http` (attestation cache only, not a `srv-v9:` HTTP context receipt).
pub(crate) fn client_attested_receipt_key(shard_key: &str) -> String {
    format!("client-attested-v1:{shard_key}")
}

/// Offload a coalesced batch of uncached theorem shards to a remote `turbo-lean serve` coordinator
/// via `POST /check-shards-batch`. On `ok == true`, publishes local attestation-cache receipts
/// strictly for items verified against `resp.verified_decl_types` (never caller hashes).
#[allow(clippy::too_many_arguments)]
pub fn offload_check_shards_batch_http(
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
    let filtered_args = crate::module_builder::validate_effective_lean_args(lean_args)?;
    let args_digest_opt = crate::module_builder::compute_lean_args_digest(&filtered_args)?;
    let req = CheckShardsBatchRequest {
        items: items.to_vec(),
        coalesced_shard_source: coalesced_shard_source.to_string(),
        trust_domain: trust_domain.to_string(),
        toolchain: toolchain.to_string(),
        lean_path: lean_path.to_string(),
        allowed_axioms: Some(crate::splitter::extra_allowed_axiom_patterns()),
        lean_args: filtered_args,
    };
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
    let resp_bytes = http_request("POST", &url, "application/json", &serde_json::to_vec(&req)?)?;
    let resp: CheckShardsBatchResponse = serde_json::from_slice(&resp_bytes)?;

    if resp.ok {
        let expected_types: Vec<(String, String)> = items
            .iter()
            .filter_map(|i| {
                i.expected_kernel_type_hash
                    .as_ref()
                    .map(|k| (i.decl_name.clone(), k.clone()))
            })
            .collect();
        if !expected_types.is_empty() {
            crate::zygote::verify_attested_decl_types(&resp.verified_decl_types, &expected_types)
                .with_context(|| {
                format!(
                    "Remote batch coordinator `{url}` did not attest expected kernel statement types"
                )
            })?;
        }
        if !items.is_empty() && !resp.verified_decl_types.is_empty() {
            let now = now_unix();
            let per_shard_ms = ((resp.elapsed_ms as i64) / (items.len() as i64).max(1)).max(1);
            let publish_items: Vec<_> = items
                .iter()
                .filter_map(|item| {
                    let clean_decl = crate::splitter::canonicalize_lean_name(&item.decl_name);
                    if clean_decl.is_empty() {
                        return None;
                    }
                    let kth = match item.expected_kernel_type_hash.as_ref() {
                        Some(exp) => exp.clone(),
                        None => {
                            let mut m = resp
                                .verified_decl_types
                                .iter()
                                .filter(|(got, _)| {
                                    crate::splitter::matches_attested_decl_or_fast_verify(
                                        got,
                                        &item.decl_name,
                                    )
                                })
                                .map(|(_, h)| h);
                            let first = m.next()?;
                            if first.is_empty() || !m.all(|h| h == first) {
                                return None;
                            }
                            first.clone()
                        }
                    };
                    crate::zygote::verify_attested_decl_types(
                        &resp.verified_decl_types,
                        &[(item.decl_name.clone(), kth.clone())],
                    )
                    .ok()?;
                    let mut receipt_obj = serde_json::json!({
                        "decl": clean_decl,
                        "kernel_type_hash": kth,
                        "verified_at": now,
                        "scanner_version": crate::zygote::ZYGOTE_SCANNER_VERSION,
                        "replay_version": crate::zygote::ZYGOTE_REPLAY_VERSION
                    });
                    if let Some((ad, map)) =
                        args_digest_opt.as_ref().zip(receipt_obj.as_object_mut())
                    {
                        map.insert("lean_args_digest".into(), ad.clone().into());
                    }
                    Some((
                        client_attested_receipt_key(&item.shard_key),
                        clean_decl,
                        serde_json::to_vec(&receipt_obj).ok()?,
                        per_shard_ms,
                    ))
                })
                .collect();
            if !publish_items.is_empty() {
                store.batch_publish_theorem_shards(tc, td, &publish_items)?;
            }
        }
    }

    Ok(resp)
}

pub type PrefetchedExportItem = (Vec<u8>, Option<PrefetchedPackPrestage>);

pub fn resolve_remote_cache_url() -> Option<String> {
    std::env::var("TURBO_LEAN_REMOTE_CACHE")
        .ok()
        .map(|s| s.trim().trim_end_matches('/').to_string())
        .filter(|s| !s.is_empty())
}

pub fn resolve_remote_cache_token() -> Option<String> {
    std::env::var("TURBO_LEAN_REMOTE_TOKEN")
        .ok()
        .filter(|s| !s.trim().is_empty())
        .or_else(|| {
            std::env::var("TURBO_LEAN_API_TOKEN")
                .ok()
                .filter(|s| !s.trim().is_empty())
        })
}

pub fn fetch_remote_cache_manifest(
    base_url: &str,
    auth_token: Option<&str>,
) -> Result<DeltaManifest> {
    let base = base_url.trim_end_matches('/');
    let bytes = http_request_with_timeout_and_token(
        "GET",
        &format!("{}/manifest", base),
        "application/json",
        &[],
        Some(15_000),
        auth_token,
        || {},
    )?;
    let dm = serde_json::from_slice::<DeltaManifest>(&bytes)
        .context("Failed to parse remote cache `/manifest` JSON")?;
    Ok(dm)
}

pub fn try_pull_remote_module_action(
    store: &mut TurboStore,
    base_url: &str,
    auth_token: Option<&str>,
    remote_manifest: &mut Option<DeltaManifest>,
    wanted_action_keys: &[String],
    trust_domain: &str,
    is_untrusted: bool,
) -> Result<bool> {
    if wanted_action_keys.is_empty() {
        return Ok(false);
    }
    let base = base_url.trim_end_matches('/');
    if remote_manifest.is_none() {
        *remote_manifest = Some(fetch_remote_cache_manifest(base, auth_token)?);
    }
    let Some(ref dm) = remote_manifest else {
        return Ok(false);
    };
    let wanted_set: HashSet<&str> = wanted_action_keys.iter().map(|s| s.as_str()).collect();
    if !dm
        .action_keys
        .iter()
        .any(|k| wanted_set.contains(k.as_str()))
    {
        return Ok(false);
    }
    let exclude_actions: Vec<String> = dm
        .action_keys
        .iter()
        .filter(|k| !wanted_set.contains(k.as_str()))
        .cloned()
        .collect();
    let local_manifest = get_store_manifest(store, true).unwrap_or_default();
    let req_body = serde_json::to_vec(&ExportDeltaRequest {
        exclude_actions,
        exclude_blobs: local_manifest.blob_hashes,
    })?;
    let pack_bytes = http_request_with_timeout_and_token(
        "POST",
        &format!("{}/pull-delta", base),
        "application/json",
        &req_body,
        Some(30_000),
        auth_token,
        || {},
    )?;
    if pack_bytes.is_empty() {
        return Ok(false);
    }
    let requested_domain = if is_untrusted || trust_domain == "untrusted" {
        Some("untrusted")
    } else {
        Some("trusted")
    };
    let has_env_pubkey = std::env::var("TURBO_LEAN_PACK_TRUSTED_PUBKEY")
        .ok()
        .is_some_and(|s| !s.trim().is_empty());
    let allow_unattested_trusted = !is_untrusted && !has_env_pubkey;
    let (acts, blobs) = import_pack_bytes_with_policy(
        store,
        &pack_bytes,
        requested_domain,
        None,
        allow_unattested_trusted,
    )?;
    Ok(acts > 0 || blobs > 0)
}

#[allow(clippy::too_many_arguments)]
pub fn try_push_remote_module_action(
    store: &TurboStore,
    base_url: &str,
    auth_token: Option<&str>,
    remote_manifest: &mut Option<DeltaManifest>,
    mod_action_key: &str,
    mod_name: &str,
    artifact_digest_opt: Option<&str>,
    trust_domain: &str,
    is_untrusted: bool,
) -> Result<bool> {
    if is_untrusted || trust_domain != "trusted" {
        return Ok(false);
    }
    let base = base_url.trim_end_matches('/');
    if remote_manifest.is_none() {
        *remote_manifest = fetch_remote_cache_manifest(base, auth_token).ok();
    }
    let mut remote_blobs: HashSet<String> = HashSet::new();
    if let Some(ref dm) = remote_manifest {
        if dm.action_keys.iter().any(|k| k == mod_action_key) {
            return Ok(false);
        }
        remote_blobs.extend(dm.blob_hashes.iter().cloned());
    }
    let mut allowed_actions = HashSet::new();
    allowed_actions.insert(mod_action_key.to_string());
    let mut allowed_mods = HashSet::new();
    if !mod_name.is_empty() {
        allowed_mods.insert(mod_name.to_string());
    }
    let allowed_digs = artifact_digest_opt.map(|d| {
        let mut s = HashSet::new();
        s.insert(d.to_string());
        s
    });
    let filter = ExportInclusionFilter {
        allowed_actions: Some(allowed_actions),
        allowed_replay_modules: Some(allowed_mods),
        allowed_replay_artifact_digests: allowed_digs,
    };
    let (n_acts, n_blobs, _, pack_bytes) = export_pack_with_filter_mode_and_signing_key(
        store,
        true,
        &HashSet::new(),
        &remote_blobs,
        Some(&filter),
        false,
        None,
    )?;
    if n_acts == 0 && n_blobs == 0 {
        return Ok(false);
    }
    http_request_with_timeout_and_token(
        "POST",
        &format!("{}/import-delta", base),
        "application/octet-stream",
        &pack_bytes,
        Some(30_000),
        auth_token,
        || {},
    )?;
    if let Some(ref mut dm) = remote_manifest {
        if !dm.action_keys.iter().any(|k| k == mod_action_key) {
            dm.action_keys.push(mod_action_key.to_string());
        }
    }
    Ok(true)
}

/// Execute `turbo-lean export`.
pub fn run_export_command(
    store: &TurboStore,
    json: bool,
    output: std::path::PathBuf,
    portable_only: bool,
    signing_key: Option<String>,
    cone: Option<String>,
    project_dir: Option<std::path::PathBuf>,
) -> Result<()> {
    let cone_filter = if let Some(ref cone_target) = cone {
        let proj = match project_dir {
            Some(p) => p,
            None => {
                std::env::current_dir().context("Failed to resolve current working directory")?
            }
        };
        Some(crate::module_builder::build_cone_export_filter(
            store,
            &proj,
            cone_target,
        )?)
    } else {
        None
    };
    let (acts, blobs, bytes) = export_pack_with_filter_and_signing_key(
        store,
        &output,
        portable_only,
        &HashSet::new(),
        &HashSet::new(),
        cone_filter.as_ref(),
        signing_key.as_deref(),
    )?;
    if json {
        let mut obj = serde_json::json!({
            "exported_actions": acts,
            "exported_blobs": blobs,
            "raw_bytes": bytes,
            "archive": output.display().to_string()
        });
        if let Some(ref c) = cone {
            if let Some(map) = obj.as_object_mut() {
                map.insert("cone".to_string(), serde_json::Value::String(c.clone()));
            }
        }
        println!("{}", serde_json::to_string_pretty(&obj)?);
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
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
pub fn run_import_command(
    store: &mut TurboStore,
    json: bool,
    input: std::path::PathBuf,
    trust_domain: Option<String>,
    trusted_pubkey: Option<String>,
    allow_unattested_trusted: bool,
    expected_sha256: Option<String>,
    prefetched: Option<std::thread::JoinHandle<Option<PrefetchedPackPrestage>>>,
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
    } else if let Some((manifest, staged_blobs, newly_written, pub_guard)) =
        prefetched.and_then(|h| h.join().ok().flatten())
    {
        let td =
            resolve_pack_import_trust_domain(&manifest, req_td, pk_opt, allow_unattested_trusted)?;
        let res = finish_import_from_prestaged_shared_cas_inner(
            store,
            &manifest,
            &staged_blobs,
            newly_written,
            td,
            pk_opt,
            false,
        )?;
        drop(pub_guard);
        res
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
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
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
                        pulled = if let Some((manifest, staged_blobs, newly_written, pub_guard)) =
                            prestaged_opt
                        {
                            let td = resolve_pack_import_trust_domain(
                                &manifest,
                                req_td,
                                pk_opt,
                                allow_unattested_trusted,
                            )?;
                            let res = finish_import_from_prestaged_shared_cas_inner(
                                store,
                                &manifest,
                                &staged_blobs,
                                newly_written,
                                td,
                                pk_opt,
                                false,
                            )?;
                            drop(pub_guard);
                            res
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
