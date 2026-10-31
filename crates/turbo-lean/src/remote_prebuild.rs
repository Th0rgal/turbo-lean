//! Remote prebuild client (`POST /v1/prebuilds` + poll `GET /v1/prebuilds/:id` + SHA-256 verified artifact stream).
//!
//! Normalizes base or full endpoint URLs cleanly so callers can pass either `https://example.org`
//! or `https://example.org/v1/prebuilds`, requires explicit target modules and `manifest_sha256`
//! (computed automatically from `lake-manifest.json` or `lakefile.toml` / `lakefile.lean`), and
//! returns structured `ready`, `compile_failed`, or `fallback` results.

use crate::pack::{encode_hex_bytes, http_request_full, http_request_full_anonymous};
use anyhow::Result;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RemotePrebuildRequest {
    pub repo_url: String,
    pub commit_sha: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub toolchain: Option<String>,
    pub manifest_sha256: String,
    pub targets: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub artifact_format: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub export_declarations: Vec<String>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct RemotePrebuildResponse {
    #[serde(default)]
    pub job_id: Option<String>,
    #[serde(default)]
    pub status: String,
    #[serde(default)]
    pub status_url: Option<String>,
    #[serde(default)]
    pub artifact_url: Option<String>,
    #[serde(default)]
    pub artifact_sha256: Option<String>,
    #[serde(default)]
    pub artifact_size_bytes: Option<u64>,
    #[serde(default)]
    pub failing_module: Option<String>,
    #[serde(default)]
    pub error: Option<String>,
    #[serde(default)]
    pub elapsed_ms: Option<u64>,
}

/// Normalizes a coordinator URL to its `/v1/prebuilds` endpoint if only a base origin was supplied,
/// while preserving explicit paths (such as `/v1/prebuilds` or custom test paths) verbatim.
pub fn resolve_prebuilds_endpoint_url(raw_url: &str) -> String {
    let trimmed = raw_url.trim().trim_end_matches('/');
    if let Some(scheme_sep) = trimmed.find("://") {
        let after_scheme = &trimmed[scheme_sep + 3..];
        if !after_scheme.contains('/') {
            return format!("{trimmed}/v1/prebuilds");
        }
    }
    trimmed.to_string()
}

/// Computes a deterministic 64-hex SHA-256 manifest digest for the Lean project.
/// Uses `lake-manifest.json` verbatim when present (matching remote coordinator verification),
/// falling back to `lakefile.toml` or `lakefile.lean` if no `lake-manifest.json` exists.
pub fn compute_project_manifest_sha256(project_dir: &Path) -> Option<String> {
    if let Ok(bytes) = fs::read(project_dir.join("lake-manifest.json")) {
        return Some(encode_hex_bytes(&Sha256::digest(&bytes)));
    }
    for fallback in ["lakefile.toml", "lakefile.lean"] {
        if let Ok(bytes) = fs::read(project_dir.join(fallback)) {
            return Some(encode_hex_bytes(&Sha256::digest(&bytes)));
        }
    }
    None
}

fn is_valid_commit_sha40(sha: &str) -> bool {
    let s = sha.trim();
    s.len() == 40 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

fn detect_git_repo_and_head(project_dir: &Path) -> (Option<String>, Option<String>) {
    let env_repo = std::env::var("GITHUB_SERVER_URL")
        .ok()
        .zip(std::env::var("GITHUB_REPOSITORY").ok())
        .filter(|(s, r)| !s.trim().is_empty() && !r.trim().is_empty())
        .map(|(s, r)| format!("{}/{}.git", s.trim_end_matches('/'), r.trim()));
    let repo = env_repo.or_else(|| {
        Command::new("git")
            .args(["config", "--get", "remote.origin.url"])
            .current_dir(project_dir)
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
            .filter(|s| !s.is_empty())
    });
    let head = std::env::var("GITHUB_SHA")
        .ok()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .or_else(|| {
            Command::new("git")
                .args(["rev-parse", "HEAD"])
                .current_dir(project_dir)
                .output()
                .ok()
                .filter(|o| o.status.success())
                .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
                .filter(|s| !s.is_empty())
        });
    (repo, head)
}

/// `(scheme, host, port)` of an `http(s)` URL with default ports resolved and the host lowercased.
/// Returns `None` for other schemes, userinfo, backslashes, or malformed authorities so callers
/// fail closed.
fn url_origin(url: &str) -> Option<(String, String, u16)> {
    let (scheme, rest) = url.trim().split_once("://")?;
    let scheme = scheme.to_ascii_lowercase();
    let default_port = match scheme.as_str() {
        "http" => 80,
        "https" => 443,
        _ => return None,
    };
    let authority = rest.split(['/', '?', '#']).next()?;
    if authority.contains(['@', '\\']) {
        return None;
    }
    let (host, port_part) = if authority.starts_with('[') {
        let end = authority.find(']')? + 1;
        authority.split_at(end)
    } else {
        authority
            .find(':')
            .map_or((authority, ""), |i| authority.split_at(i))
    };
    let port = match port_part.strip_prefix(':') {
        Some(p) => p.parse::<u16>().ok()?,
        None if port_part.is_empty() => default_port,
        None => return None,
    };
    let host = host.to_ascii_lowercase();
    (!host.is_empty()).then_some((scheme, host, port))
}

/// True when both URLs are `http(s)` and share scheme, host, and port.
fn same_origin(a: &str, b: &str) -> bool {
    matches!((url_origin(a), url_origin(b)), (Some(x), Some(y)) if x == y)
}

/// Paths from `git status --porcelain=v1 -z --untracked-files=all`: every tracked change and every
/// untracked file, since any of them can be a build input the remote commit lacks (ignored files
/// are not reported by git and so are not covered).
fn dirty_paths_from_porcelain(porcelain_z: &[u8]) -> Vec<String> {
    let mut entries = porcelain_z.split(|&b| b == 0).filter(|e| !e.is_empty());
    let mut dirty = Vec::new();
    while let Some(entry) = entries.next() {
        let entry = String::from_utf8_lossy(entry);
        let (Some(xy), Some(path)) = (entry.get(..2), entry.get(3..)) else {
            continue;
        };
        if xy.starts_with(['R', 'C']) || xy.ends_with(['R', 'C']) {
            entries.next();
        }
        dirty.push(path.to_string());
    }
    dirty
}

/// Ways the local checkout under `project_dir` differs from the commit `selected_sha` that the
/// remote will build (uncommitted paths, or a `HEAD` on another commit); empty when it is not a git
/// work tree.
fn working_tree_dirty_paths(project_dir: &Path, selected_sha: &str) -> Result<Vec<String>> {
    let git = |args: &[&str]| {
        Command::new("git")
            .args(args)
            .current_dir(project_dir)
            .output()
    };
    let inside = git(&["rev-parse", "--is-inside-work-tree"])
        .ok()
        .filter(|o| o.status.success())
        .is_some_and(|o| String::from_utf8_lossy(&o.stdout).trim() == "true");
    if !inside {
        return Ok(Vec::new());
    }
    let out = git(&[
        "status",
        "--porcelain=v1",
        "-z",
        "--untracked-files=all",
        "--ignore-submodules=none",
        "--",
        ".",
    ])?;
    if !out.status.success() {
        anyhow::bail!(
            "`git status` failed: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    let mut dirty = dirty_paths_from_porcelain(&out.stdout);
    let head = git(&["rev-parse", "HEAD"])
        .ok()
        .filter(|o| o.status.success())
        .map(|o| {
            String::from_utf8_lossy(&o.stdout)
                .trim()
                .to_ascii_lowercase()
        });
    if let Some(head) = head.filter(|h| !selected_sha.is_empty() && h != selected_sha) {
        dirty.push(format!(
            "HEAD is {head} but the selected commit is {selected_sha}"
        ));
    }
    Ok(dirty)
}

/// Refuses a dirty tree unless `allow_dirty`; returns the dirty paths to report when allowed.
fn dirty_tree_decision(dirty: Vec<String>, allow_dirty: bool) -> Result<Vec<String>, String> {
    if dirty.is_empty() || allow_dirty {
        return Ok(dirty);
    }
    Err(format!(
        "local checkout differs from the commit the remote will build ({}); the result would not \
         describe this tree. Commit/check out the commit or pass --allow-dirty to accept the mismatch",
        dirty.join(", ")
    ))
}

fn stream_download_with_sha256(
    url: &str,
    output_path: &Path,
    expected_sha256: Option<&str>,
    timeout_ms: u64,
    max_bytes: u64,
) -> Result<(u64, String)> {
    if let Some(parent) = output_path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)?;
        }
    }
    let tmp_path = output_path.with_extension("part");
    let result: Result<(u64, String)> = (|| {
        let mut out_file = fs::File::create(&tmp_path)?;
        let mut hasher = Sha256::new();
        let mut total_bytes: u64 = 0;

        if url.starts_with("https://") {
            let agent = ureq::AgentBuilder::new()
                .timeout_connect(Duration::from_millis(timeout_ms.clamp(500, 10_000)))
                .timeout(Duration::from_millis(timeout_ms.max(5_000)))
                .redirects(0)
                .build();
            let resp = agent
                .get(url)
                .call()
                .map_err(|e| anyhow::anyhow!("artifact download {} failed: {}", url, e))?;
            if resp.status() != 200 {
                anyhow::bail!("artifact download {} returned HTTP {}", url, resp.status());
            }
            let mut reader = resp.into_reader().take(max_bytes.saturating_add(1));
            let mut buf = [0u8; 64 * 1024];
            loop {
                let n = reader.read(&mut buf)?;
                if n == 0 {
                    break;
                }
                total_bytes = total_bytes.saturating_add(n as u64);
                if total_bytes > max_bytes {
                    anyhow::bail!(
                        "downloaded artifact from {} exceeded {} byte limit",
                        url,
                        max_bytes
                    );
                }
                hasher.update(&buf[..n]);
                out_file.write_all(&buf[..n])?;
            }
        } else if url.starts_with("http://") {
            // `url` is server-supplied: never attach ambient credentials.
            let body = http_request_full_anonymous(
                "GET",
                url,
                "application/octet-stream",
                &[],
                Some(timeout_ms.max(5_000)),
                None,
                || {},
            )?;
            total_bytes = body.len() as u64;
            if total_bytes > max_bytes {
                anyhow::bail!(
                    "downloaded artifact from {} exceeded {} byte limit",
                    url,
                    max_bytes
                );
            }
            hasher.update(&body);
            out_file.write_all(&body)?;
        } else {
            anyhow::bail!("unsupported artifact URL scheme: {}", url);
        }

        out_file.sync_all()?;
        drop(out_file);
        let actual_hex = encode_hex_bytes(&hasher.finalize());
        if let Some(exp) = expected_sha256.map(str::trim).filter(|s| !s.is_empty()) {
            if !actual_hex.eq_ignore_ascii_case(exp) {
                anyhow::bail!(
                    "artifact SHA-256 mismatch: expected {}, got {}",
                    exp,
                    actual_hex
                );
            }
        }
        fs::rename(&tmp_path, output_path)?;
        Ok((total_bytes, actual_hex))
    })();
    if result.is_err() {
        let _ = fs::remove_file(&tmp_path);
    }
    result
}

#[allow(clippy::too_many_arguments)]
pub fn run_remote_prebuild_command(
    json_mode: bool,
    endpoint_url: &str,
    project_dir: &Path,
    repo_url: Option<String>,
    commit_sha: Option<String>,
    targets: Vec<String>,
    artifact_format: Option<String>,
    output_path: Option<PathBuf>,
    token: Option<String>,
    timeout_secs: u64,
    poll_interval_ms: u64,
    allow_dirty: bool,
) -> Result<()> {
    let started = Instant::now();
    let deadline = started + Duration::from_secs(timeout_secs.max(1));
    let resolved_endpoint = resolve_prebuilds_endpoint_url(endpoint_url);
    let resolved_token = token
        .filter(|s| !s.trim().is_empty())
        .or_else(|| {
            std::env::var("TURBO_LEAN_REMOTE_TOKEN")
                .ok()
                .filter(|s| !s.trim().is_empty())
        })
        .or_else(|| {
            std::env::var("TURBO_LEAN_API_TOKEN")
                .ok()
                .filter(|s| !s.trim().is_empty())
        });

    let (auto_repo, auto_sha) = detect_git_repo_and_head(project_dir);
    let final_repo = repo_url
        .filter(|s| !s.trim().is_empty())
        .or(auto_repo)
        .unwrap_or_default();
    let final_sha = commit_sha
        .filter(|s| !s.trim().is_empty())
        .or(auto_sha)
        .unwrap_or_default()
        .to_ascii_lowercase();
    let normalized_targets: Vec<String> = targets
        .into_iter()
        .flat_map(|t| {
            t.split(|c: char| c == ',' || c.is_ascii_whitespace())
                .map(str::trim)
                .filter(|s| !s.is_empty())
                .map(ToOwned::to_owned)
                .collect::<Vec<_>>()
        })
        .collect();

    // The remote builds a commit, so uncommitted local changes are refused unless `--allow-dirty`;
    // `accepted_dirty` is non-empty only when they were knowingly accepted.
    let dirty_decision = working_tree_dirty_paths(project_dir, &final_sha)
        .map_err(|e| e.to_string())
        .and_then(|dirty| dirty_tree_decision(dirty, allow_dirty));
    let accepted_dirty = dirty_decision.clone().unwrap_or_default();
    let emit_result = |mut payload: serde_json::Value| -> Result<()> {
        if !accepted_dirty.is_empty() {
            payload["working_tree_dirty"] = serde_json::json!(true);
            payload["dirty_paths"] = serde_json::json!(accepted_dirty);
            payload["warning"] =
                serde_json::json!("result describes the remote commit, not the local checkout");
        }
        if json_mode {
            println!("{}", serde_json::to_string_pretty(&payload)?);
        } else {
            let status = payload
                .get("status")
                .and_then(|v| v.as_str())
                .unwrap_or("fallback");
            let detail = payload
                .get("error")
                .or_else(|| payload.get("failing_module"))
                .or_else(|| payload.get("output_path"))
                .and_then(|v| v.as_str())
                .unwrap_or("");
            println!("[turbo-lean remote-prebuild] status={} {}", status, detail);
        }
        Ok(())
    };

    if final_repo.is_empty() || !is_valid_commit_sha40(&final_sha) {
        return emit_result(serde_json::json!({
            "status": "fallback",
            "error": "missing repository URL or valid 40-hex commit SHA for remote-prebuild",
            "elapsed_ms": started.elapsed().as_millis() as u64,
        }));
    }

    if let Err(error) = dirty_decision {
        return emit_result(serde_json::json!({
            "status": "fallback",
            "error": error,
            "elapsed_ms": started.elapsed().as_millis() as u64,
        }));
    }

    if normalized_targets.is_empty() {
        return emit_result(serde_json::json!({
            "status": "fallback",
            "error": "at least one explicit target module is required (--targets)",
            "elapsed_ms": started.elapsed().as_millis() as u64,
        }));
    }

    let Some(manifest_sha256) = compute_project_manifest_sha256(project_dir) else {
        return emit_result(serde_json::json!({
            "status": "fallback",
            "error": "unable to compute manifest_sha256 (missing lake-manifest.json or lakefile)",
            "elapsed_ms": started.elapsed().as_millis() as u64,
        }));
    };

    let toolchain = fs::read_to_string(project_dir.join("lean-toolchain"))
        .ok()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty());

    let req_payload = RemotePrebuildRequest {
        repo_url: final_repo,
        commit_sha: final_sha,
        toolchain,
        manifest_sha256,
        targets: normalized_targets,
        artifact_format,
        export_declarations: Vec::new(),
    };
    let req_bytes = serde_json::to_vec(&req_payload)?;
    let rem_ms = || -> u64 {
        deadline
            .saturating_duration_since(Instant::now())
            .as_millis() as u64
    };

    let submit_bytes = match http_request_full(
        "POST",
        &resolved_endpoint,
        "application/json",
        &req_bytes,
        Some(rem_ms().clamp(1_000, 30_000)),
        resolved_token.as_deref(),
        None,
        || {},
    ) {
        Ok(b) => b,
        Err(e) => {
            return emit_result(serde_json::json!({
                "status": "fallback",
                "error": e.to_string(),
                "elapsed_ms": started.elapsed().as_millis() as u64,
            }));
        }
    };

    let mut cur: RemotePrebuildResponse = match serde_json::from_slice(&submit_bytes) {
        Ok(r) => r,
        Err(e) => {
            return emit_result(serde_json::json!({
                "status": "fallback",
                "error": format!("invalid remote-prebuild JSON response: {}", e),
                "elapsed_ms": started.elapsed().as_millis() as u64,
            }));
        }
    };

    let poll_url = cur.status_url.clone().or_else(|| {
        cur.job_id
            .as_ref()
            .map(|id| format!("{}/{}", resolved_endpoint.trim_end_matches('/'), id))
    });

    while matches!(
        cur.status.as_str(),
        "queued" | "running" | "pending" | "building"
    ) {
        if Instant::now() >= deadline {
            return emit_result(serde_json::json!({
                "status": "fallback",
                "job_id": cur.job_id,
                "error": format!("remote-prebuild timed out after {}s", timeout_secs),
                "elapsed_ms": started.elapsed().as_millis() as u64,
            }));
        }
        std::thread::sleep(Duration::from_millis(poll_interval_ms.clamp(100, 5_000)));
        let Some(ref s_url) = poll_url else {
            return emit_result(serde_json::json!({
                "status": "fallback",
                "job_id": cur.job_id,
                "error": "remote-prebuild job is non-terminal without status_url or job_id",
                "elapsed_ms": started.elapsed().as_millis() as u64,
            }));
        };
        // `status_url` is server-supplied: never send credentials to another origin.
        if !same_origin(&resolved_endpoint, s_url) {
            return emit_result(serde_json::json!({
                "status": "fallback",
                "job_id": cur.job_id,
                "error": format!(
                    "refusing to poll status_url {} outside the configured endpoint origin {}",
                    s_url, resolved_endpoint
                ),
                "elapsed_ms": started.elapsed().as_millis() as u64,
            }));
        }
        let poll_bytes = match http_request_full(
            "GET",
            s_url,
            "application/json",
            &[],
            Some(rem_ms().clamp(1_000, 15_000)),
            resolved_token.as_deref(),
            None,
            || {},
        ) {
            Ok(b) => b,
            Err(e) => {
                return emit_result(serde_json::json!({
                    "status": "fallback",
                    "job_id": cur.job_id,
                    "error": e.to_string(),
                    "elapsed_ms": started.elapsed().as_millis() as u64,
                }));
            }
        };
        cur = match serde_json::from_slice(&poll_bytes) {
            Ok(r) => r,
            Err(e) => {
                return emit_result(serde_json::json!({
                    "status": "fallback",
                    "job_id": cur.job_id,
                    "error": format!("invalid poll JSON response: {}", e),
                    "elapsed_ms": started.elapsed().as_millis() as u64,
                }));
            }
        };
    }

    match cur.status.as_str() {
        "ready" | "completed" => {
            if let (Some(ref out_p), Some(ref a_url)) = (&output_path, &cur.artifact_url) {
                match stream_download_with_sha256(
                    a_url,
                    out_p,
                    cur.artifact_sha256.as_deref(),
                    rem_ms().max(5_000),
                    512 * 1024 * 1024,
                ) {
                    Ok((dl_bytes, sha_hex)) => emit_result(serde_json::json!({
                        "status": "ready",
                        "job_id": cur.job_id,
                        "output_path": out_p.to_string_lossy(),
                        "artifact_sha256": sha_hex,
                        "artifact_size_bytes": dl_bytes,
                        "elapsed_ms": started.elapsed().as_millis() as u64,
                    })),
                    Err(e) => emit_result(serde_json::json!({
                        "status": "fallback",
                        "job_id": cur.job_id,
                        "error": e.to_string(),
                        "elapsed_ms": started.elapsed().as_millis() as u64,
                    })),
                }
            } else {
                emit_result(serde_json::json!({
                    "status": "ready",
                    "job_id": cur.job_id,
                    "artifact_url": cur.artifact_url,
                    "artifact_sha256": cur.artifact_sha256,
                    "artifact_size_bytes": cur.artifact_size_bytes,
                    "elapsed_ms": started.elapsed().as_millis() as u64,
                }))
            }
        }
        "compile_failed" => emit_result(serde_json::json!({
            "status": "compile_failed",
            "job_id": cur.job_id,
            "failing_module": cur.failing_module,
            "error": cur.error,
            "elapsed_ms": started.elapsed().as_millis() as u64,
        })),
        _ => emit_result(serde_json::json!({
            "status": "fallback",
            "job_id": cur.job_id,
            "error": cur.error.unwrap_or_else(|| format!("remote-prebuild returned status `{}`", cur.status)),
            "elapsed_ms": started.elapsed().as_millis() as u64,
        })),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::TcpListener;

    #[test]
    fn resolves_base_origin_to_v1_prebuilds_and_preserves_explicit_paths() {
        assert_eq!(
            resolve_prebuilds_endpoint_url("https://coordinator.example.org"),
            "https://coordinator.example.org/v1/prebuilds"
        );
        assert_eq!(
            resolve_prebuilds_endpoint_url("https://coordinator.example.org/"),
            "https://coordinator.example.org/v1/prebuilds"
        );
        assert_eq!(
            resolve_prebuilds_endpoint_url("https://coordinator.example.org/v1/prebuilds"),
            "https://coordinator.example.org/v1/prebuilds"
        );
    }

    #[test]
    fn remote_prebuild_posts_v1_prebuilds_with_manifest_sha256_and_verifies_artifact() -> Result<()>
    {
        let tmp = std::env::temp_dir().join(format!(
            "turbo_lean_remote_prebuild_v1_test_{}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&tmp);
        fs::create_dir_all(&tmp)?;
        fs::write(tmp.join("lean-toolchain"), "leanprover/lean4:v4.33.1\n")?;
        let manifest_bytes = b"{\"version\": 1, \"packages\": []}\n";
        fs::write(tmp.join("lake-manifest.json"), manifest_bytes)?;
        let expected_manifest_sha = encode_hex_bytes(&Sha256::digest(manifest_bytes));

        let artifact_bytes = b"Solution -- TheoremExport\n";
        let artifact_sha = encode_hex_bytes(&Sha256::digest(artifact_bytes));

        let listener = TcpListener::bind("127.0.0.1:0")?;
        let addr = listener.local_addr()?;
        let sha_for_srv = artifact_sha.clone();
        let manifest_for_srv = expected_manifest_sha.clone();
        let srv = std::thread::spawn(move || {
            for step in 0..5 {
                if let Ok((mut sock, _)) = listener.accept() {
                    let mut rbuf = [0u8; 4096];
                    let n = sock.read(&mut rbuf).unwrap_or(0);
                    let req = String::from_utf8_lossy(&rbuf[..n]);
                    let body = match step {
                        0 => {
                            assert!(req.contains("POST /v1/prebuilds "));
                            assert!(req.contains("Authorization: Bearer test-secret-tok"));
                            assert!(req.contains(&manifest_for_srv));
                            assert!(req.contains("\"targets\":[\"Solution\"]"));
                            format!(
                                "{{\"job_id\":\"j1\",\"status\":\"queued\",\"status_url\":\"http://{}/v1/prebuilds/j1\"}}",
                                addr
                            )
                            .into_bytes()
                        }
                        1 => {
                            assert!(req.contains("GET /v1/prebuilds/j1 "));
                            format!(
                                "{{\"job_id\":\"j1\",\"status\":\"ready\",\"artifact_url\":\"http://{}/blob/j1\",\"artifact_sha256\":\"{}\",\"artifact_size_bytes\":{}}}",
                                addr,
                                sha_for_srv,
                                artifact_bytes.len()
                            )
                            .into_bytes()
                        }
                        2 => {
                            assert!(req.contains("GET /blob/j1 "));
                            artifact_bytes.to_vec()
                        }
                        3 => b"{\"job_id\":\"j2\",\"status\":\"compile_failed\",\"failing_module\":\"Candidate.Bad\",\"error\":\"type mismatch\"}".to_vec(),
                        _ => format!(
                            "{{\"job_id\":\"j3\",\"status\":\"ready\",\"artifact_url\":\"http://{}/blob/j3\",\"artifact_sha256\":\"0000000000000000000000000000000000000000000000000000000000000000\"}}",
                            addr
                        )
                        .into_bytes(),
                    };
                    let hdr = format!(
                        "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                        body.len()
                    );
                    let _ = sock.write_all(hdr.as_bytes());
                    let _ = sock.write_all(&body);
                }
            }
        });

        // Passing only the base origin auto-targets `/v1/prebuilds`
        let out_file = tmp.join("out").join("solution.export.zst");
        run_remote_prebuild_command(
            true,
            &format!("http://{}", addr),
            &tmp,
            Some("https://example.invalid/repo.git".to_string()),
            Some("deadbeefdeadbeefdeadbeefdeadbeefdeadbeef".to_string()),
            vec!["Solution".to_string()],
            Some("export.zst".to_string()),
            Some(out_file.clone()),
            Some("test-secret-tok".to_string()),
            10,
            100,
            false,
        )?;
        assert_eq!(fs::read(&out_file)?, artifact_bytes);

        // Compile failure path
        run_remote_prebuild_command(
            true,
            &format!("http://{}/v1/prebuilds", addr),
            &tmp,
            Some("https://example.invalid/repo.git".to_string()),
            Some("deadbeefdeadbeefdeadbeefdeadbeefdeadbeef".to_string()),
            vec!["Solution".to_string()],
            None,
            None,
            Some("test-secret-tok".to_string()),
            10,
            100,
            false,
        )?;

        // Tampered SHA-256 fallback path
        let tampered_out = tmp.join("out").join("tampered.export.zst");
        run_remote_prebuild_command(
            true,
            &format!("http://{}/v1/prebuilds", addr),
            &tmp,
            Some("https://example.invalid/repo.git".to_string()),
            Some("deadbeefdeadbeefdeadbeefdeadbeefdeadbeef".to_string()),
            vec!["Solution".to_string()],
            None,
            Some(tampered_out.clone()),
            Some("test-secret-tok".to_string()),
            10,
            100,
            false,
        )?;
        assert!(!tampered_out.exists());

        let _ = srv.join();
        let _ = fs::remove_dir_all(&tmp);
        Ok(())
    }

    #[test]
    fn origin_match_requires_scheme_host_and_port() {
        let base = "https://Coordinator.example.org/v1/prebuilds";
        assert!(same_origin(
            base,
            "https://coordinator.example.org:443/v1/prebuilds/j1"
        ));
        assert!(same_origin("http://127.0.0.1:80/x", "http://127.0.0.1/y"));
        assert!(same_origin(
            "http://[::1]:9400/a",
            "http://[::1]:9400/b?q=1"
        ));
        for other in [
            "https://evil.example/v1/prebuilds/j1",
            "https://coordinator.example.org.evil.example/x",
            "https://coordinator.example.org:8443/x",
            "http://coordinator.example.org/x",
            "https://coordinator.example.org@evil.example/x",
            "https://evil.example\\@coordinator.example.org/x",
            "https://coordinator.example.org:/x",
            "ftp://coordinator.example.org/x",
            "/v1/prebuilds/j1",
        ] {
            assert!(!same_origin(base, other), "{other}");
        }
    }

    #[test]
    fn porcelain_dirty_paths_cover_every_tracked_and_untracked_change() {
        let z = b" M A.lean\0A  new.lean\0R  moved.lean\0old.lean\0?? Extra.lean\0?? notes.txt\0?? out/a.bin\0";
        assert_eq!(
            dirty_paths_from_porcelain(z),
            [
                "A.lean",
                "new.lean",
                "moved.lean",
                "Extra.lean",
                "notes.txt",
                "out/a.bin"
            ]
        );
        assert!(dirty_paths_from_porcelain(b"").is_empty());
    }

    #[test]
    fn dirty_tree_is_refused_unless_explicitly_allowed() {
        let dirty = vec!["A.lean".to_string()];
        let err = dirty_tree_decision(dirty.clone(), false).unwrap_err();
        assert!(err.contains("A.lean") && err.contains("--allow-dirty"));
        assert_eq!(dirty_tree_decision(dirty.clone(), true), Ok(dirty));
        assert_eq!(dirty_tree_decision(Vec::new(), false), Ok(Vec::new()));
    }

    fn git_ok(dir: &Path, args: &[&str]) {
        let st = Command::new("git")
            .args(["-c", "user.email=t@t", "-c", "user.name=t"])
            .args(args)
            .current_dir(dir)
            .status()
            .unwrap();
        assert!(st.success(), "git {args:?}");
    }

    fn git_out(dir: &Path, args: &[&str]) -> String {
        let out = Command::new("git")
            .args(args)
            .current_dir(dir)
            .output()
            .unwrap();
        String::from_utf8_lossy(&out.stdout).trim().to_string()
    }

    #[test]
    fn working_tree_dirty_paths_tracks_real_git_state() -> Result<()> {
        let tmp = std::env::temp_dir().join(format!("turbo_lean_rp_dirty_{}", std::process::id()));
        let _ = fs::remove_dir_all(&tmp);
        fs::create_dir_all(&tmp)?;
        git_ok(&tmp, &["init", "-q"]);
        fs::write(tmp.join("A.lean"), "def a := 1\n")?;
        git_ok(&tmp, &["add", "."]);
        git_ok(&tmp, &["commit", "-q", "-m", "init"]);
        let head = git_out(&tmp, &["rev-parse", "HEAD"]);
        assert!(working_tree_dirty_paths(&tmp, &head)?.is_empty());
        fs::write(tmp.join("native.c"), "x")?;
        assert_eq!(working_tree_dirty_paths(&tmp, &head)?, ["native.c"]);
        fs::remove_file(tmp.join("native.c"))?;
        fs::write(tmp.join("A.lean"), "def a := 2\n")?;
        assert_eq!(working_tree_dirty_paths(&tmp, &head)?, ["A.lean"]);
        git_ok(&tmp, &["checkout", "-q", "A.lean"]);
        // A clean checkout on a commit other than the one the remote will build is a mismatch.
        let other = "0".repeat(40);
        let mismatch = working_tree_dirty_paths(&tmp, &other)?;
        assert_eq!(mismatch.len(), 1);
        assert!(mismatch[0].contains(&head) && mismatch[0].contains(&other));
        // Dirty submodules stay visible even when the repo config hides them.
        let sub = std::env::temp_dir().join(format!("turbo_lean_rp_sub_{}", std::process::id()));
        let _ = fs::remove_dir_all(&sub);
        fs::create_dir_all(&sub)?;
        git_ok(&sub, &["init", "-q"]);
        fs::write(sub.join("S.lean"), "def s := 1\n")?;
        git_ok(&sub, &["add", "."]);
        git_ok(&sub, &["commit", "-q", "-m", "sub"]);
        git_ok(
            &tmp,
            &[
                "-c",
                "protocol.file.allow=always",
                "submodule",
                "add",
                "-q",
                sub.to_str().unwrap(),
                "dep",
            ],
        );
        git_ok(&tmp, &["commit", "-q", "-m", "add dep"]);
        git_ok(&tmp, &["config", "submodule.dep.ignore", "all"]);
        let head = git_out(&tmp, &["rev-parse", "HEAD"]);
        assert!(working_tree_dirty_paths(&tmp, &head)?.is_empty());
        fs::write(tmp.join("dep").join("S.lean"), "def s := 2\n")?;
        assert_eq!(working_tree_dirty_paths(&tmp, &head)?, ["dep"]);
        let _ = fs::remove_dir_all(&tmp);
        let _ = fs::remove_dir_all(&sub);
        Ok(())
    }

    #[test]
    fn remote_prebuild_never_polls_or_sends_token_to_foreign_status_url() -> Result<()> {
        let tmp =
            std::env::temp_dir().join(format!("turbo_lean_rp_xorigin_{}", std::process::id()));
        let _ = fs::remove_dir_all(&tmp);
        fs::create_dir_all(&tmp)?;
        fs::write(tmp.join("lake-manifest.json"), "{}")?;
        let coordinator = TcpListener::bind("127.0.0.1:0")?;
        let coordinator_addr = coordinator.local_addr()?;
        let foreign = TcpListener::bind("127.0.0.1:0")?;
        foreign.set_nonblocking(true)?;
        let foreign_addr = foreign.local_addr()?;
        let srv = std::thread::spawn(move || {
            let (mut sock, _) = coordinator.accept().unwrap();
            let mut rbuf = [0u8; 4096];
            let _ = sock.read(&mut rbuf);
            let body = format!(
                "{{\"job_id\":\"j1\",\"status\":\"queued\",\"status_url\":\"http://{foreign_addr}/steal\"}}"
            );
            let _ = write!(
                sock,
                "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
                body.len()
            );
        });
        run_remote_prebuild_command(
            true,
            &format!("http://{coordinator_addr}"),
            &tmp,
            Some("https://example.invalid/repo.git".to_string()),
            Some("deadbeefdeadbeefdeadbeefdeadbeefdeadbeef".to_string()),
            vec!["Solution".to_string()],
            None,
            None,
            Some("test-secret-tok".to_string()),
            10,
            100,
            false,
        )?;
        srv.join().unwrap();
        let err = foreign
            .accept()
            .expect_err("foreign origin must never be contacted");
        assert_eq!(err.kind(), std::io::ErrorKind::WouldBlock);
        let _ = fs::remove_dir_all(&tmp);
        Ok(())
    }
}
