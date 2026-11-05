use crate::db::{BlobEntry, SingleflightOutcome, TurboStore};
use crate::pack::{export_pack_with_filter_and_signing_key, ExportInclusionFilter};
use anyhow::{Context, Result};
use clap::Args;
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;
use walkdir::WalkDir;

const DEFAULT_TARGET: &str = "x86_64";
const DEFAULT_INPUT: &str = "canonical";
const SUPPORTED_TARGETS: [&str; 4] = ["x86_64", "arm64", "cuda_ptx", "apple_metal"];

#[derive(Debug, Clone, Args)]
pub struct SuperoptEvolveArgs {
    #[arg(long, default_value = DEFAULT_TARGET)]
    pub target: String,

    #[arg(long)]
    pub generations: Option<usize>,

    #[arg(long)]
    pub seed: Option<u64>,

    #[arg(long)]
    pub bundle_out: Option<PathBuf>,

    #[arg(long)]
    pub pack_out: Option<PathBuf>,

    #[arg(long, default_value = DEFAULT_INPUT)]
    pub input: PathBuf,
}

#[derive(Debug, Clone)]
pub struct PackExportSummary {
    pub action_key: String,
    pub exported_actions: usize,
    pub exported_blobs: usize,
    pub raw_bytes: u64,
    pub archive: PathBuf,
}

struct TempBundleGuard(PathBuf);

impl TempBundleGuard {
    fn new(store: &TurboStore) -> Result<Self> {
        let dir = store.root.join("staging").join(format!(
            "superopt_evolve_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir)
            .with_context(|| format!("Failed to create temporary bundle dir {}", dir.display()))?;
        Ok(Self(dir))
    }

    fn bundle_path(&self) -> PathBuf {
        self.0.join("bundle.json")
    }
}

impl Drop for TempBundleGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

pub fn normalize_superopt_target(raw: &str) -> Result<&'static str> {
    match raw.trim() {
        "x86_64" => Ok("x86_64"),
        "arm64" => Ok("arm64"),
        "cuda_ptx" => Ok("cuda_ptx"),
        "apple_metal" => Ok("apple_metal"),
        other => anyhow::bail!(
            "Unsupported superopt-evolve target '{}' (expected one of: {})",
            other,
            SUPPORTED_TARGETS.join(", ")
        ),
    }
}

pub fn build_helper_args(
    args: &SuperoptEvolveArgs,
    effective_bundle_out: Option<&Path>,
    json: bool,
) -> Result<Vec<String>> {
    let target = normalize_superopt_target(&args.target)?;
    let mut cmd_args = vec![
        "superopt-evolve".to_string(),
        "--target".to_string(),
        target.to_string(),
    ];
    if let Some(generations) = args.generations {
        cmd_args.push("--generations".to_string());
        cmd_args.push(generations.to_string());
    }
    if let Some(seed) = args.seed {
        cmd_args.push("--seed".to_string());
        cmd_args.push(seed.to_string());
    }
    if let Some(bundle_path) = effective_bundle_out.or(args.bundle_out.as_deref()) {
        cmd_args.push("--bundle-out".to_string());
        cmd_args.push(bundle_path.to_string_lossy().into_owned());
    }
    let input_str = args.input.to_string_lossy();
    let effective_input = if input_str.trim().is_empty() {
        DEFAULT_INPUT.to_string()
    } else {
        input_str.into_owned()
    };
    cmd_args.push("--input".to_string());
    cmd_args.push(effective_input);
    if json {
        cmd_args.push("--json".to_string());
    }
    Ok(cmd_args)
}

pub fn resolve_lean_native_core_bin() -> Result<PathBuf> {
    if let Ok(raw) = std::env::var("LEAN_NATIVE_CORE_BIN") {
        let trimmed = raw.trim();
        if !trimmed.is_empty() {
            let candidate = PathBuf::from(trimmed);
            anyhow::ensure!(
                candidate.is_file(),
                "LEAN_NATIVE_CORE_BIN points to missing file: {}",
                candidate.display()
            );
            return Ok(candidate);
        }
    }

    if let Some(path_os) = std::env::var_os("PATH") {
        for dir in std::env::split_paths(&path_os) {
            let candidate = dir.join("lean-native-core");
            if candidate.is_file() {
                return Ok(candidate);
            }
        }
    }

    if let Ok(exe) = std::env::current_exe() {
        if let Some(parent) = exe.parent() {
            let sibling = parent.join("lean-native-core");
            if sibling.is_file() {
                return Ok(sibling);
            }
        }
        for anc in exe.ancestors() {
            let candidate = anc
                .join("lean")
                .join(".lake")
                .join("build")
                .join("bin")
                .join("lean-native-core");
            if candidate.is_file() {
                return Ok(candidate);
            }
        }
    }

    if let Ok(cwd) = std::env::current_dir() {
        for anc in cwd.ancestors() {
            let candidate = anc
                .join("lean")
                .join(".lake")
                .join("build")
                .join("bin")
                .join("lean-native-core");
            if candidate.is_file() {
                return Ok(candidate);
            }
        }
    }

    anyhow::bail!(
        "Unable to locate lean-native-core binary (set LEAN_NATIVE_CORE_BIN or add it to PATH)"
    )
}

fn collect_bundle_artifacts(
    bundle_path: &Path,
    fallback_stdout: &[u8],
) -> Result<Vec<(String, Vec<u8>)>> {
    if fs::symlink_metadata(bundle_path).is_ok() {
        let resolved = fs::canonicalize(bundle_path).unwrap_or_else(|_| bundle_path.to_path_buf());
        if resolved.is_file() {
            let rel_name = bundle_path
                .file_name()
                .and_then(|s| s.to_str())
                .filter(|s| !s.is_empty() && *s != "." && *s != "..")
                .unwrap_or("superopt_bundle.json");
            let bytes = fs::read(&resolved)
                .with_context(|| format!("Failed to read bundle {}", resolved.display()))?;
            return Ok(vec![(format!("superopt_evolve/{}", rel_name), bytes)]);
        }
        if resolved.is_dir() {
            let mut entries = Vec::new();
            for entry in WalkDir::new(&resolved).follow_links(false) {
                let entry = entry?;
                if entry.file_type().is_file() {
                    let rel = entry
                        .path()
                        .strip_prefix(&resolved)
                        .unwrap_or_else(|_| entry.path())
                        .to_string_lossy()
                        .replace('\\', "/");
                    let clean_rel = rel.trim_start_matches('/');
                    if clean_rel.is_empty() || clean_rel.starts_with('.') {
                        continue;
                    }
                    let bytes = fs::read(entry.path())?;
                    entries.push((format!("superopt_evolve/{}", clean_rel), bytes));
                }
            }
            entries.sort_by(|a, b| a.0.cmp(&b.0));
            if !entries.is_empty() {
                return Ok(entries);
            }
        }
    }

    if !fallback_stdout.is_empty()
        && serde_json::from_slice::<serde_json::Value>(fallback_stdout).is_ok()
    {
        return Ok(vec![(
            "superopt_evolve/report.json".to_string(),
            fallback_stdout.to_vec(),
        )]);
    }

    anyhow::bail!(
        "lean-native-core superopt-evolve did not materialize bundle output at {}",
        bundle_path.display()
    )
}

pub fn export_bundle_to_pack(
    store: &mut TurboStore,
    args: &SuperoptEvolveArgs,
    artifacts: &[(String, Vec<u8>)],
    duration_ms: i64,
    pack_out: &Path,
) -> Result<PackExportSummary> {
    anyhow::ensure!(
        !artifacts.is_empty(),
        "Cannot export empty superopt-evolve bundle to {}",
        pack_out.display()
    );
    let target = normalize_superopt_target(&args.target)?;
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-lean:superopt-evolve:v1\0");
    hasher.update(target.as_bytes());
    hasher.update(b"\0");
    if let Some(g) = args.generations {
        hasher.update(g.to_string().as_bytes());
    }
    hasher.update(b"\0");
    if let Some(s) = args.seed {
        hasher.update(s.to_string().as_bytes());
    }
    hasher.update(b"\0");
    hasher.update(args.input.to_string_lossy().as_bytes());
    hasher.update(b"\0");

    let mut staged_items = Vec::with_capacity(artifacts.len());
    for (rel_path, bytes) in artifacts {
        let bh = blake3::hash(bytes).to_hex().to_string();
        hasher.update(rel_path.as_bytes());
        hasher.update(b":");
        hasher.update(bh.as_bytes());
        hasher.update(b"\n");
        staged_items.push((
            bh,
            bytes.clone(),
            "receipt".to_string(),
            rel_path.clone(),
            bytes.len() as u64,
        ));
    }
    let action_key = format!("superopt_evolve_{}", hasher.finalize().to_hex());
    let blob_entries: Vec<BlobEntry> =
        store.batch_store_immutable_blobs(&staged_items, "trusted", 0)?;

    match store.acquire_singleflight(
        &action_key,
        "lean-native-core",
        "superopt_evolve",
        "trusted",
    )? {
        SingleflightOutcome::Leader(lease) => {
            store.publish_action(&lease, &blob_entries, duration_ms, 0, 0, "trusted")?;
        }
        SingleflightOutcome::CacheHit { .. } => {}
    }

    if let Some(parent) = pack_out.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent).with_context(|| {
                format!(
                    "Failed to create parent directory for pack output {}",
                    pack_out.display()
                )
            })?;
        }
    }

    let mut allowed_actions = HashSet::new();
    allowed_actions.insert(action_key.clone());
    let filter = ExportInclusionFilter {
        allowed_actions: Some(allowed_actions),
        allowed_replay_modules: Some(HashSet::new()),
        allowed_replay_artifact_digests: Some(HashSet::new()),
    };

    let (exported_actions, exported_blobs, raw_bytes) = export_pack_with_filter_and_signing_key(
        store,
        pack_out,
        true,
        &HashSet::new(),
        &HashSet::new(),
        Some(&filter),
        None,
    )?;

    Ok(PackExportSummary {
        action_key,
        exported_actions,
        exported_blobs,
        raw_bytes,
        archive: pack_out.to_path_buf(),
    })
}

pub fn run_superopt_evolve_command(
    store: &mut TurboStore,
    json: bool,
    args: SuperoptEvolveArgs,
) -> Result<()> {
    let target = normalize_superopt_target(&args.target)?;
    let helper_bin = resolve_lean_native_core_bin()?;

    if let Some(ref bundle_out) = args.bundle_out {
        if let Some(parent) = bundle_out.parent() {
            if !parent.as_os_str().is_empty() {
                fs::create_dir_all(parent).with_context(|| {
                    format!(
                        "Failed to create parent directory for bundle output {}",
                        bundle_out.display()
                    )
                })?;
            }
        }
    }

    let temp_bundle = if args.pack_out.is_some() && args.bundle_out.is_none() {
        Some(TempBundleGuard::new(store)?)
    } else {
        None
    };
    let effective_bundle_path = args
        .bundle_out
        .clone()
        .or_else(|| temp_bundle.as_ref().map(TempBundleGuard::bundle_path));

    let helper_json = json || args.pack_out.is_some();
    let helper_args = build_helper_args(&args, effective_bundle_path.as_deref(), helper_json)?;

    let t0 = Instant::now();
    let mut command = Command::new(&helper_bin);
    command.args(&helper_args);
    if matches!(
        std::env::var("TURBO_LEAN_TELEMETRY")
            .unwrap_or_default()
            .trim()
            .to_ascii_lowercase()
            .as_str(),
        "0" | "off" | "false" | "no" | "none" | "disable" | "disabled"
    ) {
        command.env("LEAN_NATIVE_TELEMETRY", "off");
    }

    let output = command.output().with_context(|| {
        format!(
            "Failed to execute {} {}",
            helper_bin.display(),
            helper_args.join(" ")
        )
    })?;
    let duration_ms = t0.elapsed().as_millis() as i64;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let detail = if !stderr.trim().is_empty() {
            stderr.trim()
        } else {
            stdout.trim()
        };
        anyhow::bail!(
            "lean-native-core superopt-evolve failed (exit {:?}): {}",
            output.status.code(),
            detail
        );
    }

    let pack_summary = if let Some(ref pack_out) = args.pack_out {
        let bundle_path = effective_bundle_path
            .as_deref()
            .context("Internal error: missing bundle path for --pack-out")?;
        let artifacts = collect_bundle_artifacts(bundle_path, &output.stdout)?;
        Some(export_bundle_to_pack(
            store,
            &args,
            &artifacts,
            duration_ms,
            pack_out,
        )?)
    } else {
        None
    };

    let stdout_str = String::from_utf8_lossy(&output.stdout);
    if json {
        let mut payload = match serde_json::from_str::<serde_json::Value>(stdout_str.trim()) {
            Ok(serde_json::Value::Object(map)) => serde_json::Value::Object(map),
            Ok(other) => serde_json::json!({
                "status": "ok",
                "target": target,
                "result": other,
            }),
            Err(_) => serde_json::json!({
                "status": "ok",
                "target": target,
                "stdout": stdout_str.trim(),
            }),
        };
        if let Some(obj) = payload.as_object_mut() {
            if let Some(ref bundle_out) = args.bundle_out {
                obj.entry("bundle_out".to_string())
                    .or_insert_with(|| serde_json::Value::String(bundle_out.display().to_string()));
            }
            if let Some(ref summary) = pack_summary {
                obj.insert(
                    "pack_out".to_string(),
                    serde_json::Value::String(summary.archive.display().to_string()),
                );
                obj.insert(
                    "pack_export".to_string(),
                    serde_json::json!({
                        "action_key": summary.action_key,
                        "exported_actions": summary.exported_actions,
                        "exported_blobs": summary.exported_blobs,
                        "raw_bytes": summary.raw_bytes,
                        "archive": summary.archive.display().to_string(),
                    }),
                );
            }
        }
        println!("{}", serde_json::to_string_pretty(&payload)?);
    } else {
        let trimmed = stdout_str.trim_end();
        if !trimmed.is_empty() {
            println!("{}", trimmed);
        }
        if let Some(ref summary) = pack_summary {
            println!(
                "[turbo-lean] Exported superopt-evolve bundle ({} actions, {} blobs, {} bytes) to {}",
                summary.exported_actions,
                summary.exported_blobs,
                summary.raw_bytes,
                summary.archive.display()
            );
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pack::import_pack_with_policy;
    use std::sync::Mutex;

    static ENV_LOCK: Mutex<()> = Mutex::new(());

    fn unique_test_dir(label: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "turbo_superopt_evolve_{}_{}_{}",
            label,
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[cfg(unix)]
    fn write_mock_helper(dir: &Path, body: &str) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let path = dir.join("mock-lean-native-core");
        fs::write(&path, body).unwrap();
        let mut perms = fs::metadata(&path).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&path, perms).unwrap();
        path
    }

    #[test]
    fn test_normalize_superopt_target_and_helper_args_defaults() {
        for valid in SUPPORTED_TARGETS {
            assert_eq!(normalize_superopt_target(valid).unwrap(), valid);
        }
        assert!(normalize_superopt_target("riscv64").is_err());

        let args = SuperoptEvolveArgs {
            target: "cuda_ptx".to_string(),
            generations: None,
            seed: None,
            bundle_out: None,
            pack_out: Some(PathBuf::from("/tmp/ignored_by_helper.tlpack")),
            input: PathBuf::from("canonical"),
        };
        let built = build_helper_args(&args, None, false).unwrap();
        assert_eq!(
            built,
            vec![
                "superopt-evolve",
                "--target",
                "cuda_ptx",
                "--input",
                "canonical"
            ]
        );

        let with_all = SuperoptEvolveArgs {
            target: "apple_metal".to_string(),
            generations: Some(12),
            seed: Some(42),
            bundle_out: Some(PathBuf::from("/tmp/out_bundle.json")),
            pack_out: Some(PathBuf::from("/tmp/out.tlpack")),
            input: PathBuf::from("/tmp/sample.lnir"),
        };
        let built_all = build_helper_args(&with_all, None, true).unwrap();
        assert_eq!(
            built_all,
            vec![
                "superopt-evolve",
                "--target",
                "apple_metal",
                "--generations",
                "12",
                "--seed",
                "42",
                "--bundle-out",
                "/tmp/out_bundle.json",
                "--input",
                "/tmp/sample.lnir",
                "--json"
            ]
        );
        assert!(!built_all.iter().any(|a| a == "--pack-out"));
    }

    #[cfg(unix)]
    #[test]
    fn test_run_superopt_evolve_pack_export_and_import_roundtrip() {
        let _guard = ENV_LOCK.lock().unwrap();
        let dir = unique_test_dir("roundtrip");
        let args_log = dir.join("args.txt");
        let script = format!(
            "#!/bin/sh\nprintf '%s\\n' \"$@\" > \"{}\"\nbundle=\"\"\nprev=\"\"\nfor a in \"$@\"; do\n  if [ \"$prev\" = \"--bundle-out\" ]; then bundle=\"$a\"; fi\n  prev=\"$a\"\ndone\nif [ -n \"$bundle\" ]; then\n  printf '{{\"schema\":\"lean-native.superopt-evolve.v1\",\"rules\":[{{\"name\":\"xor_self_zero\",\"verified\":true}}]}}' > \"$bundle\"\nfi\nprintf '{{\"status\":\"evolved\",\"acceptedRules\":1,\"rejectedCandidates\":3}}\\n'\n",
            args_log.display()
        );
        let mock_bin = write_mock_helper(&dir, &script);
        let prev_bin = std::env::var_os("LEAN_NATIVE_CORE_BIN");
        std::env::set_var("LEAN_NATIVE_CORE_BIN", &mock_bin);

        let src_store_dir = dir.join("store_src");
        let dst_store_dir = dir.join("store_dst");
        let bundle_out = dir.join("certs").join("evolved_bundle.json");
        let pack_out = dir.join("packs").join("evolved.tlpack");

        let mut src_store = TurboStore::open(Some(&src_store_dir)).unwrap();
        let run_res = run_superopt_evolve_command(
            &mut src_store,
            true,
            SuperoptEvolveArgs {
                target: "arm64".to_string(),
                generations: Some(8),
                seed: Some(1337),
                bundle_out: Some(bundle_out.clone()),
                pack_out: Some(pack_out.clone()),
                input: PathBuf::from("canonical"),
            },
        );

        match prev_bin {
            Some(v) => std::env::set_var("LEAN_NATIVE_CORE_BIN", v),
            None => std::env::remove_var("LEAN_NATIVE_CORE_BIN"),
        }

        run_res.unwrap();
        assert!(bundle_out.is_file());
        assert!(pack_out.is_file());

        let logged: Vec<String> = fs::read_to_string(&args_log)
            .unwrap()
            .lines()
            .map(|s| s.to_string())
            .collect();
        assert_eq!(
            logged,
            vec![
                "superopt-evolve".to_string(),
                "--target".to_string(),
                "arm64".to_string(),
                "--generations".to_string(),
                "8".to_string(),
                "--seed".to_string(),
                "1337".to_string(),
                "--bundle-out".to_string(),
                bundle_out.display().to_string(),
                "--input".to_string(),
                "canonical".to_string(),
                "--json".to_string(),
            ]
        );

        let pack_bytes = fs::read(&pack_out).unwrap();
        assert!(pack_bytes.starts_with(b"TLPK\x00\x00\x00\x02"));

        let mut dst_store = TurboStore::open(Some(&dst_store_dir)).unwrap();
        let (imported_actions, imported_blobs) =
            import_pack_with_policy(&mut dst_store, &pack_out, Some("trusted"), None, true)
                .unwrap();
        assert_eq!(imported_actions, 1);
        assert_eq!(imported_blobs, 1);

        let _ = fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_run_superopt_evolve_pack_only_uses_temp_bundle_and_cleans_up() {
        let _guard = ENV_LOCK.lock().unwrap();
        let dir = unique_test_dir("pack_only");
        let bundle_seen = dir.join("bundle_seen.txt");
        let script = format!(
            "#!/bin/sh\nbundle=\"\"\nprev=\"\"\nfor a in \"$@\"; do\n  if [ \"$prev\" = \"--bundle-out\" ]; then bundle=\"$a\"; fi\n  prev=\"$a\"\ndone\nprintf '%s' \"$bundle\" > \"{}\"\nprintf '{{\"schema\":\"lean-native.superopt-evolve.v1\",\"certified\":true}}' > \"$bundle\"\nprintf '{{\"status\":\"evolved\",\"acceptedRules\":2}}\\n'\n",
            bundle_seen.display()
        );
        let mock_bin = write_mock_helper(&dir, &script);
        let prev_bin = std::env::var_os("LEAN_NATIVE_CORE_BIN");
        std::env::set_var("LEAN_NATIVE_CORE_BIN", &mock_bin);

        let store_dir = dir.join("store");
        let pack_out = dir.join("only_pack.tlpack");
        let mut store = TurboStore::open(Some(&store_dir)).unwrap();
        let res = run_superopt_evolve_command(
            &mut store,
            false,
            SuperoptEvolveArgs {
                target: "x86_64".to_string(),
                generations: None,
                seed: None,
                bundle_out: None,
                pack_out: Some(pack_out.clone()),
                input: PathBuf::from("canonical"),
            },
        );

        match prev_bin {
            Some(v) => std::env::set_var("LEAN_NATIVE_CORE_BIN", v),
            None => std::env::remove_var("LEAN_NATIVE_CORE_BIN"),
        }

        res.unwrap();
        assert!(pack_out.is_file());
        let seen_temp_bundle = PathBuf::from(fs::read_to_string(&bundle_seen).unwrap());
        assert!(!seen_temp_bundle.exists());

        let _ = fs::remove_dir_all(&dir);
    }
}
