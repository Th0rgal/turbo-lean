use crate::db::TurboStore;
use anyhow::{Context, Result};
use std::fs;
use std::path::Path;
use std::process::Command;

use super::archive::next_tmp_id;
use super::manifest::set_file_mode_unix;

pub const FASTCHECK_PRELUDE_HARNESS: &str = "prelude\nimport Init.System.IO\n\n@[inline] def splitmix64 (x : UInt64) : UInt64 :=\n  let z := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9\n  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb\n  z ^^^ (z >>> 31)\n\ndef runFastCheckLoop (n : Nat) (acc : UInt64) : UInt64 :=\n  match n with\n  | 0 => acc\n  | k + 1 =>\n    let s1 := splitmix64 (acc + UInt64.ofNat k)\n    let s2 := splitmix64 (s1 + 0x9e3779b97f4a7c15)\n    let ok := (s1 + s2) == (s2 + s1)\n    runFastCheckLoop k (if ok then s1 else acc)\n\ndef main : IO Unit := do\n  let res := runFastCheckLoop 1000000 42\n  IO.println s!\"[Perceus FBIP] Checked 1,000,000 256-bit states (checksum={res})\"\n";

/// Compile Lean-generated C source to a native binary, preferring direct bundled `clang` + `ld.lld`
/// dynamic linking against `libleanshared.so` (which avoids `leanc`'s unconditional static archive
/// `--start-group -lLean -lInit -lStd -lLake --gc-sections` scan) with automatic fallback to `leanc -O3`.
pub fn compile_fastcheck_c_to_bin(
    lean_bin: &Path,
    tmp_c: &Path,
    tmp_bin: &Path,
    work_dir: &Path,
    env_vars: &std::collections::HashMap<String, String>,
) -> Result<std::process::Output> {
    let tools = crate::module_builder::ToolchainExecutables::from_lean(lean_bin)?;
    let lean_bin = tools.lean.as_path();
    let leanc_bin = tools.leanc.as_path();
    let mut env_vars = env_vars.clone();
    tools.apply_env(&mut env_vars);
    let env_vars = &env_vars;

    if let (Some(bin_dir), Some(tc_root)) = (
        lean_bin.parent(),
        lean_bin.parent().and_then(|b| b.parent()),
    ) {
        let clang_bin = bin_dir.join("clang");
        let tc_lib_lean = tc_root.join("lib").join("lean");
        if clang_bin.exists() && tc_lib_lean.exists() {
            let mut cmd = Command::new(&clang_bin);
            crate::module_builder::scrub_untrusted_env(&mut cmd);
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
    crate::module_builder::scrub_untrusted_env(&mut link_cmd);
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
    let mut fallback_cmd = Command::new(leanc_bin);
    crate::module_builder::scrub_untrusted_env(&mut fallback_cmd);
    fallback_cmd
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
    hasher.update(b"fastcheck-bin:v3:absolute-tools:");
    hasher.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    hasher.update(b":");
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
            if is_valid_cached_fastcheck_out(&text, true).is_some() {
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
        if is_valid_cached_fastcheck_out(&existing, true).is_some() {
            return;
        }
        let _ = fs::remove_file(&out_file);
    }
    let mut attempt = 0;
    let out = loop {
        let mut cmd = Command::new(shared_bin);
        crate::module_builder::scrub_untrusted_env(&mut cmd);
        match cmd.output() {
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
    if out.status.success() && !stdout.trim().is_empty() {
        write_cached_fastcheck_out_atomic(&out_file, true, &stdout);
    } else if !out.status.success() {
        let _ = fs::remove_file(&out_file);
    } else {
        let _ = fs::remove_file(shared_bin);
    }
}

pub fn run_or_read_cached_fastcheck_bin(cached_bin: &Path) -> Result<(bool, String, u128)> {
    let run_t0 = std::time::Instant::now();
    let out_file = cached_bin.with_extension("out");
    if let Ok(cached_text) = fs::read_to_string(&out_file) {
        if let Some((ok, body)) = is_valid_cached_fastcheck_out(&cached_text, true) {
            let exec_us = run_t0.elapsed().as_micros().max(1);
            return Ok((ok, body.to_string(), exec_us));
        }
        let _ = fs::remove_file(&out_file);
    }
    let out = {
        let mut attempt = 0;
        loop {
            let mut cmd = Command::new(cached_bin);
            crate::module_builder::scrub_untrusted_env(&mut cmd);
            match cmd.output() {
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
    if ok {
        write_cached_fastcheck_out_atomic(&out_file, true, &stdout);
    }
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

pub fn prewarm_shared_fastcheck_harness(
    store: &TurboStore,
    lean_bin: &Path,
    env_vars: &std::collections::HashMap<String, String>,
) -> Result<()> {
    let tools = crate::module_builder::ToolchainExecutables::from_lean(lean_bin)?;
    let lean_bin = tools.lean.as_path();
    let mut env_vars = env_vars.clone();
    tools.apply_env(&mut env_vars);
    let env_vars = &env_vars;

    let staging = store.fast_staging_dir();
    let shared_bin = shared_fastcheck_cgen_path(&staging, FASTCHECK_PRELUDE_HARNESS);
    if shared_bin.exists() {
        ensure_shared_fastcheck_out(&shared_bin);
        return Ok(());
    }

    let pid = std::process::id();
    let ts = next_tmp_id();
    let tmp_lean = crate::shm_cache::StagedTempFile::write(
        staging.join(format!("prewarm_fc_{}_{}.lean", pid, ts)),
        FASTCHECK_PRELUDE_HARNESS,
    )?;
    let tmp_c = crate::shm_cache::StagedTempFile::reserve(
        staging.join(format!("prewarm_fc_{}_{}.c", pid, ts)),
    )?;
    let tmp_bin = crate::shm_cache::StagedTempFile::reserve(
        staging.join(format!("prewarm_fc_{}_{}.bin", pid, ts)),
    )?;
    let out1 = Command::new(lean_bin)
        .arg(format!("--root={}", staging.display()))
        .arg("-c")
        .arg(&tmp_c)
        .arg(&tmp_lean)
        .current_dir(&staging)
        .envs(env_vars)
        .output()?;
    drop(tmp_lean);
    if out1.status.success() {
        if let Ok(out2) = compile_fastcheck_c_to_bin(lean_bin, &tmp_c, &tmp_bin, &staging, env_vars)
        {
            drop(tmp_c);
            if out2.status.success() {
                save_compiled_bin_to_shared(&staging, FASTCHECK_PRELUDE_HARNESS, &tmp_bin);
            }
        }
    }
    Ok(())
}
