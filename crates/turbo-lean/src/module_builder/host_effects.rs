use super::*;

pub(crate) fn purge_elab_host_effect_artifacts_in_closure(
    cfg: &ProjectConfig,
    seeds: &[String],
) -> Result<bool> {
    let mut visited = HashSet::new();
    let mut postorder: Vec<DiscoveredModuleSpec> = Vec::new();
    let mut stack: Vec<(DiscoveredModuleSpec, bool)> = seeds
        .iter()
        .filter_map(|imp| {
            let site = match resolve_module_in_package(&cfg.root_pkg, true, imp) {
                Some(rs) => ImportSite::Module(Box::new(rs)),
                None => resolve_import_site(cfg, imp),
            };
            match site {
                ImportSite::Module(spec) => Some((*spec, false)),
                _ => None,
            }
        })
        .collect();
    while let Some((spec, expanded)) = stack.pop() {
        let key = (spec.pkg_root.clone(), spec.module_name.clone());
        if expanded {
            postorder.push(spec);
            continue;
        }
        if !visited.insert(key) {
            continue;
        }
        let sub_imps = fs::read_to_string(&spec.src_path)
            .ok()
            .map(|s| parse_header_info(&s))
            .filter(|h| h.header_error.is_none())
            .map(|h| h.imports)
            .unwrap_or_default();
        stack.push((spec, true));
        for sub in sub_imps {
            let site = match resolve_module_in_package(&cfg.root_pkg, true, &sub) {
                Some(rs) => ImportSite::Module(Box::new(rs)),
                None => resolve_import_site(cfg, &sub),
            };
            if let ImportSite::Module(sub_spec) = site {
                if !visited.contains(&(sub_spec.pkg_root.clone(), sub_spec.module_name.clone())) {
                    stack.push((*sub_spec, false));
                }
            }
        }
    }
    let mut tainted: HashSet<(PathBuf, String)> = HashSet::new();
    let mut purged_any = false;
    for spec in postorder {
        let Ok(src_raw) = fs::read_to_string(&spec.src_path) else {
            tainted.insert((spec.pkg_root.clone(), spec.module_name.clone()));
            crate::lake_build::remove_spec_build_artifacts_checked(&spec)?;
            purged_any = true;
            continue;
        };
        let hdr = parse_header_info(&src_raw);
        let imp_tainted = hdr.header_error.is_some()
            || hdr.imports.iter().any(|sub| {
                let site = match resolve_module_in_package(&cfg.root_pkg, true, sub) {
                    Some(rs) => ImportSite::Module(Box::new(rs)),
                    None => resolve_import_site(cfg, sub),
                };
                match site {
                    ImportSite::Module(sub_spec) => {
                        tainted.contains(&(sub_spec.pkg_root, sub_spec.module_name))
                    }
                    _ => false,
                }
            });
        if imp_tainted || spec_source_has_disallowed_elab_host_effects(cfg, &spec, &src_raw) {
            tainted.insert((spec.pkg_root.clone(), spec.module_name.clone()));
            crate::lake_build::remove_spec_build_artifacts_checked(&spec)?;
            purged_any = true;
        }
    }
    Ok(purged_any)
}

pub(crate) fn source_ineligible_for_stamp_reuse(
    cfg: &ProjectConfig,
    pkg_root: &Path,
    module_name: &str,
    src_path: &Path,
    src_raw: &str,
) -> bool {
    let Ok(pkg_root) = fs::canonicalize(pkg_root) else {
        return true;
    };
    crate::splitter::source_may_read_host_state(src_raw)
        || !std::iter::once(&cfg.root_pkg)
            .chain(cfg.dep_pkgs.iter())
            .find(|pkg| fs::canonicalize(&pkg.pkg_root).is_ok_and(|root| root == pkg_root))
            .is_some_and(|pkg| {
                module_includes_all_covered_by_lake_inputs(pkg, module_name, src_path, src_raw)
            })
}

pub(super) fn source_has_disallowed_elab_host_effects_for_module(
    cfg: &ProjectConfig,
    pkg_root: &Path,
    is_root_pkg: bool,
    is_git_pinned: bool,
    module_name: &str,
    src_path: &Path,
    src_raw: &str,
) -> bool {
    if source_ineligible_for_stamp_reuse(cfg, pkg_root, module_name, src_path, src_raw) {
        true
    } else if is_root_pkg {
        crate::splitter::source_has_disallowed_root_runtime_replacement_attribute(src_raw)
    } else if is_git_pinned {
        false
    } else {
        crate::splitter::source_may_execute_elab_host_effects(src_raw, false)
    }
}

pub(crate) fn spec_source_has_disallowed_elab_host_effects(
    cfg: &ProjectConfig,
    spec: &DiscoveredModuleSpec,
    src_raw: &str,
) -> bool {
    source_has_disallowed_elab_host_effects_for_module(
        cfg,
        &spec.pkg_root,
        spec.is_root_pkg,
        !spec.is_root_pkg && is_git_pinned_manifest_package(cfg, spec),
        &spec.module_name,
        &spec.src_path,
        src_raw,
    )
}

pub(crate) fn build_lean_search_path(cfg: &ProjectConfig, is_untrusted: bool) -> (String, String) {
    let mut lp_parts = Vec::new();
    let mut ld_parts = Vec::new();
    let push_unique = |vec: &mut Vec<String>, s: String| {
        if !s.is_empty() && !vec.contains(&s) {
            vec.push(s);
        }
    };
    let root_build = cfg.root_pkg.pkg_root.join(&cfg.root_pkg.build_dir);
    let root_lib_lean = root_build.join(&cfg.root_pkg.lean_lib_dir);
    let root_native_lib = root_build.join(&cfg.root_pkg.native_lib_dir);
    let root_lib = root_build.join("lib");
    push_unique(&mut lp_parts, root_lib_lean.to_string_lossy().to_string());
    push_unique(&mut ld_parts, root_native_lib.to_string_lossy().to_string());
    push_unique(&mut ld_parts, root_lib.to_string_lossy().to_string());
    push_unique(&mut ld_parts, root_lib_lean.to_string_lossy().to_string());
    for dp in &cfg.dep_pkgs {
        let dep_build = dp.pkg_root.join(&dp.build_dir);
        let dep_lib_lean = dep_build.join(&dp.lean_lib_dir);
        let dep_native_lib = dep_build.join(&dp.native_lib_dir);
        let dep_lib = dep_build.join("lib");
        push_unique(&mut lp_parts, dep_lib_lean.to_string_lossy().to_string());
        push_unique(&mut ld_parts, dep_native_lib.to_string_lossy().to_string());
        push_unique(&mut ld_parts, dep_lib.to_string_lossy().to_string());
        push_unique(&mut ld_parts, dep_lib_lean.to_string_lossy().to_string());
    }
    if !is_untrusted {
        if let Ok(caller_lp) = std::env::var("LEAN_PATH") {
            for part in caller_lp.split(':') {
                let trimmed = part.trim();
                if !trimmed.is_empty() && !lp_parts.iter().any(|p| p == trimmed) {
                    lp_parts.push(trimmed.to_string());
                }
            }
        }
    }
    let tc_lp = cfg.toolchain_lib_lean.to_string_lossy().to_string();
    if !lp_parts.contains(&tc_lp) {
        lp_parts.push(tc_lp.clone());
    }
    ld_parts.push(tc_lp);
    ld_parts.push(cfg.toolchain_lib.to_string_lossy().to_string());
    if !is_untrusted {
        if let Ok(orig_ld) = std::env::var("LD_LIBRARY_PATH") {
            if !orig_ld.trim().is_empty() {
                ld_parts.push(orig_ld);
            }
        }
    }
    (lp_parts.join(":"), ld_parts.join(":"))
}
pub(crate) fn scrub_untrusted_env(cmd: &mut Command) {
    for (k, _) in std::env::vars() {
        let ku = k.to_ascii_uppercase();
        if ku.contains("TOKEN")
            || ku.contains("SECRET")
            || ku.contains("KEY")
            || ku.contains("PASSWORD")
            || ku.contains("CREDENTIAL")
            || ku.starts_with("AWS_")
            || ku.starts_with("GH_")
            || ku.starts_with("GITHUB_")
            || ku.starts_with("GIT_")
            || ku.starts_with("OPENAI_")
            || ku.starts_with("ANTHROPIC_")
            || ku == "LEAN_SRC_PATH"
            || ku == "LAKE"
            || ku == "LAKE_HOME"
            || ku == "LD_PRELOAD"
            || ku == "LD_AUDIT"
            || ku == "DYLD_INSERT_LIBRARIES"
        {
            cmd.env_remove(&k);
        }
    }
}
pub(super) struct TempDirGuard(pub(super) PathBuf);
impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Typed timeout marker for `run_command_with_timeout*` so call sites can attribute a
/// timeout to the right knob by downcast instead of string matching (#437).
#[derive(Debug, Clone, Copy)]
pub(crate) struct CommandTimedOut {
    pub(crate) timeout: std::time::Duration,
}

impl std::fmt::Display for CommandTimedOut {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "`lean` command timed out after {}ms",
            self.timeout.as_millis()
        )
    }
}

impl std::error::Error for CommandTimedOut {}

pub(crate) fn run_command_with_timeout(
    cmd: &mut Command,
    timeout: std::time::Duration,
    is_untrusted: bool,
) -> Result<std::process::Output> {
    run_command_with_timeout_pinned_fd(cmd, timeout, is_untrusted, None)
}

pub(crate) fn run_command_with_timeout_pinned_fd(
    cmd: &mut Command,
    timeout: std::time::Duration,
    is_untrusted: bool,
    pinned_dir_raw_fd: Option<i32>,
) -> Result<std::process::Output> {
    #[cfg(target_os = "linux")]
    let _inherited_dir_fd: Option<std::os::unix::io::OwnedFd> = if !is_untrusted {
        if let Some(src_fd) = pinned_dir_raw_fd {
            use std::os::unix::io::FromRawFd;
            let dup_fd = unsafe { libc::fcntl(src_fd, libc::F_DUPFD_CLOEXEC, 32) };
            anyhow::ensure!(
                dup_fd >= 0,
                "Failed to duplicate pinned closure snapshot dir_fd {}: {}",
                src_fd,
                std::io::Error::last_os_error()
            );
            let owned = unsafe { std::os::unix::io::OwnedFd::from_raw_fd(dup_fd) };
            let cur_lp = cmd
                .get_envs()
                .find(|(k, _)| *k == std::ffi::OsStr::new("LEAN_PATH"))
                .and_then(|(_, v)| v.map(|s| s.to_string_lossy().to_string()))
                .unwrap_or_default();
            let new_lp = match cur_lp.split_once(':') {
                Some((_, rest)) if !rest.is_empty() => format!("/proc/self/fd/{dup_fd}:{rest}"),
                _ => format!("/proc/self/fd/{dup_fd}"),
            };
            cmd.env("LEAN_PATH", new_lp);
            Some(owned)
        } else {
            None
        }
    } else {
        None
    };
    #[cfg(not(target_os = "linux"))]
    let _ = pinned_dir_raw_fd;
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.process_group(0);
        #[cfg(target_os = "linux")]
        let child_keep_fd: Option<i32> = {
            use std::os::unix::io::AsRawFd;
            _inherited_dir_fd.as_ref().map(|f| f.as_raw_fd())
        };
        #[cfg(not(target_os = "linux"))]
        let child_keep_fd: Option<i32> = None;
        if is_untrusted || child_keep_fd.is_some() {
            unsafe {
                cmd.pre_exec(move || {
                    if let Some(fd) = child_keep_fd {
                        let flags = libc::fcntl(fd, libc::F_GETFD);
                        if flags < 0
                            || libc::fcntl(fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0
                        {
                            return Err(std::io::Error::last_os_error());
                        }
                    }
                    if is_untrusted {
                        for (res, lim) in [
                            (libc::RLIMIT_CORE, 0),
                            (libc::RLIMIT_DATA, 12 * 1024 * 1024 * 1024),
                            (libc::RLIMIT_FSIZE, 512 * 1024 * 1024),
                        ] {
                            let mut cur = std::mem::zeroed::<libc::rlimit>();
                            let capped = if libc::getrlimit(res, &mut cur) == 0
                                && cur.rlim_max != libc::RLIM_INFINITY
                                && cur.rlim_max < lim
                            {
                                cur.rlim_max
                            } else {
                                lim
                            };
                            let r = libc::rlimit {
                                rlim_cur: capped,
                                rlim_max: capped,
                            };
                            if libc::setrlimit(res, &r) != 0 {
                                return Err(std::io::Error::last_os_error());
                            }
                        }
                    }
                    Ok(())
                });
            }
        }
    }
    cmd.stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    let mut child = cmd.spawn()?;
    #[cfg(target_os = "linux")]
    drop(_inherited_dir_fd);
    let mut stdout_pipe = child.stdout.take();
    let mut stderr_pipe = child.stderr.take();
    let out_handle = std::thread::spawn(move || -> Vec<u8> {
        let mut buf = Vec::new();
        if let Some(ref mut r) = stdout_pipe {
            let _ = std::io::Read::read_to_end(r, &mut buf);
        }
        buf
    });
    let err_handle = std::thread::spawn(move || -> Vec<u8> {
        let mut buf = Vec::new();
        if let Some(ref mut r) = stderr_pipe {
            let _ = std::io::Read::read_to_end(r, &mut buf);
        }
        buf
    });
    let start = Instant::now();
    let mut poll_iter = 0u32;
    loop {
        if let Some(status) = child.try_wait()? {
            #[cfg(unix)]
            {
                let pgid = child.id() as i32;
                if pgid > 0 {
                    unsafe {
                        let _ = libc::kill(-pgid, libc::SIGKILL);
                    }
                }
            }
            let stdout = out_handle.join().unwrap_or_default();
            let stderr = err_handle.join().unwrap_or_default();
            return Ok(std::process::Output {
                status,
                stdout,
                stderr,
            });
        }
        if start.elapsed() >= timeout {
            #[cfg(unix)]
            {
                let pgid = child.id() as i32;
                if pgid > 0 {
                    unsafe {
                        let _ = libc::kill(-pgid, libc::SIGKILL);
                    }
                }
            }
            let _ = child.kill();
            let _ = child.wait();
            let _ = out_handle.join();
            let _ = err_handle.join();
            return Err(anyhow::Error::new(CommandTimedOut { timeout }));
        }
        let sleep_dur = if poll_iter < 25 {
            std::time::Duration::from_micros(200)
        } else if poll_iter < 50 {
            std::time::Duration::from_millis(1)
        } else {
            std::time::Duration::from_millis(5)
        };
        poll_iter = poll_iter.saturating_add(1);
        std::thread::sleep(sleep_dur);
    }
}

#[cfg(test)]
pub(super) static TEST_BWRAP_BIN_OVERRIDE: std::sync::Mutex<Option<String>> = std::sync::Mutex::new(None);

#[cfg(test)]
pub(crate) struct ScopedTestBwrapOverride {
    pub(super) prev: Option<String>,
}

#[cfg(test)]
impl ScopedTestBwrapOverride {
    pub(crate) fn set(val: impl Into<String>) -> Self {
        let mut guard = TEST_BWRAP_BIN_OVERRIDE
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let prev = guard.replace(val.into());
        Self { prev }
    }

    pub(crate) fn write_fake_bwrap_script(dir: &Path) -> std::io::Result<PathBuf> {
        let path = dir.join("fake_bwrap.sh");
        fs::write(
            &path,
            concat!(
                "#!/usr/bin/env bash\nset -euo pipefail\nENV_ARGS=()\nCHDIR=\"\"\n",
                "while [[ $# -gt 0 ]]; do\n  case \"$1\" in\n",
                "    --unshare-all|--new-session|--die-with-parent) shift ;;\n",
                "    --clearenv) ENV_ARGS=(\"-i\"); shift ;;\n",
                "    --setenv) ENV_ARGS+=(\"$2=$3\"); shift 3 ;;\n",
                "    --dev|--proc|--tmpfs) shift 2 ;;\n",
                "    --ro-bind|--ro-bind-try|--bind) shift 3 ;;\n",
                "    --chdir) CHDIR=\"$2\"; shift 2 ;;\n",
                "    *) break ;;\n  esac\ndone\n",
                "[[ -n \"$CHDIR\" ]] && cd \"$CHDIR\"\nexec env \"${ENV_ARGS[@]}\" \"$@\"\n",
            ),
        )?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = fs::metadata(&path)?.permissions();
            perms.set_mode(0o755);
            fs::set_permissions(&path, perms)?;
        }
        Ok(path)
    }
}

#[cfg(test)]
impl Drop for ScopedTestBwrapOverride {
    fn drop(&mut self) {
        let prev = self.prev.take();
        let mut guard = TEST_BWRAP_BIN_OVERRIDE
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        *guard = prev;
    }
}

pub(crate) fn probe_bwrap_sandbox(project: &Path) -> Option<PathBuf> {
    #[cfg(test)]
    if let Some(test_bwrap) = TEST_BWRAP_BIN_OVERRIDE
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .clone()
        .or_else(|| std::env::var("TURBO_LEAN_TEST_BWRAP_BIN").ok())
    {
        let trimmed = test_bwrap.trim();
        if trimmed == "__NONE__" || trimmed.is_empty() {
            return None;
        }
        let p = PathBuf::from(trimmed);
        if p.is_file() {
            return Some(p);
        }
        return None;
    }
    let mut cands = Vec::new();
    if let Some(nix_bw) = option_env!("TURBO_LEAN_NIX_BWRAP").filter(|s| !s.is_empty()) {
        cands.push(nix_bw);
    }
    cands.extend([
        "/usr/bin/bwrap",
        "/bin/bwrap",
        "/run/current-system/sw/bin/bwrap",
    ]);
    probe_bwrap_candidates(project, &cands)
}

pub(super) fn probe_bwrap_candidates(project: &Path, candidates: &[&str]) -> Option<PathBuf> {
    let sys_path = crate::trusted_tools::trusted_sys_path();
    for candidate in candidates {
        let Ok(cand) = crate::trusted_tools::system_executable(Path::new(candidate), project)
        else {
            continue;
        };
        let mut probe = Command::new(&cand);
        probe.env_clear().env("PATH", &sys_path);
        probe.args([
            "--unshare-all",
            "--new-session",
            "--die-with-parent",
            "--clearenv",
            "--setenv",
            "PATH",
            &sys_path,
            "--dev",
            "/dev",
            "--proc",
            "/proc",
            "--tmpfs",
            "/tmp",
        ]);
        for sys_dir in [
            "/usr",
            "/bin",
            "/lib",
            "/lib64",
            "/etc",
            "/nix",
            "/run/current-system/sw",
        ] {
            let p = Path::new(sys_dir);
            if p.exists() {
                probe.arg("--ro-bind").arg(p).arg(p);
            }
        }
        let probe_bin = [
            "/usr/bin/true",
            "/bin/true",
            "/run/current-system/sw/bin/true",
        ]
        .into_iter()
        .find(|p| Path::new(p).exists())
        .unwrap_or("/bin/sh");
        if probe_bin == "/bin/sh" {
            probe.args(["/bin/sh", "-c", "true"]);
        } else {
            probe.arg(probe_bin);
        }
        if probe.output().map(|o| o.status.success()).unwrap_or(false) {
            return Some(cand);
        }
    }
    None
}

#[cfg(test)]
#[test]
pub(super) fn unusable_system_sandbox_never_falls_back_to_project_bwrap() -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let root = std::env::temp_dir().join(format!(
        "turbo-bwrap-shim-{}-{}",
        std::process::id(),
        crate::pack::next_tmp_id()
    ));
    fs::create_dir_all(&root)?;
    let shim = root.join("bwrap");
    let marker = root.join("executed");
    fs::write(
        &shim,
        format!("#!/bin/sh\ntouch '{}'\nexit 0\n", marker.display()),
    )?;
    fs::set_permissions(&shim, fs::Permissions::from_mode(0o755))?;
    assert!(Command::new(&shim).status()?.success());
    fs::remove_file(&marker)?;
    // An absolute, executable system candidate fails its probe; neither a bare
    // PATH fallback nor an absolute checkout shim may replace it.
    assert!(
        probe_bwrap_candidates(&root, &["/usr/bin/false", "bwrap", shim.to_str().unwrap()])
            .is_none()
    );
    assert!(!marker.exists());
    fs::remove_dir_all(root)?;
    Ok(())
}

pub(super) fn canonicalize_path_with_missing_tail(p: &Path) -> Result<PathBuf> {
    if !p.is_absolute()
        || p.components()
            .any(|c| matches!(c, std::path::Component::ParentDir))
    {
        anyhow::bail!(
            "Search path entry `{}` must be absolute and contain no `..`",
            p.display()
        );
    }
    let mut cur = p;
    let mut tail_names: Vec<std::ffi::OsString> = Vec::new();
    // A dangling symlink is not a missing tail: canonicalizing it below fails closed.
    while fs::symlink_metadata(cur).is_err() {
        let fname = cur.file_name().ok_or_else(|| {
            anyhow::anyhow!("Cannot resolve non-existent root path `{}`", p.display())
        })?;
        tail_names.push(fname.to_os_string());
        cur = cur
            .parent()
            .ok_or_else(|| anyhow::anyhow!("Cannot resolve parent of path `{}`", p.display()))?;
    }
    let mut canon = cur.canonicalize().with_context(|| {
        format!(
            "Failed to canonicalize existing ancestor `{}` of `{}`",
            cur.display(),
            p.display()
        )
    })?;
    for name in tail_names.into_iter().rev() {
        canon.push(name);
    }
    Ok(canon)
}

/// Roots an untrusted build may use as package roots: the checkout, plus directories the
/// operator lists in `TURBO_LEAN_TRUSTED_PACKAGES_DIR` (e.g. a shared `.lake/packages` cache).
pub(super) fn untrusted_package_roots(canon_dir: &Path) -> Vec<PathBuf> {
    let mut roots = vec![canon_dir.to_path_buf()];
    if let Some(v) = std::env::var_os("TURBO_LEAN_TRUSTED_PACKAGES_DIR") {
        roots.extend(
            std::env::split_paths(&v)
                .filter(|p| p.is_absolute())
                .filter_map(|p| p.canonicalize().ok()),
        );
    }
    roots
}

/// Fail closed unless every directory a native build writes to (package build directories and
/// each module's artifact directories) lies inside its package root. Untrusted builds also
/// resolve symlinks and require each package root inside the checkout or a trusted packages dir.
pub(super) fn validate_build_write_dirs(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    canon_dir: &Path,
    is_untrusted: bool,
) -> Result<()> {
    let roots = untrusted_package_roots(canon_dir);
    let check = |pkg_root: &Path, dir: &Path| -> Result<()> {
        let lexical_ok = dir.starts_with(pkg_root)
            && !dir
                .components()
                .any(|c| matches!(c, std::path::Component::ParentDir));
        let canonical_ok = !is_untrusted
            || (|| -> Result<bool> {
                let canon_root = pkg_root.canonicalize()?;
                Ok(roots.iter().any(|r| canon_root.starts_with(r))
                    && canonicalize_path_with_missing_tail(dir)?.starts_with(&canon_root))
            })()
            .unwrap_or(false);
        if !(lexical_ok && canonical_ok) {
            anyhow::bail!(
                "Refusing to write build outputs to `{}`: outside package `{}`: fail-closed build path gate",
                dir.display(),
                pkg_root.display()
            );
        }
        Ok(())
    };
    for pkg in std::iter::once(&cfg.root_pkg).chain(&cfg.dep_pkgs) {
        let build = pkg.pkg_root.join(&pkg.build_dir);
        for dir in [
            build.join(&pkg.bin_dir),
            build.join(&pkg.lean_lib_dir),
            build.join(&pkg.native_lib_dir),
            build.join(&pkg.ir_dir),
            pkg.pkg_root.join(".lake/build"),
        ] {
            check(&pkg.pkg_root, &dir)?;
        }
    }
    for sl in &dag.shared_libs {
        if let Some(pkg) = std::iter::once(&cfg.root_pkg)
            .chain(&cfg.dep_pkgs)
            .find(|p| p.pkg_root == sl.pkg_root)
        {
            check(&pkg.pkg_root, sl.path.parent().unwrap_or(&sl.path))?;
        }
    }
    for node in dag.nodes.values() {
        check(&node.pkg_root, &node.pkg_root.join(".lake/build"))?;
        for p in [&node.olean_path, &node.ilean_path, &node.c_path] {
            check(&node.pkg_root, p.parent().unwrap_or(p))?;
        }
        if let Some(so_p) = module_dynlib_so_path(node) {
            check(&node.pkg_root, so_p.parent().unwrap_or(&so_p))?;
        }
    }
    Ok(())
}

pub(crate) fn validate_untrusted_sandbox_search_paths(
    cfg: &ProjectConfig,
    tc_prefix: &Path,
    lean_path_env: &str,
    ld_library_path_env: &str,
) -> Result<()> {
    let canon_tc = tc_prefix.canonicalize().with_context(|| {
        format!(
            "Failed to canonicalize toolchain prefix `{}`",
            tc_prefix.display()
        )
    })?;
    let canon_root_pkg = cfg.root_pkg.pkg_root.canonicalize().with_context(|| {
        format!(
            "Failed to canonicalize root package `{}`",
            cfg.root_pkg.pkg_root.display()
        )
    })?;
    let mut canon_deps: Vec<PathBuf> = Vec::with_capacity(cfg.dep_pkgs.len());
    for dp in &cfg.dep_pkgs {
        canon_deps.push(dp.pkg_root.canonicalize().with_context(|| {
            format!(
                "Failed to canonicalize dependency package `{}`",
                dp.pkg_root.display()
            )
        })?);
    }
    for env_val in [lean_path_env, ld_library_path_env] {
        for entry in env_val.split(':').filter(|s| !s.is_empty()) {
            let p = Path::new(entry);
            let Ok(canon_entry) = canonicalize_path_with_missing_tail(p) else {
                anyhow::bail!(
                    "Invalid or unbound search path entry `{}` in untrusted sandbox: fail-closed sandbox gate",
                    entry
                );
            };
            let is_bound_root = canon_entry.starts_with(&canon_tc)
                || canon_entry.starts_with(&canon_root_pkg)
                || canon_deps.iter().any(|dp| canon_entry.starts_with(dp));
            if !is_bound_root {
                anyhow::bail!(
                    "Invalid or unbound search path entry `{}` (canonical `{}`) in untrusted sandbox: fail-closed sandbox gate",
                    entry,
                    canon_entry.display()
                );
            }
        }
    }
    Ok(())
}

pub(crate) fn per_worker_lean_num_threads(
    raw_env: Option<&str>,
    host_cores: usize,
    compile_pool_size: usize,
) -> usize {
    let pool = compile_pool_size.max(1);
    let cores = host_cores.max(1);
    let configured = raw_env
        .and_then(|s| s.trim().parse::<usize>().ok())
        .filter(|&n| n > 0);
    if pool <= 1 {
        configured.unwrap_or(cores)
    } else {
        let fair_share = (cores / pool).max(1);
        configured.map_or(fair_share, |c| c.min(fair_share))
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn build_module_compile_command(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    tmp_dir: &Path,
    tmp_olean: &Path,
    tmp_ilean: &Path,
    tmp_c: &Path,
    tmp_setup: &Path,
    lean_path_env: &str,
    ld_library_path_env: &str,
    is_untrusted: bool,
    bwrap_bin: Option<&Path>,
    compile_pool_size: usize,
) -> Result<Command> {
    let stack_kb = if is_untrusted {
        "262144".to_string()
    } else {
        std::env::var("LEAN_STACK_SIZE_KB").unwrap_or_else(|_| "262144".to_string())
    };
    let mut cmd = if is_untrusted {
        let bwrap_path = bwrap_bin.ok_or_else(|| {
            anyhow::anyhow!(
                "Untrusted module compilation requires a working bubblewrap (`bwrap`) sandbox: fail-closed sandbox gate"
            )
        })?;
        let tc_prefix = cfg
            .toolchain_lib
            .parent()
            .filter(|p| p.is_dir() && p.is_absolute() && *p != Path::new("/"))
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "Invalid toolchain prefix `{}` for bubblewrap sandbox: fail-closed sandbox gate",
                    cfg.toolchain_lib.display()
                )
            })?;
        validate_untrusted_sandbox_search_paths(
            cfg,
            tc_prefix,
            lean_path_env,
            ld_library_path_env,
        )?;
        let mut c = Command::new(bwrap_path);
        c.args([
            "--unshare-all",
            "--new-session",
            "--die-with-parent",
            "--clearenv",
            "--setenv",
            "PATH",
            "/usr/bin:/bin",
            "--setenv",
            "LEAN_PATH",
            lean_path_env,
            "--setenv",
            "LEAN_NUM_THREADS",
            "4",
            "--setenv",
            "LEAN_STACK_SIZE_KB",
            &stack_kb,
        ]);
        if !ld_library_path_env.is_empty() {
            c.args(["--setenv", "LD_LIBRARY_PATH", ld_library_path_env]);
        }
        c.args(["--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp"]);
        for sys_p in [
            "/usr",
            "/bin",
            "/lib",
            "/lib64",
            "/nix",
            "/run/current-system/sw",
            "/etc/ld.so.cache",
            "/etc/localtime",
        ] {
            c.args(["--ro-bind-try", sys_p, sys_p]);
        }
        c.arg("--ro-bind").arg(tc_prefix).arg(tc_prefix);
        c.arg("--ro-bind")
            .arg(&cfg.root_pkg.pkg_root)
            .arg(&cfg.root_pkg.pkg_root);
        for dp in &cfg.dep_pkgs {
            if !dp.pkg_root.starts_with(&cfg.root_pkg.pkg_root) {
                c.arg("--ro-bind").arg(&dp.pkg_root).arg(&dp.pkg_root);
            }
        }
        c.arg("--bind").arg(tmp_dir).arg(tmp_dir);
        c.arg("--chdir").arg(&node.pkg_root);
        c.arg(&cfg.lean_bin);
        scrub_untrusted_env(&mut c);
        c
    } else {
        let host_cores = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4);
        let lean_threads = per_worker_lean_num_threads(
            std::env::var("LEAN_NUM_THREADS").ok().as_deref(),
            host_cores,
            compile_pool_size,
        );
        let mut c = Command::new(&cfg.lean_bin);
        c.current_dir(&node.pkg_root)
            .env("PATH", verifier_path(&cfg.lean_bin))
            .env("LEAN_PATH", lean_path_env)
            .env("LD_LIBRARY_PATH", ld_library_path_env)
            .env("LEAN_STACK_SIZE_KB", &stack_kb)
            .env("LEAN_NUM_THREADS", lean_threads.to_string());
        c
    };
    // When `is_untrusted`, pass Lean's `-M 4096 -j 4` (4096 MB internal allocator limit and 4
    // task threads so 256 MB per-thread stacks + imported `.olean` mappings fit inside the 12 GiB
    // `RLIMIT_DATA` cap on ≥8-core hosts)
    // after `cfg.lean_bin` in addition to the OS-level `RLIMIT_DATA` enforced in `run_command_with_timeout`.
    if is_untrusted {
        cmd.args(["-M", "4096", "-j", "4"]);
    }
    // Lake passes `weakLeanArgs` before `moreLeanArgs`.
    for arg in &node.weak_args {
        cmd.arg(verification_lake_arg(arg));
    }
    for arg in &node.strong_args {
        cmd.arg(verification_lake_arg(arg));
    }
    cmd.arg("-Dwarn.sorry=true")
        .arg("-Ddebug.skipKernelTC=false")
        .arg(&node.src_path)
        .arg("-R")
        .arg(&node.src_root)
        .arg("-o")
        .arg(tmp_olean)
        .arg("-i")
        .arg(tmp_ilean)
        .arg("--setup")
        .arg(tmp_setup);
    if node.needs_c {
        cmd.arg("-c").arg(tmp_c);
    }
    Ok(cmd)
}

pub(super) type ModuleCompileOutput = (i64, String, String);
pub(super) type StagedModuleCompileOutput = (i64, String, TempDirGuard);

/// Per-module / per-shard compile timeout in seconds (`TURBO_LEAN_MODULE_TIMEOUT_SECS` or
/// `[build] module_timeout_secs` in turbo-lean.toml, which main.rs maps onto the same
/// environment key), clamped in untrusted mode to `[15, 600]` so heavy proof modules do not
/// spuriously fail on shared 4-vCPU CI runners while untrusted builds remain bounded.
///
/// With no explicit setting the trusted default is adaptive (#437): `max(300 s, 3 × the
/// last recorded compile duration)` when the caller knows one, else 1800 s — a flat 300 s
/// killed legitimate proof-heavy modules that take over 400 s.
pub(crate) fn module_compile_timeout_secs_with_history(
    raw_env: Option<&str>,
    is_untrusted: bool,
    last_duration_ms: Option<u64>,
) -> u64 {
    let configured = raw_env
        .and_then(|s| s.trim().parse::<u64>().ok())
        .filter(|&n| n > 0);
    if is_untrusted {
        return configured.unwrap_or(300).clamp(15, 600);
    }
    configured.unwrap_or_else(|| match last_duration_ms {
        Some(ms) => ms.div_ceil(1000).saturating_mul(3).max(300),
        None => 1800,
    })
}

pub(crate) fn module_compile_timeout_secs_from(raw_env: Option<&str>, is_untrusted: bool) -> u64 {
    module_compile_timeout_secs_with_history(raw_env, is_untrusted, None)
}

pub(crate) fn module_compile_timeout_secs(is_untrusted: bool) -> u64 {
    module_compile_timeout_secs_from(
        std::env::var("TURBO_LEAN_MODULE_TIMEOUT_SECS")
            .ok()
            .as_deref(),
        is_untrusted,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn compile_single_module_staged(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    node: &ModuleNode,
    lean_path_env: &str,
    ld_library_path_env: &str,
    is_untrusted: bool,
    bwrap_bin: Option<&Path>,
    preserve_lake: bool,
    compile_pool_size: usize,
) -> Result<StagedModuleCompileOutput> {
    let t0 = Instant::now();
    record_scheduler_test_event(
        "compile_subprocess_start",
        std::slice::from_ref(&node.module_name),
    );
    let pid = std::process::id();
    let seq = crate::pack::next_tmp_id();
    let build_root = node.pkg_root.join(".lake/build");
    fs::create_dir_all(&build_root)?;
    let rel_slash = module_name_to_rel_slash(&node.module_name);
    let tmp_dir = build_root.join(format!(
        ".turbo_mod_tmp_{}_{}_{}",
        pid,
        seq,
        rel_slash.replace('/', "_")
    ));
    let _ = fs::remove_dir_all(&tmp_dir);
    fs::create_dir_all(&tmp_dir)?;
    let tmp_guard = TempDirGuard(tmp_dir.clone());
    let tmp_olean = tmp_dir.join(format!("{}.olean", rel_slash));
    let tmp_ilean = tmp_dir.join(format!("{}.ilean", rel_slash));
    let tmp_c = tmp_dir.join(format!("{}.c", rel_slash));
    let tmp_setup = tmp_dir.join(format!("{}.setup.json", rel_slash));
    if let Some(parent) = tmp_olean.parent() {
        fs::create_dir_all(parent)?;
    }
    let setup_json = build_setup_json(cfg, dag, node, None, None)?;
    let setup_bytes = serde_json::to_vec(&setup_json)?;
    fs::write(&tmp_setup, &setup_bytes)?;
    if !preserve_lake {
        write_file_atomic(&module_setup_json_path(node), &setup_bytes)?;
    }
    let mut cmd = build_module_compile_command(
        cfg,
        node,
        &tmp_dir,
        &tmp_olean,
        &tmp_ilean,
        &tmp_c,
        &tmp_setup,
        lean_path_env,
        ld_library_path_env,
        is_untrusted,
        bwrap_bin,
        compile_pool_size,
    )?;
    let timeout_secs = module_compile_timeout_secs(is_untrusted);
    let output = run_command_with_timeout(
        &mut cmd,
        std::time::Duration::from_secs(timeout_secs),
        is_untrusted,
    )
    .map_err(|e| {
        // #437: a timeout names the knob instead of a bare "timed out after Nms".
        if e.downcast_ref::<CommandTimedOut>().is_some() {
            e.context(format!(
                "module `{}` exceeded its {}s compile timeout (raise `[build] module_timeout_secs` in turbo-lean.toml or `TURBO_LEAN_MODULE_TIMEOUT_SECS`)",
                node.module_name, timeout_secs
            ))
        } else {
            e.context(format!(
                "Failed to invoke `lean` compiler ({}) for module `{}`",
                cfg.lean_bin.display(),
                node.module_name
            ))
        }
    })?;
    record_scheduler_test_event(
        "compile_subprocess_end",
        std::slice::from_ref(&node.module_name),
    );
    let stdout_str = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr_str = String::from_utf8_lossy(&output.stderr).to_string();
    if !output.status.success() {
        anyhow::bail!(
            "Native Lean compilation failed for module `{}` ({}):\n{}\n{}",
            node.module_name,
            node.src_path.display(),
            stdout_str.trim(),
            stderr_str.trim()
        );
    }
    if stdout_str.contains("declaration uses ") || stderr_str.contains("declaration uses ") {
        anyhow::bail!(
            "Native Lean compilation rejected module `{}` ({}) due to `sorry` axiom usage",
            node.module_name,
            node.src_path.display()
        );
    }
    let tmp_srv = PathBuf::from(format!("{}.server", tmp_olean.display()));
    let tmp_priv = PathBuf::from(format!("{}.private", tmp_olean.display()));
    let is_regular_nonempty_in_tmp =
        |p: &Path| -> bool { p.starts_with(&tmp_dir) && is_regular_nonempty_file(p) };
    let has_olean = is_regular_nonempty_in_tmp(&tmp_olean);
    let has_ilean = is_regular_nonempty_in_tmp(&tmp_ilean);
    let has_srv = is_regular_nonempty_in_tmp(&tmp_srv);
    let has_priv = is_regular_nonempty_in_tmp(&tmp_priv);
    let has_c = is_regular_nonempty_in_tmp(&tmp_c);
    let artifacts_ok = c_abi::verify_module_artifact_set(
        has_olean,
        has_ilean,
        node.is_module,
        has_srv,
        has_priv,
        node.needs_c,
        has_c,
    );
    if !artifacts_ok {
        anyhow::bail!(
            "C-ABI gate `turbo_spec_verify_module_artifact_set` failed after compiling `{}` (olean={}, ilean={}, is_module={}, srv={}, priv={}, needs_c={}, c={})",
            node.module_name,
            has_olean,
            has_ilean,
            node.is_module,
            has_srv,
            has_priv,
            node.needs_c,
            has_c
        );
    }
    let dur_ms = t0.elapsed().as_millis() as i64;
    Ok((dur_ms, stdout_str, tmp_guard))
}

/// `check` / trusted `pr-verify` gate: every non-toolchain `.olean` that `target_files`
/// transitively import (project-local or dependency, however it was built) must carry current
/// kernel-replay authority in `TurboStore` (`kernel_replayed_oleans` keyed by freshly hashed
/// on-disk `.olean`+`.ilean` bytes, `ZYGOTE_REPLAY_VERSION`, and `lean_githash`) or be
/// independently replayed now. Checkout manifests (`.turbo_verified_sources.json`) are freshness
/// metadata only and never grant replay authority. Fails closed.
/// Verify that an imported non-toolchain module belonging to the workspace root package or one
/// of its dependency packages resolves unambiguously to a `.lean` source file whose directives
/// satisfy checking-weakening and native-decide hygiene gates. Fails closed if a workspace or
/// dependency package `.olean` artifact lacks a resolvable `.lean` source or fails source hygiene.
pub(crate) fn verify_imported_package_module_source_hygiene(
    cfg: &ProjectConfig,
    mod_name: &str,
    olean_path: &Path,
    allowed_axioms: &[String],
) -> Result<bool> {
    let mut specs = Vec::new();
    if let Some(root_spec) = resolve_module_in_package(&cfg.root_pkg, true, mod_name) {
        specs.push(root_spec);
    }
    for dp in &cfg.dep_pkgs {
        if let Some(dep_spec) = resolve_module_in_package(dp, false, mod_name) {
            specs.push(dep_spec);
        }
    }
    if specs.len() > 1 {
        let pkg_names: Vec<&str> = specs.iter().map(|s| s.pkg_name.as_str()).collect();
        anyhow::bail!(
            "Ambiguous imported module `{mod_name}` resolved in multiple packages ({pkg_names:?}): fail-closed"
        );
    }
    let Some(spec) = specs.into_iter().next() else {
        let canon_olean = olean_path
            .canonicalize()
            .unwrap_or_else(|_| olean_path.to_path_buf());
        let belongs_to_pkg = std::iter::once(&cfg.root_pkg)
            .chain(cfg.dep_pkgs.iter())
            .any(|pkg| {
                let pkg_root_canon = pkg
                    .pkg_root
                    .canonicalize()
                    .unwrap_or_else(|_| pkg.pkg_root.clone());
                let pkg_lib_canon = pkg
                    .pkg_root
                    .join(&pkg.build_dir)
                    .join(&pkg.lean_lib_dir)
                    .canonicalize()
                    .unwrap_or_else(|_| pkg.pkg_root.join(&pkg.build_dir).join(&pkg.lean_lib_dir));
                canon_olean.starts_with(&pkg_lib_canon) || canon_olean.starts_with(&pkg_root_canon)
            });
        if belongs_to_pkg {
            // Standalone root-package `.lean` files outside Lake library/exe globs (e.g.
            // `TurboLean.lean` alongside `TurboLean.+`, or auxiliary scripts compiled by
            // `stock_statement_build`) still resolve unambiguously under a root-package source dir.
            let canon_root_lib = cfg
                .root_pkg
                .pkg_root
                .join(&cfg.root_pkg.build_dir)
                .join(&cfg.root_pkg.lean_lib_dir)
                .canonicalize()
                .unwrap_or_else(|_| {
                    cfg.root_pkg
                        .pkg_root
                        .join(&cfg.root_pkg.build_dir)
                        .join(&cfg.root_pkg.lean_lib_dir)
                });
            let canon_root_pkg = cfg
                .root_pkg
                .pkg_root
                .canonicalize()
                .unwrap_or_else(|_| cfg.root_pkg.pkg_root.clone());
            let canon_packages = cfg
                .root_pkg
                .pkg_root
                .join(&cfg.root_pkg.packages_dir)
                .canonicalize()
                .unwrap_or_else(|_| cfg.root_pkg.pkg_root.join(&cfg.root_pkg.packages_dir));
            if canon_olean.starts_with(&canon_root_lib)
                || (canon_olean.starts_with(&canon_root_pkg)
                    && !canon_olean.starts_with(&canon_packages))
            {
                let rel_slash = module_name_to_rel_slash(mod_name);
                let base = cfg.root_pkg.pkg_root.join(&cfg.root_pkg.src_dir);
                let mut roots = vec![base.clone()];
                roots.extend(
                    cfg.root_pkg
                        .libs
                        .iter()
                        .filter_map(|l| l.src_dir.as_ref())
                        .map(|d| base.join(d)),
                );
                roots.extend(
                    cfg.root_pkg
                        .exes
                        .iter()
                        .filter_map(|e| e.src_dir.as_ref())
                        .map(|d| base.join(d)),
                );
                roots.sort();
                roots.dedup();
                let cands: Vec<PathBuf> = roots
                    .into_iter()
                    .map(|r| r.join(format!("{rel_slash}.lean")))
                    .filter(|p| p.is_file())
                    .collect();
                if cands.len() == 1 {
                    let standalone_src = &cands[0];
                    let hygiene = load_source_hygiene_cached(standalone_src).with_context(|| {
                        format!(
                            "Failed to read `.lean` source `{}` for imported module `{mod_name}`: fail-closed",
                            standalone_src.display()
                        )
                    })?;
                    anyhow::ensure!(
                        !hygiene.has_checking_weakening,
                        "Soundness hygiene violation in imported module `{mod_name}` ({}): {:?}",
                        standalone_src.display(),
                        hygiene.disallowed_items_under(allowed_axioms)
                    );
                    anyhow::ensure!(
                        !hygiene.native_violation_under(allowed_axioms),
                        "[TurboLean.KernelGate] native_decide/bv_decide in imported module `{mod_name}` ({}) is not admitted by the project's axiom allowlist",
                        standalone_src.display()
                    );
                    anyhow::ensure!(
                        !hygiene.has_trust_compiler,
                        "Soundness hygiene violation (trustCompiler) in imported module `{mod_name}` ({})",
                        standalone_src.display()
                    );
                    return Ok(true);
                }
            }
            anyhow::bail!(
                "Workspace/dependency `.olean` `{}` for imported module `{mod_name}` has no resolvable `.lean` source in project or dependency packages: fail-closed",
                olean_path.display()
            );
        }
        return Ok(false);
    };
    let hygiene = load_source_hygiene_cached(&spec.src_path).with_context(|| {
        format!(
            "Failed to read `.lean` source `{}` for imported module `{mod_name}`: fail-closed",
            spec.src_path.display()
        )
    })?;
    let is_git_pinned_dep = !spec.is_root_pkg && is_git_pinned_manifest_package(cfg, &spec);
    anyhow::ensure!(
        if is_git_pinned_dep {
            !hygiene.has_checking_weakening_option
        } else {
            !hygiene.has_checking_weakening
        },
        "Soundness hygiene violation in imported module `{mod_name}` ({}): {:?}",
        spec.src_path.display(),
        hygiene.disallowed_items_under(allowed_axioms)
    );
    anyhow::ensure!(
        is_git_pinned_dep || !hygiene.native_violation_under(allowed_axioms),
        "[TurboLean.KernelGate] native_decide/bv_decide in imported module `{mod_name}` ({}) is not admitted by the project's axiom allowlist",
        spec.src_path.display()
    );
    anyhow::ensure!(
        !hygiene.has_trust_compiler,
        "Soundness hygiene violation (trustCompiler) in imported module `{mod_name}` ({})",
        spec.src_path.display()
    );
    Ok(spec.is_root_pkg)
}

pub(crate) fn ensure_imported_oleans_replayed(
    store: &TurboStore,
    canon_dir: &Path,
    target_files: &[PathBuf],
) -> Result<usize> {
    ensure_imported_oleans_replayed_with_options(store, canon_dir, target_files, false)
}

pub(crate) fn ensure_imported_oleans_replayed_with_options(
    store: &TurboStore,
    canon_dir: &Path,
    target_files: &[PathBuf],
    allow_sorry: bool,
) -> Result<usize> {
    let mut allowed = splitter::allowed_axioms();
    if allow_sorry && !allowed.iter().any(|a| a == "sorryAx") {
        allowed.push("sorryAx".to_string());
    }
    ensure_imported_oleans_replayed_with_roots_and_axioms(
        store,
        canon_dir,
        target_files,
        &[],
        &allowed,
    )
}

pub(crate) fn ensure_imported_oleans_replayed_with_roots(
    store: &TurboStore,
    canon_dir: &Path,
    target_files: &[PathBuf],
    root_modules: &[String],
) -> Result<usize> {
    ensure_imported_oleans_replayed_with_roots_and_axioms(
        store,
        canon_dir,
        target_files,
        root_modules,
        &splitter::allowed_axioms(),
    )
}

pub(crate) fn ensure_imported_oleans_replayed_with_roots_and_axioms(
    store: &TurboStore,
    canon_dir: &Path,
    target_files: &[PathBuf],
    root_modules: &[String],
    allowed_axioms: &[String],
) -> Result<usize> {
    let mut worklist: Vec<String> = target_files
        .iter()
        .filter_map(|f| fs::read_to_string(f).ok())
        .flat_map(|s| parse_header_info(&s).imports)
        .chain(root_modules.iter().cloned())
        .collect();
    if worklist.is_empty() {
        return Ok(0);
    }
    let cfg = resolve_project_config(canon_dir);
    let tc_lib = cfg.as_ref().map(|c| c.toolchain_lib_lean.clone()).ok();
    let tc_gh = cfg.as_ref().map(|c| c.lean_githash.clone()).ok();
    let lean_path = match &cfg {
        Ok(c) => build_lean_search_path(c, false).0,
        Err(_) => lake_build::resolve_remote_lean_path(canon_dir, None),
    };
    let mut dirs: Vec<PathBuf> = std::env::split_paths(&lean_path).collect();
    if let Some(ref t) = tc_lib {
        if !t.as_os_str().is_empty() && !dirs.contains(t) {
            dirs.push(t.clone());
        }
    }
    let mut seen = HashSet::new();
    let mut imported: Vec<(String, PathBuf)> = Vec::new();
    while let Some(m) = worklist.pop() {
        if !seen.insert(m.clone()) {
            continue;
        }
        let Some(path) = resolve_olean_along_search_dirs(&dirs, &m) else {
            continue;
        };
        if let Some(ref t) = tc_lib {
            if is_verified_toolchain_olean_file(t, tc_gh.as_deref(), &path) {
                continue;
            }
        }
        let (imps, _) = read_olean_binary_imports_cached(&path).with_context(|| {
            format!(
                "Failed to parse binary `.olean` header of imported `{m}` (`{}`): fail-closed",
                path.display()
            )
        })?;
        worklist.extend(imps.into_iter().map(|i| i.module));
        imported.push((m, path));
    }
    if imported.is_empty() {
        return Ok(0);
    }
    let cfg = cfg.context(
        "Cannot kernel-replay imported `.olean`s without a resolvable project configuration: fail-closed",
    )?;
    let mut pending_audit = Vec::new();
    let mut pending_replay = Vec::new();
    let (replay_lp, _) = build_lean_search_path(&cfg, false);
    let mut replay_batch = ReplayLookupBatchCache::new(store, &cfg, &replay_lp);
    for (m, path) in &imported {
        let needs_audit =
            verify_imported_package_module_source_hygiene(&cfg, m, path, allowed_axioms)?;
        if needs_audit {
            if !replay_batch.is_audited_in_store(store, &cfg, &replay_lp, m, path) {
                pending_audit.push(m.clone());
            }
        } else if !replay_batch.is_replayed_in_store(store, &cfg, &replay_lp, path) {
            pending_replay.push(m.clone());
        }
    }
    if !pending_audit.is_empty() {
        let allow_sorry_axiom = allowed_axioms.iter().any(|a| a == "sorryAx");
        crate::zygote::audit_compiled_modules_with_zygote_options(
            store,
            &cfg,
            &pending_audit,
            &replay_lp,
            &[],
            false,
            allow_sorry_axiom,
        )
        .context("Imported `.olean` failed in-kernel soundness & replay audit")?;
    }
    if !pending_replay.is_empty() {
        crate::zygote::kernel_replay_modules_with_zygote(store, &cfg, &pending_replay, &replay_lp)
            .context("Imported `.olean` failed independent kernel replay")?;
    }
    Ok(pending_audit.len() + pending_replay.len())
}

pub(crate) fn node_is_git_pinned_manifest_package(cfg: &ProjectConfig, node: &ModuleNode) -> bool {
    is_clean_git_pinned_pkg(
        cfg,
        node.is_root_pkg,
        &node.pkg_name,
        &node.pkg_base_name,
        &node.pkg_root,
    )
}

pub(super) fn node_source_has_disallowed_elab_host_effects(
    cfg: &ProjectConfig,
    node: &ModuleNode,
    src_raw: &str,
) -> bool {
    source_has_disallowed_elab_host_effects_for_module(
        cfg,
        &node.pkg_root,
        node.is_root_pkg,
        !node.is_root_pkg && node_is_git_pinned_manifest_package(cfg, node),
        &node.module_name,
        &node.src_path,
        src_raw,
    )
}

pub(super) fn compute_tainted_elab_host_effect_modules(
    cfg: &ProjectConfig,
    dag: &ModuleDag,
) -> HashSet<String> {
    let mut ext_tainted_memo: HashMap<PathBuf, bool> = HashMap::new();
    let mut tainted: HashSet<String> = HashSet::new();
    for mod_name in &dag.topological_order {
        let Some(node) = dag.nodes.get(mod_name) else {
            continue;
        };
        let self_tainted = fs::read_to_string(&node.src_path)
            .map(|s| node_source_has_disallowed_elab_host_effects(cfg, node, &s))
            .unwrap_or(true);
        let dag_dep_tainted = node.direct_dag_deps.iter().any(|d| tainted.contains(d));
        let ext_dep_tainted = node.external_olean_deps.iter().any(|(_, olean_path)| {
            *ext_tainted_memo
                .entry(olean_path.clone())
                .or_insert_with(|| {
                    resolve_source_spec_for_prebuilt_olean(cfg, olean_path).is_some_and(|spec| {
                        fs::read_to_string(&spec.src_path)
                            .map(|s| spec_source_has_disallowed_elab_host_effects(cfg, &spec, &s))
                            .unwrap_or(true)
                    })
                })
        });
        if self_tainted || dag_dep_tainted || ext_dep_tainted {
            tainted.insert(mod_name.clone());
        }
    }
    tainted
}

#[derive(Deserialize)]
pub(super) struct WorkerZygoteAuditReply {
    pub(super) ok: bool,
    #[serde(default)]
    pub(super) audited: Option<Vec<String>>,
    #[serde(default)]
    pub(super) violations: Vec<String>,
}

pub(super) fn parse_worker_audit_reply(out: &std::process::Output, mod_names: &[String]) -> Result<()> {
    let stdout_str = String::from_utf8_lossy(&out.stdout);
    let stderr_str = String::from_utf8_lossy(&out.stderr);
    let json_line = stdout_str
        .lines()
        .rev()
        .map(str::trim)
        .find(|l| l.starts_with('{') && l.ends_with('}'))
        .unwrap_or("");
    let parsed: Option<WorkerZygoteAuditReply> = serde_json::from_str(json_line).ok();
    match parsed {
        Some(reply)
            if out.status.success()
                && reply.ok
                && reply.violations.is_empty()
                && reply.audited.as_deref() == Some(mod_names) =>
        {
            Ok(())
        }
        Some(reply) => {
            let details = if reply.violations.is_empty() {
                format!(
                    "exit={} stdout={} stderr={}",
                    out.status,
                    stdout_str.trim(),
                    stderr_str.trim()
                )
            } else {
                reply.violations.join("\n")
            };
            anyhow::bail!(
                "In-kernel `.olean` soundness audit rejected compiled artifact(s) ({:?}):\n{}",
                mod_names,
                details
            );
        }
        None => {
            anyhow::bail!(
                "In-kernel `.olean` soundness auditor failed closed (exit={}, modules={:?}):\nstdout: {}\nstderr: {}",
                out.status,
                mod_names,
                stdout_str.trim(),
                stderr_str.trim()
            );
        }
    }
}

pub(super) fn scheduler_audit_batch_size() -> usize {
    std::env::var("TURBO_LEAN_AUDIT_BATCH_SIZE")
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .filter(|&v| v > 0)
        .unwrap_or(8)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn run_audit_chunk_subprocess(
    store_root: &Path,
    cfg: &ProjectConfig,
    mod_names: &[String],
    lean_path_env: &str,
    extra_ro_binds: &[PathBuf],
    is_untrusted: bool,
    skip_child_replay: bool,
    pinned_dir_raw_fd: Option<i32>,
) -> Result<()> {
    if mod_names.is_empty() || mod_names.iter().any(|m| m.trim().is_empty()) {
        anyhow::bail!("In-kernel `.olean` audit received an empty module name: fail-closed");
    }
    record_scheduler_test_event("audit_subprocess_start", mod_names);
    let (mut cmd, timeout) = crate::zygote::kernel_reader_command(
        store_root,
        cfg,
        lean_path_env,
        extra_ro_binds,
        is_untrusted,
    )?;
    cmd.arg("--audit-modules");
    if skip_child_replay {
        cmd.arg("--skip-child-replay");
    }
    for a in crate::zygote::pinned_ffi_allow_args(cfg, mod_names) {
        cmd.arg(a);
    }
    for m in mod_names {
        cmd.arg(m);
    }
    let out =
        run_command_with_timeout_pinned_fd(&mut cmd, timeout, is_untrusted, pinned_dir_raw_fd);
    record_scheduler_test_event("audit_subprocess_end", mod_names);
    match out.and_then(|o| parse_worker_audit_reply(&o, mod_names)) {
        Ok(()) => Ok(()),
        Err(_) if mod_names.len() > 1 => {
            let mid = mod_names.len() / 2;
            run_audit_chunk_subprocess(
                store_root,
                cfg,
                &mod_names[..mid],
                lean_path_env,
                extra_ro_binds,
                is_untrusted,
                skip_child_replay,
                pinned_dir_raw_fd,
            )?;
            run_audit_chunk_subprocess(
                store_root,
                cfg,
                &mod_names[mid..],
                lean_path_env,
                extra_ro_binds,
                is_untrusted,
                skip_child_replay,
                pinned_dir_raw_fd,
            )
        }
        Err(e) => Err(e),
    }
}

pub(super) type ModuleSnapshotAuthority = (std::sync::Arc<crate::zygote::ClosureSnapshot>, bool, bool);
pub(super) enum ModuleAuditAuthority {
    Snapshot(ModuleSnapshotAuthority),
    FastStore(VerifiedFastStoreAuthority),
}
pub(super) type PerModuleAuditOutcome = (Result<()>, Option<ModuleAuditAuthority>);
pub(super) type AuditBatchWorkerOutcome = HashMap<String, PerModuleAuditOutcome>;

pub(super) fn run_audit_or_replay_batch_worker_bound(
    store_root: &Path,
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    mod_names: &[String],
    snap: &std::sync::Arc<crate::zygote::ClosureSnapshot>,
    live_lean_path_env: &str,
    is_untrusted: bool,
) -> Result<AuditBatchWorkerOutcome> {
    let (snap_lp, snap_dir) =
        crate::zygote::ensure_bound_audit_closure(snap, "sched_audit_before_replay")?;
    let pinned_fd = crate::zygote::snapshot_pinned_dir_raw_fd(snap);
    let parent_snap_lp =
        crate::zygote::snapshot_parent_search_path(snap).unwrap_or_else(|| snap_lp.clone());
    let snap_binds: Vec<PathBuf> = if is_untrusted {
        vec![snap_dir]
    } else {
        Vec::new()
    };

    let (mut audit, replay): (Vec<String>, Vec<String>) = mod_names
        .iter()
        .cloned()
        .partition(|m| is_untrusted || dag.nodes.get(m).is_none_or(|n| n.is_root_pkg));
    audit.sort();
    audit.dedup();
    let mut replay_sorted = replay;
    replay_sorted.sort();
    replay_sorted.dedup();

    let mut per_mod: AuditBatchWorkerOutcome = HashMap::with_capacity(mod_names.len());
    let mut snap_replayed: HashSet<String> = HashSet::new();
    if !is_untrusted {
        if let Ok(worker_store) = TurboStore::open(Some(store_root)) {
            let live_batch = ReplayLookupBatchCache::new(&worker_store, cfg, live_lean_path_env);
            let mut snap_batch = ReplayLookupBatchCache::new(&worker_store, cfg, &parent_snap_lp);
            for m in audit.iter().chain(replay_sorted.iter()) {
                let Some(snap_olean) = snap_batch.resolve_module_olean(m) else {
                    continue;
                };
                let Some((ref orig_olean, _)) = snap.entries.get(m).and_then(|e| e.as_ref()) else {
                    continue;
                };
                let binds_policy = live_batch.is_root_module_olean(orig_olean);
                if snap_batch.is_replayed_in_store_with_binds_policy(
                    &worker_store,
                    cfg,
                    &snap_olean,
                    binds_policy,
                ) {
                    snap_replayed.insert(m.clone());
                }
            }
        }
    }

    let need_replay_audit: Vec<String> = audit
        .iter()
        .filter(|m| is_untrusted || !snap_replayed.contains(*m))
        .cloned()
        .collect();
    let need_replay_dep: Vec<String> = replay_sorted
        .iter()
        .filter(|m| !snap_replayed.contains(*m))
        .cloned()
        .collect();
    let mut pre_replayed = need_replay_audit.is_empty() && !is_untrusted;
    if is_untrusted && audit.len() > 1 {
        crate::zygote::kernel_replay_modules_exec_pinned(
            store_root,
            cfg,
            &audit,
            &snap_lp,
            &snap_binds,
            true,
            None,
        )?;
        let _ = crate::zygote::ensure_bound_audit_closure(snap, "sched_audit_after_replay")?;
        pre_replayed = true;
    } else if !is_untrusted && need_replay_audit.len() + need_replay_dep.len() > 1 {
        let mut union_replay = Vec::with_capacity(need_replay_audit.len() + need_replay_dep.len());
        union_replay.extend(need_replay_audit.iter().cloned());
        union_replay.extend(need_replay_dep.iter().cloned());
        union_replay.sort();
        union_replay.dedup();
        if crate::zygote::kernel_replay_modules_exec_pinned(
            store_root,
            cfg,
            &union_replay,
            &parent_snap_lp,
            &[],
            false,
            pinned_fd,
        )
        .is_ok()
        {
            let _ = crate::zygote::ensure_bound_audit_closure(snap, "sched_audit_after_replay")?;
            pre_replayed = true;
            for m in &replay_sorted {
                let record_rep = !snap_replayed.contains(m);
                per_mod.insert(
                    m.clone(),
                    (
                        Ok(()),
                        Some(ModuleAuditAuthority::Snapshot((
                            std::sync::Arc::clone(snap),
                            record_rep,
                            false,
                        ))),
                    ),
                );
            }
            replay_sorted.clear();
        }
    } else if !is_untrusted && need_replay_dep.is_empty() && !replay_sorted.is_empty() {
        for m in &replay_sorted {
            per_mod.insert(
                m.clone(),
                (
                    Ok(()),
                    Some(ModuleAuditAuthority::Snapshot((
                        std::sync::Arc::clone(snap),
                        false,
                        false,
                    ))),
                ),
            );
        }
        replay_sorted.clear();
    }

    let explicit_audit_batch = std::env::var("TURBO_LEAN_AUDIT_BATCH_SIZE")
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .filter(|&v| v > 0);
    let audit_chunk_sz = match explicit_audit_batch {
        Some(sz) => sz,
        None if !is_untrusted => 128,
        None => scheduler_audit_batch_size(),
    };

    for chunk in audit.chunks(audit_chunk_sz) {
        let _ = crate::zygote::ensure_bound_audit_closure(snap, "sched_audit_before_chunk")?;
        let chunk_skip_replay = (is_untrusted && pre_replayed)
            || (!is_untrusted && (pre_replayed || chunk.iter().all(|m| snap_replayed.contains(m))));
        match run_audit_chunk_subprocess(
            store_root,
            cfg,
            chunk,
            &snap_lp,
            &snap_binds,
            is_untrusted,
            chunk_skip_replay,
            pinned_fd,
        ) {
            Ok(()) => {
                let _ = crate::zygote::ensure_bound_audit_closure(snap, "sched_audit_after_chunk")?;
                for m in chunk {
                    let record_rep = !is_untrusted && !snap_replayed.contains(m);
                    let record_aud = !is_untrusted;
                    per_mod.insert(
                        m.clone(),
                        (
                            Ok(()),
                            Some(ModuleAuditAuthority::Snapshot((
                                std::sync::Arc::clone(snap),
                                record_rep,
                                record_aud,
                            ))),
                        ),
                    );
                }
            }
            Err(chunk_err) => {
                if chunk.len() == 1 {
                    per_mod.insert(chunk[0].clone(), (Err(chunk_err), None));
                } else {
                    for m in chunk {
                        let single_skip_replay = (is_untrusted && pre_replayed)
                            || (!is_untrusted && (pre_replayed || snap_replayed.contains(m)));
                        let single_res = crate::zygote::ensure_bound_audit_closure(
                            snap,
                            "sched_audit_before_chunk",
                        )
                        .and_then(|_| {
                            run_audit_chunk_subprocess(
                                store_root,
                                cfg,
                                std::slice::from_ref(m),
                                &snap_lp,
                                &snap_binds,
                                is_untrusted,
                                single_skip_replay,
                                pinned_fd,
                            )?;
                            let _ = crate::zygote::ensure_bound_audit_closure(
                                snap,
                                "sched_audit_after_chunk",
                            )?;
                            Ok(())
                        });
                        match single_res {
                            Ok(()) => {
                                let record_rep = !is_untrusted && !snap_replayed.contains(m);
                                let record_aud = !is_untrusted;
                                per_mod.insert(
                                    m.clone(),
                                    (
                                        Ok(()),
                                        Some(ModuleAuditAuthority::Snapshot((
                                            std::sync::Arc::clone(snap),
                                            record_rep,
                                            record_aud,
                                        ))),
                                    ),
                                );
                            }
                            Err(e) => {
                                per_mod.insert(m.clone(), (Err(e), None));
                            }
                        }
                    }
                }
            }
        }
    }

    for m in &replay_sorted {
        if m.trim().is_empty() {
            per_mod.insert(
                m.clone(),
                (
                    Err(anyhow::anyhow!(
                        "Kernel replay received an empty module name: fail-closed"
                    )),
                    None,
                ),
            );
            continue;
        }
        if !is_untrusted && snap_replayed.contains(m) {
            per_mod.insert(
                m.clone(),
                (
                    Ok(()),
                    Some(ModuleAuditAuthority::Snapshot((
                        std::sync::Arc::clone(snap),
                        false,
                        false,
                    ))),
                ),
            );
            continue;
        }
        record_scheduler_test_event("replay_subprocess_start", std::slice::from_ref(m));
        let res = (|| -> Result<()> {
            let _ = crate::zygote::ensure_bound_audit_closure(snap, "sched_replay_before_single")?;
            let (mut cmd, timeout) =
                crate::zygote::kernel_reader_command(store_root, cfg, &snap_lp, &[], false)?;
            cmd.args(["--kernel-replay-module", m.as_str()]);
            let out = run_command_with_timeout_pinned_fd(&mut cmd, timeout, false, pinned_fd)
                .context(
                    "Failed to execute independent kernel replay (`--kernel-replay-module`)",
                )?;
            anyhow::ensure!(
                out.status.success(),
                "[TurboLean.KernelReplay] independent kernel re-check of dependency `{}` failed (exit={}):\n{}",
                m,
                out.status,
                String::from_utf8_lossy(&out.stderr).trim()
            );
            let _ = crate::zygote::ensure_bound_audit_closure(snap, "sched_replay_after_single")?;
            Ok(())
        })();
        record_scheduler_test_event("replay_subprocess_end", std::slice::from_ref(m));
        match res {
            Ok(()) => {
                per_mod.insert(
                    m.clone(),
                    (
                        Ok(()),
                        Some(ModuleAuditAuthority::Snapshot((
                            std::sync::Arc::clone(snap),
                            true,
                            false,
                        ))),
                    ),
                );
            }
            Err(e) => {
                per_mod.insert(m.clone(), (Err(e), None));
            }
        }
    }

    Ok(per_mod)
}

pub(super) fn run_audit_or_replay_batch_worker(
    store_root: &Path,
    cfg: &ProjectConfig,
    dag: &ModuleDag,
    mod_names: &[String],
    lean_path_env: &str,
    is_untrusted: bool,
) -> Result<AuditBatchWorkerOutcome> {
    if mod_names.is_empty() {
        return Ok(HashMap::new());
    }
    if is_untrusted {
        crate::zygote::validate_untrusted_audit_caller_paths(cfg, lean_path_env, &[])?;
    }
    match crate::zygote::materialize_bound_audit_closure(cfg, mod_names, lean_path_env) {
        Ok(snap) => {
            let snap = std::sync::Arc::new(snap);
            run_audit_or_replay_batch_worker_bound(
                store_root,
                cfg,
                dag,
                mod_names,
                &snap,
                lean_path_env,
                is_untrusted,
            )
        }
        Err(batch_err) if mod_names.len() == 1 => {
            let mut per_mod = HashMap::with_capacity(1);
            per_mod.insert(mod_names[0].clone(), (Err(batch_err), None));
            Ok(per_mod)
        }
        Err(_) => {
            let mut per_mod = HashMap::with_capacity(mod_names.len());
            for m in mod_names {
                let single_slice = std::slice::from_ref(m);
                match crate::zygote::materialize_bound_audit_closure(
                    cfg,
                    single_slice,
                    lean_path_env,
                ) {
                    Ok(snap) => {
                        let snap = std::sync::Arc::new(snap);
                        match run_audit_or_replay_batch_worker_bound(
                            store_root,
                            cfg,
                            dag,
                            single_slice,
                            &snap,
                            lean_path_env,
                            is_untrusted,
                        ) {
                            Ok(mut sub) => {
                                if let Some(v) = sub.remove(m) {
                                    per_mod.insert(m.clone(), v);
                                }
                            }
                            Err(e) => {
                                per_mod.insert(m.clone(), (Err(e), None));
                            }
                        }
                    }
                    Err(e) => {
                        per_mod.insert(m.clone(), (Err(e), None));
                    }
                }
            }
            Ok(per_mod)
        }
    }
}

#[cfg(test)]
pub(crate) static BWRAP_TEST_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
