//! Host tools used at verification boundaries must never come from project PATH.
use anyhow::{Context, Result};
use std::fs;
use std::ops::{Deref, DerefMut};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

const SYSTEM_BINS: [&str; 6] = [
    "/usr/bin",
    "/bin",
    "/usr/local/bin",
    "/usr/sbin",
    "/sbin",
    "/run/current-system/sw/bin",
];

pub(crate) fn format_git_locality_disabled_warning(err: &anyhow::Error) -> String {
    format!("[turbo-lean] warning: proof-edit locality disabled ({err}); set TURBO_LEAN_GIT to a Git >= 2.46 binary to avoid full Lake dependent rebuilds")
}

fn git_locality_warning_repo(dir: &Path) -> Option<PathBuf> {
    let dir = dir.canonicalize().ok()?;
    dir.ancestors()
        .find(|p| p.join(".git").exists())
        .map(Path::to_path_buf)
}

pub(crate) fn warn_git_locality_disabled(dir: &Path, err: &anyhow::Error) {
    static WARNED: OnceLock<std::sync::Mutex<std::collections::HashSet<PathBuf>>> = OnceLock::new();
    let Some(repo) = git_locality_warning_repo(dir) else {
        return;
    };
    if WARNED
        .get_or_init(Default::default)
        .lock()
        .is_ok_and(|mut seen| seen.insert(repo))
    {
        eprintln!("{}", format_git_locality_disabled_warning(err));
    }
}

#[cfg(test)]
mod locality_warning_tests {
    use super::*;

    #[test]
    fn git_locality_warning_requires_repo_and_explains_remedy() -> Result<()> {
        let dir = std::env::temp_dir().join(format!("git-locality-warning-{}", std::process::id()));
        fs::create_dir_all(&dir)?;
        assert!(git_locality_warning_repo(&dir).is_none());
        fs::create_dir_all(dir.join(".git"))?;
        assert_eq!(git_locality_warning_repo(&dir), Some(dir.canonicalize()?));
        let msg = format_git_locality_disabled_warning(&anyhow::anyhow!("Git 2.43 < 2.46"));
        assert!(msg.contains("proof-edit locality disabled (Git 2.43 < 2.46)"));
        assert!(msg.contains("set TURBO_LEAN_GIT to a Git >= 2.46 binary"));
        fs::remove_dir_all(dir)?;
        Ok(())
    }
}

pub(crate) fn trusted_sys_path() -> String {
    match option_env!("TURBO_LEAN_NIX_SYS_PATH") {
        Some(nix_p) if !nix_p.is_empty() => {
            format!("{nix_p}:/run/current-system/sw/bin:/usr/bin:/bin")
        }
        _ if Path::new("/run/current-system/sw/bin").is_dir() => {
            "/run/current-system/sw/bin:/usr/bin:/bin".to_string()
        }
        _ => "/usr/bin:/bin".to_string(),
    }
}

pub(crate) fn outside_checkout(path: &Path, project: &Path) -> Result<PathBuf> {
    anyhow::ensure!(
        path.is_absolute(),
        "Trusted executable must be absolute: {}",
        path.display()
    );
    let path = path
        .canonicalize()
        .with_context(|| format!("Cannot resolve {}", path.display()))?;
    let project = project.canonicalize()?;
    let checkout = project
        .ancestors()
        .find(|p| p.join(".git").exists())
        .unwrap_or(&project);
    anyhow::ensure!(
        !path.starts_with(checkout) && !path.ancestors().any(|p| p.join(".git").exists()),
        "Trusted executable is inside a project/checkout: {}",
        path.display()
    );
    anyhow::ensure!(
        path.is_file(),
        "Trusted executable is not a file: {}",
        path.display()
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        anyhow::ensure!(
            fs::metadata(&path)?.permissions().mode() & 0o111 != 0,
            "Trusted executable is not executable: {}",
            path.display()
        );
    }
    Ok(path)
}

pub(crate) fn system_executable(path: &Path, project: &Path) -> Result<PathBuf> {
    let path = outside_checkout(path, project)?;
    let in_nix_store_bin = path.starts_with("/nix/store/")
        && path
            .parent()
            .and_then(|p| p.file_name())
            .is_some_and(|n| n == "bin");
    anyhow::ensure!(
        in_nix_store_bin
            || SYSTEM_BINS
                .iter()
                .filter_map(|p| Path::new(p).canonicalize().ok())
                .any(|bin| path.parent() == Some(bin.as_path())),
        "Executable is outside trusted system bin directories: {}",
        path.display()
    );
    Ok(path)
}

pub(crate) fn system_command(name: &str) -> Result<Command> {
    let project = std::env::current_dir()?;
    let nix_bin = option_env!("TURBO_LEAN_NIX_SYS_PATH")
        .into_iter()
        .flat_map(|s| s.split(':'))
        .filter(|d| !d.is_empty())
        .find_map(|dir| system_executable(&Path::new(dir).join(name), &project).ok());
    let bin = nix_bin
        .or_else(|| {
            SYSTEM_BINS
                .iter()
                .find_map(|dir| system_executable(&Path::new(dir).join(name), &project).ok())
        })
        .with_context(|| format!("No trusted system executable for {name}"))?;
    let mut command = Command::new(bin);
    command.env_clear().env("PATH", trusted_sys_path());
    Ok(command)
}

struct PrivateHome(PathBuf);
impl PrivateHome {
    fn new() -> Result<Self> {
        // Ignore project-controlled TMPDIR. create_dir is exclusive and permissions
        // are private before Git can observe any files in the directory.
        use std::os::unix::fs::DirBuilderExt;
        loop {
            let path = Path::new("/tmp").join(format!(
                "turbo-git-{}-{}",
                std::process::id(),
                crate::pack::next_tmp_id()
            ));
            match fs::DirBuilder::new().mode(0o700).create(&path) {
                Ok(()) => return Ok(Self(path)),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(e.into()),
            }
        }
    }
}
impl Drop for PrivateHome {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

pub(crate) struct GitCommand {
    command: Command,
    _home: PrivateHome,
}
impl Deref for GitCommand {
    type Target = Command;
    fn deref(&self) -> &Command {
        &self.command
    }
}
impl DerefMut for GitCommand {
    fn deref_mut(&mut self) -> &mut Command {
        &mut self.command
    }
}

/// Oldest Git that honors `GIT_NO_LAZY_FETCH`. Older Git silently fetches missing objects of a
/// partial clone, running repository-configured transports and credential helpers on the host.
const MIN_GIT: (u32, u32) = (2, 46);

fn parse_git_version(out: &str) -> Option<(u32, u32)> {
    let rest = out
        .lines()
        .find_map(|line| line.trim().strip_prefix("git version "))?;
    let mut parts = rest.split('.');
    let major = parts.next()?.parse().ok()?;
    let minor_digits: String = parts
        .next()?
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect();
    Some((major, minor_digits.parse().ok()?))
}

fn checked_git(path: PathBuf) -> Result<PathBuf> {
    let out = Command::new(&path)
        .arg("version")
        .env_clear()
        .env("PATH", trusted_sys_path())
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .current_dir("/")
        .output()
        .with_context(|| format!("Cannot run {}", path.display()))?;
    anyhow::ensure!(
        out.status.success(),
        "`{} version` exited with {}: {}",
        path.display(),
        out.status,
        String::from_utf8_lossy(&out.stderr).trim()
    );
    let text = String::from_utf8_lossy(&out.stdout);
    let version = parse_git_version(&text).with_context(|| {
        format!(
            "Unrecognized Git version output {:?} from {}",
            text.trim(),
            path.display()
        )
    })?;
    anyhow::ensure!(
        version >= MIN_GIT,
        "{} reports `{}` (parsed {}.{}); verification requires Git >= {}.{} (GIT_NO_LAZY_FETCH): fail-closed. \
         Install Git >= {}.{} or set TURBO_LEAN_GIT=/abs/path/to/git",
        path.display(),
        text.trim(),
        version.0,
        version.1,
        MIN_GIT.0,
        MIN_GIT.1,
        MIN_GIT.0,
        MIN_GIT.1
    );
    Ok(path)
}

fn resolve_trusted_git_uncached(project: &Path) -> Result<PathBuf> {
    if let Some(path) = std::env::var_os("TURBO_LEAN_GIT") {
        let raw = Path::new(&path);
        let vetted = outside_checkout(raw, project)
            .with_context(|| format!("Invalid TURBO_LEAN_GIT={}", raw.display()))?;
        return checked_git(vetted);
    }
    if let Some(nix_git) = option_env!("TURBO_LEAN_NIX_DEFAULT_GIT").filter(|s| !s.is_empty()) {
        if let Ok(vetted) = outside_checkout(Path::new(nix_git), project) {
            return checked_git(vetted);
        }
    }
    let candidate = SYSTEM_BINS
        .iter()
        .find_map(|dir| system_executable(&Path::new(dir).join("git"), project).ok())
        .context(
            "No trusted system Git in /usr/bin, /bin, /usr/local/bin, /usr/sbin, /sbin, or /run/current-system/sw/bin; \
             set TURBO_LEAN_GIT=/abs/path/to/git outside all checkouts",
        )?;
    checked_git(candidate)
}

/// Resolve once per process, then validate against every project (including
/// dependency checkouts). No inherited GIT_*, loader, shell or config environment.
/// Repository-local config and includes stay readable, so every key that can run a
/// program or reach the network is overridden on the command line, and lazy fetching
/// of missing partial-clone objects is disabled: a missing object is an error.
pub(crate) fn git(project: &Path) -> Result<GitCommand> {
    static GIT: OnceLock<std::result::Result<PathBuf, String>> = OnceLock::new();
    let program = GIT
        .get_or_init(|| resolve_trusted_git_uncached(project).map_err(|e| format!("{e:#}")))
        .as_ref()
        .map_err(|e| anyhow::anyhow!("Trusted Git unavailable: {e}"))?;
    let program = outside_checkout(program, project)?;
    let home = PrivateHome::new()?;
    let sys_path = trusted_sys_path();
    let prepare = |extra: &[String]| {
        let mut command = Command::new(&program);
        command
            .env_clear()
            .env("PATH", &sys_path)
            .env("HOME", &home.0)
            .env("XDG_CONFIG_HOME", &home.0)
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_ATTR_NOSYSTEM", "1")
            .env("GIT_NO_REPLACE_OBJECTS", "1")
            .env("GIT_TERMINAL_PROMPT", "0")
            .env("GIT_NO_LAZY_FETCH", "1")
            // An empty allowlist permits no transport at all. Unlike `protocol.allow`, it
            // cannot be relaxed by a repository's `protocol.<name>.allow`.
            .env("GIT_ALLOW_PROTOCOL", "")
            .env("GIT_OPTIONAL_LOCKS", "0")
            .env("LC_ALL", "C")
            .env_remove("GIT_ASKPASS")
            .env_remove("SSH_ASKPASS");
        // Overrides travel in GIT_CONFIG_PARAMETERS (the `-c` channel) so that every Git
        // process this one spawns inherits them too: Git keeps that variable even for the
        // child processes it runs inside submodules.
        let config = BASE_CONFIG
            .iter()
            .map(|(k, v)| (*k, *v))
            .chain(extra.iter().map(|k| (k.as_str(), filter_override(k))))
            .map(|(k, v)| format!("{}={}", sq_quote(k), sq_quote(v)))
            .collect::<Vec<_>>()
            .join(" ");
        command.env("GIT_CONFIG_PARAMETERS", config);
        command
    };
    let mut command = prepare(&[]);
    // Status/diff can run clean filters in this repository. Suppress its filters.
    // This is NOT checkout isolation: conditional includes can change with the
    // git directory. Verification snapshots must use raw objects, never checkout.
    // Nor does it cover a submodule's own config: callers must never let Git recurse
    // into submodules (`NO_SUBMODULES`, and `reject_gitlinks` where contents matter).
    let filters = command
        .args(["-C"])
        .arg(project)
        .args([
            "config",
            "--null",
            "--name-only",
            "--get-regexp",
            "^filter\\..*\\.(process|smudge|clean|required)$",
        ])
        .output()?;
    anyhow::ensure!(
        filters.status.success() || filters.status.code() == Some(1),
        "Cannot isolate repository Git filters: {}",
        String::from_utf8_lossy(&filters.stderr)
    );
    let keys = filters
        .stdout
        .split(|b| *b == 0)
        .filter(|s| !s.is_empty())
        .map(|k| Ok(std::str::from_utf8(k)?.to_owned()))
        .collect::<Result<Vec<_>>>()?;
    Ok(GitCommand {
        command: prepare(&keys),
        _home: home,
    })
}

/// Every key that could run a program, reach the network, or make Git recurse into a
/// submodule (whose own config, filters and includes this process never vetted).
const BASE_CONFIG: [(&str, &str); 13] = [
    ("core.fsmonitor", ""),
    ("core.hooksPath", "/dev/null"),
    ("core.sshCommand", "false"),
    ("core.askPass", ""),
    ("credential.helper", ""),
    ("protocol.allow", "never"),
    ("diff.external", ""),
    ("log.showSignature", "false"),
    ("core.pager", "cat"),
    ("core.attributesFile", "/dev/null"),
    ("submodule.recurse", "false"),
    ("diff.ignoreSubmodules", "all"),
    ("status.submoduleSummary", "false"),
];

/// Pass to every `status`/`diff` on a verification path. Config alone is not enough: a
/// repository's `submodule.<name>.ignore` outranks `diff.ignoreSubmodules`, and recursing
/// runs `git status` inside the submodule with that submodule's own filters.
pub(crate) const NO_SUBMODULES: &str = "--ignore-submodules=all";

fn filter_override(key: &str) -> &'static str {
    if key.ends_with(".required") {
        "false"
    } else {
        ""
    }
}

/// Git's `sq_quote`: the encoding `GIT_CONFIG_PARAMETERS` is parsed with.
fn sq_quote(s: &str) -> String {
    format!("'{}'", s.replace('\'', "'\\''").replace('!', "'\\!'"))
}

/// Fail closed on submodule gitlinks in the index (and in `revs`) under `pathspec`. Their
/// contents are never inspected, so a dirty-state or source answer would be incomplete.
/// Neither `ls-files -s` nor `ls-tree` enters a submodule.
pub(crate) fn reject_gitlinks(repo: &Path, revs: &[&str], pathspec: &Path) -> Result<()> {
    reject_gitlinks_filtered(repo, revs, pathspec, |_| true)
}

/// Like `reject_gitlinks`, but invokes `touches_lean` with the repository-relative path of each
/// `160000` gitlink entry and only rejects gitlinks for which `touches_lean` returns `true`.
pub(crate) fn reject_gitlinks_filtered<F>(
    repo: &Path,
    revs: &[&str],
    pathspec: &Path,
    mut touches_lean: F,
) -> Result<()>
where
    F: FnMut(&Path) -> bool,
{
    use std::os::unix::ffi::OsStrExt;
    let mut lists = vec![git(repo)?
        .arg("-C")
        .arg(repo)
        .args(["ls-files", "-s", "-z", "--"])
        .arg(pathspec)
        .output()?];
    for rev in revs {
        anyhow::ensure!(!rev.starts_with('-'), "Invalid git revision `{rev}`");
        lists.push(
            git(repo)?
                .arg("-C")
                .arg(repo)
                .args(["ls-tree", "-r", "-z", rev, "--"])
                .arg(pathspec)
                .output()?,
        );
    }
    for out in lists {
        anyhow::ensure!(
            out.status.success(),
            "Cannot list Git entries: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        );
        for link in out
            .stdout
            .split(|b| *b == 0)
            .filter(|e| e.starts_with(b"160000 "))
        {
            let path = link.splitn(2, |b| *b == b'\t').nth(1).unwrap_or_default();
            let rel = Path::new(std::ffi::OsStr::from_bytes(path));
            if touches_lean(rel) {
                anyhow::bail!(
                    "Submodule gitlinks are not supported on verification paths (their contents \
                     and config are never inspected): {}",
                    String::from_utf8_lossy(path)
                );
            }
        }
    }
    Ok(())
}

#[cfg(test)]
#[test]
fn trusted_executables_reject_relative_and_checkout_symlink_targets() -> Result<()> {
    use std::os::unix::fs::symlink;
    let root = std::env::temp_dir().join(format!(
        "turbo-trusted-tools-{}-{}",
        std::process::id(),
        crate::pack::next_tmp_id()
    ));
    fs::create_dir_all(root.join(".git"))?;
    fs::create_dir_all(root.join("sub"))?;
    fs::copy("/usr/bin/true", root.join("git"))?;
    symlink(root.join("git"), root.join("link"))?;
    assert!(outside_checkout(Path::new("git"), &root).is_err());
    assert!(outside_checkout(&root.join("link"), &root.join("sub")).is_err());
    // Even another checkout cannot provide an operator override or system tool.
    assert!(outside_checkout(&root.join("link"), Path::new("/tmp")).is_err());
    assert!(system_executable(&root.join("link"), &root).is_err());
    assert!(system_executable(Path::new("/usr/bin/git"), &root).is_ok());
    fs::remove_dir_all(root)?;
    Ok(())
}

#[cfg(test)]
pub(crate) fn discover_or_skip_trusted_git_for_test(project: &Path) -> Result<Option<PathBuf>> {
    if let Some(raw) = std::env::var_os("TURBO_LEAN_GIT") {
        let vetted = outside_checkout(Path::new(&raw), project)
            .with_context(|| format!("Invalid TURBO_LEAN_GIT={}", Path::new(&raw).display()))?;
        return checked_git(vetted).map(Some);
    }
    let mut candidates: Vec<PathBuf> = SYSTEM_BINS
        .iter()
        .map(|d| Path::new(d).join("git"))
        .collect();
    for extra in [
        "/opt/homebrew/bin/git",
        "/usr/local/git/bin/git",
        "/nix/var/nix/profiles/default/bin/git",
    ] {
        candidates.push(PathBuf::from(extra));
    }
    if let Some(path_env) = std::env::var_os("PATH") {
        for dir in std::env::split_paths(&path_env) {
            candidates.push(dir.join("git"));
        }
    }
    for cand in candidates {
        if let Ok(vetted) = outside_checkout(&cand, project) {
            if let Ok(ok_git) = checked_git(vetted) {
                return Ok(Some(ok_git));
            }
        }
    }
    if std::env::var_os("CI").is_some() {
        anyhow::bail!(
            "CI requires Git >= {}.{} for trusted_tools tests (or explicit TURBO_LEAN_GIT)",
            MIN_GIT.0,
            MIN_GIT.1
        );
    }
    eprintln!(
        "skipping trusted_tools Git >= {}.{} runtime test in local non-CI environment (host Git < {}.{})",
        MIN_GIT.0, MIN_GIT.1, MIN_GIT.0, MIN_GIT.1
    );
    Ok(None)
}

#[cfg(test)]
#[test]
fn trusted_git_rejects_old_versions() -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    assert_eq!(parse_git_version("git version 2.46.0\n"), Some((2, 46)));
    assert_eq!(
        parse_git_version("git version 2.46.1 (Apple Git-155)\n"),
        Some((2, 46))
    );
    assert_eq!(parse_git_version("git version 2.47.rc1\n"), Some((2, 47)));
    assert_eq!(
        parse_git_version("git version 2.43.0.windows.1"),
        Some((2, 43))
    );
    assert_eq!(parse_git_version("not git"), None);
    let root = std::env::temp_dir().join(format!(
        "turbo-old-git-{}-{}",
        std::process::id(),
        crate::pack::next_tmp_id()
    ));
    fs::create_dir_all(&root)?;
    for (version, ok) in [
        ("2.43.0", false),
        ("2.45.9", false),
        ("2.46.0", true),
        ("3.0.0", true),
    ] {
        let fake = root.join(format!("git-{version}"));
        fs::write(&fake, format!("#!/bin/sh\necho 'git version {version}'\n"))?;
        fs::set_permissions(&fake, fs::Permissions::from_mode(0o755))?;
        let checked = checked_git(fake);
        assert_eq!(checked.is_ok(), ok, "{version}: {checked:?}");
        if !ok {
            let msg = format!("{:#}", checked.unwrap_err());
            assert!(
                msg.contains("Git >= 2.46") && msg.contains("TURBO_LEAN_GIT"),
                "{msg}"
            );
        }
    }
    let bad_exit = root.join("git-exit-1");
    fs::write(&bad_exit, "#!/bin/sh\necho 'fatal: broken' >&2\nexit 1\n")?;
    fs::set_permissions(&bad_exit, fs::Permissions::from_mode(0o755))?;
    let err = checked_git(bad_exit).expect_err("non-zero git version must fail closed");
    assert!(format!("{err:#}").contains("exited with"), "{err:#}");
    fs::remove_dir_all(root)?;
    Ok(())
}

/// A repository-local promisor remote, transport command and credential helper must never run
/// through the trusted wrapper. Positive controls first prove plain Git runs each of them.
#[cfg(test)]
#[test]
fn trusted_git_never_lazily_fetches_or_runs_repository_helpers() -> Result<()> {
    let root = std::env::temp_dir().join(format!(
        "turbo-lazy-fetch-{}-{}",
        std::process::id(),
        crate::pack::next_tmp_id()
    ));
    let repo = root.join("repo");
    fs::create_dir_all(&repo)?;
    let Some(git_bin) = discover_or_skip_trusted_git_for_test(&repo)? else {
        let _ = fs::remove_dir_all(&root);
        return Ok(());
    };
    if std::env::var_os("TURBO_LEAN_GIT").is_none() {
        std::env::set_var("TURBO_LEAN_GIT", &git_bin);
    }
    let marker = root.join("marker");
    // Plain Git with no inherited environment, like a host user or CI shell.
    let plain = |args: &[&str]| {
        Command::new(&git_bin)
            .env_clear()
            .env("PATH", "/usr/bin:/bin")
            .env("HOME", &root)
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .current_dir(&repo)
            .args(args)
            .stdin(std::process::Stdio::piped())
            .output()
    };
    let ok = |args: &[&str]| -> Result<String> {
        let out = plain(args)?;
        anyhow::ensure!(out.status.success(), "{args:?}: {out:?}");
        Ok(String::from_utf8(out.stdout)?.trim().to_string())
    };
    ok(&["init", "-q"])?;
    fs::write(repo.join("A.lean"), "theorem a : True := trivial\n")?;
    ok(&["add", "A.lean"])?;
    ok(&[
        "-c",
        "user.name=t",
        "-c",
        "user.email=t@t",
        "commit",
        "-qm",
        "base",
    ])?;
    let oid = ok(&["rev-parse", "HEAD:A.lean"])?;
    fs::remove_file(repo.join(".git/objects").join(&oid[..2]).join(&oid[2..]))?;
    let touch = format!("sh -c 'touch {}; exit 1' --", marker.display());
    for (key, value) in [
        ("remote.origin.url", "ssh://example.invalid/repo"),
        ("remote.origin.promisor", "true"),
        ("extensions.partialClone", "origin"),
        ("core.sshCommand", &touch),
        ("protocol.ssh.allow", "always"),
        (
            "credential.helper",
            &format!("!touch {} #", marker.display()),
        ),
    ] {
        ok(&["config", key, value])?;
    }
    // Positive controls: Git lazily fetches the promised blob over the repository's
    // ssh command, and runs the repository's credential helper.
    assert!(!plain(&["cat-file", "-p", "HEAD:A.lean"])?.status.success());
    assert!(marker.exists(), "lazy fetch control did not run sshCommand");
    fs::remove_file(&marker)?;
    let mut fill = Command::new(&git_bin);
    fill.env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("HOME", &root)
        .env("GIT_TERMINAL_PROMPT", "0")
        .current_dir(&repo)
        .args(["credential", "fill"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    let mut child = fill.spawn()?;
    use std::io::Write;
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b"protocol=https\nhost=example.invalid\n\n")?;
    child.wait()?;
    assert!(marker.exists(), "credential helper control did not run");
    fs::remove_file(&marker)?;

    for args in [
        &["cat-file", "-p", "HEAD:A.lean"][..],
        &["show", "--no-textconv", "HEAD:A.lean"],
        &["fetch", "origin"],
    ] {
        let out = git(&repo)?.arg("-C").arg(&repo).args(args).output()?;
        assert!(!out.status.success(), "{args:?}");
        assert!(!marker.exists(), "{args:?} ran a repository helper");
    }
    let mut child = git(&repo)?
        .arg("-C")
        .arg(&repo)
        .args(["credential", "fill"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()?;
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b"protocol=https\nhost=example.invalid\n\n")?;
    child.wait()?;
    assert!(
        !marker.exists(),
        "credential helper ran through trusted Git"
    );
    // Reading base blobs by object id reports the missing object instead of skipping it.
    let err = crate::pr_verify::fetch_git_blobs_batch(&repo, "HEAD", &["A.lean".into()])
        .expect_err("missing promised blob must fail closed");
    assert!(format!("{err:#}").contains("missing"), "{err:#}");
    assert!(!marker.exists());
    fs::remove_dir_all(root)?;
    Ok(())
}

/// Test fixture: a repository with an initialized submodule `dep` whose tracked `data.txt`
/// has a clean filter defined ONLY in the submodule's own config (directly, or through an
/// `include.path` there) that touches `marker`. `data.txt` is modified with a new mtime, so
/// any `git status`/`diff` that enters the submodule runs the filter.
#[cfg(test)]
pub(crate) fn submodule_filter_fixture(root: &Path, via_include: bool) -> Result<PathBuf> {
    let git_bin = std::env::var_os("TURBO_LEAN_GIT")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/usr/bin/git"));
    let plain = |dir: &Path, args: &[&str]| -> Result<()> {
        let out = Command::new(&git_bin)
            .env_clear()
            .env("PATH", "/usr/bin:/bin")
            .env("HOME", root)
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .args(["-c", "user.name=t", "-c", "user.email=t@t"])
            .args(["-c", "protocol.file.allow=always"])
            .current_dir(dir)
            .args(args)
            .output()?;
        anyhow::ensure!(out.status.success(), "{args:?}: {out:?}");
        Ok(())
    };
    let (sub, repo, marker) = (root.join("sub"), root.join("repo"), root.join("marker"));
    fs::create_dir_all(&sub)?;
    fs::create_dir_all(&repo)?;
    plain(&sub, &["init", "-q"])?;
    fs::write(sub.join(".gitattributes"), "*.txt filter=subattack\n")?;
    fs::write(sub.join("data.txt"), "a\n")?;
    fs::write(sub.join("S.lean"), "def s := 1\n")?;
    plain(&sub, &["add", "."])?;
    plain(&sub, &["commit", "-qm", "sub"])?;
    plain(&repo, &["init", "-q"])?;
    fs::write(repo.join("lean-toolchain"), "leanprover/lean4:v4.35.0\n")?;
    fs::write(repo.join(".gitignore"), ".lake/\ncache/\ncache-staging/\n")?;
    fs::write(
        repo.join("Demo.lean"),
        "theorem pinned : 1 + 1 = 2 := rfl\n",
    )?;
    plain(&repo, &["add", "."])?;
    plain(&repo, &["commit", "-qm", "base"])?;
    plain(
        &repo,
        &["submodule", "add", "-q", &sub.to_string_lossy(), "dep"],
    )?;
    plain(&repo, &["commit", "-qm", "dep"])?;
    let filter = format!("touch '{}'; cat", marker.display());
    let dep = repo.join("dep");
    if via_include {
        let inc = root.join("sub-include");
        plain(
            root,
            &[
                "config",
                "--file",
                &inc.to_string_lossy(),
                "filter.subattack.clean",
                &filter,
            ],
        )?;
        plain(&dep, &["config", "include.path", &inc.to_string_lossy()])?;
    } else {
        plain(&dep, &["config", "filter.subattack.clean", &filter])?;
    }
    fs::write(dep.join("data.txt"), "b\n")?;
    Ok(repo)
}

/// Give `data.txt` a new mtime (same size as the committed blob) so Git cannot decide from
/// stat data alone and must run the clean filter to compare contents.
#[cfg(test)]
pub(crate) fn restat_submodule_file(repo: &Path) -> Result<()> {
    use std::sync::atomic::{AtomicU64, Ordering};
    static RESTAT: AtomicU64 = AtomicU64::new(0);
    let f = fs::File::options()
        .append(true)
        .open(repo.join("dep/data.txt"))?;
    f.set_modified(
        std::time::SystemTime::now()
            + std::time::Duration::from_secs(1 + RESTAT.fetch_add(1, Ordering::Relaxed)),
    )?;
    Ok(())
}

/// A clean filter defined only in a submodule's config (or an include there) is invisible to
/// the superproject's filter enumeration. Plain `git status` runs it; trusted Git must never
/// enter the submodule, and gitlinks are refused where their contents would matter.
#[cfg(test)]
#[test]
fn trusted_git_never_runs_submodule_only_filters() -> Result<()> {
    let probe_dir = std::env::temp_dir();
    let Some(git_bin) = discover_or_skip_trusted_git_for_test(&probe_dir)? else {
        return Ok(());
    };
    if std::env::var_os("TURBO_LEAN_GIT").is_none() {
        std::env::set_var("TURBO_LEAN_GIT", &git_bin);
    }
    for via_include in [false, true] {
        let root = std::env::temp_dir().join(format!(
            "turbo-sub-filter-{}-{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let repo = submodule_filter_fixture(&root, via_include)?;
        let marker = root.join("marker");
        let plain = |args: &[&str]| -> Result<std::process::Output> {
            restat_submodule_file(&repo)?;
            Ok(Command::new(&git_bin)
                .env_clear()
                .env("PATH", "/usr/bin:/bin")
                .env("HOME", &root)
                .env("GIT_CONFIG_NOSYSTEM", "1")
                .current_dir(&repo)
                .args(args)
                .output()?)
        };
        // The superproject's effective config does not contain the filter.
        assert_eq!(
            plain(&["config", "--get", "filter.subattack.clean"])?
                .status
                .code(),
            Some(1)
        );
        // Positive controls: plain status and diff recurse and run the submodule's filter.
        for args in [
            &["status", "--porcelain"][..],
            &["diff", "--name-only", "HEAD"],
        ] {
            assert!(plain(args)?.status.success());
            assert!(
                marker.exists(),
                "{via_include}: control {args:?} did not run the filter"
            );
            fs::remove_file(&marker)?;
        }
        // Trusted Git, with and without the explicit flag (config defaults), and even with a
        // repository `submodule.<name>.ignore=none` that outranks `diff.ignoreSubmodules`.
        for repo_ignore in [None, Some("none")] {
            if let Some(v) = repo_ignore {
                assert!(plain(&["config", "submodule.dep.ignore", v])?
                    .status
                    .success());
            }
            let mut cases = vec![
                vec!["status", "--porcelain", "-uall", NO_SUBMODULES],
                vec![
                    "status",
                    "--porcelain=v1",
                    "-z",
                    "--untracked-files=all",
                    NO_SUBMODULES,
                ],
                vec![
                    "diff",
                    "--no-ext-diff",
                    "--no-textconv",
                    NO_SUBMODULES,
                    "--name-only",
                    "HEAD",
                ],
                vec!["ls-files", "--others", "--exclude-standard"],
                vec![
                    "ls-files",
                    "-z",
                    "--cached",
                    "--others",
                    "--exclude-standard",
                ],
                vec!["ls-files", "-s", "-z"],
                vec!["ls-tree", "-r", "-z", "HEAD"],
            ];
            if repo_ignore.is_none() {
                cases.push(vec!["status", "--porcelain"]);
                cases.push(vec!["diff", "--name-only", "HEAD"]);
            }
            for args in cases {
                restat_submodule_file(&repo)?;
                let out = git(&repo)?.arg("-C").arg(&repo).args(&args).output()?;
                assert!(out.status.success(), "{args:?}: {out:?}");
                assert!(
                    !marker.exists(),
                    "{via_include} {repo_ignore:?}: {args:?} ran the filter"
                );
            }
        }
        // Inherited by child processes: GIT_CONFIG_PARAMETERS carries the overrides.
        let probe = git(&repo)?
            .arg("-C")
            .arg(&repo)
            .args([
                "config",
                "--show-scope",
                "--get-regexp",
                "^(submodule\\.recurse|diff\\.ignoresubmodules|status\\.submodulesummary)$",
            ])
            .output()?;
        let shown = String::from_utf8(probe.stdout)?;
        for line in [
            "command\tsubmodule.recurse false",
            "command\tdiff.ignoresubmodules all",
            "command\tstatus.submodulesummary false",
        ] {
            assert!(shown.contains(line), "{shown}");
        }
        let err = reject_gitlinks(&repo, &["HEAD"], &repo).expect_err("gitlink must be refused");
        assert!(format!("{err:#}").contains("gitlinks") && format!("{err:#}").contains("dep"));
        // Outside the gitlink's pathspec the repository is acceptable.
        reject_gitlinks(&repo, &["HEAD"], &repo.join("Demo.lean"))?;
        assert!(!marker.exists());
        fs::remove_dir_all(root)?;
    }
    Ok(())
}

#[cfg(test)]
#[test]
fn trusted_git_uncached_resolution_validates_override_and_ci_fail_closed() -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let _env_guard = crate::pack::tests::env_test_lock()
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let prev_git = std::env::var_os("TURBO_LEAN_GIT");
    let prev_ci = std::env::var_os("CI");
    let root = Path::new("/tmp").join(format!(
        "turbo-trusted-git-res-{}-{}",
        std::process::id(),
        crate::pack::next_tmp_id()
    ));
    let proj = root.join("proj");
    let bins = root.join("bins");
    fs::create_dir_all(proj.join(".git"))?;
    fs::create_dir_all(&bins)?;

    let in_repo = proj.join("git-fake");
    fs::write(&in_repo, "#!/bin/sh\necho 'git version 2.46.0'\n")?;
    fs::set_permissions(&in_repo, fs::Permissions::from_mode(0o755))?;
    std::env::set_var("TURBO_LEAN_GIT", &in_repo);
    let err_inside = resolve_trusted_git_uncached(&proj)
        .expect_err("TURBO_LEAN_GIT inside checkout must fail closed");
    assert!(
        format!("{err_inside:#}").contains("inside a project/checkout"),
        "{err_inside:#}"
    );

    let old_bin = bins.join("git-2.43");
    fs::write(&old_bin, "#!/bin/sh\necho 'git version 2.43.0'\n")?;
    fs::set_permissions(&old_bin, fs::Permissions::from_mode(0o755))?;
    std::env::set_var("TURBO_LEAN_GIT", &old_bin);
    let err_old =
        resolve_trusted_git_uncached(&proj).expect_err("TURBO_LEAN_GIT < 2.46 must fail closed");
    assert!(
        format!("{err_old:#}").contains("Git >= 2.46"),
        "{err_old:#}"
    );

    let new_bin = bins.join("git-2.46");
    fs::write(&new_bin, "#!/bin/sh\necho 'git version 2.46.2'\n")?;
    fs::set_permissions(&new_bin, fs::Permissions::from_mode(0o755))?;
    std::env::set_var("TURBO_LEAN_GIT", &new_bin);
    let resolved = resolve_trusted_git_uncached(&proj)?;
    assert_eq!(resolved, new_bin.canonicalize()?);

    std::env::set_var("CI", "1");
    std::env::set_var("TURBO_LEAN_GIT", &old_bin);
    assert!(discover_or_skip_trusted_git_for_test(&proj).is_err());

    match prev_git {
        Some(v) => std::env::set_var("TURBO_LEAN_GIT", v),
        None => std::env::remove_var("TURBO_LEAN_GIT"),
    }
    match prev_ci {
        Some(v) => std::env::set_var("CI", v),
        None => std::env::remove_var("CI"),
    }
    let _ = fs::remove_dir_all(&root);
    Ok(())
}
