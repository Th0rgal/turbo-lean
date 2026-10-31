//! Host tools used at verification boundaries must never come from project PATH.
use anyhow::{Context, Result};
use std::fs;
use std::ops::{Deref, DerefMut};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

const SYSTEM_BINS: [&str; 5] = ["/usr/bin", "/bin", "/usr/local/bin", "/usr/sbin", "/sbin"];

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
    anyhow::ensure!(
        SYSTEM_BINS
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
    let bin = SYSTEM_BINS
        .iter()
        .find_map(|dir| system_executable(&Path::new(dir).join(name), &project).ok())
        .with_context(|| format!("No trusted system executable for {name}"))?;
    let mut command = Command::new(bin);
    command.env_clear().env("PATH", "/usr/bin:/bin");
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

/// Resolve once per process, then validate against every project (including
/// dependency checkouts). No inherited GIT_*, loader, shell or config environment.
pub(crate) fn git(project: &Path) -> Result<GitCommand> {
    static GIT: OnceLock<std::result::Result<PathBuf, String>> = OnceLock::new();
    let program = GIT.get_or_init(|| {
        (|| -> Result<PathBuf> {
            if let Some(path) = std::env::var_os("TURBO_LEAN_GIT") {
                return outside_checkout(Path::new(&path), project);
            }
            SYSTEM_BINS.iter().find_map(|dir| system_executable(&Path::new(dir).join("git"), project).ok())
                .context("No trusted system Git; set TURBO_LEAN_GIT to an absolute executable outside all checkouts")
        })().map_err(|e| e.to_string())
    }).as_ref().map_err(|e| anyhow::anyhow!("Trusted Git unavailable: {e}"))?;
    let program = outside_checkout(program, project)?;
    let home = PrivateHome::new()?;
    let prepare = || {
        let mut command = Command::new(&program);
        command
            .env_clear()
            .env("PATH", "/usr/bin:/bin")
            .env("HOME", &home.0)
            .env("XDG_CONFIG_HOME", &home.0)
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_ATTR_NOSYSTEM", "1")
            .env("GIT_NO_REPLACE_OBJECTS", "1")
            .env("GIT_TERMINAL_PROMPT", "0")
            .env("GIT_OPTIONAL_LOCKS", "0")
            .env("LC_ALL", "C")
            .args([
                "-c",
                "core.fsmonitor=",
                "-c",
                "core.hooksPath=/dev/null",
                "-c",
                "diff.external=",
                "-c",
                "core.pager=cat",
                "-c",
                "core.attributesFile=/dev/null",
            ]);
        command
    };
    let mut command = prepare();
    // Status/diff can run clean filters in this repository. Suppress its filters.
    // This is NOT checkout isolation: conditional includes can change with the
    // git directory. Verification snapshots must use raw objects, never checkout.
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
    let mut isolated = prepare();
    for key in filters.stdout.split(|b| *b == 0).filter(|s| !s.is_empty()) {
        let key = std::str::from_utf8(key)?;
        isolated.arg("-c").arg(format!(
            "{key}={}",
            if key.ends_with(".required") {
                "false"
            } else {
                ""
            }
        ));
    }
    Ok(GitCommand {
        command: isolated,
        _home: home,
    })
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
