//! Real Lake fixtures and complete filesystem identity snapshots for opt-out regressions.
use anyhow::Result;
use std::fs;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::Command;

pub(crate) struct LakeTree {
    pub root: PathBuf,
    pub project: PathBuf,
}

impl LakeTree {
    pub fn new(label: &str, sources: &[(&str, &str)]) -> Result<Self> {
        let root = std::env::temp_dir().join(format!(
            "turbo_optout_{label}_{}_{}",
            std::process::id(),
            crate::pack::next_tmp_id()
        ));
        let project = root.join("project");
        fs::create_dir_all(&project)?;
        fs::write(
            project.join("lean-toolchain"),
            include_str!("../../../lean/lean-toolchain"),
        )?;
        fs::write(project.join("lakefile.toml"),
            "name = \"fixture\"\ndefaultTargets = [\"P\"]\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n")?;
        fs::write(project.join(".gitignore"), ".lake/\n")?;
        for (rel, source) in sources {
            let path = project.join(rel);
            fs::create_dir_all(path.parent().unwrap())?;
            fs::write(path, source)?;
        }
        let tree = Self { root, project };
        tree.lake(&["build", "P"])?;
        Ok(tree)
    }

    pub fn imports(label: &str) -> Result<Self> {
        Self::new(
            label,
            &[
                ("P/A.lean", "def a : Nat := 1\n"),
                (
                    "P/Middle.lean",
                    "import P.A\ntheorem middle : a = 1 := rfl\n",
                ),
                (
                    "P/Target.lean",
                    "import P.Middle\ntheorem target : a = 1 := rfl\n",
                ),
            ],
        )
    }

    pub fn lake(&self, args: &[&str]) -> Result<()> {
        let out = Command::new("lake")
            .args(args)
            .current_dir(&self.project)
            .output()?;
        anyhow::ensure!(
            out.status.success(),
            "lake {args:?}: {}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        Ok(())
    }

    pub fn opt_out(&self) -> Result<()> {
        fs::write(
            self.project.join("turbo-lean.toml"),
            "[worktree]\nauto_link = false\n",
        )?;
        Ok(())
    }

    pub fn stale_import(&self) -> Result<()> {
        let path = self.project.join("P/A.lean");
        fs::write(
            &path,
            "def a : Nat := 1\n-- edited after Lake built the imports\n",
        )?;
        // Ensure strict ordering even on filesystems with coarse timestamp resolution.
        fs::File::options()
            .write(true)
            .open(path)?
            .set_modified(std::time::SystemTime::now() + std::time::Duration::from_secs(2))?;
        Ok(())
    }

    /// Exercise preservation of read-only and shared artifacts, with no pre-existing lock.
    pub fn prepare_snapshot(&self, rel: &str) -> Result<()> {
        let lock = self.project.join(".lake/build/.turbo_publish.lock");
        if lock.exists() {
            fs::remove_file(&lock)?;
        }
        assert!(!lock.exists());
        let artifact = self.project.join(rel);
        fs::set_permissions(&artifact, fs::Permissions::from_mode(0o444))?;
        fs::hard_link(&artifact, self.root.join("external-link"))?;
        Ok(())
    }
}

impl Drop for LakeTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Entry(PathBuf, u64, u64, u32, u64, (i64, i64), (i64, i64), Vec<u8>);

/// Includes every entry, contents, inode, mode, link count, and modification/change time.
pub(crate) fn snapshot(project: &Path) -> Result<Vec<Entry>> {
    let mut rows = Vec::new();
    for entry in walkdir::WalkDir::new(project.join(".lake")) {
        let entry = entry?;
        let p = entry.path();
        let m = fs::symlink_metadata(p)?;
        let bytes = if m.is_file() {
            fs::read(p)?
        } else if m.file_type().is_symlink() {
            fs::read_link(p)?.as_os_str().as_encoded_bytes().to_vec()
        } else {
            Vec::new()
        };
        rows.push(Entry(
            p.strip_prefix(project)?.to_path_buf(),
            m.dev(),
            m.ino(),
            m.mode(),
            m.nlink(),
            (m.mtime(), m.mtime_nsec()),
            (m.ctime(), m.ctime_nsec()),
            bytes,
        ));
    }
    rows.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(rows)
}

pub(crate) fn assert_stale_error(err: &anyhow::Error) {
    let text = err.to_string();
    assert!(
        text.contains("Worktree opt-out prevents refreshing stale imports: P.A, P.Middle"),
        "{text}"
    );
    assert!(
        text.contains("Rebuild explicitly with Lake (`lake build P.A P.Middle`)"),
        "{text}"
    );
}

/// Re-execute one test in an isolated process, keeping environment changes out of other tests.
pub(crate) struct TestChild(std::process::Child);

impl TestChild {
    pub fn command(test: &str) -> Result<Command> {
        let mut command = Command::new(std::env::current_exe()?);
        command
            .args(["--exact", test, "--nocapture"])
            .env("TURBO_LEAN_TELEMETRY", "off")
            .env("LEAN_NATIVE_TELEMETRY", "off")
            .env("TURBO_LEAN_NO_REMOTE_TELEMETRY", "1");
        Ok(command)
    }

    pub fn spawn(command: &mut Command) -> Result<Self> {
        Ok(Self(command.spawn()?))
    }

    pub fn wait_for(&mut self, path: &Path) -> Result<()> {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(30);
        while !path.exists() {
            anyhow::ensure!(
                self.0.try_wait()?.is_none(),
                "child exited before {}",
                path.display()
            );
            anyhow::ensure!(
                std::time::Instant::now() < deadline,
                "child timed out: {}",
                path.display()
            );
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        Ok(())
    }

    pub fn assert_blocked(&mut self, done: &Path) -> Result<()> {
        std::thread::sleep(std::time::Duration::from_millis(250));
        anyhow::ensure!(
            !done.exists() && self.0.try_wait()?.is_none(),
            "publication lock did not block child"
        );
        Ok(())
    }

    pub fn finish(&mut self, done: &Path) -> Result<()> {
        self.wait_for(done)?;
        anyhow::ensure!(self.0.wait()?.success(), "child test failed");
        Ok(())
    }
}

impl Drop for TestChild {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}
