#[cfg(not(unix))]
use crate::db::TurboStore;
use crate::pack::next_tmp_id;
use anyhow::Result;
use std::fs;
use std::path::{Path, PathBuf};

use super::*;

/// Test-only fault injection: named callbacks fired at race-sensitive points of the digest /
/// import pipeline, and a forced filesystem timestamp granularity. Thread-local, so parallel
/// tests never observe each other's hooks; compiled out of non-test builds.
#[cfg(test)]
pub(crate) mod digest_test_hooks {
    use std::cell::{Cell, RefCell};
    use std::collections::HashMap;
    use std::sync::atomic::{AtomicI64, Ordering};
    type Hook = Box<dyn FnMut()>;
    static FORCED_TS_GRANULARITY_SHARED_NS: AtomicI64 = AtomicI64::new(0);
    thread_local! {
        static HOOKS: RefCell<HashMap<&'static str, Hook>> = RefCell::new(HashMap::new());
        static FORCED_TS_GRANULARITY_TLS_NS: Cell<Option<i128>> = const { Cell::new(None) };
    }
    pub(crate) fn set_forced_ts_granularity_ns(val: Option<i128>) {
        FORCED_TS_GRANULARITY_TLS_NS.with(|c| c.set(val));
    }
    pub(crate) fn set_forced_ts_granularity_shared_ns(val: Option<i64>) {
        FORCED_TS_GRANULARITY_SHARED_NS.store(val.unwrap_or(0), Ordering::SeqCst);
    }
    pub(crate) fn forced_ts_granularity_ns() -> Option<i128> {
        FORCED_TS_GRANULARITY_TLS_NS.with(|c| c.get()).or_else(|| {
            let v = FORCED_TS_GRANULARITY_SHARED_NS.load(Ordering::SeqCst);
            (v > 0).then_some(v as i128)
        })
    }
    pub(crate) fn set(name: &'static str, hook: impl FnMut() + 'static) {
        HOOKS.with(|h| h.borrow_mut().insert(name, Box::new(hook)));
    }
    pub(crate) fn clear() {
        HOOKS.with(|h| h.borrow_mut().clear());
        set_forced_ts_granularity_ns(None);
        set_forced_ts_granularity_shared_ns(None);
    }
    pub(crate) fn has_active_hooks() -> bool {
        HOOKS.with(|h| !h.borrow().is_empty()) || forced_ts_granularity_ns().is_some()
    }
    pub(super) fn run(name: &'static str) {
        let Some(mut hook) = HOOKS.with(|h| h.borrow_mut().remove(name)) else {
            return;
        };
        // Taken out while it runs, so a hook may itself hash (and fire hooks).
        hook();
        HOOKS.with(|h| {
            h.borrow_mut().entry(name).or_insert(hook);
        });
    }
}

#[inline(always)]
pub(super) fn has_active_digest_test_hook() -> bool {
    #[cfg(test)]
    {
        digest_test_hooks::has_active_hooks()
    }
    #[cfg(not(test))]
    {
        false
    }
}

#[inline(always)]
pub(super) fn run_digest_test_hook(_name: &'static str) {
    #[cfg(test)]
    digest_test_hooks::run(_name);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub(crate) struct OleanFileStatSig {
    pub(crate) dev: u64,
    pub(crate) ino: u64,
    pub(crate) mtime_sec: i64,
    pub(crate) mtime_nsec: i64,
    pub(crate) ctime_sec: i64,
    pub(crate) ctime_nsec: i64,
    pub(crate) size: u64,
}

impl OleanFileStatSig {
    pub(crate) fn from_meta(meta: &fs::Metadata) -> Self {
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            #[allow(unused_mut)]
            let mut sig = Self {
                dev: meta.dev(),
                ino: meta.ino(),
                mtime_sec: meta.mtime(),
                mtime_nsec: meta.mtime_nsec(),
                ctime_sec: meta.ctime(),
                ctime_nsec: meta.ctime_nsec(),
                size: meta.len(),
            };
            // Emulate a filesystem that only stores timestamps at the forced granularity.
            #[cfg(test)]
            if let Some(g) = digest_test_hooks::forced_ts_granularity_ns() {
                let trunc = |sec: i64, nsec: i64| {
                    let ns = ((sec as i128) * 1_000_000_000 + nsec as i128).div_euclid(g) * g;
                    (
                        ns.div_euclid(1_000_000_000) as i64,
                        ns.rem_euclid(1_000_000_000) as i64,
                    )
                };
                (sig.mtime_sec, sig.mtime_nsec) = trunc(sig.mtime_sec, sig.mtime_nsec);
                (sig.ctime_sec, sig.ctime_nsec) = trunc(sig.ctime_sec, sig.ctime_nsec);
            }
            sig
        }
        #[cfg(not(unix))]
        {
            let (ms, mn, sz) = TurboStore::extract_file_stat_tuple(meta);
            Self {
                dev: 0,
                ino: 0,
                mtime_sec: ms,
                mtime_nsec: mn,
                ctime_sec: 0,
                ctime_nsec: 0,
                size: sz as u64,
            }
        }
    }

    pub(crate) fn ctime_ns(&self) -> i128 {
        (self.ctime_sec as i128) * 1_000_000_000 + (self.ctime_nsec as i128)
    }
}

/// Stat-tuple trust rule for `FILE_DIGEST_MEMO`.
///
/// A memoized entry digest is reused on a matching `(dev, ino, mtime, ctime, size)` tuple only
/// if any later rewrite must change that tuple. Every write sets `ctime` to the kernel clock
/// truncated to the filesystem granularity `g`, so this holds when:
/// 1. `g` is proven sub-second for the file's device: a stored `ctime`/`mtime` with non-zero
///    nanoseconds was observed, or a probe file created next to it got one; and
/// 2. every `ctime` in the entry was more than `max(g, 2 s)` = `STAT_TRUST_WINDOW_NS` older
///    than the wall clock when hashing began. A write after that point gets a strictly newer
///    `ctime`, which also covers coarse-clock lag and modest client/server skew.
///
/// Everything else re-hashes the bytes and memoizes nothing: coarse or unproven granularity
/// (FAT, ext3, HFS+, some network/FUSE filesystems), recent `ctime`s, and non-Unix hosts.
pub(crate) const STAT_TRUST_WINDOW_NS: i128 = 2_000_000_000;

static TS_SUBSECOND_BY_DEV: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<u64, bool>>,
> = std::sync::OnceLock::new();

/// Whether `sig.dev` is proven to store sub-second timestamps (rule 1 above).
pub(crate) fn dev_records_subsecond_timestamps(sig: &OleanFileStatSig) -> bool {
    #[cfg(test)]
    if digest_test_hooks::forced_ts_granularity_ns().is_some_and(|g| g >= 1_000_000_000) {
        return false;
    }
    if !cfg!(unix) {
        return false;
    }
    let cache =
        TS_SUBSECOND_BY_DEV.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()));
    // A stored non-zero nanosecond field is only possible on a sub-second filesystem.
    let sampled = sig.ctime_nsec != 0 || sig.mtime_nsec != 0;
    if !sampled {
        if let Some(&known) = cache
            .lock()
            .ok()
            .and_then(|g| g.get(&sig.dev).copied())
            .as_ref()
        {
            return known;
        }
    }
    let proven = sampled || probe_subsecond_ctime(sig.dev);
    if let Ok(mut g) = cache.lock() {
        if g.len() >= 1024 {
            g.clear();
        }
        g.insert(sig.dev, proven);
    }
    proven
}

/// Probe write: a fresh file on `dev` stored with non-zero `ctime` nanoseconds (three tries,
/// as a write can legitimately land on a whole second).
pub(super) fn probe_subsecond_ctime(dev: u64) -> bool {
    (0..3).any(|_| probe_ctime_fence(dev).is_some_and(|ns| ns.rem_euclid(1_000_000_000) != 0))
}

/// Create and remove a scratch file on `dev` and return its `ctime`: every later write to a
/// file on that filesystem gets a `ctime` >= this fence. The probe only goes to the temp dir,
/// never next to the `.olean`s: that would move `LEAN_PATH` directory mtimes, which
/// `compute_search_path_oleans_digest` hashes for package directories.
pub(super) fn probe_ctime_fence(dev: u64) -> Option<i128> {
    probe_ctime_in(&std::env::temp_dir()).filter(|_| {
        fs::metadata(std::env::temp_dir()).is_ok_and(|m| OleanFileStatSig::from_meta(&m).dev == dev)
    })
}

/// Create and remove a scratch file in `dir` and return its `ctime`.
pub(super) fn probe_ctime_in(dir: &Path) -> Option<i128> {
    if !cfg!(unix) {
        return None;
    }
    let probe = dir.join(format!(
        ".turbo-lean-ts-probe-{}-{}",
        std::process::id(),
        next_tmp_id()
    ));
    let file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&probe)
        .ok()?;
    let meta = file.metadata();
    let _ = fs::remove_file(&probe);
    Some(OleanFileStatSig::from_meta(&meta.ok()?).ctime_ns())
}

/// A memoized file digest: valid only for the opened object `(canonical path, dev, ino)` it was
/// read through, and only while that object's `fstat` tuple is `sig`.
#[derive(Clone)]
pub(super) struct CachedFileDigest {
    pub(super) sig: OleanFileStatSig,
    pub(super) hash: String,
    pub(super) deps: Option<Vec<String>>,
}

pub(super) type FileDigestKey = (PathBuf, u64, u64);

pub(super) static FILE_DIGEST_MEMO: std::sync::OnceLock<
    std::sync::Mutex<std::collections::HashMap<FileDigestKey, CachedFileDigest>>,
> = std::sync::OnceLock::new();

/// One file's content digest, read through a single open handle.
pub(super) struct FileRead {
    /// The canonical path that was opened.
    pub(super) canon: PathBuf,
    /// `fstat` of the opened object before reading.
    pub(super) sig: OleanFileStatSig,
    pub(super) hash: String,
    /// Direct imports parsed from the same bytes (`.olean` only; `None` if unparseable).
    pub(super) deps: Option<Vec<String>>,
    /// `fstat` was identical before and after the read.
    pub(super) stable: bool,
}

/// Digest a file through one open handle: canonicalize, open once, `fstat`, read, `fstat`
/// again. Nothing ever follows the pathname a second time, so a symlink or directory switched
/// mid-read cannot pair one object's stat tuple with another object's bytes. The memo is keyed
/// by the canonical path plus the opened object's `(dev, ino)` and filled only when both
/// `fstat` tuples are identical and the trust rule (`STAT_TRUST_WINDOW_NS`) holds.
///
/// `Ok(None)`: no such file. `Err`: not a regular file, or unreadable.
pub(super) fn read_file_digest(path: &Path) -> Result<Option<FileRead>, ()> {
    read_file_digest_opts(path, true)
}

pub(super) fn read_file_digest_opts(path: &Path, need_olean_deps: bool) -> Result<Option<FileRead>, ()> {
    use std::io::Read;
    let not_found = |e: &std::io::Error| e.kind() == std::io::ErrorKind::NotFound;
    let canon = match fs::canonicalize(path) {
        Ok(c) => c,
        Err(e) if not_found(&e) => return Ok(None),
        Err(_) => return Err(()),
    };
    let mut file = match fs::File::open(&canon) {
        Ok(f) => f,
        Err(e) if not_found(&e) => return Ok(None),
        Err(_) => return Err(()),
    };
    let pre_meta = file.metadata().map_err(drop)?;
    if !pre_meta.is_file() {
        return Err(());
    }
    let pre = OleanFileStatSig::from_meta(&pre_meta);
    let is_olean = canon.extension().is_some_and(|e| e == "olean");
    let parse_deps = need_olean_deps && is_olean;
    let key = (canon.clone(), pre.dev, pre.ino);
    let trusted = dev_records_subsecond_timestamps(&pre);
    let memo = FILE_DIGEST_MEMO.get_or_init(Default::default);
    if trusted {
        if let Some(hit) = memo.lock().ok().and_then(|g| g.get(&key).cloned()) {
            if hit.sig == pre && (!parse_deps || hit.deps.is_some()) {
                return Ok(Some(FileRead {
                    canon,
                    sig: pre,
                    hash: hit.hash,
                    deps: hit.deps,
                    stable: true,
                }));
            }
        }
    }
    let read_started_ns = wall_clock_ns();
    run_digest_test_hook("file_digest_after_stat");
    let mut bytes = Vec::with_capacity(pre.size as usize);
    file.read_to_end(&mut bytes).map_err(drop)?;
    run_digest_test_hook("file_digest_after_read");
    let post = OleanFileStatSig::from_meta(&file.metadata().map_err(drop)?);
    let hash = blake3::hash(&bytes).to_hex().to_string();
    let deps = parse_deps
        .then(|| crate::module_builder::parse_olean_binary_imports(&bytes))
        .flatten()
        .map(|(imps, _)| imps.into_iter().map(|i| i.module).collect::<Vec<String>>());
    let stable = post == pre;
    if stable
        && (!is_olean || deps.is_some())
        && trusted
        && read_started_ns > 0
        && pre.ctime_ns() < read_started_ns - STAT_TRUST_WINDOW_NS
    {
        if let Ok(mut g) = memo.lock() {
            if g.len() >= 65536 {
                g.clear();
            }
            g.insert(
                key,
                CachedFileDigest {
                    sig: pre,
                    hash: hash.clone(),
                    deps: deps.clone(),
                },
            );
        }
    }
    Ok(Some(FileRead {
        canon,
        sig: pre,
        hash,
        deps,
        stable,
    }))
}

/// The companions Lean may load next to `<mod>.olean`, as `(tag, path)`.
pub(super) fn olean_companion_paths(olean_path: &Path) -> [(&'static str, PathBuf); 5] {
    let suffixed = |p: &Path, sfx: &str| PathBuf::from(format!("{}{}", p.display(), sfx));
    let ir = olean_path.with_extension("ir");
    [
        ("srv", suffixed(olean_path, ".server")),
        ("priv", suffixed(olean_path, ".private")),
        ("ilean", olean_path.with_extension("ilean")),
        ("ir_sig", suffixed(&ir, ".sig")),
        ("ir", ir),
    ]
}

/// Canonical digest bytes of one `.olean` and its companions, the stat tuples they were read
/// under, and its parsed direct imports (`None` when unreadable, unparseable or modified while
/// read, so the closure cannot be proven complete).
#[derive(PartialEq, Eq)]
pub(crate) struct OleanEntryDigest {
    pub(super) bytes: Vec<u8>,
    pub(super) stats: [Option<OleanFileStatSig>; 6],
    /// Per file (`.olean`, then `olean_companion_paths` order), the BLAKE3 of its bytes.
    pub(crate) hashes: [Option<String>; 6],
    pub(super) deps: Option<Vec<String>>,
}

pub(super) fn digest_olean_path_entry(olean_path: &Path) -> OleanEntryDigest {
    let mut bytes = Vec::with_capacity(512);
    bytes.extend_from_slice(olean_path.to_string_lossy().as_bytes());
    bytes.push(b':');
    let mut stats: [Option<OleanFileStatSig>; 6] = Default::default();
    let mut hashes: [Option<String>; 6] = Default::default();
    let Ok(Some(main)) = read_file_digest(olean_path) else {
        bytes.extend_from_slice(b"unreadable;");
        return OleanEntryDigest {
            bytes,
            stats,
            hashes,
            deps: None,
        };
    };
    stats[0] = Some(main.sig);
    hashes[0] = Some(main.hash.clone());
    bytes.extend_from_slice(main.hash.as_bytes());
    let mut stable = main.stable;
    for (idx, (tag, comp)) in olean_companion_paths(olean_path).iter().enumerate() {
        bytes.push(b'|');
        bytes.extend_from_slice(tag.as_bytes());
        bytes.push(b':');
        match read_file_digest(comp) {
            Ok(Some(r)) => {
                stats[idx + 1] = Some(r.sig);
                stable &= r.stable;
                bytes.extend_from_slice(r.hash.as_bytes());
                hashes[idx + 1] = Some(r.hash);
            }
            Ok(None) => bytes.push(b'0'),
            Err(()) => {
                stable = false;
                bytes.extend_from_slice(b"err");
            }
        }
    }
    bytes.push(b';');
    OleanEntryDigest {
        bytes,
        stats,
        hashes,
        deps: main.deps.filter(|_| stable),
    }
}

/// Compute a deterministic 256-bit BLAKE3 digest over the full transitive closure of
/// resolved `.olean` files and their companions (`.olean.server`, `.olean.private`, `.ilean`,
/// `.ir`, `.ir.sig`) for `imports_csv` along `effective_lean_path`.
pub fn compute_imported_oleans_digest(imports_csv: &str, effective_lean_path: &str) -> String {
    ClosureSnapshot::take(imports_csv, effective_lean_path, None).digest
}

#[cfg(test)]
pub(super) fn compute_imported_oleans_digest_inner(
    imports_csv: &str,
    effective_lean_path: &str,
) -> (String, bool) {
    let snap = ClosureSnapshot::take(imports_csv, effective_lean_path, None);
    (snap.digest, snap.complete)
}

pub(super) fn is_toolchain_builtin_prefix(mod_name: &str) -> bool {
    mod_name == "Init"
        || mod_name.starts_with("Init.")
        || mod_name == "Std"
        || mod_name.starts_with("Std.")
        || mod_name == "Lean"
        || mod_name.starts_with("Lean.")
        || mod_name == "Lake"
        || mod_name.starts_with("Lake.")
}

pub(crate) fn is_sysroot_lib_lean_dir(dir: &Path) -> bool {
    let check = |p: &Path| {
        p.ends_with("lib/lean")
            && p.parent().and_then(|lib| lib.parent()).is_some_and(|tc| {
                tc.join("bin/lean").is_file() || tc.join("bin/lean.exe").is_file()
            })
    };
    check(dir) || fs::canonicalize(dir).ok().is_some_and(|c| check(&c))
}

pub(crate) fn is_toolchain_dir_match(dir: &Path, toolchain_lib: Option<&Path>) -> bool {
    match toolchain_lib.filter(|p| !p.as_os_str().is_empty()) {
        Some(tc) => {
            dir == tc
                || fs::canonicalize(dir).ok().is_some_and(|c| {
                    let canon_tc = fs::canonicalize(tc).unwrap_or_else(|_| tc.to_path_buf());
                    c == canon_tc || c.starts_with(&canon_tc)
                })
        }
        None => is_sysroot_lib_lean_dir(dir),
    }
}

pub(crate) fn is_resolved_toolchain_builtin(
    search_dirs: &[&Path],
    mod_name: &str,
    toolchain_lib: Option<&Path>,
) -> bool {
    if !is_toolchain_builtin_prefix(mod_name) {
        return false;
    }
    if let Some(tc) = toolchain_lib.filter(|p| !p.as_os_str().is_empty()) {
        let gh = crate::module_builder::lean_githash_for_sysroot_lib_lean(tc);
        return crate::module_builder::is_builtin_toolchain_module(tc, gh.as_deref(), mod_name);
    }
    if !search_dirs.iter().copied().any(is_sysroot_lib_lean_dir) {
        return true;
    }
    search_dirs
        .iter()
        .copied()
        .filter(|d| is_sysroot_lib_lean_dir(d))
        .any(|d| {
            let gh = crate::module_builder::lean_githash_for_sysroot_lib_lean(d);
            crate::module_builder::is_builtin_toolchain_module(d, gh.as_deref(), mod_name)
        })
}

/// Resolve `mod_name` along `search_dirs` the way Lean's `findOLean` (`findWithExt`) does:
/// the first directory holding the module's root package (`<pkg>/` or `<pkg>.olean`) decides,
/// so a closure snapshot with one search root resolves every module exactly as the live
/// search path did. `None` for a toolchain builtin no other directory shadows, or for a
/// missing module.
pub(crate) fn resolve_closure_module(
    search_dirs: &[&Path],
    mod_name: &str,
    toolchain_lib: Option<&Path>,
) -> Option<PathBuf> {
    let resolved = crate::module_builder::resolve_olean_along_search_dirs(search_dirs, mod_name);
    let rel = crate::module_builder::module_name_to_rel_slash(mod_name);
    let pkg = rel.split('/').next().unwrap_or_default();
    let root = search_dirs
        .iter()
        .find(|d| d.join(pkg).is_dir() || d.join(format!("{pkg}.olean")).exists());
    if is_resolved_toolchain_builtin(search_dirs, mod_name, toolchain_lib)
        && root.is_none_or(|d| is_toolchain_dir_match(d, toolchain_lib))
    {
        return None;
    }
    resolved
}

pub(super) fn split_lean_path(lean_path: &str) -> Vec<&Path> {
    lean_path
        .split(':')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(Path::new)
        .collect()
}

/// The imported `.olean` closure of `imports_csv`: its digest, and per module the resolved
/// path with the entry bytes and stat tuples that produced it.
pub(crate) struct ClosureSnapshot {
    pub(super) lean_path: String,
    pub(super) toolchain_lib: Option<PathBuf>,
    pub(super) digest: String,
    /// Every module resolved, parsed, and read identically twice.
    pub(super) complete: bool,
    pub(crate) entries: std::collections::BTreeMap<String, Option<(PathBuf, OleanEntryDigest)>>,
    /// Wall clock before the first read.
    pub(super) taken_at_ns: i128,
    /// Per device, the `ctime` of a probe file created after the first read: any later write
    /// to a file on that device gets a `ctime` >= this fence.
    pub(super) fences: std::collections::HashMap<u64, i128>,
    /// The private, content-addressed copy of the closure the worker imports, once verified.
    pub(crate) materialized: Option<MaterializedClosure>,
    /// Materialization read other bytes than the scan hashed.
    pub(super) materialize_changed: bool,
}

/// A verified, immutable copy of a closure's non-toolchain `.olean`s and companions.
pub(crate) struct MaterializedClosure {
    /// Digest of the snapshot's manifest: per module, every file's relative name and content
    /// hash (or absence). It labels every cache the worker's env feeds.
    pub(super) label: String,
    /// The worker's only non-toolchain search root.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) dir: PathBuf,
    /// Open `O_DIRECTORY | O_CLOEXEC` handle pinning `dir` by `(dev, ino)` so Linux workers
    /// import through `/proc/self/fd/<fd>` without re-traversing mutable ancestor pathnames.
    #[cfg(target_os = "linux")]
    pub(crate) dir_fd: std::os::unix::io::OwnedFd,
    #[cfg(target_os = "linux")]
    pub(super) dir_dev_ino: (u64, u64),
    #[cfg(target_os = "linux")]
    pub(super) toolchain_lib: Option<PathBuf>,
    /// The worker's canonical `LEAN_PATH`: `dir`, then the toolchain library.
    pub(super) search_path: String,
    /// Non-root ancestor directories above `dir` (`(path, dev, ino, ctime_ns, has_subsec, check_ctime)`),
    /// used to detect ancestor rename/symlink swaps across pathname resolution.
    #[cfg(unix)]
    pub(super) ancestors: Vec<SnapshotAncestorSig>,
    #[cfg(not(unix))]
    pub(super) ancestors: Vec<(PathBuf, u64, u64, i128, bool, bool)>,
    /// Wall clock before ancestor verification (`STAT_TRUST_WINDOW_NS` fallback).
    pub(super) taken_at_ns: i128,
    /// Every directory in the snapshot tree (`dir` and all subdirectories) and the `lstat`
    /// tuple it held after being sealed read-only (`0o500`). Any directory rename/swap or
    /// link/unlink inside the tree changes a directory inode or `mtime`/`ctime`.
    pub(super) dirs: Vec<(PathBuf, OleanFileStatSig)>,
    /// Every present snapshot file and the `fstat` tuple it was verified under. Hardlinked
    /// files share the source's inode, so they must still hold this tuple after the import.
    pub(super) files: Vec<(PathBuf, OleanFileStatSig)>,
    /// `ctime` of a probe created in the snapshot root after verification, strictly newer than
    /// every recorded directory and file `ctime` (`None`: unavailable, so nothing is proven).
    pub(super) fence: Option<i128>,
}

#[cfg(unix)]
pub(super) fn fstatat_dir_sig(
    dir_fd: std::os::unix::io::RawFd,
    rel: &Path,
) -> Option<(OleanFileStatSig, u32)> {
    use std::os::unix::ffi::OsStrExt;
    let c_rel = if rel.as_os_str().is_empty() {
        std::ffi::CString::new(".").ok()?
    } else {
        std::ffi::CString::new(rel.as_os_str().as_bytes()).ok()?
    };
    let mut st: libc::stat = unsafe { std::mem::zeroed() };
    let rc = unsafe { libc::fstatat(dir_fd, c_rel.as_ptr(), &mut st, libc::AT_SYMLINK_NOFOLLOW) };
    if rc != 0 {
        return None;
    }
    #[allow(unused_mut)]
    let mut sig = OleanFileStatSig {
        dev: st.st_dev as u64,
        ino: st.st_ino as u64,
        mtime_sec: st.st_mtime as i64,
        mtime_nsec: st.st_mtime_nsec as i64,
        ctime_sec: st.st_ctime as i64,
        ctime_nsec: st.st_ctime_nsec as i64,
        size: st.st_size as u64,
    };
    #[cfg(test)]
    if let Some(g) = digest_test_hooks::forced_ts_granularity_ns() {
        let trunc = |sec: i64, nsec: i64| {
            let ns = ((sec as i128) * 1_000_000_000 + nsec as i128).div_euclid(g) * g;
            (
                ns.div_euclid(1_000_000_000) as i64,
                ns.rem_euclid(1_000_000_000) as i64,
            )
        };
        (sig.mtime_sec, sig.mtime_nsec) = trunc(sig.mtime_sec, sig.mtime_nsec);
        (sig.ctime_sec, sig.ctime_nsec) = trunc(sig.ctime_sec, sig.ctime_nsec);
    }
    Some((sig, st.st_mode as u32))
}

impl MaterializedClosure {
    /// `Bound` iff no snapshot directory, file, or ancestor path was mutated or swapped since
    /// verification: every snapshot directory and file still matches its verified stat tuple and
    /// `0o500` mode (both by pathname and, on Linux, relative to the pinned `dir_fd`), and
    /// every verified `ctime` predates the fence.
    pub(super) fn binding(&self) -> ClosureBinding {
        let mut ordered = self.fence.is_some();
        #[cfg(unix)]
        for (anc, dev, ino, ctime_ns, has_subsec, check_ctime) in &self.ancestors {
            use std::os::unix::fs::MetadataExt;
            let Ok(meta) = fs::symlink_metadata(anc) else {
                return ClosureBinding::Changed;
            };
            if meta.file_type().is_symlink()
                || !meta.is_dir()
                || meta.dev() != *dev
                || meta.ino() != *ino
            {
                return ClosureBinding::Changed;
            }
            // `ancestors[0]` is `<closure_cache_base>/closure-snapshots` (whose `ctime` advances
            // when sibling snapshots publish), and ancestors strictly above `closure_cache_base()`
            // (such as `<cache_root>` / `TURBO_LEAN_HOME` or `/tmp`) legitimately record new store
            // keys (`fastcheck_bins`, `.verifier_replay_hmac_key`) or sibling temp directories.
            // Only `closure_cache_base()` itself (`check_ctime == true`), isolated in
            // `<cache_root>/closure-realm` (`0o700`), enforces `ctime` invariance to catch ABA
            // swaps of `closure-snapshots` within `closure_cache_base()`.
            if *check_ctime {
                let cur_ctime = OleanFileStatSig::from_meta(&meta).ctime_ns();
                if cur_ctime != *ctime_ns {
                    return ClosureBinding::Changed;
                }
                let anc_ordered = match self.fence {
                    Some(f) if meta.dev() == self.dirs.last().map_or(0, |(_, s)| s.dev) => {
                        *ctime_ns < f
                    }
                    _ => {
                        self.taken_at_ns > 0
                            && *ctime_ns < self.taken_at_ns - STAT_TRUST_WINDOW_NS
                            && *has_subsec
                    }
                };
                ordered &= anc_ordered;
            }
        }
        #[cfg(not(unix))]
        let _ = (&self.ancestors, self.taken_at_ns);

        for (path, sig) in &self.dirs {
            let Ok(meta) = fs::symlink_metadata(path) else {
                return ClosureBinding::Changed;
            };
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                if !meta.is_dir() || (meta.permissions().mode() & 0o777) != 0o500 {
                    return ClosureBinding::Changed;
                }
            }
            if OleanFileStatSig::from_meta(&meta) != *sig {
                return ClosureBinding::Changed;
            }
            #[cfg(target_os = "linux")]
            {
                use std::os::unix::io::AsRawFd;
                let Ok(rel) = path.strip_prefix(&self.dir) else {
                    return ClosureBinding::Changed;
                };
                let Some((fd_sig, fd_mode)) = fstatat_dir_sig(self.dir_fd.as_raw_fd(), rel) else {
                    return ClosureBinding::Changed;
                };
                if (fd_mode & libc::S_IFMT) != libc::S_IFDIR
                    || (fd_mode & 0o777) != 0o500
                    || fd_sig != *sig
                {
                    return ClosureBinding::Changed;
                }
            }
            ordered &= self.fence.is_some_and(|f| sig.ctime_ns() < f);
        }
        for (path, sig) in &self.files {
            let now = fs::symlink_metadata(path).map(|m| OleanFileStatSig::from_meta(&m));
            if now.as_ref().ok() != Some(sig) {
                return ClosureBinding::Changed;
            }
            #[cfg(target_os = "linux")]
            {
                use std::os::unix::io::AsRawFd;
                let Ok(rel) = path.strip_prefix(&self.dir) else {
                    return ClosureBinding::Changed;
                };
                let Some((fd_sig, fd_mode)) = fstatat_dir_sig(self.dir_fd.as_raw_fd(), rel) else {
                    return ClosureBinding::Changed;
                };
                if (fd_mode & libc::S_IFMT) != libc::S_IFREG || fd_sig != *sig {
                    return ClosureBinding::Changed;
                }
            }
            ordered &= self.fence.is_some_and(|f| sig.ctime_ns() < f);
        }
        if ordered {
            ClosureBinding::Bound
        } else {
            ClosureBinding::Unproven
        }
    }

    #[cfg(target_os = "linux")]
    pub(super) fn worker_spawn_lean_path(&self, inherited_fd: std::os::unix::io::RawFd) -> String {
        match &self.toolchain_lib {
            Some(t) => format!("/proc/self/fd/{}:{}", inherited_fd, t.display()),
            None => format!("/proc/self/fd/{}", inherited_fd),
        }
    }
}

///Whether work done between `ClosureSnapshot::take` and `rebind` read the snapshot's bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ClosureBinding {
    /// Provably unchanged: the snapshot may label caches.
    Bound,
    /// A change was observed: the work read other bytes than the snapshot's.
    Changed,
    /// No change observed, but none can be excluded either.
    Unproven,
}

pub(crate) fn wall_clock_ns() -> i128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos() as i128)
        .unwrap_or(0)
}

impl ClosureSnapshot {
    /// Single pass: each module's entry is read once, and those same bytes feed both import
    /// discovery and the digest. Every entry is then re-read; if any changed meanwhile the
    /// closure was not stable and `complete` is `false`.
    pub(super) fn take(imports_csv: &str, lean_path: &str, toolchain_lib: Option<&Path>) -> Self {
        let taken_at_ns = wall_clock_ns();
        let canon_tc = toolchain_lib.and_then(|p| fs::canonicalize(p).ok());
        let tc_ref = canon_tc.as_deref().or(toolchain_lib);
        let search_dirs = split_lean_path(lean_path);
        let mut worklist: Vec<String> = imports_csv
            .split(',')
            .filter_map(|m| parse_zygote_import_entry(m).map(|e| e.0))
            .collect();
        let mut entries = std::collections::BTreeMap::new();
        let mut complete = true;
        while let Some(mod_name) = worklist.pop() {
            if entries.contains_key(&mod_name) {
                continue;
            }
            let entry = resolve_closure_module(&search_dirs, &mod_name, tc_ref).map(|olean_path| {
                let e = digest_olean_path_entry(&olean_path);
                match &e.deps {
                    Some(sub) => worklist.extend(sub.iter().cloned()),
                    None => complete = false,
                }
                (olean_path, e)
            });
            complete &=
                entry.is_some() || is_resolved_toolchain_builtin(&search_dirs, &mod_name, tc_ref);
            entries.insert(mod_name, entry);
        }

        // Per device, a fence strictly newer than every recorded `ctime`: `ctime` comes from a
        // coarse clock, so a file written just before the snapshot may share the probe's tick
        // (then a same-tick rewrite would keep its tuple); re-probe briefly until it does not.
        let mut newest: std::collections::HashMap<u64, i128> = std::collections::HashMap::new();
        for s in entries
            .values()
            .flatten()
            .flat_map(|(_, e)| e.stats.iter().flatten())
        {
            let n = newest.entry(s.dev).or_insert(i128::MIN);
            *n = (*n).max(s.ctime_ns());
        }
        let mut fences = std::collections::HashMap::new();
        for (dev, newest_ctime) in newest {
            let mut prev: Option<i128> = None;
            for _ in 0..80 {
                match probe_ctime_fence(dev) {
                    Some(f) if f > newest_ctime => {
                        fences.insert(dev, f);
                        break;
                    }
                    Some(f) => {
                        let wait_ms = if prev == Some(f) { 10 } else { 2 };
                        prev = Some(f);
                        std::thread::sleep(std::time::Duration::from_millis(wait_ms));
                    }
                    None => break,
                }
            }
        }

        run_digest_test_hook("closure_reread");
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"turbo-zygote-olean-digest:v5:");
        hasher.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
        hasher.update(b":");
        hasher.update(lean_path.as_bytes());
        hasher.update(b"|");
        hasher.update(imports_csv.as_bytes());
        hasher.update(b"|");
        for (mod_name, entry) in &entries {
            hasher.update(b"mod:");
            hasher.update(mod_name.as_bytes());
            hasher.update(b":");
            match entry {
                Some((olean_path, e)) => {
                    hasher.update(&e.bytes);
                    complete &= digest_olean_path_entry(olean_path) == *e;
                }
                None if is_resolved_toolchain_builtin(&search_dirs, mod_name, tc_ref) => {
                    hasher.update(b"toolchain-builtin;");
                }
                None => {
                    hasher.update(b"missing;");
                }
            }
        }
        Self {
            lean_path: lean_path.to_string(),
            toolchain_lib: tc_ref.map(Path::to_path_buf),
            digest: hasher.finalize().to_hex().to_string(),
            complete,
            entries,
            taken_at_ns,
            fences,
            materialized: None,
            materialize_changed: false,
        }
    }

    /// Copy the closure into its private snapshot directory (fail closed: on any error the
    /// snapshot stays unmaterialized and nothing is labelled by it).
    pub(super) fn materialize(&mut self, toolchain_lib: Option<&Path>) {
        if !self.complete {
            return;
        }
        run_digest_test_hook("closure_materialize");
        match materialize_closure(&self.entries, toolchain_lib) {
            Ok(m) => self.materialized = Some(m),
            Err(SnapshotError::Changed) => self.materialize_changed = true,
            Err(SnapshotError::Io) => {}
        }
    }

    /// The label of the bytes the worker imports, if they are a verified snapshot.
    pub(super) fn label(&self) -> Option<&str> {
        self.materialized.as_ref().map(|m| m.label.as_str())
    }

    /// The worker's `LEAN_PATH`: the snapshot alone, or (unlabelled) the live search path.
    pub(super) fn worker_lean_path(&self) -> String {
        match &self.materialized {
            Some(m) => m.search_path.clone(),
            None => self.lean_path.clone(),
        }
    }

    /// Whether the work just done imported exactly the labelled bytes. A worker on a
    /// snapshot read only the snapshot and the toolchain: `Bound` iff no snapshot directory or
    /// file was mutated since it was verified. Without a snapshot it read the live search path:
    /// never `Bound`, and `Changed` (retry) if a change was seen.
    pub(super) fn binding(&self) -> ClosureBinding {
        if let Some(m) = &self.materialized {
            return m.binding();
        }
        match self.rebind() {
            ClosureBinding::Changed => ClosureBinding::Changed,
            _ if self.materialize_changed => ClosureBinding::Changed,
            _ => ClosureBinding::Unproven,
        }
    }

    /// Re-read the closure after the work the snapshot labels (one pass).
    ///
    /// `Changed` if any module now resolves elsewhere, reads differently, has another stat
    /// tuple, or has a `ctime` newer than its device's probe fence. `Bound` iff every module resolves to the same path with identical entry bytes and stat
    /// tuples, and each recorded `ctime` predates a write the snapshot can order against:
    /// - the device's probe fence (strictly older), so a write after the probe would have
    ///   changed the tuple: this needs no assumption about timestamp granularity; or
    /// - with no fence (temp dir on another filesystem), the `STAT_TRUST_WINDOW_NS` rule
    ///   against `taken_at_ns` on a device with proven sub-second timestamps.
    ///
    /// The work (an import) ran after the probe, so it read exactly the snapshot's bytes,
    /// even across an A -> B -> A rewrite that restores the content.
    pub(super) fn rebind(&self) -> ClosureBinding {
        let search_dirs = split_lean_path(&self.lean_path);
        for (mod_name, entry) in &self.entries {
            let now = resolve_closure_module(&search_dirs, mod_name, self.toolchain_lib.as_deref())
                .map(|p| {
                    let e = digest_olean_path_entry(&p);
                    (p, e)
                });
            if now != *entry {
                return ClosureBinding::Changed;
            }
        }
        let stats = || {
            self.entries
                .values()
                .flatten()
                .flat_map(|(_, e)| e.stats.iter().flatten())
        };
        // Written after the probe: whatever the work read, it may not be these bytes.
        if stats().any(|s| self.fences.get(&s.dev).is_some_and(|&f| s.ctime_ns() > f)) {
            return ClosureBinding::Changed;
        }
        let window_cutoff = self.taken_at_ns - STAT_TRUST_WINDOW_NS;
        let ordered = stats().all(|s| match self.fences.get(&s.dev) {
            Some(&fence) => s.ctime_ns() < fence,
            None => {
                self.taken_at_ns > 0
                    && s.ctime_ns() < window_cutoff
                    && dev_records_subsecond_timestamps(s)
            }
        });
        if self.complete && ordered {
            ClosureBinding::Bound
        } else {
            ClosureBinding::Unproven
        }
    }
}

#[derive(Debug)]
pub(super) enum SnapshotError {
    /// A source file no longer holds the bytes the scan hashed.
    Changed,
    Io,
}

impl From<std::io::Error> for SnapshotError {
    fn from(_: std::io::Error) -> Self {
        SnapshotError::Io
    }
}

/// Snapshots kept beyond the current one before the least recently used are collected.
pub(super) const CLOSURE_SNAPSHOT_KEEP: usize = 32;
/// Snapshots used within this window are never collected (a pooled worker may still use one).
pub(super) const CLOSURE_SNAPSHOT_MIN_IDLE: std::time::Duration = std::time::Duration::from_secs(600);
pub(super) const CLOSURE_SNAPSHOT_USAGE_DIR: &str = ".last-used";

thread_local! {
    /// Per-test-thread override for `closure_snapshot_root()` so ancestor-rename tests do not
    /// interfere with parallel tests sharing `TURBO_LEAN_HOME/closure-snapshots`.
    #[cfg(test)]
    pub(super) static TEST_CLOSURE_SNAPSHOT_CACHE_BASE: std::cell::RefCell<Option<PathBuf>> =
        const { std::cell::RefCell::new(None) };
}

pub(super) fn closure_cache_base() -> PathBuf {
    #[cfg(test)]
    if let Some(p) = TEST_CLOSURE_SNAPSHOT_CACHE_BASE.with(|c| c.borrow().clone()) {
        return p;
    }
    crate::shm_cache::cache_root().join("closure-realm")
}

pub(super) fn closure_snapshot_root() -> PathBuf {
    closure_cache_base().join("closure-snapshots")
}

/// Refresh the sibling last-used timestamp for snapshot `label` without touching the sealed
/// `0o500` snapshot directory tree itself.
pub(super) fn mark_closure_snapshot_used_in(root: &Path, label: &str) -> Result<(), SnapshotError> {
    if label.is_empty() {
        return Ok(());
    }
    let usage = ensure_private_dir(&root.join(CLOSURE_SNAPSHOT_USAGE_DIR))?;
    fs::write(usage.join(label), b"")?;
    Ok(())
}

pub(super) fn mark_closure_snapshot_used(label: &str) {
    if !label.is_empty() {
        if let Ok(root) = ensure_private_dir(&closure_snapshot_root()) {
            let _ = mark_closure_snapshot_used_in(&root, label);
        }
    }
}

/// Create `dir` (and any missing parent components) with mode `0o700` from birth, require a
/// real directory owned by us, and enforce `0o700` on `dir` and our `cache_root()` hierarchy.
pub(super) fn ensure_private_dir(dir: &Path) -> Result<PathBuf, SnapshotError> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::{DirBuilderExt, MetadataExt, PermissionsExt};
        let uid = unsafe { libc::geteuid() };
        fs::DirBuilder::new()
            .recursive(true)
            .mode(0o700)
            .create(dir)?;
        let cache_base = closure_cache_base();
        let mut cur = Some(dir);
        while let Some(p) = cur {
            if p == dir || p == cache_base || p.starts_with(&cache_base) {
                let m = fs::symlink_metadata(p)?;
                if !m.is_dir() || m.uid() != uid {
                    return Err(SnapshotError::Io);
                }
                if m.mode() & 0o077 != 0 {
                    fs::set_permissions(p, fs::Permissions::from_mode(0o700))?;
                }
            }
            if p == cache_base {
                break;
            }
            cur = p.parent();
        }
        let canon = fs::canonicalize(dir)?;
        let meta = fs::symlink_metadata(&canon)?;
        if !meta.is_dir() || meta.uid() != uid {
            return Err(SnapshotError::Io);
        }
        if meta.mode() & 0o077 != 0 {
            fs::set_permissions(&canon, fs::Permissions::from_mode(0o700))?;
        }
        Ok(canon)
    }
    #[cfg(not(unix))]
    {
        let _ = dir;
        Err(SnapshotError::Io)
    }
}

#[cfg(unix)]
pub(super) type SnapshotAncestorSig = (PathBuf, u64, u64, i128, bool, bool);

/// Record every non-root ancestor directory above canonical `dir`
/// (`(path, dev, ino, ctime_ns, has_subsec, check_ctime)`), rejecting symlinks or non-directory
/// components. `check_ctime` is enabled for private snapshot-realm ancestors at or below
/// `canon_cache_base` above `closure-snapshots` (`depth > 0`), without pinning shared `<cache_root>`
/// or `/tmp` directory `ctime`s.
#[cfg(unix)]
pub(super) fn stat_snapshot_ancestors(
    dir: &Path,
    canon_cache_base: &Path,
) -> Result<Vec<SnapshotAncestorSig>, SnapshotError> {
    use std::os::unix::fs::MetadataExt;
    let mut out = Vec::new();
    let mut cur = dir.parent();
    let mut depth = 0usize;
    while let Some(p) = cur {
        if p == Path::new("/") || p.as_os_str().is_empty() {
            break;
        }
        let meta = fs::symlink_metadata(p)?;
        if meta.file_type().is_symlink() || !meta.is_dir() {
            return Err(SnapshotError::Changed);
        }
        let sig = OleanFileStatSig::from_meta(&meta);
        let subsec = dev_records_subsecond_timestamps(&sig);
        let check_ctime = depth > 0 && p.starts_with(canon_cache_base);
        out.push((
            p.to_path_buf(),
            meta.dev(),
            meta.ino(),
            sig.ctime_ns(),
            subsec,
            check_ctime,
        ));
        depth += 1;
        cur = p.parent();
    }
    Ok(out)
}

#[cfg(not(unix))]
pub(super) fn stat_snapshot_ancestors(
    dir: &Path,
    canon_cache_base: &Path,
) -> Result<Vec<(PathBuf, u64, u64, i128, bool, bool)>, SnapshotError> {
    let _ = (dir, canon_cache_base);
    Err(SnapshotError::Io)
}

#[cfg(target_os = "linux")]
pub(super) fn open_pinned_snapshot_dir(
    dir: &Path,
    expected_root_sig: &OleanFileStatSig,
) -> Result<(std::os::unix::io::OwnedFd, (u64, u64)), SnapshotError> {
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::io::FromRawFd;
    let c_dir =
        std::ffi::CString::new(dir.as_os_str().as_bytes()).map_err(|_| SnapshotError::Io)?;
    let raw = unsafe {
        libc::open(
            c_dir.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC | libc::O_NOFOLLOW,
        )
    };
    if raw < 0 {
        return Err(SnapshotError::Changed);
    }
    let fd = unsafe { std::os::unix::io::OwnedFd::from_raw_fd(raw) };
    let Some((fd_sig, fd_mode)) = fstatat_dir_sig(raw, Path::new("")) else {
        return Err(SnapshotError::Changed);
    };
    if (fd_mode & libc::S_IFMT) != libc::S_IFDIR
        || (fd_mode & 0o777) != 0o500
        || fd_sig != *expected_root_sig
    {
        return Err(SnapshotError::Changed);
    }
    Ok((fd, (fd_sig.dev, fd_sig.ino)))
}

/// Collect every directory in `dir` (post-order: children before parents, ending at `dir`),
/// rejecting symlinks or non-directory entries.
pub(super) fn collect_snapshot_dirs_postorder(
    dir: &Path,
    out: &mut Vec<PathBuf>,
) -> Result<(), SnapshotError> {
    let meta = fs::symlink_metadata(dir)?;
    if !meta.is_dir() {
        return Err(SnapshotError::Changed);
    }
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let emeta = fs::symlink_metadata(&path)?;
        if emeta.file_type().is_symlink() {
            return Err(SnapshotError::Changed);
        }
        if emeta.is_dir() {
            collect_snapshot_dirs_postorder(&path, out)?;
        }
    }
    out.push(dir.to_path_buf());
    Ok(())
}

/// Seal every directory in `dir` to `0o500` (if not already `0o500`) and return their verified
/// `(path, OleanFileStatSig)` tuples. Avoiding redundant `chmod` on already-`0o500` directories
/// keeps `ctime` untouched across repeated snapshot hits.
pub(super) fn seal_and_stat_snapshot_dirs(
    dir: &Path,
) -> Result<Vec<(PathBuf, OleanFileStatSig)>, SnapshotError> {
    let mut dirs = Vec::new();
    collect_snapshot_dirs_postorder(dir, &mut dirs)?;
    let mut out = Vec::with_capacity(dirs.len());
    for d in dirs {
        let mut meta = fs::symlink_metadata(&d)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if (meta.permissions().mode() & 0o777) != 0o500 {
                fs::set_permissions(&d, fs::Permissions::from_mode(0o500))?;
                meta = fs::symlink_metadata(&d)?;
            }
        }
        out.push((d, OleanFileStatSig::from_meta(&meta)));
    }
    Ok(out)
}

/// Restore owner write permissions (`0o700`) on a sealed snapshot tree before removing it.
pub(crate) fn purge_snapshot_dir(dir: &Path) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fn unseal_rec(p: &Path) {
            let Ok(meta) = fs::symlink_metadata(p) else {
                return;
            };
            if meta.is_dir() {
                let _ = fs::set_permissions(p, fs::Permissions::from_mode(0o700));
                if let Ok(rd) = fs::read_dir(p) {
                    for e in rd.flatten() {
                        unseal_rec(&e.path());
                    }
                }
            }
        }
        unseal_rec(dir);
    }
    let _ = fs::remove_dir_all(dir);
}

/// Materialize the non-toolchain part of a closure as `<root>/<label>/` and verify it.
///
/// Every file comes from a private content-addressed blob (`<root>/blobs/<blake3>`): a copy
/// of the resolved source (a reflink where the filesystem supports one), re-hashed through
/// its own handle before it is published read-only under its hash. The snapshot tree is made
/// of hardlinks to blobs, so an edit to one module copies only the changed files. Blobs are
/// never hardlinked to sources: Lean `mmap`s `.olean`s, and an in-place rewrite of a shared
/// inode would reach a cached env's untouched pages. Whatever the source path does after the
/// copy (rewritten, renamed over, symlink retargeted, a shadow appearing earlier on the
/// search path) the worker only sees verified blobs. The tree is published by an atomic
/// `rename` and re-verified on every use (cheaply, through the `fstat`-keyed memo), including
/// the absence of every companion the source lacks; `MaterializedClosure::binding` re-proves
/// after the import that no snapshot file was written. Modules resolved inside
/// `toolchain_lib` stay on the toolchain's search path; their hashes are part of the label.
pub(super) fn materialize_closure(
    entries: &std::collections::BTreeMap<String, Option<(PathBuf, OleanEntryDigest)>>,
    toolchain_lib: Option<&Path>,
) -> Result<MaterializedClosure, SnapshotError> {
    let toolchain_lib = toolchain_lib.and_then(|p| fs::canonicalize(p).ok());
    // (relative name, expected hash or absent, source path)
    let mut files: Vec<(PathBuf, Option<String>, PathBuf)> = Vec::new();
    let mut label = blake3::Hasher::new();
    label.update(b"turbo-zygote-closure-snapshot:v2:");
    label.update(crate::TURBO_LEAN_BUILD_EPOCH.as_bytes());
    label.update(b":");
    for (mod_name, entry) in entries {
        label.update(b"mod:");
        label.update(mod_name.as_bytes());
        let Some((src, e)) = entry else {
            label.update(b"|toolchain-builtin;");
            continue;
        };
        let canon = fs::canonicalize(src).map_err(|_| SnapshotError::Changed)?;
        let on_toolchain = toolchain_lib.as_ref().is_some_and(|t| canon.starts_with(t));
        label.update(if on_toolchain { b"|tc" } else { b"|sn" });
        let rel = PathBuf::from(format!(
            "{}.olean",
            crate::module_builder::module_name_to_rel_slash(mod_name)
        ));
        let rel_names =
            std::iter::once(rel.clone()).chain(olean_companion_paths(&rel).map(|(_, p)| p));
        let src_names =
            std::iter::once(src.clone()).chain(olean_companion_paths(src).map(|(_, p)| p));
        for ((rel_name, src_name), hash) in rel_names.zip(src_names).zip(&e.hashes) {
            label.update(b"|");
            label.update(rel_name.to_string_lossy().as_bytes());
            label.update(b"=");
            label.update(hash.as_deref().unwrap_or("-").as_bytes());
            if !on_toolchain {
                files.push((rel_name, hash.clone(), src_name));
            }
        }
        label.update(b";");
    }
    let label = label.finalize().to_hex().to_string();
    let root = ensure_private_dir(&closure_snapshot_root())?;
    let dir = root.join(&label);
    let search_path = match &toolchain_lib {
        Some(t) => format!("{}:{}", dir.display(), t.display()),
        None => dir.to_string_lossy().to_string(),
    };
    // Re-hash every snapshot file through its own handle; return the verified tuples.
    let verify = |dir: &Path| -> Result<Vec<(PathBuf, OleanFileStatSig)>, SnapshotError> {
        let verify_one = |(rel, hash, _): &(PathBuf, Option<String>, PathBuf)|
         -> Result<Option<(PathBuf, OleanFileStatSig)>, SnapshotError> {
            let path = dir.join(rel);
            match read_file_digest_opts(&path, false).map_err(|_| SnapshotError::Io)? {
                // Opened by its canonical path: a symlink inside the snapshot is not ours.
                Some(r) if Some(&r.hash) == hash.as_ref() && r.stable && r.canon == path => {
                    Ok(Some((path, r.sig)))
                }
                None if hash.is_none() => Ok(None),
                _ => Err(SnapshotError::Changed),
            }
        };
        let par_workers = if files.len() >= 32 && !has_active_digest_test_hook() {
            std::thread::available_parallelism()
                .map(|n| n.get().min(8))
                .unwrap_or(4)
                .min(files.len())
        } else {
            1
        };
        if par_workers <= 1 {
            let mut verified = Vec::with_capacity(files.len());
            for item in &files {
                if let Some(v) = verify_one(item)? {
                    verified.push(v);
                }
            }
            return Ok(verified);
        }
        let next_idx = std::sync::atomic::AtomicUsize::new(0);
        let aborted = std::sync::atomic::AtomicBool::new(false);
        type VerifiedFile = Result<Option<(PathBuf, OleanFileStatSig)>, SnapshotError>;
        let slots: Vec<std::sync::Mutex<Option<VerifiedFile>>> =
            (0..files.len()).map(|_| std::sync::Mutex::new(None)).collect();
        std::thread::scope(|s| {
            for _ in 0..par_workers {
                s.spawn(|| loop {
                    if aborted.load(std::sync::atomic::Ordering::Relaxed) {
                        break;
                    }
                    let idx = next_idx.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if idx >= files.len() {
                        break;
                    }
                    let res = verify_one(&files[idx]);
                    if res.is_err() {
                        aborted.store(true, std::sync::atomic::Ordering::Relaxed);
                    }
                    if let Ok(mut g) = slots[idx].lock() {
                        *g = Some(res);
                    }
                });
            }
        });
        let mut verified = Vec::with_capacity(files.len());
        for slot in slots {
            match slot.into_inner().unwrap_or(None) {
                Some(Ok(Some(v))) => verified.push(v),
                Some(Ok(None)) => {}
                Some(Err(e)) => return Err(e),
                None => return Err(SnapshotError::Changed),
            }
        }
        Ok(verified)
    };
    let finish = |verified_dirs: Vec<(PathBuf, OleanFileStatSig)>,
                  verified_files: Vec<(PathBuf, OleanFileStatSig)>|
     -> Result<MaterializedClosure, SnapshotError> {
        let _ = ensure_private_dir(&root.join(CLOSURE_BLOB_DIR))?;
        let fence_probe_dir = ensure_private_dir(&root.join(CLOSURE_SNAPSHOT_USAGE_DIR))?;
        let canon_cache_base = root.parent().unwrap_or(&root);
        let taken_at_ns = wall_clock_ns();
        let ancestors = stat_snapshot_ancestors(&dir, canon_cache_base)?;
        #[cfg(target_os = "linux")]
        let (dir_fd, dir_dev_ino) = {
            let (_, root_sig) = verified_dirs.last().ok_or(SnapshotError::Changed)?;
            let (fd, dev_ino) = open_pinned_snapshot_dir(&dir, root_sig)?;
            if stat_snapshot_ancestors(&dir, canon_cache_base)? != ancestors {
                return Err(SnapshotError::Changed);
            }
            (fd, dev_ino)
        };
        let mut newest = verified_dirs
            .iter()
            .chain(&verified_files)
            .map(|(_, s)| s.ctime_ns())
            .max()
            .unwrap_or(i128::MIN);
        let root_dev = verified_dirs.last().map_or(0, |(_, s)| s.dev);
        for (_, adev, _, actime, _, check_ctime) in &ancestors {
            if *check_ctime && *adev == root_dev {
                newest = newest.max(*actime);
            }
        }
        let fence = fence_after_in(&fence_probe_dir, newest);
        Ok(MaterializedClosure {
            fence,
            label: label.clone(),
            dir: dir.clone(),
            #[cfg(target_os = "linux")]
            dir_fd,
            #[cfg(target_os = "linux")]
            dir_dev_ino,
            #[cfg(target_os = "linux")]
            toolchain_lib: toolchain_lib.clone(),
            search_path: search_path.clone(),
            ancestors,
            taken_at_ns,
            dirs: verified_dirs,
            files: verified_files,
        })
    };
    if dir.is_dir() {
        if let Ok(verified_files) = verify(&dir) {
            if let Ok(verified_dirs) = seal_and_stat_snapshot_dirs(&dir) {
                mark_closure_snapshot_used_in(&root, &label)?;
                if let Ok(mat) = finish(verified_dirs, verified_files) {
                    return Ok(mat);
                }
            }
        }
        // Not what its name says (a source rewritten in place through a hardlink, tampered
        // permissions, or partially collected): unseal and rebuild it.
        purge_snapshot_dir(&dir);
    }
    let blobs = ensure_private_dir(&root.join(CLOSURE_BLOB_DIR))?;
    let tmp = root.join(format!(".tmp-{}-{}", std::process::id(), next_tmp_id()));
    let built = (|| -> Result<(), SnapshotError> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt;
            fs::DirBuilder::new().mode(0o700).create(&tmp)?;
        }
        #[cfg(not(unix))]
        fs::create_dir(&tmp)?;
        let mut parents = std::collections::BTreeSet::new();
        let mut copy_jobs: Vec<(&Path, &str, &Path, PathBuf)> = Vec::with_capacity(files.len());
        for (rel, hash, src) in &files {
            let Some(hash) = hash.as_deref() else {
                continue;
            };
            let dst = tmp.join(rel);
            if let Some(parent) = dst.parent() {
                if parent != tmp {
                    parents.insert(parent.to_path_buf());
                }
            }
            copy_jobs.push((rel.as_path(), hash, src.as_path(), dst));
        }
        for parent in parents {
            #[cfg(unix)]
            {
                use std::os::unix::fs::DirBuilderExt;
                fs::DirBuilder::new()
                    .recursive(true)
                    .mode(0o700)
                    .create(&parent)?;
            }
            #[cfg(not(unix))]
            fs::create_dir_all(&parent)?;
        }
        let par_workers = if copy_jobs.len() >= 32 && !has_active_digest_test_hook() {
            std::thread::available_parallelism()
                .map(|n| n.get().min(8))
                .unwrap_or(4)
                .min(copy_jobs.len())
        } else {
            1
        };
        if par_workers <= 1 {
            for (_, hash, src, dst) in &copy_jobs {
                copy_verified_snapshot_file(&blobs, hash, src, dst)?;
            }
        } else {
            let next_idx = std::sync::atomic::AtomicUsize::new(0);
            let first_err: std::sync::Mutex<Option<SnapshotError>> = std::sync::Mutex::new(None);
            let aborted = std::sync::atomic::AtomicBool::new(false);
            std::thread::scope(|s| {
                for _ in 0..par_workers {
                    s.spawn(|| loop {
                        if aborted.load(std::sync::atomic::Ordering::Relaxed) {
                            break;
                        }
                        let idx = next_idx.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if idx >= copy_jobs.len() {
                            break;
                        }
                        let (_, hash, src, ref dst) = copy_jobs[idx];
                        if let Err(e) = copy_verified_snapshot_file(&blobs, hash, src, dst) {
                            aborted.store(true, std::sync::atomic::Ordering::Relaxed);
                            if let Ok(mut g) = first_err.lock() {
                                if g.is_none() {
                                    *g = Some(e);
                                }
                            }
                            break;
                        }
                    });
                }
            });
            if let Some(e) = first_err.into_inner().unwrap_or(None) {
                return Err(e);
            }
        }
        Ok(())
    })();
    if let Err(e) = built {
        purge_snapshot_dir(&tmp);
        return Err(e);
    }
    let verified_files = match fs::rename(&tmp, &dir) {
        Ok(()) => verify(&dir),
        Err(_) => {
            // Published concurrently by another request: use that one if it verifies.
            purge_snapshot_dir(&tmp);
            verify(&dir)
        }
    };
    let (verified_dirs, verified_files) =
        match verified_files.and_then(|vf| seal_and_stat_snapshot_dirs(&dir).map(|vd| (vd, vf))) {
            Ok(pair) => pair,
            Err(e) => {
                // A source changed between the scan and the link/copy: this name is not ours.
                purge_snapshot_dir(&dir);
                return Err(e);
            }
        };
    mark_closure_snapshot_used_in(&root, &label)?;
    collect_closure_snapshots(&root, &label);
    finish(verified_dirs, verified_files)
}

pub(super) const CLOSURE_BLOB_DIR: &str = "blobs";

/// Populate `dst` as a snapshot-private read-only inode holding `hash` (reflink/copy from the
/// verified blob cache, never a shared hardlink whose `ctime` would advance on sibling link/unlink).
pub(super) fn copy_verified_snapshot_file(
    blobs: &Path,
    hash: &str,
    src: &Path,
    dst: &Path,
) -> Result<(), SnapshotError> {
    if link_immutable_snapshot_file(src, dst, hash)? {
        return Ok(());
    }
    let blob = ensure_closure_blob(blobs, hash, src)?;
    copy_file_reflink(&blob, dst).map_err(|_| SnapshotError::Changed)?;
    let mut perms = fs::metadata(dst)?.permissions();
    perms.set_readonly(true);
    fs::set_permissions(dst, perms)?;
    Ok(())
}

pub(super) fn link_immutable_snapshot_file(src: &Path, dst: &Path, hash: &str) -> Result<bool, SnapshotError> {
    #[cfg(target_os = "linux")]
    {
        use std::os::unix::{fs::MetadataExt, io::AsRawFd};
        let file = fs::File::open(src)?;
        let before = file.metadata()?;
        let mut flags: libc::c_long = 0;
        let verity = unsafe { libc::ioctl(file.as_raw_fd(), 0x80086601 as libc::c_ulong, &mut flags) } == 0 && flags & 0x00100000 != 0;
        let mut stat = std::mem::MaybeUninit::<libc::statvfs>::uninit();
        let readonly_fs = unsafe {
            libc::fstatvfs(file.as_raw_fd(), stat.as_mut_ptr()) == 0
                && stat.assume_init().f_flag & libc::ST_RDONLY != 0
        };
        if (!verity && !readonly_fs) || !before.permissions().readonly() {
            return Ok(false);
        }
        if fs::hard_link(src, dst).is_err() {
            return Ok(false);
        }
        let verified = read_file_digest_opts(dst, false)
            .ok()
            .flatten()
            .is_some_and(|r| {
                r.stable
                    && r.hash == hash
                    && r.sig.dev == before.dev()
                    && r.sig.ino == before.ino()
                    && fs::metadata(dst).is_ok_and(|after| {
                        after.len() == before.len()
                            && after.mtime() == before.mtime()
                            && after.mtime_nsec() == before.mtime_nsec()
                    })
            });
        if !verified {
            let _ = fs::remove_file(dst);
            return Err(SnapshotError::Changed);
        }
        Ok(true)
    }
    #[cfg(not(target_os = "linux"))]
    { let _ = (src, dst, hash); Ok(false) }
}

/// The verified blob holding `hash`, copied from `src` if not yet present.
pub(super) fn ensure_closure_blob(blobs: &Path, hash: &str, src: &Path) -> Result<PathBuf, SnapshotError> {
    let blob = blobs.join(hash);
    match read_file_digest_opts(&blob, false) {
        Ok(Some(r)) if r.hash == hash && r.stable => return Ok(blob),
        Ok(None) => {}
        // Not what its name says: replace it.
        _ => {
            let _ = fs::remove_file(&blob);
        }
    }
    let tmp = blobs.join(format!(".tmp-{}-{}", std::process::id(), next_tmp_id()));
    let res = (|| -> Result<(), SnapshotError> {
        run_digest_test_hook("closure_blob_copy");
        copy_file_reflink(src, &tmp).map_err(|_| SnapshotError::Changed)?;
        let mut perms = fs::metadata(&tmp)?.permissions();
        perms.set_readonly(true);
        fs::set_permissions(&tmp, perms)?;
        // The source may have changed since it was hashed: only its verified bytes count.
        match read_file_digest_opts(&tmp, false) {
            Ok(Some(r)) if r.hash == hash && r.stable => {}
            _ => return Err(SnapshotError::Changed),
        }
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStrExt;
            let c_tmp = std::ffi::CString::new(tmp.as_os_str().as_bytes())
                .map_err(|_| SnapshotError::Io)?;
            let c_blob = std::ffi::CString::new(blob.as_os_str().as_bytes())
                .map_err(|_| SnapshotError::Io)?;
            if unsafe { libc::link(c_tmp.as_ptr(), c_blob.as_ptr()) } == 0 {
                let _ = fs::remove_file(&tmp);
                return Ok(());
            }
            if std::io::Error::last_os_error().kind() == std::io::ErrorKind::AlreadyExists {
                if let Ok(Some(r)) = read_file_digest_opts(&blob, false) {
                    if r.hash == hash && r.stable {
                        let _ = fs::remove_file(&tmp);
                        return Ok(());
                    }
                }
            }
        }
        fs::rename(&tmp, &blob)?;
        Ok(())
    })();
    if res.is_err() {
        let _ = fs::remove_file(&tmp);
    }
    res.map(|()| blob)
}

/// Copy `src` to a new file `dst`: a reflink (`FICLONE`) when the filesystem supports it,
/// otherwise a byte copy. Either way `dst` is an independent inode.
pub(crate) fn copy_file_reflink(src: &Path, dst: &Path) -> std::io::Result<()> {
    let from = fs::File::open(src)?;
    let mut to = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(dst)?;
    #[cfg(target_os = "linux")]
    {
        use std::os::unix::io::AsRawFd;
        if unsafe { libc::ioctl(to.as_raw_fd(), libc::FICLONE, from.as_raw_fd()) } == 0 {
            return Ok(());
        }
    }
    std::io::copy(&mut &from, &mut to)?;
    Ok(())
}

/// A probe `ctime` in `dir` strictly newer than `newest` (re-probed briefly, as `ctime` comes
/// from a coarse clock); see `ClosureSnapshot::take`.
pub(super) fn fence_after_in(dir: &Path, newest: i128) -> Option<i128> {
    let mut prev: Option<i128> = None;
    for _ in 0..80 {
        match probe_ctime_in(dir) {
            Some(f) if f > newest => return Some(f),
            Some(f) => {
                let wait_ms = if prev == Some(f) { 10 } else { 2 };
                prev = Some(f);
                std::thread::sleep(std::time::Duration::from_millis(wait_ms));
            }
            None => return None,
        }
    }
    None
}

/// Keep the `CLOSURE_SNAPSHOT_KEEP` most recently used snapshots (plus `keep`), never
/// removing one used within `CLOSURE_SNAPSHOT_MIN_IDLE`, and drop abandoned temp dirs.
pub(super) fn collect_closure_snapshots(root: &Path, keep: &str) {
    let Ok(rd) = fs::read_dir(root) else { return };
    let now = std::time::SystemTime::now();
    let idle = |p: &Path| {
        fs::metadata(p)
            .and_then(|m| m.modified())
            .ok()
            .and_then(|t| now.duration_since(t).ok())
            .unwrap_or_default()
    };
    let usage_dir = root.join(CLOSURE_SNAPSHOT_USAGE_DIR);
    let mut snaps = Vec::new();
    for e in rd.flatten() {
        let name = e.file_name().to_string_lossy().to_string();
        let path = e.path();
        if name.starts_with(".tmp-") {
            if idle(&path) > 6 * CLOSURE_SNAPSHOT_MIN_IDLE {
                purge_snapshot_dir(&path);
            }
        } else if name != keep && name != CLOSURE_BLOB_DIR && name != CLOSURE_SNAPSHOT_USAGE_DIR {
            let marker = usage_dir.join(&name);
            let age = if marker.exists() {
                idle(&marker)
            } else {
                idle(&path)
            };
            snaps.push((age, name, path));
        }
    }
    if snaps.len() <= CLOSURE_SNAPSHOT_KEEP {
        return;
    }
    snaps.sort_by_key(|(age, _, _)| std::cmp::Reverse(*age));
    let excess = snaps.len() - CLOSURE_SNAPSHOT_KEEP;
    for (age, name, path) in snaps.into_iter().take(excess) {
        if age > CLOSURE_SNAPSHOT_MIN_IDLE {
            purge_snapshot_dir(&path);
            let _ = fs::remove_file(usage_dir.join(name));
        }
    }
    // Blobs no snapshot links any more (link count 1), once idle.
    #[cfg(unix)]
    for e in fs::read_dir(root.join(CLOSURE_BLOB_DIR))
        .into_iter()
        .flatten()
        .flatten()
    {
        use std::os::unix::fs::MetadataExt;
        let unreferenced = e.metadata().is_ok_and(|m| m.nlink() == 1);
        if unreferenced && idle(&e.path()) > CLOSURE_SNAPSHOT_MIN_IDLE {
            let _ = fs::remove_file(e.path());
        }
    }
}

/// Digest of the declarative Lake file inputs of every package whose build directory is on the
/// worker's search path.
///
/// A zygote worker is reused on the strength of `olean_digest` and the pool key: the toolchain, the
/// search path, and the content of the `.olean` files it imported. An `input_dir` file is none of
/// those -- it is read while a module elaborates and leaves every `.olean` byte untouched -- so a
/// warm worker, its replayed `warm_prefixes`, and the in-process verified-shard memo all survived
/// an input edit and answered from the old bytes. Folding this into `olean_digest` retires all
/// three at once: the memo key contains it, `warm_imports` is compared against it before a worker
/// is reused, and prefix reuse requires that same `warm_imports` match.
///
/// Package roots are recovered from the search path, which is the only project location this
/// function is given. `<pkg_root>/.lake/build/lib/lean` is only the *default* layout -- `buildDir`
/// and `leanLibDir` are both Lake package fields -- so each entry is walked up to the nearest
/// ancestor that carries a Lake config instead of counting a fixed four components. A package whose
/// `buildDir` is custom would otherwise contribute no tag at all, and its `input_dir` edit would
/// leave `olean_digest` unmoved: a warm worker answering from the old bytes.
///
/// Empty -- and free, see `workspace_may_declare_lake_inputs` -- for every workspace that declares
/// no inputs, including every toolchain entry on the path, which carries no Lake config.
pub(super) fn compute_lean_path_lake_inputs_digest(
    effective_lean_path: &str,
    env_vars: &std::collections::HashMap<String, String>,
) -> (String, bool) {
    let mut tags: Vec<String> = Vec::new();
    let mut uncacheable = false;
    let mut record_workspace =
        |dir: &Path| match crate::module_builder::try_project_lake_inputs_tag(dir) {
            Ok(Some(tag)) => {
                if !tags.contains(&tag) {
                    tags.push(tag);
                }
            }
            Ok(None) => {}
            Err(_) => {
                uncacheable = true;
                if let Some(tag) = crate::module_builder::project_lake_inputs_tag(dir) {
                    tags.push(tag);
                }
            }
        };
    for part in effective_lean_path.split(':').filter(|p| !p.is_empty()) {
        // Walk every ancestor without an arbitrary depth cap so deeply nested custom
        // `buildDir` / `leanLibDir` layouts still resolve their enclosing package root.
        for anc in Path::new(part).ancestors() {
            if !crate::lake_build::has_lake_config(anc) {
                continue;
            }
            record_workspace(anc);
            break;
        }
    }
    if let Some(proj) = env_vars
        .get("TURBO_LEAN_PROJECT_DIR")
        .filter(|s| !s.is_empty())
        .map(Path::new)
        .or_else(|| {
            env_vars
                .get("TURBO_LEAN_CALLER_CWD")
                .filter(|s| !s.is_empty())
                .map(Path::new)
                .filter(|p| crate::lake_build::has_lake_config(p))
        })
    {
        let root = crate::lake_build::find_project_root(proj);
        if crate::lake_build::has_lake_config(&root) {
            record_workspace(&root);
        }
    }
    tags.sort();
    (tags.join(","), uncacheable)
}

/// Compute a deterministic BLAKE3 digest over all `.olean` files inside non-toolchain,
/// non-external-package search-path directories of `effective_lean_path`. This ensures that:
/// 1. Different `import` sets on the same `LEAN_PATH` reuse the same warm `ZygoteWorkerProcess`
///    (which holds multiple `Environment`s in its in-memory `envCache`), and
/// 2. Any in-place modification or rebuild of any local `.olean` on `LEAN_PATH`
///    immediately changes `pool_key` and spawns a fresh worker, without scanning 5,400+
///    immutable `.lake/packages/*` `.olean` files on every cold CLI invocation.
pub fn compute_search_path_oleans_digest(effective_lean_path: &str) -> String {
    compute_search_path_oleans_digest_with_toolchain(effective_lean_path, None)
}

pub(super) fn compute_search_path_oleans_digest_with_toolchain(
    effective_lean_path: &str,
    toolchain_lib: Option<&Path>,
) -> String {
    fn collect_oleans_rec(dir: &Path, depth: usize, out: &mut Vec<PathBuf>, max_files: usize) {
        if depth > 12 || out.len() >= max_files {
            return;
        }
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            if out.len() >= max_files {
                break;
            }
            let p = entry.path();
            if p.is_dir() {
                collect_oleans_rec(&p, depth + 1, out, max_files);
            } else if p.extension().and_then(|e| e.to_str()) == Some("olean") {
                out.push(p);
            }
        }
    }

    let mut hasher = blake3::Hasher::new();
    hasher.update(b"turbo-zygote-search-path-oleans:v2:");
    let mut olean_files = Vec::new();
    for seg in effective_lean_path.split(':') {
        let s = seg.trim();
        if s.is_empty() {
            continue;
        }
        let dir = Path::new(s);
        if !dir.is_dir() || is_toolchain_dir_match(dir, toolchain_lib) {
            continue;
        }
        if s.contains("/.lake/packages/") || s.contains("\\.lake\\packages\\") {
            if let Ok(meta) = fs::metadata(dir) {
                let (mtime_sec, mtime_nsec, _) = TurboStore::extract_file_stat_tuple(&meta);
                hasher.update(s.as_bytes());
                hasher.update(&mtime_sec.to_le_bytes());
                hasher.update(&mtime_nsec.to_le_bytes());
            }
            continue;
        }
        collect_oleans_rec(dir, 0, &mut olean_files, 4096);
    }
    olean_files.sort();
    olean_files.dedup();

    for olean_path in olean_files {
        hasher.update(&digest_olean_path_entry(&olean_path).bytes);
    }
    hasher.finalize().to_hex().to_string()
}

pub(super) fn hex_encode_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = Vec::with_capacity(bytes.len() * 2);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize]);
        out.push(HEX[(b & 0x0f) as usize]);
    }
    // Safety: HEX contains only valid ASCII characters
    unsafe { String::from_utf8_unchecked(out) }
}

