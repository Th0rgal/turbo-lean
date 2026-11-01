use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

pub const MODULES: &[&str] = &["Commands", "Proofs", "Recursion"];
pub fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/check_decl_corpus")
}
pub fn run(cmd: &mut Command) -> Output {
    cmd.env("LEAN_NUM_THREADS", "4")
        .output()
        .expect("required Lean/CLI executable")
}
pub fn diagnostic(o: &Output) -> String {
    format!(
        "{}\n{}",
        String::from_utf8_lossy(&o.stdout),
        String::from_utf8_lossy(&o.stderr)
    )
}
pub fn oracle(dir: &Path, module: &str, src: &str) -> BTreeSet<String> {
    let helper = fs::read_to_string(fixtures().join("Dump.lean")).unwrap();
    let helper = helper.strip_prefix("import Lean\n").unwrap();
    let file = dir.join(format!("{module}Dump.lean"));
    fs::write(
        &file,
        format!("import Lean\n{src}\n{helper}\n#dump_corpus_theorems\n"),
    )
    .unwrap();
    let out = run(Command::new("lean").arg(&file).current_dir(dir));
    assert!(out.status.success(), "{module}: {}", diagnostic(&out));
    let names: BTreeSet<_> = String::from_utf8_lossy(&out.stdout)
        .lines()
        .filter_map(|l| l.split_once("CORPUS_THEOREM ").map(|(_, n)| n.to_owned()))
        .collect();
    assert!(
        !names.is_empty(),
        "empty oracle for {module}: {}",
        diagnostic(&out)
    );
    names
}
pub struct Temp(pub PathBuf);
impl Temp {
    pub fn new(label: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "turbo-corpus-{label}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }
}
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
