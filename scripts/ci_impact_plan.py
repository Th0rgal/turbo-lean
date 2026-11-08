#!/usr/bin/env python3
"""Conservative CI impact planning over immutable Git trees (stdlib only).

Digests include the entire tracked non-documentation input closure, including
toolchain, lockfiles, workflows and suite drivers. They are receipt identities,
not authorization to trust receipts from an untrusted PR cache.
"""
import argparse
import hashlib
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path


def git(*args):
    return subprocess.check_output(["git", *args])


def is_doc(path):
    return path == "README.md" or (
        path.startswith(("docs/", "roadmap/")) and path.endswith(".md")
    )


def is_sdk(path):
    return path.startswith("sdk/")


def classify(paths, event="pull_request", ref=""):
    force = event in {"workflow_dispatch", "schedule"} or (
        event == "push" and ref in {"main", "refs/heads/main"}
    )
    domains = dict.fromkeys(("ci_scripts", "sdk", "rust_cli", "lean_turbo",
                            "lean_ir_semantics", "llvm_backend",
                            "gpu_tpu_backend", "c_abi_runtime"), False)
    full = force
    for p in paths:
        if is_doc(p):
            continue
        if is_sdk(p):
            domains["sdk"] = True
        elif p.startswith(("scripts/", ".github/")):
            domains["ci_scripts"] = True
            full = True
        elif p.startswith("crates/turbo-lean/src/") and p.endswith("cli.rs"):
            domains["rust_cli"] = True
        elif p.startswith("lean/TurboLean/"):
            domains["lean_turbo"] = True
        elif p.startswith("lean/LeanNative/Backend/"):
            domains["llvm_backend" if "LLVM" in p else "gpu_tpu_backend"] = True
            full = True
        elif p.startswith("verification/lean-mlir-bridge/"):
            domains["llvm_backend"] = True
            full = True
        elif p.startswith("verification/lnsym-bridge/"):
            domains["gpu_tpu_backend"] = True
            full = True
        elif p.startswith("verification/"):
            domains["llvm_backend"] = True
            domains["gpu_tpu_backend"] = True
            full = True
        elif p.startswith("lean/LeanNative/"):
            domains["lean_ir_semantics"] = True
            full = True
        elif p.startswith(("runtime/", "crates/", "plugins/")):
            domains["c_abi_runtime"] = True
            full = True
        else:
            # Unknown inputs, manifests, dependencies and policy fail closed.
            full = True
    docs = bool(paths) and all(map(is_doc, paths))
    preflight_only = bool(paths) and all(is_doc(p) or is_sdk(p) for p in paths)
    return dict(domains, docs_only=docs, force_full=force,
                run_lean_build=force or not preflight_only,
                run_conformance_full=full,
                conformance_seeds=64 if force else 50 if full else 16)


def digest_records(records):
    h = hashlib.sha256(b"turbo-lean-ci-impact-v1\0")
    for record in sorted(records):
        h.update(len(record).to_bytes(8, "big"))
        h.update(record)
    return h.hexdigest()


def tree_digest(head):
    # Git blob identities transitively include contents; tree records also bind
    # file modes, paths and submodule commits. No checkout-dependent reads.
    records = git("ls-tree", "-rz", "--full-tree", head).split(b"\0")
    return digest_records(r for r in records if r and not (
        is_doc(p := r.split(b"\t", 1)[1].decode("utf-8", "surrogateescape"))
        or is_sdk(p)
    ))


def plan_trees(base, head, event, ref):
    # Include both sides of renames so moving code into docs cannot hide it.
    paths = [p.decode("utf-8", "surrogateescape") for p in git(
        "diff", "--name-only", "--no-renames", "-z", base, head).split(b"\0") if p]
    plan = classify(paths, event, ref)
    plan["impact_digest"] = tree_digest(head)
    plan["base_impact_digest"] = tree_digest(base)
    plan["inputs_unchanged"] = plan["impact_digest"] == plan["base_impact_digest"]
    # A path-based docs/sdk-only decision must also agree with immutable-tree
    # content identity. This is an impact gate, not a successful-build receipt.
    preflight_only = plan["docs_only"] or (
        plan["sdk"] and not any(
            plan[k] for k in ("ci_scripts", "rust_cli", "lean_turbo",
                              "lean_ir_semantics", "llvm_backend",
                              "gpu_tpu_backend", "c_abi_runtime")
        ) and not plan["run_conformance_full"]
    )
    plan["run_lean_build"] = (plan["force_full"] or not preflight_only
                              or not plan["inputs_unchanged"])
    return plan, paths


class Tests(unittest.TestCase):
    def test_docs(self):
        p = classify(["README.md"])
        self.assertTrue(p["docs_only"])
        self.assertFalse(p["run_lean_build"])
        self.assertFalse(p["run_conformance_full"])
        for path in ("AGENTS.md", "docs/tool.py", "unknown.file"):
            self.assertFalse(classify([path])["docs_only"])
            self.assertTrue(classify([path])["run_conformance_full"])

    def test_backend(self):
        p = classify(["lean/LeanNative/Backend/PTXAst/PP.lean"])
        for k in ("gpu_tpu_backend", "run_lean_build", "run_conformance_full"):
            self.assertTrue(p[k])
        self.assertEqual(p["conformance_seeds"], 50)
        pv = classify(["verification/lean-mlir-bridge/LeanMLIRBridge/Bisimulation.lean"])
        for k in ("llvm_backend", "run_lean_build", "run_conformance_full"):
            self.assertTrue(pv[k])
        self.assertFalse(pv["gpu_tpu_backend"])
        self.assertEqual(pv["conformance_seeds"], 50)
        pl = classify(["verification/lnsym-bridge/LNSymBridge/Bisimulation.lean"])
        for k in ("gpu_tpu_backend", "run_lean_build", "run_conformance_full"):
            self.assertTrue(pl[k])
        self.assertFalse(pl["llvm_backend"])
        self.assertEqual(pl["conformance_seeds"], 50)

    def test_sdk_and_plugins(self):
        ps = classify(["sdk/accelerator-template/plugin.py"])
        self.assertTrue(ps["sdk"])
        self.assertFalse(ps["docs_only"])
        self.assertFalse(ps["run_lean_build"])
        self.assertFalse(ps["run_conformance_full"])
        self.assertEqual(ps["conformance_seeds"], 16)
        pm = classify(["README.md", "sdk/accelerator-template/validate.py"])
        self.assertTrue(pm["sdk"])
        self.assertFalse(pm["docs_only"])
        self.assertFalse(pm["run_lean_build"])
        self.assertFalse(pm["run_conformance_full"])
        pp = classify(["plugins/verity_yul_plugin.py"])
        self.assertTrue(pp["c_abi_runtime"])
        self.assertTrue(pp["run_lean_build"])
        self.assertTrue(pp["run_conformance_full"])
        self.assertEqual(pp["conformance_seeds"], 50)
        for event, ref in (("push", "refs/heads/main"),
                           ("workflow_dispatch", ""), ("schedule", "")):
            pf = classify(["sdk/accelerator-template/plugin.py"], event, ref)
            for k in ("force_full", "run_lean_build", "run_conformance_full"):
                self.assertTrue(pf[k])

    def test_cli(self):
        p = classify(["crates/turbo-lean/src/cli.rs"])
        self.assertTrue(p["rust_cli"])
        self.assertTrue(p["run_lean_build"])
        self.assertFalse(p["run_conformance_full"])
        self.assertEqual(p["conformance_seeds"], 16)

    def test_forced(self):
        for event, ref in (("push", "refs/heads/main"),
                           ("workflow_dispatch", ""), ("schedule", "")):
            p = classify(["README.md"], event, ref)
            for k in ("force_full", "run_lean_build", "run_conformance_full"):
                self.assertTrue(p[k])
            self.assertEqual(p["conformance_seeds"], 64)

    def test_mixed_and_empty(self):
        self.assertFalse(classify(["README.md", "Cargo.lock"])["docs_only"])
        self.assertTrue(classify([])["run_lean_build"])

    def test_digest(self):
        self.assertEqual(digest_records([b"b", b"a"]), digest_records([b"a", b"b"]))
        self.assertNotEqual(digest_records([b"a", b"bc"]), digest_records([b"ab", b"c"]))
        self.assertNotEqual(digest_records([b"a"]), digest_records([b"b"]))

    def test_repository_history(self):
        # Exercise the CLI against real immutable trees, including deletions,
        # mode changes and documentation renames across the impact boundary.
        script = str(Path(__file__).resolve())
        with tempfile.TemporaryDirectory(prefix="ci-impact-") as directory:
            root = Path(directory)

            def command(*args):
                return subprocess.check_output(args, cwd=root, stderr=subprocess.PIPE).decode().strip()

            def commit():
                command("git", "add", "-A")
                command("git", "-c", "user.name=Planner Test", "-c",
                        "user.email=planner@example.invalid", "-c", "commit.gpgsign=false",
                        "commit", "-qm", "fixture")
                return command("git", "rev-parse", "HEAD")

            def plan(base, head="HEAD", *extra):
                output = root / "outputs"
                result = json.loads(command("python3", script, "--base", base,
                    "--head", head, "--event", "pull_request", "--ref", "",
                    "--github-output", str(output), *extra))
                self.assertIn("impact_digest=" + result["impact_digest"], output.read_text())
                output.unlink()
                return result

            command("git", "init", "-q")
            (root / "README.md").write_text("original docs\n")
            (root / "Cargo.lock").write_text("original lock\n")
            base = commit()
            original = plan(base)
            (root / "README.md").write_text("revised docs\n")
            docs = commit()
            doc_plan = plan(base)
            self.assertTrue(doc_plan["docs_only"])
            self.assertFalse(doc_plan["run_lean_build"])
            self.assertEqual(original["impact_digest"], doc_plan["impact_digest"])
            self.assertTrue(doc_plan["inputs_unchanged"])
            # Working-tree edits must not contaminate a committed-tree receipt.
            (root / "Cargo.lock").write_text("changed lock\n")
            self.assertEqual(plan(base)["impact_digest"], doc_plan["impact_digest"])
            changed = commit()
            self.assertNotEqual(plan(docs)["impact_digest"], doc_plan["impact_digest"])
            self.assertTrue(plan(docs)["run_conformance_full"])
            self.assertFalse(plan(docs)["inputs_unchanged"])
            (root / "Cargo.lock").chmod(0o755)
            mode = commit()
            self.assertNotEqual(plan(changed)["impact_digest"], plan(docs, changed)["impact_digest"])
            (root / "Cargo.lock").unlink()
            commit()
            self.assertEqual(plan(mode)["changed_files"], ["Cargo.lock"])
            self.assertTrue(plan(mode)["run_conformance_full"])
            before_rename = command("git", "rev-parse", "HEAD")
            (root / "README.md").rename(root / "policy.txt")
            commit()
            renamed = plan(before_rename)
            self.assertEqual(renamed["changed_files"], ["README.md", "policy.txt"])
            self.assertTrue(renamed["run_conformance_full"])
            (root / "sdk").mkdir()
            (root / "sdk" / "foo.py").write_text("print(1)\n")
            sdk_base = commit()
            (root / "sdk" / "foo.py").write_text("print(2)\n")
            sdk_edit = commit()
            sdk_plan = plan(sdk_base, sdk_edit)
            self.assertTrue(sdk_plan["sdk"])
            self.assertFalse(sdk_plan["run_lean_build"])
            self.assertTrue(sdk_plan["inputs_unchanged"])
            (root / "crates").mkdir()
            (root / "sdk" / "foo.py").rename(root / "crates" / "foo.rs")
            sdk_renamed_head = commit()
            sdk_renamed = plan(sdk_edit, sdk_renamed_head)
            self.assertEqual(sorted(sdk_renamed["changed_files"]), ["crates/foo.rs", "sdk/foo.py"])
            self.assertTrue(sdk_renamed["c_abi_runtime"])
            self.assertTrue(sdk_renamed["run_lean_build"])
            self.assertTrue(sdk_renamed["run_conformance_full"])
            self.assertFalse(sdk_renamed["inputs_unchanged"])
            for event in ("workflow_dispatch", "schedule"):
                forced = plan(base, docs, "--event", event)
                self.assertTrue(forced["force_full"])
                self.assertTrue(forced["run_lean_build"])
            checked = json.loads(command("python3", script, "--check", "--base", base))
            self.assertEqual(checked["base"], base)
            checked_default = json.loads(command("python3", script, "--check"))
            self.assertEqual(checked_default["head"], command("git", "rev-parse", "HEAD"))


def verify_plan_invariants(plan):
    for key in ("impact_digest", "base_impact_digest"):
        digest = plan.get(key, "")
        if not (isinstance(digest, str) and len(digest) == 64):
            raise AssertionError(f"invalid {key}: {digest!r}")
    preflight_only = plan["docs_only"] or (
        plan.get("sdk", False) and not any(
            plan[k] for k in ("ci_scripts", "rust_cli", "lean_turbo",
                              "lean_ir_semantics", "llvm_backend",
                              "gpu_tpu_backend", "c_abi_runtime")
        ) and not plan["run_conformance_full"]
    )
    expected_build = (plan["force_full"] or not preflight_only
                      or not plan["inputs_unchanged"])
    if plan["run_lean_build"] != expected_build:
        raise AssertionError(f"run_lean_build mismatch: {plan}")
    if plan["force_full"] and not (
        plan["run_lean_build"] and plan["run_conformance_full"]
        and plan["conformance_seeds"] == 64
    ):
        raise AssertionError(f"force_full invariant failed: {plan}")


def resolve_default_base():
    for candidate in ("origin/main", "main", "HEAD"):
        try:
            return subprocess.check_output(
                ["git", "rev-parse", "--verify", "-q", candidate + "^{commit}"],
                stderr=subprocess.DEVNULL,
            ).decode().strip()
        except subprocess.CalledProcessError:
            continue
    raise SystemExit("unable to resolve default base commit for --check")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--base")
    ap.add_argument("--head", default="HEAD")
    ap.add_argument("--event", default=os.getenv("GITHUB_EVENT_NAME", "pull_request"))
    ap.add_argument("--ref", default=os.getenv("GITHUB_REF", ""))
    ap.add_argument("--github-output", default=os.getenv("GITHUB_OUTPUT"))
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(Tests))
        return 0 if result.wasSuccessful() else 1
    if not args.base and not args.check:
        ap.error("--base is required unless --self-test or --check is used")
    base = (git("rev-parse", "--verify", args.base + "^{commit}").decode().strip()
            if args.base else resolve_default_base())
    head = git("rev-parse", "--verify", args.head + "^{commit}").decode().strip()
    plan, paths = plan_trees(base, head, args.event, args.ref)
    if args.check:
        verify_plan_invariants(plan)
    print(json.dumps(dict(plan, base=base, head=head, changed_files=paths), sort_keys=True))
    if args.github_output:
        with open(args.github_output, "a", encoding="utf-8") as out:
            for key, value in plan.items():
                out.write(f"{key}={str(value).lower()}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
