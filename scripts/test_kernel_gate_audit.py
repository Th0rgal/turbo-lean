#!/usr/bin/env python3
"""Regression suite for `turbo-zygote --audit-modules` (in-kernel `.olean` gate).

Checks fail-closed rejection of nested inductives through non-core containers,
csimp-shaped constant replacement theorems (including `local csimp`), and
`@[extern]` opaques outside the exact pinned `--ffi-allow` table.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean"
ZYGOTE = LEAN_DIR / ".lake" / "build" / "bin" / "turbo-zygote"

FIXTURES = {
    "FxBox": "structure MyBox (α : Type) where\n  v : α\n",
    "FxNestOk": "inductive T where\n  | leaf : Nat → T\n  | node : List T → Array T → Option T → T × T → T\n",
    "FxNestBad": "import FxBox\ninductive U where\n  | leaf : Nat → U\n  | wrap : MyBox U → U\n",
    "FxCsimpLocal": "def slowF : Nat → Nat | 0 => 0 | n + 1 => slowF n + 1\n"
    "def fastF : Nat → Nat | 0 => 0 | n + 1 => fastF n + 1\n"
    "theorem slowF_eq : @slowF = @fastF := by funext n; induction n <;> simp [slowF, fastF, *]\n"
    "attribute [local csimp] slowF_eq\n"
    "def callerLocal (n : Nat) : Nat := slowF n\n",
    "FxCsimpInlineLocal": "def slowI (n : Nat) : Nat := n * 2\ndef fastI (n : Nat) : Nat := n + n\n"
    "theorem slowI_eq : @slowI = @fastI := by funext n; simp [slowI, fastI, Nat.mul_two]\n"
    "attribute [local csimp] slowI_eq\n"
    "def callerI (n : Nat) : Nat := slowI n\n",
    "FxCsimpGlobal": "def slowGlob (n : Nat) : Nat := n + 0\ndef fastGlob (n : Nat) : Nat := n\n"
    "@[csimp] theorem slowGlob_eq : @slowGlob = @fastGlob := by funext n; rfl\n",
    "FxCsimpPlain": "def slowG : Nat → Nat | 0 => 0 | n + 1 => slowG n + 1\n"
    "def fastG : Nat → Nat | 0 => 0 | n + 1 => fastG n + 1\n"
    "theorem slowG_eq : @slowG = @fastG := by funext n; induction n <;> simp [slowG, fastG, *]\n"
    "def callerPlain (n : Nat) : Nat := slowG n\n",
    "FxBoolCheck": "def chk : Bool := true\ntheorem chk_ok : chk = true := rfl\n",
    "FxExtern": "@[extern \"fx_evil\"] opaque evil : Nat → Nat\n",
    "FxPartialOk": "partial def legitLoop (n : Nat) : Nat := if n == 0 then 1 else legitLoop (n - 1)\n",
    "FxPartialHijack": "import Lean\nopen Lean\ndef safeTarget (n : Nat) : Nat := n + 1\n"
    "run_meta do\n"
    "  let ty := mkForall `n .default (mkConst ``Nat) (mkConst ``Nat)\n"
    "  let val := mkLambda `n .default (mkConst ``Nat) (mkNatLit 999)\n"
    "  addDecl (.defnDecl { name := Compiler.mkUnsafeRecName ``safeTarget, levelParams := [], type := ty, value := val, hints := .opaque, safety := .partial })\n",
    "FxUnsafeDef": "unsafe def badUnsafe (n : Nat) : Nat := badUnsafe n\n",
}


def lean_env() -> dict[str, str]:
    out = subprocess.run(["lake", "env", "printenv"], cwd=LEAN_DIR,
                         check=True, capture_output=True, text=True)
    env = dict(os.environ)
    for line in out.stdout.splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            if k in ("LEAN_PATH", "PATH", "LD_LIBRARY_PATH", "ELAN_HOME"):
                env[k] = v
    return env


@unittest.skipUnless(ZYGOTE.is_file(), "turbo-zygote not built")
class KernelGateAudit(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.tmp = Path(tempfile.mkdtemp(prefix="kgate-"))
        out = cls.tmp / "out"
        out.mkdir()
        base_env = lean_env()
        orig_lp = base_env.get("LEAN_PATH", "")
        env = dict(base_env, LEAN_PATH=str(out))
        for name, src in FIXTURES.items():
            (cls.tmp / f"{name}.lean").write_text(src)
            subprocess.run(["lean", "-o", str(out / f"{name}.olean"), f"{name}.lean"],
                           cwd=cls.tmp, env=env, check=True, capture_output=True, text=True)
        cls.env = dict(base_env, LEAN_PATH=f"{orig_lp}:{out}")

    @classmethod
    def tearDownClass(cls) -> None:
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def audit(self, *args: str) -> dict:
        res = subprocess.run([str(ZYGOTE), "--audit-modules", *args], env=self.env,
                             capture_output=True, text=True, timeout=120)
        return json.loads(res.stdout.strip().splitlines()[-1])

    def assert_rejected(self, mod: str, needle: str, *extra: str) -> None:
        r = self.audit(*extra, mod)
        self.assertFalse(r["ok"], r)
        self.assertEqual(r["audited"], [mod])
        self.assertTrue(any(needle in v for v in r["violations"]), r)

    def test_nested_inductive_through_core_containers_accepted(self) -> None:
        self.assertTrue(self.audit("FxNestOk")["ok"])

    def test_nested_inductive_through_user_container_rejected(self) -> None:
        self.assert_rejected("FxNestBad", "nested inductive type `U`")

    def test_local_csimp_rejected(self) -> None:
        self.assert_rejected("FxCsimpLocal", "local csimp replacement `slowF_eq`")
        self.assert_rejected("FxCsimpInlineLocal", "local csimp replacement `slowI_eq`")

    def test_global_csimp_rejected(self) -> None:
        self.assert_rejected("FxCsimpGlobal", "csimp replacement `slowGlob_eq`")

    def test_csimp_shaped_theorem_accepted_without_attribute(self) -> None:
        self.assertTrue(self.audit("FxCsimpPlain")["ok"])

    def test_bool_check_theorem_not_flagged(self) -> None:
        self.assertTrue(self.audit("FxBoolCheck")["ok"])

    def test_extern_rejected_without_pin(self) -> None:
        self.assert_rejected("FxExtern", "extern/implemented_by bypass on `evil`")

    def test_extern_rejected_with_mismatched_pin(self) -> None:
        self.assert_rejected("FxExtern", "bypass", "--ffi-allow=FxExtern=evil=other_sym")
        self.assert_rejected("FxExtern", "bypass", "--ffi-allow=FxBox=evil=fx_evil")

    def test_malformed_pin_fails_closed(self) -> None:
        r = self.audit("--ffi-allow=junk", "FxBoolCheck")
        self.assertFalse(r["ok"], r)

    def test_extern_accepted_with_exact_pin(self) -> None:
        r = self.audit("--ffi-allow=FxExtern=evil=fx_evil", "FxExtern")
        self.assertTrue(r["ok"], r)
        self.assertEqual(r["audited"], ["FxExtern"])

    def test_missing_module_fails_closed(self) -> None:
        r = self.audit("FxDoesNotExist")
        self.assertFalse(r["ok"], r)

    def test_partial_def_accepted_and_unsafe_rec_hijack_rejected(self) -> None:
        self.assertTrue(self.audit("FxPartialOk")["ok"])
        self.assert_rejected("FxPartialHijack", "forged or unpaired _unsafe_rec/partial declaration `safeTarget._unsafe_rec`")
        self.assert_rejected("FxUnsafeDef", "unsafe declaration `badUnsafe`")


if __name__ == "__main__":
    unittest.main()
