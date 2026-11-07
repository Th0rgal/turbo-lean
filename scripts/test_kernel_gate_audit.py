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
ZYGOTE = Path(os.environ.get("TURBO_ZYGOTE_BIN", str(LEAN_DIR / ".lake" / "build" / "bin" / "turbo-zygote")))

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
    "FxMutualWfOk": "mutual\n"
    "def walkA (fuel x : Nat) : Nat :=\n"
    "  match fuel with\n"
    "  | 0 => 0\n"
    "  | f + 1 => walkB f x + walkC f (x + 1)\n"
    "termination_by fuel\n"
    "private def walkB (fuel x : Nat) : Nat :=\n"
    "  match fuel with\n"
    "  | 0 => x\n"
    "  | f + 1 => walkA f (x / 2)\n"
    "termination_by fuel\n"
    "def walkC (fuel x : Nat) : Nat :=\n"
    "  match fuel with\n"
    "  | 0 => 1\n"
    "  | f + 1 => walkB f x\n"
    "termination_by fuel\n"
    "end\n"
    "def ackWf : Nat → Nat → Nat\n"
    "  | 0, y => y + 1\n"
    "  | x + 1, 0 => ackWf x 1\n"
    "  | x + 1, y + 1 => ackWf x (ackWf (x + 1) y)\n"
    "termination_by x y => (x, y)\n"
    "mutual\n"
    "def pfA (n : Nat) : Option Nat := if n == 0 then some 1 else pfB (n - 1)\n"
    "partial_fixpoint\n"
    "def pfB (n : Nat) : Option Nat := if n == 0 then some 2 else pfA (n - 1)\n"
    "partial_fixpoint\n"
    "end\n"
    "inductive AbiTy where\n"
    "  | staticWords : Nat → AbiTy\n"
    "  | tuple : List AbiTy → AbiTy\n"
    "  | dynamicArray : AbiTy → AbiTy\n"
    "mutual\n"
    "def abiStatic : AbiTy → Bool\n"
    "  | .staticWords _ => true\n"
    "  | .tuple xs => abiStaticList xs\n"
    "  | .dynamicArray _ => false\n"
    "def abiStaticList : List AbiTy → Bool\n"
    "  | [] => true\n"
    "  | x :: xs => abiStatic x && abiStaticList xs\n"
    "end\n"
    "mutual\n"
    "def tupleSizesFuel (fuel : Nat) (children : List AbiTy) : Option Nat :=\n"
    "  match fuel, children with\n"
    "  | 0, _ => none\n"
    "  | _, [] => some 0\n"
    "  | f + 1, c :: cs =>\n"
    "    match encodedSizeFuel f c, tupleSizesFuel f cs with\n"
    "    | some a, some b => some (a + b)\n"
    "    | _, _ => none\n"
    "termination_by fuel\n"
    "def arraySizesFuel (fuel i count : Nat) (elem : AbiTy) : Option Nat :=\n"
    "  match fuel with\n"
    "  | 0 => none\n"
    "  | f + 1 =>\n"
    "    if i < count then\n"
    "      match encodedSizeFuel f elem, arraySizesFuel f (i + 1) count elem with\n"
    "      | some a, some b => some (a + b)\n"
    "      | _, _ => none\n"
    "    else some 0\n"
    "termination_by fuel\n"
    "def encodedSizeFuel (fuel : Nat) (t : AbiTy) : Option Nat :=\n"
    "  match fuel with\n"
    "  | 0 => none\n"
    "  | f + 1 =>\n"
    "    match t with\n"
    "    | .staticWords n => some (n * 32)\n"
    "    | .tuple cs => if abiStatic t then tupleSizesFuel f cs else tupleSizesFuel f cs\n"
    "    | .dynamicArray elem => arraySizesFuel f 0 2 elem\n"
    "termination_by fuel\n"
    "end\n",
    "FxPartialHijack": "import Lean\nopen Lean\ndef safeTarget (n : Nat) : Nat := n\n"
    "theorem safeTarget_eq : safeTarget 5 = 5 := rfl\n"
    "run_meta do\n"
    "  let ty := mkForall `n .default (mkConst ``Nat) (mkConst ``Nat)\n"
    "  let twin := Compiler.mkUnsafeRecName ``safeTarget\n"
    "  let val := mkLambda `n .default (mkConst ``Nat) (mkNatLit 999)\n"
    "  addDecl (.mutualDefnDecl [{ name := twin, levelParams := [], type := ty, value := val, hints := .opaque, safety := .partial, all := [twin] }])\n",
    "FxPartialSelfLoopSpoofEqn": "import Lean\nopen Lean\n"
    "def spoofedTarget (n : Nat) : Nat := n\n"
    "theorem spoofedTarget_eq : spoofedTarget 5 = 5 := rfl\n"
    "theorem spoofedTargetEq (n : Nat) : spoofedTarget n = n := rfl\n"
    "run_meta do\n"
    "  let ty := mkForall `n .default (mkConst ``Nat) (mkConst ``Nat)\n"
    "  let twin := Compiler.mkUnsafeRecName ``spoofedTarget\n"
    "  let val := mkLambda `n .default (mkConst ``Nat) (mkApp (mkConst twin []) (mkBVar 0))\n"
    "  addDecl (.mutualDefnDecl [{ name := twin, levelParams := [], type := ty, value := val, hints := .opaque, safety := .partial, all := [twin] }])\n"
    "  let .thmInfo eqn ← getConstInfo ``spoofedTargetEq | throwError \"missing equation\"\n"
    "  addDecl (.thmDecl { eqn with name := `spoofedTarget.eq_def, all := [`spoofedTarget.eq_def] })\n"
    "  modifyEnv fun env => Elab.Structural.eqnInfoExt.insert env ``spoofedTarget {\n"
    "    (default : Elab.PreDefinition) with\n"
    "    declName := ``spoofedTarget, levelParams := [], type := ty, value := mkLambda `n .default (mkConst ``Nat) (mkBVar 0),\n"
    "    declNames := #[``spoofedTarget], recArgPos := 0, fixedParamPerms := default\n"
    "  }\n",
    "FxRealizeA": "module\n@[expose] public def stepFn : Nat → Nat\n  | 0 => 1\n  | n + 1 => stepFn n + 2\n",
    "FxRealizeB": "module\npublic import FxRealizeA\npublic theorem step_pos (n : Nat) : 0 < stepFn n := by\n  fun_cases stepFn n <;> simp_all [stepFn] <;> omega\n",
    "FxRealizeBridge": "module\nimport FxRealizeB\npublic import FxRealizeA\npublic theorem step_bridge : True := trivial\n",
    "FxRealizeConsumer": "module\npublic import FxRealizeBridge\npublic theorem step_ge_one (n : Nat) : 1 ≤ stepFn n := by\n  fun_cases stepFn n <;> simp_all [stepFn] <;> omega\n",
    "FxUnsafeDef": "unsafe def badUnsafe (n : Nat) : Nat := badUnsafe n\n",
    "FxMainA": "def main : IO Unit := pure ()\ntheorem mainA_ok : (1 : Nat) = 1 := rfl\n",
    "FxMainB": "def main : IO UInt32 := pure 0\ntheorem mainB_ok : (2 : Nat) = 2 := rfl\n",
}


def lean_env() -> dict[str, str]:
    tc_override = os.environ.get("TURBO_TEST_TOOLCHAIN_DIR")
    if tc_override:
        tc = Path(tc_override)
        env = dict(os.environ)
        env["PATH"] = f"{tc / 'bin'}:{env.get('PATH', '')}"
        env["LEAN_PATH"] = str(tc / "lib" / "lean")
        env["LEAN_SYSROOT"] = str(tc)
        env["LD_LIBRARY_PATH"] = str(tc / "lib" / "lean")
        return env
    out = subprocess.run(["lake", "env", "printenv"], cwd=LEAN_DIR,
                         check=True, capture_output=True, text=True)
    env = dict(os.environ)
    for line in out.stdout.splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            if k in ("LEAN_PATH", "PATH", "LD_LIBRARY_PATH", "ELAN_HOME"):
                env[k] = v
    return env


class KernelGateAudit(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        if not (ZYGOTE.is_file() and os.access(ZYGOTE, os.X_OK)):
            raise RuntimeError(
                f"Required kernel gate binary missing or not executable: {ZYGOTE} "
                "(build with `(cd lean && lake build turbo-zygote)`)"
            )
        cls.tmp = Path(tempfile.mkdtemp(prefix="kgate-"))
        out = cls.tmp / "out"
        out.mkdir()
        base_env = lean_env()
        orig_lp = base_env.get("LEAN_PATH", "")
        env = dict(base_env, LEAN_PATH=f"{orig_lp}:{out}")
        for name, src in FIXTURES.items():
            (cls.tmp / f"{name}.lean").write_text(src)
            subprocess.run(["lean", "-o", str(out / f"{name}.olean"), f"{name}.lean"],
                           cwd=cls.tmp, env=env, check=True, capture_output=True, text=True)
        cls.env = dict(base_env, LEAN_PATH=f"{orig_lp}:{out}")
        cls._build_tampered_dup_fixtures(out, cls.env)

    @classmethod
    def _build_tampered_dup_fixtures(cls, out: Path, env: dict[str, str]) -> None:
        gen_src = (
            "import Lean\n"
            "open Lean\n"
            "def main (args : List String) : IO Unit := do\n"
            "  initSearchPath (← findSysroot)\n"
            "  let outDir := System.FilePath.mk args[0]!\n"
            "  let imp : Array Import := #[{ module := `FxBoolCheck, importAll := false, isExported := true, isMeta := false }]\n"
            "  let (_, imports) ← importModulesCore imp |>.run\n"
            "  let base ← finalizeImport imports imp {} 0 false false (isModule := true)\n"
            "  let some origThm := base.find? `chk_ok | throw (IO.userError \"missing chk_ok\")\n"
            "  let .thmInfo tv := origThm | throw (IO.userError \"not thm\")\n"
            "  let sorryAx := Name.mkSimple (\"sor\" ++ \"ryAx\")\n"
            "  let sorryVal := mkApp2 (mkConst sorryAx [Level.zero]) tv.type (mkConst ``Bool.false)\n"
            "  let sorryDup : ConstantInfo := .thmInfo { tv with value := sorryVal }\n"
            "  let mSorry : ModuleData := {\n"
            "    isModule := false, imports := imp,\n"
            "    constNames := #[`chk_ok], constants := #[sorryDup],\n"
            "    extraConstNames := #[], entries := #[]\n"
            "  }\n"
            "  saveModuleData (outDir / \"FxDupSorry.olean\") `FxDupSorry mSorry\n"
            "  let badDup : ConstantInfo := .thmInfo { tv with value := mkConst ``Nat.zero }\n"
            "  let mBad : ModuleData := {\n"
            "    isModule := false, imports := imp,\n"
            "    constNames := #[`chk_ok], constants := #[badDup],\n"
            "    extraConstNames := #[], entries := #[]\n"
            "  }\n"
            "  saveModuleData (outDir / \"FxDupIllTyped.olean\") `FxDupIllTyped mBad\n"
            "  let some origDef := base.find? `chk | throw (IO.userError \"missing chk\")\n"
            "  let .defnInfo dv := origDef | throw (IO.userError \"not defn\")\n"
            "  let badDef : ConstantInfo := .defnInfo { dv with value := mkConst ``Bool.false }\n"
            "  let mDef : ModuleData := {\n"
            "    isModule := false, imports := imp,\n"
            "    constNames := #[`chk], constants := #[badDef],\n"
            "    extraConstNames := #[], entries := #[]\n"
            "  }\n"
            "  saveModuleData (outDir / \"FxDupDivergentDef.olean\") `FxDupDivergentDef mDef\n"
            "  let impPartial : Array Import := #[{ module := `FxPartialOk, importAll := false, isExported := true, isMeta := false }]\n"
            "  let tyNatNat := mkForall `n .default (mkConst ``Nat) (mkConst ``Nat)\n"
            "  let idVal := mkLambda `n .default (mkConst ``Nat) (mkBVar 0)\n"
            "  let fakeMutName := Name.mkStr `fakeAux \"_mutual\"\n"
            "  let fakeMutCi : ConstantInfo := .defnInfo { name := fakeMutName, levelParams := [], type := tyNatNat, value := idVal, hints := .opaque, safety := .safe }\n"
            "  let safeLoopCi : ConstantInfo := .defnInfo {\n"
            "    name := `safeLoopTarget, levelParams := [], type := tyNatNat,\n"
            "    value := mkLambda `n .default (mkConst ``Nat) (mkApp (mkConst fakeMutName []) (mkBVar 0)),\n"
            "    hints := .opaque, safety := .safe\n"
            "  }\n"
            "  let twinName := Compiler.mkUnsafeRecName `safeLoopTarget\n"
            "  let twinCi : ConstantInfo := .defnInfo {\n"
            "    name := twinName, levelParams := [], type := tyNatNat,\n"
            "    value := mkLambda `n .default (mkConst ``Nat) (mkApp (mkConst twinName []) (mkBVar 0)),\n"
            "    hints := .opaque, safety := .partial, all := [twinName]\n"
            "  }\n"
            "  let mPeerHijack : ModuleData := {\n"
            "    isModule := false, imports := impPartial,\n"
            "    constNames := #[fakeMutName, `safeLoopTarget, twinName],\n"
            "    constants := #[fakeMutCi, safeLoopCi, twinCi],\n"
            "    extraConstNames := #[], entries := #[]\n"
            "  }\n"
            "  saveModuleData (outDir / \"FxPartialPeerHijack.olean\") `FxPartialPeerHijack mPeerHijack\n"
            "  let fakeIbelowName := Name.mkStr `Nat \"ibelow\"\n"
            "  let fakeIbelowCi : ConstantInfo := .defnInfo { name := fakeIbelowName, levelParams := [], type := tyNatNat, value := idVal, hints := .opaque, safety := .safe }\n"
            "  let ibelowTargetCi : ConstantInfo := .defnInfo {\n"
            "    name := `safeIbelowTarget, levelParams := [], type := tyNatNat,\n"
            "    value := mkLambda `n .default (mkConst ``Nat) (mkApp (mkConst fakeIbelowName []) (mkBVar 0)),\n"
            "    hints := .opaque, safety := .safe\n"
            "  }\n"
            "  let ibelowTwinName := Compiler.mkUnsafeRecName `safeIbelowTarget\n"
            "  let ibelowTwinCi : ConstantInfo := .defnInfo {\n"
            "    name := ibelowTwinName, levelParams := [], type := tyNatNat,\n"
            "    value := mkLambda `n .default (mkConst ``Nat) (mkNatLit 999),\n"
            "    hints := .opaque, safety := .partial, all := [ibelowTwinName]\n"
            "  }\n"
            "  let mIbelowHijack : ModuleData := {\n"
            "    isModule := false, imports := #[{ module := `Init, importAll := false, isExported := true, isMeta := false }],\n"
            "    constNames := #[fakeIbelowName, `safeIbelowTarget, ibelowTwinName],\n"
            "    constants := #[fakeIbelowCi, ibelowTargetCi, ibelowTwinCi],\n"
            "    extraConstNames := #[], entries := #[]\n"
            "  }\n"
            "  saveModuleData (outDir / \"FxPartialIbelowHijack.olean\") `FxPartialIbelowHijack mIbelowHijack\n"
        )
        gen_file = cls.tmp / "GenTamperedDup.lean"
        gen_file.write_text(gen_src)
        subprocess.run(["lean", "--run", str(gen_file), str(out)],
                       cwd=cls.tmp, env=env, check=True, capture_output=True, text=True)

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

    def assert_replay_rejected(self, mod: str, needle: str) -> None:
        res = subprocess.run([str(ZYGOTE), "--kernel-replay-module", mod], env=self.env,
                             capture_output=True, text=True, timeout=60)
        self.assertNotEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertIn(needle, res.stdout + res.stderr)

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

    def shard_audit(self, imports_csv: str, code: str) -> dict:
        req = f"{imports_csv}\t{code.encode().hex()}\tstrict_all\n"
        res = subprocess.run([str(ZYGOTE)], input=req, env=self.env,
                             capture_output=True, text=True, timeout=120)
        return json.loads(res.stdout.strip().splitlines()[-1])

    def test_partial_def_accepted_and_unsafe_rec_hijack_rejected(self) -> None:
        self.assertTrue(self.audit("FxPartialOk")["ok"])
        self.assertTrue(self.audit("FxMutualWfOk")["ok"])
        self.assert_rejected("FxPartialHijack", "forged or unpaired _unsafe_rec/partial declaration `safeTarget._unsafe_rec`")
        self.assert_rejected("FxPartialSelfLoopSpoofEqn", "forged or unpaired _unsafe_rec/partial declaration `spoofedTarget._unsafe_rec`")
        self.assert_rejected("FxPartialPeerHijack", "forged or unpaired _unsafe_rec/partial declaration `safeLoopTarget._unsafe_rec`")
        self.assert_rejected("FxPartialIbelowHijack", "forged or unpaired _unsafe_rec/partial declaration `safeIbelowTarget._unsafe_rec`")
        self.assert_rejected("FxUnsafeDef", "unsafe declaration `badUnsafe`")

    def test_live_shard_recursion_accepted_and_hijacks_rejected(self) -> None:
        pos_src = FIXTURES["FxPartialOk"] + "\n" + (
            "mutual\n"
            "def walkS_A (fuel x : Nat) : Nat :=\n"
            "  match fuel with | 0 => 0 | f + 1 => walkS_B f x + 1\n"
            "termination_by fuel\n"
            "private def walkS_B (fuel x : Nat) : Nat :=\n"
            "  match fuel with | 0 => x | f + 1 => walkS_A f (x / 2)\n"
            "termination_by fuel\n"
            "end\n"
            "mutual\n"
            "def pfS_A (n : Nat) : Option Nat := if n == 0 then some 1 else pfS_B (n - 1)\n"
            "partial_fixpoint\n"
            "def pfS_B (n : Nat) : Option Nat := if n == 0 then some 2 else pfS_A (n - 1)\n"
            "partial_fixpoint\n"
            "end\n"
            "mutual\n"
            "def evenS : Nat → Bool | 0 => true | n + 1 => oddS n\n"
            "def oddS : Nat → Bool | 0 => false | n + 1 => evenS n\n"
            "end\n"
        )
        pos = self.shard_audit("Init", pos_src)
        self.assertTrue(pos["ok"], pos)

        pos_imported_nested = self.shard_audit(
            "FxMutualWfOk",
            "mutual\n"
            "def shardTupleFuel (fuel : Nat) (children : List AbiTy) : Option Nat :=\n"
            "  match fuel, children with\n"
            "  | 0, _ => none\n"
            "  | _, [] => some 0\n"
            "  | f + 1, c :: cs =>\n"
            "    match shardEncFuel f c, shardTupleFuel f cs with\n"
            "    | some a, some b => some (a + b)\n"
            "    | _, _ => none\n"
            "termination_by fuel\n"
            "def shardEncFuel (fuel : Nat) (t : AbiTy) : Option Nat :=\n"
            "  match fuel with\n"
            "  | 0 => none\n"
            "  | f + 1 =>\n"
            "    match t with\n"
            "    | .staticWords n => some (n * 32)\n"
            "    | .tuple cs => shardTupleFuel f cs\n"
            "    | .dynamicArray elem => shardEncFuel f elem\n"
            "termination_by fuel\n"
            "end\n"
            "theorem abi_size_smoke : encodedSizeFuel 3 (.tuple [.staticWords 1]) = some 32 := by\n"
            "  simp [encodedSizeFuel, tupleSizesFuel, abiStatic, abiStaticList]\n",
        )
        self.assertTrue(pos_imported_nested["ok"], pos_imported_nested)

        bad_hijack_src = "\n".join(FIXTURES["FxPartialHijack"].splitlines()[1:]) + "\n"
        bad_hijack = self.shard_audit("Lean", bad_hijack_src)
        self.assertFalse(bad_hijack["ok"], bad_hijack)
        self.assertTrue(
            any("forged or unpaired _unsafe_rec/partial declaration `safeTarget._unsafe_rec`" in e for e in bad_hijack["errors"]),
            bad_hijack,
        )

        bad_helper_src = (
            "open Lean\n"
            "def fakeAux._mutual (n : Nat) : Nat := n\n"
            "def safeTarget (n : Nat) : Nat := fakeAux._mutual n\n"
            "theorem safeTarget_eq : safeTarget 5 = 5 := rfl\n"
            "run_meta do\n"
            "  let ty := mkForall `n .default (mkConst ``Nat) (mkConst ``Nat)\n"
            "  let twin := Compiler.mkUnsafeRecName ``safeTarget\n"
            "  let val := mkLambda `n .default (mkConst ``Nat) (mkApp (mkConst twin []) (mkBVar 0))\n"
            "  addDecl (.mutualDefnDecl [{ name := twin, levelParams := [], type := ty, value := val, hints := .opaque, safety := .partial, all := [twin] }])\n"
        )
        bad_helper = self.shard_audit("Lean", bad_helper_src)
        self.assertFalse(bad_helper["ok"], bad_helper)
        self.assertTrue(
            any("forged or unpaired _unsafe_rec/partial declaration `safeTarget._unsafe_rec`" in e for e in bad_helper["errors"]),
            bad_helper,
        )

    def test_recursion_over_prefix_stub_accepted_and_unexempt_sorry_rejected(self) -> None:
        stub_rec_src = (
            "theorem modulus_pos : 0 < 256 := sorry\n"
            "def modWrap (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt n modulus_pos⟩\n"
            "def powBySquaring (b e : Fin 256) : Fin 256 :=\n"
            "  if h : e.val = 0 then modWrap 1\n"
            "  else have : e.val / 2 < e.val := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)\n"
            "       powBySquaring (modWrap (b.val * b.val)) ⟨e.val / 2, Nat.lt_trans this e.isLt⟩\n"
            "termination_by e.val\n"
            "theorem target_thm : (modWrap 1).val = 1 := rfl\n"
        )
        live_mode = f"allow_stub:{'target_thm'.encode().hex()}:{'modulus_pos'.encode().hex()}"
        req = f"Init\t{stub_rec_src.encode().hex()}\t{live_mode}\n"
        res = subprocess.run([str(ZYGOTE)], input=req, env=self.env,
                             capture_output=True, text=True, timeout=120)
        live_ok = json.loads(res.stdout.strip().splitlines()[-1])
        self.assertTrue(live_ok["ok"], live_ok)

        live_strict = self.shard_audit("Init", stub_rec_src)
        self.assertFalse(live_strict["ok"], live_strict)

        req_allow_sorry = f"Init\t{stub_rec_src.encode().hex()}\tallow_sorry\n"
        res_allow_sorry = subprocess.run([str(ZYGOTE)], input=req_allow_sorry, env=self.env,
                                         capture_output=True, text=True, timeout=120)
        live_allow_sorry = json.loads(res_allow_sorry.stdout.strip().splitlines()[-1])
        self.assertTrue(live_allow_sorry["ok"], live_allow_sorry)
        self.assertIn("modulus_pos", live_allow_sorry.get("sorry_decls", []))

        fx_path = self.tmp / "FxStubRecShard.lean"
        fx_olean = Path(self.env["LEAN_PATH"].split(":")[-1]) / "FxStubRecShard.olean"
        fx_path.write_text(stub_rec_src)
        subprocess.run(["lean", "-o", str(fx_olean), str(fx_path)],
                       cwd=self.tmp, env=self.env, check=True, capture_output=True, text=True)
        shard_ok = self.audit("--shard", "--stub-ok=modulus_pos", "FxStubRecShard")
        self.assertTrue(shard_ok["ok"], shard_ok)
        shard_no_stub = self.audit("--shard", "FxStubRecShard")
        self.assertFalse(shard_no_stub["ok"], shard_no_stub)
        shard_allow_sorry = self.audit("--allow-sorry", "FxStubRecShard")
        self.assertTrue(shard_allow_sorry["ok"], shard_allow_sorry)

    def test_realized_module_reexports_accepted_and_tampered_duplicates_rejected(self) -> None:
        r = self.audit("FxRealizeA", "FxRealizeB", "FxRealizeBridge", "FxRealizeConsumer")
        self.assertTrue(r["ok"], r)
        self.assert_rejected("FxDupSorry", "disallowed axiom `sorryAx`")
        self.assert_rejected("FxDupIllTyped", "duplicate realized theorem `chk_ok` in `FxDupIllTyped` failed kernel check")
        self.assert_rejected("FxDupDivergentDef", "already contains 'chk'")
        self.assert_replay_rejected("FxDupDivergentDef", "`FxDupDivergentDef` redeclares imported constant `chk`")

    def test_colliding_root_main_modules_bisect_in_child_processes(self) -> None:
        r = self.audit("FxMainA", "FxMainB")
        self.assertTrue(r["ok"], r)
        self.assertEqual(r["audited"], ["FxMainA", "FxMainB"])
        bad = self.audit("FxMainA", "FxMainB", "FxUnsafeDef")
        self.assertFalse(bad["ok"], bad)
        self.assertTrue(any("unsafe declaration `badUnsafe`" in v for v in bad["violations"]), bad)

    def test_cross_module_custom_monad_wf_recursion_accepted_under_load_exts_false(self) -> None:
        out_dir = Path(self.env["LEAN_PATH"].split(":")[-1])
        base_src = self.tmp / "FxMonadBase.lean"
        caller_src = self.tmp / "FxMonadCaller.lean"
        base_src.write_text(
            "abbrev AuditM := Except String\n"
            "inductive AuditStmt where\n"
            "  | leaf (n : Nat)\n"
            "  | seq (xs : List AuditStmt)\n"
        )
        caller_src.write_text(
            "import FxMonadBase\n"
            "def evalAuditStmt : AuditStmt → AuditM Nat\n"
            "  | .leaf n => pure n\n"
            "  | .seq xs => do\n"
            "      let mut acc := 0\n"
            "      for x in xs do\n"
            "        acc := acc + (← evalAuditStmt x)\n"
            "      pure acc\n"
            "termination_by s => sizeOf s\n"
            "decreasing_by\n"
            "  simp_wf\n"
            "  have h := List.sizeOf_lt_of_mem ‹x ∈ xs›\n"
            "  omega\n"
        )
        subprocess.run(
            ["lean", "-o", str(out_dir / "FxMonadBase.olean"), str(base_src)],
            cwd=self.tmp, env=self.env, check=True, capture_output=True, text=True,
        )
        subprocess.run(
            ["lean", "-o", str(out_dir / "FxMonadCaller.olean"), str(caller_src)],
            cwd=self.tmp, env=self.env, check=True, capture_output=True, text=True,
        )
        r = self.audit("FxMonadBase", "FxMonadCaller")
        self.assertTrue(r["ok"], r)


if __name__ == "__main__":
    unittest.main()
