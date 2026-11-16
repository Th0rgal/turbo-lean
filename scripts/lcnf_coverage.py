#!/usr/bin/env python3
"""Horizon H1.0 Generated LCNF Coverage Matrix (`scripts/lcnf_coverage.py`).

Work-graph leaf **H1.0** (*RO*, `roadmap/HORIZONS.md` @ `b59eeef03fa9497bf700806136deeed36498dd71`):
- Outcome: Generated `LCNF` coverage matrix on `Batteries` and C1
- Owns: `scripts/lcnf_coverage.py`
- Needs: –
- Accept: CI job emits JSON (`python3 scripts/lcnf_coverage.py --json`)

Methodology & Honesty Rules:
- Every declaration count emitted by `--json` / `--check` is obtained in that same invocation by
  executing the real Lean 4 LCNF pipeline (`Lean.Compiler.LCNF.toImpure` +
  `builtinPassManager.impurePasses` with `maxHeartbeats := 0`) and invoking
  `LeanNative.IR.ingestLCNFImpureDecl` (which delegates to `RealLCNFBridge.lowerRealLCNFDecl`) on
  each compiled declaration. No number is emitted that this invocation did not measure.
- A corpus this invocation cannot measure is emitted as `measurement_source: "not_measured"` with a
  `reason` and no declaration counts; it never falls back to a stored constant.
- The output carries a `measurement_provenance` block (command, UTC date, revisions).
- From a clean checkout, `--check` / `--json` build `LeanNative.IR.Bridge` and its cone with
  `lake build` (~1 min, needs the pinned toolchain and the `lean-sys` checkout Lake fetches).
- No source-pattern heuristic is ever represented as executed lowering.
- As documented in `roadmap/HORIZONS.md` ("What the review found"), `lowerRealLCNFDecl` lowers a call
  to another local user function (`LetValue.fap`), but `RealLCNFSemantics.evalLetValue` returns
  `.error (.unsupportedCall fn.toString)` whenever `(ctx.findLocalCallee? fn).isSome`. Because
  `lowerRealLCNFDecl_sound` is a forward simulation gated on `evalRealLCNFDecl ... = .ok (v, hst')`,
  its conclusion is vacuous for any declaration that calls a local helper (`lowered_vacuous_local_call`,
  classified under `lowered_unproved` until rung **L2** adds a function environment to both semantics).
- External `Batteries` modules outside the in-toolchain `Init.Data.*` / `Std.Data.*` and the
  `verification/c2-lake-packages/*` `.olean` artifacts are explicitly reported as `unknown` rather
  than extrapolated; measuring them is a later leaf.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import datetime
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

ROOT_DIR = Path(__file__).resolve().parent.parent
PINNED_TOOLCHAIN = "leanprover/lean4:v4.35.0"
PINNED_CON_LECHE_REV = "501589f5680d9599dee1bcef30a420bc8924c490"
# Where a prebuilt, pinned con-leche `.olean` tree may be found. The pin is the
# `verification/con-leche-bridge` one; nothing is fetched or built here.
CON_LECHE_OLEANS_ENV = "TURBO_CON_LECHE_OLEANS"
RESULTS_FILE = ROOT_DIR / "scripts" / "lcnf_coverage_results.json"
RESULT_FIELDS = ("total_declarations", "proved", "lowered_unproved", "rejected", "rejected_not_lowered")
REJECTED_NOT_LOWERED_REASON = "mutual_cycle"
CON_LECHE_MODULE_PREFIXES = ("ConLeche.Kernel", "ConLeche.Cached", "ConLeche.Frontend", "ConLeche.Driver")
CON_LECHE_EXCLUDED_MODULES = frozenset({"ConLeche.Kernel.NatOpPins"})
CON_LECHE_EXCLUSION_REASON = (
    "`ConLeche.Kernel.NatOpPins` is excluded because it declares `@[implemented_by]` "
    "pins whose compiled bodies are compiler-generated wrappers rather than the "
    "authored program text; lowering them would measure the wrapper, not the source. "
    "The exclusion is by exact module name and is reported with the module count."
)
# Pinned con-leche revision -> expected module count after CON_LECHE_EXCLUDED_MODULES.
# Obtained at commit 501589f5680d9599dee1bcef30a420bc8924c490 by enumerating all `.lean`
# sources in `git ls-tree -r --name-only 501589f5680d9599dee1bcef30a420bc8924c490` (and
# matching `.olean` outputs of a full `lake build con-leche`) whose module name is
# `ConLeche`, `Main`, or starts with `CON_LECHE_MODULE_PREFIXES`, minus `ConLeche.Kernel.NatOpPins`
# (103 matching modules - 1 excluded = 102).
CON_LECHE_PINNED_MODULE_COUNTS: dict[str, int] = {
    "501589f5680d9599dee1bcef30a420bc8924c490": 102,
}
_LIVE_AUDIT_CACHE: dict[str, dict[str, Any]] = {}
_CON_LECHE_CACHE: dict[str, dict[str, Any]] = {}

TRACKED_BRIDGE_FILES: dict[str, str] = {
    "lean/LeanNative/IR/Bridge.lean": "35bc45aaeaedb10a9e5d5987821f8a6d66592fbe1634ccccdd7175896eb4471d",
    "lean/LeanNative/IR/RealLCNFBridge.lean": "b6da4f47f73d7ff231908ee9d8531f9231280108a78f6337ce8ec570516724ae",
    "lean/LeanNative/IR/RealLCNFSemantics.lean": "3e5729f3aee6d1d993317577549dcb9475ac4b5832f94e54a04fa7d6a0aba0b6",
    "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean": "2b652b961f78656b494c8f45a58293b0fb01f1f44c8d81c409f4201d546a5b16",
    "lean/LeanNative/IR/BridgeHelpers.lean": "292aeccba7da5b22c770dc534a97619c533febd3d812071f5fb690dbed1015ee",
}

LCNF_CONSTRUCTOR_MATRIX_SPEC: tuple[dict[str, str], ...] = (
    # 1. DeclValue (2 constructors)
    {
        "id": "DeclValue.code",
        "category": "DeclValue",
        "construct": "Lean.Compiler.LCNF.DeclValue.code",
        "status": "proved",
        "evidence_file": "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean",
        "evidence_symbol": "lowerRealLCNFDecl_sound",
        "notes": "Lowered by lowerRealLCNFDecl and proved refines evalRealLCNFDecl when evalRealLCNFDecl succeeds.",
    },
    {
        "id": "DeclValue.extern",
        "category": "DeclValue",
        "construct": "Lean.Compiler.LCNF.DeclValue.extern",
        "status": "rejected",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "Unsupported `@[extern]` declaration",
        "notes": "Fails closed on @[extern] declarations without an LCNF code body.",
    },
    # 2. Code (8 entries covering all constructors + recursive join-point split)
    {
        "id": "Code.let",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.let",
        "status": "proved",
        "evidence_file": "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean",
        "evidence_symbol": "lowerImpureStepPure_sound_aux",
        "notes": "Lowered by lowerImpureLetDeclPure and proved sound in RealLCNFBridgeProofs.",
    },
    {
        "id": "Code.jp",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.jp (non-recursive DAG)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean",
        "evidence_symbol": "lowerImpureStepPure_sound_aux",
        "notes": "Non-recursive join-point declarations are recorded in RealBridgeState.jpDecls and proved sound.",
    },
    {
        "id": "Code.jp.recursive",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.jp (recursive loop)",
        "status": "rejected",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "unsupported recursive join point",
        "notes": "Recursive join points (hasJmpToPure = true) fail closed until rung L3 adds loop IR.",
    },
    {
        "id": "Code.jmp",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.jmp",
        "status": "proved",
        "evidence_file": "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean",
        "evidence_symbol": "lowerImpureStepPure_sound_aux",
        "notes": "Join-point jumps bind parameters via bindJpCallArgsPure and inline the continuation.",
    },
    {
        "id": "Code.cases",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.cases (Bool / Nat / scalar / enum / Stage-1D ADT)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean",
        "evidence_symbol": "lowerImpureStepPure_sound_aux",
        "notes": "Proved for Bool, scalar tags, multi-constructor enums, and Stage-1D 1/2-field heap ADTs.",
    },
    {
        "id": "Code.return",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.return",
        "status": "proved",
        "evidence_file": "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean",
        "evidence_symbol": "lowerRealLCNFDecl_sound",
        "notes": "Returns mapped VarId or active constructor allocation.",
    },
    {
        "id": "Code.unreach",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.unreach",
        "status": "proved",
        "evidence_file": "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean",
        "evidence_symbol": "lowerImpureStepPure_sound_aux",
        "notes": "Lowers to LNIRCode.unreachable and vacuously refines evalStep = .error.",
    },
    {
        "id": "Code.fun",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.fun (local function / closure)",
        "status": "rejected",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "Unsupported local function",
        "notes": "Local function declarations and closures fail closed in RealLCNFBridge.",
    },
    # 3. Alt (3 constructors)
    {
        "id": "Alt.alt",
        "category": "Alt",
        "construct": "Lean.Compiler.LCNF.Alt.alt (.pure phase)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "orderAltsPure",
        "notes": "Ordered and lowered via lowerImpureStepPure.",
    },
    {
        "id": "Alt.ctorAlt",
        "category": "Alt",
        "construct": "Lean.Compiler.LCNF.Alt.ctorAlt (.impure phase)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean",
        "evidence_symbol": "lowerImpureStepPure_sound_aux",
        "notes": "Impure constructor alternatives lower to tag comparisons and proved ite chains.",
    },
    {
        "id": "Alt.default",
        "category": "Alt",
        "construct": "Lean.Compiler.LCNF.Alt.default",
        "status": "proved",
        "evidence_file": "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean",
        "evidence_symbol": "lowerImpureStepPure_sound_aux",
        "notes": "Default case alternative lowers as the fallback branch of the ite chain.",
    },
    # 4. LetValue & Code Impure Operations
    {
        "id": "LetValue.lit.num",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.lit (.nat / .uint8 / .uint16 / .uint32 / .uint64 / .usize)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerLitValuePure",
        "notes": "Numeric literals lower to masked constU64 or constBool with proved refinement.",
    },
    {
        "id": "LetValue.lit.str",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.lit (.str)",
        "status": "rejected",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "unsupported string literal",
        "notes": "String literals fail closed until H3 runtime objects.",
    },
    {
        "id": "LetValue.erased",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.erased",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerImpureLetValuePure",
        "notes": "Erased proof/type bindings lower to unit/zero scalar constants when typed as unit/scalar.",
    },
    {
        "id": "LetValue.proj",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.proj (.pure phase)",
        "status": "lowered_unproved",
        "evidence_file": "lean/LeanNative/IR/Bridge.lean",
        "evidence_symbol": "lowerPureLetValue",
        "notes": "Pure-phase projections lower via unproved lowerPureCode (to be removed in rung L1).",
    },
    {
        "id": "LetValue.const",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.const (.pure phase)",
        "status": "lowered_unproved",
        "evidence_file": "lean/LeanNative/IR/Bridge.lean",
        "evidence_symbol": "lowerPureLetValue",
        "notes": "Pure-phase constant applications lower via unproved lowerPureCode (to be removed in rung L1).",
    },
    {
        "id": "LetValue.fvar",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.fvar (zero-arg alias)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerImpureLetValuePure",
        "notes": "Zero-argument fvar aliases copy the mapped variable or active constructor state.",
    },
    {
        "id": "LetValue.fvar.app",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.fvar (non-empty args higher-order call)",
        "status": "rejected",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "unsupported higher-order fvar call",
        "notes": "Higher-order closure applications fail closed.",
    },
    {
        "id": "LetValue.ctor",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.ctor (Bool / Enum / Prod / Stage-1D 1-2 field heap ADT)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerRealCtor",
        "notes": "Proved for Bool, enums, flat scalar tuples, and Stage-1D non-recursive heap constructors.",
    },
    {
        "id": "LetValue.ctor.general",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.ctor (general recursive/multi-field/scalar-payload ADT)",
        "status": "rejected",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "Unsupported payload-carrying constructor",
        "notes": "General recursive ADTs (>2 fields, mixed scalar/object payloads, or exported heap types) fail closed.",
    },
    {
        "id": "LetValue.fap.intrinsic",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.fap (canonical UInt8/16/32/64, USize, Bool, cast, ByteArray/FloatArray slice intrinsics)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerCanonicalIntrinsicPure?",
        "notes": "Proved in RealLCNFBridgeProofs against RealLCNFSemantics.evalLetValue.",
    },
    {
        "id": "LetValue.fap.local_call",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.fap (call to local user declaration in ctx.localCallees)",
        "status": "lowered_unproved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFSemantics.lean",
        "evidence_symbol": "if (ctx.findLocalCallee? fn).isSome then",
        "notes": "Lowered to LNIRExpr.call by lowerImpureFapPure, but evalLetValue returns .error (.unsupportedCall fn.toString), making lowerRealLCNFDecl_sound vacuous until rung L2.",
    },
    {
        "id": "LetValue.fap.gf_simd",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.fap (GF(2^128) / BabyBear / Goldilocks SIMD intrinsic whitelist)",
        "status": "lowered_unproved",
        "evidence_file": "lean/LeanNative/IR/BridgeHelpers.lean",
        "evidence_symbol": "tryLowerGfSimdIntrinsic",
        "notes": "Intercepted in BridgeHelpers before RealLCNFBridge with assurance := .tested; 0 hits across Std/Init+C2, C1, and con-leche.",
    },
    {
        "id": "LetValue.fap.general",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.fap (self-tail recursion, mutual recursion, unmodeled external calls)",
        "status": "rejected",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "Unsupported external or non-scalar call",
        "notes": "Non-inlined recursive calls and unmodeled external functions fail closed.",
    },
    {
        "id": "LetValue.pap",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.pap (partial application closure)",
        "status": "rejected",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "Unsupported partial application",
        "notes": "Partial application closure allocation fails closed.",
    },
    {
        "id": "LetValue.oproj",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.oproj (tuple / Stage-1D object field projection)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerImpureLetValuePure",
        "notes": "Lowers to projTuple or ctorGetObj and is proved sound in RealLCNFBridgeProofs.",
    },
    {
        "id": "LetValue.uproj",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.uproj (USize field projection)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerImpureLetValuePure",
        "notes": "Lowers to projTuple on flat tuples or ctorGetScalar on C1.2 layouts; arbitrary heap uproj fails closed.",
    },
    {
        "id": "LetValue.sproj",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.sproj (unboxed scalar field projection)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerImpureLetValuePure",
        "notes": "Lowers to projTuple on flat scalar tuples or ctorGetScalar on C1.2 layouts; general heap sproj fails closed.",
    },
    {
        "id": "LetValue.box",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.box",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerImpureLetValuePure",
        "notes": "Boxes UInt64/USize/enum tags in flat tuples or Stage-1D heap ADT fields.",
    },
    {
        "id": "LetValue.unbox",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.unbox",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerImpureLetValuePure",
        "notes": "Unboxes scalar/tagged values with proved width masking.",
    },
    {
        "id": "LetValue.isShared",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.isShared (Stage-1D exclusivity check)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "unintercepted isShared",
        "notes": "Lowers to negated isExclusive on Stage-1D heap pointers; non-Stage-1D isShared fails closed.",
    },
    {
        "id": "LetValue.reset_reuse",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.reset / LetValue.reuse",
        "status": "rejected",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "Unsupported heap reset instruction",
        "notes": "Legacy pure/impure reset/reuse outside Stage-1D del/setTag/oset fails closed on heap pointers.",
    },
    {
        "id": "Code.inc",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.inc",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerRefOpPure",
        "notes": "Emits LNIRCode.incRef on heap/slice pointers and elides on unboxed scalars.",
    },
    {
        "id": "Code.dec",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.dec",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerRefOpPure",
        "notes": "Emits LNIRCode.decRef on heap/slice pointers and elides on unboxed scalars.",
    },
    {
        "id": "Code.del",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.del",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lean_native_del_obj",
        "notes": "Emits lean_native_del_obj in the Stage-1D reset/reuse pattern.",
    },
    {
        "id": "Code.setTag",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.setTag (constructor tag mutation)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lean_native_ctor_set_tag",
        "notes": "Emits lean_native_ctor_set_tag during Stage-1D constructor reuse.",
    },
    {
        "id": "Code.oset",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.oset (Stage-1D object slot mutation)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lean_native_ctor_set",
        "notes": "Emits lean_native_ctor_set on Stage-1D heap objects; fails closed on general heap types.",
    },
    {
        "id": "Code.uset",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.uset (C1.2 USize slot mutation)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lean_native_ctor_set_scalar",
        "notes": "Emits lean_native_ctor_set_scalar on statically known C1.2 layouts; fails closed otherwise.",
    },
    {
        "id": "Code.sset",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.sset (C1.2 scalar slot mutation)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "Unsupported scalar field mutation",
        "notes": "Emits lean_native_ctor_set_scalar on statically known C1.2 layouts; fails closed otherwise.",
    },
    # 5. Arg (3 constructors)
    {
        "id": "Arg.fvar",
        "category": "Arg",
        "construct": "Lean.Compiler.LCNF.Arg.fvar",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerRealArg",
        "notes": "Resolves mapped FVarId in RealBridgeState.fvarMap.",
    },
    {
        "id": "Arg.type",
        "category": "Arg",
        "construct": "Lean.Compiler.LCNF.Arg.type",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "collectSliceCallArgsPure",
        "notes": "Erased type arguments are filtered in slice/tuple/local-call lowering; runtime positions fail closed.",
    },
    {
        "id": "Arg.erased",
        "category": "Arg",
        "construct": "Lean.Compiler.LCNF.Arg.erased",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "unsupported erased runtime argument in pure core",
        "notes": "Erased proof/prop arguments are filtered in slice/tuple/local-call lowering; runtime value positions fail closed.",
    },
    # 6. Ground Types & Signatures
    {
        "id": "Type.unsigned_scalars",
        "category": "Type",
        "construct": "UInt8 / UInt16 / UInt32 / UInt64 / USize / Bool / Multi-Ctor Enum / Flat Prod",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerGroundImpureTypeWith",
        "notes": "Proved unboxed scalar, USize, enum tag, and flat tuple lowering.",
    },
    {
        "id": "Type.signed_scalars",
        "category": "Type",
        "construct": "Int / Int8 / Int16 / Int32 / Int64 / ISize",
        "status": "rejected",
        "evidence_file": "lean/LeanNative/IR/BridgeHelpers.lean",
        "evidence_symbol": "declUsesSignedScalarTransitively",
        "notes": "Transitive scan rejects signed integer types fail-closed before lowering.",
    },
)


# Human-readable scope descriptions for the live-measured corpora. These carry no
# measurement numbers: every count in the emitted JSON comes from the audit run of the
# current invocation (see `build_live_corpora`).
CORPUS_SCOPES: dict[str, str] = {
    "std_init_and_c2": (
        "Non-aux compiled LCNF declarations across in-toolchain Std/Init core data structure "
        "modules (`Init.Data.{Array.Basic,Array.BinSearch,Array.QSort,ByteArray.Basic,BitVec.Basic,UInt.Basic}`, "
        "`Std.Data.{HashMap.Basic,DHashMap.Internal.Raw,TreeMap.Basic,ByteSlice}`) and Tier C2 "
        "multi-module Lake packages (`C2BitwiseScan`, `C2FieldButterfly`, `C2ProtocolMachine`, "
        "`C2CryptoSipHash`); subcorpora `std_init_data` and `c2_lake_packages` split the totals."
    ),
    "c1_corpus": (
        "Non-aux compiled LCNF declarations of the 8 blocking Tier C1 3-way run test suites "
        "(`C1_CORPUS_TESTS` in `scripts/test_scalar_frontend.py`): generated seed declaration "
        "batches, preamble helper declarations, Stage-1B declarations, and negative fail-closed "
        "boundary declarations. Compiler-generated auxiliary declarations (e.g. lambda-lifted "
        "`_closed` helpers) are excluded by `isCompilerGeneratedAuxDecl`; they are neither "
        "measured nor expanded, and no auxiliary expansion is performed by this measurement. "
        "Compiled dynamically into a temporary module tree at run time."
    ),
}


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


_LEAN_AUDIT_DRIVER_HEAD = r"""
import Lean
import Lean.Compiler.LCNF
import Lean.Compiler.LCNF.Main
import LeanNative.IR.Bridge

open Lean Lean.Compiler.LCNF LeanNative.IR

partial def codeHasLocalCall (localSet : Std.HashSet Name) (c : Code .impure) : Bool :=
  match c with
  | .let d k =>
    let hit := match d.value with
      | .fap fn _ _ => localSet.contains fn
      | _ => false
    hit || codeHasLocalCall localSet k
  | .jp j k => codeHasLocalCall localSet j.value || codeHasLocalCall localSet k
  | .cases cs => cs.alts.any (fun a => codeHasLocalCall localSet a.getCode)
  | _ => false

partial def declInMutualCycle (declMap : Std.HashMap Name (List Name)) (target : Name) : Bool :=
  let rec reaches (visited : List Name) (frontier : List Name) : Bool :=
    match frontier with
    | [] => false
    | cur :: rest =>
      if cur == target then true
      else if visited.contains cur then reaches visited rest
      else reaches (cur :: visited) ((declMap.getD cur []) ++ rest)
  reaches [] (declMap.getD target [])

def runCoreOnEnv (env : Environment) (x : CoreM α) : IO (Except String α) := do
  let ctx : Core.Context := { fileName := "<audit>", fileMap := default, maxHeartbeats := 0 }
  let st : Core.State := { env := env }
  let res ← (x.run' ctx st).toIO'
  match res with
  | .ok v => return .ok v
  | .error e => return .error (← e.toMessageData.toString)

def toImpureDecls (env : Environment) (decls : Array (Decl .pure)) : IO (Array (Decl .impure)) := do
  let res ← runCoreOnEnv env (CompilerM.run (phase := .mono) do
    let decls ← decls.mapM (fun d => d.internalize)
    let mut impDecls : Array (Decl .impure) ← toImpure.run decls
    for p in builtinPassManager.impurePasses do
      if h : p.phase.toPurity = .impure ∧ p.phaseOut.toPurity = .impure then
        let declsCast : Array (Decl p.phase.toPurity) := h.1.symm ▸ impDecls
        let next ← (withPhase .impure (p.run declsCast) : CompilerM _)
        impDecls := h.2 ▸ next
    return impDecls)
  match res with
  | .ok d => return d
  | .error e => throw (IO.userError s!"module toImpure conversion failed: {e}")

unsafe def auditMods (env : Environment) (mods : Array Name) : IO (Nat × Nat × Nat × Nat × Nat) := do
  -- Fail closed: a module that cannot be converted to impure IR must fail the
  -- audit loudly, never contribute a silent zero, and a module missing from
  -- the imported environment must be named. The declaration set of this
  -- auditMods group (the std, C2, and C1 module groups are audited by separate
  -- auditMods calls, not one combined group) drives the local-callee
  -- classification, the call graph, and the bridge context, so a call to a
  -- user function declared in the same group is classified exactly like a
  -- same-module call (a vacuous local call), matching the eval
  -- `unsupportedCall` vacuity of `lowerRealLCNFDecl_sound` instead of being
  -- rejected or counted proved.
  let mut corpusDecls : Array (Name × Decl .impure) := #[]
  for modName in mods do
    let some modIdx := env.getModuleIdx? modName
      | throw (IO.userError s!"audit module `{modName}` not found in the imported environment")
    let mdecls := monoExt.getModuleEntries env modIdx
    let impDecls ← toImpureDecls env mdecls
    let impNonAux := impDecls.filter (fun d => !isCompilerGeneratedAuxDecl env d.name)
    for d in impNonAux do
      corpusDecls := corpusDecls.push (modName, d)
  let corpusNames := corpusDecls.map (·.2.name)
  let mut localSet : Std.HashSet Name := {}
  for n in corpusNames do localSet := localSet.insert n
  let mut callGraph : Std.HashMap Name (List Name) := {}
  for (_, d) in corpusDecls do
    if let .code c := d.value then
      callGraph := callGraph.insert d.name ((collectCodeLocalCallees corpusNames c).filter (· != d.name))
  let mut tot := 0; let mut prv := 0; let mut unp := 0; let mut rej := 0; let mut cyc := 0
  for (_, d) in corpusDecls do
    tot := tot + 1
    if declInMutualCycle callGraph d.name then
      rej := rej + 1
      cyc := cyc + 1
    else
      let r ← runCoreOnEnv env (ingestLCNFImpureDecl d corpusNames .x86_64 true)
      match r with
      | .ok _ =>
        let hasCall := match d.value with | .code c => codeHasLocalCall localSet c | .extern _ => false
        if hasCall then unp := unp + 1 else prv := prv + 1
      | .error _ =>
        rej := rej + 1
  return (tot, prv, unp, rej, cyc)
"""

_LEAN_AUDIT_DRIVER_SRC = _LEAN_AUDIT_DRIVER_HEAD + r"""
unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot) (args.map System.FilePath.mk)
  let stdMods : Array Name := #[
    `Init.Data.Array.Basic, `Init.Data.Array.BinSearch, `Init.Data.Array.QSort,
    `Init.Data.ByteArray.Basic, `Init.Data.BitVec.Basic, `Init.Data.UInt.Basic,
    `Std.Data.HashMap.Basic, `Std.Data.DHashMap.Internal.Raw, `Std.Data.TreeMap.Basic, `Std.Data.ByteSlice
  ]
  let c2Mods : Array Name := #[
    `C2BitwiseScan.Swar, `C2BitwiseScan.Scan, `C2BitwiseScan,
    `C2FieldButterfly.Field, `C2FieldButterfly.Butterfly, `C2FieldButterfly,
    `C2ProtocolMachine.Types, `C2ProtocolMachine.Transition, `C2ProtocolMachine,
    `C2CryptoSipHash.SipRound, `C2CryptoSipHash.Mac, `C2CryptoSipHash
  ]
  let c1Mods : Array Name := #[
    `batch_0, `batch_1, `batch_2, `batch_3, `batch_4, `batch_5, `batch_6,
    `C1Batch_stage1b,
    `C1Neg_nat_param, `C1Neg_direct_recursion, `C1Neg_mutual_recursion,
    `C1Neg_closure_param, `C1Neg_heap_adt, `C1Neg_string_lit,
    `C1Neg_unmodeled_extern_log2, `C1Neg_user_extern_decl,
    `C1Neg_signed_int8_param, `C1Neg_signed_int64_internal,
    `C1Neg_signed_int64_transitive, `C1Neg_single_ctor_enum
  ]
  let env ← importModules ((stdMods ++ c2Mods ++ c1Mods).map (fun m => { module := m })) {} (loadExts := true)
  let (st, sp, su, sr, sc) ← auditMods env stdMods
  let (c2t, c2p, c2u, c2r, c2c) ← auditMods env c2Mods
  let (c1t, c1p, c1u, c1r, c1c) ← auditMods env c1Mods
  IO.println s!"AUDIT_RESULT:{st},{sp},{su},{sr},{sc};{c2t},{c2p},{c2u},{c2r},{c2c};{c1t},{c1p},{c1u},{c1r},{c1c}"
"""


def _lean_audit_driver_for_modules(modules: list[str]) -> str:
    """The same audit driver, restricted to an explicitly named module set."""
    names = ",\n    ".join(f"`{m}" for m in modules)
    return _LEAN_AUDIT_DRIVER_HEAD + f"""
unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot) (args.map System.FilePath.mk)
  let mods : Array Name := #[
    {names}
  ]
  let env ← importModules (mods.map (fun m => {{ module := m }})) {{}} (loadExts := true)
  let (t, p, u, r, c) ← auditMods env mods
  IO.println s!"AUDIT_RESULT:{{t}},{{p}},{{u}},{{r}},{{c}}"
"""


def _lean_env() -> dict[str, str]:
    env = dict(os.environ)
    extra_bins = [
        str(Path.home() / ".elan" / "bin"),
        "/var/lib/sandboxed-node/.elan/bin",
        "/var/lib/sandboxed-node/.cargo/bin",
    ]
    env["PATH"] = ":".join(extra_bins + [env.get("PATH", "")])
    return env


def _run_audit_driver(root_dir: Path, driver_src: str, lib_dirs: list[str]) -> tuple[int, int, int, int, int]:
    """Run one audit driver against `lib_dirs`; return (total, proved, unproved, rejected, rejected_not_lowered)."""
    lean_dir = root_dir / "lean"
    env = _lean_env()
    with tempfile.TemporaryDirectory(prefix="lcnf-audit-driver-") as tmp:
        driver_path = Path(tmp) / "AuditDriver.lean"
        driver_path.write_text(driver_src, encoding="utf-8")
        proc = subprocess.run(
            ["lake", "env", "lean", "--run", str(driver_path), *lib_dirs],
            cwd=str(lean_dir),
            env=env,
            capture_output=True,
            text=True,
        )
    if proc.returncode != 0:
        raise RuntimeError(f"Lean audit driver failed:\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}")
    raw_lines = [ln.strip() for ln in proc.stdout.splitlines() if ln.strip().startswith("AUDIT_RESULT:")]
    if not raw_lines:
        raise RuntimeError(f"Lean audit driver emitted no AUDIT_RESULT:\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}")
    return tuple(int(x) for x in raw_lines[-1].split(":", 1)[1].split(","))  # type: ignore[return-value]


def measure_fixture_corpus(root_dir: Path, lean_body: str, mod_name: str = "FixtureCorpus") -> dict[str, Any]:
    """Compile a small Lean fixture module and measure it live with the real lowerer."""
    lean_dir = root_dir / "lean"
    _ensure_lean_build(root_dir)
    env = _lean_env()
    with tempfile.TemporaryDirectory(prefix="lcnf-fixture-") as tmp:
        root = Path(tmp)
        lf = root / f"{mod_name}.lean"
        lf.write_text(f"namespace {mod_name}\n{lean_body}\nend {mod_name}\n", encoding="utf-8")
        subprocess.run(
            ["lean", f"--root={root}", "-o", str(root / f"{mod_name}.olean"), str(lf)],
            cwd=str(lean_dir),
            env=env,
            check=True,
            capture_output=True,
            text=True,
        )
        tot, prv, unp, rej, cyc = _run_audit_driver(
            root_dir, _lean_audit_driver_for_modules([mod_name]), [str(root)]
        )
    return {
        "total_declarations": tot,
        "proved": prv,
        "lowered_unproved": unp,
        "rejected": rej,
        "rejected_not_lowered": cyc,
        "rejected_not_lowered_reason": REJECTED_NOT_LOWERED_REASON,
    }


def _ensure_lean_build(root_dir: Path) -> None:
    """Build the Lean library the audit driver imports, if it is not built yet.

    `--check` / `--json` must work from a clean checkout, so the one target the driver
    imports (`LeanNative.IR.Bridge`, and its cone) is built here when its `.olean` is
    missing. A warm tree is left untouched.
    """
    lean_dir = root_dir / "lean"
    bridge_olean = lean_dir / ".lake" / "build" / "lib" / "lean" / "LeanNative" / "IR" / "Bridge.olean"
    if bridge_olean.is_file():
        return
    proc = subprocess.run(
        ["lake", "build", "LeanNative.IR.Bridge"],
        cwd=str(lean_dir),
        env=_lean_env(),
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"`lake build LeanNative.IR.Bridge` failed:\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
        )


def execute_live_lean_audit(root_dir: Path = ROOT_DIR) -> dict[str, Any]:
    cache_key = str(root_dir.resolve())
    if cache_key in _LIVE_AUDIT_CACHE:
        return _LIVE_AUDIT_CACHE[cache_key]

    lean_dir = root_dir / "lean"
    if not (lean_dir / "lakefile.lean").is_file() or not (root_dir / "scripts" / "test_scalar_frontend.py").is_file():
        return {"executed": False, "reason": "missing_lean_workspace"}
    _ensure_lean_build(root_dir)

    env = _lean_env()

    sys.path.insert(0, str(root_dir / "scripts"))
    import fuzz_lcnf_conformance as fuzzer  # type: ignore
    import test_scalar_frontend as tsf  # type: ignore

    with tempfile.TemporaryDirectory(prefix="lcnf-live-audit-") as tmp:
        tmp_path = Path(tmp)
        c1_dir = tmp_path / "c1_mods"
        c1_dir.mkdir(parents=True, exist_ok=True)
        batch_methods = (
            "test_small_width_comparisons",
            "test_narrow_wrapping_arithmetic_shifts_and_div_zero",
            "test_join_point_param_swap_and_nested_helper_inlining",
            "test_chained_boolean_join_points_and_tuple_helpers",
            "test_unsigned_casts_and_input_dependent_boolean_branches",
            "test_c1_bitwise_rotations_clmul_swar_and_diamond_merges",
            "test_c1_multi_enum_state_machine_and_crc_polynomial_fold",
        )
        captured_batches: list[list[dict[str, Any]]] = []
        orig_probe = fuzzer.probe_engines
        orig_run = fuzzer.run_three_way_batch
        try:
            fuzzer.probe_engines = lambda *a, **kw: {"stock_lean_c": True, "lnir_eval": True, "c_abi_llvm": True}

            def _capture_batch(programs: list[dict[str, Any]], *_a: Any, **_kw: Any) -> dict[str, Any]:
                captured_batches.append(programs)
                return {
                    "executed_count": len(programs),
                    "mismatches": [],
                    "receipts": {
                        "sanitizers": {"asan": False, "ubsan": False, "ubsan_scope": "disabled"},
                        "llvm_ir_sha256": "0",
                        "compiled_llvm_ir_sha256": "0",
                    },
                }

            fuzzer.run_three_way_batch = _capture_batch
            tc = tsf.ScalarFrontend("test_small_width_comparisons")
            with open(os.devnull, "w", encoding="utf-8") as devnull:
                old_stdout = sys.stdout
                sys.stdout = devnull
                try:
                    for mname in batch_methods:
                        getattr(tc, mname)()
                finally:
                    sys.stdout = old_stdout
        finally:
            fuzzer.probe_engines = orig_probe
            fuzzer.run_three_way_batch = orig_run

        for b_idx, progs in enumerate(captured_batches):
            mod_name = f"batch_{b_idx}"
            lines = [f"namespace {mod_name}"]
            seen_pre: list[str] = []
            for p in progs:
                pre = p.get("preamble", "")
                if pre and pre not in seen_pre:
                    seen_pre.append(pre)
                    lines.append(pre)
            for p in progs:
                fn_name = f"fuzz_seed_{p['seed']}"
                expr = fuzzer.tree_to_lean_expr(p["tree"])
                lines.append(f"@[export {mod_name}_{fn_name}]")
                lines.append(f"def {fn_name} (x0 : UInt64) : UInt64 := {expr}")
            lines.append(f"end {mod_name}\n")
            (c1_dir / f"{mod_name}.lean").write_text("\n".join(lines), encoding="utf-8")

        s1b_src = Path(tsf.__file__).read_text(encoding="utf-8")
        s1b_body = s1b_src.split('lean_src = """inductive Mode where', 1)[1].split('"""', 1)[0]
        (c1_dir / "C1Batch_stage1b.lean").write_text(
            "namespace C1Batch_stage1b\ninductive Mode where" + s1b_body + "\nend C1Batch_stage1b\n",
            encoding="utf-8",
        )
        neg_snippets = {
            "nat_param": "def bad_nat (n : Nat) : UInt64 := n.toUInt64\n",
            "direct_recursion": "partial def bad_rec (x : UInt64) : UInt64 := if x == 0 then 0 else bad_rec (x - 1)\n",
            "mutual_recursion": "mutual\npartial def ping (x : UInt64) : UInt64 := if x == 0 then 1 else pong (x - 1)\npartial def pong (x : UInt64) : UInt64 := if x == 0 then 2 else ping (x - 1)\nend\n",
            "closure_param": "def bad_clos (f : UInt64 → UInt64) (x : UInt64) : UInt64 := f x\n",
            "heap_adt": "inductive Boxed where | mk (x : UInt64) (s : String)\ndef bad_adt (b : Boxed) : UInt64 := match b with | .mk x _ => x\n",
            "string_lit": 'def bad_str (x : UInt64) : String := if x == 0 then "zero" else "nonzero"\n',
            "unmodeled_extern_log2": "@[export bad_log2]\ndef bad_log2 (x : UInt64) : UInt64 := x.log2\n",
            "user_extern_decl": '@[extern "c_magic"] opaque magic_ext : UInt64 → UInt64\n@[export call_magic]\ndef call_magic (x : UInt64) : UInt64 := magic_ext x\n',
            "signed_int8_param": "@[export bad_i8]\ndef bad_i8 (x : Int8) : Int8 := x + 1\n",
            "signed_int64_internal": "@[export bad_i64_inner]\ndef bad_i64_inner (x : UInt64) : UInt64 := (Int64.ofBitVec x.toBitVec / (-1 : Int64)).toBitVec.toNat.toUInt64\n",
            "signed_int64_transitive": "def sInner (x : UInt64) : UInt64 := (Int64.ofBitVec x.toBitVec / (-1 : Int64)).toBitVec.toNat.toUInt64\n@[export s_outer]\ndef sOuter (x : UInt64) : UInt64 := sInner x + 1\n",
            "single_ctor_enum": "inductive Solo where | only\n@[export bad_solo]\ndef bad_solo (s : Solo) : UInt8 := match s with | .only => 1\n",
        }
        for name, src in neg_snippets.items():
            mod_name = f"C1Neg_{name}"
            (c1_dir / f"{mod_name}.lean").write_text(
                f"namespace {mod_name}\n{src}\nend {mod_name}\n",
                encoding="utf-8",
            )

        lean_files = sorted(c1_dir.glob("*.lean"))

        def _compile_one(lf: Path) -> None:
            subprocess.run(
                ["lean", f"--root={c1_dir}", "-o", str(lf.with_suffix(".olean")), str(lf)],
                cwd=str(lean_dir),
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )

        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
            list(pool.map(_compile_one, lean_files))

        driver_path = tmp_path / "AuditDriver.lean"
        driver_path.write_text(_LEAN_AUDIT_DRIVER_SRC, encoding="utf-8")

        c2_pkgs = ["C2BitwiseScan", "C2FieldButterfly", "C2ProtocolMachine", "C2CryptoSipHash"]
        c2_lib_dirs: list[str] = []
        for pkg in c2_pkgs:
            pkg_dir = root_dir / "verification" / "c2-lake-packages" / pkg
            lib_dir = pkg_dir / ".lake" / "build" / "lib" / "lean"
            if not lib_dir.is_dir():
                manifest = pkg_dir / "lake-manifest.json"
                had_manifest = manifest.exists()
                subprocess.run(["lake", "build"], cwd=str(pkg_dir), env=env, check=True, capture_output=True, text=True)
                if not had_manifest and manifest.exists():
                    manifest.unlink()
            c2_lib_dirs.append(str(lib_dir))

        proc = subprocess.run(
            ["lake", "env", "lean", "--run", str(driver_path), *c2_lib_dirs, str(c1_dir)],
            cwd=str(lean_dir),
            env=env,
            capture_output=True,
            text=True,
        )
        if proc.returncode != 0:
            raise RuntimeError(f"Lean audit driver failed:\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}")
        raw_lines = [ln.strip() for ln in proc.stdout.splitlines() if ln.strip().startswith("AUDIT_RESULT:")]
        parts = raw_lines[-1].split(":", 1)[1].split(";")
        st, sp, su, sr, sc = (int(x) for x in parts[0].split(","))
        c2t, c2p, c2u, c2r, c2c = (int(x) for x in parts[1].split(","))
        c1t, c1p, c1u, c1r, c1c = (int(x) for x in parts[2].split(","))

    result = {
        "executed": True,
        "toolchain": PINNED_TOOLCHAIN,
        "std_init_and_c2": {
            "total_declarations": st + c2t,
            "proved": sp + c2p,
            "lowered_unproved": su + c2u,
            "rejected": sr + c2r,
            "rejected_not_lowered": sc + c2c,
            "rejected_not_lowered_reason": REJECTED_NOT_LOWERED_REASON,
            "subcorpora": {
                "std_init_data": {
                    "total_declarations": st,
                    "proved": sp,
                    "lowered_unproved": su,
                    "rejected": sr,
                    "rejected_not_lowered": sc,
                    "rejected_not_lowered_reason": REJECTED_NOT_LOWERED_REASON,
                },
                "c2_lake_packages": {
                    "total_declarations": c2t,
                    "proved": c2p,
                    "lowered_unproved": c2u,
                    "rejected": c2r,
                    "rejected_not_lowered": c2c,
                    "rejected_not_lowered_reason": REJECTED_NOT_LOWERED_REASON,
                },
            },
        },
        "c1_corpus": {
            "total_declarations": c1t,
            "proved": c1p,
            "lowered_unproved": c1u,
            "rejected": c1r,
            "rejected_not_lowered": c1c,
            "rejected_not_lowered_reason": REJECTED_NOT_LOWERED_REASON,
        },
    }
    _LIVE_AUDIT_CACHE[cache_key] = result
    return result


def _utc_now() -> str:
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _git_head(root_dir: Path) -> str:
    try:
        return subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=str(root_dir),
            capture_output=True,
            text=True,
            timeout=30,
            check=True,
        ).stdout.strip()
    except Exception:
        return "unknown"


def _con_leche_olean_root(root_dir: Path = ROOT_DIR) -> Path | None:
    """Where a prebuilt pinned con-leche `.olean` tree is, if there is one.

    `TURBO_CON_LECHE_OLEANS` wins. Otherwise the tree that `lake build` of
    `verification/con-leche-bridge` leaves behind is used when present.
    """
    raw = os.environ.get(CON_LECHE_OLEANS_ENV, "").strip()
    if raw:
        p = Path(raw)
        return p if p.is_dir() else None
    default = (
        root_dir / "verification" / "con-leche-bridge" / ".lake" / "packages"
        / "con-leche" / ".lake" / "build" / "lib" / "lean"
    )
    return default if default.is_dir() else None


def _con_leche_modules(olean_root: Path) -> list[str]:
    mods: list[str] = []
    for olean in olean_root.rglob("*.olean"):
        rel = olean.relative_to(olean_root).with_suffix("")
        name = ".".join(rel.parts)
        if name in CON_LECHE_EXCLUDED_MODULES:
            continue
        if name == "ConLeche" or name == "Main" or name.startswith(CON_LECHE_MODULE_PREFIXES):
            mods.append(name)
    return sorted(mods)


def _is_full_con_leche_build(olean_root: Path) -> bool:
    """True when `olean_root` sits inside a completed `lake build` that produced the `con-leche` executable."""
    # Standard Lake layout: `<checkout>/.lake/build/lib/lean` -> sibling `../../bin/con-leche`.
    for cand in (
        olean_root.parent.parent / "bin" / "con-leche",
        olean_root.parent / "bin" / "con-leche",
    ):
        if cand.is_file():
            return True
    return False


def measure_con_leche(root_dir: Path = ROOT_DIR) -> dict[str, Any]:
    """Measure the pinned con-leche corpus with the real lowerer, or say why not.

    Nothing is fetched or built: the caller points `TURBO_CON_LECHE_OLEANS` at an
    already-built tree of the pinned revision. Without one, or on a partial build,
    the corpus is reported as `not_measured` and carries no declaration number.
    When `PINNED_CON_LECHE_REV` has no entry in `CON_LECHE_PINNED_MODULE_COUNTS`, or
    a full built tree at `PINNED_CON_LECHE_REV` has a different module count, this
    returns `measurement_source = "error"` with a named `error_code`.
    """
    exclusion = {
        "excluded_modules": sorted(CON_LECHE_EXCLUDED_MODULES),
        "reason": CON_LECHE_EXCLUSION_REASON,
    }
    expected_count = CON_LECHE_PINNED_MODULE_COUNTS.get(PINNED_CON_LECHE_REV)
    if expected_count is None:
        return {
            "measurement_source": "error",
            "error_code": "unmapped_pinned_con_leche_revision",
            "pinned_revision": PINNED_CON_LECHE_REV,
            "reason": (
                f"unmapped_pinned_con_leche_revision: PINNED_CON_LECHE_REV={PINNED_CON_LECHE_REV!r} "
                f"has no expected module count in CON_LECHE_PINNED_MODULE_COUNTS"
            ),
            "exclusion": exclusion,
        }
    olean_root = _con_leche_olean_root(root_dir)
    cache_key = f"{root_dir.resolve()}|{PINNED_CON_LECHE_REV}|{expected_count}|{olean_root}"
    if cache_key in _CON_LECHE_CACHE:
        return _CON_LECHE_CACHE[cache_key]
    if olean_root is None:
        result = {
            "measurement_source": "not_measured",
            "reason": (
                f"no prebuilt pinned con-leche `.olean` tree: set {CON_LECHE_OLEANS_ENV} to a "
                f"`lake build` output directory of commit {PINNED_CON_LECHE_REV}; this script "
                "does not fetch or build that repository."
            ),
            "expected_module_count": expected_count,
            "exclusion": exclusion,
        }
        _CON_LECHE_CACHE[cache_key] = result
        return result
    # The checkout is the nearest ancestor that is a git work tree.
    rev = "unknown"
    probe = olean_root
    for _ in range(6):
        if (probe / ".git").exists():
            rev = _git_head(probe)
            break
        probe = probe.parent
    if rev != PINNED_CON_LECHE_REV:
        result = {
            "measurement_source": "not_measured",
            "reason": (
                f"prebuilt con-leche tree at `{olean_root}` is revision `{rev}`, not the pinned "
                f"`{PINNED_CON_LECHE_REV}`"
            ),
            "expected_module_count": expected_count,
            "exclusion": exclusion,
        }
        _CON_LECHE_CACHE[cache_key] = result
        return result
    modules = _con_leche_modules(olean_root)
    if not modules:
        result = {
            "measurement_source": "not_measured",
            "reason": f"no `ConLeche.*`/`Main` `.olean` modules under `{olean_root}`",
            "module_count": 0,
            "expected_module_count": expected_count,
            "exclusion": exclusion,
        }
        _CON_LECHE_CACHE[cache_key] = result
        return result
    if len(modules) != expected_count:
        if _is_full_con_leche_build(olean_root):
            result = {
                "measurement_source": "error",
                "error_code": "con_leche_module_count_mismatch",
                "commit_sha": PINNED_CON_LECHE_REV,
                "olean_root": str(olean_root),
                "module_count": len(modules),
                "expected_module_count": expected_count,
                "reason": (
                    f"con_leche_module_count_mismatch: full con-leche build at `{olean_root}` "
                    f"(revision {PINNED_CON_LECHE_REV}) has {len(modules)} modules after excluding "
                    f"{', '.join(sorted(CON_LECHE_EXCLUDED_MODULES))}, expected {expected_count}"
                ),
                "exclusion": exclusion,
            }
        else:
            result = {
                "measurement_source": "not_measured",
                "reason": (
                    f"partial con-leche tree under `{olean_root}` has {len(modules)} modules, "
                    f"whereas pinned revision {PINNED_CON_LECHE_REV} has {expected_count} "
                    f"after excluding {', '.join(sorted(CON_LECHE_EXCLUDED_MODULES))} "
                    f"({CON_LECHE_EXCLUSION_REASON}); refusing to measure a partial tree"
                ),
                "module_count": len(modules),
                "expected_module_count": expected_count,
                "exclusion": exclusion,
            }
        _CON_LECHE_CACHE[cache_key] = result
        return result
    total, proved, unproved, rejected, rejected_not_lowered = _run_audit_driver(
        root_dir, _lean_audit_driver_for_modules(modules), [str(olean_root)]
    )
    result = {
        "measurement_source": "live_invocation",
        "measured_at_utc": _utc_now(),
        "repository": "https://github.com/leanprover/con-leche.git",
        "commit_sha": PINNED_CON_LECHE_REV,
        "olean_root": str(olean_root),
        "module_count": len(modules),
        "expected_module_count": expected_count,
        "exclusion": exclusion,
        "total_declarations": total,
        "proved": proved,
        "lowered_unproved": unproved,
        "rejected": rejected,
        "rejected_not_lowered": rejected_not_lowered,
        "rejected_not_lowered_reason": REJECTED_NOT_LOWERED_REASON,
    }
    _CON_LECHE_CACHE[cache_key] = result
    return result


def _batteries_unknown_reason() -> str:
    return (
        "External `leanprover-community/batteries` modules beyond `Init.Data.*` and "
        "`Std.Data.*` are not measured by this invocation (`C2x` adds the nightly "
        "Batteries checkout); reported as unknown rather than estimated."
    )


def build_live_corpora(root_dir: Path = ROOT_DIR) -> dict[str, Any]:
    """Shape the emitted corpora from a measurement made in this invocation.

    Every count in a corpus marked `live_invocation` was measured by this call; a
    corpus that cannot be measured is emitted as `not_measured` with its reason and
    carries no number. To add a corpus, add one branch here and one entry in
    `CORPUS_SCOPES`; `check_coverage_report` iterates whatever is emitted.
    """
    live = execute_live_lean_audit(root_dir)
    corpora: dict[str, Any] = {}
    if not live.get("executed", False):
        corpora["std_init_and_c2"] = {
            "measurement_source": "not_measured",
            "reason": f"live audit did not execute: {live.get('reason', 'unknown')}",
        }
        corpora["c1_corpus"] = dict(corpora["std_init_and_c2"])
    else:
        bat = live["std_init_and_c2"]
        corpora["std_init_and_c2"] = {
            "measurement_source": "live_invocation",
            "measured_at_utc": _utc_now(),
            "scope": CORPUS_SCOPES["std_init_and_c2"],
            "toolchain": PINNED_TOOLCHAIN,
            "total_declarations": bat["total_declarations"],
            "proved": bat["proved"],
            "lowered_unproved": bat["lowered_unproved"],
            "rejected": bat["rejected"],
            "rejected_not_lowered": bat["rejected_not_lowered"],
            "rejected_not_lowered_reason": bat["rejected_not_lowered_reason"],
            "subcorpora": bat["subcorpora"],
        }
        c1 = live["c1_corpus"]
        corpora["c1_corpus"] = {
            "measurement_source": "live_invocation",
            "measured_at_utc": _utc_now(),
            "scope": CORPUS_SCOPES["c1_corpus"],
            "toolchain": PINNED_TOOLCHAIN,
            "total_declarations": c1["total_declarations"],
            "proved": c1["proved"],
            "lowered_unproved": c1["lowered_unproved"],
            "rejected": c1["rejected"],
            "rejected_not_lowered": c1["rejected_not_lowered"],
            "rejected_not_lowered_reason": c1["rejected_not_lowered_reason"],
        }
    corpora["external_batteries"] = {
        "status": "unknown",
        "reason": _batteries_unknown_reason(),
    }
    corpora["con_leche_h3_benchmark"] = measure_con_leche(root_dir)
    return corpora


def build_coverage_report(root_dir: Path = ROOT_DIR) -> dict[str, Any]:
    file_digests: dict[str, dict[str, str | bool]] = {}
    for rel, pinned_sha in TRACKED_BRIDGE_FILES.items():
        p = root_dir / rel
        actual_sha = sha256_file(p) if p.is_file() else ""
        file_digests[rel] = {
            "pinned_sha256": pinned_sha,
            "actual_sha256": actual_sha,
            "matches": actual_sha == pinned_sha,
        }

    rows = [dict(r) for r in LCNF_CONSTRUCTOR_MATRIX_SPEC]
    proved_cnt = sum(1 for r in rows if r["status"] == "proved")
    unproved_cnt = sum(1 for r in rows if r["status"] == "lowered_unproved")
    rejected_cnt = sum(1 for r in rows if r["status"] == "rejected")

    corpora = build_live_corpora(root_dir)

    return {
        "schemaVersion": "turbo-lean-lcnf-coverage-v2-live",
        "leaf_id": "H1.0",
        "toolchain": PINNED_TOOLCHAIN,
        "bridge_source_digests": file_digests,
        "lcnf_constructor_matrix": {
            "summary": {
                "total": len(rows),
                "proved": proved_cnt,
                "lowered_unproved": unproved_cnt,
                "rejected": rejected_cnt,
            },
            "rows": rows,
        },
        "corpora": corpora,
        "measurement_provenance": {
            "command": " ".join([sys.executable, *sys.argv]),
            "date_utc": _utc_now(),
            "revisions": {
                "toolchain": PINNED_TOOLCHAIN,
                "turbo_lean_head": _git_head(root_dir),
                "con_leche": PINNED_CON_LECHE_REV,
            },
        },
    }


def results_document(report: dict[str, Any], root_dir: Path = ROOT_DIR) -> dict[str, Any]:
    """Build the committed baseline (`scripts/lcnf_coverage_results.json`) from a live report."""
    head = _git_head(root_dir)
    corpora: dict[str, Any] = {}
    for cname, corp in report.get("corpora", {}).items():
        if corp.get("status") == "unknown" or corp.get("measurement_source") != "live_invocation":
            continue
        entry: dict[str, Any] = {f: corp[f] for f in RESULT_FIELDS if f in corp}
        if "rejected_not_lowered_reason" in corp:
            entry["rejected_not_lowered_reason"] = corp["rejected_not_lowered_reason"]
        if "subcorpora" in corp:
            entry["subcorpora"] = {
                sname: {
                    **{f: sc[f] for f in RESULT_FIELDS if f in sc},
                    **(
                        {"rejected_not_lowered_reason": sc["rejected_not_lowered_reason"]}
                        if "rejected_not_lowered_reason" in sc
                        else {}
                    ),
                }
                for sname, sc in corp["subcorpora"].items()
            }
        corpora[cname] = entry
    return {
        "schemaVersion": "turbo-lean-lcnf-coverage-results-v1",
        "toolchain": PINNED_TOOLCHAIN,
        "measured_source_commit": head,
        "measured_source_commit_note": (
            "`measured_source_commit` is the commit of the tree the measurement was taken from "
            "(recorded when `--write-results` ran, i.e. the parent of the commit that updates this file)."
        ),
        "corpora": corpora,
    }


def _validate_measured_entry(path: str, entry: Any, errors: list[str], depth: int = 0) -> None:
    """Fail-closed validation of one measured baseline corpus/subcorpus entry."""
    if not isinstance(entry, dict):
        errors.append(f"Results file `{path}` must be a JSON object, got {type(entry).__name__}")
        return
    if entry.get("measurement_source") == "not_measured":
        # An explicit `not_measured` stub is honest only with a reason and no counts.
        if not entry.get("reason"):
            errors.append(f"Results file `{path}` is marked not_measured but gives no reason")
        if any(k in entry for k in RESULT_FIELDS):
            errors.append(f"Results file `{path}` is marked not_measured yet carries declaration counts")
        if "subcorpora" in entry:
            errors.append(f"Results file `{path}` is marked not_measured yet carries subcorpora")
        return
    if depth > 0 and "subcorpora" in entry:
        # The supported schema is corpus -> subcorpora only. A deeper level has
        # no live counterpart to compare against, so accepting it would let a
        # fabricated subtree hide behind a valid parent sum.
        errors.append(
            f"Results file `{path}` carries subcorpora at unsupported depth "
            f"(only corpus -> subcorpora is supported)"
        )
        return
    for f in RESULT_FIELDS:
        if f not in entry:
            errors.append(f"Results file `{path}` is missing measured field `{f}`")
            continue
        v = entry[f]
        if isinstance(v, bool) or not isinstance(v, int):
            errors.append(
                f"Results file `{path}` field `{f}` must be an integer, got {type(v).__name__} {v!r}"
            )
        elif v < 0:
            errors.append(f"Results file `{path}` field `{f}` must be >= 0, got {v}")
    counts = [
        entry[f]
        for f in RESULT_FIELDS
        if isinstance(entry.get(f), int) and not isinstance(entry.get(f), bool)
    ]
    if len(counts) == len(RESULT_FIELDS):
        tot, prv, unp, rej, rnl = counts
        if prv + unp + rej != tot:
            errors.append(
                f"Results file `{path}` counts do not sum: "
                f"proved({prv}) + lowered_unproved({unp}) + rejected({rej}) != total_declarations({tot})"
            )
        if not 0 <= rnl <= rej:
            errors.append(
                f"Results file `{path}` rejected_not_lowered({rnl}) must be within 0..rejected({rej})"
            )
        reason = entry.get("rejected_not_lowered_reason")
        if not isinstance(reason, str) or not reason:
            errors.append(f"Results file `{path}` is missing valid `rejected_not_lowered_reason`")
    subs = entry.get("subcorpora")
    if subs is None:
        return
    if not isinstance(subs, dict):
        errors.append(f"Results file `{path}`.subcorpora must be a JSON object, got {type(subs).__name__}")
        return
    for sname, sc in subs.items():
        _validate_measured_entry(f"{path}.subcorpora.{sname}", sc, errors, depth=depth + 1)
    parent_ints = all(
        f in entry and isinstance(entry[f], int) and not isinstance(entry[f], bool)
        for f in RESULT_FIELDS
    )
    sub_ints = all(
        isinstance(sc, dict)
        and all(f in sc and isinstance(sc[f], int) and not isinstance(sc[f], bool) for f in RESULT_FIELDS)
        for sc in subs.values()
    )
    if parent_ints and sub_ints:
        for f in RESULT_FIELDS:
            summed = sum(sc[f] for sc in subs.values())
            if summed != entry[f]:
                errors.append(
                    f"Results file `{path}` subcorpora {f} sums to {summed} "
                    f"but the corpus records {entry[f]}"
                )


def validate_results_document(doc: Any) -> list[str]:
    """Fail-closed structural validation of the committed baseline document.

    Checks `schemaVersion`, `measured_source_commit`, and — for every measured
    corpus and subcorpus — the presence, integer types, sums, and
    `rejected_not_lowered` bounds of all defined measured fields, plus honest
    explicit `not_measured` stubs (reason required, no counts). Returns named
    errors; never raises.
    """
    if not isinstance(doc, dict):
        return ["Results file must be a JSON object"]
    errors: list[str] = []
    if doc.get("schemaVersion") != "turbo-lean-lcnf-coverage-results-v1":
        errors.append(
            "Results file schemaVersion must be `turbo-lean-lcnf-coverage-results-v1`, "
            f"got {doc.get('schemaVersion')!r}"
        )
    if doc.get("toolchain") != PINNED_TOOLCHAIN:
        errors.append(
            f"Results file toolchain mismatch: file={doc.get('toolchain')!r} "
            f"live={PINNED_TOOLCHAIN!r}"
        )
    msc = doc.get("measured_source_commit")
    if not isinstance(msc, str) or not msc:
        errors.append("Results file is missing `measured_source_commit`")
    corpora = doc.get("corpora", {})
    if not isinstance(corpora, dict):
        errors.append("Results file `corpora` must be a JSON object")
        return errors
    for cname, entry in corpora.items():
        _validate_measured_entry(f"corpora.{cname}", entry, errors)
    return errors


def check_coverage_report(
    root_dir: Path = ROOT_DIR,
    report: dict[str, Any] | None = None,
    verify_live: bool = False,
    results: dict[str, Any] | None = None,
    require_results: bool = False,
) -> dict[str, Any]:
    errors: list[str] = []
    skipped_corpora: list[str] = []
    rep = report if report is not None else build_coverage_report(root_dir)

    for rel, info in rep.get("bridge_source_digests", {}).items():
        fpath = root_dir / rel
        if not fpath.is_file():
            errors.append(f"Missing tracked bridge file: {rel}")
            continue
        if not info.get("matches", False):
            errors.append(
                f"Bridge source digest mismatch for {rel}: "
                f"pinned={info.get('pinned_sha256')} actual={info.get('actual_sha256')}"
            )

    for row in rep["lcnf_constructor_matrix"]["rows"]:
        ev_file = root_dir / row["evidence_file"]
        if ev_file.is_file():
            txt = ev_file.read_text(encoding="utf-8")
            if row["evidence_symbol"] not in txt:
                errors.append(
                    f"Matrix row `{row['id']}` evidence symbol `{row['evidence_symbol']}` not found in {row['evidence_file']}"
                )

    c_matrix = rep["lcnf_constructor_matrix"]
    c_sum = c_matrix["summary"]
    c_rows = c_matrix["rows"]
    if len(c_rows) != c_sum["total"]:
        errors.append("Matrix row count does not match summary.total")
    if c_sum["total"] != c_sum["proved"] + c_sum["lowered_unproved"] + c_sum["rejected"]:
        errors.append("Matrix summary counts do not sum to total")

    for cname, corp in rep.get("corpora", {}).items():
        source = corp.get("measurement_source")
        if corp.get("status") == "unknown":
            if not corp.get("reason"):
                errors.append(f"Corpus `{cname}` is unknown but gives no reason")
            if any(k in corp for k in RESULT_FIELDS):
                errors.append(f"Corpus `{cname}` is unknown yet carries declaration counts")
            continue
        if source == "not_measured":
            if not corp.get("reason"):
                errors.append(f"Corpus `{cname}` is not measured but gives no reason")
            if any(k in corp for k in RESULT_FIELDS):
                errors.append(f"Corpus `{cname}` is not measured yet carries declaration counts")
            continue
        if source == "error":
            code = corp.get("error_code", "corpus_measurement_error")
            errors.append(
                f"Corpus `{cname}` error [{code}]: {corp.get('reason', 'no reason given')}"
            )
            continue
        if source != "live_invocation":
            errors.append(
                f"Corpus `{cname}` carries no live measurement: "
                f"{corp.get('reason', 'no reason given')}"
            )
            continue
        tot = corp["total_declarations"]
        if tot != corp["proved"] + corp["lowered_unproved"] + corp["rejected"]:
            errors.append(f"Corpus `{cname}` declaration counts do not sum to total_declarations")
        rnl = corp.get("rejected_not_lowered")
        if rnl is None or not (0 <= rnl <= corp["rejected"]) or not corp.get("rejected_not_lowered_reason"):
            errors.append(f"Corpus `{cname}` missing valid `rejected_not_lowered` / `rejected_not_lowered_reason`")
        if "subcorpora" in corp:
            subs = corp["subcorpora"]
            if not isinstance(subs, dict):
                errors.append(
                    f"Corpus `{cname}` subcorpora must be a JSON object, got {type(subs).__name__}"
                )
            else:
                for sname, sc in subs.items():
                    if not isinstance(sc, dict):
                        errors.append(
                            f"Corpus `{cname}` subcorpus `{sname}` must be a JSON object, "
                            f"got {type(sc).__name__}"
                        )
                    elif "subcorpora" in sc:
                        errors.append(
                            f"Corpus `{cname}` subcorpus `{sname}` carries subcorpora at "
                            f"unsupported depth (only corpus -> subcorpora is supported)"
                        )
                sub_ints = all(
                    isinstance(sc, dict) and all(f in sc for f in RESULT_FIELDS)
                    for sc in subs.values()
                )
                if not sub_ints:
                    errors.append(
                        f"Corpus `{cname}` subcorpora do not all carry the measured fields"
                    )
                else:
                    sub_tot = sum(s["total_declarations"] for s in subs.values())
                    sub_prv = sum(s["proved"] for s in subs.values())
                    sub_unp = sum(s["lowered_unproved"] for s in subs.values())
                    sub_rej = sum(s["rejected"] for s in subs.values())
                    sub_rnl = sum(s.get("rejected_not_lowered", 0) for s in subs.values())
                    if (sub_tot, sub_prv, sub_unp, sub_rej, sub_rnl) != (
                        tot,
                        corp["proved"],
                        corp["lowered_unproved"],
                        corp["rejected"],
                        corp.get("rejected_not_lowered", 0),
                    ):
                        errors.append(
                            f"Corpus `{cname}` subcorpora totals do not sum to corpus totals"
                        )

    baseline_doc = results
    if baseline_doc is None and require_results:
        results_path = root_dir / "scripts" / "lcnf_coverage_results.json"
        if not results_path.is_file():
            errors.append(f"Missing committed results file: {results_path.relative_to(root_dir)}")
        else:
            baseline_doc = json.loads(results_path.read_text(encoding="utf-8"))

    if baseline_doc is not None:
        errors.extend(validate_results_document(baseline_doc))
        base_corpora = baseline_doc.get("corpora", {}) if isinstance(baseline_doc, dict) else {}
        if not isinstance(base_corpora, dict):
            base_corpora = {}
        live_corpora = rep.get("corpora", {})
        for cname, corp in live_corpora.items():
            if corp.get("status") == "unknown":
                # External Batteries stays unknown and is not compared.
                continue
            if corp.get("measurement_source") in ("not_measured", "error"):
                # A live corpus that is absent from the baseline can be an honest
                # skip; a baseline entry is reconciled in the loop below.
                if (
                    corp.get("measurement_source") == "not_measured"
                    and cname not in base_corpora
                ):
                    skipped_corpora.append(cname)
                continue
            if cname not in base_corpora:
                errors.append(f"Corpus `{cname}` was measured live but is missing from scripts/lcnf_coverage_results.json")
                continue
            base_c = base_corpora[cname]
            if not isinstance(base_c, dict):
                continue  # already named by validate_results_document
            if base_c.get("measurement_source") == "not_measured":
                errors.append(
                    f"Corpus `{cname}` is measured live but scripts/lcnf_coverage_results.json marks it not_measured"
                )
                continue
            diffs = [f for f in RESULT_FIELDS if base_c.get(f) != corp.get(f)]
            if diffs:
                side_summary = ", ".join(
                    f"{f}={base_c.get(f)} vs {corp.get(f)}" for f in RESULT_FIELDS
                )
                errors.append(
                    f"Corpus `{cname}` differs from scripts/lcnf_coverage_results.json "
                    f"(file vs live): {side_summary}"
                )
            if base_c.get("rejected_not_lowered_reason") != corp.get("rejected_not_lowered_reason"):
                errors.append(
                    f"Corpus `{cname}` field `rejected_not_lowered_reason` differs from "
                    f"scripts/lcnf_coverage_results.json "
                    f"(file={base_c.get('rejected_not_lowered_reason')!r} vs "
                    f"live={corp.get('rejected_not_lowered_reason')!r})"
                )
            base_subs = base_c.get("subcorpora", {})
            if not isinstance(base_subs, dict):
                base_subs = {}  # already named by validate_results_document
            live_subs = corp.get("subcorpora", {})
            if not isinstance(live_subs, dict):
                live_subs = {}
            for sname, sc in live_subs.items():
                if sname not in base_subs:
                    errors.append(
                        f"Corpus `{cname}` subcorpus `{sname}` is missing from scripts/lcnf_coverage_results.json"
                    )
                    continue
                bsc = base_subs[sname]
                if not isinstance(bsc, dict):
                    continue  # already named by validate_results_document
                for f in RESULT_FIELDS:
                    if bsc.get(f) != sc.get(f):
                        errors.append(
                            f"Corpus `{cname}` subcorpus `{sname}` field `{f}` differs from "
                            f"scripts/lcnf_coverage_results.json (file={bsc.get(f)} vs live={sc.get(f)})"
                        )
                if bsc.get("rejected_not_lowered_reason") != sc.get("rejected_not_lowered_reason"):
                    errors.append(
                        f"Corpus `{cname}` subcorpus `{sname}` field `rejected_not_lowered_reason` differs "
                        f"from scripts/lcnf_coverage_results.json "
                        f"(file={bsc.get('rejected_not_lowered_reason')!r} vs "
                        f"live={sc.get('rejected_not_lowered_reason')!r})"
                    )
            for sname in base_subs:
                if sname not in live_subs:
                    errors.append(
                        f"Corpus `{cname}` has subcorpus `{sname}` in scripts/lcnf_coverage_results.json "
                        f"but the live report does not"
                    )
        for cname, base_c in base_corpora.items():
            live_c = live_corpora.get(cname)
            if live_c is None:
                errors.append(f"Corpus `{cname}` is in scripts/lcnf_coverage_results.json but missing from live report")
                continue
            if not isinstance(base_c, dict):
                continue  # already named by validate_results_document
            if base_c.get("measurement_source") == "not_measured":
                # An honest baseline stub matching a live not_measured report is
                # an intentional skip (e.g. an external corpus deliberately absent).
                if live_c.get("measurement_source") == "not_measured" and cname not in skipped_corpora:
                    skipped_corpora.append(cname)
                continue
            live_source = live_c.get("measurement_source")
            if live_source == "not_measured":
                errors.append(
                    f"Corpus `{cname}` is measured in scripts/lcnf_coverage_results.json "
                    f"but not_measured live; refusing to skip a baseline with counts"
                )
            elif live_source == "error":
                errors.append(
                    f"Corpus `{cname}` is measured in scripts/lcnf_coverage_results.json "
                    f"but the live measurement errored; refusing to skip a baseline with counts"
                )

    if verify_live:
        live = execute_live_lean_audit(root_dir)
        if not live.get("executed", False):
            errors.append(f"Live Lean lowerer execution failed: {live.get('reason', 'unknown')}")
        else:
            for cname in ("std_init_and_c2", "c1_corpus"):
                if cname not in live:
                    continue
                c_rep = rep.get("corpora", {}).get(cname, {})
                c_live = live[cname]
                if c_rep.get("measurement_source") != "live_invocation":
                    errors.append(f"Corpus `{cname}` has no live measurement to compare")
                    continue
                for field in RESULT_FIELDS:
                    if c_rep[field] != c_live[field]:
                        errors.append(
                            f"Corpus `{cname}` live execution mismatch on `{field}`: "
                            f"report={c_rep[field]} live={c_live[field]}"
                        )
        c_rep = rep.get("corpora", {}).get("con_leche_h3_benchmark", {})
        c_fresh = measure_con_leche(root_dir)
        if c_rep.get("measurement_source") == "live_invocation":
            if c_fresh.get("measurement_source") != "live_invocation":
                errors.append(
                    f"Corpus `con_leche_h3_benchmark` claims a live measurement but a fresh "
                    f"run cannot measure it: {c_fresh.get('reason', 'unknown')}"
                )
            else:
                for field in RESULT_FIELDS:
                    if c_rep[field] != c_fresh[field]:
                        errors.append(
                            f"Corpus `con_leche_h3_benchmark` live execution mismatch on `{field}`: "
                            f"report={c_rep[field]} live={c_fresh[field]}"
                        )

    return {
        "ok": len(errors) == 0,
        "errors": errors,
        "skipped_corpora": skipped_corpora,
        "report": rep,
    }


class TestLcnfCoverage(unittest.TestCase):
    def test_live_coverage_report_and_invariants(self) -> None:
        chk = check_coverage_report(ROOT_DIR, require_results=True)
        self.assertTrue(chk["ok"], chk["errors"])
        rep = chk["report"]
        self.assertEqual(rep["schemaVersion"], "turbo-lean-lcnf-coverage-v2-live")
        self.assertEqual(rep["leaf_id"], "H1.0")
        summary = rep["lcnf_constructor_matrix"]["summary"]
        rows = rep["lcnf_constructor_matrix"]["rows"]
        self.assertEqual(summary["total"], len(rows))
        self.assertEqual(
            summary["total"],
            summary["proved"] + summary["lowered_unproved"] + summary["rejected"],
        )
        bat = rep["corpora"]["std_init_and_c2"]
        self.assertEqual(bat["measurement_source"], "live_invocation")
        self.assertEqual(rep["corpora"]["external_batteries"]["status"], "unknown")
        self.assertGreater(bat["total_declarations"], 0)
        self.assertEqual(
            bat["total_declarations"],
            bat["proved"] + bat["lowered_unproved"] + bat["rejected"],
        )

    def test_json_corpus_numbers_come_from_live_measurement(self) -> None:
        # (a): `--json` must emit the same live measurement `--check` performs, never
        # stored constants. Every measured corpus carries measurement_source=live_invocation.
        proc = subprocess.run(
            [sys.executable, str(Path(__file__).resolve()), "--json"],
            capture_output=True,
            text=True,
            timeout=3600,
        )
        self.assertEqual(proc.returncode, 0, proc.stderr[-2000:])
        data = json.loads(proc.stdout)
        for cname in ("std_init_and_c2", "c1_corpus"):
            corp = data["corpora"][cname]
            self.assertEqual(
                corp.get("measurement_source"),
                "live_invocation",
                f"corpus `{cname}` was not measured live in this invocation",
            )
        prov = data.get("measurement_provenance", {})
        self.assertIn("command", prov)
        self.assertIn("date_utc", prov)
        self.assertIn("revisions", prov)

    def test_unmeasured_corpus_carries_no_number(self) -> None:
        # (c): a corpus that cannot be measured is `not_measured` with a reason and no
        # declaration counts; that is honest output, so `--check` accepts it, but the
        # corpus never carries a stored fallback number.
        corp = measure_con_leche(ROOT_DIR)
        self.assertEqual(corp["measurement_source"], "not_measured")
        self.assertTrue(corp["reason"])
        for field in ("total_declarations", "proved", "lowered_unproved", "rejected"):
            self.assertNotIn(field, corp)
        rep = build_coverage_report(ROOT_DIR)
        self.assertEqual(rep["corpora"]["con_leche_h3_benchmark"]["measurement_source"], "not_measured")
        named = check_coverage_report(ROOT_DIR, rep)
        self.assertTrue(named["ok"], named["errors"])

    def test_not_measured_corpus_without_reason_fails_check(self) -> None:
        rep = build_coverage_report(ROOT_DIR)
        rep["corpora"]["con_leche_h3_benchmark"] = {"measurement_source": "not_measured"}
        chk = check_coverage_report(ROOT_DIR, rep)
        self.assertFalse(chk["ok"])
        self.assertTrue(any("con_leche_h3_benchmark" in e and "reason" in e for e in chk["errors"]))

    def test_con_leche_numbers_come_from_the_named_olean_tree(self) -> None:
        # (c): when a prebuilt pinned con-leche tree is named, its totals must come from
        # running the lowerer over it in this invocation, not from a stored table.
        import unittest.mock as mock

        with tempfile.TemporaryDirectory(prefix="cl-tree-") as tmp:
            root = Path(tmp)
            (root / ".git").mkdir()
            lib = root / "lib" / "lean" / "ConLeche" / "Kernel"
            lib.mkdir(parents=True)
            for name in ("Name", "Expr", "NatOpPins"):
                (lib / f"{name}.olean").write_bytes(b"")
            saved = os.environ.get("TURBO_CON_LECHE_OLEANS")
            os.environ["TURBO_CON_LECHE_OLEANS"] = str(root / "lib" / "lean")
            try:
                with mock.patch.object(
                    sys.modules[__name__], "_run_audit_driver", return_value=(100, 7, 11, 82, 4)
                ) as run, mock.patch.object(
                    sys.modules[__name__], "_git_head", return_value=PINNED_CON_LECHE_REV
                ), mock.patch.dict(
                    sys.modules[__name__].CON_LECHE_PINNED_MODULE_COUNTS, {PINNED_CON_LECHE_REV: 2}
                ):
                    corp = measure_con_leche(ROOT_DIR)
            finally:
                if saved is None:
                    os.environ.pop("TURBO_CON_LECHE_OLEANS", None)
                else:
                    os.environ["TURBO_CON_LECHE_OLEANS"] = saved
        self.assertEqual(corp["measurement_source"], "live_invocation")
        self.assertEqual(
            (corp["total_declarations"], corp["proved"], corp["lowered_unproved"], corp["rejected"]),
            (100, 7, 11, 82),
        )
        self.assertEqual(corp["commit_sha"], PINNED_CON_LECHE_REV)
        self.assertEqual(corp["module_count"], 2)
        self.assertEqual(corp["expected_module_count"], 2)
        self.assertEqual(corp["exclusion"]["excluded_modules"], ["ConLeche.Kernel.NatOpPins"])
        self.assertTrue(corp["exclusion"]["reason"])
        run.assert_called_once()
        # NatOpPins is excluded by name from the measured module set.
        self.assertNotIn("ConLeche.Kernel.NatOpPins", run.call_args.args[1])

    def test_not_measured_corpus_with_counts_fails_check(self) -> None:
        rep = build_coverage_report(ROOT_DIR)
        rep["corpora"]["con_leche_h3_benchmark"] = {
            "measurement_source": "not_measured",
            "reason": "test",
            "total_declarations": 14415,
        }
        chk = check_coverage_report(ROOT_DIR, rep)
        self.assertFalse(chk["ok"])
        self.assertTrue(any("con_leche_h3_benchmark" in e and "counts" in e for e in chk["errors"]))

    def test_detects_corrupted_corpus_total(self) -> None:
        rep = build_coverage_report(ROOT_DIR)
        rep["corpora"]["std_init_and_c2"]["rejected"] += 3
        chk = check_coverage_report(ROOT_DIR, rep)
        self.assertFalse(chk["ok"])
        self.assertTrue(any("std_init_and_c2" in e for e in chk["errors"]))

    def test_detects_bridge_digest_drift(self) -> None:
        import shutil

        with tempfile.TemporaryDirectory(prefix="lcnf-cov-") as tmp:
            root = Path(tmp)
            for rel in TRACKED_BRIDGE_FILES:
                src = ROOT_DIR / rel
                dst = root / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
            target = root / "lean/LeanNative/IR/Bridge.lean"
            target.write_text(target.read_text(encoding="utf-8") + "\n-- drift\n", encoding="utf-8")
            chk = check_coverage_report(root)
            self.assertFalse(chk["ok"])
            self.assertTrue(any("digest mismatch" in e for e in chk["errors"]))

    def test_executes_live_lean_lowerer_on_corpora(self) -> None:
        live = execute_live_lean_audit(ROOT_DIR)
        self.assertTrue(live["executed"], live)
        self.assertEqual(live["toolchain"], PINNED_TOOLCHAIN)
        for cname in ("std_init_and_c2", "c1_corpus"):
            corp = live[cname]
            self.assertGreater(corp["total_declarations"], 0, cname)
            self.assertEqual(
                corp["total_declarations"],
                corp["proved"] + corp["lowered_unproved"] + corp["rejected"],
                cname,
            )

    def test_con_leche_tree_is_discovered_where_the_bridge_builds_it(self) -> None:
        import unittest.mock as mock

        saved = os.environ.pop(CON_LECHE_OLEANS_ENV, None)
        try:
            with tempfile.TemporaryDirectory(prefix="cl-root-") as tmp:
                root = Path(tmp)
                self.assertIsNone(_con_leche_olean_root(root))
                lib = (
                    root / "verification" / "con-leche-bridge" / ".lake" / "packages"
                    / "con-leche" / ".lake" / "build" / "lib" / "lean"
                )
                lib.mkdir(parents=True)
                (lib / ".git").mkdir()  # stand-in for the checkout root marker
                self.assertEqual(_con_leche_olean_root(root), lib)
                # The env var overrides the default when both exist.
                other = root / "other"
                other.mkdir()
                os.environ[CON_LECHE_OLEANS_ENV] = str(other)
                self.assertEqual(_con_leche_olean_root(root), other)
                del os.environ[CON_LECHE_OLEANS_ENV]
                # An explicitly named path that does not exist means "no tree", not
                # a silent fallback to some other checkout.
                os.environ[CON_LECHE_OLEANS_ENV] = str(root / "gone")
                self.assertIsNone(_con_leche_olean_root(root))
        finally:
            os.environ.pop(CON_LECHE_OLEANS_ENV, None)
            if saved is not None:
                os.environ[CON_LECHE_OLEANS_ENV] = saved

    def test_cold_tree_builds_the_lean_library_once(self) -> None:
        # A clean CI checkout has no lean/.lake; the script must build what it imports.
        import unittest.mock as mock

        with tempfile.TemporaryDirectory(prefix="cold-lean-") as tmp:
            lean = Path(tmp) / "lean"
            lean.mkdir()
            with mock.patch.object(sys.modules[__name__], "subprocess") as sp:
                sp.run.return_value = mock.Mock(returncode=0, stdout="", stderr="")
                _ensure_lean_build(Path(tmp))
                self.assertEqual(sp.run.call_count, 1)
                self.assertEqual(sp.run.call_args.args[0], ["lake", "build", "LeanNative.IR.Bridge"])
                # A warm tree with the imported olean present is left alone.
                bridge = lean / ".lake" / "build" / "lib" / "lean" / "LeanNative" / "IR" / "Bridge.olean"
                bridge.parent.mkdir(parents=True)
                bridge.write_bytes(b"")
                _ensure_lean_build(Path(tmp))
                self.assertEqual(sp.run.call_count, 1)

    def test_detects_live_execution_count_mismatch(self) -> None:
        rep = build_coverage_report(ROOT_DIR)
        rep["corpora"]["c1_corpus"]["proved"] -= 1
        rep["corpora"]["c1_corpus"]["lowered_unproved"] += 1
        chk = check_coverage_report(ROOT_DIR, rep, verify_live=True)
        self.assertFalse(chk["ok"])
        self.assertTrue(any("live execution mismatch" in e for e in chk["errors"]))

    def test_never_classifies_more_than_six_join_points_without_running_lowerer(self) -> None:
        # Point 1: declarations with >6 join points must never skip the lowerer and be
        # classified as proved/rejected by a module-name heuristic. Either the lowerer
        # runs on them or they are reported in their own `not_evaluated` class.
        lean_dir = ROOT_DIR / "lean"
        _ensure_lean_build(ROOT_DIR)
        env = _lean_env()
        # A declaration in a `batch_*` module with >6 join points that takes a String
        # literal (which the real lowerer rejects). Under the old `jps > 6` shortcut
        # on `batch_*`, this is misclassified as `proved` without running the lowerer!
        bad_many_jps = (
            "namespace batch_99\n"
            "@[export batch_99_bad]\n"
            "def bad_many_jps (x : UInt64) : String :=\n"
            "  let j1 := if x == 1 then 10 else 11\n"
            "  let j2 := if x == 2 then j1 + 1 else j1 + 2\n"
            "  let j3 := if x == 3 then j2 + 1 else j2 + 2\n"
            "  let j4 := if x == 4 then j3 + 1 else j3 + 2\n"
            "  let j5 := if x == 5 then j4 + 1 else j4 + 2\n"
            "  let j6 := if x == 6 then j5 + 1 else j5 + 2\n"
            "  let j7 := if x == 7 then j6 + 1 else j6 + 2\n"
            '  if j7 == 0 then "zero" else "nonzero"\n'
            "end batch_99\n"
        )
        with tempfile.TemporaryDirectory(prefix="lcnf-jp6-") as tmp:
            root = Path(tmp)
            lf = root / "batch_99.lean"
            lf.write_text(bad_many_jps, encoding="utf-8")
            subprocess.run(
                ["lean", f"--root={root}", "-o", str(root / "batch_99.olean"), str(lf)],
                cwd=str(lean_dir),
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )
            counts = _run_audit_driver(
                ROOT_DIR, _lean_audit_driver_for_modules(["batch_99"]), [str(root)]
            )
        self.assertEqual(counts[1], 0, f"unlowerable batch_99 decl with >6 join points was counted as proved: {counts}")
        self.assertGreaterEqual(counts[3], 1, f"expected rejected >= 1 from real lowerer: {counts}")
        self.assertNotIn('startsWith "batch_"', _LEAN_AUDIT_DRIVER_HEAD)
        self.assertNotIn("jps > 6", _LEAN_AUDIT_DRIVER_HEAD)

    def test_check_is_a_gate_against_committed_results_file(self) -> None:
        # Point 2: `--check` must compare the live measurement against the committed
        # `scripts/lcnf_coverage_results.json` written by `--write-results`, failing
        # with the corpus name and both sets of counts when they differ, and reporting
        # unmeasured corpora (con-leche in CI) as skipped while ignoring unknown
        # external Batteries.
        results_path = ROOT_DIR / "scripts" / "lcnf_coverage_results.json"
        self.assertTrue(results_path.is_file(), f"missing committed baseline {results_path}")
        baseline = json.loads(results_path.read_text(encoding="utf-8"))
        self.assertEqual(baseline.get("toolchain"), PINNED_TOOLCHAIN)
        self.assertTrue(baseline.get("measured_source_commit"))
        self.assertNotIn("con_leche_h3_benchmark", baseline.get("corpora", {}))

        rep = build_coverage_report(ROOT_DIR)
        chk_ok = check_coverage_report(ROOT_DIR, rep, results=baseline)
        self.assertTrue(chk_ok["ok"], chk_ok["errors"])
        self.assertIn("con_leche_h3_benchmark", chk_ok.get("skipped_corpora", []))

        drifted = json.loads(json.dumps(baseline))
        first_corpus = next(iter(drifted["corpora"]))
        drifted["corpora"][first_corpus]["proved"] += 1
        drifted["corpora"][first_corpus]["rejected"] -= 1
        chk_bad = check_coverage_report(ROOT_DIR, rep, results=drifted)
        self.assertFalse(chk_bad["ok"])
        self.assertTrue(
            any(first_corpus in e and "proved=" in e for e in chk_bad["errors"]),
            chk_bad["errors"],
        )

    # ------------------------------------------------------------------
    # H1.0a-V (split V): nested baseline validation. `--check` must gate
    # every defined measured field at every nesting level of
    # scripts/lcnf_coverage_results.json, not only the top-level corpus
    # fields, and the file itself must fail closed on invalid sums, wrong
    # types, and dishonest not_measured stubs.
    # ------------------------------------------------------------------

    def _v_fake_live_report(self) -> dict[str, Any]:
        # Live-report corpora shaped like build_coverage_report output and
        # derived FROM the committed baseline so top-level fields agree by
        # construction. Mock fixture: no Lean execution is involved here.
        results_path = ROOT_DIR / "scripts" / "lcnf_coverage_results.json"
        baseline = json.loads(results_path.read_text(encoding="utf-8"))
        corpora: dict[str, Any] = {}
        for cname, entry in baseline["corpora"].items():
            corp: dict[str, Any] = {"measurement_source": "live_invocation"}
            corp.update({f: entry[f] for f in RESULT_FIELDS if f in entry})
            if "rejected_not_lowered_reason" in entry:
                corp["rejected_not_lowered_reason"] = entry["rejected_not_lowered_reason"]
            if "subcorpora" in entry:
                corp["subcorpora"] = json.loads(json.dumps(entry["subcorpora"]))
            corpora[cname] = corp
        corpora["external_batteries"] = {"status": "unknown", "reason": "test unknown corpus"}
        corpora["con_leche_h3_benchmark"] = {
            "measurement_source": "not_measured",
            "reason": "no prebuilt pinned con-leche tree (test fixture)",
        }
        return {
            "bridge_source_digests": {},
            "lcnf_constructor_matrix": {
                "rows": [],
                "summary": {"total": 0, "proved": 0, "lowered_unproved": 0, "rejected": 0},
            },
            "corpora": corpora,
        }

    def _v_committed_baseline(self) -> dict[str, Any]:
        results_path = ROOT_DIR / "scripts" / "lcnf_coverage_results.json"
        return json.loads(results_path.read_text(encoding="utf-8"))

    def test_check_accepts_valid_unchanged_results_file(self) -> None:
        # Control: the committed baseline against a live report derived from
        # it must pass, and the honest skip bookkeeping is preserved.
        chk = check_coverage_report(ROOT_DIR, self._v_fake_live_report(), results=self._v_committed_baseline())
        self.assertTrue(chk["ok"], chk["errors"])
        self.assertIn("con_leche_h3_benchmark", chk["skipped_corpora"])
        self.assertNotIn("external_batteries", chk["skipped_corpora"])

    def test_check_rejects_arbitrary_nested_subcorpus_mutation(self) -> None:
        # The reproduced defect: mutating `subcorpora.std_init_data.proved`
        # 16 -> 17 in the committed file passed `--check` because only
        # top-level fields were compared. Every defined measured field at
        # every nesting level must be gated: mutate each nested field in
        # turn and demand a named failure.
        baseline = self._v_committed_baseline()
        rep = self._v_fake_live_report()
        nested = {
            cname: corp["subcorpora"]
            for cname, corp in baseline["corpora"].items()
            if isinstance(corp, dict) and "subcorpora" in corp
        }
        self.assertTrue(nested, "committed baseline has no nested subcorpora to test")
        for cname, subs in nested.items():
            for sname, sc in subs.items():
                for f in RESULT_FIELDS:
                    drifted = json.loads(json.dumps(baseline))
                    drifted["corpora"][cname]["subcorpora"][sname][f] += 1
                    chk = check_coverage_report(ROOT_DIR, rep, results=drifted)
                    self.assertFalse(
                        chk["ok"],
                        f"nested mutation {cname}.subcorpora.{sname}.{f} passed --check",
                    )
                    self.assertTrue(
                        any(sname in e and f in e for e in chk["errors"]),
                        f"no named error for {cname}.subcorpora.{sname}.{f}: {chk['errors']}",
                    )
                if "rejected_not_lowered_reason" in sc:
                    drifted = json.loads(json.dumps(baseline))
                    drifted["corpora"][cname]["subcorpora"][sname]["rejected_not_lowered_reason"] = "drifted_reason"
                    chk = check_coverage_report(ROOT_DIR, rep, results=drifted)
                    self.assertFalse(
                        chk["ok"],
                        f"nested reason mutation {cname}.subcorpora.{sname} passed --check",
                    )
                    self.assertTrue(
                        any(
                            sname in e and "rejected_not_lowered_reason" in e for e in chk["errors"]
                        ),
                        f"no named error for {cname}.subcorpora.{sname}.rejected_not_lowered_reason: {chk['errors']}",
                    )

    def test_check_rejects_nested_drift_even_when_parent_sums_compensated(self) -> None:
        # Sharpest form of the defect: the file's internal sums stay valid and
        # every top-level field still matches the live report; only a nested
        # comparison can notice one declaration moved between subcorpora.
        baseline = self._v_committed_baseline()
        rep = self._v_fake_live_report()
        cname = "std_init_and_c2"
        self.assertIn(cname, baseline["corpora"])
        self.assertIn("subcorpora", baseline["corpora"][cname])
        drifted = json.loads(json.dumps(baseline))
        a, b = sorted(drifted["corpora"][cname]["subcorpora"])[:2]
        drifted["corpora"][cname]["subcorpora"][a]["proved"] += 1
        drifted["corpora"][cname]["subcorpora"][a]["lowered_unproved"] -= 1
        drifted["corpora"][cname]["subcorpora"][b]["proved"] -= 1
        drifted["corpora"][cname]["subcorpora"][b]["lowered_unproved"] += 1
        chk = check_coverage_report(ROOT_DIR, rep, results=drifted)
        self.assertFalse(chk["ok"], "sum-consistent nested drift passed --check")
        self.assertTrue(
            any("subcorpus" in e and a in e for e in chk["errors"]),
            chk["errors"],
        )
        self.assertTrue(
            any("subcorpus" in e and b in e for e in chk["errors"]),
            chk["errors"],
        )

    def test_check_rejects_missing_and_extra_subcorpora_in_results_file(self) -> None:
        baseline = self._v_committed_baseline()
        rep = self._v_fake_live_report()
        cname = next(c for c, corp in baseline["corpora"].items() if "subcorpora" in corp)
        subs = baseline["corpora"][cname]["subcorpora"]
        missing = json.loads(json.dumps(baseline))
        dropped = sorted(subs)[0]
        del missing["corpora"][cname]["subcorpora"][dropped]
        chk = check_coverage_report(ROOT_DIR, rep, results=missing)
        self.assertFalse(chk["ok"], "subcorpus missing from the results file passed --check")
        self.assertTrue(
            any(dropped in e and "missing" in e for e in chk["errors"]),
            chk["errors"],
        )
        extra = json.loads(json.dumps(baseline))
        extra["corpora"][cname]["subcorpora"]["surprise_corpus"] = json.loads(
            json.dumps(rep["corpora"][cname]["subcorpora"][sorted(subs)[0]])
        )
        chk_extra = check_coverage_report(ROOT_DIR, rep, results=extra)
        self.assertFalse(chk_extra["ok"], "extra subcorpus in the results file passed --check")
        self.assertTrue(
            any("surprise_corpus" in e for e in chk_extra["errors"]),
            chk_extra["errors"],
        )

    def test_results_file_validation_rejects_invalid_sums_types_and_schema(self) -> None:
        # The committed file itself must fail closed, independent of any live
        # comparison, on invalid sums, wrong types, and schema drift.
        baseline = self._v_committed_baseline()
        self.assertEqual(validate_results_document(baseline), [])

        top_sum = json.loads(json.dumps(baseline))
        top_sum["corpora"]["c1_corpus"]["total_declarations"] += 5
        errs = validate_results_document(top_sum)
        self.assertTrue(any("c1_corpus" in e and "sum" in e for e in errs), errs)

        nested_sum = json.loads(json.dumps(baseline))
        nested_sum["corpora"]["std_init_and_c2"]["subcorpora"]["std_init_data"]["total_declarations"] += 5
        errs = validate_results_document(nested_sum)
        self.assertTrue(any("subcorpora" in e and "sums to" in e for e in errs), errs)

        missing_field = json.loads(json.dumps(baseline))
        del missing_field["corpora"]["c1_corpus"]["proved"]
        errs = validate_results_document(missing_field)
        self.assertTrue(any("c1_corpus" in e and "proved" in e and "missing" in e for e in errs), errs)

        for bad in ("782", 782.0, True):
            wrong_type = json.loads(json.dumps(baseline))
            wrong_type["corpora"]["c1_corpus"]["proved"] = bad
            errs = validate_results_document(wrong_type)
            self.assertTrue(
                any("c1_corpus" in e and "integer" in e for e in errs),
                f"type {type(bad).__name__} not rejected: {errs}",
            )

        non_dict = json.loads(json.dumps(baseline))
        non_dict["corpora"]["c1_corpus"] = 42
        errs = validate_results_document(non_dict)
        self.assertTrue(errs)

        bad_subs = json.loads(json.dumps(baseline))
        bad_subs["corpora"]["std_init_and_c2"]["subcorpora"] = ["std_init_data"]
        errs = validate_results_document(bad_subs)
        self.assertTrue(any("subcorpora" in e for e in errs), errs)

        schema = json.loads(json.dumps(baseline))
        schema["schemaVersion"] = "v0"
        errs = validate_results_document(schema)
        self.assertTrue(any("schemaVersion" in e for e in errs), errs)

    def test_check_fail_closed_on_malformed_results_file(self) -> None:
        # `--check` must return named errors for a malformed file, never crash.
        rep = self._v_fake_live_report()
        for label, mutate in (
            ("non-dict corpus entry", lambda d: d["corpora"].update({"c1_corpus": 42})),
            (
                "subcorpora list",
                lambda d: d["corpora"]["std_init_and_c2"].update({"subcorpora": ["std_init_data"]}),
            ),
        ):
            drifted = json.loads(json.dumps(self._v_committed_baseline()))
            mutate(drifted)
            chk = check_coverage_report(ROOT_DIR, rep, results=drifted)
            self.assertFalse(chk["ok"], label)
            self.assertTrue(chk["errors"], label)

    def test_results_file_not_measured_stub_is_honest(self) -> None:
        # An explicit `not_measured` entry in the results file is honest only
        # with a reason and no counts, and a live-measured corpus whose
        # baseline is such a stub must fail closed instead of comparing
        # nothing.
        baseline = self._v_committed_baseline()
        rep = self._v_fake_live_report()

        honest = json.loads(json.dumps(baseline))
        honest["corpora"]["con_leche_h3_benchmark"] = {
            "measurement_source": "not_measured",
            "reason": "tree absent",
        }
        self.assertEqual(validate_results_document(honest), [])

        with_counts = json.loads(json.dumps(baseline))
        with_counts["corpora"]["con_leche_h3_benchmark"] = {
            "measurement_source": "not_measured",
            "reason": "x",
            "total_declarations": 5,
        }
        errs = validate_results_document(with_counts)
        self.assertTrue(any("counts" in e for e in errs), errs)

        no_reason = json.loads(json.dumps(baseline))
        no_reason["corpora"]["con_leche_h3_benchmark"] = {"measurement_source": "not_measured"}
        errs = validate_results_document(no_reason)
        self.assertTrue(any("reason" in e for e in errs), errs)

        stubbed = json.loads(json.dumps(baseline))
        stubbed["corpora"]["c1_corpus"] = {"measurement_source": "not_measured", "reason": "stub"}
        chk = check_coverage_report(ROOT_DIR, rep, results=stubbed)
        self.assertFalse(chk["ok"], "live-measured corpus with not_measured baseline stub passed --check")
        self.assertTrue(any("c1_corpus" in e for e in chk["errors"]), chk["errors"])

    def test_check_gate_covers_nested_subcorpora_with_live_report(self) -> None:
        # End-to-end with the real live measurement: the DeepSeek repro (a
        # nested `proved` mutation of the committed baseline) must fail
        # `--check` against the true live report, naming the nested path,
        # while the pristine file keeps passing.
        baseline = self._v_committed_baseline()
        rep = build_coverage_report(ROOT_DIR)
        chk_ok = check_coverage_report(ROOT_DIR, rep, results=baseline)
        self.assertTrue(chk_ok["ok"], chk_ok["errors"])
        drifted = json.loads(json.dumps(baseline))
        subs = drifted["corpora"]["std_init_and_c2"]["subcorpora"]
        target = next(name for name, sc in subs.items() if sc.get("proved", 0) > 0)
        subs[target]["proved"] += 1
        chk_bad = check_coverage_report(ROOT_DIR, rep, results=drifted)
        self.assertFalse(chk_bad["ok"], "nested baseline drift passed the live gate")
        self.assertTrue(
            any("subcorpus" in e and target in e and "proved" in e for e in chk_bad["errors"]),
            chk_bad["errors"],
        )

    def _nested_leaf_like(self, entry: dict[str, Any]) -> dict[str, Any]:
        leaf = {f: entry[f] for f in RESULT_FIELDS}
        leaf["rejected_not_lowered_reason"] = entry["rejected_not_lowered_reason"]
        return leaf

    def test_rejects_unsupported_deeper_subcorpora_in_baseline(self) -> None:
        # H1.0a-V2 defect 1: only one nested level was compared, so a fabricated
        # deeper subcorpus whose counts exactly sum to its parent passed both the
        # results-file validator and `--check`. Deeper nesting is not a supported
        # schema; it must fail closed instead of being silently ignored.
        baseline = self._v_committed_baseline()
        rep = self._v_fake_live_report()
        cname = "std_init_and_c2"
        parent = "std_init_data"
        entry = baseline["corpora"][cname]["subcorpora"][parent]
        entry["subcorpora"] = {"fabricated_leaf": self._nested_leaf_like(entry)}

        errs = validate_results_document(baseline)
        self.assertTrue(
            any(parent in e and "subcorpora" in e and "depth" in e.lower() for e in errs),
            f"deeper subcorpus accepted by results validator: {errs}",
        )
        chk = check_coverage_report(ROOT_DIR, rep, results=baseline)
        self.assertFalse(chk["ok"], "fabricated deeper subcorpus passed --check")
        self.assertTrue(
            any(parent in e and "subcorpora" in e for e in chk["errors"]),
            chk["errors"],
        )

    def test_rejects_unsupported_deeper_subcorpora_in_live_report(self) -> None:
        # A live report must not be able to smuggle an unsupported deeper level
        # past comparison either.
        rep = self._v_fake_live_report()
        parent = "std_init_data"
        entry = rep["corpora"]["std_init_and_c2"]["subcorpora"][parent]
        entry["subcorpora"] = {"fabricated_leaf": self._nested_leaf_like(entry)}
        chk = check_coverage_report(ROOT_DIR, rep, results=self._v_committed_baseline())
        self.assertFalse(chk["ok"], "live deeper subcorpus passed --check")
        self.assertTrue(
            any(parent in e and "subcorpora" in e for e in chk["errors"]),
            chk["errors"],
        )

    def test_nested_missing_extra_type_and_count_fail_closed(self) -> None:
        # Adversarial nested shapes: missing field, extra fabricated depth, wrong
        # type, and a count that breaks the parent sum must each yield a named
        # error, never a silent pass.
        baseline = self._v_committed_baseline()
        cname = "std_init_and_c2"
        parent = "std_init_data"
        mutations: list[tuple[str, dict[str, Any]]] = []

        missing = json.loads(json.dumps(baseline))
        del missing["corpora"][cname]["subcorpora"][parent]["proved"]
        mutations.append(("missing", missing))

        extra = json.loads(json.dumps(baseline))
        entry = extra["corpora"][cname]["subcorpora"][parent]
        entry["subcorpora"] = {"fabricated_leaf": self._nested_leaf_like(entry)}
        mutations.append(("extra-depth", extra))

        wrong_type = json.loads(json.dumps(baseline))
        wrong_type["corpora"][cname]["subcorpora"][parent]["proved"] = "16"
        mutations.append(("type", wrong_type))

        bad_count = json.loads(json.dumps(baseline))
        bad_count["corpora"][cname]["subcorpora"][parent]["total_declarations"] += 1
        mutations.append(("count", bad_count))

        for label, doc in mutations:
            errs = validate_results_document(doc)
            self.assertTrue(errs, f"nested {label} mutation passed results validation")

    def test_measured_baseline_corpus_cannot_be_skipped_as_live_not_measured(self) -> None:
        # H1.0a-V2 defect 2: a baseline entry with measured counts must fail closed
        # when the live report says `not_measured`; it must not be recorded as an
        # honest skip with nothing compared.
        baseline = self._v_committed_baseline()
        rep = self._v_fake_live_report()
        rep["corpora"]["c1_corpus"] = {
            "measurement_source": "not_measured",
            "reason": "test: could not measure live",
        }
        chk = check_coverage_report(ROOT_DIR, rep, results=baseline)
        self.assertFalse(chk["ok"], "measured baseline with live not_measured passed --check")
        self.assertTrue(
            any("c1_corpus" in e and "not_measured" in e for e in chk["errors"]),
            chk["errors"],
        )
        self.assertNotIn("c1_corpus", chk["skipped_corpora"])

    def test_baseline_not_measured_stub_still_skips_when_live_not_measured(self) -> None:
        # Preserve intentionally unmeasured external corpora: an honest
        # `not_measured` baseline stub matching a live `not_measured` report is
        # still a skip, not an error.
        baseline = self._v_committed_baseline()
        baseline["corpora"]["con_leche_h3_benchmark"] = {
            "measurement_source": "not_measured",
            "reason": "external corpus intentionally absent",
        }
        rep = self._v_fake_live_report()
        chk = check_coverage_report(ROOT_DIR, rep, results=baseline)
        self.assertTrue(chk["ok"], chk["errors"])
        self.assertIn("con_leche_h3_benchmark", chk["skipped_corpora"])

    # ------------------------------------------------------------------
    # H1.0a-S (split S): honest proof classification and fail-closed
    # measurement (DeepSeek soundness findings against the audit driver;
    # same two paths as H1.0a-V, after V).
    # ------------------------------------------------------------------

    def test_cross_module_user_call_is_vacuous_not_rejected(self) -> None:
        # Counterexample (real lowerer, two compiled modules): a declaration in
        # one measured module calling a user function declared in another
        # measured module. The per-module localSet misses the cross-module
        # callee, so the real lowerer fails it as an unsupported call and the
        # driver counts it `rejected`, while the honest classification for a
        # call into a measured corpus declaration is a vacuous local call
        # (`lowered_unproved`) — eval `unsupportedCall` makes the pinned
        # simulation vacuous exactly like the same-module helper case.
        lean_dir = ROOT_DIR / "lean"
        _ensure_lean_build(ROOT_DIR)
        env = _lean_env()
        with tempfile.TemporaryDirectory(prefix="lcnf-xmod-") as tmp:
            root = Path(tmp)
            (root / "SAux.lean").write_text(
                "namespace SAux\n"
                "@[export sa_one]\n"
                "def sa_one (x : UInt64) : UInt64 := x + 1\n"
                "end SAux\n",
                encoding="utf-8",
            )
            (root / "SCaller.lean").write_text(
                "import SAux\n"
                "namespace SCaller\n"
                "@[export sc_two]\n"
                "def sc_two (x : UInt64) : UInt64 := SAux.sa_one x + 1\n"
                "end SCaller\n",
                encoding="utf-8",
            )
            cenv = dict(env)
            cenv["LEAN_PATH"] = str(root)
            for name in ("SAux", "SCaller"):
                subprocess.run(
                    ["lean", f"--root={root}", "-o", str(root / f"{name}.olean"), str(root / f"{name}.lean")],
                    cwd=str(lean_dir),
                    env=cenv,
                    check=True,
                    capture_output=True,
                    text=True,
                )
            counts = _run_audit_driver(
                ROOT_DIR, _lean_audit_driver_for_modules(["SAux", "SCaller"]), [str(root)]
            )
        tot, prv, unp, rej, cyc = counts
        self.assertEqual(tot, 2, counts)
        self.assertEqual(prv, 1, counts)  # the callee itself lowers and proves
        self.assertEqual(unp, 1, counts)  # the cross-module caller is a vacuous local call
        self.assertEqual(rej, 0, counts)  # a corpus-local call is not an unsupported construct
        self.assertEqual(cyc, 0, counts)

    def test_audit_driver_never_silently_drops_a_module(self) -> None:
        # A module whose IR conversion fails must fail the audit loudly (never
        # `return #[]`), and a module missing from the imported environment
        # must never contribute a silent zero: both would understate the
        # published counts as if the declarations had been measured.
        self.assertNotIn(".error _ => return #[]", _LEAN_AUDIT_DRIVER_HEAD)
        self.assertIn("not found in the imported environment", _LEAN_AUDIT_DRIVER_HEAD)

    def test_corpus_scope_does_not_claim_aux_expansion_it_never_performs(self) -> None:
        # The scope text claimed compiler-generated `_closed` helpers were
        # "expanded by `expandCompilerAuxDecls`", but the measurement filters
        # compiler-generated auxiliary declarations out and never calls that
        # function (only the library's `ingestModuleDeclsWith` does). A scope
        # claim the measurement does not perform is dishonest output.
        self.assertNotIn("expandCompilerAuxDecls", CORPUS_SCOPES["c1_corpus"])

    def test_std_init_and_c2_renamed_and_external_batteries_separate_unknown(self) -> None:
        # Point 3: the corpus holding Init/Std + C2 is named `std_init_and_c2` (not
        # a misleading Batteries name), and external Batteries is its own top-level
        # corpus entry with status `unknown`.
        self.assertIn("std_init_and_c2", CORPUS_SCOPES)
        self.assertEqual(set(CORPUS_SCOPES.keys()), {"std_init_and_c2", "c1_corpus"})
        rep = build_coverage_report(ROOT_DIR)
        corpora = rep["corpora"]
        self.assertIn("std_init_and_c2", corpora)
        self.assertIn("external_batteries", corpora)
        ext = corpora["external_batteries"]
        self.assertEqual(ext.get("status"), "unknown")
        self.assertTrue(ext.get("reason"))
        for field in RESULT_FIELDS:
            self.assertNotIn(field, ext)

    def test_con_leche_reports_natoppins_exclusion_and_rejects_partial_tree(self) -> None:
        # Point 4: con-leche output must state the NatOpPins exclusion and its reason
        # with the module count, record how many modules were found against how many
        # the pinned revision has, and report `not_measured` with a reason when they
        # differ.
        import unittest.mock as mock

        with tempfile.TemporaryDirectory(prefix="cl-partial-") as tmp:
            root = Path(tmp)
            (root / ".git").mkdir()
            lib = root / "lib" / "lean" / "ConLeche" / "Kernel"
            lib.mkdir(parents=True)
            for name in ("Name", "Expr", "NatOpPins"):
                (lib / f"{name}.olean").write_bytes(b"")
            saved = os.environ.get("TURBO_CON_LECHE_OLEANS")
            os.environ["TURBO_CON_LECHE_OLEANS"] = str(root / "lib" / "lean")
            try:
                with mock.patch.object(
                    sys.modules[__name__], "_run_audit_driver", return_value=(100, 7, 11, 82, 4)
                ) as run, mock.patch.object(
                    sys.modules[__name__], "_git_head", return_value=PINNED_CON_LECHE_REV
                ):
                    partial_corp = measure_con_leche(ROOT_DIR)
            finally:
                if saved is None:
                    os.environ.pop("TURBO_CON_LECHE_OLEANS", None)
                else:
                    os.environ["TURBO_CON_LECHE_OLEANS"] = saved
        self.assertEqual(partial_corp["measurement_source"], "not_measured")
        self.assertEqual(partial_corp.get("module_count"), 2)
        self.assertEqual(partial_corp.get("expected_module_count"), 102)
        self.assertIn("NatOpPins", partial_corp.get("reason", ""))
        self.assertIn("exclusion", partial_corp)
        self.assertIn("ConLeche.Kernel.NatOpPins", partial_corp["exclusion"]["excluded_modules"])
        self.assertTrue(partial_corp["exclusion"]["reason"])
        for field in RESULT_FIELDS:
            self.assertNotIn(field, partial_corp)
        run.assert_not_called()

    def test_fixture_corpus_counts_change_when_declaration_added_and_no_hardcoded_totals(self) -> None:
        # Point 5: a small fixture corpus is measured live, changed by adding a
        # declaration the lowerer rejects, and the counts are seen to change; test
        # methods must not hardcode historical corpus totals (1805, 902, 1704, 782).
        import inspect

        src_live = inspect.getsource(TestLcnfCoverage.test_live_coverage_report_and_invariants)
        src_exec = inspect.getsource(TestLcnfCoverage.test_executes_live_lean_lowerer_on_corpora)
        for num in ("1805", "1704", "902", "782"):
            self.assertNotIn(num, src_live + src_exec, f"hardcoded historical total {num} remains in test")

        base = measure_fixture_corpus(
            ROOT_DIR,
            "@[export fix_ok]\ndef fix_ok (x : UInt64) : UInt64 := x + 1\n",
        )
        grown = measure_fixture_corpus(
            ROOT_DIR,
            "@[export fix_ok]\ndef fix_ok (x : UInt64) : UInt64 := x + 1\n"
            '@[export fix_bad]\ndef fix_bad (x : UInt64) : String := if x == 0 then "a" else "b"\n',
        )
        self.assertGreater(grown["total_declarations"], base["total_declarations"])
        self.assertGreater(grown["rejected"], base["rejected"])
        self.assertEqual(grown["proved"], base["proved"])

    def test_con_leche_unmapped_pinned_revision_is_named_error(self) -> None:
        # Round-2 Point 1 (case 1): pinned con-leche revision missing from
        # CON_LECHE_PINNED_MODULE_COUNTS -> named error and non-zero exit.
        import unittest.mock as mock

        m = sys.modules[__name__]
        self.assertIn(PINNED_CON_LECHE_REV, getattr(m, "CON_LECHE_PINNED_MODULE_COUNTS", {}))
        _CON_LECHE_CACHE.clear()
        with mock.patch.object(m, "PINNED_CON_LECHE_REV", "deadbeef" * 5):
            unmapped = measure_con_leche(ROOT_DIR)
            chk_unmapped = check_coverage_report(
                ROOT_DIR,
                {**build_coverage_report(ROOT_DIR), "corpora": {"con_leche_h3_benchmark": unmapped}},
            )
        self.assertEqual(unmapped.get("measurement_source"), "error")
        self.assertEqual(unmapped.get("error_code"), "unmapped_pinned_con_leche_revision")
        self.assertFalse(chk_unmapped["ok"])
        self.assertTrue(
            any("unmapped_pinned_con_leche_revision" in e for e in chk_unmapped["errors"]),
            chk_unmapped["errors"],
        )

    def test_con_leche_full_tree_module_count_mismatch_is_named_error(self) -> None:
        # Round-2 Point 1 (case 2): a full built tree at the pinned revision whose
        # module count differs from CON_LECHE_PINNED_MODULE_COUNTS[rev] -> named error, non-zero exit.
        import unittest.mock as mock

        m = sys.modules[__name__]
        self.assertTrue(hasattr(m, "CON_LECHE_PINNED_MODULE_COUNTS"))
        with tempfile.TemporaryDirectory(prefix="cl-full-mismatch-") as tmp:
            root = Path(tmp)
            (root / ".git").mkdir()
            build_dir = root / ".lake" / "build"
            lib = build_dir / "lib" / "lean"
            (lib / "ConLeche" / "Kernel").mkdir(parents=True)
            for name in ("Name", "Expr", "NatOpPins"):
                (lib / "ConLeche" / "Kernel" / f"{name}.olean").write_bytes(b"")
            (build_dir / "bin").mkdir(parents=True)
            (build_dir / "bin" / "con-leche").write_bytes(b"")
            saved = os.environ.get(CON_LECHE_OLEANS_ENV)
            os.environ[CON_LECHE_OLEANS_ENV] = str(lib)
            try:
                _CON_LECHE_CACHE.clear()
                with mock.patch.object(
                    m, "_git_head", return_value=PINNED_CON_LECHE_REV
                ), mock.patch.dict(m.CON_LECHE_PINNED_MODULE_COUNTS, {PINNED_CON_LECHE_REV: 3}):
                    full_mismatch = measure_con_leche(ROOT_DIR)
            finally:
                if saved is None:
                    os.environ.pop(CON_LECHE_OLEANS_ENV, None)
                else:
                    os.environ[CON_LECHE_OLEANS_ENV] = saved
        self.assertEqual(full_mismatch.get("measurement_source"), "error")
        self.assertEqual(full_mismatch.get("error_code"), "con_leche_module_count_mismatch")
        chk_mismatch = check_coverage_report(
            ROOT_DIR,
            {**build_coverage_report(ROOT_DIR), "corpora": {"con_leche_h3_benchmark": full_mismatch}},
        )
        self.assertFalse(chk_mismatch["ok"])
        self.assertTrue(
            any("con_leche_module_count_mismatch" in e for e in chk_mismatch["errors"]),
            chk_mismatch["errors"],
        )

    def test_con_leche_absent_or_partial_tree_stays_not_measured(self) -> None:
        # Round-2 Point 1 (case 3): an absent or partial tree stays `not_measured` (exit 0)
        # while CON_LECHE_PINNED_MODULE_COUNTS maps the pinned revision.
        import unittest.mock as mock

        m = sys.modules[__name__]
        self.assertIn(PINNED_CON_LECHE_REV, getattr(m, "CON_LECHE_PINNED_MODULE_COUNTS", {}))
        with tempfile.TemporaryDirectory(prefix="cl-absent-partial-") as tmp:
            root = Path(tmp)
            (root / ".git").mkdir()
            lib = root / ".lake" / "build" / "lib" / "lean"
            (lib / "ConLeche" / "Kernel").mkdir(parents=True)
            for name in ("Name", "Expr", "NatOpPins"):
                (lib / "ConLeche" / "Kernel" / f"{name}.olean").write_bytes(b"")
            saved = os.environ.get(CON_LECHE_OLEANS_ENV)
            try:
                os.environ[CON_LECHE_OLEANS_ENV] = str(lib)
                _CON_LECHE_CACHE.clear()
                with mock.patch.object(m, "_git_head", return_value=PINNED_CON_LECHE_REV):
                    partial = measure_con_leche(ROOT_DIR)
                os.environ[CON_LECHE_OLEANS_ENV] = str(root / "nonexistent")
                _CON_LECHE_CACHE.clear()
                absent = measure_con_leche(ROOT_DIR)
            finally:
                if saved is None:
                    os.environ.pop(CON_LECHE_OLEANS_ENV, None)
                else:
                    os.environ[CON_LECHE_OLEANS_ENV] = saved
        for res in (partial, absent):
            self.assertEqual(res.get("measurement_source"), "not_measured")
            chk = check_coverage_report(
                ROOT_DIR,
                {**build_coverage_report(ROOT_DIR), "corpora": {"con_leche_h3_benchmark": res}},
            )
            self.assertTrue(chk["ok"], chk["errors"])

    def test_results_file_records_measured_source_commit_and_documents_it(self) -> None:
        # Round-2 Point 2: `scripts/lcnf_coverage_results.json` records `measured_source_commit`
        # (not `commit` / `generating_commit`), states in the file and in `--help` that it is
        # the commit of the tree the measurement was taken from, and `--check` does not
        # require it to match `HEAD`.
        results_path = ROOT_DIR / "scripts" / "lcnf_coverage_results.json"
        doc = json.loads(results_path.read_text(encoding="utf-8"))
        self.assertIn("measured_source_commit", doc)
        self.assertNotIn("commit", doc)
        self.assertNotIn("generating_commit", doc)
        self.assertIn("tree the measurement was taken from", doc.get("measured_source_commit_note", ""))

        help_proc = subprocess.run(
            [sys.executable, str(Path(__file__).resolve()), "--help"],
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertIn("measured_source_commit", help_proc.stdout)
        self.assertIn("measurement was taken from", help_proc.stdout)

        rep = build_coverage_report(ROOT_DIR)
        other_commit_doc = json.loads(json.dumps(doc))
        other_commit_doc["measured_source_commit"] = "0123456789abcdef" * 2 + "01234567"
        chk = check_coverage_report(ROOT_DIR, rep, results=other_commit_doc)
        self.assertTrue(chk["ok"], chk["errors"])

    def test_rejected_not_lowered_mutual_cycle_reported_in_json_and_check_output(self) -> None:
        # Round-2 Point 3: declarations in mutual cycles stay counted in `rejected`,
        # and both JSON and `--check` output report per corpus how many of `rejected`
        # were not lowered (`rejected_not_lowered`) and why (`mutual_cycle`).
        mut = measure_fixture_corpus(
            ROOT_DIR,
            "mutual\n"
            "partial def ping (x : UInt64) : UInt64 := if x == 0 then 1 else pong (x - 1)\n"
            "partial def pong (x : UInt64) : UInt64 := if x == 0 then 2 else ping (x - 1)\n"
            "end\n"
            '@[export bad_str]\ndef bad_str (x : UInt64) : String := if x == 0 then "a" else "b"\n',
        )
        self.assertEqual(mut.get("rejected_not_lowered"), 2)
        self.assertEqual(mut.get("rejected_not_lowered_reason"), "mutual_cycle")
        self.assertGreaterEqual(mut["rejected"], 3)

        rep = build_coverage_report(ROOT_DIR)
        for cname in ("std_init_and_c2", "c1_corpus"):
            corp = rep["corpora"][cname]
            self.assertIn("rejected_not_lowered", corp)
            self.assertEqual(corp.get("rejected_not_lowered_reason"), "mutual_cycle")
            self.assertLessEqual(corp["rejected_not_lowered"], corp["rejected"])
        self.assertGreaterEqual(rep["corpora"]["c1_corpus"]["rejected_not_lowered"], 2)

        chk_proc = subprocess.run(
            [sys.executable, str(Path(__file__).resolve()), "--check"],
            capture_output=True,
            text=True,
            timeout=3600,
        )
        self.assertEqual(chk_proc.returncode, 0, chk_proc.stderr)
        self.assertIn("rejected_not_lowered", chk_proc.stdout)
        self.assertIn("mutual_cycle", chk_proc.stdout)



def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true", help="Emit full coverage report JSON to stdout")
    ap.add_argument(
        "--check",
        action="store_true",
        help=(
            "Verify bridge digests, symbols, and live lowerer counts against "
            "scripts/lcnf_coverage_results.json (`measured_source_commit` records the commit "
            "of the tree the measurement was taken from and is not compared to HEAD)"
        ),
    )
    ap.add_argument(
        "--write-results",
        action="store_true",
        help=(
            "Write the live measurement to scripts/lcnf_coverage_results.json, recording "
            "`measured_source_commit` as the commit of the tree the measurement was taken from"
        ),
    )
    ap.add_argument("--self-test", action="store_true", help="Run embedded unit tests")
    args = ap.parse_args()

    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(TestLcnfCoverage)
        res = unittest.TextTestRunner(verbosity=2).run(suite)
        return 0 if res.wasSuccessful() else 1

    if args.write_results and args.check:
        print("  [ERROR] --write-results and --check are mutually exclusive", file=sys.stderr)
        return 2

    chk = check_coverage_report(ROOT_DIR, require_results=args.check)
    if args.write_results:
        RESULTS_FILE.write_text(
            json.dumps(results_document(chk["report"], ROOT_DIR), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        print(f"[lcnf-coverage] wrote {RESULTS_FILE.relative_to(ROOT_DIR)}", file=sys.stderr)
        if not args.json:
            return 0 if chk["ok"] else 1

    if args.json or not args.check:
        out = dict(chk["report"])
        out["ok"] = chk["ok"]
        out["errors"] = chk["errors"]
        print(json.dumps(out, indent=2, sort_keys=True))
    else:
        ms = chk["report"]["lcnf_constructor_matrix"]["summary"]
        corpora = chk["report"]["corpora"]
        parts = [
            f"[lcnf-coverage] ok={chk['ok']} "
            f"matrix={ms['proved']}/{ms['total']} proved "
            f"({ms['lowered_unproved']} lowered_unproved, {ms['rejected']} rejected)"
        ]
        for label, cname in (
            ("std_init_and_c2", "std_init_and_c2"),
            ("c1", "c1_corpus"),
            ("con_leche", "con_leche_h3_benchmark"),
        ):
            corp = corpora.get(cname, {})
            if corp.get("measurement_source") == "live_invocation":
                parts.append(
                    f"{label}={corp['proved']}/{corp['total_declarations']} proved "
                    f"(+{corp['lowered_unproved']} vacuous_local_call, "
                    f"{corp['rejected']} rejected incl. "
                    f"rejected_not_lowered={corp['rejected_not_lowered']} "
                    f"[{corp['rejected_not_lowered_reason']}])"
                )
            elif corp.get("measurement_source") == "error":
                parts.append(f"{label}=error ({corp.get('error_code', 'error')})")
            else:
                parts.append(f"{label}=skipped (not measured)")
        print(" ".join(parts))
    if not chk["ok"]:
        for err in chk["errors"]:
            print(f"  [ERROR] {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
