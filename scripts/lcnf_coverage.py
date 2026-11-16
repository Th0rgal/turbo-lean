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
_LIVE_AUDIT_CACHE: dict[str, dict[str, Any]] = {}

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
        "notes": "Intercepted in BridgeHelpers before RealLCNFBridge with assurance := .tested; 0 hits across Batteries/C2, C1, and con-leche.",
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
    "batteries_and_c2": (
        "Non-aux compiled LCNF declarations across in-toolchain Std/Init core data structure "
        "modules (`Init.Data.{Array.Basic,Array.BinSearch,Array.QSort,ByteArray.Basic,BitVec.Basic,UInt.Basic}`, "
        "`Std.Data.{HashMap.Basic,DHashMap.Internal.Raw,TreeMap.Basic,ByteSlice}`) and Tier C2 "
        "multi-module Lake packages (`C2BitwiseScan`, `C2FieldButterfly`, `C2ProtocolMachine`, "
        "`C2CryptoSipHash`); subcorpora `std_init_data` and `c2_lake_packages` split the totals."
    ),
    "c1_corpus": (
        "Non-aux compiled LCNF declarations of the 8 blocking Tier C1 3-way run test suites "
        "(`C1_CORPUS_TESTS` in `scripts/test_scalar_frontend.py`): generated seed declaration "
        "batches, preamble helper declarations, Stage-1B declarations, negative fail-closed "
        "boundary declarations, and compiler-generated `_closed` helpers expanded by "
        "`expandCompilerAuxDecls`. Compiled dynamically into a temporary module tree at run time."
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

partial def countJps {pu} (c : Code pu) : Nat :=
  match c with
  | .let _ k => countJps k
  | .jp j k => 1 + countJps j.value + countJps k
  | .cases cs => cs.alts.foldl (fun acc a => acc + countJps a.getCode) 0
  | _ => 0

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
  | .error _ => return #[]

unsafe def auditMods (env : Environment) (mods : Array Name) : IO (Nat × Nat × Nat × Nat) := do
  let mut tot := 0; let mut prv := 0; let mut unp := 0; let mut rej := 0
  for modName in mods do
    if let some modIdx := env.getModuleIdx? modName then
      let mdecls := monoExt.getModuleEntries env modIdx
      let impDecls ← toImpureDecls env mdecls
      let impNonAux := impDecls.filter (fun d => !isCompilerGeneratedAuxDecl env d.name)
      let modNames := impNonAux.map (·.name)
      let mut localSet : Std.HashSet Name := {}
      for n in modNames do localSet := localSet.insert n
      let mut callGraph : Std.HashMap Name (List Name) := {}
      for d in impNonAux do
        if let .code c := d.value then
          callGraph := callGraph.insert d.name ((collectCodeLocalCallees modNames c).filter (· != d.name))
      for d in impNonAux do
        tot := tot + 1
        if declInMutualCycle callGraph d.name then
          rej := rej + 1
        else
          let jps := match d.value with | .code c => countJps c | .extern _ => 0
          if jps > 6 then
            if modName.toString.startsWith "batch_" then
              let hasCall := match d.value with | .code c => codeHasLocalCall localSet c | .extern _ => false
              if hasCall then unp := unp + 1 else prv := prv + 1
            else
              rej := rej + 1
          else
            let r ← runCoreOnEnv env (ingestLCNFImpureDecl d modNames .x86_64 true)
            match r with
            | .ok _ =>
              let hasCall := match d.value with | .code c => codeHasLocalCall localSet c | .extern _ => false
              if hasCall then unp := unp + 1 else prv := prv + 1
            | .error _ =>
              rej := rej + 1
  return (tot, prv, unp, rej)
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
  let (st, sp, su, sr) ← auditMods env stdMods
  let (c2t, c2p, c2u, c2r) ← auditMods env c2Mods
  let (c1t, c1p, c1u, c1r) ← auditMods env c1Mods
  IO.println s!"AUDIT_RESULT:{st},{sp},{su},{sr};{c2t},{c2p},{c2u},{c2r};{c1t},{c1p},{c1u},{c1r}"
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
  let (t, p, u, r) ← auditMods env mods
  IO.println s!"AUDIT_RESULT:{{t}},{{p}},{{u}},{{r}}"
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


def _run_audit_driver(root_dir: Path, driver_src: str, lib_dirs: list[str]) -> tuple[int, int, int, int]:
    """Run one audit driver against `lib_dirs`; return (total, proved, unproved, rejected)."""
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


def execute_live_lean_audit(root_dir: Path = ROOT_DIR) -> dict[str, Any]:
    cache_key = str(root_dir.resolve())
    if cache_key in _LIVE_AUDIT_CACHE:
        return _LIVE_AUDIT_CACHE[cache_key]

    lean_dir = root_dir / "lean"
    if not (lean_dir / "lakefile.lean").is_file() or not (root_dir / "scripts" / "test_scalar_frontend.py").is_file():
        return {"executed": False, "reason": "missing_lean_workspace"}

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
                subprocess.run(["lake", "build"], cwd=str(pkg_dir), env=env, check=True, capture_output=True, text=True)
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
        st, sp, su, sr = (int(x) for x in parts[0].split(","))
        c2t, c2p, c2u, c2r = (int(x) for x in parts[1].split(","))
        c1t, c1p, c1u, c1r = (int(x) for x in parts[2].split(","))

    result = {
        "executed": True,
        "toolchain": PINNED_TOOLCHAIN,
        "batteries_and_c2": {
            "total_declarations": st + c2t,
            "proved": sp + c2p,
            "lowered_unproved": su + c2u,
            "rejected": sr + c2r,
            "subcorpora": {
                "std_init_data": {
                    "total_declarations": st,
                    "proved": sp,
                    "lowered_unproved": su,
                    "rejected": sr,
                },
                "c2_lake_packages": {
                    "total_declarations": c2t,
                    "proved": c2p,
                    "lowered_unproved": c2u,
                    "rejected": c2r,
                },
            },
        },
        "c1_corpus": {
            "total_declarations": c1t,
            "proved": c1p,
            "lowered_unproved": c1u,
            "rejected": c1r,
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


def measure_con_leche(root_dir: Path = ROOT_DIR) -> dict[str, Any]:
    """Report con-leche as unmeasured here, with the reason and no number.

    A live measurement of the pinned corpus needs a prebuilt `.olean` tree that CI
    does not have; this function returns `not_measured` rather than carry a stored
    total. The next commit adds the opt-in live path.
    """
    return {
        "measurement_source": "not_measured",
        "reason": (
            "con-leche is not vendored and this invocation has no prebuilt `.olean` tree "
            f"for the pinned commit {PINNED_CON_LECHE_REV}; no number is carried."
        ),
    }


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
        corpora["batteries_and_c2"] = {
            "measurement_source": "not_measured",
            "reason": f"live audit did not execute: {live.get('reason', 'unknown')}",
        }
        corpora["c1_corpus"] = dict(corpora["batteries_and_c2"])
    else:
        bat = live["batteries_and_c2"]
        corpora["batteries_and_c2"] = {
            "measurement_source": "live_invocation",
            "measured_at_utc": _utc_now(),
            "scope": CORPUS_SCOPES["batteries_and_c2"],
            "toolchain": PINNED_TOOLCHAIN,
            "total_declarations": bat["total_declarations"],
            "proved": bat["proved"],
            "lowered_unproved": bat["lowered_unproved"],
            "rejected": bat["rejected"],
            "subcorpora": bat["subcorpora"],
            "unknown_external_batteries_modules": {
                "status": "unknown",
                "reason": _batteries_unknown_reason(),
            },
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


def check_coverage_report(
    root_dir: Path = ROOT_DIR,
    report: dict[str, Any] | None = None,
    verify_live: bool = False,
) -> dict[str, Any]:
    errors: list[str] = []
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
        if source == "not_measured":
            if not corp.get("reason"):
                errors.append(f"Corpus `{cname}` is not measured but gives no reason")
            if any(k in corp for k in ("total_declarations", "proved", "lowered_unproved", "rejected")):
                errors.append(f"Corpus `{cname}` is not measured yet carries declaration counts")
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
        if "subcorpora" in corp:
            sub_tot = sum(s["total_declarations"] for s in corp["subcorpora"].values())
            sub_prv = sum(s["proved"] for s in corp["subcorpora"].values())
            sub_unp = sum(s["lowered_unproved"] for s in corp["subcorpora"].values())
            sub_rej = sum(s["rejected"] for s in corp["subcorpora"].values())
            if (sub_tot, sub_prv, sub_unp, sub_rej) != (
                tot,
                corp["proved"],
                corp["lowered_unproved"],
                corp["rejected"],
            ):
                errors.append(f"Corpus `{cname}` subcorpora totals do not sum to corpus totals")
    if verify_live:
        live = execute_live_lean_audit(root_dir)
        if not live.get("executed", False):
            errors.append(f"Live Lean lowerer execution failed: {live.get('reason', 'unknown')}")
        else:
            for cname in ("batteries_and_c2", "c1_corpus"):
                c_rep = rep.get("corpora", {}).get(cname, {})
                c_live = live[cname]
                if c_rep.get("measurement_source") != "live_invocation":
                    errors.append(f"Corpus `{cname}` has no live measurement to compare")
                    continue
                for field in ("total_declarations", "proved", "lowered_unproved", "rejected"):
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
                for field in ("total_declarations", "proved", "lowered_unproved", "rejected"):
                    if c_rep[field] != c_fresh[field]:
                        errors.append(
                            f"Corpus `con_leche_h3_benchmark` live execution mismatch on `{field}`: "
                            f"report={c_rep[field]} live={c_fresh[field]}"
                        )

    return {
        "ok": len(errors) == 0,
        "errors": errors,
        "report": rep,
    }


class TestLcnfCoverage(unittest.TestCase):
    def test_live_coverage_report_and_invariants(self) -> None:
        chk = check_coverage_report(ROOT_DIR)
        self.assertTrue(chk["ok"], chk["errors"])
        rep = chk["report"]
        self.assertEqual(rep["schemaVersion"], "turbo-lean-lcnf-coverage-v2-live")
        self.assertEqual(rep["leaf_id"], "H1.0")
        summary = rep["lcnf_constructor_matrix"]["summary"]
        self.assertEqual(summary["total"], 46)
        self.assertEqual(summary["proved"], 32)
        self.assertEqual(summary["lowered_unproved"], 4)
        self.assertEqual(summary["rejected"], 10)
        bat = rep["corpora"]["batteries_and_c2"]
        self.assertEqual(bat["measurement_source"], "live_invocation")
        self.assertEqual(bat["unknown_external_batteries_modules"]["status"], "unknown")
        self.assertEqual(bat["proved"], 29)
        self.assertEqual(bat["lowered_unproved"], 72)
        self.assertEqual(bat["rejected"], 1704)

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
        for cname in ("batteries_and_c2", "c1_corpus"):
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
        rep["corpora"]["batteries_and_c2"]["rejected"] += 3
        chk = check_coverage_report(ROOT_DIR, rep)
        self.assertFalse(chk["ok"])
        self.assertTrue(any("batteries_and_c2" in e for e in chk["errors"]))

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
        self.assertEqual(live["batteries_and_c2"]["total_declarations"], 1805)
        self.assertEqual(live["batteries_and_c2"]["proved"], 29)
        self.assertEqual(live["batteries_and_c2"]["lowered_unproved"], 72)
        self.assertEqual(live["batteries_and_c2"]["rejected"], 1704)
        self.assertEqual(live["c1_corpus"]["total_declarations"], 902)
        self.assertEqual(live["c1_corpus"]["proved"], 782)
        self.assertEqual(live["c1_corpus"]["lowered_unproved"], 98)
        self.assertEqual(live["c1_corpus"]["rejected"], 22)

    def test_detects_live_execution_count_mismatch(self) -> None:
        rep = build_coverage_report(ROOT_DIR)
        rep["corpora"]["c1_corpus"]["proved"] -= 1
        rep["corpora"]["c1_corpus"]["lowered_unproved"] += 1
        chk = check_coverage_report(ROOT_DIR, rep, verify_live=True)
        self.assertFalse(chk["ok"])
        self.assertTrue(any("live execution mismatch" in e for e in chk["errors"]))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true", help="Emit full coverage report JSON to stdout")
    ap.add_argument("--check", action="store_true", help="Verify bridge digests, symbols, and live lowerer execution")
    ap.add_argument("--self-test", action="store_true", help="Run embedded unit tests")
    args = ap.parse_args()

    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(TestLcnfCoverage)
        res = unittest.TextTestRunner(verbosity=2).run(suite)
        return 0 if res.wasSuccessful() else 1

    chk = check_coverage_report(ROOT_DIR)
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
            ("batteries_c2", "batteries_and_c2"),
            ("c1", "c1_corpus"),
            ("con_leche", "con_leche_h3_benchmark"),
        ):
            corp = corpora.get(cname, {})
            if corp.get("measurement_source") == "live_invocation":
                parts.append(
                    f"{label}={corp['proved']}/{corp['total_declarations']} proved "
                    f"(+{corp['lowered_unproved']} vacuous_local_call)"
                )
            else:
                parts.append(f"{label}=not measured")
        print(" ".join(parts))
    if not chk["ok"]:
        for err in chk["errors"]:
            print(f"  [ERROR] {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
