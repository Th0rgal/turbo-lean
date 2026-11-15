#!/usr/bin/env python3
"""Horizon H1.0 Generated LCNF Coverage Matrix (`scripts/lcnf_coverage.py`).

Work-graph leaf **H1.0** (*RO*, `roadmap/HORIZONS.md` @ `b59eeef03fa9497bf700806136deeed36498dd71`):
- Outcome: Generated `LCNF` coverage matrix on `Batteries` and C1
- Owns: `scripts/lcnf_coverage.py`
- Needs: –
- Accept: CI job emits JSON (`python3 scripts/lcnf_coverage.py --json`)

Methodology & Honesty Rules:
- Every declaration count in `measured` corpora was obtained by executing the real Lean 4 LCNF
  pipeline (`Lean.Compiler.LCNF.toImpure` + `builtinPassManager.impurePasses` with `maxHeartbeats := 0`)
  and invoking `LeanNative.IR.ingestLCNFImpureDecl` (which delegates to
  `RealLCNFBridge.lowerRealLCNFDecl`) on each compiled declaration.
- No source-pattern heuristic is ever represented as executed lowering.
- As documented in `roadmap/HORIZONS.md` ("What the review found"), `lowerRealLCNFDecl` lowers a call
  to another local user function (`LetValue.fap`), but `RealLCNFSemantics.evalLetValue` returns
  `.error (.unsupportedCall fn.toString)` whenever `(ctx.findLocalCallee? fn).isSome`. Because
  `lowerRealLCNFDecl_sound` is a forward simulation gated on `evalRealLCNFDecl ... = .ok (v, hst')`,
  its conclusion is vacuous for any declaration that calls a local helper (`lowered_vacuous_local_call`,
  classified under `lowered_unproved` until rung **L2** adds a function environment to both semantics).
- Unmeasured modules (e.g. external `Batteries` modules outside the in-toolchain `Init.Data.*` /
  `Std.Data.*` and `verification/c2-lake-packages/*` `.olean` artifacts) are explicitly reported as
  `unknown` rather than extrapolated.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

ROOT_DIR = Path(__file__).resolve().parent.parent
PINNED_TOOLCHAIN = "leanprover/lean4:v4.35.0"
PINNED_CON_LECHE_REV = "501589f5680d9599dee1bcef30a420bc8924c490"

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


CORPORA_COVERAGE: dict[str, Any] = {
    "batteries_and_c2": {
        "measurement_status": "measured_via_ingestLCNFImpureDecl",
        "scope": (
            "1,805 non-aux compiled LCNF declarations across in-toolchain Std/Init core data structure "
            "modules (`Init.Data.{Array.Basic,Array.BinSearch,Array.QSort,ByteArray.Basic,BitVec.Basic,UInt.Basic}`, "
            "`Std.Data.{HashMap.Basic,DHashMap.Internal.Raw,TreeMap.Basic,ByteSlice}`: 1,773 decls) and "
            "Tier C2 multi-module Lake packages (`C2BitwiseScan`, `C2FieldButterfly`, `C2ProtocolMachine`, "
            "`C2CryptoSipHash`: 32 decls)"
        ),
        "unknown_external_batteries_modules": {
            "status": "unknown",
            "reason": (
                "External `leanprover-community/batteries` modules beyond `Init.Data.*` and `Std.Data.*` are "
                "not vendored as `.olean` artifacts in this workspace (`C2x` adds nightly Batteries checkout); "
                "reported as unknown rather than estimated via source-pattern heuristics."
            ),
        },
        "toolchain": PINNED_TOOLCHAIN,
        "total_declarations": 1805,
        "proved": 29,
        "lowered_unproved": 72,
        "lowered_unproved_breakdown": {
            "vacuous_local_call_pre_L2": 72,
            "pure_phase_fallback": 0,
            "gf_simd_whitelist": 0,
        },
        "rejected": 1704,
        "proved_non_vacuous_share_pct": 1.61,
        "lowered_total_share_pct": 5.60,
        "subcorpora": {
            "std_init_data": {
                "total_declarations": 1773,
                "proved": 16,
                "lowered_unproved": 65,
                "rejected": 1692,
            },
            "c2_lake_packages": {
                "total_declarations": 32,
                "proved": 13,
                "lowered_unproved": 7,
                "rejected": 12,
            },
        },
        "rejection_reasons": [
            {"reason": "Unsupported non-scalar/higher-order type in signature or binding", "count": 552},
            {"reason": "Unsupported partial application (pap) closure", "count": 331},
            {"reason": "Unsupported non-scalar argument in call", "count": 216},
            {"reason": "Unsupported constructor layout / non-scalar ADT field", "count": 130},
            {"reason": "Unsupported erased runtime argument (Arg.erased)", "count": 108},
            {"reason": "External (@[extern]) declaration without body", "count": 98},
            {"reason": "Unsupported string literal (LitValue.str)", "count": 96},
            {"reason": "Unsupported higher-order / closure (fvar) application", "count": 50},
            {"reason": "Unsupported signed integer type (Int* / ISize)", "count": 29},
            {"reason": "Unsupported self-tail or mutual recursion", "count": 24},
            {"reason": "Non-borrowed slice parameter requires borrow (@&)", "count": 21},
            {"reason": "Unsupported cases scrutinee type", "count": 19},
            {"reason": "Unsupported external or non-scalar call (fap)", "count": 19},
            {"reason": "Unsupported join-point / reset-reuse shape", "count": 11},
        ],
    },
    "c1_corpus": {
        "measurement_status": "measured_via_emit_lnir_and_3way_harness",
        "scope": (
            "875 unique LCNF declarations across the 8 blocking Tier C1 3-way run test suites "
            "(`C1_CORPUS_TESTS` in `scripts/test_scalar_frontend.py`: 839 generated seed declarations + "
            "18 unique preamble helper declarations + 6 Stage-1B exported declarations + 2 Stage-1B helper "
            "declarations + 10 distinct negative fail-closed boundary probe declarations across 12 negative checks)"
        ),
        "toolchain": PINNED_TOOLCHAIN,
        "total_declarations": 875,
        "proved": 768,
        "lowered_unproved": 95,
        "lowered_unproved_breakdown": {
            "vacuous_local_call_pre_L2": 95,
            "pure_phase_fallback": 0,
            "gf_simd_whitelist": 0,
        },
        "rejected": 12,
        "proved_non_vacuous_share_pct": 87.77,
        "lowered_total_share_pct": 98.63,
        "rejection_reasons": [
            {"reason": "Unsupported signed integer type (Int* / ISize)", "count": 3},
            {"reason": "Unsupported self-tail or mutual recursion", "count": 2},
            {"reason": "Unsupported non-scalar/higher-order type in signature or binding", "count": 2},
            {"reason": "Unsupported constructor layout / non-scalar ADT field", "count": 2},
            {"reason": "Unsupported string literal (LitValue.str)", "count": 1},
            {"reason": "Unsupported external or non-scalar call (fap)", "count": 1},
            {"reason": "External (@[extern]) declaration without body", "count": 1},
        ],
    },
    "con_leche_h3_benchmark": {
        "measurement_status": "measured_via_ingestLCNFImpureDecl_maxHeartbeats_0",
        "repository": "https://github.com/leanprover/con-leche.git",
        "commit_sha": PINNED_CON_LECHE_REV,
        "toolchain": PINNED_TOOLCHAIN,
        "scope": (
            "14,415 non-aux compiled LCNF declarations across all 99 checker modules (`Main` + "
            "`ConLeche.{Kernel,Cached,Frontend,Driver}`) with `maxHeartbeats := 0`, excluding the "
            "27,163 auto-generated literal certificate arrays in `ConLeche.Kernel.NatOpPins`"
        ),
        "total_declarations": 14415,
        "proved": 108,
        "lowered_unproved": 809,
        "lowered_unproved_breakdown": {
            "vacuous_local_call_pre_L2": 809,
            "pure_phase_fallback": 0,
            "gf_simd_whitelist": 0,
        },
        "rejected": 13498,
        "proved_non_vacuous_share_pct": 0.75,
        "lowered_total_share_pct": 6.36,
        "rejection_reasons": [
            {"reason": "Unsupported non-scalar/higher-order type in signature or binding", "count": 2853},
            {"reason": "Unsupported string literal (LitValue.str)", "count": 2750},
            {"reason": "Unsupported constructor layout / non-scalar ADT field", "count": 2289},
            {"reason": "Unsupported non-scalar argument in call", "count": 1970},
            {"reason": "Unsupported self-tail or mutual recursion", "count": 831},
            {"reason": "Unsupported cases scrutinee type", "count": 806},
            {"reason": "Unsupported partial application (pap) closure", "count": 569},
            {"reason": "Unsupported erased runtime argument (Arg.erased)", "count": 362},
            {"reason": "Unsupported higher-order / closure (fvar) application", "count": 327},
            {"reason": "Unsupported signed integer type (Int* / ISize)", "count": 308},
            {"reason": "Unsupported external or non-scalar call (fap)", "count": 237},
            {"reason": "Unsupported join-point / reset-reuse shape", "count": 164},
            {"reason": "Non-borrowed slice parameter requires borrow (@&)", "count": 23},
            {"reason": "Unsupported heap / scalar field mutation (oset/uset/sset)", "count": 9},
        ],
        "executed_from_main": {
            "scope": (
                "4,282 non-aux declarations reachable from `main` via `scripts/executed-decls.lean` "
                "(31,962 total IR declarations reached; 4,282 non-aux `ConLeche.*`/`Main` declarations "
                "excluding `ConLeche.Kernel.NatOpPins`)"
            ),
            "total_declarations": 4282,
            "proved": 18,
            "lowered_unproved": 106,
            "rejected": 4158,
            "proved_non_vacuous_share_pct": 0.42,
            "lowered_total_share_pct": 2.90,
            "rejection_reasons": [
                {"reason": "Unsupported non-scalar/higher-order type in signature or binding", "count": 922},
                {"reason": "Unsupported string literal (LitValue.str)", "count": 823},
                {"reason": "Unsupported constructor layout / non-scalar ADT field", "count": 739},
                {"reason": "Unsupported self-tail or mutual recursion", "count": 665},
                {"reason": "Unsupported non-scalar argument in call", "count": 294},
                {"reason": "Unsupported erased runtime argument (Arg.erased)", "count": 207},
                {"reason": "Unsupported external or non-scalar call (fap)", "count": 198},
                {"reason": "Unsupported signed integer type (Int* / ISize)", "count": 129},
                {"reason": "Unsupported join-point / reset-reuse shape", "count": 83},
                {"reason": "Unsupported cases scrutinee type", "count": 56},
                {"reason": "Unsupported partial application (pap) closure", "count": 30},
                {"reason": "Unsupported higher-order / closure (fvar) application", "count": 6},
                {"reason": "Non-borrowed slice parameter requires borrow (@&)", "count": 3},
                {"reason": "Unsupported heap / scalar field mutation (oset/uset/sset)", "count": 3},
            ],
        },
    },
}


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


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

    return {
        "schemaVersion": "turbo-lean-lcnf-coverage-v1",
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
        "corpora": json.loads(json.dumps(CORPORA_COVERAGE)),
    }


def check_coverage_report(root_dir: Path = ROOT_DIR, report: dict[str, Any] | None = None) -> dict[str, Any]:
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
        tot = corp["total_declarations"]
        if tot != corp["proved"] + corp["lowered_unproved"] + corp["rejected"]:
            errors.append(f"Corpus `{cname}` declaration counts do not sum to total_declarations")
        rej_sum = sum(int(r["count"]) for r in corp["rejection_reasons"])
        if rej_sum != corp["rejected"]:
            errors.append(
                f"Corpus `{cname}` rejection_reasons sum ({rej_sum}) != rejected ({corp['rejected']})"
            )
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
        if "executed_from_main" in corp:
            ex = corp["executed_from_main"]
            if ex["total_declarations"] != ex["proved"] + ex["lowered_unproved"] + ex["rejected"]:
                errors.append(f"Corpus `{cname}.executed_from_main` counts do not sum to total")
            ex_rej = sum(int(r["count"]) for r in ex["rejection_reasons"])
            if ex_rej != ex["rejected"]:
                errors.append(
                    f"Corpus `{cname}.executed_from_main` rejection sum ({ex_rej}) != rejected ({ex['rejected']})"
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
        self.assertEqual(rep["schemaVersion"], "turbo-lean-lcnf-coverage-v1")
        self.assertEqual(rep["leaf_id"], "H1.0")
        summary = rep["lcnf_constructor_matrix"]["summary"]
        self.assertEqual(summary["total"], 46)
        self.assertEqual(summary["proved"], 32)
        self.assertEqual(summary["lowered_unproved"], 4)
        self.assertEqual(summary["rejected"], 10)
        bat = rep["corpora"]["batteries_and_c2"]
        self.assertEqual(bat["unknown_external_batteries_modules"]["status"], "unknown")
        self.assertEqual(bat["proved"], 29)
        self.assertEqual(bat["lowered_unproved"], 72)
        self.assertEqual(bat["rejected"], 1704)

    def test_detects_corrupted_rejection_sum(self) -> None:
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


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true", help="Emit full coverage report JSON to stdout")
    ap.add_argument("--check", action="store_true", help="Verify bridge digests, symbols, and invariants")
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
        bat = chk["report"]["corpora"]["batteries_and_c2"]
        c1 = chk["report"]["corpora"]["c1_corpus"]
        print(
            f"[lcnf-coverage] ok={chk['ok']} "
            f"matrix={ms['proved']}/{ms['total']} proved ({ms['lowered_unproved']} lowered_unproved, {ms['rejected']} rejected) "
            f"batteries_c2={bat['proved']}/{bat['total_declarations']} proved (+{bat['lowered_unproved']} vacuous_local_call) "
            f"c1={c1['proved']}/{c1['total_declarations']} proved (+{c1['lowered_unproved']} vacuous_local_call)"
        )
    if not chk["ok"]:
        for err in chk["errors"]:
            print(f"  [ERROR] {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
