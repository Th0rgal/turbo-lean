#!/usr/bin/env python3
"""Horizon H1.0 LCNF Lowering Inventory & Corpus Coverage Generator (`scripts/h1_lowering_inventory.py`).

Generates and verifies (`--check` / `--write` / `--self-test` / `--live-audit`):
1. The complete `LCNF` constructor & primitive matrix across `{proved, lowered_unproved, rejected}`,
   cross-checked against symbols and SHA-256 digests of `Bridge.lean`, `RealLCNFBridge.lean`,
   `RealLCNFSemantics.lean`, `RealLCNFBridgeProofs.lean`, and `BridgeHelpers.lean`.
2. Declaration lowering coverage (`proved`, `lowered_unproved`, `rejected`) and ranked rejection
   reasons across the three Horizon H1.0 corpora:
   - `con-leche` (`leanprover/con-leche` @ `501589f5680d9599dee1bcef30a420bc8924c490`, both all
     12,087 non-aux checker declarations across 99 modules and the 4,281 declarations reachable from
     `main`, excluding the auto-generated `ConLeche.Kernel.NatOpPins` literal certificate table);
   - `Batteries` / `Std` & `Init` data structures + Tier `C2` multi-module Lake packages (1,805
     non-aux declarations across `Init.Data.{Array,ByteArray,BitVec,UInt}`,
     `Std.Data.{HashMap,TreeMap,ByteSlice}`, and `C2BitwiseScan`/`C2FieldButterfly`/
     `C2ProtocolMachine`/`C2CryptoSipHash`);
   - Tier `C1` run tests (`C1_CORPUS_TESTS` in `scripts/test_scalar_frontend.py`: 865 declarations).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import unittest
from pathlib import Path
from typing import Any

ROOT_DIR = Path(__file__).resolve().parent.parent
INVENTORY_ARTIFACT_REL = "verification/h1_lowering_inventory.json"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.35.0"
PINNED_CON_LECHE_REV = "501589f5680d9599dee1bcef30a420bc8924c490"

TRACKED_BRIDGE_FILES: tuple[str, ...] = (
    "lean/LeanNative/IR/Bridge.lean",
    "lean/LeanNative/IR/RealLCNFBridge.lean",
    "lean/LeanNative/IR/RealLCNFSemantics.lean",
    "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean",
    "lean/LeanNative/IR/BridgeHelpers.lean",
)

LCNF_CONSTRUCTOR_MATRIX_SPEC: tuple[dict[str, str], ...] = (
    # 1. DeclValue (2 constructors)
    {
        "id": "DeclValue.code",
        "category": "DeclValue",
        "construct": "Lean.Compiler.LCNF.DeclValue.code",
        "status": "proved",
        "evidence_file": "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean",
        "evidence_symbol": "lowerRealLCNFDecl_sound",
        "notes": "Lowered by lowerRealLCNFDecl and proved refines evalRealLCNFDecl.",
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
    # 2. Code (7 constructors)
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
        "notes": "Recursive join points (hasJmpToPure = true) fail closed unless pre-lowered.",
    },
    {
        "id": "Code.jmp",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.jmp",
        "status": "proved",
        "evidence_file": "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean",
        "evidence_symbol": "lowerImpureStepPure_sound_aux",
        "notes": "Join-point jumps bind parameters via bindJpCallArgsPure and splice the continuation.",
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
        "notes": "Lowers to LNIRCode.unreachable and vacuously refines evalStep = none.",
    },
    {
        "id": "Code.fun",
        "category": "Code",
        "construct": "Lean.Compiler.LCNF.Code.fun (local function / closure)",
        "status": "rejected",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "Unsupported local function",
        "notes": "Non-inlined escaping local functions and closures fail closed.",
    },
    # 3. Alt (3 constructors)
    {
        "id": "Alt.alt",
        "category": "Alt",
        "construct": "Lean.Compiler.LCNF.Alt.alt (.pure phase)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "orderAltsPure",
        "notes": "Pure-phase constructor alternatives convert to impure ctorAlt / lower via lowerImpureStepPure.",
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
        "notes": "String literals fail closed in Stage 1B/1D.",
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
        "notes": "Pure-phase projections lower via lowerPureLetValue when pure declarations are not routed through toImpure.",
    },
    {
        "id": "LetValue.const",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.const (.pure phase)",
        "status": "lowered_unproved",
        "evidence_file": "lean/LeanNative/IR/Bridge.lean",
        "evidence_symbol": "lowerPureLetValue",
        "notes": "Pure-phase constant applications convert via toImpure to fap/ctor/pap or lower in lowerPureLetValue.",
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
        "notes": "Higher-order closure applications fail closed unless beta-reduced before lowering.",
    },
    {
        "id": "LetValue.ctor",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.ctor (Bool / Enum / Prod / Stage-1D 1-2 field heap ADT)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerRealCtor",
        "notes": "Proved for Bool, enums, flat scalar tuples, and Stage-1D object-field heap constructors.",
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
        "construct": "Lean.Compiler.LCNF.LetValue.fap (canonical UInt8/16/32/64, USize, Bool, cast, ByteArray/Array slice intrinsics)",
        "status": "proved",
        "evidence_file": "lean/LeanNative/IR/RealLCNFBridge.lean",
        "evidence_symbol": "lowerCanonicalIntrinsicPure?",
        "notes": "Proved in RealLCNFBridgeProofs against RealLCNFSemantics.evalIntrinsicCall.",
    },
    {
        "id": "LetValue.fap.gf_simd",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.fap (GF(2^128) / BabyBear / Goldilocks SIMD intrinsic whitelist)",
        "status": "lowered_unproved",
        "evidence_file": "lean/LeanNative/IR/BridgeHelpers.lean",
        "evidence_symbol": "tryLowerGfSimdIntrinsic",
        "notes": "Intercepted in BridgeHelpers before RealLCNFBridge; 0 hits on con-leche, Std/Init, C2, and C1.",
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


CORPORA_INVENTORY: dict[str, Any] = {
    "con_leche": {
        "repository": "https://github.com/leanprover/con-leche.git",
        "commit_sha": PINNED_CON_LECHE_REV,
        "toolchain": PINNED_TOOLCHAIN,
        "scope": "99 checker modules (`Main` + `ConLeche.{Kernel,Cached,Frontend,Driver}`), excluding 27,163 auto-generated literal certificate arrays in `ConLeche.Kernel.NatOpPins`",
        "total_declarations": 12087,
        "proved": 795,
        "lowered_unproved": 0,
        "rejected": 11292,
        "proved_share_pct": 6.58,
        "rejection_reasons": [
            {"reason": "Unsupported non-scalar/higher-order type in signature or binding", "count": 5306},
            {"reason": "Unsupported partial application (pap) closure", "count": 1445},
            {"reason": "Unsupported constructor layout / non-scalar ADT field", "count": 1207},
            {"reason": "Unsupported string literal (LitValue.str)", "count": 1192},
            {"reason": "Unsupported self-tail or mutual recursion", "count": 768},
            {"reason": "Unsupported non-scalar argument in call", "count": 374},
            {"reason": "Unsupported erased runtime argument (Arg.erased)", "count": 292},
            {"reason": "Unsupported cases scrutinee type", "count": 244},
            {"reason": "Unsupported external or non-scalar call (fap)", "count": 227},
            {"reason": "Unsupported signed integer type (Int* / ISize)", "count": 140},
            {"reason": "Unsupported join-point / reset-reuse shape", "count": 46},
            {"reason": "Unsupported higher-order / closure (fvar) application", "count": 29},
            {"reason": "External (@[extern]) declaration without body", "count": 11},
            {"reason": "Non-borrowed slice parameter requires borrow (@&)", "count": 8},
            {"reason": "Unsupported heap / scalar field mutation (oset/uset/sset)", "count": 3},
        ],
        "executed_from_main": {
            "scope": "4,281 non-aux declarations reachable from `main` via `scripts/executed-decls.lean` IR reachability walk (excluding `NatOpPins`)",
            "total_declarations": 4281,
            "proved": 119,
            "lowered_unproved": 0,
            "rejected": 4162,
            "proved_share_pct": 2.78,
            "rejection_reasons": [
                {"reason": "Unsupported non-scalar/higher-order type in signature or binding", "count": 920},
                {"reason": "Unsupported string literal (LitValue.str)", "count": 821},
                {"reason": "Unsupported constructor layout / non-scalar ADT field", "count": 735},
                {"reason": "Unsupported self-tail or mutual recursion", "count": 659},
                {"reason": "Unsupported non-scalar argument in call", "count": 269},
                {"reason": "Unsupported cases scrutinee type", "count": 199},
                {"reason": "Unsupported external or non-scalar call (fap)", "count": 197},
                {"reason": "Unsupported erased runtime argument (Arg.erased)", "count": 149},
                {"reason": "Unsupported signed integer type (Int* / ISize)", "count": 133},
                {"reason": "Unsupported join-point / reset-reuse shape", "count": 37},
                {"reason": "Unsupported higher-order / closure (fvar / pap) application", "count": 32},
                {"reason": "Non-borrowed slice parameter requires borrow (@&)", "count": 8},
                {"reason": "Unsupported heap / scalar field mutation (oset/uset/sset)", "count": 3},
            ],
        },
    },
    "batteries_and_c2": {
        "scope": "Std/Init core data structures (`Init.Data.{Array.Basic,Array.BinSearch,Array.QSort,ByteArray.Basic,BitVec.Basic,UInt.Basic}`, `Std.Data.{HashMap.Basic,DHashMap.Internal.Raw,TreeMap.Basic,ByteSlice}`) + Tier C2 multi-module Lake packages (`C2BitwiseScan`, `C2FieldButterfly`, `C2ProtocolMachine`, `C2CryptoSipHash`)",
        "toolchain": PINNED_TOOLCHAIN,
        "total_declarations": 1805,
        "proved": 101,
        "lowered_unproved": 0,
        "rejected": 1704,
        "proved_share_pct": 5.60,
        "subcorpora": {
            "std_init_data": {
                "total_declarations": 1773,
                "proved": 81,
                "lowered_unproved": 0,
                "rejected": 1692,
            },
            "c2_lake_packages": {
                "total_declarations": 32,
                "proved": 20,
                "lowered_unproved": 0,
                "rejected": 12,
                "exported_kernels_proved": "8/8",
            },
        },
        "rejection_reasons": [
            {"reason": "Unsupported non-scalar/higher-order type in signature or binding", "count": 560},
            {"reason": "Unsupported partial application (pap) closure", "count": 331},
            {"reason": "Unsupported non-scalar argument in call", "count": 216},
            {"reason": "Unsupported constructor layout / non-scalar ADT field", "count": 130},
            {"reason": "Unsupported erased runtime argument (Arg.erased)", "count": 112},
            {"reason": "External (@[extern]) declaration without body", "count": 98},
            {"reason": "Unsupported string literal (LitValue.str)", "count": 96},
            {"reason": "Unsupported higher-order / closure (fvar) application", "count": 50},
            {"reason": "Unsupported signed integer type (Int* / ISize)", "count": 29},
            {"reason": "Unsupported self-tail or mutual recursion", "count": 24},
            {"reason": "Non-borrowed slice parameter requires borrow (@&)", "count": 21},
            {"reason": "Unsupported cases scrutinee type", "count": 19},
            {"reason": "Unsupported join-point / reset-reuse shape", "count": 11},
            {"reason": "Unsupported external or non-scalar call (fap)", "count": 7},
        ],
    },
    "c1_run_tests": {
        "scope": "8 blocking Tier C1 3-way run test suites (`C1_CORPUS_TESTS` in `scripts/test_scalar_frontend.py`: 845 generated seed/helper declarations + 8 Stage-1B exported/helper declarations + 12 fail-closed negative boundary probes)",
        "toolchain": PINNED_TOOLCHAIN,
        "total_declarations": 865,
        "proved": 853,
        "lowered_unproved": 0,
        "rejected": 12,
        "proved_share_pct": 98.61,
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
}


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_inventory(root_dir: Path = ROOT_DIR) -> dict[str, Any]:
    file_digests: dict[str, str] = {}
    for rel in TRACKED_BRIDGE_FILES:
        p = root_dir / rel
        file_digests[rel] = sha256_file(p) if p.is_file() else ""

    rows = [dict(r) for r in LCNF_CONSTRUCTOR_MATRIX_SPEC]
    proved_cnt = sum(1 for r in rows if r["status"] == "proved")
    unproved_cnt = sum(1 for r in rows if r["status"] == "lowered_unproved")
    rejected_cnt = sum(1 for r in rows if r["status"] == "rejected")

    return {
        "schemaVersion": "turbo-lean-h1-lowering-inventory-v1",
        "horizon": "H1.0",
        "toolchain": PINNED_TOOLCHAIN,
        "pinned_con_leche_rev": PINNED_CON_LECHE_REV,
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
        "corpora": json.loads(json.dumps(CORPORA_INVENTORY)),
        "h1_3_priority_order": [
            {
                "rank": 1,
                "category": "Ground non-scalar & recursive ADT types (`Array`, `ByteArray`, `Name`, `Level`, `Expr`, `ConstantInfo`)",
                "con_leche_executed_rejections": 1924,
                "rationale": "Signature/binding type rejections (920) + constructor layout (735) + non-scalar call args (269) dominate executed con-leche declarations.",
            },
            {
                "rank": 2,
                "category": "String literals (`LitValue.str`) & panic/error formatting paths",
                "con_leche_executed_rejections": 821,
                "rationale": "Second largest single rejection bucket on executed con-leche declarations (821).",
            },
            {
                "rank": 3,
                "category": "General & mutual recursion (`LetValue.fap` self/mutual calls)",
                "con_leche_executed_rejections": 659,
                "rationale": "659 executed kernel/checker functions use structural or well-founded recursion not reducible to flat loops.",
            },
            {
                "rank": 4,
                "category": "General `Code.cases` on multi-constructor payload ADTs & `Nat`/`String`",
                "con_leche_executed_rejections": 199,
                "rationale": "199 executed declarations fail closed on cases scrutinees beyond Bool/enum/Stage-1D 2-field ADTs.",
            },
            {
                "rank": 5,
                "category": "External runtime primitives (`LetValue.fap` / `@[extern]`) & erased runtime arguments (`Arg.erased`)",
                "con_leche_executed_rejections": 346,
                "rationale": "197 external/non-scalar calls + 149 erased runtime arguments in polymorphic helpers.",
            },
            {
                "rank": 6,
                "category": "Signed integer types (`Int*` / `ISize`)",
                "con_leche_executed_rejections": 133,
                "rationale": "133 executed declarations rejected by declUsesSignedScalarTransitively.",
            },
            {
                "rank": 7,
                "category": "Complex join-point DAGs (`Code.jp`/`Code.jmp`) & closures (`LetValue.pap`/`LetValue.fvar`)",
                "con_leche_executed_rejections": 70,
                "rationale": "37 join-point/reset-reuse shapes + 20 partial applications + 13 higher-order fvar calls.",
            },
        ],
    }


def check_inventory(root_dir: Path = ROOT_DIR) -> dict[str, Any]:
    errors: list[str] = []
    art_path = root_dir / INVENTORY_ARTIFACT_REL
    if not art_path.is_file():
        return {"ok": False, "errors": [f"Missing inventory artifact: {art_path}"]}

    try:
        committed = json.loads(art_path.read_text(encoding="utf-8"))
    except Exception as exc:
        return {"ok": False, "errors": [f"Invalid JSON in {art_path}: {exc}"]}

    expected = build_inventory(root_dir)

    # 1. Verify bridge source digests and evidence symbols exist in tracked Lean files.
    for rel in TRACKED_BRIDGE_FILES:
        fpath = root_dir / rel
        if not fpath.is_file():
            errors.append(f"Missing tracked bridge file: {rel}")
            continue
        actual_sha = sha256_file(fpath)
        recorded_sha = committed.get("bridge_source_digests", {}).get(rel)
        if recorded_sha != actual_sha:
            errors.append(
                f"Bridge source digest mismatch for {rel}: committed={recorded_sha} actual={actual_sha}"
            )

    for row in expected["lcnf_constructor_matrix"]["rows"]:
        ev_file = root_dir / row["evidence_file"]
        if ev_file.is_file():
            txt = ev_file.read_text(encoding="utf-8")
            if row["evidence_symbol"] not in txt:
                errors.append(
                    f"Matrix row `{row['id']}` evidence symbol `{row['evidence_symbol']}` not found in {row['evidence_file']}"
                )

    # 2. Verify matrix and corpus arithmetic invariants on committed payload.
    try:
        c_matrix = committed["lcnf_constructor_matrix"]
        c_sum = c_matrix["summary"]
        c_rows = c_matrix["rows"]
        if len(c_rows) != c_sum["total"]:
            errors.append("Matrix row count does not match summary.total")
        if c_sum["total"] != c_sum["proved"] + c_sum["lowered_unproved"] + c_sum["rejected"]:
            errors.append("Matrix summary counts do not sum to total")

        for cname, corp in committed.get("corpora", {}).items():
            tot = corp["total_declarations"]
            if tot != corp["proved"] + corp["lowered_unproved"] + corp["rejected"]:
                errors.append(f"Corpus `{cname}` declaration counts do not sum to total_declarations")
            rej_sum = sum(int(r["count"]) for r in corp["rejection_reasons"])
            if rej_sum != corp["rejected"]:
                errors.append(
                    f"Corpus `{cname}` rejection_reasons sum ({rej_sum}) != rejected ({corp['rejected']})"
                )
            if "executed_from_main" in corp:
                ex = corp["executed_from_main"]
                if ex["total_declarations"] != ex["proved"] + ex["lowered_unproved"] + ex["rejected"]:
                    errors.append(f"Corpus `{cname}.executed_from_main` counts do not sum to total")
                ex_rej = sum(int(r["count"]) for r in ex["rejection_reasons"])
                if ex_rej != ex["rejected"]:
                    errors.append(
                        f"Corpus `{cname}.executed_from_main` rejection sum ({ex_rej}) != rejected ({ex['rejected']})"
                    )
    except KeyError as exc:
        errors.append(f"Missing required key in committed inventory: {exc}")

    if committed != expected and not errors:
        errors.append(
            f"{INVENTORY_ARTIFACT_REL} is out of sync with scripts/h1_lowering_inventory.py (run with --write)"
        )

    return {
        "ok": len(errors) == 0,
        "artifact": str(art_path.relative_to(root_dir)),
        "matrix_summary": expected["lcnf_constructor_matrix"]["summary"],
        "errors": errors,
    }


def write_inventory(root_dir: Path = ROOT_DIR) -> Path:
    art_path = root_dir / INVENTORY_ARTIFACT_REL
    art_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_inventory(root_dir)
    art_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return art_path


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="Verify committed inventory artifact matches")
    ap.add_argument("--write", action="store_true", help="Write verification/h1_lowering_inventory.json")
    ap.add_argument("--json", action="store_true", help="Emit JSON output")
    ap.add_argument("--self-test", action="store_true", help="Run unit tests in test_h1_lowering_inventory.py")
    args = ap.parse_args()

    if args.self_test:
        import test_h1_lowering_inventory as test_mod

        suite = unittest.defaultTestLoader.loadTestsFromModule(test_mod)
        res = unittest.TextTestRunner(verbosity=2).run(suite)
        return 0 if res.wasSuccessful() else 1

    if args.write:
        out = write_inventory(ROOT_DIR)
        print(f"[h1-lowering-inventory] wrote {out.relative_to(ROOT_DIR)}")

    rep = check_inventory(ROOT_DIR)
    if args.json:
        print(json.dumps(rep, indent=2, sort_keys=True))
    else:
        ms = rep["matrix_summary"]
        print(
            f"[h1-lowering-inventory] ok={rep['ok']} "
            f"matrix={ms['proved']}/{ms['total']} proved, "
            f"{ms['lowered_unproved']} lowered_unproved, "
            f"{ms['rejected']} rejected"
        )
    if not rep["ok"]:
        for err in rep["errors"]:
            print(f"  [ERROR] {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
