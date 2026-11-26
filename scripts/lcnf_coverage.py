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
  classified under `lowered_unproved`). Rung **L2** (`420d1d1`) added a function environment to both
  semantics and proved `lowerRealLCNFDecl_soundF` (`lean/LeanNative/Proofs/LowerCalls.lean`) for
  non-recursive resolved calls whose arguments are all `.fvar`. Its contract hands the reclassification
  of those declarations (L2's "matrix moves" accept) to this script, which does not perform it yet, so
  every lowered declaration with a local call is still counted `lowered_unproved`.
- A call to a user function OUTSIDE the measured corpus is refused by the real lowerer and
  counted `rejected`, not `proved`, in the one measured counterexample pinned by
  `test_out_of_corpus_callee_is_rejected_never_proved` (a two-module fixture audited caller-only:
  1 total / 0 proved / 0 unproved / 1 rejected); no broader claim about out-of-corpus calls is
  made than that test measures.
- Compiler-generated auxiliary declarations (`isCompilerGeneratedAuxDecl`) are excluded from every
  corpus denominator — the measurement neither lowers nor expands them — and the number excluded is
  published per corpus and subcorpus as `compiler_aux_decls_excluded`, so the scope of
  `total_declarations` is auditable rather than claimed.
- The external `Batteries` corpus (`external_batteries`, leaf H1.0b) is measured only over an
  already-built `lake build` tree of the pinned `leanprover-community/batteries` revision
  (`PINNED_BATTERIES_REV`, whose `lean-toolchain` is the pinned `leanprover/lean4:v4.35.0`),
  discovered via `TURBO_BATTERIES_OLEANS` or at the conventional untracked checkout
  `scratch/batteries`. Nothing is fetched or built by this script; without such a tree (or on a
  partial one) the corpus is reported `not_measured` with a reason, never extrapolated.
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
# Compiler-generated auxiliary declarations (`isCompilerGeneratedAuxDecl`) are
# excluded from every corpus denominator; the count excluded is measured and
# published per corpus/subcorpus so the scope of `total_declarations` is
# auditable instead of claimed. It is outside the proved+unproved+rejected sum.
AUX_FIELD = "compiler_aux_decls_excluded"
MEASURED_INT_FIELDS = RESULT_FIELDS + (AUX_FIELD,)
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
# H1.0b external Batteries corpus. Nothing is fetched or built by this script:
# the measurement runs only over an already-built default-target `lake build`
# tree of the pinned `leanprover-community/batteries` revision (whose
# `lean-toolchain` file reads the pinned `leanprover/lean4:v4.35.0`), found via
# `TURBO_BATTERIES_OLEANS` or at the conventional untracked checkout
# `scratch/batteries`.
PINNED_BATTERIES_REV = "66e469188fe07963e5cf666c7d4433f45b8131c5"
BATTERIES_OLEANS_ENV = "TURBO_BATTERIES_OLEANS"
BATTERIES_REPO_URL = "https://github.com/leanprover-community/batteries.git"
# Pinned Batteries revision -> expected `Batteries`/`Batteries.*` module count of
# a full default-target `lake build` (the `Batteries` lib plus the `runLinter`
# exe; `runLinter` is not a corpus module). Obtained at commit
# 66e469188fe07963e5cf666c7d4433f45b8131c5 by counting `Batteries.lean` plus
# `Batteries/**/*.lean` in `git ls-tree -r` (195 sources) and matching the 195
# `Batteries*`-named `.olean` outputs of the completed 222-job build.
BATTERIES_PINNED_MODULE_COUNTS: dict[str, int] = {
    "66e469188fe07963e5cf666c7d4433f45b8131c5": 195,
}
_LIVE_AUDIT_CACHE: dict[str, dict[str, Any]] = {}
_CON_LECHE_CACHE: dict[str, dict[str, Any]] = {}
_BATTERIES_CACHE: dict[str, dict[str, Any]] = {}

# The committed results pin the sha256 of every tracked bridge/semantics/proof
# source they were measured from (`bridge_file_sha256` in
# `scripts/lcnf_coverage_results.json`, written by `--write-results` and gated
# by `--check`). The script itself carries no hard-coded digest: editing a
# tracked file fails `--check` against the committed results until the
# measurement is regenerated, and L1-L3 bridge PRs regenerate the JSON instead
# of hand-editing this script.
TRACKED_BRIDGE_FILES: tuple[str, ...] = (
    "lean/LeanNative/IR/Bridge.lean",
    "lean/LeanNative/IR/RealLCNFBridge.lean",
    "lean/LeanNative/IR/RealLCNFSemantics.lean",
    "lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean",
    "lean/LeanNative/IR/BridgeHelpers.lean",
)
# Every split helper module under these directories is tracked too (the S3a
# split moved the helper bodies out of BridgeHelpers.lean); a helper file
# added or removed changes the tracked set and fails `--check` until the
# committed results are re-measured.
TRACKED_BRIDGE_DIRS: tuple[str, ...] = ("lean/LeanNative/IR/BridgeHelpers",)
# Everything the measurement compiles or executes: the Lean tree (the tracked
# bridge dirs included, so an untracked `*.lean` stray shows as `??`), this
# script with its embedded audit driver, the C1 generators, and the C2 lake
# packages. `--write-results` refuses while any of these is dirty, because
# `measured_source_commit` claims the measurement came from HEAD's bytes. The
# committed results file itself is deliberately absent: rewriting it is the
# point of `--write-results`.
MEASUREMENT_INPUT_PATHS: tuple[str, ...] = (
    "lean",
    "scripts/lcnf_coverage.py",
    "scripts/test_scalar_frontend.py",
    "scripts/fuzz_lcnf_conformance.py",
    "verification/c2-lake-packages",
)
RESULTS_SCHEMA_VERSION = "turbo-lean-lcnf-coverage-results-v3"
MEASURED_SOURCE_COMMIT_NOTE = (
    "`measured_source_commit` is the commit of the tree the measurement was taken from "
    "(recorded when `--write-results` ran, i.e. the parent of the commit that updates this file)."
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
        "status": "rejected",
        "evidence_file": "lean/LeanNative/IR/BridgeHelpers/DeclIngestAndValidation.lean",
        "evidence_symbol": "no impure LCNF form",
        "notes": "L1 (81986e6a) deleted the pure-phase lowering (lowerPureCode / lowerPureLetValue): a declaration with no impure LCNF form fails closed at ingest. In the impure phase the lowerer reads, .proj is uninhabited (nomatch in RealLCNFCallSemantics.lean); impure projections are the LetValue.oproj / uproj / sproj rows.",
    },
    {
        "id": "LetValue.const",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.const (.pure phase)",
        "status": "rejected",
        "evidence_file": "lean/LeanNative/IR/BridgeHelpers/DeclIngestAndValidation.lean",
        "evidence_symbol": "no impure LCNF form",
        "notes": "L1 (81986e6a) deleted the pure-phase lowering (lowerPureCode / lowerPureLetValue): a declaration with no impure LCNF form fails closed at ingest. In the impure phase the lowerer reads, .const is uninhabited (nomatch in RealLCNFCallSemantics.lean); impure constant applications are the LetValue.fap / pap rows.",
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
        "notes": "Lowered to LNIRExpr.call by lowerImpureFapPure; evalLetValue returns .error (.unsupportedCall fn.toString) on a local callee, so lowerRealLCNFDecl_sound is vacuous here. L2 (420d1d1) proved lowerRealLCNFDecl_soundF (Proofs/LowerCalls.lean) for non-recursive resolved calls with all-.fvar arguments; this script does not yet reclassify those declarations (L2's \"matrix moves\" handoff), so every lowered declaration with a local call stays lowered_unproved.",
    },
    {
        "id": "LetValue.fap.gf_simd",
        "category": "LetValue",
        "construct": "Lean.Compiler.LCNF.LetValue.fap (GF(2^128) / BabyBear / Goldilocks SIMD intrinsic whitelist)",
        "status": "lowered_unproved",
        "evidence_file": "lean/LeanNative/IR/BridgeHelpers/StateAndIntrinsics.lean",
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
        "evidence_file": "lean/LeanNative/IR/BridgeHelpers/TypesAndSigs.lean",
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


def _tracked_bridge_paths(root_dir: Path = ROOT_DIR) -> list[str]:
    """The bridge/semantics/proof sources whose sha256 the committed results pin.

    The static `TRACKED_BRIDGE_FILES` plus every git-tracked `*.lean` directly
    under the `TRACKED_BRIDGE_DIRS` directories (`git ls-files`, so a scratch
    or dotfile `.lean` stray never joins the measured set), following the S3a
    BridgeHelpers/ split without hand-editing a list. Outside a git work tree
    (test fixture roots), the direct-children filesystem glob is the fallback.
    """
    paths = set(TRACKED_BRIDGE_FILES)
    inside_work_tree: bool | None = None
    for rel_dir in TRACKED_BRIDGE_DIRS:
        d = root_dir / rel_dir
        if not d.is_dir():
            continue
        if inside_work_tree is None:
            probe = subprocess.run(
                ["git", "rev-parse", "--is-inside-work-tree"],
                cwd=str(root_dir),
                capture_output=True,
                text=True,
                timeout=30,
            )
            inside_work_tree = probe.returncode == 0 and probe.stdout.strip() == "true"
        if not inside_work_tree:
            # Not a git work tree (test fixture roots): direct-children glob.
            paths.update(f"{rel_dir}/{f.name}" for f in sorted(d.glob("*.lean")))
            continue
        # `-z` gives NUL-separated raw paths, so a quotable (non-ASCII or
        # special-character) tracked path is never dropped by the filter.
        # Inside a work tree there is NO glob fallback: an empty tracked set
        # stays empty, and any other git failure is raised, so an untracked
        # stray can never silently rejoin the measured set.
        proc = subprocess.run(
            ["git", "ls-files", "-z", "--", rel_dir],
            cwd=str(root_dir),
            capture_output=True,
            text=True,
            timeout=30,
        )
        if proc.returncode != 0:
            raise RuntimeError(
                f"`git ls-files` failed for `{rel_dir}`; the tracked bridge set "
                f"cannot be enumerated:\n{proc.stderr}"
            )
        paths.update(
            p
            for p in proc.stdout.split("\0")
            if p.endswith(".lean") and "/" not in p[len(rel_dir) + 1 :]
        )
    return sorted(paths)


def _bridge_digests(root_dir: Path = ROOT_DIR) -> dict[str, dict[str, str]]:
    """Live sha256 of every tracked bridge source (empty string when missing)."""
    digests: dict[str, dict[str, str]] = {}
    for rel in _tracked_bridge_paths(root_dir):
        p = root_dir / rel
        digests[rel] = {"actual_sha256": sha256_file(p) if p.is_file() else ""}
    return digests


def _refuse_dirty_measurement_inputs(root_dir: Path = ROOT_DIR) -> None:
    """Refuse `--write-results` on a dirty measurement tree (fail closed).

    `measured_source_commit` claims the measurement came from HEAD's bytes, so
    every path in `MEASUREMENT_INPUT_PATHS` must be clean. Untracked files
    count (`?? ...` rows): an untracked `*.lean` under a tracked bridge dir is
    an input HEAD does not contain, and it was exactly what the earlier
    digest-keys pathspec missed. Ignored build outputs (`.lake/`) do not show
    in porcelain and do not refuse.
    """
    proc = subprocess.run(
        ["git", "status", "--porcelain", "--", *MEASUREMENT_INPUT_PATHS],
        cwd=str(root_dir),
        capture_output=True,
        text=True,
        timeout=30,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            "refusing to write results: `git status` failed for the measurement "
            f"inputs:\n{proc.stderr}"
        )
    if proc.stdout.strip():
        dirty = ", ".join(sorted(ln[3:].strip() for ln in proc.stdout.splitlines() if ln.strip()))
        raise RuntimeError(
            "refusing to write results: measurement inputs have uncommitted or "
            f"untracked changes ({dirty}); the recorded `measured_source_commit` "
            "would not match the measured bytes"
        )


def _is_hex_digest(value: Any, length: int) -> bool:
    return (
        isinstance(value, str)
        and len(value) == length
        and all(c in "0123456789abcdef" for c in value)
    )


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

unsafe def auditMods (env : Environment) (mods : Array Name) : IO (Nat × Nat × Nat × Nat × Nat × Nat) := do
  -- Fail closed: a module that cannot be converted to impure IR must fail the
  -- audit loudly, never contribute a silent zero, and a module missing from
  -- the imported environment must be named. The declaration set of this
  -- auditMods group (the std, C2, and C1 module groups are audited by separate
  -- auditMods calls, not one combined group) drives the local-callee
  -- classification, the call graph, and the bridge context, so a call to a
  -- user function declared in the same group is classified exactly like a
  -- same-module call (a vacuous local call), matching the eval
  -- `unsupportedCall` vacuity of `lowerRealLCNFDecl_sound` instead of being
  -- rejected or counted proved. Compiler-generated auxiliary declarations are
  -- excluded from the corpus (never measured, never expanded); the number
  -- excluded is returned so the published denominator's scope is auditable.
  let mut corpusDecls : Array (Name × Decl .impure) := #[]
  let mut auxTot := 0
  for modName in mods do
    let some modIdx := env.getModuleIdx? modName
      | throw (IO.userError s!"audit module `{modName}` not found in the imported environment")
    let mdecls := monoExt.getModuleEntries env modIdx
    let impDecls ← toImpureDecls env mdecls
    let impNonAux := impDecls.filter (fun d => !isCompilerGeneratedAuxDecl env d.name)
    auxTot := auxTot + (impDecls.size - impNonAux.size)
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
  return (tot, prv, unp, rej, cyc, auxTot)
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
  let (st, sp, su, sr, sc, sa) ← auditMods env stdMods
  let (c2t, c2p, c2u, c2r, c2c, c2a) ← auditMods env c2Mods
  let (c1t, c1p, c1u, c1r, c1c, c1a) ← auditMods env c1Mods
  IO.println s!"AUDIT_RESULT:{st},{sp},{su},{sr},{sc},{sa};{c2t},{c2p},{c2u},{c2r},{c2c},{c2a};{c1t},{c1p},{c1u},{c1r},{c1c},{c1a}"
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
  let (t, p, u, r, c, a) ← auditMods env mods
  IO.println s!"AUDIT_RESULT:{{t}},{{p}},{{u}},{{r}},{{c}},{{a}}"
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


def _parse_audit_result(
    stdout: str, stderr: str, *, groups: int
) -> list[tuple[int, int, int, int, int, int]]:
    """Parse the last AUDIT_RESULT line fail-closed.

    Requires exactly `groups` `;`-separated groups of exactly 6 integer fields
    (total, proved, unproved, rejected, rejected_not_lowered,
    compiler_aux_decls_excluded); a marker-less stdout, a wrong group count, a
    wrong field arity, or a non-integer field each raise a named error, so a
    malformed driver run is never converted into counts.
    """
    raw_lines = [ln.strip() for ln in stdout.splitlines() if ln.strip().startswith("AUDIT_RESULT:")]
    if not raw_lines:
        raise RuntimeError(
            f"Lean audit driver emitted no AUDIT_RESULT:\nSTDOUT:\n{stdout}\nSTDERR:\n{stderr}"
        )
    payload = raw_lines[-1].split(":", 1)[1]
    parts = payload.split(";")
    if len(parts) != groups:
        raise RuntimeError(
            f"Lean audit driver AUDIT_RESULT has {len(parts)} group(s), expected {groups}: {payload!r}"
        )
    out: list[tuple[int, int, int, int, int, int]] = []
    for part in parts:
        fields = part.split(",")
        if len(fields) != 6:
            raise RuntimeError(
                f"Lean audit driver AUDIT_RESULT group has {len(fields)} field(s), expected 6: {part!r}"
            )
        try:
            out.append(tuple(int(x) for x in fields))  # type: ignore[arg-type]
        except ValueError as exc:
            raise RuntimeError(
                f"Lean audit driver AUDIT_RESULT carries a non-integer field: {part!r}"
            ) from exc
    return out


def _run_audit_driver(
    root_dir: Path, driver_src: str, lib_dirs: list[str]
) -> tuple[int, int, int, int, int, int]:
    """Run one audit driver against `lib_dirs`.

    Returns (total, proved, unproved, rejected, rejected_not_lowered,
    compiler_aux_decls_excluded). A driver that exits non-zero, emits no
    AUDIT_RESULT, or emits a malformed one raises; a failed run is never
    converted into counts.
    """
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
    return _parse_audit_result(proc.stdout, proc.stderr, groups=1)[0]


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
        tot, prv, unp, rej, cyc, aux = _run_audit_driver(
            root_dir, _lean_audit_driver_for_modules([mod_name]), [str(root)]
        )
    return {
        "total_declarations": tot,
        "proved": prv,
        "lowered_unproved": unp,
        "rejected": rej,
        "rejected_not_lowered": cyc,
        "rejected_not_lowered_reason": REJECTED_NOT_LOWERED_REASON,
        "compiler_aux_decls_excluded": aux,
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
        audit_groups = _parse_audit_result(proc.stdout, proc.stderr, groups=3)
        st, sp, su, sr, sc, sa = audit_groups[0]
        c2t, c2p, c2u, c2r, c2c, c2a = audit_groups[1]
        c1t, c1p, c1u, c1r, c1c, c1a = audit_groups[2]

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
            "compiler_aux_decls_excluded": sa + c2a,
            "subcorpora": {
                "std_init_data": {
                    "total_declarations": st,
                    "proved": sp,
                    "lowered_unproved": su,
                    "rejected": sr,
                    "rejected_not_lowered": sc,
                    "rejected_not_lowered_reason": REJECTED_NOT_LOWERED_REASON,
                    "compiler_aux_decls_excluded": sa,
                },
                "c2_lake_packages": {
                    "total_declarations": c2t,
                    "proved": c2p,
                    "lowered_unproved": c2u,
                    "rejected": c2r,
                    "rejected_not_lowered": c2c,
                    "rejected_not_lowered_reason": REJECTED_NOT_LOWERED_REASON,
                    "compiler_aux_decls_excluded": c2a,
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
            "compiler_aux_decls_excluded": c1a,
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
    total, proved, unproved, rejected, rejected_not_lowered, aux_excluded = _run_audit_driver(
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
        "compiler_aux_decls_excluded": aux_excluded,
    }
    _CON_LECHE_CACHE[cache_key] = result
    return result


def _batteries_olean_root(root_dir: Path = ROOT_DIR) -> Path | None:
    """Where a prebuilt pinned Batteries `.olean` tree is, if there is one.

    `TURBO_BATTERIES_OLEANS` wins. Otherwise the tree a full `lake build` of an
    untracked `scratch/batteries` checkout leaves behind is used when present.
    """
    raw = os.environ.get(BATTERIES_OLEANS_ENV, "").strip()
    if raw:
        p = Path(raw)
        return p if p.is_dir() else None
    default = root_dir / "scratch" / "batteries" / ".lake" / "build" / "lib" / "lean"
    return default if default.is_dir() else None


def _batteries_modules(olean_root: Path) -> list[str]:
    mods: list[str] = []
    for olean in olean_root.rglob("*.olean"):
        rel = olean.relative_to(olean_root).with_suffix("")
        name = ".".join(rel.parts)
        if name == "Batteries" or name.startswith("Batteries."):
            mods.append(name)
    return sorted(mods)


def _is_full_batteries_build(olean_root: Path) -> bool:
    """True when `olean_root` sits inside a completed default-target `lake build`.

    The pinned revision's default targets are the `Batteries` lib and the
    `runLinter` exe, so a finished build leaves `../../bin/runLinter` beside the
    `.olean` tree; a lib-only partial build does not.
    """
    return (olean_root.parent.parent / "bin" / "runLinter").is_file()


def _merge_batteries_shard_facts(
    decl_rows: list[tuple[str, bool, list[str], str]], aux_total: int
) -> tuple[tuple[int, int, int, int, int, int], list[str]]:
    """Whole-corpus classification over per-declaration shard facts.

    `decl_rows` holds one row per non-aux corpus declaration, in corpus order:
    (decl name, has_local_call, same-corpus callees minus self, ingest verdict
    "ok" or "err:<head>"). The classification is auditMods' exactly: a
    declaration on a directed call-graph cycle (reachable from its own callees;
    self-edges are already removed at emission) is rejected_not_lowered without
    consulting its ingest verdict; otherwise an ok ingest splits proved vs
    lowered_unproved on has_local_call, and an ingest error is rejected.
    Returns the auditMods tuple (total, proved, lowered_unproved, rejected,
    rejected_not_lowered, aux_total) plus the rejection reason heads
    ("mutual_cycle" or the error head), which are diagnostic only and are never
    written to the committed results.
    """
    edges: dict[str, list[str]] = {}
    for name, _, callees, _ in decl_rows:
        edges[name] = callees  # a duplicate name overwrites, as HashMap.insert does

    def _on_cycle(target: str) -> bool:
        # declInMutualCycle's relation: DFS from the target's own callees over
        # the corpus call graph; true iff the target itself is reached (a node
        # absent from the graph contributes no edges).
        seen: set[str] = set()
        frontier = list(edges.get(target, ()))
        while frontier:
            cur = frontier.pop()
            if cur == target:
                return True
            if cur in seen:
                continue
            seen.add(cur)
            frontier.extend(edges.get(cur, ()))
        return False

    tot = prv = unp = rej = cyc = 0
    reasons: list[str] = []
    for name, has_call, _, verdict in decl_rows:
        tot += 1
        if _on_cycle(name):
            rej += 1
            cyc += 1
            reasons.append(REJECTED_NOT_LOWERED_REASON)
        elif verdict == "ok":
            if has_call:
                unp += 1
            else:
                prv += 1
        else:
            rej += 1
            reasons.append(verdict[4:] if verdict.startswith("err:") else verdict)
    return (tot, prv, unp, rej, cyc, aux_total), reasons


def _lean_shard_facts_driver(all_modules: list[str], shard_modules: list[str]) -> str:
    """A facts-emitting audit driver for one module shard of a larger corpus.

    Semantics parity with `auditMods` is by construction: the driver imports
    and converts (`toImpureDecls`) the WHOLE corpus so that `corpusNames`, the
    local-callee set, the per-declaration callee lists, and every
    `ingestLCNFImpureDecl` call see exactly the global name set the monolithic
    driver sees; only the per-declaration work (ingest, has-local-call, callee
    emission) is restricted to this shard's modules. The whole-corpus cycle
    pass runs once in `_merge_batteries_shard_facts` over the merged facts.
    Cycle members' ingest verdicts are computed here but ignored by the merger,
    which is sound because each ingest runs in a fresh `runCoreOnEnv` state and
    has no cross-declaration effect.
    """
    all_names = ",\n    ".join(f"`{m}" for m in all_modules)
    shard_names = ",\n    ".join(f"`{m}" for m in shard_modules)
    return _LEAN_AUDIT_DRIVER_HEAD + f"""
unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot) (args.map System.FilePath.mk)
  let allMods : Array Name := #[
    {all_names}
  ]
  let shardMods : Array Name := #[
    {shard_names}
  ]
  let env ← importModules (allMods.map (fun m => {{ module := m }})) {{}} (loadExts := true)
  let shardSet : Std.HashSet Name := shardMods.foldl (fun s m => s.insert m) {{}}
  let mut corpusDecls : Array (Name × Decl .impure) := #[]
  for modName in allMods do
    let some modIdx := env.getModuleIdx? modName
      | throw (IO.userError s!"audit module `{{modName}}` not found in the imported environment")
    let mdecls := monoExt.getModuleEntries env modIdx
    let impDecls ← toImpureDecls env mdecls
    let impNonAux := impDecls.filter (fun d => !isCompilerGeneratedAuxDecl env d.name)
    if shardSet.contains modName then
      IO.println s!"SHARD_AUX:{{modName}}|{{impDecls.size - impNonAux.size}}"
    for d in impNonAux do
      corpusDecls := corpusDecls.push (modName, d)
    IO.println s!"PROGRESS toimpure {{modName}}"
  let corpusNames := corpusDecls.map (·.2.name)
  let mut localSet : Std.HashSet Name := {{}}
  for n in corpusNames do localSet := localSet.insert n
  for modName in shardMods do
    for (m, d) in corpusDecls do
      if m == modName then
        let callees := match d.value with
          | .code c => (collectCodeLocalCallees corpusNames c).filter (· != d.name)
          | _ => []
        let hasCall := match d.value with
          | .code c => codeHasLocalCall localSet c
          | .extern _ => false
        let r ← runCoreOnEnv env (ingestLCNFImpureDecl d corpusNames .x86_64 true)
        let verdict := match r with
          | .ok _ => "ok"
          | .error e => "err:" ++ (((e.replace "\\n" " ").replace "|" "/").take 200)
        let calleeStr := String.intercalate "," (callees.map (fun n => n.toString))
        let hc := if hasCall then "1" else "0"
        IO.println s!"SHARD_DECL:{{d.name}}|{{hc}}|{{calleeStr}}|{{verdict}}"
    IO.println s!"PROGRESS ingest {{modName}}"
  IO.println "SHARD_DONE"
"""


def _run_sharded_batteries_audit(
    root_dir: Path,
    olean_root: Path,
    modules: list[str],
    workers: int | None = None,
    shard_count: int | None = None,
    log_dir: Path | None = None,
) -> tuple[tuple[int, int, int, int, int, int], list[str]]:
    """Measure a module corpus with the real lowerer, sharded across processes.

    Each shard is one `lake env lean --run` of `_lean_shard_facts_driver`; the
    merged per-declaration facts are classified by
    `_merge_batteries_shard_facts` (the whole-corpus cycle pass included), so
    the result tuple is `auditMods`-equivalent by construction. Fail-closed: a
    shard that exits non-zero, omits `SHARD_DONE`, drops or duplicates a
    module's `SHARD_AUX` line, or emits an unparsable facts line raises; a
    failed run is never converted into counts. `TURBO_BATTERIES_AUDIT_WORKERS`
    overrides the worker count; `TURBO_BATTERIES_AUDIT_LOG_DIR` (or `log_dir`)
    streams each shard's stdout to `<dir>/batteries-shard-<i>.log` for
    progress, instead of a run-private temporary directory.
    """
    if not modules:
        raise RuntimeError("sharded audit called with no modules")
    env_workers = os.environ.get("TURBO_BATTERIES_AUDIT_WORKERS", "").strip()
    if workers is None:
        workers = int(env_workers) if env_workers.isdigit() and int(env_workers) > 0 else 24
    workers = max(1, min(workers, len(modules)))
    if shard_count is None:
        shard_count = workers
    shard_count = max(1, min(shard_count, len(modules)))
    shards = [modules[i::shard_count] for i in range(shard_count)]
    env_log_dir = os.environ.get("TURBO_BATTERIES_AUDIT_LOG_DIR", "").strip()
    if log_dir is None and env_log_dir:
        log_dir = Path(env_log_dir)
    lean_dir = root_dir / "lean"
    env = _lean_env()

    def _run_shard(idx_and_shard: tuple[int, list[str]], out_dir: Path) -> list[str]:
        idx, shard = idx_and_shard
        driver_path = out_dir / f"ShardDriver{idx}.lean"
        driver_path.write_text(_lean_shard_facts_driver(modules, shard), encoding="utf-8")
        shard_log = out_dir / f"batteries-shard-{idx}.log"
        with open(shard_log, "w", encoding="utf-8") as lf:
            proc = subprocess.run(
                ["lake", "env", "lean", "--run", str(driver_path), str(olean_root)],
                cwd=str(lean_dir),
                env=env,
                stdout=lf,
                stderr=subprocess.PIPE,
                text=True,
            )
        out = shard_log.read_text(encoding="utf-8")
        if proc.returncode != 0 or "SHARD_DONE" not in out:
            raise RuntimeError(
                f"Batteries shard {idx} failed (rc={proc.returncode}):\n"
                f"STDOUT tail:\n{out[-4000:]}\nSTDERR tail:\n{proc.stderr[-4000:]}"
            )
        return out.splitlines()

    with tempfile.TemporaryDirectory(prefix="lcnf-batteries-shards-") as tmp:
        out_dir = Path(tmp)
        if log_dir is not None:
            log_dir.mkdir(parents=True, exist_ok=True)
            out_dir = log_dir
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            shard_lines = list(
                pool.map(lambda pair: _run_shard(pair, out_dir), enumerate(shards))
            )

    aux_by_module: dict[str, int] = {}
    decl_rows: list[tuple[str, bool, list[str], str]] = []
    for lines in shard_lines:
        for ln in lines:
            if ln.startswith("SHARD_AUX:"):
                mod, aux = ln[len("SHARD_AUX:"):].split("|", 1)
                if mod in aux_by_module:
                    raise RuntimeError(f"module `{mod}` reported by more than one shard")
                aux_by_module[mod] = int(aux)
            elif ln.startswith("SHARD_DECL:"):
                parts = ln[len("SHARD_DECL:"):].split("|", 3)
                if len(parts) != 4 or parts[1] not in ("0", "1"):
                    raise RuntimeError(f"unparsable shard facts line: {ln!r}")
                name, hc, callees_s, verdict = parts
                callees = [c for c in callees_s.split(",") if c]
                decl_rows.append((name, hc == "1", callees, verdict))
    missing = sorted(set(modules) - set(aux_by_module))
    if missing:
        raise RuntimeError(
            "sharded audit silently dropped module(s): " + ", ".join(missing)
        )
    aux_total = sum(aux_by_module.values())
    return _merge_batteries_shard_facts(decl_rows, aux_total)


def measure_external_batteries(root_dir: Path = ROOT_DIR) -> dict[str, Any]:
    """Measure the pinned external Batteries corpus with the real lowerer, or say why not.

    Same honesty contract as `measure_con_leche`: nothing is fetched or built.
    The caller points `TURBO_BATTERIES_OLEANS` at (or leaves at `scratch/batteries`)
    an already-built `lake build` tree of `PINNED_BATTERIES_REV`. Without one, or
    on a partial build, the corpus is `not_measured` with a reason and no counts.
    An unmapped pinned revision, or a full built tree whose module count differs
    from `BATTERIES_PINNED_MODULE_COUNTS[rev]`, returns
    `measurement_source = "error"` with a named `error_code`.
    """
    expected_count = BATTERIES_PINNED_MODULE_COUNTS.get(PINNED_BATTERIES_REV)
    if expected_count is None:
        return {
            "measurement_source": "error",
            "error_code": "unmapped_pinned_batteries_revision",
            "pinned_revision": PINNED_BATTERIES_REV,
            "reason": (
                f"unmapped_pinned_batteries_revision: PINNED_BATTERIES_REV={PINNED_BATTERIES_REV!r} "
                f"has no expected module count in BATTERIES_PINNED_MODULE_COUNTS"
            ),
        }
    olean_root = _batteries_olean_root(root_dir)
    cache_key = f"{root_dir.resolve()}|{PINNED_BATTERIES_REV}|{expected_count}|{olean_root}"
    if cache_key in _BATTERIES_CACHE:
        return _BATTERIES_CACHE[cache_key]
    if olean_root is None:
        result = {
            "measurement_source": "not_measured",
            "reason": (
                f"no prebuilt pinned Batteries `.olean` tree: set {BATTERIES_OLEANS_ENV} to a "
                f"`lake build` output directory of {BATTERIES_REPO_URL} commit "
                f"{PINNED_BATTERIES_REV} (or check that commit out at `scratch/batteries` and "
                "`lake build` it); this script does not fetch or build that repository."
            ),
            "expected_module_count": expected_count,
        }
        _BATTERIES_CACHE[cache_key] = result
        return result
    # The checkout is the nearest ancestor that is a git work tree.
    rev = "unknown"
    probe = olean_root
    for _ in range(6):
        if (probe / ".git").exists():
            rev = _git_head(probe)
            break
        probe = probe.parent
    if rev != PINNED_BATTERIES_REV:
        result = {
            "measurement_source": "not_measured",
            "reason": (
                f"prebuilt Batteries tree at `{olean_root}` is revision `{rev}`, not the pinned "
                f"`{PINNED_BATTERIES_REV}`"
            ),
            "expected_module_count": expected_count,
        }
        _BATTERIES_CACHE[cache_key] = result
        return result
    modules = _batteries_modules(olean_root)
    if not modules:
        result = {
            "measurement_source": "not_measured",
            "reason": f"no `Batteries`/`Batteries.*` `.olean` modules under `{olean_root}`",
            "module_count": 0,
            "expected_module_count": expected_count,
        }
        _BATTERIES_CACHE[cache_key] = result
        return result
    if len(modules) != expected_count:
        if _is_full_batteries_build(olean_root):
            result = {
                "measurement_source": "error",
                "error_code": "batteries_module_count_mismatch",
                "commit_sha": PINNED_BATTERIES_REV,
                "olean_root": str(olean_root),
                "module_count": len(modules),
                "expected_module_count": expected_count,
                "reason": (
                    f"batteries_module_count_mismatch: full Batteries build at `{olean_root}` "
                    f"(revision {PINNED_BATTERIES_REV}) has {len(modules)} `Batteries*` modules, "
                    f"expected {expected_count}"
                ),
            }
        else:
            result = {
                "measurement_source": "not_measured",
                "reason": (
                    f"partial Batteries tree under `{olean_root}` has {len(modules)} `Batteries*` "
                    f"modules, whereas pinned revision {PINNED_BATTERIES_REV} has "
                    f"{expected_count}; refusing to measure a partial tree"
                ),
                "module_count": len(modules),
                "expected_module_count": expected_count,
            }
        _BATTERIES_CACHE[cache_key] = result
        return result
    (
        total,
        proved,
        unproved,
        rejected,
        rejected_not_lowered,
        aux_excluded,
    ), _reasons = _run_sharded_batteries_audit(root_dir, olean_root, modules)
    result = {
        "measurement_source": "live_invocation",
        "measured_at_utc": _utc_now(),
        "repository": BATTERIES_REPO_URL,
        "commit_sha": PINNED_BATTERIES_REV,
        "toolchain": PINNED_TOOLCHAIN,
        "olean_root": str(olean_root),
        "module_count": len(modules),
        "expected_module_count": expected_count,
        "total_declarations": total,
        "proved": proved,
        "lowered_unproved": unproved,
        "rejected": rejected,
        "rejected_not_lowered": rejected_not_lowered,
        "rejected_not_lowered_reason": REJECTED_NOT_LOWERED_REASON,
        "compiler_aux_decls_excluded": aux_excluded,
    }
    _BATTERIES_CACHE[cache_key] = result
    return result


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
            "compiler_aux_decls_excluded": bat["compiler_aux_decls_excluded"],
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
            "compiler_aux_decls_excluded": c1["compiler_aux_decls_excluded"],
        }
    corpora["external_batteries"] = measure_external_batteries(root_dir)
    corpora["con_leche_h3_benchmark"] = measure_con_leche(root_dir)
    return corpora


def build_coverage_report(root_dir: Path = ROOT_DIR) -> dict[str, Any]:
    file_digests = _bridge_digests(root_dir)

    rows = [dict(r) for r in LCNF_CONSTRUCTOR_MATRIX_SPEC]
    proved_cnt = sum(1 for r in rows if r["status"] == "proved")
    unproved_cnt = sum(1 for r in rows if r["status"] == "lowered_unproved")
    rejected_cnt = sum(1 for r in rows if r["status"] == "rejected")

    corpora = build_live_corpora(root_dir)

    return {
        "schemaVersion": "turbo-lean-lcnf-coverage-v3-live",
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
    """Build the committed baseline (`scripts/lcnf_coverage_results.json`) from a live report.

    Fails closed: a provenance commit that is not a real sha, or a tracked
    bridge file without a live digest, refuses to write rather than committing
    an unverifiable baseline.
    """
    head = _git_head(root_dir)
    if not _is_hex_digest(head, 40):
        raise RuntimeError(
            f"refusing to write results: `git rev-parse HEAD` gave {head!r}, not a 40-hex commit"
        )
    digests: dict[str, str] = {}
    for rel, info in report.get("bridge_source_digests", {}).items():
        actual = info.get("actual_sha256", "") if isinstance(info, dict) else ""
        if not _is_hex_digest(actual, 64):
            raise RuntimeError(
                f"refusing to write results: tracked bridge file `{rel}` has no live sha256"
            )
        digests[rel] = actual
    if not digests:
        raise RuntimeError("refusing to write results: live report tracks no bridge files")
    # Defense in depth: main() runs this before the measurement; a direct
    # results_document caller gets the same refusal here.
    _refuse_dirty_measurement_inputs(root_dir)
    corpora: dict[str, Any] = {}
    for cname, corp in report.get("corpora", {}).items():
        if corp.get("status") == "unknown" or corp.get("measurement_source") != "live_invocation":
            continue
        entry: dict[str, Any] = {f: corp[f] for f in MEASURED_INT_FIELDS if f in corp}
        if "rejected_not_lowered_reason" in corp:
            entry["rejected_not_lowered_reason"] = corp["rejected_not_lowered_reason"]
        if "subcorpora" in corp:
            entry["subcorpora"] = {
                sname: {
                    **{f: sc[f] for f in MEASURED_INT_FIELDS if f in sc},
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
        "schemaVersion": RESULTS_SCHEMA_VERSION,
        "toolchain": PINNED_TOOLCHAIN,
        "measured_source_commit": head,
        "measured_source_commit_note": MEASURED_SOURCE_COMMIT_NOTE,
        "bridge_file_sha256": digests,
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
        if any(k in entry for k in MEASURED_INT_FIELDS):
            errors.append(f"Results file `{path}` is marked not_measured yet carries declaration counts")
        if "subcorpora" in entry:
            errors.append(f"Results file `{path}` is marked not_measured yet carries subcorpora")
        unknown = sorted(set(entry) - {"measurement_source", "reason"} - set(MEASURED_INT_FIELDS) - {"subcorpora"})
        if unknown:
            errors.append(
                f"Results file `{path}` not_measured stub carries unknown keys: {', '.join(unknown)}"
            )
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
    allowed_keys = set(MEASURED_INT_FIELDS) | {"rejected_not_lowered_reason"}
    if depth == 0:
        allowed_keys.add("subcorpora")
    unknown = sorted(set(entry) - allowed_keys)
    if unknown:
        errors.append(f"Results file `{path}` carries unknown keys: {', '.join(unknown)}")
    for f in MEASURED_INT_FIELDS:
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
        for f in MEASURED_INT_FIELDS
    )
    sub_ints = all(
        isinstance(sc, dict)
        and all(f in sc and isinstance(sc[f], int) and not isinstance(sc[f], bool) for f in MEASURED_INT_FIELDS)
        for sc in subs.values()
    )
    if parent_ints and sub_ints:
        for f in MEASURED_INT_FIELDS:
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
    required_top = (
        "schemaVersion",
        "toolchain",
        "measured_source_commit",
        "measured_source_commit_note",
        "bridge_file_sha256",
        "corpora",
    )
    unknown_top = sorted(set(doc) - set(required_top))
    if unknown_top:
        errors.append(f"Results file carries unknown top-level keys: {', '.join(unknown_top)}")
    for key in required_top:
        if key not in doc:
            errors.append(f"Results file is missing required key `{key}`")
    if doc.get("schemaVersion") != RESULTS_SCHEMA_VERSION:
        errors.append(
            f"Results file schemaVersion must be `{RESULTS_SCHEMA_VERSION}`, "
            f"got {doc.get('schemaVersion')!r}"
        )
    if doc.get("toolchain") != PINNED_TOOLCHAIN:
        errors.append(
            f"Results file toolchain mismatch: file={doc.get('toolchain')!r} "
            f"live={PINNED_TOOLCHAIN!r}"
        )
    msc = doc.get("measured_source_commit")
    if not _is_hex_digest(msc, 40):
        errors.append(
            f"Results file `measured_source_commit` must be a 40-hex commit sha, got {msc!r}"
        )
    if doc.get("measured_source_commit_note") != MEASURED_SOURCE_COMMIT_NOTE:
        errors.append(
            "Results file `measured_source_commit_note` does not match the canonical note text "
            "this script writes"
        )
    digests = doc.get("bridge_file_sha256")
    if not isinstance(digests, dict) or not digests:
        errors.append(
            "Results file `bridge_file_sha256` must be a non-empty JSON object of "
            "tracked path -> sha256"
        )
    else:
        for rel in sorted(digests):
            sha = digests[rel]
            if not isinstance(rel, str) or not rel.endswith(".lean"):
                errors.append(
                    f"Results file `bridge_file_sha256` key {rel!r} is not a tracked `.lean` path"
                )
            if not _is_hex_digest(sha, 64):
                errors.append(
                    f"Results file `bridge_file_sha256[{rel}]` must be a 64-hex sha256, got {sha!r}"
                )
    corpora = doc.get("corpora", {})
    if not isinstance(corpora, dict):
        errors.append("Results file `corpora` must be a JSON object")
        return errors
    for cname, entry in corpora.items():
        _validate_measured_entry(f"corpora.{cname}", entry, errors)
    return errors


def _live_measured_status_error(cname: str, corp: Any) -> str | None:
    """Fail-closed status validation for a live corpus with a counted baseline.

    The existing measured live shape has no `status` (or an explicit null) and
    `measurement_source == "live_invocation"`. Any other status/source is an
    unmeasured or malformed entry and must not satisfy a baseline with counts.
    """
    if not isinstance(corp, dict):
        return f"Corpus `{cname}` live entry must be a JSON object, got {type(corp).__name__}"
    status = corp.get("status")
    if status is not None:
        return (
            f"Corpus `{cname}` is measured in scripts/lcnf_coverage_results.json "
            f"but the live entry has status {status!r}; counted baselines require "
            f"a measured live entry"
        )
    source = corp.get("measurement_source")
    if source != "live_invocation":
        return (
            f"Corpus `{cname}` is measured in scripts/lcnf_coverage_results.json "
            f"but the live entry measurement_source is {source!r}, not 'live_invocation'"
        )
    for field in MEASURED_INT_FIELDS:
        value = corp.get(field)
        if isinstance(value, bool) or not isinstance(value, int):
            return (
                f"Corpus `{cname}` is measured in scripts/lcnf_coverage_results.json "
                f"but the live entry field `{field}` is not an integer "
                f"(got {type(value).__name__} {value!r})"
            )
    return None


def _compare_committed_digests(
    rep: dict[str, Any], base_digests: dict[str, Any], errors: list[str]
) -> None:
    """Compare the live report's tracked-file hashes against the committed pins."""
    live_digests = rep.get("bridge_source_digests", {})
    for rel, info in live_digests.items():
        actual = info.get("actual_sha256", "") if isinstance(info, dict) else ""
        if rel not in base_digests:
            errors.append(
                f"Tracked bridge file `{rel}` is missing from "
                f"scripts/lcnf_coverage_results.json `bridge_file_sha256`"
            )
            continue
        if base_digests[rel] != actual:
            errors.append(
                f"Bridge source digest mismatch for {rel}: "
                f"committed={base_digests[rel]} actual={actual}"
            )
    for rel in sorted(base_digests):
        if rel not in live_digests:
            errors.append(
                f"File `{rel}` is pinned in scripts/lcnf_coverage_results.json "
                f"`bridge_file_sha256` but is not tracked by the live report"
            )


def check_coverage_report(
    root_dir: Path = ROOT_DIR,
    report: dict[str, Any] | None = None,
    verify_live: bool = False,
    results: dict[str, Any] | None = None,
    require_results: bool = False,
    compare_results_digests: bool = True,
) -> dict[str, Any]:
    errors: list[str] = []
    skipped_corpora: list[str] = []
    rep = report if report is not None else build_coverage_report(root_dir)

    for rel in rep.get("bridge_source_digests", {}):
        if not (root_dir / rel).is_file():
            errors.append(f"Missing tracked bridge file: {rel}")

    for row in rep["lcnf_constructor_matrix"]["rows"]:
        ev_file = root_dir / row["evidence_file"]
        if ev_file.is_file():
            txt = ev_file.read_text(encoding="utf-8")
            if row["evidence_symbol"] not in txt:
                errors.append(
                    f"Matrix row `{row['id']}` evidence symbol `{row['evidence_symbol']}` not found in {row['evidence_file']}"
                )
        else:
            errors.append(
                f"Matrix row `{row['id']}` evidence file `{row['evidence_file']}` does not exist"
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
            if any(k in corp for k in MEASURED_INT_FIELDS):
                errors.append(f"Corpus `{cname}` is unknown yet carries declaration counts")
            continue
        if source == "not_measured":
            if not corp.get("reason"):
                errors.append(f"Corpus `{cname}` is not measured but gives no reason")
            if any(k in corp for k in MEASURED_INT_FIELDS):
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
        bad_fields = [
            field
            for field in MEASURED_INT_FIELDS
            if isinstance(corp.get(field), bool) or not isinstance(corp.get(field), int)
        ]
        if bad_fields:
            errors.append(
                f"Corpus `{cname}` live measured entry has non-integer fields: "
                + ", ".join(bad_fields)
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
                    isinstance(sc, dict) and all(f in sc for f in MEASURED_INT_FIELDS)
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
                    sub_aux = sum(s.get(AUX_FIELD, 0) for s in subs.values())
                    if (sub_tot, sub_prv, sub_unp, sub_rej, sub_rnl, sub_aux) != (
                        tot,
                        corp["proved"],
                        corp["lowered_unproved"],
                        corp["rejected"],
                        corp.get("rejected_not_lowered", 0),
                        corp.get(AUX_FIELD, 0),
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
        base_digests = baseline_doc.get("bridge_file_sha256", {}) if isinstance(baseline_doc, dict) else {}
        if not isinstance(base_digests, dict):
            base_digests = {}  # already named by validate_results_document
        _compare_committed_digests(rep, base_digests, errors)
        base_corpora = baseline_doc.get("corpora", {}) if isinstance(baseline_doc, dict) else {}
        if not isinstance(base_corpora, dict):
            base_corpora = {}
        live_corpora = rep.get("corpora", {})
        status_failed: set[str] = set()
        for cname, corp in live_corpora.items():
            if not isinstance(corp, dict):
                errors.append(
                    f"Live corpus `{cname}` must be a JSON object, got {type(corp).__name__}"
                )
                continue
            base_c = base_corpora.get(cname)
            if isinstance(base_c, dict) and base_c.get("measurement_source") != "not_measured":
                status_err = _live_measured_status_error(cname, corp)
                if status_err is not None:
                    errors.append(status_err)
                    status_failed.add(cname)
                    continue
            if corp.get("status") == "unknown":
                # An `unknown` corpus carries no counts and is not compared.
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
            diffs = [f for f in MEASURED_INT_FIELDS if base_c.get(f) != corp.get(f)]
            if diffs:
                side_summary = ", ".join(
                    f"{f}={base_c.get(f)} vs {corp.get(f)}" for f in MEASURED_INT_FIELDS
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
                for f in MEASURED_INT_FIELDS:
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
            if cname in status_failed:
                continue  # already named by the counted-baseline status guard
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
    elif compare_results_digests:
        # H1.0's acceptance command is `--json`: bridge-digest drift must not
        # pass silently outside `--check` either. When a committed baseline
        # exists it is loaded for the digest comparison alone (only
        # `--write-results`, which replaces the baseline, skips this).
        results_path = root_dir / "scripts" / "lcnf_coverage_results.json"
        if results_path.is_file():
            committed: Any = None
            try:
                committed = json.loads(results_path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                errors.append(f"Committed results file is unreadable: {exc}")
            if committed is not None and not isinstance(committed, dict):
                errors.append("Committed results file must be a JSON object")
            elif isinstance(committed, dict):
                base_digests = committed.get("bridge_file_sha256")
                if not isinstance(base_digests, dict) or not base_digests:
                    errors.append(
                        "Committed results file carries no `bridge_file_sha256` map "
                        "to gate bridge-source drift"
                    )
                else:
                    _compare_committed_digests(rep, base_digests, errors)
        else:
            errors.append(
                "Missing committed results file scripts/lcnf_coverage_results.json: "
                "bridge-digest drift cannot be gated (run --write-results to create it)"
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
                for field in MEASURED_INT_FIELDS:
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
                for field in MEASURED_INT_FIELDS:
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
        self.assertEqual(rep["schemaVersion"], "turbo-lean-lcnf-coverage-v3-live")
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
        ext = rep["corpora"]["external_batteries"]
        self.assertIn(ext.get("measurement_source"), ("live_invocation", "not_measured"), ext)
        self.assertGreater(bat["total_declarations"], 0)
        self.assertEqual(
            bat["total_declarations"],
            bat["proved"] + bat["lowered_unproved"] + bat["rejected"],
        )

    def test_json_corpus_numbers_come_from_live_measurement(self) -> None:
        # (a): `--json` must emit the same live measurement `--check` performs, never
        # stored constants. Every measured corpus carries measurement_source=live_invocation.
        # The spawned CLI is a cold process: without this env override it would
        # re-measure the full external Batteries corpus (hours of CPU) just to
        # exercise the --json path. Pointing it at a nonexistent tree makes the
        # subprocess report external_batteries as an honest not_measured stub
        # (--json performs no baseline comparison, so that is exit 0), while
        # std/c1 are still measured live end to end.
        sub_env = dict(os.environ)
        sub_env[BATTERIES_OLEANS_ENV] = str(ROOT_DIR / "scripts" / "no-such-batteries-olean-tree")
        proc = subprocess.run(
            [sys.executable, str(Path(__file__).resolve()), "--json"],
            capture_output=True,
            text=True,
            timeout=3600,
            env=sub_env,
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
        ext = data["corpora"]["external_batteries"]
        self.assertEqual(ext.get("measurement_source"), "not_measured")
        for field in RESULT_FIELDS:
            self.assertNotIn(field, ext)
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
                    sys.modules[__name__], "_run_audit_driver", return_value=(100, 7, 11, 82, 4, 9)
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
        # The digest pins live in the committed results (`bridge_file_sha256`),
        # not in this script: a drifted value, a dropped entry, and an entry
        # for a file the live report does not track each fail `--check` with a
        # named error, and the tracked set covers the S3a BridgeHelpers/ split.
        rep = self._v_fake_live_report()
        tracked = _tracked_bridge_paths(ROOT_DIR)
        self.assertGreaterEqual(len(tracked), 11, tracked)  # 5 static + the split helper files
        self.assertIn("lean/LeanNative/IR/BridgeHelpers/RealBridgeCtxAndSlices.lean", tracked)
        baseline = self._v_committed_baseline()
        self.assertEqual(sorted(baseline["bridge_file_sha256"]), tracked)

        first = sorted(baseline["bridge_file_sha256"])[0]
        drifted = json.loads(json.dumps(baseline))
        drifted["bridge_file_sha256"][first] = "0" * 64
        chk = check_coverage_report(ROOT_DIR, rep, results=drifted)
        self.assertFalse(chk["ok"])
        self.assertTrue(
            any("digest mismatch" in e and first in e for e in chk["errors"]), chk["errors"]
        )

        dropped = json.loads(json.dumps(baseline))
        del dropped["bridge_file_sha256"][first]
        chk = check_coverage_report(ROOT_DIR, rep, results=dropped)
        self.assertFalse(chk["ok"])
        self.assertTrue(
            any(first in e and "missing" in e for e in chk["errors"]), chk["errors"]
        )

        extra = json.loads(json.dumps(baseline))
        extra["bridge_file_sha256"]["lean/LeanNative/IR/NotTracked.lean"] = "0" * 64
        chk = check_coverage_report(ROOT_DIR, rep, results=extra)
        self.assertFalse(chk["ok"])
        self.assertTrue(
            any("NotTracked.lean" in e and "not tracked" in e for e in chk["errors"]),
            chk["errors"],
        )

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
        # unmeasured corpora (con-leche in CI) as skipped.
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
            corp.update({f: entry[f] for f in MEASURED_INT_FIELDS if f in entry})
            if "rejected_not_lowered_reason" in entry:
                corp["rejected_not_lowered_reason"] = entry["rejected_not_lowered_reason"]
            if "subcorpora" in entry:
                corp["subcorpora"] = json.loads(json.dumps(entry["subcorpora"]))
            corpora[cname] = corp
        corpora["con_leche_h3_benchmark"] = {
            "measurement_source": "not_measured",
            "reason": "no prebuilt pinned con-leche tree (test fixture)",
        }
        return {
            "bridge_source_digests": _bridge_digests(ROOT_DIR),
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

    def test_counted_baseline_live_status_truth_table(self) -> None:
        # SUBLEAF STATUS ONLY: for a baseline corpus carrying measured counts,
        # the live entry must be a valid measured entry. The complete truth
        # table: status must be absent/None (the existing measured shape) and
        # measurement_source must be exactly `live_invocation`; `unknown`,
        # `not_measured`, `error`, missing/null, wrong types, and unrecognized
        # values all fail closed. All RESULT_FIELDS must be present integers.
        # A baseline `not_measured` stub matching live `not_measured` remains a
        # legitimate skip (covered by the stub test above).
        baseline = self._v_committed_baseline()
        rep = self._v_fake_live_report()
        valid = json.loads(json.dumps(rep["corpora"]["c1_corpus"]))
        chk_ok = check_coverage_report(ROOT_DIR, rep, results=baseline)
        self.assertTrue(chk_ok["ok"], chk_ok["errors"])

        def entry(**changes: Any) -> dict[str, Any]:
            e = json.loads(json.dumps(valid))
            e.update(changes)
            return e

        def report(e: dict[str, Any]) -> dict[str, Any]:
            r = json.loads(json.dumps(rep))
            r["corpora"]["c1_corpus"] = e
            return r

        invalid: list[tuple[str, dict[str, Any]]] = []
        # Exact review repro shape: a live entry that only says unknown with a
        # reason (the external-corpus shape) must not satisfy a counted baseline.
        invalid.append(
            ("status unknown no counts", report({"status": "unknown", "reason": "review repro"}))
        )
        invalid.append(("status unknown with counts", report(entry(status="unknown"))))
        for label, value in (
            ("status not_measured", "not_measured"),
            ("status error", "error"),
            ("status unrecognized", "mystery"),
            ("status int", 7),
            ("status bool", True),
            ("status list", []),
        ):
            invalid.append((label, report(entry(status=value))))

        missing_source = entry()
        missing_source.pop("measurement_source", None)
        invalid.append(("source missing", report(missing_source)))
        invalid.append(("source null", report(entry(measurement_source=None))))
        invalid.append(("source not_measured", report(entry(measurement_source="not_measured"))))
        invalid.append(("source error", report(entry(measurement_source="error"))))
        invalid.append(("source unrecognized", report(entry(measurement_source="mystery"))))
        for label, value in (
            ("source int", 7),
            ("source bool", True),
            ("source list", []),
            ("source object", {}),
        ):
            invalid.append((label, report(entry(measurement_source=value))))

        for field in RESULT_FIELDS:
            missing_count = entry()
            missing_count.pop(field, None)
            invalid.append((f"count missing {field}", report(missing_count)))
            for label, value in (
                ("str", "1"),
                ("bool", True),
                ("null", None),
                ("float", 1.5),
                ("list", []),
            ):
                invalid.append(
                    (f"count {field} {label}", report(entry(**{field: value})))
                )

        for label, mutant in invalid:
            chk = check_coverage_report(ROOT_DIR, mutant, results=baseline)
            self.assertFalse(chk["ok"], f"{label} passed --check")
            self.assertTrue(
                any("c1_corpus" in e for e in chk["errors"]),
                f"{label}: {chk['errors']}",
            )

    def test_cli_check_rejects_unknown_live_status_for_counted_baseline(self) -> None:
        # CLI-adversarial status injection: drive `main()` with a live report
        # whose counted corpus is marked unknown and require the --check path to
        # return failure with a named error, not exit 0.
        import contextlib
        import io
        import unittest.mock as mock

        rep = self._v_fake_live_report()
        rep["corpora"]["c1_corpus"] = {
            "status": "unknown",
            "reason": "review repro: live status unknown",
        }
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(
            sys.modules[__name__], "build_coverage_report", return_value=rep
        ), mock.patch.object(
            sys, "argv", ["lcnf_coverage.py", "--check"]
        ), contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = sys.modules[__name__].main()
        self.assertEqual(rc, 1, f"unknown live status passed CLI --check: {out.getvalue()}")
        self.assertIn("c1_corpus", err.getvalue())
        self.assertIn("status", err.getvalue().lower())

    def test_missing_matrix_evidence_file_fails_check(self) -> None:
        # Review F2: a matrix row whose evidence_file does not exist must fail
        # `--check` with a named error instead of silently skipping the
        # evidence-symbol check (the V round retargeted two rows at the split
        # BridgeHelpers files; a typo there must not pass).
        baseline = self._v_committed_baseline()
        rep = self._v_fake_live_report()
        rep["lcnf_constructor_matrix"]["rows"] = [
            {
                "id": "Bogus.row",
                "category": "Test",
                "construct": "x",
                "status": "proved",
                "evidence_file": "lean/LeanNative/No/Such/File.lean",
                "evidence_symbol": "nope",
                "notes": "",
            }
        ]
        rep["lcnf_constructor_matrix"]["summary"] = {
            "total": 1, "proved": 1, "lowered_unproved": 0, "rejected": 0,
        }
        chk = check_coverage_report(ROOT_DIR, rep, results=baseline)
        self.assertFalse(chk["ok"], "missing evidence_file passed --check")
        self.assertTrue(
            any("Bogus.row" in e and "does not exist" in e for e in chk["errors"]),
            chk["errors"],
        )
        # Positive control: a real file + symbol row passes the matrix checks.
        rep2 = self._v_fake_live_report()
        rep2["lcnf_constructor_matrix"]["rows"] = [
            {
                "id": "Control.row",
                "category": "Test",
                "construct": "x",
                "status": "proved",
                "evidence_file": "lean/LeanNative/IR/BridgeHelpers/TypesAndSigs.lean",
                "evidence_symbol": "declUsesSignedScalarTransitively",
                "notes": "",
            }
        ]
        rep2["lcnf_constructor_matrix"]["summary"] = {
            "total": 1, "proved": 1, "lowered_unproved": 0, "rejected": 0,
        }
        chk2 = check_coverage_report(ROOT_DIR, rep2, results=baseline)
        self.assertTrue(chk2["ok"], chk2["errors"])

    def test_detects_real_bridge_content_drift_in_json_and_check_modes(self) -> None:
        # Review F1 + F6: a real content edit to a tracked bridge file must
        # fail the digest gate through the REAL report builder, both with an
        # explicit baseline (--check) and in non-check modes (--json / no
        # flag), where the committed results file is loaded for the digest
        # comparison. `--json` is the H1.0 acceptance command.
        import contextlib
        import io
        import shutil
        import unittest.mock as mock

        baseline = self._v_committed_baseline()
        with tempfile.TemporaryDirectory(prefix="lcnf-realdrift-") as tmp:
            root = Path(tmp)
            for rel in _tracked_bridge_paths(ROOT_DIR):
                dst = root / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(ROOT_DIR / rel, dst)
            (root / "scripts").mkdir()
            (root / "scripts" / "lcnf_coverage_results.json").write_text(
                json.dumps(baseline), encoding="utf-8"
            )
            target = root / "lean/LeanNative/IR/Bridge.lean"
            pristine = target.read_text(encoding="utf-8")
            target.write_text(pristine + "\n-- drift\n", encoding="utf-8")

            def _strip_matrix(r: dict[str, Any]) -> dict[str, Any]:
                # This test gates DIGESTS; the constructor matrix's evidence
                # files are deliberately not copied into the sparse tmp root
                # and would fail the (also new) evidence-file existence check.
                r = dict(r)
                r["lcnf_constructor_matrix"] = {
                    "rows": [],
                    "summary": {"total": 0, "proved": 0, "lowered_unproved": 0, "rejected": 0},
                }
                return r

            rep_drifted = _strip_matrix(build_coverage_report(root))
            # --check path (explicit baseline).
            chk = check_coverage_report(root, rep_drifted, results=baseline)
            self.assertFalse(chk["ok"], "content drift passed --check")
            self.assertTrue(
                any("digest mismatch" in e and "Bridge.lean" in e for e in chk["errors"]),
                chk["errors"],
            )
            # Non-check path: no results= and require_results=False, the
            # committed file in `root` is still consulted for digests.
            chk_json = check_coverage_report(root, rep_drifted)
            self.assertFalse(chk_json["ok"], "content drift passed the non-check digest gate")
            self.assertTrue(
                any("digest mismatch" in e and "Bridge.lean" in e for e in chk_json["errors"]),
                chk_json["errors"],
            )
            # Control: the undrifted copy is clean on the digest gate. On the
            # --check path the counted baseline is still (rightly) refused,
            # because this sparse root measures nothing live — that is the
            # measured-baseline-cannot-be-skipped guard, not digest drift — so
            # assert specifically that no digest error remains.
            target.write_text(pristine, encoding="utf-8")
            rep_clean = _strip_matrix(build_coverage_report(root))
            chk_clean = check_coverage_report(root, rep_clean, results=baseline)
            self.assertFalse(
                any("digest mismatch" in e for e in chk_clean["errors"]), chk_clean["errors"]
            )
            # The non-check path compares digests alone: the clean copy passes.
            chk_clean_json = check_coverage_report(root, rep_clean)
            self.assertTrue(chk_clean_json["ok"], chk_clean_json["errors"])
            # CLI-level: `--json` with a drifted live report exits 1, ok=false.
            out, err = io.StringIO(), io.StringIO()
            with mock.patch.object(
                sys.modules[__name__], "build_coverage_report", return_value=rep_drifted
            ), mock.patch.object(
                sys, "argv", ["lcnf_coverage.py", "--json"]
            ), contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                rc = sys.modules[__name__].main()
            self.assertEqual(rc, 1, "bridge drift passed CLI --json")
            self.assertFalse(json.loads(out.getvalue())["ok"])

    def test_write_results_refuses_dirty_tracked_bridge_files(self) -> None:
        # Round-1 F4 + round-2 F5: `--write-results` must refuse when a
        # measurement input has uncommitted changes, and the test must pin the
        # exact git command line, not just the canned outcome: the guard runs
        # `git status --porcelain --` over MEASUREMENT_INPUT_PATHS (which
        # covers the bridge dirs, so an edit AND an untracked stray both show).
        import unittest.mock as mock

        m = sys.modules[__name__]
        rel = "lean/LeanNative/IR/Bridge.lean"
        report = {"bridge_source_digests": {rel: {"actual_sha256": "0" * 64}}, "corpora": {}}
        with mock.patch.object(m, "_git_head", return_value="a" * 40), mock.patch.object(
            m.subprocess, "run"
        ) as run:
            run.return_value = mock.Mock(returncode=0, stdout=f" M {rel}\n", stderr="")
            with self.assertRaises(RuntimeError) as ctx:
                results_document(report, ROOT_DIR)
        self.assertIn("uncommitted", str(ctx.exception))
        self.assertIn(rel, str(ctx.exception))
        argv = run.call_args.args[0]
        self.assertEqual(argv[:4], ["git", "status", "--porcelain", "--"])
        for p in MEASUREMENT_INPUT_PATHS:
            self.assertIn(p, argv[4:], argv)
        self.assertEqual(run.call_args.kwargs.get("cwd"), str(ROOT_DIR))
        # Control: a clean status writes the document.
        with mock.patch.object(m, "_git_head", return_value="a" * 40), mock.patch.object(
            m.subprocess, "run"
        ) as run:
            run.return_value = mock.Mock(returncode=0, stdout="", stderr="")
            doc = results_document(report, ROOT_DIR)
        self.assertEqual(doc["bridge_file_sha256"], {rel: "0" * 64})

    def test_write_results_refuses_untracked_bridge_stray(self) -> None:
        # Round-2 F1, real temp git repo: an UNTRACKED `*.lean` directly under
        # a tracked bridge dir is a measurement input HEAD does not contain;
        # the dirty guard must refuse (`?? ...` in porcelain), where the
        # round-1 guard's digest-only pathspec let it through silently.
        with tempfile.TemporaryDirectory(prefix="lcnf-stray-") as tmp:
            root = Path(tmp)
            helpers = root / TRACKED_BRIDGE_DIRS[0]
            helpers.mkdir(parents=True)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True, capture_output=True, text=True)
            (helpers / "Tracked.lean").write_text("-- tracked\n", encoding="utf-8")
            subprocess.run(["git", "add", "."], cwd=root, check=True, capture_output=True, text=True)
            subprocess.run(
                ["git", "-c", "user.name=t", "-c", "user.email=t@example.com", "commit", "-qm", "init"],
                cwd=root, check=True, capture_output=True, text=True,
            )
            _refuse_dirty_measurement_inputs(root)  # clean repo: no refusal
            (helpers / "StrayScratch.lean").write_text("-- untracked stray\n", encoding="utf-8")
            with self.assertRaises(RuntimeError) as ctx:
                _refuse_dirty_measurement_inputs(root)
            self.assertIn("StrayScratch.lean", str(ctx.exception))
            # End to end: results_document refuses on the same repo.
            report = {
                "bridge_source_digests": {
                    f"{TRACKED_BRIDGE_DIRS[0]}/Tracked.lean": {"actual_sha256": "0" * 64}
                },
                "corpora": {},
            }
            with self.assertRaises(RuntimeError) as ctx2:
                results_document(report, root)
            self.assertIn("StrayScratch.lean", str(ctx2.exception))

    def test_write_results_dirty_guard_runs_before_measurement(self) -> None:
        # Round-2 F2 (cheap half): under `--write-results` the dirty guard runs
        # at the start of main, before the minutes-long audit, and a refusal is
        # a named [ERROR] + exit 1, not a traceback after the build.
        import contextlib
        import io
        import unittest.mock as mock

        m = sys.modules[__name__]
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(
            m, "_refuse_dirty_measurement_inputs",
            side_effect=RuntimeError("refusing to write results: dirty fixture"),
        ) as guard, mock.patch.object(
            m, "build_coverage_report",
            side_effect=AssertionError("measurement ran before the dirty guard"),
        ) as bcr, mock.patch.object(
            sys, "argv", ["lcnf_coverage.py", "--write-results"]
        ), contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = m.main()
        self.assertEqual(rc, 1)
        guard.assert_called_once()
        bcr.assert_not_called()
        self.assertIn("refusing to write results", err.getvalue())

    def test_json_mode_errors_when_results_file_missing(self) -> None:
        # Round-2 F3: outside --check, a MISSING committed results file must be
        # a named error (ok=false), not a silent skip of the digest gate —
        # `--json` is the H1.0 acceptance command. `--write-results` is the
        # bootstrap path and keeps compare_results_digests off.
        import shutil

        with tempfile.TemporaryDirectory(prefix="lcnf-noresults-") as tmp:
            root = Path(tmp)
            for rel in _tracked_bridge_paths(ROOT_DIR):
                dst = root / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(ROOT_DIR / rel, dst)
            rep = build_coverage_report(root)
            rep["lcnf_constructor_matrix"] = {
                "rows": [],
                "summary": {"total": 0, "proved": 0, "lowered_unproved": 0, "rejected": 0},
            }
            chk = check_coverage_report(root, rep)
            self.assertFalse(chk["ok"], "missing results file passed the non-check digest gate")
            self.assertTrue(
                any("Missing committed results file" in e for e in chk["errors"]),
                chk["errors"],
            )

    def test_tracked_bridge_paths_git_enumeration_edges(self) -> None:
        # Round-2 F4, real temp git repos: `-z` keeps a quotable (non-ASCII)
        # tracked path in the set; an untracked stray never joins it inside a
        # work tree, even when NOTHING is tracked under the dir (no silent
        # glob fallback there); the glob fallback applies only outside a git
        # work tree.
        rel_dir = TRACKED_BRIDGE_DIRS[0]
        with tempfile.TemporaryDirectory(prefix="lcnf-lsfiles-") as tmp:
            root = Path(tmp)
            helpers = root / rel_dir
            helpers.mkdir(parents=True)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True, capture_output=True, text=True)
            (helpers / "Hélper.lean").write_text("-- unicode-named helper\n", encoding="utf-8")
            subprocess.run(["git", "add", "."], cwd=root, check=True, capture_output=True, text=True)
            subprocess.run(
                ["git", "-c", "user.name=t", "-c", "user.email=t@example.com", "commit", "-qm", "init"],
                cwd=root, check=True, capture_output=True, text=True,
            )
            (helpers / "StrayScratch.lean").write_text("-- untracked stray\n", encoding="utf-8")
            paths = _tracked_bridge_paths(root)
            self.assertIn(f"{rel_dir}/Hélper.lean", paths, paths)
            self.assertNotIn(f"{rel_dir}/StrayScratch.lean", paths, paths)
        with tempfile.TemporaryDirectory(prefix="lcnf-lsfiles-none-") as tmp:
            root = Path(tmp)
            helpers = root / rel_dir
            helpers.mkdir(parents=True)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True, capture_output=True, text=True)
            (helpers / "OnlyStray.lean").write_text("-- untracked stray\n", encoding="utf-8")
            paths = _tracked_bridge_paths(root)
            self.assertNotIn(f"{rel_dir}/OnlyStray.lean", paths, paths)
        with tempfile.TemporaryDirectory(prefix="lcnf-lsfiles-nongit-") as tmp:
            root = Path(tmp)
            helpers = root / rel_dir
            helpers.mkdir(parents=True)
            (helpers / "PlainGlob.lean").write_text("-- glob fallback outside git\n", encoding="utf-8")
            paths = _tracked_bridge_paths(root)
            self.assertIn(f"{rel_dir}/PlainGlob.lean", paths, paths)

    def test_results_schema_rejects_unknown_keys_and_bad_provenance(self) -> None:
        # H1.0a-V hardening: each of these mutations passed the pre-hardening
        # gate (measured 2026-11-25). The committed note text is pinned, the
        # provenance commit must be a real 40-hex sha (its VALUE is provenance
        # and is deliberately not compared to HEAD), and unknown keys are
        # rejected at the top level, in corpus entries, in subcorpus entries,
        # and in not_measured stubs.
        rep = self._v_fake_live_report()

        def stubbed(d: dict[str, Any]) -> None:
            d["corpora"]["con_leche_h3_benchmark"] = {
                "measurement_source": "not_measured",
                "reason": "tree absent",
                "surprise_key": 1,
            }

        cases: list[tuple[str, Any, str]] = [
            (
                "altered measured_source_commit_note",
                lambda d: d.update(measured_source_commit_note="drifted note"),
                "measured_source_commit_note",
            ),
            (
                "dropped measured_source_commit_note",
                lambda d: d.pop("measured_source_commit_note"),
                "measured_source_commit_note",
            ),
            (
                "non-sha measured_source_commit",
                lambda d: d.update(measured_source_commit="not-a-sha"),
                "measured_source_commit",
            ),
            (
                "'unknown' measured_source_commit",
                lambda d: d.update(measured_source_commit="unknown"),
                "measured_source_commit",
            ),
            ("extra top-level key", lambda d: d.update(surprise_key=1), "surprise_key"),
            (
                "extra corpus-entry key",
                lambda d: d["corpora"]["c1_corpus"].update(surprise_key=1),
                "surprise_key",
            ),
            (
                "extra subcorpus-entry key",
                lambda d: d["corpora"]["std_init_and_c2"]["subcorpora"]["std_init_data"].update(
                    surprise_key=1
                ),
                "surprise_key",
            ),
            ("extra not_measured stub key", stubbed, "surprise_key"),
        ]
        for label, mutate, needle in cases:
            doc = self._v_committed_baseline()
            mutate(doc)
            chk = check_coverage_report(ROOT_DIR, rep, results=doc)
            self.assertFalse(chk["ok"], f"{label} passed --check")
            self.assertTrue(
                any(needle in e for e in chk["errors"]),
                f"{label}: no error names `{needle}`: {chk['errors']}",
            )

    def test_every_committed_nested_field_mutation_is_rejected(self) -> None:
        # H1.0a-V acceptance: walk the REAL committed baseline and prove, node
        # by node, that `--check` rejects (a) an alteration of every scalar
        # field, (b) a drop of every key, and (c) an unknown key injected into
        # every object — at every nesting level, bridge_file_sha256 and
        # subcorpora included. `measured_source_commit` alteration appends a
        # non-hex suffix because its value is provenance by design; every
        # other scalar is altered in kind (int +1, str suffix).
        rep = self._v_fake_live_report()
        pristine = self._v_committed_baseline()
        self.assertTrue(
            check_coverage_report(ROOT_DIR, rep, results=self._v_committed_baseline())["ok"]
        )

        mutants: list[tuple[str, dict[str, Any]]] = []

        def clone_at(path: tuple[str, ...]) -> tuple[dict[str, Any], dict[str, Any]]:
            clone = json.loads(json.dumps(pristine))
            node = clone
            for k in path:
                node = node[k]
            return clone, node

        def rec(node: Any, path: tuple[str, ...]) -> None:
            if isinstance(node, dict):
                clone, tgt = clone_at(path)
                tgt["injected_unexpected_key"] = 1
                mutants.append((f"inject unknown key at {'.'.join(path) or '<top>'}", clone))
                for k, v in node.items():
                    clone, tgt = clone_at(path)
                    del tgt[k]
                    mutants.append((f"drop {'.'.join(path + (k,))}", clone))
                    rec(v, path + (k,))
            else:
                clone, tgt = clone_at(path[:-1])
                leaf = path[-1]
                if isinstance(node, bool) or not isinstance(node, (int, str)):
                    tgt[leaf] = "drifted"
                elif isinstance(node, int):
                    tgt[leaf] = node + 1
                else:
                    tgt[leaf] = node + "x"
                mutants.append((f"alter {'.'.join(path)}", clone))

        rec(pristine, ())
        self.assertGreater(len(mutants), 60, "walk found suspiciously few committed fields")
        for label, doc in mutants:
            chk = check_coverage_report(ROOT_DIR, rep, results=doc)
            self.assertFalse(chk["ok"], f"committed-field mutation passed --check: {label}")
            self.assertTrue(chk["errors"], label)

    # ------------------------------------------------------------------
    # H1.0a-S (split S): honest proof classification and fail-closed
    # measurement (DeepSeek soundness findings against the audit driver;
    # same two paths as H1.0a-V, after V).
    # ------------------------------------------------------------------

    def _compile_xmod_fixture(self, root: Path) -> None:
        """Compile two modules into `root`: SCaller calls SAux.sa_one across modules."""
        lean_dir = ROOT_DIR / "lean"
        env = _lean_env()
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

    def test_cross_module_user_call_is_vacuous_not_rejected(self) -> None:
        # Counterexample (real lowerer, two compiled modules): a declaration in
        # one measured module calling a user function declared in another
        # measured module. The per-module localSet misses the cross-module
        # callee, so the real lowerer fails it as an unsupported call and the
        # driver counts it `rejected`, while the honest classification for a
        # call into a measured corpus declaration is a vacuous local call
        # (`lowered_unproved`) — eval `unsupportedCall` makes the pinned
        # simulation vacuous exactly like the same-module helper case.
        _ensure_lean_build(ROOT_DIR)
        with tempfile.TemporaryDirectory(prefix="lcnf-xmod-") as tmp:
            root = Path(tmp)
            self._compile_xmod_fixture(root)
            counts = _run_audit_driver(
                ROOT_DIR, _lean_audit_driver_for_modules(["SAux", "SCaller"]), [str(root)]
            )
        tot, prv, unp, rej, cyc, _aux = counts
        self.assertEqual(tot, 2, counts)
        self.assertEqual(prv, 1, counts)  # the callee itself lowers and proves
        self.assertEqual(unp, 1, counts)  # the cross-module caller is a vacuous local call
        self.assertEqual(rej, 0, counts)  # a corpus-local call is not an unsupported construct
        self.assertEqual(cyc, 0, counts)

    def test_out_of_corpus_callee_is_rejected_never_proved(self) -> None:
        # H1.0a-S classification investigation, pinned: a call to a user
        # function OUTSIDE the measured corpus (SAux is importable but not
        # audited) is refused by the real lowerer and counted `rejected` —
        # never `proved`, which would be dishonest because
        # `RealLCNFSemantics.evalLetValue` errors on the call and the pinned
        # simulation would be vacuous while the matrix claimed a proof.
        _ensure_lean_build(ROOT_DIR)
        with tempfile.TemporaryDirectory(prefix="lcnf-xcorpus-") as tmp:
            root = Path(tmp)
            self._compile_xmod_fixture(root)
            counts = _run_audit_driver(
                ROOT_DIR, _lean_audit_driver_for_modules(["SCaller"]), [str(root)]
            )
        tot, prv, unp, rej, cyc, _aux = counts
        self.assertEqual((tot, prv, unp, rej, cyc), (1, 0, 0, 1, 0), counts)

    def test_audit_driver_never_silently_drops_a_module(self) -> None:
        # H1.0a-S acceptance: an EXECUTABLE failure reproduction of the silent
        # module-IR drop, for the MISSING-MODULE branch only. The pre-fix
        # driver skipped a module missing from the imported environment
        # (`if let some modIdx := ... then`), so published counts silently
        # omitted declarations; the shipped driver must fail loudly, naming
        # the module, and the reconstructed pre-fix variant is run on the same
        # input and shown to emit exactly that silent under-count. The other
        # pre-fix drop (`.error _ => return #[]` on a failed IR conversion)
        # has no known fixture that makes `toImpure` fail deterministically,
        # so it is guarded TEXTUALLY by the assertNotIn below, not executed.
        self.assertNotIn(".error _ => return #[]", _LEAN_AUDIT_DRIVER_HEAD)
        self.assertIn("not found in the imported environment", _LEAN_AUDIT_DRIVER_HEAD)
        _ensure_lean_build(ROOT_DIR)
        main_src = """
unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot) (args.map System.FilePath.mk)
  let env ← importModules (#[`SAux].map (fun m => { module := m })) {} (loadExts := true)
  let (t, p, u, r, c, a) ← auditMods env #[`SAux, `SCaller]
  IO.println s!"AUDIT_RESULT:{t},{p},{u},{r},{c},{a}"
"""
        with tempfile.TemporaryDirectory(prefix="lcnf-silent-drop-") as tmp:
            root = Path(tmp)
            self._compile_xmod_fixture(root)
            # AFTER (shipped): SCaller is named for audit but absent from the
            # imported environment -> the run dies loudly, naming the module.
            with self.assertRaises(RuntimeError) as ctx:
                _run_audit_driver(ROOT_DIR, _LEAN_AUDIT_DRIVER_HEAD + main_src, [str(root)])
            self.assertIn(
                "audit module `SCaller` not found in the imported environment",
                str(ctx.exception),
            )
            # BEFORE (reconstructed pre-fix silent skip): the same input yields
            # a quiet AUDIT_RESULT that simply omits SCaller's declaration.
            before_head = _LEAN_AUDIT_DRIVER_HEAD.replace(
                '    let some modIdx := env.getModuleIdx? modName\n'
                '      | throw (IO.userError s!"audit module `{modName}` not found in the imported environment")',
                "    let some modIdx := env.getModuleIdx? modName\n      | continue",
            )
            self.assertNotEqual(before_head, _LEAN_AUDIT_DRIVER_HEAD)
            tot, prv, _unp, _rej, _cyc, _aux = _run_audit_driver(
                ROOT_DIR, before_head + main_src, [str(root)]
            )
            self.assertEqual(
                (tot, prv), (1, 1), "pre-fix variant should silently omit SCaller, counting SAux only"
            )

    def test_driver_failure_never_becomes_counts(self) -> None:
        # Python-side fail-closed: a driver that exits non-zero, and a driver
        # that exits 0 without printing AUDIT_RESULT, each raise a named
        # RuntimeError; neither is ever converted into declaration counts.
        with self.assertRaises(RuntimeError) as ctx:
            _run_audit_driver(
                ROOT_DIR,
                'def main (_ : List String) : IO Unit := throw (IO.userError "synthetic module IR failure")\n',
                [],
            )
        self.assertIn("Lean audit driver failed", str(ctx.exception))
        self.assertIn("synthetic module IR failure", str(ctx.exception))
        with self.assertRaises(RuntimeError) as ctx2:
            _run_audit_driver(
                ROOT_DIR,
                'def main (_ : List String) : IO Unit := IO.println "no audit marker"\n',
                [],
            )
        self.assertIn("emitted no AUDIT_RESULT", str(ctx2.exception))
        # Review F3: a malformed AUDIT_RESULT (wrong field arity) through the
        # real subprocess path is a named error, never counts.
        with self.assertRaises(RuntimeError) as ctx3:
            _run_audit_driver(
                ROOT_DIR,
                'def main (_ : List String) : IO Unit := IO.println "AUDIT_RESULT:1,2,3"\n',
                [],
            )
        self.assertIn("expected 6", str(ctx3.exception))
        # The shared parser also guards the three-group main path
        # (execute_live_lean_audit) fail-closed: wrong group count, wrong
        # field arity, non-integer fields, and a marker-less stdout each
        # raise named errors instead of IndexError/garbage counts.
        with self.assertRaises(RuntimeError) as g1:
            _parse_audit_result("AUDIT_RESULT:1,2,3,4,5,6", "", groups=3)
        self.assertIn("expected 3", str(g1.exception))
        with self.assertRaises(RuntimeError) as g2:
            _parse_audit_result("AUDIT_RESULT:1,2,3;1,2,3,4,5,6;1,2,3,4,5,6", "", groups=3)
        self.assertIn("expected 6", str(g2.exception))
        with self.assertRaises(RuntimeError) as g3:
            _parse_audit_result("AUDIT_RESULT:1,2,3,4,5,x", "", groups=1)
        self.assertIn("non-integer", str(g3.exception))
        with self.assertRaises(RuntimeError) as g4:
            _parse_audit_result("nothing here", "", groups=3)
        self.assertIn("emitted no AUDIT_RESULT", str(g4.exception))
        self.assertEqual(
            _parse_audit_result("AUDIT_RESULT:1,2,3,4,5,6;7,8,9,10,11,12", "", groups=2),
            [(1, 2, 3, 4, 5, 6), (7, 8, 9, 10, 11, 12)],
        )

    def test_corpus_scope_does_not_claim_aux_expansion_it_never_performs(self) -> None:
        # The scope text claimed compiler-generated `_closed` helpers were
        # "expanded by `expandCompilerAuxDecls`", but the measurement filters
        # compiler-generated auxiliary declarations out and never calls that
        # function (only the library's `ingestModuleDeclsWith` does). A scope
        # claim the measurement does not perform is dishonest output.
        self.assertNotIn("expandCompilerAuxDecls", CORPUS_SCOPES["c1_corpus"])

    def test_std_init_and_c2_renamed_and_external_batteries_separate_corpus(self) -> None:
        # Point 3 + H1.0b: the corpus holding Init/Std + C2 is named `std_init_and_c2`
        # (not a misleading Batteries name), and external Batteries is its own
        # top-level corpus entry: measured live from the pinned prebuilt tree when
        # one is present, else an honest `not_measured` stub with a reason and no
        # counts, never an extrapolated number.
        self.assertIn("std_init_and_c2", CORPUS_SCOPES)
        self.assertEqual(set(CORPUS_SCOPES.keys()), {"std_init_and_c2", "c1_corpus"})
        rep = build_coverage_report(ROOT_DIR)
        corpora = rep["corpora"]
        self.assertIn("std_init_and_c2", corpora)
        self.assertIn("external_batteries", corpora)
        ext = corpora["external_batteries"]
        self.assertIn(ext.get("measurement_source"), ("live_invocation", "not_measured"), ext)
        if ext["measurement_source"] == "live_invocation":
            self.assertEqual(ext["commit_sha"], PINNED_BATTERIES_REV)
            self.assertEqual(ext["module_count"], ext["expected_module_count"])
            self.assertEqual(
                ext["total_declarations"],
                ext["proved"] + ext["lowered_unproved"] + ext["rejected"],
            )
        else:
            self.assertTrue(ext.get("reason"))
            for field in RESULT_FIELDS:
                self.assertNotIn(field, ext)

    def test_batteries_numbers_come_from_the_named_olean_tree(self) -> None:
        # H1.0b: when a prebuilt pinned Batteries tree is named, its totals must come
        # from running the lowerer over it in this invocation, not a stored table,
        # and the measured module set is exactly the `Batteries*` modules (never the
        # `runLinter` exe module that a default-target build leaves beside them).
        import unittest.mock as mock

        m = sys.modules[__name__]
        saved_cache = dict(_BATTERIES_CACHE)
        with tempfile.TemporaryDirectory(prefix="bat-tree-") as tmp:
            root = Path(tmp)
            (root / ".git").mkdir()
            lib = root / ".lake" / "build" / "lib" / "lean"
            (lib / "Batteries" / "Data").mkdir(parents=True)
            (lib / "Batteries.olean").write_bytes(b"")
            (lib / "Batteries" / "Data" / "List.olean").write_bytes(b"")
            (lib / "runLinter.olean").write_bytes(b"")
            saved = os.environ.get(BATTERIES_OLEANS_ENV)
            os.environ[BATTERIES_OLEANS_ENV] = str(lib)
            try:
                _BATTERIES_CACHE.clear()
                with mock.patch.object(
                    m,
                    "_run_sharded_batteries_audit",
                    return_value=((100, 7, 11, 82, 4, 9), ["mutual_cycle"]),
                ) as run, mock.patch.object(
                    m, "_git_head", return_value=PINNED_BATTERIES_REV
                ), mock.patch.dict(
                    m.BATTERIES_PINNED_MODULE_COUNTS, {PINNED_BATTERIES_REV: 2}
                ):
                    corp = measure_external_batteries(ROOT_DIR)
            finally:
                _BATTERIES_CACHE.clear()
                _BATTERIES_CACHE.update(saved_cache)
                if saved is None:
                    os.environ.pop(BATTERIES_OLEANS_ENV, None)
                else:
                    os.environ[BATTERIES_OLEANS_ENV] = saved
        self.assertEqual(corp["measurement_source"], "live_invocation")
        self.assertEqual(
            (corp["total_declarations"], corp["proved"], corp["lowered_unproved"], corp["rejected"]),
            (100, 7, 11, 82),
        )
        self.assertEqual(
            (corp["rejected_not_lowered"], corp["compiler_aux_decls_excluded"]), (4, 9)
        )
        self.assertEqual(corp["commit_sha"], PINNED_BATTERIES_REV)
        self.assertEqual(corp["module_count"], 2)
        self.assertEqual(corp["expected_module_count"], 2)
        run.assert_called_once()
        self.assertEqual(
            run.call_args.args, (ROOT_DIR, lib, ["Batteries", "Batteries.Data.List"])
        )

    def test_batteries_absent_partial_mismatch_and_unmapped_shapes(self) -> None:
        # H1.0b fail-closed shapes, mirroring the con-leche corpus: an absent or
        # partial tree stays `not_measured` with a reason and no counts (an honest
        # skip absent a counted baseline); a FULL default-target build with a wrong
        # module count, and an unmapped pinned revision, are named errors `--check`
        # refuses.
        import unittest.mock as mock

        m = sys.modules[__name__]
        self.assertIn(PINNED_BATTERIES_REV, BATTERIES_PINNED_MODULE_COUNTS)
        saved_cache = dict(_BATTERIES_CACHE)
        with tempfile.TemporaryDirectory(prefix="bat-shapes-") as tmp:
            root = Path(tmp)
            (root / ".git").mkdir()
            build_dir = root / ".lake" / "build"
            lib = build_dir / "lib" / "lean"
            (lib / "Batteries").mkdir(parents=True)
            (lib / "Batteries.olean").write_bytes(b"")
            (lib / "Batteries" / "Basic.olean").write_bytes(b"")
            saved = os.environ.get(BATTERIES_OLEANS_ENV)
            try:
                os.environ[BATTERIES_OLEANS_ENV] = str(lib)
                _BATTERIES_CACHE.clear()
                with mock.patch.object(m, "_git_head", return_value=PINNED_BATTERIES_REV):
                    partial = measure_external_batteries(ROOT_DIR)
                    (build_dir / "bin").mkdir(parents=True)
                    (build_dir / "bin" / "runLinter").write_bytes(b"")
                    _BATTERIES_CACHE.clear()
                    full_mismatch = measure_external_batteries(ROOT_DIR)
                os.environ[BATTERIES_OLEANS_ENV] = str(root / "nonexistent")
                _BATTERIES_CACHE.clear()
                absent = measure_external_batteries(ROOT_DIR)
                with mock.patch.object(m, "PINNED_BATTERIES_REV", "deadbeef" * 5):
                    _BATTERIES_CACHE.clear()
                    unmapped = measure_external_batteries(ROOT_DIR)
            finally:
                _BATTERIES_CACHE.clear()
                _BATTERIES_CACHE.update(saved_cache)
                if saved is None:
                    os.environ.pop(BATTERIES_OLEANS_ENV, None)
                else:
                    os.environ[BATTERIES_OLEANS_ENV] = saved
        base_rep = build_coverage_report(ROOT_DIR)
        for res in (partial, absent):
            self.assertEqual(res.get("measurement_source"), "not_measured", res)
            self.assertTrue(res.get("reason"))
            for field in RESULT_FIELDS:
                self.assertNotIn(field, res)
            chk = check_coverage_report(
                ROOT_DIR, {**base_rep, "corpora": {"external_batteries": res}}
            )
            self.assertTrue(chk["ok"], chk["errors"])
        self.assertEqual(full_mismatch.get("measurement_source"), "error")
        self.assertEqual(full_mismatch.get("error_code"), "batteries_module_count_mismatch")
        self.assertEqual(unmapped.get("measurement_source"), "error")
        self.assertEqual(unmapped.get("error_code"), "unmapped_pinned_batteries_revision")
        for res, code in (
            (full_mismatch, "batteries_module_count_mismatch"),
            (unmapped, "unmapped_pinned_batteries_revision"),
        ):
            chk_bad = check_coverage_report(
                ROOT_DIR, {**base_rep, "corpora": {"external_batteries": res}}
            )
            self.assertFalse(chk_bad["ok"])
            self.assertTrue(any(code in e for e in chk_bad["errors"]), chk_bad["errors"])

    def test_batteries_shard_merge_matches_auditmods_classification(self) -> None:
        # H1.0b sharded path: the Python merger classifies per-declaration shard
        # facts exactly as auditMods does. A cycle member is rejected_not_lowered
        # without consulting its ingest verdict (even an "ok" or an error), a
        # non-cycle ok declaration splits proved vs lowered_unproved on
        # has_local_call, an ingest error is rejected with its reason head, and
        # a callee absent from the corpus graph contributes no edges.
        rows = [
            ("A", True, ["B"], "ok"),  # on the 2-cycle with B -> rejected_not_lowered
            ("B", True, ["A"], "err:boom"),  # same cycle; its ingest verdict is ignored
            ("C", True, ["A"], "ok"),  # calls into the cycle, not on it -> lowered_unproved
            ("D", False, [], "ok"),  # fully lowered, no local call -> proved
            ("E", False, [], "err:unsupported thing"),  # rejected with its reason head
            ("F", True, ["Z"], "ok"),  # callee outside the graph -> lowered_unproved
        ]
        counts, reasons = _merge_batteries_shard_facts(rows, aux_total=7)
        self.assertEqual(counts, (6, 1, 2, 3, 2, 7))
        self.assertEqual(sorted(reasons), ["mutual_cycle", "mutual_cycle", "unsupported thing"])

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
                    sys.modules[__name__], "_run_audit_driver", return_value=(100, 7, 11, 82, 4, 9)
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

    def test_fixture_corpus_counts_compiler_aux_exclusions(self) -> None:
        # Review F5: value-assert the aux count once against the live lowerer.
        # A single authored declaration still compiles with compiler-generated
        # auxiliary declarations beside it; they are counted in
        # `compiler_aux_decls_excluded` and are absent from the
        # `total_declarations` denominator (total == the 1 authored decl).
        plain = measure_fixture_corpus(
            ROOT_DIR,
            "@[export aux_plain]\ndef aux_plain (x : UInt64) : UInt64 := x + 1\n",
            mod_name="AuxPlainFixture",
        )
        self.assertEqual(plain["total_declarations"], 1, plain)
        self.assertEqual(plain["proved"], 1, plain)
        self.assertEqual(plain["compiler_aux_decls_excluded"], 1, plain)
        # A local closure over a fold lambda-lifts: more aux decls excluded,
        # and the published sum invariant holds on what IS counted.
        closure = measure_fixture_corpus(
            ROOT_DIR,
            "def helper (x : UInt64) : UInt64 := x + 7\n"
            "@[export aux_fold]\n"
            "def aux_fold (x : UInt64) : UInt64 := (List.range 3).foldl (fun a _ => helper a) x\n",
            mod_name="AuxClosureFixture",
        )
        # Round-2 F5: pin the exact measured values on the pinned toolchain
        # (the sum assertion that stood here was a tautology of auditMods).
        # total == 4, NOT 2: the 2 authored decls plus 2 compiler-generated
        # fold specializations that `isCompilerGeneratedAuxDecl` does NOT
        # class as aux, counted honestly in the denominator (helper proves;
        # the other 3 are rejected heap/closure shapes). aux == 3 > plain's 1,
        # so the lambda-lifted closure itself is among the excluded.
        self.assertEqual(
            (
                closure["total_declarations"],
                closure["proved"],
                closure["lowered_unproved"],
                closure["rejected"],
                closure["compiler_aux_decls_excluded"],
            ),
            (4, 1, 0, 3, 3),
            closure,
        )

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

        # The --check CLI's one-line human summary is asserted through its
        # extracted builder (`_human_check_summary`, the exact function main()
        # prints) over the in-process cached report, instead of spawning a cold
        # --check subprocess that would re-measure the full external Batteries
        # corpus; the end-to-end CLI path stays covered by the --json spawn
        # above and by the repository's real --check gate runs.
        summary_line = _human_check_summary(rep, True)
        self.assertIn("rejected_not_lowered", summary_line)
        self.assertIn("mutual_cycle", summary_line)
        self.assertIn("std_init_and_c2=", summary_line)
        self.assertIn("batteries=", summary_line)



def _human_check_summary(report: dict[str, Any], ok: bool) -> str:
    """The one-line human summary `--check` prints (extracted so tests can
    assert its exact content without spawning a cold CLI process that would
    re-measure every corpus)."""
    ms = report["lcnf_constructor_matrix"]["summary"]
    corpora = report["corpora"]
    parts = [
        f"[lcnf-coverage] ok={ok} "
        f"matrix={ms['proved']}/{ms['total']} proved "
        f"({ms['lowered_unproved']} lowered_unproved, {ms['rejected']} rejected)"
    ]
    for label, cname in (
        ("std_init_and_c2", "std_init_and_c2"),
        ("c1", "c1_corpus"),
        ("batteries", "external_batteries"),
        ("con_leche", "con_leche_h3_benchmark"),
    ):
        corp = corpora.get(cname, {})
        if corp.get("measurement_source") == "live_invocation":
            parts.append(
                f"{label}={corp['proved']}/{corp['total_declarations']} proved "
                f"(+{corp['lowered_unproved']} vacuous_local_call, "
                f"{corp['rejected']} rejected incl. "
                f"rejected_not_lowered={corp['rejected_not_lowered']} "
                f"[{corp['rejected_not_lowered_reason']}], "
                f"aux_excluded={corp['compiler_aux_decls_excluded']})"
            )
        elif corp.get("measurement_source") == "error":
            parts.append(f"{label}=error ({corp.get('error_code', 'error')})")
        else:
            parts.append(f"{label}=skipped (not measured)")
    return " ".join(parts)


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

    if args.write_results:
        # Fail in seconds on a dirty measurement tree, not minutes into the
        # audit: the same guard runs again inside results_document.
        try:
            _refuse_dirty_measurement_inputs(ROOT_DIR)
        except RuntimeError as exc:
            print(f"  [ERROR] {exc}", file=sys.stderr)
            return 1

    chk = check_coverage_report(
        ROOT_DIR,
        require_results=args.check,
        compare_results_digests=not args.write_results,
    )
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
        print(_human_check_summary(chk["report"], chk["ok"]))
    if not chk["ok"]:
        for err in chk["errors"]:
            print(f"  [ERROR] {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
