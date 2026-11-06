import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.RealLCNFBridge
import LeanNative.IR.RealLCNFSemantics
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.RealLCNFBridge.CtorIntrinsic

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.IR.RealLCNFBridge
open LeanNative.IR.RealLCNFSemantics
open LeanNative.Semantics

/-! ## Wave 0.A Soundness Proofs: Zero-Copy `ByteArray` / `FloatArray` Slice Intrinsic Lowering

Zero `def`, zero `structure`, zero `inductive` in this file. Standard axioms only.
Follows `AGENTS.md` Layer I / Layer II discipline: reusable parameterized Layer I combinators
followed by `≤ 3`-line Layer II corollaries covering both target `evalExpr` semantics and
end-to-end `RealLCNFSemantics` source-to-target `.fap` refinement.
-/

/-! ### Layer I — Parameterized Slice Intrinsic Combinators -/

/-- Layer I combinator: any canonical zero-copy length intrinsic (`ByteArray.usize`, `FloatArray.usize`)
    lowering to `.sarrayLen arrVar` evaluates to `buf.data.size.toUInt64` without mutating `HeapState`. -/
theorem evalSliceLen_of_lower
    (fnName : Lean.Name) (elemTy retTy : LNIRType) (arch : TargetArch)
    (env : VarEnv) (st : HeapState) (arrVar : VarId) (bufId : Nat) (buf : ArrayBuffer)
    (e : LNIRExpr)
    (hlow : lowerSliceIntrinsicPure? fnName [arrVar] retTy [.sarray elemTy] false arch = some e)
    (harr : env arrVar = some (.sarrayId bufId))
    (hfind : st.findBuffer bufId = some buf) :
    evalExpr env st e = .ok (.u64 buf.data.size.toUInt64, st) := by
  unfold lowerSliceIntrinsicPure? at hlow
  cases hwasm : arch.isWasm
  · rw [hwasm] at hlow
    have hs0 : stripErasedSliceArgs? [arrVar] [.sarray elemTy] = some ([arrVar], [.sarray elemTy]) := rfl
    simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte, hs0] at hlow
    cases hc : (((fnName == ``ByteArray.usize && lnirTypeEq elemTy .i8) ||
        (fnName == ``FloatArray.usize && lnirTypeEq elemTy .f64)) &&
        (lnirTypeEq retTy .i64 || (lnirTypeEq retTy .usize && archSupportsUSize arch)))
    · simp [hc] at hlow
    · simp only [hc, ↓reduceIte] at hlow
      injection hlow with h'
      subst h'
      simp [evalExpr, harr, hfind]
  · rw [hwasm] at hlow; simp at hlow

/-- Layer I combinator: any canonical proof-indexed slice read intrinsic (`ByteArray.uget`, `FloatArray.uget`)
    lowering to `.sarrayGet arrVar idxVar elemTy` reads the masked element `maskElemVal elemTy elem` at `idx.toNat`
    without mutating `HeapState`. -/
theorem evalSliceUget_of_lower
    (fnName : Lean.Name) (elemTy idxTy retTy : LNIRType) (arch : TargetArch)
    (env : VarEnv) (st : HeapState) (arrVar idxVar : VarId)
    (bufId : Nat) (idx elem : UInt64) (e : LNIRExpr)
    (hnotUnit : lnirTypeEq idxTy .unit = false)
    (hlow : lowerSliceIntrinsicPure? fnName [arrVar, idxVar] retTy [.sarray elemTy, idxTy] false arch = some e)
    (harr : env arrVar = some (.sarrayId bufId))
    (hidx : env idxVar = some (.u64 idx))
    (hread : st.readElem bufId idx.toNat = .ok elem) :
    evalExpr env st e = .ok (.u64 (maskElemVal elemTy elem), st) := by
  unfold lowerSliceIntrinsicPure? at hlow
  cases hwasm : arch.isWasm
  · rw [hwasm] at hlow
    have hs0 : stripErasedSliceArgs? [arrVar, idxVar] [.sarray elemTy, idxTy] =
        some ([arrVar, idxVar], [.sarray elemTy, idxTy]) := by
      simp [stripErasedSliceArgs?, hnotUnit]
      rfl
    simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte, hs0] at hlow
    cases hvi : (lnirTypeEq idxTy .i64 || (lnirTypeEq idxTy .usize && archSupportsUSize arch))
    · simp [hvi] at hlow
    · simp only [hvi, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hlow
      cases hg : ((fnName == ``ByteArray.uget && lnirTypeEq elemTy .i8 && lnirTypeEq retTy .i8) ||
          (fnName == ``FloatArray.uget && lnirTypeEq elemTy .f64 && lnirTypeEq retTy .f64))
      · simp [hg] at hlow
      · simp only [hg, ↓reduceIte] at hlow
        injection hlow with h'
        subst h'
        simp [evalExpr, harr, hidx, hread]
  · rw [hwasm] at hlow; simp at hlow

/-- Layer I combinator: canonical slice `.fap` source-to-target refinement (stripping internal `ctor?` witness). -/
theorem lowerSliceCall_refines_of_name
    (fnName : Lean.Name) (retTy : LNIRType)
    (ctx : RealBridgeCtx) (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState)
    (args : Array (Lean.Compiler.LCNF.Arg .impure)) (himp : Lean.Compiler.LCNF.Purity.impure = .impure)
    (expr : LNIRExpr) (v : Val) (ctor? : Option Lean.Name) (hinv : BridgeStateInv st lenv venv)
    (hs : lowerSliceCallPure? st fnName args.toList retTy (ctx.findLocalCallee? fnName).isSome ctx.arch = some expr)
    (ho : evalLetValue ctx lenv hst (.fap fnName args himp) retTy = .ok (v, hst', ctor?)) :
    evalExpr venv hst expr = .ok (v, hst') ∧ hst' = hst ∧ ctor? = none := by
  rcases lowerSliceCallPure_sound ctx st lenv venv hst hst' fnName args himp retTy expr v ctor?
    hinv hs ho with ⟨he, hh, hc, _⟩
  exact ⟨he, hh, hc⟩

/-! ### Layer II — `≤ 3`-Line Concrete Intrinsic Soundness & Source-to-Target Refinement Corollaries -/

/-- Canonical `ByteArray.usize` over `.sarray .i8` evaluates to `buf.data.size.toUInt64` without mutating `HeapState`. -/
theorem lowerSliceIntrinsic_byteArrayUsize_sound
    (env : VarEnv) (st : HeapState) (arrVar : VarId) (bufId : Nat) (buf : ArrayBuffer) (e : LNIRExpr)
    (hlow : lowerSliceIntrinsicPure? ``ByteArray.usize [arrVar] .usize [.sarray .i8] false .x86_64 = some e)
    (harr : env arrVar = some (.sarrayId bufId)) (hfind : st.findBuffer bufId = some buf) :
    evalExpr env st e = .ok (.u64 buf.data.size.toUInt64, st) :=
  evalSliceLen_of_lower ``ByteArray.usize .i8 .usize .x86_64 env st arrVar bufId buf e hlow harr hfind

/-- Canonical `FloatArray.usize` over `.sarray .f64` evaluates to `buf.data.size.toUInt64` without mutating `HeapState`. -/
theorem lowerSliceIntrinsic_floatArrayUsize_sound
    (env : VarEnv) (st : HeapState) (arrVar : VarId) (bufId : Nat) (buf : ArrayBuffer) (e : LNIRExpr)
    (hlow : lowerSliceIntrinsicPure? ``FloatArray.usize [arrVar] .usize [.sarray .f64] false .x86_64 = some e)
    (harr : env arrVar = some (.sarrayId bufId)) (hfind : st.findBuffer bufId = some buf) :
    evalExpr env st e = .ok (.u64 buf.data.size.toUInt64, st) :=
  evalSliceLen_of_lower ``FloatArray.usize .f64 .usize .x86_64 env st arrVar bufId buf e hlow harr hfind

/-- Canonical `ByteArray.uget` over `(.sarray .i8, .usize)` reads `elem &&& 0xff` at `idx.toNat` without mutating `HeapState`. -/
theorem lowerSliceIntrinsic_byteArrayUget_sound
    (env : VarEnv) (st : HeapState) (arrVar idxVar : VarId) (bufId : Nat) (idx elem : UInt64) (e : LNIRExpr)
    (hlow : lowerSliceIntrinsicPure? ``ByteArray.uget [arrVar, idxVar] .i8 [.sarray .i8, .usize] false .x86_64 = some e)
    (harr : env arrVar = some (.sarrayId bufId)) (hidx : env idxVar = some (.u64 idx))
    (hread : st.readElem bufId idx.toNat = .ok elem) :
    evalExpr env st e = .ok (.u64 (elem &&& 0xff), st) :=
  evalSliceUget_of_lower ``ByteArray.uget .i8 .usize .i8 .x86_64 env st arrVar idxVar bufId idx elem e
    rfl hlow harr hidx hread

/-- Canonical `FloatArray.uget` over `(.sarray .f64, .usize)` reads `elem` at `idx.toNat` without mutating `HeapState`. -/
theorem lowerSliceIntrinsic_floatArrayUget_sound
    (env : VarEnv) (st : HeapState) (arrVar idxVar : VarId) (bufId : Nat) (idx elem : UInt64) (e : LNIRExpr)
    (hlow : lowerSliceIntrinsicPure? ``FloatArray.uget [arrVar, idxVar] .f64 [.sarray .f64, .usize] false .x86_64 = some e)
    (harr : env arrVar = some (.sarrayId bufId)) (hidx : env idxVar = some (.u64 idx))
    (hread : st.readElem bufId idx.toNat = .ok elem) :
    evalExpr env st e = .ok (.u64 elem, st) :=
  evalSliceUget_of_lower ``FloatArray.uget .f64 .usize .f64 .x86_64 env st arrVar idxVar bufId idx elem e
    rfl hlow harr hidx hread

/-- Source-to-target `RealLCNFSemantics` refinement for `ByteArray.usize` `.fap` calls. -/
theorem lowerSliceCall_byteArrayUsize_refines
    (ctx : RealBridgeCtx) (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState)
    (args : Array (Lean.Compiler.LCNF.Arg .impure)) (himp : Lean.Compiler.LCNF.Purity.impure = .impure)
    (expr : LNIRExpr) (v : Val) (ctor? : Option Lean.Name) (hinv : BridgeStateInv st lenv venv)
    (hs : lowerSliceCallPure? st ``ByteArray.usize args.toList .usize
      (ctx.findLocalCallee? ``ByteArray.usize).isSome ctx.arch = some expr)
    (ho : evalLetValue ctx lenv hst (.fap ``ByteArray.usize args himp) .usize = .ok (v, hst', ctor?)) :
    evalExpr venv hst expr = .ok (v, hst') ∧ hst' = hst ∧ ctor? = none :=
  lowerSliceCall_refines_of_name ``ByteArray.usize .usize
    ctx st lenv venv hst hst' args himp expr v ctor? hinv hs ho

/-- Source-to-target `RealLCNFSemantics` refinement for `FloatArray.usize` `.fap` calls. -/
theorem lowerSliceCall_floatArrayUsize_refines
    (ctx : RealBridgeCtx) (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState)
    (args : Array (Lean.Compiler.LCNF.Arg .impure)) (himp : Lean.Compiler.LCNF.Purity.impure = .impure)
    (expr : LNIRExpr) (v : Val) (ctor? : Option Lean.Name) (hinv : BridgeStateInv st lenv venv)
    (hs : lowerSliceCallPure? st ``FloatArray.usize args.toList .usize
      (ctx.findLocalCallee? ``FloatArray.usize).isSome ctx.arch = some expr)
    (ho : evalLetValue ctx lenv hst (.fap ``FloatArray.usize args himp) .usize = .ok (v, hst', ctor?)) :
    evalExpr venv hst expr = .ok (v, hst') ∧ hst' = hst ∧ ctor? = none :=
  lowerSliceCall_refines_of_name ``FloatArray.usize .usize
    ctx st lenv venv hst hst' args himp expr v ctor? hinv hs ho

/-- Source-to-target `RealLCNFSemantics` refinement for `ByteArray.uget` `.fap` calls (including erased proof args). -/
theorem lowerSliceCall_byteArrayUget_refines
    (ctx : RealBridgeCtx) (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState)
    (args : Array (Lean.Compiler.LCNF.Arg .impure)) (himp : Lean.Compiler.LCNF.Purity.impure = .impure)
    (expr : LNIRExpr) (v : Val) (ctor? : Option Lean.Name) (hinv : BridgeStateInv st lenv venv)
    (hs : lowerSliceCallPure? st ``ByteArray.uget args.toList .i8
      (ctx.findLocalCallee? ``ByteArray.uget).isSome ctx.arch = some expr)
    (ho : evalLetValue ctx lenv hst (.fap ``ByteArray.uget args himp) .i8 = .ok (v, hst', ctor?)) :
    evalExpr venv hst expr = .ok (v, hst') ∧ hst' = hst ∧ ctor? = none :=
  lowerSliceCall_refines_of_name ``ByteArray.uget .i8
    ctx st lenv venv hst hst' args himp expr v ctor? hinv hs ho

/-- Source-to-target `RealLCNFSemantics` refinement for `FloatArray.uget` `.fap` calls (including erased proof args). -/
theorem lowerSliceCall_floatArrayUget_refines
    (ctx : RealBridgeCtx) (st : RealBridgeState) (lenv : LEnv) (venv : VarEnv) (hst hst' : HeapState)
    (args : Array (Lean.Compiler.LCNF.Arg .impure)) (himp : Lean.Compiler.LCNF.Purity.impure = .impure)
    (expr : LNIRExpr) (v : Val) (ctor? : Option Lean.Name) (hinv : BridgeStateInv st lenv venv)
    (hs : lowerSliceCallPure? st ``FloatArray.uget args.toList .f64
      (ctx.findLocalCallee? ``FloatArray.uget).isSome ctx.arch = some expr)
    (ho : evalLetValue ctx lenv hst (.fap ``FloatArray.uget args himp) .f64 = .ok (v, hst', ctor?)) :
    evalExpr venv hst expr = .ok (v, hst') ∧ hst' = hst ∧ ctor? = none :=
  lowerSliceCall_refines_of_name ``FloatArray.uget .f64
    ctx st lenv venv hst hst' args himp expr v ctor? hinv hs ho

/-- Fail-closed safety gate (Mutant Kill #1): local user-defined shadowing functions (`isLocal = true`)
    are NEVER lowered as trusted `ByteArray` / `FloatArray` intrinsics. -/
theorem lowerSliceIntrinsic_rejects_local_shadow
    (fnName : Lean.Name) (args : List VarId) (retTy : LNIRType)
    (argTys : List LNIRType) (arch : TargetArch) :
    lowerSliceIntrinsicPure? fnName args retTy argTys true arch = none :=
  rfl

/-- Fail-closed safety gate (Mutant Kill #2): untyped heap `.objPtr` arguments are rejected (`none`). -/
theorem lowerSliceIntrinsic_rejects_heap_objPtr
    (arrVar idxVar : VarId) :
    lowerSliceIntrinsicPure? ``ByteArray.uget [arrVar, idxVar] .i8 [.objPtr, .usize] false .x86_64 = none :=
  rfl

/-- Fail-closed safety gate (Mutant Kill #3): element-width mismatch (`ByteArray.uget` on `.sarray .f64`)
    is rejected (`none`). -/
theorem lowerSliceIntrinsic_rejects_element_mismatch
    (arrVar idxVar : VarId) :
    lowerSliceIntrinsicPure? ``ByteArray.uget [arrVar, idxVar] .i8 [.sarray .f64, .usize] false .x86_64 = none :=
  rfl

/-- Fail-closed safety gate (Mutant Kill #4): panicking `ByteArray.get!` is rejected (`none`)
    rather than lowered to raw unchecked GEP. -/
theorem lowerSliceIntrinsic_rejects_panicking_getBang
    (arrVar idxVar : VarId) :
    lowerSliceIntrinsicPure? ``ByteArray.get! [arrVar, idxVar] .i8 [.sarray .i8, .usize] false .x86_64 = none :=
  rfl

end LeanNative.Proofs
