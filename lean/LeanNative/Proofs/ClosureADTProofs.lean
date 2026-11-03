import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.IR.ClosureADT

namespace LeanNative.Proofs

open LeanNative.IR
open LeanNative.Semantics

/-! ## C8 Deliverable 2 Soundness Proofs: Closure Defunctionalization & ADT Match Lowering

Zero `def`, zero `structure`, zero `inductive` in this file. Standard axioms only.
-/

private theorem evalTagEq_u64 (env : VarEnv) (st : HeapState) (tagVar : VarId) (a b : UInt64)
    (h : env tagVar = some (.u64 a)) :
    evalExpr env st (.scalar (.binOp .eq (.var tagVar) (.constU64 b))) =
      .ok (.bool (a == b), st) := by
  simp only [evalExpr, evalScalarExpr, h]
  rfl

/-- Tag read of a live heap constructor: `lean_native_ctor_tag` returns the object's tag. -/
theorem ctorTag_obj_sound (env : VarEnv) (st : HeapState) (v : VarId) (objId : Nat)
    (henv : env v = some (.objPtr objId)) (o : HeapObj)
    (hlive : st.liveHeapObj objId = .ok o) :
    evalExpr env st (.call "lean_native_ctor_tag" [v] .i64 false) =
      .ok (.u64 o.tag.toUInt64, st) := by
  simp only [evalExpr, evalVarList, henv]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h1 : ("lean_native_ctor_tag" == "lean_native_box_u64") = false := rfl
  have h2 : ("lean_native_ctor_tag" == "lean_native_unbox_u64") = false := rfl
  have h3 : ("lean_native_ctor_tag" == "lean_native_ensure_exclusive") = false := rfl
  have h4 : ("lean_native_ctor_tag" == "lean_native_sarray_len") = false := rfl
  have h5 : ("lean_native_ctor_tag" == "lean_native_ctor_set") = false := rfl
  have h6 : ("lean_native_ctor_tag" == "lean_native_ctor_set_scalar") = false := rfl
  have h7 : ("lean_native_ctor_tag" == "lean_native_ctor_set_tag") = false := rfl
  have h8 : ("lean_native_ctor_tag" == "lean_native_del_obj") = false := rfl
  have h9 : ("lean_native_ctor_tag" == "lean_native_ctor_tag") = true := rfl
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hlive]
  rfl

/-- Tag read of a fieldless constructor tuple `.tuple [.u64 tag]`. -/
theorem ctorTag_tuple_sound (env : VarEnv) (st : HeapState) (v : VarId) (tag : UInt64)
    (henv : env v = some (.tuple [.u64 tag])) :
    evalExpr env st (.call "lean_native_ctor_tag" [v] .i64 false) = .ok (.u64 tag, st) := by
  simp [evalExpr, evalVarList, henv]

/-- Projecting object slot `idx` of a live constructor yields that captured field. -/
theorem ctorGetObj_sound (env : VarEnv) (st : HeapState) (v : VarId) (objId idx : Nat)
    (henv : env v = some (.objPtr objId)) (o : HeapObj) (fld : Val)
    (hlive : st.liveHeapObj objId = .ok o) (hidx : o.objFields[idx]? = some fld) :
    evalExpr env st (.ctorGetObj v idx) = .ok (fld, st) := by
  simp only [evalExpr, evalCtorGet, henv, hlive, ↓reduceIte]
  dsimp only [Bind.bind, Except.bind]
  rw [hidx]

/-- `lowerClosureAlloc` allocates a fresh closure object and threads it into `k`. -/
theorem lowerClosureAlloc_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (dst : VarId) (cl : ClosureSpec) (k : LNIRCode) (vals : List Val)
    (hvals : evalVarList env (cl.fields.map (·.src)) = .ok vals) (hne : vals.isEmpty = false)
    (hwf : vals.all Val.wfField = true) (v : Val) (st' : HeapState)
    (hk : evalCode fuel (env.bind dst (.objPtr (st.nextId + 1)))
        (st.allocHeapCtor cl.codeIdx vals []).2 k = .ok (v, st')) :
    evalCode fuel env st (lowerClosureAlloc dst cl k) = .ok (v, st') := by
  unfold lowerClosureAlloc
  rw [evalCode]
  have hexpr : evalExpr env st (.allocCtor cl.codeIdx (cl.fields.map (·.src)) []) =
      .ok (.objPtr (st.nextId + 1), (st.allocHeapCtor cl.codeIdx vals []).2) := by
    have hempty : evalVarList env [] = .ok [] := rfl
    simp only [evalExpr, hvals, hempty, hne, hwf, Bool.false_and, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hexpr]
  exact hk

/-- `specializeKnownClosure` evaluates the direct call with captured fields prepended to `extra`. -/
theorem specializeKnownClosure_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (dst : VarId) (retTy : LNIRType) (fnName : String) (cl : ClosureSpec)
    (extra : List VarId) (k : LNIRCode) (res : Val) (st1 : HeapState) (v : Val) (st' : HeapState)
    (hcall : evalExpr env st (.call fnName (cl.fields.map (·.src) ++ extra) retTy false) = .ok (res, st1))
    (hk : evalCode fuel (env.bind dst res) st1 k = .ok (v, st')) :
    evalCode fuel env st (specializeKnownClosure dst retTy fnName cl extra k) = .ok (v, st') := by
  unfold specializeKnownClosure
  rw [evalCode, hcall]
  exact hk

/-- Single-step execution of a closure `seqFor` combinator over a non-empty `[lo, lo + 1)` range. -/
theorem lowerClosureSeqFor_step1_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (idx lo hi acc init : VarId) (accTy : LNIRType) (body k : LNIRCode)
    (n : UInt64) (initV stepV v : Val) (st1 st' : HeapState)
    (hlo : env lo = some (.u64 n)) (hhi : env hi = some (.u64 (n + 1)))
    (hbound : n.toNat + 1 < UInt64.size)
    (hinit : env init = some initV)
    (hbody : evalCode fuel ((env.bind idx (.u64 n.toNat.toUInt64)).bind acc initV) st body = .ok (stepV, st1))
    (hk : evalCode fuel (env.bind acc stepV) st1 k = .ok (v, st')) :
    evalCode fuel env st (lowerClosureSeqFor idx lo hi acc init accTy body k) = .ok (v, st') := by
  unfold lowerClosureSeqFor
  rw [evalCode]
  simp only [hlo, hhi, hinit]
  have hcnt : (n + 1).toNat - n.toNat = 1 := by
    have : (n + 1).toNat = n.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt hbound]
    omega
  rw [hcnt]
  simp only [evalSeqLoop, hbody]
  exact hk

/-- Matching tag arm: when `tagVar` holds `arm.tag.toUInt64` the arm body is taken. -/
theorem adtMatchArm_taken (fuel : Nat) (env : VarEnv) (st : HeapState)
    (tagVar cond : VarId) (tag : Nat) (thenB rest : LNIRCode) (v : Val) (st' : HeapState)
    (htag : env tagVar = some (.u64 tag.toUInt64))
    (htaken : evalCode fuel (env.bind cond (.bool true)) st thenB = .ok (v, st')) :
    evalCode fuel env st
      (.letBind cond .i1 (.scalar (.binOp .eq (.var tagVar) (.constU64 tag.toUInt64))) (.ite cond thenB rest)) =
      .ok (v, st') := by
  rw [evalCode, evalTagEq_u64 env st tagVar tag.toUInt64 tag.toUInt64 htag]
  simp only [beq_self_eq_true]
  rw [evalCode]
  simp only [VarEnv.bind_self]
  exact htaken

/-- Non-matching tag arm: when `seen ≠ arm.tag.toUInt64`, execution falls through to `rest`. -/
theorem adtMatchArm_fallthrough (fuel : Nat) (env : VarEnv) (st : HeapState)
    (tagVar cond : VarId) (tag : Nat) (seen : UInt64) (thenB rest : LNIRCode) (v : Val) (st' : HeapState)
    (hdiff : (seen == tag.toUInt64) = false) (htag : env tagVar = some (.u64 seen))
    (hrest : evalCode fuel (env.bind cond (.bool false)) st rest = .ok (v, st')) :
    evalCode fuel env st
      (.letBind cond .i1 (.scalar (.binOp .eq (.var tagVar) (.constU64 tag.toUInt64))) (.ite cond thenB rest)) =
      .ok (v, st') := by
  rw [evalCode, evalTagEq_u64 env st tagVar seen tag.toUInt64 htag]
  simp only [hdiff]
  rw [evalCode]
  simp only [VarEnv.bind_self]
  exact hrest

/-- Defunctionalization soundness: packing a captured value with `lowerClosureAlloc` then reading
    slot `0` with `lowerClosureGetField` recovers the exact captured value with live heap state. -/
theorem defunctionalizeClosure_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (cap clVar outVar : VarId) (ty : LNIRType) (codeIdx : Nat) (captured : Val)
    (hcap : env cap = some captured) (hwf : captured.wfField = true) :
    evalCode fuel env st
      (lowerClosureAlloc clVar { codeIdx := codeIdx, fields := [{ src := cap, ty := ty }] }
        (lowerClosureGetField outVar ty clVar 0 (.ret outVar))) =
      .ok (captured, (st.allocHeapCtor codeIdx [captured] []).2) := by
  have hvals : evalVarList env (([{ src := cap, ty := ty }] : List CapturedField).map (·.src)) =
      .ok [captured] := by simp [evalVarList, hcap]
  apply lowerClosureAlloc_sound fuel env st clVar
    { codeIdx := codeIdx, fields := [{ src := cap, ty := ty }] }
    (lowerClosureGetField outVar ty clVar 0 (.ret outVar)) [captured] hvals rfl (by simp [hwf])
  let st1 := (st.allocHeapCtor codeIdx [captured] []).2
  let objId := st.nextId + 1
  have hlive : st1.liveHeapObj objId =
      .ok { id := objId, tag := codeIdx, objFields := [captured], scalarFields := [] } := by
    simp [st1, objId, HeapState.allocHeapCtor, HeapState.liveHeapObj,
      HeapState.getObjRefCount, HeapState.findHeapObj]
  unfold lowerClosureGetField
  rw [evalCode, ctorGetObj_sound _ st1 clVar objId 0 (VarEnv.bind_self _ _ _) _ captured hlive rfl]
  dsimp only
  rw [evalCode]
  simp only [VarEnv.bind_self]
  rfl

/-- End-to-end ADT `match` soundness (`lowerAdtMatch_sound`): on a 2-arm ADT `match`, if the
    scrutinee is a live constructor whose tag matches arm 2 (falling past arm 1), `lowerAdtMatch`
    projects arm 2's payload field and evaluates arm 2's body. -/
theorem lowerAdtMatch_sound (fuel : Nat) (env : VarEnv) (st : HeapState)
    (scrut tagVar condBase : VarId) (objId tag1 tag2 : Nat) (o : HeapObj) (fldVal : Val)
    (arm1 arm2 fallback : LNIRCode) (fld : CapturedField) (v : Val) (st' : HeapState)
    (htag_scr : scrut ≠ tagVar) (hc0_scr : scrut ≠ condBase) (hc1_scr : scrut ≠ condBase + 1)
    (hc0_tag : tagVar ≠ condBase)
    (hdiff : (tag2.toUInt64 == tag1.toUInt64) = false)
    (hscr : env scrut = some (.objPtr objId)) (hlive : st.liveHeapObj objId = .ok o)
    (ho_tag : o.tag = tag2) (hfld : o.objFields[0]? = some fldVal)
    (harm2 : evalCode fuel
        ((((env.bind tagVar (.u64 tag2.toUInt64)).bind condBase (.bool false)).bind
          (condBase + 1) (.bool true)).bind fld.src fldVal)
        st arm2 = .ok (v, st')) :
    evalCode fuel env st (lowerAdtMatch scrut tagVar condBase
      [ { tag := tag1, fields := [], body := arm1 }
      , { tag := tag2, fields := [fld], body := arm2 } ] fallback) = .ok (v, st') := by
  unfold lowerAdtMatch lowerAdtMatchArms
  rw [evalCode, ctorTag_obj_sound env st scrut objId hscr o hlive, ho_tag]
  dsimp only
  let env1 := env.bind tagVar (.u64 tag2.toUInt64)
  have ht1 : env1 tagVar = some (.u64 tag2.toUInt64) := VarEnv.bind_self _ _ _
  apply adtMatchArm_fallthrough _ _ _ tagVar condBase tag1 tag2.toUInt64 _ _ _ _ hdiff ht1
  let env2 := env1.bind condBase (.bool false)
  have ht2 : env2 tagVar = some (.u64 tag2.toUInt64) := by
    simp [env2, beq_false_of_ne hc0_tag, ht1]
  apply adtMatchArm_taken _ _ _ tagVar (condBase + 1) tag2 _ _ _ _ ht2
  let env3 := env2.bind (condBase + 1) (.bool true)
  have hscr3 : env3 scrut = some (.objPtr objId) := by
    simp [env3, env2, env1, beq_false_of_ne hc1_scr,
      beq_false_of_ne hc0_scr, beq_false_of_ne htag_scr, hscr]
  unfold bindAdtFields
  rw [evalCode, ctorGetObj_sound env3 st scrut objId 0 hscr3 o fldVal hlive hfld]
  exact harm2

end LeanNative.Proofs
